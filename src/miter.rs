//! The struct used to perform combinational equivalence checking between two AIGs.
//!
//! For background on what is a miter, please check
//! [Verification of large synthesized designs](https://doi.org/10.1109/ICCAD.1993.580110) by D. Brand.
//!
//! To see how to use it in practice, check [`Miter`] and [`cnf`] docs.
//!
//! [`cnf`]: crate::cnf

use std::{
    cmp::max,
    collections::{HashMap, HashSet},
    num::TryFromIntError,
};

use thiserror::Error;

use crate::{
    Aig, AigError, AigNode, AigNodeRef, NodeId, Result,
    cnf::{Cnf, Lit},
    dfs::Dfs,
};

/// Error returned when an operation related to the miter fails
/// (creation, combinational equivalence checking, ...).
#[derive(Debug, Error)]
pub enum MiterError {
    /// Creation of a miter failed because the two AIGs have different inputs.
    /// We are just checking for the inputs id, they should correspond.
    #[error("AIGs have different inputs: {0:?} vs {1:?}")]
    MiterDifferentInputs(HashSet<NodeId>, HashSet<NodeId>),

    /// Creation of a miter failed because the two AIGs have different latches.
    /// We are just checking for the latches id, they should correspond.
    /// We don't care about the potential initialized value of the latch.
    #[error("AIGs have different latches: {0:?} vs {1:?}")]
    MiterDifferentLatches(HashSet<NodeId>, HashSet<NodeId>),

    /// Creation of a miter failed because the two AIGs have different outputs.
    /// We cannot compare the id of each output because they might change,
    /// so we are just checking that all outputs are mapped between the two AIGs.
    #[error("trying to construct a miter between two AIGs with different outputs")]
    MiterDifferentOutputs,

    /// A node was not mapped to any SAT literal in the miter.
    #[error("node id {0} is not mapped to any literal")]
    UnmappedNodeToLit(NodeId),

    /// Conversion from a NodeId to a SAT literal failed.
    /// Inputs are assigned their own index as SAT literals.
    /// However, an input id is represented as a `u64`, and a SAT literal is a `i64`
    /// so the conversion might fail.
    #[error("conversion from NodeId to Lit failed because of {0}")]
    NodeIdToLit(TryFromIntError),
}

impl From<TryFromIntError> for MiterError {
    fn from(value: TryFromIntError) -> Self {
        MiterError::NodeIdToLit(value)
    }
}

/// The struct used to perform combinational equivalence checking between two AIGs.
///
/// For background on what is a miter, please check
/// [Verification of large synthesized designs](https://doi.org/10.1109/ICCAD.1993.580110) by D. Brand.
///
/// To use this struct:
/// - create a new miter with [`Miter::new`]
/// - (optional) merge internal nodes: verify they are equivalent using [`extract_cnf_node`],
///   and use [`merge`] if the extracted formula was UNSAT (it will incrementally simplify
///   the search space of the generated SAT queries). In case of an obvious merging,
///   you can also use [`mergeable`] to determine wether two nodes can be obviously merged.
/// - then prove the two original AIGs are equivalent using [`extract_cnf`]:
///   if the extracted formula is UNSAT, AIGs are equivalent. Else if it is SAT, then
///   you have determined an input vector on which the AIGs differ.
///
/// [`extract_cnf_node`]: Miter::extract_cnf_node
/// [`merge`]: Miter::merge
/// [`mergeable`]: Miter::mergeable
/// [`extract_cnf`]: Miter::extract_cnf
pub struct Miter {
    /// The reference miter.
    /// Public for crate because it is required for [`Miter::to_dot`], implemented in [`crate::dot`].
    pub(super) a: Aig,
    /// The optimized miter.
    /// Public for crate because it is required for [`Miter::to_dot`], implemented in [`crate::dot`].
    pub(super) b: Aig,
    /// Maps outputs of `a` to outputs of `b`.
    /// Public for crate because it is required for [`Miter::to_dot`], implemented in [`crate::dot`].
    pub(super) outputs_map: HashMap<(NodeId, bool), (NodeId, bool)>,
    /// Associating a SAT literal to each node.
    /// Nodes from `a` might also refer a literal originally associated with a node of `b`.
    litmap_a: HashMap<NodeId, Lit>,
    /// Associating a SAT literal to each node.
    /// Nodes from `a` might also refer a literal originally associated with a node of `b`.
    litmap_b: HashMap<NodeId, Lit>,
    /// Keeping track of all nodes from `a` which has been merged to a node of `b`,
    /// ie nodes of `a` pointing at the same SAT literal as a node of `b`.
    merged_a: HashSet<NodeId>,
    /// Keep track of all merged nodes (id_a, id_b, complement).
    /// Complement indicates wether nodes have equal boolean functions, or complemented ones.
    merged: HashSet<(NodeId, NodeId, bool)>,
    /// The index of the next literal (for internal use only).
    next_lit: i64,
}

fn check_outputs(
    a: &Aig,
    b: &Aig,
    outputs_map: &HashMap<(NodeId, bool), (NodeId, bool)>,
) -> Result<()> {
    // Checking outputs of a are registered
    if a.get_outputs()
        .iter()
        .map(|output| (output.get_node_id(), output.get_complement()))
        .collect::<HashSet<(u64, bool)>>()
        != outputs_map.keys().copied().collect()
    {
        return Err(MiterError::MiterDifferentOutputs.into());
    }

    // Checking outputs of b are registered
    if b.get_outputs()
        .iter()
        .map(|output| (output.get_node_id(), output.get_complement()))
        .collect::<HashSet<(u64, bool)>>()
        != outputs_map.values().copied().collect()
    {
        return Err(MiterError::MiterDifferentOutputs.into());
    }

    Ok(())
}

impl Miter {
    /// Create miter between two AIGs.
    ///
    /// This will fail if:
    /// - the given AIGs have different inputs (ie inputs with different ids)
    /// - or they have different latches
    /// - or they have different outputs.
    ///
    /// To check the latter, the `outputs_map` is used:
    /// every output of `a` must be mapped to an output of `b`.
    pub fn new(
        a: &Aig,
        b: &Aig,
        outputs_map: HashMap<(NodeId, bool), (NodeId, bool)>,
    ) -> Result<Self> {
        // Checking inputs
        if a.get_inputs_id() != b.get_inputs_id() {
            return Err(
                MiterError::MiterDifferentInputs(a.get_inputs_id(), b.get_inputs_id()).into(),
            );
        }

        // Checking latches
        if a.get_latches_id() != b.get_latches_id() {
            return Err(
                MiterError::MiterDifferentLatches(a.get_latches_id(), b.get_latches_id()).into(),
            );
        }

        // Checking outputs
        check_outputs(a, b, &outputs_map)?;

        // Finding the first usable literal (ie not used by any input)
        let max_input_id = i64::try_from(*a.get_inputs_id().iter().max().unwrap_or(&1))
            .map_err(MiterError::from)?;
        let max_latch_id = i64::try_from(*a.get_latches_id().iter().max().unwrap_or(&1))
            .map_err(MiterError::from)?;
        let next_lit = max(max_input_id, max_latch_id);

        let mut miter = Miter {
            a: a.clone(),
            b: b.clone(),
            outputs_map,
            litmap_a: HashMap::new(),
            litmap_b: HashMap::new(),
            merged: HashSet::new(),
            merged_a: HashSet::new(),
            next_lit,
        };
        miter.initialize_litmaps()?;

        Ok(miter)
    }

    fn initialize_litmaps(&mut self) -> Result<()> {
        // Assigning literals to nodes in a
        let mut dfs = Dfs::from_outputs(&self.a);
        while let Some(n) = dfs.next(&self.a) {
            match *n.borrow() {
                AigNode::Input(id) => self
                    .litmap_a
                    .insert(id, Lit::try_from(id).map_err(MiterError::from)?),
                // Warning: we don't care wether the latch is initialized or not.
                AigNode::Latch { id, .. } => self
                    .litmap_a
                    .insert(id, Lit::try_from(id).map_err(MiterError::from)?),
                AigNode::And { id, .. } => {
                    let lit = self.fresh_lit();
                    self.litmap_a.insert(id, lit)
                }
                AigNode::False => None,
            };
        }

        // Same for b
        let mut dfs = Dfs::from_outputs(&self.b);
        while let Some(n) = dfs.next(&self.b) {
            match *n.borrow() {
                AigNode::Input(id) => self
                    .litmap_b
                    .insert(id, Lit::try_from(id).map_err(MiterError::from)?),
                // Warning: we don't care wether the latch is initialized or not.
                AigNode::Latch { id, .. } => self
                    .litmap_b
                    .insert(id, Lit::try_from(id).map_err(MiterError::from)?),
                AigNode::And { id, .. } => {
                    let lit = self.fresh_lit();
                    self.litmap_b.insert(id, lit)
                }
                AigNode::False => None,
            };
        }

        Ok(())
    }

    /// Returns a yet unused SAT literal.
    pub fn fresh_lit(&mut self) -> Lit {
        // Make sure next_lit is initialized above all inputs/latches id.
        let lit = self.next_lit.into();
        self.next_lit += 1;
        lit
    }

    /// Internal DFS not investigating children of a merged node.
    ///
    fn extract_cnf_from(
        &self,
        node: AigNodeRef,
        cnf: &mut Cnf,
        done: &mut HashSet<NodeId>,
        litmap: &HashMap<u64, Lit>,
    ) -> Result<()> {
        // Invariants for the stack, nodes
        // - are not in done
        // - are not in merged
        let mut stack = Vec::new();

        // Making sure invariants are satisfied
        let id = node.borrow().get_id();
        if done.contains(&id) {
            return Ok(());
        }
        stack.push(node);

        while let Some(node) = stack.pop() {
            let id = node.borrow().get_id();

            done.insert(id);
            cnf.add_clauses_node(&*node.borrow(), litmap)?;

            // Time to add potential fanins
            match &*node.borrow() {
                // Interested in and gates only
                AigNode::And { fanin0, fanin1, .. } => {
                    for fanin in [fanin0, fanin1] {
                        let fanin_id = fanin.get_node_id();
                        // Has the node been already handled?
                        if !done.contains(&fanin_id) {
                            stack.push(fanin.get_node());
                        }
                    }
                }
                _ => (),
            };
        }

        Ok(())
    }

    /// Generates one modular SAT query to try to prove two internal signals of the AIGs are equivalent.
    /// Signals are described by a node id and a complement flag.
    ///
    /// You can then give the resulting CNF to a SAT solver.
    ///
    /// If the SAT solver returns UNSAT, then nodes are equivalent.
    /// Don't forget to merge them using [`Miter::merge`].
    pub fn extract_cnf_node(
        &mut self,
        node_a: NodeId,
        compl_a: bool,
        node_b: NodeId,
        compl_b: bool,
    ) -> Result<Cnf> {
        let mut cnf = Cnf::new();

        // Generating clauses from a
        let mut done_a = HashSet::new();
        self.extract_cnf_from(
            self.a
                .get_node(node_a)
                .ok_or(AigError::NodeDoesNotExist(node_a))?,
            &mut cnf,
            &mut done_a,
            &self.litmap_a,
        )?;

        // Generating clauses from b
        let mut done_b = HashSet::new();
        self.extract_cnf_from(
            self.b
                .get_node(node_b)
                .ok_or(AigError::NodeDoesNotExist(node_b))?,
            &mut cnf,
            &mut done_b,
            &self.litmap_b,
        )?;

        // Generating final clauses
        let lit_a = *self
            .litmap_a
            .get(&node_a)
            .ok_or(MiterError::UnmappedNodeToLit(node_a))?;
        let lit_b = *self
            .litmap_b
            .get(&node_b)
            .ok_or(MiterError::UnmappedNodeToLit(node_b))?;
        cnf.add_xor_whose_output_is_true(
            if compl_a { !lit_a } else { lit_a },
            if compl_b { !lit_b } else { lit_b },
        );

        Ok(cnf)
    }

    /// Generates one monolithic SAT query to try to prove the AIGs are equivalent.
    /// You can then give the resulting CNF to a SAT solver.
    ///
    /// If the SAT solver returns UNSAT, then the AIGs are indeed equivalent.
    ///
    /// This is the naive implementation of combinational equivalence checking.
    /// Note that it might also just take too much time on large circuits,
    /// because the generated SAT query is way too large for SAT solvers.
    pub fn extract_cnf(&mut self) -> Result<Cnf> {
        let mut cnf = Cnf::new();

        // Generating clauses from a
        let mut done_a = HashSet::new();
        for output in self.a.get_outputs() {
            self.extract_cnf_from(output.get_node(), &mut cnf, &mut done_a, &self.litmap_a)?;
        }

        // Generating clauses from b
        let mut done_b = HashSet::new();
        for output in self.b.get_outputs() {
            self.extract_cnf_from(output.get_node(), &mut cnf, &mut done_b, &self.litmap_b)?;
        }

        // Generating final clauses
        let mut xor_lits = Vec::new();
        // Clauses for real outputs
        let outputs_map = self.outputs_map.clone();
        for ((id_a, compl_a), (id_b, compl_b)) in outputs_map {
            let z = self.fresh_lit();
            let a = *self
                .litmap_a
                .get(&id_a)
                .ok_or(MiterError::UnmappedNodeToLit(id_a))?;
            let b = *self
                .litmap_b
                .get(&id_b)
                .ok_or(MiterError::UnmappedNodeToLit(id_b))?;
            cnf.add_xor(
                if compl_a { !a } else { a },
                if compl_b { !b } else { b },
                z,
            );
            xor_lits.push(z);
        }
        // Clauses for pseudo-outputs (ie latches)
        for id in self.a.get_latches_id() {
            let latch_a = self.a.get_node(id).ok_or(AigError::NodeDoesNotExist(id))?;
            let latch_b = self.b.get_node(id).ok_or(AigError::NodeDoesNotExist(id))?;

            let fanin_a = latch_a.borrow().get_fanins()[0].clone();
            let fanin_b = latch_b.borrow().get_fanins()[0].clone();
            let z = self.fresh_lit();

            cnf.add_xor_pseudo_output(fanin_a, &self.litmap_a, fanin_b, &self.litmap_b, z)?;

            xor_lits.push(z);
        }

        cnf.add_or_whose_output_is_true(xor_lits);

        Ok(cnf)
    }

    /// **WARNING**
    ///
    /// This function is dangerous (and powerful).
    /// If you have proven ~yourself valuable~ that `node_a` and `node_b` are equivalent,
    /// then you can simplify the miter by merging `node_a` to `node_b` using this function.
    ///
    /// It is public mostly to allow *structural hashing* (also known as *strashing*) external implementations.
    /// Or other optimizations when trying to prove equivalence between AIGs.
    ///
    /// For more information on strashing, check the following paper:
    /// FRAIGs: A Unifying Representation for Logic Synthesis and Verification
    /// by Alan Mishchenko, Satrajit Chatterjee, Roland Jiang, Robert Brayton.
    pub fn merge(&mut self, node_a: NodeId, node_b: NodeId, complement: bool) -> Result<()> {
        // If nodes are false, they do not have a mapped literal.
        // False nodes have already been merged
        if node_a == 0 && node_b == 0 {
            return Ok(());
        } else if node_a == 0 || node_b == 0 {
            return Err(AigError::InvalidState(format!(
                "trying to merge node false with non-false node: id_a = {}, id_b = {} --- unsupported feature for now",
                node_a, node_b
            )));
        }

        let lit_b = *self
            .litmap_b
            .get(&node_b)
            .ok_or(MiterError::UnmappedNodeToLit(node_b))?;
        self.litmap_a
            .insert(node_a, if complement { !lit_b } else { lit_b });
        self.merged.insert((node_a, node_b, complement));
        self.merged_a.insert(node_a);
        Ok(())
    }

    /// Call this function to know wether two nodes can be merged without using a CNF.
    /// This checks if they indeed have the same logic functions.
    ///
    /// Internally, we keep track of all equivalent nodes that have been merged before.
    ///
    /// Behavior is as follows:
    /// - if the two nodes are false, they can be merged
    /// - if the two nodes are the same input, they can be merged
    /// - if the two nodes are latches with the same id they can be merged.
    ///   Note that we don't care about their init values nor their next state.
    ///   Indeed, here merging them allow us to consider as pseudo inputs.
    ///   Their next state will be added as pseudo outputs to be checked when calling [`Miter::extract_cnf`].
    /// - if the two nodes are and gates, we check if they have the same output function,
    ///   regardless of their fanins order for example. We also deal with complemented equivalence.
    ///   For example, a = b ^ c and a' = c' ^ not(b') are equivalent if b is equivalent to not(b')
    ///   and c is equivalent to c'.
    ///
    /// Unfortunately, it is not possible to check wether two nodes have complemented logic functions
    /// (the functions are the negation of each other).
    ///
    /// Also that constant signal propagation is not supported for now.
    /// So an `AigNode::False`, and an `AigNode::And` with one fanin set to false,
    /// are not considered mergeable.
    pub fn mergeable(&self, node_a: NodeId, node_b: NodeId) -> Result<bool> {
        let na = self
            .a
            .get_node(node_a)
            .ok_or(AigError::NodeDoesNotExist(node_a))?;
        let nb = self
            .b
            .get_node(node_b)
            .ok_or(AigError::NodeDoesNotExist(node_b))?;
        match (&*na.borrow(), &*nb.borrow()) {
            (
                AigNode::And {
                    fanin0: fanin0_a,
                    fanin1: fanin1_a,
                    ..
                },
                AigNode::And {
                    fanin0: fanin0_b,
                    fanin1: fanin1_b,
                    ..
                },
            ) => {
                let id0a = fanin0_a.get_node_id();
                let c0a = fanin0_a.get_complement();
                let id1a = fanin1_a.get_node_id();
                let c1a = fanin1_a.get_complement();
                let id0b = fanin0_b.get_node_id();
                let c0b = fanin0_b.get_complement();
                let id1b = fanin1_b.get_node_id();
                let c1b = fanin1_b.get_complement();

                // We expect the boolean functions to be the same:
                // either f0a <=> f0b && f1a <=> f1b
                // or f0a <=> f1b && f1a <=> f0b
                Ok((self.merged.contains(&(id0a, id0b, c0a ^ c0b))
                    && self.merged.contains(&(id1a, id1b, c1a ^ c1b)))
                    || (self.merged.contains(&(id0a, id1b, c0a ^ c1b))
                        && self.merged.contains(&(id1a, id0b, c1a ^ c0b))))
            }
            // Ignoring init values for latches and next state, they are pseudo inputs.
            (AigNode::Latch { id: id_a, .. }, AigNode::Latch { id: id_b, .. }) => {
                Ok(*id_a == *id_b)
            }
            (AigNode::Input(id_a), AigNode::Input(id_b)) => Ok(*id_a == *id_b),
            (AigNode::False, AigNode::False) => Ok(true),
            // Some others merge could be considered, but let's not consider them for now.
            // Example: constant signal propagation
            _ => Ok(false),
        }
    }

    /// Returns true iff all outputs have been merged ie circuits are equivalent.
    ///
    /// **WARNING**  
    /// For now, consider only real outputs and not pseudo outputs induced by latches. TODO?
    pub fn are_outputs_merged(&self) -> bool {
        for out in self.a.get_outputs() {
            if !self.merged_a.contains(&out.get_node_id()) {
                return false;
            }
        }
        return true;
    }
}

#[cfg(test)]
mod test {
    use crate::AigEdge;

    use super::*;

    #[test]
    fn new_miter_test() {
        let mut a = Aig::new();
        let a1 = a.add_node(AigNode::Input(1)).unwrap();
        let mut b = Aig::new();
        let b2 = b.add_node(AigNode::Input(2)).unwrap();
        assert!(Miter::new(&a, &b, HashMap::new()).is_err());

        let a2 = a.add_node(AigNode::Input(2)).unwrap();
        b.add_node(AigNode::Input(1)).unwrap(); // not using b1
        a.add_node(AigNode::and(
            3,
            AigEdge::new(a1.clone(), false),
            AigEdge::new(a2.clone(), false),
        ))
        .unwrap();
        let b0 = b.add_node(AigNode::False).unwrap();
        b.add_node(AigNode::and(
            3,
            AigEdge::new(b0.clone(), false),
            AigEdge::new(b2.clone(), false),
        ))
        .unwrap();
        a.add_output(3, true).unwrap();
        let mut outputs = HashMap::new();
        outputs.insert((3, true), (3, false));
        assert!(Miter::new(&a, &b, outputs.clone()).is_err());
        outputs.clear();

        b.add_output(3, false).unwrap();
        outputs.insert((3, true), (3, true));
        assert!(Miter::new(&a, &b, outputs.clone()).is_err());

        outputs.clear();
        outputs.insert((3, true), (3, false));
        assert!(Miter::new(&a, &b, outputs.clone()).is_ok());

        // b1 is not used, but inputs are not pruned
        // a and b still will have same inputs set
        b.update();
        assert!(Miter::new(&a, &b, outputs.clone()).is_ok());
    }

    #[test]
    fn mergeable_test() {
        let mut a = Aig::new();
        let a1 = a.add_node(AigNode::Input(1)).unwrap();
        let a2 = a.add_node(AigNode::Input(2)).unwrap();
        let a3 = a
            .add_node(AigNode::and(
                3,
                AigEdge::new(a1.clone(), false),
                AigEdge::new(a2.clone(), false),
            ))
            .unwrap();
        let _a4 = a.add_node(AigNode::latch(4, AigEdge::new(a3.clone(), true), None));
        a.add_output(4, false).unwrap();

        let mut b = Aig::new();
        let b1 = b.add_node(AigNode::Input(1)).unwrap();
        let b2 = b.add_node(AigNode::Input(2)).unwrap();
        let b3 = b
            .add_node(AigNode::and(
                3,
                AigEdge::new(b2.clone(), false),
                AigEdge::new(b1.clone(), false),
            ))
            .unwrap();
        let _b4 = b.add_node(AigNode::latch(
            4,
            AigEdge::new(b3.clone(), false), // next do not matter
            Some(true),                      // init value does not matter
        ));
        b.add_output(4, false).unwrap();

        let outputs = HashMap::from([((4, false), (4, false))]);
        let mut miter = Miter::new(&a, &b, outputs).unwrap();

        assert!(!miter.mergeable(1, 2).unwrap());
        assert!(!miter.mergeable(2, 1).unwrap());
        assert!(!miter.mergeable(1, 2).unwrap());
        assert!(!miter.mergeable(3, 3).unwrap()); // We haven't proven equivalence of inputs yet
        assert!(miter.mergeable(4, 4).unwrap());

        assert!(miter.mergeable(1, 1).unwrap());
        assert!(miter.mergeable(2, 2).unwrap());
        miter.merge(1, 1, false).unwrap();
        miter.merge(2, 2, false).unwrap();
        assert!(miter.mergeable(3, 3).unwrap());
        miter.merge(3, 3, false).unwrap();
        assert!(miter.mergeable(4, 4).unwrap()); // init values do not matter
        miter.merge(4, 4, false).unwrap();
    }
}
