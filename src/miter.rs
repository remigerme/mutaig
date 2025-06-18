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
/// - create a new miter with [`new`]
/// - (optional) merge internal nodes that you know are equivalent using [`try_prove_eq_node`]
///   (it will incrementally simplify the search space of the generated SAT queries)
/// - then prove the two original AIGs are equivalent using [`try_prove_eq`].
///
/// [`new`]: Miter::new
/// [`try_prove_eq_node`]: Miter::try_prove_eq_node
/// [`try_prove_eq`]: Miter::try_prove_eq
pub struct Miter {
    /// The reference miter.
    a: Aig,
    /// The optimized miter.
    b: Aig,
    /// Maps outputs of `a` to outputs of `b`.
    outputs_map: HashMap<(NodeId, bool), (NodeId, bool)>,
    /// Associating a SAT literal to each node.
    /// Nodes from `a` might also refer a literal originally associated with a node of `b`.
    litmap_a: HashMap<NodeId, Lit>,
    /// Associating a SAT literal to each node.
    /// Nodes from `a` might also refer a literal originally associated with a node of `b`.
    litmap_b: HashMap<NodeId, Lit>,
    /// Keeping track of all nodes from `a` which has been merged to a node of `b`,
    /// ie nodes of `a` pointing at the same SAT literal as a node of `b`.
    merged: HashSet<NodeId>,
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
        .map(|output| (output.get_node().borrow().get_id(), output.get_complement()))
        .collect::<HashSet<(u64, bool)>>()
        != outputs_map.keys().copied().collect()
    {
        return Err(MiterError::MiterDifferentOutputs.into());
    }

    // Checking outputs of b are registered
    if b.get_outputs()
        .iter()
        .map(|output| (output.get_node().borrow().get_id(), output.get_complement()))
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
        merged: Option<&HashSet<NodeId>>,
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
        if let Some(merged_set) = merged {
            if merged_set.contains(&id) {
                return Ok(());
            }
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
                        let fanin_id = fanin.get_node().borrow().get_id();
                        // Has the node been already handled?
                        if !done.contains(&fanin_id) {
                            // Was a merged set provided? Was the node merged before?
                            if let Some(merged_set) = merged {
                                if !merged_set.contains(&fanin_id) {
                                    stack.push(fanin.get_node());
                                }
                            } else {
                                stack.push(fanin.get_node());
                            }
                        }
                    }
                }
                _ => (),
            };
        }

        Ok(())

        // Adding the
    }

    /// Generates one modular SAT query to try to prove two internal nodes of the AIGs are equivalent.
    /// You can then give the resulting CNF to a SAT solver.
    ///
    /// If the SAT solver returns UNSAT, then nodes are equivalent.
    /// Don't forget to merge them using [`Miter::merge`].
    pub fn extract_cnf_node(&mut self, node_a: NodeId, node_b: NodeId) -> Result<Cnf> {
        let mut cnf = Cnf::new();

        // Generating clauses from a
        let mut done_a = HashSet::new();
        self.extract_cnf_from(
            self.a
                .get_node(node_a)
                .ok_or(AigError::NodeDoesNotExist(node_a))?,
            &mut cnf,
            &mut done_a,
            Some(&self.merged),
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
            None,
            &self.litmap_b,
        )?;

        // Generating final clauses
        cnf.add_xor_whose_output_is_true(
            *self
                .litmap_a
                .get(&node_a)
                .ok_or(MiterError::UnmappedNodeToLit(node_a))?,
            *self
                .litmap_b
                .get(&node_b)
                .ok_or(MiterError::UnmappedNodeToLit(node_b))?,
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
            self.extract_cnf_from(
                output.get_node(),
                &mut cnf,
                &mut done_a,
                Some(&self.merged),
                &self.litmap_a,
            )?;
        }

        // Generating clauses from b
        let mut done_b = HashSet::new();
        for output in self.b.get_outputs() {
            self.extract_cnf_from(
                output.get_node(),
                &mut cnf,
                &mut done_b,
                None,
                &self.litmap_b,
            )?;
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
    pub fn merge(&mut self, node_a: NodeId, node_b: NodeId) -> Result<()> {
        self.litmap_a.insert(
            node_a,
            *self
                .litmap_b
                .get(&node_b)
                .ok_or(MiterError::UnmappedNodeToLit(node_b))?,
        );
        self.merged.insert(node_a);
        Ok(())
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
        a.add_node(AigNode::And {
            id: 3,
            fanin0: AigEdge::new(a1.clone(), false),
            fanin1: AigEdge::new(a2.clone(), false),
        })
        .unwrap();
        let b0 = b.add_node(AigNode::False).unwrap();
        b.add_node(AigNode::And {
            id: 3,
            fanin0: AigEdge::new(b0.clone(), false),
            fanin1: AigEdge::new(b2.clone(), false),
        })
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
}
