use std::{
    collections::{HashMap, HashSet},
    num::TryFromIntError,
};

use thiserror::Error;

use crate::{
    Aig, AigError, AigNode, NodeId, Result,
    cnf::{Cnf, Lit},
    dfs::Dfs,
};

/// Error returned when an operation related to the miter fails
/// (creation, combinational equivalence checking, ...).
#[derive(Debug, Error)]
pub enum MiterError {
    /// Creation of a miter failed because the two AIGs have different inputs.
    /// We are just checking for the inputs id, they should correspond.
    #[error("AIGs have different inputs : {0:?} vs {1:?}")]
    MiterDifferentInputs(HashSet<NodeId>, HashSet<NodeId>),

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
    outputs_map: HashMap<NodeId, NodeId>,
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

impl Miter {
    /// Create miter between two AIGs.
    ///
    /// This will fail if:
    /// - the given AIGs have different inputs (ie inputs with different ids)
    /// - or they have different outputs.
    ///
    /// To check the latter, the `outputs_map` is used:
    /// every output of `a` must be mapped to an output of `b`.
    pub fn new(a: &Aig, b: &Aig, outputs_map: HashMap<NodeId, NodeId>) -> Result<Self> {
        // Checking inputs
        if a.get_inputs_id() != b.get_inputs_id() {
            return Err(
                MiterError::MiterDifferentInputs(a.get_inputs_id(), b.get_inputs_id()).into(),
            );
        }

        // Checking outputs of a are registered
        if a.get_outputs_id() != outputs_map.iter().map(|(oa, _)| *oa).collect() {
            return Err(MiterError::MiterDifferentOutputs.into());
        }

        // Checking outputs of b are registered
        if b.get_outputs_id() != outputs_map.iter().map(|(_, ob)| *ob).collect() {
            return Err(MiterError::MiterDifferentOutputs.into());
        }

        // Finding the first usable literal (ie not used by any input)
        let mut next_lit = 1;
        while a.get_inputs_id().contains(&(next_lit as u64)) {
            next_lit += 1;
        }

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
                AigNode::And { id, .. } => {
                    let lit = self.fresh_lit();
                    self.litmap_a.insert(id, lit)
                }
                _ => None,
                // TODO SUPPORT LATCHES
            };
        }

        // Same for b
        let mut dfs = Dfs::from_outputs(&self.b);
        while let Some(n) = dfs.next(&self.b) {
            match *n.borrow() {
                AigNode::Input(id) => self
                    .litmap_b
                    .insert(id, Lit::try_from(id).map_err(MiterError::from)?),
                AigNode::And { id, .. } => {
                    let lit = self.fresh_lit();
                    self.litmap_b.insert(id, lit)
                }
                _ => None,
                // TODO SUPPORT LATCHES
            };
        }

        Ok(())
    }

    /// Returns a yet unused SAT literal.
    pub fn fresh_lit(&mut self) -> Lit {
        let lit = self.next_lit.into();
        self.next_lit += 1;
        // Making sure we're not using a SAT literal used by any input
        while self.a.get_inputs_id().contains(&(self.next_lit as u64)) {
            self.next_lit += 1;
        }
        lit
    }

    /// Tries to prove that `node_a` and `node_b` (resp. from `a` and `b`) are equivalent.
    /// - if it succeeds, nodes are merged internally for future proofs
    /// - else, an error explaining why the nodes could not be merged is returned.
    ///
    /// TODO : RELY ON A SAT SOLVER
    pub fn try_prove_eq_node(&mut self, node_a: NodeId, node_b: NodeId) -> Result<()> {
        let mut cnf = Cnf::new();

        // Generating clauses from a
        let mut dfs = Dfs::from_node(
            self.a
                .get_node(node_a)
                .ok_or(AigError::NodeDoesNotExist(node_a))?,
        );
        while let Some(n) = dfs.next(&self.a) {
            if !self.merged.contains(&n.borrow().get_id()) {
                cnf.add_clauses_node(&*n.borrow(), &self.litmap_a)?;
            }
        }

        // Generating clauses from b
        let mut dfs = Dfs::from_node(
            self.b
                .get_node(node_b)
                .ok_or(AigError::NodeDoesNotExist(node_b))?,
        );
        while let Some(n) = dfs.next(&self.b) {
            cnf.add_clauses_node(&*n.borrow(), &self.litmap_b)?;
        }

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

        // TODO
        // prove the CNF is UNSAT using a SAT solver

        // Nodes are equivalent, we merge node_a to node_b
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

    /// Tries to prove that the two AIGs are equivalent by generating one monolithic SAT query.
    /// - if it succeeds, the function simply returns Ok(())
    /// - else, it fails with an error indicating what went wrong.
    ///
    /// This is the naive implementation of combinational equivalence checking.
    /// Note that it might also just take too much time on large circuits,
    /// because the generated SAT query is too large for SAT solvers.
    pub fn try_prove_eq(&mut self) -> Result<()> {
        let mut cnf = Cnf::new();

        // Generating clauses from a
        let mut dfs = Dfs::from_outputs(&self.a);
        while let Some(n) = dfs.next(&self.a) {
            if !self.merged.contains(&n.borrow().get_id()) {
                cnf.add_clauses_node(&*n.borrow(), &self.litmap_a)?;
            }
        }

        // Generating clauses from b
        let mut dfs = Dfs::from_outputs(&self.b);
        while let Some(n) = dfs.next(&self.b) {
            cnf.add_clauses_node(&*n.borrow(), &self.litmap_b)?;
        }

        // Generating final clauses
        let mut xor_lits = Vec::new();
        let outputs_map = self.outputs_map.clone();
        for (oa, ob) in outputs_map {
            let z = self.fresh_lit();
            cnf.add_xor(
                *self
                    .litmap_a
                    .get(&oa)
                    .ok_or(MiterError::UnmappedNodeToLit(oa))?,
                *self
                    .litmap_b
                    .get(&ob)
                    .ok_or(MiterError::UnmappedNodeToLit(ob))?,
                z,
            );
            xor_lits.push(z);
        }
        cnf.add_or_whose_output_is_true(xor_lits);

        // TODO SAT SOLVER

        Ok(())
    }
}
