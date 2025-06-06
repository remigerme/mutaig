//! Generate miters between two circuits and the resulting SAT formula as a CNF.
//!
//! To prove combinational equivalence checking (CEC) between two circuits `a` and `b`:
//! - generate miter from `a` and `b` with TODO
//! - extract CNF from the miter with TODO
//! - check that the CNF is *UNSAT* with a SAT solver.
//!
//! If the resulting CNF is SAT, it means that the two circuits are *not equivalent*.

use std::{num::TryFromIntError, ops::Not};

use crate::{Aig, AigEdge, AigNode, NodeId};

/// A SAT literal.
#[derive(Debug, Clone, Copy)]
pub struct Lit(i64);

impl Not for Lit {
    type Output = Self;

    fn not(self) -> Self::Output {
        Lit(-self.0)
    }
}

impl TryFrom<NodeId> for Lit {
    type Error = TryFromIntError;

    fn try_from(value: NodeId) -> Result<Self, Self::Error> {
        Ok(Lit(i64::try_from(value)?))
    }
}

/// A SAT clause.
pub struct Clause(Vec<Lit>);

impl From<Vec<Lit>> for Clause {
    fn from(value: Vec<Lit>) -> Self {
        Clause(value)
    }
}

/// A SAT CNF that can be passed to a SAT solver.
///
/// It provides useful methods to create a miter such as [`add_xor`]
/// and [`add_or_whose_output_is_one`], which can be used to finish the construction of the miter.
///
/// [`add_xor`]: Cnf::add_xor
/// [`add_or_whose_output_is_one`]: Cnf::add_or_whose_output_is_one
pub struct Cnf(Vec<Clause>);

impl Cnf {
    /// Add the given clause to the CNF.
    pub fn add_clause(&mut self, clause: Clause) {
        self.0.push(clause);
    }

    /// Add clauses that encode `z = XOR(a, b)`
    ///
    /// - a is the literal associated with the `fanin0`
    /// - b is the literal associated with the `fanin1`
    /// - z is the literal of the XOR gate itself
    ///
    /// If you are creating a miter, you should create z with TODO
    pub fn add_xor(&mut self, a: Lit, b: Lit, z: Lit) {
        self.add_clause(Clause::from(vec![a, b, !z]));
        self.add_clause(Clause::from(vec![a, !b, z]));
        self.add_clause(Clause::from(vec![!a, b, z]));
        self.add_clause(Clause::from(vec![!a, !b, !z]));
    }

    /// Add clauses that encode `z = OR(inputs)` while assuming z is true.
    ///
    /// This is the last node of the miter to compare two circuits.
    /// We assume that the output is true, which means there are at least a pair of outputs
    /// which differ for the same set of inputs:
    /// - if this is possible (ie the CNF is SAT), then circuits are not equivalent
    /// - if the CNF is UNSAT, then circuits are equivalent.
    pub fn add_or_whose_output_is_true(&mut self, inputs: Vec<Lit>) {
        self.add_clause(Clause::from(inputs));
    }
}

impl AigEdge {
    fn get_literal(&self) -> Lit {
        let lit = Lit::try_from(self.node.borrow().get_id()).unwrap();
        if self.complement { !lit } else { lit }
    }
}

impl AigNode {
    fn add_clauses(&self, cnf: &mut Cnf) {
        match self {
            AigNode::And { id, fanin0, fanin1 } => {
                let a = fanin0.get_literal();
                let b = fanin1.get_literal();
                let z = Lit::try_from(*id).unwrap();
                cnf.add_clause(Clause::from(vec![a, !z]));
                cnf.add_clause(Clause::from(vec![b, !z]));
                cnf.add_clause(Clause::from(vec![!a, !b, z]));
            }
            // The other nodes do not induce any clause, they only generate literals
            // TODO : what about latches (depending on their initialization status)
            _ => (),
        }
    }
}

impl Aig {}
