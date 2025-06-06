//! Generate miters between two circuits and the resulting SAT formula as a CNF.
//!
//! To prove combinational equivalence checking (CEC) between two circuits `a` and `b`:
//! - generate miter from `a` and `b` with TODO
//! - extract CNF from the miter with TODO
//! - check that the CNF is **UNSAT** with a SAT solver.
//!
//! If the resulting CNF is SAT, it means that the two circuits are **not equivalent**.

use std::{num::TryFromIntError, ops::Not};

use crate::{AigEdge, AigNode, NodeId};

/// A SAT literal.
///
/// Note that all AIG nodes do not correspond to a SAT literal.
/// For example, `False` node do not map to any literal, but rather is omitted
/// as false boolean variables can be removed from a clause without changing the problem.
/// Clauses that contain a true boolean variable (ie a complemented edge to `False` node)
/// are obviously true and don't need to be emitted.
///
/// These cases are handled by the internal `LitRes` data structure.
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

#[derive(Debug, Clone, Copy)]
enum LitRes {
    False,
    True,
    Lit(Lit),
}

impl Not for LitRes {
    type Output = Self;

    fn not(self) -> Self::Output {
        match self {
            LitRes::False => LitRes::True,
            LitRes::True => LitRes::False,
            LitRes::Lit(lit) => LitRes::Lit(!lit),
        }
    }
}

impl From<Lit> for LitRes {
    fn from(value: Lit) -> Self {
        LitRes::Lit(value)
    }
}

impl TryFrom<&AigNode> for LitRes {
    type Error = TryFromIntError;

    fn try_from(value: &AigNode) -> Result<Self, Self::Error> {
        match value {
            AigNode::False => Ok(LitRes::False),
            node => Ok(LitRes::Lit(Lit::try_from(node.get_id())?)),
        }
    }
}

/// A SAT clause.
pub struct Clause(Vec<Lit>);

impl Clause {
    /// A new empty clause.
    pub fn new() -> Self {
        Clause(Vec::new())
    }

    /// Returns the true SAT clause once we got rid of `True` and `False` literals.
    /// If there is a `True`, then the Clause is obviously satisfied, so we return None.
    /// `False` literals are omitted, and real literals are added to the clause.
    /// If the clause is empty (lits were only `False`), None is returned.
    fn from_lit_res(lits: Vec<LitRes>) -> Option<Clause> {
        let mut literals = Vec::new();

        for lit_res in lits {
            match lit_res {
                LitRes::True => return None,
                LitRes::False => (),
                LitRes::Lit(lit) => literals.push(lit),
            }
        }

        if literals.is_empty() {
            None
        } else {
            Some(Clause(literals))
        }
    }
}

impl From<Vec<Lit>> for Clause {
    fn from(value: Vec<Lit>) -> Self {
        Clause(value)
    }
}

/// A SAT CNF that can be passed to a SAT solver.
///
/// It provides useful methods to create a miter such as [`add_xor`]
/// and [`add_or_whose_output_is_true`], which can be used to finish the construction of the miter.
///
/// [`add_xor`]: Cnf::add_xor
/// [`add_or_whose_output_is_true`]: Cnf::add_or_whose_output_is_true
pub struct Cnf(Vec<Clause>);

impl Cnf {
    /// A new empty CNF.
    pub fn new() -> Self {
        Cnf(Vec::new())
    }

    /// Add the given clause to the CNF.
    pub fn add_clause(&mut self, clause: Clause) {
        self.0.push(clause);
    }

    /// Add the given clause to the CNF, else does nothing.
    pub fn add_clause_if(&mut self, clause: Option<Clause>) {
        if let Some(c) = clause {
            self.add_clause(c);
        }
    }

    /// Add clauses induced by the node.
    fn add_clauses(&mut self, node: &AigNode) {
        match node {
            AigNode::And { id, fanin0, fanin1 } => {
                let a = fanin0.get_literal_res();
                let b = fanin1.get_literal_res();
                let z = LitRes::from(Lit::try_from(*id).unwrap());

                self.add_clause_if(Clause::from_lit_res(vec![a, !z]));
                self.add_clause_if(Clause::from_lit_res(vec![b, !z]));
                self.add_clause_if(Clause::from_lit_res(vec![!a, !b, z]));
            }
            // The other nodes do not induce any clause, they only generate literals
            // TODO : what about latches (depending on their initialization status)
            _ => (),
        }
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
    fn get_literal_res(&self) -> LitRes {
        let lit = LitRes::try_from(&*self.node.borrow()).unwrap();
        if self.complement { !lit } else { lit }
    }
}
