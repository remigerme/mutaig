//! Generate miters between two circuits and the resulting SAT formula as a CNF.
//!
//! To prove combinational equivalence checking (CEC) between two circuits `a` and `b`:
//! - generate miter from `a` and `b` with [`Miter::new`]
//! - extract CNF from the miter with methods of [`Cnf`]
//! - check that the CNF is **UNSAT** with a SAT solver.
//!
//! If the resulting CNF is SAT, it means that the two circuits are **not equivalent**.
//!
//! This is already implemented in [`Miter::try_prove_eq_node`] and [`Miter::try_prove_eq`].
//!
//! [`Miter::new`]: crate::miter::Miter::new
//! [`Cnf`]: Cnf
//! [`Miter::try_prove_eq_node`]: crate::miter::Miter::try_prove_eq_node
//! [`Miter::try_prove_eq`]: crate::miter::Miter::try_prove_eq

use std::{collections::HashMap, num::TryFromIntError, ops::Not};

use crate::{AigEdge, AigNode, NodeId, Result, miter::MiterError};

/// A SAT literal.
///
/// Note that all AIG nodes do not correspond to a SAT literal.
/// For example, [`AigNode::False`] node do not map to any literal, but rather is omitted
/// as false boolean variables can be removed from a clause without changing the problem.
/// Clauses that contain a true boolean variable (ie a complemented edge to [`AigNode::False`] node)
/// are obviously true and don't need to be emitted.
///
/// These cases are handled by the internal `LitRes` data structure.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Lit(i64);

impl Not for Lit {
    type Output = Self;

    fn not(self) -> Self::Output {
        Lit(-self.0)
    }
}

impl From<i64> for Lit {
    fn from(value: i64) -> Self {
        if value == 0 {
            panic!("Tried to create a Lit from 0. 0 is not a valid literal in DIMACS format.");
        }
        Lit(value)
    }
}

impl TryFrom<NodeId> for Lit {
    type Error = TryFromIntError;

    fn try_from(value: NodeId) -> std::result::Result<Self, Self::Error> {
        Ok(Lit::from(i64::try_from(value)?))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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

/// A SAT clause.
#[derive(Debug, Clone, PartialEq, Eq)]
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
/// It provides useful methods to create a miter such as [`add_xor`], [`add_xor_whose_output_is_true`],
/// and [`add_or_whose_output_is_true`], which can be used to finish the construction of the miter.
///
/// [`add_xor`]: Cnf::add_xor
/// [`add_xor_whose_output_is_true`]: Cnf::add_xor_whose_output_is_true
/// [`add_or_whose_output_is_true`]: Cnf::add_or_whose_output_is_true
#[derive(Debug, Clone, PartialEq, Eq)]
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
    pub fn add_clauses_node(
        &mut self,
        node: &AigNode,
        litmap: &HashMap<NodeId, Lit>,
    ) -> Result<()> {
        match node {
            AigNode::And { id, fanin0, fanin1 } => {
                let a = fanin0.get_literal_res(litmap)?;
                let b = fanin1.get_literal_res(litmap)?;
                let z = LitRes::from(*litmap.get(id).ok_or(MiterError::UnmappedNodeToLit(*id))?);

                self.add_clause_if(Clause::from_lit_res(vec![a, !z]));
                self.add_clause_if(Clause::from_lit_res(vec![b, !z]));
                self.add_clause_if(Clause::from_lit_res(vec![!a, !b, z]));
            }
            // The other nodes do not induce any clause, they only generate literals
            // TODO : what about latches (depending on their initialization status)
            _ => (),
        }
        Ok(())
    }

    /// Add clauses that encode `z = XOR(a, b)`.
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

    /// Add clauses that encode `XOR(a, b) = true`.
    ///
    /// This is the function to use if you want to compare two internal nodes of the miter for AIGs `a` and `b`:
    /// - a is the literal associated with the node from aig `a`
    /// - b is the literal associated with the node from aig `b`
    pub fn add_xor_whose_output_is_true(&mut self, a: Lit, b: Lit) {
        self.add_clause(Clause::from(vec![a, b]));
        self.add_clause(Clause::from(vec![!a, !b]));
    }

    /// Add clauses that encode `OR(inputs) = true`.
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
    fn get_literal_res(&self, litmap: &HashMap<NodeId, Lit>) -> Result<LitRes> {
        let lit = if *self.node.borrow() == AigNode::False {
            LitRes::False
        } else {
            let id = self.node.borrow().get_id();
            LitRes::from(*litmap.get(&id).ok_or(MiterError::UnmappedNodeToLit(id))?)
        };
        Ok(if self.complement { !lit } else { lit })
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn not_lit_test() {
        let l1 = Lit(1);
        assert_eq!(!l1, Lit(-1));
    }

    #[test]
    fn not_lit_res_test() {
        let ltrue = LitRes::True;
        let lfalse = LitRes::False;
        let l1 = LitRes::Lit(Lit(1));
        assert_eq!(!lfalse, ltrue);
        assert_eq!(!l1, LitRes::Lit(!Lit(1)));
    }

    #[test]
    fn clause_from_lit_res_test() {
        let ltrue = LitRes::True;
        let lfalse = LitRes::False;
        let l1 = Lit(1);
        let l2 = Lit(2);
        let lr1 = LitRes::Lit(l1);
        let lr2 = LitRes::Lit(l2);

        assert!(Clause::from_lit_res(vec![lfalse, lfalse]).is_none());
        assert!(Clause::from_lit_res(vec![lfalse, ltrue, lr1]).is_none());
        assert_eq!(
            Clause::from_lit_res(vec![lr1, lfalse, lr2]).unwrap(),
            Clause(vec![l1, l2])
        );
    }

    #[test]
    fn add_clause_test() {
        let l1 = Lit(1);
        let l2 = Lit(2);
        let c = Clause::from(vec![l1, l2]);

        let mut cnf = Cnf::new();

        cnf.add_clause(c.clone());
        assert_eq!(cnf.0, vec![c.clone()]);

        cnf.add_clause_if(Some(c.clone()));
        assert_eq!(cnf.0, vec![c.clone(), c.clone()]);

        cnf.add_clause_if(None);
        assert_eq!(cnf.0, vec![c.clone(), c.clone()]);
    }

    #[test]
    #[should_panic]
    fn invalid_lit_from_test() {
        _ = Lit::from(0);
    }

    #[test]
    #[should_panic]
    fn invalid_lit_tryfrom_test() {
        _ = Lit::try_from(0 as NodeId);
    }
}
