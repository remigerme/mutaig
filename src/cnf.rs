//! Extract a SAT formula from a previously generated [`Miter`].
//!
//! To prove combinational equivalence checking (CEC) between two circuits `a` and `b`:
//! - generate miter from `a` and `b` with [`Miter::new`]
//! - extract CNF from the miter with methods of [`Cnf`]
//! - check that the CNF is **UNSAT** with a SAT solver.
//!
//! If the resulting CNF is SAT, it means that the two circuits are **not equivalent**.
//!
//! The core methods to extract a SAT formula are:
//! - [`Miter::extract_cnf_node`] if you want to prove the equivalence of two internal nodes.
//!   Once the nodes are proven equivalent, merge them using [`Miter::merge`].
//! - [`Miter::extract_cnf`] if you wat to prove the equivalence of the whole circuits.
//!
//! Note that you can also try to merge obviously equivalent internal nodes with
//! [`Miter::mergeable`] then [`Miter::merge`].
//!
//! [`Miter`]: crate::miter::Miter
//! [`Miter::new`]: crate::miter::Miter::new
//! [`Miter::extract_cnf_node`]: crate::miter::Miter::extract_cnf_node
//! [`Miter::extract_cnf`]: crate::miter::Miter::extract_cnf
//! [`Miter::merge`]: crate::miter::Miter::merge
//! [`Miter::mergeable`]: crate::miter::Miter::mergeable

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

impl Lit {
    pub fn get_idx(&self) -> i64 {
        self.0
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

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn get_lits(&self) -> Vec<Lit> {
        self.0.clone()
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

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn get_clauses(&self) -> Vec<Clause> {
        self.0.clone()
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
    ///
    /// Latches outputs are considered as pseudo-inputs, and their inputs as pseudo-outputs.
    pub fn add_clauses_node(
        &mut self,
        node: &AigNode,
        litmap: &HashMap<NodeId, Lit>,
    ) -> Result<()> {
        match node {
            AigNode::And {
                id, fanin0, fanin1, ..
            } => {
                let a = fanin0.get_literal_res(litmap)?;
                let b = fanin1.get_literal_res(litmap)?;
                let z = LitRes::from(*litmap.get(id).ok_or(MiterError::UnmappedNodeToLit(*id))?);

                self.add_clause_if(Clause::from_lit_res(vec![a, !z]));
                self.add_clause_if(Clause::from_lit_res(vec![b, !z]));
                self.add_clause_if(Clause::from_lit_res(vec![!a, !b, z]));
            }
            // The other nodes do not induce any clause, they only generate literals
            // Latches are treated as pseudo-outputs/inputs see in miter.
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
    /// If you are creating a miter, you should create z with the [`fresh_lit()`] method.
    ///
    /// [`fresh_lit()`]: crate::miter::Miter::fresh_lit
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

    /// Add a xor between the two pseudo outputs a and b.
    /// They are the fanins of some latches which should be equivalent.
    pub fn add_xor_pseudo_output(
        &mut self,
        a: AigEdge,
        litmap_a: &HashMap<NodeId, Lit>,
        b: AigEdge,
        litmap_b: &HashMap<NodeId, Lit>,
        z: Lit,
    ) -> Result<()> {
        let a = a.get_literal_res(litmap_a)?;
        let b = b.get_literal_res(litmap_b)?;
        let z = LitRes::from(z);

        self.add_clause_if(Clause::from_lit_res(vec![a, b, !z]));
        self.add_clause_if(Clause::from_lit_res(vec![a, !b, z]));
        self.add_clause_if(Clause::from_lit_res(vec![!a, b, z]));
        self.add_clause_if(Clause::from_lit_res(vec![!a, !b, !z]));

        Ok(())
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

    /// Returns a string using DIMACS format to represent CNF.
    pub fn to_dimacs(&self) -> String {
        let var_max = self
            .0
            .iter()
            .flat_map(|clause| &clause.0)
            .map(|lit| lit.0.abs())
            .max()
            .unwrap_or(0);

        // Pre-calculate approximate size to reduce allocations
        let estimated_size = 30 + self.0.len() * 20; // rough estimate
        let mut dimacs = String::with_capacity(estimated_size);

        // Add header
        dimacs.push_str("p cnf ");
        dimacs.push_str(&var_max.to_string());
        dimacs.push(' ');
        dimacs.push_str(&self.0.len().to_string());
        dimacs.push('\n');

        // Add clauses
        for clause in &self.0 {
            for Lit(val) in &clause.0 {
                dimacs.push_str(&val.to_string());
                dimacs.push(' ');
            }
            dimacs.push('0');
            dimacs.push('\n');
        }

        dimacs
    }
}

impl AigEdge {
    fn get_literal_res(&self, litmap: &HashMap<NodeId, Lit>) -> Result<LitRes> {
        let lit = if *self.get_node().borrow() == AigNode::False {
            LitRes::False
        } else {
            let id = self.get_node().borrow().get_id();
            LitRes::from(*litmap.get(&id).ok_or(MiterError::UnmappedNodeToLit(id))?)
        };
        Ok(if self.get_complement() { !lit } else { lit })
    }
}

#[cfg(test)]
mod test {
    use std::{cell::RefCell, rc::Rc};

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

    #[test]
    fn empty_to_dimacs_test() {
        let cnf = Cnf::new();
        assert_eq!(cnf.to_dimacs(), "p cnf 0 0\n");
    }

    #[test]
    fn to_dimacs_test() {
        let mut cnf = Cnf::new();
        cnf.add_clause(Clause::from(vec![Lit(1)]));
        cnf.add_clause(Clause::from(vec![Lit(-1), Lit(2)]));
        assert_eq!(cnf.to_dimacs(), "p cnf 2 2\n1 0\n-1 2 0\n");

        cnf.add_clause(Clause::from(vec![Lit(5), Lit(-4), Lit(2)]));
        assert_eq!(cnf.to_dimacs(), "p cnf 5 3\n1 0\n-1 2 0\n5 -4 2 0\n");

        cnf.add_clause(Clause::from(vec![Lit(-6)]));
        assert_eq!(cnf.to_dimacs(), "p cnf 6 4\n1 0\n-1 2 0\n5 -4 2 0\n-6 0\n")
    }

    #[test]
    fn get_literal_res_test() {
        let nf = Rc::new(RefCell::new(AigNode::False));
        let mut litmap = HashMap::new();
        assert_eq!(
            AigEdge::new(nf.clone(), false)
                .get_literal_res(&litmap)
                .unwrap(),
            LitRes::False
        );
        assert_eq!(
            AigEdge::new(nf.clone(), true)
                .get_literal_res(&litmap)
                .unwrap(),
            LitRes::True
        );
        let i1 = Rc::new(RefCell::new(AigNode::Input(1)));
        litmap.insert(1, Lit::from(1));
        assert_eq!(
            AigEdge::new(i1.clone(), false)
                .get_literal_res(&litmap)
                .unwrap(),
            LitRes::Lit(Lit::from(1))
        );
        assert_eq!(
            AigEdge::new(i1.clone(), true)
                .get_literal_res(&litmap)
                .unwrap(),
            LitRes::Lit(Lit::from(-1))
        );
    }
}
