use std::collections::HashMap;

use crate::{
    Aig, AigError, NodeId, Result,
    cnf::{Cnf, Lit},
    dfs::Dfs,
};

pub struct Miter {
    a: Aig,
    b: Aig,
    litmap_a: HashMap<NodeId, Lit>,
    litmap_b: HashMap<NodeId, Lit>,
}

impl Miter {
    pub fn new(a: &Aig, b: &Aig) -> Result<Self> {
        if !(a.get_inputs_id() == b.get_inputs_id()) {
            return Err(AigError::MiterDifferentInputs);
        }
        // if !(a.get_outputs_id() == b.get_outputs_id()) {
        //     return Err(());
        // }
        Ok(Miter {
            a: a.clone(),
            b: b.clone(),
            litmap_a: HashMap::new(),
            litmap_b: HashMap::new(),
        })
    }

    pub fn try_prove_eq(&self, node_a: NodeId, node_b: NodeId) -> Result<()> {
        let mut cnf = Cnf::new();

        // Generating clauses from A
        let mut dfs = Dfs::from_node(
            self.a
                .get_node(node_a)
                .ok_or(AigError::NodeDoesNotExist(node_a))?,
        );
        while let Some(n) = dfs.next(&self.a) {
            cnf.add_clauses_node(&*n.borrow(), &self.litmap_a)?;
        }

        // Generating clauses from B
        let mut dfs = Dfs::from_node(
            self.b
                .get_node(node_b)
                .ok_or(AigError::NodeDoesNotExist(node_b))?,
        );
        while let Some(n) = dfs.next(&self.b) {
            cnf.add_clauses_node(&*n.borrow(), &self.litmap_b)?;
        }

        // TODO
        // prove the CNF is UNSAT using a SAT solver

        // If that's okay, merge nodes using litmaps

        Ok(())
    }
}
