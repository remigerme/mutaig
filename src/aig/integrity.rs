use std::ops::Deref;

use crate::{Aig, AigEdge, AigError, AigNode, AigNodeRef, NodeId, Result};

impl Aig {
    fn check_node_id_aiger_consistency(&self, id: NodeId) -> Result<()> {
        let i = self.inputs.len() as u64;
        let l = self.latches.len() as u64;
        let n_nodes = self.nodes.len() as u64;
        match self.get_node(id) {
            None => Err(AigError::NodeDoesNotExist(id)),
            Some(n) => {
                (id == 0)
                    .then(|| match n.borrow().is_false() {
                        true => Ok(()),
                        false => Err(AigError::IdZeroButNotFalse),
                    })
                    .unwrap_or(Ok(()))?;
                (1 <= id && id <= i)
                    .then(|| match n.borrow().is_input() {
                        true => Ok(()),
                        false => Err(AigError::InvalidState(format!(
                            "id={} (expected inputs from 1 to {}) but node is not an input",
                            id, i
                        ))),
                    })
                    .unwrap_or(Ok(()))?;
                (1 + i <= id && id <= i + l)
                    .then(|| match n.borrow().is_latch() {
                        true => Ok(()),
                        false => Err(AigError::InvalidState(format!(
                            "id={} (expected latches from {} to {}) but node is not a latch",
                            id,
                            1 + i,
                            i + l
                        ))),
                    })
                    .unwrap_or(Ok(()))?;
                (1 + i + l <= id && id < n_nodes)
                    .then(|| match n.borrow().is_and() {
                        true => Ok(()),
                        false => Err(AigError::InvalidState(format!(
                            "id={} (expected and gates from {} to {}) but node is not an and gate",
                            id,
                            1 + i + l,
                            n_nodes - 1
                        ))),
                    })
                    .unwrap_or(Ok(()))?;
                (id >= n_nodes)
                    .then(|| {
                        Err(AigError::InvalidState(format!(
                            "id={} but there is {} nodes overall (max id = {})",
                            id,
                            n_nodes,
                            n_nodes - 1
                        )))
                    })
                    .unwrap_or(Ok(()))
            }
        }
    }

    /// Tests if the current AIG nodes are in a valid AIGER format:
    /// - constant with id $0$
    /// - then inputs with ids $1, ..., i$
    /// - then latches with ids $i + 1, ..., i + l + 1$
    /// - then and gates with ids $i + l + 1, ..., i + l + a + 1$ such as for all gate z = and(a, b),
    ///   $id(z) \gt id(a) \geq id(b)$
    /// You can use [`Aig::minimize_ids`] to mutate the current AIG into an AIGER-compliant AIG.
    pub fn check_valid_aiger(&self) -> Result<()> {
        let n_nodes = self.nodes.len() as u64;
        for k in 0..n_nodes {
            self.check_node_id_aiger_consistency(k)?;
        }

        let i = self.inputs.len() as u64;
        let l = self.latches.len() as u64;
        let a = n_nodes - i - l - 1;

        for k in 0..a {
            let id = 1 + i + l + k;
            let n = self.get_node(id).unwrap();
            let fanins = n.borrow().get_fanins();
            let i0 = fanins[0].get_node().borrow().get_id();
            let i1 = fanins[1].get_node().borrow().get_id();

            if id <= i0 {
                return Err(AigError::InvalidState(format!(
                    "id of parent {} should be strictly larger than its fanin0 {}",
                    id, i0
                )));
            }
            if i0 < i1 {
                return Err(AigError::InvalidState(format!(
                    "(parent {}) id of fanin0 {} should be superior or equal to fanin1 {}",
                    id, i0, i1
                )));
            }
        }

        Ok(())
    }

    /// Checking if the AIG structure is correct.
    /// This function was written for debug purposes, as the library is supposed to maintain
    /// integrity of the AIG at any moment.
    pub fn check_integrity(&self) -> Result<()> {
        // Checking that all nodes have relevant id
        // and perform some individual integrity checks
        for (&id, weak_node) in &self.nodes {
            if let Some(node) = weak_node.upgrade() {
                if node.borrow().get_id() != id {
                    return Err(AigError::InvalidState("incoherent node id".to_string()));
                }

                self.check_node_integrity(node)?;
            }
        }

        // Checking that all outputs are registered as nodes
        for output in &self.outputs {
            let output_id = output.get_node().borrow().get_id();
            if self.get_node(output_id).is_none() {
                return Err(AigError::InvalidState(format!(
                    "output ({}, {}) refers to node {} which is not in the aig",
                    output_id,
                    output.get_complement(),
                    output_id
                )));
            }
        }

        // Checks for acyclicity
        self.get_topological_sort()?;

        Ok(())
    }

    /// Check the integrity for an individual node, that is:
    /// - check that only `False` have id 0
    /// - check that fanins (`AigEdge`) for latch and and gate are valid too
    ///   (ie they refer to a known node for this AIG)
    fn check_node_integrity(&self, node: AigNodeRef) -> Result<()> {
        match node.borrow().deref() {
            AigNode::False => {
                if node.borrow().get_id() != 0 {
                    return Err(AigError::InvalidState("invalid false node".to_string()));
                }
            }
            AigNode::Input(id) => {
                if *id == 0 {
                    return Err(AigError::IdZeroButNotFalse);
                }
            }
            AigNode::Latch { id, next, .. } => {
                if *id == 0 {
                    return Err(AigError::IdZeroButNotFalse);
                }
                self.check_edge_integrity(next)?;
            }
            AigNode::And {
                id,
                fanin0,
                fanin1,
                fanouts,
            } => {
                if *id == 0 {
                    return Err(AigError::IdZeroButNotFalse);
                }
                for (fanout_id, fanout_weak) in fanouts {
                    if let Some(fanout) = fanout_weak.upgrade() {
                        let fanout_id_real = fanout.borrow().get_id();
                        if *fanout_id != fanout_id_real {
                            return Err(AigError::InvalidState(format!(
                                "incoherent fanout node id : {} in map vs {} in reality",
                                fanout_id, fanout_id_real
                            )));
                        }
                        if !self.nodes.contains_key(&fanout.borrow().get_id()) {
                            return Err(AigError::InvalidState(format!(
                                "fanout {} is no longer in the AIG",
                                fanout.borrow().get_id()
                            )));
                        }
                    }
                }
                self.check_edge_integrity(fanin0)?;
                self.check_edge_integrity(fanin1)?;
            }
        }
        Ok(())
    }

    fn check_edge_integrity(&self, fanin: &AigEdge) -> Result<()> {
        let id = fanin.node.borrow().get_id();
        self.get_node(id).ok_or(AigError::InvalidState(format!(
            "edge pointing at node {} which is not in the AIG anymore",
            id
        )))?;
        Ok(())
    }
}
