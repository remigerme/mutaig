use std::ops::Deref;

use crate::{Aig, AigEdge, AigError, AigNode, Result};

impl Aig {
    /// Performs a real recursive clone of the AIG.
    ///
    /// We are not just incrementing reference counters, but instead creating
    /// brand new nodes, completely unrelated with the previous AIG.
    ///
    /// The strategy to do the clone is roughly same as the one used to instantiate an AIG
    /// from an AIGER binary file, see [`Aig::from_bin`]. Basically :
    /// - create inputs
    /// - create dummy latches
    /// - create and gates
    /// - update latches fanins
    /// - register outputs
    pub fn deep_clone(&self) -> Result<Self> {
        self.check_integrity()?;

        let mut aig = Aig::new();
        let node_false = aig.get_node(0).unwrap();

        // Adding inputs
        for input in &self.get_inputs() {
            if let AigNode::Input(id) = input.borrow().deref() {
                aig.add_node(AigNode::Input(*id))?;
            } else {
                panic!("Expected input, got node {:?}", input);
            }
        }

        // Adding latches with dummy fanins
        for latch in self.get_latches() {
            if let AigNode::Latch { id, init, .. } = latch.borrow().deref() {
                aig.add_node(AigNode::Latch {
                    id: *id,
                    next: AigEdge::new(node_false.clone(), false),
                    init: *init,
                })?;
            } else {
                panic!("Expected latch, got node {:?}", latch);
            }
        }

        // Adding and gates in topological order
        for node in self.get_topological_sort()? {
            if let AigNode::And {
                id, fanin0, fanin1, ..
            } = node.borrow().deref()
            {
                // Beware, we also must recreate the corresponding fanins
                let i0 = fanin0.get_node().borrow().get_id();
                let new_fanin0 = AigEdge::new(
                    aig.get_node(i0).ok_or(AigError::NodeDoesNotExist(i0))?,
                    fanin0.get_complement(),
                );
                let i1 = fanin1.get_node().borrow().get_id();
                let new_fanin1 = AigEdge::new(
                    aig.get_node(i1).ok_or(AigError::NodeDoesNotExist(i1))?,
                    fanin1.get_complement(),
                );

                aig.add_node(AigNode::and(*id, new_fanin0, new_fanin1))?;
            }
        }

        // Edit the fanin of the latches
        for id in aig.get_latches_id() {
            let latch_ref = self.get_node(id).ok_or(AigError::NodeDoesNotExist(id))?;
            if let AigNode::Latch { next, .. } = latch_ref.borrow().deref() {
                aig.replace_fanin(
                    id,
                    crate::FaninId::Fanin0,
                    next.get_node().borrow().get_id(),
                    next.complement,
                )?;
            } else {
                panic!("Expected latch, got node {:?}", latch_ref);
            }
        }

        // Mark outputs
        for output in self.get_outputs() {
            aig.add_output(output.get_node().borrow().get_id(), output.complement)?;
        }

        aig.update();
        aig.check_integrity()?;

        Ok(aig)
    }
}

#[cfg(test)]
mod test {
    use std::path::Path;

    use crate::Aig;

    fn deep_clone_test<P: AsRef<Path>>(path: P) {
        let aig = Aig::from_file(path).unwrap();
        let new = aig.deep_clone().unwrap();
        assert_eq!(aig, new);
    }

    #[test]
    fn deep_clone_half_adder() {
        deep_clone_test("assets/circuits/half-adder.aag");
    }

    #[test]
    fn deep_clone_ctrl() {
        deep_clone_test("assets/circuits/ctrl.aig");
    }

    #[test]
    fn deep_clone_beemandrsn1f1() {
        deep_clone_test("assets/circuits/beemandrsn1f1.aig");
    }
}
