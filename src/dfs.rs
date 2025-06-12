//! Provides a DFS visitor to allow simple AIG traversal.
//!
//! See [`Dfs`] for details.
//!
//! [`Dfs`]: Dfs

use std::collections::HashSet;

use crate::{Aig, AigNodeRef, NodeId};

/// A simple DFS visitor.
///
/// Nodes are yielded in preorder. You can:
/// - start a DFS from a node using [`from_node`]
/// - or visit all the AIG by starting from the outputs using [`from_outputs`].
///
/// In the latter case, it will start by the fanin of the first output,
/// then explore all non-previously-explored nodes from the fanin of the second output,
/// and so on until all the outputs have been processed.
///
/// [`from_node`]: Dfs::from_node
/// [`from_outputs`]: Dfs::from_outputs
///
/// Example:
///
/// ```rust
/// use mutaig::{Aig, dfs::Dfs};
/// let mut aig = Aig::new();
/// // You can modify the aig here
/// let mut dfs = Dfs::from_outputs(&aig);
/// while let Some(noderef) = dfs.next(&aig) {
///     // You can still borrow mut aig here
///     // ...
/// }
/// ```
///
/// Inspired by [petgraph DFS](https://docs.rs/petgraph/latest/petgraph/visit/struct.Dfs.html).
pub struct Dfs {
    /// Must maintain the following invariant:
    /// - all nodes on the stack have not been visited yet
    /// - their `seen` flag is set to true to avoid adding them one more time to the stack
    /// - the different outputs from which to start a DFS are in starts
    ///   (they might have been visited already by the time we start the DFS from them,
    ///   and will simply be discarded if that's the case).
    stack: Vec<NodeId>,
    seen: HashSet<NodeId>,
    starts: Vec<NodeId>,
}

impl Dfs {
    /// Create a DFS from the initial start node.
    /// You will only browse the fanin of this node.
    pub fn from_node(start: AigNodeRef) -> Self {
        let start_id = start.borrow().get_id();
        Dfs {
            stack: vec![start_id],
            seen: HashSet::from([start_id]),
            starts: Vec::new(),
        }
    }

    /// Create a DFS from the outputs of the given AIG.
    /// It will explore all the AIG (as all nodes are in a fanin of one of the outputs).
    /// It will start by the fanin of the first output, then explore all non-previously-explored nodes
    /// from the fanin of the second output, and so on until all the outputs have been processed.
    pub fn from_outputs(aig: &Aig) -> Self {
        let mut ids: Vec<NodeId> = aig
            .get_outputs()
            .iter()
            .map(|fanin| fanin.node.borrow().get_id())
            .collect();
        if ids.is_empty() {
            return Dfs {
                stack: Vec::new(),
                seen: HashSet::new(),
                starts: Vec::new(),
            };
        }

        let start_id = ids.pop().unwrap();
        let stack = vec![start_id];
        let seen = HashSet::from([start_id]);
        Dfs {
            stack,
            seen,
            starts: ids,
        }
    }

    /// Returns true if we are ready to start again! Else false, we are done.
    /// Should only be called when stack is empty (ie we are done with the current fanin).
    fn new_start(&mut self) -> bool {
        assert!(self.stack.is_empty());

        while let Some(id) = self.starts.pop() {
            if !self.seen.contains(&id) {
                self.seen.insert(id);
                self.stack.push(id);
                return true;
            }
        }
        false
    }

    /// Yield the next node of the DFS, or None if it is done.
    /// If you created the DFS with the [`from_outputs`] method,
    /// this might be a new output if the current fanin has been fully explored.
    ///
    /// [`from_outputs`]: Dfs::from_outputs
    pub fn next(&mut self, aig: &Aig) -> Option<AigNodeRef> {
        while let Some(id) = self.stack.pop() {
            let node = aig.get_node(id).unwrap();
            for child in node.borrow().get_fanins() {
                let child_id = child.borrow().get_id();
                if !self.seen.contains(&child_id) {
                    self.seen.insert(child_id);
                    self.stack.push(child_id);
                }
            }
            return Some(node);
        }

        // Maybe we can start from a different output?
        if self.new_start() {
            return self.next(aig);
        }

        None
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{Aig, AigEdge, AigNode};

    #[test]
    fn from_node_test() {
        // Constructing the AIG
        let mut aig = Aig::new();
        let n0 = aig.add_node(AigNode::False).unwrap();
        let n1 = aig.add_node(AigNode::Input(1)).unwrap();
        let n2 = aig
            .add_node(AigNode::And {
                id: 2,
                fanin0: AigEdge::new(n0.clone(), false),
                fanin1: AigEdge::new(n1.clone(), false),
            })
            .unwrap();

        // Now using the DFS
        let mut dfs = Dfs::from_node(n2.clone());
        assert_eq!(dfs.next(&aig).unwrap(), n2.clone()); // first node is known
        let n = dfs.next(&aig).unwrap(); // second node could be either one of its child
        if n == n0.clone() {
            assert_eq!(dfs.next(&aig).unwrap(), n1.clone());
        } else if n == n1.clone() {
            assert_eq!(dfs.next(&aig).unwrap(), n0.clone());
        } else {
            panic!("Test failed.");
        }
        // Now there shouldn't be anything
        assert!(dfs.next(&aig).is_none());
        assert!(dfs.next(&aig).is_none());
        assert!(dfs.next(&aig).is_none());
    }

    #[test]
    fn from_outputs_test() {
        // Creating the AIG
        let mut aig = Aig::new();
        let n0 = aig.add_node(AigNode::False).unwrap();
        let n1 = aig.add_node(AigNode::Input(1)).unwrap();
        let n2 = aig
            .add_node(AigNode::And {
                id: 2,
                fanin0: AigEdge::new(n0.clone(), false),
                fanin1: AigEdge::new(n1.clone(), false),
            })
            .unwrap();
        let n3 = aig.add_node(AigNode::Input(3)).unwrap();
        let n4 = aig
            .add_node(AigNode::And {
                id: 4,
                fanin0: AigEdge::new(n2.clone(), false),
                fanin1: AigEdge::new(n3.clone(), false),
            })
            .unwrap();
        aig.add_output(2, false).unwrap();
        aig.add_output(4, true).unwrap();

        // Let's use the AIG - we have so many possible and equally valid DFS :')
        let mut dfs = Dfs::from_outputs(&aig);
        let n = dfs.next(&aig).unwrap();
        // If we start by n2
        if n == n2.clone() {
            // Processing n2 fanin
            let n = dfs.next(&aig).unwrap();
            if n == n0.clone() {
                assert_eq!(dfs.next(&aig).unwrap(), n1.clone());
            } else if n == n1.clone() {
                assert_eq!(dfs.next(&aig).unwrap(), n0.clone());
            } else {
                panic!("Test failed.");
            }

            // Processing n4 fanin
            assert_eq!(dfs.next(&aig).unwrap(), n4.clone());
            assert_eq!(dfs.next(&aig).unwrap(), n3.clone());
        }
        // Else we start by n4
        else if n == n4.clone() {
            let n = dfs.next(&aig).unwrap();
            // If we start by n2
            if n == n2.clone() {
                // We start by processing n2 fanin
                let n = dfs.next(&aig).unwrap();
                if n == n0.clone() {
                    assert_eq!(dfs.next(&aig).unwrap(), n1.clone());
                } else if n == n1.clone() {
                    assert_eq!(dfs.next(&aig).unwrap(), n0.clone());
                } else {
                    panic!("Test failed.");
                }

                // Then we must process n3
                assert_eq!(dfs.next(&aig).unwrap(), n3.clone());
            }
            // Else we start by n3
            else if n == n3.clone() {
                // Then we must handle n2 fanin
                assert_eq!(dfs.next(&aig).unwrap(), n2.clone());
                let n = dfs.next(&aig).unwrap();
                if n == n0.clone() {
                    assert_eq!(dfs.next(&aig).unwrap(), n1.clone());
                } else if n == n1.clone() {
                    assert_eq!(dfs.next(&aig).unwrap(), n0.clone());
                } else {
                    panic!("Test failed.");
                }
            } else {
                panic!("Test failed.");
            }
        } else {
            panic!("Test failed.")
        }

        // Now the DFS should be done
        assert!(dfs.next(&aig).is_none());
        assert!(dfs.next(&aig).is_none());
        assert!(dfs.next(&aig).is_none());
    }

    #[test]
    fn repeated_node() {
        let mut aig = Aig::new();
        let n0 = aig.add_node(AigNode::Input(1)).unwrap();
        let n1 = aig.add_node(AigNode::Input(1)).unwrap();
        let n2 = aig
            .add_node(AigNode::And {
                id: 2,
                fanin0: AigEdge::new(n0.clone(), false),
                fanin1: AigEdge::new(n1.clone(), true),
            })
            .unwrap();
        let mut dfs = Dfs::from_node(n2.clone());
        assert_eq!(dfs.next(&aig).unwrap(), n2.clone());
        assert_eq!(dfs.next(&aig).unwrap(), n1.clone());
        assert!(dfs.next(&aig).is_none());
    }
}
