//! A simple DFS visitor.
//!
//! Start a DFS from a node using [`from_node`], or visit all the AIG by starting from the outputs
//! using [`from_outputs`]. In the latter case, it will start by the fanin of the first output,
//! then explore all non-previously-explored nodes from the fanin of the second output,
//! and so on until all the outputs have been processed.
//!
//! [`from_node`]: Dfs::from_node
//! [`from_outputs`]: Dfs::from_outputs
//!
//! Example:
//!
//! ```rust
//! let aig = Aig::new();
//! ...
//! let dfs = Dfs::from_outputs(&aig);
//! while let Some(noderef) = dfs.next(&aig) {
//!     // You can borrow mut aig here!
//!     ...
//! }
//! ```
//!
//! Inspired by [petgraph DFS](https://docs.rs/petgraph/latest/petgraph/visit/struct.Dfs.html).

use std::collections::HashSet;

use crate::{Aig, AigNode, AigNodeRef, NodeId};

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
    pub fn from_node(start: &AigNode) -> Self {
        let start_id = start.get_id();
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
        let mut ids: Vec<NodeId> = aig.outputs.keys().copied().collect();
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
