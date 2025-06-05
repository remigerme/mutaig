use std::cell::RefCell;
use std::collections::HashMap;
use std::ops::Not;
use std::rc::{Rc, Weak};

use thiserror::Error;

/// A node id.
///
/// The constant node `False` has id 0 by convention. Also, id must be unique.
pub type NodeId = u64;

/// The result of an AIG operation.
pub type Result<T> = std::result::Result<T, AigError>;

/// Error returned when an AIG operation failed.
#[derive(Debug, Error)]
pub enum AigError {
    /// A different node with the given id already exists.
    #[error("a different node with id={0} already exists")]
    DuplicateId(NodeId),

    /// The node with given id does not exist.
    #[error("node with id={0} does not exist")]
    NodeDoesNotExist(NodeId),

    /// Invalid operation on a node which should be an AND gate but is not.
    #[error("the node is not an AND gate")]
    NotAndGate,

    /// The AIG has reached an invalid state. This should never happen.
    /// For example, when tracking the nodes internally with the hashmap nodes,
    /// node `nodes[id]` should have id `id`. If this error is raised, my code is garbage.
    #[error("the AIG has reached an invalid state - this should not happen")]
    InvalidState,
}

/// Unambiguous fanin selector.
pub enum FaninId {
    Fanin0,
    Fanin1,
}

/// A directed edge representing a fanin for AIG nodes.
///
/// The edge can carry an inverter according to the value of `complement`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AigEdge {
    /// The node the edge is refering to.
    /// It is wrapped in Rc<RefCell<_>> to allow multiple nodes refering to it.
    node: AigNodeRef,
    /// Set to true if signal should be inverted.
    complement: bool,
}

impl Not for AigEdge {
    type Output = Self;

    fn not(mut self) -> Self::Output {
        self.complement = !self.complement;
        self
    }
}

/// An AIG node.
///
/// Each node has an id. By convention, id for constant node `False` is 0. The id must be unique.
#[derive(Debug, PartialEq, Eq)]
pub enum AigNode {
    /// The constant low/false signal.
    False,
    /// A primary input.
    Input(NodeId),
    /// A latch (for sequential circuits).
    Latch {
        id: NodeId,
        next: AigEdge,
        init: Option<bool>,
    },
    /// An AND gate with two fanins.
    And {
        id: NodeId,
        fanin0: AigEdge,
        fanin1: AigEdge,
    },
}

/// A wrapper for AIG nodes to allow multiple references to it.
pub type AigNodeRef = Rc<RefCell<AigNode>>;

/// A non-counting reference to an AIG node - used internally
type AigNodeWeak = Weak<RefCell<AigNode>>;

impl AigNode {
    fn get_id(&self) -> NodeId {
        match *self {
            AigNode::False => 0,
            AigNode::Input(id) => id,
            AigNode::Latch { id, .. } => id,
            AigNode::And { id, .. } => id,
        }
    }

    fn set_fanin(&mut self, fanin: &AigEdge, fanin_id: FaninId) -> Result<()> {
        match (self, fanin_id) {
            (AigNode::And { fanin0, .. }, FaninId::Fanin0) => Ok(*fanin0 = fanin.clone()),
            (AigNode::And { fanin1, .. }, FaninId::Fanin1) => Ok(*fanin1 = fanin.clone()),
            _ => Err(AigError::NotAndGate),
        }
    }
}

pub struct Aig {
    nodes: HashMap<NodeId, AigNodeWeak>,
    outputs: HashMap<NodeId, AigNodeRef>,
    keep_nodes_alive: Vec<AigNodeRef>,
}

impl Aig {
    pub fn new() -> Self {
        Aig {
            nodes: HashMap::new(),
            outputs: HashMap::new(),
            keep_nodes_alive: Vec::new(),
        }
    }

    /// Retrieves a node from its id
    pub fn get_node(&self, id: NodeId) -> Option<AigNodeRef> {
        self.nodes.get(&id)?.upgrade()
    }

    pub fn update(&mut self) {
        // Stop keeping nodes artificially alive
        self.keep_nodes_alive.clear();

        // Removing no longer valid entries from the nodes
        self.nodes
            .retain(|_, weak_node| weak_node.upgrade().is_some());
    }

    /// Create a new (or retrieve existing) node within the AIG.
    /// This will fail if a different node with the same id already exists in the AIG.
    fn add_node(&mut self, node: AigNode) -> Result<AigNodeRef> {
        let id = node.get_id();
        match self.get_node(id) {
            // No node with this id, let's create a new one
            None => {
                let n: Rc<RefCell<AigNode>> = Rc::new(RefCell::new(node));
                self.nodes.insert(id, Rc::downgrade(&n));
                self.keep_nodes_alive.push(n.clone());
                Ok(n)
            }
            // A node was found, maybe it is just the one we're trying to create
            Some(n) => {
                if *n.borrow() == node {
                    Ok(n)
                } else {
                    Err(AigError::DuplicateId(id))
                }
            }
        }
    }

    /// Create a new and node (or retrieve it if the exact same node already exists).
    pub fn new_and(&mut self, id: NodeId, fanin0: AigEdge, fanin1: AigEdge) -> Result<AigNodeRef> {
        let candidate = AigNode::And { id, fanin0, fanin1 };
        self.add_node(candidate)
    }

    /// Mark an existing node as an output.
    pub fn add_output(&mut self, id: NodeId) -> Result<()> {
        let node = self.get_node(id).ok_or(AigError::NodeDoesNotExist(id))?;
        self.outputs.insert(id, node);
        Ok(())
    }

    /// Remove a node from the outputs. Do not error if node does not exist or was not an output,
    /// simply returns None instead of the node.
    pub fn remove_output(&mut self, id: NodeId) -> Option<AigNodeRef> {
        let node = self.get_node(id)?;
        self.outputs.remove(&node.borrow().get_id())
    }

    /// Replace the given fanin of a node by a new fanin
    /// Both nodes need to already exist in the AIG
    pub fn replace_fanin(
        &mut self,
        parent_id: NodeId,
        fanin_id: FaninId,
        child_id: NodeId,
        complement: bool,
    ) -> Result<()> {
        let parent = self
            .get_node(parent_id)
            .ok_or(AigError::NodeDoesNotExist(parent_id))?;
        let child = self
            .get_node(child_id)
            .ok_or(AigError::NodeDoesNotExist(child_id))?;

        let fanin = AigEdge {
            node: child,
            complement,
        };

        parent.borrow_mut().set_fanin(&fanin, fanin_id)
    }

    /// Checking if the AIG structure is correct.
    /// This function was written for debug purposes, as the library is supposed to maintain
    /// integrity of the AIG at any moment.
    pub fn check_integrity(&self) -> Result<()> {
        // Checking that all nodes have relevant id
        for (&id, weak_node) in &self.nodes {
            if let Some(node) = weak_node.upgrade() {
                if node.borrow().get_id() != id {
                    return Err(AigError::InvalidState);
                }
            }
        }

        // Checking that all outputs are registered as nodes
        for (&id, _) in &self.outputs {
            if self.get_node(id).is_none() {
                return Err(AigError::InvalidState);
            }
        }

        // TODO more sophisticated checks
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn edge_eq() {
        let node = AigNode::False;
        let noderef = Rc::new(RefCell::new(node));

        // Checking expected equality
        let e1 = AigEdge {
            node: noderef.clone(),
            complement: false,
        };
        let e2 = AigEdge {
            node: noderef.clone(),
            complement: false,
        };
        assert_eq!(e1, e2);

        let new_node = AigNode::Input(1);
        let new_noderef = Rc::new(RefCell::new(new_node));
        let e3 = AigEdge {
            node: new_noderef.clone(),
            complement: false,
        };
        assert_eq!(e1, e3);

        // Checking Not implementation
        let e4 = AigEdge {
            node: noderef.clone(),
            complement: true,
        };
        assert_ne!(e1, e4);
        assert_eq!(e1, !e4);
    }

    #[test]
    fn node_lifetime() {
        let mut aig = Aig::new();

        {
            let node = AigNode::False;
            aig.add_node(node).unwrap();
        }
        assert!(aig.get_node(0).is_some());

        aig.update();
        assert!(aig.get_node(0).is_none());
    }
}
