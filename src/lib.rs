use std::cell::RefCell;
use std::collections::HashMap;
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
}

/// Unambiguous fanin selector.
pub enum FaninId {
    Fanin0,
    Fanin1,
}

/// A directed edge representing a fanin for AIG nodes.
///
/// The edge can carry an inverter according to the value of `complement`.
#[derive(Clone, Debug, PartialEq)]
pub struct AigEdge {
    /// The node the edge is refering to.
    /// It is wrapped in Rc<RefCell<_>> to allow multiple nodes refering to it.
    node: AigNodeRef,
    /// Set to true if signal should be inverted.
    complement: bool,
}

/// An AIG node.
///
/// Each node has an id. By convention, id for constant node `False` is 0. The id must be unique.
#[derive(Debug, PartialEq)]
pub enum AigNode {
    /// The constant low/false signal.
    False,
    /// A primary input.
    Input(NodeId),
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
    keep_nodes_alive: Vec<AigNodeRef>,
}

impl Aig {
    pub fn new() -> Self {
        Aig {
            nodes: HashMap::new(),
            keep_nodes_alive: Vec::new(),
        }
    }

    pub fn update(&mut self) {
        self.keep_nodes_alive.clear();
    }

    /// Create a new (or retrieve existing) node within the AIG.
    /// This will fail if a different node with the same id already exists in the AIG.
    pub fn add_node(&mut self, node: AigNode) -> Result<AigNodeRef> {
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

    /// Retrieves a node from its id
    pub fn get_node(&self, id: NodeId) -> Option<AigNodeRef> {
        self.nodes.get(&id)?.upgrade()
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
}

#[cfg(test)]
mod tests {
    use super::*;

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
