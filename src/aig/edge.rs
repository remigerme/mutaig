//! An [`AigEdge`] points at an [`AigNode`] and can be complemented (indicates the presence of a NOT gate).
//!
//! [`AigNode`]: crate::AigNode

use std::ops::Not;

use crate::NodeId;

use super::AigNodeRef;

/// Unambiguous fanin selector.
#[derive(Debug, Clone, Copy)]
pub enum FaninId {
    Fanin0,
    Fanin1,
}

impl From<bool> for FaninId {
    fn from(value: bool) -> Self {
        if value {
            FaninId::Fanin1
        } else {
            FaninId::Fanin0
        }
    }
}

impl From<usize> for FaninId {
    fn from(value: usize) -> Self {
        if value == 0 {
            FaninId::Fanin0
        } else if value == 1 {
            FaninId::Fanin1
        } else {
            panic!("could not create FaninId from value={}", value)
        }
    }
}

/// A directed edge representing a fanin for AIG nodes.
///
/// The edge can carry an inverter according to the value of `complement`.
///
/// For example:
///
/// ```rust
/// use mutaig::{Aig, AigEdge, AigNode};
/// let mut aig = Aig::new();
/// let node_false = aig.add_node(AigNode::False).unwrap();
/// let fanin_false = AigEdge::new(node_false.clone(), false);
/// let fanin_true = AigEdge::new(node_false.clone(), true);
/// assert_eq!(fanin_false, !fanin_true);
/// ```
#[derive(Clone, Debug, Eq)]
pub struct AigEdge {
    /// The node the edge is refering to.
    /// It is wrapped in Rc<RefCell<_>> to allow multiple nodes refering to it.
    pub(super) node: AigNodeRef,
    /// Set to true if signal should be inverted.
    pub(super) complement: bool,
}

impl Not for AigEdge {
    type Output = Self;

    fn not(mut self) -> Self::Output {
        self.complement = !self.complement;
        self
    }
}

impl PartialEq for AigEdge {
    fn eq(&self, other: &Self) -> bool {
        self.complement == other.complement && self.get_node_id() == other.get_node_id()
    }
}

impl Into<(NodeId, bool)> for &AigEdge {
    fn into(self) -> (NodeId, bool) {
        (self.get_node_id(), self.get_complement())
    }
}

impl AigEdge {
    pub fn new(node: AigNodeRef, complement: bool) -> Self {
        AigEdge { node, complement }
    }

    pub fn get_node(&self) -> AigNodeRef {
        self.node.clone()
    }

    pub fn get_node_id(&self) -> NodeId {
        self.node.borrow().get_id()
    }

    pub fn get_complement(&self) -> bool {
        self.complement
    }

    pub fn is_cst_false(&self) -> bool {
        self.get_node_id() == 0 && !self.complement
    }

    pub fn is_cst_true(&self) -> bool {
        self.get_node_id() == 0 && self.complement
    }

    pub fn is_complement_of(&self, other: &AigEdge) -> bool {
        self.get_node_id() == other.get_node_id() && self.get_complement() ^ other.get_complement()
    }
}
