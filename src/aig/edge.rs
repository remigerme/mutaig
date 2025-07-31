use std::ops::Not;

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
        self.complement == other.complement
            && self.node.borrow().get_id() == other.node.borrow().get_id()
    }
}

impl AigEdge {
    pub fn new(node: AigNodeRef, complement: bool) -> Self {
        AigEdge { node, complement }
    }

    pub fn get_node(&self) -> AigNodeRef {
        self.node.clone()
    }

    pub fn get_complement(&self) -> bool {
        self.complement
    }
}
