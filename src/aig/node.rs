//! Define [`AigNode`] and its commonly used alias [`AigNodeRef`].
//!
//! In an AIG, nodes are wrapped by [`Rc<RefCell<AigNode>>`], so in practice
//! you often deal with [`AigNodeRef`] (alias for the previous type) instead.
//!
//! For internal use, you can also use `AigNodeWeak` sometimes.

use std::{
    cell::RefCell,
    collections::HashMap,
    mem::swap,
    rc::{Rc, Weak},
};

use super::{AigEdge, AigError, FaninId, Result};

/// A node id.
///
/// The constant node [`AigNode::False`] has id 0 by convention. Also, id must be unique.
pub type NodeId = u64;

/// An AIG node.
///
/// Each node has an id. By convention, id for constant node `False` is 0. The id must be unique.
///
/// Internal note: gates carry their fanouts with them. Make sure to update this correctly.
#[derive(Debug, Clone)]
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
    /// An AND gate with two fanins - also carry their fanouts (update that correctly).
    And {
        id: NodeId,
        fanin0: AigEdge,
        fanin1: AigEdge,
        fanouts: HashMap<NodeId, AigNodeWeak>,
    },
}

/// A wrapper for AIG nodes to allow multiple references to it.
pub type AigNodeRef = Rc<RefCell<AigNode>>;

/// A non-counting reference to an AIG node - used internally.
pub(crate) type AigNodeWeak = Weak<RefCell<AigNode>>;

impl PartialEq for AigNode {
    /// Equalities for [`AigNode::False`], [`AigNode::Input`], and [`AigNode::Latch`] are straightforward.
    /// For [`AigNode::And`]:
    /// - order of fanins is not relevant
    /// - [`AigNode::And::fanouts`] is not taken into account.
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (AigNode::False, AigNode::False) => true,
            (AigNode::Input(id1), AigNode::Input(id2)) => id1 == id2,
            (
                AigNode::Latch {
                    id: id1,
                    next: next1,
                    init: init1,
                },
                AigNode::Latch {
                    id: id2,
                    next: next2,
                    init: init2,
                },
            ) => id1 == id2 && next1 == next2 && init1 == init2,
            (
                AigNode::And {
                    id: id1,
                    fanin0: fanin01,
                    fanin1: fanin11,
                    ..
                },
                AigNode::And {
                    id: id2,
                    fanin0: fanin02,
                    fanin1: fanin12,
                    ..
                },
            ) => {
                id1 == id2
                    && ((fanin01 == fanin02 && fanin11 == fanin12)
                        || (fanin01 == fanin12 && fanin11 == fanin02))
            }
            (_, _) => false,
        }
    }
}

impl Eq for AigNode {}

impl AigNode {
    /// Returns a new and gate (initialize empty fanouts).
    pub fn and(id: NodeId, fanin0: AigEdge, fanin1: AigEdge) -> Self {
        if id == 0 {
            panic!(
                "Hey, you are trying to create an AND gate with id=0. \
                Id=0 is reserved for the constant node AigNode::False."
            )
        }
        AigNode::And {
            id,
            fanin0,
            fanin1,
            fanouts: HashMap::new(),
        }
    }

    /// Returns a new latch.
    pub fn latch(id: NodeId, next: AigEdge, init: Option<bool>) -> Self {
        if id == 0 {
            panic!(
                "Hey, you are trying to create a latch with id=0. \
                Id=0 is reserved for the constant node AigNode::False."
            )
        }
        AigNode::Latch { id, next, init }
    }

    pub fn is_false(&self) -> bool {
        matches!(self, AigNode::False)
    }

    pub fn is_input(&self) -> bool {
        matches!(self, AigNode::Input(_))
    }

    pub fn is_latch(&self) -> bool {
        matches!(self, AigNode::Latch { .. })
    }

    pub fn is_and(&self) -> bool {
        matches!(self, AigNode::And { .. })
    }

    pub fn get_id(&self) -> NodeId {
        match *self {
            AigNode::False => 0,
            AigNode::Input(id) => id,
            AigNode::Latch { id, .. } => id,
            AigNode::And { id, .. } => id,
        }
    }

    /// Returns fanouts as a hashmap if the node is an and gate, else returns [`None`].
    pub fn get_and_fanouts(&self) -> Option<HashMap<NodeId, AigNodeWeak>> {
        match self {
            AigNode::And { fanouts, .. } => Some(fanouts.clone()),
            _ => None,
        }
    }

    pub(super) fn clear_fanouts(&mut self) {
        match self {
            AigNode::And { fanouts, .. } => fanouts.clear(),
            _ => (),
        }
    }

    /// Okay, what is going on here is a bit subtle.
    /// The core problem is that in practice, the `fanout` is mutably owned by the caller.
    /// The first approach of taking an `AigNodeRef` as an argument, and computing the `NodeId`
    /// by borrowing doesn't work : we are not allowed to borrow!
    /// So we need to supply the id of the fanout to store and be able to identify the fanout,
    /// without borrowing the `AigNodeRef`.
    pub(super) fn add_fanout(&mut self, fanout_id: NodeId, fanout: AigNodeWeak) {
        match self {
            AigNode::And { fanouts, .. } => {
                fanouts.insert(fanout_id, fanout);
            }
            _ => (),
        }
    }

    /// What is going on with fanouts is a bit subtle, check [`AigNode::add_fanout`] for more information.
    fn remove_fanout(&mut self, fanout_id: NodeId) -> Result<()> {
        match self {
            AigNode::And { fanouts, .. } => {
                fanouts.retain(|_, weak| weak.upgrade().is_some());
                let old_size = fanouts.len();
                fanouts.retain(|&id, _| id != fanout_id);
                let new_size = fanouts.len();
                if new_size < old_size {
                    Ok(())
                } else {
                    Err(AigError::InvalidState(format!(
                        "failed to remove fanout {} (not found) from node {}",
                        fanout_id,
                        self.get_id()
                    )))
                }
            }
            _ => Ok(()),
        }
    }

    /// What is going on with fanouts is a bit subtle, check [`AigNode::add_fanout`] for more information.
    /// You can also check the code of [`AigNode::remove_fanout`].
    fn update_fanout_entry(&mut self, old_fanout_id: NodeId, new_fanout_id: NodeId) -> Result<()> {
        let self_id = self.get_id();
        match self {
            AigNode::And { fanouts, .. } => {
                let weak = fanouts
                    .remove(&old_fanout_id)
                    .ok_or(AigError::InvalidState(format!(
                        "failed to update fanout {} (not found) to {} from node {}",
                        old_fanout_id, new_fanout_id, self_id
                    )))?;
                fanouts.insert(new_fanout_id, weak);
                Ok(())
            }
            _ => Ok(()),
        }
    }

    /// **WARNING**
    ///
    /// You should ABSOLUTELY maintain the owning AIG structure invariants.
    /// Make sure you update the [`Aig::nodes`] map with the new id.
    ///
    /// This function was originally proposed to implement [`Aig::minimize_ids`].
    ///
    /// Note that fanouts must also be taken into account.
    /// Here, we must update the fanout keys of the fanins of this node.
    ///
    /// [`Aig::nodes`]: super::Aig::nodes
    /// [`Aig::minimize_ids`]: super::Aig::minimize_ids
    pub(super) fn set_id(&mut self, id: NodeId) -> Result<()> {
        match self {
            AigNode::And {
                id: eid,
                fanin0,
                fanin1,
                ..
            } => {
                fanin0
                    .get_node()
                    .borrow_mut()
                    .update_fanout_entry(*eid, id)?;
                fanin1
                    .get_node()
                    .borrow_mut()
                    .update_fanout_entry(*eid, id)?;

                *eid = id;
                Ok(())
            }
            _ => Err(AigError::InvalidState(format!(
                "you are trying to rewrite id of false/input/latch node with current id={}, there is no good reason you are trying to do that",
                self.get_id()
            ))),
        }
    }

    pub fn get_fanins(&self) -> Vec<AigEdge> {
        match self {
            AigNode::Latch { next, .. } => vec![next.clone()],
            AigNode::And { fanin0, fanin1, .. } => vec![fanin0.clone(), fanin1.clone()],
            _ => vec![],
        }
    }

    /// This function also updates fanouts of previous and new fanins.
    pub(super) fn set_fanin(
        &mut self,
        fanin: &AigEdge,
        fanin_id: FaninId,
        self_weak: AigNodeWeak,
    ) -> Result<()> {
        let self_id = self.get_id();
        match (self, fanin_id) {
            (AigNode::And { fanin0, .. }, FaninId::Fanin0) => {
                fanin0.get_node().borrow_mut().remove_fanout(self_id)?;
                *fanin0 = fanin.clone();
                fanin0
                    .get_node()
                    .borrow_mut()
                    .add_fanout(self_id, self_weak);
                Ok(())
            }
            (AigNode::And { fanin1, .. }, FaninId::Fanin1) => {
                fanin1.get_node().borrow_mut().remove_fanout(self_id)?;
                *fanin1 = fanin.clone();
                fanin1
                    .get_node()
                    .borrow_mut()
                    .add_fanout(self_id, self_weak);
                Ok(())
            }
            (AigNode::Latch { next, .. }, FaninId::Fanin0) => Ok(*next = fanin.clone()),
            _ => Err(AigError::NoFanin),
        }
    }

    /// Invert signal of fanin of the current node from node child_id.
    pub(super) fn invert_edge(&mut self, child_id: NodeId) -> Result<()> {
        match self {
            AigNode::And {
                id, fanin0, fanin1, ..
            } => {
                let mut found = false;
                if fanin0.get_node_id() == child_id {
                    found = true;
                    fanin0.complement = !fanin0.complement;
                }
                if fanin1.get_node_id() == child_id {
                    found = true;
                    fanin1.complement = !fanin1.complement;
                }
                if found {
                    Ok(())
                } else {
                    Err(AigError::InvalidState(format!(
                        "node {} does not have fanin {}",
                        id, child_id
                    )))
                }
            }
            AigNode::Latch { id, next, .. } => {
                if next.get_node_id() == child_id {
                    next.complement = !next.complement;
                    Ok(())
                } else {
                    Err(AigError::InvalidState(format!(
                        "node {} does not have fanin {}",
                        id, child_id
                    )))
                }
            }
            _ => Err(AigError::InvalidState(format!(
                "input {} has no fanin",
                self.get_id()
            ))),
        }
    }

    /// Reorders fanins to make sure fanin0_id >= fanin1_id for AND gates.
    ///
    /// This is part of the AIGER binary format requirements, and is part of
    /// the [`Aig::minimize_ids`] procedure.
    ///
    /// [`Aig::minimize_ids`]: super::Aig::minimize_ids
    pub(super) fn reorder_fanins(&mut self) {
        match self {
            AigNode::And { fanin0, fanin1, .. } => {
                let id0 = fanin0.get_node_id();
                let id1 = fanin1.get_node_id();
                if id0 < id1 {
                    swap(fanin0, fanin1);
                }
            }
            _ => (),
        }
    }
}

#[cfg(test)]
mod test {
    use std::{cell::RefCell, rc::Rc};

    use crate::{AigEdge, AigNode, AigNodeRef};

    fn wrap(node: AigNode) -> AigNodeRef {
        Rc::new(RefCell::new(node))
    }

    fn edge(node: AigNodeRef) -> AigEdge {
        AigEdge::new(node, false)
    }

    #[test]
    #[should_panic]
    fn create_node_test_invalid_latch_id0() {
        let nf = wrap(AigNode::False);
        let _ = AigNode::latch(0, edge(nf), None);
    }

    #[test]
    #[should_panic]
    fn create_node_test_invalid_and_id0() {
        let nf = wrap(AigNode::False);
        let _ = AigNode::and(0, edge(nf.clone()), edge(nf));
    }

    #[test]
    fn node_eq_test() {
        let nf = wrap(AigNode::False);
        let i1 = wrap(AigNode::Input(1));
        let a2 = wrap(AigNode::and(2, edge(nf.clone()), edge(i1.clone())));
        let l3 = wrap(AigNode::latch(3, edge(a2.clone()), None));

        assert_eq!(nf, wrap(AigNode::False));

        assert_eq!(i1, wrap(AigNode::Input(1)));
        assert_ne!(i1, wrap(AigNode::Input(2)));

        // Note that fanouts are not taken into account for equality
        assert_eq!(
            a2,
            wrap(AigNode::and(2, edge(nf.clone()), edge(i1.clone()),))
        );
        // Fanins do commute
        assert_eq!(
            a2,
            wrap(AigNode::and(2, edge(i1.clone()), edge(nf.clone()),))
        );
        assert_ne!(
            a2,
            wrap(AigNode::and(2, !edge(nf.clone()), edge(i1.clone()),))
        );
        assert_ne!(
            a2,
            wrap(AigNode::and(2, edge(nf.clone()), !edge(i1.clone()),))
        );

        assert_eq!(l3, wrap(AigNode::latch(3, edge(a2.clone()), None,)));
        assert_ne!(l3, wrap(AigNode::latch(3, edge(a2.clone()), Some(false),)));
    }

    #[test]
    fn invert_edge_test() {
        let i1 = wrap(AigNode::Input(1));
        let i2 = wrap(AigNode::Input(2));
        let a3 = wrap(AigNode::and(3, edge(i1.clone()), edge(i2.clone())));
        let l4 = wrap(AigNode::latch(4, edge(a3.clone()), None));

        assert!(!a3.borrow_mut().get_fanins()[0].complement);
        assert!(!a3.borrow_mut().get_fanins()[1].complement);

        assert!(a3.borrow_mut().invert_edge(1).is_ok());
        assert!(a3.borrow_mut().get_fanins()[0].complement);
        assert!(!a3.borrow_mut().get_fanins()[1].complement);

        assert!(a3.borrow_mut().invert_edge(2).is_ok());
        assert!(a3.borrow_mut().get_fanins()[0].complement);
        assert!(a3.borrow_mut().get_fanins()[1].complement);

        assert!(a3.borrow_mut().invert_edge(99).is_err());

        assert!(!l4.borrow_mut().get_fanins()[0].complement);

        assert!(l4.borrow_mut().invert_edge(3).is_ok());

        assert!(l4.borrow_mut().get_fanins()[0].complement);
        assert!(l4.borrow_mut().invert_edge(99).is_err());

        let nf = wrap(AigNode::False);
        assert!(nf.borrow_mut().invert_edge(1).is_err());

        let i5 = wrap(AigNode::Input(5));
        assert!(i5.borrow_mut().invert_edge(1).is_err());
    }

    #[test]
    fn reorder_fanins_test() {
        let i1 = wrap(AigNode::Input(1));
        let i2 = wrap(AigNode::Input(2));
        let a5 = wrap(AigNode::and(5, edge(i1.clone()), edge(i2.clone())));
        let l3 = wrap(AigNode::latch(3, edge(a5.clone()), None));
        let a6 = wrap(AigNode::and(6, edge(a5.clone()), edge(l3.clone())));
        let a7 = wrap(AigNode::and(7, edge(a5.clone()), edge(a6.clone())));

        // Copy that we are not going to modify
        let b1 = wrap(AigNode::Input(1));
        let b2 = wrap(AigNode::Input(2));
        let b5 = wrap(AigNode::and(5, edge(b1.clone()), edge(b2.clone())));
        let b3 = wrap(AigNode::latch(3, edge(b5.clone()), None));
        let b6 = wrap(AigNode::and(6, edge(b5.clone()), edge(b3.clone())));

        // Fanins swapped
        a7.borrow_mut().reorder_fanins();
        assert_eq!(
            a7,
            wrap(AigNode::and(7, edge(b6.clone()), edge(b5.clone())))
        );

        // Fanins not swapped
        a6.borrow_mut().reorder_fanins();
        assert_eq!(a6, b6);

        // Fanins swapped
        a5.borrow_mut().reorder_fanins();
        assert_eq!(
            a5,
            wrap(AigNode::and(5, edge(b2.clone()), edge(b1.clone())))
        );
    }
}
