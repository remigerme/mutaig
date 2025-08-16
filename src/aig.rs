//! Module defining the [`Aig`] struct, as well as [`AigNode`], [`AigEdge`] and some others relevant structs.
//!
//! To start proving combinational equivalence, check [`crate::cnf`] and [`crate::miter::Miter`] docs.

mod clone;
pub mod dfs;
pub mod dot;
pub mod edge;
pub mod error;
mod integrity;
pub mod node;
mod parser;

use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    ops::Deref,
    rc::Rc,
};

pub use edge::{AigEdge, FaninId};
pub use error::{AigError, Result};
pub(crate) use node::AigNodeWeak;
pub use node::{AigNode, AigNodeRef, NodeId};

/// A whole AIG.
///
/// Nodes are kept alive artificially to allow rewrites of the structure.
/// Once you are done with rewriting (ie, your AIG should now be in a relevant state), you can
/// call the [`.update()`] method to remove all unused nodes.
///
/// For example, if you just created a node using [`.new_and(id, fanin0, fanin1)`], this node isn't used as a fanin to any
/// other node for now. It won't be deleted directly (fortunately!). But if after finishing your rewrite you
/// call [`.update()`] and the node still is not used by any other node, then, it will get deleted.
///
/// [`.update()`]: Aig::update
/// [`.new_and(id, fanin0, fanin1)`]: Aig::new_and
///
/// The use of [`Rc`] and [`AigNodeRef`] allows us not to worry about having to drop manually nodes
/// that are no longer used, eg. nodes that were used before by node `A` as their `fanin0`,
/// but `A` is rewritten to use another `fanin0`.
///
/// Note that [`Aig::clone`] will perform a shallow copy of the AIG (the nodes won't be copied).
/// If you want to recursively clone the data structure (ie not incrementing Rc
/// but creating new nodes), use [`Aig::deep_clone`] instead.
#[derive(Debug, Clone)]
pub struct Aig {
    nodes: HashMap<NodeId, AigNodeWeak>,
    /// Inputs must be kept artificially alive as
    /// we don't want to remove them even if the outputs do not depend on them.
    inputs: HashMap<NodeId, AigNodeRef>,
    /// Latches must be kept artificially alive as
    /// we don't want to remove them even if the outputs do not depend on them.
    latches: HashMap<NodeId, AigNodeRef>,
    outputs: Vec<AigEdge>,
    keep_nodes_alive: Vec<AigNodeRef>,
    // Keep alive node false.
    _node_false: AigNodeRef,

    /// Strashing
    /// ---------
    /// For more information on strashing, check "Robust boolean reasoning for equivalence checking" by Kuehlmann et al.
    ///
    /// This map allows for strashing. Moreover, we still need to be able to refer to nodes
    /// that might have not been instantiated because of strashing. For example:
    ///
    /// Current AIG  | Node to add  
    ///     3        |      4
    ///    / \       |     / \
    ///   1   2      |    2   1
    ///
    /// We are not going to create a new node. Instead, we just want to create a link from id 4 to node 3.
    /// This is done using [`Aig::strash_repr`].
    ///
    /// Technical details:
    /// - [`AigEdge`] are not used directly to not keep nodes alive artificially
    /// - whenever a node is updated, [`Aig::strash_map`] must be updated accordingly
    /// - the same goes for [`Aig::strash_repr`].
    strash_map: HashMap<((NodeId, bool), (NodeId, bool)), AigNodeWeak>,
    strash_repr: HashMap<NodeId, AigNodeWeak>,
}

impl Aig {
    /// Create a brand new AIG (constant node [`AigNode::False`] included).
    pub fn new() -> Self {
        let node_false = Rc::new(RefCell::new(AigNode::False));
        let nodes = HashMap::from([(0, Rc::downgrade(&node_false))]);
        Aig {
            nodes,
            inputs: HashMap::new(),
            latches: HashMap::new(),
            outputs: Vec::new(),
            keep_nodes_alive: Vec::new(),
            _node_false: node_false,
            strash_map: HashMap::new(),
            strash_repr: HashMap::new(),
        }
    }

    /// Retrieves a node from its id.
    ///
    /// The returned node might have a different id, this is because of strashing.
    /// For more information, check internal docs of [`Aig`].
    pub fn get_node(&self, id: NodeId) -> Option<AigNodeRef> {
        if let Some(node) = self.strash_repr.get(&id) {
            node.upgrade()
        } else {
            self.nodes.get(&id)?.upgrade()
        }
    }

    /// Call this function when you are done with your rewrite.
    /// All nodes that are not part of the AIG anymore (ie not reachable from an output) will be deleted.
    pub fn update(&mut self) {
        // Stop keeping nodes artificially alive
        self.keep_nodes_alive.clear();

        // Removing no longer valid entries from the nodes
        self.nodes
            .retain(|_, weak_node| weak_node.upgrade().is_some());
        self.strash_map.retain(|_, weak| weak.upgrade().is_some());
        self.strash_repr.retain(|_, weak| weak.upgrade().is_some());
    }

    /// Retrieves inputs reference.
    pub fn get_inputs(&self) -> Vec<AigNodeRef> {
        self.inputs.values().cloned().collect()
    }

    /// Retrieves inputs id.
    pub fn get_inputs_id(&self) -> HashSet<NodeId> {
        self.inputs.keys().copied().collect()
    }

    /// Retrieves latches reference.
    pub fn get_latches(&self) -> Vec<AigNodeRef> {
        self.latches.values().cloned().collect()
    }

    /// Retrieves latches id.
    pub fn get_latches_id(&self) -> HashSet<NodeId> {
        self.latches.keys().copied().collect()
    }

    /// Retrieves outputs reference.
    pub fn get_outputs(&self) -> Vec<AigEdge> {
        self.outputs.clone()
    }

    fn topological_visit(
        &self,
        node: AigNodeRef,
        sort: &mut Vec<AigNodeRef>,
        seen: &mut HashSet<NodeId>,
        done: &mut HashSet<NodeId>,
        outputs_to_visit: &mut Vec<AigNodeRef>,
    ) -> Result<()> {
        let mut stack: Vec<(AigNodeRef, bool)> = Vec::new();
        stack.push((node, false));

        while let Some((node, last_time)) = stack.pop() {
            let id = node.borrow().get_id();

            // Post order check
            if last_time {
                done.insert(id);
                sort.push(node);
                continue;
            }

            if done.contains(&id) {
                return Ok(());
            } else if seen.contains(&id) {
                return Err(AigError::InvalidState("found a cycle".to_string()));
            }

            seen.insert(id);
            stack.push((node.clone(), true));

            // Time to add potential fanins
            match node.borrow().deref() {
                // For latches, we don't want to detect "cycles" so we add their fanins
                // to the list of outputs to visit for later.
                AigNode::Latch { next, .. } => {
                    if !done.contains(&next.get_node_id()) {
                        outputs_to_visit.push(next.get_node());
                    }
                }
                // For and gates, we simply keep going on the DFS.
                AigNode::And { fanin0, fanin1, .. } => {
                    for fanin in [fanin0, fanin1] {
                        if !done.contains(&fanin.get_node_id()) {
                            stack.push((fanin.get_node(), false));
                        }
                    }
                }
                _ => (),
            }
        }

        Ok(())
    }

    /// Returns a topological sort of the AIG nodes, will error if a cycle is detected.
    ///
    /// The "topological" sort makes sense only for the purely combinational part of the AIG,
    /// ie only without latches. Indeed, latches are allowed to create cycles through their next-state fanin.
    pub fn get_topological_sort(&self) -> Result<Vec<AigNodeRef>> {
        let mut sort = Vec::new();
        let mut seen = HashSet::new();
        let mut done = HashSet::new();
        let mut outputs_to_visit = self
            .outputs
            .iter()
            .map(|output| output.get_node())
            .collect::<Vec<AigNodeRef>>();

        while let Some(node) = outputs_to_visit.pop() {
            self.topological_visit(node, &mut sort, &mut seen, &mut done, &mut outputs_to_visit)?;
        }
        Ok(sort)
    }

    fn check_valid_node_to_add(&self, node: &AigNode) -> Result<()> {
        match node {
            AigNode::False => Ok(()),
            AigNode::Input(id) => {
                if *id == 0 {
                    Err(AigError::IdZeroButNotFalse)
                } else {
                    Ok(())
                }
            }
            AigNode::And {
                id, fanin0, fanin1, ..
            } => {
                if *id == 0 {
                    Err(AigError::IdZeroButNotFalse)
                } else {
                    let fanin0_id = fanin0.get_node_id();
                    let fanin1_id = fanin1.get_node_id();
                    if self.get_node(fanin0_id).is_none() {
                        Err(AigError::NodeDoesNotExist(fanin0_id))
                    } else if self.get_node(fanin1_id).is_none() {
                        Err(AigError::NodeDoesNotExist(fanin1_id))
                    } else {
                        Ok(())
                    }
                }
            }
            AigNode::Latch { id, next, .. } => {
                if *id == 0 {
                    Err(AigError::IdZeroButNotFalse)
                } else {
                    let next_id = next.get_node_id();
                    if self.get_node(next_id).is_none() {
                        Err(AigError::NodeDoesNotExist(next_id))
                    } else {
                        Ok(())
                    }
                }
            }
        }
    }

    /// Create a new (or retrieve existing) node within the AIG.
    /// This will fail if a different node with the same id already exists in the AIG,
    /// or if a node uses id 0 (reserved for constant node [`AigNode::False`]).
    ///
    /// ```rust
    /// use mutaig::{Aig, AigEdge, AigNode};
    /// let mut aig = Aig::new();
    /// let node_false = aig.add_node(AigNode::False).unwrap();
    /// let i1 = aig.add_node(AigNode::Input(1)).unwrap();
    /// let i1_ = aig.add_node(AigNode::Input(1)).unwrap(); // will simply retrieve the existing node
    /// assert_eq!(i1, i1_);
    ///
    /// let and_gate =
    ///     aig.add_node(AigNode::and(
    ///         2,
    ///         AigEdge::new(i1.clone(), false),
    ///         AigEdge::new(i1.clone(), true)
    ///     )).unwrap(); // represent i1 ^ !i1 so will be false all the time (just an example)
    ///
    /// // Some stuff we cannot do
    /// // Node with id 0
    /// assert!(aig.add_node(AigNode::Input(0)).is_err());
    /// // Id 1 is already taken by an input
    /// assert!(
    ///     aig.add_node(AigNode::and(
    ///         1,
    ///         AigEdge::new(i1.clone(), false),
    ///         AigEdge::new(i1.clone(), false)
    ///     ))
    ///     .is_err()
    /// );
    /// ```
    pub fn add_node(&mut self, node: AigNode) -> Result<AigNodeRef> {
        self.check_valid_node_to_add(&node)?;

        let id = node.get_id();
        match self.get_node(id) {
            // We're adding a node not existing yet, let's create a new
            // apart from AND gates that might get strashed.
            None => {
                let n = Rc::new(RefCell::new(node));
                let real_n = match n.clone().borrow().deref() {
                    AigNode::False => n,
                    AigNode::Input(_) => self.inputs.insert(id, n.clone()).unwrap_or(n),
                    AigNode::Latch { .. } => self.latches.insert(id, n.clone()).unwrap_or(n),
                    AigNode::And { fanin0, fanin1, .. } => {
                        // Trivial cases of strashing
                        if fanin0.is_cst_false() {
                            self.strash_repr
                                .insert(id, Rc::downgrade(&self._node_false));
                            return Ok(self._node_false.clone());
                        } else if fanin1.is_cst_false() {
                            self.strash_repr
                                .insert(id, Rc::downgrade(&self._node_false));
                            return Ok(self._node_false.clone());
                        } else if fanin0.is_cst_true() {
                            if !fanin1.get_complement() {
                                self.strash_repr
                                    .insert(id, Rc::downgrade(&fanin1.get_node()));
                                return Ok(fanin1.get_node());
                            } else {
                                // todo!()
                            }
                        } else if fanin1.is_cst_true() {
                            if !fanin0.get_complement() {
                                self.strash_repr
                                    .insert(id, Rc::downgrade(&fanin0.get_node()));
                                return Ok(fanin0.get_node());
                            } else {
                                // todo!()
                            }
                        } else if fanin0 == fanin1 {
                            if !fanin0.get_complement() {
                                self.strash_repr
                                    .insert(id, Rc::downgrade(&fanin0.get_node()));
                                return Ok(fanin0.get_node());
                            } else {
                                // todo!()
                            }
                        } else if fanin0.is_complement_of(fanin1) {
                            self.strash_repr
                                .insert(id, Rc::downgrade(&self._node_false));
                            return Ok(self._node_false.clone());
                        }

                        // Existing strashed node
                        if let Some(weak) = self.strash_map.get(&(fanin0.into(), fanin1.into())) {
                            self.strash_repr.insert(id, weak.clone());
                            return Ok(weak.upgrade().unwrap());
                        }

                        // If we end up here, we are going to create a brand new node
                        fanin0
                            .get_node()
                            .borrow_mut()
                            .add_fanout(id, Rc::downgrade(&n));
                        fanin1
                            .get_node()
                            .borrow_mut()
                            .add_fanout(id, Rc::downgrade(&n));
                        n.clone()
                    }
                };

                // Warning, in case of strashing, id != real_n.id
                // so we must have early returned at this point.
                self.nodes.insert(id, Rc::downgrade(&real_n));
                self.keep_nodes_alive.push(real_n.clone());

                Ok(real_n)
            }
            // A node was found, maybe it is just the one we're trying to create,
            // note that it could also be an AND gate with a different id because of strashing,
            // in that case we just compare fanins.
            Some(n) => (*n.borrow() == node || n.borrow().strashable(&node))
                .then(|| n.clone())
                .ok_or(AigError::DuplicateId(id)),
        }
    }

    /// Create a new and node (or retrieve it if the exact same node already exists).
    pub fn new_and(&mut self, id: NodeId, fanin0: AigEdge, fanin1: AigEdge) -> Result<AigNodeRef> {
        let candidate = AigNode::and(id, fanin0, fanin1);
        self.add_node(candidate)
    }

    /// Mark an existing node as an output.
    pub fn add_output(&mut self, id: NodeId, complement: bool) -> Result<()> {
        let node = self.get_node(id).ok_or(AigError::NodeDoesNotExist(id))?;
        self.outputs.push(AigEdge::new(node, complement));
        Ok(())
    }

    /// Remove a fanin from the outputs. Do not error if node refered by fanin does not exist
    /// or if fanin was not an output, simply returns None instead of the node.
    pub fn remove_output(&mut self, id: NodeId, complement: bool) -> Option<AigNodeRef> {
        let node = self.get_node(id)?;
        let output = AigEdge::new(node.clone(), complement);
        let len_before = self.outputs.len();
        self.outputs.retain(|out| *out != output);
        if self.outputs.len() < len_before {
            Some(node)
        } else {
            None
        }
    }

    /// Replace the given fanin of a node by a new fanin.
    /// Both nodes need to already exist in the AIG.
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

        let weak_parent = Rc::downgrade(&parent);
        parent.borrow_mut().set_fanin(&fanin, fanin_id, weak_parent)
    }

    /// Replace a node by another existing node.
    /// Both nodes need to already exist in the AIG.
    pub fn replace_node(&mut self, old_id: NodeId, id: NodeId, complement: bool) -> Result<()> {
        // We also need to keep the map of nodes updated
        let old = self
            .nodes
            .remove(&old_id)
            .ok_or(AigError::NodeDoesNotExist(old_id))?
            .upgrade()
            .ok_or(AigError::InvalidState(format!(
                "node {} is no longer valid",
                old_id
            )))?;

        let new = self
            .nodes
            .get(&id)
            .ok_or(AigError::NodeDoesNotExist(id))?
            .upgrade()
            .ok_or(AigError::InvalidState(format!(
                "node {} is no longer valid",
                id
            )))?;

        assert!(old.borrow().is_and());

        let fanouts: Vec<AigNodeRef> = old
            .borrow()
            .get_and_fanouts()
            .unwrap()
            .iter()
            .filter_map(|(_, fanout_weak)| fanout_weak.upgrade())
            .collect();

        for fanout in fanouts {
            let fanout_weak = Rc::downgrade(&fanout);
            let fanins_of_fanout = fanout.borrow().get_fanins();

            let mut fanin_id = 0;
            for fanin_of_fanout in fanins_of_fanout {
                if fanin_of_fanout.get_node_id() == old_id {
                    let old_compl = fanin_of_fanout.get_complement();
                    let new_fanin = AigEdge::new(new.clone(), old_compl ^ complement);
                    fanout.borrow_mut().set_fanin(
                        &new_fanin,
                        FaninId::from(fanin_id),
                        fanout_weak.clone(),
                    )?;
                }
                fanin_id += 1;
            }
        }
        for output in &mut self.outputs {
            if output.get_node_id() == old_id {
                output.node = new.clone();
                output.complement = output.complement ^ complement;
            }
        }

        old.borrow_mut().clear_fanouts();

        Ok(())
    }

    fn minimize_ids_visit(
        &self,
        node: AigNodeRef,
        new_nodes: &mut Vec<AigNodeRef>,
        done: &mut HashSet<NodeId>,
    ) -> Result<()> {
        let mut stack: Vec<(AigNodeRef, bool)> = Vec::new();
        stack.push((node, false));

        while let Some((node, last_time)) = stack.pop() {
            let id = node.borrow().get_id();

            // Post order check
            if last_time {
                done.insert(id);
                if node.borrow().is_and() {
                    new_nodes.push(node);
                }
                continue;
            }

            if done.contains(&id) {
                continue;
            }

            stack.push((node.clone(), true));

            let mut fanins = node.borrow().get_fanins();
            fanins.sort_unstable_by_key(|fanin| fanin.get_node_id());

            for fanin in fanins {
                if !done.contains(&fanin.get_node_id()) {
                    stack.push((fanin.get_node(), false));
                }
            }
        }

        Ok(())
    }

    /// Minimize ids of gates (as they would be stored in AIGER format):
    /// - check false node exists
    /// - check inputs and latches are in order
    /// - minimize ids of AND gates to match their id in AIGER format
    ///
    /// Internally relying on a DFS on lower CertifId to ensure reproducibility (see ABC).
    pub fn minimize_ids(&mut self) -> Result<()> {
        self.update();

        // All inputs and latches should be there
        let i = self.inputs.len() as u64;
        let l = self.latches.len() as u64;

        // Checking constant node
        if self.get_node(0).map(|n| n.borrow().is_false()) != Some(true) {
            return Err(AigError::NodeDoesNotExist(0));
        }
        // Checking inputs
        for k in 0..i {
            if self.get_node(1 + k).map(|n| n.borrow().is_input()) != Some(true) {
                return Err(AigError::NodeDoesNotExist(1 + k));
            }
        }
        // Checking latches
        for k in 0..l {
            if self.get_node(1 + i + k).map(|n| n.borrow().is_latch()) != Some(true) {
                return Err(AigError::NodeDoesNotExist(1 + i + k));
            }
        }

        // We need to renumber the AND gates.
        // Performing the DFS on lower ids first.
        let mut new_nodes = Vec::new();
        let mut seen = HashSet::new();
        let mut outputs_to_visit = self
            .outputs
            .iter()
            .map(|output| output.get_node())
            .collect::<Vec<AigNodeRef>>();
        outputs_to_visit.sort_unstable_by_key(|node| node.borrow().get_id());

        while let Some(node) = outputs_to_visit.pop() {
            self.minimize_ids_visit(node, &mut new_nodes, &mut seen)?;
        }

        // Updating ids and map
        // Also making sure fanins are correctly ordered (fanin0 >= fanin1)
        let mut new_nodes_map = self.nodes.clone();
        new_nodes_map.retain(|id, _| *id < 1 + i + l); // keeping only inputs and latches (and constant node)
        let mut idx = 1 + i + l;
        for node in new_nodes {
            new_nodes_map.insert(idx, Rc::downgrade(&node));
            node.borrow_mut().set_id(idx)?;
            node.borrow_mut().reorder_fanins();

            idx += 1;
        }
        self.nodes = new_nodes_map;

        // Reconstructing fanouts
        // This is needed because the loop above might destroy proper fanouts
        // Let's consider the situation
        // A   B
        //  \ /
        //   C
        // where id of A is going to be set to id of B and assuming A is first in topological order
        // when id of A is set to id(B), the fanout from C to A is updated
        // but during the update it replaces the fanout from C to B, overwriting it
        // and then when id of B is rewritten to something else, the fanout from C to A
        // is again rewritten to fanout from C to B. It basically destroys everything.
        for (&id, weak) in &self.nodes {
            let node = weak.upgrade().unwrap();
            match node.borrow().deref() {
                AigNode::False | AigNode::Input(_) => (),
                AigNode::Latch { next, .. } => {
                    next.get_node().borrow_mut().add_fanout(id, weak.clone())
                }
                AigNode::And { fanin0, fanin1, .. } => {
                    fanin0.get_node().borrow_mut().add_fanout(id, weak.clone());
                    fanin1.get_node().borrow_mut().add_fanout(id, weak.clone());
                }
            }
        }

        self.check_integrity()?;
        self.check_valid_aiger()
    }
}

impl PartialEq for Aig {
    /// Compares the two AIGs. They are equal iff:
    /// - their inputs are equal (in terms of set)
    /// - their outputs are equal
    /// - their latches are equal
    /// - their valid nodes are equal.
    fn eq(&self, other: &Self) -> bool {
        self.outputs == other.outputs
            && self.inputs == other.inputs
            && self.latches == other.latches
            && true
            && self
                .nodes
                .iter()
                .filter_map(|(&id, weak)| Some((id, weak.upgrade()?)))
                .collect::<HashMap<NodeId, AigNodeRef>>()
                == other
                    .nodes
                    .iter()
                    .filter_map(|(&id, weak)| Some((id, weak.upgrade()?)))
                    .collect::<HashMap<NodeId, AigNodeRef>>()
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn add_node_test() {
        let mut aig = Aig::new();

        // Adding legit nodes
        let nf = AigNode::False;
        let rnf = aig.add_node(nf.clone()).unwrap();
        assert_eq!(*rnf.borrow(), nf);
        let i1 = AigNode::Input(1);
        let ri1 = aig.add_node(i1.clone()).unwrap();
        assert_eq!(*ri1.borrow(), i1);
        let a2 = AigNode::and(
            2,
            AigEdge::new(rnf.clone(), false),
            AigEdge::new(ri1.clone(), false),
        );
        let ra2 = aig.add_node(a2.clone()).unwrap();
        assert_eq!(*ra2.borrow(), a2);

        // Now, trying to add some illegal nodes
        assert!(aig.add_node(AigNode::Input(2)).is_err());
        assert!(
            aig.add_node(AigNode::and(
                1,
                AigEdge::new(rnf.clone(), false),
                AigEdge::new(rnf.clone(), false)
            ))
            .is_err()
        );

        // Trying to re-add existing nodes (legal)
        assert_eq!(*aig.add_node(nf.clone()).unwrap().borrow(), nf);
        assert_eq!(*aig.add_node(i1.clone()).unwrap().borrow(), i1);
        assert_eq!(*aig.add_node(a2.clone()).unwrap().borrow(), a2);
    }

    #[test]
    fn add_node_test_invalid_input_id0() {
        let mut a = Aig::new();
        assert!(a.add_node(AigNode::Input(0)).is_err());
        // You should use constructors instead of doing this anyway.
        assert!(
            a.add_node(AigNode::Latch {
                id: 0,
                next: AigEdge::new(a.get_node(0).unwrap(), false),
                init: None
            })
            .is_err()
        );
        assert!(
            a.add_node(AigNode::And {
                id: 0,
                fanin0: AigEdge::new(a.get_node(0).unwrap(), false),
                fanin1: AigEdge::new(a.get_node(0).unwrap(), false),
                fanouts: HashMap::new()
            })
            .is_err()
        );
    }

    #[test]
    fn add_node_test_invalid_dependency() {
        // Warning: false is included
        let mut a = Aig::new();

        let fake_input = Rc::new(RefCell::new(AigNode::Input(1)));
        assert!(
            a.add_node(AigNode::and(
                1,
                AigEdge::new(fake_input.clone(), false),
                AigEdge::new(fake_input.clone(), false),
            ))
            .is_err()
        );

        assert!(
            a.add_node(AigNode::latch(
                1,
                AigEdge::new(fake_input.clone(), false),
                None
            ))
            .is_err()
        );
    }

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
        assert_ne!(e1, e3);

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

        // Manipulating the AIG without saving output
        assert_eq!(
            *aig.add_node(AigNode::False).unwrap().borrow(),
            AigNode::False
        );
        assert_eq!(
            *aig.add_node(AigNode::Input(1)).unwrap().borrow(),
            AigNode::Input(1)
        );
        assert_eq!(*aig.get_node(0).unwrap().borrow(), AigNode::False);
        assert_eq!(*aig.get_node(1).unwrap().borrow(), AigNode::Input(1));
        aig.update();
        assert!(aig.get_node(0).is_some()); // false does not get deleted
        assert!(aig.get_node(1).is_some()); // inputs do not get deleted

        // Now let's save the output
        assert_eq!(
            *aig.add_node(AigNode::False).unwrap().borrow(),
            AigNode::False
        );
        assert_eq!(
            *aig.add_node(AigNode::Input(1)).unwrap().borrow(),
            AigNode::Input(1)
        );
        let a2 = AigNode::and(
            2,
            AigEdge::new(aig.get_node(0).unwrap(), false),
            AigEdge::new(aig.get_node(1).unwrap(), false),
        );
        assert_eq!(*aig.add_node(a2.clone()).unwrap().borrow(), a2);
        assert_eq!(*aig.get_node(0).unwrap().borrow(), AigNode::False);
        assert_eq!(*aig.get_node(1).unwrap().borrow(), AigNode::Input(1));
        assert_eq!(*aig.get_node(2).unwrap().borrow(), a2);
        assert!(aig.add_output(2, true).is_ok());
        aig.update();
        assert_eq!(*aig.get_node(0).unwrap().borrow(), AigNode::False);
        assert_eq!(*aig.get_node(1).unwrap().borrow(), AigNode::Input(1));
        assert_eq!(*aig.get_node(2).unwrap().borrow(), a2);

        assert!(aig.remove_output(2, false).is_none());
        assert_eq!(*aig.remove_output(2, true).unwrap().borrow(), a2);
        drop(a2); // making sure a2 doesn't exist elsewhere
        aig.update();
        assert!(aig.get_node(0).is_some()); // false node does not get deleted
        assert!(aig.get_node(1).is_some()); // inputs do not get deleted
        assert!(aig.get_node(2).is_none());

        // Now let's create the following AIG
        //   A1  A2
        //  / \ / \
        // I1  I2  I3
        // If A1 is not an output, then A1 should be cleared (but I1 is kept alive)
        // and if A2 is an output, then A2, I2, I3 will be kept alive
        let mut aig = Aig::new();
        aig.add_node(AigNode::Input(1)).unwrap();
        aig.add_node(AigNode::Input(2)).unwrap();
        aig.add_node(AigNode::Input(3)).unwrap();
        aig.add_node(AigNode::and(
            4,
            AigEdge::new(aig.get_node(1).unwrap(), false),
            AigEdge::new(aig.get_node(2).unwrap(), false),
        ))
        .unwrap();
        aig.add_node(AigNode::and(
            5,
            AigEdge::new(aig.get_node(2).unwrap(), false),
            AigEdge::new(aig.get_node(3).unwrap(), false),
        ))
        .unwrap();
        aig.add_output(5, false).unwrap();
        aig.update();
        assert!(aig.get_node(1).is_some());
        assert!(aig.get_node(4).is_none());
        assert!(aig.get_node(2).is_some());
        assert!(aig.get_node(3).is_some());
        assert!(aig.get_node(5).is_some());
    }

    #[test]
    fn aig_eq_test() {
        let mut a = Aig::new();
        let a1 = a.add_node(AigNode::Input(1)).unwrap();
        let a2 = a.add_node(AigNode::Input(2)).unwrap();
        let a3 = a
            .add_node(AigNode::and(
                3,
                AigEdge::new(a1.clone(), false),
                AigEdge::new(a2.clone(), false),
            ))
            .unwrap();
        let _a4 = a.add_node(AigNode::latch(4, AigEdge::new(a3.clone(), true), None));
        // Do not save the node - or drop it explicitly later
        a.add_node(AigNode::and(
            5,
            AigEdge::new(a1.clone(), true),
            AigEdge::new(a2.clone(), true),
        ))
        .unwrap();
        a.add_output(4, false).unwrap();

        let mut b = Aig::new();
        let b1 = b.add_node(AigNode::Input(1)).unwrap();
        let b2 = b.add_node(AigNode::Input(2)).unwrap();
        let b3 = b
            .add_node(AigNode::and(
                3,
                AigEdge::new(b1.clone(), false),
                AigEdge::new(b2.clone(), false),
            ))
            .unwrap();
        let _b4 = b.add_node(AigNode::latch(4, AigEdge::new(b3.clone(), true), None));
        b.add_output(4, false).unwrap();

        a.update();
        b.update();

        assert_eq!(a, b);
    }

    #[test]
    fn aig_eq_commuted_fanins() {
        let mut a = Aig::new();
        let mut b = Aig::new();

        let a1 = a.add_node(AigNode::Input(1)).unwrap();
        let b2 = b.add_node(AigNode::Input(2)).unwrap();

        assert_ne!(a, b);

        let a2 = a.add_node(AigNode::Input(2)).unwrap();
        let b1 = b.add_node(AigNode::Input(1)).unwrap();

        assert_eq!(a, b);

        let _a3 = a
            .add_node(AigNode::and(
                3,
                AigEdge::new(a1.clone(), false),
                AigEdge::new(a2.clone(), false),
            ))
            .unwrap();
        let _b3 = b
            .add_node(AigNode::and(
                3,
                AigEdge::new(b2.clone(), false),
                AigEdge::new(b1.clone(), false),
            ))
            .unwrap();

        // Order of fanins are not relevant
        assert_eq!(a, b);
    }

    #[test]
    fn aig_neq_test() {
        // Complemented outputs
        let mut a1 = Aig::new();
        let mut a2 = Aig::new();
        a1.add_node(AigNode::Input(1)).unwrap();
        a2.add_node(AigNode::Input(1)).unwrap();
        a1.add_output(1, false).unwrap();
        a2.add_output(1, true).unwrap();
        assert_ne!(a1, a2);

        // Different number of outputs
        let mut a3 = Aig::new();
        let mut a4 = Aig::new();
        a3.add_node(AigNode::Input(1)).unwrap();
        a3.add_node(AigNode::Input(2)).unwrap();
        a4.add_node(AigNode::Input(1)).unwrap();
        a4.add_node(AigNode::Input(2)).unwrap();
        a3.add_output(1, false).unwrap();
        a4.add_output(1, false).unwrap();
        a4.add_output(2, false).unwrap();
        assert_ne!(a3, a4);

        // Different inputs
        let mut a5 = Aig::new();
        let mut a6 = Aig::new();
        a5.add_node(AigNode::Input(1)).unwrap();
        a6.add_node(AigNode::Input(2)).unwrap(); // Different input id
        assert_ne!(a5, a6);

        // Different latches
        let mut a7 = Aig::new();
        let mut a8 = Aig::new();
        let i1_a7 = a7.add_node(AigNode::Input(1)).unwrap();
        let i1_a8 = a8.add_node(AigNode::Input(1)).unwrap();
        a7.add_node(AigNode::latch(2, AigEdge::new(i1_a7.clone(), false), None))
            .unwrap();
        a8.add_node(AigNode::latch(2, AigEdge::new(i1_a8.clone(), true), None))
            .unwrap();
        assert_ne!(a7, a8);

        // Different AND gates
        let mut a9 = Aig::new();
        let mut a10 = Aig::new();
        let i1_a9 = a9.add_node(AigNode::Input(1)).unwrap();
        let i2_a9 = a9.add_node(AigNode::Input(2)).unwrap();
        let i1_a10 = a10.add_node(AigNode::Input(1)).unwrap();
        let i2_a10 = a10.add_node(AigNode::Input(2)).unwrap();
        a9.add_node(AigNode::and(
            3,
            AigEdge::new(i1_a9.clone(), false),
            AigEdge::new(i2_a9.clone(), false),
        ))
        .unwrap();
        a10.add_node(AigNode::and(
            3,
            AigEdge::new(i1_a10.clone(), true),
            AigEdge::new(i2_a10.clone(), false),
        ))
        .unwrap(); // Different complement on fanin0
        a9.add_output(3, false).unwrap();
        a10.add_output(3, false).unwrap();
        assert_ne!(a9, a10);

        // Missing nodes after update
        let mut a11 = Aig::new();
        let mut a12 = Aig::new();
        let i1_a11 = a11.add_node(AigNode::Input(1)).unwrap();
        let i1_a12 = a12.add_node(AigNode::Input(1)).unwrap();
        let _and_a11 = a11
            .add_node(AigNode::and(
                2,
                AigEdge::new(i1_a11.clone(), false),
                AigEdge::new(i1_a11.clone(), false),
            ))
            .unwrap();
        let _and_a12 = a12
            .add_node(AigNode::and(
                2,
                AigEdge::new(i1_a12.clone(), false),
                AigEdge::new(i1_a12.clone(), false),
            ))
            .unwrap();
        a11.add_output(2, false).unwrap();
        // a12 doesn't use the AND gate as output, so it will be removed after update
        a11.update();
        a12.update();
        assert_ne!(a11, a12);
    }

    #[test]
    fn mut_id_test() {
        let mut aig = Aig::new();
        let i1 = aig.add_node(AigNode::Input(1)).unwrap();
        assert!(i1.borrow_mut().set_id(2).is_err()); // not allowed to rewrite input
        let i2 = aig.add_node(AigNode::Input(2)).unwrap();
        let a3 = aig
            .add_node(AigNode::and(
                3,
                AigEdge::new(i1.clone(), false),
                AigEdge::new(i2.clone(), false),
            ))
            .unwrap();
        let a4 = aig
            .add_node(AigNode::and(
                4,
                AigEdge::new(a3.clone(), false),
                AigEdge::new(i2.clone(), false),
            ))
            .unwrap();

        let a4_ = a4.clone();
        a3.borrow_mut().set_id(5).unwrap();
        assert_eq!(a4, a4_);
        assert!(aig.check_integrity().is_err()); // nodes map have not been updated
        aig.nodes.insert(5, Rc::downgrade(&a3));
        aig.nodes.remove(&3);
        assert!(aig.check_integrity().is_ok());
    }

    #[test]
    fn minimize_ids_test() {
        let mut a = Aig::new();
        let i1 = a.add_node(AigNode::Input(1)).unwrap();
        a.add_node(AigNode::Input(2)).unwrap(); // not used to check if kept alive
        let l3 = a
            .add_node(AigNode::latch(3, AigEdge::new(i1.clone(), true), None))
            .unwrap();
        let a8 = a
            .add_node(AigNode::and(
                8,
                AigEdge::new(i1.clone(), false),
                AigEdge::new(l3.clone(), false),
            ))
            .unwrap();
        let _a15 = a
            .add_node(AigNode::and(
                15,
                AigEdge::new(a8.clone(), false),
                AigEdge::new(i1.clone(), true),
            ))
            .unwrap();
        a.add_output(15, false).unwrap();
        a.minimize_ids().unwrap();

        let mut b = Aig::new();
        let b1 = b.add_node(AigNode::Input(1)).unwrap();
        b.add_node(AigNode::Input(2)).unwrap(); // not used to check if kept alive
        let b3 = b
            .add_node(AigNode::latch(3, AigEdge::new(b1.clone(), true), None))
            .unwrap();
        let b4 = b
            .add_node(AigNode::and(
                4,
                AigEdge::new(b3.clone(), false),
                AigEdge::new(b1.clone(), false),
            ))
            .unwrap();
        let _b5 = b
            .add_node(AigNode::and(
                5,
                AigEdge::new(b4.clone(), false),
                AigEdge::new(b1.clone(), true),
            ))
            .unwrap();
        b.add_output(5, false).unwrap();

        assert_eq!(a, b);
    }
}
