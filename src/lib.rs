pub mod cnf;
pub mod dfs;
pub mod miter;
mod parser;

use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    mem::swap,
    ops::Not,
    rc::{Rc, Weak},
};

use thiserror::Error;

use crate::miter::MiterError;

/// A node id.
///
/// The constant node [`AigNode::False`] has id 0 by convention. Also, id must be unique.
pub type NodeId = u64;

/// The result of an AIG operation.
pub type Result<T> = std::result::Result<T, AigError>;

/// Error returned when parsing from file failed.
#[derive(Debug, Error)]
pub enum ParserError {
    /// All features are not supported (only the basics in fact).
    #[error("unsupported feature: {0}")]
    UnsupportedFeature(String),

    /// Invalid token, something else was expected.
    #[error("invalid token: {0}")]
    InvalidToken(String),

    /// An IO error occured (file doesn't exist, or doesn't have the right extension, ...).
    #[error("io error: {0}")]
    IoError(String),
}

/// Error returned when an AIG operation failed.
#[derive(Debug, Error)]
pub enum AigError {
    /// A different node with the given id already exists.
    #[error("a different node with id={0} already exists")]
    DuplicateId(NodeId),

    /// The id 0 is reserved for the `False` constant node only.
    #[error("id=0 is for node False only")]
    IdZeroButNotFalse,

    /// The node with given id does not exist.
    #[error("node with id={0} does not exist")]
    NodeDoesNotExist(NodeId),

    /// Invalid operation on a node which does not have such specified fanin.
    /// Latches only have [`FaninId::Fanin0`].
    #[error("the node has no such fanin")]
    NoFanin,

    /// The AIG has reached an invalid state. This should never happen.
    /// For example, when tracking the nodes internally with the hashmap nodes,
    /// node `nodes[id]` should have id `id`. If this error is raised, my code is garbage.
    #[error("the AIG has reached an invalid state - this should not happen - error: {0}")]
    InvalidState(String),

    /// Just forwarding a [`MiterError`].
    ///
    /// [`MiterError`]: miter::MiterError
    #[error("{0}")]
    MiterError(#[from] MiterError),

    /// Just forwarding a [`ParserError`].
    #[error("{0}")]
    ParserError(#[from] ParserError),
}

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

/// An AIG node.
///
/// Each node has an id. By convention, id for constant node `False` is 0. The id must be unique.
#[derive(Debug, Clone, PartialEq, Eq)]
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

/// A non-counting reference to an AIG node - used internally.
type AigNodeWeak = Weak<RefCell<AigNode>>;

impl AigNode {
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

    /// **WARNING**
    ///
    /// You should ABSOLUTELY maintain the owning AIG structure invariants.
    /// Make sure you update the [`Aig::nodes`] map with the new id.
    ///
    /// This function was originally proposed to implement [`Aig::minimize_ids`].
    fn set_id(&mut self, id: NodeId) -> Result<()> {
        match self {
            AigNode::And { id: eid, .. } => Ok(*eid = id),
            _ => Err(AigError::InvalidState(format!(
                "you are trying to rewrite id of false/input/latch node with current id={}, there is no good reason you are trying to do that",
                self.get_id()
            ))),
        }
    }

    fn get_fanins(&self) -> Vec<AigEdge> {
        match self {
            AigNode::Latch { next, .. } => vec![next.clone()],
            AigNode::And { fanin0, fanin1, .. } => vec![fanin0.clone(), fanin1.clone()],
            _ => vec![],
        }
    }

    fn set_fanin(&mut self, fanin: &AigEdge, fanin_id: FaninId) -> Result<()> {
        match (self, fanin_id) {
            (AigNode::And { fanin0, .. }, FaninId::Fanin0) => Ok(*fanin0 = fanin.clone()),
            (AigNode::And { fanin1, .. }, FaninId::Fanin1) => Ok(*fanin1 = fanin.clone()),
            (AigNode::Latch { next, .. }, FaninId::Fanin0) => Ok(*next = fanin.clone()),
            _ => Err(AigError::NoFanin),
        }
    }

    /// Reorders fanins to make sure fanin0_id >= fanin1_id for AND gates.
    fn reorder_fanins(&mut self) {
        match self {
            AigNode::And { fanin0, fanin1, .. } => {
                let id0 = fanin0.get_node().borrow().get_id();
                let id1 = fanin1.get_node().borrow().get_id();
                if id0 < id1 {
                    swap(fanin0, fanin1);
                }
            }
            _ => (),
        }
    }
}

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
/// The use of [`Rc`] allows us not to worry about having to drop manually nodes that are no longer used, eg.
/// nodes that were used before by node `A` as their `fanin0`, but `A` is rewritten to use another `fanin0`.
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
        }
    }

    /// Retrieves a node from its id.
    pub fn get_node(&self, id: NodeId) -> Option<AigNodeRef> {
        self.nodes.get(&id)?.upgrade()
    }

    /// Call this function when you are done with your rewrite.
    /// All nodes that are not part of the AIG anymore (ie not reachable from an output) will be deleted.
    pub fn update(&mut self) {
        // Stop keeping nodes artificially alive
        self.keep_nodes_alive.clear();

        // Removing no longer valid entries from the nodes
        self.nodes
            .retain(|_, weak_node| weak_node.upgrade().is_some());
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

        while !stack.is_empty() {
            let (node, last_time) = stack.pop().unwrap();
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
            match &*node.borrow() {
                // For latches, we don't want to detect "cycles" so we add their fanins
                // to the list of outputs to visit for later.
                AigNode::Latch { next, .. } => {
                    if !done.contains(&next.get_node().borrow().get_id()) {
                        outputs_to_visit.push(next.get_node());
                    }
                }
                // For and gates, we simply keep going on the DFS.
                AigNode::And { fanin0, fanin1, .. } => {
                    for fanin in [fanin0, fanin1] {
                        if !done.contains(&fanin.get_node().borrow().get_id()) {
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

    fn check_valid_node_to_add(&self, node: AigNode) -> Result<()> {
        match node {
            AigNode::False => Ok(()),
            AigNode::Input(id) => {
                if id == 0 {
                    Err(AigError::IdZeroButNotFalse)
                } else {
                    Ok(())
                }
            }
            AigNode::And { id, fanin0, fanin1 } => {
                if id == 0 {
                    Err(AigError::IdZeroButNotFalse)
                } else {
                    let fanin0_id = fanin0.node.borrow().get_id();
                    let fanin1_id = fanin1.node.borrow().get_id();
                    if !self.nodes.contains_key(&fanin0_id) {
                        Err(AigError::NodeDoesNotExist(fanin0_id))
                    } else if !self.nodes.contains_key(&fanin1_id) {
                        Err(AigError::NodeDoesNotExist(fanin1_id))
                    } else {
                        Ok(())
                    }
                }
            }
            AigNode::Latch { id, next, .. } => {
                if id == 0 {
                    Err(AigError::IdZeroButNotFalse)
                } else {
                    let next_id = next.node.borrow().get_id();
                    if !self.nodes.contains_key(&next_id) {
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
    ///     aig.add_node(AigNode::And {
    ///         id: 2,
    ///         fanin0: AigEdge::new(i1.clone(), false),
    ///         fanin1: AigEdge::new(i1.clone(), true)
    ///     }).unwrap(); // represent i1 ^ !i1 so will be false all the time (just an example)
    ///
    /// // Some stuff we cannot do
    /// // Node with id 0
    /// assert!(aig.add_node(AigNode::Input(0)).is_err());
    /// // Id 1 is already taken by an input
    /// assert!(
    ///     aig.add_node(AigNode::And {
    ///         id: 1,
    ///         fanin0: AigEdge::new(i1.clone(), false),
    ///         fanin1: AigEdge::new(i1.clone(), false)
    ///     })
    ///     .is_err()
    /// );
    /// ```
    pub fn add_node(&mut self, node: AigNode) -> Result<AigNodeRef> {
        self.check_valid_node_to_add(node.clone())?;

        let id = node.get_id();
        match self.get_node(id) {
            // No node with this id, let's create a new one
            None => {
                let n: Rc<RefCell<AigNode>> = Rc::new(RefCell::new(node));
                self.nodes.insert(id, Rc::downgrade(&n));
                self.keep_nodes_alive.push(n.clone());
                // If the node is an input or a latch, we must add it to the map
                match *n.borrow() {
                    AigNode::Input(_) => self.inputs.insert(id, n.clone()),
                    AigNode::Latch { .. } => self.latches.insert(id, n.clone()),
                    _ => None,
                };
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

    /// Replace a node by another existing node.
    /// Both nodes need to already exist in the AIG.
    pub fn replace_node(&mut self, old_id: NodeId, id: NodeId, complement: bool) -> Result<()> {
        assert!(
            !complement,
            "Unsupported feature: cannot replace a node by a negated equivalent."
        );

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
            .remove(&id)
            .ok_or(AigError::NodeDoesNotExist(id))?
            .upgrade()
            .ok_or(AigError::InvalidState(format!(
                "node {} is no longer valid",
                id
            )))?;

        assert!(old.borrow().is_and());
        assert!(new.borrow().is_and());

        let fanins = new.borrow().get_fanins();

        old.borrow_mut().set_fanin(&fanins[0], FaninId::Fanin0)?;
        old.borrow_mut().set_fanin(&fanins[1], FaninId::Fanin1)?;
        old.borrow_mut().set_id(id)?;

        // Keeping the map updated
        self.nodes.insert(id, Rc::downgrade(&old));

        // If complement (ie the new node is the negation of the old one), we need to update its fanout
        // (potentially including outputs)
        // We're not supporting this yet - in practice such a rewrite never happens.

        Ok(())
    }

    fn minimize_ids_visit(
        &self,
        node: AigNodeRef,
        new_nodes: &mut Vec<AigNodeRef>,
        seen: &mut HashSet<NodeId>,
    ) -> Result<()> {
        let mut stack: Vec<AigNodeRef> = Vec::new();
        stack.push(node);

        while let Some(node) = stack.pop() {
            let id = node.borrow().get_id();

            if seen.contains(&id) {
                return Ok(());
            }
            seen.insert(id);

            let mut fanins = node.borrow().get_fanins();
            fanins.sort_unstable_by_key(|fanin| fanin.get_node().borrow().get_id());

            for fanin in fanins {
                if !seen.contains(&fanin.get_node().borrow().get_id()) {
                    stack.push(fanin.get_node());
                }
            }

            if node.borrow().is_and() {
                new_nodes.push(node);
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
        new_nodes.reverse();

        // Updating ids and map
        // Also making sure fanins are correctly ordered (fanin0 >= fanin1)
        let mut new_nodes_map = self.nodes.clone();
        new_nodes_map.retain(|id, _| *id < 1 + i + l); // keeping only inputs and latches
        let mut idx = 1 + i + l;
        for node in new_nodes {
            new_nodes_map.insert(idx, Rc::downgrade(&node));
            node.borrow_mut().set_id(idx)?;
            node.borrow_mut().reorder_fanins();

            idx += 1;
        }
        self.nodes = new_nodes_map;

        self.check_integrity()
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
            if self.get_node(output.node.borrow().get_id()).is_none() {
                return Err(AigError::InvalidState(
                    "output is not a node of the aig".to_string(),
                ));
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
        match &*node.borrow() {
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
            AigNode::And { id, fanin0, fanin1 } => {
                if *id == 0 {
                    return Err(AigError::IdZeroButNotFalse);
                }
                self.check_edge_integrity(fanin0)?;
                self.check_edge_integrity(fanin1)?;
            }
        }
        Ok(())
    }

    fn check_edge_integrity(&self, fanin: &AigEdge) -> Result<()> {
        self.get_node(fanin.node.borrow().get_id())
            .ok_or(AigError::InvalidState(
                "edge pointing at a node node in aig".to_string(),
            ))?;
        Ok(())
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
        let a2 = AigNode::And {
            id: 2,
            fanin0: AigEdge::new(rnf.clone(), false),
            fanin1: AigEdge::new(ri1.clone(), false),
        };
        let ra2 = aig.add_node(a2.clone()).unwrap();
        assert_eq!(*ra2.borrow(), a2);

        // Now, trying to add some illegal nodes
        assert!(aig.add_node(AigNode::Input(2)).is_err());
        assert!(
            aig.add_node(AigNode::And {
                id: 1,
                fanin0: AigEdge::new(rnf.clone(), false),
                fanin1: AigEdge::new(rnf.clone(), false)
            })
            .is_err()
        );

        // Trying to re-add existing nodes (legal)
        assert_eq!(*aig.add_node(nf.clone()).unwrap().borrow(), nf);
        assert_eq!(*aig.add_node(i1.clone()).unwrap().borrow(), i1);
        assert_eq!(*aig.add_node(a2.clone()).unwrap().borrow(), a2);
    }

    #[test]
    fn add_node_test_invalid_id0() {
        let mut a = Aig::new();
        // Even if False node does not exist in the AIG
        assert!(a.add_node(AigNode::Input(0)).is_err());
        let i1 = a.add_node(AigNode::Input(1)).unwrap();
        assert!(
            a.add_node(AigNode::And {
                id: 0,
                fanin0: AigEdge::new(i1.clone(), false),
                fanin1: AigEdge::new(i1.clone(), false)
            })
            .is_err()
        );
        assert!(
            a.add_node(AigNode::Latch {
                id: 0,
                next: AigEdge::new(i1.clone(), false),
                init: None
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
            a.add_node(AigNode::And {
                id: 1,
                fanin0: AigEdge::new(fake_input.clone(), false),
                fanin1: AigEdge::new(fake_input.clone(), false),
            })
            .is_err()
        );

        assert!(
            a.add_node(AigNode::Latch {
                id: 1,
                next: AigEdge::new(fake_input.clone(), false),
                init: None
            })
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
        let a2 = AigNode::And {
            id: 2,
            fanin0: AigEdge::new(aig.get_node(0).unwrap(), false),
            fanin1: AigEdge::new(aig.get_node(1).unwrap(), false),
        };
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
        aig.add_node(AigNode::And {
            id: 4,
            fanin0: AigEdge::new(aig.get_node(1).unwrap(), false),
            fanin1: AigEdge::new(aig.get_node(2).unwrap(), false),
        })
        .unwrap();
        aig.add_node(AigNode::And {
            id: 5,
            fanin0: AigEdge::new(aig.get_node(2).unwrap(), false),
            fanin1: AigEdge::new(aig.get_node(3).unwrap(), false),
        })
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
            .add_node(AigNode::And {
                id: 3,
                fanin0: AigEdge::new(a1.clone(), false),
                fanin1: AigEdge::new(a2.clone(), false),
            })
            .unwrap();
        let _a4 = a.add_node(AigNode::Latch {
            id: 4,
            next: AigEdge::new(a3.clone(), true),
            init: None,
        });
        // Do not save the node - or drop it explicitly later
        a.add_node(AigNode::And {
            id: 5,
            fanin0: AigEdge::new(a1.clone(), true),
            fanin1: AigEdge::new(a2.clone(), true),
        })
        .unwrap();
        a.add_output(4, false).unwrap();

        let mut b = Aig::new();
        let b1 = b.add_node(AigNode::Input(1)).unwrap();
        let b2 = b.add_node(AigNode::Input(2)).unwrap();
        let b3 = b
            .add_node(AigNode::And {
                id: 3,
                fanin0: AigEdge::new(b1.clone(), false),
                fanin1: AigEdge::new(b2.clone(), false),
            })
            .unwrap();
        let _b4 = b.add_node(AigNode::Latch {
            id: 4,
            next: AigEdge::new(b3.clone(), true),
            init: None,
        });
        b.add_output(4, false).unwrap();

        a.update();
        b.update();

        assert_eq!(a, b);
    }

    #[test]
    fn aig_neq_test() {
        let mut a = Aig::new();
        let mut b = Aig::new();

        let a1 = a.add_node(AigNode::Input(1)).unwrap();
        let b2 = b.add_node(AigNode::Input(2)).unwrap();

        assert_ne!(a, b);

        let a2 = a.add_node(AigNode::Input(2)).unwrap();
        let b1 = b.add_node(AigNode::Input(1)).unwrap();

        assert_eq!(a, b);

        let _a3 = a
            .add_node(AigNode::And {
                id: 3,
                fanin0: AigEdge::new(a1.clone(), false),
                fanin1: AigEdge::new(a2.clone(), false),
            })
            .unwrap();
        let _b3 = b
            .add_node(AigNode::And {
                id: 3,
                fanin0: AigEdge::new(b2.clone(), false),
                fanin1: AigEdge::new(b1.clone(), false),
            })
            .unwrap();

        assert_ne!(a, b);

        let mut c = Aig::new();
        let mut d = Aig::new();

        let cf = c.add_node(AigNode::False).unwrap();
        let df = d.add_node(AigNode::False).unwrap();
        c.add_node(AigNode::Latch {
            id: 1,
            next: AigEdge::new(cf.clone(), false),
            init: None,
        })
        .unwrap();
        d.add_node(AigNode::Latch {
            id: 1,
            next: AigEdge::new(df.clone(), false),
            init: Some(false),
        })
        .unwrap();
    }

    #[test]
    fn mut_id_test() {
        let mut aig = Aig::new();
        let i1 = aig.add_node(AigNode::Input(1)).unwrap();
        assert!(i1.borrow_mut().set_id(2).is_err()); // not allowed to rewrite input
        let i2 = aig.add_node(AigNode::Input(2)).unwrap();
        let a3 = aig
            .add_node(AigNode::And {
                id: 3,
                fanin0: AigEdge::new(i1.clone(), false),
                fanin1: AigEdge::new(i2.clone(), false),
            })
            .unwrap();
        let a4 = aig
            .add_node(AigNode::And {
                id: 4,
                fanin0: AigEdge::new(a3.clone(), false),
                fanin1: AigEdge::new(i2.clone(), false),
            })
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
        let _i2 = a.add_node(AigNode::Input(2)).unwrap(); // not used to check if kept alive
        let l3 = a
            .add_node(AigNode::Latch {
                id: 3,
                next: AigEdge::new(i1.clone(), true),
                init: None,
            })
            .unwrap();
        let a8 = a
            .add_node(AigNode::And {
                id: 8,
                fanin0: AigEdge::new(i1.clone(), false),
                fanin1: AigEdge::new(l3.clone(), false),
            })
            .unwrap();
        let _a15 = a
            .add_node(AigNode::And {
                id: 15,
                fanin0: AigEdge::new(a8.clone(), false),
                fanin1: AigEdge::new(i1.clone(), true),
            })
            .unwrap();
        a.add_output(15, false).unwrap();
        a.minimize_ids().unwrap();

        let mut b = Aig::new();
        let b1 = b.add_node(AigNode::Input(1)).unwrap();
        let _b2 = b.add_node(AigNode::Input(2)).unwrap(); // not used to check if kept alive
        let b3 = b
            .add_node(AigNode::Latch {
                id: 3,
                next: AigEdge::new(b1.clone(), true),
                init: None,
            })
            .unwrap();
        let b4 = b
            .add_node(AigNode::And {
                id: 4,
                fanin0: AigEdge::new(b3.clone(), false),
                fanin1: AigEdge::new(b1.clone(), false),
            })
            .unwrap();
        let _b5 = b
            .add_node(AigNode::And {
                id: 5,
                fanin0: AigEdge::new(b4.clone(), false),
                fanin1: AigEdge::new(b1.clone(), true),
            })
            .unwrap();
        b.add_output(5, false).unwrap();

        assert_eq!(a, b);
    }
}
