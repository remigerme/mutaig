//! # MUTAIG: mutable AIG
//!
//! A library for manipulating And-Inverter Graphs (AIGs), designed for combinational equivalence checking.
//!
//! ## Installation
//!
//! As for any other Rust library:
//!
//! ```shell
//! cargo add mutaig
//! ```
//!
//! ## Getting started
//!
//! ### Creating an AIG
//!
//! See [README](https://github.com/remigerme/mutaig?tab=readme-ov-file#creating-your-first-aig)
//! for instructions on how to manually create an AIG.
//!
//! In practice, you will probably never have to build an AIG by hand. Instead, you can use the [`Aig::from_file`] function:
//!
//! ```rust
//! use mutaig::Aig;
//!
//! let mut aig = Aig::from_file("assets/circuits/half-adder.aag").unwrap();
//! ```
//!
//! with [`half-adder.aag`](https://github.com/remigerme/mutaig/blob/main/assets/circuits/half-adder.aag)
//! in the AIGER format (here ASCII) corresponding to the AIG above:
//!
//! ```aag
//! aag 7 2 0 2 3
//! 2
//! 4
//! 6
//! 12
//! 6 13 15
//! 12 2 4
//! 14 3 5
//! ```
//!
//! Note that the [`Aig::from_file`] function also supports `.aig` files, which is the binary [AIGER](https://fmv.jku.at/aiger/) format.
//!
//! ### Proving functional equivalence
//!
//! For a complete small example, once again, check the
//! [README](https://github.com/remigerme/mutaig?tab=readme-ov-file#proving-your-first-functional-equivalence).
//!
//! The strategy is to generate a [`Miter`] from the two circuits we want to compare, then extract a [`Cnf`] from this miter.
//! The SAT clauses are generated using the [Tseytin transformation](https://en.wikipedia.org/wiki/Tseytin_transformation).
//! Give the obtained CNF to a SAT solver:
//!
//! - if the CNF is UNSAT, then AIGs have been proven equivalent
//! - else if the CNF is SAT, the AIGs functionally differ (there exists a set of inputs such that the two AIGs return two different results).
//!
//! If you are not familiar with this strategy, check the docs of [`Miter`] and [`cnf`].
//!
//! [`Miter`]: miter::Miter
//! [`Cnf`]: cnf::Cnf
//!
//! In terms of Rust code:
//!
//! ```rust
//! use std::collections::HashMap;
//! use mutaig::{Aig, NodeId, miter::Miter};
//!
//! let reference = Aig::from_file("assets/circuits/ctrl.aig").unwrap(); // path to the golden reference here
//! let optimized = Aig::from_file("assets/circuits/ctrl.aig").unwrap(); // path to the optimized circuit here
//!
//! // Here the outputs are exactly the same because the AIG was not modified
//! let outputs_mapping = reference
//!     .get_outputs()
//!     .iter()
//!     .map(|fanin| {
//!        (
//!            (fanin.get_node_id(), fanin.get_complement()),
//!            (fanin.get_node_id(), fanin.get_complement()),
//!        )
//!     })
//!     .collect::<HashMap<(NodeId, bool), (NodeId, bool)>>();
//!
//! let mut miter = Miter::new(&reference, &optimized, outputs_mapping).unwrap();
//! let cnf = miter.extract_cnf().unwrap();
//!
//! // Here you can give the CNF to any SAT solver
//! // You can use the dimacs format:
//! let dimacs = cnf.to_dimacs();
//!
//! // If the CNF is UNSAT, AIGs have been proved equivalent using Tseytin transformation and a SAT solver!
//! ```
//!
//! ### Proving functional equivalence of internal nodes
//!
//! When AIGs are too large, the extracted CNF is too large for SAT solvers. Note that modern SAT solvers are incredibly efficient (for example [kissat](https://github.com/arminbiere/kissat) was able to prove a CNF with 50 million of clauses UNSAT in less than 10s). But still, this doesn't scale for very large circuits.
//!
//! You should look at three very helpful functions:
//!
//! - [`Miter::mergeable`]: to check if nodes are obviously functionally equivalent
//! - [`Miter::extract_cnf_node`]: to extract a miter+CNF between two internal nodes
//! - [`Miter::merge`]: to merge two nodes that you have proven equivalent
//!   (using [`Miter::mergeable`] or [`Miter::extract_cnf_node`])
//!
//! [`Miter::mergeable`]: miter::Miter::mergeable
//! [`Miter::extract_cnf_node`]: miter::Miter::extract_cnf_node
//! [`Miter::merge`]: miter::Miter::merge
//!
//! ### Export to Graphviz (DOT)
//!
//! You can also export AIGs and miters to the Graphviz dot format using their [`Aig::to_dot`]/[`Miter::to_dot`] methods.
//!
//! [`Miter::to_dot`]: miter::Miter::to_dot
//!
//! ```rust
//! use mutaig::Aig;
//! use mutaig::miter::Miter;
//! use mutaig::dot::GraphvizStyle;
//!
//! let aig = Aig::from_file("assets/circuits/half-adder.aag").unwrap();
//! println!("{}", aig.to_dot(GraphvizStyle::default()));
//! // GraphvizStyle::debug() can also be convenient.
//!
//! // Creating a miter between two copies of the circuit
//! let outputs_map = aig
//!     .get_outputs()
//!     .iter()
//!     .map(|edge| {
//!         let id = edge.get_node_id();
//!         let b = edge.get_complement();
//!         ((id, b), (id, b))
//!     })
//!     .collect();
//!
//! let new_aig = aig.deep_clone();
//! let miter = Miter::new(&aig, &aig, outputs_map).unwrap();
//! println!("{}", miter.to_dot(GraphvizStyle::default()));
//! ```
//!
//! You can then render the graphs using the DOT engine.

pub mod aig;
pub mod cnf;
pub mod miter;

// Re-exporting symbols and modules.
pub use aig::dfs;
pub use aig::dot;
pub use aig::{Aig, AigEdge, AigError, AigNode, AigNodeRef, FaninId, NodeId, Result};
