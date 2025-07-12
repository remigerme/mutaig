//! You can also export AIGs and miters to the Graphviz dot format using their `to_dot` methods: [`Aig::to_dot`], [`Miter::to_dot`].
//!
//! ```rust
//! use mutaig::Aig;
//! use mutaig::miter::Miter;
//! use mutaig::dot::GraphvizStyle;
//!
//! let aig = Aig::from_file("assets/circuits/half-adder.aag").unwrap();
//! println!("{}", aig.to_dot(GraphvizStyle::default()));
//!
//! // Creating a miter between two copies of the circuit
//! let outputs_map = aig
//!     .get_outputs()
//!     .iter()
//!     .map(|edge| {
//!         let id = edge.get_node().borrow().get_id();
//!         let b = edge.get_complement();
//!         ((id, b), (id, b))
//!     })
//!     .collect();
//!
//! let miter = Miter::new(&aig, &aig, outputs_map).unwrap();
//! println!("{}", miter.to_dot(GraphvizStyle::default()));
//! ```
//!
//! You can then render the graphs using the DOT engine.

use std::{fmt::Display, ops::Add};

use crate::{Aig, AigEdge, AigNode, NodeId, dfs::Dfs, miter::Miter};

// Definining default global style.
const DEFAULT_RANKDIR: &str = "BT";
const DEFAULT_MITER_OUTPUT_LABEL: &str = "Z";

// Defining default style for nodes.
const DEFAULT_FALSE_NODE_FORMAT: &str = "[shape=point, label=\"GND\", width=1.5]";
const DEFAULT_INPUT_NODE_FORMAT: &str = "[shape=box]";
const DEFAULT_LATCH_NODE_FORMAT: &str = "[shape=diamond]";
const DEFAULT_AND_NODE_FORMAT: &str = "[shape=circle]";
const DEFAULT_XOR_NODE_FORMAT: &str = "[shape=circle, label=\"⊕\"]";
const DEFAULT_OR_NODE_FORMAT: &str = "[shape=circle, label=\"∪\"]";
/// See https://stackoverflow.com/questions/50822798/how-to-use-graphviz-to-draw-a-node-pointed-by-an-arrow.
const DEFAULT_OUTPUT_NODE_FORMAT: &str = "[shape=none, height=.0, width=.0]";

// Defining default style for edges.
const DEFAULT_EDGE_ALL_FORMAT: &str = "[arrowsize=0.3]";
const DEFAULT_EDGE_COMPLEMENT_FORMAT: &str = "[headlabel=\"●\", labelangle=.0, labeldistance=1.5]";
const DEFAULT_EDGE_LATCH_FORMAT: &str = "[style=\"dashed\"]";
const DEFAULT_EDGE_OUTPUT_FORMAT: &str = "[arrowhead=none]";

/// String containing the graphviz node style (you must manually include square brackets).
///
/// See [`GraphvizStyle`] for what kind of nodes can be described.
#[derive(Debug, Clone)]
pub struct GraphvizNodeStyle(String);

impl Display for GraphvizNodeStyle {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// String containing the graphviz edge style (you must manually include square brackets).
///
/// See [`GraphvizStyle`] for what kind of edges can be described.
#[derive(Debug, Clone)]
pub struct GraphvizEdgeStyle(String);

impl Display for GraphvizEdgeStyle {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Default for GraphvizEdgeStyle {
    fn default() -> Self {
        GraphvizEdgeStyle("".to_string())
    }
}

impl Add for GraphvizEdgeStyle {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        GraphvizEdgeStyle(format!("{}{}", self.0, rhs.0))
    }
}

/// Parameters for Graphviz rendering.
///
/// ### Global parameters
/// - `rankdir`
///
/// ### Nodes
/// The following nodes can be rendered using [`GraphvizNodeStyle`]:
/// - [`AigNode::False`]
/// - [`AigNode::Input`]
/// - [`AigNode::Latch`]
/// - [`AigNode::And`]
/// - output (by default, invisible node just to get an arrow)
/// - `xor` gate (for miter)
/// - `or` gate (for miter).
///  
/// ### Edges
/// Edge styles are additive. All edges implement the `edge_all` style. To that can be added:
/// - `edge_latch` if the edge is pointing at a latch
/// - `edge_complement` if the edge is complemented
/// - `edge_output` if the edge is directed to a final output (an output for an AIG, the output of the final `OR`/`XOR` gate for a miter depending on its structure).
pub struct GraphvizStyle {
    // Global
    rankdir: String,
    miter_output_label: String,

    // Nodes
    cst_false: GraphvizNodeStyle,
    input: GraphvizNodeStyle,
    latch: GraphvizNodeStyle,
    and: GraphvizNodeStyle,
    output: GraphvizNodeStyle,
    xor: GraphvizNodeStyle,
    or: GraphvizNodeStyle,

    // Edges
    edge_all: GraphvizEdgeStyle,
    edge_latch: GraphvizEdgeStyle,
    edge_complement: GraphvizEdgeStyle,
    edge_output: GraphvizEdgeStyle,
}

impl Default for GraphvizStyle {
    fn default() -> Self {
        GraphvizStyle {
            rankdir: DEFAULT_RANKDIR.to_string(),
            miter_output_label: DEFAULT_MITER_OUTPUT_LABEL.to_string(),

            cst_false: GraphvizNodeStyle(DEFAULT_FALSE_NODE_FORMAT.to_string()),
            input: GraphvizNodeStyle(DEFAULT_INPUT_NODE_FORMAT.to_string()),
            latch: GraphvizNodeStyle(DEFAULT_LATCH_NODE_FORMAT.to_string()),
            and: GraphvizNodeStyle(DEFAULT_AND_NODE_FORMAT.to_string()),
            xor: GraphvizNodeStyle(DEFAULT_XOR_NODE_FORMAT.to_string()),
            or: GraphvizNodeStyle(DEFAULT_OR_NODE_FORMAT.to_string()),
            output: GraphvizNodeStyle(DEFAULT_OUTPUT_NODE_FORMAT.to_string()),

            edge_all: GraphvizEdgeStyle(DEFAULT_EDGE_ALL_FORMAT.to_string()),
            edge_latch: GraphvizEdgeStyle(DEFAULT_EDGE_LATCH_FORMAT.to_string()),
            edge_complement: GraphvizEdgeStyle(DEFAULT_EDGE_COMPLEMENT_FORMAT.to_string()),
            edge_output: GraphvizEdgeStyle(DEFAULT_EDGE_OUTPUT_FORMAT.to_string()),
        }
    }
}

impl AigNode {
    /// `id_prefix` is used only for latches and and gates (useful when mitering).
    fn get_graphviz_id(&self, id_prefix: Option<String>) -> String {
        match self {
            AigNode::False => "0".to_string(),
            AigNode::Input(id) => id.to_string(),
            AigNode::Latch { id, .. } | AigNode::And { id, .. } => {
                format!("{}{}", id_prefix.unwrap_or_default(), id)
            }
        }
    }

    /// Beware, [`AigNode::False`] is a special case.
    fn graphviz_decl(&self, id_prefix: Option<String>) -> String {
        let graphviz_id = self.get_graphviz_id(id_prefix);

        let label = match self {
            AigNode::False => return graphviz_id, // early return, we don't '\n' because style is defined later
            AigNode::Input(id) => format!("i{}", id),
            AigNode::Latch { .. } => format!("l{}", graphviz_id),
            AigNode::And { .. } => "".to_string(),
        };
        format!("{} [label=\"{}\"]\n", graphviz_id, label)
    }
}

impl AigEdge {
    fn graphviz_decl(
        &self,
        to: String,
        to_latch: bool,
        to_output: bool,
        graphviz_style: &GraphvizStyle,
        id_prefix: Option<String>,
    ) -> String {
        let mut style = GraphvizEdgeStyle::default();
        if self.complement {
            style = style + graphviz_style.edge_complement.clone();
        }
        if to_latch {
            style = style + graphviz_style.edge_latch.clone();
        }
        if to_output {
            style = style + graphviz_style.edge_output.clone();
        }
        let graphviz_id = self.get_node().borrow().get_graphviz_id(id_prefix);
        format!("{} -> {} {}\n", graphviz_id, to, style)
    }
}

fn get_output_id(output: &AigEdge) -> String {
    format!(
        "o{}{}",
        output.get_node().borrow().get_id(),
        output.get_complement()
    )
}

fn get_xor_id(ia: NodeId, ca: bool, ib: NodeId, cb: bool) -> String {
    format!("xor{}{}{}{}", ia, ca, ib, cb)
}

impl Aig {
    /// Returns a DOT representation of the AIG.
    pub fn to_dot(&self, graphviz_style: GraphvizStyle) -> String {
        let mut decl_edges = String::new();

        // Creating different subgraphs for node declarations
        let mut decl_false_node_optional = "".to_string();
        let mut decl_inputs = format!("subgraph inputs {{\n node {}\n", graphviz_style.input);
        let mut decl_latches = format!("subgraph latches {{\n node {}\n", graphviz_style.latch);
        let mut decl_outputs = format!("subgraph outputs {{\n node {}\n", graphviz_style.output);
        let mut decl_ands = format!("subgraph ands {{\n node {}\n", graphviz_style.and);

        // Adding artificial outputs to point to
        for (i, output) in self.outputs.iter().enumerate() {
            let output_id = get_output_id(output);
            let output_decl = format!("{} [label=\"o{}\"]\n", output_id, 1 + i);
            decl_outputs.push_str(&output_decl);
            decl_edges.push_str(&output.graphviz_decl(
                output_id,
                false,
                true,
                &graphviz_style,
                None,
            ));
        }

        // DFS from outputs
        let mut dfs = Dfs::from_outputs(self);
        while let Some(node) = dfs.next(self) {
            match &*node.borrow() {
                AigNode::False => decl_false_node_optional.push_str(&format!(
                    "{} {}\n",
                    node.borrow().graphviz_decl(None),
                    graphviz_style.cst_false
                )),
                AigNode::Input(_) => {
                    decl_inputs.push_str(&node.borrow().graphviz_decl(None));
                }
                AigNode::Latch { .. } => {
                    decl_latches.push_str(&node.borrow().graphviz_decl(None));
                }
                AigNode::And { .. } => {
                    decl_ands.push_str(&node.borrow().graphviz_decl(None));
                }
            }
            for fanin in node.borrow().get_fanins() {
                decl_edges.push_str(&fanin.graphviz_decl(
                    node.borrow().get_id().to_string(),
                    node.borrow().is_latch(),
                    false,
                    &graphviz_style,
                    None,
                ));
            }
        }

        // Concatenating everything together
        format!(
            "
strict digraph {{
    rankdir=\"{}\"
    edge {}
    {}
    {}
    }}
    {}
    }}
    {}
    }}
    {}
    }}
    {}
}}",
            graphviz_style.rankdir,
            graphviz_style.edge_all,
            decl_false_node_optional,
            decl_inputs,
            decl_latches,
            decl_ands,
            decl_outputs,
            decl_edges
        )
    }
}

impl Miter {
    /// Returns a DOT representation of the miter.
    pub fn to_dot(&self, graphviz_style: GraphvizStyle) -> String {
        let mut decl_edges = String::new();

        // Creating different subgraphs for node declarations
        let mut decl_false_node_optional = "".to_string();
        let mut decl_inputs = format!("subgraph inputs {{\n node {}\n", graphviz_style.input);
        let mut decl_latches = format!("subgraph latches {{\n node {}\n", graphviz_style.latch);
        let mut decl_xors = format!(
            "subgraph outputs {{\n rank=same\n node {}\n",
            graphviz_style.xor
        );
        let mut decl_or_optional = "".to_string();
        let mut decl_ands_a = format!(
            "subgraph cluster_ands_a {{
            label=\"A\"
            labelloc=b
            labeljust=l
            node {}
            ",
            graphviz_style.and
        );
        let mut decl_ands_b = format!(
            "subgraph cluster_ands_b {{
            label=\"B\"
            labelloc=b
            labeljust=r
            node {}
            ",
            graphviz_style.and
        );

        // We also need an artifical output
        let output_id = "final";
        let decl_output = format!(
            "{} {} [label=\"{}\"]\n",
            output_id, graphviz_style.output, graphviz_style.miter_output_label
        );

        // If comparing more than one output, let's also create a final OR gate
        let or_id = "or";
        let draw_or = self.outputs_map.len() > 1;
        if draw_or {
            decl_or_optional.push_str(&format!("{} {}\n", or_id, graphviz_style.or));
            decl_edges.push_str(&format!(
                "{} -> {} {}\n",
                or_id, output_id, graphviz_style.edge_output
            ));
        }

        // Creating XOR gates
        for ((ia, ca), (ib, cb)) in &self.outputs_map {
            let xor_id = get_xor_id(*ia, *ca, *ib, *cb);
            decl_xors.push_str(&format!("{}\n", xor_id));
            let sa = ca
                .then(|| graphviz_style.edge_complement.clone())
                .unwrap_or_default();
            let sb = cb
                .then(|| graphviz_style.edge_complement.clone())
                .unwrap_or_default();
            let gia = self
                .a
                .get_node(*ia)
                .unwrap()
                .borrow()
                .get_graphviz_id(Some("a".to_string()));
            let gib = self
                .b
                .get_node(*ib)
                .unwrap()
                .borrow()
                .get_graphviz_id(Some("b".to_string()));
            decl_edges.push_str(&format!("{} -> {} {}\n", gia, xor_id, sa));
            decl_edges.push_str(&format!("{} -> {} {}\n", gib, xor_id, sb));
            if draw_or {
                decl_edges.push_str(&format!("{} -> {}\n", xor_id, or_id));
            } else {
                decl_edges.push_str(&format!(
                    "{} -> {} {}\n",
                    xor_id, output_id, graphviz_style.edge_output
                ));
            }
        }

        // DFS from outputs for a
        let mut dfs = Dfs::from_outputs(&self.a);
        while let Some(node) = dfs.next(&self.a) {
            match &*node.borrow() {
                AigNode::False => decl_false_node_optional.push_str(&format!(
                    "{} {}\n",
                    node.borrow().graphviz_decl(Some("a".to_string())),
                    graphviz_style.cst_false
                )),
                AigNode::Input(_) => {
                    decl_inputs.push_str(&node.borrow().graphviz_decl(Some("a".to_string())));
                }
                AigNode::Latch { .. } => {
                    decl_latches.push_str(&node.borrow().graphviz_decl(Some("a".to_string())));
                }
                AigNode::And { .. } => {
                    decl_ands_a.push_str(&node.borrow().graphviz_decl(Some("a".to_string())));
                }
            }
            for fanin in node.borrow().get_fanins() {
                decl_edges.push_str(&fanin.graphviz_decl(
                    node.borrow().get_graphviz_id(Some("a".to_string())), // TODO MITER MIGHT BE MERGED
                    node.borrow().is_latch(),
                    false,
                    &graphviz_style,
                    Some("a".to_string()),
                ));
            }
        }

        // DFS from outputs for b.
        // We assume that false node, inputs, and latches have already all been visited from DFS of a.
        let mut dfs = Dfs::from_outputs(&self.b);
        while let Some(node) = dfs.next(&self.b) {
            match &*node.borrow() {
                AigNode::And { .. } => {
                    decl_ands_b.push_str(&node.borrow().graphviz_decl(Some("b".to_string())));
                }
                _ => (),
            }
            for fanin in node.borrow().get_fanins() {
                decl_edges.push_str(&fanin.graphviz_decl(
                    node.borrow().get_graphviz_id(Some("b".to_string())), // Same todo
                    node.borrow().is_latch(),
                    false,
                    &graphviz_style,
                    Some("b".to_string()),
                ));
            }
        }

        // Concatenating everything together
        format!(
            "
strict digraph {{
    rankdir=\"{}\"
    edge {}
    {}
    {}
    {}
    }}
    {}
    }}
    {}
    }}
    {}
    }}
    {}
    }}
    {}
    {}
}}",
            graphviz_style.rankdir,
            graphviz_style.edge_all,
            decl_false_node_optional,
            decl_output,
            decl_inputs,
            decl_latches,
            decl_ands_a,
            decl_ands_b,
            decl_xors,
            decl_or_optional,
            decl_edges
        )
    }
}

#[cfg(test)]
mod test {
    use std::path::Path;

    use super::*;

    fn circuit_to_dot<P: AsRef<Path>>(path: P) {
        let aig = Aig::from_file(path).unwrap();
        println!("{}", aig.to_dot(GraphvizStyle::default()));
    }

    fn circuit_miter_to_dot<P: AsRef<Path>>(path: P) {
        let aig = Aig::from_file(path).unwrap();

        // Creating a miter between two copies of the circuit
        let outputs_map = aig
            .get_outputs()
            .iter()
            .map(|edge| {
                let id = edge.get_node().borrow().get_id();
                let b = edge.get_complement();
                ((id, b), (id, b))
            })
            .collect();

        let miter = Miter::new(&aig, &aig, outputs_map).unwrap();
        println!("{}", miter.to_dot(GraphvizStyle::default()));
    }

    #[test]
    fn half_adder_to_dot() {
        circuit_to_dot("assets/circuits/half-adder.aag");
    }

    #[test]
    fn half_adder_miter_to_dot() {
        circuit_miter_to_dot("assets/circuits/half-adder.aag");
    }

    #[test]
    fn ctrl_to_dot() {
        circuit_to_dot("assets/circuits/ctrl.aig");
    }

    #[test]
    fn ctrl_miter_to_dot() {
        circuit_miter_to_dot("assets/circuits/ctrl.aig");
    }
}
