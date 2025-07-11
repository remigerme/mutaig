use std::{fmt::Display, ops::Add};

use crate::{Aig, AigEdge, AigNode, dfs::Dfs, miter::Miter};

// Definining default global style.
const DEFAULT_RANKDIR: &str = "BT";

// Defining default style for nodes.
const DEFAULT_FALSE_NODE_FORMAT: &str = "[shape=point, label=\"GND\", width=1.5]";
const DEFAULT_INPUT_NODE_FORMAT: &str = "[shape=box]";
const DEFAULT_LATCH_NODE_FORMAT: &str = "[shape=diamond]";
const DEFAULT_AND_NODE_FORMAT: &str = "[shape=circle]";
const DEFAULT_XOR_NODE_FORMAT: &str = "";
const DEFAULT_OR_NODE_FORMAT: &str = "";
/// See https://stackoverflow.com/questions/50822798/how-to-use-graphviz-to-draw-a-node-pointed-by-an-arrow.
const DEFAULT_OUTPUT_NODE_FORMAT: &str = "[shape=none, height=.0, width=.0]";

// Defining default style for edges.
const DEFAULT_EDGE_ALL_FORMAT: &str = "[arrowsize=0.3]";
const DEFAULT_EDGE_COMPLEMENT_FORMAT: &str = "[headlabel=\"●\", labelangle=.0, labeldistance=1.5]";
const DEFAULT_EDGE_LATCH_FORMAT: &str = "[style=\"dashed\"]";

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
pub struct GraphvizStyle {
    // Global
    rankdir: String,

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
}

impl Default for GraphvizStyle {
    fn default() -> Self {
        GraphvizStyle {
            rankdir: DEFAULT_RANKDIR.to_string(),

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
        }
    }
}

impl AigNode {
    /// Beware, [`AigNode::False`] is a special case.
    fn graphviz_decl(&self) -> String {
        let (id, label) = match self {
            AigNode::False => return "0".to_string(),
            AigNode::Input(id) => (*id, format!("i{}", id)),
            AigNode::Latch { id, .. } => (*id, format!("l{}", id)),
            AigNode::And { id, .. } => (*id, "".to_string()),
        };
        format!("{} [label=\"{}\"]\n", id, label)
    }
}

impl AigEdge {
    fn graphviz_decl(&self, to: String, to_latch: bool, graphviz_style: &GraphvizStyle) -> String {
        let mut style = GraphvizEdgeStyle::default();
        if self.complement {
            style = style + graphviz_style.edge_complement.clone();
        }
        if to_latch {
            style = style + graphviz_style.edge_latch.clone();
        }
        format!(
            "{} -> {} {}\n",
            self.get_node().borrow().get_id(),
            to,
            style
        )
    }
}

fn get_output_id(output: &AigEdge) -> String {
    format!(
        "o{}{}",
        output.get_node().borrow().get_id(),
        output.get_complement()
    )
}

impl Aig {
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
            decl_edges.push_str(&output.graphviz_decl(output_id, false, &graphviz_style));
        }

        // DFS from outputs
        let mut dfs = Dfs::from_outputs(self);
        while let Some(node) = dfs.next(self) {
            match &*node.borrow() {
                AigNode::False => decl_false_node_optional.push_str(&format!(
                    "{} {}\n",
                    node.borrow().graphviz_decl(),
                    graphviz_style.cst_false
                )),
                AigNode::Input(_) => {
                    decl_inputs.push_str(&node.borrow().graphviz_decl());
                }
                AigNode::Latch { .. } => {
                    decl_latches.push_str(&node.borrow().graphviz_decl());
                }
                AigNode::And { .. } => {
                    decl_ands.push_str(&node.borrow().graphviz_decl());
                }
            }
            for fanin in node.borrow().get_fanins() {
                decl_edges.push_str(&fanin.graphviz_decl(
                    node.borrow().get_id().to_string(),
                    node.borrow().is_latch(),
                    &graphviz_style,
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
    pub fn to_dot(&self, _graphviz_style: GraphvizStyle) -> String {
        todo!()
    }
}

#[cfg(test)]
mod test {
    use crate::{Aig, dot::GraphvizStyle};

    #[test]
    fn d() {
        let aig = Aig::from_file("adder.aig").unwrap();
        eprintln!("{}", aig.to_dot(GraphvizStyle::default()));
    }
}
