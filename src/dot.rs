use std::{fmt::Display, ops::Add};

use crate::{Aig, AigEdge, AigNode, dfs::Dfs, miter::Miter};

// Defining default style for nodes.
const DEFAULT_FALSE_NODE_FORMAT: &str = "";
const DEFAULT_INPUT_NODE_FORMAT: &str = " [shape=box] ";
const DEFAULT_LATCH_NODE_FORMAT: &str = " [shape=diamond] ";
const DEFAULT_AND_NODE_FORMAT: &str = " [shape=circle] ";
const DEFAULT_XOR_NODE_FORMAT: &str = "";
const DEFAULT_OR_NODE_FORMAT: &str = "";
/// See https://stackoverflow.com/questions/50822798/how-to-use-graphviz-to-draw-a-node-pointed-by-an-arrow.
const DEFAULT_OUTPUT_NODE_FORMAT: &str = " [shape=none, height=.0, width=.0] ";

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

impl Add for GraphvizEdgeStyle {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        GraphvizEdgeStyle(format!("{}{}", self.0, rhs.0))
    }
}

/// Parameters for Graphviz rendering.
///
/// The following nodes can be rendered using [`GraphvizNodeStyle`]:
/// - [`AigNode::False`]
/// - [`AigNode::Input`]
/// - [`AigNode::Latch`]
/// - [`AigNode::And`]
/// - output (by default, invisible node just to get an arrow)
/// - `xor` gate (for miter)
/// - `or` gate (for miter).
pub struct GraphvizStyle {
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
    fn graphviz_decl(&self, graphviz_style: &GraphvizStyle) -> String {
        let (id, style, label) = match self {
            AigNode::False => (0, graphviz_style.cst_false.clone(), "".to_string()),
            AigNode::Input(id) => (*id, graphviz_style.input.clone(), format!("i{}", id)),
            AigNode::Latch { id, .. } => (*id, graphviz_style.latch.clone(), format!("l{}", id)),
            AigNode::And { id, .. } => (*id, graphviz_style.and.clone(), "".to_string()),
        };
        format!("{} {} [label=\"{}\"]\n", id, style, label)
    }
}

impl AigEdge {
    fn graphviz_decl(&self, to: String, to_latch: bool, graphviz_style: &GraphvizStyle) -> String {
        let mut style = graphviz_style.edge_all.clone();
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
        let mut s = String::new();

        // DOT header
        s.push_str("strict digraph {\n");
        s.push_str("rankdir=\"BT\"\n");

        // Adding artificial outputs to point to
        for (i, output) in self.outputs.iter().enumerate() {
            let output_id = get_output_id(output);
            let output_decl = format!(
                "{} {} [label=\"o{}\"]\n",
                output_id,
                graphviz_style.output,
                1 + i
            );
            s.push_str(&output_decl);
            s.push_str(&output.graphviz_decl(output_id, false, &graphviz_style));
        }

        // DFS from outputs
        let mut dfs = Dfs::from_outputs(self);
        while let Some(node) = dfs.next(self) {
            s.push_str(&node.borrow().graphviz_decl(&graphviz_style));
            for fanin in node.borrow().get_fanins() {
                s.push_str(&fanin.graphviz_decl(
                    node.borrow().get_id().to_string(),
                    node.borrow().is_latch(),
                    &graphviz_style,
                ));
            }
        }

        // DOT footer
        s.push('}');
        s.push('\n');

        s
    }
}

impl Miter {
    pub fn to_dot(&self, _graphviz_style: GraphvizStyle) -> String {
        todo!()
    }
}
