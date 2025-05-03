use std::collections::{HashMap, HashSet};
use std::fmt::Write; // Import the Write trait

use crate::{
    middleware::{OperationType, Statement},
    prover::types::ProofSolution,
};

/// Generates a Graphviz DOT representation of the proof structure.
///
/// Nodes represent Statements (base facts or derived).
/// Edges represent Operations, connecting input statements to output statements.
///
/// Args:
///     solution: The ProofSolution containing the bindings, scope (base facts), and proof chains.
///
/// Returns:
///     A String containing the graph description in DOT format.
pub fn generate_graphviz_dot(solution: &ProofSolution) -> String {
    let mut dot = String::new();
    let mut node_ids = HashMap::new();
    let mut nodes_declared = HashSet::new();
    let mut edges_declared = HashSet::new();
    let mut node_counter = 0;

    // Helper to get or assign a node ID for a statement
    let get_node_id =
        |stmt: &Statement, counter: &mut usize, ids: &mut HashMap<Statement, String>| -> String {
            ids.entry(stmt.clone())
                .or_insert_with(|| {
                    let id = format!("stmt_{}", *counter);
                    *counter += 1;
                    id
                })
                .clone()
        };

    // Helper to format statement for label, escaping special characters
    let format_label = |stmt: &Statement| -> String {
        format!("{}", stmt)
            .replace('\\', "\\\\")
            .replace('\"', "\\\"")
            .replace('\n', "\\n")
    };

    // Helper to format operation for label
    let format_op_label = |op: &OperationType| -> String {
        format!("{:?}", op)
            .replace('\\', "\\\\")
            .replace('\"', "\\\"")
            .replace('\n', "\\n")
    };

    // --- Start Graph ---
    writeln!(dot, "digraph Proof {{").unwrap();
    writeln!(dot, "  rankdir=LR;").unwrap(); // Left-to-right layout often works well
    writeln!(dot, "  node [shape=box];").unwrap(); // Default shape for statements

    // --- Declare Base Fact Nodes ---
    writeln!(dot, "\n  // Base Facts (Scope)").unwrap();
    for (pod_id, stmt) in &solution.scope {
        let node_id = get_node_id(stmt, &mut node_counter, &mut node_ids);
        if nodes_declared.insert(node_id.clone()) {
            // Add origin PodId to the label
            let label = format!("Origin: {}\\n{}", pod_id, format_label(stmt));
            writeln!(
                dot,
                "  {} [label=\"{}\", style=filled, fillcolor=lightblue];",
                node_id, label
            )
            .unwrap();
        }
    }

    // --- Process Proof Chains ---
    writeln!(dot, "\n  // Derived Statements and Operations").unwrap();
    let mut op_counter = 0; // Counter for unique operation nodes

    for proof_chain in solution.proof_chains.values() {
        for step in &proof_chain.0 {
            let output_node_id = get_node_id(&step.output, &mut node_counter, &mut node_ids);

            // Declare output node if not already declared (might be a base fact if copied)
            if nodes_declared.insert(output_node_id.clone()) {
                // Style derived statements differently if needed (e.g., no fill)
                writeln!(
                    dot,
                    "  {} [label=\"{}\"];",
                    output_node_id,
                    format_label(&step.output)
                )
                .unwrap();
            }

            // Create an intermediate node for the operation
            let op_node_id = format!("op_{}", op_counter);
            op_counter += 1;
            writeln!(
                dot,
                "  {} [label=\"{}\", shape=ellipse, style=filled, fillcolor=lightgrey];",
                op_node_id,
                format_op_label(&step.operation)
            )
            .unwrap();

            // Declare input nodes and edges from inputs to operation
            for input_stmt in &step.inputs {
                let input_node_id = get_node_id(input_stmt, &mut node_counter, &mut node_ids);
                // Ensure input node is declared (should be from scope or previous steps)
                if nodes_declared.insert(input_node_id.clone()) {
                    // This case might happen if an input wasn't in scope but derived in a different chain part
                    // Declare it with default style
                    writeln!(
                        dot,
                        "  {} [label=\"{}\"];",
                        input_node_id,
                        format_label(input_stmt)
                    )
                    .unwrap();
                }
                // Add edge from input to operation node
                let edge = (input_node_id.clone(), op_node_id.clone());
                if edges_declared.insert(edge) {
                    writeln!(dot, "  {} -> {};", input_node_id, op_node_id).unwrap();
                }
            }

            // Add edge from operation node to output node
            let edge = (op_node_id.clone(), output_node_id.clone());
            if edges_declared.insert(edge) {
                writeln!(dot, "  {} -> {};", op_node_id, output_node_id).unwrap();
            }
        }
    }

    // --- End Graph ---
    writeln!(dot, "}}").unwrap();

    dot
}
