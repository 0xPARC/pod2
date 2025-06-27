use std::{
    collections::{HashMap, HashSet},
    fmt::Write,
    sync::Arc,
};

use crate::{
    middleware::{NativePredicate, Predicate, StatementArg},
    solver::proof::{Justification, Proof, ProofNode},
};

/// Generates a Graphviz DOT representation of a proof tree.
///
/// Statement nodes are boxes, operation/justification nodes are ellipses.
/// Child statements connect to an operation node, which then connects to the
/// derived statement.
pub fn graphviz_dot(proof: &Proof) -> String {
    let mut dot = String::new();
    writeln!(&mut dot, "digraph Proof {{").unwrap();
    writeln!(&mut dot, "  rankdir=LR;").unwrap();
    writeln!(&mut dot, "  node [shape=box];").unwrap();

    let mut stmt_ids: HashMap<String, String> = HashMap::new();
    let mut nodes_declared: HashSet<String> = HashSet::new();
    let mut edges_declared: HashSet<(String, String)> = HashSet::new();
    let mut stmt_counter = 0usize;
    let mut op_counter = 0usize;

    // Assign deterministic id for statement string
    let mut get_stmt_id = |s: &str, counter: &mut usize, map: &mut HashMap<String, String>| {
        map.entry(s.to_string())
            .or_insert_with(|| {
                let id = format!("stmt_{}", *counter);
                *counter += 1;
                id
            })
            .clone()
    };

    // recursive closure to walk proof
    #[allow(clippy::too_many_arguments)]
    fn walk_node(
        node: &Arc<ProofNode>,
        stmt_ids: &mut HashMap<String, String>,
        nodes_declared: &mut HashSet<String>,
        edges_declared: &mut HashSet<(String, String)>,
        stmt_counter: &mut usize,
        op_counter: &mut usize,
        dot: &mut String,
        get_stmt_id: &mut impl FnMut(&str, &mut usize, &mut HashMap<String, String>) -> String,
    ) {
        // Do not emit the synthetic _request_goal predicate; dive into its premises instead.
        if matches!(node.statement.predicate(),
            Predicate::Custom(cpr) if cpr.predicate().name == "_request_goal")
        {
            if let Justification::Custom(_, premises) = &node.justification {
                for child in premises {
                    walk_node(
                        child,
                        stmt_ids,
                        nodes_declared,
                        edges_declared,
                        stmt_counter,
                        op_counter,
                        dot,
                        get_stmt_id,
                    );
                }
            }
            return;
        }

        let stmt_str = format!("{}", node.statement);
        let stmt_id = get_stmt_id(&stmt_str, stmt_counter, stmt_ids);
        if nodes_declared.insert(stmt_id.clone()) {
            writeln!(dot, "  {} [label=\"{}\"];", stmt_id, escape(&stmt_str)).unwrap();
        }

        match &node.justification {
            Justification::Fact => {}
            Justification::ValueComparison(op) | Justification::Special(op) => {
                let op_id = format!("op_{}", *op_counter);
                *op_counter += 1;
                writeln!(
                    dot,
                    "  {} [label=\"{:?}\", shape=ellipse, style=filled, fillcolor=lightgrey];",
                    op_id, op
                )
                .unwrap();
                let edge = (op_id.clone(), stmt_id.clone());
                if edges_declared.insert(edge.clone()) {
                    writeln!(dot, "  {} -> {};", op_id, stmt_id).unwrap();
                }
            }
            Justification::Custom(cpr, premises) => {
                let op_id = format!("op_{}", *op_counter);
                *op_counter += 1;
                writeln!(
                    dot,
                    "  {} [label=\"{}\", shape=ellipse, style=filled, fillcolor=lightgrey];",
                    op_id,
                    escape(&cpr.predicate().name)
                )
                .unwrap();
                let edge = (op_id.clone(), stmt_id.clone());
                if edges_declared.insert(edge.clone()) {
                    writeln!(dot, "  {} -> {};", op_id, stmt_id).unwrap();
                }
                for child in premises {
                    walk_node(
                        child,
                        stmt_ids,
                        nodes_declared,
                        edges_declared,
                        stmt_counter,
                        op_counter,
                        dot,
                        get_stmt_id,
                    );
                    let child_id =
                        get_stmt_id(&format!("{}", child.statement), stmt_counter, stmt_ids);
                    let edge = (child_id.clone(), op_id.clone());
                    if edges_declared.insert(edge.clone()) {
                        writeln!(dot, "  {} -> {};", child_id, op_id).unwrap();
                    }
                }
            }
        }
    }

    for root in &proof.root_nodes {
        walk_node(
            root,
            &mut stmt_ids,
            &mut nodes_declared,
            &mut edges_declared,
            &mut stmt_counter,
            &mut op_counter,
            &mut dot,
            &mut get_stmt_id,
        );
    }

    writeln!(&mut dot, "}}").unwrap();
    dot
}

/// Escapes special characters for DOT labels.
fn escape(s: &str) -> String {
    s.replace('\\', "\\\\")
        .replace('"', "\\\"")
        .replace('\n', "\\n")
}

fn escape_md(s: &str) -> String {
    s.replace('\\', "\\\\")
        .replace('"', "&quot;")
        .replace('\n', "<br>")
}

/// Generates a Mermaid markdown diagram of the proof.
/// The diagram is compatible with GitHub-flavoured Mermaid.
pub fn mermaid_markdown(proof: &Proof) -> String {
    let mut md = String::new();
    writeln!(&mut md, "graph TD;").unwrap();
    let mut stmt_ids: HashMap<String, String> = HashMap::new();
    let mut nodes_declared: HashSet<String> = HashSet::new();
    let mut edges_declared: HashSet<(String, String)> = HashSet::new();
    let mut stmt_counter = 0usize;
    let mut op_counter = 0usize;

    let mut get_stmt_id = |s: &str, counter: &mut usize, map: &mut HashMap<String, String>| {
        map.entry(s.to_string())
            .or_insert_with(|| {
                let id = format!("S{}", *counter);
                *counter += 1;
                id
            })
            .clone()
    };

    #[allow(clippy::too_many_arguments)]
    fn walk(
        node: &Arc<ProofNode>,
        stmt_ids: &mut HashMap<String, String>,
        nodes_declared: &mut HashSet<String>,
        edges_declared: &mut HashSet<(String, String)>,
        stmt_counter: &mut usize,
        op_counter: &mut usize,
        md: &mut String,
        get_stmt_id: &mut impl FnMut(&str, &mut usize, &mut HashMap<String, String>) -> String,
    ) {
        // Skip the synthetic _request_goal node itself.
        if matches!(node.statement.predicate(),
            Predicate::Custom(cpr) if cpr.predicate().name == "_request_goal")
        {
            if let Justification::Custom(_, premises) = &node.justification {
                for child in premises {
                    walk(
                        child,
                        stmt_ids,
                        nodes_declared,
                        edges_declared,
                        stmt_counter,
                        op_counter,
                        md,
                        get_stmt_id,
                    );
                }
            }
            return;
        }

        let stmt_str = format!("{}", node.statement);
        let stmt_id = get_stmt_id(&stmt_str, stmt_counter, stmt_ids);
        if nodes_declared.insert(stmt_id.clone()) {
            writeln!(md, "  {}[\"{}\"];", stmt_id, escape_md(&stmt_str)).unwrap();
        }

        match &node.justification {
            Justification::Fact => {}
            Justification::ValueComparison(op) => {
                let op_id = format!("OP{}", *op_counter);
                *op_counter += 1;
                writeln!(md, "  {}(\"{:?}\");", op_id, op,).unwrap();
                if edges_declared.insert((op_id.clone(), stmt_id.clone())) {
                    writeln!(md, "  {} --> {};", op_id, stmt_id).unwrap();
                }
                node.statement
                    .args()
                    .iter()
                    .enumerate()
                    .for_each(|(i, arg)| match arg {
                        StatementArg::Key(k) => {
                            writeln!(
                                md,
                                "  {}_{}(\"{}\") --> {};",
                                op_id,
                                i,
                                escape_md(&format!("{}", k)),
                                op_id
                            )
                            .unwrap();
                        }
                        StatementArg::Literal(l) => {
                            writeln!(
                                md,
                                "  {}_{}(\"{}\") --> {};",
                                op_id,
                                i,
                                escape_md(&format!("{}", l)),
                                op_id
                            )
                            .unwrap();
                        }
                        _ => {}
                    });
            }
            Justification::Special(op) => {
                let op_id = format!("OP{}", *op_counter);
                *op_counter += 1;
                writeln!(md, "  {}(\"{:?}\");", op_id, op,).unwrap();
                if edges_declared.insert((op_id.clone(), stmt_id.clone())) {
                    writeln!(md, "  {} --> {};", op_id, stmt_id).unwrap();
                }
            }
            Justification::Custom(cpr, premises) => {
                let op_id = format!("OP{}", *op_counter);
                *op_counter += 1;
                writeln!(md, "  {}(\"{}\");", op_id, escape_md(&cpr.predicate().name)).unwrap();
                if edges_declared.insert((op_id.clone(), stmt_id.clone())) {
                    writeln!(md, "  {} --> {};", op_id, stmt_id).unwrap();
                }
                for child in premises {
                    if Predicate::Native(NativePredicate::None) == child.statement.predicate() {
                        continue;
                    }
                    walk(
                        child,
                        stmt_ids,
                        nodes_declared,
                        edges_declared,
                        stmt_counter,
                        op_counter,
                        md,
                        get_stmt_id,
                    );
                    let child_id =
                        get_stmt_id(&format!("{}", child.statement), stmt_counter, stmt_ids);
                    if edges_declared.insert((child_id.clone(), op_id.clone())) {
                        writeln!(md, "  {} --> {};", child_id, op_id).unwrap();
                    }
                }
            }
        }
    }

    for root in &proof.root_nodes {
        walk(
            root,
            &mut stmt_ids,
            &mut nodes_declared,
            &mut edges_declared,
            &mut stmt_counter,
            &mut op_counter,
            &mut md,
            &mut get_stmt_id,
        );
    }

    md
}
