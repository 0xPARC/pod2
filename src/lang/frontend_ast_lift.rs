//! Lifting pass for anonymous inline predicates
//!
//! This module transforms inline conjunctions (AND/OR blocks within predicate bodies)
//! into separate anonymous predicates. This is necessary because the middleware
//! `CustomPredicate` can only have a single conjunction type (AND or OR).
//!
//! Example transformation:
//! ```text
//! some_pred(A, B) = AND(
//!     AND(
//!         Equal(A["foo"], 123)
//!     )
//!     Equal(A["bar"], B)
//! )
//! ```
//!
//! Becomes:
//! ```text
//! some_pred$anon_0(A) = AND(
//!     Equal(A["foo"], 123)
//! )
//!
//! some_pred(A, B) = AND(
//!     some_pred$anon_0(A)
//!     Equal(A["bar"], B)
//! )
//! ```

use std::collections::HashSet;

use super::frontend_ast::{
    ArgSection, CustomPredicateDef, Identifier, StatementTmpl, StatementTmplArg, StatementTmplKind,
};

/// Lifts inline conjunctions to anonymous predicates
pub struct AnonPredicateLifter {
    /// Counter for generating unique names
    counter: usize,
    /// Generated anonymous predicates (in dependency order - inner predicates first)
    generated: Vec<CustomPredicateDef>,
}

impl AnonPredicateLifter {
    /// Create a new lifter
    fn new() -> Self {
        Self {
            counter: 0,
            generated: Vec::new(),
        }
    }

    /// Lift all inline conjunctions in the given predicates.
    /// Returns predicates in dependency order (anonymous first).
    pub fn lift_predicates(predicates: Vec<CustomPredicateDef>) -> Vec<CustomPredicateDef> {
        let mut lifter = Self::new();
        let mut result = Vec::new();

        for pred in predicates {
            let transformed = lifter.transform_predicate(pred);
            result.push(transformed);
        }

        // Anonymous predicates come first (they're already in dependency order from DFS)
        let mut final_predicates = lifter.generated;
        final_predicates.extend(result);

        final_predicates
    }

    /// Transform a single predicate, lifting any inline conjunctions in its statements.
    fn transform_predicate(&mut self, pred: CustomPredicateDef) -> CustomPredicateDef {
        let parent_name = pred.name.name.clone();

        // Collect all wildcards in scope (both public and private)
        let wildcards_in_scope: HashSet<String> = {
            let mut set: HashSet<String> = pred
                .args
                .public_args
                .iter()
                .map(|id| id.name.clone())
                .collect();
            if let Some(private_args) = &pred.args.private_args {
                set.extend(private_args.iter().map(|id| id.name.clone()));
            }
            set
        };

        // Transform statements
        let new_statements: Vec<StatementTmpl> = pred
            .statements
            .into_iter()
            .map(|stmt| self.transform_statement(stmt, &parent_name, &wildcards_in_scope))
            .collect();

        CustomPredicateDef {
            name: pred.name,
            args: pred.args,
            conjunction_type: pred.conjunction_type,
            statements: new_statements,
            span: pred.span,
        }
    }

    /// Transform a single statement, lifting inline conjunctions to anonymous predicates.
    fn transform_statement(
        &mut self,
        stmt: StatementTmpl,
        parent_name: &str,
        wildcards_in_scope: &HashSet<String>,
    ) -> StatementTmpl {
        match stmt.kind {
            StatementTmplKind::Call { .. } => {
                // Regular call - no transformation needed
                stmt
            }
            StatementTmplKind::InlineConjunction {
                conjunction_type,
                statements,
            } => {
                // Generate unique name for anonymous predicate
                let anon_name = self.generate_name(parent_name);

                // Collect all wildcards used in this inline conjunction
                let used_wildcards = collect_wildcards_from_statements(&statements);

                // Filter to only wildcards that are in scope
                let mut anon_args: Vec<String> = used_wildcards
                    .iter()
                    .filter(|w| wildcards_in_scope.contains(*w))
                    .cloned()
                    .collect();
                // Sort for deterministic ordering
                anon_args.sort();

                // Build the set of wildcards in scope for the anonymous predicate
                let anon_scope: HashSet<String> = anon_args.iter().cloned().collect();

                // Recursively transform nested statements
                let transformed_statements: Vec<StatementTmpl> = statements
                    .into_iter()
                    .map(|s| self.transform_statement(s, &anon_name, &anon_scope))
                    .collect();

                // Create anonymous predicate with public-only args
                let anon_pred = CustomPredicateDef {
                    name: Identifier {
                        name: anon_name.clone(),
                        span: None,
                    },
                    args: ArgSection {
                        public_args: anon_args
                            .iter()
                            .map(|name| Identifier {
                                name: name.clone(),
                                span: None,
                            })
                            .collect(),
                        private_args: None, // Anonymous predicates have no private args
                        span: None,
                    },
                    conjunction_type,
                    statements: transformed_statements,
                    span: None,
                };

                // Add to generated predicates (inner predicates are added first due to DFS)
                self.generated.push(anon_pred);

                // Replace inline conjunction with call to anonymous predicate
                let call_args: Vec<StatementTmplArg> = anon_args
                    .iter()
                    .map(|name| {
                        StatementTmplArg::Wildcard(Identifier {
                            name: name.clone(),
                            span: None,
                        })
                    })
                    .collect();

                StatementTmpl::call(
                    Identifier {
                        name: anon_name,
                        span: None,
                    },
                    call_args,
                    stmt.span,
                )
            }
        }
    }

    /// Generate a unique name for an anonymous predicate
    fn generate_name(&mut self, parent_name: &str) -> String {
        let name = format!("{}$anon_{}", parent_name, self.counter);
        self.counter += 1;
        name
    }
}

/// Collect all wildcard names from a list of statements
fn collect_wildcards_from_statements(statements: &[StatementTmpl]) -> HashSet<String> {
    let mut wildcards = HashSet::new();
    for stmt in statements {
        collect_wildcards_from_statement_recursive(stmt, &mut wildcards);
    }
    wildcards
}

/// Recursively collect wildcards from a statement (including nested inline conjunctions)
fn collect_wildcards_from_statement_recursive(
    stmt: &StatementTmpl,
    wildcards: &mut HashSet<String>,
) {
    match &stmt.kind {
        StatementTmplKind::Call { args, .. } => {
            for arg in args {
                match arg {
                    StatementTmplArg::Wildcard(id) => {
                        wildcards.insert(id.name.clone());
                    }
                    StatementTmplArg::AnchoredKey(ak) => {
                        wildcards.insert(ak.root.name.clone());
                    }
                    StatementTmplArg::Literal(_) => {}
                }
            }
        }
        StatementTmplKind::InlineConjunction { statements, .. } => {
            for inner_stmt in statements {
                collect_wildcards_from_statement_recursive(inner_stmt, wildcards);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::{
        frontend_ast::{parse, ConjunctionType},
        parser::parse_podlang,
    };

    fn parse_predicates(input: &str) -> Vec<CustomPredicateDef> {
        let parsed = parse_podlang(input).expect("Failed to parse");
        let doc =
            parse::parse_document(parsed.into_iter().next().unwrap()).expect("Failed to parse");
        doc.items
            .into_iter()
            .filter_map(|item| {
                if let crate::lang::frontend_ast::DocumentItem::CustomPredicateDef(pred) = item {
                    Some(pred)
                } else {
                    None
                }
            })
            .collect()
    }

    #[test]
    fn test_no_inline_conjunctions() {
        let input = r#"
            simple_pred(A, B) = AND(
                Equal(A["foo"], 123)
                Equal(A["bar"], B)
            )
        "#;

        let predicates = parse_predicates(input);
        let result = AnonPredicateLifter::lift_predicates(predicates);

        // No inline conjunctions, so no anonymous predicates generated
        assert_eq!(result.len(), 1);
        assert_eq!(result[0].name.name, "simple_pred");
    }

    #[test]
    fn test_simple_inline_and() {
        let input = r#"
            my_pred(A, B) = AND(
                AND(
                    Equal(A["foo"], 123)
                )
                Equal(A["bar"], B)
            )
        "#;

        let predicates = parse_predicates(input);
        let result = AnonPredicateLifter::lift_predicates(predicates);

        // Should generate 2 predicates: anon first, then original
        assert_eq!(result.len(), 2);
        assert_eq!(result[0].name.name, "my_pred$anon_0");
        assert_eq!(result[1].name.name, "my_pred");

        // Anonymous predicate should have 1 statement
        assert_eq!(result[0].statements.len(), 1);
        // And should have A as its only public arg
        assert_eq!(result[0].args.public_args.len(), 1);
        assert_eq!(result[0].args.public_args[0].name, "A");

        // Original predicate should have 2 statements
        assert_eq!(result[1].statements.len(), 2);
        // First statement should be call to anonymous predicate
        assert_eq!(
            result[1].statements[0].predicate().unwrap().name,
            "my_pred$anon_0"
        );
    }

    #[test]
    fn test_deeply_nested() {
        let input = r#"
            deep(A) = AND(
                OR(
                    AND(
                        Equal(A["x"], 1)
                    )
                    Equal(A["y"], 2)
                )
            )
        "#;

        let predicates = parse_predicates(input);
        let result = AnonPredicateLifter::lift_predicates(predicates);

        // Should generate 3 predicates:
        // Processing order: deep's OR gets processed, which processes its AND child
        // Counter is global, so:
        // 1. deep$anon_0$anon_1 (innermost AND, named from its parent deep$anon_0 + counter 1)
        // 2. deep$anon_0 (OR, counter 0)
        // 3. deep (original)
        assert_eq!(result.len(), 3);
        assert_eq!(result[0].name.name, "deep$anon_0$anon_1");
        assert_eq!(result[1].name.name, "deep$anon_0");
        assert_eq!(result[2].name.name, "deep");

        // Innermost is AND
        assert_eq!(result[0].conjunction_type, ConjunctionType::And);
        // Middle is OR
        assert_eq!(result[1].conjunction_type, ConjunctionType::Or);
    }

    #[test]
    fn test_uses_parent_private_wildcard() {
        let input = r#"
            my_pred(A, private: B) = AND(
                AND(
                    Equal(A["foo"], B["bar"])
                )
            )
        "#;

        let predicates = parse_predicates(input);
        let result = AnonPredicateLifter::lift_predicates(predicates);

        // Should work - B becomes public arg of anon pred
        assert_eq!(result.len(), 2);
        assert_eq!(result[0].name.name, "my_pred$anon_0");

        // Anonymous predicate should have both A and B as public args
        let anon_args: Vec<&str> = result[0]
            .args
            .public_args
            .iter()
            .map(|id| id.name.as_str())
            .collect();
        assert!(anon_args.contains(&"A"));
        assert!(anon_args.contains(&"B"));
    }

    #[test]
    fn test_arg_subset() {
        let input = r#"
            my_pred(A, B, C) = AND(
                AND(
                    Equal(A["foo"], 123)
                )
                Equal(B["bar"], C)
            )
        "#;

        let predicates = parse_predicates(input);
        let result = AnonPredicateLifter::lift_predicates(predicates);

        assert_eq!(result.len(), 2);

        // Anonymous predicate should only have A (the only wildcard it uses)
        assert_eq!(result[0].args.public_args.len(), 1);
        assert_eq!(result[0].args.public_args[0].name, "A");
    }
}
