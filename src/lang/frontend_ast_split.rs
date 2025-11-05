//! Predicate splitting for frontend AST
//!
//! This module implements automatic predicate splitting when predicates exceed
//! middleware constraints.
//!
//! When splitting a predicate, we try to group statements that use the same
//! wildcards together. However, if a private wildcard must be used across a
//! split boundary, it must be promoted to a public argument in the latter
//! predicate, to ensure that it is bound to the same value in both predicates.
//!
//! A wildcard is "live" at a split boundary if it is used in a statement on both
//! sides of the boundary. We want to minimize the number of live wildcards at
//! split boundaries, to minimize the number of promotions required.
//!
//! We use a greedy algorithm to order the statements in a predicate to minimize
//! the number of live wildcards at split boundaries.

use std::collections::{HashMap, HashSet};

// SplittingError is now defined in error.rs
pub use crate::lang::error::SplittingError;
use crate::{lang::frontend_ast::*, middleware::Params};

/// A link in the predicate chain
#[derive(Debug, Clone)]
pub struct ChainLink {
    /// Statements in this link
    pub statements: Vec<StatementTmpl>,
    /// Public arguments coming into this link
    pub public_args_in: Vec<String>,
    /// Private arguments used only in this link
    pub private_args: Vec<String>,
    /// Public arguments promoted to pass to next link (empty if last link)
    pub public_args_out: Vec<String>,
}

/// Wildcard usage information
#[derive(Debug, Clone)]
struct WildcardUsage {
    /// Indices of statements using this wildcard
    used_in_statements: HashSet<usize>,
}

/// Early validation: Check if predicate is fundamentally splittable
pub fn validate_predicate_is_splittable(
    pred: &CustomPredicateDef,
    params: &Params,
) -> Result<(), SplittingError> {
    let public_args = pred.args.public_args.len();

    // Check: public args must fit in operation arg limit
    if public_args > params.max_statement_args {
        return Err(SplittingError::TooManyPublicArgs {
            predicate: pred.name.name.clone(),
            count: public_args,
            max_allowed: params.max_statement_args,
            message: "Public arguments exceed max operation args - cannot call this predicate"
                .to_string(),
        });
    }

    Ok(())
}

/// Split a predicate into a chain if it exceeds statement limit
pub fn split_predicate_if_needed(
    pred: CustomPredicateDef,
    params: &Params,
) -> Result<Vec<CustomPredicateDef>, SplittingError> {
    // Early validation
    validate_predicate_is_splittable(&pred, params)?;

    // If within limits, no splitting needed
    if pred.statements.len() <= params.max_custom_predicate_arity {
        return Ok(vec![pred]);
    }

    // Need to split - execute the splitting algorithm
    let chain = split_into_chain(pred, params)?;

    Ok(chain)
}

fn analyze_wildcards(statements: &[StatementTmpl]) -> HashMap<String, WildcardUsage> {
    let mut usage: HashMap<String, WildcardUsage> = HashMap::new();

    for (idx, stmt) in statements.iter().enumerate() {
        let wildcards = collect_wildcards_from_statement(stmt);

        for wildcard in wildcards {
            usage
                .entry(wildcard.clone())
                .or_insert_with(|| WildcardUsage {
                    used_in_statements: HashSet::new(),
                })
                .used_in_statements
                .insert(idx);
        }
    }

    usage
}

/// Collect all wildcard names from a statement
fn collect_wildcards_from_statement(stmt: &StatementTmpl) -> HashSet<String> {
    let mut wildcards = HashSet::new();

    for arg in &stmt.args {
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

    wildcards
}

/// Order constraints optimally to minimize liveness at boundaries
fn order_constraints_optimally(
    statements: Vec<StatementTmpl>,
    _usage: &HashMap<String, WildcardUsage>,
    params: &Params,
) -> Vec<StatementTmpl> {
    // If no splitting needed, preserve original order
    if statements.len() <= params.max_custom_predicate_arity {
        return statements;
    }

    let mut ordered = Vec::new();
    let mut remaining: HashSet<usize> = (0..statements.len()).collect();
    let mut active_wildcards: HashSet<String> = HashSet::new();

    while !remaining.is_empty() {
        let best_idx = find_best_next_statement(
            &statements,
            &remaining,
            &active_wildcards,
            ordered.len(),
            params,
        );

        remaining.remove(&best_idx);
        let stmt = &statements[best_idx];
        ordered.push(stmt.clone());

        // Update active wildcards
        let stmt_wildcards = collect_wildcards_from_statement(stmt);
        active_wildcards.extend(stmt_wildcards);

        // Remove wildcards no longer needed by remaining statements
        let needed_later: HashSet<_> = remaining
            .iter()
            .flat_map(|&i| collect_wildcards_from_statement(&statements[i]))
            .collect();
        active_wildcards.retain(|w| needed_later.contains(w));
    }

    ordered
}

/// Compute tie-breaker metrics for deterministic ordering when scores are equal
/// Returns (simplicity, public_closure, negative_fanout) tuple for use in max_by_key
fn compute_tie_breakers(
    stmt: &StatementTmpl,
    active_wildcards: &HashSet<String>,
    statements: &[StatementTmpl],
    remaining: &HashSet<usize>,
) -> (usize, usize, i32) {
    let stmt_wildcards = collect_wildcards_from_statement(stmt);

    // Metric 1: Simplicity - prefer statements with fewer wildcards
    let simplicity = usize::MAX - stmt_wildcards.len();

    // Metric 2: Public closure - prefer statements that close active wildcards
    // (wildcards that won't be needed by any remaining statements)
    let needed_later: HashSet<String> = remaining
        .iter()
        .flat_map(|&i| collect_wildcards_from_statement(&statements[i]))
        .collect();

    let closes_count = stmt_wildcards
        .intersection(active_wildcards)
        .filter(|w| !needed_later.contains(*w))
        .count();

    // Metric 3: Fanout - prefer statements with lower future usage
    // (number of remaining statements that use any wildcard from this statement)
    let fanout = remaining
        .iter()
        .filter(|&&i| {
            let other_wildcards = collect_wildcards_from_statement(&statements[i]);
            !stmt_wildcards.is_disjoint(&other_wildcards)
        })
        .count();

    (simplicity, closes_count, -(fanout as i32))
}

/// Find the best next statement to add based on scoring heuristic
fn find_best_next_statement(
    statements: &[StatementTmpl],
    remaining: &HashSet<usize>,
    active_wildcards: &HashSet<String>,
    ordered_count: usize,
    params: &Params,
) -> usize {
    // Calculate distance to next split point
    let bucket_size = params.max_custom_predicate_arity - 1; // Reserve slot for chain call
    let distance_to_split = bucket_size - (ordered_count % bucket_size);
    let approaching_split = distance_to_split <= 2;

    remaining
        .iter()
        .max_by_key(|&&idx| {
            let primary_score = score_statement(
                &statements[idx],
                active_wildcards,
                statements,
                remaining,
                approaching_split,
            );
            let tie_breakers =
                compute_tie_breakers(&statements[idx], active_wildcards, statements, remaining);
            (primary_score, tie_breakers)
        })
        .copied()
        .unwrap()
}

/// Score a statement based on how well it minimizes liveness
fn score_statement(
    stmt: &StatementTmpl,
    active_wildcards: &HashSet<String>,
    statements: &[StatementTmpl],
    remaining: &HashSet<usize>,
    approaching_split: bool,
) -> i32 {
    let stmt_wildcards = collect_wildcards_from_statement(stmt);

    // How many active wildcards does this reuse?
    let reuse_count = stmt_wildcards.intersection(active_wildcards).count();

    // How many new wildcards does this introduce?
    let new_wildcard_count = stmt_wildcards.difference(active_wildcards).count();

    // After adding this statement, what would be active?
    let mut projected_active = active_wildcards.clone();
    projected_active.extend(stmt_wildcards.clone());

    // Which wildcards are still needed by other remaining statements?
    let needed_later: HashSet<String> = remaining
        .iter()
        .flat_map(|&i| collect_wildcards_from_statement(&statements[i]))
        .collect();

    // Wildcards we can close = active now but not needed later
    projected_active.retain(|w| needed_later.contains(w));
    let still_active_count = projected_active.len();

    // Base score calculation
    // - Prefer statements that reuse active wildcards (don't introduce new liveness)
    // - Penalize introducing new wildcards (increases liveness)
    // - Penalize keeping many wildcards active (higher liveness)
    let base_score = (reuse_count * 3) as i32
        - (new_wildcard_count * 4) as i32
        - (still_active_count * 2) as i32;

    // Look-ahead bonus: when approaching split, heavily favor closing wildcards
    if approaching_split {
        let closes_count = active_wildcards.len() + new_wildcard_count - still_active_count;
        base_score + (closes_count * 10) as i32
    } else {
        base_score
    }
}

/// Calculate which wildcards are live at a split boundary
fn calculate_live_wildcards(
    before_split: &[StatementTmpl],
    after_split: &[StatementTmpl],
) -> HashSet<String> {
    let before: HashSet<_> = before_split
        .iter()
        .flat_map(collect_wildcards_from_statement)
        .collect();

    let after: HashSet<_> = after_split
        .iter()
        .flat_map(collect_wildcards_from_statement)
        .collect();

    // Live = in both sets (crosses boundary)
    before.intersection(&after).cloned().collect()
}

/// Generate a refactor suggestion for wildcards crossing a boundary
fn generate_refactor_suggestion(
    crossing_wildcards: &[String],
    ordered_statements: &[StatementTmpl],
    _pos: usize,
    _end: usize,
) -> Option<crate::lang::error::RefactorSuggestion> {
    use crate::lang::error::RefactorSuggestion;

    if crossing_wildcards.is_empty() {
        return None;
    }

    // Analyze the span of each crossing wildcard
    let mut wildcard_spans: Vec<(String, usize, usize, usize)> = Vec::new();

    for wildcard in crossing_wildcards {
        let mut first_use = None;
        let mut last_use = None;

        for (i, stmt) in ordered_statements.iter().enumerate() {
            let wildcards = collect_wildcards_from_statement(stmt);
            if wildcards.contains(wildcard) {
                if first_use.is_none() {
                    first_use = Some(i);
                }
                last_use = Some(i);
            }
        }

        if let (Some(first), Some(last)) = (first_use, last_use) {
            let span = last - first;
            wildcard_spans.push((wildcard.clone(), first, last, span));
        }
    }

    // Sort by span (largest first)
    wildcard_spans.sort_by(|a, b| b.3.cmp(&a.3));

    if let Some((wildcard, first, last, span)) = wildcard_spans.first() {
        // If a single wildcard has a large span, suggest reducing it
        if *span > 3 {
            return Some(RefactorSuggestion::ReduceWildcardSpan {
                wildcard: wildcard.clone(),
                first_use: *first,
                last_use: *last,
                span: *span,
            });
        }
    }

    // If multiple wildcards cross the boundary, suggest grouping
    if crossing_wildcards.len() > 1 {
        return Some(RefactorSuggestion::GroupWildcardUsages {
            wildcards: crossing_wildcards.to_vec(),
        });
    }

    None
}

/// Split into chain using bucket-filling approach
fn split_into_chain(
    pred: CustomPredicateDef,
    params: &Params,
) -> Result<Vec<CustomPredicateDef>, SplittingError> {
    let original_name = pred.name.name.clone();
    let conjunction = pred.conjunction_type;

    let usage = analyze_wildcards(&pred.statements);

    let ordered_statements = order_constraints_optimally(pred.statements, &usage, params);

    let original_public_args: Vec<String> = pred
        .args
        .public_args
        .iter()
        .map(|id| id.name.clone())
        .collect();

    let mut chain_links = Vec::new();
    let mut pos = 0;
    let mut incoming_public = original_public_args.clone();

    while pos < ordered_statements.len() {
        let remaining = ordered_statements.len() - pos;
        let is_last = remaining <= params.max_custom_predicate_arity;

        let bucket_size = if is_last {
            remaining // Last predicate uses all remaining
        } else {
            params.max_custom_predicate_arity - 1 // Reserve slot for chain call
        };

        let end = pos + bucket_size;

        // Calculate liveness at this split boundary
        let live_at_boundary = if is_last {
            HashSet::new()
        } else {
            calculate_live_wildcards(&ordered_statements[pos..end], &ordered_statements[end..])
        };

        // Check: Can we fit promoted wildcards in public args?
        // Need to account for possible overlap between incoming_public and live_at_boundary
        let incoming_set: HashSet<_> = incoming_public.iter().cloned().collect();
        let new_promotions: Vec<_> = live_at_boundary
            .iter()
            .filter(|w| !incoming_set.contains(*w))
            .cloned()
            .collect();
        let total_public = incoming_public.len() + new_promotions.len();
        if total_public > params.max_statement_args {
            let context = crate::lang::error::SplitContext {
                split_index: chain_links.len(),
                statement_range: (pos, end),
                incoming_public: incoming_public.clone(),
                crossing_wildcards: new_promotions.clone(),
                total_public,
            };

            let suggestion =
                generate_refactor_suggestion(&new_promotions, &ordered_statements, pos, end);

            return Err(SplittingError::TooManyPublicArgsAtSplit {
                predicate: original_name.clone(),
                context: Box::new(context),
                max_allowed: params.max_statement_args,
                suggestion: suggestion.map(Box::new),
            });
        }

        // Calculate private args (used in this segment but not incoming and not outgoing)
        let segment_wildcards: HashSet<_> = ordered_statements[pos..end]
            .iter()
            .flat_map(collect_wildcards_from_statement)
            .collect();

        let mut private_args: Vec<String> = segment_wildcards
            .difference(&incoming_set)
            .filter(|w| !live_at_boundary.contains(*w))
            .cloned()
            .collect();
        private_args.sort(); // Deterministic ordering

        // Check: Total args constraint (incoming + new promotions + private)
        let public_count = incoming_public.len() + new_promotions.len();
        let private_count = private_args.len();
        let total_args = public_count + private_count;
        if total_args > params.max_custom_predicate_wildcards {
            return Err(SplittingError::TooManyTotalArgsInChainLink {
                predicate: original_name.clone(),
                link_index: chain_links.len(),
                public_count,
                private_count,
                total_count: total_args,
                max_allowed: params.max_custom_predicate_wildcards,
            });
        }

        let mut public_args_out: Vec<String> = live_at_boundary.iter().cloned().collect();
        public_args_out.sort(); // Deterministic ordering

        chain_links.push(ChainLink {
            statements: ordered_statements[pos..end].to_vec(),
            public_args_in: incoming_public.clone(),
            private_args,
            public_args_out: public_args_out.clone(),
        });

        pos = end;

        // Next link's incoming public args = current incoming + newly promoted live wildcards
        // Only add wildcards that aren't already in incoming_public to avoid duplicates
        for wildcard in public_args_out {
            if !incoming_set.contains(&wildcard) {
                incoming_public.push(wildcard);
            }
        }
    }

    let chain_predicates =
        generate_chain_predicates(&original_name, chain_links, conjunction, params)?;

    validate_chain(&chain_predicates, &original_name, params)?;

    Ok(chain_predicates)
}

/// Phase 4: Generate synthetic predicates from chain links
fn generate_chain_predicates(
    original_name: &str,
    chain_links: Vec<ChainLink>,
    conjunction: ConjunctionType,
    _params: &Params,
) -> Result<Vec<CustomPredicateDef>, SplittingError> {
    let mut predicates = Vec::new();

    for (i, link) in chain_links.iter().enumerate() {
        let pred_name = if i == 0 {
            Identifier {
                name: original_name.to_string(),
                span: None,
            }
        } else {
            Identifier {
                name: format!("{}_{}", original_name, i),
                span: None,
            }
        };

        let is_last = i == chain_links.len() - 1;
        let mut statements = link.statements.clone();

        // Add chain call if not last
        if !is_last {
            let next_pred_name = Identifier {
                name: format!("{}_{}", original_name, i + 1),
                span: None,
            };

            // Create arguments for chain call: all public args (incoming + promoted)
            let mut chain_call_args = Vec::new();
            for arg_name in &link.public_args_in {
                chain_call_args.push(StatementTmplArg::Wildcard(Identifier {
                    name: arg_name.clone(),
                    span: None,
                }));
            }
            for arg_name in &link.public_args_out {
                chain_call_args.push(StatementTmplArg::Wildcard(Identifier {
                    name: arg_name.clone(),
                    span: None,
                }));
            }

            let chain_call = StatementTmpl {
                predicate: next_pred_name,
                args: chain_call_args,
                span: None,
            };

            statements.push(chain_call);
        }

        // Build public args (incoming)
        let public_args: Vec<Identifier> = link
            .public_args_in
            .iter()
            .map(|name| Identifier {
                name: name.clone(),
                span: None,
            })
            .collect();

        // Build private args (private + promoted for next)
        let mut private_arg_names = link.private_args.clone();
        if !is_last {
            private_arg_names.extend(link.public_args_out.clone());
        }

        let private_args = if private_arg_names.is_empty() {
            None
        } else {
            Some(
                private_arg_names
                    .into_iter()
                    .map(|name| Identifier { name, span: None })
                    .collect(),
            )
        };

        predicates.push(CustomPredicateDef {
            name: pred_name,
            args: ArgSection {
                public_args,
                private_args,
                span: None,
            },
            conjunction_type: conjunction,
            statements,
            span: None,
        });
    }

    Ok(predicates)
}

/// Phase 5: Validate the generated chain
fn validate_chain(
    chain: &[CustomPredicateDef],
    original_name: &str,
    params: &Params,
) -> Result<(), SplittingError> {
    if chain.len() > params.max_custom_batch_size {
        return Err(SplittingError::TooManyPredicatesInChain {
            predicate: original_name.to_string(),
            count: chain.len(),
            max_allowed: params.max_custom_batch_size,
        });
    }

    for pred in chain {
        // Each predicate should have ≤ max_statements
        assert!(pred.statements.len() <= params.max_custom_predicate_arity);

        // Public args should fit
        assert!(pred.args.public_args.len() <= params.max_statement_args);

        // Total args should fit
        let total =
            pred.args.public_args.len() + pred.args.private_args.as_ref().map_or(0, |v| v.len());
        assert!(total <= params.max_custom_predicate_wildcards);
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::{frontend_ast::parse::parse_document, parser::parse_podlang};

    fn parse_predicate(input: &str) -> CustomPredicateDef {
        let parsed = parse_podlang(input).expect("Failed to parse");
        let document = parse_document(parsed.into_iter().next().unwrap()).expect("Failed to parse");

        for item in document.items {
            if let DocumentItem::CustomPredicateDef(pred) = item {
                return pred;
            }
        }

        panic!("No custom predicate found");
    }

    #[test]
    fn test_validate_splittable() {
        let input = r#"
            my_pred(A, B) = AND (
                Equal(A, B)
            )
        "#;

        let pred = parse_predicate(input);
        let params = Params::default();

        assert!(validate_predicate_is_splittable(&pred, &params).is_ok());
    }

    #[test]
    fn test_validate_too_many_public_args() {
        let input = r#"
            my_pred(A, B, C, D, E, F) = AND (
                Equal(A, B)
            )
        "#;

        let pred = parse_predicate(input);
        let params = Params::default(); // max_statement_args = 5

        let result = validate_predicate_is_splittable(&pred, &params);
        assert!(matches!(
            result,
            Err(SplittingError::TooManyPublicArgs { .. })
        ));
    }

    #[test]
    fn test_no_split_needed() {
        let input = r#"
            my_pred(A, B) = AND (
                Equal(A["x"], B["y"])
                Equal(A["z"], 1)
            )
        "#;

        let pred = parse_predicate(input);
        let params = Params::default();

        let result = split_predicate_if_needed(pred, &params);
        assert!(result.is_ok());

        let chain = result.unwrap();
        assert_eq!(chain.len(), 1); // No split needed
    }

    #[test]
    fn test_simple_split() {
        let input = r#"
            my_pred(A) = AND (
                Equal(A["a"], 1)
                Equal(A["b"], 2)
                Equal(A["c"], 3)
                Equal(A["d"], 4)
                Equal(A["e"], 5)
                Equal(A["f"], 6)
            )
        "#;

        let pred = parse_predicate(input);
        let params = Params::default(); // max_custom_predicate_arity = 5

        let result = split_predicate_if_needed(pred, &params);
        assert!(result.is_ok());

        let chain = result.unwrap();
        assert_eq!(chain.len(), 2); // Should split into 2 predicates

        // First predicate: 4 statements + chain call = 5
        assert_eq!(chain[0].statements.len(), 5);

        // Second predicate: 2 remaining statements
        assert_eq!(chain[1].statements.len(), 2);
    }

    #[test]
    fn test_split_with_private_wildcards() {
        let input = r#"
            complex(A, B, private: T1, T2) = AND (
                Equal(T1["x"], A["y"])
                Equal(T1["z"], 100)
                Equal(T2["a"], T1["x"])
                HashOf(T2["b"], B)
                Equal(A["result"], T2["a"])
                Equal(B["final"], T2["b"])
            )
        "#;

        let pred = parse_predicate(input);
        let params = Params::default(); // max_custom_predicate_arity = 5

        let result = split_predicate_if_needed(pred, &params);
        assert!(result.is_ok());

        let chain = result.unwrap();
        assert_eq!(chain.len(), 2); // Should split into 2 predicates

        // First predicate should have wildcards that cross boundary promoted
        // Check that chain call is present
        let last_stmt = &chain[0].statements.last().unwrap();
        assert_eq!(last_stmt.predicate.name, "complex_1");
    }

    #[test]
    fn test_split_into_three_predicates() {
        let input = r#"
            large_pred(A) = AND (
                Equal(A["a"], 1)
                Equal(A["b"], 2)
                Equal(A["c"], 3)
                Equal(A["d"], 4)
                Equal(A["e"], 5)
                Equal(A["f"], 6)
                Equal(A["g"], 7)
                Equal(A["h"], 8)
                Equal(A["i"], 9)
                Equal(A["j"], 10)
                Equal(A["k"], 11)
            )
        "#;

        let pred = parse_predicate(input);
        let params = Params::default(); // max_custom_predicate_arity = 5

        let result = split_predicate_if_needed(pred, &params);
        assert!(result.is_ok());

        let chain = result.unwrap();
        assert_eq!(chain.len(), 3); // Should split into 3 predicates

        // First: 4 + chain call = 5
        assert_eq!(chain[0].statements.len(), 5);
        // Second: 4 + chain call = 5
        assert_eq!(chain[1].statements.len(), 5);
        // Third: 3 remaining
        assert_eq!(chain[2].statements.len(), 3);
    }

    #[test]
    fn test_no_duplicate_promoted_wildcards() {
        // Test that a wildcard used across multiple chain boundaries
        // doesn't get duplicated in incoming_public
        let input = r#"
            reuse_pred(A, private: T) = AND (
                Equal(T["x"], A["start"])
                Equal(T["y"], 1)
                Equal(T["z"], 2)
                Equal(T["w"], 3)
                Equal(A["mid"], T["x"])
                Equal(T["a"], 4)
                Equal(T["b"], 5)
                Equal(T["c"], 6)
                Equal(A["end"], T["x"])
            )
        "#;

        let pred = parse_predicate(input);
        let params = Params::default();

        let result = split_predicate_if_needed(pred, &params);
        assert!(result.is_ok());

        let chain = result.unwrap();
        // Should split into 2 predicates
        // T is used in first segment and crosses to second, then used again in second
        assert_eq!(chain.len(), 2);

        // Check that second predicate's public args don't have duplicates
        let second_pred_public_count = chain[1].args.public_args.len();
        let second_pred_public_names: Vec<_> = chain[1]
            .args
            .public_args
            .iter()
            .map(|id| &id.name)
            .collect();
        let unique_count = second_pred_public_names
            .iter()
            .collect::<std::collections::HashSet<_>>()
            .len();

        assert_eq!(
            second_pred_public_count, unique_count,
            "Public args should not contain duplicates"
        );
    }

    #[test]
    fn test_greedy_ordering_reduces_liveness() {
        // This test verifies that our greedy ordering algorithm reduces wildcard liveness
        // by clustering statements that use the same wildcards together.
        //
        // The predicate has 8 statements using 3 private wildcards (T1, T2, T3):
        // - T1 used in statements 1, 4, 7
        // - T2 used in statements 2, 5, 8
        // - T3 used in statements 3, 6
        //
        // NAIVE ORDERING (original order):
        // Would interleave T1, T2, T3 usage throughout the predicate.
        // When splitting at statement limit (5 statements per predicate):
        //   Predicate 1: statements 1-5 (introduces T1, T2, T3 - none complete)
        //   Predicate 2: statements 6-8 (all 3 wildcards still live)
        // Result: 2 public args (A, B) + 3 promoted wildcards = 5 total in predicate 2
        //
        // GREEDY ORDERING (our algorithm):
        // Clusters statements by wildcard to minimize liveness:
        // Groups T1 statements together, then T2, then T3
        //   Predicate 1: completes some wildcards before the split point
        //   Predicate 2: fewer wildcards need to cross the boundary
        // Result: 2 public args (A, B) + 1-2 promoted wildcards = 3-4 total in predicate 2
        let input = r#"
            clustered(A, B, private: T1, T2, T3) = AND (
                Equal(T1["x"], 1)
                Equal(T2["y"], 2)
                Equal(T3["z"], 3)
                Equal(T1["a"], 4)
                Equal(T2["b"], 5)
                Equal(T3["c"], 6)
                Equal(T1["d"], A["result"])
                Equal(T2["e"], B["value"])
            )
        "#;

        let pred = parse_predicate(input);
        let params = Params::default();

        let result = split_predicate_if_needed(pred, &params);
        assert!(result.is_ok());

        let chain = result.unwrap();
        assert_eq!(chain.len(), 2, "Predicate should split into 2 links");

        let second_pred = &chain[1];
        let second_pred_public_count = second_pred.args.public_args.len();

        // Verify greedy ordering achieves better results than naive ordering would
        // Started with 2 public args (A, B)
        // Naive would have: 2 + 3 promoted = 5 public args in second predicate
        // Greedy achieves: 2 + 1-2 promoted = 3-4 public args in second predicate
        assert!(
            second_pred_public_count <= 4,
            "Greedy ordering should reduce promotions to ≤4 public args, but got {}",
            second_pred_public_count
        );
    }

    #[test]
    fn test_error_message_formatting() {
        // Test that error messages format correctly with detailed context
        // We'll manually construct the error to test the formatting
        use crate::lang::error::{RefactorSuggestion, SplitContext};

        let context = SplitContext {
            split_index: 0,
            statement_range: (0, 4),
            incoming_public: vec!["A".to_string(), "B".to_string(), "C".to_string()],
            crossing_wildcards: vec!["T1".to_string(), "T2".to_string(), "T3".to_string()],
            total_public: 6,
        };

        let suggestion = Some(RefactorSuggestion::GroupWildcardUsages {
            wildcards: vec!["T1".to_string(), "T2".to_string(), "T3".to_string()],
        });

        let error = SplittingError::TooManyPublicArgsAtSplit {
            predicate: "test_pred".to_string(),
            context: Box::new(context),
            max_allowed: 5,
            suggestion: suggestion.map(Box::new),
        };

        let error_msg = format!("{}", error);

        // Verify the error message contains all the key information
        assert!(error_msg.contains("test_pred"));
        assert!(error_msg.contains("split boundary 0"));
        assert!(error_msg.contains("3 incoming public"));
        assert!(error_msg.contains("3 crossing wildcards"));
        assert!(error_msg.contains("= 6 total"));
        assert!(error_msg.contains("exceeds max of 5"));
        assert!(error_msg.contains("Statements 0-4"));
        assert!(error_msg.contains("Incoming public args: A, B, C"));
        assert!(error_msg.contains("Wildcards crossing this boundary: T1, T2, T3"));
        assert!(error_msg.contains("Suggestion:"));
        assert!(error_msg.contains("Group operations for wildcards"));

        eprintln!("\n=== Example Error Message ===\n{}\n", error_msg);
    }

    #[test]
    fn test_error_too_many_total_args_formatting() {
        // Test the TooManyTotalArgsInChainLink error message formatting
        let error = SplittingError::TooManyTotalArgsInChainLink {
            predicate: "huge_pred".to_string(),
            link_index: 1,
            public_count: 5,
            private_count: 6,
            total_count: 11,
            max_allowed: 10,
        };

        let error_msg = format!("{}", error);

        // Verify the error message includes breakdown
        assert!(error_msg.contains("huge_pred"));
        assert!(error_msg.contains("chain link 1"));
        assert!(error_msg.contains("5 public"));
        assert!(error_msg.contains("6 private"));
        assert!(error_msg.contains("= 11 total"));
        assert!(error_msg.contains("exceeds max of 10"));

        eprintln!("\n=== Example TooManyTotalArgs Error ===\n{}\n", error_msg);
    }

    #[test]
    fn test_refactor_suggestion_reduce_wildcard_span() {
        // Test the "reduce wildcard span" suggestion formatting
        use crate::lang::error::RefactorSuggestion;

        let suggestion = RefactorSuggestion::ReduceWildcardSpan {
            wildcard: "T".to_string(),
            first_use: 0,
            last_use: 7,
            span: 7,
        };

        let suggestion_text = suggestion.format();

        // Verify the suggestion formats correctly
        assert!(suggestion_text.contains("'T'"));
        assert!(suggestion_text.contains("used across 7 statements"));
        assert!(suggestion_text.contains("statements 0-7"));
        assert!(suggestion_text.contains("grouping all 'T' operations together"));

        eprintln!(
            "\n=== Example ReduceWildcardSpan Suggestion ===\n{}\n",
            suggestion_text
        );
    }

    #[test]
    fn test_refactor_suggestion_group_wildcards() {
        // Test the "group wildcard usages" suggestion formatting
        use crate::lang::error::RefactorSuggestion;

        let suggestion = RefactorSuggestion::GroupWildcardUsages {
            wildcards: vec!["T1".to_string(), "T2".to_string(), "T3".to_string()],
        };

        let suggestion_text = suggestion.format();

        // Verify the suggestion formats correctly
        assert!(suggestion_text.contains("Group operations for wildcards"));
        assert!(suggestion_text.contains("T1, T2, T3"));
        assert!(suggestion_text.contains("used across multiple segments"));

        eprintln!(
            "\n=== Example GroupWildcardUsages Suggestion ===\n{}\n",
            suggestion_text
        );
    }
}
