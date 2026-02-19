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

use std::{cmp::Reverse, collections::HashSet};

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
    /// Private wildcards promoted to public for the next link (empty if last link)
    pub promoted_wildcards: Vec<String>,
}

/// Information about a single piece of a split predicate chain
#[derive(Debug, Clone)]
pub struct SplitChainPiece {
    /// Name of this predicate piece (e.g., "foo_1")
    pub name: String,
    /// Number of "real" statements in this piece (excludes chain call)
    pub real_statement_count: usize,
    /// Whether this piece has a chain call to the next piece
    pub has_chain_call: bool,
}

/// Metadata about a split predicate chain
#[derive(Debug, Clone)]
pub struct SplitChainInfo {
    /// Original predicate name (e.g., "foo")
    pub original_name: String,
    /// Chain pieces in execution order (innermost continuation first: [foo_2, foo_1, foo])
    pub chain_pieces: Vec<SplitChainPiece>,
    /// Total number of "real" user statements (excludes chain calls)
    pub real_statement_count: usize,
    /// Maps original statement index → reordered index
    /// e.g., if original stmt 0 became reordered stmt 3, then `reorder_map[0] = 3`
    pub reorder_map: Vec<usize>,
}

/// Result of splitting a predicate
#[derive(Debug, Clone)]
pub struct SplitResult {
    /// The predicates (continuations first, original last if split)
    pub predicates: Vec<CustomPredicateDef>,
    /// Split chain info, if splitting occurred (None for non-split)
    pub chain_info: Option<SplitChainInfo>,
}

/// Early validation: Check if predicate is fundamentally splittable
pub fn validate_predicate_is_splittable(pred: &CustomPredicateDef) -> Result<(), SplittingError> {
    let public_args = pred.args.public_args.len();

    // Check: public args must fit in operation arg limit
    if public_args > Params::max_statement_args() {
        return Err(SplittingError::TooManyPublicArgs {
            predicate: pred.name.name.clone(),
            count: public_args,
            max_allowed: Params::max_statement_args(),
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
) -> Result<SplitResult, SplittingError> {
    // Early validation
    validate_predicate_is_splittable(&pred)?;

    // If within limits, no splitting needed
    if pred.statements.len() <= Params::max_custom_predicate_arity() {
        return Ok(SplitResult {
            predicates: vec![pred],
            chain_info: None,
        });
    }

    // Need to split - execute the splitting algorithm
    let (predicates, chain_info) = split_into_chain(pred, params)?;

    Ok(SplitResult {
        predicates,
        chain_info: Some(chain_info),
    })
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
/// Result of ordering statements optimally for splitting
struct OrderingResult {
    /// Reordered statements
    statements: Vec<StatementTmpl>,
    /// Maps original statement index → reordered index
    /// reorder_map[original_idx] = new_idx
    reorder_map: Vec<usize>,
}

fn order_constraints_optimally(
    statements: Vec<StatementTmpl>,
    public_args: &HashSet<String>,
) -> OrderingResult {
    let n = statements.len();

    // If no splitting needed, preserve original order (identity mapping)
    if n <= Params::max_custom_predicate_arity() {
        return OrderingResult {
            statements,
            reorder_map: (0..n).collect(),
        };
    }

    let mut ordered = Vec::new();
    let mut reorder_map = vec![0; n];
    let mut remaining: HashSet<usize> = (0..n).collect();
    let mut active_wildcards: HashSet<String> = HashSet::new();

    while !remaining.is_empty() {
        let best_idx = find_best_next_statement(
            &statements,
            &remaining,
            &active_wildcards,
            ordered.len(),
            public_args,
        );

        remaining.remove(&best_idx);
        let stmt = &statements[best_idx];

        // Record the mapping: original index best_idx → new index ordered.len()
        reorder_map[best_idx] = ordered.len();
        ordered.push(stmt.clone());

        // Only track private wildcards in the active set — public args are always
        // available at every boundary so their liveness is irrelevant to split cost.
        let stmt_wildcards = collect_wildcards_from_statement(stmt);
        active_wildcards.extend(
            stmt_wildcards
                .into_iter()
                .filter(|w| !public_args.contains(w)),
        );

        // Remove private wildcards no longer needed by remaining statements
        let needed_later: HashSet<_> = remaining
            .iter()
            .flat_map(|&i| collect_wildcards_from_statement(&statements[i]))
            .filter(|w| !public_args.contains(w))
            .collect();
        active_wildcards.retain(|w| needed_later.contains(w));
    }

    OrderingResult {
        statements: ordered,
        reorder_map,
    }
}

/// Compute tie-breaker metrics for deterministic ordering when scores are equal
/// Returns (simplicity, public_closure, negative_fanout) tuple for use in max_by_key
fn compute_tie_breakers(
    stmt: &StatementTmpl,
    active_wildcards: &HashSet<String>,
    statements: &[StatementTmpl],
    remaining: &HashSet<usize>,
    needed_later: &HashSet<String>,
    public_args: &HashSet<String>,
) -> (usize, usize, i32) {
    let all_wildcards = collect_wildcards_from_statement(stmt);
    // Only consider private wildcards for tie-breaking metrics
    let stmt_wildcards: HashSet<_> = all_wildcards
        .into_iter()
        .filter(|w| !public_args.contains(w))
        .collect();

    // Metric 1: Simplicity - prefer statements with fewer private wildcards
    let simplicity = usize::MAX - stmt_wildcards.len();

    // Metric 2: Closure - prefer statements that close active private wildcards
    // (wildcards that won't be needed by any remaining statements)
    let closes_count = stmt_wildcards
        .intersection(active_wildcards)
        .filter(|w| !needed_later.contains(*w))
        .count();

    // Metric 3: Fanout - prefer statements with lower future usage
    // (number of remaining statements sharing private wildcards with this statement)
    let fanout = remaining
        .iter()
        .filter(|&&i| {
            let other_wildcards: HashSet<_> = collect_wildcards_from_statement(&statements[i])
                .into_iter()
                .filter(|w| !public_args.contains(w))
                .collect();
            !stmt_wildcards.is_disjoint(&other_wildcards)
        })
        .count();

    (simplicity, closes_count, -(fanout as i32))
}

fn statement_selection_key(
    idx: usize,
    statements: &[StatementTmpl],
    active_wildcards: &HashSet<String>,
    remaining: &HashSet<usize>,
    approaching_split: bool,
    public_args: &HashSet<String>,
) -> (i32, (usize, usize, i32), Reverse<usize>) {
    // Pre-compute needed_later once and share between primary score and tie-breakers.
    // These are all private wildcards referenced by any remaining statement (including
    // the current candidate, since `remaining` contains it at this point).
    let needed_later: HashSet<String> = remaining
        .iter()
        .flat_map(|&i| collect_wildcards_from_statement(&statements[i]))
        .filter(|w| !public_args.contains(w))
        .collect();

    let primary_score = score_statement(
        &statements[idx],
        active_wildcards,
        approaching_split,
        public_args,
        &needed_later,
    );
    let tie_breakers = compute_tie_breakers(
        &statements[idx],
        active_wildcards,
        statements,
        remaining,
        &needed_later,
        public_args,
    );

    // Final deterministic tie-breaker: prefer smaller original indices.
    // This avoids hash-iteration-dependent selection when scores are equal.
    (primary_score, tie_breakers, Reverse(idx))
}

/// Find the best next statement to add based on scoring heuristic
fn find_best_next_statement(
    statements: &[StatementTmpl],
    remaining: &HashSet<usize>,
    active_wildcards: &HashSet<String>,
    ordered_count: usize,
    public_args: &HashSet<String>,
) -> usize {
    // Calculate distance to next split point
    let bucket_size = Params::max_custom_predicate_arity() - 1; // Reserve slot for chain call
    let distance_to_split = bucket_size - (ordered_count % bucket_size);
    let approaching_split = distance_to_split <= 2;

    remaining
        .iter()
        .max_by_key(|&&idx| {
            statement_selection_key(
                idx,
                statements,
                active_wildcards,
                remaining,
                approaching_split,
                public_args,
            )
        })
        .copied()
        .unwrap()
}

/// Score a statement based on how well it minimizes private-wildcard liveness at boundaries.
/// `needed_later` is the set of private wildcards used by any remaining statement.
fn score_statement(
    stmt: &StatementTmpl,
    active_wildcards: &HashSet<String>,
    approaching_split: bool,
    public_args: &HashSet<String>,
    needed_later: &HashSet<String>,
) -> i32 {
    let all_wildcards = collect_wildcards_from_statement(stmt);

    // Only score based on private wildcards. Public args are always available at every
    // split boundary — they never consume a promotion slot, so their liveness is free.
    let stmt_wildcards: HashSet<_> = all_wildcards
        .into_iter()
        .filter(|w| !public_args.contains(w))
        .collect();

    // Statements that touch only public args ("cheap" statements) waste a bucket slot
    // that could be used to cluster private wildcards. Strongly defer them while any
    // private-wildcard statements remain, so they fill leftover space at the end.
    // `needed_later` is non-empty iff some remaining statement has a private wildcard.
    if stmt_wildcards.is_empty() {
        return if needed_later.is_empty() {
            0
        } else {
            i32::MIN / 2
        };
    }

    // How many active private wildcards does this reuse?
    let reuse_count = stmt_wildcards.intersection(active_wildcards).count();

    // How many new private wildcards does this introduce?
    let new_wildcard_count = stmt_wildcards.difference(active_wildcards).count();

    // Which of the projected-active wildcards are still needed after this statement?
    let mut projected_active = active_wildcards.clone();
    projected_active.extend(stmt_wildcards);
    projected_active.retain(|w| needed_later.contains(w));
    let still_active_count = projected_active.len();

    // Base score:
    //   +3 per reused wildcard  — rewards clustering (wildcard already open, no new cost)
    //   -4 per new wildcard     — penalises opening new live ranges
    //   -2 per still-live       — penalises carrying many wildcards toward the boundary
    let base_score = (reuse_count * 3) as i32
        - (new_wildcard_count * 4) as i32
        - (still_active_count * 2) as i32;

    // When close to a split boundary, strongly reward statements that close wildcards
    // (active.len() + new - still_active = number of wildcards resolved by this statement).
    // Weight 10 >> max base-score magnitude to make closing the dominant factor.
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
) -> Option<crate::lang::error::RefactorSuggestion> {
    use crate::lang::error::RefactorSuggestion;

    if crossing_wildcards.is_empty() {
        return None;
    }

    // Normalize wildcard order so diagnostics are deterministic.
    let mut sorted_crossing_wildcards = crossing_wildcards.to_vec();
    sorted_crossing_wildcards.sort();

    // Analyze the span of each crossing wildcard
    let mut wildcard_spans: Vec<(String, usize, usize, usize)> = Vec::new();

    for wildcard in &sorted_crossing_wildcards {
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
    if sorted_crossing_wildcards.len() > 1 {
        return Some(RefactorSuggestion::GroupWildcardUsages {
            wildcards: sorted_crossing_wildcards,
        });
    }

    None
}

/// Split into chain using bucket-filling approach
/// Returns the split predicates and metadata about the split
fn split_into_chain(
    pred: CustomPredicateDef,
    params: &Params,
) -> Result<(Vec<CustomPredicateDef>, SplitChainInfo), SplittingError> {
    let original_name = pred.name.name.clone();
    let conjunction = pred.conjunction_type;

    let original_public_args: Vec<String> = pred
        .args
        .public_args
        .iter()
        .map(|id| id.name.clone())
        .collect();

    let public_args_set: HashSet<String> = original_public_args.iter().cloned().collect();

    let real_statement_count = pred.statements.len();

    let ordering_result = order_constraints_optimally(pred.statements, &public_args_set);
    let ordered_statements = ordering_result.statements;
    let reorder_map = ordering_result.reorder_map;

    let mut chain_links = Vec::new();
    let mut pos = 0;
    let mut incoming_public = original_public_args.clone();

    while pos < ordered_statements.len() {
        let remaining = ordered_statements.len() - pos;
        let is_last = remaining <= Params::max_custom_predicate_arity();

        let bucket_size = if is_last {
            remaining // Last predicate uses all remaining
        } else {
            Params::max_custom_predicate_arity() - 1 // Reserve slot for chain call
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
        let mut new_promotions: Vec<_> = live_at_boundary
            .iter()
            .filter(|w| !incoming_set.contains(*w))
            .cloned()
            .collect();
        new_promotions.sort();
        let total_public = incoming_public.len() + new_promotions.len();
        if total_public > Params::max_statement_args() {
            let context = crate::lang::error::SplitContext {
                split_index: chain_links.len(),
                statement_range: (pos, end),
                incoming_public: incoming_public.clone(),
                crossing_wildcards: new_promotions.clone(),
                total_public,
            };

            let suggestion = generate_refactor_suggestion(&new_promotions, &ordered_statements);

            return Err(SplittingError::TooManyPublicArgsAtSplit {
                predicate: original_name.clone(),
                context: Box::new(context),
                max_allowed: Params::max_statement_args(),
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

        chain_links.push(ChainLink {
            statements: ordered_statements[pos..end].to_vec(),
            public_args_in: incoming_public.clone(),
            private_args,
            // new_promotions are already sorted and already filtered to exclude incoming_public
            promoted_wildcards: new_promotions.clone(),
        });

        pos = end;

        // Extend incoming_public for the next link with the newly promoted wildcards.
        // new_promotions is already filtered to exclude incoming_set, so no dedup needed.
        incoming_public.extend(new_promotions);
    }

    // Backward pass: prune each continuation's public args to the minimal set needed.
    //
    // The forward pass accumulates incoming_public monotonically, so a continuation may
    // inherit original public args that none of its statements (or downstream continuations)
    // ever reference.  A continuation must declare every public arg it receives, and the
    // proof system constrains each declared arg - an arg that goes unused has no constraints
    // and will not match the value the caller passes.
    //
    // Propagating from the last link backward ensures each continuation declares exactly the
    // args it uses directly, plus any args its successor still needs. Link 0 (the original
    // predicate) is left untouched - its public-arg signature is user-declared.
    {
        let num_links = chain_links.len();
        if num_links > 1 {
            // Collect wildcards referenced by each link's statements once.
            let link_wildcards: Vec<HashSet<String>> = chain_links
                .iter()
                .map(|link| {
                    link.statements
                        .iter()
                        .flat_map(collect_wildcards_from_statement)
                        .collect()
                })
                .collect();

            let last = num_links - 1;

            // Seed: last link retains only args it directly references.
            chain_links[last]
                .public_args_in
                .retain(|a| link_wildcards[last].contains(a));

            // Propagate backward through intermediate continuation links (skip link 0).
            for i in (1..last).rev() {
                let needed_downstream: HashSet<String> =
                    chain_links[i + 1].public_args_in.iter().cloned().collect();
                chain_links[i]
                    .public_args_in
                    .retain(|a| link_wildcards[i].contains(a) || needed_downstream.contains(a));
            }
        }
    }

    // Build SplitChainInfo from chain_links before generating predicates
    // Pieces are in execution order: innermost continuation first, original last
    let num_links = chain_links.len();
    let mut chain_pieces = Vec::new();
    for i in (0..num_links).rev() {
        let link = &chain_links[i];
        let is_last = i == num_links - 1;
        let name = if i == 0 {
            original_name.clone()
        } else {
            format!("{}_{}", original_name, i)
        };
        chain_pieces.push(SplitChainPiece {
            name,
            real_statement_count: link.statements.len(),
            has_chain_call: !is_last,
        });
    }

    let chain_info = SplitChainInfo {
        original_name: original_name.clone(),
        chain_pieces,
        real_statement_count,
        reorder_map,
    };

    let mut chain_predicates =
        generate_chain_predicates(&original_name, chain_links, conjunction, params)?;

    validate_chain(&chain_predicates, params);

    // Reverse so continuations come before callers in declaration order.
    // This ensures that when batched, continuations are in earlier batches
    // and can be referenced by their callers.
    chain_predicates.reverse();

    Ok((chain_predicates, chain_info))
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

            // Create arguments for chain call: use next link's public_args_in
            // which is current public_args_in extended with current promoted_wildcards
            let next_link = &chain_links[i + 1];
            let chain_call_args: Vec<StatementTmplArg> = next_link
                .public_args_in
                .iter()
                .map(|arg_name| {
                    StatementTmplArg::Wildcard(Identifier {
                        name: arg_name.clone(),
                        span: None,
                    })
                })
                .collect();

            let chain_call = StatementTmpl {
                predicate: PredicateRef::Local(next_pred_name),
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

        // Build private args: segment-local private wildcards, plus any wildcards being
        // promoted to public for the next link (they must be declared here so the solver
        // can bind them before passing them as public args to the continuation).
        let mut private_arg_names = link.private_args.clone();
        if !is_last {
            private_arg_names.extend(link.promoted_wildcards.iter().cloned());
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

/// Sanity-check the generated chain. All three constraints are enforced as proper errors
/// earlier in `split_into_chain`, so violations here indicate a bug in the algorithm.
fn validate_chain(chain: &[CustomPredicateDef], params: &Params) {
    for pred in chain {
        assert!(
            pred.statements.len() <= Params::max_custom_predicate_arity(),
            "chain link '{}' has {} statements, exceeds max {}",
            pred.name.name,
            pred.statements.len(),
            Params::max_custom_predicate_arity(),
        );
        assert!(
            pred.args.public_args.len() <= Params::max_statement_args(),
            "chain link '{}' has {} public args, exceeds max {}",
            pred.name.name,
            pred.args.public_args.len(),
            Params::max_statement_args(),
        );
        let total =
            pred.args.public_args.len() + pred.args.private_args.as_ref().map_or(0, |v| v.len());
        assert!(
            total <= params.max_custom_predicate_wildcards,
            "chain link '{}' has {} total args, exceeds max {}",
            pred.name.name,
            total,
            params.max_custom_predicate_wildcards,
        );
    }
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

        assert!(validate_predicate_is_splittable(&pred).is_ok());
    }

    #[test]
    fn test_validate_too_many_public_args() {
        let input = r#"
            my_pred(A, B, C, D, E, F) = AND (
                Equal(A, B)
            )
        "#;

        let pred = parse_predicate(input);

        let result = validate_predicate_is_splittable(&pred);
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

        let split_result = result.unwrap();
        assert_eq!(split_result.predicates.len(), 1); // No split needed
        assert!(split_result.chain_info.is_none()); // No chain info for non-split
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

        let split_result = result.unwrap();
        let chain = &split_result.predicates;
        assert_eq!(chain.len(), 2); // Should split into 2 predicates

        // Chain is reversed: continuation comes first, original comes last
        // Last predicate (index 1): original name, 4 statements + chain call = 5
        assert_eq!(chain[1].statements.len(), 5);
        assert_eq!(chain[1].name.name, "my_pred");

        // First predicate (index 0): continuation, 2 remaining statements
        assert_eq!(chain[0].statements.len(), 2);
        assert_eq!(chain[0].name.name, "my_pred_1");

        // Verify chain_info is present
        let chain_info = split_result.chain_info.as_ref().unwrap();
        assert_eq!(chain_info.original_name, "my_pred");
        assert_eq!(chain_info.real_statement_count, 6);
        assert_eq!(chain_info.chain_pieces.len(), 2);
        // Pieces are in execution order: innermost first
        assert_eq!(chain_info.chain_pieces[0].name, "my_pred_1");
        assert!(!chain_info.chain_pieces[0].has_chain_call);
        assert_eq!(chain_info.chain_pieces[1].name, "my_pred");
        assert!(chain_info.chain_pieces[1].has_chain_call);
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

        let split_result = result.unwrap();
        let chain = &split_result.predicates;
        assert_eq!(chain.len(), 2); // Should split into 2 predicates

        // Chain is reversed: continuation first, original last
        // Original predicate should have chain call as last statement
        let original = &chain[1];
        assert_eq!(original.name.name, "complex");
        let last_stmt = original.statements.last().unwrap();
        assert_eq!(last_stmt.predicate.predicate_name(), "complex_1");
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

        let split_result = result.unwrap();
        let chain = &split_result.predicates;
        assert_eq!(chain.len(), 3); // Should split into 3 predicates

        // Chain is reversed: [_2, _1, original]
        // chain[0]: large_pred_2 (3 remaining statements)
        assert_eq!(chain[0].statements.len(), 3);
        assert_eq!(chain[0].name.name, "large_pred_2");
        // chain[1]: large_pred_1 (4 + chain call = 5)
        assert_eq!(chain[1].statements.len(), 5);
        assert_eq!(chain[1].name.name, "large_pred_1");
        // chain[2]: large_pred (4 + chain call = 5)
        assert_eq!(chain[2].statements.len(), 5);
        assert_eq!(chain[2].name.name, "large_pred");

        // Verify chain_info
        let chain_info = split_result.chain_info.as_ref().unwrap();
        assert_eq!(chain_info.real_statement_count, 11);
        assert_eq!(chain_info.chain_pieces.len(), 3);
        // Execution order: innermost first
        assert_eq!(chain_info.chain_pieces[0].name, "large_pred_2");
        assert_eq!(chain_info.chain_pieces[1].name, "large_pred_1");
        assert_eq!(chain_info.chain_pieces[2].name, "large_pred");
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

        let split_result = result.unwrap();
        let chain = &split_result.predicates;
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
    fn test_statement_selection_prefers_lower_index_on_tie() {
        // Two structurally symmetric statements produce identical heuristic scores.
        // Determinism comes from the final index-based tie breaker.
        let input = r#"
            tie_break(A, B) = AND (
                Equal(A["x"], B["x"])
                Equal(A["y"], B["y"])
            )
        "#;

        let pred = parse_predicate(input);
        let statements = pred.statements;
        let remaining: HashSet<usize> = [0, 1].into_iter().collect();
        let active_wildcards = HashSet::new();

        // A and B are the public args of tie_break(A, B)
        let public_args: HashSet<String> = ["A".to_string(), "B".to_string()].into_iter().collect();
        let key0 = statement_selection_key(
            0,
            &statements,
            &active_wildcards,
            &remaining,
            false,
            &public_args,
        );
        let key1 = statement_selection_key(
            1,
            &statements,
            &active_wildcards,
            &remaining,
            false,
            &public_args,
        );

        assert_eq!(key0.0, key1.0, "Primary heuristic score should tie");
        assert_eq!(key0.1, key1.1, "Secondary tie-breaker metrics should tie");
        assert!(
            key0 > key1,
            "Lower original index should win deterministic final tie-breaker"
        );

        let selected =
            find_best_next_statement(&statements, &remaining, &active_wildcards, 0, &public_args);
        assert_eq!(selected, 0);
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

        let split_result = result.unwrap();
        let chain = &split_result.predicates;
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

    // --- Regression tests for known bugs ---

    /// Bug: the greedy ordering algorithm scores statements using public args the same as
    /// private wildcards. Statements that only touch public args look "cheap" and get pulled
    /// into the first bucket early, wasting slots and forcing private wildcards to cross the
    /// split boundary unnecessarily.
    ///
    /// With 4 public args and two "cheap" statements (public-args-only) picked early,
    /// the greedy produces 4 incoming public + 2 crossing private = 6 > max(5), causing
    /// an error even though a valid ordering exists with only 1 crossing wildcard.
    ///
    /// Mirrors the real-world UnlockObject predicate failure.
    #[test]
    fn test_split_succeeds_with_four_public_args_and_public_only_statements() {
        // 4 public args, 7 statements.
        // W1 is used in stmts 0, 1, 4. W2 is used in stmts 1, 2, 3.
        // Stmts 5 and 6 only reference public args ("cheap" statements).
        //
        // Optimal split: bucket0={0,1,2,3}, bucket1={4,5,6}
        //   → only W1 crosses (used in 0,1 and 4), total = 4 public + 1 crossing = 5 ✓
        //
        // Greedy (buggy) picks stmts 5,6 early into bucket0, scattering W1 and W2
        // across the boundary → 4 + 2 = 6 > 5 ✗
        let input = r#"
            pred(A, B, C, D, private: W1, W2) = AND(
                Equal(W1["x"], A["v"])
                Equal(W2["y"], W1["x"])
                Equal(W2["z"], B["v"])
                Equal(C["r"], W2["y"])
                Equal(D["s"], W1["x"])
                Equal(A["out"], C["out"])
                Equal(B["out"], D["out"])
            )
        "#;

        let pred = parse_predicate(input);
        let params = Params::default();

        let result = split_predicate_if_needed(pred, &params);
        assert!(
            result.is_ok(),
            "Should find a valid split with ≤1 crossing wildcard, got: {:?}",
            result.err()
        );
    }

    /// Bug: when splitting a predicate, continuation predicates include ALL original public
    /// args in their public_args_in, even those not used in any of their statements.
    ///
    /// An unused public arg in a continuation causes the proof builder to treat it as
    /// unconstrained (defaulting to 0), while the parent predicate passes the real value,
    /// causing a mismatch and proof failure.
    #[test]
    fn test_continuation_excludes_public_args_unused_after_split() {
        // Public arg A is only used in stmt0 (first segment).
        // Public arg B is only used in stmts 4-5 (second segment).
        // The continuation predicate (_1) should include B but not A.
        let input = r#"
            pred(A, B, private: T) = AND(
                Equal(T["x"], A["val"])
                Equal(T["y"], 1)
                Equal(T["z"], 2)
                Equal(T["w"], 3)
                Equal(B["r"], T["x"])
                Equal(B["s"], T["y"])
            )
        "#;

        let pred = parse_predicate(input);
        let params = Params::default();

        let result = split_predicate_if_needed(pred, &params).unwrap();
        // chain[0] is the continuation (_1 suffix), chain[1] is the original
        let continuation = result
            .predicates
            .iter()
            .find(|p| p.name.name == "pred_1")
            .expect("Expected a pred_1 continuation predicate");

        let cont_public: Vec<&str> = continuation
            .args
            .public_args
            .iter()
            .map(|id| id.name.as_str())
            .collect();

        assert!(
            !cont_public.contains(&"A"),
            "Continuation should drop unused public arg 'A', got: {:?}",
            cont_public
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
