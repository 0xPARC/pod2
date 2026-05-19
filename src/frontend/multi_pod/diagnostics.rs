//! Diagnostic views and structured-failure analysis.
//!
//! - [`ResourceSummary`]: pre-solve aggregate resource demand vs. per-POD
//!   limits, with the dominant bottleneck flagged.
//! - [`SolutionBreakdown`]: post-solve per-POD utilisation.
//! - [`CapViolation`] / [`diagnose_failure`]: when [`partition`] returns
//!   `None`, a greedy walk over the topo ordering surfaces the first cap
//!   that overflows, with the segment range and overflowing dimension.
//!
//! [`partition`]: super::partition::partition

use std::{
    collections::{BTreeSet, HashSet},
    fmt,
};

use super::{
    cost::{ResourceTotals, StatementCost},
    shape::{AbstractDep, InputShape, OutputShape},
};
use crate::middleware::Params;

/// Usage of a single resource category against its per-POD cap. Reused for
/// pre-solve aggregate demand and post-solve per-POD breakdowns.
#[derive(Clone, Debug)]
pub struct UtilizationRow {
    pub name: &'static str,
    pub used: usize,
    pub limit: usize,
}

impl UtilizationRow {
    pub fn utilization(&self) -> f64 {
        if self.limit == 0 {
            if self.used == 0 {
                0.0
            } else {
                f64::INFINITY
            }
        } else {
            self.used as f64 / self.limit as f64
        }
    }

    /// Minimum PODs needed for this resource alone: `ceil(used / limit)`.
    /// `None` if `limit == 0` and `used > 0` (infeasible).
    pub fn min_pods(&self) -> Option<usize> {
        lower_bound(self.used, self.limit)
    }
}

fn lower_bound(used: usize, limit: usize) -> Option<usize> {
    if used == 0 {
        Some(0)
    } else if limit == 0 {
        None
    } else {
        Some(used.div_ceil(limit))
    }
}

/// Aggregate resource costs into category rows. Single source of truth for
/// the category names and their corresponding `Params` limits.
///
/// Merkle dimensions report small and medium counts separately, each
/// against its own pool cap. Small-eligible ops can substitute up into
/// medium slots when small is exhausted; that substitution is enforced by
/// [`ResourceTotals::fits_in_pod`] / [`ResourceTotals::min_pods`] rather
/// than visible here, since folding it into the display ("total" rows)
/// confused readers comparing per-pool usage.
fn aggregate_rows<'a>(
    costs: impl IntoIterator<Item = &'a StatementCost>,
    params: &Params,
) -> (Vec<UtilizationRow>, usize) {
    let totals = ResourceTotals::accumulate(costs);
    let state = &params.containers.state;
    let transition = &params.containers.transition;
    let rows = vec![
        UtilizationRow {
            name: "total statements",
            used: totals.num_statements,
            limit: params.max_statements,
        },
        UtilizationRow {
            name: "merkle proofs (small)",
            used: totals.merkle_proofs_small,
            limit: state.max_small,
        },
        UtilizationRow {
            name: "merkle proofs (medium)",
            used: totals.merkle_proofs_medium,
            limit: state.max_medium,
        },
        UtilizationRow {
            name: "merkle state transitions (small)",
            used: totals.merkle_state_transitions_small,
            limit: transition.max_small,
        },
        UtilizationRow {
            name: "merkle state transitions (medium)",
            used: totals.merkle_state_transitions_medium,
            limit: transition.max_medium,
        },
        UtilizationRow {
            name: "custom pred verifications",
            used: totals.custom_pred_verifications,
            limit: params.max_custom_predicate_verifications,
        },
        UtilizationRow {
            name: "signed_by",
            used: totals.signed_by,
            limit: params.max_signed_by,
        },
        UtilizationRow {
            name: "public_key_of",
            used: totals.public_key_of,
            limit: params.max_public_key_of,
        },
        UtilizationRow {
            name: "distinct custom predicates",
            used: totals.distinct_custom_predicates,
            limit: params.max_custom_predicates,
        },
    ];
    (rows, totals.num_statements)
}

/// Pre-solve aggregate resource summary.
#[derive(Clone, Debug)]
pub struct ResourceSummary {
    pub rows: Vec<UtilizationRow>,
    pub num_statements: usize,
}

impl ResourceSummary {
    pub fn from_input(input: &InputShape) -> Self {
        Self::from_costs(input.costs.iter(), &input.params)
    }

    /// Build a summary from a stream of `StatementCost`s plus a `Params`,
    /// without going through an `InputShape`. Lets callers report on
    /// builder-stage costs before deps have been materialised.
    pub fn from_costs<'a>(
        costs: impl IntoIterator<Item = &'a StatementCost>,
        params: &Params,
    ) -> Self {
        let (rows, num_statements) = aggregate_rows(costs, params);
        Self {
            rows,
            num_statements,
        }
    }

    /// The resource category requiring the most PODs (the bottleneck).
    pub fn bottleneck(&self) -> Option<&UtilizationRow> {
        self.rows
            .iter()
            .filter(|r| r.used > 0)
            .max_by_key(|r| r.min_pods().unwrap_or(usize::MAX))
    }
}

impl fmt::Display for ResourceSummary {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Resource Summary ({} statements)", self.num_statements)?;
        writeln!(
            f,
            "  {:<30} {:>5}   {:>9}   {:>8}",
            "Category", "Total", "Limit/POD", "Min PODs"
        )?;

        let bottleneck_name = self.bottleneck().map(|r| r.name);

        for row in &self.rows {
            let min_pods_str = match row.min_pods() {
                Some(n) => format!("{}", n),
                None => "inf".to_string(),
            };
            let marker = if Some(row.name) == bottleneck_name && row.used > 0 {
                "  <<<"
            } else {
                ""
            };
            writeln!(
                f,
                "  {:<30} {:>5}   {:>9}   {:>8}{}",
                row.name, row.used, row.limit, min_pods_str, marker
            )?;
        }

        Ok(())
    }
}

/// Per-POD resource utilisation in a solved partition. Extends the
/// aggregate rows with tree-specific dimensions.
#[derive(Clone, Debug)]
pub struct PodUtilization {
    pub pod_idx: usize,
    pub is_output: bool,
    pub num_statements: usize,
    pub resources: Vec<UtilizationRow>,
    pub imports: UtilizationRow,
    pub external_pods: UtilizationRow,
}

/// Post-solve per-POD breakdown.
#[derive(Clone, Debug)]
pub struct SolutionBreakdown {
    pub pods: Vec<PodUtilization>,
    pub num_statements: usize,
    pub pod_count: usize,
}

impl SolutionBreakdown {
    /// Build a breakdown from an [`InputShape`] and its [`OutputShape`].
    /// Re-derives per-POD imports and external-pod references from the
    /// dep graph and the partition; both are pure functions of the inputs.
    pub fn from_solution(input: &InputShape, output: &OutputShape) -> Self {
        let n = input.num_statements();
        let pod_count = output.pod_count;

        // For each statement, the POD it lives in.
        let mut pod_of: Vec<usize> = vec![usize::MAX; n];
        for (p, stmts) in output.pod_statements.iter().enumerate() {
            for &s in stmts {
                pod_of[s] = p;
            }
        }

        let output_pub_set: BTreeSet<usize> = input.output_public_indices.iter().copied().collect();

        let pods = (0..pod_count)
            .map(|pod_idx| {
                let stmts = &output.pod_statements[pod_idx];
                let is_output = pod_idx + 1 == pod_count;
                let (resources, num_stmts) =
                    aggregate_rows(stmts.iter().map(|&s| &input.costs[s]), &input.params);

                let mut chain_imports: HashSet<usize> = HashSet::new();
                let mut external_imports: HashSet<usize> = HashSet::new();
                let mut external_pods: HashSet<usize> = HashSet::new();
                for &s in stmts {
                    for dep in &input.dep_edges[s] {
                        match dep {
                            AbstractDep::Internal(d) => {
                                if pod_of[*d] != pod_idx {
                                    chain_imports.insert(*d);
                                }
                            }
                            AbstractDep::External { pod, statement } => {
                                external_imports.insert(*statement);
                                external_pods.insert(*pod);
                            }
                        }
                    }
                }
                if is_output {
                    for &op in &output_pub_set {
                        if pod_of[op] != pod_idx {
                            chain_imports.insert(op);
                        }
                    }
                }

                let imports_row = UtilizationRow {
                    name: "tree imports",
                    used: chain_imports.len() + external_imports.len(),
                    limit: input.params.max_open_input_statements,
                };
                let external_row = UtilizationRow {
                    name: "external pods",
                    used: external_pods.len(),
                    limit: input.params.max_input_pods,
                };

                PodUtilization {
                    pod_idx,
                    is_output,
                    num_statements: num_stmts,
                    resources,
                    imports: imports_row,
                    external_pods: external_row,
                }
            })
            .collect();

        Self {
            pods,
            num_statements: n,
            pod_count,
        }
    }
}

impl fmt::Display for SolutionBreakdown {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(
            f,
            "Solution Breakdown ({} statements -> {} PODs)",
            self.num_statements, self.pod_count
        )?;

        for pod in &self.pods {
            let role = if pod.is_output {
                "output"
            } else {
                "intermediate"
            };
            writeln!(f, "  POD {} ({}):", pod.pod_idx, role)?;

            for row in pod
                .resources
                .iter()
                .chain([&pod.imports, &pod.external_pods])
            {
                if row.used > 0 {
                    let pct = if row.limit > 0 {
                        format!("({:>3}%)", (row.used * 100) / row.limit)
                    } else {
                        String::new()
                    };
                    writeln!(
                        f,
                        "    {:<30} {:>3}/{:<3} {}",
                        row.name, row.used, row.limit, pct
                    )?;
                }
            }
            writeln!(f)?;
        }

        Ok(())
    }
}

/// First cap violation found by a greedy walk over the topo ordering. Used
/// to produce a structured failure when the DP can't find a partition.
#[derive(Clone, Debug)]
pub enum CapViolation {
    /// Adding statement `stmt` to the current segment would exceed a
    /// resource cap. `segment_range` is the statements already accumulated
    /// when the violation surfaced.
    Resource {
        segment_index: usize,
        segment_range: (usize, usize),
        offending_stmt: usize,
        category: &'static str,
        used: usize,
        max_allowed: usize,
    },
    /// A single statement consumes more distinct tree imports (chain
    /// producers plus external statements) than fit, even in a segment by
    /// itself. No partition fixes this; the statement must be refactored.
    Unsplittable {
        stmt: usize,
        distinct_imports: usize,
        max_allowed: usize,
    },
    /// A single statement is infeasible on its own, but
    /// `identify_overflow`'s recognized cap categories don't explain
    /// why. Surfaced so the diagnostic walk terminates instead of
    /// looping forever. Extend [`identify_overflow`] to cover the
    /// missing cap when this fires.
    UnrecognizedOverflow { stmt: usize, segment_index: usize },
}

impl fmt::Display for CapViolation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CapViolation::Resource {
                segment_index,
                segment_range,
                offending_stmt,
                category,
                used,
                max_allowed,
            } => write!(
                f,
                "segment {} (statements {:?}) overflows {}: {} > {} when adding statement {}",
                segment_index, segment_range, category, used, max_allowed, offending_stmt
            ),
            CapViolation::Unsplittable {
                stmt,
                distinct_imports,
                max_allowed,
            } => write!(
                f,
                "statement {} alone requires {} distinct tree imports \
                 (chain producers plus external statements), exceeding the \
                 cap of {}",
                stmt, distinct_imports, max_allowed
            ),
            CapViolation::UnrecognizedOverflow {
                stmt,
                segment_index,
            } => write!(
                f,
                "statement {} is infeasible on its own at segment {}, but no \
                 recognised cap category explains the overflow (extend \
                 identify_overflow to surface the responsible cap)",
                stmt, segment_index
            ),
        }
    }
}

/// Greedy-walk diagnostic: run the same source-order Kahn ordering the DP
/// uses, then accumulate statements into segments, opening a new segment
/// when a cap would overflow. Surfaces the first segment where no further
/// statement fits and identifies the responsible cap. Also flags
/// statements that are individually unsplittable.
pub fn diagnose_failure(input: &InputShape) -> Option<CapViolation> {
    let n = input.num_statements();
    let identity_priority: Vec<usize> = (0..n).collect();
    let ordering = super::partition::kahn_with_priority(input, &identity_priority)?;

    for &s in &ordering {
        if let Some(v) = check_unsplittable(input, s) {
            return Some(v);
        }
    }

    // Walk segments greedily. Open a new segment when the next statement
    // doesn't fit; if it doesn't fit on its own (Unsplittable above didn't
    // trigger but the segment-relative caps overflow), surface the
    // violation that broke the camel's back.
    let mut segment_start = 0_usize;
    let mut segment_index = 0_usize;
    let mut pos = 0_usize;
    while pos < n {
        let next_pos = pos + 1;
        if super::partition::segment_feasible(&ordering, input, segment_start, next_pos) {
            pos = next_pos;
            continue;
        }
        if segment_start == pos {
            if let Some(v) =
                identify_overflow(input, &ordering, segment_start, next_pos, segment_index)
            {
                return Some(v);
            }
            // identify_overflow doesn't recognise this cap. Surfacing
            // UnrecognizedOverflow both terminates the walk and points
            // the next reader at the missing category. Without this
            // return, `pos` would never advance and we'd loop forever
            // (segment_start = pos is a no-op when they're equal).
            return Some(CapViolation::UnrecognizedOverflow {
                stmt: ordering[pos],
                segment_index,
            });
        }
        segment_start = pos;
        segment_index += 1;
    }
    None
}

fn check_unsplittable(input: &InputShape, s: usize) -> Option<CapViolation> {
    let mut chain: HashSet<usize> = HashSet::new();
    let mut external: HashSet<usize> = HashSet::new();
    for dep in &input.dep_edges[s] {
        match dep {
            AbstractDep::Internal(d) => {
                chain.insert(*d);
            }
            AbstractDep::External { statement, .. } => {
                external.insert(*statement);
            }
        }
    }
    let total = chain.len() + external.len();
    let max_imports = input.params.max_open_input_statements;
    if total > max_imports {
        Some(CapViolation::Unsplittable {
            stmt: s,
            distinct_imports: total,
            max_allowed: max_imports,
        })
    } else {
        None
    }
}

/// When a single-statement segment fails feasibility, identify which cap
/// overflows so the diagnostic surfaces the actionable category.
fn identify_overflow(
    input: &InputShape,
    ordering: &[usize],
    a: usize,
    p: usize,
    segment_index: usize,
) -> Option<CapViolation> {
    let params = &input.params;
    let s = ordering[a];
    let c = &input.costs[s];

    let state = &params.containers.state;
    let transition = &params.containers.transition;
    let categories: &[(&'static str, usize, usize)] = &[
        ("total statements", 1, params.max_statements),
        (
            "merkle proofs (small)",
            c.merkle_proofs_small,
            state.max_small,
        ),
        (
            "merkle proofs (medium)",
            c.merkle_proofs_medium,
            state.max_medium,
        ),
        (
            "merkle state transitions (small)",
            c.merkle_state_transitions_small,
            transition.max_small,
        ),
        (
            "merkle state transitions (medium)",
            c.merkle_state_transitions_medium,
            transition.max_medium,
        ),
        (
            "custom pred verifications",
            c.custom_pred_verifications,
            params.max_custom_predicate_verifications,
        ),
        ("signed_by", c.signed_by, params.max_signed_by),
        ("public_key_of", c.public_key_of, params.max_public_key_of),
        (
            "distinct custom predicates",
            c.custom_predicates_ids.len(),
            params.max_custom_predicates,
        ),
    ];

    for &(name, used, limit) in categories {
        if used > limit {
            return Some(CapViolation::Resource {
                segment_index,
                segment_range: (a, p),
                offending_stmt: s,
                category: name,
                used,
                max_allowed: limit,
            });
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::multi_pod::partition;

    fn independent(n: usize, output_public: Vec<usize>, params: Params) -> InputShape {
        InputShape {
            costs: (0..n).map(|_| StatementCost::default()).collect(),
            dep_edges: (0..n).map(|_| Vec::new()).collect(),
            output_public_indices: output_public,
            num_external_pods: 0,
            statement_pod: vec![],
            params,
        }
    }

    #[test]
    fn resource_summary_flags_statement_bottleneck() {
        let params = Params {
            max_statements: 2,
            ..Params::default()
        };
        // max_statements = 2; 6 statements -> bottleneck is statements.
        let input = independent(6, vec![5], params);
        let summary = ResourceSummary::from_input(&input);
        let bottleneck = summary
            .bottleneck()
            .expect("non-empty problem has a bottleneck");
        assert_eq!(bottleneck.name, "total statements");
        assert_eq!(bottleneck.min_pods(), Some(3)); // ceil(6/2)
    }

    #[test]
    fn solution_breakdown_reports_per_pod_utilisation() {
        let params = Params {
            max_statements: 2,
            ..Params::default()
        };
        let input = independent(3, vec![2], params);
        let output = partition::partition(&input).expect("must partition");
        let breakdown = SolutionBreakdown::from_solution(&input, &output);
        assert_eq!(breakdown.pod_count, output.pod_count);
        assert!(breakdown.pods.last().unwrap().is_output);
    }
}
