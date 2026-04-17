//! Diagnostic utilities for multi-POD resource analysis.
//!
//! Provides two views:
//! - [`ResourceSummary`]: Pre-solve aggregate resource demand vs. per-POD limits.
//!   Shows which resource category is the bottleneck (requires the most PODs).
//! - [`SolutionBreakdown`]: Post-solve per-POD utilization showing how full each POD is.

use std::fmt;

use super::cost::StatementCost;
use crate::middleware::Params;

/// A single resource category's demand vs. limit.
#[derive(Clone, Debug)]
pub struct ResourceRow {
    /// Human-readable name of the resource.
    pub name: &'static str,
    /// Total demand across all statements.
    pub total: usize,
    /// Per-POD limit from Params.
    pub limit: usize,
    /// Minimum PODs needed for this resource alone: ceil(total / limit).
    /// `None` if limit is 0 and total > 0 (infeasible).
    pub min_pods: Option<usize>,
}

/// Pre-solve aggregate resource summary.
///
/// Shows total resource demand across all operations and the minimum PODs
/// each resource category would require independently.
#[derive(Clone, Debug)]
pub struct ResourceSummary {
    pub rows: Vec<ResourceRow>,
    pub num_statements: usize,
}

impl ResourceSummary {
    /// Compute a resource summary from per-statement costs and params.
    pub fn from_costs(costs: &[StatementCost], params: &Params) -> Self {
        let max_priv = params.max_priv_statements();

        let mut merkle_proofs = 0usize;
        let mut merkle_state_transitions = 0usize;
        let mut custom_pred_verifications = 0usize;
        let mut signed_by = 0usize;
        let mut public_key_of = 0usize;
        let mut all_custom_predicate_ids = std::collections::BTreeSet::new();

        for c in costs {
            merkle_proofs += c.merkle_proofs;
            merkle_state_transitions += c.merkle_state_transitions;
            custom_pred_verifications += c.custom_pred_verifications;
            signed_by += c.signed_by;
            public_key_of += c.public_key_of;
            all_custom_predicate_ids.extend(c.custom_predicates_ids.iter().cloned());
        }

        let n = costs.len();
        let rows = vec![
            ResourceRow {
                name: "private statements",
                total: n,
                limit: max_priv,
                min_pods: lower_bound(n, max_priv),
            },
            ResourceRow {
                name: "merkle proofs",
                total: merkle_proofs,
                limit: params.max_merkle_proofs_containers,
                min_pods: lower_bound(merkle_proofs, params.max_merkle_proofs_containers),
            },
            ResourceRow {
                name: "merkle state transitions",
                total: merkle_state_transitions,
                limit: params.max_merkle_tree_state_transition_proofs_containers,
                min_pods: lower_bound(
                    merkle_state_transitions,
                    params.max_merkle_tree_state_transition_proofs_containers,
                ),
            },
            ResourceRow {
                name: "custom pred verifications",
                total: custom_pred_verifications,
                limit: params.max_custom_predicate_verifications,
                min_pods: lower_bound(
                    custom_pred_verifications,
                    params.max_custom_predicate_verifications,
                ),
            },
            ResourceRow {
                name: "signed_by",
                total: signed_by,
                limit: params.max_signed_by,
                min_pods: lower_bound(signed_by, params.max_signed_by),
            },
            ResourceRow {
                name: "public_key_of",
                total: public_key_of,
                limit: params.max_public_key_of,
                min_pods: lower_bound(public_key_of, params.max_public_key_of),
            },
            ResourceRow {
                name: "distinct custom predicates",
                total: all_custom_predicate_ids.len(),
                limit: params.max_custom_predicates,
                min_pods: lower_bound(all_custom_predicate_ids.len(), params.max_custom_predicates),
            },
        ];

        Self {
            rows,
            num_statements: n,
        }
    }

    /// The resource category requiring the most PODs (the bottleneck).
    /// Returns `None` only if there are no statements.
    pub fn bottleneck(&self) -> Option<&ResourceRow> {
        self.rows
            .iter()
            .filter(|r| r.total > 0)
            .max_by_key(|r| r.min_pods.unwrap_or(usize::MAX))
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
            let min_pods_str = match row.min_pods {
                Some(n) => format!("{}", n),
                None => "inf".to_string(),
            };
            let marker = if Some(row.name) == bottleneck_name && row.total > 0 {
                "  <<<"
            } else {
                ""
            };
            writeln!(
                f,
                "  {:<30} {:>5}   {:>9}   {:>8}{}",
                row.name, row.total, row.limit, min_pods_str, marker
            )?;
        }

        Ok(())
    }
}

/// Per-POD resource utilization in a solved solution.
#[derive(Clone, Debug)]
pub struct PodUtilization {
    /// POD index.
    pub pod_idx: usize,
    /// Whether this is the output POD (last).
    pub is_output: bool,
    /// Number of statements in this POD.
    pub num_statements: usize,
    /// Resource usage vs. limits for each category.
    pub resources: Vec<UtilizationRow>,
}

/// A single resource's usage in one POD.
#[derive(Clone, Debug)]
pub struct UtilizationRow {
    pub name: &'static str,
    pub used: usize,
    pub limit: usize,
}

impl UtilizationRow {
    /// Utilization as a fraction (0.0 to 1.0).
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
}

/// Post-solve per-POD resource breakdown.
#[derive(Clone, Debug)]
pub struct SolutionBreakdown {
    pub pods: Vec<PodUtilization>,
    pub num_statements: usize,
    pub pod_count: usize,
}

impl SolutionBreakdown {
    /// Compute a solution breakdown from per-statement costs, the solution's
    /// pod_statements assignment, and params.
    pub fn from_solution(
        costs: &[StatementCost],
        pod_statements: &[Vec<usize>],
        pod_count: usize,
        num_statements: usize,
        params: &Params,
    ) -> Self {
        let max_priv = params.max_priv_statements();

        let pods = (0..pod_count)
            .map(|pod_idx| {
                let stmts = &pod_statements[pod_idx];

                let mut merkle_proofs = 0usize;
                let mut merkle_state_transitions = 0usize;
                let mut custom_pred_verifications = 0usize;
                let mut signed_by = 0usize;
                let mut public_key_of = 0usize;
                let mut custom_pred_ids = std::collections::BTreeSet::new();

                for &s in stmts {
                    let c = &costs[s];
                    merkle_proofs += c.merkle_proofs;
                    merkle_state_transitions += c.merkle_state_transitions;
                    custom_pred_verifications += c.custom_pred_verifications;
                    signed_by += c.signed_by;
                    public_key_of += c.public_key_of;
                    custom_pred_ids.extend(c.custom_predicates_ids.iter().cloned());
                }

                let resources = vec![
                    UtilizationRow {
                        name: "private statements",
                        used: stmts.len(),
                        limit: max_priv,
                    },
                    UtilizationRow {
                        name: "merkle proofs",
                        used: merkle_proofs,
                        limit: params.max_merkle_proofs_containers,
                    },
                    UtilizationRow {
                        name: "merkle state transitions",
                        used: merkle_state_transitions,
                        limit: params.max_merkle_tree_state_transition_proofs_containers,
                    },
                    UtilizationRow {
                        name: "custom pred verifications",
                        used: custom_pred_verifications,
                        limit: params.max_custom_predicate_verifications,
                    },
                    UtilizationRow {
                        name: "signed_by",
                        used: signed_by,
                        limit: params.max_signed_by,
                    },
                    UtilizationRow {
                        name: "public_key_of",
                        used: public_key_of,
                        limit: params.max_public_key_of,
                    },
                    UtilizationRow {
                        name: "distinct custom predicates",
                        used: custom_pred_ids.len(),
                        limit: params.max_custom_predicates,
                    },
                ];

                PodUtilization {
                    pod_idx,
                    is_output: pod_idx == pod_count - 1,
                    num_statements: stmts.len(),
                    resources,
                }
            })
            .collect();

        Self {
            pods,
            num_statements,
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

            for row in &pod.resources {
                // Only show rows with nonzero usage to reduce noise
                if row.used > 0 {
                    let pct = if row.limit > 0 {
                        format!("({:>3}%)", (row.used * 100) / row.limit)
                    } else {
                        "".to_string()
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

fn lower_bound(total: usize, limit: usize) -> Option<usize> {
    if total == 0 {
        Some(0)
    } else if limit == 0 {
        None
    } else {
        Some(total.div_ceil(limit))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        frontend::multi_pod::cost::CustomPredicateId,
        middleware::{Hash, RawValue},
    };

    fn default_params() -> Params {
        Params {
            max_statements: 48,
            max_public_statements: 8,
            max_merkle_proofs_containers: 8,
            max_merkle_tree_state_transition_proofs_containers: 4,
            max_custom_predicate_verifications: 10,
            max_custom_predicates: 2,
            max_signed_by: 4,
            max_public_key_of: 4,
            ..Params::default()
        }
    }

    #[test]
    fn test_resource_summary_bottleneck() {
        let params = default_params();
        // max_priv = 48 - 8 = 40

        // 6 merkle proofs, 3 state transitions, rest zero-cost
        let costs: Vec<StatementCost> = (0..14)
            .map(|i| {
                let mut c = StatementCost::default();
                if i < 6 {
                    c.merkle_proofs = 1;
                } else if i < 9 {
                    c.merkle_state_transitions = 1;
                }
                c
            })
            .collect();

        let summary = ResourceSummary::from_costs(&costs, &params);

        // 14 statements / 40 per pod = 1 pod for statements
        // 6 merkle proofs / 8 per pod = 1 pod
        // 3 state transitions / 4 per pod = 1 pod
        // All categories need 1 pod, so bottleneck is whichever has the highest min_pods.
        // They're all 1, so the first with total > 0 wins in max_by_key (stable).
        let bottleneck = summary.bottleneck().unwrap();
        assert_eq!(bottleneck.min_pods, Some(1));

        // Verify display doesn't panic
        let display = format!("{}", summary);
        assert!(display.contains("Resource Summary (14 statements)"));
        assert!(display.contains("merkle proofs"));
    }

    #[test]
    fn test_resource_summary_signed_by_bottleneck() {
        let params = Params {
            max_statements: 48,
            max_public_statements: 8,
            max_signed_by: 2,
            ..Params::default()
        };
        // max_priv = 40

        // 6 signed_by operations
        let costs: Vec<StatementCost> = (0..6)
            .map(|_| StatementCost {
                signed_by: 1,
                ..Default::default()
            })
            .collect();

        let summary = ResourceSummary::from_costs(&costs, &params);
        let bottleneck = summary.bottleneck().unwrap();

        assert_eq!(bottleneck.name, "signed_by");
        // 6 / 2 = 3 pods
        assert_eq!(bottleneck.min_pods, Some(3));
    }

    #[test]
    fn test_resource_summary_custom_predicates_bottleneck() {
        let params = Params {
            max_statements: 48,
            max_public_statements: 8,
            max_custom_predicates: 1, // Only 1 distinct predicate per POD
            max_custom_predicate_verifications: 10,
            ..Params::default()
        };

        // 3 statements using 3 different custom predicates
        let costs: Vec<StatementCost> = (0..3)
            .map(|i| {
                let mut ids = std::collections::BTreeSet::new();
                ids.insert(CustomPredicateId(Hash::from(RawValue::from(i as i64))));
                StatementCost {
                    custom_pred_verifications: 1,
                    custom_predicates_ids: ids,
                    ..Default::default()
                }
            })
            .collect();

        let summary = ResourceSummary::from_costs(&costs, &params);
        let bottleneck = summary.bottleneck().unwrap();

        assert_eq!(bottleneck.name, "distinct custom predicates");
        // 3 distinct predicates / 1 per pod = 3 pods
        assert_eq!(bottleneck.min_pods, Some(3));
    }

    #[test]
    fn test_solution_breakdown_display() {
        let params = default_params();

        let costs: Vec<StatementCost> = (0..8)
            .map(|i| {
                let mut c = StatementCost::default();
                if i < 4 {
                    c.merkle_proofs = 1;
                } else {
                    c.merkle_state_transitions = 1;
                }
                c
            })
            .collect();

        let pod_statements = vec![
            vec![0, 1, 2, 3], // POD 0: 4 merkle proofs
            vec![4, 5, 6, 7], // POD 1: 4 state transitions
        ];

        let breakdown = SolutionBreakdown::from_solution(&costs, &pod_statements, 2, 8, &params);

        assert_eq!(breakdown.pods.len(), 2);
        assert!(!breakdown.pods[0].is_output);
        assert!(breakdown.pods[1].is_output);

        // POD 0 should have 4 merkle proofs
        let mp = breakdown.pods[0]
            .resources
            .iter()
            .find(|r| r.name == "merkle proofs")
            .unwrap();
        assert_eq!(mp.used, 4);
        assert_eq!(mp.limit, 8);

        // POD 1 should have 4 state transitions
        let mst = breakdown.pods[1]
            .resources
            .iter()
            .find(|r| r.name == "merkle state transitions")
            .unwrap();
        assert_eq!(mst.used, 4);
        assert_eq!(mst.limit, 4);

        // Verify display doesn't panic and contains expected content
        let display = format!("{}", breakdown);
        assert!(display.contains("Solution Breakdown (8 statements -> 2 PODs)"));
        assert!(display.contains("POD 0 (intermediate)"));
        assert!(display.contains("POD 1 (output)"));
    }

    #[test]
    fn test_utilization_row_fraction() {
        let row = UtilizationRow {
            name: "test",
            used: 3,
            limit: 4,
        };
        assert!((row.utilization() - 0.75).abs() < f64::EPSILON);

        let zero_row = UtilizationRow {
            name: "test",
            used: 0,
            limit: 4,
        };
        assert!((zero_row.utilization()).abs() < f64::EPSILON);
    }
}
