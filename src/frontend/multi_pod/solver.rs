//! Shared types for multi-POD solver solutions.
//!
//! Contains the solution representation (`MultiPodSolution`), solver input
//! (`SolverInput`), and an independent constraint validator.

use std::collections::BTreeSet;

use crate::{
    frontend::multi_pod::{
        cost::StatementCost,
        deps::{DependencyGraph, ExternalDependency, StatementSource},
    },
    middleware::{Hash, Params},
};

/// Solution to the multi-POD packing problem.
///
/// Describes how statements are assigned to pods, which statements are
/// public in each pod, and how pods are wired together via internal and
/// external inputs.
#[derive(Debug)]
pub struct MultiPodSolution {
    /// Number of PODs needed.
    pub pod_count: usize,

    /// For each statement index, which POD(s) it is proved in.
    /// (A statement may be proved in multiple PODs if re-proving is cheaper than copying.)
    pub statement_to_pods: Vec<Vec<usize>>,

    /// For each POD, which statement indices are proved in it.
    pub pod_statements: Vec<Vec<usize>>,

    /// For each POD, which statement indices are public in it.
    pub pod_public_statements: Vec<BTreeSet<usize>>,

    /// For each POD, which earlier internal PODs are used as inputs.
    pub pod_internal_inputs: Vec<BTreeSet<usize>>,

    /// External input POD hashes referenced by the solution.
    /// `pod_external_inputs[*]` stores indices into this vector.
    pub external_pod_hashes: Vec<Hash>,

    /// For each POD, which external input PODs are used as inputs.
    /// Indices are into `external_pod_hashes`.
    pub pod_external_inputs: Vec<BTreeSet<usize>>,

    /// Unique external premises referenced by statement dependencies.
    pub external_premises: Vec<ExternalDependency>,

    /// For each POD, which external premises are exposed as public statements.
    /// Indices are into `external_premises`.
    pub pod_public_external_premises: Vec<BTreeSet<usize>>,
}

impl MultiPodSolution {
    /// Independently validate all constraints of the solution against the
    /// original problem input. Returns a list of violations (empty = valid).
    ///
    /// Checks:
    /// 1. Structural consistency (lengths, index bounds)
    /// 2. Output pod contains all required public statements
    /// 3. Per-pod resource limits (statements, merkle, cpv, signed_by, etc.)
    /// 4. Per-pod input slot limits (internal + external ≤ max_input_pods)
    /// 5. Per-pod public statement limits
    /// 6. Dependency satisfaction: every internal dep of a local statement
    ///    is either local or available from an input pod's public set
    /// 7. Topological ordering: internal inputs reference earlier pods
    pub fn validate(&self, input: &SolverInput) -> Vec<String> {
        let mut errors = Vec::new();

        // 1. Structural consistency
        if self.pod_count == 0 {
            errors.push("pod_count is 0".into());
            return errors;
        }
        if self.pod_statements.len() != self.pod_count {
            errors.push(format!(
                "pod_statements.len()={} != pod_count={}",
                self.pod_statements.len(),
                self.pod_count
            ));
        }
        if self.pod_public_statements.len() != self.pod_count {
            errors.push(format!(
                "pod_public_statements.len()={} != pod_count={}",
                self.pod_public_statements.len(),
                self.pod_count
            ));
        }
        if self.pod_internal_inputs.len() != self.pod_count {
            errors.push(format!(
                "pod_internal_inputs.len()={} != pod_count={}",
                self.pod_internal_inputs.len(),
                self.pod_count
            ));
        }
        if self.pod_external_inputs.len() != self.pod_count {
            errors.push(format!(
                "pod_external_inputs.len()={} != pod_count={}",
                self.pod_external_inputs.len(),
                self.pod_count
            ));
        }
        if !errors.is_empty() {
            return errors; // Can't continue with mismatched lengths.
        }

        // 2. Output pod (last) contains all required public statements
        let output_idx = self.pod_count - 1;
        for &pub_idx in input.output_public_indices {
            let in_local = self.pod_statements[output_idx].contains(&pub_idx);
            let in_public = self.pod_public_statements[output_idx].contains(&pub_idx);
            if !in_public {
                errors.push(format!(
                    "output pod {} missing required public statement {}",
                    output_idx, pub_idx
                ));
            }
            // If not proved locally, it must come from a parent pod's public set.
            if !in_local {
                let available_from_parent = self.pod_internal_inputs[output_idx]
                    .iter()
                    .any(|&parent| self.pod_public_statements[parent].contains(&pub_idx));
                if !available_from_parent {
                    errors.push(format!(
                        "output pod {} has public statement {} but it's not proved \
                         locally and not available from any parent pod",
                        output_idx, pub_idx
                    ));
                }
            }
        }

        let max_priv = input.params.max_priv_statements();

        for p in 0..self.pod_count {
            let stmts = &self.pod_statements[p];
            let local_set: BTreeSet<usize> = stmts.iter().copied().collect();

            // 3. Resource limits
            let mut total_stmts = 0usize;
            let mut total_merkle = 0usize;
            let mut total_merkle_st = 0usize;
            let mut total_cpv = 0usize;
            let mut total_signed_by = 0usize;
            let mut total_pko = 0usize;
            for &s in stmts {
                if s >= input.costs.len() {
                    errors.push(format!("pod {} has out-of-bounds statement {}", p, s));
                    continue;
                }
                let c = &input.costs[s];
                total_stmts += 1;
                total_merkle += c.merkle_proofs;
                total_merkle_st += c.merkle_state_transitions;
                total_cpv += c.custom_pred_verifications;
                total_signed_by += c.signed_by;
                total_pko += c.public_key_of;
            }
            if total_stmts > max_priv {
                errors.push(format!(
                    "pod {} has {} statements, limit {}",
                    p, total_stmts, max_priv
                ));
            }
            if total_merkle > input.params.max_merkle_proofs_containers {
                errors.push(format!(
                    "pod {} has {} merkle proofs, limit {}",
                    p, total_merkle, input.params.max_merkle_proofs_containers
                ));
            }
            if total_merkle_st
                > input
                    .params
                    .max_merkle_tree_state_transition_proofs_containers
            {
                errors.push(format!(
                    "pod {} has {} merkle state transitions, limit {}",
                    p,
                    total_merkle_st,
                    input
                        .params
                        .max_merkle_tree_state_transition_proofs_containers
                ));
            }
            if total_cpv > input.params.max_custom_predicate_verifications {
                errors.push(format!(
                    "pod {} has {} custom pred verifications, limit {}",
                    p, total_cpv, input.params.max_custom_predicate_verifications
                ));
            }
            if total_signed_by > input.params.max_signed_by {
                errors.push(format!(
                    "pod {} has {} signed_by, limit {}",
                    p, total_signed_by, input.params.max_signed_by
                ));
            }
            if total_pko > input.params.max_public_key_of {
                errors.push(format!(
                    "pod {} has {} public_key_of, limit {}",
                    p, total_pko, input.params.max_public_key_of
                ));
            }

            // 4. Input slot limits
            let total_inputs =
                self.pod_internal_inputs[p].len() + self.pod_external_inputs[p].len();
            if total_inputs > input.params.max_input_pods {
                errors.push(format!(
                    "pod {} has {} inputs ({}i + {}e), limit {}",
                    p,
                    total_inputs,
                    self.pod_internal_inputs[p].len(),
                    self.pod_external_inputs[p].len(),
                    input.params.max_input_pods
                ));
            }

            // 5. Public statement limits
            let total_public =
                self.pod_public_statements[p].len() + self.pod_public_external_premises[p].len();
            if total_public > input.params.max_public_statements {
                errors.push(format!(
                    "pod {} has {} public statements, limit {}",
                    p, total_public, input.params.max_public_statements
                ));
            }

            // 6. Dependency satisfaction
            for &s in stmts {
                if s >= input.deps.statement_deps.len() {
                    continue; // Already flagged as out-of-bounds.
                }
                for dep in &input.deps.statement_deps[s] {
                    match dep {
                        StatementSource::Internal(dep_idx) => {
                            if local_set.contains(dep_idx) {
                                continue; // Proved locally.
                            }
                            // Must be available from an input pod's public set.
                            let from_parent = self.pod_internal_inputs[p].iter().any(|&parent| {
                                self.pod_statements[parent].contains(dep_idx)
                                    && self.pod_public_statements[parent].contains(dep_idx)
                            });
                            if !from_parent {
                                errors.push(format!(
                                    "pod {} statement {} depends on {} which is not \
                                     local and not public in any parent pod",
                                    p, s, dep_idx
                                ));
                            }
                        }
                        StatementSource::External(ext) => {
                            // The external pod must be an input to this pod,
                            // OR available via a parent pod that forwards it.
                            let ext_pod_idx = self
                                .external_pod_hashes
                                .iter()
                                .position(|h| *h == ext.pod_hash);
                            let direct = ext_pod_idx
                                .map(|idx| self.pod_external_inputs[p].contains(&idx))
                                .unwrap_or(false);
                            if !direct {
                                let ext_prem_idx =
                                    self.external_premises.iter().position(|e| e == ext);
                                let forwarded = ext_prem_idx.is_some_and(|prem_idx| {
                                    self.pod_internal_inputs[p].iter().any(|&parent| {
                                        self.pod_public_external_premises[parent]
                                            .contains(&prem_idx)
                                    })
                                });
                                if !forwarded {
                                    errors.push(format!(
                                        "pod {} statement {} depends on external pod {:?} \
                                         which is not a direct input and not forwarded \
                                         by any parent",
                                        p, s, ext.pod_hash
                                    ));
                                }
                            }
                        }
                    }
                }
            }

            // 7. Topological ordering
            for &parent in &self.pod_internal_inputs[p] {
                if parent >= p {
                    errors.push(format!(
                        "pod {} references input pod {} which is not earlier in order",
                        p, parent
                    ));
                }
            }
        }

        errors
    }
}

/// Input to the solver.
#[derive(Debug)]
pub struct SolverInput<'a> {
    /// Number of statements.
    pub num_statements: usize,

    /// Resource costs for each statement.
    pub costs: &'a [StatementCost],

    /// Dependency graph.
    pub deps: &'a DependencyGraph,

    /// Indices of statements that must be public in output PODs.
    pub output_public_indices: &'a [usize],

    /// Parameters defining per-POD limits.
    pub params: &'a Params,

    /// Maximum number of PODs the solver will consider.
    pub max_pods: usize,
}
