//! Test-only MILP oracle used to cross-validate the DP partitioner. Not part
//! of any production code path; the DP partitioner is the sole production
//! algorithm. The oracle exists so randomized tests can assert that whenever
//! MILP finds a feasible split at some K, DP also finds one at some K
//! (possibly larger, since DP is exact only over the chosen ordering).

#![allow(clippy::needless_range_loop)]

use good_lp::{
    constraint, solvers::scip::SCIPProblem, variable, Expression, ProblemVariables, Solution,
    SolverModel, Variable,
};

use crate::{lang::frontend_ast_split::LinkAssignment, middleware::Params};

const SCIP_RANDOM_SEED: i32 = 0;
const SOLVER_BINARY_THRESHOLD: f64 = 0.5;

/// MILP variables. All binary; constraints C1..C7 in `add_structural_constraints`
/// pin every variable other than `assign` to be an exact function of the
/// assignment.
struct MilpVars {
    n: usize,
    k: usize,
    num_wildcards: usize,
    assign: Vec<Vec<Variable>>,
    u: Vec<Vec<Variable>>,
    before: Vec<Vec<Variable>>,
    after: Vec<Vec<Variable>>,
    pubin: Vec<Vec<Variable>>,
    privin: Vec<Vec<Variable>>,
}

fn mk_binary_grid(vars: &mut ProblemVariables, rows: usize, cols: usize) -> Vec<Vec<Variable>> {
    (0..rows)
        .map(|_| (0..cols).map(|_| vars.add(variable().binary())).collect())
        .collect()
}

fn declare_milp_vars(
    vars: &mut ProblemVariables,
    n: usize,
    k: usize,
    num_wildcards: usize,
) -> MilpVars {
    MilpVars {
        n,
        k,
        num_wildcards,
        assign: mk_binary_grid(vars, n, k),
        u: mk_binary_grid(vars, num_wildcards, k),
        before: mk_binary_grid(vars, num_wildcards, k),
        after: mk_binary_grid(vars, num_wildcards, k),
        pubin: mk_binary_grid(vars, num_wildcards, k),
        privin: mk_binary_grid(vars, num_wildcards, k),
    }
}

fn source_order_tiebreaker(v: &MilpVars) -> Expression {
    (0..v.n)
        .flat_map(|s| (0..v.k).map(move |i| (s, i)))
        .map(|(s, i)| ((v.n - s) as f64) * (i as f64) * v.assign[s][i])
        .sum()
}

fn build_scip_model(vars: ProblemVariables, objective: Expression) -> SCIPProblem {
    vars.minimise(objective)
        .using(good_lp::solvers::scip::scip)
        .set_option("randomization/randomseedshift", SCIP_RANDOM_SEED)
        .set_verbose(false)
        // Huge gap: any integer-feasible incumbent satisfies the gap
        // limit, so SCIP exits with `GapLimit` after the first feasible
        // solution.
        .set_option("limits/gap", 1e20_f64)
        .set_option("separating/maxrounds", 0_i32)
        .set_option("separating/maxroundsroot", 0_i32)
}

fn add_structural_constraints<M: SolverModel>(
    model: &mut M,
    v: &MilpVars,
    statements_using: &[Vec<usize>],
    is_original_public: &[bool],
) {
    let max_arity = Params::max_custom_predicate_arity();
    let MilpVars {
        n,
        k,
        num_wildcards,
        assign,
        u,
        before,
        after,
        pubin,
        privin,
    } = v;
    let (n, k, num_wildcards) = (*n, *k, *num_wildcards);

    // C1: Each statement assigned to exactly one link.
    for s in 0..n {
        let sum: Expression = (0..k).map(|i| assign[s][i]).sum();
        model.add_constraint(constraint!(sum == 1));
    }

    // C2: Per-link statement count. Non-last links reserve a slot for the
    // chain call. Also require at least one statement per link.
    for i in 0..k {
        let cap = if i + 1 < k { max_arity - 1 } else { max_arity };
        let sum_le: Expression = (0..n).map(|s| assign[s][i]).sum();
        model.add_constraint(constraint!(sum_le <= cap as f64));
        let sum_ge: Expression = (0..n).map(|s| assign[s][i]).sum();
        model.add_constraint(constraint!(sum_ge >= 1));
    }

    // C3: u[w][i] is exactly the OR over s referencing w of assign[s][i].
    for w in 0..num_wildcards {
        for i in 0..k {
            for &s in &statements_using[w] {
                model.add_constraint(constraint!(u[w][i] >= assign[s][i]));
            }
            let upper: Expression = statements_using[w]
                .iter()
                .map(|&s| Expression::from(assign[s][i]))
                .sum();
            model.add_constraint(constraint!(u[w][i] <= upper));
        }
    }

    // C4: before[w][i] = u[w][0] OR ... OR u[w][i].
    for w in 0..num_wildcards {
        model.add_constraint(constraint!(before[w][0] == u[w][0]));
        for i in 1..k {
            model.add_constraint(constraint!(before[w][i] >= before[w][i - 1]));
            model.add_constraint(constraint!(before[w][i] >= u[w][i]));
            model.add_constraint(constraint!(before[w][i] <= before[w][i - 1] + u[w][i]));
        }
    }

    // C5: after[w][i] = u[w][i] OR ... OR u[w][k-1].
    for w in 0..num_wildcards {
        model.add_constraint(constraint!(after[w][k - 1] == u[w][k - 1]));
        for i in (0..k - 1).rev() {
            model.add_constraint(constraint!(after[w][i] >= after[w][i + 1]));
            model.add_constraint(constraint!(after[w][i] >= u[w][i]));
            model.add_constraint(constraint!(after[w][i] <= after[w][i + 1] + u[w][i]));
        }
    }

    // C6: pubin definitions.
    for w in 0..num_wildcards {
        if is_original_public[w] {
            model.add_constraint(constraint!(pubin[w][0] == 1));
            for i in 1..k {
                model.add_constraint(constraint!(pubin[w][i] == after[w][i]));
            }
        } else {
            model.add_constraint(constraint!(pubin[w][0] == 0));
            for i in 1..k {
                model.add_constraint(constraint!(pubin[w][i] <= before[w][i - 1]));
                model.add_constraint(constraint!(pubin[w][i] <= after[w][i]));
                model.add_constraint(constraint!(
                    pubin[w][i] >= before[w][i - 1] + after[w][i] - 1
                ));
            }
        }
    }

    // C7: privin definitions.
    for w in 0..num_wildcards {
        if is_original_public[w] {
            for i in 0..k {
                model.add_constraint(constraint!(privin[w][i] == 0));
            }
        } else {
            model.add_constraint(constraint!(privin[w][0] == u[w][0]));
            for i in 1..k {
                model.add_constraint(constraint!(privin[w][i] <= u[w][i]));
                model.add_constraint(constraint!(privin[w][i] <= 1 - before[w][i - 1]));
                model.add_constraint(constraint!(privin[w][i] >= u[w][i] - before[w][i - 1]));
            }
        }
    }
}

/// Try to partition `n` statements into exactly `k` links using MILP.
/// Returns `Some(assignment)` if feasible, `None` if infeasible at this K.
pub(super) fn solve_milp_for_k(
    n: usize,
    k: usize,
    statements_using: &[Vec<usize>],
    is_original_public: &[bool],
    params: &Params,
) -> Option<LinkAssignment> {
    let max_args = Params::max_statement_args();
    let max_wildcards = params.max_custom_predicate_wildcards;
    let num_wildcards = is_original_public.len();

    let mut vars = ProblemVariables::new();
    let v = declare_milp_vars(&mut vars, n, k, num_wildcards);
    let objective = source_order_tiebreaker(&v);
    let mut model = build_scip_model(vars, objective);
    add_structural_constraints(&mut model, &v, statements_using, is_original_public);

    // C8: per-link public-args cap.
    for i in 0..k {
        let sum: Expression = (0..num_wildcards).map(|w| v.pubin[w][i]).sum();
        model.add_constraint(constraint!(sum <= max_args as f64));
    }

    // C9: per-link total declared wildcards cap.
    for i in 0..k {
        let sum: Expression = (0..num_wildcards)
            .map(|w| Expression::from(v.pubin[w][i]) + v.privin[w][i])
            .sum();
        model.add_constraint(constraint!(sum <= max_wildcards as f64));
    }

    let solution = model.solve().ok()?;

    let mut links: LinkAssignment = vec![Vec::new(); k];
    for s in 0..n {
        for i in 0..k {
            if solution.value(v.assign[s][i]) > SOLVER_BINARY_THRESHOLD {
                links[i].push(s);
                break;
            }
        }
    }
    Some(links)
}

#[cfg(test)]
mod tests {
    use super::solve_milp_for_k;
    use crate::{
        lang::frontend_ast_split::{
            build_pred, compute_min_links, prepare_split_input, split_predicate_if_needed,
            validate_predicate_is_splittable,
        },
        middleware::Params,
    };

    /// DP-vs-MILP parity sweep. For randomized predicates, asserts:
    /// whenever MILP finds a feasible K, DP also finds a feasible split
    /// (possibly at a larger K, since DP is exact only over the chosen
    /// ordering).
    ///
    /// Shapes are biased toward the tight cases: more public args (4 leaves
    /// only 1 slot for promotion), wildcard pools at or above the per-link
    /// total-wildcards cap of 8, and statement arity 3 to keep every link
    /// crowded. Shapes that almost always fit easily are uninteresting here.
    ///
    /// Run with `cargo test --release dp_milp_parity -- --ignored --nocapture`.
    /// `#[ignore]`d because it runs MILP 1200 times (~90s on a developer laptop).
    /// Last run clean on 2026-05-11: 1200 trials, 1177 MILP-feasible, 0 DP divergences.
    #[test]
    #[ignore]
    fn dp_milp_parity() {
        use rand::{Rng, SeedableRng};
        use rand_chacha::ChaCha20Rng;

        let params = Params::default();
        let mut rng = ChaCha20Rng::seed_from_u64(0xDEADBEEF);
        let mut checked = 0usize;
        let mut milp_feasible = 0usize;
        let mut divergences = 0usize;
        let mut milp_total = std::time::Duration::ZERO;
        let mut dp_total = std::time::Duration::ZERO;
        let mut milp_max = std::time::Duration::ZERO;
        let mut dp_max = std::time::Duration::ZERO;

        for &n_stmts in &[9usize, 10, 11, 12] {
            for &n_pub in &[3usize, 4] {
                for &n_priv in &[4usize, 5, 6] {
                    let pub_names: Vec<String> = (0..n_pub).map(|i| format!("A{}", i)).collect();
                    let priv_names: Vec<String> = (0..n_priv).map(|i| format!("T{}", i)).collect();
                    let all_names: Vec<String> =
                        pub_names.iter().chain(priv_names.iter()).cloned().collect();

                    for trial in 0..50 {
                        let stmt_wildcards: Vec<Vec<String>> = (0..n_stmts)
                            .map(|_| {
                                let arity = 3;
                                let mut chosen = Vec::new();
                                let mut tries = 0;
                                while chosen.len() < arity && tries < 20 {
                                    let pick = all_names[rng.gen_range(0..all_names.len())].clone();
                                    if !chosen.contains(&pick) {
                                        chosen.push(pick);
                                    }
                                    tries += 1;
                                }
                                chosen
                            })
                            .collect();

                        let stmt_refs: Vec<Vec<&str>> = stmt_wildcards
                            .iter()
                            .map(|v| v.iter().map(|s| s.as_str()).collect())
                            .collect();
                        let stmt_slices: Vec<&[&str]> =
                            stmt_refs.iter().map(|v| v.as_slice()).collect();
                        let pub_refs: Vec<&str> = pub_names.iter().map(|s| s.as_str()).collect();
                        let priv_refs: Vec<&str> = priv_names.iter().map(|s| s.as_str()).collect();

                        let pred = build_pred("p", &pub_refs, &priv_refs, &stmt_slices);
                        if validate_predicate_is_splittable(&pred).is_err() {
                            continue;
                        }
                        checked += 1;

                        let input = prepare_split_input(&pred);
                        let n = input.n;
                        let milp_start = std::time::Instant::now();
                        let mut milp_ok = false;
                        for k in compute_min_links(n)..=n {
                            if solve_milp_for_k(
                                n,
                                k,
                                &input.statements_using,
                                &input.is_original_public,
                                &params,
                            )
                            .is_some()
                            {
                                milp_ok = true;
                                break;
                            }
                        }
                        let milp_elapsed = milp_start.elapsed();
                        milp_total += milp_elapsed;
                        if milp_elapsed > milp_max {
                            milp_max = milp_elapsed;
                        }

                        let dp_start = std::time::Instant::now();
                        let dp_result = split_predicate_if_needed(pred, &params);
                        let dp_elapsed = dp_start.elapsed();
                        dp_total += dp_elapsed;
                        if dp_elapsed > dp_max {
                            dp_max = dp_elapsed;
                        }
                        let dp_ok = dp_result.is_ok();

                        if milp_ok {
                            milp_feasible += 1;
                        }
                        if milp_ok && !dp_ok {
                            divergences += 1;
                            eprintln!(
                                "\n=== DIVERGENCE #{} (n={}, n_pub={}, n_priv={}, trial={}) ===",
                                divergences, n_stmts, n_pub, n_priv, trial
                            );
                            for (i, wcs) in stmt_wildcards.iter().enumerate() {
                                eprintln!("  s{}: {:?}", i, wcs);
                            }
                            eprintln!(
                                "  MILP: feasible, DP: {}",
                                dp_result.as_ref().err().unwrap()
                            );
                        }
                    }
                }
            }
        }

        let safe_divs = |total: std::time::Duration, n: usize| -> std::time::Duration {
            if n == 0 {
                std::time::Duration::ZERO
            } else {
                total / n as u32
            }
        };
        eprintln!(
            "Parity sweep: checked={}, milp_feasible={}, dp_divergences={}",
            checked, milp_feasible, divergences
        );
        eprintln!(
            "  MILP total={:?} mean={:?} max={:?}",
            milp_total,
            safe_divs(milp_total, checked),
            milp_max
        );
        eprintln!(
            "  DP   total={:?} mean={:?} max={:?}",
            dp_total,
            safe_divs(dp_total, checked),
            dp_max
        );
        assert_eq!(
            divergences, 0,
            "DP failed where MILP succeeded on {} predicates",
            divergences
        );
    }
}
