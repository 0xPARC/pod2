//! Predicate splitting for frontend AST
//!
//! Predicates whose statement count exceeds the middleware's
//! `max_custom_predicate_arity` are split into a chain of smaller predicates,
//! each calling the next via a tail-position chain call. Private wildcards
//! that span a split boundary must be promoted to public arguments on the
//! continuation, since they need the same binding on both sides.
//!
//! The split is computed by an MILP that, for a given number of links K:
//!
//! - Assigns each statement to exactly one link.
//! - Tracks which wildcards are used and where, derives "live ranges," and
//!   counts each link's declared public/private wildcards.
//! - Caps each link's public-arg count at `max_statement_args` and total
//!   declared wildcards at `max_custom_predicate_wildcards`.
//! - Reserves a chain-call slot on every non-last link.
//!
//! We try `K = K_min, K_min+1, ...` and stop at the first feasible K. The
//! objective is a tiny `Σ (n-s) · i · assign[s][i]` tiebreaker that biases
//! statements with low original index toward low-index links — so the chain
//! roughly follows source order when nothing else forces a rearrangement.
//!
//! On infeasibility for every K up to `n`, we emit
//! [`SplittingError::Infeasible`].

#![allow(clippy::needless_range_loop)]

use std::{
    collections::{HashMap, HashSet, VecDeque},
    fmt,
};

use good_lp::{
    constraint, solvers::scip::SCIPProblem, variable, Expression, ProblemVariables, Solution,
    SolverModel, Variable,
};
use itertools::Itertools;

/// Solver random-seed shift. Pinning this gives within-version reproducibility
/// against any internal SCIP heuristics that consult the seed (random
/// branching, restart shuffles, etc.). Cross-version determinism still
/// depends on SCIP not changing its algorithms; pin russcip in `Cargo.toml`
/// to control that.
const SCIP_RANDOM_SEED: i32 = 0;

pub use crate::lang::error::SplittingError;
use crate::{lang::frontend_ast::*, middleware::Params};

/// Threshold for interpreting MILP solver's floating-point results as binary.
/// The solver returns continuous values in [0, 1] for binary variables;
/// values > 0.5 are interpreted as "true" (1), otherwise "false" (0).
const SOLVER_BINARY_THRESHOLD: f64 = 0.5;

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

/// Per-link bottleneck found by [`analyze_infeasibility`]: how far each
/// binding link overshoots the per-link caps, and which wildcards crowd it.
#[derive(Debug, Clone)]
pub struct LinkOvershoot {
    pub link_index: usize,
    /// Number of public-args slots over `max_statement_args` for this link.
    pub public_args_overflow: usize,
    /// Number of total declared-wildcard slots over `max_custom_predicate_wildcards`.
    pub total_args_overflow: usize,
    /// Wildcards passed in to this link as public args (in the elastic solution).
    pub public_args_in: Vec<String>,
    /// Wildcards declared as private at this link (in the elastic solution).
    pub private_args: Vec<String>,
}

/// Diagnostic report explaining why [`split_predicate_if_needed`] returned
/// [`SplittingError::Infeasible`]. Produced by [`analyze_infeasibility`] on
/// demand — the splitter itself doesn't compute it, since computing it
/// requires a second LP solve.
#[derive(Debug, Clone)]
pub struct InfeasibilityReport {
    pub predicate: String,
    /// Number of links the elastic LP was solved at (the minimum K).
    pub k: usize,
    /// Per-link overshoots in link-index order. Links not over any cap are omitted.
    pub overshoots: Vec<LinkOvershoot>,
}

impl fmt::Display for InfeasibilityReport {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(
            f,
            "Predicate '{}' cannot be split into {} link(s) without overflowing per-link caps:",
            self.predicate, self.k
        )?;
        let max_args = Params::max_statement_args();
        for o in &self.overshoots {
            if o.public_args_overflow > 0 {
                writeln!(
                    f,
                    "  link {}: public_args_in = [{}] ({} args, {} over the {}-arg cap)",
                    o.link_index,
                    o.public_args_in.join(", "),
                    o.public_args_in.len(),
                    o.public_args_overflow,
                    max_args
                )?;
            }
            if o.total_args_overflow > 0 {
                writeln!(
                    f,
                    "  link {}: declared {} wildcards (public_args_in + private_args), {} over the cap",
                    o.link_index,
                    o.public_args_in.len() + o.private_args.len(),
                    o.total_args_overflow,
                )?;
            }
        }
        Ok(())
    }
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

/// Split a predicate into a chain if it exceeds statement limit.
pub fn split_predicate_if_needed(
    pred: &CustomPredicateDef,
    params: &Params,
) -> Result<SplitResult, SplittingError> {
    validate_predicate_is_splittable(pred)?;
    eprintln!("Splitting predicate: {}", pred);

    if pred.statements.len() <= Params::max_custom_predicate_arity() {
        return Ok(SplitResult {
            predicates: vec![pred.clone()],
            chain_info: None,
        });
    }

    let (predicates, chain_info) = split_into_chain(pred, params)?;

    eprintln!(
        "Split result: {}",
        predicates
            .clone()
            .into_iter()
            .map(|p| format!("{}", p))
            .join("\n\n")
    );

    Ok(SplitResult {
        predicates,
        chain_info: Some(chain_info),
    })
}

fn collect_wildcards_from_statement(stmt: &StatementTmpl) -> HashSet<String> {
    stmt.wildcard_names().map(str::to_string).collect()
}

/// Compute the minimum number of chain links needed to fit `n` statements,
/// given that non-last links reserve 1 slot for the chain call (so they hold
/// up to `max_arity - 1` real statements) and the last link uses all of
/// `max_arity`.
fn compute_min_links(n: usize) -> usize {
    let max_arity = Params::max_custom_predicate_arity();
    if n <= max_arity {
        1
    } else {
        // Smallest K such that (K-1)·(max_arity-1) + max_arity >= n
        (n - max_arity).div_ceil(max_arity - 1) + 1
    }
}

/// Build the projected stmt-adjacency graph: two stmts are adjacent iff they
/// share any wildcard.
fn build_stmt_adjacency(n: usize, statements_using: &[Vec<usize>]) -> Vec<HashSet<usize>> {
    let mut adjacency: Vec<HashSet<usize>> = vec![HashSet::new(); n];
    for stmts in statements_using {
        for i in 0..stmts.len() {
            for j in (i + 1)..stmts.len() {
                adjacency[stmts[i]].insert(stmts[j]);
                adjacency[stmts[j]].insert(stmts[i]);
            }
        }
    }
    adjacency
}

/// Reverse Cuthill–McKee from a chosen start node. Visits in BFS order,
/// neighbours sorted by (degree, index); reverses the visit order at the end.
fn rcm_from_start(
    n: usize,
    adjacency: &[HashSet<usize>],
    degrees: &[usize],
    start: usize,
) -> Vec<usize> {
    let mut visited = vec![false; n];
    let mut result = Vec::with_capacity(n);
    visited[start] = true;
    let mut queue = VecDeque::new();
    queue.push_back(start);

    loop {
        while let Some(node) = queue.pop_front() {
            result.push(node);
            let mut neighbors: Vec<usize> = adjacency[node]
                .iter()
                .copied()
                .filter(|&m| !visited[m])
                .collect();
            neighbors.sort_by_key(|&m| (degrees[m], m));
            for m in neighbors {
                if !visited[m] {
                    visited[m] = true;
                    queue.push_back(m);
                }
            }
        }
        if result.len() == n {
            break;
        }
        // Disconnected wildcard graphs are rare in real predicates but
        // possible (e.g. an unused public arg shares no statements with the
        // rest), so restart BFS at the lowest-degree unvisited node.
        let next_start = (0..n)
            .filter(|&i| !visited[i])
            .min_by_key(|&i| (degrees[i], i))
            .expect("unvisited nodes remain");
        visited[next_start] = true;
        queue.push_back(next_start);
    }

    result.reverse();
    result
}

/// Try (R)CM from every start node, in both forward and reversed BFS order.
/// Returns distinct orderings only.
fn rcm_orderings(n: usize, statements_using: &[Vec<usize>]) -> Vec<Vec<usize>> {
    let adjacency = build_stmt_adjacency(n, statements_using);
    let degrees: Vec<usize> = adjacency.iter().map(|s| s.len()).collect();
    let mut seen: HashSet<Vec<usize>> = HashSet::new();
    let mut out = Vec::new();
    for start in 0..n {
        let rcm = rcm_from_start(n, &adjacency, &degrees, start);
        if seen.insert(rcm.clone()) {
            out.push(rcm.clone());
        }
        let mut cm = rcm;
        cm.reverse();
        if seen.insert(cm.clone()) {
            out.push(cm);
        }
    }
    out
}

/// Per-position wildcard usage and the running prefix/suffix unions over an
/// ordering. `wcs_at[p]` lists the wildcards used by the statement at
/// position `p`; `prefix[p]` and `suffix[p]` are the running unions of
/// `wcs_at` over `[0..p)` and `[p..n)` respectively.
struct WildcardLifetimes {
    wcs_at: Vec<HashSet<usize>>,
    prefix: Vec<HashSet<usize>>,
    suffix: Vec<HashSet<usize>>,
}

/// Compute [`WildcardLifetimes`] for a given ordering. Shared between
/// [`ordering_excess_cost`] and [`try_dp_at_k`], which both need to know
/// which wildcards are alive across each cut.
fn wildcard_lifetimes(
    ordering: &[usize],
    statements_using: &[Vec<usize>],
    num_wildcards: usize,
) -> WildcardLifetimes {
    let n = ordering.len();
    let mut pos_of = vec![usize::MAX; statements_using.len().max(n)];
    for (p, &s) in ordering.iter().enumerate() {
        if s < pos_of.len() {
            pos_of[s] = p;
        }
    }
    let mut wcs_at: Vec<HashSet<usize>> = vec![HashSet::new(); n];
    for (w, stmts) in statements_using.iter().enumerate().take(num_wildcards) {
        for &s in stmts {
            let p = pos_of[s];
            if p != usize::MAX {
                wcs_at[p].insert(w);
            }
        }
    }
    let mut prefix: Vec<HashSet<usize>> = vec![HashSet::new(); n + 1];
    for p in 0..n {
        prefix[p + 1] = prefix[p].clone();
        prefix[p + 1].extend(&wcs_at[p]);
    }
    let mut suffix: Vec<HashSet<usize>> = vec![HashSet::new(); n + 1];
    for p in (0..n).rev() {
        suffix[p] = suffix[p + 1].clone();
        suffix[p].extend(&wcs_at[p]);
    }
    WildcardLifetimes {
        wcs_at,
        prefix,
        suffix,
    }
}

/// Sum of "bandwidth excess" over an ordering: for each potential boundary
/// position, how many wildcards beyond `max_args` would cross it. Lower is
/// better for the DP partitioner — when this drops to 0, every position is
/// a viable boundary, so any chunking that fits the per-link statement cap
/// is feasible.
fn ordering_excess_cost(
    ordering: &[usize],
    statements_using: &[Vec<usize>],
    is_original_public: &[bool],
    max_args: usize,
) -> usize {
    let n = ordering.len();
    let num_wildcards = is_original_public.len();
    let WildcardLifetimes {
        prefix, suffix, ..
    } = wildcard_lifetimes(ordering, statements_using, num_wildcards);
    let mut total: usize = 0;
    for p in 1..n {
        let mut bw: usize = 0;
        for w in 0..num_wildcards {
            if is_original_public[w] {
                if suffix[p].contains(&w) {
                    bw += 1;
                }
            } else if prefix[p].contains(&w) && suffix[p].contains(&w) {
                bw += 1;
            }
        }
        total += bw.saturating_sub(max_args);
    }
    total
}

/// Iteration budget for [`refine_ordering`]. Local search is cheap per step
/// (a swap and a full cost recompute) so a few thousand attempts comfortably
/// fits in the per-predicate budget on the inputs we've measured.
const REFINE_ITERATIONS: usize = 5_000;

/// Local-search refinement: starting from `initial`, try random pair swaps
/// to reduce ordering excess cost. Returns the best ordering found. Uses a
/// seeded ChaCha RNG so the result is deterministic for a given input.
fn refine_ordering(
    initial: Vec<usize>,
    statements_using: &[Vec<usize>],
    is_original_public: &[bool],
    max_args: usize,
    iters: usize,
) -> Vec<usize> {
    use rand::{Rng, SeedableRng};
    use rand_chacha::ChaCha20Rng;

    let n = initial.len();
    if n < 2 {
        return initial;
    }
    let mut current = initial.clone();
    let mut current_cost =
        ordering_excess_cost(&current, statements_using, is_original_public, max_args);
    if current_cost == 0 {
        return current;
    }
    // Mix the full initial ordering into the seed so different starting
    // orderings explore independent swap sequences.
    let mut seed: u64 = 0x9E3779B97F4A7C15;
    for &v in &initial {
        seed = seed.wrapping_mul(0x100000001B3).wrapping_add(v as u64 + 1);
    }
    let mut rng = ChaCha20Rng::seed_from_u64(seed);
    for _ in 0..iters {
        let i = rng.gen_range(0..n);
        let j = rng.gen_range(0..n);
        if i == j {
            continue;
        }
        current.swap(i, j);
        let cand = ordering_excess_cost(&current, statements_using, is_original_public, max_args);
        // Accept equal-cost swaps too — sideways moves let us escape plateaus
        // toward a swap that finally reduces cost.
        if cand <= current_cost {
            current_cost = cand;
            if current_cost == 0 {
                break;
            }
        } else {
            current.swap(i, j);
        }
    }
    current
}

/// DP-based partitioner. Given an ordering of statements, decide where to
/// place K-1 boundaries using O(n²·K·W) dynamic programming. Returns the
/// per-link statement assignment in original-index order if a feasible
/// partition exists for this ordering at this K, else `None`.
///
/// Insight: once the ordering is fixed, the set of wildcards "live across"
/// any boundary position is a function of the ordering alone, so the only
/// remaining decision is where the boundaries go. This is exact for the
/// chosen ordering — the only heuristic is the ordering itself.
fn try_dp_at_k(
    ordering: &[usize],
    k: usize,
    statements_using: &[Vec<usize>],
    is_original_public: &[bool],
    params: &Params,
) -> Option<LinkAssignment> {
    let n = ordering.len();
    let max_arity = Params::max_custom_predicate_arity();
    let max_args = Params::max_statement_args();
    let max_wildcards = params.max_custom_predicate_wildcards;
    let num_wildcards = is_original_public.len();

    let WildcardLifetimes {
        wcs_at,
        prefix: prefix_wcs,
        suffix: suffix_wcs,
    } = wildcard_lifetimes(ordering, statements_using, num_wildcards);

    // Wildcards incoming as public args to a link starting at boundary `a`:
    //   - a = 0: full original-public-arg signature, including any unused
    //     originals — backward pruning never trims link 0.
    //   - a > 0: originals still used at some position ≥ a, plus private
    //     wildcards crossing a (used both < a and ≥ a).
    let incoming_at = |a: usize| -> HashSet<usize> {
        if a == 0 {
            return (0..num_wildcards)
                .filter(|&w| is_original_public[w])
                .collect();
        }
        suffix_wcs[a]
            .iter()
            .copied()
            .filter(|&w| is_original_public[w] || prefix_wcs[a].contains(&w))
            .collect()
    };

    // Incoming sets per boundary, with `None` for boundaries that are
    // already over `max_args` and so can never start a link.
    let incoming_set: Vec<Option<HashSet<usize>>> = (0..=n)
        .map(|a| {
            let inc = incoming_at(a);
            (inc.len() <= max_args).then_some(inc)
        })
        .collect();

    // dp[cur_k][p] = Some(prev_a) if [0..p) can be partitioned into exactly
    // cur_k links, with the cur_k'th link being chunk [prev_a..p). Iterating
    // `a` from largest to smallest gives partitions where earlier links fill
    // to the cap and the trailing link absorbs the slack — matches the
    // source-order shape tests expect.
    let mut dp: Vec<Vec<Option<usize>>> = vec![vec![None; n + 1]; k + 1];
    dp[0][0] = Some(0);

    for cur_k in 1..=k {
        let is_last = cur_k == k;
        let stmt_cap = if is_last { max_arity } else { max_arity - 1 };

        for p in 1..=n {
            let a_min = p.saturating_sub(stmt_cap);
            for a in (a_min..p).rev() {
                if dp[cur_k - 1][a].is_none() {
                    continue;
                }
                let Some(inc) = &incoming_set[a] else {
                    continue;
                };
                let mut total = inc.clone();
                for pos in a..p {
                    total.extend(&wcs_at[pos]);
                }
                if total.len() > max_wildcards {
                    continue;
                }
                dp[cur_k][p] = Some(a);
                break;
            }
        }
    }

    dp[k][n]?;

    let mut links: LinkAssignment = vec![Vec::new(); k];
    let mut cur_p = n;
    for cur_k in (1..=k).rev() {
        let a = dp[cur_k][cur_p].expect("dp reachability already verified");
        for pos in a..cur_p {
            links[cur_k - 1].push(ordering[pos]);
        }
        cur_p = a;
    }
    for link in &mut links {
        link.sort();
    }
    Some(links)
}

/// MILP outcome for a single K: `links[i]` is the list of original statement
/// indices placed in link i, in original order.
type LinkAssignment = Vec<Vec<usize>>;

/// MILP variables shared by the strict feasibility solve and the elastic
/// diagnostic solve.
///
/// All variables are binary. Constraints (C1..C7 below) make every variable
/// other than `assign` an exact function of the assignment, so the strict and
/// elastic models differ only in how they handle the per-link caps (C8/C9).
struct MilpVars {
    n: usize,
    k: usize,
    num_wildcards: usize,
    /// `assign[s][i]`: statement `s` placed in link `i`.
    assign: Vec<Vec<Variable>>,
    /// `u[w][i]`: wildcard `w` referenced by some statement at link `i`.
    u: Vec<Vec<Variable>>,
    /// `before[w][i]`: cumulative OR of `u[w][·]` from the left — w is used at link ≤ i.
    before: Vec<Vec<Variable>>,
    /// `after[w][i]`: cumulative OR of `u[w][·]` from the right — w is used at link ≥ i.
    after: Vec<Vec<Variable>>,
    /// `pubin[w][i]`: w appears in link i's `public_args_in`.
    pubin: Vec<Vec<Variable>>,
    /// `privin[w][i]`: w appears in link i's `private_args` list.
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

/// Source-order tiebreaker: prefers low-original-index statements at low-link
/// indices, so the chain roughly preserves source order when nothing else
/// forces a rearrangement.
///
/// Coefficient `(n - s)` is strictly positive for every statement, so every
/// pairwise swap of distinct `(s, i)` assignments changes the objective by a
/// non-zero amount. That makes the tiebreaker uniquely-optimising — the
/// solver can't pick between equivalent placements of any single statement.
fn source_order_tiebreaker(v: &MilpVars) -> Expression {
    (0..v.n)
        .flat_map(|s| (0..v.k).map(move |i| (s, i)))
        .map(|(s, i)| ((v.n - s) as f64) * (i as f64) * v.assign[s][i])
        .sum()
}

/// Build a SCIP model with the splitter's deterministic-build settings:
/// pinned random seed and silent output. When `accept_first_feasible` is
/// true, SCIP terminates as soon as it has an integer-feasible solution
/// rather than proving optimality — used by the strict MILP, where the
/// objective is just a tiebreaker. The elastic diagnostic LP needs proper
/// optimisation (minimum slack) so it must pass `false`.
fn build_scip_model(
    vars: ProblemVariables,
    objective: Expression,
    accept_first_feasible: bool,
) -> SCIPProblem {
    let mut model = vars
        .minimise(objective)
        .using(good_lp::solvers::scip::scip)
        .set_option("randomization/randomseedshift", SCIP_RANDOM_SEED)
        .set_verbose(false);
    if accept_first_feasible {
        // Huge gap → any integer-feasible incumbent satisfies the gap limit,
        // so SCIP exits with `GapLimit` after the first feasible solution.
        // ~10× faster than proving optimality on the dense, weakly-objective
        // models we hand SCIP, and the tiebreaker still steers the primal
        // heuristics toward source-ordered partitions.
        model = model
            .set_option("limits/gap", 1e20_f64)
            // Cuts tighten the LP bound, but with gap=∞ we don't need a
            // tight bound — only a feasible integer solution. Disabling
            // separation alone roughly halves solve time on the tested cases.
            .set_option("separating/maxrounds", 0_i32)
            .set_option("separating/maxroundsroot", 0_i32);
    }
    model
}

/// Add the MILP's structural constraints (C1..C7): assignment, link size,
/// `u`/`before`/`after`/`pubin`/`privin` definitions. Cap constraints (C8/C9)
/// are added by the caller — the strict and elastic versions differ there.
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

    // C4: before[w][i] = u[w][0] OR u[w][1] OR ... OR u[w][i].
    for w in 0..num_wildcards {
        model.add_constraint(constraint!(before[w][0] == u[w][0]));
        for i in 1..k {
            model.add_constraint(constraint!(before[w][i] >= before[w][i - 1]));
            model.add_constraint(constraint!(before[w][i] >= u[w][i]));
            model.add_constraint(constraint!(before[w][i] <= before[w][i - 1] + u[w][i]));
        }
    }

    // C5: after[w][i] = u[w][i] OR u[w][i+1] OR ... OR u[w][k-1].
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
            // Original public args: declared at link 0 (predicate signature)
            // and forwarded to link i iff used at some link ≥ i.
            model.add_constraint(constraint!(pubin[w][0] == 1));
            for i in 1..k {
                model.add_constraint(constraint!(pubin[w][i] == after[w][i]));
            }
        } else {
            // Private wildcards: pubin[w][i] = before[w][i-1] AND after[w][i]
            // (used somewhere strictly before AND somewhere at i or later).
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
            // privin[w][0] = u[w][0]: at link 0 there is no "before," so a
            // private wildcard used at link 0 is necessarily declared private.
            model.add_constraint(constraint!(privin[w][0] == u[w][0]));
            for i in 1..k {
                // privin[w][i] = u[w][i] AND NOT before[w][i-1]
                model.add_constraint(constraint!(privin[w][i] <= u[w][i]));
                model.add_constraint(constraint!(privin[w][i] <= 1 - before[w][i - 1]));
                model.add_constraint(constraint!(privin[w][i] >= u[w][i] - before[w][i - 1]));
            }
        }
    }
}

/// Try to partition `n` statements into exactly `k` links using MILP.
///
/// Returns `Some(assignment)` if a feasible partition exists, `None` if the
/// model is infeasible at this K (caller should try a larger K).
fn solve_milp_for_k(
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
    let mut model = build_scip_model(vars, objective, true);
    add_structural_constraints(&mut model, &v, statements_using, is_original_public);

    // C8: per-link public-args cap (incoming chain-call args).
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

    // Extract per-link statement lists in original-index order.
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

/// Convert an MILP link assignment into [`ChainLink`]s, computing each link's
/// public/private/promoted wildcards from the assignment plus the original
/// public-args list.
fn build_chain_links_from_assignment(
    links: LinkAssignment,
    statements: &[StatementTmpl],
    original_public_args: &[String],
) -> Vec<ChainLink> {
    let k = links.len();
    let stmt_wcs: Vec<HashSet<String>> = statements
        .iter()
        .map(collect_wildcards_from_statement)
        .collect();
    let link_wcs: Vec<HashSet<String>> = (0..k)
        .map(|i| {
            links[i]
                .iter()
                .flat_map(|&s| stmt_wcs[s].iter().cloned())
                .collect()
        })
        .collect();

    let mut result = Vec::with_capacity(k);
    let mut incoming: Vec<String> = original_public_args.to_vec();

    for i in 0..k {
        let stmts: Vec<StatementTmpl> = links[i].iter().map(|&s| statements[s].clone()).collect();

        // Wildcards crossing forward from link i (used here AND later).
        let after_wcs: HashSet<String> = (i + 1..k)
            .flat_map(|j| link_wcs[j].iter().cloned())
            .collect();
        let crossings: HashSet<String> = link_wcs[i].intersection(&after_wcs).cloned().collect();

        let incoming_set: HashSet<String> = incoming.iter().cloned().collect();

        let mut promotions: Vec<String> = crossings
            .iter()
            .filter(|w| !incoming_set.contains(*w))
            .cloned()
            .collect();
        promotions.sort();

        let mut private_args: Vec<String> = link_wcs[i]
            .difference(&incoming_set)
            .filter(|w| !crossings.contains(*w))
            .cloned()
            .collect();
        private_args.sort();

        result.push(ChainLink {
            statements: stmts,
            public_args_in: incoming.clone(),
            private_args,
            promoted_wildcards: promotions.clone(),
        });

        incoming.extend(promotions);
    }

    // Backward pruning: drop public args from continuations that no link
    // (this one or downstream) actually references. Link 0 keeps its full
    // user-declared signature.
    let num_links = result.len();
    if num_links > 1 {
        let last = num_links - 1;
        result[last]
            .public_args_in
            .retain(|a| link_wcs[last].contains(a));
        for i in (1..last).rev() {
            let needed_downstream: HashSet<String> =
                result[i + 1].public_args_in.iter().cloned().collect();
            result[i]
                .public_args_in
                .retain(|a| link_wcs[i].contains(a) || needed_downstream.contains(a));
        }
    }

    result
}

/// Numeric encoding of a predicate's wildcard graph, ready for either the
/// strict MILP or the elastic diagnostic LP.
struct MilpInput {
    n: usize,
    wildcard_names: Vec<String>,
    statements_using: Vec<Vec<usize>>,
    is_original_public: Vec<bool>,
    original_public_args: Vec<String>,
}

fn prepare_milp_input(pred: &CustomPredicateDef) -> MilpInput {
    let original_public_args: Vec<String> = pred
        .args
        .public_args
        .iter()
        .map(|id| id.name.clone())
        .collect();

    // Stable, sorted index over wildcards referenced by statements OR declared
    // as public args (a public arg may be unused in any statement).
    let mut wildcard_set: HashSet<String> = pred
        .statements
        .iter()
        .flat_map(collect_wildcards_from_statement)
        .collect();
    for name in &original_public_args {
        wildcard_set.insert(name.clone());
    }
    let mut wildcard_names: Vec<String> = wildcard_set.into_iter().collect();
    wildcard_names.sort();
    let wildcard_index: HashMap<String, usize> = wildcard_names
        .iter()
        .enumerate()
        .map(|(i, name)| (name.clone(), i))
        .collect();

    // Inverse: which statements reference each wildcard (by index).
    let mut statements_using: Vec<Vec<usize>> = vec![Vec::new(); wildcard_names.len()];
    for (s, stmt) in pred.statements.iter().enumerate() {
        let mut seen: HashSet<usize> = HashSet::new();
        for name in stmt.wildcard_names() {
            let w = wildcard_index[name];
            if seen.insert(w) {
                statements_using[w].push(s);
            }
        }
    }

    let mut is_original_public = vec![false; wildcard_names.len()];
    for name in &original_public_args {
        is_original_public[wildcard_index[name]] = true;
    }

    MilpInput {
        n: pred.statements.len(),
        wildcard_names,
        statements_using,
        is_original_public,
        original_public_args,
    }
}

/// Solve the elastic LP at the given K, returning per-link slack and
/// wildcard membership for the binding links. Slack variables on each cap
/// turn the otherwise-infeasible model into one that minimises constraint
/// violation, exposing exactly which links are over their caps and by how
/// much.
fn solve_elastic_lp(k: usize, input: &MilpInput, params: &Params) -> Option<Vec<LinkOvershoot>> {
    let max_args = Params::max_statement_args();
    let max_wildcards = params.max_custom_predicate_wildcards;
    let num_wildcards = input.wildcard_names.len();
    let n = input.n;

    let mut vars = ProblemVariables::new();
    let v = declare_milp_vars(&mut vars, n, k, num_wildcards);
    let slack_pub: Vec<Variable> = (0..k).map(|_| vars.add(variable().min(0.0))).collect();
    let slack_total: Vec<Variable> = (0..k).map(|_| vars.add(variable().min(0.0))).collect();

    let slack_term: Expression = (0..k)
        .map(|i| Expression::from(slack_pub[i]) + slack_total[i])
        .sum();
    // Tiebreaker bound is n²k². Scale so even the worst-case tiebreaker total
    // is < 1 — never enough to outweigh a single unit of slack.
    let scale = 1.0 / ((n * n * k * k + 1) as f64);
    let objective = slack_term + scale * source_order_tiebreaker(&v);

    let mut model = build_scip_model(vars, objective, false);
    add_structural_constraints(
        &mut model,
        &v,
        &input.statements_using,
        &input.is_original_public,
    );

    // C8 elastic: Σ pubin[w][i] ≤ max_args + slack_pub[i].
    for i in 0..k {
        let sum: Expression = (0..num_wildcards).map(|w| v.pubin[w][i]).sum();
        model.add_constraint(constraint!(sum <= max_args as f64 + slack_pub[i]));
    }

    // C9 elastic: Σ (pubin + privin)[w][i] ≤ max_wildcards + slack_total[i].
    for i in 0..k {
        let sum: Expression = (0..num_wildcards)
            .map(|w| Expression::from(v.pubin[w][i]) + v.privin[w][i])
            .sum();
        model.add_constraint(constraint!(sum <= max_wildcards as f64 + slack_total[i]));
    }

    let solution = model.solve().ok()?;

    let mut overshoots = Vec::new();
    for i in 0..k {
        let pub_overflow = solution.value(slack_pub[i]).round() as usize;
        let total_overflow = solution.value(slack_total[i]).round() as usize;
        if pub_overflow == 0 && total_overflow == 0 {
            continue;
        }
        let mut public_args_in = Vec::new();
        let mut private_args = Vec::new();
        for w in 0..num_wildcards {
            if solution.value(v.pubin[w][i]) > SOLVER_BINARY_THRESHOLD {
                public_args_in.push(input.wildcard_names[w].clone());
            }
            if solution.value(v.privin[w][i]) > SOLVER_BINARY_THRESHOLD {
                private_args.push(input.wildcard_names[w].clone());
            }
        }
        public_args_in.sort();
        private_args.sort();
        overshoots.push(LinkOvershoot {
            link_index: i,
            public_args_overflow: pub_overflow,
            total_args_overflow: total_overflow,
            public_args_in,
            private_args,
        });
    }
    Some(overshoots)
}

/// Diagnose why the splitter rejected `pred`. Runs an elastic version of the
/// MILP that allows the per-link caps to be violated by non-negative slack
/// and minimises total slack — the result tells you exactly which links
/// overshoot which caps and by how much.
///
/// Only meaningful to call on inputs that produced
/// [`SplittingError::Infeasible`]. On feasible inputs the report's
/// `overshoots` will be empty.
pub fn analyze_infeasibility(pred: &CustomPredicateDef, params: &Params) -> InfeasibilityReport {
    let input = prepare_milp_input(pred);
    let k = compute_min_links(input.n);
    let overshoots = solve_elastic_lp(k, &input, params).unwrap_or_default();
    InfeasibilityReport {
        predicate: pred.name.name.clone(),
        k,
        overshoots,
    }
}

/// Split a predicate into a chain via MILP. Tries `K = K_min, K_min+1, ...`,
/// returning the first feasible chain or [`SplittingError::Infeasible`] if
/// no `K` up to `n` works.
fn split_into_chain(
    pred: &CustomPredicateDef,
    params: &Params,
) -> Result<(Vec<CustomPredicateDef>, SplitChainInfo), SplittingError> {
    let original_name = pred.name.name.clone();
    let conjunction = pred.conjunction_type;
    let real_statement_count = pred.statements.len();

    let input = prepare_milp_input(pred);
    let n = input.n;

    let k_min = compute_min_links(n);
    let mut found: Option<(usize, LinkAssignment)> = None;

    let max_args = Params::max_statement_args();
    let mut orderings: Vec<Vec<usize>> = std::iter::once((0..n).collect())
        .chain(rcm_orderings(n, &input.statements_using))
        .collect();
    // One local-search pass on the lowest-cost initial ordering. Refining
    // every ordering would be wasted preprocessing — RCM produces dozens of
    // near-identical orderings on this problem class.
    if let Some(best) = orderings
        .iter()
        .min_by_key(|o| {
            ordering_excess_cost(
                o,
                &input.statements_using,
                &input.is_original_public,
                max_args,
            )
        })
        .cloned()
    {
        let refined = refine_ordering(
            best,
            &input.statements_using,
            &input.is_original_public,
            max_args,
            REFINE_ITERATIONS,
        );
        if !orderings.iter().any(|o| o == &refined) {
            orderings.insert(0, refined);
        }
    }
    // Try DP across the full K range starting from K_min: an extra link is
    // cheap, MILP at any K is not. If no ordering admits feasibility at any
    // K, fall back to MILP.
    'dp_search: for k in k_min..=n {
        for ordering in &orderings {
            if let Some(assignment) = try_dp_at_k(
                ordering,
                k,
                &input.statements_using,
                &input.is_original_public,
                params,
            ) {
                found = Some((k, assignment));
                break 'dp_search;
            }
        }
    }

    if found.is_none() {
        for k in k_min..=n {
            if let Some(assignment) = solve_milp_for_k(
                n,
                k,
                &input.statements_using,
                &input.is_original_public,
                params,
            ) {
                found = Some((k, assignment));
                break;
            }
        }
    }

    let (_k, assignment) = found.ok_or_else(|| SplittingError::Infeasible {
        predicate: original_name.clone(),
        max_links: n,
        max_statement_args: Params::max_statement_args(),
        max_wildcards: params.max_custom_predicate_wildcards,
    })?;

    // Reorder map: original index → position in flattened chain.
    let mut reorder_map = vec![0usize; n];
    {
        let mut flat = 0usize;
        for link in &assignment {
            for &s in link {
                reorder_map[s] = flat;
                flat += 1;
            }
        }
    }

    let chain_links = build_chain_links_from_assignment(
        assignment,
        &pred.statements,
        &input.original_public_args,
    );

    // Build SplitChainInfo (execution order: innermost continuation first).
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
    chain_predicates.reverse();

    Ok((chain_predicates, chain_info))
}

/// Build the chain's [`CustomPredicateDef`]s from the per-link metadata,
/// inserting a chain call on every non-last link.
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

        if !is_last {
            let next_pred_name = Identifier {
                name: format!("{}_{}", original_name, i + 1),
                span: None,
            };

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

        // Build public args (incoming).
        let public_args: Vec<TypedArg> = link
            .public_args_in
            .iter()
            .map(|name| TypedArg {
                name: name.clone(),
                type_name: None,
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
                    .map(|name| TypedArg {
                        name,
                        type_name: None,
                        span: None,
                    })
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

        let result = split_predicate_if_needed(&pred, &params);
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

        let result = split_predicate_if_needed(&pred, &params);
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

        let result = split_predicate_if_needed(&pred, &params);
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

        let result = split_predicate_if_needed(&pred, &params);
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

        let result = split_predicate_if_needed(&pred, &params);
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

    // --- Regression tests ---

    /// Statements that reference only public args should be deferred until private-wildcard
    /// statements have been clustered, so they don't consume bucket slots that would reduce
    /// liveness at split boundaries.
    ///
    /// 4 public args, 7 statements: W1 used in stmts 0,1,4; W2 used in stmts 1,2,3;
    /// stmts 5,6 reference only public args.  The scoring correctly defers stmts 5,6,
    /// yielding bucket0={0,1,2,3}, bucket1={4,5,6} with only W1 crossing (4+1=5 <= max).
    #[test]
    fn test_split_succeeds_with_four_public_args_and_public_only_statements() {
        // Optimal split: bucket0={0,1,2,3}, bucket1={4,5,6}
        // Only W1 crosses (used in 0,1 and 4), total = 4 public + 1 crossing = 5 ✓
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

        let result = split_predicate_if_needed(&pred, &params);
        assert!(
            result.is_ok(),
            "Should find a valid split with ≤1 crossing wildcard, got: {:?}",
            result.err()
        );
    }

    /// Continuation predicates should only declare the public args they actually use -
    /// original public args that are not referenced in a continuation's statements or
    /// any of its downstream continuations must be omitted from its signature.
    #[test]
    fn test_continuation_excludes_public_args_unused_after_split() {
        // A is used only in the first segment; B is used only in the second segment.
        // The continuation predicate (pred_1) must include B but not A.
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

        let result = split_predicate_if_needed(&pred, &params).unwrap();
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

    // ===================================================================
    // Completeness probe for the splitter.
    //
    // `build_pred` constructs a CustomPredicateDef from a "wildcard set per
    // statement" specification (cheaper than parsing). `find_any_feasible_ordering`
    // brute-forces all permutations and uses the same per-link constraints as
    // `split_into_chain` to check whether a feasible chain exists at all.
    // ===================================================================

    fn build_pred(
        name: &str,
        public_args: &[&str],
        private_args: &[&str],
        stmt_wildcards: &[&[&str]],
    ) -> CustomPredicateDef {
        let statements: Vec<StatementTmpl> = stmt_wildcards
            .iter()
            .map(|wcs| {
                let args: Vec<StatementTmplArg> = wcs
                    .iter()
                    .map(|n| {
                        StatementTmplArg::Wildcard(Identifier {
                            name: n.to_string(),
                            span: None,
                        })
                    })
                    .collect();
                StatementTmpl {
                    predicate: PredicateRef::Local(Identifier {
                        name: "Equal".to_string(),
                        span: None,
                    }),
                    args,
                    span: None,
                }
            })
            .collect();

        let private_args = if private_args.is_empty() {
            None
        } else {
            Some(
                private_args
                    .iter()
                    .map(|n| TypedArg {
                        name: n.to_string(),
                        type_name: None,
                        span: None,
                    })
                    .collect(),
            )
        };

        CustomPredicateDef {
            name: Identifier {
                name: name.to_string(),
                span: None,
            },
            args: ArgSection {
                public_args: public_args
                    .iter()
                    .map(|n| TypedArg {
                        name: n.to_string(),
                        type_name: None,
                        span: None,
                    })
                    .collect(),
                private_args,
                span: None,
            },
            conjunction_type: ConjunctionType::And,
            statements,
            span: None,
        }
    }

    /// Replicates the bucket-fill constraint check from `split_into_chain` for
    /// a *fixed* ordering of statements. Returns Ok if the ordering produces a
    /// valid chain, Err otherwise.
    fn check_ordering_feasible(
        ordered: &[StatementTmpl],
        original_public_args: &[String],
        params: &Params,
    ) -> bool {
        if ordered.len() <= Params::max_custom_predicate_arity() {
            return true;
        }

        let mut pos = 0;
        let mut incoming_public: Vec<String> = original_public_args.to_vec();

        while pos < ordered.len() {
            let remaining = ordered.len() - pos;
            let is_last = remaining <= Params::max_custom_predicate_arity();
            let bucket_size = if is_last {
                remaining
            } else {
                Params::max_custom_predicate_arity() - 1
            };
            let end = pos + bucket_size;

            let live: HashSet<String> = if is_last {
                HashSet::new()
            } else {
                let before: HashSet<String> = ordered[pos..end]
                    .iter()
                    .flat_map(collect_wildcards_from_statement)
                    .collect();
                let after: HashSet<String> = ordered[end..]
                    .iter()
                    .flat_map(collect_wildcards_from_statement)
                    .collect();
                before.intersection(&after).cloned().collect()
            };

            let incoming_set: HashSet<String> = incoming_public.iter().cloned().collect();
            let new_promotions: Vec<String> = live
                .iter()
                .filter(|w| !incoming_set.contains(*w))
                .cloned()
                .collect();
            let total_public = incoming_public.len() + new_promotions.len();
            if total_public > Params::max_statement_args() {
                return false;
            }

            let segment_wildcards: HashSet<String> = ordered[pos..end]
                .iter()
                .flat_map(collect_wildcards_from_statement)
                .collect();
            let private_args: Vec<String> = segment_wildcards
                .difference(&incoming_set)
                .filter(|w| !live.contains(*w))
                .cloned()
                .collect();
            let total_args = total_public + private_args.len();
            if total_args > params.max_custom_predicate_wildcards {
                return false;
            }

            pos = end;
            incoming_public.extend(new_promotions);
        }

        true
    }

    /// Brute-force search over all permutations of the predicate's statements
    /// for *any* ordering that produces a feasible split. Returns the
    /// permutation if found, else None. Caps at 9! to keep tests cheap.
    fn find_any_feasible_ordering(
        pred: &CustomPredicateDef,
        params: &Params,
    ) -> Option<Vec<usize>> {
        use itertools::Itertools;

        let n = pred.statements.len();
        assert!(n <= 9, "brute-force capped at 9! permutations");

        let original_public_args: Vec<String> = pred
            .args
            .public_args
            .iter()
            .map(|id| id.name.clone())
            .collect();

        for perm in (0..n).permutations(n) {
            let ordered: Vec<StatementTmpl> =
                perm.iter().map(|&i| pred.statements[i].clone()).collect();
            if check_ordering_feasible(&ordered, &original_public_args, params) {
                return Some(perm);
            }
        }
        None
    }

    /// 6 statements with 2 public args (A0, A1) and 5 private wildcards
    /// (T0..T4). A feasible 4+2 chain exists where exactly 3 wildcards cross
    /// the boundary (3 promotions + 2 incoming = 5 total public, hitting the
    /// cap). The splitter must find one — a partition that puts an extra
    /// wildcard across the boundary fails the per-link public-arg cap.
    ///
    /// Found by random search with seed 0xC0FFEE; inlined for determinism.
    #[test]
    fn test_splitter_handles_tight_public_arg_cap() {
        let pred = build_pred(
            "p",
            &["A0", "A1"],
            &["T0", "T1", "T2", "T3", "T4"],
            &[
                &["T0", "T4", "T2"],
                &["T1", "T3", "T4"],
                &["T2", "T3", "T1"],
                &["T4", "A0", "A1"],
                &["T3", "T0", "T2"],
                &["T0", "A1", "T1"],
            ],
        );
        let params = Params::default();

        // Sanity: brute force confirms a feasible ordering exists.
        let feasible = find_any_feasible_ordering(&pred, &params);
        assert!(
            feasible.is_some(),
            "expected at least one feasible permutation"
        );

        let result = split_predicate_if_needed(&pred, &params);
        assert!(
            result.is_ok(),
            "splitter rejected an input with a feasible ordering ({:?}): {}",
            feasible.unwrap(),
            result.err().unwrap()
        );
    }

    /// A predicate with one statement that references 9 distinct wildcards
    /// is unsplittable: any link containing that statement declares ≥ 9
    /// wildcards, exceeding the per-link cap of 8. `analyze_infeasibility`
    /// must surface this as a non-zero `total_args_overflow` and list the
    /// crowded link's private args.
    #[test]
    fn test_analyze_infeasibility_reports_total_args_overflow() {
        let pred = build_pred(
            "dense",
            &["A"],
            &["W0", "W1", "W2", "W3", "W4", "W5", "W6", "W7", "W8"],
            &[
                &["W0", "W1", "W2", "W3", "W4", "W5", "W6", "W7", "W8"],
                &["W0"],
                &["W0"],
                &["W0"],
                &["W0"],
                &["W0"],
            ],
        );
        let params = Params::default();

        // Sanity: regular splitter rejects this input.
        assert!(matches!(
            split_predicate_if_needed(&pred, &params),
            Err(SplittingError::Infeasible { .. })
        ));

        let report = analyze_infeasibility(&pred, &params);
        assert_eq!(report.predicate, "dense");
        assert_eq!(report.k, 2);

        let total_overflow: usize = report
            .overshoots
            .iter()
            .map(|o| o.total_args_overflow)
            .sum();
        assert!(
            total_overflow >= 1,
            "expected ≥1 total-args overflow, got {} (overshoots: {:?})",
            total_overflow,
            report.overshoots
        );

        // The dense statement forces W1..W8 into one link as private args.
        let crowded_link_has_dense_privates = report
            .overshoots
            .iter()
            .any(|o| o.private_args.iter().filter(|w| w.starts_with('W')).count() >= 8);
        assert!(
            crowded_link_has_dense_privates,
            "expected a binding link to declare 8+ W-wildcards as private; got {:?}",
            report.overshoots
        );

        // Display impl shouldn't panic and should mention the predicate name.
        let formatted = format!("{}", report);
        assert!(formatted.contains("dense"));
    }

    /// 30-statement predicate with a 7-link wildcard chain (`chain0..chain6,
    /// chain`) — modelled on `CraftRefinery` from the zk-craft episode-1
    /// plugin. K_min = 8 with `max_custom_predicate_arity = 5`, and the
    /// chain transitions force at most one promoted wildcard per boundary.
    /// Used to measure splitter latency on real-world-shaped inputs.
    ///
    /// Run with `cargo test --release test_split_craft_refinery_shape -- --nocapture`.
    #[test]
    fn test_split_craft_refinery_shape() {
        let pred = build_pred(
            "CraftRefinery",
            &["in", "out", "chain0", "chain"],
            &[
                "chain1", "chain2", "chain3", "chain4", "chain5", "chain6", "oil", "water",
                "tar_a0", "tar_a1", "tar_a", "tar_b", "tar_c", "fuel", "gas", "key", "work",
            ],
            &[
                &["in", "oil"],                 // 0:  ArrayContains(in, _, oil)
                &["in", "water"],               // 1:  ArrayContains(in, _, water)
                &["out", "tar_a"],              // 2:  ArrayContains(out, _, tar_a)
                &["out", "tar_b"],              // 3:  ArrayContains(out, _, tar_b)
                &["out", "tar_c"],              // 4:  ArrayContains(out, _, tar_c)
                &["out", "fuel"],               // 5:  ArrayContains(out, _, fuel)
                &["out", "gas"],                // 6:  ArrayContains(out, _, gas)
                &["tar_a0"],                    // 7:  DictContains(tar_a0, ...)
                &["tar_b"],                     // 8:  DictContains(tar_b, ...)
                &["tar_c"],                     // 9:  DictContains(tar_c, ...)
                &["fuel"],                      // 10: DictContains(fuel, ...)
                &["gas"],                       // 11: DictContains(gas, ...)
                &["tar_a1", "tar_a0", "key"],   // 12: DictUpdate(tar_a1, tar_a0, _, key)
                &["tar_a1"],                    // 13: LtEqU256(tar_a1, _)
                &["tar_a1", "work"],            // 14: Vdf(_, tar_a1, work)
                &["tar_a", "tar_a1", "work"],   // 15: DictUpdate(tar_a, tar_a1, _, work)
                &["oil"],                       // 16: DictContains(oil, ...)
                &["chain1", "chain0", "oil"],   // 17: TxDelete(chain1, chain0, oil)
                &["water"],                     // 18: DictContains(water, ...)
                &["chain2", "chain1", "water"], // 19: TxDelete(chain2, chain1, water)
                &["tar_a"],                     // 20: DictContains(tar_a, ...)
                &["chain3", "chain2", "tar_a"], // 21: TxInsert(chain3, chain2, tar_a)
                &["tar_b"],                     // 22: DictContains(tar_b, ...)
                &["chain4", "chain3", "tar_b"], // 23: TxInsert(chain4, chain3, tar_b)
                &["tar_c"],                     // 24: DictContains(tar_c, ...)
                &["chain5", "chain4", "tar_c"], // 25: TxInsert(chain5, chain4, tar_c)
                &["fuel"],                      // 26: DictContains(fuel, ...)
                &["chain6", "chain5", "fuel"],  // 27: TxInsert(chain6, chain5, fuel)
                &["gas"],                       // 28: DictContains(gas, ...)
                &["chain", "chain6", "gas"],    // 29: TxInsert(chain, chain6, gas)
            ],
        );
        let params = Params::default();

        let start = std::time::Instant::now();
        let result = split_predicate_if_needed(&pred, &params);
        let elapsed = start.elapsed();

        eprintln!("CraftRefinery split took {:?}", elapsed);
        assert!(result.is_ok(), "split failed: {:?}", result.err());
        let split = result.unwrap();
        assert!(split.chain_info.is_some(), "expected a chain split");
        let info = split.chain_info.unwrap();
        eprintln!(
            "  chain has {} pieces, real_statement_count = {}",
            info.chain_pieces.len(),
            info.real_statement_count
        );
    }

    /// 51-statement predicate with a 13-link wildcard chain — modelled on
    /// `CraftRefineryCracked` from the zk-craft episode-1 plugin. K_min = 13
    /// with `max_custom_predicate_arity = 5`. This is the failure case the
    /// CraftRefinery test was a smaller instance of.
    ///
    /// Run with `cargo test --release test_split_craft_refinery_cracked_shape -- --nocapture --ignored`.
    #[test]
    #[ignore]
    fn test_split_craft_refinery_cracked_shape() {
        let pred = build_pred(
            "CraftRefineryCracked",
            &["in", "out", "chain0", "chain"],
            &[
                "chain1",
                "chain2",
                "chain3",
                "chain4",
                "chain5",
                "chain6",
                "chain7",
                "chain8",
                "chain9",
                "chain10",
                "chain11",
                "chain12",
                "oil",
                "water",
                "tar_a0",
                "tar_a1",
                "tar_a",
                "tar_b",
                "tar_c",
                "tar_d",
                "tar_e",
                "fuel_a",
                "fuel_b",
                "fuel_c",
                "gas_a",
                "gas_b",
                "key",
                "work",
                "_TouchCrackingUnit_in_0",
                "_TouchCrackingUnit_out_0",
            ],
            &[
                &["in", "oil"],     // 0
                &["in", "water"],   // 1
                &["out", "tar_a"],  // 2
                &["out", "tar_b"],  // 3
                &["out", "tar_c"],  // 4
                &["out", "tar_d"],  // 5
                &["out", "tar_e"],  // 6
                &["out", "fuel_a"], // 7
                &["out", "fuel_b"], // 8
                &["out", "fuel_c"], // 9
                &["out", "gas_a"],  // 10
                &["out", "gas_b"],  // 11
                &[
                    "_TouchCrackingUnit_in_0",
                    "_TouchCrackingUnit_out_0",
                    "chain0",
                    "chain1",
                ], // 12: TouchCrackingUnit
                &["tar_a0"],        // 13
                &["tar_b"],         // 14
                &["tar_c"],         // 15
                &["tar_d"],         // 16
                &["tar_e"],         // 17
                &["fuel_a"],        // 18
                &["fuel_b"],        // 19
                &["fuel_c"],        // 20
                &["gas_a"],         // 21
                &["gas_b"],         // 22
                &["tar_a1", "tar_a0", "key"], // 23
                &["tar_a1"],        // 24
                &["tar_a1", "work"], // 25
                &["tar_a", "tar_a1", "work"], // 26
                &["oil"],           // 27
                &["chain2", "chain1", "oil"], // 28
                &["water"],         // 29
                &["chain3", "chain2", "water"], // 30
                &["tar_a"],         // 31
                &["chain4", "chain3", "tar_a"], // 32
                &["tar_b"],         // 33
                &["chain5", "chain4", "tar_b"], // 34
                &["tar_c"],         // 35
                &["chain6", "chain5", "tar_c"], // 36
                &["tar_d"],         // 37
                &["chain7", "chain6", "tar_d"], // 38
                &["tar_e"],         // 39
                &["chain8", "chain7", "tar_e"], // 40
                &["fuel_a"],        // 41
                &["chain9", "chain8", "fuel_a"], // 42
                &["fuel_b"],        // 43
                &["chain10", "chain9", "fuel_b"], // 44
                &["fuel_c"],        // 45
                &["chain11", "chain10", "fuel_c"], // 46
                &["gas_a"],         // 47
                &["chain12", "chain11", "gas_a"], // 48
                &["gas_b"],         // 49
                &["chain", "chain12", "gas_b"], // 50
            ],
        );
        let params = Params::default();

        let start = std::time::Instant::now();
        let result = split_predicate_if_needed(&pred, &params);
        let elapsed = start.elapsed();

        eprintln!("CraftRefineryCracked split took {:?}", elapsed);
        match &result {
            Ok(s) => eprintln!(
                "  chain has {} pieces",
                s.chain_info.as_ref().map_or(0, |c| c.chain_pieces.len())
            ),
            Err(e) => eprintln!("  split failed: {}", e),
        }
        assert!(result.is_ok(), "split failed: {:?}", result.err());
    }

    /// Randomized counterexample search. Run with
    /// `cargo test --release search_splitter -- --ignored --nocapture`.
    #[test]
    #[ignore]
    fn search_splitter_counterexample() {
        // Tiny LCG so we don't pull rand as a dep.
        struct Lcg(u64);
        impl Lcg {
            fn next(&mut self) -> u64 {
                self.0 = self
                    .0
                    .wrapping_mul(6364136223846793005)
                    .wrapping_add(1442695040888963407);
                self.0
            }
            fn rand_in(&mut self, n: usize) -> usize {
                (self.next() as usize) % n
            }
        }

        let params = Params::default();
        let mut rng = Lcg(0xC0FFEE);
        let mut checked = 0;
        let mut found = 0;

        // Sweep over (n_stmts, n_pub, n_priv) combos.
        for &n_stmts in &[6usize, 7, 8, 9] {
            for &n_pub in &[1usize, 2, 3, 4] {
                for &n_priv in &[2usize, 3, 4, 5] {
                    let pub_names: Vec<String> = (0..n_pub).map(|i| format!("A{}", i)).collect();
                    let priv_names: Vec<String> = (0..n_priv).map(|i| format!("T{}", i)).collect();
                    let all_names: Vec<String> =
                        pub_names.iter().chain(priv_names.iter()).cloned().collect();

                    // Generate 200 random predicates per shape.
                    for trial in 0..200 {
                        // Each statement gets 2-3 distinct wildcards drawn from all_names.
                        let stmt_wildcards: Vec<Vec<String>> = (0..n_stmts)
                            .map(|_| {
                                let arity = 2 + rng.rand_in(2); // 2 or 3
                                let mut chosen = Vec::new();
                                let mut tries = 0;
                                while chosen.len() < arity && tries < 20 {
                                    let pick = all_names[rng.rand_in(all_names.len())].clone();
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

                        // Skip inputs that fail early validation (e.g. too many public args).
                        if validate_predicate_is_splittable(&pred).is_err() {
                            continue;
                        }

                        checked += 1;
                        let feasible = find_any_feasible_ordering(&pred, &params);
                        let split = split_predicate_if_needed(&pred, &params);

                        if let (Err(err), Some(perm)) = (split, feasible) {
                            found += 1;
                            eprintln!(
                                "\n=== COUNTEREXAMPLE #{} ===\n\
                                 shape: n={}, n_pub={}, n_priv={}, trial={}\n\
                                 statements (original order):",
                                found, n_stmts, n_pub, n_priv, trial
                            );
                            for (i, wcs) in stmt_wildcards.iter().enumerate() {
                                eprintln!("  s{}: {:?}", i, wcs);
                            }
                            eprintln!("feasible permutation: {:?}", perm);
                            eprintln!("splitter error: {}\n", err);

                            if found >= 3 {
                                eprintln!(
                                    "Found {} counterexamples (out of {} checked); stopping.",
                                    found, checked
                                );
                                return;
                            }
                        }
                    }
                }
            }
        }

        eprintln!(
            "Searched {} predicates; found {} counterexamples.",
            checked, found
        );
        if found == 0 {
            eprintln!("No counterexamples found.");
        }
    }
}
