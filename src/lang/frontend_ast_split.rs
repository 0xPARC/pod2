//! Predicate splitting for frontend AST
//!
//! Predicates whose statement count exceeds the middleware's
//! `max_custom_predicate_arity` are split into a chain of smaller predicates,
//! each calling the next via a tail-position chain call. Private wildcards
//! that span a split boundary are promoted to public arguments on the
//! continuation, since they need the same binding on both sides.
//!
//! Each link in the resulting chain satisfies three caps: statement count
//! (`max_custom_predicate_arity`, minus a slot for the chain call on non-last
//! links), public-args-in (`max_statement_args`), and total declared wildcards
//! (`max_custom_predicate_wildcards`). When no partition fits, the splitter
//! returns a [`SplittingError`] pointing at the first cap that overflows, with
//! an actionable [`RefactorSuggestion`] when one applies.
//!
//! Splits are deterministic: the same predicate always produces the same chain
//! across clients and platforms.

#![allow(clippy::needless_range_loop)]

use std::collections::{HashMap, HashSet, VecDeque};

pub use crate::lang::error::SplittingError;
use crate::{
    lang::{
        error::{RefactorSuggestion, SplitContext},
        frontend_ast::*,
    },
    middleware::Params,
};

/// A link in the predicate chain
#[derive(Debug, Clone)]
struct ChainLink {
    /// Statements in this link
    statements: Vec<StatementTmpl>,
    /// Public arguments coming into this link
    public_args_in: Vec<String>,
    /// Private arguments used only in this link
    private_args: Vec<String>,
    /// Private wildcards promoted to public for the next link (empty if last link)
    promoted_wildcards: Vec<String>,
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
    /// Maps original statement index to reordered index
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
pub(super) fn validate_predicate_is_splittable(
    pred: &CustomPredicateDef,
) -> Result<(), SplittingError> {
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
    let (predicates, chain_info) = split_into_chain(&pred, params)?;

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
pub(super) fn compute_min_links(n: usize) -> usize {
    let max_arity = Params::max_custom_predicate_arity();
    if n <= max_arity {
        1
    } else {
        // Smallest K such that (K-1) * (max_arity-1) + max_arity >= n
        (n - max_arity).div_ceil(max_arity - 1) + 1
    }
}

// Ordering heuristic. At each candidate split boundary, every wildcard alive
// across it (first_use < boundary <= last_use) must be promoted to a public
// arg on the continuation, and the public-args cap is the binding constraint
// on splittability. That count is exactly the bandwidth of the statement-
// wildcard incidence matrix at the boundary column, and Reverse Cuthill-
// McKee on the statement-adjacency graph (built here) is the standard cheap
// heuristic for keeping bandwidth low across all columns at once. RCM is
// itself a heuristic with no optimality guarantee, so the splitter refines
// the lowest-cost RCM seeds via local search before handing orderings to
// the DP partitioner.

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

/// Reverse Cuthill-McKee from a chosen start node. Visits in BFS order,
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
                visited[m] = true;
                queue.push_back(m);
            }
        }
        if result.len() == n {
            break;
        }
        // The statement-adjacency graph can have multiple components: any
        // predicate whose statements split into groups that share no
        // wildcards (e.g. independent claims about disjoint inputs) produces
        // one. Restart BFS at the lowest-degree unvisited node so the visit
        // covers every statement.
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
/// `wcs_at` over `0..p` and `p..n` respectively.
struct WildcardLifetimes {
    wcs_at: Vec<HashSet<usize>>,
    prefix: Vec<HashSet<usize>>,
    suffix: Vec<HashSet<usize>>,
}

/// Compute [`WildcardLifetimes`] for a given ordering.
fn wildcard_lifetimes(
    ordering: &[usize],
    statements_using: &[Vec<usize>],
    num_wildcards: usize,
) -> WildcardLifetimes {
    let n = ordering.len();
    let mut pos_of = vec![usize::MAX; n];
    for (p, &s) in ordering.iter().enumerate() {
        pos_of[s] = p;
    }
    let mut wcs_at: Vec<HashSet<usize>> = vec![HashSet::new(); n];
    for (w, stmts) in statements_using.iter().enumerate().take(num_wildcards) {
        for &s in stmts {
            wcs_at[pos_of[s]].insert(w);
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
/// better for the DP partitioner: when this drops to 0, every position
/// satisfies the per-link public-args cap. The total-wildcards cap is
/// checked separately by the DP.
fn ordering_excess_cost(
    ordering: &[usize],
    statements_using: &[Vec<usize>],
    is_original_public: &[bool],
    max_args: usize,
) -> usize {
    let n = ordering.len();
    let num_wildcards = is_original_public.len();

    let mut pos_of = vec![usize::MAX; n];
    for (p, &s) in ordering.iter().enumerate() {
        pos_of[s] = p;
    }

    // Represent each wildcard by just the first and last position at which it
    // appears in the ordering.
    let mut first = vec![usize::MAX; num_wildcards];
    let mut last = vec![0usize; num_wildcards];
    for (w, stmts) in statements_using.iter().enumerate().take(num_wildcards) {
        for &s in stmts {
            let p = pos_of[s];
            if p < first[w] {
                first[w] = p;
            }
            if p > last[w] {
                last[w] = p;
            }
        }
    }

    let mut total: usize = 0;
    for p in 1..n {
        let mut bw: usize = 0;
        for w in 0..num_wildcards {
            if first[w] == usize::MAX {
                continue;
            }
            // Public args are alive from position 0 (declared on the predicate
            // signature regardless of where they're first referenced), so they
            // cross p iff they're used at or after p. Private wildcards only
            // count once they've actually appeared.
            if is_original_public[w] {
                if last[w] >= p {
                    bw += 1;
                }
            } else if first[w] < p && last[w] >= p {
                bw += 1;
            }
        }
        total += bw.saturating_sub(max_args);
    }
    total
}

/// Swap attempts per local-search seed. Iterations are cheap per step, so
/// thousands of iterations comfortably fits in the per-predicate budget.
const REFINE_ITERATIONS: usize = 5_000;

/// Number of low-cost RCM orderings handed to local search.
const REFINE_STARTS: usize = 5;

/// Number of random-shuffle starts refined alongside the RCM seeds.
const REFINE_RANDOM_STARTS: usize = 8;

/// Deterministic seed derived from an ordering. Used to seed the shuffle RNG
/// in `split_into_chain` so the random-start orderings depend only on the
/// predicate, not on test/run order.
/// Rust's `DefaultHasher` does not guarantee a stable algorithm across
/// releases, so we pick our own constants.
fn seed_from_ordering(ordering: &[usize]) -> u64 {
    // 0x9E3779B97F4A7C15 is the 64-bit golden-ratio constant; 0x100000001B3 is
    // the 64-bit FNV prime. Used here as an arbitrary mixing function - we
    // only need determinism, not cryptographic quality.
    let mut seed: u64 = 0x9E3779B97F4A7C15;
    for &v in ordering {
        seed = seed.wrapping_mul(0x100000001B3).wrapping_add(v as u64 + 1);
    }
    seed
}

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
    // Seed from the initial ordering so different starting orderings explore
    // independent swap sequences.
    let mut rng = ChaCha20Rng::seed_from_u64(seed_from_ordering(&initial));
    for _ in 0..iters {
        let i = rng.gen_range(0..n);
        let j = rng.gen_range(0..n);
        if i == j {
            continue;
        }
        current.swap(i, j);
        let cand = ordering_excess_cost(&current, statements_using, is_original_public, max_args);
        // Accept equal-cost swaps too: sideways moves let us escape plateaus
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

/// Splitting a predicate is two problems: pick a statement order, then pick
/// where to cut it. Picking the order is the hard part: that's the job of
/// the heuristics upstream (RCM, refinement, random shuffles). Picking the
/// cuts, given a fixed order, is easy: a left-to-right prefix DP finds a
/// min-K partition if one exists. So if the splitter ever fails, it's
/// because no ordering it tried worked, not because the cutting step gave up.
fn try_partition(
    ordering: &[usize],
    statements_using: &[Vec<usize>],
    is_original_public: &[bool],
    params: &Params,
) -> Option<(usize, LinkAssignment)> {
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
    //     originals: backward pruning never trims link 0.
    //   - a > 0: originals still used at some position >= a, plus private
    //     wildcards crossing a (used both < a and >= a).
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

    // True iff the segment `[a..p]` admits a link with `incoming_set[a]`
    // as its incoming-public-args under the total-wildcards cap. The
    // statement-count cap is the caller's job (via the `a` lower bound).
    let segment_ok = |a: usize, p: usize| -> bool {
        let Some(inc) = &incoming_set[a] else {
            return false;
        };
        let mut total = inc.clone();
        for pos in a..p {
            total.extend(&wcs_at[pos]);
        }
        total.len() <= max_wildcards
    };

    // Main prefix DP over non-terminal links (cap max_arity - 1).
    let non_last_cap = max_arity - 1;
    let mut dp: Vec<Option<(usize, usize)>> = vec![None; n + 1];
    dp[0] = Some((0, 0));
    for p in 1..=n {
        let a_lo = p.saturating_sub(non_last_cap);
        // Largest a first: source order wins ties.
        for a in (a_lo..p).rev() {
            let Some((prev_k, _)) = dp[a] else {
                continue;
            };
            if !segment_ok(a, p) {
                continue;
            }
            let new_k = prev_k + 1;
            if dp[p].is_none_or(|(cur_k, _)| new_k < cur_k) {
                dp[p] = Some((new_k, a));
            }
        }
    }

    // Terminal scan: find the largest `a` such that `[a..n]` is feasible
    // as the last link (cap max_arity) and `dp[a]` is reachable; that gives
    // the smallest overall K because later prefixes have larger or equal
    // min_k.
    let a_lo = n.saturating_sub(max_arity);
    let mut best: Option<(usize, usize)> = None; // (total_k, end_start)
    for a in (a_lo..n).rev() {
        let Some((prev_k, _)) = dp[a] else {
            continue;
        };
        if !segment_ok(a, n) {
            continue;
        }
        let total_k = prev_k + 1;
        if best.is_none_or(|(cur_k, _)| total_k < cur_k) {
            best = Some((total_k, a));
        }
    }
    let (k, end_start) = best?;

    // Reconstruct: last link first, then walk dp's prev_a chain.
    let mut links: LinkAssignment = vec![Vec::new(); k];
    for pos in end_start..n {
        links[k - 1].push(ordering[pos]);
    }
    let mut cur_p = end_start;
    for i in (0..k - 1).rev() {
        let (_, prev_a) = dp[cur_p].expect("dp reachability already verified");
        for pos in prev_a..cur_p {
            links[i].push(ordering[pos]);
        }
        cur_p = prev_a;
    }
    for link in &mut links {
        link.sort();
    }
    Some((k, links))
}

/// Per-link statement assignment: `links[i]` is the list of original statement
/// indices placed in link i, in original order.
pub(super) type LinkAssignment = Vec<Vec<usize>>;

/// Convert a link assignment into [`ChainLink`]s, computing each link's
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

/// Numeric encoding of a predicate's wildcard graph, ready for the DP
/// partitioner.
pub(super) struct SplitInput {
    pub(super) n: usize,
    wildcard_names: Vec<String>,
    pub(super) statements_using: Vec<Vec<usize>>,
    pub(super) is_original_public: Vec<bool>,
    original_public_args: Vec<String>,
}

pub(super) fn prepare_split_input(pred: &CustomPredicateDef) -> SplitInput {
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

    SplitInput {
        n: pred.statements.len(),
        wildcard_names,
        statements_using,
        is_original_public,
        original_public_args,
    }
}

/// Build the priority-ordered list of orderings the DP partitioner will try.
/// Source order plus RCM orderings form the baseline; refined versions of the
/// lowest-cost RCM seeds and a few random shuffles are prepended so the DP
/// probes the lowest-bandwidth candidates first.
fn candidate_orderings(input: &SplitInput) -> Vec<Vec<usize>> {
    use rand::{seq::SliceRandom, SeedableRng};
    use rand_chacha::ChaCha20Rng;

    let n = input.n;
    let max_args = Params::max_statement_args();

    let mut orderings: Vec<Vec<usize>> = std::iter::once((0..n).collect())
        .chain(rcm_orderings(n, &input.statements_using))
        .collect();

    let cost = |o: &[usize]| -> usize {
        ordering_excess_cost(
            o,
            &input.statements_using,
            &input.is_original_public,
            max_args,
        )
    };

    // Multi-start refinement. Refine the top REFINE_STARTS lowest-cost RCM
    // orderings, then add REFINE_RANDOM_STARTS random shuffles each refined
    // from a different seed. Tight predicates (4 public args, dense private
    // wildcard pool > max_arity) have narrow feasibility basins that a
    // single refinement from the RCM optimum routinely misses.
    //
    // Cost 0 means every position fits the public-args cap, but DP also
    // checks the total-wildcards cap which cost doesn't model, so all seeds
    // are refined unconditionally; the DP search picks the first one that
    // satisfies both caps.
    let mut refined_seeds: Vec<Vec<usize>> = orderings.clone();
    refined_seeds.sort_by_key(|o| cost(o));
    refined_seeds.truncate(REFINE_STARTS);

    let identity: Vec<usize> = (0..n).collect();
    let mut shuffle_rng = ChaCha20Rng::seed_from_u64(seed_from_ordering(&identity));
    for _ in 0..REFINE_RANDOM_STARTS {
        let mut shuffled: Vec<usize> = (0..n).collect();
        shuffled.shuffle(&mut shuffle_rng);
        refined_seeds.push(shuffled);
    }

    let mut refined: Vec<(Vec<usize>, usize)> = refined_seeds
        .into_iter()
        .map(|seed| {
            let r = refine_ordering(
                seed,
                &input.statements_using,
                &input.is_original_public,
                max_args,
                REFINE_ITERATIONS,
            );
            let c = cost(&r);
            (r, c)
        })
        .collect();
    // Refined orderings go first so DP probes the lowest-bandwidth candidates
    // before the bulk RCM list.
    refined.sort_by_key(|(_, c)| *c);
    for (r, _) in refined.into_iter().rev() {
        if !orderings.contains(&r) {
            orderings.insert(0, r);
        }
    }

    orderings
}

/// Split a predicate into a chain via DP partitioning. Tries every K from
/// `K_min` to `n` across a small set of heuristic orderings, returning the
/// first feasible chain. If every (ordering, K) pair fails, walks the
/// lowest-cost ordering bucket-by-bucket and emits the first cap violation
/// as a detailed [`SplittingError`].
fn split_into_chain(
    pred: &CustomPredicateDef,
    params: &Params,
) -> Result<(Vec<CustomPredicateDef>, SplitChainInfo), SplittingError> {
    let original_name = pred.name.name.clone();
    let conjunction = pred.conjunction_type;
    let real_statement_count = pred.statements.len();

    let input = prepare_split_input(pred);
    let n = input.n;
    let k_min = compute_min_links(n);
    let orderings = candidate_orderings(&input);

    let mut found: Option<(usize, LinkAssignment)> = None;
    for ordering in &orderings {
        let Some((k, assignment)) = try_partition(
            ordering,
            &input.statements_using,
            &input.is_original_public,
            params,
        ) else {
            continue;
        };
        if found.as_ref().is_none_or(|(best_k, _)| k < *best_k) {
            found = Some((k, assignment));
            // K_min is the arity-only lower bound; no ordering can beat it,
            // so stop the moment any candidate hits it.
            if k <= k_min {
                break;
            }
        }
    }

    let assignment = match found {
        Some((_, a)) => a,
        None => {
            // Lowest-cost ordering is at orderings[0] by construction;
            // candidate_orderings always produces at least the source order.
            let chosen = orderings
                .first()
                .expect("candidate_orderings always returns >= 1 ordering");
            return Err(diagnose_dp_failure(&original_name, &input, chosen, params));
        }
    };

    // Reorder map: original index -> position in flattened chain.
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

// ============================================================================
// Failure path. Everything below runs only when the DP exhausts every
// (ordering, K) pair without finding a feasible partition. It walks the
// lowest-cost ordering bucket-by-bucket to surface the first cap that
// overflows and renders a structured error. Not on the critical path: a bug
// here makes diagnostics worse, not splits wrong.
//
// `first_cap_violation` mirrors the per-link cap rules in `try_partition`; if
// those rules change, update both.
// ============================================================================

/// First per-link cap violation produced by a greedy bucket walk over a fixed
/// ordering.
enum CapViolation {
    PublicArgs {
        link_index: usize,
        statement_range: (usize, usize),
        incoming_public: Vec<String>,
        crossing_wildcards: Vec<String>,
        total_public: usize,
    },
    TotalArgs {
        link_index: usize,
        public_count: usize,
        private_count: usize,
        total_count: usize,
    },
}

/// Walk buckets of `ordered_wcs` applying the same cap rules the DP enforces,
/// returning the first violation or `None` if the ordering admits a feasible
/// chain.
fn first_cap_violation(
    ordered_wcs: &[HashSet<String>],
    original_public_args: &[String],
    params: &Params,
) -> Option<CapViolation> {
    let n = ordered_wcs.len();
    let max_arity = Params::max_custom_predicate_arity();
    let max_args = Params::max_statement_args();
    let max_wildcards = params.max_custom_predicate_wildcards;

    if n <= max_arity {
        return None;
    }

    let mut prefix_wcs: Vec<HashSet<String>> = vec![HashSet::new(); n + 1];
    for p in 0..n {
        prefix_wcs[p + 1] = prefix_wcs[p].clone();
        prefix_wcs[p + 1].extend(ordered_wcs[p].iter().cloned());
    }
    let mut suffix_wcs: Vec<HashSet<String>> = vec![HashSet::new(); n + 1];
    for p in (0..n).rev() {
        suffix_wcs[p] = suffix_wcs[p + 1].clone();
        suffix_wcs[p].extend(ordered_wcs[p].iter().cloned());
    }
    let original_pub_set: HashSet<String> = original_public_args.iter().cloned().collect();

    // Mirrors `try_partition`'s `incoming_at`: originals still in use plus
    // privates that cross the boundary. Without this, accumulating
    // promotions in a running ledger would report public args the DP would
    // have pruned, inflating `total_public` past the real cap.
    let incoming_at = |a: usize| -> Vec<String> {
        let mut out: Vec<String> = if a == 0 {
            original_public_args.to_vec()
        } else {
            suffix_wcs[a]
                .iter()
                .filter(|w| original_pub_set.contains(*w) || prefix_wcs[a].contains(*w))
                .cloned()
                .collect()
        };
        out.sort();
        out
    };

    let mut pos = 0;
    let mut link_index = 0;

    while pos < n {
        let remaining = n - pos;
        let is_last = remaining <= max_arity;
        let bucket_size = if is_last { remaining } else { max_arity - 1 };
        let end = pos + bucket_size;

        let incoming_public = incoming_at(pos);
        let incoming_set: HashSet<String> = incoming_public.iter().cloned().collect();

        let segment_wcs: HashSet<String> = ordered_wcs[pos..end]
            .iter()
            .flat_map(|s| s.iter().cloned())
            .collect();

        if !is_last {
            let next_incoming = incoming_at(end);
            if next_incoming.len() > max_args {
                let mut crossings: Vec<String> = next_incoming
                    .iter()
                    .filter(|w| !incoming_set.contains(*w))
                    .cloned()
                    .collect();
                crossings.sort();
                return Some(CapViolation::PublicArgs {
                    link_index,
                    statement_range: (pos, end),
                    incoming_public,
                    crossing_wildcards: crossings,
                    total_public: next_incoming.len(),
                });
            }
        }

        let mut total = incoming_set.clone();
        total.extend(segment_wcs.iter().cloned());
        if total.len() > max_wildcards {
            let private_count = segment_wcs
                .iter()
                .filter(|w| !incoming_set.contains(*w))
                .count();
            return Some(CapViolation::TotalArgs {
                link_index,
                public_count: incoming_public.len(),
                private_count,
                total_count: total.len(),
            });
        }

        pos = end;
        link_index += 1;
    }

    None
}

/// Per-statement wildcard names, indexed by original statement position. The
/// inverse of `SplitInput::statements_using`; resolving names once up front
/// is cheaper than `stmts.contains(&s)` scans inside the ordering loop.
fn wildcards_per_statement(input: &SplitInput) -> Vec<HashSet<String>> {
    let mut out: Vec<HashSet<String>> = vec![HashSet::new(); input.n];
    for (w, stmts) in input.statements_using.iter().enumerate() {
        for &s in stmts {
            out[s].insert(input.wildcard_names[w].clone());
        }
    }
    out
}

/// Largest-span wildcard wins over a generic "group these N" hint: a single
/// long live-range is usually the actionable refactor, while a multi-wildcard
/// crossing typically can't be resolved without restructuring the predicate.
fn refactor_suggestion_for(
    crossing: &[String],
    ordered_wcs: &[HashSet<String>],
) -> Option<RefactorSuggestion> {
    if crossing.is_empty() {
        return None;
    }
    let mut spans: Vec<(String, usize, usize, usize)> = Vec::new();
    for wildcard in crossing {
        let mut first_use = None;
        let mut last_use = None;
        for (i, wcs) in ordered_wcs.iter().enumerate() {
            if wcs.contains(wildcard) {
                if first_use.is_none() {
                    first_use = Some(i);
                }
                last_use = Some(i);
            }
        }
        if let (Some(first), Some(last)) = (first_use, last_use) {
            spans.push((wildcard.clone(), first, last, last - first));
        }
    }
    spans.sort_by(|a, b| b.3.cmp(&a.3));
    if let Some((wildcard, first, last, span)) = spans.first() {
        // A span longer than `max_arity - 2` necessarily crosses at least one
        // link boundary regardless of where the split is placed, which is the
        // case where "reduce this wildcard's live range" is actionable advice.
        if *span > 3 {
            return Some(RefactorSuggestion::ReduceWildcardSpan {
                wildcard: wildcard.clone(),
                first_use: *first,
                last_use: *last,
                span: *span,
            });
        }
    }
    if crossing.len() > 1 {
        let mut sorted = crossing.to_vec();
        sorted.sort();
        return Some(RefactorSuggestion::GroupWildcardUsages { wildcards: sorted });
    }
    None
}

/// Run the bucket walk on the lowest-cost ordering and convert the first cap
/// violation it finds into a detailed `SplittingError`. `first_cap_violation`
/// is guaranteed to return `Some` here: the bucket walk is a strict subset of
/// the partitions the DP searches, so if the DP failed for every (ordering, K),
/// greedy must also fail on the chosen ordering.
fn diagnose_dp_failure(
    predicate: &str,
    input: &SplitInput,
    ordering: &[usize],
    params: &Params,
) -> SplittingError {
    let max_args = Params::max_statement_args();
    let max_wildcards = params.max_custom_predicate_wildcards;

    let wcs_per_stmt = wildcards_per_statement(input);
    let ordered_wcs: Vec<HashSet<String>> =
        ordering.iter().map(|&s| wcs_per_stmt[s].clone()).collect();

    match first_cap_violation(&ordered_wcs, &input.original_public_args, params) {
        Some(CapViolation::PublicArgs {
            link_index,
            statement_range,
            incoming_public,
            crossing_wildcards,
            total_public,
        }) => {
            let suggestion =
                refactor_suggestion_for(&crossing_wildcards, &ordered_wcs).map(Box::new);
            SplittingError::TooManyPublicArgsAtSplit {
                predicate: predicate.to_string(),
                context: Box::new(SplitContext {
                    split_index: link_index,
                    statement_range,
                    incoming_public,
                    crossing_wildcards,
                    total_public,
                }),
                max_allowed: max_args,
                suggestion,
            }
        }
        Some(CapViolation::TotalArgs {
            link_index,
            public_count,
            private_count,
            total_count,
        }) => SplittingError::TooManyTotalArgsInChainLink {
            predicate: predicate.to_string(),
            link_index,
            public_count,
            private_count,
            total_count,
            max_allowed: max_wildcards,
        },
        None => unreachable!(
            "DP failed for every (ordering, K) but greedy walk found no cap violation on '{}'",
            predicate
        ),
    }
}

/// Build a `CustomPredicateDef` from a "wildcard set per statement"
/// specification. Cheaper than parsing for tests that don't care about
/// concrete statement predicates or anchored-key syntax.
#[cfg(test)]
pub(super) fn build_pred(
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
            reuse_pred(A, private: X) = AND (
                Equal(X["x"], A["start"])
                Equal(X["y"], 1)
                Equal(X["z"], 2)
                Equal(X["w"], 3)
                Equal(A["mid"], X["x"])
                Equal(X["a"], 4)
                Equal(X["b"], 5)
                Equal(X["c"], 6)
                Equal(A["end"], X["x"])
            )
        "#;

        let pred = parse_predicate(input);
        let params = Params::default();

        let result = split_predicate_if_needed(pred, &params);
        assert!(result.is_ok());

        let split_result = result.unwrap();
        let chain = &split_result.predicates;
        // Should split into 2 predicates
        // X is used in first segment and crosses to second, then used again in second
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

    /// Statements that reference only public args should be deferred until private-wildcard
    /// statements have been clustered, so they don't consume bucket slots that would reduce
    /// liveness at split boundaries.
    ///
    /// 4 public args, 7 statements: X0 used in stmts 0,1,4; X1 used in stmts 1,2,3;
    /// stmts 5,6 reference only public args.  The scoring correctly defers stmts 5,6,
    /// yielding bucket0={0,1,2,3}, bucket1={4,5,6} with only X0 crossing (4+1=5 <= max).
    #[test]
    fn test_split_succeeds_with_four_public_args_and_public_only_statements() {
        // Optimal split: bucket0={0,1,2,3}, bucket1={4,5,6}
        // Only X0 crosses (used in 0,1 and 4), total = 4 public + 1 crossing = 5 (OK)
        let input = r#"
            pred(A, B, C, D, private: X0, X1) = AND(
                Equal(X0["x"], A["v"])
                Equal(X1["y"], X0["x"])
                Equal(X1["z"], B["v"])
                Equal(C["r"], X1["y"])
                Equal(D["s"], X0["x"])
                Equal(A["out"], C["out"])
                Equal(B["out"], D["out"])
            )
        "#;

        let pred = parse_predicate(input);
        let params = Params::default();

        let result = split_predicate_if_needed(pred, &params);
        assert!(
            result.is_ok(),
            "Should find a valid split with <=1 crossing wildcard, got: {:?}",
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
            pred(A, B, private: X) = AND(
                Equal(X["x"], A["val"])
                Equal(X["y"], 1)
                Equal(X["z"], 2)
                Equal(X["w"], 3)
                Equal(B["r"], X["x"])
                Equal(B["s"], X["y"])
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

    /// 6 statements with 2 public args (A, B) and 5 private wildcards
    /// (X0..X4). A feasible 4+2 chain exists where exactly 3 wildcards cross
    /// the boundary (3 promotions + 2 incoming = 5 total public, hitting the
    /// cap). The splitter must find one: a partition that puts an extra
    /// wildcard across the boundary fails the per-link public-arg cap.
    ///
    /// Found by random search with seed 0xC0FFEE; inlined for determinism.
    #[test]
    fn test_splitter_handles_tight_public_arg_cap() {
        let pred = build_pred(
            "p",
            &["A", "B"],
            &["X0", "X1", "X2", "X3", "X4"],
            &[
                &["X0", "X4", "X2"],
                &["X1", "X3", "X4"],
                &["X2", "X3", "X1"],
                &["X4", "A", "B"],
                &["X3", "X0", "X2"],
                &["X0", "B", "X1"],
            ],
        );
        let params = Params::default();

        let result = split_predicate_if_needed(pred, &params);
        assert!(
            result.is_ok(),
            "splitter rejected a known-feasible input: {}",
            result.err().unwrap()
        );
    }

    /// A predicate with one statement that references 9 distinct wildcards
    /// is unsplittable: any link containing that statement declares 9
    /// wildcards, exceeding the per-link cap of 8. The DP-failure diagnostic
    /// must surface this as a `TooManyTotalArgsInChainLink` pinpointing the
    /// link that holds the dense statement.
    #[test]
    fn test_dp_failure_reports_total_args_in_chain_link() {
        let pred = build_pred(
            "dense",
            &["A"],
            &["X0", "X1", "X2", "X3", "X4", "X5", "X6", "X7", "X8"],
            &[
                &["X0", "X1", "X2", "X3", "X4", "X5", "X6", "X7", "X8"],
                &["X0"],
                &["X0"],
                &["X0"],
                &["X0"],
                &["X0"],
            ],
        );
        let params = Params::default();

        let err = split_predicate_if_needed(pred, &params).expect_err("splitter should fail");
        match err {
            SplittingError::TooManyTotalArgsInChainLink {
                predicate,
                link_index,
                private_count,
                total_count,
                max_allowed,
                ..
            } => {
                assert_eq!(predicate, "dense");
                assert_eq!(link_index, 0, "dense statement should fall in link 0");
                assert!(
                    private_count >= 8,
                    "link 0 should declare X1..X8 as private, got private_count={}",
                    private_count
                );
                assert!(
                    total_count > max_allowed,
                    "total_count {} should exceed max_allowed {}",
                    total_count,
                    max_allowed
                );
            }
            other => panic!("expected TooManyTotalArgsInChainLink, got: {:?}", other),
        }
    }

    /// Direct unit test of the bucket-walk diagnostic. Hand-crafted ordering
    /// puts 6 distinct wildcards live across the first boundary, forcing the
    /// per-link public-arg cap of 5 to overflow at link 0. Tests
    /// `first_cap_violation` directly because hand-constructing a predicate
    /// the DP can't split (across every ordering and every K) is brittle:
    /// the DP is too good at clustering related wildcards into one link.
    #[test]
    fn test_first_cap_violation_reports_public_args_at_split() {
        let mk =
            |names: &[&str]| -> HashSet<String> { names.iter().map(|s| s.to_string()).collect() };
        // 9 positions, 6 private wildcards each used in both halves so they
        // all cross the K=2 boundary at position 4. The bucket walk then
        // sees 6 promotions on top of the 0 incoming publics -> 6 > 5.
        let ordered_wcs: Vec<HashSet<String>> = vec![
            mk(&["X0", "X1"]),
            mk(&["X2", "X3"]),
            mk(&["X4", "X5"]),
            mk(&["X0", "X2"]),
            mk(&["X1", "X3"]),
            mk(&["X4", "X5"]),
            mk(&["X0", "X4"]),
            mk(&["X1", "X5"]),
            mk(&["X2", "X3"]),
        ];
        let params = Params::default();
        let violation =
            first_cap_violation(&ordered_wcs, &[], &params).expect("expected a violation");

        match violation {
            CapViolation::PublicArgs {
                link_index,
                total_public,
                crossing_wildcards,
                ..
            } => {
                assert_eq!(link_index, 0);
                assert!(
                    total_public > Params::max_statement_args(),
                    "total_public {} should exceed cap of {}",
                    total_public,
                    Params::max_statement_args()
                );
                assert!(
                    crossing_wildcards.len() >= 6,
                    "expected >=6 crossings, got {:?}",
                    crossing_wildcards
                );
            }
            CapViolation::TotalArgs { .. } => {
                panic!("expected PublicArgs violation, got TotalArgs")
            }
        }
    }

    /// Past the first link, original publics that are no longer used must
    /// drop out of the reported incoming set: otherwise the diagnostic
    /// blames public args the chain wouldn't actually pass.
    #[test]
    fn test_first_cap_violation_prunes_unused_original_publics() {
        let mk = |names: &[&str]| -> HashSet<String> {
            names.iter().map(|s| s.to_string()).collect()
        };
        // Originals A, B used only at position 0; X3..X8 first appear in
        // link 1 and cross into link 2. Six crossers exceed max_args = 5,
        // so the bust is at link 1's transition - where A and B should
        // already be pruned.
        let ordered_wcs: Vec<HashSet<String>> = vec![
            mk(&["A", "B", "X0", "X1", "X2"]), // 0
            mk(&["X0"]),                       // 1
            mk(&["X1"]),                       // 2
            mk(&["X2"]),                       // 3
            mk(&["X3", "X4", "X5"]),           // 4 - link 1 starts
            mk(&["X6", "X7", "X8"]),           // 5
            mk(&["X3", "X6"]),                 // 6
            mk(&["X4", "X7"]),                 // 7
            mk(&["X3", "X4", "X5", "X6", "X7", "X8"]), // 8 - link 2
            mk(&["X3"]),                       // 9
        ];
        let originals = vec!["A".to_string(), "B".to_string()];
        let params = Params::default();
        let violation =
            first_cap_violation(&ordered_wcs, &originals, &params).expect("expected a violation");

        match violation {
            CapViolation::PublicArgs {
                link_index,
                incoming_public,
                crossing_wildcards,
                total_public,
                ..
            } => {
                assert_eq!(link_index, 1);
                assert!(
                    !incoming_public.iter().any(|w| w == "A" || w == "B"),
                    "unused original publics should be pruned, got: {:?}",
                    incoming_public
                );
                assert_eq!(crossing_wildcards.len(), 6);
                assert_eq!(total_public, 6);
            }
            CapViolation::TotalArgs { .. } => {
                panic!("expected PublicArgs, got TotalArgs")
            }
        }
    }

    /// 51-statement predicate with a 13-link wildcard chain, modelled on
    /// `CraftRefineryCracked` from the zk-craft episode-1 plugin. K_min = 13
    /// with `max_custom_predicate_arity = 5`. Acts as a real-world-shaped
    /// stress test for splitter latency.
    #[test]
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
        let result = split_predicate_if_needed(pred, &params);
        assert!(result.is_ok(), "split failed: {:?}", result.err());
    }
}
