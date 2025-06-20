use std::{collections::HashMap, time::Duration};

use crate::solver::{engine::semi_naive::FactStore, ir::PredicateIdentifier};

pub enum MetricsLevel {
    None,
    Basic,
    Counts,
    Verbose,
}

pub struct SolverMetrics {
    pub total_solve_time: Option<Duration>,
    pub planning_time: Option<Duration>,
    pub evaluation_time: Option<Duration>,
    pub reconstruction_time: Option<Duration>,

    // Level 2: Counters
    pub fixpoint_iterations: Option<u32>,
    pub facts_derived_per_predicate: Option<HashMap<PredicateIdentifier, usize>>,
    pub materializer_calls: Option<u64>,

    // Level 3: Verbose
    pub deltas: Option<Vec<FactStore>>,
}
