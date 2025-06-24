use std::{collections::HashMap, time::Duration};

use crate::solver::{engine::semi_naive::FactStore, ir::PredicateIdentifier};

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

#[derive(Default)]
pub struct MetricsCollector {
    pub fixpoint_iterations: u32,
    pub facts_derived_per_predicate: HashMap<PredicateIdentifier, usize>,
    pub materializer_calls: u64,
    pub deltas: Vec<FactStore>,
}

/// Specifies the level of metrics to collect during solving.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum MetricsLevel {
    /// No metrics are collected. This should have zero runtime cost.
    None,
    /// Only inexpensive counters are collected.
    Counters,
    /// Detailed, potentially expensive debug information is collected.
    Debug,
}

/// A trait for collecting metrics during the solving process.
/// This allows for different levels of detail without cluttering the engine with conditionals.
pub trait MetricsSink: Default + Send + Sync {
    /// Increments the counter for fixpoint iterations.
    fn increment_iterations(&mut self);
    /// Records the number of new facts from a completed iteration.
    fn record_delta_size(&mut self, num_facts: usize);
    /// Records a delta.
    fn record_delta(&mut self, delta: FactStore) {}
}

// --- Sink Implementations ---

/// A metrics sink that performs no operations, allowing the compiler to
/// eliminate all metrics-related code when used.
#[derive(Default, Debug)]
pub struct NoOpMetrics;
impl MetricsSink for NoOpMetrics {
    fn increment_iterations(&mut self) { /* no-op */
    }
    fn record_delta_size(&mut self, _num_facts: usize) { /* no-op */
    }
    fn record_delta(&mut self, delta: FactStore) {
        /* no-op */
    }
}

/// A metrics sink that collects simple counters.
#[derive(Default, Debug)]
pub struct CounterMetrics {
    pub fixpoint_iterations: u32,
    pub facts_in_deltas: u64,
}
impl MetricsSink for CounterMetrics {
    fn increment_iterations(&mut self) {
        self.fixpoint_iterations += 1;
    }
    fn record_delta_size(&mut self, num_facts: usize) {
        self.facts_in_deltas += num_facts as u64;
    }
}

/// A metrics sink that collects detailed information for debugging.
/// For now, it delegates to the CounterMetrics implementation.
#[derive(Default, Debug)]
pub struct DebugMetrics {
    pub counters: CounterMetrics,
    pub deltas: Vec<FactStore>,
}
impl MetricsSink for DebugMetrics {
    fn increment_iterations(&mut self) {
        self.counters.increment_iterations();
    }
    fn record_delta_size(&mut self, num_facts: usize) {
        self.counters.record_delta_size(num_facts);
    }
    fn record_delta(&mut self, delta: FactStore) {
        self.deltas.push(delta);
    }
}

/// The final report returned to the user, containing the collected metrics.
#[derive(Debug)]
pub enum MetricsReport {
    None,
    Counters(CounterMetrics),
    Debug(DebugMetrics),
}
