pub mod enumerator;
pub mod predicates;
pub mod provider;

pub use provider::PodSemantics;

use super::{engine::Solution, error::SolverError};
use crate::middleware::{AnchoredKey, CustomPredicateRef, StatementTmpl};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Binding {
    Bound,
    Free,
}

pub type Adornment = [Binding];

/// A template for a justification, returned by the `SemanticsProvider` during
/// the search process. It mirrors the final `Justification` enum, but contains
/// `StatementTmpl`s as premises instead of fully-proven `ProofNode`s.
#[derive(Debug, Clone)]
pub enum JustificationTemplate {
    /// The conclusion is a known fact from the `FactDB`.
    Fact,
    /// The conclusion was derived by applying a native operation like `EqualFromEntries`.
    ValueComparison,
    /// The conclusion was derived from a path in the equality graph.
    Transitive(Vec<AnchoredKey>),
    /// The conclusion was derived by applying a custom predicate. The `premises`
    /// are the sub-goals from the predicate's body that must be proven.
    Custom {
        predicate: CustomPredicateRef,
        premises: Vec<StatementTmpl>,
    },
}

/// Represents a potential way to satisfy a single goal statement, returned by
/// the `SemanticsProvider`.
#[derive(Debug, Clone)]
pub struct SolutionCandidate {
    /// New bindings for previously unbound wildcards.
    pub new_bindings: Solution,
    /// The template for the justification that explains *how* this solution
    /// was found.
    pub justification: JustificationTemplate,
}
