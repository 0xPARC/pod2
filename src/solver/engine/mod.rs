use std::collections::HashMap;

use crate::{
    middleware::{StatementTmpl, Value},
    solver::{error::SolverError, proof::Proof, semantics::PodSemantics},
};

//pub mod proof_reconstruction;
pub mod semi_naive;

/// A map from wildcard names to their bound `Value`.
pub type Solution = HashMap<String, Value>;

/// A request to be proven, consisting of a set of statement templates.
pub type ProofRequest = Vec<StatementTmpl>;

/// The generic interface for any query resolution engine.
pub trait QueryEngine {
    /// Solves a proof request using the provided semantics provider, returning
    /// the first valid solution found.
    ///
    /// The engine will extract any necessary custom predicate definitions
    /// from the request itself.
    ///
    /// # Returns
    /// - `Ok(Some(proof))` if a valid proof tree is found.
    /// - `Ok(None)` if the request cannot be proven.
    /// - `Err(SolverError)` if an unexpected error occurs during solving.
    fn solve(
        &self,
        request: &ProofRequest,
        semantics: &PodSemantics,
    ) -> Result<Option<Proof>, SolverError>;
}
