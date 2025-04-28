use std::{collections::HashMap, sync::Arc};

use crate::middleware::{self, CustomPredicate, PodId, Statement, F};

pub type CustomDefinitions = HashMap<Vec<F>, middleware::CustomPredicate>;
pub type InitialFacts = Vec<(PodId, middleware::Statement)>;

/// The overall result of the translation stage.
pub struct TranslationOutput {
    pub custom_definitions: CustomDefinitions,
    pub initial_facts: InitialFacts,
}

// Add other shared types as needed, e.g.:
// pub struct ProofSolution { ... }
// pub struct ProofStep { ... }
// pub struct ProofChain { ... }
