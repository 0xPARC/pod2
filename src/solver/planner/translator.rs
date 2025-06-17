//! Translates `StatementTmpl`s into the Datalog IR.
//!
//! This module is responsible for collecting wildcards from statement templates.

use std::collections::HashSet;

use crate::{
    middleware::{StatementTmplArg, Wildcard},
    solver::error::SolverError,
};

/// Collects all unique wildcards from a slice of `StatementTmplArg`s.
pub(super) fn collect_wildcards(
    args: &[StatementTmplArg],
) -> Result<HashSet<Wildcard>, SolverError> {
    let mut wildcards = HashSet::new();
    for arg in args {
        match arg {
            StatementTmplArg::Wildcard(w) => {
                wildcards.insert(w.clone());
            }
            StatementTmplArg::AnchoredKey(pod_wc, _) => {
                wildcards.insert(pod_wc.clone());
            }
            StatementTmplArg::Literal(_) => {}
            StatementTmplArg::None => {
                return Err(SolverError::Internal(
                    "None argument not supported in custom predicates".to_string(),
                ));
            }
        }
    }
    Ok(wildcards)
}
