//! Translates `StatementTmpl`s into the Datalog IR.
//!
//! This module is responsible for the "flattening" of `StatementTmpl`s,
//! which converts structured `AnchoredKey` arguments into separate `GetValue`
//! literals in the IR.

use std::collections::HashSet;

use crate::{
    middleware::{StatementTmplArg, Wildcard},
    solver::{
        error::SolverError,
        ir::{Literal, PredicateIdentifier, Term},
    },
};

/// A context for translating a single rule body. It keeps track of new
/// literals created via flattening and allocates fresh variables.
pub(super) struct TranslationContext {
    pub(super) flattened_literals: Vec<Literal>,
    fresh_var_counter: usize,
    pub(super) bound_variables: HashSet<Wildcard>,
}

impl TranslationContext {
    pub(super) fn new() -> Self {
        Self {
            flattened_literals: Vec::new(),
            fresh_var_counter: 0,
            bound_variables: HashSet::new(),
        }
    }

    /// Generates a new, unique wildcard for intermediate values.
    fn fresh_wildcard(&mut self) -> Wildcard {
        let var = Wildcard::new(format!("_fresh{}", self.fresh_var_counter), 99); // ID is arbitrary
        self.fresh_var_counter += 1;
        var
    }

    /// Converts a `StatementTmplArg` into an IR `Term`, flattening `AnchoredKey`
    /// templates into `GetValue` literals as needed.
    pub(super) fn translate_arg_to_term(
        &mut self,
        arg: &StatementTmplArg,
    ) -> Result<Term, SolverError> {
        match arg {
            StatementTmplArg::Literal(v) => Ok(Term::Constant(v.clone())),
            StatementTmplArg::Wildcard(w) => {
                self.bound_variables.insert(w.clone());
                Ok(Term::Variable(w.clone()))
            }
            StatementTmplArg::AnchoredKey(pod_wc, key) => {
                // Create a fresh variable for the value of the AnchoredKey.
                let value_wc = self.fresh_wildcard();
                let value_term = Term::Variable(value_wc.clone());

                // Create the new GetValue literal.
                let get_value_literal = Literal {
                    predicate: PredicateIdentifier::GetValue,
                    terms: vec![
                        Term::Variable(pod_wc.clone()),
                        Term::Constant(key.name().into()),
                        value_term.clone(),
                    ],
                };
                self.flattened_literals.push(get_value_literal);
                self.bound_variables.insert(pod_wc.clone());
                self.bound_variables.insert(value_wc);

                Ok(value_term)
            }
            StatementTmplArg::None => Err(SolverError::Internal(
                "None argument not supported in custom predicates".to_string(),
            )),
        }
    }
}
