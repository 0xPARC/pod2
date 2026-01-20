//! middleware errors

use std::{backtrace::Backtrace, fmt::Debug};

use crate::middleware::{
    CustomPredicate, Hash, Key, Operation, Predicate, Statement, StatementArg, StatementTmplArg,
    Value, Wildcard,
};

pub type Result<T, E = Error> = core::result::Result<T, E>;

#[derive(Debug, thiserror::Error)]
pub enum MiddlewareInnerError {
    #[error("incorrect statement args")]
    IncorrectStatementArgs,
    #[error("invalid deduction: {0:?} ⇏ {1:#}")]
    InvalidDeduction(Operation, Statement),
    #[error("statement argument {0:?} should be a {1}")]
    InvalidStatementArg(StatementArg, String),
    #[error("{0} {1} is over the limit {2}")]
    MaxLength(String, usize, usize),
    #[error("{0} amount of {1} should be {2} but it's {3}")]
    DiffAmount(String, String, usize, usize),
    #[error("{0} should be assigned the value {1} but has previously been assigned {2}")]
    InvalidWildcardAssignment(Wildcard, Value, Value),
    #[error("{0} matches POD ID {1}, yet the template key {2} does not match {3}")]
    MismatchedAnchoredKeyInStatementTmplArg(Wildcard, Hash, Key, Key),
    #[error("{0} does not match against {1}")]
    MismatchedStatementTmplArg(StatementTmplArg, StatementArg),
    #[error("Expected a statement of type {0}, got {1}")]
    MismatchedStatementType(Predicate, Predicate),
    #[error("Expected a statement with hash(predicate) {0}, got {1} ({2})")]
    MismatchedStatementWildcardPredicate(Value, Value, Predicate),
    #[error("Value {0} does not match argument {1} with index {2} in the following custom predicate:\n{3}")]
    MismatchedWildcardValueAndStatementArg(Value, Value, usize, CustomPredicate),
    #[error(
        "None of the statement templates of the following custom predicate have been matched:\n{0}"
    )]
    UnsatisfiedCustomPredicateDisjunction(CustomPredicate),
    // Other
    #[error("{0}")]
    Custom(String),
}

#[derive(thiserror::Error)]
pub enum Error {
    #[error("Inner: {inner}\n{backtrace}")]
    Inner {
        inner: Box<MiddlewareInnerError>,
        backtrace: Box<Backtrace>,
    },
    #[error(transparent)]
    Tree(#[from] crate::backends::plonky2::primitives::merkletree::error::TreeError),
}

impl Debug for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self, f)
    }
}

macro_rules! new {
    ($inner:expr) => {
        Error::Inner {
            inner: Box::new($inner),
            backtrace: Box::new(Backtrace::capture()),
        }
    };
}
use MiddlewareInnerError::*;
impl Error {
    pub(crate) fn incorrect_statements_args() -> Self {
        new!(IncorrectStatementArgs)
    }
    pub(crate) fn invalid_deduction(op: Operation, st: Statement) -> Self {
        new!(InvalidDeduction(op, st))
    }
    pub(crate) fn invalid_statement_arg(st_arg: StatementArg, v: String) -> Self {
        new!(InvalidStatementArg(st_arg, v))
    }
    pub(crate) fn max_length(obj: String, found: usize, expect: usize) -> Self {
        new!(MaxLength(obj, found, expect))
    }
    pub(crate) fn diff_amount(obj: String, unit: String, expect: usize, found: usize) -> Self {
        new!(DiffAmount(obj, unit, expect, found))
    }
    pub(crate) fn invalid_wildcard_assignment(
        wildcard: Wildcard,
        value: Value,
        prev_value: Value,
    ) -> Self {
        new!(InvalidWildcardAssignment(wildcard, value, prev_value))
    }
    pub(crate) fn mismatched_anchored_key_in_statement_tmpl_arg(
        root_wildcard: Wildcard,
        root: Hash,
        key_tmpl: Key,
        key: Key,
    ) -> Self {
        new!(MismatchedAnchoredKeyInStatementTmplArg(
            root_wildcard,
            root,
            key_tmpl,
            key
        ))
    }
    pub(crate) fn mismatched_statement_tmpl_arg(
        st_tmpl_arg: StatementTmplArg,
        st_arg: StatementArg,
    ) -> Self {
        new!(MismatchedStatementTmplArg(st_tmpl_arg, st_arg))
    }
    pub(crate) fn mismatched_statement_type(expected: Predicate, seen: Predicate) -> Self {
        new!(MismatchedStatementType(expected, seen))
    }
    pub(crate) fn mismatched_statement_wc_pred(
        expected: Value,
        seen: Value,
        seen_pred: Predicate,
    ) -> Self {
        new!(MismatchedStatementWildcardPredicate(
            expected, seen, seen_pred
        ))
    }
    pub(crate) fn mismatched_wildcard_value_and_statement_arg(
        wc_value: Value,
        st_arg: Value,
        arg_index: usize,
        pred: CustomPredicate,
    ) -> Self {
        new!(MismatchedWildcardValueAndStatementArg(
            wc_value, st_arg, arg_index, pred
        ))
    }
    pub(crate) fn unsatisfied_custom_predicate_disjunction(pred: CustomPredicate) -> Self {
        new!(UnsatisfiedCustomPredicateDisjunction(pred))
    }
    pub(crate) fn custom(s: String) -> Self {
        new!(Custom(s))
    }
}
