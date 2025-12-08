use std::{backtrace::Backtrace, fmt::Debug};

use crate::middleware::{BackendError, Statement, StatementTmpl, Value};

pub type Result<T, E = Error> = core::result::Result<T, E>;

fn display_wc_map(wc_map: &[Option<Value>]) -> String {
    let mut out = String::new();
    use std::fmt::Write;
    for (i, v) in wc_map.iter().enumerate() {
        write!(out, "- {}: ", i).unwrap();
        if let Some(v) = v {
            writeln!(out, "{}", v).unwrap();
        } else {
            writeln!(out, "none").unwrap();
        }
    }
    out
}

#[derive(thiserror::Error, Debug)]
pub enum InnerError {
    #[error("{0} {1} is over the limit {2}")]
    MaxLength(String, usize, usize),
    #[error("{0} doesn't match {1:#}.\nWildcard map:\n{map}\nInternal error: {3}", map=display_wc_map(.2))]
    StatementsDontMatch(
        Statement,
        StatementTmpl,
        Vec<Option<Value>>,
        crate::middleware::Error,
    ),
    #[error("invalid arguments to {0} operation")]
    OpInvalidArgs(String),
    #[error("Podlang parse error: {0}")]
    PodlangParse(String),
    #[error("POD Request validation error: {0}")]
    PodRequestValidation(String),
    #[error("Too many input PODs provided: {0} were provided, but the maximum is {1}")]
    TooManyInputPods(usize, usize),
    #[error("Too many public statements provided: {0} were provided, but the maximum is {1}")]
    TooManyPublicStatements(usize, usize),
    #[error("Too many statements provided: {0} were provided, but the maximum is {1}")]
    TooManyStatements(usize, usize),
    // Other
    #[error("{0}")]
    Custom(String),
}

#[derive(thiserror::Error)]
pub enum Error {
    #[error("Inner: {inner}\n{backtrace}")]
    Inner {
        inner: Box<InnerError>,
        backtrace: Box<Backtrace>,
    },
    #[error(transparent)]
    Backend(#[from] BackendError),
    #[error(transparent)]
    Middleware(#[from] crate::middleware::Error),
}

impl From<std::convert::Infallible> for Error {
    fn from(value: std::convert::Infallible) -> Self {
        match value {}
    }
}

impl From<crate::lang::LangError> for Error {
    fn from(value: crate::lang::LangError) -> Self {
        Error::podlang_parse(value)
    }
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
use InnerError::*;
impl Error {
    pub(crate) fn custom(s: impl Into<String>) -> Self {
        new!(Custom(s.into()))
    }
    pub(crate) fn op_invalid_args(s: String) -> Self {
        new!(OpInvalidArgs(s))
    }
    pub(crate) fn statements_dont_match(
        s0: Statement,
        s1: StatementTmpl,
        wc_map: Vec<Option<Value>>,
        mid_error: crate::middleware::Error,
    ) -> Self {
        new!(StatementsDontMatch(s0, s1, wc_map, mid_error))
    }
    pub(crate) fn max_length(obj: String, found: usize, expect: usize) -> Self {
        new!(MaxLength(obj, found, expect))
    }
    pub(crate) fn podlang_parse(e: crate::lang::LangError) -> Self {
        new!(PodlangParse(e.to_string()))
    }
    pub(crate) fn pod_request_validation(e: String) -> Self {
        new!(PodRequestValidation(e))
    }
    pub(crate) fn too_many_input_pods(found: usize, max: usize) -> Self {
        new!(TooManyInputPods(found, max))
    }
    pub(crate) fn too_many_public_statements(found: usize, max: usize) -> Self {
        new!(TooManyPublicStatements(found, max))
    }
    pub(crate) fn too_many_statements(found: usize, max: usize) -> Self {
        new!(TooManyStatements(found, max))
    }
}
