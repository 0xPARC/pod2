use std::{fmt, ops::Deref};

use thiserror::Error;

use crate::{
    frontend,
    lang::{frontend_ast::Span, parser::ParseError},
    middleware,
};

#[derive(Error, Debug)]
pub enum LangErrorKind {
    #[error("Parsing failed: {0}")]
    Parse(Box<ParseError>),

    #[error("Middleware error during processing: {0}")]
    Middleware(Box<middleware::Error>),

    #[error("Frontend error: {0}")]
    Frontend(Box<frontend::Error>),

    #[error("Validation error: {0}")]
    Validation(Box<ValidationError>),

    #[error("Lowering error: {0}")]
    Lowering(Box<LoweringError>),

    #[error("Batching error: {0}")]
    Batching(Box<BatchingError>),
}

/// Top-level error type for the Podlang pipeline.
///
/// When source text is attached (e.g. from [`crate::lang::parse`]), `Display` produces a rich,
/// source-annotated diagnostic. Otherwise it falls back to a plain message.
///
/// The inner [`LangErrorKind`] variants are accessible via `Deref`, so existing match patterns
/// like `LangError::Validation(e)` continue to work.
pub struct LangError {
    pub kind: LangErrorKind,
    source_text: Option<String>,
    path: Option<String>,
}

impl LangError {
    pub fn new(kind: LangErrorKind) -> Self {
        Self {
            kind,
            source_text: None,
            path: None,
        }
    }

    /// Attach source text (and optional path) so that `Display` produces a rich diagnostic.
    pub fn with_source(mut self, source: impl Into<String>, path: Option<String>) -> Self {
        self.source_text = Some(source.into());
        self.path = path;
        self
    }
}

impl fmt::Debug for LangError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

impl Deref for LangError {
    type Target = LangErrorKind;
    fn deref(&self) -> &LangErrorKind {
        &self.kind
    }
}

impl fmt::Display for LangError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.source_text {
            Some(source) => {
                let rendered =
                    crate::lang::diagnostics::render_error(source, self.path.as_deref(), self);
                write!(f, "{}", rendered)
            }
            None => write!(f, "{}", self.kind),
        }
    }
}

impl std::error::Error for LangError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        self.kind.source()
    }
}

/// Validation errors from frontend AST validation
#[derive(Debug, thiserror::Error)]
pub enum ValidationError {
    #[error("Invalid hash: {hash}")]
    InvalidHash { hash: String, span: Option<Span> },

    #[error("Duplicate predicate definition: {name}")]
    DuplicatePredicate {
        name: String,
        first_span: Option<Span>,
        second_span: Option<Span>,
    },

    #[error("Duplicate import name: {name}")]
    DuplicateImport { name: String, span: Option<Span> },

    #[error("Import arity mismatch: expected {expected} predicates, found {found}")]
    ImportArityMismatch {
        expected: usize,
        found: usize,
        span: Option<Span>,
    },

    #[error("Module not found: {name}")]
    ModuleNotFound { name: String, span: Option<Span> },

    #[error("Undefined predicate: {name}")]
    UndefinedPredicate { name: String, span: Option<Span> },

    #[error("Undefined wildcard: {name} in predicate {pred_name}")]
    UndefinedWildcard {
        name: String,
        pred_name: String,
        span: Option<Span>,
    },

    #[error("Argument count mismatch for {predicate}: expected {expected}, found {found}")]
    ArgumentCountMismatch {
        predicate: String,
        expected: usize,
        found: usize,
        span: Option<Span>,
    },

    #[error("Duplicate wildcard in predicate arguments: {name}")]
    DuplicateWildcard { name: String, span: Option<Span> },

    #[error("Empty statement list in {context}")]
    EmptyStatementList { context: String, span: Option<Span> },

    #[error("Multiple REQUEST definitions found. Only one is allowed.")]
    MultipleRequestDefinitions {
        first_span: Option<Span>,
        second_span: Option<Span>,
    },

    #[error("Wildcard '{name}' collides with a predicate name")]
    WildcardPredicateNameCollision { name: String },

    #[error("Predicate definitions are not allowed in requests")]
    PredicatesNotAllowedInRequest { span: Option<Span> },

    #[error("REQUEST block is not allowed in modules")]
    RequestNotAllowedInModule { span: Option<Span> },

    #[error("Modules must contain at least one predicate definition")]
    NoPredicatesInModule,

    #[error("Self-referential predicate literal not allowed in requests")]
    SelfReferentialPredicateLiteralNotAllowedInRequests { span: Option<Span> },

    #[error("Requests must contain a REQUEST block")]
    NoRequestBlock,

    #[error("Duplicate record definition: {name}")]
    DuplicateRecord {
        name: String,
        first_span: Option<Span>,
        second_span: Option<Span>,
    },

    #[error("Record '{name}' has {count} entries, exceeding the limit of {max}")]
    RecordTooManyEntries {
        name: String,
        count: usize,
        max: usize,
        span: Option<Span>,
    },

    #[error("Duplicate entry name '{entry}' in record '{record}'")]
    DuplicateRecordEntry {
        record: String,
        entry: String,
        span: Option<Span>,
    },

    #[error("Unknown record type: {name}")]
    UnknownRecord { name: String, span: Option<Span> },

    #[error("Record '{record}' has no entry '{entry}'")]
    UnknownRecordEntry {
        record: String,
        entry: String,
        span: Option<Span>,
    },

    #[error("Duplicate entry '{entry}' in record literal '{record}'")]
    DuplicateLiteralRecordEntry {
        record: String,
        entry: String,
        span: Option<Span>,
    },

    #[error("Bracket access '{wildcard}[...]' is not allowed on a wildcard typed as record '{record}'; use `{wildcard}.entry` instead")]
    BracketAccessOnTypedWildcard {
        wildcard: String,
        record: String,
        span: Option<Span>,
    },
}

/// Lowering errors from frontend AST lowering to middleware
#[derive(Debug, thiserror::Error)]
pub enum LoweringError {
    #[error("Too many statements in predicate '{predicate}': {count} exceeds limit of {max}")]
    TooManyStatements {
        predicate: String,
        count: usize,
        max: usize,
    },

    #[error("Too many wildcards in predicate '{predicate}': {count} exceeds limit of {max}")]
    TooManyWildcards {
        predicate: String,
        count: usize,
        max: usize,
    },

    #[error("Too many arguments in statement template: {count} exceeds limit of {max}")]
    TooManyStatementArgs { count: usize, max: usize },

    #[error("Predicate '{name}' not found in symbol table")]
    PredicateNotFound { name: String },

    #[error("Invalid argument type in statement template")]
    InvalidArgumentType,

    #[error("Middleware error: {0}")]
    Middleware(#[from] middleware::Error),

    #[error("Splitting error: {0}")]
    Splitting(#[from] SplittingError),

    #[error("Batching error: {0}")]
    Batching(#[from] BatchingError),

    #[error("Cannot lower document with validation errors")]
    ValidationErrors,
}

/// Batching errors from multi-batch packing
#[derive(Debug, thiserror::Error)]
pub enum BatchingError {
    #[error("Internal batching error: {message}")]
    Internal { message: String },
}

/// Splitting errors from predicate splitting
#[derive(Debug, thiserror::Error)]
pub enum SplittingError {
    #[error("Too many public arguments in predicate '{predicate}': {count} exceeds max of {max_allowed}. {message}")]
    TooManyPublicArgs {
        predicate: String,
        count: usize,
        max_allowed: usize,
        message: String,
    },

    #[error("Could not split predicate '{predicate}' into a chain: no feasible partition exists with up to {max_links} links. \
             The predicate's wildcard structure may be too dense for any chain to fit within max_statement_args ({max_statement_args}) \
             and max_custom_predicate_wildcards ({max_wildcards}) per link.")]
    Infeasible {
        predicate: String,
        max_links: usize,
        max_statement_args: usize,
        max_wildcards: usize,
    },
}

impl From<ParseError> for LangError {
    fn from(err: ParseError) -> Self {
        LangError::new(LangErrorKind::Parse(Box::new(err)))
    }
}

impl From<middleware::Error> for LangError {
    fn from(err: middleware::Error) -> Self {
        LangError::new(LangErrorKind::Middleware(Box::new(err)))
    }
}

impl From<ValidationError> for LangError {
    fn from(err: ValidationError) -> Self {
        LangError::new(LangErrorKind::Validation(Box::new(err)))
    }
}

impl From<LoweringError> for LangError {
    fn from(err: LoweringError) -> Self {
        LangError::new(LangErrorKind::Lowering(Box::new(err)))
    }
}

impl From<BatchingError> for LangError {
    fn from(err: BatchingError) -> Self {
        LangError::new(LangErrorKind::Batching(Box::new(err)))
    }
}
