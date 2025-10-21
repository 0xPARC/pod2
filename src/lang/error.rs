use thiserror::Error;

use crate::{
    frontend,
    lang::{frontend_ast::Span, parser::ParseError},
    middleware,
};

#[derive(Error, Debug)]
pub enum LangError {
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

    #[error("Batch not found: {id}")]
    BatchNotFound { id: String, span: Option<Span> },

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

    #[error("Invalid argument type for {predicate}: anchored keys not allowed")]
    InvalidArgumentType {
        predicate: String,
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
}

/// Lowering errors from frontend AST lowering to middleware
#[derive(Debug, thiserror::Error)]
pub enum LoweringError {
    #[error("Too many custom predicates: {count} exceeds limit of {max} (batch: {batch_name})")]
    TooManyPredicates {
        batch_name: String,
        count: usize,
        max: usize,
    },

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

    #[error("Cannot lower document with validation errors")]
    ValidationErrors,
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

    #[error("Too many total arguments in predicate '{predicate}': {count} exceeds max of {max_allowed}. {message}")]
    TooManyTotalArgs {
        predicate: String,
        count: usize,
        max_allowed: usize,
        message: String,
    },

    #[error("Too many total arguments in chain link {link_index}: {total_count} exceeds max of {max_allowed}")]
    TooManyTotalArgsInChainLink {
        link_index: usize,
        total_count: usize,
        max_allowed: usize,
    },

    #[error("Too many public arguments at split boundary in predicate '{predicate}': {count} exceeds max of {max_allowed}")]
    TooManyPublicArgsAtSplit {
        predicate: String,
        count: usize,
        max_allowed: usize,
    },

    #[error("Too many predicates in chain for '{predicate}': {count} exceeds batch limit of {max_allowed}")]
    TooManyPredicatesInChain {
        predicate: String,
        count: usize,
        max_allowed: usize,
    },
}

impl From<ParseError> for LangError {
    fn from(err: ParseError) -> Self {
        LangError::Parse(Box::new(err))
    }
}

impl From<middleware::Error> for LangError {
    fn from(err: middleware::Error) -> Self {
        LangError::Middleware(Box::new(err))
    }
}

impl From<ValidationError> for LangError {
    fn from(err: ValidationError) -> Self {
        LangError::Validation(Box::new(err))
    }
}

impl From<LoweringError> for LangError {
    fn from(err: LoweringError) -> Self {
        LangError::Lowering(Box::new(err))
    }
}
