use thiserror::Error;

use super::Rule;
use crate::{frontend, lang::parser::ParseError, middleware};

#[derive(Error, Debug)]
pub enum LangError {
    #[error("Parsing failed: {0}")]
    Parse(Box<ParseError>),

    #[error("Processing failed: {0}")]
    Processing(String),

    #[error("AST processing error: {0}")]
    Processor(Box<ProcessorError>),

    #[error("Middleware error during processing: {0}")]
    Middleware(Box<middleware::Error>),

    #[error("Frontend error: {0}")]
    Frontend(Box<frontend::Error>),
}

/// Errors that can occur during the processing of Podlog Pest tree into middleware structures.
#[derive(thiserror::Error, Debug)]
pub enum ProcessorError {
    #[error("Semantic error: {message} at {span:?}")]
    Semantic {
        message: String,
        span: Option<(usize, usize)>,
    },
    #[error("Undefined identifier: '{name}' at {span:?}")]
    UndefinedIdentifier {
        name: String,
        span: Option<(usize, usize)>,
    },
    #[error("Duplicate definition: '{name}' at {span:?}")]
    DuplicateDefinition {
        name: String,
        span: Option<(usize, usize)>,
    },
    #[error("Duplicate wildcard: ?{name} in scope at {span:?}")]
    DuplicateWildcard {
        name: String,
        span: Option<(usize, usize)>,
    },
    #[error("Type error: expected {expected}, found {found} for '{item}' at {span:?}")]
    TypeError {
        expected: String,
        found: String,
        item: String,
        span: Option<(usize, usize)>,
    },
    #[error(
        "Invalid argument count for '{predicate}': expected {expected}, found {found} at {span:?}"
    )]
    ArgumentCountMismatch {
        predicate: String,
        expected: usize,
        found: usize,
        span: Option<(usize, usize)>,
    },
    #[error("Multiple REQUEST definitions found. Only one is allowed. First at {first_span:?}, second at {second_span:?}")]
    MultipleRequestDefinitions {
        first_span: Option<(usize, usize)>,
        second_span: Option<(usize, usize)>,
    },
    #[error("Internal processing error: {0}")]
    Internal(String),
    #[error("Middleware error: {0}")]
    Middleware(middleware::Error),
    #[error("Undefined wildcard: '?{name}' at {span:?}")]
    UndefinedWildcard {
        name: String,
        span: Option<(usize, usize)>,
    },
    #[error("Pest rule mismatch: expected {expected_rule:?}, found {found_rule:?} for '{context}' at {span:?}")]
    RuleMismatch {
        expected_rule: Rule,
        found_rule: Rule,
        context: String,
        span: Option<(usize, usize)>,
    },
    #[error("Missing element: expected {element_type} for '{context}' at {span:?}")]
    MissingElement {
        element_type: String,
        context: String,
        span: Option<(usize, usize)>,
    },
    #[error("Invalid literal format for {kind}: '{value}' at {span:?}")]
    InvalidLiteralFormat {
        kind: String,
        value: String,
        span: Option<(usize, usize)>,
    },
    #[error(
        "Hex literal '0x{value}' has invalid length {len} (must be even and >= 2) at {span:?}"
    )]
    InvalidHexLength {
        value: String,
        len: usize,
        span: Option<(usize, usize)>,
    },
    #[error("Frontend error: {0}")]
    Frontend(frontend::Error),
}

impl From<frontend::Error> for ProcessorError {
    fn from(err: frontend::Error) -> Self {
        ProcessorError::Frontend(err)
    }
}

// We need to manually implement From for the boxed types because
// the `?` operator needs to automatically convert ParseError to Box<ParseError> etc.
// `thiserror`'s `#[from]` handles the Box<Error> -> LangError part.

impl From<ParseError> for LangError {
    fn from(err: ParseError) -> Self {
        LangError::Parse(Box::new(err))
    }
}

impl From<ProcessorError> for LangError {
    fn from(err: ProcessorError) -> Self {
        LangError::Processor(Box::new(err))
    }
}

impl From<middleware::Error> for LangError {
    fn from(err: middleware::Error) -> Self {
        LangError::Middleware(Box::new(err))
    }
}

impl From<frontend::Error> for LangError {
    fn from(err: frontend::Error) -> Self {
        LangError::Frontend(Box::new(err))
    }
}
