use thiserror::Error;

use crate::{frontend, lang::parser::ParseError, middleware};

#[derive(Error, Debug)]
pub enum LangError {
    #[error("Parsing failed: {0}")]
    Parse(Box<ParseError>),

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
    #[error("Invalid literal format for {kind}: '{value}' at {span:?}")]
    InvalidLiteralFormat {
        kind: String,
        value: String,
        span: Option<(usize, usize)>,
    },
    #[error("Frontend error: {0}")]
    Frontend(#[from] frontend::Error),
}

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
