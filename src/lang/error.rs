use thiserror::Error;

use crate::{
    lang::{ast::AstBuildError, parser::ParseError, processor::ProcessorError},
    middleware,
};

#[derive(Error, Debug)]
pub enum LangError {
    #[error("Parsing failed: {0}")]
    Parse(#[from] Box<ParseError>),

    #[error("AST building failed: {0}")]
    AstBuild(#[from] Box<AstBuildError>),

    #[error("AST processing failed: {0}")]
    Processing(String),

    #[error("AST processing error: {0}")]
    Processor(#[from] Box<ProcessorError>),

    #[error("Middleware error during processing: {0}")]
    Middleware(#[from] Box<middleware::Error>),
}

// We need to manually implement From for the boxed types because
// the `?` operator needs to automatically convert ParseError to Box<ParseError> etc.
// `thiserror`'s `#[from]` handles the Box<Error> -> LangError part.

impl From<ParseError> for LangError {
    fn from(err: ParseError) -> Self {
        LangError::Parse(Box::new(err))
    }
}

impl From<AstBuildError> for LangError {
    fn from(err: AstBuildError) -> Self {
        LangError::AstBuild(Box::new(err))
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
