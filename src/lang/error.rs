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

    #[error("Batching error: {0}")]
    Batching(Box<BatchingError>),
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

/// Context information for split boundary failures
#[derive(Debug, Clone)]
pub struct SplitContext {
    /// Index of the split boundary (0-based)
    pub split_index: usize,
    /// Range of statement indices in the segment before the split
    pub statement_range: (usize, usize),
    /// Public arguments coming into this segment
    pub incoming_public: Vec<String>,
    /// Wildcards that cross this boundary (need to be promoted)
    pub crossing_wildcards: Vec<String>,
    /// Total public arguments needed (incoming + crossing)
    pub total_public: usize,
}

/// Suggestions for refactoring predicates that fail to split
#[derive(Debug, Clone)]
pub enum RefactorSuggestion {
    /// A wildcard is used across too many statements
    ReduceWildcardSpan {
        wildcard: String,
        first_use: usize,
        last_use: usize,
        span: usize,
    },
    /// Multiple wildcards should be grouped together
    GroupWildcardUsages { wildcards: Vec<String> },
}

impl RefactorSuggestion {
    pub fn format(&self) -> String {
        match self {
            RefactorSuggestion::ReduceWildcardSpan {
                wildcard,
                first_use,
                last_use,
                span,
            } => {
                format!(
                    "Wildcard '{}'  is used across {} statements (statements {}-{}).\n\
                     Consider grouping all '{}' operations together, or split the wildcard\n\
                     into separate early/late variables.",
                    wildcard, span, first_use, last_use, wildcard
                )
            }
            RefactorSuggestion::GroupWildcardUsages { wildcards } => {
                format!(
                    "Group operations for wildcards: {}\n\
                     These wildcards are used across multiple segments. Try to complete\n\
                     all operations for each wildcard before moving to the next.",
                    wildcards.join(", ")
                )
            }
        }
    }
}

/// Formats a detailed error message for TooManyPublicArgsAtSplit
fn format_public_args_at_split_error(
    predicate: &str,
    context: &SplitContext,
    max_allowed: usize,
    suggestion: &Option<Box<RefactorSuggestion>>,
) -> String {
    let mut msg = format!(
        "Too many public arguments at split boundary {} in predicate '{}':\n",
        context.split_index, predicate
    );

    msg.push_str(&format!(
        "  {} incoming public + {} crossing wildcards = {} total (exceeds max of {})\n",
        context.incoming_public.len(),
        context.crossing_wildcards.len(),
        context.total_public,
        max_allowed
    ));

    msg.push_str(&format!(
        "  Statements {}-{} in this segment\n",
        context.statement_range.0, context.statement_range.1
    ));

    if !context.incoming_public.is_empty() {
        msg.push_str(&format!(
            "  Incoming public args: {}\n",
            context.incoming_public.join(", ")
        ));
    }

    if !context.crossing_wildcards.is_empty() {
        msg.push_str(&format!(
            "  Wildcards crossing this boundary: {}\n",
            context.crossing_wildcards.join(", ")
        ));
    }

    if let Some(suggestion) = suggestion {
        msg.push_str("\nSuggestion:\n");
        msg.push_str(&suggestion.format());
    }

    msg
}

/// Batching errors from multi-batch packing
#[derive(Debug, thiserror::Error)]
pub enum BatchingError {
    #[error("Forward cross-batch reference: predicate '{caller}' (batch {caller_batch}) calls '{callee}' (batch {callee_batch}). Move '{callee}' earlier or '{caller}' later.")]
    ForwardCrossBatchReference {
        caller: String,
        caller_batch: usize,
        callee: String,
        callee_batch: usize,
    },

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

    #[error("Too many total arguments in predicate '{predicate}': {count} exceeds max of {max_allowed}. {message}")]
    TooManyTotalArgs {
        predicate: String,
        count: usize,
        max_allowed: usize,
        message: String,
    },

    #[error("Too many total arguments in chain link {link_index} of predicate '{predicate}': {public_count} public + {private_count} private = {total_count} total (exceeds max of {max_allowed})")]
    TooManyTotalArgsInChainLink {
        predicate: String,
        link_index: usize,
        public_count: usize,
        private_count: usize,
        total_count: usize,
        max_allowed: usize,
    },

    #[error("{}", format_public_args_at_split_error(.predicate, .context, *.max_allowed, .suggestion))]
    TooManyPublicArgsAtSplit {
        predicate: String,
        context: Box<SplitContext>,
        max_allowed: usize,
        suggestion: Option<Box<RefactorSuggestion>>,
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

impl From<BatchingError> for LangError {
    fn from(err: BatchingError) -> Self {
        LangError::Batching(Box::new(err))
    }
}
