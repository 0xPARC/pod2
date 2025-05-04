use std::collections::HashMap;

use pest::iterators::{Pair, Pairs};
use thiserror::Error;

use crate::lang::parser::Rule;

// --- Error Type ---
#[derive(Error, Debug, Clone, PartialEq)]
pub enum AstBuildError {
    #[error("AST build failed at {span:?}: {message}")]
    Generic {
        message: String,
        span: Option<(usize, usize)>,
    },
    #[error("Unexpected rule {rule:?} at {span:?}")]
    UnexpectedRule {
        rule: Rule,
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
    #[error("Internal error during AST build: {0}")]
    Internal(String), // For unexpected logic errors
}

// Helper to get span from a Pair
fn get_span(pair: &Pair<Rule>) -> (usize, usize) {
    let span = pair.as_span();
    (span.start(), span.end())
}

// Helper macro for errors with spans
macro_rules! ast_err {
    (Generic, $pair:expr, $($arg:tt)*) => {
        AstBuildError::Generic {
            message: format!($($arg)*),
            span: Some(get_span($pair)),
        }
    };
    (UnexpectedRule, $pair:expr) => {
         AstBuildError::UnexpectedRule {
            rule: $pair.as_rule(),
            span: Some(get_span($pair)),
        }
    };
     (InvalidLiteralFormat, $kind:expr, $pair:expr) => {
         AstBuildError::InvalidLiteralFormat {
            kind: $kind.to_string(),
            value: $pair.as_str().to_string(),
            span: Some(get_span($pair)),
        }
    };
     (InvalidHexLength, $pair:expr, $len: expr) => {
        AstBuildError::InvalidHexLength {
            value: $pair.as_str().strip_prefix("0x").unwrap_or("").to_string(),
            len: $len,
            span: Some(get_span($pair)),
        }
    };
}

// --- Literals ---

#[derive(Debug, Clone, PartialEq)]
pub enum Literal {
    Int(i64),
    Bool(bool),
    Raw(Vec<u8>), // Store as bytes
    String(String),
    Array(Vec<Literal>),
    Set(Vec<Literal>), // Note: Processor will need to validate uniqueness if required
    Dict(HashMap<String, Literal>), // Keys are always strings in the AST
}

// --- Basic Identifiers ---

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Identifier(pub String); // For predicate names

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Variable(pub String); // For ?Var names

// --- Arguments & Keys ---

#[derive(Debug, Clone, PartialEq)]
pub enum AnchoredKeyKey {
    LiteralString(String),
    Variable(Variable),
}

#[derive(Debug, Clone, PartialEq)]
pub struct AnchoredKey {
    pub pod_var: Variable,
    pub key: AnchoredKeyKey,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Argument {
    Literal(Literal),
    Variable(Variable),
    AnchoredKey(AnchoredKey),
}

// --- Statements ---

// Corresponds to middleware::NativePredicate, but potentially different args for AST
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum NativePredicate {
    ValueOf,
    Equal,
    NotEqual,
    Gt,
    Lt,
    Contains,
    NotContains,
    SumOf,
    ProductOf,
    MaxOf,
}

#[derive(Debug, Clone, PartialEq)]
pub struct NativePredicateCall {
    pub predicate: NativePredicate,
    pub args: Vec<Argument>, // Arguments during parsing stage
}

#[derive(Debug, Clone, PartialEq)]
pub struct CustomPredicateCall {
    pub name: Identifier,
    pub args: Vec<Argument>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Statement {
    Native(NativePredicateCall),
    Custom(CustomPredicateCall),
}

// --- Definitions ---

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CustomPredicateType {
    And,
    Or,
}

#[derive(Debug, Clone, PartialEq)]
pub struct CustomPredicateDefinition {
    pub name: Identifier,
    pub public_args: Vec<Variable>,
    pub private_args: Vec<Variable>, // Order matters
    pub type_: CustomPredicateType,
    pub statements: Vec<Statement>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct RequestDefinition {
    pub statements: Vec<Statement>,
}

// --- Top Level ---

#[derive(Debug, Clone, PartialEq)]
pub enum TopLevelDefinition {
    CustomPredicate(CustomPredicateDefinition),
    Request(RequestDefinition),
}

#[derive(Debug, Clone, PartialEq, Default)]
pub struct Document {
    pub definitions: Vec<TopLevelDefinition>,
}

// --- AST Building Logic ---

pub fn build_ast(pairs: Pairs<'_, Rule>) -> Result<Document, AstBuildError> {
    let mut definitions = Vec::new();

    // Iterate directly over the inner pairs of the document rule if the top pair is `document`
    let relevant_pairs = if pairs.peek().is_some_and(|p| p.as_rule() == Rule::document) {
        // If the first pair is the document rule itself, get its inner pairs
        pairs.into_iter().next().unwrap().into_inner()
    } else {
        // Otherwise, assume pairs are already the inner content
        pairs
    };

    for pair in relevant_pairs {
        match pair.as_rule() {
            // Match specific definition types directly
            Rule::custom_predicate_def => {
                definitions.push(TopLevelDefinition::CustomPredicate(build_custom_predicate(
                    pair,
                )?));
            }
            Rule::request_def => {
                definitions.push(TopLevelDefinition::Request(build_request(pair)?));
            }
            Rule::EOI => break,                    // End of input
            Rule::COMMENT | Rule::WHITESPACE => {} // Ignore comments/whitespace
            _ => return Err(ast_err!(UnexpectedRule, &pair)),
        }
    }

    Ok(Document { definitions })
}

fn build_custom_predicate(
    pair: Pair<'_, Rule>,
) -> Result<CustomPredicateDefinition, AstBuildError> {
    let mut name_opt: Option<Identifier> = None;
    let mut public_args: Vec<Variable> = Vec::new();
    let mut type_opt: Option<CustomPredicateType> = None;
    let mut private_args: Vec<Variable> = Vec::new();
    let mut statements: Vec<Statement> = Vec::new();

    for inner_pair in pair.into_inner() {
        match inner_pair.as_rule() {
            Rule::identifier => {
                // This should no longer happen for the predicate name itself
                // If it occurs elsewhere unexpectedly, it might indicate a grammar issue
                // or an issue in how this function is called.
                // For now, let's treat it as an internal error if encountered here.
                return Err(AstBuildError::Internal(format!(
                    "Unexpected 'identifier' rule ({}) encountered directly within custom_predicate_def. Expected 'predicate_identifier'.",
                    inner_pair.as_str()
                )));
            }
            Rule::predicate_identifier => {
                // Correctly handle the predicate name identifier
                if name_opt.is_some() {
                    // Avoid overwriting if somehow matched twice
                    return Err(AstBuildError::Internal(
                        "Found multiple predicate names".to_string(),
                    ));
                }
                // Build the identifier directly from the predicate_identifier pair's string content
                name_opt = Some(build_identifier(inner_pair)?);
            }
            Rule::def_arg_list => {
                // Check if it's for public or private args based on context (hacky, better grammar might help)
                // For now, assume first def_arg_list is public, second is private if seen after private_kw
                if type_opt.is_none() {
                    // Before AND/OR = public
                    public_args = inner_pair
                        .into_inner()
                        .map(|p| build_identifier(p).map(|ident| Variable(ident.0)))
                        .collect::<Result<Vec<Variable>, _>>()?;
                } else {
                    // After AND/OR = must be inside private_args_def
                    // This case handled by Rule::private_args_def inner iteration
                    return Err(ast_err!(UnexpectedRule, &inner_pair));
                }
            }
            Rule::private_args_def => {
                private_args = inner_pair
                    .into_inner() // Get inner of private_args_def
                    .find(|p| p.as_rule() == Rule::def_arg_list) // Find the def_arg_list within it
                    .map_or(Ok(Vec::new()), |arg_list_pair| {
                        arg_list_pair
                            .into_inner()
                            .map(|p| build_identifier(p).map(|ident| Variable(ident.0)))
                            .collect::<Result<Vec<Variable>, _>>()
                    })?;
            }
            Rule::statement_list => {
                statements = inner_pair
                    .into_inner()
                    .map(build_statement)
                    .collect::<Result<_, _>>()?;
            }
            // Match the new conjunction_type rule
            Rule::conjunction_type => {
                if type_opt.is_some() {
                    return Err(AstBuildError::Internal(
                        "Found multiple conjunction types".to_string(),
                    ));
                }
                type_opt = match inner_pair.as_str() {
                    "AND" => Some(CustomPredicateType::And),
                    "OR" => Some(CustomPredicateType::Or),
                    _ => {
                        return Err(AstBuildError::Internal(
                            "Unexpected content for conjunction_type".to_string(),
                        ))
                    } // Should not happen
                };
            }
            // Ignore known syntax/comments/whitespace, error on others
            Rule::COMMENT | Rule::WHITESPACE => { /* Ignore */ }
            _ if ["=", "(", ")", "private"].contains(&inner_pair.as_str().trim()) => { /* Ignore */
            }
            _ => {
                // If it's not a handled rule or known syntax/ignored rules, it's unexpected
                return Err(ast_err!(UnexpectedRule, &inner_pair));
            }
        }
    }

    let name = name_opt.ok_or_else(|| {
        AstBuildError::Internal("Missing predicate name in parsed pairs".to_string())
    })?;
    let type_ = type_opt.ok_or_else(|| {
        AstBuildError::Internal("Missing predicate type (AND/OR) in parsed pairs".to_string())
    })?;

    Ok(CustomPredicateDefinition {
        name,
        public_args,
        private_args,
        type_,
        statements,
    })
}

fn build_request(pair: Pair<'_, Rule>) -> Result<RequestDefinition, AstBuildError> {
    let maybe_statement_list = pair
        .into_inner()
        .find(|p| p.as_rule() == Rule::statement_list);
    // .ok_or_else(|| {
    //     AstBuildError::Internal("Missing statement_list in request_def".to_string())
    // })?;

    let statements = match maybe_statement_list {
        Some(statement_list) => statement_list
            .into_inner()
            .filter(|p| p.as_rule() == Rule::statement)
            .map(build_statement)
            .collect::<Result<_, _>>()?,
        None => Vec::new(), // Handle case where statement_list is not present
    };

    Ok(RequestDefinition { statements })
}

fn build_statement(pair: Pair<'_, Rule>) -> Result<Statement, AstBuildError> {
    // The statement rule directly contains one of the specific stmt rules or a custom call
    let inner_pair = pair
        .into_inner()
        .next()
        .ok_or_else(|| AstBuildError::Internal("Empty statement".to_string()))?;
    match inner_pair.as_rule() {
        // Match specific native statement rules
        Rule::value_of_stmt
        | Rule::equal_stmt
        | Rule::not_equal_stmt
        | Rule::gt_stmt
        | Rule::lt_stmt
        | Rule::contains_stmt
        | Rule::not_contains_stmt
        | Rule::sum_of_stmt
        | Rule::product_of_stmt
        | Rule::max_of_stmt => Ok(Statement::Native(build_native_call(inner_pair)?)),
        Rule::custom_predicate_call => Ok(Statement::Custom(build_custom_call(inner_pair)?)),
        _ => Err(ast_err!(UnexpectedRule, &inner_pair)),
    }
}

fn build_native_call(pair: Pair<'_, Rule>) -> Result<NativePredicateCall, AstBuildError> {
    // The specific rule tells us the predicate type
    let predicate = match pair.as_rule() {
        Rule::value_of_stmt => NativePredicate::ValueOf,
        Rule::equal_stmt => NativePredicate::Equal,
        Rule::not_equal_stmt => NativePredicate::NotEqual,
        Rule::gt_stmt => NativePredicate::Gt,
        Rule::lt_stmt => NativePredicate::Lt,
        Rule::contains_stmt => NativePredicate::Contains,
        Rule::not_contains_stmt => NativePredicate::NotContains,
        Rule::sum_of_stmt => NativePredicate::SumOf,
        Rule::product_of_stmt => NativePredicate::ProductOf,
        Rule::max_of_stmt => NativePredicate::MaxOf,
        // This function should only be called with one of the above rules
        _ => return Err(ast_err!(UnexpectedRule, &pair)),
    };

    // The inner pairs are the arguments
    let args = match predicate {
        NativePredicate::ValueOf => {
            // Get an iterator for the inner pairs
            let mut inner_pairs = pair.into_inner();

            let ak_pair = inner_pairs
                .next()
                .ok_or_else(|| AstBuildError::Internal("Missing ValueOf arg 1".to_string()))?;
            let lit_pair = inner_pairs // Use the *same* iterator
                .next()
                .ok_or_else(|| AstBuildError::Internal("Missing ValueOf arg 2".to_string()))?;

            // Perform rule checks after getting the pairs
            if ak_pair.as_rule() != Rule::anchored_key {
                return Err(AstBuildError::Internal(format!(
                    "Invalid arg type for ValueOf arg 1: expected anchored_key, got {:?}",
                    ak_pair.as_rule()
                )));
            }
            if lit_pair.as_rule() != Rule::literal_value {
                return Err(AstBuildError::Internal(format!(
                    "Invalid arg type for ValueOf arg 2: expected literal_value, got {:?}",
                    lit_pair.as_rule()
                )));
            }

            vec![
                Argument::AnchoredKey(build_anchored_key(ak_pair)?),
                Argument::Literal(build_literal(lit_pair)?),
            ]
        }
        _ => pair
            .into_inner()
            // Need to handle argument types based on the specific predicate
            .map(|arg_pair| match (predicate.clone(), arg_pair.as_rule()) {
                // Most predicates take AnchoredKey args
                (
                    NativePredicate::Equal
                    | NativePredicate::NotEqual
                    | NativePredicate::Gt
                    | NativePredicate::Lt
                    | NativePredicate::Contains
                    | NativePredicate::NotContains
                    | NativePredicate::SumOf
                    | NativePredicate::ProductOf
                    | NativePredicate::MaxOf,
                    Rule::anchored_key,
                ) => Ok(Argument::AnchoredKey(build_anchored_key(arg_pair)?)),

                // Predicates allowing CallArg (which includes literals/vars/AK) as second arg
                (
                    NativePredicate::Equal
                    | NativePredicate::NotEqual
                    | NativePredicate::Gt
                    | NativePredicate::Lt,
                    Rule::call_arg,
                ) => build_argument(arg_pair), // Call the existing argument builder

                // Other combinations are errors for native calls
                _ => Err(ast_err!(UnexpectedRule, &arg_pair)),
            })
            .collect::<Result<_, _>>()?,
    };

    Ok(NativePredicateCall { predicate, args })
}

fn build_custom_call(pair: Pair<'_, Rule>) -> Result<CustomPredicateCall, AstBuildError> {
    let mut inner = pair.into_inner();
    let name = build_identifier(inner.next().ok_or_else(|| {
        AstBuildError::Internal("Missing custom predicate call name".to_string())
    })?)?;
    let args_pair = inner.next();

    let args = match args_pair {
        Some(p) => p
            .into_inner()
            .map(build_argument)
            .collect::<Result<_, _>>()?,
        None => Vec::new(),
    };

    Ok(CustomPredicateCall { name, args })
}

fn build_argument(pair: Pair<'_, Rule>) -> Result<Argument, AstBuildError> {
    // The call_arg rule directly contains one of the argument types
    let inner_pair = pair
        .into_inner()
        .next()
        .ok_or_else(|| AstBuildError::Internal("Empty call_arg".to_string()))?;
    match inner_pair.as_rule() {
        Rule::literal_value => Ok(Argument::Literal(build_literal(inner_pair)?)), // Use literal_value
        Rule::variable => Ok(Argument::Variable(build_variable(&inner_pair)?)),
        Rule::anchored_key => Ok(Argument::AnchoredKey(build_anchored_key(inner_pair)?)),
        _ => Err(ast_err!(UnexpectedRule, &inner_pair)),
    }
}

fn build_anchored_key(pair: Pair<'_, Rule>) -> Result<AnchoredKey, AstBuildError> {
    let mut inner = pair.into_inner();
    let pod_var = build_variable(&inner.next().ok_or_else(|| {
        AstBuildError::Internal("Missing pod variable in anchored key".to_string())
    })?)?;
    let key_pair = inner
        .next()
        .ok_or_else(|| AstBuildError::Internal("Missing key in anchored key".to_string()))?;
    let key = build_anchored_key_key(&key_pair)?;
    Ok(AnchoredKey { pod_var, key })
}

fn build_anchored_key_key(pair: &Pair<'_, Rule>) -> Result<AnchoredKeyKey, AstBuildError> {
    match pair.as_rule() {
        Rule::literal_string => Ok(AnchoredKeyKey::LiteralString(parse_string_literal(pair)?)),
        Rule::variable => Ok(AnchoredKeyKey::Variable(build_variable(pair)?)),
        _ => Err(ast_err!(UnexpectedRule, pair)),
    }
}

fn build_variable(pair: &Pair<'_, Rule>) -> Result<Variable, AstBuildError> {
    // The variable rule is atomic (@), so we get the full string `?Name`
    // and strip the prefix.
    let var_str = pair.as_str();
    let name = var_str.strip_prefix("?").ok_or_else(|| {
        ast_err!(
            Generic,
            pair,
            "Expected variable '{}' to start with '?'",
            var_str
        )
    })?;
    // Basic validation: ensure it's not just "?"
    if name.is_empty() {
        return Err(ast_err!(
            Generic,
            pair,
            "Variable name cannot be empty after '?'"
        ));
    }
    // You might add identifier validation here if needed (e.g., match identifier rule regex)
    Ok(Variable(name.to_string()))
}

fn build_identifier(pair: Pair<'_, Rule>) -> Result<Identifier, AstBuildError> {
    Ok(Identifier(pair.as_str().to_string()))
}

fn build_literal(pair: Pair<'_, Rule>) -> Result<Literal, AstBuildError> {
    // Expect pair rule to be literal_value
    if pair.as_rule() != Rule::literal_value {
        return Err(ast_err!(UnexpectedRule, &pair));
    }
    let inner_pair = pair
        .into_inner()
        .next()
        .ok_or_else(|| AstBuildError::Internal("Empty literal_value".to_string()))?;
    match inner_pair.as_rule() {
        Rule::literal_int => {
            let val = inner_pair
                .as_str()
                .parse::<i64>()
                .map_err(|_| ast_err!(InvalidLiteralFormat, "int", &inner_pair))?;
            Ok(Literal::Int(val))
        }
        Rule::literal_bool => {
            let val = inner_pair
                .as_str()
                .parse::<bool>()
                .map_err(|_| ast_err!(InvalidLiteralFormat, "bool", &inner_pair))?;
            Ok(Literal::Bool(val))
        }
        Rule::literal_raw => {
            let hex_str = inner_pair.as_str().strip_prefix("0x").unwrap_or("");
            let len = hex_str.len();
            if len < 2 || len % 2 != 0 {
                return Err(ast_err!(InvalidHexLength, &inner_pair, len));
            }
            let bytes = hex::decode(hex_str)
                .map_err(|_| ast_err!(InvalidLiteralFormat, "raw hex", &inner_pair))?;
            Ok(Literal::Raw(bytes))
        }
        Rule::literal_string => Ok(Literal::String(parse_string_literal(&inner_pair)?)),
        Rule::literal_array => {
            // The inner of literal_array can be empty or contain literal_values
            let elements = inner_pair
                .into_inner()
                .map(build_literal)
                .collect::<Result<_, _>>()?;
            Ok(Literal::Array(elements))
        }
        Rule::literal_set => {
            // The inner of literal_set can be empty or contain literal_values
            let elements = inner_pair
                .into_inner()
                .map(build_literal)
                .collect::<Result<_, _>>()?;
            Ok(Literal::Set(elements))
        }
        Rule::literal_dict => {
            // The inner of literal_dict can be empty or contain dict_pairs
            let pairs = inner_pair
                .into_inner()
                .map(|dict_entry_pair| {
                    // dict_entry_pair rule is dict_pair
                    let mut entry_inner = dict_entry_pair.into_inner();
                    // First inner is literal_string
                    let key_pair = entry_inner
                        .next()
                        .ok_or_else(|| AstBuildError::Internal("Missing dict key".to_string()))?;
                    // Second inner is literal_value
                    let val_pair = entry_inner
                        .next()
                        .ok_or_else(|| AstBuildError::Internal("Missing dict value".to_string()))?;
                    let key = parse_string_literal(&key_pair)?;
                    let val = build_literal(val_pair)?; // build_literal expects literal_value
                    Ok((key, val))
                })
                .collect::<Result<HashMap<_, _>, _>>()?;
            Ok(Literal::Dict(pairs))
        }
        _ => Err(ast_err!(UnexpectedRule, &inner_pair)),
    }
}

fn parse_string_literal(pair: &Pair<'_, Rule>) -> Result<String, AstBuildError> {
    if pair.as_rule() != Rule::literal_string {
        return Err(ast_err!(UnexpectedRule, pair));
    }

    // Get the inner pair, which should be the atomic `inner` rule
    let inner_pair = pair.clone().into_inner().next().ok_or_else(|| {
        ast_err!(
            Generic,
            pair,
            "Internal error: literal_string lacks inner pair"
        )
    })?;

    if inner_pair.as_rule() != Rule::inner {
        // This shouldn't happen if the grammar is correct
        return Err(ast_err!(
            Generic,
            &inner_pair,
            "Internal error: Expected inner rule inside literal_string"
        ));
    }

    let raw_content = inner_pair.as_str();
    let mut result = String::with_capacity(raw_content.len());
    let mut chars = raw_content.chars().peekable();

    while let Some(c) = chars.next() {
        if c == '\\' {
            // Escape sequence
            match chars.next() {
                Some('"') => result.push('"'),
                Some('\\') => result.push('\\'),
                Some('/') => result.push('/'), // Note: JSON technically allows unescaped /
                Some('b') => result.push('\x08'),
                Some('f') => result.push('\x0C'),
                Some('n') => result.push('\n'),
                Some('r') => result.push('\r'),
                Some('t') => result.push('\t'),
                Some('u') => {
                    // Expect 4 hex digits
                    let mut hex_code = String::with_capacity(4);
                    for _ in 0..4 {
                        hex_code.push(chars.next().ok_or_else(|| {
                            ast_err!(
                                Generic,
                                &inner_pair,
                                "Malformed Unicode escape: incomplete sequence"
                            )
                        })?);
                    }
                    let char_code = u32::from_str_radix(&hex_code, 16).map_err(|_| {
                        ast_err!(
                            Generic,
                            &inner_pair,
                            "Malformed Unicode escape: invalid hex digits"
                        )
                    })?;
                    result.push(std::char::from_u32(char_code).ok_or_else(|| {
                        ast_err!(
                            Generic,
                            &inner_pair,
                            "Malformed Unicode escape: invalid code point"
                        )
                    })?);
                }
                Some(other) => {
                    // Invalid escape character
                    return Err(ast_err!(
                        Generic,
                        &inner_pair,
                        "Invalid escape character: {}",
                        other
                    ));
                }
                None => {
                    // Dangling backslash at end of string
                    return Err(ast_err!(
                        Generic,
                        &inner_pair,
                        "String ends with backslash escape"
                    ));
                }
            }
        } else {
            // Regular character
            result.push(c);
        }
    }

    Ok(result)
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap; // Add this import

    use pest::Parser;

    use super::*; // Import items from parent module (ast)
    use crate::lang::parser::{PodlogParser, Rule}; // Import parser and Rule

    // Helper to parse a string with a specific rule and expect success
    fn parse_rule(rule: Rule, input: &str) -> Result<Pair<'_, Rule>, String> {
        // Map the base rule to its corresponding anchored test rule
        let test_rule = match rule {
            Rule::identifier => Rule::test_identifier,
            Rule::variable => Rule::test_variable,
            Rule::literal_int => Rule::test_literal_int,
            Rule::literal_raw => Rule::test_literal_raw,
            // Add other mappings here if needed for tests
            // For rules without a specific test rule, maybe just use the original?
            // Or panic if a test requires an anchored version that doesn't exist.
            _ => rule, // Fallback to original rule, might need adjustment
                       // Consider panicking or returning Err for unhandled test rules
                       // panic!("No corresponding test rule defined for {:?}", rule);
        };

        match PodlogParser::parse(test_rule, input) {
            Ok(mut pairs) => {
                // The test rules should contain the actual rule we care about
                let test_pair = pairs
                    .next()
                    .ok_or_else(|| format!("Parser OK but no pair for {:?}", test_rule))?;
                // Dig into the test rule to get the pair for the actual rule
                let rule_inside_test = test_pair.as_rule(); // Store rule before moving test_pair
                if test_rule == rule {
                    Ok(test_pair)
                } else {
                    test_pair.into_inner().next().ok_or_else(|| {
                        format!(
                            "No inner pair found within {:?} for rule {:?}",
                            rule_inside_test, rule
                        )
                    })
                }
            }
            Err(e) => Err(format!(
                "Parser failed for input '{}' with rule {:?}: {}",
                input, test_rule, e
            )),
        }
    }

    // Helper function to parse a string and build a literal
    fn build_test_literal(input: &str) -> Result<Literal, AstBuildError> {
        // Need to wrap the literal rule in literal_value for build_literal
        match PodlogParser::parse(Rule::test_literal_value, input) {
            // Use the anchored test rule
            Ok(mut pairs) => {
                let test_pair = pairs.next().ok_or_else(|| {
                    AstBuildError::Internal(
                        "Parser returned OK but no pair for test_literal_value".to_string(),
                    )
                })?;
                // The test_literal_value rule contains literal_value as its inner rule
                let literal_value_pair = test_pair.into_inner().next().ok_or_else(|| {
                    AstBuildError::Internal(
                        "No inner literal_value found in test_literal_value".to_string(),
                    )
                })?;

                // Check if the inner pair is the actual literal or literal_value itself
                // The pair returned by parsing literal_value should *always* be literal_value
                if literal_value_pair.as_rule() == Rule::literal_value {
                    build_literal(literal_value_pair)
                } else {
                    // This case indicates a parser/grammar inconsistency
                    Err(ast_err!(UnexpectedRule, &literal_value_pair))
                }
            }
            Err(e) => Err(AstBuildError::Internal(format!(
                "Parser failed for literal input '{}': {}",
                input, e
            ))),
        }
    }

    #[test]
    fn test_build_literals() {
        // Int
        assert_eq!(
            build_test_literal("123"),
            Ok(Literal::Int(123)),
            "Test Int Positive"
        );
        assert_eq!(
            build_test_literal("-45"),
            Ok(Literal::Int(-45)),
            "Test Int Negative"
        );
        assert_eq!(
            build_test_literal("0"),
            Ok(Literal::Int(0)),
            "Test Int Zero"
        );
        // Parser should fail for floats, resulting in Internal error from build_test_literal
        assert!(
            matches!(build_test_literal("1.23"), Err(AstBuildError::Internal(_))),
            "Test Int Fail Float"
        );

        // Bool
        assert_eq!(
            build_test_literal("true"),
            Ok(Literal::Bool(true)),
            "Test Bool True"
        );
        assert_eq!(
            build_test_literal("false"),
            Ok(Literal::Bool(false)),
            "Test Bool False"
        );

        // Raw
        assert_eq!(
            build_test_literal("0xabcd"),
            Ok(Literal::Raw(vec![0xab, 0xcd])),
            "Test Raw Basic"
        );
        assert_eq!(
            build_test_literal("0x0102"),
            Ok(Literal::Raw(vec![0x01, 0x02])),
            "Test Raw Leading Zero"
        );
        assert_eq!(
            build_test_literal("0xff"),
            Ok(Literal::Raw(vec![0xff])),
            "Test Raw Single Byte"
        );
        let long_raw_bytes = hex::decode("deadbeef01234567").unwrap();
        assert_eq!(
            build_test_literal("0xdeadbeef01234567"),
            Ok(Literal::Raw(long_raw_bytes)),
            "Test Raw Longer"
        );
        // AST builder should fail for odd length / empty / invalid hex
        assert!(
            matches!(
                build_test_literal("0xabc"),
                Err(AstBuildError::Internal(_)) // Expect Internal error due to parse failure
                                                // Err(AstBuildError::InvalidHexLength { .. }) // Original incorrect expectation
            ),
            "Test Raw Fail Odd"
        );
        assert!(
            matches!(
                build_test_literal("0x"),
                Err(AstBuildError::Internal(_)) // Expect Internal error due to parse failure
            ),
            "Test Raw Fail Empty"
        );
        // Parser should fail for invalid hex chars
        assert!(
            matches!(build_test_literal("0xgg"), Err(AstBuildError::Internal(_))),
            "Test Raw Fail Invalid Hex"
        );

        // String
        assert_eq!(
            build_test_literal(r#""hello""#),
            Ok(Literal::String("hello".to_string())),
            "Test String Basic"
        );
        assert_eq!(
            build_test_literal(r#""escaped \" quote""#),
            Ok(Literal::String("escaped \" quote".to_string())),
            "Test String Escaped Quote"
        );
        assert_eq!(
            build_test_literal(r#""\\ backslash""#),
            Ok(Literal::String("\\ backslash".to_string())),
            "Test String Escaped Backslash"
        );
        assert_eq!(
            build_test_literal(r#""\n newline""#),
            Ok(Literal::String("\n newline".to_string())),
            "Test String Escaped Newline"
        );
        // Parser should fail for unterminated
        assert!(
            matches!(
                build_test_literal("\"unterminated"),
                Err(AstBuildError::Internal(_))
            ),
            "Test String Fail Unterminated"
        );
        // AST builder should fail for invalid escape
        assert!(
            matches!(
                build_test_literal(r#""invalid \escape""#),
                Err(AstBuildError::Internal(_))
            ),
            "Test String Fail Invalid Escape"
        );

        // Array
        assert_eq!(
            build_test_literal("[]"),
            Ok(Literal::Array(vec![])),
            "Test Array Empty"
        );
        assert_eq!(
            build_test_literal("[1, true, \"hello\"]"),
            Ok(Literal::Array(vec![
                Literal::Int(1),
                Literal::Bool(true),
                Literal::String("hello".to_string())
            ])),
            "Test Array Mixed"
        );
        assert_eq!(
            build_test_literal("[[], [2]]"),
            Ok(Literal::Array(vec![
                Literal::Array(vec![]),
                Literal::Array(vec![Literal::Int(2)])
            ])),
            "Test Array Nested"
        );

        // Set
        assert_eq!(
            build_test_literal("#[]"),
            Ok(Literal::Set(vec![])),
            "Test Set Empty"
        );
        assert_eq!(
            build_test_literal("#[1, 2, 1]"), // Duplicates allowed in AST, processor checks later
            Ok(Literal::Set(vec![
                Literal::Int(1),
                Literal::Int(2),
                Literal::Int(1)
            ])),
            "Test Set Simple"
        );

        // Dict
        assert_eq!(
            build_test_literal("{}"),
            Ok(Literal::Dict(HashMap::new())),
            "Test Dict Empty"
        );
        let mut expected_dict = HashMap::new();
        expected_dict.insert("name".to_string(), Literal::String("Alice".to_string()));
        expected_dict.insert("age".to_string(), Literal::Int(30));
        assert_eq!(
            build_test_literal(r#"{ "name": "Alice", "age": 30 }"#),
            Ok(Literal::Dict(expected_dict)),
            "Test Dict Simple"
        );
        let mut expected_nested_dict = HashMap::new();
        let mut inner_dict = HashMap::new();
        inner_dict.insert("val".to_string(), Literal::Bool(true));
        expected_nested_dict.insert("inner".to_string(), Literal::Dict(inner_dict));
        assert_eq!(
            build_test_literal(r#"{ "inner": { "val": true } }"#),
            Ok(Literal::Dict(expected_nested_dict)),
            "Test Dict Nested"
        );
        // Parser should fail for non-string key
        assert!(
            matches!(
                build_test_literal("{ name: \"Alice\" }"),
                Err(AstBuildError::Internal(_))
            ),
            "Test Dict Fail Non-String Key"
        );
    }

    #[test]
    fn test_build_identifier() {
        let pair = parse_rule(Rule::identifier, "my_pred").expect("Parser failed for identifier");
        assert_eq!(
            build_identifier(pair),
            Ok(Identifier("my_pred".to_string()))
        );

        let pair = parse_rule(Rule::identifier, "_internal").expect("Parser failed for identifier");
        assert_eq!(
            build_identifier(pair),
            Ok(Identifier("_internal".to_string()))
        );

        let pair =
            parse_rule(Rule::identifier, "ValidName123").expect("Parser failed for identifier");
        assert_eq!(
            build_identifier(pair),
            Ok(Identifier("ValidName123".to_string()))
        );
        // Parser should fail for invalid identifiers
        assert!(parse_rule(Rule::identifier, "1_invalid").is_err());
        assert!(parse_rule(Rule::identifier, "invalid-char").is_err());
    }

    #[test]
    fn test_build_variable() {
        let pair = parse_rule(Rule::variable, "?Var").expect("Parser failed for variable");
        assert_eq!(build_variable(&pair), Ok(Variable("Var".to_string())));

        let pair = parse_rule(Rule::variable, "?_Internal").expect("Parser failed for variable");
        assert_eq!(build_variable(&pair), Ok(Variable("_Internal".to_string())));

        let pair = parse_rule(Rule::variable, "?X1").expect("Parser failed for variable");
        assert_eq!(build_variable(&pair), Ok(Variable("X1".to_string())));

        // Parser should fail for just "?"
        assert!(
            parse_rule(Rule::variable, "?").is_err(),
            "Parser should fail for '?'"
        );

        // Parser should fail for invalid variable chars
        assert!(parse_rule(Rule::variable, "?invalid-char").is_err());
    }

    #[test]
    fn test_build_anchored_key() {
        // Literal key
        let pair_lit =
            parse_rule(Rule::anchored_key, "?PodVar[\"key\"]").expect("Parse AK literal failed");
        let expected_lit = Ok(AnchoredKey {
            pod_var: Variable("PodVar".to_string()),
            key: AnchoredKeyKey::LiteralString("key".to_string()),
        });
        assert_eq!(build_anchored_key(pair_lit), expected_lit);

        // Variable key
        let pair_var =
            parse_rule(Rule::anchored_key, "?PodVar[?KeyVar]").expect("Parse AK variable failed");
        let expected_var = Ok(AnchoredKey {
            pod_var: Variable("PodVar".to_string()),
            key: AnchoredKeyKey::Variable(Variable("KeyVar".to_string())),
        });
        assert_eq!(build_anchored_key(pair_var), expected_var);

        // Error cases (parser should catch these)
        assert!(parse_rule(Rule::anchored_key, "PodVar[\"key\"]").is_err()); // Missing `?` on pod var
        assert!(parse_rule(Rule::anchored_key, "?PodVar[invalid]").is_err()); // Invalid key type (not var or string lit)
        assert!(parse_rule(Rule::anchored_key, "?PodVar[]").is_err()); // Empty key
    }

    #[test]
    fn test_build_argument() {
        // Literal arg
        let pair_lit = parse_rule(Rule::call_arg, "123").expect("Parse literal arg failed");
        assert_eq!(
            build_argument(pair_lit),
            Ok(Argument::Literal(Literal::Int(123)))
        );

        // Variable arg
        let pair_var = parse_rule(Rule::call_arg, "?MyVar").expect("Parse variable arg failed");
        assert_eq!(
            build_argument(pair_var),
            Ok(Argument::Variable(Variable("MyVar".to_string())))
        );

        // Anchored Key arg
        let pair_ak = parse_rule(Rule::call_arg, "?Pod[\"k\"]").expect("Parse AK arg failed");
        let expected_ak = Argument::AnchoredKey(AnchoredKey {
            pod_var: Variable("Pod".to_string()),
            key: AnchoredKeyKey::LiteralString("k".to_string()),
        });
        assert_eq!(build_argument(pair_ak), Ok(expected_ak));

        // Anchored Key with Var key arg
        let pair_ak_var =
            parse_rule(Rule::call_arg, "?Pod[?Key]").expect("Parse AK var-key arg failed");
        let expected_ak_var = Argument::AnchoredKey(AnchoredKey {
            pod_var: Variable("Pod".to_string()),
            key: AnchoredKeyKey::Variable(Variable("Key".to_string())),
        });
        assert_eq!(build_argument(pair_ak_var), Ok(expected_ak_var));
    }

    // Helper to parse and build a native call
    fn build_test_native_call(
        input: &str,
        rule: Rule,
    ) -> Result<NativePredicateCall, AstBuildError> {
        let pair = parse_rule(rule, input).map_err(|e| {
            AstBuildError::Internal(format!("Parser failed for native call: {}", e))
        })?;
        build_native_call(pair)
    }

    #[test]
    fn test_build_native_call() {
        // ValueOf(AnchoredKey, Literal)
        let result_vo = build_test_native_call("ValueOf(?Pod[\"k\"], 1)", Rule::value_of_stmt);
        let expected_vo = Ok(NativePredicateCall {
            predicate: NativePredicate::ValueOf,
            args: vec![
                Argument::AnchoredKey(AnchoredKey {
                    pod_var: Variable("Pod".to_string()),
                    key: AnchoredKeyKey::LiteralString("k".to_string()),
                }),
                Argument::Literal(Literal::Int(1)),
            ],
        });
        assert_eq!(result_vo, expected_vo);

        // Equal(AnchoredKey, CallArg)
        let result_eq = build_test_native_call("Equal(?P1[?K], ?P2[\"fixed\"])", Rule::equal_stmt);
        let expected_eq = Ok(NativePredicateCall {
            predicate: NativePredicate::Equal,
            args: vec![
                Argument::AnchoredKey(AnchoredKey {
                    pod_var: Variable("P1".to_string()),
                    key: AnchoredKeyKey::Variable(Variable("K".to_string())),
                }),
                Argument::AnchoredKey(AnchoredKey {
                    pod_var: Variable("P2".to_string()),
                    key: AnchoredKeyKey::LiteralString("fixed".to_string()),
                }),
            ],
        });
        assert_eq!(result_eq, expected_eq);

        // Lt(AnchoredKey, CallArg = Literal)
        let result_lt_lit = build_test_native_call("Lt(?A[\"x\"], 5)", Rule::lt_stmt);
        let expected_lt_lit = Ok(NativePredicateCall {
            predicate: NativePredicate::Lt,
            args: vec![
                Argument::AnchoredKey(AnchoredKey {
                    pod_var: Variable("A".to_string()),
                    key: AnchoredKeyKey::LiteralString("x".to_string()),
                }),
                Argument::Literal(Literal::Int(5)),
            ],
        });
        assert_eq!(result_lt_lit, expected_lt_lit);

        // Gt(AnchoredKey, CallArg = Variable)
        let result_gt_var = build_test_native_call("Gt(?A[\"x\"], ?MyVar)", Rule::gt_stmt);
        let expected_gt_var = Ok(NativePredicateCall {
            predicate: NativePredicate::Gt,
            args: vec![
                Argument::AnchoredKey(AnchoredKey {
                    pod_var: Variable("A".to_string()),
                    key: AnchoredKeyKey::LiteralString("x".to_string()),
                }),
                Argument::Variable(Variable("MyVar".to_string())),
            ],
        });
        assert_eq!(result_gt_var, expected_gt_var);

        // NotContains(AnchoredKey, AnchoredKey)
        let result_nc = build_test_native_call(
            "NotContains(?Set[\"k1\"], ?Val[\"k2\"])",
            Rule::not_contains_stmt,
        );
        let expected_nc = Ok(NativePredicateCall {
            predicate: NativePredicate::NotContains,
            args: vec![
                Argument::AnchoredKey(AnchoredKey {
                    pod_var: Variable("Set".to_string()),
                    key: AnchoredKeyKey::LiteralString("k1".to_string()),
                }),
                Argument::AnchoredKey(AnchoredKey {
                    pod_var: Variable("Val".to_string()),
                    key: AnchoredKeyKey::LiteralString("k2".to_string()),
                }),
            ],
        });
        assert_eq!(result_nc, expected_nc);

        // SumOf(AnchoredKey, AnchoredKey, AnchoredKey)
        let result_sum = build_test_native_call(
            "SumOf(?R[\"res\"], ?A[\"a\"], ?B[\"b\"])",
            Rule::sum_of_stmt,
        );
        let expected_sum = Ok(NativePredicateCall {
            predicate: NativePredicate::SumOf,
            args: vec![
                Argument::AnchoredKey(AnchoredKey {
                    pod_var: Variable("R".to_string()),
                    key: AnchoredKeyKey::LiteralString("res".to_string()),
                }),
                Argument::AnchoredKey(AnchoredKey {
                    pod_var: Variable("A".to_string()),
                    key: AnchoredKeyKey::LiteralString("a".to_string()),
                }),
                Argument::AnchoredKey(AnchoredKey {
                    pod_var: Variable("B".to_string()),
                    key: AnchoredKeyKey::LiteralString("b".to_string()),
                }),
            ],
        });
        assert_eq!(result_sum, expected_sum);
    }

    // Helper to parse and build a custom call
    fn build_test_custom_call(input: &str) -> Result<CustomPredicateCall, AstBuildError> {
        let pair = parse_rule(Rule::custom_predicate_call, input).map_err(|e| {
            AstBuildError::Internal(format!("Parser failed for custom call: {}", e))
        })?;
        build_custom_call(pair)
    }

    #[test]
    fn test_build_custom_call() {
        // No args
        let result_no_args = build_test_custom_call("my_pred()");
        let expected_no_args = Ok(CustomPredicateCall {
            name: Identifier("my_pred".to_string()),
            args: vec![],
        });
        assert_eq!(result_no_args, expected_no_args);

        // One arg
        let result_one_arg = build_test_custom_call("pred_one(?A)");
        let expected_one_arg = Ok(CustomPredicateCall {
            name: Identifier("pred_one".to_string()),
            args: vec![Argument::Variable(Variable("A".to_string()))],
        });
        assert_eq!(result_one_arg, expected_one_arg);

        // Multiple mixed args
        let result_mixed = build_test_custom_call("pred_mix(?A, 123, ?P[\"k\"])");
        let expected_mixed = Ok(CustomPredicateCall {
            name: Identifier("pred_mix".to_string()),
            args: vec![
                Argument::Variable(Variable("A".to_string())),
                Argument::Literal(Literal::Int(123)),
                Argument::AnchoredKey(AnchoredKey {
                    pod_var: Variable("P".to_string()),
                    key: AnchoredKeyKey::LiteralString("k".to_string()),
                }),
            ],
        });
        assert_eq!(result_mixed, expected_mixed);
    }

    // Helper to parse and build a statement
    fn build_test_statement(input: &str) -> Result<Statement, AstBuildError> {
        let pair = parse_rule(Rule::statement, input)
            .map_err(|e| AstBuildError::Internal(format!("Parser failed for statement: {}", e)))?;
        build_statement(pair)
    }

    #[test]
    fn test_build_statement() {
        // Native statement
        let result_native = build_test_statement("Equal(?A[\"k\"], ?B[\"k\"])");
        let expected_native = Ok(Statement::Native(NativePredicateCall {
            predicate: NativePredicate::Equal,
            args: vec![
                Argument::AnchoredKey(AnchoredKey {
                    pod_var: Variable("A".to_string()),
                    key: AnchoredKeyKey::LiteralString("k".to_string()),
                }),
                Argument::AnchoredKey(AnchoredKey {
                    pod_var: Variable("B".to_string()),
                    key: AnchoredKeyKey::LiteralString("k".to_string()),
                }),
            ],
        }));
        assert_eq!(result_native, expected_native);

        // Custom statement
        let result_custom = build_test_statement("my_pred(?X)");
        let expected_custom = Ok(Statement::Custom(CustomPredicateCall {
            name: Identifier("my_pred".to_string()),
            args: vec![Argument::Variable(Variable("X".to_string()))],
        }));
        assert_eq!(result_custom, expected_custom);
    }

    // Helper to parse and build a custom predicate definition
    fn build_test_custom_predicate(
        input: &str,
    ) -> Result<CustomPredicateDefinition, AstBuildError> {
        let pair = parse_rule(Rule::custom_predicate_def, input).map_err(|e| {
            AstBuildError::Internal(format!("Parser failed for custom pred def: {}", e))
        })?;
        build_custom_predicate(pair)
    }

    #[test]
    fn test_build_custom_predicate() {
        // Simple AND predicate
        let input_and = r#"simple_and(A, B) = AND(
            Equal(?A["val"], ?B["val"])
        )"#;
        let result_and = build_test_custom_predicate(input_and);
        let expected_and = Ok(CustomPredicateDefinition {
            name: Identifier("simple_and".to_string()),
            public_args: vec![Variable("A".to_string()), Variable("B".to_string())],
            private_args: vec![],
            type_: CustomPredicateType::And,
            statements: vec![Statement::Native(NativePredicateCall {
                predicate: NativePredicate::Equal,
                args: vec![
                    Argument::AnchoredKey(AnchoredKey {
                        pod_var: Variable("A".to_string()),
                        key: AnchoredKeyKey::LiteralString("val".to_string()),
                    }),
                    Argument::AnchoredKey(AnchoredKey {
                        pod_var: Variable("B".to_string()),
                        key: AnchoredKeyKey::LiteralString("val".to_string()),
                    }),
                ],
            })],
        });
        assert_eq!(result_and, expected_and);

        // Predicate with private args
        let input_priv = r#"with_priv(Pub) = OR(
            private(Priv1, Priv2)
            Lt(?Pub["x"], ?Priv1["y"])
            Gt(?Priv1["y"], ?Priv2["z"])
        )"#;
        let result_priv = build_test_custom_predicate(input_priv);
        let expected_priv = Ok(CustomPredicateDefinition {
            name: Identifier("with_priv".to_string()),
            public_args: vec![Variable("Pub".to_string())],
            private_args: vec![Variable("Priv1".to_string()), Variable("Priv2".to_string())],
            type_: CustomPredicateType::Or,
            statements: vec![
                Statement::Native(NativePredicateCall {
                    predicate: NativePredicate::Lt,
                    args: vec![
                        Argument::AnchoredKey(AnchoredKey {
                            pod_var: Variable("Pub".to_string()),
                            key: AnchoredKeyKey::LiteralString("x".to_string()),
                        }),
                        Argument::AnchoredKey(AnchoredKey {
                            pod_var: Variable("Priv1".to_string()),
                            key: AnchoredKeyKey::LiteralString("y".to_string()),
                        }),
                    ],
                }),
                Statement::Native(NativePredicateCall {
                    predicate: NativePredicate::Gt,
                    args: vec![
                        Argument::AnchoredKey(AnchoredKey {
                            pod_var: Variable("Priv1".to_string()),
                            key: AnchoredKeyKey::LiteralString("y".to_string()),
                        }),
                        Argument::AnchoredKey(AnchoredKey {
                            pod_var: Variable("Priv2".to_string()),
                            key: AnchoredKeyKey::LiteralString("z".to_string()),
                        }),
                    ],
                }),
            ],
        });
        assert_eq!(result_priv, expected_priv);

        // Predicate with no args, no statements
        let input_empty = "empty_pred() = AND()";
        let result_empty = build_test_custom_predicate(input_empty);
        let expected_empty = Ok(CustomPredicateDefinition {
            name: Identifier("empty_pred".to_string()),
            public_args: vec![],
            private_args: vec![],
            type_: CustomPredicateType::And,
            statements: vec![],
        });
        assert_eq!(result_empty, expected_empty);

        // Predicate with args, no statements
        let input_no_stmts = "no_stmts(A, B) = OR()";
        let result_no_stmts = build_test_custom_predicate(input_no_stmts);
        let expected_no_stmts = Ok(CustomPredicateDefinition {
            name: Identifier("no_stmts".to_string()),
            public_args: vec![Variable("A".to_string()), Variable("B".to_string())],
            private_args: vec![],
            type_: CustomPredicateType::Or,
            statements: vec![],
        });
        assert_eq!(result_no_stmts, expected_no_stmts);
    }

    // Helper to parse and build a request definition
    fn build_test_request(input: &str) -> Result<RequestDefinition, AstBuildError> {
        let pair = parse_rule(Rule::request_def, input).map_err(|e| {
            AstBuildError::Internal(format!("Parser failed for request def: {}", e))
        })?;
        build_request(pair)
    }

    #[test]
    fn test_build_request() {
        let input = r#"REQUEST(
            Equal(?A["k"], ?B["k"])
            my_custom(?C)
        )"#;
        let result = build_test_request(input);
        let expected = Ok(RequestDefinition {
            statements: vec![
                Statement::Native(NativePredicateCall {
                    predicate: NativePredicate::Equal,
                    args: vec![
                        Argument::AnchoredKey(AnchoredKey {
                            pod_var: Variable("A".to_string()),
                            key: AnchoredKeyKey::LiteralString("k".to_string()),
                        }),
                        Argument::AnchoredKey(AnchoredKey {
                            pod_var: Variable("B".to_string()),
                            key: AnchoredKeyKey::LiteralString("k".to_string()),
                        }),
                    ],
                }),
                Statement::Custom(CustomPredicateCall {
                    name: Identifier("my_custom".to_string()),
                    args: vec![Argument::Variable(Variable("C".to_string()))],
                }),
            ],
        });
        assert_eq!(result, expected);

        // Empty request
        let input_empty = "REQUEST()";
        let result_empty = build_test_request(input_empty);
        let expected_empty = Ok(RequestDefinition { statements: vec![] });
        assert_eq!(result_empty, expected_empty);

        // Request with comments
        let input_comments = r#"REQUEST(
            // First statement
            Gt(?Val["x"], 0)
            // Another custom call
            other_pred()
        )"#;
        let result_comments = build_test_request(input_comments);
        let expected_comments = Ok(RequestDefinition {
            statements: vec![
                Statement::Native(NativePredicateCall {
                    predicate: NativePredicate::Gt,
                    args: vec![
                        Argument::AnchoredKey(AnchoredKey {
                            pod_var: Variable("Val".to_string()),
                            key: AnchoredKeyKey::LiteralString("x".to_string()),
                        }),
                        Argument::Literal(Literal::Int(0)),
                    ],
                }),
                Statement::Custom(CustomPredicateCall {
                    name: Identifier("other_pred".to_string()),
                    args: vec![],
                }),
            ],
        });
        assert_eq!(result_comments, expected_comments);
    }

    // Helper to parse and build a full document
    fn build_test_document(input: &str) -> Result<Document, AstBuildError> {
        // Use parse_podlog directly which handles the document rule and potential errors
        let pairs = crate::lang::parser::parse_podlog(input)
            .map_err(|e| AstBuildError::Internal(format!("Parser failed for document: {}", e)))?;
        build_ast(pairs)
    }

    #[test]
    fn test_build_ast() {
        // Document with one predicate and one request
        let input_full = r#"
            // Predicate first
            pred(X) = AND(
                Gt(?X["a"], 0)
            )

            // Then request
            REQUEST(
                pred(?MyData)
                Lt(?MyData["b"], 100)
            )
        "#;
        let result_full = build_test_document(input_full);

        let expected_pred = TopLevelDefinition::CustomPredicate(CustomPredicateDefinition {
            name: Identifier("pred".to_string()),
            public_args: vec![Variable("X".to_string())],
            private_args: vec![],
            type_: CustomPredicateType::And,
            statements: vec![Statement::Native(NativePredicateCall {
                predicate: NativePredicate::Gt,
                args: vec![
                    Argument::AnchoredKey(AnchoredKey {
                        pod_var: Variable("X".to_string()),
                        key: AnchoredKeyKey::LiteralString("a".to_string()),
                    }),
                    Argument::Literal(Literal::Int(0)),
                ],
            })],
        });
        let expected_req = TopLevelDefinition::Request(RequestDefinition {
            statements: vec![
                Statement::Custom(CustomPredicateCall {
                    name: Identifier("pred".to_string()),
                    args: vec![Argument::Variable(Variable("MyData".to_string()))],
                }),
                Statement::Native(NativePredicateCall {
                    predicate: NativePredicate::Lt,
                    args: vec![
                        Argument::AnchoredKey(AnchoredKey {
                            pod_var: Variable("MyData".to_string()),
                            key: AnchoredKeyKey::LiteralString("b".to_string()),
                        }),
                        Argument::Literal(Literal::Int(100)),
                    ],
                }),
            ],
        });
        let expected_full = Ok(Document {
            definitions: vec![expected_pred, expected_req],
        });
        assert_eq!(result_full, expected_full);

        // Document with only comments and whitespace
        let input_empty = "// comment 1\n   // comment 2 \n \n";
        let result_empty = build_test_document(input_empty);
        let expected_empty_doc = Ok(Document {
            definitions: vec![],
        });
        assert_eq!(result_empty, expected_empty_doc);

        // Document with only predicate
        let input_pred_only = "pred_only() = OR()";
        let result_pred_only = build_test_document(input_pred_only);
        let expected_pred_only = Ok(Document {
            definitions: vec![TopLevelDefinition::CustomPredicate(
                CustomPredicateDefinition {
                    name: Identifier("pred_only".to_string()),
                    public_args: vec![],
                    private_args: vec![],
                    type_: CustomPredicateType::Or,
                    statements: vec![],
                },
            )],
        });
        assert_eq!(result_pred_only, expected_pred_only);

        // Document with only request
        let input_req_only = "REQUEST( Equal(?A[\"k\"], ?B[\"k\"]) )";
        let result_req_only = build_test_document(input_req_only);
        let expected_req_only = Ok(Document {
            definitions: vec![TopLevelDefinition::Request(RequestDefinition {
                statements: vec![Statement::Native(NativePredicateCall {
                    predicate: NativePredicate::Equal,
                    args: vec![
                        Argument::AnchoredKey(AnchoredKey {
                            pod_var: Variable("A".to_string()),
                            key: AnchoredKeyKey::LiteralString("k".to_string()),
                        }),
                        Argument::AnchoredKey(AnchoredKey {
                            pod_var: Variable("B".to_string()),
                            key: AnchoredKeyKey::LiteralString("k".to_string()),
                        }),
                    ],
                })],
            })],
        });
        assert_eq!(result_req_only, expected_req_only);

        // Document with mixed order
        let input_mixed = r#"
            REQUEST(
                pred1(?A)
            )
            pred2(Y) = OR()
            pred1(X) = AND()
        "#;
        let result_mixed = build_test_document(input_mixed);
        let expected_req_mixed = TopLevelDefinition::Request(RequestDefinition {
            statements: vec![Statement::Custom(CustomPredicateCall {
                name: Identifier("pred1".to_string()),
                args: vec![Argument::Variable(Variable("A".to_string()))],
            })],
        });
        let expected_pred2_mixed = TopLevelDefinition::CustomPredicate(CustomPredicateDefinition {
            name: Identifier("pred2".to_string()),
            public_args: vec![Variable("Y".to_string())],
            private_args: vec![],
            type_: CustomPredicateType::Or,
            statements: vec![],
        });
        let expected_pred1_mixed = TopLevelDefinition::CustomPredicate(CustomPredicateDefinition {
            name: Identifier("pred1".to_string()),
            public_args: vec![Variable("X".to_string())],
            private_args: vec![],
            type_: CustomPredicateType::And,
            statements: vec![],
        });
        let expected_mixed_doc = Ok(Document {
            definitions: vec![
                expected_req_mixed,
                expected_pred2_mixed,
                expected_pred1_mixed,
            ],
        });
        assert_eq!(result_mixed, expected_mixed_doc);
    }
}
