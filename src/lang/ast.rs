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
    Internal(String), // For unexpected logic errors during AST construction
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

// Corresponds to middleware::NativePredicate
#[derive(Debug, Clone, PartialEq, Eq, Hash, Copy)]
pub enum NativePredicate {
    ValueOf,
    Equal,
    NotEqual,
    Gt,
    GtEq,
    Lt,
    LtEq,
    Contains,
    NotContains,
    SumOf,
    ProductOf,
    MaxOf,
    HashOf,
    DictContains,
    DictNotContains,
    SetContains,
    SetNotContains,
    ArrayContains,
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
                return Err(ast_err!(Generic, &inner_pair, "Unexpected 'identifier' rule ({}) encountered directly within custom_predicate_def. Expected 'predicate_identifier'.", inner_pair.as_str()));
            }
            Rule::predicate_identifier => {
                // Avoid overwriting if somehow matched twice
                if name_opt.is_some() {
                    return Err(ast_err!(
                        Generic,
                        &inner_pair,
                        "Found multiple predicate names"
                    ));
                }
                name_opt = Some(build_identifier(inner_pair)?);
            }
            Rule::arg_section => {
                for arg_pair in inner_pair.into_inner() {
                    match arg_pair.as_rule() {
                        Rule::public_arg_list => {
                            if !public_args.is_empty() {
                                return Err(ast_err!(
                                    Generic,
                                    &arg_pair,
                                    "Duplicate public_arg_list found"
                                ));
                            }
                            public_args = arg_pair
                                .into_inner()
                                .map(|p| build_identifier(p).map(|ident| Variable(ident.0)))
                                .collect::<Result<Vec<Variable>, _>>()?;
                        }
                        Rule::private_arg_list => {
                            if !private_args.is_empty() {
                                return Err(ast_err!(
                                    Generic,
                                    &arg_pair,
                                    "Duplicate private_arg_list found"
                                ));
                            }
                            private_args = arg_pair
                                .into_inner()
                                .map(|p| build_identifier(p).map(|ident| Variable(ident.0)))
                                .collect::<Result<Vec<Variable>, _>>()?;
                        }
                        Rule::private_kw | Rule::COMMENT | Rule::WHITESPACE => {}
                        _ if [","].contains(&arg_pair.as_str().trim()) => {}
                        _ => return Err(ast_err!(UnexpectedRule, &arg_pair)),
                    }
                }
            }
            Rule::statement_list => {
                statements = inner_pair
                    .into_inner()
                    .map(build_statement)
                    .collect::<Result<_, _>>()?;
            }
            // Match the conjunction_type rule
            Rule::conjunction_type => {
                if type_opt.is_some() {
                    return Err(ast_err!(
                        Generic,
                        &inner_pair,
                        "Found multiple conjunction types"
                    ));
                }
                type_opt = match inner_pair.as_str() {
                    "AND" => Some(CustomPredicateType::And),
                    "OR" => Some(CustomPredicateType::Or),
                    _ => {
                        // Should not happen if grammar is correct
                        return Err(ast_err!(
                            Generic,
                            &inner_pair,
                            "Unexpected content for conjunction_type: {}",
                            inner_pair.as_str()
                        ));
                    }
                };
            }
            // Ignore known syntax/comments/whitespace, error on others
            Rule::COMMENT | Rule::WHITESPACE => { /* Ignore */ }
            // Updated the list of ignored syntactic literals
            _ if ["=", "(", ")", ",", "private:"].contains(&inner_pair.as_str().trim()) => { /* Ignore */
            }
            _ => {
                // If it's not a handled rule or known syntax/ignored rules, it's unexpected
                return Err(ast_err!(UnexpectedRule, &inner_pair));
            }
        }
    }

    let name = name_opt.ok_or_else(|| {
        // Span isn't easily available here if the name was completely missing.
        AstBuildError::Internal("Missing predicate name in parsed pairs".to_string())
    })?;
    let type_ = type_opt.ok_or_else(|| {
        // Span isn't easily available here either.
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
    // Keep outer pair reference for potential errors on unexpected rules.
    let outer_pair = pair.clone();
    let maybe_statement_list = pair
        .into_inner()
        .find(|p| p.as_rule() == Rule::statement_list);

    let statements = match maybe_statement_list {
        Some(statement_list) => statement_list
            .into_inner()
            .filter(|p| p.as_rule() == Rule::statement)
            .map(build_statement)
            .collect::<Result<_, _>>()?, // Errors from build_statement will have spans
        None => Vec::new(),
    };

    // Check for unexpected rules inside request_def (besides statement_list or comments/ws).
    for inner in outer_pair.into_inner() {
        match inner.as_rule() {
            Rule::statement_list | Rule::COMMENT | Rule::WHITESPACE => {}
            _ if ["REQUEST", "(", ")"].contains(&inner.as_str().trim()) => {}
            _ => return Err(ast_err!(UnexpectedRule, &inner)),
        }
    }

    Ok(RequestDefinition { statements })
}

fn build_statement(pair: Pair<'_, Rule>) -> Result<Statement, AstBuildError> {
    // The statement rule directly contains one of the specific stmt rules or a custom call
    let inner_pair = pair
        .clone()
        .into_inner()
        .next()
        .ok_or_else(|| ast_err!(Generic, &pair, "Empty statement encountered"))?;
    match inner_pair.as_rule() {
        // Match specific native statement rules
        Rule::value_of_stmt
        | Rule::equal_stmt
        | Rule::not_equal_stmt
        | Rule::gt_stmt
        | Rule::gt_eq_stmt
        | Rule::lt_stmt
        | Rule::lt_eq_stmt
        | Rule::contains_stmt
        | Rule::not_contains_stmt
        | Rule::sum_of_stmt
        | Rule::product_of_stmt
        | Rule::max_of_stmt
        | Rule::hash_of_stmt
        | Rule::dict_contains_stmt
        | Rule::dict_not_contains_stmt
        | Rule::set_contains_stmt
        | Rule::set_not_contains_stmt
        | Rule::array_contains_stmt => Ok(Statement::Native(build_native_call(inner_pair)?)),
        Rule::custom_predicate_call => Ok(Statement::Custom(build_custom_call(inner_pair)?)),
        _ => Err(ast_err!(UnexpectedRule, &inner_pair)),
    }
}

fn build_native_call(pair: Pair<'_, Rule>) -> Result<NativePredicateCall, AstBuildError> {
    let predicate = match pair.as_rule() {
        Rule::value_of_stmt => NativePredicate::ValueOf,
        Rule::equal_stmt => NativePredicate::Equal,
        Rule::not_equal_stmt => NativePredicate::NotEqual,
        Rule::gt_stmt => NativePredicate::Gt,
        Rule::gt_eq_stmt => NativePredicate::GtEq,
        Rule::lt_stmt => NativePredicate::Lt,
        Rule::lt_eq_stmt => NativePredicate::LtEq,
        Rule::contains_stmt => NativePredicate::Contains,
        Rule::not_contains_stmt => NativePredicate::NotContains,
        Rule::sum_of_stmt => NativePredicate::SumOf,
        Rule::product_of_stmt => NativePredicate::ProductOf,
        Rule::max_of_stmt => NativePredicate::MaxOf,
        Rule::hash_of_stmt => NativePredicate::HashOf,
        Rule::dict_contains_stmt => NativePredicate::DictContains,
        Rule::dict_not_contains_stmt => NativePredicate::DictNotContains,
        Rule::set_contains_stmt => NativePredicate::SetContains,
        Rule::set_not_contains_stmt => NativePredicate::SetNotContains,
        Rule::array_contains_stmt => NativePredicate::ArrayContains,
        _ => return Err(ast_err!(UnexpectedRule, &pair)), // Should not happen if called correctly
    };

    // Process arguments differently for ValueOf vs other native predicates.
    let args = if predicate == NativePredicate::ValueOf {
        // ValueOf requires (AnchoredKey, Literal)
        let mut inner_pairs = pair.clone().into_inner();
        let ak_pair = inner_pairs.next().ok_or_else(|| {
            ast_err!(
                Generic,
                &pair,
                "Missing ValueOf argument 1 (expected anchored_key)"
            )
        })?;
        let lit_pair = inner_pairs.next().ok_or_else(|| {
            ast_err!(
                Generic,
                &pair,
                "Missing ValueOf argument 2 (expected literal_value)"
            )
        })?;

        // Rule checks
        if ak_pair.as_rule() != Rule::anchored_key {
            return Err(ast_err!(
                Generic,
                &ak_pair,
                "Invalid arg type for ValueOf arg 1: expected anchored_key, got {:?}",
                ak_pair.as_rule()
            ));
        }
        if lit_pair.as_rule() != Rule::literal_value {
            return Err(ast_err!(
                Generic,
                &lit_pair,
                "Invalid arg type for ValueOf arg 2: expected literal_value, got {:?}",
                lit_pair.as_rule()
            ));
        }
        if inner_pairs.next().is_some() {
            return Err(ast_err!(
                Generic,
                &pair,
                "Too many arguments for ValueOf (expected 2)"
            ));
        }

        vec![
            Argument::AnchoredKey(build_anchored_key(ak_pair)?),
            Argument::Literal(build_literal(lit_pair)?),
        ]
    } else {
        // All other native predicates expect only AnchoredKey arguments.
        build_native_call_args(predicate, pair)?
    };

    Ok(NativePredicateCall { predicate, args })
}

// Helper function to process arguments for most native calls (non-ValueOf)
fn build_native_call_args(
    predicate: NativePredicate, // Pass the predicate type explicitly
    pair: Pair<'_, Rule>,       // Pass the *original* pair for iteration
) -> Result<Vec<Argument>, AstBuildError> {
    pair.into_inner()
        .map(|arg_pair| match arg_pair.as_rule() {
            // Only AnchoredKey is expected now for these predicates
            Rule::anchored_key => Ok(Argument::AnchoredKey(build_anchored_key(arg_pair)?)),
            // Any other rule is an error
            _ => Err(ast_err!(
                Generic,
                &arg_pair,
                "Invalid argument type {:?} for native predicate {:?}, expected AnchoredKey",
                arg_pair.as_rule(),
                predicate
            )),
        })
        .collect::<Result<_, _>>()
}

fn build_custom_call(pair: Pair<'_, Rule>) -> Result<CustomPredicateCall, AstBuildError> {
    let mut inner = pair.clone().into_inner(); // Clone for potential errors
    let name = build_identifier(
        inner
            .next()
            .ok_or_else(|| ast_err!(Generic, &pair, "Missing custom predicate call name"))?,
    )?;
    let args_pair = inner.next();

    let args = match args_pair {
        Some(p) => {
            p.into_inner() // Should contain custom_call_arg pairs
                .map(|custom_arg_pair| {
                    // custom_call_arg contains either variable or literal_value
                    let arg_content =
                        custom_arg_pair.clone().into_inner().next().ok_or_else(|| {
                            ast_err!(Generic, &custom_arg_pair, "Empty custom_call_arg")
                        })?;
                    match arg_content.as_rule() {
                        Rule::variable => Ok(Argument::Variable(build_variable(&arg_content)?)),
                        Rule::literal_value => Ok(Argument::Literal(build_literal(arg_content)?)),
                        _ => Err(ast_err!(UnexpectedRule, &arg_content)),
                    }
                })
                .collect::<Result<_, _>>()?
        }
        None => Vec::new(),
    };

    Ok(CustomPredicateCall { name, args })
}

fn build_anchored_key(pair: Pair<'_, Rule>) -> Result<AnchoredKey, AstBuildError> {
    let mut inner = pair.clone().into_inner(); // Clone for errors
    let pod_var = build_variable(
        &inner
            .next()
            .ok_or_else(|| ast_err!(Generic, &pair, "Missing pod variable in anchored key"))?,
    )?;
    let key_pair = inner
        .next()
        .ok_or_else(|| ast_err!(Generic, &pair, "Missing key in anchored key"))?;
    let key = build_anchored_key_key(&key_pair)?;
    if inner.next().is_some() {
        return Err(ast_err!(
            Generic,
            &pair,
            "Unexpected extra content in anchored key"
        ));
    }
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
    // and strip the `?` prefix.
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

    // Optional: Add further validation for identifier characters if the grammar allows too much.
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
        .clone()
        .into_inner()
        .next()
        .ok_or_else(|| ast_err!(Generic, &pair, "Empty literal_value encountered"))?;
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
            let elements = inner_pair
                .into_inner()
                .map(build_literal)
                .collect::<Result<_, _>>()?;
            Ok(Literal::Array(elements))
        }
        Rule::literal_set => {
            let elements = inner_pair
                .into_inner()
                .map(build_literal)
                .collect::<Result<_, _>>()?;
            Ok(Literal::Set(elements))
        }
        Rule::literal_dict => {
            let pairs = inner_pair
                .into_inner()
                .map(|dict_entry_pair| {
                    let mut entry_inner = dict_entry_pair.clone().into_inner();
                    let key_pair = entry_inner
                        .next()
                        .ok_or_else(|| ast_err!(Generic, &dict_entry_pair, "Missing dict key"))?;
                    let val_pair = entry_inner
                        .next()
                        .ok_or_else(|| ast_err!(Generic, &dict_entry_pair, "Missing dict value"))?;
                    if entry_inner.next().is_some() {
                        return Err(ast_err!(
                            Generic,
                            &dict_entry_pair,
                            "Unexpected extra content in dict entry"
                        ));
                    }
                    let key = parse_string_literal(&key_pair)?;
                    let val = build_literal(val_pair)?;
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
            match chars.next() {
                Some('"') => result.push('"'),
                Some('\\') => result.push('\\'),
                Some('/') => result.push('/'), // Note: JSON technically allows unescaped /.
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
                    return Err(ast_err!(
                        Generic,
                        &inner_pair,
                        "Invalid escape character: {}",
                        other
                    ));
                }
                None => {
                    return Err(ast_err!(
                        Generic,
                        &inner_pair,
                        "String ends with backslash escape"
                    ));
                }
            }
        } else {
            result.push(c);
        }
    }

    Ok(result)
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use pest::Parser;

    use super::*;
    use crate::lang::parser::{PodlogParser, Rule};

    // Helper to parse a string with a specific rule and expect success.
    // Uses anchored test rules (e.g., `test_identifier`) from the grammar
    // to ensure the entire input matches the target rule.
    fn parse_rule(rule: Rule, input: &str) -> Result<Pair<'_, Rule>, String> {
        // Map the base rule to its corresponding anchored test rule.
        let test_rule = match rule {
            Rule::identifier => Rule::test_identifier,
            Rule::variable => Rule::test_variable,
            Rule::literal_int => Rule::test_literal_int,
            Rule::literal_raw => Rule::test_literal_raw,
            // Add other mappings here if needed for tests
            // For rules without a specific test rule, maybe just use the original?
            // Or panic if a test requires an anchored version that doesn't exist.
            _ => rule, // Fallback to original rule, might need adjustment
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

    // Helper function to parse a string and build a literal.
    // It specifically parses using the `test_literal_value` rule, which
    // anchors the `literal_value` rule to ensure the whole input is consumed.
    // It then calls `build_literal` on the inner `literal_value` pair.
    fn build_test_literal(input: &str) -> Result<Literal, AstBuildError> {
        // Need to wrap the literal rule in literal_value for build_literal
        match PodlogParser::parse(Rule::test_literal_value, input) {
            Ok(mut pairs) => {
                let test_pair = pairs.next().ok_or_else(|| {
                    AstBuildError::Internal(
                        "Parser returned OK but no pair for test_literal_value".to_string(),
                    )
                })?;
                // The test_literal_value rule contains literal_value as its inner rule.
                let literal_value_pair = test_pair.into_inner().next().ok_or_else(|| {
                    AstBuildError::Internal(
                        "No inner literal_value found in test_literal_value".to_string(),
                    )
                })?;

                // The pair returned by parsing literal_value should *always* be literal_value.
                if literal_value_pair.as_rule() == Rule::literal_value {
                    build_literal(literal_value_pair)
                } else {
                    // This case indicates a parser/grammar inconsistency.
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
        // Parser should fail for floats, resulting in Internal error from build_test_literal.
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
        // Note: Grammar now enforces even length >= 2, so parser fails first.
        assert!(
            matches!(
                build_test_literal("0xabc"),
                Err(AstBuildError::Internal(_)) // Expect Internal error due to parse failure
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
        // Parser should fail for invalid hex chars.
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
        // Parser should fail for unterminated strings.
        assert!(
            matches!(
                build_test_literal("\"unterminated"),
                Err(AstBuildError::Internal(_))
            ),
            "Test String Fail Unterminated"
        );
        // Parser should fail for invalid escape sequences.
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
            build_test_literal("#[1, 2, 1]"), // Duplicates allowed in AST, processor checks later.
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
        // Parser should fail for non-string key.
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
        // Parser should fail for invalid identifiers.
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

        // Parser should fail for just "?".
        assert!(
            parse_rule(Rule::variable, "?").is_err(),
            "Parser should fail for '?'"
        );

        // Parser should fail for invalid variable chars.
        assert!(parse_rule(Rule::variable, "?invalid-char").is_err());
    }

    #[test]
    fn test_build_anchored_key() {
        let pair_lit =
            parse_rule(Rule::anchored_key, "?PodVar[\"key\"]").expect("Parse AK literal failed");
        let expected_lit = Ok(AnchoredKey {
            pod_var: Variable("PodVar".to_string()),
            key: AnchoredKeyKey::LiteralString("key".to_string()),
        });
        assert_eq!(build_anchored_key(pair_lit), expected_lit);

        let pair_var =
            parse_rule(Rule::anchored_key, "?PodVar[?KeyVar]").expect("Parse AK variable failed");
        let expected_var = Ok(AnchoredKey {
            pod_var: Variable("PodVar".to_string()),
            key: AnchoredKeyKey::Variable(Variable("KeyVar".to_string())),
        });
        assert_eq!(build_anchored_key(pair_var), expected_var);

        // Error cases (parser should catch these).
        assert!(parse_rule(Rule::anchored_key, "PodVar[\"key\"]").is_err()); // Missing `?` on pod var
        assert!(parse_rule(Rule::anchored_key, "?PodVar[invalid]").is_err()); // Invalid key type (not var or string lit)
        assert!(parse_rule(Rule::anchored_key, "?PodVar[]").is_err()); // Empty key
    }

    // Helper to parse and build a statement
    fn build_test_statement(input: &str) -> Result<Statement, AstBuildError> {
        let pair = parse_rule(Rule::statement, input)
            .map_err(|e| AstBuildError::Internal(format!("Parser failed for statement: {}", e)))?;
        build_statement(pair)
    }

    #[test]
    fn test_build_statement() {
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

        let input_priv = r#"with_priv(Pub, private: Priv1, Priv2) = OR(
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

        let input_empty = "REQUEST()";
        let result_empty = build_test_request(input_empty);
        let expected_empty = Ok(RequestDefinition { statements: vec![] });
        assert_eq!(result_empty, expected_empty);

        let input_comments = r#"REQUEST(
            // Comment line
            Gt(?Val["x"], ?Other["y"])
            // Another comment
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
                        Argument::AnchoredKey(AnchoredKey {
                            pod_var: Variable("Other".to_string()),
                            key: AnchoredKeyKey::LiteralString("y".to_string()),
                        }),
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
        let input_full = r#"
            // Predicate definition
            pred(X) = AND(
                Gt(?X["a"], ?X["b"])
            )

            // Request definition
            REQUEST(
                pred(?MyData)
                Lt(?MyData["b"], ?Z["z"])
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
                    Argument::AnchoredKey(AnchoredKey {
                        pod_var: Variable("X".to_string()),
                        key: AnchoredKeyKey::LiteralString("b".to_string()),
                    }),
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
                        Argument::AnchoredKey(AnchoredKey {
                            pod_var: Variable("Z".to_string()),
                            key: AnchoredKeyKey::LiteralString("z".to_string()),
                        }),
                    ],
                }),
            ],
        });
        let expected_full = Ok(Document {
            definitions: vec![expected_pred, expected_req],
        });
        assert_eq!(result_full, expected_full);

        let input_empty = "// comment 1\n   // comment 2 \n \n";
        let result_empty = build_test_document(input_empty);
        let expected_empty_doc = Ok(Document {
            definitions: vec![],
        });
        assert_eq!(result_empty, expected_empty_doc);

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

        let input_mixed = r#"
            REQUEST(
                pred1(?A)
            )
            pred2(Y) = OR(
                Equal(?Y["foo"], ?Y["bar"])
            )
            pred1(X) = AND(
                Equal(?X["foo"], ?X["bar"])
            )
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
            statements: vec![Statement::Native(NativePredicateCall {
                predicate: NativePredicate::Equal,
                args: vec![
                    Argument::AnchoredKey(AnchoredKey {
                        pod_var: Variable("Y".to_string()),
                        key: AnchoredKeyKey::LiteralString("foo".to_string()),
                    }),
                    Argument::AnchoredKey(AnchoredKey {
                        pod_var: Variable("Y".to_string()),
                        key: AnchoredKeyKey::LiteralString("bar".to_string()),
                    }),
                ],
            })],
        });
        let expected_pred1_mixed = TopLevelDefinition::CustomPredicate(CustomPredicateDefinition {
            name: Identifier("pred1".to_string()),
            public_args: vec![Variable("X".to_string())],
            private_args: vec![],
            type_: CustomPredicateType::And,
            statements: vec![Statement::Native(NativePredicateCall {
                predicate: NativePredicate::Equal,
                args: vec![
                    Argument::AnchoredKey(AnchoredKey {
                        pod_var: Variable("X".to_string()),
                        key: AnchoredKeyKey::LiteralString("foo".to_string()),
                    }),
                    Argument::AnchoredKey(AnchoredKey {
                        pod_var: Variable("X".to_string()),
                        key: AnchoredKeyKey::LiteralString("bar".to_string()),
                    }),
                ],
            })],
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
