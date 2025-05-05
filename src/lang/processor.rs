// src/lang/processor.rs

use std::{
    collections::{BTreeMap, HashMap, HashSet},
    sync::Arc,
};

use hex;
use plonky2::field::types::Field;

use crate::{
    lang::ast::{self, TopLevelDefinition},
    middleware::{
        self, basetypes::VALUE_SIZE, CustomPredicate, CustomPredicateBatch, Key, KeyOrWildcard,
        NativePredicate, Params, Predicate, StatementTmpl, StatementTmplArg, Value, Wildcard, F,
    },
};

// Using thiserror for structured processor errors
#[derive(thiserror::Error, Debug)]
pub enum ProcessorError {
    #[error("Semantic error: {0}")]
    Semantic(String),
    // TODO: Add span information to errors
    // #[error("Error at {span:?}: {message}")]
    // WithSpan { message: String, span: (usize, usize) },
    #[error("Undefined identifier: {0}")] // Can be variable or predicate name
    UndefinedIdentifier(String),
    #[error("Duplicate definition: {0}")]
    DuplicateDefinition(String),
    #[error("Duplicate variable: ?{0}")] // Prefix with ? for clarity
    DuplicateVariable(String),
    #[error("Expected {expected}, found {found}")]
    TypeError { expected: String, found: String },
    #[error("Invalid argument count for {predicate}: expected {expected}, found {found}")]
    ArgumentCountMismatch {
        predicate: String,
        expected: usize,
        found: usize,
    },
    #[error("Multiple REQUEST definitions found. Only one is allowed.")]
    MultipleRequestDefinitions,
    #[error("Internal processing error: {0}")]
    Internal(String), // For unexpected issues
    #[error("Middleware error: {0}")]
    Middleware(#[from] middleware::Error),
}

/// Holds the processed output: a single batch of custom predicates
/// and the list of statement templates for the main request.
#[derive(Debug, Clone, PartialEq)] // Removed Default
pub struct ProcessedOutput {
    pub custom_batch: Arc<CustomPredicateBatch>,
    pub request_templates: Vec<StatementTmpl>,
}

/// Context used during the processing phase.
/// Contains parameters and information gathered in the first pass.
struct ProcessingContext<'a> {
    params: &'a Params,
    /// Maps custom predicate names to their index and public arity.
    custom_predicate_signatures: HashMap<String, (usize, usize)>, // (index, public_args_len)
}

/// Context specific to processing statements within a single definition (predicate or request).
struct ScopeContext<'a> {
    processing_ctx: &'a ProcessingContext<'a>,
    /// Maps variable name to its Wildcard (index + name).
    /// We use BTreeMap to ensure deterministic iteration order if needed later.
    variables: BTreeMap<String, Wildcard>,
    next_wildcard_index: usize,
}

/// Processes the parsed Podlog AST into middleware structures.
///
/// Takes the AST `Document` and `Params` (needed for middleware validation).
/// Returns the processed output or an error.
pub fn process_document(
    document: ast::Document,
    params: &Params,
) -> Result<ProcessedOutput, ProcessorError> {
    let mut custom_definitions = Vec::new();
    let mut request_definition: Option<ast::RequestDefinition> = None;
    let mut defined_names = HashSet::new(); // Track defined predicate names

    // 1. Separate definitions and check for duplicates/multiple requests
    for definition in document.definitions {
        match definition {
            TopLevelDefinition::CustomPredicate(pred_def) => {
                let name = &pred_def.name.0;
                if defined_names.contains(name) {
                    return Err(ProcessorError::DuplicateDefinition(name.clone()));
                }
                defined_names.insert(name.clone());
                custom_definitions.push(pred_def);
            }
            TopLevelDefinition::Request(req_def) => {
                if request_definition.is_some() {
                    return Err(ProcessorError::MultipleRequestDefinitions);
                }
                request_definition = Some(req_def);
            }
        }
    }

    // --- First Pass: Collect Signatures ---
    let mut custom_predicate_signatures = HashMap::new();
    for (index, pred_def) in custom_definitions.iter().enumerate() {
        let name = &pred_def.name.0;
        let public_arity = pred_def.public_args.len();
        custom_predicate_signatures.insert(name.clone(), (index, public_arity));
    }

    // --- Second Pass: Process Bodies ---
    let processing_ctx = ProcessingContext {
        params,
        custom_predicate_signatures,
    };

    // Process Custom Predicate Bodies
    let mut processed_custom_predicates = Vec::with_capacity(custom_definitions.len());
    for pred_def in custom_definitions {
        // Use the context built from the first pass
        let middleware_pred = process_custom_predicate_body(pred_def, &processing_ctx)?;
        processed_custom_predicates.push(middleware_pred);
    }

    let custom_batch = Arc::new(CustomPredicateBatch {
        name: "PodlogBatch".to_string(), // TODO: Allow batch name configuration later?
        predicates: processed_custom_predicates, // Use the processed predicates
    });

    // Check batch size limit
    if custom_batch.predicates.len() > params.max_custom_batch_size {
        return Err(ProcessorError::Middleware(middleware::Error::max_length(
            "custom predicates".to_string(),
            custom_batch.predicates.len(),
            params.max_custom_batch_size,
        )));
    }

    // Process Request (if exists) using the same context
    let request_templates = if let Some(req_def) = request_definition {
        process_request(req_def, &processing_ctx)? // Pass the context
    } else {
        Vec::new() // No request defined
    };

    Ok(ProcessedOutput {
        custom_batch,
        request_templates,
    })
}

// --- Renamed Helper Function ---

// Processes the body of a custom predicate definition using the pre-built context.
fn process_custom_predicate_body(
    pred_def: ast::CustomPredicateDefinition,
    processing_ctx: &ProcessingContext,
) -> Result<CustomPredicate, ProcessorError> {
    let mut scope = ScopeContext {
        processing_ctx, // Pass the main context
        variables: BTreeMap::new(),
        next_wildcard_index: 0,
    };

    // Register public args
    for arg_var in &pred_def.public_args {
        let name = &arg_var.0;
        if scope.variables.contains_key(name) {
            return Err(ProcessorError::DuplicateVariable(name.clone()));
        }
        let index = scope.next_wildcard_index;
        scope.variables.insert(
            name.clone(),
            Wildcard {
                name: name.clone(),
                index,
            },
        );
        scope.next_wildcard_index += 1;
    }
    let public_args_len = pred_def.public_args.len(); // Already checked against params in first pass

    // Register private args
    for arg_var in &pred_def.private_args {
        let name = &arg_var.0;
        if scope.variables.contains_key(name) {
            return Err(ProcessorError::DuplicateVariable(name.clone()));
        }
        let index = scope.next_wildcard_index;
        scope.variables.insert(
            name.clone(),
            Wildcard {
                name: name.clone(),
                index,
            },
        );
        scope.next_wildcard_index += 1;
    }

    // Check total wildcard limit
    let total_wildcards = scope.next_wildcard_index;
    if total_wildcards > processing_ctx.params.max_custom_predicate_wildcards {
        return Err(ProcessorError::Middleware(middleware::Error::max_length(
            format!("wildcards in predicate {}", pred_def.name.0),
            total_wildcards,
            processing_ctx.params.max_custom_predicate_wildcards,
        )));
    }

    // Process statements
    let mut middleware_statements = Vec::with_capacity(pred_def.statements.len());
    for statement in pred_def.statements {
        // Pass the scope which contains the processing_ctx reference
        middleware_statements.push(process_statement(statement, &mut scope, false)?);
    }

    let conjunction = match pred_def.type_ {
        ast::CustomPredicateType::And => true,
        ast::CustomPredicateType::Or => false,
    };

    // Construct the middleware CustomPredicate
    // Arity check for the definition itself happened in the first pass.
    // Arity checks for calls *within* the body happened in process_statement.
    let middleware_pred = CustomPredicate::new(
        pred_def.name.0,
        processing_ctx.params, // Pass params for internal middleware checks
        conjunction,
        middleware_statements,
        public_args_len,
    )?; // Propagate potential middleware errors

    Ok(middleware_pred)
}

// --- Existing process_request, process_statement etc need minor adjustments ---

// Processes the body of a request using the pre-built context.
fn process_request(
    req_def: ast::RequestDefinition,
    processing_ctx: &ProcessingContext, // Changed parameter
) -> Result<Vec<StatementTmpl>, ProcessorError> {
    let mut scope = ScopeContext {
        processing_ctx, // Pass the context
        variables: BTreeMap::new(),
        next_wildcard_index: 0,
    };

    let mut request_templates = Vec::with_capacity(req_def.statements.len());

    for statement in req_def.statements {
        // process_statement now uses the processing_ctx within scope
        request_templates.push(process_statement(statement, &mut scope, true)?);
    }

    // Check request template count limit
    if request_templates.len() > processing_ctx.params.max_statements {
        return Err(ProcessorError::Middleware(middleware::Error::max_length(
            "request statements".to_string(),
            request_templates.len(),
            processing_ctx.params.max_statements,
        )));
    }

    Ok(request_templates)
}

fn process_statement(
    statement: ast::Statement,
    scope: &mut ScopeContext,
    create_vars_if_missing: bool,
) -> Result<StatementTmpl, ProcessorError> {
    match statement {
        ast::Statement::Native(call) => {
            let middleware_args: Result<Vec<_>, _> = call
                .args
                .into_iter()
                .map(|arg| process_argument(arg, scope, create_vars_if_missing))
                .collect();
            let middleware_args = middleware_args?;
            let middleware_pred = map_native_predicate(call.predicate);

            check_native_arity(middleware_pred, middleware_args.len())?;

            Ok(StatementTmpl {
                pred: Predicate::Native(middleware_pred),
                args: middleware_args,
            })
        }
        ast::Statement::Custom(call) => {
            let pred_name = &call.name.0;
            // Use signatures from the context within the scope
            let (pred_index, expected_arity) = scope
                .processing_ctx
                .custom_predicate_signatures
                .get(pred_name)
                .ok_or_else(|| ProcessorError::UndefinedIdentifier(pred_name.clone()))?; // Use UndefinedIdentifier

            let middleware_args: Result<Vec<_>, _> = call
                .args
                .into_iter()
                .map(|arg| process_argument(arg, scope, create_vars_if_missing))
                .collect();
            let middleware_args = middleware_args?;

            // Arity check for custom predicate call
            if middleware_args.len() != *expected_arity {
                return Err(ProcessorError::ArgumentCountMismatch {
                    predicate: pred_name.clone(),
                    expected: *expected_arity,
                    found: middleware_args.len(),
                });
            }

            // Check arg count limit for the statement itself
            if middleware_args.len() > scope.processing_ctx.params.max_statement_args {
                return Err(ProcessorError::Middleware(middleware::Error::max_length(
                    format!("arguments for custom call to {}", pred_name),
                    middleware_args.len(),
                    scope.processing_ctx.params.max_statement_args,
                )));
            }

            Ok(StatementTmpl {
                pred: Predicate::BatchSelf(*pred_index), // Use the index from signatures
                args: middleware_args,
            })
        }
    }
}

fn process_argument(
    arg: ast::Argument,
    scope: &mut ScopeContext,
    create_if_missing: bool,
) -> Result<StatementTmplArg, ProcessorError> {
    match arg {
        ast::Argument::Literal(lit) => {
            let value = process_literal(lit)?;
            Ok(StatementTmplArg::Literal(value))
        }
        ast::Argument::Variable(var) => {
            let wildcard = resolve_variable(var, scope, create_if_missing)?;
            Ok(StatementTmplArg::WildcardLiteral(wildcard))
        }
        ast::Argument::AnchoredKey(ak) => {
            let pod_wildcard = resolve_variable(ak.pod_var, scope, create_if_missing)?;
            let key_or_wildcard = match ak.key {
                ast::AnchoredKeyKey::LiteralString(s) => KeyOrWildcard::Key(Key::new(s)),
                ast::AnchoredKeyKey::Variable(var) => {
                    let key_wildcard = resolve_variable(var, scope, create_if_missing)?;
                    KeyOrWildcard::Wildcard(key_wildcard)
                }
            };
            Ok(StatementTmplArg::Key(pod_wildcard, key_or_wildcard))
        }
    }
}

// Converts an AST Literal to a middleware Value
fn process_literal(literal: ast::Literal) -> Result<Value, ProcessorError> {
    match literal {
        ast::Literal::Int(i) => Ok(Value::from(i)),
        ast::Literal::Bool(b) => Ok(Value::from(b)),
        ast::Literal::String(s) => Ok(Value::from(s)),
        ast::Literal::Raw(bytes) => {
            const MAX_RAW_BYTES: usize = VALUE_SIZE * 8; // 4 * 8 = 32 bytes
            if bytes.len() > MAX_RAW_BYTES {
                return Err(ProcessorError::Semantic(format!(
                    "Raw literal 0x{} is too long (max {} bytes)",
                    hex::encode(&bytes),
                    MAX_RAW_BYTES
                )));
            }
            // Encode bytes back to hex string
            let hex_str = hex::encode(&bytes);
            // Pad with leading zeros to 64 characters (representing 32 bytes)
            let padded_hex_str = format!("{:0>64}", hex_str);
            // Parse the 64-char hex string into [F; VALUE_SIZE]
            parse_hex_to_raw_value(&padded_hex_str).map(Value::from)
        }
        ast::Literal::Array(elements) => {
            let processed_elements = elements
                .into_iter()
                .map(process_literal)
                .collect::<Result<Vec<_>, _>>()?;
            let middleware_array = middleware::containers::Array::new(processed_elements)
                .map_err(|e| ProcessorError::Internal(format!("Failed to create Array: {}", e)))?;
            Ok(Value::from(middleware_array))
        }
        ast::Literal::Set(elements) => {
            let processed_elements = elements
                .into_iter()
                .map(process_literal)
                .collect::<Result<HashSet<_>, _>>()?;
            let middleware_set = middleware::containers::Set::new(processed_elements)
                .map_err(|e| ProcessorError::Internal(format!("Failed to create Set: {}", e)))?;
            Ok(Value::from(middleware_set))
        }
        ast::Literal::Dict(map) => {
            let processed_map = map
                .into_iter()
                .map(|(k, v)| process_literal(v).map(|val| (Key::new(k), val)))
                .collect::<Result<HashMap<_, _>, _>>()?;
            let middleware_dict =
                middleware::containers::Dictionary::new(processed_map).map_err(|e| {
                    ProcessorError::Internal(format!("Failed to create Dictionary: {}", e))
                })?;
            Ok(Value::from(middleware_dict))
        }
    }
}

// Helper function similar to middleware::serialization::deserialize_field_tuple
fn parse_hex_to_raw_value(hex_str: &str) -> Result<middleware::RawValue, ProcessorError> {
    if hex_str.len() != 64 {
        return Err(ProcessorError::Internal(format!(
            "Internal error: Expected 64 hex chars for RawValue, got {}",
            hex_str.len()
        )));
    }
    if !hex_str.chars().all(|c| c.is_ascii_hexdigit()) {
        return Err(ProcessorError::Internal(format!(
            "Internal error: Invalid hex char found in {}",
            hex_str
        )));
    }

    let mut v = [F::ZERO; VALUE_SIZE];
    for (i, element) in v.iter_mut().enumerate() {
        let start = i * 16;
        let end = start + 16;
        let hex_part = &hex_str[start..end];
        *element = F::from_canonical_u64(u64::from_str_radix(hex_part, 16).map_err(|e| {
            ProcessorError::Internal(format!("Failed to parse hex chunk '{}': {}", hex_part, e))
        })?);
    }
    Ok(middleware::RawValue(v))
}

// Resolves a variable name within the current scope.
// For custom predicates, `create_if_missing` should be false.
// For requests, `create_if_missing` should be true.
fn resolve_variable(
    var: ast::Variable,
    scope: &mut ScopeContext,
    create_if_missing: bool, // Flag to control behavior for requests
) -> Result<Wildcard, ProcessorError> {
    let var_name = &var.0;
    if let Some(wildcard) = scope.variables.get(var_name) {
        Ok(wildcard.clone())
    } else if create_if_missing {
        let index = scope.next_wildcard_index;
        // Check wildcard limit before adding
        // Use max_custom_predicate_wildcards limit even for request wildcards for consistency? Check Params def.
        // Assuming the same limit applies for now.
        if index >= scope.processing_ctx.params.max_custom_predicate_wildcards {
            return Err(ProcessorError::Middleware(middleware::Error::max_length(
                "wildcards in request".to_string(), // Clarify context
                index + 1,                          // We are about to add one more
                scope.processing_ctx.params.max_custom_predicate_wildcards,
            )));
        }
        let new_wildcard = Wildcard {
            name: var_name.clone(),
            index,
        };
        scope
            .variables
            .insert(var_name.clone(), new_wildcard.clone());
        scope.next_wildcard_index += 1;
        Ok(new_wildcard)
    } else {
        // If variable is not found in predicate scope (create_if_missing=false)
        Err(ProcessorError::UndefinedIdentifier(var_name.clone())) // Use UndefinedIdentifier
    }
}

// Helper to map AST NativePredicate to middleware::NativePredicate
fn map_native_predicate(ast_pred: ast::NativePredicate) -> NativePredicate {
    match ast_pred {
        ast::NativePredicate::ValueOf => NativePredicate::ValueOf,
        ast::NativePredicate::Equal => NativePredicate::Equal,
        ast::NativePredicate::NotEqual => NativePredicate::NotEqual,
        ast::NativePredicate::Gt => NativePredicate::Gt,
        ast::NativePredicate::Lt => NativePredicate::Lt,
        ast::NativePredicate::Contains => NativePredicate::Contains,
        ast::NativePredicate::NotContains => NativePredicate::NotContains,
        ast::NativePredicate::SumOf => NativePredicate::SumOf,
        ast::NativePredicate::ProductOf => NativePredicate::ProductOf,
        ast::NativePredicate::MaxOf => NativePredicate::MaxOf,
    }
}

// Helper to check argument count for native predicates
fn check_native_arity(pred: NativePredicate, args_len: usize) -> Result<(), ProcessorError> {
    let (expected_min, expected_max) = match pred {
        NativePredicate::ValueOf => (2, 2),
        NativePredicate::Equal => (2, 2),
        NativePredicate::NotEqual => (2, 2),
        NativePredicate::Gt => (2, 2),
        NativePredicate::Lt => (2, 2),
        NativePredicate::Contains => (3, 3),
        NativePredicate::NotContains => (2, 2),
        NativePredicate::SumOf => (3, 3),
        NativePredicate::ProductOf => (3, 3),
        NativePredicate::MaxOf => (3, 3),
        NativePredicate::None => (0, 0),
        // Syntactic sugar predicates shouldn't reach here in processor
        _ => {
            return Err(ProcessorError::Internal(format!(
                "Unexpected native predicate {:?} in arity check",
                pred
            )))
        }
    };

    if args_len < expected_min || args_len > expected_max {
        Err(ProcessorError::ArgumentCountMismatch {
            predicate: format!("{:?}", pred),
            // For simplicity, just show expected min if range is used (though currently all are fixed)
            expected: expected_min,
            found: args_len,
        })
    } else {
        Ok(())
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::{
        lang::ast::{
            AnchoredKey, AnchoredKeyKey, Argument, CustomPredicateCall, CustomPredicateDefinition,
            CustomPredicateType, Document, Identifier, Literal, NativePredicateCall, Statement,
            TopLevelDefinition, Variable,
        },
        middleware::{KeyOrWildcard, NativePredicate as MwNativePred, Predicate as MwPredicate},
    };

    // Helper to create Variable
    fn var(name: &str) -> Variable {
        Variable(name.to_string())
    }

    // Helper to create Identifier
    fn ident(name: &str) -> Identifier {
        Identifier(name.to_string())
    }

    #[test]
    fn test_process_simple_doc() {
        // Manually construct the AST for:
        // is_eq(A, B) = AND(
        //   Equal(?A["val"], ?B["val"])
        // )
        // REQUEST(
        //   is_eq(?X, ?Y)
        // )

        let is_eq_pred = CustomPredicateDefinition {
            name: ident("is_eq"),
            public_args: vec![var("A"), var("B")],
            private_args: vec![],
            type_: CustomPredicateType::And,
            statements: vec![Statement::Native(NativePredicateCall {
                predicate: ast::NativePredicate::Equal,
                args: vec![
                    Argument::AnchoredKey(AnchoredKey {
                        pod_var: var("A"),
                        key: AnchoredKeyKey::LiteralString("val".to_string()),
                    }),
                    Argument::AnchoredKey(AnchoredKey {
                        pod_var: var("B"),
                        key: AnchoredKeyKey::LiteralString("val".to_string()),
                    }),
                ],
            })],
        };

        let request_def = ast::RequestDefinition {
            statements: vec![Statement::Custom(CustomPredicateCall {
                name: ident("is_eq"),
                args: vec![Argument::Variable(var("X")), Argument::Variable(var("Y"))],
            })],
        };

        let doc = Document {
            definitions: vec![
                TopLevelDefinition::CustomPredicate(is_eq_pred),
                TopLevelDefinition::Request(request_def),
            ],
        };

        let params = Params::default();
        let result = process_document(doc, &params);

        // Assert basic success
        assert!(result.is_ok(), "Processing failed: {:?}", result.err());
        let output = result.unwrap();

        // --- Check Custom Predicate Batch ---
        assert_eq!(output.custom_batch.predicates.len(), 1);
        assert_eq!(output.custom_batch.name, "PodlogBatch");
        let processed_pred = &output.custom_batch.predicates[0];

        assert_eq!(processed_pred.name, "is_eq");
        assert!(processed_pred.conjunction); // AND
        assert_eq!(processed_pred.args_len, 2); // A, B
        assert_eq!(processed_pred.statements.len(), 1);

        // Check the statement inside the custom predicate
        let pred_stmt = &processed_pred.statements[0];
        assert_eq!(pred_stmt.pred, MwPredicate::Native(MwNativePred::Equal));
        assert_eq!(pred_stmt.args.len(), 2);
        // Expected: Equal( ?A["val"], ?B["val"] )
        // ?A -> Wildcard{ name: "A", index: 0 }
        // ?B -> Wildcard{ name: "B", index: 1 }
        // "val" -> KeyOrWildcard::Key
        assert_eq!(
            pred_stmt.args[0],
            StatementTmplArg::Key(
                Wildcard {
                    name: "A".to_string(),
                    index: 0
                },
                KeyOrWildcard::Key(Key::new("val".to_string()))
            )
        );
        assert_eq!(
            pred_stmt.args[1],
            StatementTmplArg::Key(
                Wildcard {
                    name: "B".to_string(),
                    index: 1
                },
                KeyOrWildcard::Key(Key::new("val".to_string()))
            )
        );

        // --- Check Request Templates ---
        assert_eq!(output.request_templates.len(), 1);
        let req_stmt = &output.request_templates[0];

        // Expected: is_eq(?X, ?Y)
        // is_eq -> BatchSelf(0)
        // ?X -> Wildcard { name: "X", index: 0 } (Indices restart in request scope)
        // ?Y -> Wildcard { name: "Y", index: 1 }
        assert_eq!(req_stmt.pred, MwPredicate::BatchSelf(0));
        assert_eq!(req_stmt.args.len(), 2);
        assert_eq!(
            req_stmt.args[0],
            StatementTmplArg::WildcardLiteral(Wildcard {
                name: "X".to_string(),
                index: 0
            })
        );
        assert_eq!(
            req_stmt.args[1],
            StatementTmplArg::WildcardLiteral(Wildcard {
                name: "Y".to_string(),
                index: 1
            })
        );
    }

    #[test]
    fn test_process_private_vars() {
        // is_eq_priv(Pub) = AND(
        //   private(Priv)
        //   Equal(?Pub["pub_key"], ?Priv["priv_key"])
        // )
        let pred_def = CustomPredicateDefinition {
            name: ident("is_eq_priv"),
            public_args: vec![var("Pub")],
            private_args: vec![var("Priv")], // Declare private var
            type_: CustomPredicateType::And,
            statements: vec![Statement::Native(NativePredicateCall {
                predicate: ast::NativePredicate::Equal,
                args: vec![
                    Argument::AnchoredKey(AnchoredKey {
                        pod_var: var("Pub"),
                        key: AnchoredKeyKey::LiteralString("pub_key".to_string()),
                    }),
                    Argument::AnchoredKey(AnchoredKey {
                        pod_var: var("Priv"),
                        key: AnchoredKeyKey::LiteralString("priv_key".to_string()),
                    }),
                ],
            })],
        };

        let doc = Document {
            definitions: vec![TopLevelDefinition::CustomPredicate(pred_def)],
        };
        let params = Params::default();
        let result = process_document(doc, &params);

        assert!(result.is_ok(), "Processing failed: {:?}", result.err());
        let output = result.unwrap();

        assert_eq!(output.custom_batch.predicates.len(), 1);
        let processed_pred = &output.custom_batch.predicates[0];

        assert_eq!(processed_pred.name, "is_eq_priv");
        assert!(processed_pred.conjunction);
        assert_eq!(processed_pred.args_len, 1); // Only Pub is public
        assert_eq!(processed_pred.statements.len(), 1);

        let pred_stmt = &processed_pred.statements[0];
        assert_eq!(pred_stmt.pred, MwPredicate::Native(MwNativePred::Equal));
        assert_eq!(pred_stmt.args.len(), 2);

        // Check wildcards: Pub should be index 0, Priv should be index 1
        assert_eq!(
            pred_stmt.args[0],
            StatementTmplArg::Key(
                Wildcard {
                    name: "Pub".to_string(),
                    index: 0
                },
                KeyOrWildcard::Key(Key::new("pub_key".to_string()))
            )
        );
        assert_eq!(
            pred_stmt.args[1],
            StatementTmplArg::Key(
                Wildcard {
                    name: "Priv".to_string(),
                    index: 1
                }, // Index 1
                KeyOrWildcard::Key(Key::new("priv_key".to_string()))
            )
        );
        // No request, so request_templates should be empty
        assert!(output.request_templates.is_empty());
    }

    #[test]
    fn test_process_literal_args() {
        // process_lits(Data) = AND(
        //   ValueOf(?Data["num"], 123)
        //   ValueOf(?Data["flag"], true)
        //   ValueOf(?Data["msg"], "hello")
        // )
        // REQUEST(
        //   process_lits(?Pod)
        // )
        let pred_def = CustomPredicateDefinition {
            name: ident("process_lits"),
            public_args: vec![var("Data")],
            private_args: vec![],
            type_: CustomPredicateType::And,
            statements: vec![
                Statement::Native(NativePredicateCall {
                    predicate: ast::NativePredicate::ValueOf,
                    args: vec![
                        Argument::AnchoredKey(AnchoredKey {
                            pod_var: var("Data"),
                            key: AnchoredKeyKey::LiteralString("num".to_string()),
                        }),
                        Argument::Literal(Literal::Int(123)),
                    ],
                }),
                Statement::Native(NativePredicateCall {
                    predicate: ast::NativePredicate::ValueOf,
                    args: vec![
                        Argument::AnchoredKey(AnchoredKey {
                            pod_var: var("Data"),
                            key: AnchoredKeyKey::LiteralString("flag".to_string()),
                        }),
                        Argument::Literal(Literal::Bool(true)),
                    ],
                }),
                Statement::Native(NativePredicateCall {
                    predicate: ast::NativePredicate::ValueOf,
                    args: vec![
                        Argument::AnchoredKey(AnchoredKey {
                            pod_var: var("Data"),
                            key: AnchoredKeyKey::LiteralString("msg".to_string()),
                        }),
                        Argument::Literal(Literal::String("hello".to_string())),
                    ],
                }),
            ],
        };

        let request_def = ast::RequestDefinition {
            statements: vec![Statement::Custom(CustomPredicateCall {
                name: ident("process_lits"),
                args: vec![Argument::Variable(var("Pod"))],
            })],
        };

        let doc = Document {
            definitions: vec![
                TopLevelDefinition::CustomPredicate(pred_def),
                TopLevelDefinition::Request(request_def),
            ],
        };

        let params = Params::default();
        let result = process_document(doc, &params);

        assert!(result.is_ok(), "Processing failed: {:?}", result.err());
        let output = result.unwrap();

        // Check predicate processing (ensure literals were handled)
        assert_eq!(output.custom_batch.predicates.len(), 1);
        let processed_pred = &output.custom_batch.predicates[0];
        assert_eq!(processed_pred.statements.len(), 3);

        assert_eq!(
            processed_pred.statements[0].args[1],
            StatementTmplArg::Literal(Value::from(123i64))
        );
        assert_eq!(
            processed_pred.statements[1].args[1],
            StatementTmplArg::Literal(Value::from(true))
        );
        assert_eq!(
            processed_pred.statements[2].args[1],
            StatementTmplArg::Literal(Value::from("hello"))
        );

        // Check request processing
        assert_eq!(output.request_templates.len(), 1);
        let req_stmt = &output.request_templates[0];
        assert_eq!(req_stmt.pred, MwPredicate::BatchSelf(0));
        assert_eq!(req_stmt.args.len(), 1);
        assert_eq!(
            req_stmt.args[0],
            StatementTmplArg::WildcardLiteral(Wildcard {
                name: "Pod".to_string(),
                index: 0
            })
        );
    }

    #[test]
    fn test_process_variable_key() {
        // pred(Pod, KeyVar) = AND(
        //   Equal(?Pod[?KeyVar], ?Pod["fixed_key"])
        // )
        // REQUEST(
        //   pred(?MyPod, ?TheKey)
        // )
        let pred_def = CustomPredicateDefinition {
            name: ident("pred"),
            public_args: vec![var("Pod"), var("KeyVar")],
            private_args: vec![],
            type_: CustomPredicateType::And,
            statements: vec![Statement::Native(NativePredicateCall {
                predicate: ast::NativePredicate::Equal,
                args: vec![
                    Argument::AnchoredKey(AnchoredKey {
                        pod_var: var("Pod"),
                        key: AnchoredKeyKey::Variable(var("KeyVar")), // Variable Key
                    }),
                    Argument::AnchoredKey(AnchoredKey {
                        pod_var: var("Pod"),
                        key: AnchoredKeyKey::LiteralString("fixed_key".to_string()),
                    }),
                ],
            })],
        };

        let request_def = ast::RequestDefinition {
            statements: vec![Statement::Custom(CustomPredicateCall {
                name: ident("pred"),
                args: vec![
                    Argument::Variable(var("MyPod")),
                    Argument::Variable(var("TheKey")),
                ],
            })],
        };

        let doc = Document {
            definitions: vec![
                TopLevelDefinition::CustomPredicate(pred_def),
                TopLevelDefinition::Request(request_def),
            ],
        };

        let params = Params::default();
        let result = process_document(doc, &params);

        assert!(result.is_ok(), "Processing failed: {:?}", result.err());
        let output = result.unwrap();

        // Check predicate processing
        assert_eq!(output.custom_batch.predicates.len(), 1);
        let processed_pred = &output.custom_batch.predicates[0];
        assert_eq!(processed_pred.statements.len(), 1);
        let pred_stmt = &processed_pred.statements[0];

        // ?Pod -> index 0
        // ?KeyVar -> index 1
        assert_eq!(
            pred_stmt.args[0],
            StatementTmplArg::Key(
                Wildcard {
                    name: "Pod".to_string(),
                    index: 0
                },
                KeyOrWildcard::Wildcard(Wildcard {
                    name: "KeyVar".to_string(),
                    index: 1
                })
            )
        );
        assert_eq!(
            pred_stmt.args[1],
            StatementTmplArg::Key(
                Wildcard {
                    name: "Pod".to_string(),
                    index: 0
                },
                KeyOrWildcard::Key(Key::new("fixed_key".to_string()))
            )
        );

        // Check request processing
        assert_eq!(output.request_templates.len(), 1);
        let req_stmt = &output.request_templates[0];
        // ?MyPod -> index 0 (request scope)
        // ?TheKey -> index 1 (request scope)
        assert_eq!(
            req_stmt.args[0],
            StatementTmplArg::WildcardLiteral(Wildcard {
                name: "MyPod".to_string(),
                index: 0
            })
        );
        assert_eq!(
            req_stmt.args[1],
            StatementTmplArg::WildcardLiteral(Wildcard {
                name: "TheKey".to_string(),
                index: 1
            })
        );
    }

    #[test]
    fn test_process_multiple_predicates() {
        // pred1(X) = AND( Equal(?X["a"], ?X["b"]) )
        // pred2(Y) = AND( pred1(?Y) )
        // REQUEST( pred2(?Z) )

        let pred1_def = CustomPredicateDefinition {
            name: ident("pred1"),
            public_args: vec![var("X")],
            private_args: vec![],
            type_: CustomPredicateType::And,
            statements: vec![Statement::Native(NativePredicateCall {
                predicate: ast::NativePredicate::Equal,
                args: vec![
                    Argument::AnchoredKey(AnchoredKey {
                        pod_var: var("X"),
                        key: AnchoredKeyKey::LiteralString("a".to_string()),
                    }),
                    Argument::AnchoredKey(AnchoredKey {
                        pod_var: var("X"),
                        key: AnchoredKeyKey::LiteralString("b".to_string()),
                    }),
                ],
            })],
        };

        let pred2_def = CustomPredicateDefinition {
            name: ident("pred2"),
            public_args: vec![var("Y")],
            private_args: vec![],
            type_: CustomPredicateType::And,
            statements: vec![Statement::Custom(CustomPredicateCall {
                name: ident("pred1"), // Call the first predicate
                args: vec![Argument::Variable(var("Y"))],
            })],
        };

        let request_def = ast::RequestDefinition {
            statements: vec![Statement::Custom(CustomPredicateCall {
                name: ident("pred2"),
                args: vec![Argument::Variable(var("Z"))],
            })],
        };

        let doc = Document {
            definitions: vec![
                TopLevelDefinition::CustomPredicate(pred1_def),
                TopLevelDefinition::CustomPredicate(pred2_def),
                TopLevelDefinition::Request(request_def),
            ],
        };

        let params = Params::default();
        let result = process_document(doc, &params);

        assert!(result.is_ok(), "Processing failed: {:?}", result.err());
        let output = result.unwrap();

        // Check batch
        assert_eq!(output.custom_batch.predicates.len(), 2);
        let processed_pred1 = &output.custom_batch.predicates[0];
        let processed_pred2 = &output.custom_batch.predicates[1];

        // Basic checks on pred1
        assert_eq!(processed_pred1.name, "pred1");
        assert_eq!(processed_pred1.args_len, 1);
        assert_eq!(processed_pred1.statements.len(), 1);

        // Basic checks on pred2
        assert_eq!(processed_pred2.name, "pred2");
        assert_eq!(processed_pred2.args_len, 1);
        assert_eq!(processed_pred2.statements.len(), 1);

        // Check statement inside pred2 calls pred1 (index 0)
        let pred2_stmt = &processed_pred2.statements[0];
        assert_eq!(pred2_stmt.pred, MwPredicate::BatchSelf(0)); // Calls pred1 at index 0
        assert_eq!(pred2_stmt.args.len(), 1);
        assert_eq!(
            pred2_stmt.args[0],
            StatementTmplArg::WildcardLiteral(Wildcard {
                name: "Y".to_string(),
                index: 0
            })
        );

        // Check request calls pred2 (index 1)
        assert_eq!(output.request_templates.len(), 1);
        let req_stmt = &output.request_templates[0];
        assert_eq!(req_stmt.pred, MwPredicate::BatchSelf(1)); // Calls pred2 at index 1
        assert_eq!(req_stmt.args.len(), 1);
        assert_eq!(
            req_stmt.args[0],
            StatementTmplArg::WildcardLiteral(Wildcard {
                name: "Z".to_string(),
                index: 0
            })
        );
    }

    #[test]
    fn test_process_errors() {
        let params = Params::default();

        // Error: Duplicate Predicate Definition
        let doc_dup_pred = Document {
            definitions: vec![
                TopLevelDefinition::CustomPredicate(CustomPredicateDefinition {
                    name: ident("dup"),
                    public_args: vec![],
                    private_args: vec![],
                    type_: CustomPredicateType::And,
                    statements: vec![],
                }),
                TopLevelDefinition::CustomPredicate(CustomPredicateDefinition {
                    name: ident("dup"),
                    public_args: vec![],
                    private_args: vec![],
                    type_: CustomPredicateType::And,
                    statements: vec![],
                }),
            ],
        };
        let result = process_document(doc_dup_pred, &params);
        assert!(matches!(result, Err(ProcessorError::DuplicateDefinition(name)) if name == "dup"));

        // Error: Multiple Request Definitions
        let doc_multi_req = Document {
            definitions: vec![
                TopLevelDefinition::Request(ast::RequestDefinition { statements: vec![] }),
                TopLevelDefinition::Request(ast::RequestDefinition { statements: vec![] }),
            ],
        };
        let result = process_document(doc_multi_req, &params);
        assert!(matches!(
            result,
            Err(ProcessorError::MultipleRequestDefinitions)
        ));

        // Error: Duplicate Variable (Public/Private)
        let doc_dup_var = Document {
            definitions: vec![TopLevelDefinition::CustomPredicate(
                CustomPredicateDefinition {
                    name: ident("dup_var_pred"),
                    public_args: vec![var("A")],
                    private_args: vec![var("A")], // Duplicate!
                    type_: CustomPredicateType::And,
                    statements: vec![],
                },
            )],
        };
        let result = process_document(doc_dup_var, &params);
        assert!(matches!(result, Err(ProcessorError::DuplicateVariable(name)) if name == "A"));

        // Error: Undefined Variable (in Predicate Body)
        let doc_undef_var = Document {
            definitions: vec![TopLevelDefinition::CustomPredicate(
                CustomPredicateDefinition {
                    name: ident("undef_var_pred"),
                    public_args: vec![var("A")],
                    private_args: vec![],
                    type_: CustomPredicateType::And,
                    statements: vec![Statement::Native(NativePredicateCall {
                        // Uses ?B which is not defined
                        predicate: ast::NativePredicate::Equal,
                        args: vec![
                            Argument::AnchoredKey(AnchoredKey {
                                pod_var: var("A"),
                                key: AnchoredKeyKey::LiteralString("k".into()),
                            }),
                            Argument::AnchoredKey(AnchoredKey {
                                pod_var: var("B"),
                                key: AnchoredKeyKey::LiteralString("k".into()),
                            }),
                        ],
                    })],
                },
            )],
        };
        let result = process_document(doc_undef_var, &params);
        assert!(matches!(result, Err(ProcessorError::UndefinedIdentifier(name)) if name == "B"));

        // Error: Undefined Predicate (in Request)
        let doc_undef_pred_call = Document {
            definitions: vec![TopLevelDefinition::Request(ast::RequestDefinition {
                statements: vec![Statement::Custom(CustomPredicateCall {
                    // Calls undefined "missing_pred"
                    name: ident("missing_pred"),
                    args: vec![],
                })],
            })],
        };
        let result = process_document(doc_undef_pred_call, &params);
        assert!(
            matches!(result, Err(ProcessorError::UndefinedIdentifier(name)) if name == "missing_pred")
        );

        // Error: Arity Mismatch (Native)
        let doc_arity_native = Document {
            definitions: vec![TopLevelDefinition::Request(ast::RequestDefinition {
                statements: vec![Statement::Native(NativePredicateCall {
                    predicate: ast::NativePredicate::Equal,   // Expects 2 args
                    args: vec![Argument::Variable(var("X"))], // Only 1 provided
                })],
            })],
        };
        let result = process_document(doc_arity_native, &params);
        assert!(
            matches!(result, Err(ProcessorError::ArgumentCountMismatch { predicate, expected, found }) if predicate == "Equal" && expected == 2 && found == 1)
        );

        // Error: Arity Mismatch (Custom Call in Request)
        let doc_arity_custom = Document {
            definitions: vec![
                TopLevelDefinition::CustomPredicate(CustomPredicateDefinition {
                    name: ident("arity_pred"),
                    public_args: vec![var("P1"), var("P2")], // Expects 2 args
                    private_args: vec![],
                    type_: CustomPredicateType::And,
                    statements: vec![],
                }),
                TopLevelDefinition::Request(ast::RequestDefinition {
                    statements: vec![Statement::Custom(CustomPredicateCall {
                        name: ident("arity_pred"),
                        args: vec![Argument::Variable(var("X"))], // Only 1 provided
                    })],
                }),
            ],
        };
        let result = process_document(doc_arity_custom, &params);
        assert!(
            matches!(result, Err(ProcessorError::ArgumentCountMismatch { predicate, expected, found }) if predicate == "arity_pred" && expected == 2 && found == 1)
        );
    }

    #[test]
    fn test_process_request_variations() {
        let params = Params::default();

        // Document with predicate but no request
        let doc_no_req = Document {
            definitions: vec![TopLevelDefinition::CustomPredicate(
                CustomPredicateDefinition {
                    name: ident("no_req_pred"),
                    public_args: vec![],
                    private_args: vec![],
                    type_: CustomPredicateType::And,
                    statements: vec![],
                },
            )],
        };
        let result_no_req = process_document(doc_no_req, &params);
        assert!(result_no_req.is_ok());
        let output_no_req = result_no_req.unwrap(); // Store unwrapped value
        assert_eq!(output_no_req.request_templates.len(), 0);
        assert_eq!(output_no_req.custom_batch.predicates.len(), 1);

        // Document with only a request
        let doc_req_only = Document {
            definitions: vec![TopLevelDefinition::Request(ast::RequestDefinition {
                statements: vec![Statement::Native(NativePredicateCall {
                    predicate: ast::NativePredicate::Equal,
                    args: vec![Argument::Variable(var("X")), Argument::Variable(var("Y"))],
                })],
            })],
        };
        let result_req_only = process_document(doc_req_only, &params);
        assert!(result_req_only.is_ok());
        let output_req_only = result_req_only.unwrap(); // Store unwrapped value
        assert_eq!(output_req_only.request_templates.len(), 1);
        assert_eq!(output_req_only.custom_batch.predicates.len(), 0);

        // Document with empty request
        let doc_empty_req = Document {
            definitions: vec![TopLevelDefinition::Request(ast::RequestDefinition {
                statements: vec![],
            })],
        };
        let result_empty_req = process_document(doc_empty_req, &params);
        assert!(result_empty_req.is_ok());
        let output_empty_req = result_empty_req.unwrap(); // Store unwrapped value
        assert_eq!(output_empty_req.request_templates.len(), 0);
        assert_eq!(output_empty_req.custom_batch.predicates.len(), 0);

        // Empty document
        let doc_empty = Document {
            definitions: vec![],
        };
        let result_empty = process_document(doc_empty, &params);
        assert!(result_empty.is_ok());
        let output_empty = result_empty.unwrap(); // Store unwrapped value
        assert_eq!(output_empty.request_templates.len(), 0);
        assert_eq!(output_empty.custom_batch.predicates.len(), 0);
    }

    #[test]
    fn test_process_container_literals() {
        // containers_pred(Pod) = AND(
        //   ValueOf(?Pod["arr"], [1, true])
        //   ValueOf(?Pod["set"], #[ "a", 2 ])
        //   ValueOf(?Pod["dict"], { "k1": false, "k2": [ ] })
        // )
        // REQUEST( containers_pred(?ThePod) )

        let pred_def = CustomPredicateDefinition {
            name: ident("containers_pred"),
            public_args: vec![var("Pod")],
            private_args: vec![],
            type_: CustomPredicateType::And,
            statements: vec![
                // Array
                Statement::Native(NativePredicateCall {
                    predicate: ast::NativePredicate::ValueOf,
                    args: vec![
                        Argument::AnchoredKey(AnchoredKey {
                            pod_var: var("Pod"),
                            key: AnchoredKeyKey::LiteralString("arr".to_string()),
                        }),
                        Argument::Literal(Literal::Array(vec![
                            Literal::Int(1),
                            Literal::Bool(true),
                        ])),
                    ],
                }),
                // Set
                Statement::Native(NativePredicateCall {
                    predicate: ast::NativePredicate::ValueOf,
                    args: vec![
                        Argument::AnchoredKey(AnchoredKey {
                            pod_var: var("Pod"),
                            key: AnchoredKeyKey::LiteralString("set".to_string()),
                        }),
                        Argument::Literal(Literal::Set(vec![
                            Literal::String("a".to_string()),
                            Literal::Int(2),
                        ])),
                    ],
                }),
                // Dict
                Statement::Native(NativePredicateCall {
                    predicate: ast::NativePredicate::ValueOf,
                    args: vec![
                        Argument::AnchoredKey(AnchoredKey {
                            pod_var: var("Pod"),
                            key: AnchoredKeyKey::LiteralString("dict".to_string()),
                        }),
                        Argument::Literal(Literal::Dict(
                            vec![
                                ("k1".to_string(), Literal::Bool(false)),
                                ("k2".to_string(), Literal::Array(vec![])), // Empty nested array
                            ]
                            .into_iter()
                            .collect(),
                        )),
                    ],
                }),
            ],
        };

        let request_def = ast::RequestDefinition {
            statements: vec![Statement::Custom(CustomPredicateCall {
                name: ident("containers_pred"),
                args: vec![Argument::Variable(var("ThePod"))],
            })],
        };

        let doc = Document {
            definitions: vec![
                TopLevelDefinition::CustomPredicate(pred_def),
                TopLevelDefinition::Request(request_def),
            ],
        };

        let params = Params::default();
        let result = process_document(doc, &params);

        assert!(result.is_ok(), "Processing failed: {:?}", result.err());
        let output = result.unwrap();

        // Check predicate processing
        assert_eq!(output.custom_batch.predicates.len(), 1);
        let processed_pred = &output.custom_batch.predicates[0];
        assert_eq!(processed_pred.statements.len(), 3);

        // Expected middleware values
        let expected_arr_val = Value::from(
            middleware::containers::Array::new(vec![Value::from(1i64), Value::from(true)]).unwrap(),
        );
        let expected_set_val = Value::from(
            middleware::containers::Set::new(
                vec![Value::from("a"), Value::from(2i64)]
                    .into_iter()
                    .collect(),
            )
            .unwrap(),
        );
        let expected_dict_val = Value::from(
            middleware::containers::Dictionary::new(
                vec![
                    (Key::new("k1".to_string()), Value::from(false)),
                    (
                        Key::new("k2".to_string()),
                        Value::from(middleware::containers::Array::new(vec![]).unwrap()),
                    ),
                ]
                .into_iter()
                .collect(),
            )
            .unwrap(),
        );

        // Check Array statement
        assert_eq!(processed_pred.statements[0].args.len(), 2);
        assert_eq!(
            processed_pred.statements[0].args[1],
            StatementTmplArg::Literal(expected_arr_val)
        );

        // Check Set statement
        assert_eq!(processed_pred.statements[1].args.len(), 2);
        assert_eq!(
            processed_pred.statements[1].args[1],
            StatementTmplArg::Literal(expected_set_val)
        );

        // Check Dict statement
        assert_eq!(processed_pred.statements[2].args.len(), 2);
        assert_eq!(
            processed_pred.statements[2].args[1],
            StatementTmplArg::Literal(expected_dict_val)
        );

        // Check request processing
        assert_eq!(output.request_templates.len(), 1);
        let req_stmt = &output.request_templates[0];
        assert_eq!(req_stmt.pred, MwPredicate::BatchSelf(0));
        assert_eq!(req_stmt.args.len(), 1);
        assert_eq!(
            req_stmt.args[0],
            StatementTmplArg::WildcardLiteral(Wildcard {
                name: "ThePod".to_string(),
                index: 0
            })
        );
    }

    #[test]
    fn test_process_forward_reference() {
        // pred_b calls pred_a, but pred_b is defined first
        // pred_b(Y) = AND( pred_a(?Y) )
        // pred_a(X) = AND( Equal(?X["a"], ?X["b"]) )
        // REQUEST( pred_b(?Z) )

        let pred_b_def = CustomPredicateDefinition {
            name: ident("pred_b"),
            public_args: vec![var("Y")],
            private_args: vec![],
            type_: CustomPredicateType::And,
            statements: vec![Statement::Custom(CustomPredicateCall {
                name: ident("pred_a"), // Forward call
                args: vec![Argument::Variable(var("Y"))],
            })],
        };

        let pred_a_def = CustomPredicateDefinition {
            name: ident("pred_a"),
            public_args: vec![var("X")],
            private_args: vec![],
            type_: CustomPredicateType::And,
            statements: vec![Statement::Native(NativePredicateCall {
                predicate: ast::NativePredicate::Equal,
                args: vec![
                    Argument::AnchoredKey(AnchoredKey {
                        pod_var: var("X"),
                        key: AnchoredKeyKey::LiteralString("a".to_string()),
                    }),
                    Argument::AnchoredKey(AnchoredKey {
                        pod_var: var("X"),
                        key: AnchoredKeyKey::LiteralString("b".to_string()),
                    }),
                ],
            })],
        };

        let request_def = ast::RequestDefinition {
            statements: vec![Statement::Custom(CustomPredicateCall {
                name: ident("pred_b"),
                args: vec![Argument::Variable(var("Z"))],
            })],
        };

        let doc = Document {
            definitions: vec![
                TopLevelDefinition::CustomPredicate(pred_b_def), // pred_b first (index 0)
                TopLevelDefinition::CustomPredicate(pred_a_def), // pred_a second (index 1)
                TopLevelDefinition::Request(request_def),
            ],
        };

        let params = Params::default();
        let result = process_document(doc, &params);

        assert!(
            result.is_ok(),
            "Processing failed for forward reference: {:?}",
            result.err()
        );
        let output = result.unwrap();

        // Check batch
        assert_eq!(output.custom_batch.predicates.len(), 2);
        let processed_pred_b = &output.custom_batch.predicates[0]; // Index 0
        let processed_pred_a = &output.custom_batch.predicates[1]; // Index 1

        // Basic checks on pred_b
        assert_eq!(processed_pred_b.name, "pred_b");
        assert_eq!(processed_pred_b.args_len, 1);
        assert_eq!(processed_pred_b.statements.len(), 1);

        // Basic checks on pred_a
        assert_eq!(processed_pred_a.name, "pred_a");
        assert_eq!(processed_pred_a.args_len, 1);
        assert_eq!(processed_pred_a.statements.len(), 1);

        // Check statement inside pred_b calls pred_a (index 1)
        let pred_b_stmt = &processed_pred_b.statements[0];
        assert_eq!(pred_b_stmt.pred, MwPredicate::BatchSelf(1)); // Calls pred_a at index 1
        assert_eq!(pred_b_stmt.args.len(), 1);
        assert_eq!(
            pred_b_stmt.args[0],
            StatementTmplArg::WildcardLiteral(Wildcard {
                name: "Y".to_string(),
                index: 0 // Wildcard index within pred_b scope
            })
        );

        // Check request calls pred_b (index 0)
        assert_eq!(output.request_templates.len(), 1);
        let req_stmt = &output.request_templates[0];
        assert_eq!(req_stmt.pred, MwPredicate::BatchSelf(0)); // Calls pred_b at index 0
        assert_eq!(req_stmt.args.len(), 1);
        assert_eq!(
            req_stmt.args[0],
            StatementTmplArg::WildcardLiteral(Wildcard {
                name: "Z".to_string(),
                index: 0 // Wildcard index within request scope
            })
        );
    }

    #[test]
    fn test_process_error_undefined_identifier() {
        let params = Params::default();
        // Error: Undefined Variable (in Predicate Body) - Now UndefinedIdentifier
        let doc_undef_var = Document {
            definitions: vec![TopLevelDefinition::CustomPredicate(
                CustomPredicateDefinition {
                    name: ident("undef_var_pred"),
                    public_args: vec![var("A")],
                    private_args: vec![],
                    type_: CustomPredicateType::And,
                    statements: vec![Statement::Native(NativePredicateCall {
                        // Uses ?B which is not defined
                        predicate: ast::NativePredicate::Equal,
                        args: vec![
                            Argument::AnchoredKey(AnchoredKey {
                                pod_var: var("A"),
                                key: AnchoredKeyKey::LiteralString("k".into()),
                            }),
                            Argument::AnchoredKey(AnchoredKey {
                                pod_var: var("B"), // Undefined Variable
                                key: AnchoredKeyKey::LiteralString("k".into()),
                            }),
                        ],
                    })],
                },
            )],
        };
        let result = process_document(doc_undef_var, &params);
        assert!(matches!(result, Err(ProcessorError::UndefinedIdentifier(name)) if name == "B"));

        // Error: Undefined Predicate (in Request) - Now UndefinedIdentifier
        let doc_undef_pred_call = Document {
            definitions: vec![TopLevelDefinition::Request(ast::RequestDefinition {
                statements: vec![Statement::Custom(CustomPredicateCall {
                    // Calls undefined "missing_pred"
                    name: ident("missing_pred"), // Undefined Predicate Name
                    args: vec![],
                })],
            })],
        };
        let result = process_document(doc_undef_pred_call, &params);
        assert!(
            matches!(result, Err(ProcessorError::UndefinedIdentifier(name)) if name == "missing_pred")
        );
    }
}
