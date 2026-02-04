//! Podlang front-end: parsing, validation, lowering, and multi-batch output.
//!
//! This module is the high-level entrypoint to the Podlang pipeline. It:
//! - Parses a Podlang document (`parse_podlang`).
//! - Validates names, imports, and well-formedness (`frontend_ast_validate`).
//! - Lowers to middleware structures, including automatic predicate splitting and
//!   dependency-aware packing into one or more custom predicate batches (`frontend_ast_split`,
//!   `frontend_ast_batch`, `frontend_ast_lower`).
//!
//! The result is a [`PodlangOutput`], which contains:
//! - `module`: an optional [`Module`] wrapping a `CustomPredicateBatch` with all custom
//!   predicates defined in the document. Use [`Module::apply_predicate`] to apply a predicate
//!   into a `MainPodBuilder` (recommended primary API), or [`Module::apply_predicate_with`]
//!   for advanced control.
//! - `request`: a `PodRequest` containing the request templates defined by a `REQUEST(...)` block
//!   in the document (or empty if none was provided).
//!
//! Notes
//! - Predicate splitting: large predicates are automatically split into a chain of smaller
//!   predicates while preserving semantics; only the final chain result is public when applying a
//!   predicate as public.
//! - Multi-batch packing: predicates are packed dependency-aware; cross-batch references always
//!   point to earlier batches and forward references cannot occur.
//! - Backwards compatibility: `PodlangOutput::first_batch()` is provided to ease migration of code
//!   that expects a single custom predicate batch.
//!
pub mod error;
pub mod frontend_ast;
pub mod frontend_ast_batch;
pub mod frontend_ast_lower;
pub mod frontend_ast_split;
pub mod frontend_ast_validate;
pub mod parser;
pub mod pretty_print;

use std::{collections::HashMap, sync::Arc};

pub use error::LangError;
pub use frontend_ast_split::{SplitChainInfo, SplitChainPiece, SplitResult};
pub use parser::{parse_podlang, Pairs, ParseError, Rule};
pub use pretty_print::PrettyPrint;

use crate::{
    frontend::{Operation, OperationArg, PodRequest},
    middleware::{CustomPredicateBatch, CustomPredicateRef, Hash, Params, Statement},
};

/// Errors that can occur when applying predicates
#[derive(Debug, Clone, thiserror::Error)]
pub enum MultiOperationError {
    #[error("Predicate not found: {0}")]
    PredicateNotFound(String),

    #[error("Chain piece not found: {0}")]
    ChainPieceNotFound(String),

    #[error(
        "Wrong statement count for predicate '{predicate}': expected {expected}, got {actual}"
    )]
    WrongStatementCount {
        predicate: String,
        expected: usize,
        actual: usize,
    },

    #[error("No operation steps to apply")]
    NoSteps,
}

/// A Podlang module wrapping a middleware CustomPredicateBatch with name resolution info.
#[derive(Debug, Clone)]
pub struct Module {
    /// The middleware representation (CustomPredicateBatch)
    pub batch: Arc<CustomPredicateBatch>,

    /// Map from predicate name to index in batch
    pub predicate_index: HashMap<String, usize>,

    /// Split chain info for predicates that were split
    pub split_chains: HashMap<String, SplitChainInfo>,
}

impl Module {
    /// Create a new Module from a batch, building the predicate_index automatically
    pub fn new(
        batch: Arc<CustomPredicateBatch>,
        split_chains: HashMap<String, SplitChainInfo>,
    ) -> Self {
        let predicate_index = batch
            .predicates()
            .iter()
            .enumerate()
            .map(|(i, p)| (p.name.clone(), i))
            .collect();
        Self {
            batch,
            predicate_index,
            split_chains,
        }
    }

    /// Root hash of the module's Merkle tree
    pub fn id(&self) -> Hash {
        self.batch.id()
    }

    /// Get a reference to a predicate by name
    pub fn predicate_ref_by_name(&self, name: &str) -> Option<CustomPredicateRef> {
        let idx = self.predicate_index.get(name)?;
        Some(CustomPredicateRef::new(self.batch.clone(), *idx))
    }

    /// Check if the module contains any predicates
    pub fn is_empty(&self) -> bool {
        self.batch.predicates().is_empty()
    }

    /// Apply a predicate directly into a `MainPodBuilder` (common case).
    ///
    /// For split predicates, earlier chain links are applied as private, and only the final
    /// piece is applied as public when `public` is true. For non-split predicates, the single
    /// operation is applied with the provided `public` flag.
    ///
    /// Arguments:
    /// - `builder`: target builder to receive operations
    /// - `name`: predicate name
    /// - `statements`: user statements in original declaration order
    /// - `public`: whether the final result should be public
    pub fn apply_predicate(
        &self,
        builder: &mut crate::frontend::MainPodBuilder,
        name: &str,
        statements: Vec<Statement>,
        public: bool,
    ) -> crate::frontend::Result<Statement> {
        self.apply_predicate_with(name, statements, public, |is_public, op| {
            if is_public {
                builder.pub_op(op)
            } else {
                builder.priv_op(op)
            }
        })
    }

    /// Advanced variant: apply using a custom closure.
    ///
    /// Prefer `apply_predicate` for common usage. This method allows callers to intercept each
    /// operation (with its `public` flag) and decide how to execute it.
    ///
    /// Arguments:
    /// - `name`: predicate name
    /// - `statements`: user statements in original declaration order
    /// - `public`: whether the final result should be public
    /// - `apply_op`: closure `(is_public, operation) -> Result<Statement>` used to execute each step
    pub fn apply_predicate_with<F, E>(
        &self,
        name: &str,
        statements: Vec<Statement>,
        public: bool,
        mut apply_op: F,
    ) -> Result<Statement, E>
    where
        F: FnMut(bool, Operation) -> Result<Statement, E>,
        E: From<MultiOperationError>,
    {
        let steps = self.build_steps(name, statements, public)?;

        if steps.is_empty() {
            return Err(MultiOperationError::NoSteps.into());
        }

        let mut prev_result: Option<Statement> = None;

        for step in steps {
            let op = if let Some(prev) = prev_result {
                // Replace the last Statement::None arg with the previous result.
                let mut args = step.operation.1;
                let last = args
                    .last_mut()
                    .expect("chain statement should include placeholder arg");
                assert!(
                    matches!(last, OperationArg::Statement(Statement::None)),
                    "expected last arg to be a Statement::None placeholder"
                );
                *last = OperationArg::Statement(prev);
                Operation(step.operation.0, args, step.operation.2)
            } else {
                step.operation
            };

            prev_result = Some(apply_op(step.public, op)?);
        }

        Ok(prev_result.unwrap())
    }

    /// Build operation steps for a predicate (internal helper)
    fn build_steps(
        &self,
        predicate_name: &str,
        statements: Vec<Statement>,
        public: bool,
    ) -> Result<Vec<OperationStep>, MultiOperationError> {
        // Check if this predicate was split
        let chain_info = match self.split_chains.get(predicate_name) {
            Some(info) => info,
            None => {
                // Not split - single operation with all statements
                let pred_ref = self.predicate_ref_by_name(predicate_name).ok_or_else(|| {
                    MultiOperationError::PredicateNotFound(predicate_name.to_string())
                })?;

                return Ok(vec![OperationStep {
                    operation: Operation::custom(pred_ref, statements),
                    public,
                }]);
            }
        };

        // Validate statement count
        if statements.len() != chain_info.real_statement_count {
            return Err(MultiOperationError::WrongStatementCount {
                predicate: predicate_name.to_string(),
                expected: chain_info.real_statement_count,
                actual: statements.len(),
            });
        }

        // Reorder statements from original order to split order
        let mut reordered = vec![Statement::None; statements.len()];
        for (original_idx, stmt) in statements.into_iter().enumerate() {
            let split_idx = chain_info.reorder_map[original_idx];
            reordered[split_idx] = stmt;
        }

        // Build operations for each piece in execution order
        let num_pieces = chain_info.chain_pieces.len();

        // Compute the starting offset for each piece
        let mut piece_offsets = vec![0usize; num_pieces];
        let mut offset = 0;
        for i in (0..num_pieces).rev() {
            piece_offsets[i] = offset;
            offset += chain_info.chain_pieces[i].real_statement_count;
        }

        let mut steps = Vec::new();
        for (piece_idx, piece) in chain_info.chain_pieces.iter().enumerate() {
            let is_final = piece_idx == num_pieces - 1;

            let piece_ref = self
                .predicate_ref_by_name(&piece.name)
                .ok_or_else(|| MultiOperationError::ChainPieceNotFound(piece.name.clone()))?;

            let start = piece_offsets[piece_idx];
            let end = start + piece.real_statement_count;
            let mut args: Vec<Statement> = reordered[start..end].to_vec();

            if piece.has_chain_call {
                args.push(Statement::None);
            }

            steps.push(OperationStep {
                operation: Operation::custom(piece_ref, args),
                public: public && is_final,
            });
        }

        Ok(steps)
    }
}

/// A single step in a multi-operation sequence for split predicates
struct OperationStep {
    operation: Operation,
    public: bool,
}

/// Final result of processing a Podlang document.
///
/// - `module`: the custom predicates defined in the document (if any). Use `Module::apply_predicate`
///   to apply a predicate into a `MainPodBuilder`.
/// - `request`: the request templates defined in the document (empty if not present).
#[derive(Debug, Clone)]
pub struct PodlangOutput {
    pub module: Option<Module>,
    pub request: PodRequest,
}

impl PodlangOutput {
    /// Get the batch, if any (for backwards compatibility).
    pub fn first_batch(&self) -> Option<&Arc<CustomPredicateBatch>> {
        self.module.as_ref().map(|m| &m.batch)
    }
}

/// Parse, validate, and lower a Podlang document into middleware structures.
///
/// - `input`: Podlang source.
/// - `params`: middleware parameters limiting sizes/arity and controlling lowering behavior.
/// - `available_modules`: external modules available for `use module ...` imports, keyed by name.
///
/// Returns a [`PodlangOutput`] containing the module (if any predicates defined) and a `PodRequest`
/// (possibly empty).
pub fn parse(
    input: &str,
    params: &Params,
    available_modules: &HashMap<String, Arc<Module>>,
) -> Result<PodlangOutput, LangError> {
    let pairs = parse_podlang(input)?;
    let document_pair = pairs
        .into_iter()
        .next()
        .expect("parse_podlang should always return at least one pair for a valid document");
    let document = frontend_ast::parse::parse_document(document_pair)?;
    let validated = frontend_ast_validate::validate(document, available_modules)?;
    let lowered = frontend_ast_lower::lower(validated, params, "PodlangModule".to_string())?;

    let request = lowered.request.unwrap_or_else(|| {
        // If no request, create an empty one
        PodRequest::new(vec![])
    });

    Ok(PodlangOutput {
        module: lowered.module,
        request,
    })
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use hex::ToHex;
    use pretty_assertions::assert_eq;

    use super::*;
    use crate::{
        backends::plonky2::primitives::ec::schnorr::SecretKey,
        middleware::{
            CustomPredicate, CustomPredicateBatch, CustomPredicateRef, Key, NativePredicate,
            Params, Predicate, PredicateOrWildcard, RawValue, StatementTmpl, StatementTmplArg,
            Value, Wildcard, EMPTY_HASH,
        },
    };

    // Helper functions
    fn wc(name: &str, index: usize) -> Wildcard {
        Wildcard::new(name.to_string(), index)
    }

    fn sta_ak(pod_var: (&str, usize), key: &str) -> StatementTmplArg {
        StatementTmplArg::AnchoredKey(wc(pod_var.0, pod_var.1), Key::from(key))
    }

    fn sta_wc_lit(name: &str, index: usize) -> StatementTmplArg {
        StatementTmplArg::Wildcard(wc(name, index))
    }

    fn sta_lit(value: impl Into<Value>) -> StatementTmplArg {
        StatementTmplArg::Literal(value.into())
    }

    fn names(names: &[&str]) -> Vec<String> {
        names.iter().map(|s| s.to_string()).collect()
    }

    fn pred_lit(pred: Predicate) -> PredicateOrWildcard {
        PredicateOrWildcard::Predicate(pred)
    }

    // Helper to get the first batch from the output
    fn first_batch(output: &super::PodlangOutput) -> &Arc<CustomPredicateBatch> {
        output.first_batch().expect("Expected at least one batch")
    }

    #[test]
    fn test_e2e_simple_predicate() -> Result<(), LangError> {
        let input = r#"
            is_equal(PodA, PodB) = AND(
                Equal(PodA["the_key"], PodB["the_key"])
            )
        "#;

        let params = Params::default();
        let processed = parse(input, &params, &HashMap::new())?;
        let batch_result = first_batch(&processed);
        let request_result = processed.request.templates();

        assert_eq!(request_result.len(), 0);
        assert_eq!(batch_result.predicates().len(), 1);

        // Expected structure
        let expected_statements = vec![StatementTmpl {
            pred_or_wc: pred_lit(Predicate::Native(NativePredicate::Equal)),
            args: vec![
                sta_ak(("PodA", 0), "the_key"), // PodA["the_key"] -> Wildcard(0), Key("the_key")
                sta_ak(("PodB", 1), "the_key"), // PodB["the_key"] -> Wildcard(1), Key("the_key")
            ],
        }];
        let expected_predicate = CustomPredicate::and(
            &params,
            "is_equal".to_string(),
            expected_statements,
            2, // args_len (PodA, PodB)
            names(&["PodA", "PodB"]),
        )?;
        let expected_batch =
            CustomPredicateBatch::new("PodlangModule".to_string(), vec![expected_predicate]);

        assert_eq!(*batch_result, expected_batch);

        Ok(())
    }

    #[test]
    fn test_e2e_simple_request() -> Result<(), LangError> {
        let input = r#"
            REQUEST(
                Equal(ConstPod["my_val"], Raw(0x0000000000000000000000000000000000000000000000000000000000000001))
                Lt(GovPod["dob"], ConstPod["my_val"])
            )
        "#;

        let params = Params::default();
        let processed = parse(input, &params, &HashMap::new())?;
        let request_templates = processed.request.templates();

        assert!(processed.module.is_none());
        assert!(!request_templates.is_empty());

        // Expected structure
        let expected_templates = vec![
            StatementTmpl {
                pred_or_wc: pred_lit(Predicate::Native(NativePredicate::Equal)),
                args: vec![
                    sta_ak(("ConstPod", 0), "my_val"), // ConstPod["my_val"] -> Wildcard(0), Key("my_val")
                    sta_lit(RawValue::from(1)),
                ],
            },
            StatementTmpl {
                pred_or_wc: pred_lit(Predicate::Native(NativePredicate::Lt)),
                args: vec![
                    sta_ak(("GovPod", 1), "dob"), // GovPod["dob"] -> Wildcard(1), Key("dob")
                    sta_ak(("ConstPod", 0), "my_val"), // ConstPod["my_val"] -> Wildcard(0), Key("my_val")
                ],
            },
        ];

        assert_eq!(request_templates, expected_templates);

        Ok(())
    }

    #[test]
    fn test_e2e_predicate_with_private_var() -> Result<(), LangError> {
        let input = r#"
            uses_private(A, private: Temp) = AND(
                Equal(A["input_key"], Temp["const_key"])
                Equal(Temp["const_key"], "some_value")
            )
        "#;

        let params = Params::default();
        let processed = parse(input, &params, &HashMap::new())?;
        let batch_result = first_batch(&processed);
        let request_result = processed.request.templates();

        assert_eq!(request_result.len(), 0);
        assert_eq!(batch_result.predicates().len(), 1);

        // Expected structure: Public args: A (index 0). Private args: Temp (index 1)
        let expected_statements = vec![
            StatementTmpl {
                pred_or_wc: pred_lit(Predicate::Native(NativePredicate::Equal)),
                args: vec![
                    sta_ak(("A", 0), "input_key"), // A["input_key"] -> Wildcard(0), Key("input_key")
                    sta_ak(("Temp", 1), "const_key"), // Temp["const_key"] -> Wildcard(1), Key("const_key")
                ],
            },
            StatementTmpl {
                pred_or_wc: pred_lit(Predicate::Native(NativePredicate::Equal)),
                args: vec![
                    sta_ak(("Temp", 1), "const_key"), // Temp["const_key"] -> Wildcard(1), Key("const_key")
                    sta_lit("some_value"),            // Literal("some_value")
                ],
            },
        ];
        let expected_predicate = CustomPredicate::and(
            &params,
            "uses_private".to_string(),
            expected_statements,
            1, // args_len (A)
            names(&["A", "Temp"]),
        )?;
        let expected_batch =
            CustomPredicateBatch::new("PodlangModule".to_string(), vec![expected_predicate]);

        assert_eq!(*batch_result, expected_batch);

        Ok(())
    }

    #[test]
    fn test_e2e_request_with_custom_call() -> Result<(), LangError> {
        let input = r#"
            my_pred(X, Y) = AND(
                Equal(X["val"], Y["val"])
            )

            REQUEST(
                my_pred(Pod1, Pod2)
            )
        "#;

        let params = Params::default();
        let processed = parse(input, &params, &HashMap::new())?;
        let batch_result = first_batch(&processed);
        let request_templates = processed.request.templates();

        assert_eq!(batch_result.predicates().len(), 1);
        assert!(!request_templates.is_empty());

        // Expected Batch structure
        let expected_pred_statements = vec![StatementTmpl {
            pred_or_wc: pred_lit(Predicate::Native(NativePredicate::Equal)),
            args: vec![
                sta_ak(("X", 0), "val"), // X["val"] -> Wildcard(0), Key("val")
                sta_ak(("Y", 1), "val"), // Y["val"] -> Wildcard(1), Key("val")
            ],
        }];
        let expected_predicate = CustomPredicate::and(
            &params,
            "my_pred".to_string(),
            expected_pred_statements,
            2, // args_len (X, Y)
            names(&["X", "Y"]),
        )?;
        let expected_batch =
            CustomPredicateBatch::new("PodlangModule".to_string(), vec![expected_predicate]);

        assert_eq!(*batch_result, expected_batch);

        // Expected Request structure
        // Pod1 -> Wildcard 0, Pod2 -> Wildcard 1
        let expected_request_templates = vec![StatementTmpl {
            pred_or_wc: pred_lit(Predicate::Custom(CustomPredicateRef::new(
                expected_batch,
                0,
            ))),
            args: vec![
                StatementTmplArg::Wildcard(wc("Pod1", 0)),
                StatementTmplArg::Wildcard(wc("Pod2", 1)),
            ],
        }];

        assert_eq!(request_templates, expected_request_templates);

        Ok(())
    }

    #[test]
    fn test_e2e_request_with_various_args() -> Result<(), LangError> {
        let input = r#"
            some_pred(A, B, C) = AND( Equal(A["foo"], B["bar"]) )

            REQUEST(
                some_pred(
                    Var1,                  // Wildcard
                    12345,                  // Int Literal
                    "hello_string"         // String Literal (Removed invalid AK args)
                )
                Equal(AnotherPod["another_key"], Var1["some_field"])
            )
        "#;

        let params = Params::default();
        let processed = parse(input, &params, &HashMap::new())?;
        let batch_result = first_batch(&processed);
        let request_templates = processed.request.templates();

        assert_eq!(batch_result.predicates().len(), 1); // some_pred is defined
        assert!(!request_templates.is_empty());

        // Expected Wildcard Indices in Request Scope:
        // Var1 -> 0
        // AnotherPod -> 1

        // Expected structure
        let expected_templates = vec![
            StatementTmpl {
                pred_or_wc: pred_lit(Predicate::Custom(CustomPredicateRef::new(
                    batch_result.clone(),
                    0,
                ))), // Refers to some_pred
                args: vec![
                    StatementTmplArg::Wildcard(wc("Var1", 0)),        // Var1
                    StatementTmplArg::Literal(Value::from(12345i64)), // 12345
                    StatementTmplArg::Literal(Value::from("hello_string")), // "hello_string"
                ],
            },
            StatementTmpl {
                pred_or_wc: pred_lit(Predicate::Native(NativePredicate::Equal)),
                args: vec![
                    // AnotherPod["another_key"] -> Wildcard(1), Key("another_key")
                    sta_ak(("AnotherPod", 1), "another_key"),
                    // Var1["some_field"] -> Wildcard(0), Key("some_field")
                    sta_ak(("Var1", 0), "some_field"),
                ],
            },
        ];

        assert_eq!(request_templates, expected_templates);

        Ok(())
    }

    #[test]
    fn test_e2e_syntactic_sugar_predicates() -> Result<(), LangError> {
        let input = r#"
            REQUEST(
                GtEq(A["foo"], B["bar"])
                Gt(C["baz"], D["qux"])
                DictContains(A["foo"], B["bar"], C["baz"])
                DictNotContains(A["foo"], B["bar"])
                ArrayContains(A["foo"], B["bar"], C["baz"])
            )
        "#;

        let params = Params::default();
        let processed = parse(input, &params, &HashMap::new())?;
        let request_templates = processed.request.templates();

        assert!(processed.module.is_none());
        assert!(!request_templates.is_empty());

        let expected_templates = vec![
            StatementTmpl {
                pred_or_wc: pred_lit(Predicate::Native(NativePredicate::LtEq)),
                args: vec![sta_ak(("B", 1), "bar"), sta_ak(("A", 0), "foo")],
            },
            StatementTmpl {
                pred_or_wc: pred_lit(Predicate::Native(NativePredicate::Lt)),
                args: vec![sta_ak(("D", 3), "qux"), sta_ak(("C", 2), "baz")],
            },
            StatementTmpl {
                pred_or_wc: pred_lit(Predicate::Native(NativePredicate::Contains)),
                args: vec![
                    sta_ak(("A", 0), "foo"),
                    sta_ak(("B", 1), "bar"),
                    sta_ak(("C", 2), "baz"),
                ],
            },
            StatementTmpl {
                pred_or_wc: pred_lit(Predicate::Native(NativePredicate::NotContains)),
                args: vec![sta_ak(("A", 0), "foo"), sta_ak(("B", 1), "bar")],
            },
            StatementTmpl {
                pred_or_wc: pred_lit(Predicate::Native(NativePredicate::Contains)),
                args: vec![
                    sta_ak(("A", 0), "foo"),
                    sta_ak(("B", 1), "bar"),
                    sta_ak(("C", 2), "baz"),
                ],
            },
        ];

        assert_eq!(request_templates, expected_templates);

        Ok(())
    }

    #[test]
    fn test_e2e_zukyc_request_parsing() -> Result<(), LangError> {
        let input = r#"
            REQUEST(
                // Order matters for comparison with the hardcoded templates
                SetNotContains(sanctions["sanctionList"], gov["idNumber"])
                Lt(gov["dateOfBirth"], SELF_HOLDER_18Y["const_18y"])
                Equal(pay["startDate"], SELF_HOLDER_1Y["const_1y"])
                Equal(gov["socialSecurityNumber"], pay["socialSecurityNumber"])
                Equal(SELF_HOLDER_18Y["const_18y"], 1169909388)
                Equal(SELF_HOLDER_1Y["const_1y"], 1706367566)
            )
        "#;

        // Parse the input string
        let processed = super::parse(input, &Params::default(), &HashMap::new())?;
        let parsed_templates = processed.request.templates();

        //  Define Expected Templates (Copied from prover/mod.rs)
        let now_minus_18y_val = Value::from(1169909388_i64);
        let now_minus_1y_val = Value::from(1706367566_i64);

        // Define wildcards and keys for the request
        // Note: Indices must match the order of appearance in the *parsed* request
        // Order: sanctions, gov, SELF_HOLDER_18Y, pay, SELF_HOLDER_1Y
        let wc_sanctions = wc("sanctions", 0);
        let wc_gov = wc("gov", 1);
        let wc_self_18y = wc("SELF_HOLDER_18Y", 2);
        let wc_pay = wc("pay", 3);
        let wc_self_1y = wc("SELF_HOLDER_1Y", 4);

        let id_num_key = "idNumber";
        let dob_key = "dateOfBirth";
        let const_18y_key = "const_18y";
        let start_date_key = "startDate";
        let const_1y_key = "const_1y";
        let ssn_key = "socialSecurityNumber";
        let sanction_list_key = "sanctionList";

        // Define the request templates using wildcards for constants
        let expected_templates = vec![
            // 1. NotContains(sanctions["sanctionList"], gov["idNumber"])
            StatementTmpl {
                pred_or_wc: pred_lit(Predicate::Native(NativePredicate::NotContains)),
                args: vec![
                    sta_ak(
                        (wc_sanctions.name.as_str(), wc_sanctions.index),
                        sanction_list_key,
                    ),
                    sta_ak((wc_gov.name.as_str(), wc_gov.index), id_num_key),
                ],
            },
            // 2. Lt(gov["dateOfBirth"], SELF_HOLDER_18Y["const_18y"])
            StatementTmpl {
                pred_or_wc: pred_lit(Predicate::Native(NativePredicate::Lt)),
                args: vec![
                    sta_ak((wc_gov.name.as_str(), wc_gov.index), dob_key),
                    sta_ak(
                        (wc_self_18y.name.as_str(), wc_self_18y.index),
                        const_18y_key,
                    ),
                ],
            },
            // 3. Equal(pay["startDate"], SELF_HOLDER_1Y["const_1y"])
            StatementTmpl {
                pred_or_wc: pred_lit(Predicate::Native(NativePredicate::Equal)),
                args: vec![
                    sta_ak((wc_pay.name.as_str(), wc_pay.index), start_date_key),
                    sta_ak((wc_self_1y.name.as_str(), wc_self_1y.index), const_1y_key),
                ],
            },
            // 4. Equal(gov["socialSecurityNumber"], pay["socialSecurityNumber"])
            StatementTmpl {
                pred_or_wc: pred_lit(Predicate::Native(NativePredicate::Equal)),
                args: vec![
                    sta_ak((wc_gov.name.as_str(), wc_gov.index), ssn_key),
                    sta_ak((wc_pay.name.as_str(), wc_pay.index), ssn_key),
                ],
            },
            // 5. Equal(SELF_HOLDER_18Y["const_18y"], 1169909388)
            StatementTmpl {
                pred_or_wc: pred_lit(Predicate::Native(NativePredicate::Equal)),
                args: vec![
                    sta_ak(
                        (wc_self_18y.name.as_str(), wc_self_18y.index),
                        const_18y_key,
                    ),
                    sta_lit(now_minus_18y_val.clone()),
                ],
            },
            // 6. Equal(SELF_HOLDER_1Y["const_1y"], 1706367566)
            StatementTmpl {
                pred_or_wc: pred_lit(Predicate::Native(NativePredicate::Equal)),
                args: vec![
                    sta_ak((wc_self_1y.name.as_str(), wc_self_1y.index), const_1y_key),
                    sta_lit(now_minus_1y_val.clone()),
                ],
            },
        ];

        assert_eq!(
            parsed_templates, expected_templates,
            "Parsed ZuKYC request templates do not match the expected hard-coded version"
        );

        assert!(
            processed.module.is_none(),
            "Expected no custom predicates for a REQUEST only input"
        );

        Ok(())
    }

    #[test]
    fn test_e2e_ethdos_predicates() -> Result<(), LangError> {
        let params = Params {
            max_input_pods: 3,
            max_statements: 31,
            max_public_statements: 10,
            max_operation_args: 5,
            max_custom_predicate_wildcards: 12,
            ..Default::default()
        };

        let input = r#"
            eth_friend(src, dst, private: attestation_dict) = AND(
                SignedBy(attestation_dict, src)
                Equal(attestation_dict["attestation"], dst)
            )

            eth_dos_distance_base(src, dst, distance) = AND(
                Equal(src, dst)
                Equal(distance, 0)
            )

            eth_dos_distance_ind(src, dst, distance, private: shorter_distance, intermed) = AND(
                eth_dos_distance(src, dst, distance)
                SumOf(distance, shorter_distance, 1)
                eth_friend(intermed, dst)
            )

            eth_dos_distance(src, dst, distance) = OR(
                eth_dos_distance_base(src, dst, distance)
                eth_dos_distance_ind(src, dst, distance)
            )
        "#;

        let processed = super::parse(input, &params, &HashMap::new())?;

        assert!(
            processed.request.templates().is_empty(),
            "Expected no request templates"
        );
        assert_eq!(
            first_batch(&processed).predicates().len(),
            4,
            "Expected 4 custom predicates"
        );

        // Predicate Order: eth_friend (0), base (1), ind (2), distance (3)

        // eth_friend (Index 0)
        let expected_friend_stmts = vec![
            StatementTmpl {
                pred_or_wc: pred_lit(Predicate::Native(NativePredicate::SignedBy)),
                args: vec![sta_wc_lit("attestation_dict", 2), sta_wc_lit("src", 0)],
            },
            StatementTmpl {
                pred_or_wc: pred_lit(Predicate::Native(NativePredicate::Equal)),
                args: vec![
                    sta_ak(("attestation_dict", 2), "attestation"),
                    sta_wc_lit("dst", 1), // Pub arg 1
                ],
            },
        ];
        let expected_friend_pred = CustomPredicate::new(
            &params,
            "eth_friend".to_string(),
            true, // AND
            expected_friend_stmts,
            2, // public_args_len: src, dst
            names(&["src", "dst", "attestation_dict"]),
        )?;

        // eth_dos_distance_base (Index 1)
        let expected_base_stmts = vec![
            StatementTmpl {
                pred_or_wc: pred_lit(Predicate::Native(NativePredicate::Equal)),
                args: vec![sta_wc_lit("src", 0), sta_wc_lit("dst", 1)],
            },
            StatementTmpl {
                pred_or_wc: pred_lit(Predicate::Native(NativePredicate::Equal)),
                args: vec![sta_wc_lit("distance", 2), sta_lit(0i64)],
            },
        ];
        let expected_base_pred = CustomPredicate::new(
            &params,
            "eth_dos_distance_base".to_string(),
            true, // AND
            expected_base_stmts,
            3, // public_args_len
            names(&["src", "dst", "distance"]),
        )?;

        // eth_dos_distance_ind (Index 2)
        // Public args indices: 0-2
        // Private args indices: 3-4 (shorter_distance, intermed)
        let expected_ind_stmts = vec![
            StatementTmpl {
                pred_or_wc: pred_lit(Predicate::BatchSelf(3)), // Calls eth_dos_distance (index 3)
                args: vec![
                    // WildcardLiteral args
                    sta_wc_lit("src", 0),
                    sta_wc_lit("dst", 1),      // private arg
                    sta_wc_lit("distance", 2), // private arg
                ],
            },
            StatementTmpl {
                pred_or_wc: pred_lit(Predicate::Native(NativePredicate::SumOf)),
                args: vec![
                    sta_wc_lit("distance", 2),         // public arg
                    sta_wc_lit("shorter_distance", 3), // private arg
                    sta_lit(1),
                ],
            },
            StatementTmpl {
                pred_or_wc: pred_lit(Predicate::BatchSelf(0)), // Calls eth_friend (index 0)
                args: vec![
                    // WildcardLiteral args
                    sta_wc_lit("intermed", 4), // private arg
                    sta_wc_lit("dst", 1),      // public arg
                ],
            },
        ];
        let expected_ind_pred = CustomPredicate::new(
            &params,
            "eth_dos_distance_ind".to_string(),
            true, // AND
            expected_ind_stmts,
            3, // public_args_len
            names(&["src", "dst", "distance", "shorter_distance", "intermed"]),
        )?;

        // eth_dos_distance (Index 3)
        let expected_dist_stmts = vec![
            StatementTmpl {
                pred_or_wc: pred_lit(Predicate::BatchSelf(1)), // Calls eth_dos_distance_base (index 1)
                args: vec![
                    // WildcardLiteral args
                    sta_wc_lit("src", 0),
                    sta_wc_lit("dst", 1),
                    sta_wc_lit("distance", 2),
                ],
            },
            StatementTmpl {
                pred_or_wc: pred_lit(Predicate::BatchSelf(2)), // Calls eth_dos_distance_ind (index 2)
                args: vec![
                    // WildcardLiteral args
                    sta_wc_lit("src", 0),
                    sta_wc_lit("dst", 1),
                    sta_wc_lit("distance", 2),
                ],
            },
        ];
        let expected_dist_pred = CustomPredicate::new(
            &params,
            "eth_dos_distance".to_string(),
            false, // OR
            expected_dist_stmts,
            3, // public_args_len
            names(&["src", "dst", "distance"]),
        )?;

        let expected_batch = CustomPredicateBatch::new(
            "PodlangModule".to_string(),
            vec![
                expected_friend_pred,
                expected_base_pred,
                expected_ind_pred,
                expected_dist_pred,
            ],
        );

        assert_eq!(
            *first_batch(&processed),
            expected_batch,
            "Processed ETHDoS predicates do not match expected structure"
        );

        Ok(())
    }

    #[test]
    fn test_e2e_use_module_statement() -> Result<(), LangError> {
        let params = Params::default();

        // 1. Create a module with a predicate to be imported
        let imported_pred_stmts = vec![StatementTmpl {
            pred_or_wc: pred_lit(Predicate::Native(NativePredicate::Equal)),
            args: vec![
                sta_ak(("A", 0), "foo"), // A["foo"]
                sta_ak(("B", 1), "bar"), // B["bar"]
            ],
        }];
        let imported_predicate = CustomPredicate::and(
            &params,
            "imported_equal".to_string(),
            imported_pred_stmts,
            2,
            names(&["A", "B"]),
        )?;
        let batch = CustomPredicateBatch::new("MyBatch".to_string(), vec![imported_predicate]);
        let module = Arc::new(Module::new(batch.clone(), HashMap::new()));

        // 2. Create available modules map
        let mut available_modules = HashMap::new();
        available_modules.insert("my_module".to_string(), module);

        // 3. Create the input string that uses the module
        let input = r#"
            use module my_module

            REQUEST(
                my_module::imported_equal(Pod1, Pod2)
            )
        "#;

        // 4. Parse the input
        let processed = parse(input, &params, &available_modules)?;
        let request_templates = processed.request.templates();

        assert!(
            processed.module.is_none(),
            "No custom predicates should be defined in the main input"
        );
        assert_eq!(request_templates.len(), 1, "Expected one request template");

        // 5. Check the resulting request template uses the imported predicate
        let template = &request_templates[0];
        assert_eq!(template.args.len(), 2);

        Ok(())
    }

    #[test]
    fn test_e2e_use_module_complex() -> Result<(), LangError> {
        let params = Params::default();

        // 1. Create a module with multiple predicates
        let pred1 = CustomPredicate::and(&params, "p1".into(), vec![], 1, names(&["A"]))?;
        let pred2 = CustomPredicate::and(&params, "p2".into(), vec![], 2, names(&["B", "C"]))?;
        let pred3 = CustomPredicate::and(&params, "p3".into(), vec![], 1, names(&["D"]))?;

        let batch = CustomPredicateBatch::new("mymodule".to_string(), vec![pred1, pred2, pred3]);
        let mymodule = Arc::new(Module::new(batch.clone(), HashMap::new()));

        let mut available_modules = HashMap::new();
        available_modules.insert("mymodule".to_string(), mymodule);

        // 2. Create the input string that uses qualified predicate access
        let input = r#"
            use module mymodule

            REQUEST(
                mymodule::p1(Pod1)
                mymodule::p3(Pod2)
            )
        "#;

        // 3. Parse the input
        let processed = parse(input, &params, &available_modules)?;
        let request_templates = processed.request.templates();

        assert_eq!(request_templates.len(), 2, "Expected two request templates");

        // 4. Check the resulting request templates
        let expected_templates = vec![
            StatementTmpl {
                pred_or_wc: pred_lit(Predicate::Custom(CustomPredicateRef::new(batch.clone(), 0))),
                args: vec![StatementTmplArg::Wildcard(wc("Pod1", 0))],
            },
            StatementTmpl {
                pred_or_wc: pred_lit(Predicate::Custom(CustomPredicateRef::new(batch, 2))),
                args: vec![StatementTmplArg::Wildcard(wc("Pod2", 1))],
            },
        ];

        assert_eq!(request_templates, expected_templates);

        Ok(())
    }

    #[test]
    fn test_e2e_custom_predicate_uses_module() -> Result<(), LangError> {
        let params = Params::default();

        // 1. Create a module with a predicate to be imported
        let imported_pred_stmts = vec![StatementTmpl {
            pred_or_wc: pred_lit(Predicate::Native(NativePredicate::Equal)),
            args: vec![sta_ak(("A", 0), "foo"), sta_ak(("B", 1), "bar")],
        }];
        let imported_predicate = CustomPredicate::and(
            &params,
            "imported_equal".to_string(),
            imported_pred_stmts,
            2,
            names(&["A", "B"]),
        )?;
        let batch = CustomPredicateBatch::new("extmod".to_string(), vec![imported_predicate]);
        let extmod = Arc::new(Module::new(batch.clone(), HashMap::new()));

        let mut available_modules = HashMap::new();
        available_modules.insert("extmod".to_string(), extmod);

        // 2. Create the input string that defines a new predicate using the imported one
        let input = r#"
            use module extmod

            wrapper_pred(X, Y) = AND(
                extmod::imported_equal(X, Y)
            )
        "#;

        // 3. Parse the input
        let processed = parse(input, &params, &available_modules)?;

        assert!(
            processed.request.templates().is_empty(),
            "No request should be defined"
        );
        assert_eq!(
            first_batch(&processed).predicates().len(),
            1,
            "Expected one custom predicate to be defined"
        );

        // 4. Check the resulting predicate definition
        let defined_pred = &first_batch(&processed).predicates()[0];
        assert_eq!(defined_pred.name, "wrapper_pred");
        assert_eq!(defined_pred.statements.len(), 1);

        let expected_statement = StatementTmpl {
            pred_or_wc: pred_lit(Predicate::Custom(CustomPredicateRef::new(batch, 0))),
            args: vec![
                StatementTmplArg::Wildcard(wc("X", 0)),
                StatementTmplArg::Wildcard(wc("Y", 1)),
            ],
        };

        assert_eq!(defined_pred.statements[0], expected_statement);

        Ok(())
    }

    #[test]
    fn test_e2e_intro_import_parsing() -> Result<(), LangError> {
        let params = Params::default();

        let intro_hash = EMPTY_HASH.encode_hex::<String>();
        let input = format!(
            r#"
            use intro empty() from 0x{intro_hash}

            REQUEST(
                empty()
            )
        "#,
        );

        let processed = parse(&input, &params, &HashMap::new())?;
        let request_templates = processed.request.templates();
        assert_eq!(request_templates.len(), 1);

        if let PredicateOrWildcard::Predicate(Predicate::Intro(intro_ref)) =
            &request_templates[0].pred_or_wc
        {
            assert_eq!(intro_ref.name, "empty");
            assert_eq!(intro_ref.args_len, 0);
            assert_eq!(intro_ref.verifier_data_hash, EMPTY_HASH);
        } else {
            panic!("Expected Intro predicate");
        }

        assert!(request_templates[0].args.is_empty());

        Ok(())
    }

    #[test]
    fn test_e2e_literals() -> Result<(), LangError> {
        let pk = crate::backends::plonky2::primitives::ec::curve::Point::generator();
        let raw = RawValue::from(1);
        let string = "hello";
        let int = 123;
        let bool = true;
        let sk = SecretKey::new_rand();

        let input = format!(
            r#"
            REQUEST(
                Equal(A["pk"], {})
                Equal(B["raw"], {})
                Equal(C["string"], {})
                Equal(D["int"], {})
                Equal(E["bool"], {})
                Equal(F["sk"], {})
            )
        "#,
            Value::from(pk).to_podlang_string(),
            Value::from(raw).to_podlang_string(),
            Value::from(string).to_podlang_string(),
            Value::from(int).to_podlang_string(),
            Value::from(bool).to_podlang_string(),
            Value::from(sk.clone()).to_podlang_string()
        );
        /*
            REQUEST(
                Equal(A["pk"], PublicKey(3t9fNuU194n7mSJPRdeaJRMqw6ZQCUddzvECWNe1k2b1rdBezXpJxF))
                Equal(C["raw"], Raw(0x0000000000000000000000000000000000000000000000000000000000000001))
                Equal(D["string"], "hello")
                Equal(E["int"], 123)
                Equal(F["bool"], true)
                Equal(G["sk"], SecretKey(random_secret_key_base_64))
                Equal(H["self"], SELF)
            )
        */

        let params = Params::default();
        let processed = parse(&input, &params, &HashMap::new())?;
        let request_templates = processed.request.templates();

        let expected_templates = vec![
            StatementTmpl {
                pred_or_wc: pred_lit(Predicate::Native(NativePredicate::Equal)),
                args: vec![sta_ak(("A", 0), "pk"), sta_lit(Value::from(pk))],
            },
            StatementTmpl {
                pred_or_wc: pred_lit(Predicate::Native(NativePredicate::Equal)),
                args: vec![sta_ak(("B", 1), "raw"), sta_lit(Value::from(raw))],
            },
            StatementTmpl {
                pred_or_wc: pred_lit(Predicate::Native(NativePredicate::Equal)),
                args: vec![sta_ak(("C", 2), "string"), sta_lit(Value::from(string))],
            },
            StatementTmpl {
                pred_or_wc: pred_lit(Predicate::Native(NativePredicate::Equal)),
                args: vec![sta_ak(("D", 3), "int"), sta_lit(Value::from(int))],
            },
            StatementTmpl {
                pred_or_wc: pred_lit(Predicate::Native(NativePredicate::Equal)),
                args: vec![sta_ak(("E", 4), "bool"), sta_lit(Value::from(bool))],
            },
            StatementTmpl {
                pred_or_wc: pred_lit(Predicate::Native(NativePredicate::Equal)),
                args: vec![sta_ak(("F", 5), "sk"), sta_lit(Value::from(sk))],
            },
        ];

        assert_eq!(request_templates, expected_templates);

        Ok(())
    }

    #[test]
    fn test_e2e_use_unknown_module() {
        let params = Params::default();
        let available_modules: HashMap<String, Arc<Module>> = HashMap::new();

        let input = r#"
            use module unknown_module
            "#;

        let result = parse(input, &params, &available_modules);

        assert!(result.is_err());

        match result.err().unwrap() {
            LangError::Validation(e) => match *e {
                frontend_ast_validate::ValidationError::ModuleNotFound { name, .. } => {
                    assert_eq!(name, "unknown_module");
                }
                _ => panic!("Expected ModuleNotFound error, but got {:?}", e),
            },
            e => panic!("Expected LangError::Validation, but got {:?}", e),
        }
    }

    #[test]
    fn test_e2e_undefined_wildcard() {
        let params = Params::default();
        let available_modules: HashMap<String, Arc<Module>> = HashMap::new();

        let input = r#"
            identity_verified(username, private: identity_dict) = AND(
                Equal(identity_dict["username"], username)
                Equal(identity_dict["user_public_key"], user_public_key)
            )
        "#;

        let result = parse(input, &params, &available_modules);

        assert!(result.is_err());

        match result.err().unwrap() {
            LangError::Validation(e) => match *e {
                frontend_ast_validate::ValidationError::UndefinedWildcard {
                    name,
                    pred_name,
                    ..
                } => {
                    assert_eq!(name, "user_public_key");
                    assert_eq!(pred_name, "identity_verified");
                }
                _ => panic!("Expected UndefinedWildcard error, but got {:?}", e),
            },
            e => panic!("Expected LangError::Validation, but got {:?}", e),
        }
    }
}
