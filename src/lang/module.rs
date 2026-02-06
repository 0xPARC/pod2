//! Podlang Module: definition, construction, and predicate application.
//!
//! A [`Module`] wraps a middleware `CustomPredicateBatch` with name resolution
//! and split chain metadata. Use [`build_module`] to construct a Module from
//! validated and split predicates.

use std::{collections::HashMap, sync::Arc};

use crate::{
    frontend::{CustomPredicateBatchBuilder, Operation, OperationArg, StatementTmplBuilder},
    lang::{
        error::BatchingError,
        frontend_ast::{ConjunctionType, CustomPredicateDef},
        frontend_ast_lower::{lower_statement_arg, resolve_predicate_ref, ResolutionContext},
        frontend_ast_split::{SplitChainInfo, SplitResult},
        frontend_ast_validate::SymbolTable,
    },
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

/// Build a single Module from split predicate results.
///
/// Takes a list of split results (containing predicates and optional chain info)
/// and builds a single Module. With Merkle tree backing supporting up to 65536
/// predicates, all predicates from a document fit in one module.
///
/// `symbols` provides the symbol table for resolving predicate references,
/// including imported predicates from other modules and intro predicates.
pub fn build_module(
    split_results: Vec<SplitResult>,
    params: &Params,
    module_name: &str,
    symbols: &SymbolTable,
) -> Result<Module, BatchingError> {
    // Extract predicates and collect split chains
    let mut predicates = Vec::new();
    let mut split_chains = HashMap::new();

    for result in split_results {
        // Collect chain info if present
        if let Some(chain_info) = result.chain_info {
            split_chains.insert(chain_info.original_name.clone(), chain_info);
        }
        // Flatten predicates
        predicates.extend(result.predicates);
    }

    if predicates.is_empty() {
        // Return an empty module
        let empty_batch = CustomPredicateBatch::new(module_name.to_string(), vec![]);
        return Ok(Module::new(empty_batch, split_chains));
    }

    // Build reference map: name -> index
    let reference_map: HashMap<String, usize> = predicates
        .iter()
        .enumerate()
        .map(|(idx, pred)| (pred.name.name.clone(), idx))
        .collect();

    // Build the batch
    let batch = build_single_batch(&predicates, &reference_map, symbols, params, module_name)?;

    Ok(Module::new(batch, split_chains))
}

/// Build a batch with properly resolved references
fn build_single_batch(
    predicates: &[CustomPredicateDef],
    reference_map: &HashMap<String, usize>,
    symbols: &SymbolTable,
    params: &Params,
    batch_name: &str,
) -> Result<Arc<CustomPredicateBatch>, BatchingError> {
    let mut builder = CustomPredicateBatchBuilder::new(params.clone(), batch_name.to_string());

    for pred in predicates {
        let name = &pred.name.name;

        // Collect argument names
        let public_args: Vec<&str> = pred
            .args
            .public_args
            .iter()
            .map(|a| a.name.as_str())
            .collect();

        let private_args: Vec<&str> = pred
            .args
            .private_args
            .as_ref()
            .map(|args| args.iter().map(|a| a.name.as_str()).collect())
            .unwrap_or_default();

        // Build statement templates with resolved predicates
        let statement_builders: Vec<StatementTmplBuilder> = pred
            .statements
            .iter()
            .map(|stmt| build_statement_with_resolved_refs(stmt, reference_map, name, symbols))
            .collect::<Result<_, _>>()?;

        let conjunction = pred.conjunction_type == ConjunctionType::And;

        builder
            .predicate(
                name,
                conjunction,
                &public_args,
                &private_args,
                &statement_builders,
            )
            .map_err(|e| BatchingError::Internal {
                message: format!("Failed to add predicate '{}': {}", name, e),
            })?;
    }

    Ok(builder.finish())
}

/// Build a statement template with properly resolved predicate references
fn build_statement_with_resolved_refs(
    stmt: &crate::lang::frontend_ast::StatementTmpl,
    reference_map: &HashMap<String, usize>,
    custom_predicate_name: &str, // custom pred that defines this statement template
    symbols: &SymbolTable,
) -> Result<StatementTmplBuilder, BatchingError> {
    // Resolve the predicate using the unified resolution function
    let context = ResolutionContext::Module {
        reference_map,
        custom_predicate_name,
    };

    let pred_or_wc =
        resolve_predicate_ref(&stmt.predicate, symbols, &context).ok_or_else(|| {
            BatchingError::Internal {
                message: format!(
                    "Unknown predicate reference: '{}'",
                    stmt.predicate.display_name()
                ),
            }
        })?;

    // Build the statement template
    let mut builder = StatementTmplBuilder::new(pred_or_wc);

    for arg in &stmt.args {
        builder = builder.arg(lower_statement_arg(arg));
    }

    Ok(builder)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        lang::{
            frontend_ast::parse::parse_document,
            frontend_ast_split::split_predicate_if_needed,
            frontend_ast_validate::{validate, ParseMode, ValidatedAST},
            parser::parse_podlang,
        },
        middleware::{Predicate, PredicateOrWildcard},
    };

    /// Helper: parse and validate input, returning predicates and symbol table
    fn parse_and_validate(input: &str) -> (Vec<CustomPredicateDef>, ValidatedAST) {
        let parsed = parse_podlang(input).expect("Failed to parse");
        let document = parse_document(parsed.into_iter().next().unwrap()).expect("Failed to parse");
        let validated = validate(document.clone(), &HashMap::new(), ParseMode::Module)
            .expect("Failed to validate");

        let predicates = document
            .items
            .into_iter()
            .filter_map(|item| match item {
                crate::lang::frontend_ast::DocumentItem::CustomPredicateDef(pred) => Some(pred),
                _ => None,
            })
            .collect();

        (predicates, validated)
    }

    /// Helper: wrap predicates into SplitResult (without actually splitting)
    fn preds_to_split_results(predicates: Vec<CustomPredicateDef>) -> Vec<SplitResult> {
        predicates
            .into_iter()
            .map(|pred| SplitResult {
                predicates: vec![pred],
                chain_info: None,
            })
            .collect()
    }

    #[test]
    fn test_single_predicate() {
        let input = r#"
            my_pred(A, B) = AND(
                Equal(A["x"], B["y"])
            )
        "#;

        let (predicates, validated) = parse_and_validate(input);
        let params = Params::default();

        let result = build_module(
            preds_to_split_results(predicates),
            &params,
            "TestModule",
            validated.symbols(),
        );
        assert!(result.is_ok());

        let module = result.unwrap();
        assert_eq!(module.batch.predicates().len(), 1);
    }

    #[test]
    fn test_multiple_predicates() {
        let input = r#"
            pred1(A) = AND(Equal(A["x"], 1))
            pred2(B) = AND(Equal(B["y"], 2))
            pred3(C) = AND(Equal(C["z"], 3))
        "#;

        let (predicates, validated) = parse_and_validate(input);
        let params = Params::default();

        let result = build_module(
            preds_to_split_results(predicates),
            &params,
            "TestModule",
            validated.symbols(),
        );
        assert!(result.is_ok());

        let module = result.unwrap();
        assert_eq!(module.batch.predicates().len(), 3);
    }

    #[test]
    fn test_intra_batch_forward_reference() {
        // pred2 calls pred1, but pred2 is declared first
        // This should work because they're in the same batch
        let input = r#"
            pred2(B) = AND(pred1(B))
            pred1(A) = AND(Equal(A["x"], 1))
        "#;

        let (predicates, validated) = parse_and_validate(input);
        let params = Params::default();

        let result = build_module(
            preds_to_split_results(predicates),
            &params,
            "TestModule",
            validated.symbols(),
        );
        assert!(result.is_ok());

        let module = result.unwrap();
        assert_eq!(module.batch.predicates().len(), 2);

        // pred2 should reference pred1 via BatchSelf
        let pred2 = &module.batch.predicates()[0];
        let stmt = &pred2.statements[0];
        assert!(matches!(
            stmt.pred_or_wc(),
            PredicateOrWildcard::Predicate(Predicate::BatchSelf(1))
        )); // pred1 is at index 1
    }

    #[test]
    fn test_mutual_recursion() {
        // pred1 calls pred2, pred2 calls pred1 - mutual recursion
        // This should work because they're in the same batch
        let input = r#"
            pred1(A) = AND(pred2(A))
            pred2(B) = AND(pred1(B))
        "#;

        let (predicates, validated) = parse_and_validate(input);
        let params = Params::default();

        let result = build_module(
            preds_to_split_results(predicates),
            &params,
            "TestModule",
            validated.symbols(),
        );
        assert!(result.is_ok());

        let module = result.unwrap();
        assert_eq!(module.batch.predicates().len(), 2);

        // Both should use BatchSelf references
        let pred1 = &module.batch.predicates()[0];
        let pred2 = &module.batch.predicates()[1];
        assert!(matches!(
            pred1.statements[0].pred_or_wc(),
            PredicateOrWildcard::Predicate(Predicate::BatchSelf(1))
        )); // calls pred2
        assert!(matches!(
            pred2.statements[0].pred_or_wc(),
            PredicateOrWildcard::Predicate(Predicate::BatchSelf(0))
        )); // calls pred1
    }

    #[test]
    fn test_predicate_ref_by_name() {
        let input = r#"
            pred1(A) = AND(Equal(A["x"], 1))
            pred2(B) = AND(Equal(B["y"], 2))
        "#;

        let (predicates, validated) = parse_and_validate(input);
        let params = Params::default();

        let module = build_module(
            preds_to_split_results(predicates),
            &params,
            "TestModule",
            validated.symbols(),
        )
        .unwrap();

        // Should be able to look up both predicates
        assert!(module.predicate_ref_by_name("pred1").is_some());
        assert!(module.predicate_ref_by_name("pred2").is_some());
        assert!(module.predicate_ref_by_name("nonexistent").is_none());
    }

    #[test]
    fn test_split_predicate() {
        // A predicate that will split into 2 pieces
        let input = r#"
            large_pred(A) = AND(
                Equal(A["a"], 1)
                Equal(A["b"], 2)
                Equal(A["c"], 3)
                Equal(A["d"], 4)
                Equal(A["e"], 5)
                Equal(A["f"], 6)
            )
        "#;

        let (predicates, validated) = parse_and_validate(input);
        let params = Params::default();

        // Split the predicate
        let mut split_results = Vec::new();
        for pred in predicates {
            let result = split_predicate_if_needed(pred, &params).expect("Split failed");
            split_results.push(result);
        }

        // Should split into 2 pieces
        assert_eq!(split_results.len(), 1);
        assert_eq!(split_results[0].predicates.len(), 2);
        assert!(split_results[0].chain_info.is_some());

        let module =
            build_module(split_results, &params, "TestModule", validated.symbols()).unwrap();

        // Verify chain info is preserved
        let chain_info = module.split_chains.get("large_pred").unwrap();
        assert_eq!(chain_info.chain_pieces.len(), 2);
        assert_eq!(chain_info.real_statement_count, 6);
    }
}
