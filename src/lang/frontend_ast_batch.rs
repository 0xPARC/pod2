//! Multi-batch packing for predicates
//!
//! This module implements packing of multiple predicates (including split chains)
//! into multiple CustomPredicateBatches when they exceed single-batch limits.
//!
//! The algorithm:
//! 1. Assign predicates to batches in declaration order (fill each before starting new)
//! 2. Build batches in order, resolving references:
//!    - Same batch: BatchSelf(index) - works for any intra-batch reference
//!    - Earlier batch: Custom(CustomPredicateRef)
//!    - Later batch: Error (forward cross-batch references not allowed)
//!
//! Mutual recursion within a batch is fully supported since BatchSelf references
//! work regardless of declaration order.

use std::{collections::HashMap, str::FromStr, sync::Arc};

use crate::{
    frontend::{
        BuilderArg, CustomPredicateBatchBuilder, Operation, OperationArg, StatementTmplBuilder,
    },
    lang::{
        error::BatchingError,
        frontend_ast::{AnchoredKeyPath, ConjunctionType, CustomPredicateDef, StatementTmplArg},
        frontend_ast_split::{SplitChainInfo, SplitResult},
    },
    middleware::{
        CustomPredicateBatch, CustomPredicateRef, NativePredicate, Params, Predicate, Statement,
    },
};

/// A single step in a multi-operation sequence for split predicates
#[derive(Debug, Clone)]
struct OperationStep {
    /// The operation to perform
    operation: Operation,
    /// Whether this step's result should be public
    public: bool,
}

/// Errors that can occur when building multi-operations
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

/// Container for multiple predicate batches
#[derive(Debug, Clone)]
pub struct PredicateBatches {
    batches: Vec<Arc<CustomPredicateBatch>>,
    /// Maps predicate name to (batch_index, predicate_index_within_batch)
    predicate_index: HashMap<String, (usize, usize)>,
    /// Split chain metadata for predicates that were split
    /// Maps original predicate name to its chain info
    split_chains: HashMap<String, SplitChainInfo>,
}

impl Default for PredicateBatches {
    fn default() -> Self {
        Self::new()
    }
}

impl PredicateBatches {
    pub fn new() -> Self {
        Self {
            batches: Vec::new(),
            predicate_index: HashMap::new(),
            split_chains: HashMap::new(),
        }
    }

    /// Get split chain info for a predicate (if it was split)
    pub fn split_chain(&self, name: &str) -> Option<&SplitChainInfo> {
        self.split_chains.get(name)
    }

    /// Get a reference to a predicate by name
    pub fn predicate_ref_by_name(&self, name: &str) -> Option<CustomPredicateRef> {
        let (batch_idx, pred_idx) = self.predicate_index.get(name)?;
        let batch = self.batches.get(*batch_idx)?;
        Some(CustomPredicateRef::new(batch.clone(), *pred_idx))
    }

    /// Get all batches
    pub fn batches(&self) -> &[Arc<CustomPredicateBatch>] {
        &self.batches
    }

    /// Get the first batch (for backwards compatibility)
    pub fn first_batch(&self) -> Option<&Arc<CustomPredicateBatch>> {
        self.batches.first()
    }

    /// Get batch count
    pub fn batch_count(&self) -> usize {
        self.batches.len()
    }

    /// Check if empty
    pub fn is_empty(&self) -> bool {
        self.batches.is_empty()
    }

    /// Total predicate count across all batches
    pub fn total_predicate_count(&self) -> usize {
        self.batches.iter().map(|b| b.predicates().len()).sum()
    }

    /// Build operation steps for a predicate (internal helper)
    ///
    /// For non-split predicates, returns a single operation.
    /// For split predicates, returns the chain of operations in execution order
    /// (innermost first), with chain link placeholders.
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
        if statements.len() != chain_info.total_real_statements {
            return Err(MultiOperationError::WrongStatementCount {
                predicate: predicate_name.to_string(),
                expected: chain_info.total_real_statements,
                actual: statements.len(),
            });
        }

        // Reorder statements from original order to split order
        // reorder_map[original_idx] = split_idx
        // So we need to place statements[i] at position reorder_map[i]
        let mut reordered = vec![Statement::None; statements.len()];
        for (original_idx, stmt) in statements.into_iter().enumerate() {
            let split_idx = chain_info.reorder_map[original_idx];
            reordered[split_idx] = stmt;
        }

        // Build operations for each piece in execution order (innermost first)
        //
        // chain_pieces are in execution order: [continuation_N, ..., continuation_1, main]
        // But in split order, statements are laid out: [main's stmts, cont_1's stmts, ..., cont_N's stmts]
        // So we need to compute offsets from the END for the first pieces.
        //
        // Example with 6 statements, max_arity 5:
        //   split order: [stmt0, stmt1, stmt2, stmt3, stmt4, stmt5]
        //   chain_pieces[0] (large_pred_1): takes stmt5 (the last 1)
        //   chain_pieces[1] (large_pred): takes stmt0-4 (the first 5)
        //
        // We compute offsets by going through pieces in reverse order (matching split order).

        let num_pieces = chain_info.chain_pieces.len();

        // Compute the starting offset for each piece by iterating in reverse
        // (reverse of chain_pieces = same order as split layout)
        let mut piece_offsets = vec![0usize; num_pieces];
        let mut offset = 0;
        for i in (0..num_pieces).rev() {
            piece_offsets[i] = offset;
            offset += chain_info.chain_pieces[i].real_statement_count;
        }

        let mut steps = Vec::new();
        for (piece_idx, piece) in chain_info.chain_pieces.iter().enumerate() {
            let is_final = piece_idx == num_pieces - 1;

            // Get predicate ref for this piece
            let piece_ref = self
                .predicate_ref_by_name(&piece.name)
                .ok_or_else(|| MultiOperationError::ChainPieceNotFound(piece.name.clone()))?;

            // Slice the reordered statements for this piece
            let start = piece_offsets[piece_idx];
            let end = start + piece.real_statement_count;
            let piece_statements: Vec<Statement> = reordered[start..end].to_vec();

            // Build the operation
            // For non-final pieces, we'll add a placeholder that will be replaced
            // with the previous step's result when applied
            let mut args = piece_statements;
            if piece.has_chain_call {
                // Add placeholder for chain link - will be replaced by apply_multi_operation
                args.push(Statement::None);
            }

            steps.push(OperationStep {
                operation: Operation::custom(piece_ref, args),
                public: public && is_final, // Only final piece is public
            });
        }

        Ok(steps)
    }

    /// Apply a predicate, automatically handling split chains
    ///
    /// This method builds operations for a predicate and applies them using the provided
    /// closure. For non-split predicates, it performs a single operation.
    /// For split predicates, it wires up the chain automatically.
    ///
    /// # Arguments
    /// * `name` - Name of the predicate to apply
    /// * `statements` - User statements in **original declaration order**
    /// * `public` - Whether the final result should be public
    /// * `apply_op` - Closure that applies a single operation: `(public, operation) -> Result<Statement>`
    ///
    /// # Returns
    /// The final statement handle from applying all operations
    ///
    /// # Example
    /// ```ignore
    /// let result = batches.apply_predicate(
    ///     "my_pred",
    ///     statements,
    ///     true,
    ///     |public, op| if public { builder.pub_op(op) } else { builder.priv_op(op) }
    /// )?;
    /// ```
    pub fn apply_predicate<F, E>(
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
                // Replace the last Statement::None arg with the previous result
                let mut args = step.operation.1;
                if let Some(last) = args.last_mut() {
                    if matches!(last, OperationArg::Statement(Statement::None)) {
                        *last = OperationArg::Statement(prev);
                    }
                }
                Operation(step.operation.0, args, step.operation.2)
            } else {
                step.operation
            };

            prev_result = Some(apply_op(step.public, op)?);
        }

        // Safe to unwrap because we checked steps.is_empty() above
        Ok(prev_result.unwrap())
    }
}

/// Assignment of a predicate to a batch
#[derive(Debug, Clone)]
struct PredicateAssignment {
    /// Full name (e.g., "my_pred_1" for split link)
    full_name: String,
    /// Which batch this goes into
    batch_index: usize,
    /// Index within that batch
    index_in_batch: usize,
}

/// Information about an imported predicate for use during batching
#[derive(Debug, Clone)]
pub struct ImportedPredicateInfo {
    pub batch: Arc<CustomPredicateBatch>,
    pub index: usize,
}

/// Pack predicates into multiple batches
///
/// Takes a list of split results (containing predicates and optional chain info)
/// and packs them into batches, handling cross-batch references correctly.
///
/// Predicates are assigned to batches in declaration order. Within a batch,
/// predicates can reference each other freely via BatchSelf. Cross-batch
/// references must point to earlier batches (forward cross-batch references
/// are an error).
///
/// `imported_predicates` maps predicate names to their imported batch info,
/// allowing predicates to call imported predicates from other batches.
pub fn batch_predicates(
    split_results: Vec<SplitResult>,
    params: &Params,
    base_batch_name: &str,
    imported_predicates: &HashMap<String, ImportedPredicateInfo>,
) -> Result<PredicateBatches, BatchingError> {
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
        return Ok(PredicateBatches::new());
    }

    // Plan batch assignments in declaration order
    let assignments = plan_batch_assignments(&predicates, params.max_custom_batch_size);

    // Build reference map: name -> (batch_idx, idx_in_batch)
    let reference_map: HashMap<String, (usize, usize)> = assignments
        .iter()
        .map(|a| (a.full_name.clone(), (a.batch_index, a.index_in_batch)))
        .collect();

    // Determine number of batches
    let num_batches = assignments
        .iter()
        .map(|a| a.batch_index)
        .max()
        .map(|m| m + 1)
        .unwrap_or(0);

    // Build batches in order
    let mut batches = Vec::new();
    let mut predicate_index = HashMap::new();

    for batch_idx in 0..num_batches {
        // Collect predicates for this batch (in assignment order)
        let batch_predicates: Vec<_> = predicates
            .iter()
            .zip(assignments.iter())
            .filter(|(_, a)| a.batch_index == batch_idx)
            .map(|(p, _)| p.clone())
            .collect();

        let batch_name = if num_batches == 1 {
            base_batch_name.to_string()
        } else {
            format!("{}_{}", base_batch_name, batch_idx)
        };

        let batch = build_single_batch(
            &batch_predicates,
            batch_idx,
            &reference_map,
            &batches,
            imported_predicates,
            params,
            &batch_name,
        )?;

        // Update predicate index
        for (idx, pred) in batch_predicates.iter().enumerate() {
            predicate_index.insert(pred.name.name.clone(), (batch_idx, idx));
        }

        batches.push(batch);
    }

    Ok(PredicateBatches {
        batches,
        predicate_index,
        split_chains,
    })
}

/// Plan batch assignments (greedy fill in declaration order)
fn plan_batch_assignments(
    predicates: &[CustomPredicateDef],
    max_batch_size: usize,
) -> Vec<PredicateAssignment> {
    let mut assignments = Vec::new();
    let mut current_batch = 0;
    let mut current_batch_count = 0;

    for pred in predicates {
        if current_batch_count >= max_batch_size {
            current_batch += 1;
            current_batch_count = 0;
        }

        assignments.push(PredicateAssignment {
            full_name: pred.name.name.clone(),
            batch_index: current_batch,
            index_in_batch: current_batch_count,
        });

        current_batch_count += 1;
    }

    assignments
}

/// Build a single batch with properly resolved references
fn build_single_batch(
    predicates: &[CustomPredicateDef],
    batch_idx: usize,
    reference_map: &HashMap<String, (usize, usize)>,
    existing_batches: &[Arc<CustomPredicateBatch>],
    imported_predicates: &HashMap<String, ImportedPredicateInfo>,
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
            .map(|stmt| {
                build_statement_with_resolved_refs(
                    stmt,
                    name,
                    batch_idx,
                    reference_map,
                    existing_batches,
                    imported_predicates,
                )
            })
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
    caller_name: &str,
    current_batch_idx: usize,
    reference_map: &HashMap<String, (usize, usize)>,
    existing_batches: &[Arc<CustomPredicateBatch>],
    imported_predicates: &HashMap<String, ImportedPredicateInfo>,
) -> Result<StatementTmplBuilder, BatchingError> {
    let callee_name = &stmt.predicate.name;

    // Resolve the predicate
    let predicate = if let Ok(native) = NativePredicate::from_str(callee_name) {
        Predicate::Native(native)
    } else if let Some(&(target_batch, target_idx)) = reference_map.get(callee_name) {
        // Local predicate in this document
        if target_batch == current_batch_idx {
            // Same batch - use BatchSelf
            Predicate::BatchSelf(target_idx)
        } else if target_batch < current_batch_idx {
            // Earlier batch - use Custom ref
            let batch = &existing_batches[target_batch];
            Predicate::Custom(CustomPredicateRef::new(batch.clone(), target_idx))
        } else {
            // Forward reference to later batch - error
            return Err(BatchingError::ForwardCrossBatchReference {
                caller: caller_name.to_string(),
                caller_batch: current_batch_idx,
                callee: callee_name.to_string(),
                callee_batch: target_batch,
            });
        }
    } else if let Some(imported) = imported_predicates.get(callee_name) {
        // Imported predicate from another batch
        Predicate::Custom(CustomPredicateRef::new(
            imported.batch.clone(),
            imported.index,
        ))
    } else {
        // Unknown predicate
        return Err(BatchingError::Internal {
            message: format!("Unknown predicate reference: '{}'", callee_name),
        });
    };

    // Build the statement template
    let mut builder = StatementTmplBuilder::new(predicate);

    for arg in &stmt.args {
        let builder_arg = match arg {
            StatementTmplArg::Literal(lit) => {
                let value = lower_literal(lit)?;
                BuilderArg::Literal(value)
            }
            StatementTmplArg::Wildcard(id) => BuilderArg::WildcardLiteral(id.name.clone()),
            StatementTmplArg::AnchoredKey(ak) => {
                let key_str = match &ak.key {
                    AnchoredKeyPath::Bracket(s) => s.value.clone(),
                    AnchoredKeyPath::Dot(id) => id.name.clone(),
                };
                BuilderArg::Key(ak.root.name.clone(), key_str)
            }
        };
        builder = builder.arg(builder_arg);
    }

    Ok(builder)
}

/// Lower a literal value to middleware Value
fn lower_literal(
    lit: &crate::lang::frontend_ast::LiteralValue,
) -> Result<crate::middleware::Value, BatchingError> {
    use crate::{
        lang::frontend_ast::LiteralValue,
        middleware::{containers, Value},
    };

    let value = match lit {
        LiteralValue::Int(i) => Value::from(i.value),
        LiteralValue::Bool(b) => Value::from(b.value),
        LiteralValue::String(s) => Value::from(s.value.clone()),
        LiteralValue::Raw(r) => Value::from(r.hash.hash),
        LiteralValue::PublicKey(pk) => Value::from(pk.point),
        LiteralValue::SecretKey(sk) => Value::from(sk.secret_key.clone()),
        LiteralValue::Array(a) => {
            let elements: Result<Vec<_>, _> = a.elements.iter().map(lower_literal).collect();
            let array = containers::Array::new(elements?);
            Value::from(array)
        }
        LiteralValue::Set(s) => {
            let elements: Result<Vec<_>, _> = s.elements.iter().map(lower_literal).collect();
            let set_values: std::collections::HashSet<_> = elements?.into_iter().collect();
            let set = containers::Set::new(set_values);
            Value::from(set)
        }
        LiteralValue::Dict(d) => {
            let pairs: Result<Vec<_>, BatchingError> = d
                .pairs
                .iter()
                .map(|pair| {
                    let key = crate::middleware::Key::from(pair.key.value.as_str());
                    let value = lower_literal(&pair.value)?;
                    Ok((key, value))
                })
                .collect();
            let dict_map: std::collections::HashMap<_, _> = pairs?.into_iter().collect();
            let dict = containers::Dictionary::new(dict_map);
            Value::from(dict)
        }
    };
    Ok(value)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::{
        frontend_ast::parse::parse_document, frontend_ast_split::split_predicate_if_needed,
        parser::parse_podlang,
    };

    fn parse_predicates(input: &str) -> Vec<CustomPredicateDef> {
        let parsed = parse_podlang(input).expect("Failed to parse");
        let document = parse_document(parsed.into_iter().next().unwrap()).expect("Failed to parse");

        document
            .items
            .into_iter()
            .filter_map(|item| match item {
                crate::lang::frontend_ast::DocumentItem::CustomPredicateDef(pred) => Some(pred),
                _ => None,
            })
            .collect()
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
    fn test_single_predicate_single_batch() {
        let input = r#"
            my_pred(A, B) = AND(
                Equal(A["x"], B["y"])
            )
        "#;

        let predicates = parse_predicates(input);
        let params = Params::default();

        let result = batch_predicates(
            preds_to_split_results(predicates),
            &params,
            "TestBatch",
            &HashMap::new(),
        );
        assert!(result.is_ok());

        let batches = result.unwrap();
        assert_eq!(batches.batch_count(), 1);
        assert_eq!(batches.total_predicate_count(), 1);
    }

    #[test]
    fn test_multiple_predicates_single_batch() {
        let input = r#"
            pred1(A) = AND(Equal(A["x"], 1))
            pred2(B) = AND(Equal(B["y"], 2))
            pred3(C) = AND(Equal(C["z"], 3))
        "#;

        let predicates = parse_predicates(input);
        let params = Params::default(); // max_custom_batch_size = 4

        let result = batch_predicates(
            preds_to_split_results(predicates),
            &params,
            "TestBatch",
            &HashMap::new(),
        );
        assert!(result.is_ok());

        let batches = result.unwrap();
        assert_eq!(batches.batch_count(), 1);
        assert_eq!(batches.total_predicate_count(), 3);
    }

    #[test]
    fn test_predicates_span_multiple_batches() {
        let input = r#"
            pred1(A) = AND(Equal(A["x"], 1))
            pred2(B) = AND(Equal(B["y"], 2))
            pred3(C) = AND(Equal(C["z"], 3))
            pred4(D) = AND(Equal(D["w"], 4))
            pred5(E) = AND(Equal(E["v"], 5))
        "#;

        let predicates = parse_predicates(input);
        let params = Params::default(); // max_custom_batch_size = 4

        let result = batch_predicates(
            preds_to_split_results(predicates),
            &params,
            "TestBatch",
            &HashMap::new(),
        );
        assert!(result.is_ok());

        let batches = result.unwrap();
        assert_eq!(batches.batch_count(), 2);
        assert_eq!(batches.total_predicate_count(), 5);

        // First batch should have 4 predicates
        assert_eq!(batches.batches()[0].predicates().len(), 4);
        // Second batch should have 1 predicate
        assert_eq!(batches.batches()[1].predicates().len(), 1);
    }

    #[test]
    fn test_intra_batch_forward_reference() {
        // pred2 calls pred1, but pred2 is declared first
        // This should work because they're in the same batch
        let input = r#"
            pred2(B) = AND(pred1(B))
            pred1(A) = AND(Equal(A["x"], 1))
        "#;

        let predicates = parse_predicates(input);
        let params = Params::default();

        let result = batch_predicates(
            preds_to_split_results(predicates),
            &params,
            "TestBatch",
            &HashMap::new(),
        );
        assert!(result.is_ok());

        let batches = result.unwrap();
        assert_eq!(batches.batch_count(), 1);

        // pred2 should reference pred1 via BatchSelf
        let pred2 = &batches.batches()[0].predicates()[0];
        let stmt = &pred2.statements[0];
        assert!(matches!(stmt.pred(), Predicate::BatchSelf(1))); // pred1 is at index 1
    }

    #[test]
    fn test_mutual_recursion_in_same_batch() {
        // pred1 calls pred2, pred2 calls pred1 - mutual recursion
        // This should work because they're in the same batch
        let input = r#"
            pred1(A) = AND(pred2(A))
            pred2(B) = AND(pred1(B))
        "#;

        let predicates = parse_predicates(input);
        let params = Params::default();

        let result = batch_predicates(
            preds_to_split_results(predicates),
            &params,
            "TestBatch",
            &HashMap::new(),
        );
        assert!(result.is_ok());

        let batches = result.unwrap();
        assert_eq!(batches.batch_count(), 1);
        assert_eq!(batches.total_predicate_count(), 2);

        // Both should use BatchSelf references
        let pred1 = &batches.batches()[0].predicates()[0];
        let pred2 = &batches.batches()[0].predicates()[1];
        assert!(matches!(
            pred1.statements[0].pred(),
            Predicate::BatchSelf(1)
        )); // calls pred2
        assert!(matches!(
            pred2.statements[0].pred(),
            Predicate::BatchSelf(0)
        )); // calls pred1
    }

    #[test]
    fn test_cross_batch_reference() {
        // 5 predicates where pred5 calls pred1
        // pred1-4 go in batch 0, pred5 in batch 1
        // pred5's call to pred1 should be a cross-batch reference
        let input = r#"
            pred1(A) = AND(Equal(A["x"], 1))
            pred2(B) = AND(Equal(B["y"], 2))
            pred3(C) = AND(Equal(C["z"], 3))
            pred4(D) = AND(Equal(D["w"], 4))
            pred5(E) = AND(pred1(E))
        "#;

        let predicates = parse_predicates(input);
        let params = Params::default(); // max_custom_batch_size = 4

        let result = batch_predicates(
            preds_to_split_results(predicates),
            &params,
            "TestBatch",
            &HashMap::new(),
        );
        assert!(result.is_ok());

        let batches = result.unwrap();
        assert_eq!(batches.batch_count(), 2);

        // pred5 should reference pred1 via CustomPredicateRef
        let pred5_batch = &batches.batches()[1];
        let pred5 = &pred5_batch.predicates()[0];
        let pred5_stmt = &pred5.statements[0];

        // The predicate should be a Custom reference to batch 0
        match pred5_stmt.pred() {
            Predicate::Custom(ref_) => {
                // Should reference batch 0, index 0 (pred1)
                assert_eq!(ref_.batch.id(), batches.batches()[0].id());
            }
            _ => panic!("Expected Custom predicate reference"),
        }
    }

    #[test]
    fn test_split_chain_spans_batches() {
        // Create a predicate that will split into 2-3 predicates
        // Then add more predicates to force the chain to span batches
        let input = r#"
            pred1(A) = AND(Equal(A["x"], 1))
            pred2(B) = AND(Equal(B["y"], 2))
            pred3(C) = AND(Equal(C["z"], 3))
            large_pred(D) = AND(
                Equal(D["a"], 1)
                Equal(D["b"], 2)
                Equal(D["c"], 3)
                Equal(D["d"], 4)
                Equal(D["e"], 5)
                Equal(D["f"], 6)
            )
        "#;

        let predicates = parse_predicates(input);
        let params = Params::default();

        // Split the large predicate
        let mut all_split_results = Vec::new();
        for pred in predicates {
            let result = split_predicate_if_needed(pred, &params).expect("Split failed");
            all_split_results.push(result);
        }

        // Count total predicates across all split results
        let total_preds: usize = all_split_results.iter().map(|r| r.predicates.len()).sum();

        // We should have: pred1, pred2, pred3, large_pred_1 (continuation), large_pred
        // That's 5 predicates, which spans 2 batches
        assert_eq!(total_preds, 5);

        let result = batch_predicates(all_split_results, &params, "TestBatch", &HashMap::new());
        assert!(result.is_ok());

        let batches = result.unwrap();
        assert_eq!(batches.batch_count(), 2);
        assert_eq!(batches.total_predicate_count(), 5);

        // Verify chain info was captured
        let chain_info = batches.split_chain("large_pred");
        assert!(chain_info.is_some());
        let info = chain_info.unwrap();
        assert_eq!(info.original_name, "large_pred");
        assert_eq!(info.total_real_statements, 6);
    }

    #[test]
    fn test_empty_input() {
        let split_results: Vec<SplitResult> = vec![];
        let params = Params::default();

        let result = batch_predicates(split_results, &params, "TestBatch", &HashMap::new());
        assert!(result.is_ok());

        let batches = result.unwrap();
        assert!(batches.is_empty());
        assert_eq!(batches.batch_count(), 0);
    }

    #[test]
    fn test_predicate_ref_by_name() {
        let input = r#"
            pred1(A) = AND(Equal(A["x"], 1))
            pred2(B) = AND(Equal(B["y"], 2))
        "#;

        let predicates = parse_predicates(input);
        let params = Params::default();

        let batches = batch_predicates(
            preds_to_split_results(predicates),
            &params,
            "TestBatch",
            &HashMap::new(),
        )
        .unwrap();

        // Should be able to look up both predicates
        assert!(batches.predicate_ref_by_name("pred1").is_some());
        assert!(batches.predicate_ref_by_name("pred2").is_some());
        assert!(batches.predicate_ref_by_name("nonexistent").is_none());
    }

    // ============================================================
    // Tests for apply_predicate
    // ============================================================

    /// Helper: create a unique Statement for testing
    /// Uses Equal with distinct literal values to create distinguishable statements
    fn test_statement(id: usize) -> Statement {
        use crate::middleware::ValueRef;
        Statement::Equal(
            ValueRef::Literal((id as i64).into()),
            ValueRef::Literal((id as i64).into()),
        )
    }

    #[test]
    fn test_apply_predicate_non_split() {
        // A simple predicate that doesn't need splitting
        let input = r#"
            my_pred(A, B) = AND(
                Equal(A["x"], B["y"])
            )
        "#;

        let predicates = parse_predicates(input);
        let params = Params::default();

        let batches = batch_predicates(
            preds_to_split_results(predicates),
            &params,
            "TestBatch",
            &HashMap::new(),
        )
        .unwrap();

        // Create fake statements
        let statements = vec![Statement::None, Statement::None];

        // Track operations applied
        let mut operations_applied: Vec<(bool, usize)> = Vec::new();
        let mut stmt_counter = 0;

        let result: Result<Statement, MultiOperationError> =
            batches.apply_predicate("my_pred", statements, true, |public, op| {
                operations_applied.push((public, op.1.len()));
                stmt_counter += 1;
                Ok(test_statement(stmt_counter))
            });

        assert!(result.is_ok());
        // Should be exactly one operation
        assert_eq!(operations_applied.len(), 1);
        // Should be public
        assert!(operations_applied[0].0);
        // Should have 2 arguments
        assert_eq!(operations_applied[0].1, 2);
    }

    #[test]
    fn test_apply_predicate_2_piece_split() {
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

        let predicates = parse_predicates(input);
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

        let batches = batch_predicates(split_results, &params, "TestBatch", &HashMap::new())
            .expect("Batch failed");

        // Verify chain info
        let chain_info = batches.split_chain("large_pred").unwrap();
        assert_eq!(chain_info.chain_pieces.len(), 2);
        assert_eq!(chain_info.total_real_statements, 6);

        // Create fake statements (6 for the 6 Equal statements)
        let statements: Vec<Statement> = (0..6).map(test_statement).collect();

        // Track operations
        let mut operations_applied: Vec<(bool, usize)> = Vec::new();
        let mut stmt_counter = 100;

        let result: Result<Statement, MultiOperationError> =
            batches.apply_predicate("large_pred", statements, true, |public, op| {
                operations_applied.push((public, op.1.len()));
                stmt_counter += 1;
                Ok(test_statement(stmt_counter))
            });

        assert!(result.is_ok());
        // Should be exactly 2 operations (innermost continuation first, then main)
        assert_eq!(operations_applied.len(), 2);
        // First operation (continuation) should be private
        assert!(!operations_applied[0].0);
        // Second operation (main) should be public
        assert!(operations_applied[1].0);
    }

    #[test]
    fn test_apply_predicate_3_piece_split() {
        // A predicate that will split into 3 pieces (needs more statements)
        let input = r#"
            very_large_pred(A) = AND(
                Equal(A["a"], 1)
                Equal(A["b"], 2)
                Equal(A["c"], 3)
                Equal(A["d"], 4)
                Equal(A["e"], 5)
                Equal(A["f"], 6)
                Equal(A["g"], 7)
                Equal(A["h"], 8)
                Equal(A["i"], 9)
                Equal(A["j"], 10)
            )
        "#;

        let predicates = parse_predicates(input);
        let params = Params::default();

        // Split the predicate
        let mut split_results = Vec::new();
        for pred in predicates {
            let result = split_predicate_if_needed(pred, &params).expect("Split failed");
            split_results.push(result);
        }

        // Should split into 3 pieces
        assert_eq!(split_results.len(), 1);
        assert_eq!(split_results[0].predicates.len(), 3);
        assert!(split_results[0].chain_info.is_some());

        let batches = batch_predicates(split_results, &params, "TestBatch", &HashMap::new())
            .expect("Batch failed");

        // Verify chain info
        let chain_info = batches.split_chain("very_large_pred").unwrap();
        assert_eq!(chain_info.chain_pieces.len(), 3);
        assert_eq!(chain_info.total_real_statements, 10);

        // Create fake statements (10 for the 10 Equal statements)
        let statements: Vec<Statement> = (0..10).map(test_statement).collect();

        // Track operations
        let mut operations_applied: Vec<(bool, usize)> = Vec::new();
        let mut stmt_counter = 100;

        let result: Result<Statement, MultiOperationError> =
            batches.apply_predicate("very_large_pred", statements, true, |public, op| {
                operations_applied.push((public, op.1.len()));
                stmt_counter += 1;
                Ok(test_statement(stmt_counter))
            });

        assert!(result.is_ok());
        // Should be exactly 3 operations
        assert_eq!(operations_applied.len(), 3);
        // First two operations (continuations) should be private
        assert!(!operations_applied[0].0);
        assert!(!operations_applied[1].0);
        // Final operation (main) should be public
        assert!(operations_applied[2].0);
    }

    #[test]
    fn test_apply_predicate_wrong_statement_count() {
        // A predicate that will split
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

        let predicates = parse_predicates(input);
        let params = Params::default();

        // Split the predicate
        let mut split_results = Vec::new();
        for pred in predicates {
            let result = split_predicate_if_needed(pred, &params).expect("Split failed");
            split_results.push(result);
        }

        let batches = batch_predicates(split_results, &params, "TestBatch", &HashMap::new())
            .expect("Batch failed");

        // Try with wrong number of statements (3 instead of 6)
        let statements: Vec<Statement> = (0..3).map(test_statement).collect();

        let result: Result<Statement, MultiOperationError> =
            batches.apply_predicate("large_pred", statements, true, |_, _| {
                Ok(test_statement(999))
            });

        assert!(result.is_err());
        let err = result.unwrap_err();
        match err {
            MultiOperationError::WrongStatementCount {
                predicate,
                expected,
                actual,
            } => {
                assert_eq!(predicate, "large_pred");
                assert_eq!(expected, 6);
                assert_eq!(actual, 3);
            }
            _ => panic!("Expected WrongStatementCount error, got {:?}", err),
        }
    }

    #[test]
    fn test_apply_predicate_not_found() {
        let input = r#"
            my_pred(A) = AND(Equal(A["x"], 1))
        "#;

        let predicates = parse_predicates(input);
        let params = Params::default();

        let batches = batch_predicates(
            preds_to_split_results(predicates),
            &params,
            "TestBatch",
            &HashMap::new(),
        )
        .unwrap();

        let result: Result<Statement, MultiOperationError> =
            batches.apply_predicate("nonexistent", vec![], true, |_, _| Ok(test_statement(999)));

        assert!(result.is_err());
        match result.unwrap_err() {
            MultiOperationError::PredicateNotFound(name) => {
                assert_eq!(name, "nonexistent");
            }
            e => panic!("Expected PredicateNotFound error, got {:?}", e),
        }
    }

    #[test]
    fn test_apply_predicate_chain_wiring() {
        // Test that chain links are properly wired (previous result replaces Statement::None)
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

        let predicates = parse_predicates(input);
        let params = Params::default();

        let mut split_results = Vec::new();
        for pred in predicates {
            let result = split_predicate_if_needed(pred, &params).expect("Split failed");
            split_results.push(result);
        }

        let batches = batch_predicates(split_results, &params, "TestBatch", &HashMap::new())
            .expect("Batch failed");

        let statements: Vec<Statement> = (0..6).map(test_statement).collect();

        // Track whether the second operation has the first result as its last arg
        let mut last_args_of_ops: Vec<Option<Statement>> = Vec::new();
        let mut stmt_counter = 100;

        let result: Result<Statement, MultiOperationError> =
            batches.apply_predicate("large_pred", statements, true, |_, op| {
                // Check the last argument
                let last_arg = op.1.last().map(|arg| {
                    if let OperationArg::Statement(s) = arg {
                        s.clone()
                    } else {
                        Statement::None
                    }
                });
                last_args_of_ops.push(last_arg);
                stmt_counter += 1;
                Ok(test_statement(stmt_counter))
            });

        assert!(result.is_ok());
        assert_eq!(last_args_of_ops.len(), 2);

        // First operation's last arg should NOT be the result of previous (no previous)
        // It might be Statement::None if no chain call, or a regular arg

        // Second operation's last arg SHOULD be test_statement(101) - the result from first op
        assert_eq!(last_args_of_ops[1], Some(test_statement(101)));
    }
}
