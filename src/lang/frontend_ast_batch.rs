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
    frontend::{BuilderArg, CustomPredicateBatchBuilder, StatementTmplBuilder},
    lang::{
        error::BatchingError,
        frontend_ast::{AnchoredKeyPath, ConjunctionType, CustomPredicateDef, StatementTmplArg},
    },
    middleware::{CustomPredicateBatch, CustomPredicateRef, NativePredicate, Params, Predicate},
};

/// Container for multiple predicate batches
#[derive(Debug, Clone)]
pub struct PredicateBatches {
    batches: Vec<Arc<CustomPredicateBatch>>,
    /// Maps predicate name to (batch_index, predicate_index_within_batch)
    predicate_index: HashMap<String, (usize, usize)>,
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
        }
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
/// Takes a list of predicates (already split if needed) and packs them into
/// batches, handling cross-batch references correctly.
///
/// Predicates are assigned to batches in declaration order. Within a batch,
/// predicates can reference each other freely via BatchSelf. Cross-batch
/// references must point to earlier batches (forward cross-batch references
/// are an error).
///
/// `imported_predicates` maps predicate names to their imported batch info,
/// allowing predicates to call imported predicates from other batches.
pub fn batch_predicates(
    predicates: Vec<CustomPredicateDef>,
    params: &Params,
    base_batch_name: &str,
    imported_predicates: &HashMap<String, ImportedPredicateInfo>,
) -> Result<PredicateBatches, BatchingError> {
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

    #[test]
    fn test_single_predicate_single_batch() {
        let input = r#"
            my_pred(A, B) = AND(
                Equal(A["x"], B["y"])
            )
        "#;

        let predicates = parse_predicates(input);
        let params = Params::default();

        let result = batch_predicates(predicates, &params, "TestBatch", &HashMap::new());
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

        let result = batch_predicates(predicates, &params, "TestBatch", &HashMap::new());
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

        let result = batch_predicates(predicates, &params, "TestBatch", &HashMap::new());
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

        let result = batch_predicates(predicates, &params, "TestBatch", &HashMap::new());
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

        let result = batch_predicates(predicates, &params, "TestBatch", &HashMap::new());
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

        let result = batch_predicates(predicates, &params, "TestBatch", &HashMap::new());
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
        let mut all_predicates = Vec::new();
        for pred in predicates {
            let chain = split_predicate_if_needed(pred, &params).expect("Split failed");
            all_predicates.extend(chain);
        }

        // We should have: pred1, pred2, pred3, large_pred, large_pred_1
        // That's 5 predicates, which spans 2 batches
        assert_eq!(all_predicates.len(), 5);

        let result = batch_predicates(all_predicates, &params, "TestBatch", &HashMap::new());
        assert!(result.is_ok());

        let batches = result.unwrap();
        assert_eq!(batches.batch_count(), 2);
        assert_eq!(batches.total_predicate_count(), 5);
    }

    #[test]
    fn test_empty_input() {
        let predicates: Vec<CustomPredicateDef> = vec![];
        let params = Params::default();

        let result = batch_predicates(predicates, &params, "TestBatch", &HashMap::new());
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

        let batches = batch_predicates(predicates, &params, "TestBatch", &HashMap::new()).unwrap();

        // Should be able to look up both predicates
        assert!(batches.predicate_ref_by_name("pred1").is_some());
        assert!(batches.predicate_ref_by_name("pred2").is_some());
        assert!(batches.predicate_ref_by_name("nonexistent").is_none());
    }
}
