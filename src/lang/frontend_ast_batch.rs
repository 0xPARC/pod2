//! Building predicate modules
//!
//! This module implements building a single Module from split predicate results.
//! With Merkle tree backing supporting up to 65536 predicates per module,
//! multi-batch packing is no longer needed for predicates from a single document.

use std::collections::HashMap;

use crate::{
    frontend::{CustomPredicateBatchBuilder, StatementTmplBuilder},
    lang::{
        error::BatchingError,
        frontend_ast::{ConjunctionType, CustomPredicateDef},
        frontend_ast_lower::{lower_statement_arg, resolve_predicate_ref, ResolutionContext},
        frontend_ast_split::SplitResult,
        frontend_ast_validate::SymbolTable,
        Module,
    },
    middleware::{CustomPredicateBatch, Params},
};

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
) -> Result<std::sync::Arc<CustomPredicateBatch>, BatchingError> {
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
    use std::collections::HashMap;

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
        let validated =
            validate(document.clone(), &HashMap::new(), ParseMode::Module).expect("Failed to validate");

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
