//! Lowering from frontend AST to middleware structures
//!
//! This module converts validated frontend AST to middleware data structures.
//! Supports automatic predicate splitting and multi-batch packing.

use std::{
    collections::{HashMap, HashSet},
    str::FromStr,
};

use crate::{
    frontend::{BuilderArg, StatementTmplBuilder},
    lang::{
        frontend_ast::*,
        frontend_ast_batch::{self, PredicateBatches},
        frontend_ast_split,
        frontend_ast_validate::{PredicateKind, ValidatedAST},
    },
    middleware::{
        self, containers, IntroPredicateRef, NativePredicate, Params, Predicate,
        StatementTmpl as MWStatementTmpl, StatementTmplArg as MWStatementTmplArg, Wildcard,
    },
};

/// Result of lowering: optional custom predicate batches and optional request
///
/// A Podlang file can contain:
/// - Just custom predicates (batches: Some, request: None)
/// - Just a request (batches: None, request: Some)
/// - Both (batches: Some, request: Some)
/// - Neither (batches: None, request: None) - just imports
#[derive(Debug, Clone)]
pub struct LoweredOutput {
    pub batches: Option<PredicateBatches>,
    pub request: Option<crate::frontend::PodRequest>,
}

pub use crate::lang::error::LoweringError;

/// Lower a validated AST to middleware structures
///
/// Returns both the custom predicate batch (if any) and the request (if any).
/// At least one will be Some if the document contains custom predicates or a request.
pub fn lower(
    validated: ValidatedAST,
    params: &Params,
    batch_name: String,
) -> Result<LoweredOutput, LoweringError> {
    if !validated.diagnostics().is_empty() {
        // For now, treat any diagnostics as errors
        // In future we could allow warnings
        return Err(LoweringError::ValidationErrors);
    }

    let lowerer = Lowerer::new(validated, params);
    lowerer.lower(batch_name)
}

struct Lowerer<'a> {
    validated: ValidatedAST,
    params: &'a Params,
}

impl<'a> Lowerer<'a> {
    fn new(validated: ValidatedAST, params: &'a Params) -> Self {
        Self { validated, params }
    }

    fn lower(self, batch_name: String) -> Result<LoweredOutput, LoweringError> {
        // Lower custom predicates (if any) - now supports multiple batches
        let batches = self.lower_batches(batch_name)?;

        // Lower request (if any) - pass batches so refs can be resolved
        let request = self.lower_request(batches.as_ref())?;

        Ok(LoweredOutput { batches, request })
    }

    fn lower_batches(&self, batch_name: String) -> Result<Option<PredicateBatches>, LoweringError> {
        // Extract and split custom predicates from document
        let custom_predicates = self.extract_and_split_predicates()?;

        // If no custom predicates, return None
        if custom_predicates.is_empty() {
            return Ok(None);
        }

        // Build map of imported predicates for batching
        let imported_predicates = self.build_imported_predicates_map();

        // Use the new batching module to pack predicates into batches
        let batches = frontend_ast_batch::batch_predicates(
            custom_predicates,
            self.params,
            &batch_name,
            &imported_predicates,
        )?;

        Ok(Some(batches))
    }

    fn build_imported_predicates_map(
        &self,
    ) -> HashMap<String, frontend_ast_batch::ImportedPredicateInfo> {
        let symbols = self.validated.symbols();
        let mut imported = HashMap::new();

        for (name, info) in &symbols.predicates {
            if let PredicateKind::BatchImported { batch, index } = &info.kind {
                imported.insert(
                    name.clone(),
                    frontend_ast_batch::ImportedPredicateInfo {
                        batch: batch.clone(),
                        index: *index,
                    },
                );
            }
        }

        imported
    }

    fn lower_request(
        &self,
        batches: Option<&PredicateBatches>,
    ) -> Result<Option<crate::frontend::PodRequest>, LoweringError> {
        let doc = self.validated.document();

        // Find request definition (if any)
        let request_def = doc.items.iter().find_map(|item| match item {
            DocumentItem::RequestDef(req) => Some(req),
            _ => None,
        });

        let Some(request_def) = request_def else {
            return Ok(None);
        };

        // Build wildcard map from all wildcards used in the request statements
        let wildcard_map = self.build_request_wildcard_map(request_def);

        // Lower each statement to middleware templates, resolving predicates
        let mut request_templates = Vec::new();
        for stmt in &request_def.statements {
            let mw_stmt = self.lower_request_statement(stmt, &wildcard_map, batches)?;
            request_templates.push(mw_stmt);
        }

        Ok(Some(crate::frontend::PodRequest::new(request_templates)))
    }

    fn lower_request_statement(
        &self,
        stmt: &StatementTmpl,
        wildcard_map: &HashMap<String, usize>,
        batches: Option<&PredicateBatches>,
    ) -> Result<MWStatementTmpl, LoweringError> {
        let pred_name = &stmt.predicate.name;
        let symbols = self.validated.symbols();

        // Resolve predicate - for request statements, local custom predicates
        // must be resolved to CustomPredicateRef (not BatchSelf)
        let predicate = if let Ok(native) = NativePredicate::from_str(pred_name) {
            Predicate::Native(native)
        } else if let Some(info) = symbols.predicates.get(pred_name) {
            match &info.kind {
                PredicateKind::Native(np) => Predicate::Native(*np),
                PredicateKind::Custom { .. } => {
                    // Local custom predicates - resolve to CustomPredicateRef
                    let batches = batches.ok_or_else(|| LoweringError::PredicateNotFound {
                        name: pred_name.clone(),
                    })?;
                    let pred_ref = batches.predicate_ref_by_name(pred_name).ok_or_else(|| {
                        LoweringError::PredicateNotFound {
                            name: pred_name.clone(),
                        }
                    })?;
                    Predicate::Custom(pred_ref)
                }
                PredicateKind::BatchImported { batch, index } => {
                    Predicate::Custom(middleware::CustomPredicateRef::new(batch.clone(), *index))
                }
                PredicateKind::IntroImported {
                    name,
                    verifier_data_hash,
                } => Predicate::Intro(IntroPredicateRef {
                    name: name.clone(),
                    args_len: info.public_arity,
                    verifier_data_hash: *verifier_data_hash,
                }),
            }
        } else {
            return Err(LoweringError::PredicateNotFound {
                name: pred_name.clone(),
            });
        };

        // Create a builder with the resolved predicate and desugar
        let mut builder = StatementTmplBuilder::new(predicate);
        for arg in &stmt.args {
            let builder_arg = Self::lower_statement_arg_to_builder(arg)?;
            builder = builder.arg(builder_arg);
        }
        let desugared = builder.desugar();

        // Convert BuilderArgs to StatementTmplArgs
        let mut mw_args = Vec::new();
        for builder_arg in desugared.args {
            let mw_arg = match builder_arg {
                BuilderArg::Literal(value) => MWStatementTmplArg::Literal(value),
                BuilderArg::WildcardLiteral(name) => {
                    let index = wildcard_map.get(&name).expect("Wildcard not found");
                    MWStatementTmplArg::Wildcard(Wildcard::new(name, *index))
                }
                BuilderArg::Key(root_name, key_str) => {
                    let root_index = wildcard_map
                        .get(&root_name)
                        .expect("Root wildcard not found");
                    let wildcard = Wildcard::new(root_name, *root_index);
                    let key = middleware::Key::from(key_str.as_str());
                    MWStatementTmplArg::AnchoredKey(wildcard, key)
                }
            };
            mw_args.push(mw_arg);
        }

        Ok(MWStatementTmpl {
            pred: desugared.predicate,
            args: mw_args,
        })
    }

    fn build_request_wildcard_map(&self, request_def: &RequestDef) -> HashMap<String, usize> {
        // Collect all unique wildcards from all statements
        let mut wildcard_names = Vec::new();
        let mut seen = HashSet::new();

        for stmt in &request_def.statements {
            self.collect_statement_wildcards(stmt, &mut wildcard_names, &mut seen);
        }

        // Build map from name to index
        wildcard_names
            .into_iter()
            .enumerate()
            .map(|(idx, name)| (name, idx))
            .collect()
    }

    fn collect_statement_wildcards(
        &self,
        stmt: &StatementTmpl,
        names: &mut Vec<String>,
        seen: &mut HashSet<String>,
    ) {
        for arg in &stmt.args {
            match arg {
                StatementTmplArg::Wildcard(id) => {
                    if !seen.contains(&id.name) {
                        seen.insert(id.name.clone());
                        names.push(id.name.clone());
                    }
                }
                StatementTmplArg::AnchoredKey(ak) => {
                    if !seen.contains(&ak.root.name) {
                        seen.insert(ak.root.name.clone());
                        names.push(ak.root.name.clone());
                    }
                }
                StatementTmplArg::Literal(_) => {}
            }
        }
    }

    fn extract_and_split_predicates(&self) -> Result<Vec<CustomPredicateDef>, LoweringError> {
        let doc = self.validated.document();
        let predicates: Vec<CustomPredicateDef> = doc
            .items
            .iter()
            .filter_map(|item| match item {
                DocumentItem::CustomPredicateDef(pred) => Some(pred.clone()),
                _ => None,
            })
            .collect();

        // Apply splitting to each predicate as needed
        let mut split_predicates = Vec::new();
        for pred in predicates {
            let chain = frontend_ast_split::split_predicate_if_needed(pred, self.params)?;
            split_predicates.extend(chain);
        }

        Ok(split_predicates)
    }

    fn lower_statement_arg_to_builder(arg: &StatementTmplArg) -> Result<BuilderArg, LoweringError> {
        match arg {
            StatementTmplArg::Literal(lit) => {
                let value = Self::lower_literal(lit)?;
                Ok(BuilderArg::Literal(value))
            }
            StatementTmplArg::Wildcard(id) => {
                // For builder, we just need the wildcard name
                Ok(BuilderArg::WildcardLiteral(id.name.clone()))
            }
            StatementTmplArg::AnchoredKey(ak) => {
                let key_str = match &ak.key {
                    AnchoredKeyPath::Bracket(s) => s.value.clone(),
                    AnchoredKeyPath::Dot(id) => id.name.clone(),
                };
                Ok(BuilderArg::Key(ak.root.name.clone(), key_str))
            }
        }
    }

    fn lower_literal(lit: &LiteralValue) -> Result<middleware::Value, LoweringError> {
        let value = match lit {
            LiteralValue::Int(i) => middleware::Value::from(i.value),
            LiteralValue::Bool(b) => middleware::Value::from(b.value),
            LiteralValue::String(s) => middleware::Value::from(s.value.clone()),
            LiteralValue::Raw(r) => middleware::Value::from(r.hash.hash),
            LiteralValue::PublicKey(pk) => middleware::Value::from(pk.point),
            LiteralValue::SecretKey(sk) => middleware::Value::from(sk.secret_key.clone()),
            LiteralValue::Array(a) => {
                let elements: Result<Vec<_>, _> =
                    a.elements.iter().map(Self::lower_literal).collect();
                let array = containers::Array::new(elements?);
                middleware::Value::from(array)
            }
            LiteralValue::Set(s) => {
                let elements: Result<Vec<_>, _> =
                    s.elements.iter().map(Self::lower_literal).collect();
                let set_values: std::collections::HashSet<_> = elements?.into_iter().collect();
                let set = containers::Set::new(set_values);
                middleware::Value::from(set)
            }
            LiteralValue::Dict(d) => {
                let pairs: Result<Vec<(middleware::Key, middleware::Value)>, LoweringError> = d
                    .pairs
                    .iter()
                    .map(|pair| {
                        let key = middleware::Key::from(pair.key.value.as_str());
                        let value = Self::lower_literal(&pair.value)?;
                        Ok((key, value))
                    })
                    .collect();
                let dict_map: std::collections::HashMap<_, _> = pairs?.into_iter().collect();
                let dict = containers::Dictionary::new(dict_map);
                middleware::Value::from(dict)
            }
        };
        Ok(value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::{
        frontend_ast::parse::parse_document, frontend_ast_validate::validate, parser::parse_podlang,
    };

    fn parse_validate_and_lower(
        input: &str,
        params: &Params,
    ) -> Result<LoweredOutput, LoweringError> {
        let parsed = parse_podlang(input).expect("Failed to parse");
        let document = parse_document(parsed.into_iter().next().unwrap()).expect("Failed to parse");
        let validated = validate(document, &[]).expect("Failed to validate");
        lower(validated, params, "test_batch".to_string())
    }

    // Helper to get the first batch from the output (expecting it to exist)
    fn expect_batch(
        output: &LoweredOutput,
    ) -> &std::sync::Arc<crate::middleware::CustomPredicateBatch> {
        output
            .batches
            .as_ref()
            .expect("Expected batches to be present")
            .first_batch()
            .expect("Expected at least one batch")
    }

    #[test]
    fn test_simple_predicate() {
        let input = r#"
            my_pred(A, B) = AND (
                Equal(A["foo"], B["bar"])
            )
        "#;

        let params = Params::default();
        let result = parse_validate_and_lower(input, &params);
        if let Err(e) = &result {
            eprintln!("Error: {:?}", e);
        }
        assert!(result.is_ok());

        let lowered = result.unwrap();
        assert_eq!(expect_batch(&lowered).predicates().len(), 1);

        let pred = &expect_batch(&lowered).predicates()[0];
        assert_eq!(pred.name, "my_pred");
        assert_eq!(pred.args_len(), 2);
        assert_eq!(pred.wildcard_names().len(), 2);
        assert_eq!(pred.statements().len(), 1);
    }

    #[test]
    fn test_private_args() {
        let input = r#"
            my_pred(A, private: B, C) = AND (
                Equal(A["x"], B["y"])
                Equal(B["z"], C["w"])
            )
        "#;

        let params = Params::default();
        let result = parse_validate_and_lower(input, &params);
        assert!(result.is_ok());

        let lowered = result.unwrap();
        let pred = &expect_batch(&lowered).predicates()[0];
        assert_eq!(pred.args_len(), 1); // Only A is public
        assert_eq!(pred.wildcard_names().len(), 3); // A, B, C total
    }

    #[test]
    fn test_or_predicate() {
        let input = r#"
            my_pred(A, B) = OR (
                Equal(A["x"], 1)
                Equal(B["y"], 2)
            )
        "#;

        let params = Params::default();
        let result = parse_validate_and_lower(input, &params);
        assert!(result.is_ok());

        let lowered = result.unwrap();
        let pred = &expect_batch(&lowered).predicates()[0];
        assert!(pred.is_disjunction());
    }

    #[test]
    fn test_automatic_splitting() {
        let input = r#"
            my_pred(A) = AND (
                Equal(A["a"], 1)
                Equal(A["b"], 2)
                Equal(A["c"], 3)
                Equal(A["d"], 4)
                Equal(A["e"], 5)
                Equal(A["f"], 6)
            )
        "#;

        let params = Params::default(); // max_custom_predicate_arity = 5
        let result = parse_validate_and_lower(input, &params);
        if let Err(e) = &result {
            eprintln!("Splitting error: {:?}", e);
        }
        assert!(result.is_ok());

        let lowered = result.unwrap();
        // Should be automatically split into 2 predicates (my_pred and my_pred_1)
        let batches = lowered.batches.as_ref().expect("Expected batches");
        assert_eq!(batches.total_predicate_count(), 2);

        // With topological sorting, my_pred_1 comes first (since my_pred depends on it)
        // my_pred_1 has 2 statements
        // my_pred has 5 statements (4 + chain call)
        // Just verify we have the right total statement counts
        let batch = batches.first_batch().unwrap();
        let total_statements: usize = batch
            .predicates()
            .iter()
            .map(|p| p.statements().len())
            .sum();
        assert_eq!(total_statements, 7); // 5 + 2 = 7 total statements
    }

    #[test]
    fn test_multiple_predicates() {
        let input = r#"
            pred1(A) = AND (
                Equal(A["x"], 1)
            )

            pred2(B) = AND (
                Equal(B["y"], 2)
            )
        "#;

        let params = Params::default();
        let result = parse_validate_and_lower(input, &params);
        assert!(result.is_ok());

        let lowered = result.unwrap();
        assert_eq!(expect_batch(&lowered).predicates().len(), 2);
    }

    #[test]
    fn test_batch_self_reference() {
        let input = r#"
            pred1(A) = AND (
                Equal(A["x"], 1)
            )

            pred2(B) = AND (
                pred1(B)
            )
        "#;

        let params = Params::default();
        let result = parse_validate_and_lower(input, &params);
        assert!(result.is_ok());

        let lowered = result.unwrap();
        let pred2 = &expect_batch(&lowered).predicates()[1];
        let stmt = &pred2.statements()[0];

        // Should be BatchSelf(0) referring to pred1
        assert!(matches!(stmt.pred, Predicate::BatchSelf(0)));
    }

    #[test]
    fn test_literals() {
        let input = r#"
            my_pred(X) = AND (
                Equal(X["int"], 42)
                Equal(X["bool"], true)
                Equal(X["string"], "hello")
            )
        "#;

        let params = Params::default();
        let result = parse_validate_and_lower(input, &params);
        assert!(result.is_ok());
    }

    #[test]
    fn test_syntactic_sugar_desugaring() {
        let input = r#"
            my_pred(D) = AND (
                DictContains(D, "key", "value")
            )
        "#;

        let params = Params::default();
        let result = parse_validate_and_lower(input, &params);
        assert!(result.is_ok());

        let lowered = result.unwrap();
        let pred = &expect_batch(&lowered).predicates()[0];
        let stmt = &pred.statements()[0];

        // Should desugar to the Contains predicate
        assert!(matches!(
            stmt.pred,
            Predicate::Native(NativePredicate::Contains)
        ));
    }

    #[test]
    fn test_multi_batch_packing() {
        // Create more predicates than fit in a single batch
        // With max_custom_batch_size = 4, 5 predicates should span 2 batches
        let input = r#"
            pred1(A) = AND(Equal(A["a"], 1))
            pred2(B) = AND(Equal(B["b"], 2))
            pred3(C) = AND(Equal(C["c"], 3))
            pred4(D) = AND(Equal(D["d"], 4))
            pred5(E) = AND(Equal(E["e"], 5))
        "#;

        let params = Params::default(); // max_custom_batch_size = 4

        let result = parse_validate_and_lower(input, &params);
        assert!(result.is_ok());

        let lowered = result.unwrap();
        let batches = lowered.batches.as_ref().expect("Expected batches");

        // Should have 2 batches
        assert_eq!(batches.batch_count(), 2);
        assert_eq!(batches.total_predicate_count(), 5);

        // First batch should have 4 predicates
        assert_eq!(batches.batches()[0].predicates().len(), 4);
        // Second batch should have 1 predicate
        assert_eq!(batches.batches()[1].predicates().len(), 1);
    }

    #[test]
    fn test_split_chains_span_batches() {
        // Create predicates that will split, plus additional predicates
        // to force the split chains across batch boundaries
        let input = r#"
            pred1(A) = AND(Equal(A["a"], 1))
            pred2(B) = AND(Equal(B["b"], 2))
            pred3(C) = AND(Equal(C["c"], 3))
            large_pred(D) = AND(
                Equal(D["a"], 1)
                Equal(D["b"], 2)
                Equal(D["c"], 3)
                Equal(D["d"], 4)
                Equal(D["e"], 5)
                Equal(D["f"], 6)
            )
        "#;

        let params = Params::default();

        let result = parse_validate_and_lower(input, &params);
        assert!(result.is_ok());

        let lowered = result.unwrap();
        let batches = lowered.batches.as_ref().expect("Expected batches");

        // pred1, pred2, pred3 + large_pred split into 2 = 5 total predicates
        // Should span 2 batches
        assert_eq!(batches.total_predicate_count(), 5);
        assert_eq!(batches.batch_count(), 2);
    }
}
