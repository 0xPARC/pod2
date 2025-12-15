//! Lowering from frontend AST to middleware structures
//!
//! This module converts validated frontend AST to middleware data structures.
//! Currently implements basic 1:1 conversion without automatic predicate splitting.

use std::{
    collections::{HashMap, HashSet},
    str::FromStr,
    sync::Arc,
};

use crate::{
    frontend::{BuilderArg, CustomPredicateBatchBuilder, StatementTmplBuilder},
    lang::{
        frontend_ast::*,
        frontend_ast_split,
        frontend_ast_validate::{PredicateKind, ValidatedAST},
    },
    middleware::{
        self, containers, CustomPredicateBatch, IntroPredicateRef, NativePredicate, Params,
        Predicate, StatementTmpl as MWStatementTmpl, StatementTmplArg as MWStatementTmplArg,
        Wildcard,
    },
};

/// Result of lowering: optional custom predicate batch and optional request
///
/// A Podlang file can contain:
/// - Just custom predicates (batch: Some, request: None)
/// - Just a request (batch: None, request: Some)
/// - Both (batch: Some, request: Some)
/// - Neither (batch: None, request: None) - just imports
#[derive(Debug, Clone)]
pub struct LoweredOutput {
    pub batch: Option<Arc<CustomPredicateBatch>>,
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
    /// Map of predicate names to their index in the current batch (for split predicates)
    batch_predicate_index: HashMap<String, usize>,
}

impl<'a> Lowerer<'a> {
    fn new(validated: ValidatedAST, params: &'a Params) -> Self {
        Self {
            validated,
            params,
            batch_predicate_index: HashMap::new(),
        }
    }

    fn lower(mut self, batch_name: String) -> Result<LoweredOutput, LoweringError> {
        // Lower custom predicates (if any)
        let batch = self.lower_batch(batch_name)?;

        // Lower request (if any) - pass batch so BatchSelf refs can be converted to Custom refs
        let request = self.lower_request(batch.as_ref())?;

        Ok(LoweredOutput { batch, request })
    }

    fn lower_batch(
        &mut self,
        batch_name: String,
    ) -> Result<Option<Arc<CustomPredicateBatch>>, LoweringError> {
        // Extract and split custom predicates from document
        let (custom_predicates, original_count) = self.extract_and_split_predicates()?;

        // If no custom predicates, return None
        if custom_predicates.is_empty() {
            return Ok(None);
        }

        // Check batch size constraint
        if custom_predicates.len() > self.params.max_custom_batch_size {
            return Err(LoweringError::TooManyPredicates {
                batch_name: batch_name.clone(),
                count: custom_predicates.len(),
                max: self.params.max_custom_batch_size,
                original_count,
            });
        }

        // Build index of all predicates in the batch
        for (idx, pred) in custom_predicates.iter().enumerate() {
            self.batch_predicate_index
                .insert(pred.name.name.clone(), idx);
        }

        // Create custom predicate batch using builder
        let mut cpb_builder =
            CustomPredicateBatchBuilder::new(self.params.clone(), batch_name.clone());

        for pred_def in &custom_predicates {
            self.lower_custom_predicate(pred_def, &mut cpb_builder)?;
        }

        Ok(Some(cpb_builder.finish()))
    }

    fn lower_request(
        &self,
        batch: Option<&Arc<CustomPredicateBatch>>,
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

        // Lower each statement to a builder first
        let mut statement_builders = Vec::new();
        for stmt in &request_def.statements {
            let stmt_builder = self.lower_statement_to_builder(stmt)?;
            statement_builders.push(stmt_builder);
        }

        // Resolve builders to middleware statement templates
        let mut request_templates = Vec::new();
        for stmt_builder in statement_builders {
            let mw_stmt =
                self.resolve_request_statement_builder(stmt_builder, &wildcard_map, batch)?;
            request_templates.push(mw_stmt);
        }

        Ok(Some(crate::frontend::PodRequest::new(request_templates)))
    }

    fn resolve_request_statement_builder(
        &self,
        stmt_builder: StatementTmplBuilder,
        wildcard_map: &HashMap<String, usize>,
        batch: Option<&Arc<CustomPredicateBatch>>,
    ) -> Result<MWStatementTmpl, LoweringError> {
        // First desugar the builder
        let desugared = stmt_builder.desugar();

        // Convert BatchSelf predicate to Custom if we have a batch
        let mut predicate = desugared.predicate;
        if let Some(batch_ref) = batch {
            if let Predicate::BatchSelf(index) = predicate {
                predicate = Predicate::Custom(middleware::CustomPredicateRef::new(
                    batch_ref.clone(),
                    index,
                ));
            }
        }

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
            pred: predicate,
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

    fn extract_and_split_predicates(
        &self,
    ) -> Result<(Vec<CustomPredicateDef>, usize), LoweringError> {
        let doc = self.validated.document();
        let predicates: Vec<CustomPredicateDef> = doc
            .items
            .iter()
            .filter_map(|item| match item {
                DocumentItem::CustomPredicateDef(pred) => Some(pred.clone()),
                _ => None,
            })
            .collect();

        let original_count = predicates.len();

        // Apply splitting to each predicate as needed
        let mut split_predicates = Vec::new();
        for pred in predicates {
            let chain = frontend_ast_split::split_predicate_if_needed(pred, self.params)?;
            split_predicates.extend(chain);
        }

        Ok((split_predicates, original_count))
    }

    fn lower_custom_predicate(
        &self,
        pred_def: &CustomPredicateDef,
        cpb_builder: &mut CustomPredicateBatchBuilder,
    ) -> Result<(), LoweringError> {
        let name = pred_def.name.name.clone();

        // Note: Constraint checking is handled by the splitting phase
        // Predicates passed here should already be within limits

        // Collect public and private argument names
        let mut public_arg_names = Vec::new();
        let mut private_arg_names = Vec::new();

        for arg in &pred_def.args.public_args {
            public_arg_names.push(arg.name.clone());
        }

        if let Some(private_args) = &pred_def.args.private_args {
            for arg in private_args {
                private_arg_names.push(arg.name.clone());
            }
        }

        // Lower statements to builders
        let mut statement_builders = Vec::new();
        for stmt in &pred_def.statements {
            let stmt_builder = self.lower_statement_to_builder(stmt)?;
            statement_builders.push(stmt_builder);
        }

        // Convert to &str slices for builder API
        let public_args_str: Vec<&str> = public_arg_names.iter().map(|s| s.as_str()).collect();
        let private_args_str: Vec<&str> = private_arg_names.iter().map(|s| s.as_str()).collect();

        // Add predicate to batch using builder
        let conjunction = pred_def.conjunction_type == ConjunctionType::And;

        cpb_builder
            .predicate(
                &name,
                conjunction,
                &public_args_str,
                &private_args_str,
                &statement_builders,
            )
            .map_err(|e| match e {
                crate::frontend::Error::Middleware(mw_err) => LoweringError::Middleware(mw_err),
                _ => LoweringError::InvalidArgumentType,
            })?;

        Ok(())
    }

    fn lower_statement_to_builder(
        &self,
        stmt: &StatementTmpl,
    ) -> Result<StatementTmplBuilder, LoweringError> {
        // Get predicate
        let pred_name = &stmt.predicate.name;
        let symbols = self.validated.symbols();

        // Check for native predicates first
        let predicate = if let Ok(native) = NativePredicate::from_str(pred_name) {
            Predicate::Native(native)
        } else if let Some(&index) = self.batch_predicate_index.get(pred_name) {
            // References to other predicates in the same batch (including split chains)
            Predicate::BatchSelf(index)
        } else if let Some(info) = symbols.predicates.get(pred_name) {
            match &info.kind {
                PredicateKind::Native(np) => Predicate::Native(*np),
                PredicateKind::Custom { index } => Predicate::BatchSelf(*index),
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
            unreachable!("Predicate {} not found", pred_name);
        };

        // Check args count
        if stmt.args.len() > self.params.max_statement_args {
            return Err(LoweringError::TooManyStatementArgs {
                count: stmt.args.len(),
                max: self.params.max_statement_args,
            });
        }

        // Convert AST args to BuilderArgs
        let mut builder = StatementTmplBuilder::new(predicate);
        for arg in &stmt.args {
            let builder_arg = Self::lower_statement_arg_to_builder(arg)?;
            builder = builder.arg(builder_arg);
        }

        // Return builder without calling .desugar() - that will happen later
        Ok(builder)
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

    // Helper to get the batch from the output (expecting it to exist)
    fn expect_batch(output: &LoweredOutput) -> &Arc<CustomPredicateBatch> {
        output.batch.as_ref().expect("Expected batch to be present")
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
        assert_eq!(expect_batch(&lowered).predicates().len(), 2);

        // First predicate should have 5 statements (4 + chain call)
        assert_eq!(expect_batch(&lowered).predicates()[0].statements().len(), 5);

        // Second predicate should have 2 statements
        assert_eq!(expect_batch(&lowered).predicates()[1].statements().len(), 2);
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
    fn test_error_message_with_splitting() {
        // Create a document with predicates that will exceed the batch limit after splitting
        // We'll create 2 predicates with 4 statements each (max arity = 5)
        // Each will NOT split individually, but together they exceed a small batch limit
        let input = r#"
            pred1(A) = AND (
                Equal(A["a"], 1)
                Equal(A["b"], 2)
            )
            pred2(B) = AND (
                Equal(B["c"], 3)
                Equal(B["d"], 4)
            )
        "#;

        // Use very restrictive params to force the error
        let params = Params {
            max_custom_batch_size: 1,
            ..Default::default()
        };

        let result = parse_validate_and_lower(input, &params);

        // Should fail with TooManyPredicates error
        assert!(result.is_err());
        let err = result.unwrap_err();

        if let LoweringError::TooManyPredicates {
            count,
            max,
            original_count,
            ..
        } = err
        {
            assert_eq!(count, 2); // 2 predicates after splitting (no splitting occurred)
            assert_eq!(max, 1);
            assert_eq!(original_count, 2); // Started with 2 predicates

            // Error message should NOT mention splitting since no splitting occurred
            let err_msg = format!("{}", err);
            assert!(!err_msg.contains("before automatic splitting"));
        } else {
            panic!("Expected TooManyPredicates error, got: {:?}", err);
        }
    }

    #[test]
    fn test_error_message_after_splitting() {
        // Create TWO predicates that will EACH split into 2 predicates
        // This tests the case where splitting causes the batch to be too large
        // but no individual predicate chain exceeds the limit
        let input = r#"
            pred1(A) = AND (
                Equal(A["a"], 1)
                Equal(A["b"], 2)
                Equal(A["c"], 3)
                Equal(A["d"], 4)
                Equal(A["e"], 5)
                Equal(A["f"], 6)
            )
            pred2(B) = AND (
                Equal(B["a"], 1)
                Equal(B["b"], 2)
                Equal(B["c"], 3)
                Equal(B["d"], 4)
                Equal(B["e"], 5)
                Equal(B["f"], 6)
            )
        "#;

        // Use params where each predicate splits into 2, but total of 4 exceeds batch limit
        let params = Params {
            // Allow 3 predicates in batch
            // Default max_custom_predicate_arity is 5, so each will split into 2 predicates
            // Total: 2 original predicates -> 4 after splitting (exceeds limit of 3)
            max_custom_batch_size: 3,
            ..Default::default()
        };

        let result = parse_validate_and_lower(input, &params);

        // Should fail with TooManyPredicates error
        assert!(result.is_err());
        let err = result.unwrap_err();

        if let LoweringError::TooManyPredicates {
            count,
            max,
            original_count,
            ..
        } = err
        {
            assert_eq!(count, 4); // 4 predicates after splitting (2 from each)
            assert_eq!(max, 3);
            assert_eq!(original_count, 2); // Started with 2 predicates

            // Error message SHOULD mention splitting since splitting occurred
            let err_msg = format!("{}", err);
            assert!(err_msg.contains("before automatic splitting"));
            assert!(err_msg.contains("started with 2 predicates"));
        } else {
            panic!("Expected TooManyPredicates error, got: {:?}", err);
        }
    }
}
