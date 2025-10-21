//! Lowering from frontend AST to middleware structures
//!
//! This module converts validated frontend AST to middleware data structures.
//! Currently implements basic 1:1 conversion without automatic predicate splitting.

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use hex::FromHex;

#[cfg(test)]
use crate::middleware::NativePredicate;
use crate::{
    backends::plonky2::{deserialize_bytes, primitives::ec::curve::Point},
    lang::{
        frontend_ast::*,
        frontend_ast_split,
        frontend_ast_validate::{PredicateKind, ValidatedAST},
        utils::native_predicate_from_string,
    },
    middleware::{
        self, containers, CustomPredicate, CustomPredicateBatch, IntroPredicateRef, Params,
        Predicate, RawValue, SecretKey, StatementTmpl as MWStatementTmpl,
        StatementTmplArg as MWStatementTmplArg, Wildcard,
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
        let custom_predicates = self.extract_and_split_predicates()?;

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
            });
        }

        // Build index of all predicates in the batch
        for (idx, pred) in custom_predicates.iter().enumerate() {
            self.batch_predicate_index
                .insert(pred.name.name.clone(), idx);
        }

        // Create middleware custom predicates
        let mut middleware_predicates = Vec::new();
        for pred_def in &custom_predicates {
            let mw_pred = self.lower_custom_predicate(pred_def)?;
            middleware_predicates.push(mw_pred);
        }

        // Create batch
        let batch =
            CustomPredicateBatch::new(self.params, batch_name.clone(), middleware_predicates);

        Ok(Some(batch))
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

        // Lower each statement in the request
        let mut request_templates = Vec::new();
        for stmt in &request_def.statements {
            let mut mw_stmt = self.lower_statement_tmpl_frontend(stmt, &wildcard_map)?;

            // Convert BatchSelf references to Custom references
            // In a REQUEST context, we need to use Custom refs, not BatchSelf
            if let Some(batch_ref) = batch {
                if let Predicate::BatchSelf(index) = &mw_stmt.pred {
                    mw_stmt.pred = Predicate::Custom(middleware::CustomPredicateRef::new(
                        batch_ref.clone(),
                        *index,
                    ));
                }
            }

            request_templates.push(mw_stmt);
        }

        Ok(Some(crate::frontend::PodRequest::new(request_templates)))
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
                StatementArg::Identifier(id) => {
                    if !seen.contains(&id.name) {
                        seen.insert(id.name.clone());
                        names.push(id.name.clone());
                    }
                }
                StatementArg::AnchoredKey(ak) => {
                    if !seen.contains(&ak.root.name) {
                        seen.insert(ak.root.name.clone());
                        names.push(ak.root.name.clone());
                    }
                }
                StatementArg::Literal(_) => {}
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

    fn lower_custom_predicate(
        &self,
        pred_def: &CustomPredicateDef,
    ) -> Result<CustomPredicate, LoweringError> {
        let name = pred_def.name.name.clone();

        // Note: Constraint checking is handled by the splitting phase
        // Predicates passed here should already be within limits

        // Build wildcard mapping
        let mut wildcard_map = HashMap::new();
        let mut wildcard_names = Vec::new();
        let mut index = 0;

        for arg in &pred_def.args.public_args {
            wildcard_map.insert(arg.name.clone(), index);
            wildcard_names.push(arg.name.clone());
            index += 1;
        }

        if let Some(private_args) = &pred_def.args.private_args {
            for arg in private_args {
                wildcard_map.insert(arg.name.clone(), index);
                wildcard_names.push(arg.name.clone());
                index += 1;
            }
        }

        // Lower statements
        let mut middleware_statements = Vec::new();
        for stmt in &pred_def.statements {
            let mw_stmt = self.lower_statement_tmpl_frontend(stmt, &wildcard_map)?;
            middleware_statements.push(mw_stmt);
        }

        // Create custom predicate
        let args_len = pred_def.args.public_args.len();
        let conjunction = pred_def.conjunction_type == ConjunctionType::And;

        let custom_pred = if conjunction {
            CustomPredicate::and(
                self.params,
                name,
                middleware_statements,
                args_len,
                wildcard_names,
            )?
        } else {
            CustomPredicate::or(
                self.params,
                name,
                middleware_statements,
                args_len,
                wildcard_names,
            )?
        };

        Ok(custom_pred)
    }

    fn lower_statement_tmpl_frontend(
        &self,
        stmt: &StatementTmpl,
        wildcard_map: &HashMap<String, usize>,
    ) -> Result<MWStatementTmpl, LoweringError> {
        // Get predicate
        let pred_name = &stmt.predicate.name;
        let symbols = self.validated.symbols();

        // Check for native predicates first
        let mut predicate = if let Some(native) = native_predicate_from_string(pred_name) {
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
                    args_len,
                    verifier_data_hash,
                } => Predicate::Intro(IntroPredicateRef {
                    name: name.clone(),
                    args_len: *args_len,
                    verifier_data_hash: *verifier_data_hash,
                }),
            }
        } else {
            return Err(LoweringError::PredicateNotFound {
                name: pred_name.clone(),
            });
        };

        // Check args count
        if stmt.args.len() > self.params.max_statement_args {
            return Err(LoweringError::TooManyStatementArgs {
                count: stmt.args.len(),
                max: self.params.max_statement_args,
            });
        }

        // Lower arguments
        let mut mw_args = Vec::new();
        for arg in &stmt.args {
            let mw_arg = self.lower_statement_arg_frontend(arg, wildcard_map)?;
            mw_args.push(mw_arg);
        }

        // Desugar syntactic sugar predicates
        if let Predicate::Native(ref mut np) = predicate {
            match np {
                // GtEq/Gt -> LtEq/Lt with reversed args
                middleware::NativePredicate::GtEq => {
                    *np = middleware::NativePredicate::LtEq;
                    mw_args.reverse();
                }
                middleware::NativePredicate::Gt => {
                    *np = middleware::NativePredicate::Lt;
                    mw_args.reverse();
                }
                // Container predicates -> Contains/NotContains
                middleware::NativePredicate::DictContains
                | middleware::NativePredicate::ArrayContains
                | middleware::NativePredicate::SetContains => {
                    *np = middleware::NativePredicate::Contains;
                }
                middleware::NativePredicate::DictNotContains
                | middleware::NativePredicate::SetNotContains => {
                    *np = middleware::NativePredicate::NotContains;
                }
                _ => {}
            }
        }

        Ok(MWStatementTmpl {
            pred: predicate,
            args: mw_args,
        })
    }

    fn lower_statement_arg_frontend(
        &self,
        arg: &StatementArg,
        wildcard_map: &HashMap<String, usize>,
    ) -> Result<MWStatementTmplArg, LoweringError> {
        match arg {
            StatementArg::Literal(lit) => {
                let value = self.lower_literal(lit)?;
                Ok(MWStatementTmplArg::Literal(value))
            }
            StatementArg::Identifier(id) => {
                let index =
                    wildcard_map
                        .get(&id.name)
                        .ok_or_else(|| LoweringError::PredicateNotFound {
                            name: id.name.clone(),
                        })?;
                Ok(MWStatementTmplArg::Wildcard(Wildcard::new(
                    id.name.clone(),
                    *index,
                )))
            }
            StatementArg::AnchoredKey(ak) => {
                let root_index = wildcard_map.get(&ak.root.name).ok_or_else(|| {
                    LoweringError::PredicateNotFound {
                        name: ak.root.name.clone(),
                    }
                })?;
                let wildcard = Wildcard::new(ak.root.name.clone(), *root_index);

                let key = match &ak.key {
                    AnchoredKeyPath::Bracket(s) => middleware::Key::from(s.value.as_str()),
                    AnchoredKeyPath::Dot(id) => middleware::Key::from(id.name.as_str()),
                };

                Ok(MWStatementTmplArg::AnchoredKey(wildcard, key))
            }
        }
    }

    fn lower_literal(&self, lit: &LiteralValue) -> Result<middleware::Value, LoweringError> {
        let value = match lit {
            LiteralValue::Int(i) => middleware::Value::from(i.value),
            LiteralValue::Bool(b) => middleware::Value::from(b.value),
            LiteralValue::String(s) => middleware::Value::from(s.value.clone()),
            LiteralValue::Raw(r) => {
                // Parse hex string to RawValue (little-endian)
                let hex_str = &r.hash.value[2..]; // Skip "0x"
                let raw_value = Self::parse_hex_str_to_raw_value(hex_str)?;
                middleware::Value::from(raw_value)
            }
            LiteralValue::PublicKey(pk) => {
                // Parse base58 to Point
                let point: Point = pk
                    .base58
                    .parse()
                    .map_err(|_| LoweringError::InvalidArgumentType)?;
                middleware::Value::from(point)
            }
            LiteralValue::SecretKey(sk) => {
                // Parse base64 to SecretKey
                let bytes = deserialize_bytes(&sk.base64)
                    .map_err(|_| LoweringError::InvalidArgumentType)?;
                let secret_key = SecretKey::from_bytes(&bytes)
                    .map_err(|_| LoweringError::InvalidArgumentType)?;
                middleware::Value::from(secret_key)
            }
            LiteralValue::Array(a) => {
                let elements: Result<Vec<_>, _> =
                    a.elements.iter().map(|e| self.lower_literal(e)).collect();
                let array = containers::Array::new(self.params.max_depth_mt_containers, elements?)?;
                middleware::Value::from(array)
            }
            LiteralValue::Set(s) => {
                let elements: Result<Vec<_>, _> =
                    s.elements.iter().map(|e| self.lower_literal(e)).collect();
                let set_values: std::collections::HashSet<_> = elements?.into_iter().collect();
                let set = containers::Set::new(self.params.max_depth_mt_containers, set_values)?;
                middleware::Value::from(set)
            }
            LiteralValue::Dict(d) => {
                let pairs: Result<Vec<(middleware::Key, middleware::Value)>, LoweringError> = d
                    .pairs
                    .iter()
                    .map(|pair| {
                        let key = middleware::Key::from(pair.key.value.as_str());
                        let value = self.lower_literal(&pair.value)?;
                        Ok((key, value))
                    })
                    .collect();
                let dict_map: std::collections::HashMap<_, _> = pairs?.into_iter().collect();
                let dict =
                    containers::Dictionary::new(self.params.max_depth_mt_containers, dict_map)?;
                middleware::Value::from(dict)
            }
        };
        Ok(value)
    }

    // Helper: Parse big-endian hex string to little-endian RawValue
    fn parse_hex_str_to_raw_value(hex_str: &str) -> Result<RawValue, LoweringError> {
        RawValue::from_hex(hex_str).map_err(|_err| LoweringError::InvalidArgumentType)
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
        let document = parse_document(parsed.into_iter().next().unwrap());
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
}
