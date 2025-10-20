//! Lowering from frontend AST to middleware structures
//!
//! This module converts validated frontend AST to middleware data structures.
//! Currently implements basic 1:1 conversion without automatic predicate splitting.

use std::{collections::HashMap, sync::Arc};

use hex::FromHex;

#[cfg(test)]
use crate::middleware::NativePredicate;
use crate::{
    backends::plonky2::{deserialize_bytes, primitives::ec::curve::Point},
    lang::{
        frontend_ast::*,
        frontend_ast_split,
        frontend_ast_validate::{PredicateKind, ValidatedAST},
        processor::native_predicate_from_string,
    },
    middleware::{
        self, containers, CustomPredicate, CustomPredicateBatch, IntroPredicateRef, Params,
        Predicate, RawValue, SecretKey, StatementTmpl as MWStatementTmpl,
        StatementTmplArg as MWStatementTmplArg, Wildcard,
    },
};

/// Result of lowering: a batch of custom predicates
#[derive(Debug, Clone)]
pub struct LoweredBatch {
    pub name: String,
    pub batch: Arc<CustomPredicateBatch>,
}

/// Errors that can occur during lowering
#[derive(Debug, thiserror::Error)]
pub enum LoweringError {
    #[error("Too many custom predicates: {count} exceeds limit of {max} (batch: {batch_name})")]
    TooManyPredicates {
        batch_name: String,
        count: usize,
        max: usize,
    },

    #[error("Too many statements in predicate '{predicate}': {count} exceeds limit of {max}")]
    TooManyStatements {
        predicate: String,
        count: usize,
        max: usize,
    },

    #[error("Too many wildcards in predicate '{predicate}': {count} exceeds limit of {max}")]
    TooManyWildcards {
        predicate: String,
        count: usize,
        max: usize,
    },

    #[error("Too many arguments in statement template: {count} exceeds limit of {max}")]
    TooManyStatementArgs { count: usize, max: usize },

    #[error("Predicate '{name}' not found in symbol table")]
    PredicateNotFound { name: String },

    #[error("Invalid argument type in statement template")]
    InvalidArgumentType,

    #[error("Middleware error: {0}")]
    Middleware(#[from] middleware::Error),

    #[error("Splitting error: {0}")]
    Splitting(#[from] frontend_ast_split::SplittingError),

    #[error("Cannot lower document with validation errors")]
    ValidationErrors,

    #[error("No custom predicates to lower")]
    NoCustomPredicates,
}

/// Lower a validated AST to middleware structures
pub fn lower(
    validated: ValidatedAST,
    params: &Params,
    batch_name: String,
) -> Result<LoweredBatch, LoweringError> {
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

    fn lower(mut self, batch_name: String) -> Result<LoweredBatch, LoweringError> {
        // Extract and split custom predicates from document
        let custom_predicates = self.extract_and_split_predicates()?;

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

        Ok(LoweredBatch {
            name: batch_name,
            batch,
        })
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

        if predicates.is_empty() {
            return Err(LoweringError::NoCustomPredicates);
        }

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

        // Note: Constraint checking is now handled by the splitting phase
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
        let predicate = if let Some(native) = native_predicate_from_string(pred_name) {
            // Syntactic sugar predicates are allowed - desugaring is a separate step
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
    ) -> Result<LoweredBatch, LoweringError> {
        let parsed = parse_podlang(input).expect("Failed to parse");
        let document = parse_document(parsed.into_iter().next().unwrap());
        let validated = validate(document, &[]).expect("Failed to validate");
        lower(validated, params, "test_batch".to_string())
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
        assert_eq!(lowered.batch.predicates().len(), 1);

        let pred = &lowered.batch.predicates()[0];
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
        let pred = &lowered.batch.predicates()[0];
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
        let pred = &lowered.batch.predicates()[0];
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
        assert_eq!(lowered.batch.predicates().len(), 2);

        // First predicate should have 5 statements (4 + chain call)
        assert_eq!(lowered.batch.predicates()[0].statements().len(), 5);

        // Second predicate should have 2 statements
        assert_eq!(lowered.batch.predicates()[1].statements().len(), 2);
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
        assert_eq!(lowered.batch.predicates().len(), 2);
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
        let pred2 = &lowered.batch.predicates()[1];
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
    fn test_syntactic_sugar_allowed() {
        let input = r#"
            my_pred(D) = AND (
                DictContains(D, "key", "value")
            )
        "#;

        let params = Params::default();
        let result = parse_validate_and_lower(input, &params);
        // Syntactic sugar is now allowed - desugaring is a separate step
        assert!(result.is_ok());

        let lowered = result.unwrap();
        let pred = &lowered.batch.predicates()[0];
        let stmt = &pred.statements()[0];

        // Should preserve the DictContains predicate
        assert!(matches!(
            stmt.pred,
            Predicate::Native(NativePredicate::DictContains)
        ));
    }
}
