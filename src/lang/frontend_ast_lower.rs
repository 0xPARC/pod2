//! Lowering from frontend AST to middleware structures
//!
//! This module converts validated frontend AST to middleware data structures.
//! Supports automatic predicate splitting.

use std::{
    collections::{HashMap, HashSet},
    str::FromStr,
};

use crate::{
    frontend::{BuilderArg, PredicateOrWildcard, StatementTmplBuilder},
    lang::{
        frontend_ast::*,
        frontend_ast_split,
        frontend_ast_validate::{PredicateKind, SymbolTable, ValidatedAST},
        module, Module,
    },
    middleware::{
        self, containers, CustomPredicateRef, IntroPredicateRef, Key, NativePredicate, Params,
        Predicate, StatementTmpl as MWStatementTmpl, StatementTmplArg as MWStatementTmplArg, Value,
        Wildcard,
    },
};

/// Context for predicate resolution - determines how predicates are resolved
pub enum ResolutionContext<'a> {
    /// Request context: predicates resolve via imports only (no local definitions)
    Request,
    /// Module context: local predicates resolve to BatchSelf
    Module {
        /// Maps predicate name to index within the module
        reference_map: &'a HashMap<String, usize>,
        /// Name of the custom predicate being defined (for wildcard scope lookup)
        custom_predicate_name: &'a str,
    },
}

/// Resolve a predicate reference to a Predicate using the symbol table
pub fn resolve_predicate_ref(
    pred_ref: &PredicateRef,
    symbols: &SymbolTable,
    context: &ResolutionContext,
) -> Option<PredicateOrWildcard> {
    match pred_ref {
        PredicateRef::Qualified { module, predicate } => {
            // Look up the module in the imported_modules
            let imported_module = symbols.imported_modules.get(&module.name)?;
            // Find the predicate index in the module
            let idx = *imported_module.predicate_index.get(&predicate.name)?;
            Some(PredicateOrWildcard::Predicate(Predicate::Custom(
                CustomPredicateRef::new(imported_module.batch.clone(), idx),
            )))
        }
        PredicateRef::Local(id) => resolve_predicate(&id.name, symbols, context),
    }
}

/// Resolve a predicate name to a Predicate using the symbol table
pub fn resolve_predicate(
    pred_name: &str,
    symbols: &SymbolTable,
    context: &ResolutionContext,
) -> Option<PredicateOrWildcard> {
    // 0. Try wildcard first (only in module context where we're defining predicates)
    if let ResolutionContext::Module {
        custom_predicate_name,
        ..
    } = context
    {
        if let Some(wc_scope) = symbols.wildcard_scopes.get(*custom_predicate_name) {
            if wc_scope.wildcards.contains_key(pred_name) {
                return Some(PredicateOrWildcard::Wildcard(pred_name.to_string()));
            }
        }
    }

    // 1. Try native predicate second
    if let Ok(native) = NativePredicate::from_str(pred_name) {
        return Some(PredicateOrWildcard::Predicate(Predicate::Native(native)));
    }

    // 2. Look up in symbol table
    if let Some(info) = symbols.predicates.get(pred_name) {
        let predicate = match &info.kind {
            PredicateKind::Native(np) => Predicate::Native(*np),

            PredicateKind::Custom { .. } => match context {
                ResolutionContext::Request => {
                    // Request files can't define local predicates, so this shouldn't happen
                    return None;
                }
                ResolutionContext::Module { reference_map, .. } => {
                    resolve_local_predicate(pred_name, reference_map)?
                }
            },

            PredicateKind::BatchImported { batch, index } => {
                Predicate::Custom(CustomPredicateRef::new(batch.clone(), *index))
            }

            PredicateKind::ModuleImported {
                module_name,
                predicate_index,
                ..
            } => {
                // Look up the module in the imported_modules
                let module = symbols
                    .imported_modules
                    .get(module_name)
                    .expect("Module should exist if ModuleImported predicate kind exists");
                Predicate::Custom(CustomPredicateRef::new(
                    module.batch.clone(),
                    *predicate_index,
                ))
            }

            PredicateKind::IntroImported {
                name,
                verifier_data_hash,
            } => Predicate::Intro(IntroPredicateRef {
                name: name.clone(),
                args_len: info.public_arity,
                verifier_data_hash: *verifier_data_hash,
            }),
        };
        return Some(PredicateOrWildcard::Predicate(predicate));
    }

    // 3. In module context, also check reference_map for split chain pieces
    //    (predicates created by splitting that aren't in the original symbol table)
    if let ResolutionContext::Module { reference_map, .. } = context {
        if reference_map.contains_key(pred_name) {
            return resolve_local_predicate(pred_name, reference_map)
                .map(PredicateOrWildcard::Predicate);
        }
    }

    None
}

/// Resolve a local predicate (one in this module or a split chain piece) using the reference_map
fn resolve_local_predicate(
    pred_name: &str,
    reference_map: &HashMap<String, usize>,
) -> Option<Predicate> {
    let &idx = reference_map.get(pred_name)?;
    Some(Predicate::BatchSelf(idx))
}

// ============================================================================
// Shared lowering utilities
// ============================================================================
// These functions convert AST types to middleware/builder types and are used
// by both the request lowering (in this module) and predicate batching
// (in module.rs).

/// Lower a literal value from AST to middleware Value.
///
/// This is a pure conversion that cannot fail.
pub fn lower_literal(lit: &LiteralValue) -> Value {
    match lit {
        LiteralValue::Int(i) => Value::from(i.value),
        LiteralValue::Bool(b) => Value::from(b.value),
        LiteralValue::String(s) => Value::from(s.value.clone()),
        LiteralValue::Raw(r) => Value::from(r.hash.hash),
        LiteralValue::PublicKey(pk) => Value::from(pk.point),
        LiteralValue::SecretKey(sk) => Value::from(sk.secret_key.clone()),
        LiteralValue::Array(a) => {
            let elements: Vec<_> = a.elements.iter().map(lower_literal).collect();
            let array = containers::Array::new(elements);
            Value::from(array)
        }
        LiteralValue::Set(s) => {
            let elements: std::collections::HashSet<_> =
                s.elements.iter().map(lower_literal).collect();
            let set = containers::Set::new(elements);
            Value::from(set)
        }
        LiteralValue::Dict(d) => {
            let pairs: HashMap<_, _> = d
                .pairs
                .iter()
                .map(|pair| {
                    let key = Key::from(pair.key.value.as_str());
                    let value = lower_literal(&pair.value);
                    (key, value)
                })
                .collect();
            let dict = containers::Dictionary::new(pairs);
            Value::from(dict)
        }
    }
}

/// Lower a statement argument from AST to BuilderArg.
///
/// This is a pure conversion that cannot fail.
pub fn lower_statement_arg(arg: &StatementTmplArg) -> BuilderArg {
    match arg {
        StatementTmplArg::Literal(lit) => {
            let value = lower_literal(lit);
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
    }
}

pub use crate::lang::error::LoweringError;

/// Lower a validated module AST to a Module
///
/// The validated AST must have been validated in Module mode.
pub fn lower_module(
    validated: ValidatedAST,
    params: &Params,
    module_name: &str,
) -> Result<Module, LoweringError> {
    if !validated.diagnostics().is_empty() {
        return Err(LoweringError::ValidationErrors);
    }

    let lowerer = Lowerer::new(validated, params);
    lowerer.lower_module(module_name)
}

/// Lower a validated request AST to a PodRequest
///
/// The validated AST must have been validated in Request mode.
pub fn lower_request(
    validated: ValidatedAST,
    params: &Params,
) -> Result<crate::frontend::PodRequest, LoweringError> {
    if !validated.diagnostics().is_empty() {
        return Err(LoweringError::ValidationErrors);
    }

    let lowerer = Lowerer::new(validated, params);
    lowerer.lower_request()
}

struct Lowerer<'a> {
    validated: ValidatedAST,
    params: &'a Params,
}

impl<'a> Lowerer<'a> {
    fn new(validated: ValidatedAST, params: &'a Params) -> Self {
        Self { validated, params }
    }

    fn lower_module(self, module_name: &str) -> Result<Module, LoweringError> {
        // Extract and split custom predicates from document
        let custom_predicates = self.extract_and_split_predicates()?;

        // Build the module from split predicates
        let module = module::build_module(
            custom_predicates,
            self.params,
            module_name,
            self.validated.symbols(),
        )?;

        Ok(module)
    }

    fn lower_request(self) -> Result<crate::frontend::PodRequest, LoweringError> {
        let doc = self.validated.document();

        // Find request definition
        let request_def = doc
            .items
            .iter()
            .find_map(|item| match item {
                DocumentItem::RequestDef(req) => Some(req),
                _ => None,
            })
            .expect("Request mode validation ensures REQUEST block exists");

        // Build wildcard map from all wildcards used in the request statements
        let wildcard_map = self.build_request_wildcard_map(request_def);

        // Lower each statement to middleware templates, resolving predicates
        let mut request_templates = Vec::new();
        for stmt in &request_def.statements {
            let mw_stmt = self.lower_request_statement(stmt, &wildcard_map)?;
            request_templates.push(mw_stmt);
        }

        Ok(crate::frontend::PodRequest::new(request_templates))
    }

    fn lower_request_statement(
        &self,
        stmt: &StatementTmpl,
        wildcard_map: &HashMap<String, usize>,
    ) -> Result<MWStatementTmpl, LoweringError> {
        // Enforce argument count limit for request statements
        if stmt.args.len() > Params::max_statement_args() {
            return Err(LoweringError::TooManyStatementArgs {
                count: stmt.args.len(),
                max: Params::max_statement_args(),
            });
        }

        let symbols = self.validated.symbols();

        // Resolve predicate using the unified resolution function
        let context = ResolutionContext::Request;
        let predicate =
            resolve_predicate_ref(&stmt.predicate, symbols, &context).ok_or_else(|| {
                LoweringError::PredicateNotFound {
                    name: stmt.predicate.display_name(),
                }
            })?;

        // Create a builder with the resolved predicate and desugar
        let mut builder = StatementTmplBuilder::new(predicate.clone());
        for arg in &stmt.args {
            let builder_arg = lower_statement_arg(arg);
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
                    let key = Key::from(key_str.as_str());
                    MWStatementTmplArg::AnchoredKey(wildcard, key)
                }
            };
            mw_args.push(mw_arg);
        }

        let predicate = match desugared.pred_or_wc {
            PredicateOrWildcard::Predicate(p) => p,
            PredicateOrWildcard::Wildcard(_) => {
                unreachable!("wildcard predicates aren't considered in requests")
            }
        };
        Ok(MWStatementTmpl {
            pred_or_wc: middleware::PredicateOrWildcard::Predicate(predicate),
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
    ) -> Result<Vec<frontend_ast_split::SplitResult>, LoweringError> {
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
        let mut split_results = Vec::new();
        for pred in predicates {
            let result = frontend_ast_split::split_predicate_if_needed(pred, self.params)?;
            split_results.push(result);
        }

        Ok(split_results)
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use super::*;
    use crate::lang::{
        frontend_ast::parse::parse_document,
        frontend_ast_validate::{validate, ParseMode},
        parser::parse_podlang,
    };

    fn parse_validate_and_lower_module(
        input: &str,
        params: &Params,
    ) -> Result<Module, LoweringError> {
        let parsed = parse_podlang(input).expect("Failed to parse");
        let document = parse_document(parsed.into_iter().next().unwrap()).expect("Failed to parse");
        let validated =
            validate(document, &HashMap::new(), ParseMode::Module).expect("Failed to validate");
        lower_module(validated, params, "test_batch")
    }

    #[test]
    fn test_simple_predicate() {
        let input = r#"
            my_pred(A, B) = AND (
                Equal(A["foo"], B["bar"])
            )
        "#;

        let params = Params::default();
        let result = parse_validate_and_lower_module(input, &params);
        if let Err(e) = &result {
            eprintln!("Error: {:?}", e);
        }
        assert!(result.is_ok());

        let module = result.unwrap();
        assert_eq!(module.batch.predicates().len(), 1);

        let pred = &module.batch.predicates()[0];
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
        let result = parse_validate_and_lower_module(input, &params);
        assert!(result.is_ok());

        let module = result.unwrap();
        let pred = &module.batch.predicates()[0];
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
        let result = parse_validate_and_lower_module(input, &params);
        assert!(result.is_ok());

        let module = result.unwrap();
        let pred = &module.batch.predicates()[0];
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
        let result = parse_validate_and_lower_module(input, &params);
        if let Err(e) = &result {
            eprintln!("Splitting error: {:?}", e);
        }
        assert!(result.is_ok());

        let module = result.unwrap();
        // Should be automatically split into 2 predicates (my_pred and my_pred_1)
        assert_eq!(module.batch.predicates().len(), 2);

        // With topological sorting, my_pred_1 comes first (since my_pred depends on it)
        // my_pred_1 has 2 statements
        // my_pred has 5 statements (4 + chain call)
        // Just verify we have the right total statement counts
        let total_statements: usize = module
            .batch
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
        let result = parse_validate_and_lower_module(input, &params);
        assert!(result.is_ok());

        let module = result.unwrap();
        assert_eq!(module.batch.predicates().len(), 2);
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
        let result = parse_validate_and_lower_module(input, &params);
        assert!(result.is_ok());

        let module = result.unwrap();
        let pred2 = &module.batch.predicates()[1];
        let stmt = &pred2.statements()[0];

        // Should be BatchSelf(0) referring to pred1
        assert!(matches!(
            stmt.pred_or_wc,
            middleware::PredicateOrWildcard::Predicate(Predicate::BatchSelf(0))
        ));
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
        let result = parse_validate_and_lower_module(input, &params);
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
        let result = parse_validate_and_lower_module(input, &params);
        assert!(result.is_ok());

        let module = result.unwrap();
        let pred = &module.batch.predicates()[0];
        let stmt = &pred.statements()[0];

        // Should desugar to the Contains predicate
        assert!(matches!(
            stmt.pred_or_wc,
            middleware::PredicateOrWildcard::Predicate(Predicate::Native(
                NativePredicate::Contains
            ))
        ));
    }

    #[test]
    fn test_wc_pred() {
        let input = r#"
            my_pred(X, DynPred) = AND (
                Equal(X["pred"], DynPred)
                DynPred(X)
            )
        "#;

        let params = Params::default();
        let result = parse_validate_and_lower_module(input, &params);
        assert!(result.is_ok());
    }

    #[test]
    fn test_intro_predicate_in_custom_predicate() {
        use hex::ToHex;

        use crate::middleware::EMPTY_HASH;

        // Import an intro predicate and use it inside a custom predicate definition
        let intro_hash = EMPTY_HASH.encode_hex::<String>();
        let input = format!(
            r#"
            use intro external_check(X) from 0x{intro_hash}

            my_pred(A) = AND (
                Equal(A["foo"], 42)
                external_check(A)
            )
        "#
        );

        let params = Params::default();

        // Parse, validate, and lower
        let parsed = parse_podlang(&input).expect("Failed to parse");
        let document =
            parse_document(parsed.into_iter().next().unwrap()).expect("Failed to parse document");
        let validated =
            validate(document, &HashMap::new(), ParseMode::Module).expect("Failed to validate");
        let result = lower_module(validated, &params, "test_batch");

        assert!(result.is_ok(), "Lowering failed: {:?}", result.err());

        let module = result.unwrap();

        // Should have one custom predicate
        assert_eq!(module.batch.predicates().len(), 1);

        let pred = &module.batch.predicates()[0];
        assert_eq!(pred.name, "my_pred");
        // 2 statements: Equal and external_check
        assert_eq!(pred.statements().len(), 2);

        // Verify the second statement is an intro predicate reference
        let intro_stmt = &pred.statements()[1];
        match intro_stmt.pred_or_wc() {
            middleware::PredicateOrWildcard::Predicate(Predicate::Intro(intro_ref)) => {
                assert_eq!(intro_ref.name, "external_check");
                assert_eq!(intro_ref.args_len, 1);
                assert_eq!(intro_ref.verifier_data_hash, EMPTY_HASH);
            }
            other => panic!("Expected Intro predicate, got {:?}", other),
        }
    }
}
