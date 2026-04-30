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
        frontend_ast_validate::{PredicateKind, RecordSource, SymbolTable, ValidatedAST},
        module, Module,
    },
    middleware::{
        self, containers, db::mem::MemDB, CustomPredicateRef, IntroPredicateRef, Key,
        NativePredicate, Params, Predicate, StatementTmpl as MWStatementTmpl,
        StatementTmplArg as MWStatementTmplArg, StrKey, Value, Wildcard,
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
                    // Requests can't define local predicates, so this shouldn't happen
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
/// This is a pure conversion that cannot fail for context-free literals.
/// Panics on `ExternalPredicateHash`, `Record`, and `RecordEntryIndex` —
/// use `lower_literal_with_context` when any of those may appear (records
/// and entry indices need the symbol table to resolve the record schema;
/// external predicate hashes need the imported-module table).
pub(crate) fn lower_literal(lit: &LiteralValue) -> Value {
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
                    let key = StrKey::from(pair.key.value.as_str());
                    let value = lower_literal(&pair.value);
                    (key, value)
                })
                .collect();
            let dict = containers::Dictionary::new(pairs);
            Value::from(dict)
        }
        LiteralValue::Record(_) => {
            unreachable!(
                "Record literals must be lowered with context via lower_literal_with_context"
            )
        }
        LiteralValue::NativePredicateHash(id) => {
            let np = NativePredicate::from_str(&id.name).expect("validated native predicate");
            Value::from(Predicate::Native(np).hash())
        }
        LiteralValue::ExternalPredicateHash { .. } => {
            unreachable!(
                "ExternalPredicateHash must be lowered with context via lower_literal_with_context"
            )
        }
        LiteralValue::RecordEntryIndex { .. } => {
            unreachable!(
                "RecordEntryIndex must be lowered with context via lower_literal_with_context"
            )
        }
    }
}

/// Lower a literal value, resolving external predicate references using the symbol table.
pub fn lower_literal_with_context(
    lit: &LiteralValue,
    symbols: &SymbolTable,
    context: &ResolutionContext,
) -> Result<Value, LoweringError> {
    match lit {
        LiteralValue::ExternalPredicateHash { module, predicate } => {
            let pred_or_wc = resolve_predicate_ref(
                &PredicateRef::Qualified {
                    module: module.clone(),
                    predicate: predicate.clone(),
                },
                symbols,
                context,
            )
            .ok_or_else(|| LoweringError::PredicateNotFound {
                name: format!("{}::{}", module.name, predicate.name),
            })?;
            let pred = match pred_or_wc {
                crate::frontend::PredicateOrWildcard::Predicate(p) => p,
                _ => unreachable!(
                    "`resolve_predicate_ref` always returns `PredicateOrWildcard::Predicate` on `PredicateRef::Qualified`"
                )
            };
            Ok(Value::from(pred.hash()))
        }
        LiteralValue::Array(a) => {
            let elements: Vec<_> = a
                .elements
                .iter()
                .map(|e| lower_literal_with_context(e, symbols, context))
                .collect::<Result<_, _>>()?;
            Ok(Value::from(containers::Array::new(elements)))
        }
        LiteralValue::Set(s) => {
            let elements: std::collections::HashSet<_> = s
                .elements
                .iter()
                .map(|e| lower_literal_with_context(e, symbols, context))
                .collect::<Result<_, _>>()?;
            Ok(Value::from(containers::Set::new(elements)))
        }
        LiteralValue::Dict(d) => {
            let pairs: HashMap<_, _> = d
                .pairs
                .iter()
                .map(|pair| {
                    let key = StrKey::from(pair.key.value.as_str());
                    let value = lower_literal_with_context(&pair.value, symbols, context)?;
                    Ok((key, value))
                })
                .collect::<Result<_, LoweringError>>()?;
            Ok(Value::from(containers::Dictionary::new(pairs)))
        }
        LiteralValue::Record(r) => {
            // The schema fixes each entry's index, so source order doesn't
            // affect the merkle root and missing entries stay missing.
            let schema = symbols
                .records
                .get(&r.name.symbol_table_key())
                .expect("record schema validated");
            let mut arr = containers::Array::empty_with_db(Box::new(MemDB::new()));
            for entry_lit in &r.entries {
                let idx = schema.entry_index[&entry_lit.name.name];
                let value = lower_literal_with_context(&entry_lit.value, symbols, context)?;
                arr.insert(idx, value)?;
            }
            Ok(Value::from(arr))
        }
        LiteralValue::RecordEntryIndex { record, entry } => {
            let schema = symbols
                .records
                .get(&record.symbol_table_key())
                .expect("record schema validated");
            let idx = schema.entry_index[&entry.name];
            Ok(Value::from(idx as i64))
        }
        // All other variants are context-free
        other => Ok(lower_literal(other)),
    }
}

/// Lower a statement argument from AST to BuilderArg.
///
/// Context-free for most arg types. Panics on ExternalPredicateHash inside literals —
/// use `lower_statement_arg_with_context` when external predicate references may appear.
pub(crate) fn lower_statement_arg(arg: &StatementTmplArg) -> BuilderArg {
    match arg {
        StatementTmplArg::Literal(lit) => {
            let value = lower_literal(lit);
            BuilderArg::Literal(value)
        }
        StatementTmplArg::Wildcard(id) => BuilderArg::WildcardLiteral(id.name.clone()),
        StatementTmplArg::AnchoredKey(ak) => {
            let key = match &ak.key {
                AnchoredKeyPath::Bracket(s) => Key::new(s.value.clone()),
                AnchoredKeyPath::Dot(id) => Key::new(id.name.clone()),
                AnchoredKeyPath::Index(i) => Key::from(*i),
            };
            BuilderArg::Key(ak.root.name.clone(), key)
        }
        StatementTmplArg::SelfPredicateHash(id) => BuilderArg::SelfPredicateHash(id.name.clone()),
    }
}

/// Lower a statement argument, resolving external predicate references using the symbol table.
pub fn lower_statement_arg_with_context(
    arg: &StatementTmplArg,
    symbols: &SymbolTable,
    context: &ResolutionContext,
) -> Result<BuilderArg, LoweringError> {
    match arg {
        StatementTmplArg::Literal(lit) => {
            let value = lower_literal_with_context(lit, symbols, context)?;
            Ok(BuilderArg::Literal(value))
        }
        StatementTmplArg::SelfPredicateHash(id) => {
            Ok(BuilderArg::SelfPredicateHash(id.name.clone()))
        }
        other => Ok(lower_statement_arg(other)),
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
        let local_records = self.collect_local_records();

        // Build the module from split predicates
        let module = module::build_module(
            custom_predicates,
            self.params,
            module_name,
            self.validated.symbols(),
            local_records,
        )?;

        Ok(module)
    }

    /// Collect record declarations from this module's source. No transitive
    /// re-export — imported records aren't included.
    fn collect_local_records(&self) -> HashMap<String, Vec<String>> {
        self.validated
            .symbols()
            .records
            .iter()
            .filter(|(_, schema)| matches!(schema.source, RecordSource::Local))
            .map(|(name, schema)| (name.clone(), schema.entries.clone()))
            .collect()
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
                    name: format!("{}", stmt.predicate),
                }
            })?;

        // Create a builder with the resolved predicate and desugar
        let mut builder = StatementTmplBuilder::new(predicate.clone());
        for arg in &stmt.args {
            let builder_arg = lower_statement_arg_with_context(arg, symbols, &context)?;
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
                BuilderArg::Key(root_name, key) => {
                    let root_index = wildcard_map
                        .get(&root_name)
                        .expect("Root wildcard not found");
                    let wildcard = Wildcard::new(root_name, *root_index);
                    MWStatementTmplArg::AnchoredKey(wildcard, key)
                }
                BuilderArg::SelfPredicateHash(_) => {
                    unreachable!("SelfPredicateHash should not appear in request lowering")
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
        for name in stmt.wildcard_names() {
            if seen.insert(name.to_string()) {
                names.push(name.to_string());
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

        // Apply splitting to each predicate as needed. The typed-key rewrite
        // happens before splitting so split chain pieces inherit `Index` keys
        // unchanged.
        let mut split_results = Vec::new();
        for mut pred in predicates {
            self.rewrite_typed_dot_access(&mut pred);
            let result = frontend_ast_split::split_predicate_if_needed(pred, self.params)?;
            split_results.push(result);
        }

        Ok(split_results)
    }

    /// Rewrite `r.foo` to `r[i]` when `r` is a typed wildcard, using the
    /// record schema's entry-index map. Untyped wildcards keep
    /// `Dot`/`Bracket` keys unchanged (POD-string-key semantics).
    fn rewrite_typed_dot_access(&self, pred: &mut CustomPredicateDef) {
        let symbols = self.validated.symbols();
        let scope = symbols
            .wildcard_scopes
            .get(&pred.name.name)
            .expect("wildcard scope exists for every custom predicate after validation");
        // Skip the per-arg walk for predicates with no typed wildcards —
        // the common case before records see widespread use.
        if !scope.wildcards.values().any(|wc| wc.record_type.is_some()) {
            return;
        }
        for stmt in &mut pred.statements {
            for arg in &mut stmt.args {
                let StatementTmplArg::AnchoredKey(ak) = arg else {
                    continue;
                };
                let Some(wc_info) = scope.wildcards.get(&ak.root.name) else {
                    continue;
                };
                let Some(record_name) = &wc_info.record_type else {
                    continue;
                };
                let AnchoredKeyPath::Dot(entry) = &ak.key else {
                    continue;
                };
                let schema = symbols
                    .records
                    .get(record_name)
                    .expect("record_type was resolved at predicate-def time");
                let idx = schema.entry_index[&entry.name];
                ak.key = AnchoredKeyPath::Index(idx as i64);
            }
        }
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
        let validated = validate(document, &HashMap::new(), params, ParseMode::Module)
            .expect("Failed to validate");
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
        let validated = validate(document, &HashMap::new(), &params, ParseMode::Module)
            .expect("Failed to validate");
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

    // ---- Records: predicate-side dot-access lowering -----------------------

    /// Pull the single `Key` out of statement N, arg N of the first predicate.
    fn anchored_key_at(
        module: &Module,
        pred_idx: usize,
        stmt_idx: usize,
        arg_idx: usize,
    ) -> middleware::Key {
        let pred = &module.batch.predicates()[pred_idx];
        let stmt = &pred.statements()[stmt_idx];
        match &stmt.args()[arg_idx] {
            middleware::StatementTmplArg::AnchoredKey(_, k) => k.clone(),
            other => panic!("expected AnchoredKey at arg {arg_idx}, got {other:?}"),
        }
    }

    fn anchored_index_at(module: &Module, pred_idx: usize, stmt_idx: usize, arg_idx: usize) -> i64 {
        anchored_key_at(module, pred_idx, stmt_idx, arg_idx)
            .as_index()
            .expect("expected Index key")
            .value()
    }

    #[test]
    fn test_typed_dot_lowers_to_index_key() {
        // Single entry on a typed wildcard becomes an integer-keyed
        // AnchoredKey at the schema's entry index.
        let input = r#"
            record R = (foo, bar, baz)
            my_pred(in R) = AND(Equal(in.bar, 0))
        "#;
        let module = parse_validate_and_lower_module(input, &Params::default()).unwrap();
        assert_eq!(anchored_index_at(&module, 0, 0, 0), 1);
    }

    #[test]
    fn test_dot_on_untyped_wildcard_stays_str_key() {
        // No type tag, no schema lookup: dot-access keeps POD-string-key
        // semantics.
        let input = r#"
            my_pred(r) = AND(Equal(r.foo, 1))
        "#;
        let module = parse_validate_and_lower_module(input, &Params::default()).unwrap();
        match anchored_key_at(&module, 0, 0, 0) {
            middleware::Key::Str(sk) => assert_eq!(sk.name(), "foo"),
            other => panic!("expected Str key, got {other:?}"),
        }
    }

    #[test]
    fn test_typed_dot_multiple_entries_distinct_indices() {
        let input = r#"
            record R = (foo, bar, baz)
            my_pred(in R) = AND(
                Equal(in.foo, in.baz)
                Equal(in.bar, 0)
            )
        "#;
        let module = parse_validate_and_lower_module(input, &Params::default()).unwrap();
        assert_eq!(anchored_index_at(&module, 0, 0, 0), 0);
        assert_eq!(anchored_index_at(&module, 0, 0, 1), 2);
        assert_eq!(anchored_index_at(&module, 0, 1, 0), 1);
    }

    #[test]
    fn test_typed_dot_in_or_predicate() {
        // OR predicates: the lowering produces a single AnchoredKey per
        // statement, no cross-statement coupling, so OR works the same as AND.
        let input = r#"
            record R = (foo, bar)
            my_pred(in R) = OR(
                Equal(in.foo, 1)
                Equal(in.bar, 2)
            )
        "#;
        let module = parse_validate_and_lower_module(input, &Params::default()).unwrap();
        assert!(module.batch.predicates()[0].is_disjunction());
        assert_eq!(anchored_index_at(&module, 0, 0, 0), 0);
        assert_eq!(anchored_index_at(&module, 0, 1, 0), 1);
    }

    #[test]
    fn test_record_predicate_hash_matches_handwritten_index_form() {
        // Source-level records are syntactic sugar: the predicate hash for
        // `record R = (foo, bar); p(in R) = AND(Equal(in.bar, 7))` must equal
        // the hash of the same predicate built directly with an integer-keyed
        // anchored key. There is no Podlang surface syntax for `in[1]`, so we
        // build the reference batch via the builder API.
        use crate::{
            frontend::{CustomPredicateBatchBuilder, StatementTmplBuilder},
            middleware::NativePredicate,
        };

        let with_record = r#"
            record R = (foo, bar)
            p(in R) = AND(Equal(in.bar, 7))
        "#;
        let params = Params::default();
        let m_record = parse_validate_and_lower_module(with_record, &params).unwrap();

        let mut b = CustomPredicateBatchBuilder::new(params.clone(), "test_batch".into());
        let stb = StatementTmplBuilder::new_from_pred(NativePredicate::Equal)
            .arg(BuilderArg::Key("in".into(), Key::from(1i64)))
            .arg(BuilderArg::Literal(Value::from(7i64)));
        b.predicate_and("p", &["in"], &[], &[stb]).unwrap();
        let plain_batch = b.finish().unwrap();

        assert_eq!(m_record.batch.id(), plain_batch.id());
    }

    // ---- Records: literal lowering -----------------------------------------

    fn lower_literal_in_pred(input: &str) -> Value {
        let module = parse_validate_and_lower_module(input, &Params::default()).unwrap();
        let pred = &module.batch.predicates()[0];
        let stmt = &pred.statements()[0];
        match &stmt.args()[1] {
            middleware::StatementTmplArg::Literal(v) => v.clone(),
            other => panic!("expected Literal at arg 1, got {other:?}"),
        }
    }

    #[test]
    fn test_record_literal_full_matches_array_root() {
        // A fully populated literal must hash identically to the same values
        // packed into an `Array::new(...)` (which inserts at indices 0..n in
        // order).
        let input = r#"
            record R = (foo, bar, baz)
            my_pred(A) = AND(Equal(A["x"], R(foo: 1, bar: 2, baz: 3)))
        "#;
        let v = lower_literal_in_pred(input);
        let expected = Value::from(containers::Array::new(vec![
            Value::from(1i64),
            Value::from(2i64),
            Value::from(3i64),
        ]));
        assert_eq!(v.raw(), expected.raw());
    }

    #[test]
    fn test_record_literal_entry_order_doesnt_matter() {
        // Schema fixes the index, so source order never affects the root.
        let input_a = r#"
            record R = (foo, bar)
            my_pred(A) = AND(Equal(A["x"], R(foo: 1, bar: 2)))
        "#;
        let input_b = r#"
            record R = (foo, bar)
            my_pred(A) = AND(Equal(A["x"], R(bar: 2, foo: 1)))
        "#;
        assert_eq!(
            lower_literal_in_pred(input_a).raw(),
            lower_literal_in_pred(input_b).raw()
        );
    }

    #[test]
    fn test_record_literal_sparse_stays_sparse() {
        // Missing entries stay missing (no zero-fill). Compare against an
        // explicit sparse Array built the same way.
        let input = r#"
            record R = (foo, bar, baz)
            my_pred(A) = AND(Equal(A["x"], R(bar: 42)))
        "#;
        let v = lower_literal_in_pred(input);

        let mut sparse = containers::Array::empty_with_db(Box::new(MemDB::new()));
        sparse.insert(1, Value::from(42i64)).unwrap();
        let expected = Value::from(sparse);

        assert_eq!(v.raw(), expected.raw());
    }

    #[test]
    fn test_record_literal_nested_record_value() {
        // A record literal whose entry value is itself a record literal.
        // The outer literal commits to whatever root the inner produces.
        let input = r#"
            record Inner = (x, y)
            record Outer = (inner)
            my_pred(A) = AND(Equal(A["x"], Outer(inner: Inner(x: 1, y: 2))))
        "#;
        let v = lower_literal_in_pred(input);

        let inner = Value::from(containers::Array::new(vec![
            Value::from(1i64),
            Value::from(2i64),
        ]));
        let expected = Value::from(containers::Array::new(vec![inner]));

        assert_eq!(v.raw(), expected.raw());
    }

    #[test]
    fn test_typed_dot_survives_predicate_splitting() {
        // The rewrite runs before splitting, so chain pieces inherit
        // `Index` keys unchanged. Force a split by exceeding the
        // per-predicate statement cap.
        let input = r#"
            record R = (a, b, c, d, e, f)
            my_pred(in R) = AND(
                Equal(in.a, 1)
                Equal(in.b, 2)
                Equal(in.c, 3)
                Equal(in.d, 4)
                Equal(in.e, 5)
                Equal(in.f, 6)
            )
        "#;
        let module = parse_validate_and_lower_module(input, &Params::default()).unwrap();
        // Splitter ran (max_custom_predicate_arity = 5).
        assert!(module.batch.predicates().len() > 1);
        // Every AnchoredKey across all chain pieces is integer-keyed.
        for pred in module.batch.predicates() {
            for stmt in pred.statements() {
                for arg in stmt.args() {
                    if let middleware::StatementTmplArg::AnchoredKey(_, k) = arg {
                        assert!(
                            matches!(k, middleware::Key::Index(_)),
                            "expected Index key in split chain piece, got {k:?}"
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn test_record_entry_index_lowers_to_integer() {
        // `R::bar` resolves to integer 1 (bar is the second entry of R).
        let input = r#"
            record R = (foo, bar, baz)
            my_pred(A) = AND(Contains(A, R::bar, 7))
        "#;
        let module = parse_validate_and_lower_module(input, &Params::default()).unwrap();
        let pred = &module.batch.predicates()[0];
        let stmt = &pred.statements()[0];
        match &stmt.args()[1] {
            middleware::StatementTmplArg::Literal(v) => {
                assert_eq!(v.raw(), Value::from(1i64).raw());
            }
            other => panic!("expected Literal at arg 1, got {other:?}"),
        }
    }
}
