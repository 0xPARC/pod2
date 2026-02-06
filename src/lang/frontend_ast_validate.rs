//! Validation for the frontend AST
//!
//! This module provides semantic validation for parsed AST documents,
//! including name resolution, arity checking, and wildcard validation.

use std::{
    collections::{HashMap, HashSet},
    str::FromStr,
    sync::Arc,
};

use crate::{
    lang::{frontend_ast::*, Module},
    middleware::{CustomPredicateBatch, Hash, NativePredicate},
};

/// A validated AST document with symbol table and diagnostics
#[derive(Debug, Clone)]
pub struct ValidatedAST {
    document: Document,
    symbols: SymbolTable,
    diagnostics: Vec<Diagnostic>,
}

impl ValidatedAST {
    pub fn document(&self) -> &Document {
        &self.document
    }

    pub fn symbols(&self) -> &SymbolTable {
        &self.symbols
    }

    pub fn diagnostics(&self) -> &[Diagnostic] {
        &self.diagnostics
    }

    pub fn into_document(self) -> Document {
        self.document
    }
}

/// Symbol table containing all predicates and their metadata
#[derive(Debug, Clone)]
pub struct SymbolTable {
    /// All predicates available in this scope
    pub predicates: HashMap<String, PredicateInfo>,
    /// Wildcard scopes for each custom predicate
    pub wildcard_scopes: HashMap<String, WildcardScope>,
    /// Imported modules (bound name → Module reference)
    pub imported_modules: HashMap<String, Arc<Module>>,
}

/// Information about a predicate
#[derive(Debug, Clone)]
pub struct PredicateInfo {
    pub kind: PredicateKind,
    pub arity: usize,
    pub public_arity: usize,
    pub source_span: Option<Span>,
}

/// Kind of predicate
#[derive(Debug, Clone)]
pub enum PredicateKind {
    Native(NativePredicate),
    Custom {
        index: usize,
    },
    BatchImported {
        batch: Arc<CustomPredicateBatch>,
        index: usize,
    },
    ModuleImported {
        module_name: String,
        predicate_name: String,
        predicate_index: usize,
    },
    IntroImported {
        name: String,
        verifier_data_hash: Hash,
    },
}

/// Wildcard scope for a custom predicate
#[derive(Debug, Clone)]
pub struct WildcardScope {
    pub wildcards: HashMap<String, WildcardInfo>,
}

/// Information about a wildcard
#[derive(Debug, Clone)]
pub struct WildcardInfo {
    pub index: usize,
    pub is_public: bool,
    pub source_span: Option<Span>,
}

/// Diagnostic message (warning or info)
#[derive(Debug, Clone)]
pub struct Diagnostic {
    pub level: DiagnosticLevel,
    pub message: String,
    pub span: Option<Span>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DiagnosticLevel {
    Warning,
    Info,
}

pub use crate::lang::error::ValidationError;

/// Mode for parsing/validation - determines what constructs are allowed
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ParseMode {
    /// Module mode: predicate definitions allowed, REQUEST block not allowed
    Module,
    /// Request mode: REQUEST block required, predicate definitions not allowed
    Request,
}

/// Validate an AST document in the given mode
pub fn validate(
    document: Document,
    available_modules: &HashMap<String, Arc<Module>>,
    mode: ParseMode,
) -> Result<ValidatedAST, ValidationError> {
    let validator = Validator::new(available_modules, mode);
    validator.validate(document)
}

struct Validator {
    available_modules: HashMap<String, Arc<Module>>,
    symbols: SymbolTable,
    diagnostics: Vec<Diagnostic>,
    custom_predicate_count: usize,
    mode: ParseMode,
}

impl Validator {
    fn new(available_modules: &HashMap<String, Arc<Module>>, mode: ParseMode) -> Self {
        Self {
            available_modules: available_modules.clone(),
            symbols: SymbolTable {
                predicates: HashMap::new(),
                wildcard_scopes: HashMap::new(),
                imported_modules: HashMap::new(),
            },
            diagnostics: Vec::new(),
            custom_predicate_count: 0,
            mode,
        }
    }

    fn validate(mut self, document: Document) -> Result<ValidatedAST, ValidationError> {
        // Pass 1: Build symbol table
        self.build_symbol_table(&document)?;

        // Pass 2: Validate all references
        self.validate_references(&document)?;

        Ok(ValidatedAST {
            document,
            symbols: self.symbols,
            diagnostics: self.diagnostics,
        })
    }

    fn build_symbol_table(&mut self, document: &Document) -> Result<(), ValidationError> {
        // First process imports
        for item in &document.items {
            if let DocumentItem::UseModuleStatement(use_stmt) = item {
                self.process_use_module_statement(use_stmt)?;
            }
            if let DocumentItem::UseIntroStatement(use_stmt) = item {
                self.process_use_intro_statement(use_stmt)?;
            }
        }

        // Check mode constraints for predicate definitions
        let mut has_predicates = false;
        for item in &document.items {
            if let DocumentItem::CustomPredicateDef(pred_def) = item {
                if self.mode == ParseMode::Request {
                    return Err(ValidationError::PredicatesNotAllowedInRequest {
                        span: pred_def.span,
                    });
                }
                has_predicates = true;
                self.process_custom_predicate_def(pred_def)?;
            }
        }

        // Check mode constraints for REQUEST blocks
        let mut has_request = false;
        let mut first_request_span = None;
        for item in &document.items {
            if let DocumentItem::RequestDef(req) = item {
                if self.mode == ParseMode::Module {
                    return Err(ValidationError::RequestNotAllowedInModule { span: req.span });
                }
                if let Some(first_span) = first_request_span {
                    return Err(ValidationError::MultipleRequestDefinitions {
                        first_span: Some(first_span),
                        second_span: req.span,
                    });
                }
                first_request_span = req.span;
                has_request = true;
            }
        }

        // Enforce that modules have predicates and requests have a REQUEST block
        match self.mode {
            ParseMode::Module if !has_predicates => {
                return Err(ValidationError::NoPredicatesInModule);
            }
            ParseMode::Request if !has_request => {
                return Err(ValidationError::NoRequestBlock);
            }
            _ => {}
        }

        Ok(())
    }

    fn process_use_module_statement(
        &mut self,
        use_stmt: &UseModuleStatement,
    ) -> Result<(), ValidationError> {
        let module_name = &use_stmt.name.name;

        // Check if the module is available
        let module = self.available_modules.get(module_name).ok_or_else(|| {
            ValidationError::ModuleNotFound {
                name: module_name.clone(),
                span: use_stmt.span,
            }
        })?;

        // Store the module for later qualified name resolution
        self.symbols
            .imported_modules
            .insert(module_name.clone(), module.clone());

        Ok(())
    }

    fn process_use_intro_statement(
        &mut self,
        use_stmt: &UseIntroStatement,
    ) -> Result<(), ValidationError> {
        let intro_name = &use_stmt.name.name;
        let args = &use_stmt.args;
        let intro_predicate_ref = &use_stmt.intro_hash;

        if self.symbols.predicates.contains_key(intro_name) {
            return Err(ValidationError::DuplicateImport {
                name: intro_name.clone(),
                span: use_stmt.span,
            });
        }

        self.symbols.predicates.insert(
            intro_name.clone(),
            PredicateInfo {
                kind: PredicateKind::IntroImported {
                    name: intro_name.clone(),
                    // Hash is already parsed in the AST
                    verifier_data_hash: intro_predicate_ref.hash,
                },
                arity: args.len(),
                public_arity: args.len(),
                source_span: use_stmt.span,
            },
        );
        Ok(())
    }

    fn process_custom_predicate_def(
        &mut self,
        pred_def: &CustomPredicateDef,
    ) -> Result<(), ValidationError> {
        let name = &pred_def.name.name;

        if self.symbols.predicates.contains_key(name) {
            let first_span = self.symbols.predicates[name].source_span;
            return Err(ValidationError::DuplicatePredicate {
                name: name.clone(),
                first_span,
                second_span: pred_def.name.span,
            });
        }

        // Check for empty statement list
        if pred_def.statements.is_empty() {
            return Err(ValidationError::EmptyStatementList {
                context: format!("predicate '{}'", name),
                span: pred_def.span,
            });
        }

        // Build wildcard scope
        let mut wildcards = HashMap::new();
        let mut wildcard_index = 0;

        // Process public arguments
        for arg in &pred_def.args.public_args {
            if wildcards.contains_key(&arg.name) {
                return Err(ValidationError::DuplicateWildcard {
                    name: arg.name.clone(),
                    span: arg.span,
                });
            }
            wildcards.insert(
                arg.name.clone(),
                WildcardInfo {
                    index: wildcard_index,
                    is_public: true,
                    source_span: arg.span,
                },
            );
            wildcard_index += 1;
        }

        // Process private arguments
        let mut private_count = 0;
        if let Some(private_args) = &pred_def.args.private_args {
            for arg in private_args {
                if wildcards.contains_key(&arg.name) {
                    return Err(ValidationError::DuplicateWildcard {
                        name: arg.name.clone(),
                        span: arg.span,
                    });
                }
                wildcards.insert(
                    arg.name.clone(),
                    WildcardInfo {
                        index: wildcard_index,
                        is_public: false,
                        source_span: arg.span,
                    },
                );
                wildcard_index += 1;
                private_count += 1;
            }
        }

        // Add to symbol table
        self.symbols.predicates.insert(
            name.clone(),
            PredicateInfo {
                kind: PredicateKind::Custom {
                    index: self.custom_predicate_count,
                },
                arity: pred_def.args.public_args.len() + private_count,
                public_arity: pred_def.args.public_args.len(),
                source_span: pred_def.name.span,
            },
        );

        self.symbols
            .wildcard_scopes
            .insert(name.clone(), WildcardScope { wildcards });
        self.custom_predicate_count += 1;

        Ok(())
    }

    fn validate_references(&mut self, document: &Document) -> Result<(), ValidationError> {
        for item in &document.items {
            match item {
                DocumentItem::CustomPredicateDef(pred_def) => {
                    self.validate_custom_predicate_statements(pred_def)?;
                }
                DocumentItem::RequestDef(req_def) => {
                    self.validate_request_statements(req_def)?;
                }
                _ => {}
            }
        }
        Ok(())
    }

    fn validate_custom_predicate_statements(
        &self,
        pred_def: &CustomPredicateDef,
    ) -> Result<(), ValidationError> {
        let pred_name = pred_def.name.name.clone();

        for stmt in &pred_def.statements {
            let wildcard_scope = self
                .symbols
                .wildcard_scopes
                .get(&pred_name)
                .expect("Wildcard scope should exist after pass 1");
            self.validate_statement(stmt, Some((&pred_name, wildcard_scope)))?;
        }

        Ok(())
    }

    fn validate_request_statements(&mut self, req_def: &RequestDef) -> Result<(), ValidationError> {
        if req_def.statements.is_empty() {
            self.diagnostics.push(Diagnostic {
                level: DiagnosticLevel::Warning,
                message: "Empty REQUEST block".to_string(),
                span: req_def.span,
            });
        }

        for stmt in &req_def.statements {
            self.validate_statement(stmt, None)?;
        }

        Ok(())
    }

    /// Validate that no wildcard name collides with a predicate name to avoid ambiguity when using
    /// wildcard predicates.
    fn validate_wildcard_names(&self, names: &HashSet<&String>) -> Result<(), ValidationError> {
        for name in names {
            if NativePredicate::from_str(name).is_ok()
                || self.symbols.predicates.contains_key(*name)
            {
                return Err(ValidationError::WildcardPredicateNameCollision {
                    name: (*name).clone(),
                });
            }
        }
        Ok(())
    }

    fn validate_statement(
        &self,
        stmt: &StatementTmpl,
        wildcard_context: Option<(&str, &WildcardScope)>,
    ) -> Result<(), ValidationError> {
        let pred_name = stmt.predicate.predicate_name();
        let pred_span = match &stmt.predicate {
            PredicateRef::Local(id) => id.span,
            PredicateRef::Qualified { predicate, .. } => predicate.span,
        };

        let wc_names = match wildcard_context {
            Some((_, wc_scope)) => wc_scope.wildcards.keys().collect(),
            None => HashSet::new(),
        };
        self.validate_wildcard_names(&wc_names)?;

        // Check if predicate exists
        let pred_info = match &stmt.predicate {
            PredicateRef::Qualified { module, predicate } => {
                // Look up the predicate in the imported module
                let module_name = &module.name;
                if let Some(imported_module) = self.symbols.imported_modules.get(module_name) {
                    // Find the predicate in the module
                    if let Some(&idx) = imported_module.predicate_index.get(&predicate.name) {
                        let module_pred = &imported_module.batch.predicates()[idx];
                        Some(PredicateInfo {
                            kind: PredicateKind::ModuleImported {
                                module_name: module_name.clone(),
                                predicate_name: predicate.name.clone(),
                                predicate_index: idx,
                            },
                            arity: module_pred.wildcard_names.len(),
                            public_arity: module_pred.args_len,
                            source_span: None,
                        })
                    } else {
                        return Err(ValidationError::UndefinedPredicate {
                            name: format!("{}::{}", module_name, predicate.name),
                            span: pred_span,
                        });
                    }
                } else {
                    return Err(ValidationError::ModuleNotFound {
                        name: module_name.clone(),
                        span: module.span,
                    });
                }
            }
            PredicateRef::Local(_) => {
                if let Ok(native) = NativePredicate::from_str(pred_name) {
                    // Native predicate
                    Some(PredicateInfo {
                        kind: PredicateKind::Native(native),
                        arity: native.arity(),
                        public_arity: native.arity(),
                        source_span: None,
                    })
                } else if let Some(info) = self.symbols.predicates.get(pred_name) {
                    // Custom or imported predicate
                    Some(info.clone())
                } else if wc_names.contains(&pred_name.to_string()) {
                    None
                } else {
                    return Err(ValidationError::UndefinedPredicate {
                        name: pred_name.to_string(),
                        span: pred_span,
                    });
                }
            }
        };

        if let Some(ref pred_info) = pred_info {
            let expected_arity = pred_info.public_arity;
            if stmt.args.len() != expected_arity {
                return Err(ValidationError::ArgumentCountMismatch {
                    predicate: pred_name.to_string(),
                    expected: expected_arity,
                    found: stmt.args.len(),
                    span: stmt.span,
                });
            }
        }

        // Validate arguments
        self.validate_statement_args(stmt, pred_info.as_ref(), wildcard_context)?;

        Ok(())
    }

    fn validate_statement_args(
        &self,
        stmt: &StatementTmpl,
        pred_info: Option<&PredicateInfo>,
        wildcard_context: Option<(&str, &WildcardScope)>,
    ) -> Result<(), ValidationError> {
        // For custom predicates, only wildcards and literals are allowed
        if matches!(
            pred_info.map(|i| &i.kind),
            Some(PredicateKind::Custom { .. })
                | Some(PredicateKind::BatchImported { .. })
                | Some(PredicateKind::ModuleImported { .. })
        ) {
            for arg in &stmt.args {
                match arg {
                    StatementTmplArg::AnchoredKey(_) => {
                        return Err(ValidationError::InvalidArgumentType {
                            predicate: stmt.predicate.predicate_name().to_string(),
                            span: stmt.span,
                        });
                    }
                    StatementTmplArg::Wildcard(id) => {
                        if let Some((pred_name, scope)) = wildcard_context {
                            if !scope.wildcards.contains_key(&id.name) {
                                return Err(ValidationError::UndefinedWildcard {
                                    name: id.name.clone(),
                                    pred_name: pred_name.to_string(),
                                    span: id.span,
                                });
                            }
                        }
                    }
                    StatementTmplArg::Literal(_) => {}
                }
            }
        } else {
            // Native predicates can have anchored keys
            for arg in &stmt.args {
                match arg {
                    StatementTmplArg::Wildcard(id) => {
                        if let Some((pred_name, scope)) = wildcard_context {
                            if !scope.wildcards.contains_key(&id.name) {
                                return Err(ValidationError::UndefinedWildcard {
                                    name: id.name.clone(),
                                    pred_name: pred_name.to_string(),
                                    span: id.span,
                                });
                            }
                        }
                    }
                    StatementTmplArg::AnchoredKey(ak) => {
                        if let Some((pred_name, scope)) = wildcard_context {
                            if !scope.wildcards.contains_key(&ak.root.name) {
                                return Err(ValidationError::UndefinedWildcard {
                                    name: ak.root.name.clone(),
                                    pred_name: pred_name.to_string(),
                                    span: ak.root.span,
                                });
                            }
                        }
                    }
                    StatementTmplArg::Literal(_) => {}
                }
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use super::*;
    use crate::{
        lang::{frontend_ast::parse::parse_document, parser::parse_podlang, Module},
        middleware::{CustomPredicate, Params, EMPTY_HASH},
    };

    fn parse_and_validate_module(
        input: &str,
        modules: &HashMap<String, Arc<Module>>,
    ) -> Result<ValidatedAST, ValidationError> {
        let parsed = parse_podlang(input).expect("Failed to parse");
        let document = parse_document(parsed.into_iter().next().unwrap()).expect("Failed to parse");
        validate(document, modules, ParseMode::Module)
    }

    fn parse_and_validate_request(
        input: &str,
        modules: &HashMap<String, Arc<Module>>,
    ) -> Result<ValidatedAST, ValidationError> {
        let parsed = parse_podlang(input).expect("Failed to parse");
        let document = parse_document(parsed.into_iter().next().unwrap()).expect("Failed to parse");
        validate(document, modules, ParseMode::Request)
    }

    #[test]
    fn test_validate_simple_request() {
        let input = r#"REQUEST(
            Equal(A["foo"], B["bar"])
        )"#;
        let result = parse_and_validate_request(input, &HashMap::new());
        assert!(result.is_ok());
    }

    #[test]
    fn test_validate_custom_predicate() {
        let input = r#"
            my_pred(A, B) = AND (
                Equal(A["foo"], B["bar"])
            )
        "#;
        let result = parse_and_validate_module(input, &HashMap::new());
        assert!(result.is_ok());

        let validated = result.unwrap();
        assert!(validated.symbols.predicates.contains_key("my_pred"));
        assert!(validated.symbols.wildcard_scopes.contains_key("my_pred"));
    }

    #[test]
    fn test_undefined_predicate() {
        let input = r#"REQUEST(
            UndefinedPred(A, B)
        )"#;
        let result = parse_and_validate_request(input, &HashMap::new());
        assert!(matches!(
            result,
            Err(ValidationError::UndefinedPredicate { .. })
        ));
    }

    #[test]
    fn test_undefined_wildcard() {
        let input = r#"
            my_pred(A) = AND (
                Equal(A["foo"], B["bar"])
            )
        "#;
        let result = parse_and_validate_module(input, &HashMap::new());
        assert!(
            matches!(result, Err(ValidationError::UndefinedWildcard { name, .. }) if name == "B")
        );
    }

    #[test]
    fn test_arity_mismatch() {
        let input = r#"REQUEST(
            Equal(A, B, C)
        )"#;
        let result = parse_and_validate_request(input, &HashMap::new());
        assert!(matches!(
            result,
            Err(ValidationError::ArgumentCountMismatch { .. })
        ));
    }

    #[test]
    fn test_duplicate_predicate() {
        let input = r#"
            my_pred(A) = AND (Equal(A["x"], 1))
            my_pred(B) = AND (Equal(B["y"], 2))
        "#;
        let result = parse_and_validate_module(input, &HashMap::new());
        assert!(matches!(
            result,
            Err(ValidationError::DuplicatePredicate { .. })
        ));
    }

    #[test]
    fn test_duplicate_wildcard() {
        let input = r#"
            my_pred(A, A) = AND (Equal(A["x"], 1))
        "#;
        let result = parse_and_validate_module(input, &HashMap::new());
        assert!(matches!(
            result,
            Err(ValidationError::DuplicateWildcard { .. })
        ));
    }

    #[test]
    fn test_wildcard_predicate_collision() {
        let input = r#"
            my_pred(A, Lt) = AND (Equal(A["x"], Lt))
        "#;
        let result = parse_and_validate_module(input, &HashMap::new());
        assert!(matches!(
            result,
            Err(ValidationError::WildcardPredicateNameCollision { .. })
        ));
    }

    #[test]
    fn test_custom_predicate_with_anchored_key() {
        // First create a module with the predicate
        let params = Params::default();
        let pred = CustomPredicate::and(
            &params,
            "my_pred".to_string(),
            vec![],
            2,
            vec!["A".to_string(), "B".to_string()],
        )
        .unwrap();

        let batch = CustomPredicateBatch::new("TestBatch".to_string(), vec![pred]);
        let test_module = Arc::new(Module::new(batch, HashMap::new()));

        let mut available_modules = HashMap::new();
        available_modules.insert("testmod".to_string(), test_module);

        // Test that passing anchored key to custom predicate fails
        let input = r#"
            use module testmod

            REQUEST(
                testmod::my_pred(X["key"], Y)
            )
        "#;
        let result = parse_and_validate_request(input, &available_modules);
        assert!(matches!(
            result,
            Err(ValidationError::InvalidArgumentType { .. })
        ));
    }

    #[test]
    fn test_forward_reference() {
        let input = r#"
            pred1(A) = AND (
                pred2(A)
            )

            pred2(B) = AND (
                Equal(B["x"], 1)
            )
        "#;
        let result = parse_and_validate_module(input, &HashMap::new());
        assert!(result.is_ok());
    }

    #[test]
    fn test_private_args() {
        let input = r#"
            my_pred(A, private: B, C) = AND (
                Equal(A["x"], B["y"])
                Equal(B["z"], C["w"])
            )
        "#;
        let result = parse_and_validate_module(input, &HashMap::new());
        assert!(result.is_ok());

        let validated = result.unwrap();
        let pred_info = &validated.symbols.predicates["my_pred"];
        assert_eq!(pred_info.arity, 3);
        assert_eq!(pred_info.public_arity, 1);
    }

    #[test]
    fn test_empty_statement_list() {
        // Create a custom predicate with empty statements to test validation
        let document = Document {
            items: vec![DocumentItem::CustomPredicateDef(CustomPredicateDef {
                name: Identifier {
                    name: "my_pred".to_string(),
                    span: None,
                },
                args: ArgSection {
                    public_args: vec![Identifier {
                        name: "A".to_string(),
                        span: None,
                    }],
                    private_args: None,
                    span: None,
                },
                conjunction_type: ConjunctionType::And,
                statements: vec![], // Empty statements
                span: None,
            })],
        };
        let result = validate(document, &HashMap::new(), ParseMode::Module);
        assert!(matches!(
            result,
            Err(ValidationError::EmptyStatementList { .. })
        ));
    }

    #[test]
    fn test_multiple_request_definitions() {
        let input = r#"
            REQUEST(Equal(A["x"], 1))
            REQUEST(Equal(B["y"], 2))
        "#;
        let result = parse_and_validate_request(input, &HashMap::new());
        assert!(matches!(
            result,
            Err(ValidationError::MultipleRequestDefinitions { .. })
        ));
    }

    #[test]
    fn test_use_module_statement() {
        use std::sync::Arc;

        use hex::ToHex;

        let params = Params::default();

        // Create a module to import
        let pred = CustomPredicate::and(
            &params,
            "imported".to_string(),
            vec![],
            2,
            vec!["X".to_string(), "Y".to_string()],
        )
        .unwrap();

        let batch = CustomPredicateBatch::new("TestBatch".to_string(), vec![pred]);
        let test_module = Arc::new(Module::new(batch, HashMap::new()));

        let mut available_modules = HashMap::new();
        available_modules.insert("testmod".to_string(), test_module);

        let input = format!(
            r#"
            use module testmod
            use intro intro_pred() from 0x{}

            REQUEST(
                testmod::imported(A, B)
                intro_pred()
            )
        "#,
            EMPTY_HASH.encode_hex::<String>()
        );

        let result = parse_and_validate_request(&input, &available_modules);
        assert!(result.is_ok());

        let validated = result.unwrap();
        // Module predicates are accessed via qualified names, so no local binding
        assert!(validated.symbols.predicates.contains_key("intro_pred"));
        assert!(validated.symbols.imported_modules.contains_key("testmod"));
    }

    #[test]
    fn test_syntactic_sugar_predicates() {
        let input = r#"REQUEST(
            GtEq(A["x"], B["y"])
            DictContains(D, K, V)
            SetNotContains(S, E)
        )"#;
        let result = parse_and_validate_request(input, &HashMap::new());
        assert!(result.is_ok());
    }
}
