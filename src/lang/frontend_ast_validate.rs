//! Validation for the frontend AST
//!
//! This module provides semantic validation for parsed AST documents,
//! including name resolution, arity checking, and wildcard validation.

use std::{collections::HashMap, str::FromStr, sync::Arc};

use hex::ToHex;

use crate::{
    lang::frontend_ast::*,
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

/// Validate an AST document
pub fn validate(
    document: Document,
    available_batches: &[Arc<CustomPredicateBatch>],
) -> Result<ValidatedAST, ValidationError> {
    let validator = Validator::new(available_batches);
    validator.validate(document)
}

struct Validator {
    available_batches: HashMap<String, Arc<CustomPredicateBatch>>,
    symbols: SymbolTable,
    diagnostics: Vec<Diagnostic>,
    custom_predicate_count: usize,
}

impl Validator {
    fn new(batches: &[Arc<CustomPredicateBatch>]) -> Self {
        let mut available_batches = HashMap::new();
        for batch in batches {
            // Store by hex ID for lookup
            let id = format!("0x{}", batch.id().encode_hex::<String>());
            available_batches.insert(id, batch.clone());
        }

        Self {
            available_batches,
            symbols: SymbolTable {
                predicates: HashMap::new(),
                wildcard_scopes: HashMap::new(),
            },
            diagnostics: Vec::new(),
            custom_predicate_count: 0,
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
            if let DocumentItem::UseBatchStatement(use_stmt) = item {
                self.process_use_batch_statement(use_stmt)?;
            }
            if let DocumentItem::UseIntroStatement(use_stmt) = item {
                self.process_use_intro_statement(use_stmt)?;
            }
        }

        // Then process custom predicate definitions
        for item in &document.items {
            if let DocumentItem::CustomPredicateDef(pred_def) = item {
                self.process_custom_predicate_def(pred_def)?;
            }
        }

        // Check for multiple REQUEST definitions (only one allowed)
        let mut first_request_span = None;
        for item in &document.items {
            if let DocumentItem::RequestDef(req) = item {
                if let Some(first_span) = first_request_span {
                    return Err(ValidationError::MultipleRequestDefinitions {
                        first_span: Some(first_span),
                        second_span: req.span,
                    });
                }
                first_request_span = req.span;
            }
        }

        Ok(())
    }

    fn process_use_batch_statement(
        &mut self,
        use_stmt: &UseBatchStatement,
    ) -> Result<(), ValidationError> {
        let batch_id = format!("0x{}", use_stmt.batch_ref.hash.encode_hex::<String>());

        let batch = self.available_batches.get(&batch_id).ok_or_else(|| {
            ValidationError::BatchNotFound {
                id: batch_id.clone(),
                span: use_stmt.batch_ref.span,
            }
        })?;

        if use_stmt.imports.len() != batch.predicates().len() {
            return Err(ValidationError::ImportArityMismatch {
                expected: batch.predicates().len(),
                found: use_stmt.imports.len(),
                span: use_stmt.span,
            });
        }

        for (i, import) in use_stmt.imports.iter().enumerate() {
            if let ImportName::Named(name) = import {
                if self.symbols.predicates.contains_key(name) {
                    return Err(ValidationError::DuplicateImport {
                        name: name.clone(),
                        span: use_stmt.span,
                    });
                }

                let pred = &batch.predicates()[i];
                // CustomPredicate has args_len (public args) and wildcard_names (total args)
                let total_arity = pred.wildcard_names.len();
                let public_arity = pred.args_len;

                self.symbols.predicates.insert(
                    name.clone(),
                    PredicateInfo {
                        kind: PredicateKind::BatchImported {
                            batch: batch.clone(),
                            index: i,
                        },
                        arity: total_arity,
                        public_arity,
                        source_span: use_stmt.span,
                    },
                );
            }
        }

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

    fn validate_statement(
        &self,
        stmt: &StatementTmpl,
        wildcard_context: Option<(&str, &WildcardScope)>,
    ) -> Result<(), ValidationError> {
        let pred_name = &stmt.predicate.name;

        // Check if predicate exists
        let pred_info = if let Ok(native) = NativePredicate::from_str(pred_name) {
            // Native predicate
            PredicateInfo {
                kind: PredicateKind::Native(native),
                arity: native.arity(),
                public_arity: native.arity(),
                source_span: None,
            }
        } else if let Some(info) = self.symbols.predicates.get(pred_name) {
            // Custom or imported predicate
            info.clone()
        } else {
            return Err(ValidationError::UndefinedPredicate {
                name: pred_name.clone(),
                span: stmt.predicate.span,
            });
        };

        let expected_arity = pred_info.public_arity;

        if stmt.args.len() != expected_arity {
            return Err(ValidationError::ArgumentCountMismatch {
                predicate: pred_name.clone(),
                expected: expected_arity,
                found: stmt.args.len(),
                span: stmt.span,
            });
        }

        // Validate arguments
        self.validate_statement_args(stmt, &pred_info, wildcard_context)?;

        Ok(())
    }

    fn validate_statement_args(
        &self,
        stmt: &StatementTmpl,
        pred_info: &PredicateInfo,
        wildcard_context: Option<(&str, &WildcardScope)>,
    ) -> Result<(), ValidationError> {
        // For custom predicates, only wildcards and literals are allowed
        if matches!(
            pred_info.kind,
            PredicateKind::Custom { .. } | PredicateKind::BatchImported { .. }
        ) {
            for arg in &stmt.args {
                match arg {
                    StatementTmplArg::AnchoredKey(_) => {
                        return Err(ValidationError::InvalidArgumentType {
                            predicate: stmt.predicate.name.clone(),
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
    use super::*;
    use crate::{
        lang::{frontend_ast::parse::parse_document, parser::parse_podlang},
        middleware::{CustomPredicate, Params, EMPTY_HASH},
    };

    fn parse_and_validate(
        input: &str,
        batches: &[Arc<CustomPredicateBatch>],
    ) -> Result<ValidatedAST, ValidationError> {
        let parsed = parse_podlang(input).expect("Failed to parse");
        let document = parse_document(parsed.into_iter().next().unwrap()).expect("Failed to parse");
        validate(document, batches)
    }

    #[test]
    fn test_validate_empty() {
        let result = parse_and_validate("", &[]);
        assert!(result.is_ok());
    }

    #[test]
    fn test_validate_simple_request() {
        let input = r#"REQUEST(
            Equal(A["foo"], B["bar"])
        )"#;
        let result = parse_and_validate(input, &[]);
        assert!(result.is_ok());
    }

    #[test]
    fn test_validate_custom_predicate() {
        let input = r#"
            my_pred(A, B) = AND (
                Equal(A["foo"], B["bar"])
            )
        "#;
        let result = parse_and_validate(input, &[]);
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
        let result = parse_and_validate(input, &[]);
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
        let result = parse_and_validate(input, &[]);
        assert!(
            matches!(result, Err(ValidationError::UndefinedWildcard { name, .. }) if name == "B")
        );
    }

    #[test]
    fn test_arity_mismatch() {
        let input = r#"REQUEST(
            Equal(A, B, C)
        )"#;
        let result = parse_and_validate(input, &[]);
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
        let result = parse_and_validate(input, &[]);
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
        let result = parse_and_validate(input, &[]);
        assert!(matches!(
            result,
            Err(ValidationError::DuplicateWildcard { .. })
        ));
    }

    #[test]
    fn test_custom_predicate_with_anchored_key() {
        let input = r#"
            my_pred(A, B) = AND (
                Equal(A["foo"], B["bar"])
            )
            
            REQUEST(
                my_pred(X["key"], Y)
            )
        "#;
        let result = parse_and_validate(input, &[]);
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
        let result = parse_and_validate(input, &[]);
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
        let result = parse_and_validate(input, &[]);
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
        let result = validate(document, &[]);
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
        let result = parse_and_validate(input, &[]);
        assert!(matches!(
            result,
            Err(ValidationError::MultipleRequestDefinitions { .. })
        ));
    }

    #[test]
    fn test_use_statement() {
        let params = Params::default();

        // Create a batch to import
        let pred = CustomPredicate::and(
            &params,
            "imported".to_string(),
            vec![],
            2,
            vec!["X".to_string(), "Y".to_string()],
        )
        .unwrap();

        let batch = CustomPredicateBatch::new(&params, "TestBatch".to_string(), vec![pred]);

        let batch_id = batch.id().encode_hex::<String>();
        let input = format!(
            r#"
            use batch imported_pred from 0x{}
            use intro intro_pred() from 0x{}

            REQUEST(
                imported_pred(A, B)
                intro_pred()
            )
        "#,
            batch_id,
            EMPTY_HASH.encode_hex::<String>()
        );

        let result = parse_and_validate(&input, &[batch]);
        assert!(result.is_ok());

        let validated = result.unwrap();
        assert!(validated.symbols.predicates.contains_key("imported_pred"));
        assert!(validated.symbols.predicates.contains_key("intro_pred"));
    }

    #[test]
    fn test_syntactic_sugar_predicates() {
        let input = r#"REQUEST(
            GtEq(A["x"], B["y"])
            DictContains(D, K, V)
            SetNotContains(S, E)
        )"#;
        let result = parse_and_validate(input, &[]);
        assert!(result.is_ok());
    }
}
