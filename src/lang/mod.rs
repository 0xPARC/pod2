//! Podlang front-end: parsing, validation, and lowering.
//!
//! This module is the high-level entrypoint to the Podlang pipeline.
//!
//! ## API
//!
//! - [`load_module`]: Load a module file containing predicate definitions.
//!   Returns a [`Module`] wrapping a `CustomPredicateBatch`.
//!
//! - [`parse_request`]: Parse a request file containing a REQUEST block.
//!   Returns a [`PodRequest`] with statement templates.
//!
//! ## Module vs Request
//!
//! - **Modules** contain predicate definitions (`pred(A) = AND(...)`) and imports.
//!   They cannot contain a REQUEST block.
//!
//! - **Requests** contain a REQUEST block and imports.
//!   They cannot define predicates.
//!
//! ## Using Modules
//!
//! Use [`Module::apply_predicate`] to apply a predicate into a `MainPodBuilder`
//! (recommended), or [`Module::apply_predicate_with`] for advanced control.
//!
//! Large predicates are automatically split into chains of smaller predicates;
//! `apply_predicate` handles this transparently.
//!
pub mod diagnostics;
pub mod error;
pub mod frontend_ast;
pub mod frontend_ast_lower;
pub mod frontend_ast_split;
pub mod frontend_ast_validate;
pub mod module;
pub mod parser;
pub mod pretty_print;

use std::sync::Arc;

pub use diagnostics::render_error;
pub use error::{LangError, LangErrorKind};
pub use frontend_ast_split::{SplitChainInfo, SplitChainPiece, SplitResult};
pub use module::{Module, MultiOperationError};
pub use parser::{parse_podlang, Pairs, ParseError, Rule};
pub use pretty_print::PrettyPrint;

use crate::{frontend::PodRequest, middleware::Params};

/// Load a module from Podlang source.
///
/// Modules contain predicate definitions and imports, but no REQUEST block.
///
/// - `source`: Podlang source code
/// - `name`: Name for the module (used in batch naming)
/// - `params`: Middleware parameters limiting sizes/arity
/// - `available_modules`: External modules available for `use module ...` imports
pub fn load_module(
    source: &str,
    name: &str,
    params: &Params,
    available_modules: Vec<Arc<Module>>,
) -> Result<Module, LangError> {
    load_module_inner(source, name, params, available_modules)
        .map_err(|e| e.with_source(source.to_string(), None))
}

fn load_module_inner(
    source: &str,
    name: &str,
    params: &Params,
    available_modules: &HashMap<String, Arc<Module>>,
) -> Result<Module, LangError> {
    let pairs = parse_podlang(source)?;
    let document_pair = pairs
        .into_iter()
        .next()
        .expect("parse_podlang should always return at least one pair for a valid document");
    let document = frontend_ast::parse::parse_document(document_pair)?;
    let available_modules_map = available_modules
        .iter()
        .map(|m| (m.id(), m.clone()))
        .collect();
    let validated = frontend_ast_validate::validate(
        document,
        &available_modules_map,
        frontend_ast_validate::ParseMode::Module,
    )?;
    let module = frontend_ast_lower::lower_module(validated, params, name)?;
    Ok(module)
}

/// Parse a request from Podlang source.
///
/// Requests contain a REQUEST block and imports, but no predicate definitions.
///
/// - `source`: Podlang source code
/// - `params`: Middleware parameters limiting sizes/arity
/// - `available_modules`: External modules available for `use module ...` imports
pub fn parse_request(
    source: &str,
    params: &Params,
    available_modules: &[Arc<Module>],
) -> Result<PodRequest, LangError> {
    parse_request_inner(source, params, available_modules)
        .map_err(|e| e.with_source(source.to_string(), None))
}

fn parse_request_inner(
    source: &str,
    params: &Params,
    available_modules: &HashMap<String, Arc<Module>>,
) -> Result<PodRequest, LangError> {
    let pairs = parse_podlang(source)?;
    let document_pair = pairs
        .into_iter()
        .next()
        .expect("parse_podlang should always return at least one pair for a valid document");
    let document = frontend_ast::parse::parse_document(document_pair)?;
    let available_modules_map = available_modules
        .iter()
        .map(|m| (m.id(), m.clone()))
        .collect();
    let validated = frontend_ast_validate::validate(
        document,
        &available_modules_map,
        frontend_ast_validate::ParseMode::Request,
    )?;
    let request = frontend_ast_lower::lower_request(validated, params)?;
    Ok(request)
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use hex::ToHex;
    use pretty_assertions::assert_eq;

    use super::*;
    use crate::{
        backends::plonky2::primitives::ec::schnorr::SecretKey,
        middleware::{
            CustomPredicate, CustomPredicateBatch, CustomPredicateRef, Key, NativePredicate,
            Params, Predicate, PredicateOrWildcard, RawValue, StatementTmpl, StatementTmplArg,
            Value, Wildcard, EMPTY_HASH,
        },
    };

    // Helper functions
    fn wc(name: &str, index: usize) -> Wildcard {
        Wildcard::new(name.to_string(), index)
    }

    fn sta_ak(pod_var: (&str, usize), key: &str) -> StatementTmplArg {
        StatementTmplArg::AnchoredKey(wc(pod_var.0, pod_var.1), Key::from(key))
    }

    fn sta_wc_lit(name: &str, index: usize) -> StatementTmplArg {
        StatementTmplArg::Wildcard(wc(name, index))
    }

    fn sta_lit(value: impl Into<Value>) -> StatementTmplArg {
        StatementTmplArg::Literal(value.into())
    }

    fn names(names: &[&str]) -> Vec<String> {
        names.iter().map(|s| s.to_string()).collect()
    }

    fn pred_lit(pred: Predicate) -> PredicateOrWildcard {
        PredicateOrWildcard::Predicate(pred)
    }

    #[test]
    fn test_e2e_simple_predicate() -> Result<(), LangError> {
        let input = r#"
            is_equal(PodA, PodB) = AND(
                Equal(PodA["the_key"], PodB["the_key"])
            )
        "#;

        let params = Params::default();
        let module = load_module(input, "test_module", &params, vec![])?;

        assert_eq!(module.batch.predicates().len(), 1);

        // Expected structure
        let expected_statements = vec![StatementTmpl {
            pred_or_wc: pred_lit(Predicate::Native(NativePredicate::Equal)),
            args: vec![
                sta_ak(("PodA", 0), "the_key"), // PodA["the_key"] -> Wildcard(0), Key("the_key")
                sta_ak(("PodB", 1), "the_key"), // PodB["the_key"] -> Wildcard(1), Key("the_key")
            ],
        }];
        let expected_predicate = CustomPredicate::and(
            &params,
            "is_equal".to_string(),
            expected_statements,
            2, // args_len (PodA, PodB)
            names(&["PodA", "PodB"]),
        )?;
        let expected_batch =
            CustomPredicateBatch::new("test_module".to_string(), vec![expected_predicate]);

        assert_eq!(&*module.batch, &*expected_batch);

        Ok(())
    }

    #[test]
    fn test_e2e_simple_request() -> Result<(), LangError> {
        let input = r#"
            REQUEST(
                Equal(ConstPod["my_val"], Raw(0x0000000000000000000000000000000000000000000000000000000000000001))
                Lt(GovPod["dob"], ConstPod["my_val"])
            )
        "#;

        let params = Params::default();
        let request = parse_request(input, &params, &[])?;
        let request_templates = request.templates();

        assert!(!request_templates.is_empty());

        // Expected structure
        let expected_templates = vec![
            StatementTmpl {
                pred_or_wc: pred_lit(Predicate::Native(NativePredicate::Equal)),
                args: vec![
                    sta_ak(("ConstPod", 0), "my_val"), // ConstPod["my_val"] -> Wildcard(0), Key("my_val")
                    sta_lit(RawValue::from(1)),
                ],
            },
            StatementTmpl {
                pred_or_wc: pred_lit(Predicate::Native(NativePredicate::Lt)),
                args: vec![
                    sta_ak(("GovPod", 1), "dob"), // GovPod["dob"] -> Wildcard(1), Key("dob")
                    sta_ak(("ConstPod", 0), "my_val"), // ConstPod["my_val"] -> Wildcard(0), Key("my_val")
                ],
            },
        ];

        assert_eq!(request_templates, expected_templates);

        Ok(())
    }

    #[test]
    fn test_e2e_predicate_with_private_var() -> Result<(), LangError> {
        let input = r#"
            uses_private(A, private: Temp) = AND(
                Equal(A["input_key"], Temp["const_key"])
                Equal(Temp["const_key"], "some_value")
            )
        "#;

        let params = Params::default();
        let module = load_module(input, "test_module", &params, vec![])?;

        assert_eq!(module.batch.predicates().len(), 1);

        // Expected structure: Public args: A (index 0). Private args: Temp (index 1)
        let expected_statements = vec![
            StatementTmpl {
                pred_or_wc: pred_lit(Predicate::Native(NativePredicate::Equal)),
                args: vec![
                    sta_ak(("A", 0), "input_key"), // A["input_key"] -> Wildcard(0), Key("input_key")
                    sta_ak(("Temp", 1), "const_key"), // Temp["const_key"] -> Wildcard(1), Key("const_key")
                ],
            },
            StatementTmpl {
                pred_or_wc: pred_lit(Predicate::Native(NativePredicate::Equal)),
                args: vec![
                    sta_ak(("Temp", 1), "const_key"), // Temp["const_key"] -> Wildcard(1), Key("const_key")
                    sta_lit("some_value"),            // Literal("some_value")
                ],
            },
        ];
        let expected_predicate = CustomPredicate::and(
            &params,
            "uses_private".to_string(),
            expected_statements,
            1, // args_len (A)
            names(&["A", "Temp"]),
        )?;
        let expected_batch =
            CustomPredicateBatch::new("test_module".to_string(), vec![expected_predicate]);

        assert_eq!(&*module.batch, &*expected_batch);

        Ok(())
    }

    #[test]
    fn test_e2e_request_with_custom_call() -> Result<(), LangError> {
        // First, load the module
        let module_input = r#"
            my_pred(X, Y) = AND(
                Equal(X["val"], Y["val"])
            )
        "#;

        let params = Params::default();
        let module = Arc::new(load_module(module_input, "my_module", &params, vec![])?);

        assert_eq!(module.batch.predicates().len(), 1);

        let module_hash = module.id().encode_hex::<String>();

        // Then, parse the request using the module
        let request_input = format!(
            r#"
            use module 0x{} as my_module

            REQUEST(
                my_module::my_pred(Pod1, Pod2)
            )
        "#,
            module_hash
        );

        let request = parse_request(&request_input, &params, std::slice::from_ref(&module))?;
        let request_templates = request.templates();

        assert!(!request_templates.is_empty());

        // Expected Request structure
        // Pod1 -> Wildcard 0, Pod2 -> Wildcard 1
        let expected_request_templates = vec![StatementTmpl {
            pred_or_wc: pred_lit(Predicate::Custom(CustomPredicateRef::new(
                module.batch.clone(),
                0,
            ))),
            args: vec![
                StatementTmplArg::Wildcard(wc("Pod1", 0)),
                StatementTmplArg::Wildcard(wc("Pod2", 1)),
            ],
        }];

        assert_eq!(request_templates, expected_request_templates);

        Ok(())
    }

    #[test]
    fn test_e2e_request_with_various_args() -> Result<(), LangError> {
        // First, load the module
        let module_input = r#"
            some_pred(A, B, C) = AND( Equal(A["foo"], B["bar"]) )
        "#;

        let params = Params::default();
        let module = Arc::new(load_module(module_input, "some_module", &params, vec![])?);

        let module_hash = module.id().encode_hex::<String>();

        // Then, parse the request
        let request_input = format!(
            r#"
            use module 0x{} as some_module

            REQUEST(
                some_module::some_pred(
                    Var1,                  // Wildcard
                    12345,                  // Int Literal
                    "hello_string"         // String Literal
                )
                Equal(AnotherPod["another_key"], Var1["some_field"])
            )
        "#,
            module_hash
        );

        let request = parse_request(&request_input, &params, std::slice::from_ref(&module))?;
        let request_templates = request.templates();

        assert!(!request_templates.is_empty());

        // Expected Wildcard Indices in Request Scope:
        // Var1 -> 0
        // AnotherPod -> 1

        // Expected structure
        let expected_templates = vec![
            StatementTmpl {
                pred_or_wc: pred_lit(Predicate::Custom(CustomPredicateRef::new(
                    module.batch.clone(),
                    0,
                ))), // Refers to some_pred
                args: vec![
                    StatementTmplArg::Wildcard(wc("Var1", 0)),        // Var1
                    StatementTmplArg::Literal(Value::from(12345i64)), // 12345
                    StatementTmplArg::Literal(Value::from("hello_string")), // "hello_string"
                ],
            },
            StatementTmpl {
                pred_or_wc: pred_lit(Predicate::Native(NativePredicate::Equal)),
                args: vec![
                    // AnotherPod["another_key"] -> Wildcard(1), Key("another_key")
                    sta_ak(("AnotherPod", 1), "another_key"),
                    // Var1["some_field"] -> Wildcard(0), Key("some_field")
                    sta_ak(("Var1", 0), "some_field"),
                ],
            },
        ];

        assert_eq!(request_templates, expected_templates);

        Ok(())
    }

    #[test]
    fn test_e2e_syntactic_sugar_predicates() -> Result<(), LangError> {
        let input = r#"
            REQUEST(
                GtEq(A["foo"], B["bar"])
                Gt(C["baz"], D["qux"])
                DictContains(A["foo"], B["bar"], C["baz"])
                DictNotContains(A["foo"], B["bar"])
                ArrayContains(A["foo"], B["bar"], C["baz"])
            )
        "#;

        let params = Params::default();
        let request = parse_request(input, &params, &[])?;
        let request_templates = request.templates();

        assert!(!request_templates.is_empty());

        let expected_templates = vec![
            StatementTmpl {
                pred_or_wc: pred_lit(Predicate::Native(NativePredicate::LtEq)),
                args: vec![sta_ak(("B", 1), "bar"), sta_ak(("A", 0), "foo")],
            },
            StatementTmpl {
                pred_or_wc: pred_lit(Predicate::Native(NativePredicate::Lt)),
                args: vec![sta_ak(("D", 3), "qux"), sta_ak(("C", 2), "baz")],
            },
            StatementTmpl {
                pred_or_wc: pred_lit(Predicate::Native(NativePredicate::Contains)),
                args: vec![
                    sta_ak(("A", 0), "foo"),
                    sta_ak(("B", 1), "bar"),
                    sta_ak(("C", 2), "baz"),
                ],
            },
            StatementTmpl {
                pred_or_wc: pred_lit(Predicate::Native(NativePredicate::NotContains)),
                args: vec![sta_ak(("A", 0), "foo"), sta_ak(("B", 1), "bar")],
            },
            StatementTmpl {
                pred_or_wc: pred_lit(Predicate::Native(NativePredicate::Contains)),
                args: vec![
                    sta_ak(("A", 0), "foo"),
                    sta_ak(("B", 1), "bar"),
                    sta_ak(("C", 2), "baz"),
                ],
            },
        ];

        assert_eq!(request_templates, expected_templates);

        Ok(())
    }

    #[test]
    fn test_e2e_zukyc_request_parsing() -> Result<(), LangError> {
        let input = r#"
            REQUEST(
                // Order matters for comparison with the hardcoded templates
                SetNotContains(sanctions["sanctionList"], gov["idNumber"])
                Lt(gov["dateOfBirth"], SELF_HOLDER_18Y["const_18y"])
                Equal(pay["startDate"], SELF_HOLDER_1Y["const_1y"])
                Equal(gov["socialSecurityNumber"], pay["socialSecurityNumber"])
                Equal(SELF_HOLDER_18Y["const_18y"], 1169909388)
                Equal(SELF_HOLDER_1Y["const_1y"], 1706367566)
            )
        "#;

        // Parse the input string
        let request = parse_request(input, &Params::default(), &[])?;
        let parsed_templates = request.templates();

        //  Define Expected Templates (Copied from prover/mod.rs)
        let now_minus_18y_val = Value::from(1169909388_i64);
        let now_minus_1y_val = Value::from(1706367566_i64);

        // Define wildcards and keys for the request
        // Note: Indices must match the order of appearance in the *parsed* request
        // Order: sanctions, gov, SELF_HOLDER_18Y, pay, SELF_HOLDER_1Y
        let wc_sanctions = wc("sanctions", 0);
        let wc_gov = wc("gov", 1);
        let wc_self_18y = wc("SELF_HOLDER_18Y", 2);
        let wc_pay = wc("pay", 3);
        let wc_self_1y = wc("SELF_HOLDER_1Y", 4);

        let id_num_key = "idNumber";
        let dob_key = "dateOfBirth";
        let const_18y_key = "const_18y";
        let start_date_key = "startDate";
        let const_1y_key = "const_1y";
        let ssn_key = "socialSecurityNumber";
        let sanction_list_key = "sanctionList";

        // Define the request templates using wildcards for constants
        let expected_templates = vec![
            // 1. NotContains(sanctions["sanctionList"], gov["idNumber"])
            StatementTmpl {
                pred_or_wc: pred_lit(Predicate::Native(NativePredicate::NotContains)),
                args: vec![
                    sta_ak(
                        (wc_sanctions.name.as_str(), wc_sanctions.index),
                        sanction_list_key,
                    ),
                    sta_ak((wc_gov.name.as_str(), wc_gov.index), id_num_key),
                ],
            },
            // 2. Lt(gov["dateOfBirth"], SELF_HOLDER_18Y["const_18y"])
            StatementTmpl {
                pred_or_wc: pred_lit(Predicate::Native(NativePredicate::Lt)),
                args: vec![
                    sta_ak((wc_gov.name.as_str(), wc_gov.index), dob_key),
                    sta_ak(
                        (wc_self_18y.name.as_str(), wc_self_18y.index),
                        const_18y_key,
                    ),
                ],
            },
            // 3. Equal(pay["startDate"], SELF_HOLDER_1Y["const_1y"])
            StatementTmpl {
                pred_or_wc: pred_lit(Predicate::Native(NativePredicate::Equal)),
                args: vec![
                    sta_ak((wc_pay.name.as_str(), wc_pay.index), start_date_key),
                    sta_ak((wc_self_1y.name.as_str(), wc_self_1y.index), const_1y_key),
                ],
            },
            // 4. Equal(gov["socialSecurityNumber"], pay["socialSecurityNumber"])
            StatementTmpl {
                pred_or_wc: pred_lit(Predicate::Native(NativePredicate::Equal)),
                args: vec![
                    sta_ak((wc_gov.name.as_str(), wc_gov.index), ssn_key),
                    sta_ak((wc_pay.name.as_str(), wc_pay.index), ssn_key),
                ],
            },
            // 5. Equal(SELF_HOLDER_18Y["const_18y"], 1169909388)
            StatementTmpl {
                pred_or_wc: pred_lit(Predicate::Native(NativePredicate::Equal)),
                args: vec![
                    sta_ak(
                        (wc_self_18y.name.as_str(), wc_self_18y.index),
                        const_18y_key,
                    ),
                    sta_lit(now_minus_18y_val.clone()),
                ],
            },
            // 6. Equal(SELF_HOLDER_1Y["const_1y"], 1706367566)
            StatementTmpl {
                pred_or_wc: pred_lit(Predicate::Native(NativePredicate::Equal)),
                args: vec![
                    sta_ak((wc_self_1y.name.as_str(), wc_self_1y.index), const_1y_key),
                    sta_lit(now_minus_1y_val.clone()),
                ],
            },
        ];

        assert_eq!(
            parsed_templates, expected_templates,
            "Parsed ZuKYC request templates do not match the expected hard-coded version"
        );

        Ok(())
    }

    #[test]
    fn test_e2e_ethdos_predicates() -> Result<(), LangError> {
        let params = Params {
            max_input_pods: 3,
            max_statements: 31,
            max_public_statements: 10,
            max_operation_args: 5,
            max_custom_predicate_wildcards: 12,
            ..Default::default()
        };

        let input = r#"
            eth_friend(src, dst, private: attestation_dict) = AND(
                SignedBy(attestation_dict, src)
                Equal(attestation_dict["attestation"], dst)
            )

            eth_dos_distance_base(src, dst, distance) = AND(
                Equal(src, dst)
                Equal(distance, 0)
            )

            eth_dos_distance_ind(src, dst, distance, private: shorter_distance, intermed) = AND(
                eth_dos_distance(src, dst, distance)
                SumOf(distance, shorter_distance, 1)
                eth_friend(intermed, dst)
            )

            eth_dos_distance(src, dst, distance) = OR(
                eth_dos_distance_base(src, dst, distance)
                eth_dos_distance_ind(src, dst, distance)
            )
        "#;

        let module = load_module(input, "ethdos", &params, vec![])?;

        assert_eq!(
            module.batch.predicates().len(),
            4,
            "Expected 4 custom predicates"
        );

        // Predicate Order: eth_friend (0), base (1), ind (2), distance (3)

        // eth_friend (Index 0)
        let expected_friend_stmts = vec![
            StatementTmpl {
                pred_or_wc: pred_lit(Predicate::Native(NativePredicate::SignedBy)),
                args: vec![sta_wc_lit("attestation_dict", 2), sta_wc_lit("src", 0)],
            },
            StatementTmpl {
                pred_or_wc: pred_lit(Predicate::Native(NativePredicate::Equal)),
                args: vec![
                    sta_ak(("attestation_dict", 2), "attestation"),
                    sta_wc_lit("dst", 1), // Pub arg 1
                ],
            },
        ];
        let expected_friend_pred = CustomPredicate::new(
            &params,
            "eth_friend".to_string(),
            true, // AND
            expected_friend_stmts,
            2, // public_args_len: src, dst
            names(&["src", "dst", "attestation_dict"]),
        )?;

        // eth_dos_distance_base (Index 1)
        let expected_base_stmts = vec![
            StatementTmpl {
                pred_or_wc: pred_lit(Predicate::Native(NativePredicate::Equal)),
                args: vec![sta_wc_lit("src", 0), sta_wc_lit("dst", 1)],
            },
            StatementTmpl {
                pred_or_wc: pred_lit(Predicate::Native(NativePredicate::Equal)),
                args: vec![sta_wc_lit("distance", 2), sta_lit(0i64)],
            },
        ];
        let expected_base_pred = CustomPredicate::new(
            &params,
            "eth_dos_distance_base".to_string(),
            true, // AND
            expected_base_stmts,
            3, // public_args_len
            names(&["src", "dst", "distance"]),
        )?;

        // eth_dos_distance_ind (Index 2)
        // Public args indices: 0-2
        // Private args indices: 3-4 (shorter_distance, intermed)
        let expected_ind_stmts = vec![
            StatementTmpl {
                pred_or_wc: pred_lit(Predicate::BatchSelf(3)), // Calls eth_dos_distance (index 3)
                args: vec![
                    // WildcardLiteral args
                    sta_wc_lit("src", 0),
                    sta_wc_lit("dst", 1),      // private arg
                    sta_wc_lit("distance", 2), // private arg
                ],
            },
            StatementTmpl {
                pred_or_wc: pred_lit(Predicate::Native(NativePredicate::SumOf)),
                args: vec![
                    sta_wc_lit("distance", 2),         // public arg
                    sta_wc_lit("shorter_distance", 3), // private arg
                    sta_lit(1),
                ],
            },
            StatementTmpl {
                pred_or_wc: pred_lit(Predicate::BatchSelf(0)), // Calls eth_friend (index 0)
                args: vec![
                    // WildcardLiteral args
                    sta_wc_lit("intermed", 4), // private arg
                    sta_wc_lit("dst", 1),      // public arg
                ],
            },
        ];
        let expected_ind_pred = CustomPredicate::new(
            &params,
            "eth_dos_distance_ind".to_string(),
            true, // AND
            expected_ind_stmts,
            3, // public_args_len
            names(&["src", "dst", "distance", "shorter_distance", "intermed"]),
        )?;

        // eth_dos_distance (Index 3)
        let expected_dist_stmts = vec![
            StatementTmpl {
                pred_or_wc: pred_lit(Predicate::BatchSelf(1)), // Calls eth_dos_distance_base (index 1)
                args: vec![
                    // WildcardLiteral args
                    sta_wc_lit("src", 0),
                    sta_wc_lit("dst", 1),
                    sta_wc_lit("distance", 2),
                ],
            },
            StatementTmpl {
                pred_or_wc: pred_lit(Predicate::BatchSelf(2)), // Calls eth_dos_distance_ind (index 2)
                args: vec![
                    // WildcardLiteral args
                    sta_wc_lit("src", 0),
                    sta_wc_lit("dst", 1),
                    sta_wc_lit("distance", 2),
                ],
            },
        ];
        let expected_dist_pred = CustomPredicate::new(
            &params,
            "eth_dos_distance".to_string(),
            false, // OR
            expected_dist_stmts,
            3, // public_args_len
            names(&["src", "dst", "distance"]),
        )?;

        let expected_batch = CustomPredicateBatch::new(
            "ethdos".to_string(),
            vec![
                expected_friend_pred,
                expected_base_pred,
                expected_ind_pred,
                expected_dist_pred,
            ],
        );

        assert_eq!(
            &*module.batch, &*expected_batch,
            "Processed ETHDoS predicates do not match expected structure"
        );

        Ok(())
    }

    #[test]
    fn test_e2e_use_module_statement() -> Result<(), LangError> {
        let params = Params::default();

        // 1. Create a module with a predicate to be imported
        let imported_pred_stmts = vec![StatementTmpl {
            pred_or_wc: pred_lit(Predicate::Native(NativePredicate::Equal)),
            args: vec![
                sta_ak(("A", 0), "foo"), // A["foo"]
                sta_ak(("B", 1), "bar"), // B["bar"]
            ],
        }];
        let imported_predicate = CustomPredicate::and(
            &params,
            "imported_equal".to_string(),
            imported_pred_stmts,
            2,
            names(&["A", "B"]),
        )?;
        let batch = CustomPredicateBatch::new("my_module".to_string(), vec![imported_predicate]);
        let module = Arc::new(Module::new(batch.clone(), HashMap::new()));
        let module_hash = module.id().encode_hex::<String>();

        // 2. Create the input string that uses the module
        let input = format!(
            r#"
            use module 0x{} as my_module

            REQUEST(
                my_module::imported_equal(Pod1, Pod2)
            )
        "#,
            module_hash
        );

        // 3. Parse the request
        let request = parse_request(&input, &params, std::slice::from_ref(&module))?;
        let request_templates = request.templates();

        assert_eq!(request_templates.len(), 1, "Expected one request template");

        // 4. Check the resulting request template uses the imported predicate
        let template = &request_templates[0];
        assert_eq!(template.args.len(), 2);

        Ok(())
    }

    #[test]
    fn test_e2e_use_module_complex() -> Result<(), LangError> {
        let params = Params::default();

        // 1. Create a module with multiple predicates
        let pred1 = CustomPredicate::and(&params, "p1".into(), vec![], 1, names(&["A"]))?;
        let pred2 = CustomPredicate::and(&params, "p2".into(), vec![], 2, names(&["B", "C"]))?;
        let pred3 = CustomPredicate::and(&params, "p3".into(), vec![], 1, names(&["D"]))?;

        let batch = CustomPredicateBatch::new("mymodule".to_string(), vec![pred1, pred2, pred3]);
        let mymodule = Arc::new(Module::new(batch.clone(), HashMap::new()));
        let module_hash = mymodule.id().encode_hex::<String>();

        // 2. Create the input string that uses qualified predicate access
        let input = format!(
            r#"
            use module 0x{} as mymodule

            REQUEST(
                mymodule::p1(Pod1)
                mymodule::p3(Pod2)
            )
        "#,
            module_hash
        );

        // 3. Parse the request
        let request = parse_request(&input, &params, std::slice::from_ref(&mymodule))?;
        let request_templates = request.templates();

        assert_eq!(request_templates.len(), 2, "Expected two request templates");

        // 4. Check the resulting request templates
        let expected_templates = vec![
            StatementTmpl {
                pred_or_wc: pred_lit(Predicate::Custom(CustomPredicateRef::new(batch.clone(), 0))),
                args: vec![StatementTmplArg::Wildcard(wc("Pod1", 0))],
            },
            StatementTmpl {
                pred_or_wc: pred_lit(Predicate::Custom(CustomPredicateRef::new(batch, 2))),
                args: vec![StatementTmplArg::Wildcard(wc("Pod2", 1))],
            },
        ];

        assert_eq!(request_templates, expected_templates);

        Ok(())
    }

    #[test]
    fn test_e2e_custom_predicate_uses_module() -> Result<(), LangError> {
        let params = Params::default();

        // 1. Create a module with a predicate to be imported
        let imported_pred_stmts = vec![StatementTmpl {
            pred_or_wc: pred_lit(Predicate::Native(NativePredicate::Equal)),
            args: vec![sta_ak(("A", 0), "foo"), sta_ak(("B", 1), "bar")],
        }];
        let imported_predicate = CustomPredicate::and(
            &params,
            "imported_equal".to_string(),
            imported_pred_stmts,
            2,
            names(&["A", "B"]),
        )?;
        let batch = CustomPredicateBatch::new("extmod".to_string(), vec![imported_predicate]);
        let extmod = Arc::new(Module::new(batch.clone(), HashMap::new()));
        let extmod_hash = extmod.id().encode_hex::<String>();

        // 2. Create the input string that defines a new predicate using the imported one
        let input = format!(
            r#"
            use module 0x{} as extmod

            wrapper_pred(X, Y) = AND(
                extmod::imported_equal(X, Y)
            )
        "#,
            extmod_hash
        );

        // 3. Load as module
        let module = load_module(&input, "test", &params, vec![extmod])?;

        assert_eq!(
            module.batch.predicates().len(),
            1,
            "Expected one custom predicate to be defined"
        );

        // 4. Check the resulting predicate definition
        let defined_pred = &module.batch.predicates()[0];
        assert_eq!(defined_pred.name, "wrapper_pred");
        assert_eq!(defined_pred.statements.len(), 1);

        let expected_statement = StatementTmpl {
            pred_or_wc: pred_lit(Predicate::Custom(CustomPredicateRef::new(batch, 0))),
            args: vec![
                StatementTmplArg::Wildcard(wc("X", 0)),
                StatementTmplArg::Wildcard(wc("Y", 1)),
            ],
        };

        assert_eq!(defined_pred.statements[0], expected_statement);

        Ok(())
    }

    #[test]
    fn test_e2e_intro_import_parsing() -> Result<(), LangError> {
        let params = Params::default();

        let intro_hash = EMPTY_HASH.encode_hex::<String>();
        let input = format!(
            r#"
            use intro empty() from 0x{intro_hash}

            REQUEST(
                empty()
            )
        "#,
        );

        let request = parse_request(&input, &params, &[])?;
        let request_templates = request.templates();
        assert_eq!(request_templates.len(), 1);

        if let PredicateOrWildcard::Predicate(Predicate::Intro(intro_ref)) =
            &request_templates[0].pred_or_wc
        {
            assert_eq!(intro_ref.name, "empty");
            assert_eq!(intro_ref.args_len, 0);
            assert_eq!(intro_ref.verifier_data_hash, EMPTY_HASH);
        } else {
            panic!("Expected Intro predicate");
        }

        assert!(request_templates[0].args.is_empty());

        Ok(())
    }

    #[test]
    fn test_e2e_literals() -> Result<(), LangError> {
        let pk = crate::backends::plonky2::primitives::ec::curve::Point::generator();
        let raw = RawValue::from(1);
        let string = "hello";
        let int = 123;
        let bool = true;
        let sk = SecretKey::new_rand();

        let input = format!(
            r#"
            REQUEST(
                Equal(A["pk"], {})
                Equal(B["raw"], {})
                Equal(C["string"], {})
                Equal(D["int"], {})
                Equal(E["bool"], {})
                Equal(F["sk"], {})
            )
        "#,
            Value::from(pk).to_podlang_string(),
            Value::from(raw).to_podlang_string(),
            Value::from(string).to_podlang_string(),
            Value::from(int).to_podlang_string(),
            Value::from(bool).to_podlang_string(),
            Value::from(sk.clone()).to_podlang_string()
        );
        /*
            REQUEST(
                Equal(A["pk"], PublicKey(3t9fNuU194n7mSJPRdeaJRMqw6ZQCUddzvECWNe1k2b1rdBezXpJxF))
                Equal(C["raw"], Raw(0x0000000000000000000000000000000000000000000000000000000000000001))
                Equal(D["string"], "hello")
                Equal(E["int"], 123)
                Equal(F["bool"], true)
                Equal(G["sk"], SecretKey(random_secret_key_base_64))
                Equal(H["self"], SELF)
            )
        */

        let params = Params::default();
        let request = parse_request(&input, &params, &[])?;
        let request_templates = request.templates();

        let expected_templates = vec![
            StatementTmpl {
                pred_or_wc: pred_lit(Predicate::Native(NativePredicate::Equal)),
                args: vec![sta_ak(("A", 0), "pk"), sta_lit(Value::from(pk))],
            },
            StatementTmpl {
                pred_or_wc: pred_lit(Predicate::Native(NativePredicate::Equal)),
                args: vec![sta_ak(("B", 1), "raw"), sta_lit(Value::from(raw))],
            },
            StatementTmpl {
                pred_or_wc: pred_lit(Predicate::Native(NativePredicate::Equal)),
                args: vec![sta_ak(("C", 2), "string"), sta_lit(Value::from(string))],
            },
            StatementTmpl {
                pred_or_wc: pred_lit(Predicate::Native(NativePredicate::Equal)),
                args: vec![sta_ak(("D", 3), "int"), sta_lit(Value::from(int))],
            },
            StatementTmpl {
                pred_or_wc: pred_lit(Predicate::Native(NativePredicate::Equal)),
                args: vec![sta_ak(("E", 4), "bool"), sta_lit(Value::from(bool))],
            },
            StatementTmpl {
                pred_or_wc: pred_lit(Predicate::Native(NativePredicate::Equal)),
                args: vec![sta_ak(("F", 5), "sk"), sta_lit(Value::from(sk))],
            },
        ];

        assert_eq!(request_templates, expected_templates);

        Ok(())
    }

    #[test]
    fn test_e2e_use_unknown_module() {
        let params = Params::default();

        // Use a hash that doesn't correspond to any loaded module
        let fake_hash = EMPTY_HASH.encode_hex::<String>();
        let input = format!(
            r#"
            use module 0x{} as unknown_module

            REQUEST(
                Equal(A["x"], 1)
            )
            "#,
            fake_hash
        );

        let result = parse_request(&input, &params, &[]);

        assert!(result.is_err());

        match result.err().unwrap().kind {
            LangErrorKind::Validation(e) => match *e {
                frontend_ast_validate::ValidationError::ModuleNotFound { name, .. } => {
                    // The error now carries the hex-formatted hash
                    assert_eq!(name, fake_hash);
                }
                _ => panic!("Expected ModuleNotFound error, but got {:?}", e),
            },
            e => panic!("Expected LangError::Validation, but got {:?}", e),
        }
    }

    #[test]
    fn test_e2e_undefined_wildcard() {
        let params = Params::default();

        let input = r#"
            identity_verified(username, private: identity_dict) = AND(
                Equal(identity_dict["username"], username)
                Equal(identity_dict["user_public_key"], user_public_key)
            )
        "#;

        let result = load_module(input, "test", &params, vec![]);

        assert!(result.is_err());

        match result.err().unwrap().kind {
            LangErrorKind::Validation(e) => match *e {
                frontend_ast_validate::ValidationError::UndefinedWildcard {
                    name,
                    pred_name,
                    ..
                } => {
                    assert_eq!(name, "user_public_key");
                    assert_eq!(pred_name, "identity_verified");
                }
                _ => panic!("Expected UndefinedWildcard error, but got {:?}", e),
            },
            e => panic!("Expected LangError::Validation, but got {:?}", e),
        }
    }
}
