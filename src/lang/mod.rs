pub mod ast;
pub mod error;
pub mod parser;
pub mod processor;

use ast::build_ast;
pub use error::LangError;
pub use parser::{parse_podlog, ParseError};
pub use processor::process_document;
use processor::ProcessedOutput;

use crate::middleware::Params;

pub fn parse(input: &str) -> Result<ProcessedOutput, LangError> {
    let pairs = parse_podlog(input)?;
    let ast = build_ast(pairs)?;
    let processed = process_document(ast, &Params::default())?;
    Ok(processed)
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::{ast::build_ast, *};
    use crate::middleware::{
        CustomPredicate, CustomPredicateBatch, Key, KeyOrWildcard, NativePredicate, Params,
        Predicate, StatementTmpl, StatementTmplArg, Value, Wildcard,
    };

    // Helper to create Wildcard
    fn wc(name: &str, index: usize) -> Wildcard {
        Wildcard::new(name.to_string(), index)
    }

    // Helper to create KeyOrWildcard::Key
    fn k(name: &str) -> KeyOrWildcard {
        KeyOrWildcard::Key(Key::new(name.to_string()))
    }

    // Helper to create KeyOrWildcard::Wildcard
    fn kw(name: &str, index: usize) -> KeyOrWildcard {
        KeyOrWildcard::Wildcard(wc(name, index))
    }

    // Helper to create StatementTmplArg::Key
    fn sta_k(pod_var: (&str, usize), key_or_wc: KeyOrWildcard) -> StatementTmplArg {
        StatementTmplArg::Key(wc(pod_var.0, pod_var.1), key_or_wc)
    }

    // Helper to create StatementTmplArg::Literal
    fn sta_lit(value: impl Into<Value>) -> StatementTmplArg {
        StatementTmplArg::Literal(value.into())
    }

    #[test]
    fn test_e2e_simple_predicate() -> Result<(), LangError> {
        let input = r#"
            // Simple predicate checking equality on a specific key
            is_equal(PodA, PodB) = AND(
                Equal(?PodA["the_key"], ?PodB["the_key"])
            )
        "#;

        let params = Params::default();
        let pairs = parse_podlog(input)?;
        let ast = build_ast(pairs)?;
        let processed = process_document(ast, &params)?;
        let batch_result = processed.custom_batch;
        let request_result = processed.request_templates;

        assert_eq!(request_result.len(), 0);
        assert_eq!(batch_result.predicates.len(), 1);

        let batch = batch_result;

        // Expected structure
        let expected_statements = vec![StatementTmpl {
            pred: Predicate::Native(NativePredicate::Equal),
            args: vec![
                sta_k(("PodA", 0), k("the_key")), // ?PodA["the_key"] -> Wildcard(0), Key("the_key")
                sta_k(("PodB", 1), k("the_key")), // ?PodB["the_key"] -> Wildcard(1), Key("the_key")
            ],
        }];
        let expected_predicate = CustomPredicate::and(
            "is_equal".to_string(),
            &params,
            expected_statements,
            2, // args_len (PodA, PodB)
        )?;
        let expected_batch = Arc::new(CustomPredicateBatch {
            name: "PodlogBatch".to_string(), // Default batch name
            predicates: vec![expected_predicate],
        });

        assert_eq!(batch, expected_batch);

        Ok(())
    }

    #[test]
    fn test_e2e_simple_request() -> Result<(), LangError> {
        let input = r#"
            // Simple request
            REQUEST(
                ValueOf(?ConstPod["my_val"], 123)
                Lt(?GovPod["dob"], ?ConstPod["my_val"])
            )
        "#;

        let params = Params::default();
        let pairs = parse_podlog(input)?;
        let ast = build_ast(pairs)?;
        let processed = process_document(ast, &params)?;
        let batch_result = processed.custom_batch;
        let request_templates = processed.request_templates;

        assert_eq!(batch_result.predicates.len(), 0);
        assert!(!request_templates.is_empty());

        let request_templates = request_templates;

        // Expected structure
        let expected_templates = vec![
            StatementTmpl {
                pred: Predicate::Native(NativePredicate::ValueOf),
                args: vec![
                    sta_k(("ConstPod", 0), k("my_val")), // ?ConstPod["my_val"] -> Wildcard(0), Key("my_val")
                    sta_lit(123i64),                     // Literal(123)
                ],
            },
            StatementTmpl {
                pred: Predicate::Native(NativePredicate::Lt),
                args: vec![
                    sta_k(("GovPod", 1), k("dob")), // ?GovPod["dob"] -> Wildcard(1), Key("dob")
                    sta_k(("ConstPod", 0), k("my_val")), // ?ConstPod["my_val"] -> Wildcard(0), Key("my_val")
                ],
            },
        ];

        assert_eq!(request_templates, expected_templates);

        Ok(())
    }

    #[test]
    fn test_e2e_predicate_with_private_var() -> Result<(), LangError> {
        let input = r#"
            uses_private(A) = AND(
                private(Temp) // Private variable
                Equal(?A["input_key"], ?Temp["const_key"])
                ValueOf(?Temp["const_key"], "some_value")
            )
        "#;

        let params = Params::default();
        let pairs = parse_podlog(input)?;
        let ast = build_ast(pairs)?;
        let processed = process_document(ast, &params)?;
        let batch_result = processed.custom_batch;
        let request_result = processed.request_templates;

        assert_eq!(request_result.len(), 0);
        assert_eq!(batch_result.predicates.len(), 1);

        let batch = batch_result;

        // Expected structure: Public args: A (index 0). Private args: Temp (index 1)
        let expected_statements = vec![
            StatementTmpl {
                pred: Predicate::Native(NativePredicate::Equal),
                args: vec![
                    sta_k(("A", 0), k("input_key")), // ?A["input_key"] -> Wildcard(0), Key("input_key")
                    sta_k(("Temp", 1), k("const_key")), // ?Temp["const_key"] -> Wildcard(1), Key("const_key")
                ],
            },
            StatementTmpl {
                pred: Predicate::Native(NativePredicate::ValueOf),
                args: vec![
                    sta_k(("Temp", 1), k("const_key")), // ?Temp["const_key"] -> Wildcard(1), Key("const_key")
                    sta_lit("some_value"),              // Literal("some_value")
                ],
            },
        ];
        let expected_predicate = CustomPredicate::and(
            "uses_private".to_string(),
            &params,
            expected_statements,
            1, // args_len (A)
        )?;
        let expected_batch = Arc::new(CustomPredicateBatch {
            name: "PodlogBatch".to_string(),
            predicates: vec![expected_predicate],
        });

        assert_eq!(batch, expected_batch);
        // We might also want to check private arg count/order if the AST/processor exposes it,
        // but for now, checking the wildcard indices in the statements suffices.

        Ok(())
    }

    #[test]
    fn test_e2e_request_with_custom_call() -> Result<(), LangError> {
        let input = r#"
            my_pred(X, Y) = AND(
                Equal(?X["val"], ?Y["val"])
            )

            REQUEST(
                my_pred(?Pod1, ?Pod2)
            )
        "#;

        let params = Params::default();
        let pairs = parse_podlog(input)?;
        let ast = build_ast(pairs)?;
        let processed = process_document(ast, &params)?;
        let batch_result = processed.custom_batch;
        let request_templates = processed.request_templates;

        assert_eq!(batch_result.predicates.len(), 1);
        assert!(!request_templates.is_empty());

        let batch = batch_result;
        let request_templates = request_templates;

        // Expected Batch structure
        let expected_pred_statements = vec![StatementTmpl {
            pred: Predicate::Native(NativePredicate::Equal),
            args: vec![
                sta_k(("X", 0), k("val")), // ?X["val"] -> Wildcard(0), Key("val")
                sta_k(("Y", 1), k("val")), // ?Y["val"] -> Wildcard(1), Key("val")
            ],
        }];
        let expected_predicate = CustomPredicate::and(
            "my_pred".to_string(),
            &params,
            expected_pred_statements,
            2, // args_len (X, Y)
        )?;
        let expected_batch = Arc::new(CustomPredicateBatch {
            name: "PodlogBatch".to_string(),
            predicates: vec![expected_predicate],
        });

        assert_eq!(batch, expected_batch);

        // Expected Request structure
        // Pod1 -> Wildcard 0, Pod2 -> Wildcard 1
        let expected_request_templates = vec![StatementTmpl {
            pred: Predicate::BatchSelf(0), // Refers to my_pred within the same batch
            args: vec![
                StatementTmplArg::WildcardLiteral(wc("Pod1", 0)),
                StatementTmplArg::WildcardLiteral(wc("Pod2", 1)),
            ],
        }];

        assert_eq!(request_templates, expected_request_templates);

        Ok(())
    }

    #[test]
    fn test_e2e_request_with_various_args() -> Result<(), LangError> {
        let input = r#"
            some_pred(A, B, C, D, E) = AND() // Dummy predicate body

            REQUEST(
                some_pred(
                    ?Var1,                  // Variable
                    12345,                  // Int Literal
                    "hello_string",         // String Literal
                    ?PodVar["the_key"],     // Anchored Key (Literal Key)
                    ?PodVar[?KeyVar]        // Anchored Key (Variable Key)
                )
                // Check that variable indices are unique across statements
                Equal(?AnotherPod["another_key"], ?Var1["some_field"])
            )
        "#;

        let params = Params::default();
        let pairs = parse_podlog(input)?;
        let ast = build_ast(pairs)?;
        let processed = process_document(ast, &params)?;
        let batch_result = processed.custom_batch;
        let request_templates = processed.request_templates;

        assert_eq!(batch_result.predicates.len(), 1); // some_pred is defined
        assert!(!request_templates.is_empty());

        let request_templates = request_templates;

        // Expected Wildcard Indices in Request Scope:
        // ?Var1 -> 0
        // ?PodVar -> 1
        // ?KeyVar -> 2
        // ?AnotherPod -> 3

        // Expected structure
        let expected_templates = vec![
            StatementTmpl {
                pred: Predicate::BatchSelf(0), // Refers to some_pred
                args: vec![
                    StatementTmplArg::WildcardLiteral(wc("Var1", 0)), // ?Var1
                    StatementTmplArg::Literal(Value::from(12345i64)), // 12345
                    StatementTmplArg::Literal(Value::from("hello_string")), // "hello_string"
                    sta_k(("PodVar", 1), k("the_key")),               // ?PodVar["the_key"]
                    sta_k(("PodVar", 1), kw("KeyVar", 2)),            // ?PodVar[?KeyVar]
                ],
            },
            StatementTmpl {
                pred: Predicate::Native(NativePredicate::Equal),
                args: vec![
                    // ?AnotherPod["another_key"] -> Wildcard(3), Key("another_key")
                    sta_k(("AnotherPod", 3), k("another_key")),
                    // ?Var1["some_field"] -> Wildcard(0), Key("some_field")
                    sta_k(("Var1", 0), k("some_field")),
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
                // Order matters for comparison, match the hardcoded order
                NotContains(?sanctions["sanctionList"], ?gov["idNumber"]) // 1
                Lt(?gov["dateOfBirth"], ?SELF_HOLDER_18Y["const_18y"])       // 2
                Equal(?pay["startDate"], ?SELF_HOLDER_1Y["const_1y"])          // 3
                Equal(?gov["socialSecurityNumber"], ?pay["socialSecurityNumber"]) // 4
                ValueOf(?SELF_HOLDER_18Y["const_18y"], 1169909388)                // 5
                ValueOf(?SELF_HOLDER_1Y["const_1y"], 1706367566)                   // 6
            )
        "#;

        // Parse the input string
        let processed = super::parse(input)?;
        let parsed_templates = processed.request_templates;

        // --- Define Expected Templates (Copied from prover/mod.rs) ---
        // 2. Define constants needed in templates
        let now_minus_18y_val = Value::from(1169909388_i64);
        let now_minus_1y_val = Value::from(1706367566_i64);

        // 3. Define wildcards and keys for the request
        // Note: Indices must match the order of appearance in the *parsed* request
        // Order: sanctions, gov, SELF_HOLDER_18Y, pay, SELF_HOLDER_1Y
        let wc_sanctions = wc("sanctions", 0);
        let wc_gov = wc("gov", 1);
        let wc_self_18y = wc("SELF_HOLDER_18Y", 2);
        let wc_pay = wc("pay", 3);
        let wc_self_1y = wc("SELF_HOLDER_1Y", 4);

        let id_num_key = k("idNumber");
        let dob_key = k("dateOfBirth");
        let const_18y_key = k("const_18y");
        let start_date_key = k("startDate");
        let const_1y_key = k("const_1y");
        let ssn_key = k("socialSecurityNumber");
        let sanction_list_key = k("sanctionList");

        // 4. Define the request templates using wildcards for constants
        // ORDER MUST MATCH THE PARSED INPUT STRING
        let expected_templates = vec![
            // 1. NotContains(?sanctions["sanctionList"], ?gov["idNumber"])
            StatementTmpl {
                pred: Predicate::Native(NativePredicate::NotContains),
                args: vec![
                    sta_k(
                        (wc_sanctions.name.as_str(), wc_sanctions.index),
                        sanction_list_key.clone(),
                    ),
                    sta_k((wc_gov.name.as_str(), wc_gov.index), id_num_key.clone()),
                ],
            },
            // 2. Lt(?gov["dateOfBirth"], ?SELF_HOLDER_18Y["const_18y"])
            StatementTmpl {
                pred: Predicate::Native(NativePredicate::Lt),
                args: vec![
                    sta_k((wc_gov.name.as_str(), wc_gov.index), dob_key.clone()),
                    sta_k(
                        (wc_self_18y.name.as_str(), wc_self_18y.index),
                        const_18y_key.clone(),
                    ),
                ],
            },
            // 3. Equal(?pay["startDate"], ?SELF_HOLDER_1Y["const_1y"])
            StatementTmpl {
                pred: Predicate::Native(NativePredicate::Equal),
                args: vec![
                    sta_k((wc_pay.name.as_str(), wc_pay.index), start_date_key.clone()),
                    sta_k(
                        (wc_self_1y.name.as_str(), wc_self_1y.index),
                        const_1y_key.clone(),
                    ),
                ],
            },
            // 4. Equal(?gov["socialSecurityNumber"], ?pay["socialSecurityNumber"])
            StatementTmpl {
                pred: Predicate::Native(NativePredicate::Equal),
                args: vec![
                    sta_k((wc_gov.name.as_str(), wc_gov.index), ssn_key.clone()),
                    sta_k((wc_pay.name.as_str(), wc_pay.index), ssn_key.clone()),
                ],
            },
            // 5. ValueOf(?SELF_HOLDER_18Y["const_18y"], 1169909388)
            StatementTmpl {
                pred: Predicate::Native(NativePredicate::ValueOf),
                args: vec![
                    sta_k(
                        (wc_self_18y.name.as_str(), wc_self_18y.index),
                        const_18y_key.clone(),
                    ),
                    sta_lit(now_minus_18y_val.clone()),
                ],
            },
            // 6. ValueOf(?SELF_HOLDER_1Y["const_1y"], 1706367566)
            StatementTmpl {
                pred: Predicate::Native(NativePredicate::ValueOf),
                args: vec![
                    sta_k(
                        (wc_self_1y.name.as_str(), wc_self_1y.index),
                        const_1y_key.clone(),
                    ),
                    sta_lit(now_minus_1y_val.clone()),
                ],
            },
        ];

        // Compare parsed templates with expected ones
        assert_eq!(
            parsed_templates, expected_templates,
            "Parsed ZuKYC request templates do not match the expected hard-coded version"
        );

        // Check that no custom predicates were generated
        assert!(
            processed.custom_batch.predicates.is_empty(),
            "Expected no custom predicates for a REQUEST only input"
        );

        Ok(())
    }
}
