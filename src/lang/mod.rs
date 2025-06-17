pub mod error;
pub mod parser;
pub mod processor;

use std::sync::Arc;

pub use error::LangError;
pub use parser::{parse_podlang, Pairs, ParseError, Rule};
pub use processor::process_pest_tree;
use processor::PodlangOutput;

use crate::middleware::{CustomPredicateBatch, Params};

pub fn parse(
    input: &str,
    params: &Params,
    available_batches: &[Arc<CustomPredicateBatch>],
) -> Result<PodlangOutput, LangError> {
    let pairs = parse_podlang(input)?;
    processor::process_pest_tree(pairs, params, available_batches).map_err(LangError::from)
}

#[cfg(test)]
mod tests {
    use hex::ToHex;
    use pretty_assertions::assert_eq;

    use super::*;
    use crate::{
        lang::error::ProcessorError,
        middleware::{
            CustomPredicate, CustomPredicateBatch, CustomPredicateRef, Key, NativePredicate,
            Params, PodType, Predicate, StatementTmpl, StatementTmplArg, Value, Wildcard,
            SELF_ID_HASH,
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

    #[test]
    fn test_e2e_simple_predicate() -> Result<(), LangError> {
        let input = r#"
            is_equal(PodA, PodB) = AND(
                Equal(?PodA["the_key"], ?PodB["the_key"])
            )
        "#;

        let params = Params::default();
        let processed = parse(input, &params, &[])?;
        let batch_result = processed.custom_batch;
        let request_result = processed.request_templates;

        assert_eq!(request_result.len(), 0);
        assert_eq!(batch_result.predicates.len(), 1);

        let batch = batch_result;

        // Expected structure
        let expected_statements = vec![StatementTmpl {
            pred: Predicate::Native(NativePredicate::Equal),
            args: vec![
                sta_ak(("PodA", 0), "the_key"), // ?PodA["the_key"] -> Wildcard(0), Key("the_key")
                sta_ak(("PodB", 1), "the_key"), // ?PodB["the_key"] -> Wildcard(1), Key("the_key")
            ],
        }];
        let expected_predicate = CustomPredicate::and(
            &params,
            "is_equal".to_string(),
            expected_statements,
            2, // args_len (PodA, PodB)
            names(&["PodA", "PodB"]),
        )?;
        let expected_batch = CustomPredicateBatch::new(
            &params,
            "PodlangBatch".to_string(),
            vec![expected_predicate],
        );

        assert_eq!(batch, expected_batch);

        Ok(())
    }

    #[test]
    fn test_e2e_simple_request() -> Result<(), LangError> {
        let input = r#"
            REQUEST(
                Equal(?ConstPod["my_val"], 0x0000000000000000000000000000000000000000000000000000000000000001)
                Lt(?GovPod["dob"], ?ConstPod["my_val"])
            )
        "#;

        let params = Params::default();
        let processed = parse(input, &params, &[])?;
        let batch_result = processed.custom_batch;
        let request_templates = processed.request_templates;

        assert_eq!(batch_result.predicates.len(), 0);
        assert!(!request_templates.is_empty());

        let request_templates = request_templates;

        // Expected structure
        let expected_templates = vec![
            StatementTmpl {
                pred: Predicate::Native(NativePredicate::Equal),
                args: vec![
                    sta_ak(("ConstPod", 0), "my_val"), // ?ConstPod["my_val"] -> Wildcard(0), Key("my_val")
                    sta_lit(SELF_ID_HASH),
                ],
            },
            StatementTmpl {
                pred: Predicate::Native(NativePredicate::Lt),
                args: vec![
                    sta_ak(("GovPod", 1), "dob"), // ?GovPod["dob"] -> Wildcard(1), Key("dob")
                    sta_ak(("ConstPod", 0), "my_val"), // ?ConstPod["my_val"] -> Wildcard(0), Key("my_val")
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
                Equal(?A["input_key"], ?Temp["const_key"])
                Equal(?Temp["const_key"], "some_value")
            )
        "#;

        let params = Params::default();
        let processed = parse(input, &params, &[])?;
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
                    sta_ak(("A", 0), "input_key"), // ?A["input_key"] -> Wildcard(0), Key("input_key")
                    sta_ak(("Temp", 1), "const_key"), // ?Temp["const_key"] -> Wildcard(1), Key("const_key")
                ],
            },
            StatementTmpl {
                pred: Predicate::Native(NativePredicate::Equal),
                args: vec![
                    sta_ak(("Temp", 1), "const_key"), // ?Temp["const_key"] -> Wildcard(1), Key("const_key")
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
        let expected_batch = CustomPredicateBatch::new(
            &params,
            "PodlangBatch".to_string(),
            vec![expected_predicate],
        );

        assert_eq!(batch, expected_batch);

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
        let processed = parse(input, &params, &[])?;
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
                sta_ak(("X", 0), "val"), // ?X["val"] -> Wildcard(0), Key("val")
                sta_ak(("Y", 1), "val"), // ?Y["val"] -> Wildcard(1), Key("val")
            ],
        }];
        let expected_predicate = CustomPredicate::and(
            &params,
            "my_pred".to_string(),
            expected_pred_statements,
            2, // args_len (X, Y)
            names(&["X", "Y"]),
        )?;
        let expected_batch = CustomPredicateBatch::new(
            &params,
            "PodlangBatch".to_string(),
            vec![expected_predicate],
        );

        assert_eq!(batch, expected_batch);

        // Expected Request structure
        // Pod1 -> Wildcard 0, Pod2 -> Wildcard 1
        let expected_request_templates = vec![StatementTmpl {
            pred: Predicate::Custom(CustomPredicateRef::new(expected_batch, 0)),
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
        let input = r#"
            some_pred(A, B, C) = AND( Equal(?A["foo"], ?B["bar"]) )

            REQUEST(
                some_pred(
                    ?Var1,                  // Wildcard
                    12345,                  // Int Literal
                    "hello_string"         // String Literal (Removed invalid AK args)
                )
                Equal(?AnotherPod["another_key"], ?Var1["some_field"])
            )
        "#;

        let params = Params::default();
        let processed = parse(input, &params, &[])?;
        let batch_result = processed.custom_batch;
        let request_templates = processed.request_templates;

        assert_eq!(batch_result.predicates.len(), 1); // some_pred is defined
        assert!(!request_templates.is_empty());

        let request_templates = request_templates;

        // Expected Wildcard Indices in Request Scope:
        // ?Var1 -> 0
        // ?AnotherPod -> 1

        // Expected structure
        let expected_templates = vec![
            StatementTmpl {
                pred: Predicate::Custom(CustomPredicateRef::new(batch_result, 0)), // Refers to some_pred
                args: vec![
                    StatementTmplArg::Wildcard(wc("Var1", 0)),        // ?Var1
                    StatementTmplArg::Literal(Value::from(12345i64)), // 12345
                    StatementTmplArg::Literal(Value::from("hello_string")), // "hello_string"
                ],
            },
            StatementTmpl {
                pred: Predicate::Native(NativePredicate::Equal),
                args: vec![
                    // ?AnotherPod["another_key"] -> Wildcard(1), Key("another_key")
                    sta_ak(("AnotherPod", 1), "another_key"),
                    // ?Var1["some_field"] -> Wildcard(0), Key("some_field")
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
                GtEq(?A["foo"], ?B["bar"])
                Gt(?C["baz"], ?D["qux"])
                DictContains(?A["foo"], ?B["bar"], ?C["baz"])
                DictNotContains(?A["foo"], ?B["bar"])
                ArrayContains(?A["foo"], ?B["bar"], ?C["baz"])
            )
        "#;

        let params = Params::default();
        let processed = parse(input, &params, &[])?;
        let batch_result = processed.custom_batch;
        let request_templates = processed.request_templates;

        assert_eq!(batch_result.predicates.len(), 0);
        assert!(!request_templates.is_empty());

        let request_templates = request_templates;

        let expected_templates = vec![
            StatementTmpl {
                pred: Predicate::Native(NativePredicate::LtEq),
                args: vec![sta_ak(("B", 1), "bar"), sta_ak(("A", 0), "foo")],
            },
            StatementTmpl {
                pred: Predicate::Native(NativePredicate::Lt),
                args: vec![sta_ak(("D", 3), "qux"), sta_ak(("C", 2), "baz")],
            },
            StatementTmpl {
                pred: Predicate::Native(NativePredicate::Contains),
                args: vec![
                    sta_ak(("A", 0), "foo"),
                    sta_ak(("B", 1), "bar"),
                    sta_ak(("C", 2), "baz"),
                ],
            },
            StatementTmpl {
                pred: Predicate::Native(NativePredicate::NotContains),
                args: vec![sta_ak(("A", 0), "foo"), sta_ak(("B", 1), "bar")],
            },
            StatementTmpl {
                pred: Predicate::Native(NativePredicate::Contains),
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
                SetNotContains(?sanctions["sanctionList"], ?gov["idNumber"])
                Lt(?gov["dateOfBirth"], ?SELF_HOLDER_18Y["const_18y"])
                Equal(?pay["startDate"], ?SELF_HOLDER_1Y["const_1y"])
                Equal(?gov["socialSecurityNumber"], ?pay["socialSecurityNumber"])
                Equal(?SELF_HOLDER_18Y["const_18y"], 1169909388)
                Equal(?SELF_HOLDER_1Y["const_1y"], 1706367566)
            )
        "#;

        // Parse the input string
        let processed = super::parse(input, &Params::default(), &[])?;
        let parsed_templates = processed.request_templates;

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
            // 1. NotContains(?sanctions["sanctionList"], ?gov["idNumber"])
            StatementTmpl {
                pred: Predicate::Native(NativePredicate::NotContains),
                args: vec![
                    sta_ak(
                        (wc_sanctions.name.as_str(), wc_sanctions.index),
                        sanction_list_key,
                    ),
                    sta_ak((wc_gov.name.as_str(), wc_gov.index), id_num_key),
                ],
            },
            // 2. Lt(?gov["dateOfBirth"], ?SELF_HOLDER_18Y["const_18y"])
            StatementTmpl {
                pred: Predicate::Native(NativePredicate::Lt),
                args: vec![
                    sta_ak((wc_gov.name.as_str(), wc_gov.index), dob_key),
                    sta_ak(
                        (wc_self_18y.name.as_str(), wc_self_18y.index),
                        const_18y_key,
                    ),
                ],
            },
            // 3. Equal(?pay["startDate"], ?SELF_HOLDER_1Y["const_1y"])
            StatementTmpl {
                pred: Predicate::Native(NativePredicate::Equal),
                args: vec![
                    sta_ak((wc_pay.name.as_str(), wc_pay.index), start_date_key),
                    sta_ak((wc_self_1y.name.as_str(), wc_self_1y.index), const_1y_key),
                ],
            },
            // 4. Equal(?gov["socialSecurityNumber"], ?pay["socialSecurityNumber"])
            StatementTmpl {
                pred: Predicate::Native(NativePredicate::Equal),
                args: vec![
                    sta_ak((wc_gov.name.as_str(), wc_gov.index), ssn_key),
                    sta_ak((wc_pay.name.as_str(), wc_pay.index), ssn_key),
                ],
            },
            // 5. Equal(?SELF_HOLDER_18Y["const_18y"], 1169909388)
            StatementTmpl {
                pred: Predicate::Native(NativePredicate::Equal),
                args: vec![
                    sta_ak(
                        (wc_self_18y.name.as_str(), wc_self_18y.index),
                        const_18y_key,
                    ),
                    sta_lit(now_minus_18y_val.clone()),
                ],
            },
            // 6. Equal(?SELF_HOLDER_1Y["const_1y"], 1706367566)
            StatementTmpl {
                pred: Predicate::Native(NativePredicate::Equal),
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

        assert!(
            processed.custom_batch.predicates.is_empty(),
            "Expected no custom predicates for a REQUEST only input"
        );

        Ok(())
    }

    #[test]
    fn test_e2e_ethdos_predicates() -> Result<(), LangError> {
        let params = Params {
            max_input_signed_pods: 3,
            max_input_recursive_pods: 3,
            max_statements: 31,
            max_signed_pod_values: 8,
            max_public_statements: 10,
            max_statement_args: 6,
            max_operation_args: 5,
            max_custom_predicate_arity: 5,
            max_custom_batch_size: 5,
            max_custom_predicate_wildcards: 12,
            ..Default::default()
        };

        let input = r#"
            eth_friend(src, dst, private: attestation_pod) = AND(
                Equal(?attestation_pod["_type"], 1)
                Equal(?attestation_pod["_signer"], ?src)
                Equal(?attestation_pod["attestation"], ?dst)
            )

            eth_dos_distance_base(src, dst, distance) = AND(
                Equal(?src, ?dst)
                Equal(?distance, 0)
            )

            eth_dos_distance_ind(src, dst, distance, private: shorter_distance, intermed) = AND(
                eth_dos_distance(?src, ?dst, ?distance)
                SumOf(?distance, ?shorter_distance, 1)
                eth_friend(?intermed, ?dst)
            )

            eth_dos_distance(src, dst, distance) = OR(
                eth_dos_distance_base(?src, ?dst, ?distance)
                eth_dos_distance_ind(?src, ?dst, ?distance)
            )
        "#;

        let processed = super::parse(input, &params, &[])?;

        assert!(
            processed.request_templates.is_empty(),
            "Expected no request templates"
        );
        assert_eq!(
            processed.custom_batch.predicates.len(),
            4,
            "Expected 4 custom predicates"
        );

        // Predicate Order: eth_friend (0), base (1), ind (2), distance (3)

        // eth_friend (Index 0)
        let expected_friend_stmts = vec![
            StatementTmpl {
                pred: Predicate::Native(NativePredicate::Equal),
                args: vec![
                    sta_ak(("attestation_pod", 2), "_type"), // Pub(0-1), Priv(2)
                    sta_lit(PodType::MockSigned),
                ],
            },
            StatementTmpl {
                pred: Predicate::Native(NativePredicate::Equal),
                args: vec![
                    sta_ak(("attestation_pod", 2), "_signer"),
                    sta_wc_lit("src", 0), // Pub arg 0
                ],
            },
            StatementTmpl {
                pred: Predicate::Native(NativePredicate::Equal),
                args: vec![
                    sta_ak(("attestation_pod", 2), "attestation"),
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
            names(&["src", "dst", "attestation_pod"]),
        )?;

        // eth_dos_distance_base (Index 1)
        let expected_base_stmts = vec![
            StatementTmpl {
                pred: Predicate::Native(NativePredicate::Equal),
                args: vec![sta_wc_lit("src", 0), sta_wc_lit("dst", 1)],
            },
            StatementTmpl {
                pred: Predicate::Native(NativePredicate::Equal),
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
                pred: Predicate::BatchSelf(3), // Calls eth_dos_distance (index 3)
                args: vec![
                    // WildcardLiteral args
                    sta_wc_lit("src", 0),
                    sta_wc_lit("dst", 1),      // private arg
                    sta_wc_lit("distance", 2), // private arg
                ],
            },
            StatementTmpl {
                pred: Predicate::Native(NativePredicate::SumOf),
                args: vec![
                    sta_wc_lit("distance", 2),         // public arg
                    sta_wc_lit("shorter_distance", 3), // private arg
                    sta_lit(1),
                ],
            },
            StatementTmpl {
                pred: Predicate::BatchSelf(0), // Calls eth_friend (index 0)
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
                pred: Predicate::BatchSelf(1), // Calls eth_dos_distance_base (index 1)
                args: vec![
                    // WildcardLiteral args
                    sta_wc_lit("src", 0),
                    sta_wc_lit("dst", 1),
                    sta_wc_lit("distance", 2),
                ],
            },
            StatementTmpl {
                pred: Predicate::BatchSelf(2), // Calls eth_dos_distance_ind (index 2)
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
            &params,
            "PodlangBatch".to_string(),
            vec![
                expected_friend_pred,
                expected_base_pred,
                expected_ind_pred,
                expected_dist_pred,
            ],
        );

        assert_eq!(
            processed.custom_batch, expected_batch,
            "Processed ETHDoS predicates do not match expected structure"
        );

        Ok(())
    }

    #[test]
    fn test_e2e_use_statement() -> Result<(), LangError> {
        let params = Params::default();

        // 1. Create a batch to be imported
        let imported_pred_stmts = vec![StatementTmpl {
            pred: Predicate::Native(NativePredicate::Equal),
            args: vec![
                sta_ak(("A", 0), "foo"), // ?A["foo"]
                sta_ak(("B", 1), "bar"), // ?B["bar"]
            ],
        }];
        let imported_predicate = CustomPredicate::and(
            &params,
            "imported_equal".to_string(),
            imported_pred_stmts,
            2,
            names(&["A", "B"]),
        )?;
        let available_batch =
            CustomPredicateBatch::new(&params, "MyBatch".to_string(), vec![imported_predicate]);
        let available_batches = vec![available_batch.clone()];

        // 2. Create the input string that uses the batch
        let batch_id_str = available_batch.id().encode_hex::<String>();
        let input = format!(
            r#"
            use imported_pred from 0x{}

            REQUEST(
                imported_pred(?Pod1, ?Pod2)
            )
        "#,
            batch_id_str
        );

        // 3. Parse the input
        let processed = parse(&input, &params, &available_batches)?;
        let request_templates = processed.request_templates;

        assert!(
            processed.custom_batch.predicates.is_empty(),
            "No custom predicates should be defined in the main input"
        );
        assert_eq!(request_templates.len(), 1, "Expected one request template");

        // 4. Check the resulting request template
        let expected_request_templates = vec![StatementTmpl {
            pred: Predicate::Custom(CustomPredicateRef::new(available_batch, 0)),
            args: vec![
                StatementTmplArg::Wildcard(wc("Pod1", 0)),
                StatementTmplArg::Wildcard(wc("Pod2", 1)),
            ],
        }];

        assert_eq!(request_templates, expected_request_templates);

        Ok(())
    }

    #[test]
    fn test_e2e_use_statement_complex() -> Result<(), LangError> {
        let params = Params::default();

        // 1. Create a batch with multiple predicates
        let pred1 = CustomPredicate::and(&params, "p1".into(), vec![], 1, names(&["A"]))?;
        let pred2 = CustomPredicate::and(&params, "p2".into(), vec![], 2, names(&["B", "C"]))?;
        let pred3 = CustomPredicate::and(&params, "p3".into(), vec![], 1, names(&["D"]))?;

        let available_batch =
            CustomPredicateBatch::new(&params, "MyBatch".to_string(), vec![pred1, pred2, pred3]);
        let available_batches = vec![available_batch.clone()];

        // 2. Create the input string that uses the batch with skips
        let batch_id_str = available_batch.id().encode_hex::<String>();

        let input = format!(
            r#"
            use pred_one, _, pred_three from 0x{}

            REQUEST(
                pred_one(?Pod1)
                pred_three(?Pod2)
            )
        "#,
            batch_id_str
        );

        // 3. Parse the input
        let processed = parse(&input, &params, &available_batches)?;
        let request_templates = processed.request_templates;

        assert_eq!(request_templates.len(), 2, "Expected two request templates");

        // 4. Check the resulting request templates
        let expected_templates = vec![
            StatementTmpl {
                pred: Predicate::Custom(CustomPredicateRef::new(available_batch.clone(), 0)),
                args: vec![StatementTmplArg::Wildcard(wc("Pod1", 0))],
            },
            StatementTmpl {
                pred: Predicate::Custom(CustomPredicateRef::new(available_batch, 2)),
                args: vec![StatementTmplArg::Wildcard(wc("Pod2", 1))],
            },
        ];

        assert_eq!(request_templates, expected_templates);

        Ok(())
    }

    #[test]
    fn test_e2e_custom_predicate_uses_import() -> Result<(), LangError> {
        let params = Params::default();

        // 1. Create a batch with a predicate to be imported
        let imported_pred_stmts = vec![StatementTmpl {
            pred: Predicate::Native(NativePredicate::Equal),
            args: vec![sta_ak(("A", 0), "foo"), sta_ak(("B", 1), "bar")],
        }];
        let imported_predicate = CustomPredicate::and(
            &params,
            "imported_equal".to_string(),
            imported_pred_stmts,
            2,
            names(&["A", "B"]),
        )?;
        let available_batch =
            CustomPredicateBatch::new(&params, "MyBatch".to_string(), vec![imported_predicate]);
        let available_batches = vec![available_batch.clone()];

        // 2. Create the input string that defines a new predicate using the imported one
        let batch_id_str = available_batch.id().encode_hex::<String>();

        let input = format!(
            r#"
            use imported_eq from 0x{}

            wrapper_pred(X, Y) = AND(
                imported_eq(?X, ?Y)
            )
        "#,
            batch_id_str
        );

        // 3. Parse the input
        let processed = parse(&input, &params, &available_batches)?;

        assert!(
            processed.request_templates.is_empty(),
            "No request should be defined"
        );
        assert_eq!(
            processed.custom_batch.predicates.len(),
            1,
            "Expected one custom predicate to be defined"
        );

        // 4. Check the resulting predicate definition
        let defined_pred = &processed.custom_batch.predicates[0];
        assert_eq!(defined_pred.name, "wrapper_pred");
        assert_eq!(defined_pred.statements.len(), 1);

        let expected_statement = StatementTmpl {
            pred: Predicate::Custom(CustomPredicateRef::new(available_batch.clone(), 0)),
            args: vec![
                StatementTmplArg::Wildcard(wc("X", 0)),
                StatementTmplArg::Wildcard(wc("Y", 1)),
            ],
        };

        assert_eq!(defined_pred.statements[0], expected_statement);

        Ok(())
    }

    #[test]
    fn test_e2e_use_unknown_batch() {
        let params = Params::default();
        let available_batches = &[];

        let unknown_batch_id = format!("0x{}", "a".repeat(64));

        let input = format!(
            r#"
            use some_pred from {}
            "#,
            unknown_batch_id
        );

        let result = parse(&input, &params, available_batches);

        assert!(result.is_err());

        match result.err().unwrap() {
            LangError::Processor(e) => match *e {
                ProcessorError::BatchNotFound { id, .. } => {
                    assert_eq!(id, unknown_batch_id);
                }
                _ => panic!("Expected BatchNotFound error, but got {:?}", e),
            },
            e => panic!("Expected LangError::Processor, but got {:?}", e),
        }
    }
}
