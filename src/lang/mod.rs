pub mod error;
pub mod parser;
pub mod processor;

pub use error::LangError;
pub use parser::{parse_podlog, Pairs, ParseError, Rule};
pub use processor::process_pest_tree;
use processor::ProcessedOutput;

use crate::middleware::Params;

pub fn parse(input: &str, params: &Params) -> Result<ProcessedOutput, LangError> {
    let pairs = parse_podlog(input)?;
    processor::process_pest_tree(pairs, params).map_err(LangError::from)
}

#[cfg(test)]
mod tests {

    use pretty_assertions::assert_eq;

    use super::*;
    use crate::middleware::{
        CustomPredicate, CustomPredicateBatch, CustomPredicateRef, Key, KeyOrWildcard,
        NativePredicate, Params, PodType, Predicate, SelfOrWildcard, StatementTmpl,
        StatementTmplArg, Value, Wildcard, SELF_ID_HASH,
    };

    // Helper functions
    fn wc(name: &str, index: usize) -> Wildcard {
        Wildcard::new(name.to_string(), index)
    }

    fn k(name: &str) -> KeyOrWildcard {
        KeyOrWildcard::Key(Key::new(name.to_string()))
    }

    fn ko_wc(name: &str, index: usize) -> KeyOrWildcard {
        KeyOrWildcard::Wildcard(Wildcard::new(name.to_string(), index))
    }

    fn sta_ak(pod_var: (&str, usize), key_or_wc: KeyOrWildcard) -> StatementTmplArg {
        StatementTmplArg::AnchoredKey(
            SelfOrWildcard::Wildcard(wc(pod_var.0, pod_var.1)),
            key_or_wc,
        )
    }

    fn sta_ak_self(key_or_wc: KeyOrWildcard) -> StatementTmplArg {
        StatementTmplArg::AnchoredKey(SelfOrWildcard::SELF, key_or_wc)
    }

    fn sta_lit(value: impl Into<Value>) -> StatementTmplArg {
        StatementTmplArg::Literal(value.into())
    }

    #[test]
    fn test_e2e_simple_predicate() -> Result<(), LangError> {
        let input = r#"
            is_equal(PodA, PodB) = AND(
                Equal(?PodA["the_key"], ?PodB["the_key"])
            )
        "#;

        let params = Params::default();
        let pairs = parse_podlog(input)?;
        let processed = process_pest_tree(pairs, &params)?;
        let batch_result = processed.custom_batch;
        let request_result = processed.request_templates;

        assert_eq!(request_result.len(), 0);
        assert_eq!(batch_result.predicates.len(), 1);

        let batch = batch_result;

        // Expected structure
        let expected_statements = vec![StatementTmpl {
            pred: Predicate::Native(NativePredicate::Equal),
            args: vec![
                sta_ak(("PodA", 0), k("the_key")), // ?PodA["the_key"] -> Wildcard(0), Key("the_key")
                sta_ak(("PodB", 1), k("the_key")), // ?PodB["the_key"] -> Wildcard(1), Key("the_key")
            ],
        }];
        let expected_predicate = CustomPredicate::and(
            &params,
            "is_equal".to_string(),
            expected_statements,
            2, // args_len (PodA, PodB)
        )?;
        let expected_batch =
            CustomPredicateBatch::new(&params, "PodlogBatch".to_string(), vec![expected_predicate]);

        assert_eq!(batch, expected_batch);

        Ok(())
    }

    #[test]
    fn test_e2e_simple_request() -> Result<(), LangError> {
        let input = r#"
            REQUEST(
                ValueOf(?ConstPod["my_val"], 0x0000000000000000000000000000000000000000000000000000000000000001)
                Lt(?GovPod["dob"], ?ConstPod["my_val"])
            )
        "#;

        let params = Params::default();
        let pairs = parse_podlog(input)?;
        let processed = process_pest_tree(pairs, &params)?;
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
                    sta_ak(("ConstPod", 0), k("my_val")), // ?ConstPod["my_val"] -> Wildcard(0), Key("my_val")
                    sta_lit(SELF_ID_HASH),
                ],
            },
            StatementTmpl {
                pred: Predicate::Native(NativePredicate::Lt),
                args: vec![
                    sta_ak(("GovPod", 1), k("dob")), // ?GovPod["dob"] -> Wildcard(1), Key("dob")
                    sta_ak(("ConstPod", 0), k("my_val")), // ?ConstPod["my_val"] -> Wildcard(0), Key("my_val")
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
                ValueOf(?Temp["const_key"], "some_value")
            )
        "#;

        let params = Params::default();
        let pairs = parse_podlog(input)?;
        let processed = process_pest_tree(pairs, &params)?;
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
                    sta_ak(("A", 0), k("input_key")), // ?A["input_key"] -> Wildcard(0), Key("input_key")
                    sta_ak(("Temp", 1), k("const_key")), // ?Temp["const_key"] -> Wildcard(1), Key("const_key")
                ],
            },
            StatementTmpl {
                pred: Predicate::Native(NativePredicate::ValueOf),
                args: vec![
                    sta_ak(("Temp", 1), k("const_key")), // ?Temp["const_key"] -> Wildcard(1), Key("const_key")
                    sta_lit("some_value"),               // Literal("some_value")
                ],
            },
        ];
        let expected_predicate = CustomPredicate::and(
            &params,
            "uses_private".to_string(),
            expected_statements,
            1, // args_len (A)
        )?;
        let expected_batch =
            CustomPredicateBatch::new(&params, "PodlogBatch".to_string(), vec![expected_predicate]);

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
        let pairs = parse_podlog(input)?;
        let processed = process_pest_tree(pairs, &params)?;
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
                sta_ak(("X", 0), k("val")), // ?X["val"] -> Wildcard(0), Key("val")
                sta_ak(("Y", 1), k("val")), // ?Y["val"] -> Wildcard(1), Key("val")
            ],
        }];
        let expected_predicate = CustomPredicate::and(
            &params,
            "my_pred".to_string(),
            expected_pred_statements,
            2, // args_len (X, Y)
        )?;
        let expected_batch =
            CustomPredicateBatch::new(&params, "PodlogBatch".to_string(), vec![expected_predicate]);

        assert_eq!(batch, expected_batch);

        // Expected Request structure
        // Pod1 -> Wildcard 0, Pod2 -> Wildcard 1
        let expected_request_templates = vec![StatementTmpl {
            pred: Predicate::Custom(CustomPredicateRef::new(expected_batch, 0)),
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
        let pairs = parse_podlog(input)?;
        let processed = process_pest_tree(pairs, &params)?;
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
                    StatementTmplArg::WildcardLiteral(wc("Var1", 0)), // ?Var1
                    StatementTmplArg::Literal(Value::from(12345i64)), // 12345
                    StatementTmplArg::Literal(Value::from("hello_string")), // "hello_string"
                ],
            },
            StatementTmpl {
                pred: Predicate::Native(NativePredicate::Equal),
                args: vec![
                    // ?AnotherPod["another_key"] -> Wildcard(1), Key("another_key")
                    sta_ak(("AnotherPod", 1), k("another_key")),
                    // ?Var1["some_field"] -> Wildcard(0), Key("some_field")
                    sta_ak(("Var1", 0), k("some_field")),
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
        let pairs = parse_podlog(input)?;
        let processed = process_pest_tree(pairs, &params)?;
        let batch_result = processed.custom_batch;
        let request_templates = processed.request_templates;

        assert_eq!(batch_result.predicates.len(), 0);
        assert!(!request_templates.is_empty());

        let request_templates = request_templates;

        let expected_templates = vec![
            StatementTmpl {
                pred: Predicate::Native(NativePredicate::LtEq),
                args: vec![sta_ak(("B", 1), k("bar")), sta_ak(("A", 0), k("foo"))],
            },
            StatementTmpl {
                pred: Predicate::Native(NativePredicate::Lt),
                args: vec![sta_ak(("D", 3), k("qux")), sta_ak(("C", 2), k("baz"))],
            },
            StatementTmpl {
                pred: Predicate::Native(NativePredicate::Contains),
                args: vec![
                    sta_ak(("A", 0), k("foo")),
                    sta_ak(("B", 1), k("bar")),
                    sta_ak(("C", 2), k("baz")),
                ],
            },
            StatementTmpl {
                pred: Predicate::Native(NativePredicate::NotContains),
                args: vec![sta_ak(("A", 0), k("foo")), sta_ak(("B", 1), k("bar"))],
            },
            StatementTmpl {
                pred: Predicate::Native(NativePredicate::Contains),
                args: vec![
                    sta_ak(("A", 0), k("foo")),
                    sta_ak(("B", 1), k("bar")),
                    sta_ak(("C", 2), k("baz")),
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
                ValueOf(?SELF_HOLDER_18Y["const_18y"], 1169909388)               
                ValueOf(?SELF_HOLDER_1Y["const_1y"], 1706367566)                  
            )
        "#;

        // Parse the input string
        let processed = super::parse(input, &Params::default())?;
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

        let id_num_key = k("idNumber");
        let dob_key = k("dateOfBirth");
        let const_18y_key = k("const_18y");
        let start_date_key = k("startDate");
        let const_1y_key = k("const_1y");
        let ssn_key = k("socialSecurityNumber");
        let sanction_list_key = k("sanctionList");

        // Define the request templates using wildcards for constants
        let expected_templates = vec![
            // 1. NotContains(?sanctions["sanctionList"], ?gov["idNumber"])
            StatementTmpl {
                pred: Predicate::Native(NativePredicate::NotContains),
                args: vec![
                    sta_ak(
                        (wc_sanctions.name.as_str(), wc_sanctions.index),
                        sanction_list_key.clone(),
                    ),
                    sta_ak((wc_gov.name.as_str(), wc_gov.index), id_num_key.clone()),
                ],
            },
            // 2. Lt(?gov["dateOfBirth"], ?SELF_HOLDER_18Y["const_18y"])
            StatementTmpl {
                pred: Predicate::Native(NativePredicate::Lt),
                args: vec![
                    sta_ak((wc_gov.name.as_str(), wc_gov.index), dob_key.clone()),
                    sta_ak(
                        (wc_self_18y.name.as_str(), wc_self_18y.index),
                        const_18y_key.clone(),
                    ),
                ],
            },
            // 3. Equal(?pay["startDate"], ?SELF_HOLDER_1Y["const_1y"])
            StatementTmpl {
                pred: Predicate::Native(NativePredicate::Equal),
                args: vec![
                    sta_ak((wc_pay.name.as_str(), wc_pay.index), start_date_key.clone()),
                    sta_ak(
                        (wc_self_1y.name.as_str(), wc_self_1y.index),
                        const_1y_key.clone(),
                    ),
                ],
            },
            // 4. Equal(?gov["socialSecurityNumber"], ?pay["socialSecurityNumber"])
            StatementTmpl {
                pred: Predicate::Native(NativePredicate::Equal),
                args: vec![
                    sta_ak((wc_gov.name.as_str(), wc_gov.index), ssn_key.clone()),
                    sta_ak((wc_pay.name.as_str(), wc_pay.index), ssn_key.clone()),
                ],
            },
            // 5. ValueOf(?SELF_HOLDER_18Y["const_18y"], 1169909388)
            StatementTmpl {
                pred: Predicate::Native(NativePredicate::ValueOf),
                args: vec![
                    sta_ak(
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
                    sta_ak(
                        (wc_self_1y.name.as_str(), wc_self_1y.index),
                        const_1y_key.clone(),
                    ),
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
            eth_friend(src_key, dst_key, private: attestation_pod) = AND(
                ValueOf(?attestation_pod["_type"], 1)
                Equal(?attestation_pod["_signer"], SELF[?src_key])
                Equal(?attestation_pod["attestation"], SELF[?dst_key])
            )

            eth_dos_distance_base(src_key, dst_key, distance_key) = AND(
                Equal(SELF[?src_key], SELF[?dst_key])
                ValueOf(SELF[?distance_key], 0)
            )

            eth_dos_distance_ind(src_key, dst_key, distance_key, private: one_key, shorter_distance_key, intermed_key) = AND(
                eth_dos_distance(?src_key, ?dst_key, ?distance_key)
                ValueOf(SELF[?one_key], 1)
                SumOf(SELF[?distance_key], SELF[?shorter_distance_key], SELF[?one_key])
                eth_friend(?intermed_key, ?dst_key)
            )

            eth_dos_distance(src_key, dst_key, distance_key, private: intermed_key, shorter_distance_key) = OR(
                eth_dos_distance_base(?src_key, ?dst_key, ?distance_key)
                eth_dos_distance_ind(?src_key, ?dst_key, ?distance_key)
            )
        "#;

        let processed = super::parse(input, &params)?;

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
                pred: Predicate::Native(NativePredicate::ValueOf),
                args: vec![
                    sta_ak(("attestation_pod", 2), k("_type")), // Pub(0-1), Priv(2)
                    sta_lit(PodType::MockSigned),
                ],
            },
            StatementTmpl {
                pred: Predicate::Native(NativePredicate::Equal),
                args: vec![
                    sta_ak(("attestation_pod", 2), k("_signer")),
                    sta_ak_self(ko_wc("src_key", 0)), // Pub arg 0
                ],
            },
            StatementTmpl {
                pred: Predicate::Native(NativePredicate::Equal),
                args: vec![
                    sta_ak(("attestation_pod", 2), k("attestation")),
                    sta_ak_self(ko_wc("dst_key", 1)), // Pub arg 1
                ],
            },
        ];
        let expected_friend_pred = CustomPredicate::new(
            &params,
            "eth_friend".to_string(),
            true, // AND
            expected_friend_stmts,
            2, // public_args_len: src_key, dst_key
        )?;

        // eth_dos_distance_base (Index 1)
        let expected_base_stmts = vec![
            StatementTmpl {
                pred: Predicate::Native(NativePredicate::Equal),
                args: vec![
                    sta_ak_self(ko_wc("src_key", 0)),
                    sta_ak_self(ko_wc("dst_key", 1)),
                ],
            },
            StatementTmpl {
                pred: Predicate::Native(NativePredicate::ValueOf),
                args: vec![sta_ak_self(ko_wc("distance_key", 2)), sta_lit(0i64)],
            },
        ];
        let expected_base_pred = CustomPredicate::new(
            &params,
            "eth_dos_distance_base".to_string(),
            true, // AND
            expected_base_stmts,
            3, // public_args_len
        )?;

        // eth_dos_distance_ind (Index 2)
        // Public args indices: 0-2
        // Private args indices: 3-5 (one_key, shorter_distance_key, intermed_key)
        let expected_ind_stmts = vec![
            StatementTmpl {
                pred: Predicate::BatchSelf(3), // Calls eth_dos_distance (index 3)
                args: vec![
                    // WildcardLiteral args
                    StatementTmplArg::WildcardLiteral(wc("src_key", 0)),
                    StatementTmplArg::WildcardLiteral(wc("dst_key", 1)), // private arg
                    StatementTmplArg::WildcardLiteral(wc("distance_key", 2)), // private arg
                ],
            },
            StatementTmpl {
                pred: Predicate::Native(NativePredicate::ValueOf),
                args: vec![sta_ak_self(ko_wc("one_key", 3)), sta_lit(1i64)], // private arg
            },
            StatementTmpl {
                pred: Predicate::Native(NativePredicate::SumOf),
                args: vec![
                    sta_ak_self(ko_wc("distance_key", 2)),         // public arg
                    sta_ak_self(ko_wc("shorter_distance_key", 4)), // private arg
                    sta_ak_self(ko_wc("one_key", 3)),              // private arg
                ],
            },
            StatementTmpl {
                pred: Predicate::BatchSelf(0), // Calls eth_friend (index 0)
                args: vec![
                    // WildcardLiteral args
                    StatementTmplArg::WildcardLiteral(wc("intermed_key", 5)), // private arg
                    StatementTmplArg::WildcardLiteral(wc("dst_key", 1)),      // public arg
                ],
            },
        ];
        let expected_ind_pred = CustomPredicate::new(
            &params,
            "eth_dos_distance_ind".to_string(),
            true, // AND
            expected_ind_stmts,
            3, // public_args_len
        )?;

        // eth_dos_distance (Index 3)
        let expected_dist_stmts = vec![
            StatementTmpl {
                pred: Predicate::BatchSelf(1), // Calls eth_dos_distance_base (index 1)
                args: vec![
                    // WildcardLiteral args
                    StatementTmplArg::WildcardLiteral(wc("src_key", 0)),
                    StatementTmplArg::WildcardLiteral(wc("dst_key", 1)),
                    StatementTmplArg::WildcardLiteral(wc("distance_key", 2)),
                ],
            },
            StatementTmpl {
                pred: Predicate::BatchSelf(2), // Calls eth_dos_distance_ind (index 2)
                args: vec![
                    // WildcardLiteral args
                    StatementTmplArg::WildcardLiteral(wc("src_key", 0)),
                    StatementTmplArg::WildcardLiteral(wc("dst_key", 1)),
                    StatementTmplArg::WildcardLiteral(wc("distance_key", 2)),
                ],
            },
        ];
        let expected_dist_pred = CustomPredicate::new(
            &params,
            "eth_dos_distance".to_string(),
            false, // OR
            expected_dist_stmts,
            3, // public_args_len
        )?;

        let expected_batch = CustomPredicateBatch::new(
            &params,
            "PodlogBatch".to_string(),
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
}
