#[cfg(test)]
mod tests {
    use crate::{
        backends::plonky2::{mock_main::MockProver, mock_signed::MockSigner},
        examples::{zu_kyc_pod_builder, zu_kyc_sign_pod_builders},
        frontend::{
            containers::Array as FrontendArray, AnchoredKey, MainPodBuilder, Operation,
            OperationArg, Origin, PodClass, StatementArg, Value,
        },
        middleware::{self, hash_str, NativeOperation, OperationType, Params, PodId},
        prover::types::{WildcardStatementArg, WildcardTargetStatement},
    };

    use crate::{
        prover::engine::DeductionEngine,
        prover::types::{ProvableStatement, WildcardAnchoredKey, WildcardId},
    };

    fn make_signed_origin(id: &str) -> Origin {
        Origin {
            pod_class: PodClass::Signed,
            pod_id: PodId(hash_str(id)),
        }
    }

    fn make_anchored_key(id: &str, key: &str) -> AnchoredKey {
        AnchoredKey {
            origin: make_signed_origin(id),
            key: key.to_string(),
        }
    }

    #[test]
    fn test_transitive_equality() {
        let mut engine = DeductionEngine::new();

        // X = Y, Y = Z, Z = Q, Q = W
        engine.add_fact(ProvableStatement::Equal(
            make_anchored_key("X", "X"),
            make_anchored_key("Y", "Y"),
        ));

        engine.add_fact(ProvableStatement::Equal(
            make_anchored_key("Y", "Y"),
            make_anchored_key("Z", "Z"),
        ));

        engine.add_fact(ProvableStatement::Equal(
            make_anchored_key("Z", "Z"),
            make_anchored_key("Q", "Q"),
        ));

        engine.add_fact(ProvableStatement::Equal(
            make_anchored_key("Q", "Q"),
            make_anchored_key("W", "W"),
        ));

        // Try to prove X = W
        engine.set_target(WildcardTargetStatement::Equal(
            WildcardAnchoredKey {
                wildcard_id: WildcardId::Named("X".to_string()),
                key: "X".to_string(),
            },
            WildcardStatementArg::Key(make_anchored_key("W", "W")),
        ));

        let proofs = engine.prove();

        assert!(!proofs.is_empty(), "Should be able to prove X = W");

        // Check that we used transitive equality
        let (stmt, chain) = &proofs[0];
        engine.print_proof(stmt.clone(), chain.clone());
        assert_eq!(chain.len(), 3, "Should have exactly three deduction steps");
        let (op_code, inputs, _) = &chain[0];
        assert_eq!(
            *op_code,
            NativeOperation::TransitiveEqualFromStatements,
            "Should use TransitiveEqualFromStatements operation"
        );
        assert_eq!(inputs.len(), 2, "Should use exactly three input statements");
    }

    #[test]
    fn test_wildcard_gt() {
        let mut engine = DeductionEngine::new();

        // Add some values
        engine.add_fact(ProvableStatement::ValueOf(
            make_anchored_key("X", "value"),
            Value::Int(10),
        ));
        engine.add_fact(ProvableStatement::ValueOf(
            make_anchored_key("Y", "value"),
            Value::Int(5),
        ));

        // Add a direct GT statement
        engine.add_fact(ProvableStatement::Gt(
            make_anchored_key("A", "value"),
            make_anchored_key("B", "value"),
        ));

        // Test case 1: Find GT through value comparison
        let target = WildcardTargetStatement::Gt(
            WildcardAnchoredKey {
                wildcard_id: WildcardId::Named("n".to_string()),
                key: "value".to_string(),
            },
            WildcardStatementArg::Key(make_anchored_key("Y", "value")),
        );
        engine.set_target(target.clone());

        let proofs = engine.prove();
        assert!(
            !proofs.is_empty(),
            "Should find X > Y through value comparison"
        );
        let (stmt, chain) = &proofs[0];

        // Print the proof in a readable format
        engine.print_proof(stmt.clone(), chain.clone());

        assert_eq!(chain.len(), 1, "Should use GtFromEntries");
        assert_eq!(
            chain[0].0,
            NativeOperation::GtFromEntries,
            "Should use GtFromEntries operation"
        );

        // Verify the found statement matches what we expect
        match stmt {
            ProvableStatement::Gt(found_key, target_key) => {
                assert_eq!(
                    found_key.key, "value",
                    "Found key should have suffix 'value'"
                );
                assert_eq!(
                    target_key.key, "value",
                    "Target key should have suffix 'value'"
                );
            }
            _ => panic!("Expected Gt statement"),
        }
    }

    #[test]
    fn test_wildcard_lt() {
        let mut engine = DeductionEngine::new();

        // Add some values
        engine.add_fact(ProvableStatement::ValueOf(
            make_anchored_key("X", "value"),
            Value::Int(5),
        ));
        engine.add_fact(ProvableStatement::ValueOf(
            make_anchored_key("Y", "value"),
            Value::Int(10),
        ));

        // Add a direct LT statement
        engine.add_fact(ProvableStatement::Lt(
            make_anchored_key("A", "value"),
            make_anchored_key("B", "value"),
        ));

        // Test case 1: Find LT through value comparison
        let target = WildcardTargetStatement::Lt(
            WildcardAnchoredKey {
                wildcard_id: WildcardId::Named("n".to_string()),
                key: "value".to_string(),
            },
            WildcardStatementArg::Key(make_anchored_key("Y", "value")),
        );
        engine.set_target(target.clone());

        let proofs = engine.prove();
        assert!(
            !proofs.is_empty(),
            "Should find X < Y through value comparison"
        );
        let (stmt, chain) = &proofs[0];

        // Print the proof in a readable format
        engine.print_proof(stmt.clone(), chain.clone());

        assert_eq!(chain.len(), 1, "Should use LtFromEntries");
        assert_eq!(
            chain[0].0,
            NativeOperation::LtFromEntries,
            "Should use LtFromEntries operation"
        );

        // Verify the found statement matches what we expect
        match stmt {
            ProvableStatement::Lt(found_key, target_key) => {
                assert_eq!(
                    found_key.key, "value",
                    "Found key should have suffix 'value'"
                );
                assert_eq!(
                    target_key.key, "value",
                    "Target key should have suffix 'value'"
                );
            }
            _ => panic!("Expected Lt statement"),
        }
    }

    #[test]
    fn test_wildcard_neq() {
        let mut engine = DeductionEngine::new();

        // Add a GT statement that we'll convert to NEq
        engine.add_fact(ProvableStatement::Gt(
            make_anchored_key("X", "value"),
            make_anchored_key("Y", "value"),
        ));

        // Add a direct NEq statement
        engine.add_fact(ProvableStatement::NotEqual(
            make_anchored_key("A", "value"),
            make_anchored_key("B", "value"),
        ));

        // Test case 1: Find NEq through GT conversion
        let target = WildcardTargetStatement::NotEqual(
            WildcardAnchoredKey {
                wildcard_id: WildcardId::Named("n".to_string()),
                key: "value".to_string(),
            },
            WildcardStatementArg::Key(make_anchored_key("Y", "value")),
        );
        engine.set_target(target.clone());

        let proofs = engine.prove();
        assert!(
            !proofs.is_empty(),
            "Should find X != Y through GT conversion"
        );
        let (stmt, chain) = &proofs[0];

        // Print the proof in a readable format
        engine.print_proof(stmt.clone(), chain.clone());

        assert_eq!(chain.len(), 1, "Should use GtToNotEqual");
        assert_eq!(
            chain[0].0,
            NativeOperation::GtToNotEqual,
            "Should use GtToNotEqual operation"
        );

        // Verify the found statement matches what we expect
        match stmt {
            ProvableStatement::NotEqual(found_key, target_key) => {
                assert_eq!(
                    found_key.key, "value",
                    "Found key should have suffix 'value'"
                );
                assert_eq!(
                    target_key.key, "value",
                    "Target key should have suffix 'value'"
                );
            }
            _ => panic!("Expected NotEqual statement"),
        }
    }

    #[test]
    fn test_wildcard_neq_from_lt() {
        let mut engine = DeductionEngine::new();

        // Add an LT statement that we'll convert to NEq
        engine.add_fact(ProvableStatement::Lt(
            make_anchored_key("X", "value"),
            make_anchored_key("Y", "value"),
        ));

        // Add a direct NEq statement
        engine.add_fact(ProvableStatement::NotEqual(
            make_anchored_key("A", "value"),
            make_anchored_key("B", "value"),
        ));

        // Test case 1: Find NEq through LT conversion
        let target = WildcardTargetStatement::NotEqual(
            WildcardAnchoredKey {
                wildcard_id: WildcardId::Named("n".to_string()),
                key: "value".to_string(),
            },
            WildcardStatementArg::Key(make_anchored_key("Y", "value")),
        );
        engine.set_target(target.clone());

        let proofs = engine.prove();
        assert!(
            !proofs.is_empty(),
            "Should find X != Y through LT conversion"
        );
        let (stmt, chain) = &proofs[0];

        // Print the proof in a readable format
        engine.print_proof(stmt.clone(), chain.clone());

        assert_eq!(chain.len(), 1, "Should use LtToNotEqual");
        assert_eq!(
            chain[0].0,
            NativeOperation::LtToNotEqual,
            "Should use LtToNotEqual operation"
        );

        // Verify the found statement matches what we expect
        match stmt {
            ProvableStatement::NotEqual(found_key, target_key) => {
                assert_eq!(
                    found_key.key, "value",
                    "Found key should have suffix 'value'"
                );
                assert_eq!(
                    target_key.key, "value",
                    "Target key should have suffix 'value'"
                );
            }
            _ => panic!("Expected NotEqual statement"),
        }
    }

    #[test]
    fn test_wildcard_contains() {
        let mut engine = DeductionEngine::new();

        // Add an array that contains a value
        let values = vec![1i64, 2i64, 3i64]
            .into_iter()
            .map(|v| Value::from(v))
            .collect();
        let arr = FrontendArray::new(values);

        engine.add_fact(ProvableStatement::ValueOf(
            make_anchored_key("X", "value"),
            Value::Array(arr),
        ));
        engine.add_fact(ProvableStatement::ValueOf(
            make_anchored_key("Y", "value"),
            Value::Int(2),
        ));

        // Add a direct Contains statement
        engine.add_fact(ProvableStatement::Contains(
            make_anchored_key("A", "value"),
            make_anchored_key("B", "value"),
        ));

        // Test case 1: Find Contains through value comparison
        let target = WildcardTargetStatement::Contains(
            WildcardAnchoredKey {
                wildcard_id: WildcardId::Named("n".to_string()),
                key: "value".to_string(),
            },
            WildcardStatementArg::Key(make_anchored_key("Y", "value")),
        );
        engine.set_target(target.clone());

        let proofs = engine.prove();
        assert!(
            !proofs.is_empty(),
            "Should find X contains Y through value comparison"
        );
        let (stmt, chain) = &proofs[0];

        // Print the proof in a readable format
        engine.print_proof(stmt.clone(), chain.clone());

        assert_eq!(chain.len(), 1, "Should use ContainsFromEntries");
        assert_eq!(
            chain[0].0,
            NativeOperation::ContainsFromEntries,
            "Should use ContainsFromEntries operation"
        );

        // Verify the found statement matches what we expect
        match stmt {
            ProvableStatement::Contains(found_key, target_key) => {
                assert_eq!(
                    found_key.key, "value",
                    "Found key should have suffix 'value'"
                );
                assert_eq!(
                    target_key.key, "value",
                    "Target key should have suffix 'value'"
                );
            }
            _ => panic!("Expected Contains statement"),
        }
    }

    #[test]
    fn test_wildcard_contains_unprovable() {
        let mut engine = DeductionEngine::new();

        // Add an array that contains values 1, 2, 3
        let values = vec![1i64, 2i64, 3i64]
            .into_iter()
            .map(|v| Value::from(v))
            .collect();
        let arr = FrontendArray::new(values);

        engine.add_fact(ProvableStatement::ValueOf(
            make_anchored_key("X", "value"),
            Value::Array(arr),
        ));
        // Add a value that is NOT in the array
        engine.add_fact(ProvableStatement::ValueOf(
            make_anchored_key("Y", "value"),
            Value::Int(4),
        ));

        // Try to prove that X contains Y (which should be impossible)
        let target = WildcardTargetStatement::Contains(
            WildcardAnchoredKey {
                wildcard_id: WildcardId::Named("n".to_string()),
                key: "value".to_string(),
            },
            WildcardStatementArg::Key(make_anchored_key("Y", "value")),
        );
        engine.set_target(target.clone());

        let proofs = engine.prove();
        assert!(
            proofs.is_empty(),
            "Should NOT be able to prove X contains Y since 4 is not in the array"
        );
    }

    #[test]
    fn test_dependent_proofs() {
        let mut engine = DeductionEngine::new();

        // Set up initial facts
        engine.add_fact(ProvableStatement::Equal(
            make_anchored_key("a", "value"),
            make_anchored_key("b", "value"),
        ));
        engine.add_fact(ProvableStatement::ValueOf(
            make_anchored_key("b", "value"),
            Value::Int(10),
        ));
        engine.add_fact(ProvableStatement::ValueOf(
            make_anchored_key("c", "value"),
            Value::Int(10),
        ));
        engine.add_fact(ProvableStatement::Equal(
            make_anchored_key("c", "value"),
            make_anchored_key("d", "value"),
        ));

        let targets = vec![
            // First prove b = c (because they have the same value)
            WildcardTargetStatement::Equal(
                WildcardAnchoredKey {
                    wildcard_id: WildcardId::Concrete(make_signed_origin("b")),
                    key: "value".to_string(),
                },
                WildcardStatementArg::Key(make_anchored_key("c", "value")),
            ),
            // Then we can prove a = d (using the chain a = b = c = d)
            WildcardTargetStatement::Equal(
                WildcardAnchoredKey {
                    wildcard_id: WildcardId::Concrete(make_signed_origin("a")),
                    key: "value".to_string(),
                },
                WildcardStatementArg::Key(make_anchored_key("d", "value")),
            ),
        ];

        let proofs = engine.prove_multiple(targets);
        assert_eq!(proofs.len(), 2, "Should prove both statements");

        // Print all proofs for debugging
        for (i, (stmt, chain)) in proofs.iter().enumerate() {
            println!("\nProof {}:", i + 1);
            engine.print_proof(stmt.clone(), chain.clone());
        }

        // First proof should be b = c
        match &proofs[0].0 {
            ProvableStatement::Equal(k1, k2) => {
                assert_eq!(k1.key, "value");
                assert_eq!(k2.key, "value");
                println!("First proof keys: {} = {}", k1.key, k2.key);
                assert_eq!(k1.origin.pod_id, make_signed_origin("b").pod_id);
                assert_eq!(k2.origin.pod_id, make_signed_origin("c").pod_id);
            }
            _ => panic!("First proof should be Equal statement"),
        }

        // Second proof should be a = d
        match &proofs[1].0 {
            ProvableStatement::Equal(k1, k2) => {
                assert_eq!(k1.key, "value");
                assert_eq!(k2.key, "value");
                println!("Second proof keys: {} = {}", k1.key, k2.key);
                assert_eq!(k1.origin.pod_id, make_signed_origin("a").pod_id);
                assert_eq!(k2.origin.pod_id, make_signed_origin("d").pod_id);
            }
            _ => panic!("Second proof should be Equal statement"),
        }

        // The second proof should have a non-empty chain showing the transitive steps
        assert!(
            !proofs[1].1.is_empty(),
            "Second proof should require deduction steps"
        );
    }

    #[test]
    fn test_auto_zu_kyc() {
        let mut engine = DeductionEngine::new();

        let params = middleware::Params::default();

        let (gov_id_builder, pay_stub_builder, sanction_list_builder) =
            zu_kyc_sign_pod_builders(&params);
        let mut signer = MockSigner {
            pk: "ZooGov".into(),
        };
        let gov_id_pod = gov_id_builder.sign(&mut signer).unwrap();
        let mut signer = MockSigner {
            pk: "ZooDeel".into(),
        };
        let pay_stub_pod = pay_stub_builder.sign(&mut signer).unwrap();
        let mut signer = MockSigner {
            pk: "ZooOFAC".into(),
        };
        let sanction_list_pod = sanction_list_builder.sign(&mut signer).unwrap();

        engine.add_signed_pod(gov_id_pod.clone());
        engine.add_signed_pod(pay_stub_pod.clone());
        engine.add_signed_pod(sanction_list_pod.clone());

        let mut builder = MainPodBuilder::new(&params);

        let now_minus_18y: i64 = 1169909388;
        let now_minus_1y: i64 = 1706367566;

        let stmt = builder.pub_literal(&now_minus_18y).unwrap();
        let ak_now_minus_18y = if let StatementArg::Key(ak) = &stmt.args[0] {
            engine.add_fact(ProvableStatement::ValueOf(
                ak.clone(),
                Value::Int(now_minus_18y),
            ));
            ak.clone()
        } else {
            panic!("Expected StatementArg::Key")
        };

        let stmt = builder.pub_literal(&now_minus_1y).unwrap();
        let ak_now_minus_1y = if let StatementArg::Key(ak) = &stmt.args[0] {
            engine.add_fact(ProvableStatement::ValueOf(
                ak.clone(),
                Value::Int(now_minus_1y),
            ));
            ak.clone()
        } else {
            panic!("Expected StatementArg::Key")
        };

        let targets = vec![
            WildcardTargetStatement::NotContains(
                WildcardAnchoredKey {
                    wildcard_id: WildcardId::Concrete(Origin {
                        pod_class: PodClass::Signed,
                        pod_id: sanction_list_pod.pod.id(),
                    }),
                    key: "sanctionList".to_string(),
                },
                WildcardStatementArg::Key(AnchoredKey {
                    origin: Origin {
                        pod_class: PodClass::Signed,
                        pod_id: gov_id_pod.pod.id(),
                    },
                    key: "idNumber".to_string(),
                }),
            ),
            WildcardTargetStatement::Lt(
                WildcardAnchoredKey {
                    wildcard_id: WildcardId::Concrete(Origin {
                        pod_class: PodClass::Signed,
                        pod_id: gov_id_pod.pod.id(),
                    }),
                    key: "dateOfBirth".to_string(),
                },
                WildcardStatementArg::Key(ak_now_minus_18y.clone()),
            ),
            WildcardTargetStatement::Equal(
                WildcardAnchoredKey {
                    wildcard_id: WildcardId::Concrete(Origin {
                        pod_class: PodClass::Signed,
                        pod_id: pay_stub_pod.pod.id(),
                    }),
                    key: "socialSecurityNumber".to_string(),
                },
                WildcardStatementArg::Key(AnchoredKey {
                    origin: Origin {
                        pod_class: PodClass::Signed,
                        pod_id: gov_id_pod.pod.id(),
                    },
                    key: "socialSecurityNumber".to_string(),
                }),
            ),
            WildcardTargetStatement::Equal(
                WildcardAnchoredKey {
                    wildcard_id: WildcardId::Concrete(Origin {
                        pod_class: PodClass::Signed,
                        pod_id: pay_stub_pod.pod.id(),
                    }),
                    key: "startDate".to_string(),
                },
                WildcardStatementArg::Key(ak_now_minus_1y.clone()),
            ),
        ];

        let proofs = engine.prove_multiple(targets);

        assert_eq!(proofs.len(), 4, "Should prove all statements");
        assert_eq!(proofs[0].1[0].0, NativeOperation::NotContainsFromEntries);
        assert_eq!(proofs[1].1[0].0, NativeOperation::LtFromEntries);
        assert_eq!(proofs[2].1[0].0, NativeOperation::EqualFromEntries);
        assert_eq!(proofs[3].1[0].0, NativeOperation::EqualFromEntries);

        for (_stmt, chain) in proofs.iter() {
            for (op_code, inputs, _output) in chain {
                let op = Operation(
                    match op_code {
                        x if *x == NativeOperation::ContainsFromEntries => {
                            OperationType::Native(NativeOperation::ContainsFromEntries)
                        }
                        x if *x == NativeOperation::NotContainsFromEntries => {
                            OperationType::Native(NativeOperation::NotContainsFromEntries)
                        }
                        x if *x == NativeOperation::EqualFromEntries => {
                            OperationType::Native(NativeOperation::EqualFromEntries)
                        }
                        x if *x == NativeOperation::LtFromEntries => {
                            OperationType::Native(NativeOperation::LtFromEntries)
                        }
                        x if *x == NativeOperation::GtFromEntries => {
                            OperationType::Native(NativeOperation::GtFromEntries)
                        }
                        x if *x == NativeOperation::SumOf => {
                            OperationType::Native(NativeOperation::SumOf)
                        }
                        x if *x == NativeOperation::ProductOf => {
                            OperationType::Native(NativeOperation::ProductOf)
                        }
                        x if *x == NativeOperation::MaxOf => {
                            OperationType::Native(NativeOperation::MaxOf)
                        }
                        _ => panic!("Unknown operation code: {:?}", op_code),
                    },
                    inputs
                        .iter()
                        .map(|i| OperationArg::Statement(i.clone().into()))
                        .collect(),
                );
                println!("Adding op: {:?}", op);
                builder.pub_op(op).unwrap();
            }
        }

        builder.add_signed_pod(&gov_id_pod);
        builder.add_signed_pod(&pay_stub_pod);
        builder.add_signed_pod(&sanction_list_pod);

        println!("Builder: {:?}", builder);

        let mut prover = MockProver {};
        let pod = builder.prove(&mut prover, &params).unwrap();
        println!("Pod: {}", pod.pod.id());

        for (i, (stmt, chain)) in proofs.iter().enumerate() {
            println!("\nProof {}:", i + 1);
            engine.print_proof(stmt.clone(), chain.clone());
        }
    }

    #[test]
    fn test_arithmetic_operations() {
        let mut engine = DeductionEngine::new();

        // Add some values
        engine.add_fact(ProvableStatement::ValueOf(
            make_anchored_key("X", "value"),
            Value::Int(10),
        ));
        engine.add_fact(ProvableStatement::ValueOf(
            make_anchored_key("Y", "value"),
            Value::Int(5),
        ));
        engine.add_fact(ProvableStatement::ValueOf(
            make_anchored_key("Z", "value"),
            Value::Int(15),
        ));
        engine.add_fact(ProvableStatement::ValueOf(
            make_anchored_key("P", "value"),
            Value::Int(50),
        ));
        engine.add_fact(ProvableStatement::ValueOf(
            make_anchored_key("M", "value"),
            Value::Int(10),
        ));

        // Test SumOf
        let target = WildcardTargetStatement::SumOf(
            WildcardAnchoredKey {
                wildcard_id: WildcardId::Named("sum".to_string()),
                key: "value".to_string(),
            },
            WildcardStatementArg::Key(make_anchored_key("X", "value")),
            WildcardStatementArg::Key(make_anchored_key("Y", "value")),
        );
        engine.set_target(target.clone());

        let proofs = engine.prove();
        assert!(
            !proofs.is_empty(),
            "Should find Z = X + Y through value comparison"
        );
        let (stmt, chain) = &proofs[0];
        engine.print_proof(stmt.clone(), chain.clone());
        assert_eq!(chain.len(), 1, "Should use SumOf");
        assert_eq!(
            chain[0].0,
            NativeOperation::SumOf,
            "Should use SumOf operation"
        );

        // Reset engine before testing ProductOf
        engine.reset();

        // Re-add the values since we reset
        engine.add_fact(ProvableStatement::ValueOf(
            make_anchored_key("X", "value"),
            Value::Int(10),
        ));
        engine.add_fact(ProvableStatement::ValueOf(
            make_anchored_key("Y", "value"),
            Value::Int(5),
        ));
        engine.add_fact(ProvableStatement::ValueOf(
            make_anchored_key("Z", "value"),
            Value::Int(15),
        ));
        engine.add_fact(ProvableStatement::ValueOf(
            make_anchored_key("P", "value"),
            Value::Int(50),
        ));
        engine.add_fact(ProvableStatement::ValueOf(
            make_anchored_key("M", "value"),
            Value::Int(10),
        ));

        // Test ProductOf
        let target = WildcardTargetStatement::ProductOf(
            WildcardAnchoredKey {
                wildcard_id: WildcardId::Named("prod".to_string()),
                key: "value".to_string(),
            },
            WildcardStatementArg::Key(make_anchored_key("X", "value")),
            WildcardStatementArg::Key(make_anchored_key("Y", "value")),
        );
        engine.set_target(target.clone());

        let proofs = engine.prove();
        assert!(
            !proofs.is_empty(),
            "Should find P = X * Y through value comparison"
        );
        let (stmt, chain) = &proofs[0];
        engine.print_proof(stmt.clone(), chain.clone());
        assert_eq!(chain.len(), 1, "Should use ProductOf");
        assert_eq!(
            chain[0].0,
            NativeOperation::ProductOf,
            "Should use ProductOf operation"
        );

        // Reset engine before testing MaxOf
        engine.reset();

        // Re-add the values since we reset
        engine.add_fact(ProvableStatement::ValueOf(
            make_anchored_key("X", "value"),
            Value::Int(10),
        ));
        engine.add_fact(ProvableStatement::ValueOf(
            make_anchored_key("Y", "value"),
            Value::Int(5),
        ));
        engine.add_fact(ProvableStatement::ValueOf(
            make_anchored_key("Z", "value"),
            Value::Int(15),
        ));
        engine.add_fact(ProvableStatement::ValueOf(
            make_anchored_key("P", "value"),
            Value::Int(50),
        ));
        engine.add_fact(ProvableStatement::ValueOf(
            make_anchored_key("M", "value"),
            Value::Int(10),
        ));

        // Test MaxOf
        let target = WildcardTargetStatement::MaxOf(
            WildcardAnchoredKey {
                wildcard_id: WildcardId::Named("max".to_string()),
                key: "value".to_string(),
            },
            WildcardStatementArg::Key(make_anchored_key("X", "value")),
            WildcardStatementArg::Key(make_anchored_key("Y", "value")),
        );
        engine.set_target(target.clone());

        let proofs = engine.prove();
        assert!(
            !proofs.is_empty(),
            "Should find M = max(X, Y) through value comparison"
        );
        let (stmt, chain) = &proofs[0];
        engine.print_proof(stmt.clone(), chain.clone());
        assert_eq!(chain.len(), 1, "Should use MaxOf");
        assert_eq!(
            chain[0].0,
            NativeOperation::MaxOf,
            "Should use MaxOf operation"
        );
    }

    #[test]
    fn test_recursive_proof() {
        let mut engine = DeductionEngine::new();

        // Build standard ZuKYC Main Pod
        let params = Params::default();
        let (gov_id, pay_stub, sanction_list) = zu_kyc_sign_pod_builders(&params);

        let mut signer = MockSigner {
            pk: "ZooGov".into(),
        };
        let gov_id = gov_id.sign(&mut signer).unwrap();

        let mut signer = MockSigner {
            pk: "ZooDeel".into(),
        };
        let pay_stub = pay_stub.sign(&mut signer).unwrap();

        let mut signer = MockSigner {
            pk: "ZooOFAC".into(),
        };
        let sanction_list = sanction_list.sign(&mut signer).unwrap();

        let kyc_builder = zu_kyc_pod_builder(&params, &gov_id, &pay_stub, &sanction_list).unwrap();

        // prove kyc with MockProver and print it
        let mut prover = MockProver {};
        let kyc = kyc_builder.prove(&mut prover, &params).unwrap();

        engine.add_main_pod(kyc);

        engine.set_target(WildcardTargetStatement::Equal(
            WildcardAnchoredKey {
                wildcard_id: WildcardId::Concrete(Origin {
                    pod_class: PodClass::Signed,
                    pod_id: gov_id.pod.id(),
                }),
                key: "socialSecurityNumber".to_string(),
            },
            WildcardStatementArg::Key(AnchoredKey {
                origin: Origin {
                    pod_class: PodClass::Signed,
                    pod_id: pay_stub.pod.id(),
                },
                key: "socialSecurityNumber".to_string(),
            }),
        ));

        let proofs = engine.prove();
        assert!(!proofs.is_empty(), "Should be able to prove");
    }
}
