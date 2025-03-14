#[cfg(test)]
mod tests {
    use crate::{
        backends::plonky2::mock_signed::MockSigner,
        examples::zu_kyc_sign_pod_builders,
        frontend::{
            containers::Array as FrontendArray, AnchoredKey, MainPodBuilder, Origin, PodClass,
            Value,
        },
        middleware::{self, hash_str, NativeOperation, Operation, PodId, SELF},
    };

    use crate::{
        prover::engine::DeductionEngine,
        prover::types::{
            ProvableStatement, ProvableValue, WildcardAnchoredKey, WildcardId, WildcardStatement,
        },
    };

    fn make_signed_origin(id: &str) -> Origin {
        Origin(PodClass::Signed, PodId(hash_str(id)))
    }

    fn make_anchored_key(id: &str, key: &str) -> AnchoredKey {
        AnchoredKey(make_signed_origin(id), key.to_string())
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
        engine.set_target(WildcardStatement::Equal(
            WildcardAnchoredKey(WildcardId::Named("X".to_string()), "X".to_string()),
            make_anchored_key("W", "W"),
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
            NativeOperation::TransitiveEqualFromStatements as u8,
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
            ProvableValue::Int(10),
        ));
        engine.add_fact(ProvableStatement::ValueOf(
            make_anchored_key("Y", "value"),
            ProvableValue::Int(5),
        ));

        // Add a direct GT statement
        engine.add_fact(ProvableStatement::Gt(
            make_anchored_key("A", "value"),
            make_anchored_key("B", "value"),
        ));

        // Test case 1: Find GT through value comparison
        let target = WildcardStatement::Gt(
            WildcardAnchoredKey(WildcardId::Named("n".to_string()), "value".to_string()),
            make_anchored_key("Y", "value"),
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
            NativeOperation::GtFromEntries as u8,
            "Should use GtFromEntries operation"
        );

        // Verify the found statement matches what we expect
        match stmt {
            ProvableStatement::Gt(found_key, target_key) => {
                assert_eq!(found_key.1, "value", "Found key should have suffix 'value'");
                assert_eq!(
                    target_key.1, "value",
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
            ProvableValue::Int(5),
        ));
        engine.add_fact(ProvableStatement::ValueOf(
            make_anchored_key("Y", "value"),
            ProvableValue::Int(10),
        ));

        // Add a direct LT statement
        engine.add_fact(ProvableStatement::Lt(
            make_anchored_key("A", "value"),
            make_anchored_key("B", "value"),
        ));

        // Test case 1: Find LT through value comparison
        let target = WildcardStatement::Lt(
            WildcardAnchoredKey(WildcardId::Named("n".to_string()), "value".to_string()),
            make_anchored_key("Y", "value"),
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
            NativeOperation::LtFromEntries as u8,
            "Should use LtFromEntries operation"
        );

        // Verify the found statement matches what we expect
        match stmt {
            ProvableStatement::Lt(found_key, target_key) => {
                assert_eq!(found_key.1, "value", "Found key should have suffix 'value'");
                assert_eq!(
                    target_key.1, "value",
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
        let target = WildcardStatement::NotEqual(
            WildcardAnchoredKey(WildcardId::Named("n".to_string()), "value".to_string()),
            make_anchored_key("Y", "value"),
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
            NativeOperation::GtToNotEqual as u8,
            "Should use GtToNotEqual operation"
        );

        // Verify the found statement matches what we expect
        match stmt {
            ProvableStatement::NotEqual(found_key, target_key) => {
                assert_eq!(found_key.1, "value", "Found key should have suffix 'value'");
                assert_eq!(
                    target_key.1, "value",
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
        let target = WildcardStatement::NotEqual(
            WildcardAnchoredKey(WildcardId::Named("n".to_string()), "value".to_string()),
            make_anchored_key("Y", "value"),
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
            NativeOperation::LtToNotEqual as u8,
            "Should use LtToNotEqual operation"
        );

        // Verify the found statement matches what we expect
        match stmt {
            ProvableStatement::NotEqual(found_key, target_key) => {
                assert_eq!(found_key.1, "value", "Found key should have suffix 'value'");
                assert_eq!(
                    target_key.1, "value",
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
            ProvableValue::Array(arr),
        ));
        engine.add_fact(ProvableStatement::ValueOf(
            make_anchored_key("Y", "value"),
            ProvableValue::Int(2),
        ));

        // Add a direct Contains statement
        engine.add_fact(ProvableStatement::Contains(
            make_anchored_key("A", "value"),
            make_anchored_key("B", "value"),
        ));

        // Test case 1: Find Contains through value comparison
        let target = WildcardStatement::Contains(
            WildcardAnchoredKey(WildcardId::Named("n".to_string()), "value".to_string()),
            make_anchored_key("Y", "value"),
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
            NativeOperation::ContainsFromEntries as u8,
            "Should use ContainsFromEntries operation"
        );

        // Verify the found statement matches what we expect
        match stmt {
            ProvableStatement::Contains(found_key, target_key) => {
                assert_eq!(found_key.1, "value", "Found key should have suffix 'value'");
                assert_eq!(
                    target_key.1, "value",
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
            ProvableValue::Array(arr),
        ));
        // Add a value that is NOT in the array
        engine.add_fact(ProvableStatement::ValueOf(
            make_anchored_key("Y", "value"),
            ProvableValue::Int(4),
        ));

        // Try to prove that X contains Y (which should be impossible)
        let target = WildcardStatement::Contains(
            WildcardAnchoredKey(WildcardId::Named("n".to_string()), "value".to_string()),
            make_anchored_key("Y", "value"),
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
            ProvableValue::Int(10),
        ));
        engine.add_fact(ProvableStatement::ValueOf(
            make_anchored_key("c", "value"),
            ProvableValue::Int(10),
        ));
        engine.add_fact(ProvableStatement::Equal(
            make_anchored_key("c", "value"),
            make_anchored_key("d", "value"),
        ));

        let targets = vec![
            // First prove b = c (because they have the same value)
            WildcardStatement::Equal(
                WildcardAnchoredKey(
                    WildcardId::Concrete(make_signed_origin("b")),
                    "value".to_string(),
                ),
                make_anchored_key("c", "value"),
            ),
            // Then we can prove a = d (using the chain a = b = c = d)
            WildcardStatement::Equal(
                WildcardAnchoredKey(
                    WildcardId::Concrete(make_signed_origin("a")),
                    "value".to_string(),
                ),
                make_anchored_key("d", "value"),
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
                assert_eq!(k1.1, "value");
                assert_eq!(k2.1, "value");
                println!(
                    "First proof keys: {} = {}",
                    k1.0 .1.to_string(),
                    k2.0 .1.to_string()
                );
                assert_eq!(k1.0 .1.to_string(), hash_str("b").to_string());
                assert_eq!(k2.0 .1.to_string(), hash_str("c").to_string());
            }
            _ => panic!("First proof should be Equal statement"),
        }

        // Second proof should be a = d
        match &proofs[1].0 {
            ProvableStatement::Equal(k1, k2) => {
                assert_eq!(k1.1, "value");
                assert_eq!(k2.1, "value");
                println!(
                    "Second proof keys: {} = {}",
                    k1.0 .1.to_string(),
                    k2.0 .1.to_string()
                );
                assert_eq!(k1.0 .1.to_string(), hash_str("a").to_string());
                assert_eq!(k2.0 .1.to_string(), hash_str("d").to_string());
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

        let now_minus_18y: i64 = 1169909388;
        let now_minus_1y: i64 = 1706367566;

        let ak_now_minus_18y =
            AnchoredKey(Origin(PodClass::Main, SELF), "now_minus_18y".to_string());

        engine.add_fact(ProvableStatement::ValueOf(
            ak_now_minus_18y.clone(),
            ProvableValue::Int(now_minus_18y),
        ));

        let ak_now_minus_1y = AnchoredKey(Origin(PodClass::Main, SELF), "now_minus_1y".to_string());

        engine.add_fact(ProvableStatement::ValueOf(
            ak_now_minus_1y.clone(),
            ProvableValue::Int(now_minus_1y),
        ));

        let targets = vec![
            WildcardStatement::NotContains(
                WildcardAnchoredKey(
                    WildcardId::Concrete(Origin(PodClass::Signed, sanction_list_pod.pod.id())),
                    "sanctionList".to_string(),
                ),
                AnchoredKey(
                    Origin(PodClass::Signed, gov_id_pod.pod.id()),
                    "idNumber".to_string(),
                ),
            ),
            WildcardStatement::Lt(
                WildcardAnchoredKey(
                    WildcardId::Concrete(Origin(PodClass::Signed, gov_id_pod.pod.id())),
                    "dateOfBirth".to_string(),
                ),
                ak_now_minus_18y.clone(),
            ),
            WildcardStatement::Equal(
                WildcardAnchoredKey(
                    WildcardId::Concrete(Origin(PodClass::Signed, pay_stub_pod.pod.id())),
                    "socialSecurityNumber".to_string(),
                ),
                AnchoredKey(
                    Origin(PodClass::Signed, gov_id_pod.pod.id()),
                    "socialSecurityNumber".to_string(),
                ),
            ),
            WildcardStatement::Equal(
                WildcardAnchoredKey(
                    WildcardId::Concrete(Origin(PodClass::Signed, pay_stub_pod.pod.id())),
                    "startDate".to_string(),
                ),
                ak_now_minus_1y.clone(),
            ),
        ];

        let proofs = engine.prove_multiple(targets);

        assert_eq!(proofs.len(), 4, "Should prove all statements");
        assert_eq!(
            proofs[0].1[0].0,
            NativeOperation::NotContainsFromEntries as u8
        );
        assert_eq!(proofs[1].1[0].0, NativeOperation::LtFromEntries as u8);
        assert_eq!(proofs[2].1[0].0, NativeOperation::EqualFromEntries as u8);
        assert_eq!(proofs[3].1[0].0, NativeOperation::EqualFromEntries as u8);

        for (i, (stmt, chain)) in proofs.iter().enumerate() {
            println!("\nProof {}:", i + 1);
            engine.print_proof(stmt.clone(), chain.clone());
        }
    }
}
