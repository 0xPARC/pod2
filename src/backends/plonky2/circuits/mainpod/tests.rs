use std::{iter, ops::Not};

use num::FromPrimitive;
use plonky2::{
    field::{goldilocks_field::GoldilocksField, types::Field},
    iop::witness::WitnessWrite,
    plonk::{circuit_builder::CircuitBuilder, circuit_data::CircuitConfig},
};

use super::*;
use crate::{
    backends::plonky2::{
        basetypes::C,
        circuits::common::{tests::I64_TEST_PAIRS, IndexTarget},
        mainpod::{
            extract_custom_predicate_verifications, extract_custom_predicates, OperationArg,
            OperationAux, Size,
        },
        primitives::{
            ec::schnorr::SecretKey,
            merkletree::{MerkleClaimAndProof, MerkleTree, MerkleTreeStateTransitionProof},
        },
        signer,
    },
    dict,
    frontend::{self, literal, CustomPredicateBatchBuilder, StatementTmplBuilder},
    middleware::{
        self, hash_values, AnchoredKey, Hash, Key, OperationType, Predicate, PredicateOrWildcard,
        RawValue, Statement, StatementArg, StatementTmpl, StatementTmplArg, ValueRef, Wildcard,
        BASE_PARAMS, EMPTY_VALUE,
    },
};

#[derive(Default)]
struct Aux {
    merkle_proofs: Vec<MerkleClaimAndProof>,
    secret_keys: Vec<SecretKey>,
    signed_bys: Vec<SignedBy>,
    merkle_transition_proofs: Vec<MerkleTreeStateTransitionProof>,
}

impl Aux {
    fn merkle_proof(v: MerkleClaimAndProof) -> Self {
        Self {
            merkle_proofs: vec![v],
            ..Default::default()
        }
    }
    fn secret_key(v: SecretKey) -> Self {
        Self {
            secret_keys: vec![v],
            ..Default::default()
        }
    }
    fn signed_by(v: SignedBy) -> Self {
        Self {
            signed_bys: vec![v],
            ..Default::default()
        }
    }
    fn merkle_tree_state_transition_proof(v: MerkleTreeStateTransitionProof) -> Self {
        Self {
            merkle_transition_proofs: vec![v],
            ..Default::default()
        }
    }
}

fn operation_verify(
    st: mainpod::Statement,
    op: mainpod::Operation,
    prev_statements: Vec<mainpod::Statement>,
    aux: Aux,
) -> Result<()> {
    let params = Params {
        max_input_pods: 0,
        max_public_key_ops: aux.secret_keys.len(),
        max_signed_by_ops: aux.signed_bys.len(),
        containers: middleware::ParamsContainers {
            state_ops: middleware::ParamsMerkleProofs {
                max_small: 0,
                max_medium: aux.merkle_proofs.len(),
            },
            transition_ops: middleware::ParamsMerkleProofs {
                max_small: 0,
                max_medium: aux.merkle_transition_proofs.len(),
            },
            max_depth_small: 8,
            max_depth_medium: 32,
        },
        max_custom_predicate_verification_ops: 0,
        max_custom_predicates: 0,
        max_open_input_statement_ops: 0,
        ..Default::default()
    };

    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::new(config);

    let st_target = builder.add_virtual_statement(false);
    let op_target = builder.add_virtual_operation(&params);
    let prev_statements_target: Vec<_> = (0..prev_statements.len())
        .map(|_| builder.add_virtual_statement(false))
        .collect();
    let prev_statement_flatteneds_target: Vec<Vec<Target>> = prev_statements_target
        .iter()
        .map(|st| st.flatten())
        .collect();
    let prev_statement_hashes_target: Vec<_> = prev_statement_flatteneds_target
        .iter()
        .map(|flat| builder.hash_n_to_hash_no_pad::<PoseidonHash>(flat.clone()))
        .collect();

    let merkle_proofs_target = MerkleProofsTarget {
        medium: aux
            .merkle_proofs
            .iter()
            .map(|_| {
                MerkleClaimAndProofTarget::new_virtual(
                    params.containers.max_depth_medium,
                    &mut builder,
                )
            })
            .collect(),
        small: Vec::new(),
    };

    let secret_keys_target: Vec<_> = aux
        .secret_keys
        .iter()
        .map(|sk| builder.constant_biguint320(&sk.0))
        .collect();

    let signed_by_targets: Vec<_> = aux
        .signed_bys
        .iter()
        .map(|_| SignedByTarget::new_virtual(&mut builder))
        .collect();

    let merkle_transition_proofs_target = MerkleTransitionProofsTarget {
        medium: aux
            .merkle_transition_proofs
            .iter()
            .map(|_| {
                MerkleTreeStateTransitionProofTarget::new_virtual(
                    params.containers.max_depth_medium,
                    &mut builder,
                )
            })
            .collect(),
        small: Vec::new(),
    };

    let aux_table_inputs = AuxTableInputTargets {
        merkle_proofs: merkle_proofs_target,
        merkle_transition_proofs: merkle_transition_proofs_target,
        open_input_statements: Vec::new(),
        public_key_sks: secret_keys_target,
        signed_bys: signed_by_targets,
        custom_predicate_verifications: Vec::new(),
    };
    let aux_tables =
        build_operation_aux_table_circuit(&params, &mut builder, &[], &[], &aux_table_inputs)?;

    let st_hash_target = st_target.hash(&mut builder);
    verify_operation_circuit(
        &params,
        &mut builder,
        StatementWithHash {
            statement: &st_target,
            hash: st_hash_target,
        },
        &op_target,
        &prev_statement_flatteneds_target,
        &prev_statement_hashes_target,
        &aux_tables,
    )?;

    let mut pw = PartialWitness::<F>::new();
    st_target.set_targets(&mut pw, &st)?;
    op_target.set_targets(&mut pw, &params, &op)?;
    for (prev_st_target, prev_st) in prev_statements_target.iter().zip(prev_statements.iter()) {
        prev_st_target.set_targets(&mut pw, prev_st)?;
    }
    for (signed_by_target, signed_by) in aux_table_inputs
        .signed_bys
        .iter()
        .zip(aux.signed_bys.iter())
    {
        signed_by_target.set_targets(&mut pw, signed_by)?
    }
    for (merkle_proof_target, merkle_proof) in aux_table_inputs
        .merkle_proofs
        .medium
        .iter()
        .zip(aux.merkle_proofs.iter())
    {
        merkle_proof_target.set_targets(&mut pw, merkle_proof)?
    }
    for (merkle_tree_state_transition_proof_target, merkle_tree_state_transition_proof) in
        aux_table_inputs
            .merkle_transition_proofs
            .medium
            .iter()
            .zip(aux.merkle_transition_proofs.iter())
    {
        merkle_tree_state_transition_proof_target
            .set_targets(&mut pw, merkle_tree_state_transition_proof)?
    }

    // generate & verify proof
    let data = builder.build::<C>();
    let proof = data.prove(pw)?;
    data.verify(proof)?;

    Ok(())
}

#[test]
fn test_lt_lteq_verify_failures() {
    let invalid_int = RawValue([
        GoldilocksField::NEG_ONE,
        GoldilocksField::ZERO,
        GoldilocksField::ZERO,
        GoldilocksField::ZERO,
    ]);

    let prev_statements = [Statement::None.into()];

    [
        // 56 < 55, 55 < 55, 56 <= 55, -55 < -55, -55 < -56, -55 <= -56 should fail to verify
        (
            mainpod::Operation(
                OperationType::Native(NativeOperation::LtFromEntries),
                vec![OperationArg::Index(0), OperationArg::Index(0)],
                OperationAux::None,
            ),
            Statement::lt(56, 55).into(),
        ),
        (
            mainpod::Operation(
                OperationType::Native(NativeOperation::LtFromEntries),
                vec![OperationArg::Index(0), OperationArg::Index(0)],
                OperationAux::None,
            ),
            Statement::lt(55, 55).into(),
        ),
        (
            mainpod::Operation(
                OperationType::Native(NativeOperation::LtEqFromEntries),
                vec![OperationArg::Index(0), OperationArg::Index(0)],
                OperationAux::None,
            ),
            Statement::lt_eq(56, 55).into(),
        ),
        (
            mainpod::Operation(
                OperationType::Native(NativeOperation::LtFromEntries),
                vec![OperationArg::Index(0), OperationArg::Index(0)],
                OperationAux::None,
            ),
            Statement::lt(-55, -55).into(),
        ),
        (
            mainpod::Operation(
                OperationType::Native(NativeOperation::LtFromEntries),
                vec![OperationArg::Index(0), OperationArg::Index(0)],
                OperationAux::None,
            ),
            Statement::lt(-55, -56).into(),
        ),
        (
            mainpod::Operation(
                OperationType::Native(NativeOperation::LtEqFromEntries),
                vec![OperationArg::Index(0), OperationArg::Index(0)],
                OperationAux::None,
            ),
            Statement::lt_eq(-55, -56).into(),
        ),
        // 56 < p-1 and p-1 <= p-1 should fail to verify, where p
        // is the Goldilocks prime and 'p-1' occupies a single
        // limb.
        (
            mainpod::Operation(
                OperationType::Native(NativeOperation::LtFromEntries),
                vec![OperationArg::Index(0), OperationArg::Index(0)],
                OperationAux::None,
            ),
            Statement::lt(56, invalid_int).into(),
        ),
        (
            mainpod::Operation(
                OperationType::Native(NativeOperation::LtEqFromEntries),
                vec![OperationArg::Index(0), OperationArg::Index(0)],
                OperationAux::None,
            ),
            Statement::lt_eq(invalid_int, invalid_int).into(),
        ),
    ]
    .into_iter()
    .for_each(|(op, st)| {
        let check = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            operation_verify(st, op, prev_statements.to_vec(), Aux::default())
        }));
        match check {
            Err(e) => {
                let err_string = e.downcast_ref::<String>().unwrap();
                if !err_string.contains("Integer too large to fit") {
                    panic!("Test failed with an unexpected error: {}", err_string);
                }
            }
            Ok(Err(_)) => {}
            _ => panic!("Test passed, yet it should have failed!"),
        }
    });
}

#[test]
fn test_eq_neq_verify_failures() {
    let prev_statements = [Statement::None.into()];

    [
        // 56 == 55, 55 != 55 should fail to verify
        (
            mainpod::Operation(
                OperationType::Native(NativeOperation::EqualFromEntries),
                vec![OperationArg::Index(0), OperationArg::Index(0)],
                OperationAux::None,
            ),
            Statement::equal(56, 55).into(),
        ),
        (
            mainpod::Operation(
                OperationType::Native(NativeOperation::NotEqualFromEntries),
                vec![OperationArg::Index(0), OperationArg::Index(0)],
                OperationAux::None,
            ),
            Statement::not_equal(55, 55).into(),
        ),
    ]
    .into_iter()
    .for_each(|(op, st)| {
        assert!(operation_verify(st, op, prev_statements.to_vec(), Aux::default()).is_err())
    });
}

#[test]
fn test_operation_verify_none() -> Result<()> {
    let st: mainpod::Statement = Statement::None.into();
    let op = mainpod::Operation(
        OperationType::Native(NativeOperation::None),
        vec![],
        OperationAux::None,
    );
    let prev_statements = vec![Statement::None.into()];
    operation_verify(st, op, prev_statements, Aux::default())
}

#[test]
fn test_operation_verify_eq() -> Result<()> {
    let dict1 = dict!({"hello" => 55});
    let dict2 = dict!({"world" => 55});
    let st1: mainpod::Statement = Statement::contains(dict1.clone(), "hello", 55).into();
    let st2: mainpod::Statement = Statement::contains(dict2.clone(), "world", 55).into();
    let st: mainpod::Statement = Statement::equal(
        AnchoredKey::from((&dict1, "hello")),
        AnchoredKey::from((&dict2, "world")),
    )
    .into();
    let op = mainpod::Operation(
        OperationType::Native(NativeOperation::EqualFromEntries),
        vec![OperationArg::Index(0), OperationArg::Index(1)],
        OperationAux::None,
    );
    let prev_statements = vec![st1, st2];
    operation_verify(st, op, prev_statements, Aux::default())
}

#[test]
fn test_operation_verify_neq() -> Result<()> {
    let dict1 = dict!({"hello" => 55});
    let dict2 = dict!({"world" => 75});
    let st1: mainpod::Statement = Statement::contains(dict1.clone(), "hello", 55).into();
    let st2: mainpod::Statement = Statement::contains(dict2.clone(), "world", 75).into();
    let st: mainpod::Statement = Statement::not_equal(
        AnchoredKey::from((&dict1, "hello")),
        AnchoredKey::from((&dict2, "world")),
    )
    .into();
    let op = mainpod::Operation(
        OperationType::Native(NativeOperation::NotEqualFromEntries),
        vec![OperationArg::Index(0), OperationArg::Index(1)],
        OperationAux::None,
    );
    let prev_statements = vec![st1, st2];
    operation_verify(st, op, prev_statements, Aux::default())
}

#[test]
fn test_operation_verify_lt() -> Result<()> {
    let dict1 = dict!({"hello" => 55});
    let dict2 = dict!({"hello" => 56});
    let st1: mainpod::Statement = Statement::contains(dict1.clone(), "hello", 55).into();
    let st2: mainpod::Statement = Statement::contains(dict2.clone(), "hello", 56).into();
    let st: mainpod::Statement = Statement::lt(
        AnchoredKey::from((&dict1, "hello")),
        AnchoredKey::from((&dict2, "hello")),
    )
    .into();
    let op = mainpod::Operation(
        OperationType::Native(NativeOperation::LtFromEntries),
        vec![OperationArg::Index(0), OperationArg::Index(1)],
        OperationAux::None,
    );
    let prev_statements = vec![st1, st2.clone()];
    operation_verify(st, op, prev_statements, Aux::default())?;

    // Also check negative < negative
    let dict3 = dict!({"hola" => -56});
    let dict4 = dict!({"mundo" => -55});
    let st3: mainpod::Statement = Statement::contains(dict3.clone(), "hola", -56).into();
    let st4: mainpod::Statement = Statement::contains(dict4.clone(), "mundo", -55).into();
    let st: mainpod::Statement = Statement::lt(
        AnchoredKey::from((&dict3, "hola")),
        AnchoredKey::from((&dict4, "mundo")),
    )
    .into();
    let op = mainpod::Operation(
        OperationType::Native(NativeOperation::LtFromEntries),
        vec![OperationArg::Index(0), OperationArg::Index(1)],
        OperationAux::None,
    );
    let prev_statements = vec![st3.clone(), st4];
    operation_verify(st, op, prev_statements, Aux::default())?;

    // Also check negative < positive
    let st: mainpod::Statement = Statement::lt(
        AnchoredKey::from((&dict3, "hola")),
        AnchoredKey::from((&dict2, "hello")),
    )
    .into();
    let op = mainpod::Operation(
        OperationType::Native(NativeOperation::LtFromEntries),
        vec![OperationArg::Index(0), OperationArg::Index(1)],
        OperationAux::None,
    );
    let prev_statements = vec![st3, st2];
    operation_verify(st, op, prev_statements, Aux::default())
}

#[test]
fn test_operation_verify_lteq() -> Result<()> {
    let local = dict!({
        "n55" => 55,
        "n56" => 56,
        "n_56" => -56,
        "n_55" => -55,
    });
    let st1: mainpod::Statement = Statement::contains(local.clone(), "n55", 55).into();
    let st2: mainpod::Statement = Statement::contains(local.clone(), "n56", 56).into();
    let st: mainpod::Statement = Statement::lt_eq(
        AnchoredKey::from((&local, "n55")),
        AnchoredKey::from((&local, "n56")),
    )
    .into();
    let op = mainpod::Operation(
        OperationType::Native(NativeOperation::LtEqFromEntries),
        vec![OperationArg::Index(0), OperationArg::Index(1)],
        OperationAux::None,
    );
    let prev_statements = vec![st1, st2.clone()];
    operation_verify(st, op, prev_statements, Aux::default())?;

    // Also check negative <= negative
    let st3: mainpod::Statement = Statement::contains(local.clone(), "n_56", -56).into();
    let st4: mainpod::Statement = Statement::contains(local.clone(), "n_55", -55).into();
    let st: mainpod::Statement = Statement::lt_eq(
        AnchoredKey::from((&local, "n_56")),
        AnchoredKey::from((&local, "n_55")),
    )
    .into();
    let op = mainpod::Operation(
        OperationType::Native(NativeOperation::LtEqFromEntries),
        vec![OperationArg::Index(0), OperationArg::Index(1)],
        OperationAux::None,
    );
    let prev_statements = vec![st3.clone(), st4];
    operation_verify(st, op, prev_statements, Aux::default())?;

    // Also check negative <= positive
    let st: mainpod::Statement = Statement::lt_eq(
        AnchoredKey::from((&local, "n_56")),
        AnchoredKey::from((&local, "n56")),
    )
    .into();
    let op = mainpod::Operation(
        OperationType::Native(NativeOperation::LtEqFromEntries),
        vec![OperationArg::Index(0), OperationArg::Index(1)],
        OperationAux::None,
    );
    let prev_statements = vec![st3, st2];
    operation_verify(st, op, prev_statements.clone(), Aux::default())?;

    // Also check equality, both positive and negative.
    let st: mainpod::Statement = Statement::lt_eq(
        AnchoredKey::from((&local, "n_56")),
        AnchoredKey::from((&local, "n_56")),
    )
    .into();
    let op = mainpod::Operation(
        OperationType::Native(NativeOperation::LtEqFromEntries),
        vec![OperationArg::Index(0), OperationArg::Index(0)],
        OperationAux::None,
    );
    operation_verify(st, op, prev_statements.clone(), Aux::default())?;
    let st: mainpod::Statement = Statement::lt_eq(
        AnchoredKey::from((&local, "n56")),
        AnchoredKey::from((&local, "n56")),
    )
    .into();
    let op = mainpod::Operation(
        OperationType::Native(NativeOperation::LtEqFromEntries),
        vec![OperationArg::Index(1), OperationArg::Index(1)],
        OperationAux::None,
    );
    operation_verify(st, op, prev_statements, Aux::default())
}

#[test]
fn test_operation_verify_hash() -> Result<()> {
    let input_values = [
        Value::from(RawValue([
            GoldilocksField(1),
            GoldilocksField(2),
            GoldilocksField(3),
            GoldilocksField(4),
        ])),
        Value::from(512),
    ];
    let v3 = hash_values(&input_values);
    let [v1, v2] = input_values;

    let local = dict!({
        "hola" => v1.clone(),
        "mundo" => v2.clone(),
        "!" => v3,
    });

    let st1: mainpod::Statement = Statement::contains(local.clone(), "hola", v1).into();
    let st2: mainpod::Statement = Statement::contains(local.clone(), "mundo", v2).into();
    let st3: mainpod::Statement = Statement::contains(local.clone(), "!", v3).into();

    let st: mainpod::Statement = Statement::_hash(
        AnchoredKey::from((&local, "hola")),
        AnchoredKey::from((&local, "mundo")),
        AnchoredKey::from((&local, "!")),
    )
    .into();
    let op = mainpod::Operation(
        OperationType::Native(NativeOperation::HashFromEntries),
        vec![
            OperationArg::Index(0),
            OperationArg::Index(1),
            OperationArg::Index(2),
        ],
        OperationAux::None,
    );
    let prev_statements = vec![st1, st2, st3];
    operation_verify(st, op, prev_statements, Aux::default())
}

#[test]
fn test_operation_verify_sum() -> Result<()> {
    I64_TEST_PAIRS
        .into_iter()
        .flat_map(|(a, b)| {
            let (sum, overflow) = a.overflowing_add(b);
            overflow.not().then_some((a, b, sum))
        })
        .try_for_each(|(a, b, sum)| {
            let local = dict!({
                "a" => a,
                "b" => b,
                "sum" => sum,
            });

            let st1: mainpod::Statement = Statement::contains(local.clone(), "a", a).into();
            let st2: mainpod::Statement = Statement::contains(local.clone(), "b", b).into();
            let st3: mainpod::Statement = Statement::contains(local.clone(), "sum", sum).into();

            let st: mainpod::Statement = Statement::sum(
                AnchoredKey::from((&local, "a")),
                AnchoredKey::from((&local, "b")),
                AnchoredKey::from((&local, "sum")),
            )
            .into();
            let op = mainpod::Operation(
                OperationType::Native(NativeOperation::SumFromEntries),
                vec![
                    OperationArg::Index(0),
                    OperationArg::Index(1),
                    OperationArg::Index(2),
                ],
                OperationAux::None,
            );
            let prev_statements = vec![st1, st2, st3];
            operation_verify(st, op, prev_statements, Aux::default())
        })
}

#[test]
fn test_operation_verify_sumof_non_monotonic_repeated_indices() -> Result<()> {
    let local = dict!({
        "a" => 3,
        "noise" => 99,
        "sum" => 6,
    });
    let st_a: mainpod::Statement = Statement::contains(local.clone(), "a", 3).into();
    let st_noise: mainpod::Statement = Statement::contains(local.clone(), "noise", 99).into();
    let st_sum: mainpod::Statement = Statement::contains(local.clone(), "sum", 6).into();

    let st: mainpod::Statement = Statement::sum(
        AnchoredKey::from((&local, "a")),
        AnchoredKey::from((&local, "a")),
        AnchoredKey::from((&local, "sum")),
    )
    .into();
    let op = mainpod::Operation(
        OperationType::Native(NativeOperation::SumFromEntries),
        vec![
            // Non-monotonic and repeated indices to stress random-access resolution.
            OperationArg::Index(0),
            OperationArg::Index(0),
            OperationArg::Index(2),
        ],
        OperationAux::None,
    );
    let prev_statements = vec![st_a, st_noise, st_sum];
    operation_verify(st, op, prev_statements, Aux::default())
}

#[test]
fn test_operation_verify_product() -> Result<()> {
    I64_TEST_PAIRS
        .into_iter()
        .flat_map(|(a, b)| {
            let (prod, overflow) = a.overflowing_mul(b);
            overflow.not().then_some((a, b, prod))
        })
        .try_for_each(|(a, b, prod)| {
            let local = dict!({
                "prod" => prod,
                "a" => a,
                "b" => b,
            });

            let st1: mainpod::Statement = Statement::contains(local.clone(), "a", a).into();
            let st2: mainpod::Statement = Statement::contains(local.clone(), "b", b).into();
            let st3: mainpod::Statement = Statement::contains(local.clone(), "prod", prod).into();

            let st: mainpod::Statement = Statement::product(
                AnchoredKey::from((&local, "a")),
                AnchoredKey::from((&local, "b")),
                AnchoredKey::from((&local, "prod")),
            )
            .into();
            let op = mainpod::Operation(
                OperationType::Native(NativeOperation::ProductFromEntries),
                vec![
                    OperationArg::Index(0),
                    OperationArg::Index(1),
                    OperationArg::Index(2),
                ],
                OperationAux::None,
            );
            let prev_statements = vec![st1, st2, st3];
            operation_verify(st, op, prev_statements, Aux::default())
        })
}

#[test]
fn test_operation_verify_max() -> Result<()> {
    I64_TEST_PAIRS.into_iter().try_for_each(|(a, b)| {
        let max = i64::max(a, b);
        let local = dict!({
            "max" => max,
            "a" => a,
            "b" => b,
        });

        let st1: mainpod::Statement = Statement::contains(local.clone(), "a", a).into();
        let st2: mainpod::Statement = Statement::contains(local.clone(), "b", b).into();
        let st3: mainpod::Statement = Statement::contains(local.clone(), "max", max).into();

        let st: mainpod::Statement = Statement::max(
            AnchoredKey::from((&local, "a")),
            AnchoredKey::from((&local, "b")),
            AnchoredKey::from((&local, "max")),
        )
        .into();

        let op = mainpod::Operation(
            OperationType::Native(NativeOperation::MaxFromEntries),
            vec![
                OperationArg::Index(0),
                OperationArg::Index(1),
                OperationArg::Index(2),
            ],
            OperationAux::None,
        );
        let prev_statements = vec![st1, st2, st3];
        operation_verify(st, op, prev_statements, Aux::default())
    })
}

#[test]
fn test_operation_verify_maxof_failures() {
    [(3, 4, 5), (5, 8, 5), (4, 5, 3)]
        .into_iter()
        .for_each(|(max, a, b)| {
            let st: mainpod::Statement = Statement::max(a, b, max).into();
            let op = mainpod::Operation(
                OperationType::Native(NativeOperation::MaxFromEntries),
                vec![
                    OperationArg::Index(0),
                    OperationArg::Index(0),
                    OperationArg::Index(0),
                ],
                OperationAux::None,
            );
            let prev_statements = [Statement::None.into()];

            let check = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                operation_verify(st, op, prev_statements.to_vec(), Aux::default())
            }));
            match check {
                Err(e) => {
                    let err_string = e.downcast_ref::<String>().unwrap();
                    if !err_string.contains("Integer too large to fit") {
                        panic!("Test failed with an unexpected error: {}", err_string);
                    }
                }
                Ok(Err(_)) => {}
                _ => panic!("Test passed, yet it should have failed!"),
            }
        })
}

#[test]
fn test_operation_verify_lt_to_neq() -> Result<()> {
    let local = dict!({
        "a" => 10,
        "b" => 20,
    });
    let st: mainpod::Statement = Statement::not_equal(
        AnchoredKey::from((&local, "a")),
        AnchoredKey::from((&local, "b")),
    )
    .into();
    let st1: mainpod::Statement = Statement::lt(
        AnchoredKey::from((&local, "a")),
        AnchoredKey::from((&local, "b")),
    )
    .into();
    let op = mainpod::Operation(
        OperationType::Native(NativeOperation::LtToNotEqual),
        vec![OperationArg::Index(0)],
        OperationAux::None,
    );
    let prev_statements = vec![st1];
    operation_verify(st, op, prev_statements, Aux::default())
}

#[test]
fn test_operation_verify_transitive_eq() -> Result<()> {
    let local = dict!({
        "a" => 10,
        "b" => 10,
        "c" => 10,
    });
    let st: mainpod::Statement = Statement::equal(
        AnchoredKey::from((&local, "a")),
        AnchoredKey::from((&local, "c")),
    )
    .into();
    let st1: mainpod::Statement = Statement::equal(
        AnchoredKey::from((&local, "a")),
        AnchoredKey::from((&local, "b")),
    )
    .into();
    let st2: mainpod::Statement = Statement::equal(
        AnchoredKey::from((&local, "b")),
        AnchoredKey::from((&local, "c")),
    )
    .into();
    let op = mainpod::Operation(
        OperationType::Native(NativeOperation::TransitiveEqualFromStatements),
        vec![OperationArg::Index(0), OperationArg::Index(1)],
        OperationAux::None,
    );
    let prev_statements = vec![st1, st2];
    operation_verify(st, op, prev_statements, Aux::default())
}

#[test]
fn test_operation_verify_sintains() -> Result<()> {
    let kvs = [
        (1.into(), 55.into()),
        (2.into(), 88.into()),
        (175.into(), 0.into()),
    ]
    .into_iter()
    .collect();
    let mt = MerkleTree::new(&kvs);

    let root = mt.root();
    let key = Value::from(5);
    let local = dict!({
        "merkle_root" => root,
        "key" => key.clone(),
    });
    let root_ak = AnchoredKey::from((&local, "merkle_root"));
    let key_ak = AnchoredKey::from((&local, "key"));

    let no_key_pf = mt.prove_nonexistence(&key.raw())?;

    let root_st: mainpod::Statement =
        Statement::contains(local.clone(), "merkle_root", root).into();
    let key_st: mainpod::Statement = Statement::contains(local.clone(), "key", key.clone()).into();
    let st: mainpod::Statement = Statement::not_contains(root_ak, key_ak).into();
    let op = mainpod::Operation(
        OperationType::Native(NativeOperation::NotContainsFromEntries),
        vec![OperationArg::Index(0), OperationArg::Index(1)],
        OperationAux::MerkleProofIndex(Size::Medium, 0),
    );

    let merkle_proof = MerkleClaimAndProof::new(root, key.raw(), None, no_key_pf);
    let prev_statements = vec![root_st, key_st];
    operation_verify(st, op, prev_statements, Aux::merkle_proof(merkle_proof))
}

#[test]
fn test_operation_verify_contains() -> Result<()> {
    let kvs = [
        (1.into(), 55.into()),
        (2.into(), 88.into()),
        (175.into(), 0.into()),
    ]
    .into_iter()
    .collect();
    let mt = MerkleTree::new(&kvs);

    let root = mt.root();
    let key = Value::from(175);
    let (value, key_pf) = mt.prove(&key.raw())?;
    let local = dict!({
        "merkle_root" => root,
        "key" => key.clone(),
        "value" => value,
    });
    let root_ak = AnchoredKey::from((&local, "merkle_root"));
    let key_ak = AnchoredKey::from((&local, "key"));
    let value_ak = AnchoredKey::from((&local, "value"));

    let root_st: mainpod::Statement =
        Statement::contains(local.clone(), "merkle_root", root).into();
    let key_st: mainpod::Statement = Statement::contains(local.clone(), "key", key.clone()).into();
    let value_st: mainpod::Statement = Statement::contains(local.clone(), "value", value).into();

    let st: mainpod::Statement = Statement::contains(root_ak, key_ak, value_ak).into();
    let op = mainpod::Operation(
        OperationType::Native(NativeOperation::ContainsFromEntries),
        vec![
            OperationArg::Index(0),
            OperationArg::Index(1),
            OperationArg::Index(2),
        ],
        OperationAux::MerkleProofIndex(Size::Medium, 0),
    );

    let merkle_proof = MerkleClaimAndProof::new(root, key.raw(), Some(value), key_pf);
    let prev_statements = vec![root_st, key_st, value_st];
    operation_verify(st, op, prev_statements, Aux::merkle_proof(merkle_proof))
}

#[test]
fn test_operation_verify_merkle_insert() -> Result<()> {
    let mut tree = MerkleTree::new(&[].into());

    let key = Value::from(175);
    let value = Value::from(0);
    let state_transition_proof = tree.insert(&key.raw(), &value.raw())?;
    let old_root = state_transition_proof.old_root;
    let new_root = state_transition_proof.new_root;

    let st: mainpod::Statement = Statement::insert(old_root, key, value, new_root).into();
    let op = mainpod::Operation(
        OperationType::Native(NativeOperation::ContainerInsertFromEntries),
        vec![
            OperationArg::Index(0),
            OperationArg::Index(0),
            OperationArg::Index(0),
            OperationArg::Index(0),
        ],
        OperationAux::MerkleTransitionProofIndex(Size::Medium, 0),
    );

    let aux = Aux::merkle_tree_state_transition_proof(state_transition_proof);
    let prev_statements = vec![Statement::None.into()];
    operation_verify(st, op, prev_statements, aux)
}

#[test]
fn test_operation_verify_merkle_update() -> Result<()> {
    let mut tree = MerkleTree::new(&[(175.into(), 55.into())].into());

    let key = Value::from(175);
    let value = Value::from(0);
    let state_transition_proof = tree.update(&key.raw(), &value.raw())?;
    let old_root = state_transition_proof.old_root;
    let new_root = state_transition_proof.new_root;

    let st: mainpod::Statement = Statement::update(old_root, key, value, new_root).into();
    let op = mainpod::Operation(
        OperationType::Native(NativeOperation::ContainerUpdateFromEntries),
        vec![
            OperationArg::Index(0),
            OperationArg::Index(0),
            OperationArg::Index(0),
            OperationArg::Index(0),
        ],
        OperationAux::MerkleTransitionProofIndex(Size::Medium, 0),
    );

    let aux = Aux::merkle_tree_state_transition_proof(state_transition_proof);
    let prev_statements = vec![Statement::None.into()];
    operation_verify(st, op, prev_statements, aux)
}

#[test]
fn test_operation_verify_merkle_delete() -> Result<()> {
    let mut tree = MerkleTree::new(&[(175.into(), 55.into())].into());

    let key = Value::from(175);
    let state_transition_proof = tree.delete(&key.raw())?;
    let old_root = state_transition_proof.old_root;
    let new_root = state_transition_proof.new_root;

    let st: mainpod::Statement = Statement::delete(old_root, key, new_root).into();
    let op = mainpod::Operation(
        OperationType::Native(NativeOperation::ContainerDeleteFromEntries),
        vec![
            OperationArg::Index(0),
            OperationArg::Index(0),
            OperationArg::Index(0),
        ],
        OperationAux::MerkleTransitionProofIndex(Size::Medium, 0),
    );

    let aux = Aux::merkle_tree_state_transition_proof(state_transition_proof);
    let prev_statements = vec![Statement::None.into()];
    operation_verify(st, op, prev_statements, aux)
}

#[test]
fn test_operation_verify_publickey_ok() -> Result<()> {
    [
        SecretKey(BigUint::one()),
        SecretKey::new_rand(),
        SecretKey(&*GROUP_ORDER - BigUint::one()),
    ]
    .into_iter()
    .try_for_each(|secret_key| {
        let public_key = secret_key.public_key();

        let st: mainpod::Statement = Statement::public_key(secret_key.clone(), public_key).into();
        let op = mainpod::Operation(
            OperationType::Native(NativeOperation::PublicKeyFromEntries),
            vec![OperationArg::Index(0), OperationArg::Index(0)],
            OperationAux::PublicKeyIndex(0),
        );
        let prev_statements = vec![Statement::None.into()];
        operation_verify(st, op, prev_statements, Aux::secret_key(secret_key))
    })
}

#[test]
fn test_operation_verify_publickey_failure_wrong_key() {
    let secret_key = SecretKey(BigUint::one());
    let public_key = SecretKey(BigUint::ZERO).public_key();

    let st: mainpod::Statement = Statement::public_key(secret_key.clone(), public_key).into();
    let op = mainpod::Operation(
        OperationType::Native(NativeOperation::PublicKeyFromEntries),
        vec![OperationArg::Index(0), OperationArg::Index(0)],
        OperationAux::PublicKeyIndex(0),
    );
    let prev_statements = vec![Statement::None.into()];
    assert!(operation_verify(st, op, prev_statements, Aux::secret_key(secret_key)).is_err())
}

#[test]
fn test_operation_verify_publickey_failure_pk_type() {
    let secret_key = SecretKey(BigUint::one());
    let public_key = 123i64;

    let st: mainpod::Statement = Statement::public_key(secret_key.clone(), public_key).into();
    let op = mainpod::Operation(
        OperationType::Native(NativeOperation::PublicKeyFromEntries),
        vec![OperationArg::Index(0), OperationArg::Index(0)],
        OperationAux::None,
    );
    let prev_statements = vec![Statement::None.into()];
    assert!(operation_verify(st, op, prev_statements, Aux::secret_key(secret_key)).is_err())
}

#[test]
fn test_operation_verify_publickey_failure_sk_type() {
    let secret_key = 123i64;
    let public_key = SecretKey(BigUint::from(123u32)).public_key();

    let st: mainpod::Statement = Statement::public_key(secret_key, public_key).into();
    let op = mainpod::Operation(
        OperationType::Native(NativeOperation::PublicKeyFromEntries),
        vec![OperationArg::Index(0), OperationArg::Index(0)],
        OperationAux::PublicKeyIndex(0),
    );
    let prev_statements = vec![Statement::None.into()];
    let aux = Aux::secret_key(SecretKey(BigUint::from(123u32)));
    assert!(operation_verify(st, op, prev_statements, aux,).is_err())
}

#[test]
fn test_operation_verify_publickey_failure_sk_size() {
    let secret_key = SecretKey(&*GROUP_ORDER - BigUint::ZERO);
    let public_key = secret_key.public_key();

    let st: mainpod::Statement = Statement::public_key(secret_key.clone(), public_key).into();
    let op = mainpod::Operation(
        OperationType::Native(NativeOperation::PublicKeyFromEntries),
        vec![OperationArg::Index(0), OperationArg::Index(0)],
        OperationAux::PublicKeyIndex(0),
    );
    let prev_statements = vec![Statement::None.into()];
    assert!(operation_verify(st, op, prev_statements, Aux::secret_key(secret_key)).is_err())
}

#[test]
fn test_operation_verify_signedby_ok() -> Result<()> {
    let sk = SecretKey(BigUint::from_u32(0xbadcafe).unwrap());
    let pk = sk.public_key();
    let msg = RawValue([F(1), F(2), F(3), F(4)]);
    let nonce = BigUint::from_u32(123).unwrap();
    let sig = signer::Signer(sk).sign_with_nonce(nonce, msg);
    let signed_by = SignedBy {
        msg,
        pk,
        sig: sig.clone(),
    };

    let st: mainpod::Statement = Statement::signed_by(msg, pk).into();
    let op = mainpod::Operation(
        OperationType::Native(NativeOperation::SignedByFromEntries),
        vec![OperationArg::Index(0), OperationArg::Index(0)],
        OperationAux::SignedByIndex(0),
    );
    let prev_statements = vec![Statement::None.into()];
    operation_verify(st, op, prev_statements, Aux::signed_by(signed_by))
}

#[test]
fn test_operation_replace_value_with_entry() -> Result<()> {
    let d = dict!({"a" => 42, "b" => 33});

    // 0: None
    // 1: Lt(5, 42)
    let st_in: mainpod::Statement = Statement::lt(5, 42).into();
    // 2: Contains(d, "a", 42)
    let st_entry: mainpod::Statement = Statement::contains(d.clone(), "a", 42).into();

    let st_out: mainpod::Statement =
        Statement::lt(5, ValueRef::Key(AnchoredKey::from((&d, "a")))).into();
    let mut op_args: Vec<_> = iter::repeat(OperationArg::None)
        .take(BASE_PARAMS.max_statement_args + 1)
        .collect();
    op_args[1] = OperationArg::Index(2);
    op_args[BASE_PARAMS.max_statement_args] = OperationArg::Index(1);
    let op = mainpod::Operation(
        OperationType::Native(NativeOperation::ReplaceValueWithEntry),
        op_args,
        OperationAux::None,
    );

    let prev_statements = vec![Statement::None.into(), st_in, st_entry];
    operation_verify(st_out, op, prev_statements, Aux::default())
}

#[test]
fn test_operation_replace_value_with_entry_array() -> Result<()> {
    use middleware::containers::Array;

    let arr = Array::new(vec![Value::from(42), Value::from(33)]);

    // 0: None
    // 1: Lt(5, 42)
    let st_in: mainpod::Statement = Statement::lt(5, 42).into();
    // 2: Contains(arr, 0, 42)
    let st_entry: mainpod::Statement = Statement::contains(arr.clone(), 0i64, 42).into();

    let st_out: mainpod::Statement = Statement::lt(
        5,
        ValueRef::Key(AnchoredKey::new(arr.commitment(), Key::from(0i64))),
    )
    .into();
    let mut op_args: Vec<_> = iter::repeat(OperationArg::None)
        .take(BASE_PARAMS.max_statement_args + 1)
        .collect();
    op_args[1] = OperationArg::Index(2);
    op_args[BASE_PARAMS.max_statement_args] = OperationArg::Index(1);
    let op = mainpod::Operation(
        OperationType::Native(NativeOperation::ReplaceValueWithEntry),
        op_args,
        OperationAux::None,
    );

    let prev_statements = vec![Statement::None.into(), st_in, st_entry];
    operation_verify(st_out, op, prev_statements, Aux::default())
}

fn helper_statement_arg_from_template(
    params: &Params,
    st_tmpl_arg: StatementTmplArg,
    args: Vec<Value>,
    expected_st_arg: StatementArg,
) -> Result<()> {
    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::new(config);

    let st_tmpl_arg_target = builder.add_virtual_statement_tmpl_arg();
    let args_target: Vec<_> = (0..args.len())
        .map(|_| builder.add_virtual_value())
        .collect();
    let st_arg_target = make_statement_arg_from_template_circuit(
        params,
        &mut builder,
        &st_tmpl_arg_target,
        &args_target,
    );
    // TODO: Instead of connect, assign witness to result
    let expected_st_arg_target = builder.add_virtual_statement_arg();
    builder.connect_array(expected_st_arg_target.elements, st_arg_target.elements);

    let mut pw = PartialWitness::<F>::new();

    st_tmpl_arg_target.set_targets(&mut pw, &st_tmpl_arg)?;
    for (arg_target, arg) in args_target.iter().zip(args.iter()) {
        arg_target.set_targets(&mut pw, arg)?;
    }
    expected_st_arg_target.set_targets(&mut pw, &expected_st_arg)?;

    // generate & verify proof
    let data = builder.build::<C>();
    let proof = data.prove(pw).unwrap();
    data.verify(proof.clone()).unwrap();

    Ok(())
}

#[test]
fn test_statement_arg_from_template() -> Result<()> {
    let params = Params::default();

    let dict = Hash([F(6), F(7), F(8), F(9)]);

    // case: None
    let st_tmpl_arg = StatementTmplArg::None;
    let args = vec![Value::from(1), Value::from(2), Value::from(3)];
    let expected_st_arg = StatementArg::None;
    helper_statement_arg_from_template(&params, st_tmpl_arg, args, expected_st_arg)?;

    // case: Literal
    let st_tmpl_arg = StatementTmplArg::Literal(Value::from("foo"));
    let args = vec![Value::from(1), Value::from(2), Value::from(3)];
    let expected_st_arg = StatementArg::Literal(Value::from("foo"));
    helper_statement_arg_from_template(&params, st_tmpl_arg, args, expected_st_arg)?;

    // case: AnchoredKey(id_wildcard, key_literal)
    let st_tmpl_arg =
        StatementTmplArg::AnchoredKey(Wildcard::new("a".to_string(), 1), Key::from("foo"));
    let args = vec![Value::from(1), Value::from(dict), Value::from(3)];
    let expected_st_arg = StatementArg::Key(AnchoredKey::new(dict, Key::from("foo")));
    helper_statement_arg_from_template(&params, st_tmpl_arg, args, expected_st_arg)?;

    // case: WildcardLiteral(wildcard)
    let st_tmpl_arg = StatementTmplArg::Wildcard(Wildcard::new("a".to_string(), 1));
    let args = vec![Value::from(1), Value::from("key"), Value::from(3)];
    let expected_st_arg = StatementArg::Literal(Value::from("key"));
    helper_statement_arg_from_template(&params, st_tmpl_arg, args, expected_st_arg)?;

    Ok(())
}

fn helper_statement_from_template(
    params: &Params,
    st_tmpl: StatementTmpl,
    args: Vec<Value>,
    expected_st: Statement,
) -> Result<()> {
    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::new(config);

    let st_tmpl_target = builder.add_virtual_statement_tmpl(false);
    let args_target: Vec<_> = (0..args.len())
        .map(|_| builder.add_virtual_value())
        .collect();
    let st_target =
        make_statement_from_template_circuit(params, &mut builder, &st_tmpl_target, &args_target);
    // TODO: Instead of connect, assign witness to result
    let expected_st_target = builder.add_virtual_statement(false);
    builder.connect_flattenable(&expected_st_target, &st_target);

    let mut pw = PartialWitness::<F>::new();

    st_tmpl_target.set_targets(&mut pw, &st_tmpl)?;
    for (arg_target, arg) in args_target.iter().zip(args.iter()) {
        arg_target.set_targets(&mut pw, arg)?;
    }
    expected_st_target.set_targets(&mut pw, &expected_st.into())?;

    // generate & verify proof
    let data = builder.build::<C>();
    let proof = data.prove(pw).unwrap();
    data.verify(proof.clone()).unwrap();

    Ok(())
}

#[test]
fn test_statement_from_template() -> Result<()> {
    let params = Params::default();

    let dict = Hash([F(6), F(7), F(8), F(9)]);

    let st_tmpl = StatementTmpl {
        pred_or_wc: PredicateOrWildcard::Predicate(Predicate::Native(NativePredicate::Equal)),
        args: vec![
            StatementTmplArg::AnchoredKey(Wildcard::new("a".to_string(), 1), Key::from("key")),
            StatementTmplArg::Literal(Value::from("value")),
        ],
    };
    let args = vec![Value::from(1), Value::from(dict), Value::from(3)];
    let expected_st = Statement::equal(
        AnchoredKey::new(dict, Key::from("key")),
        Value::from("value"),
    );
    helper_statement_from_template(&params, st_tmpl, args, expected_st)?;

    let st_tmpl = StatementTmpl {
        pred_or_wc: PredicateOrWildcard::Wildcard(Wildcard::new("x".to_string(), 2)),
        args: vec![
            StatementTmplArg::AnchoredKey(Wildcard::new("a".to_string(), 1), Key::from("key")),
            StatementTmplArg::Literal(Value::from("value")),
        ],
    };
    let pred_hash = Predicate::Native(NativePredicate::NotEqual).hash();
    let args = vec![Value::from(1), Value::from(dict), Value::from(pred_hash)];
    let expected_st = Statement::not_equal(
        AnchoredKey::new(dict, Key::from("key")),
        Value::from("value"),
    );
    helper_statement_from_template(&params, st_tmpl, args, expected_st)?;

    Ok(())
}

fn helper_custom_operation_verify_gadget(
    params: &Params,
    custom_predicate: CustomPredicateRef,
    mut op_args: Vec<Statement>,
    mut args: Vec<Value>,
    expected_st: Option<Statement>,
) -> Result<()> {
    // Pad
    for _ in op_args.len()..BASE_PARAMS.max_operation_args {
        op_args.push(Statement::None);
    }
    for _ in args.len()..params.max_custom_predicate_wildcards {
        args.push(Value::from(EMPTY_VALUE));
    }

    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::new(config);

    let custom_predicate_target = builder.add_virtual_custom_predicate_entry();
    let op_args_target: Vec<_> = (0..op_args.len())
        .map(|_| builder.add_virtual_statement(false))
        .collect();
    let args_target: Vec<_> = (0..args.len())
        .map(|_| builder.add_virtual_value())
        .collect();
    let (st_target, op_type_target) = make_custom_statement_circuit(
        params,
        &mut builder,
        &custom_predicate_target,
        &op_args_target,
        &args_target,
    )?;

    let mut pw = PartialWitness::<F>::new();

    // Input
    custom_predicate_target.set_targets(&mut pw, &custom_predicate)?;
    for (op_arg_target, op_arg) in op_args_target.iter().zip(op_args.into_iter()) {
        op_arg_target.set_targets(&mut pw, &op_arg.into())?;
    }
    for (arg_target, arg) in args_target.iter().zip(args.iter()) {
        arg_target.set_targets(&mut pw, &Value::from(arg.raw()))?;
    }
    // Expected Output
    if let Some(expected_st) = expected_st {
        st_target.set_targets(&mut pw, &expected_st.into())?;
    }

    let expected_op_type = OperationType::Custom(custom_predicate);
    op_type_target.set_targets(&mut pw, &expected_op_type)?;

    // generate & verify proof
    let data = builder.build::<C>();
    let proof = data.prove(pw)?;
    Ok(data.verify(proof.clone())?)
}

fn value_ref(v: impl Into<ValueRef>) -> ValueRef {
    v.into()
}

// TODO: Add negative tests
#[test]
fn test_custom_operation_verify_gadget_positive() -> frontend::Result<()> {
    let params = Params::default();

    use NativePredicate as NP;
    use StatementTmplBuilder as STB;
    let mut builder = CustomPredicateBatchBuilder::new(params.clone(), "batch".into());
    let stb0 = STB::new_from_pred(NP::Equal)
        .arg(("id", "score"))
        .arg(literal(42));
    let stb1 = STB::new_from_pred(NP::Equal)
        .arg(("id", "key"))
        .arg("secret");
    let _ = builder.predicate_and(
        "pred_and",
        &["id"],
        &["secret"],
        &[stb0.clone(), stb1.clone()],
    )?;
    let _ = builder.predicate_or("pred_or", &["id"], &["secret"], &[stb0, stb1])?;
    let batch = builder.finish()?;

    let dict = Hash([F(6), F(7), F(8), F(9)]);

    // AND
    let custom_predicate = CustomPredicateRef::new(batch.clone(), 0);
    let op_args = vec![
        Statement::equal(AnchoredKey::new(dict, Key::from("score")), Value::from(42)),
        Statement::equal(AnchoredKey::new(dict, Key::from("key")), Value::from(1234)),
    ];
    let args = vec![Value::from(dict), Value::from(1234)];
    let expected_st = Statement::Custom(custom_predicate.clone(), vec![value_ref(args[0].clone())]);

    helper_custom_operation_verify_gadget(
        &params,
        custom_predicate,
        op_args,
        args,
        Some(expected_st),
    )
    .unwrap();

    // OR (1)
    let custom_predicate = CustomPredicateRef::new(batch.clone(), 1);
    let op_args = vec![
        Statement::equal(AnchoredKey::new(dict, Key::from("score")), Value::from(42)),
        Statement::None,
    ];
    let args = vec![Value::from(dict), Value::from(0)];
    let expected_st = Statement::Custom(custom_predicate.clone(), vec![value_ref(args[0].clone())]);

    helper_custom_operation_verify_gadget(
        &params,
        custom_predicate,
        op_args,
        args,
        Some(expected_st),
    )
    .unwrap();

    // OR (2)
    let custom_predicate = CustomPredicateRef::new(batch.clone(), 1);
    let op_args = vec![
        Statement::None,
        Statement::equal(AnchoredKey::new(dict, Key::from("key")), Value::from(1234)),
    ];
    let args = vec![Value::from(dict), Value::from(1234)];
    let expected_st = Statement::Custom(custom_predicate.clone(), vec![value_ref(args[0].clone())]);

    helper_custom_operation_verify_gadget(
        &params,
        custom_predicate,
        op_args,
        args,
        Some(expected_st),
    )
    .unwrap();

    Ok(())
}

#[test]
fn test_custom_operation_verify_gadget_negative() -> frontend::Result<()> {
    let params = Params::default();

    use NativePredicate as NP;
    use StatementTmplBuilder as STB;
    let mut builder = CustomPredicateBatchBuilder::new(params.clone(), "batch".into());
    let stb0 = STB::new_from_pred(NP::Equal)
        .arg(("id", "score"))
        .arg(literal(42));
    let stb1 = STB::new_from_pred(NP::Equal)
        .arg(("secret_id", "key"))
        .arg(("id", "score"));
    let _ = builder.predicate_and(
        "pred_and",
        &["id"],
        &["secret_id"],
        &[stb0.clone(), stb1.clone()],
    )?;
    let _ = builder.predicate_or("pred_or", &["id"], &["secret_id"], &[stb0, stb1])?;
    let batch = builder.finish()?;

    let dict = Hash([F(1), F(2), F(3), F(4)]);
    let secret_dict = Hash([F(6), F(7), F(8), F(9)]);

    // AND (0) Sanity check with correct values
    let custom_predicate = CustomPredicateRef::new(batch.clone(), 0);
    let op_args = vec![
        Statement::equal(AnchoredKey::new(dict, Key::from("score")), Value::from(42)),
        Statement::equal(
            AnchoredKey::new(secret_dict, Key::from("key")),
            AnchoredKey::new(dict, Key::from("score")),
        ),
    ];
    let args = vec![Value::from(dict), Value::from(secret_dict)];
    let expected_st = Statement::Custom(custom_predicate.clone(), vec![value_ref(args[0].clone())]);

    helper_custom_operation_verify_gadget(
        &params,
        custom_predicate,
        op_args,
        args,
        Some(expected_st),
    )
    .unwrap();

    // AND (1) Different dict for same wildcard
    let custom_predicate = CustomPredicateRef::new(batch.clone(), 0);
    let op_args = vec![
        Statement::equal(AnchoredKey::new(dict, Key::from("score")), Value::from(42)),
        Statement::equal(
            AnchoredKey::new(secret_dict, Key::from("key")),
            AnchoredKey::new(Hash([F(0), F(5), F(1), F(6)]), Key::from("score")),
        ),
    ];
    let args = vec![Value::from(dict), Value::from(secret_dict)];

    assert!(
        helper_custom_operation_verify_gadget(&params, custom_predicate, op_args, args, None,)
            .is_err()
    );

    // AND (2) key doesn't match template
    let custom_predicate = CustomPredicateRef::new(batch.clone(), 0);
    let op_args = vec![
        Statement::equal(AnchoredKey::new(dict, Key::from("BAD")), Value::from(42)),
        Statement::equal(
            AnchoredKey::new(secret_dict, Key::from("key")),
            AnchoredKey::new(dict, Key::from("score")),
        ),
    ];
    let args = vec![Value::from(dict), Value::from(secret_dict)];

    assert!(
        helper_custom_operation_verify_gadget(&params, custom_predicate, op_args, args, None,)
            .is_err()
    );

    // AND (3) literal doesn't match template
    let custom_predicate = CustomPredicateRef::new(batch.clone(), 0);
    let op_args = vec![
        Statement::equal(
            AnchoredKey::new(dict, Key::from("score")),
            Value::from(0xbad),
        ),
        Statement::equal(
            AnchoredKey::new(secret_dict, Key::from("key")),
            AnchoredKey::new(dict, Key::from("score")),
        ),
    ];
    let args = vec![Value::from(dict), Value::from(secret_dict)];

    assert!(
        helper_custom_operation_verify_gadget(&params, custom_predicate, op_args, args, None,)
            .is_err()
    );

    // AND (4) predicate doesn't match template
    let custom_predicate = CustomPredicateRef::new(batch.clone(), 0);
    let op_args = vec![
        Statement::equal(AnchoredKey::new(dict, Key::from("score")), Value::from(42)),
        Statement::not_equal(
            AnchoredKey::new(secret_dict, Key::from("key")),
            AnchoredKey::new(dict, Key::from("score")),
        ),
    ];
    let args = vec![Value::from(dict), Value::from(secret_dict)];

    assert!(
        helper_custom_operation_verify_gadget(&params, custom_predicate, op_args, args, None,)
            .is_err()
    );

    // OR (1) Two Nones
    let custom_predicate = CustomPredicateRef::new(batch.clone(), 1);
    let op_args = vec![Statement::None, Statement::None];
    let args = vec![Value::from(dict), Value::from(0)];

    assert!(
        helper_custom_operation_verify_gadget(&params, custom_predicate, op_args, args, None)
            .is_err()
    );

    Ok(())
}

#[test]
fn test_normalize_st_tmpl_self_predicate_hash() -> Result<()> {
    let params = Params::default();

    // Build a batch with two predicates:
    // pred_A: Equal(x, y)
    // pred_B: Equal(x, SelfPredicateHash(0)), references pred_A's hash
    use NativePredicate as NP;
    let mut cpb = CustomPredicateBatchBuilder::new(params.clone(), "batch".into());
    let stb_a = StatementTmplBuilder::new_from_pred(NP::Equal)
        .arg("x")
        .arg("y");
    cpb.predicate_and("pred_A", &["x", "y"], &[], &[stb_a])
        .unwrap();

    // Build pred_B's template manually with SelfPredicateHash(0)
    let stb_b_tmpl = StatementTmpl {
        pred_or_wc: PredicateOrWildcard::Predicate(Predicate::Native(NP::Equal)),
        args: vec![
            StatementTmplArg::Wildcard(Wildcard::new("x".to_string(), 0)),
            StatementTmplArg::SelfPredicateHash(0),
        ],
    };
    let pred_b = CustomPredicate::new(
        &params,
        "pred_B".into(),
        true,
        vec![stb_b_tmpl],
        1,
        vec!["x".to_string()],
    )
    .unwrap();
    cpb.predicates.push(pred_b);
    let batch = cpb.finish().unwrap();

    // Compute the expected resolved hash of pred_A
    let pred_a_ref = CustomPredicateRef::new(batch.clone(), 0);
    let pred_a_hash = Predicate::Custom(pred_a_ref).hash();
    let expected_pred_a_value = Value::from(pred_a_hash);

    // Test: normalize_st_tmpl_circuit should convert SelfPredicateHash(0) to
    // Literal(pred_a_hash). Then make_statement_from_template_circuit should produce
    // a statement with that literal value.
    let pred_b_ref = CustomPredicateRef::new(batch.clone(), 1);
    let pred_b_tmpl = &pred_b_ref.predicate().statements[0];

    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::new(config);

    // Create the template target and batch id target
    let st_tmpl_target = builder.add_virtual_statement_tmpl(true);
    let batch_id = builder.add_virtual_hash();

    // Normalize the template (this is what we're testing)
    let normalized = normalize_st_tmpl_circuit(&params, &mut builder, &st_tmpl_target, batch_id);

    // Feed normalized template into statement generation
    let args_target: Vec<_> = (0..params.max_custom_predicate_wildcards)
        .map(|_| builder.add_virtual_value())
        .collect();
    let st_target =
        make_statement_from_template_circuit(&params, &mut builder, &normalized, &args_target);

    // Connect to expected output
    let expected_st_target = builder.add_virtual_statement(false);
    builder.connect_flattenable(&expected_st_target, &st_target);

    // Set witness
    let mut pw = PartialWitness::<F>::new();
    st_tmpl_target.set_targets(&mut pw, pred_b_tmpl)?;
    pw.set_target_arr(&batch_id.elements, &batch.id().0)?;

    let some_value = Value::from(42);
    // args: first wildcard is "x" = some_value, rest are padding
    let mut args_values = vec![some_value.clone()];
    for _ in 1..params.max_custom_predicate_wildcards {
        args_values.push(Value::from(EMPTY_VALUE));
    }
    for (target, value) in args_target.iter().zip(args_values.iter()) {
        target.set_targets(&mut pw, value)?;
    }

    // Expected statement: Equal(Literal(some_value), Literal(pred_a_hash))
    let expected_st: crate::backends::plonky2::mainpod::Statement =
        Statement::equal(some_value, expected_pred_a_value).into();
    expected_st_target.set_targets(&mut pw, &expected_st)?;

    // Build and verify
    let data = builder.build::<C>();
    let proof = data.prove(pw)?;
    data.verify(proof)?;

    Ok(())
}

fn custom_pred_verify_hash_table_lookup(index: usize, expected_hash: HashOut) -> Result<()> {
    let params = Params::default();
    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::new(config);

    // `new` seeds the sentinel at index 0, so the two real rows land at indices 1 and 2.
    let mut custom_pred_verify_hashes = MuxTableTarget::new(&mut builder, &params);
    let hash0 = builder.constant_hash(HashOut {
        elements: [F(11), F(12), F(13), F(14)],
    });
    let hash1 = builder.constant_hash(HashOut {
        elements: [F(21), F(22), F(23), F(24)],
    });
    custom_pred_verify_hashes.push(hash0);
    custom_pred_verify_hashes.push(hash1);

    let index_target = IndexTarget::new_virtual(3, &mut builder);
    let resolved_query_hash = custom_pred_verify_hashes.get(&mut builder, &index_target);
    let expected_hash_target = builder.constant_hash(expected_hash);
    builder.connect_hashes(resolved_query_hash, expected_hash_target);

    let mut pw = PartialWitness::<F>::new();
    index_target.set_targets(&mut pw, index)?;
    let data = builder.build::<C>();
    let proof = data.prove(pw)?;
    data.verify(proof)?;
    Ok(())
}

#[test]
fn test_custom_pred_verify_hash_table_index_selection() {
    let hash0 = HashOut {
        elements: [F(11), F(12), F(13), F(14)],
    };
    // hash0 sits at index 1 (index 0 is the sentinel); index 2 holds the other row.
    custom_pred_verify_hash_table_lookup(1, hash0).unwrap();
    assert!(custom_pred_verify_hash_table_lookup(2, hash0).is_err());
}

/// Build a custom-verify query hash over fresh virtual targets for the given components and record
/// their witness values, returning the query-hash target.
fn build_custom_query_side(
    builder: &mut crate::backends::plonky2::basetypes::CircuitBuilder,
    pw: &mut PartialWitness<F>,
    st: HashOut,
    op: &OperationType,
    op_args: &[HashOut],
) -> Result<HashOutTarget> {
    let st_target = builder.add_virtual_hash();
    let op_target = builder.add_virtual_operation_type();
    let arg_targets: Vec<_> = op_args.iter().map(|_| builder.add_virtual_hash()).collect();
    let query_hash =
        hash_custom_predicate_verify_query(builder, &st_target, &op_target, &arg_targets);

    pw.set_hash_target(st_target, st)?;
    op_target.set_targets(pw, op)?;
    for (target, hash) in arg_targets.iter().zip(op_args) {
        pw.set_hash_target(*target, *hash)?;
    }
    Ok(query_hash)
}

/// Build two custom-verify query hashes from full components and require them to be equal, so a
/// mismatch surfaces as a prove failure. A test varies one component (statement hash, op type, or
/// op args) across the two sides to check that component is bound into the query hash.
fn custom_query_hashes_match(
    lhs: (HashOut, &OperationType, &[HashOut]),
    rhs: (HashOut, &OperationType, &[HashOut]),
) -> Result<()> {
    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::new(config);
    let mut pw = PartialWitness::<F>::new();

    let lhs_query_hash = build_custom_query_side(&mut builder, &mut pw, lhs.0, lhs.1, lhs.2)?;
    let rhs_query_hash = build_custom_query_side(&mut builder, &mut pw, rhs.0, rhs.1, rhs.2)?;
    builder.connect_hashes(lhs_query_hash, rhs_query_hash);

    let data = builder.build::<C>();
    let proof = data.prove(pw)?;
    data.verify(proof)?;
    Ok(())
}

#[test]
fn test_custom_query_hash_is_sensitive_to_op_arg_order_and_content() {
    let st = HashOut {
        elements: [F(101), F(102), F(103), F(104)],
    };
    let op = OperationType::Native(NativeOperation::None);
    let hash_a = HashOut {
        elements: [F(1), F(2), F(3), F(4)],
    };
    let hash_b = HashOut {
        elements: [F(5), F(6), F(7), F(8)],
    };
    let hash_c = HashOut {
        elements: [F(9), F(10), F(11), F(12)],
    };

    custom_query_hashes_match((st, &op, &[hash_a, hash_b]), (st, &op, &[hash_a, hash_b])).unwrap();
    assert!(
        custom_query_hashes_match((st, &op, &[hash_a, hash_b]), (st, &op, &[hash_b, hash_a]))
            .is_err()
    );
    assert!(
        custom_query_hashes_match((st, &op, &[hash_a, hash_b]), (st, &op, &[hash_a, hash_c]))
            .is_err()
    );
}

#[test]
fn test_custom_query_hash_is_sensitive_to_statement_and_op_type() {
    let st_a = HashOut {
        elements: [F(1), F(2), F(3), F(4)],
    };
    let st_b = HashOut {
        elements: [F(5), F(6), F(7), F(8)],
    };
    let op_arg = HashOut {
        elements: [F(9), F(10), F(11), F(12)],
    };
    let op_a = OperationType::Native(NativeOperation::None);
    let op_b = OperationType::Native(NativeOperation::ContainsFromEntries);

    // Identical components agree.
    custom_query_hashes_match((st_a, &op_a, &[op_arg]), (st_a, &op_a, &[op_arg])).unwrap();
    // The statement hash is bound into the query.
    assert!(custom_query_hashes_match((st_a, &op_a, &[op_arg]), (st_b, &op_a, &[op_arg])).is_err());
    // The op type is bound into the query.
    assert!(custom_query_hashes_match((st_a, &op_a, &[op_arg]), (st_a, &op_b, &[op_arg])).is_err());
}

/// Build one query of every aux kind over deliberately-overlapping field values, so only the kind
/// (and field shape) separates them, and require all the resulting hashes to be pairwise distinct.
/// Soundness rests on each kind folding a distinct prefix into its hash; this is the one place that
/// exercises every kind at once, so a duplicate `OperationAuxQueryKind` value or a dropped prefix
/// that let one kind's row satisfy another's verify circuit shows up as a collision here.
#[test]
fn test_aux_query_kinds_are_pairwise_distinct() -> Result<()> {
    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::new(config);

    // Reuse the same data across kinds so the kind, not the data, is what separates the hashes.
    let h_a = builder.constant_hash(HashOut {
        elements: [F(1), F(2), F(3), F(4)],
    });
    let h_b = builder.constant_hash(HashOut {
        elements: [F(5), F(6), F(7), F(8)],
    });
    let v_a = builder.constant_value(RawValue::from(1));
    let v_b = builder.constant_value(RawValue::from(2));
    // Give the transition query the delete op: that is the worst case for a collision with the
    // delete query (both describe a delete), so distinctness here means only the kind separates them.
    let op = builder.constant(F::from_canonical_u8(MerkleTreeOp::Delete as u8));
    let op_type = builder.add_virtual_operation_type();
    let op_arg_hashes = vec![h_a, h_b];

    let hashes = [
        hash_merkle_contains_query(&mut builder, h_a, v_a, v_b),
        hash_merkle_not_contains_query(&mut builder, h_a, v_a),
        hash_merkle_transition_query(&mut builder, op, h_a, h_b, v_a, v_b),
        hash_merkle_delete_query(&mut builder, h_a, h_b, v_a),
        hash_statement_query(&mut builder, &h_a),
        hash_pair_query(&mut builder, OperationAuxQueryKind::PublicKeyOf, h_a, h_b),
        hash_pair_query(&mut builder, OperationAuxQueryKind::SignedBy, h_a, h_b),
        hash_custom_predicate_verify_query(&mut builder, &h_a, &op_type, &op_arg_hashes),
    ];
    for hash in &hashes {
        builder.register_public_inputs(&hash.elements);
    }

    let mut pw = PartialWitness::<F>::new();
    op_type.set_targets(&mut pw, &OperationType::Native(NativeOperation::None))?;
    let data = builder.build::<C>();
    let proof = data.prove(pw)?;
    let out: Vec<HashOut> = proof
        .public_inputs
        .chunks(4)
        .map(|c| HashOut {
            elements: [c[0], c[1], c[2], c[3]],
        })
        .collect();
    data.verify(proof)?;

    assert_eq!(out.len(), hashes.len());
    for i in 0..out.len() {
        for j in (i + 1)..out.len() {
            assert_ne!(out[i], out[j], "aux query kinds {i} and {j} collide");
        }
    }
    Ok(())
}

/// Drives `verify_custom_circuit` against an aux table whose only real entry stores
/// the hash of `(stored_st, stored_op_type, stored_op_args)`.
/// The verify-side query is `(verify_st, verify_op_type, verify_op_args)` and points
/// at row `aux_index_value`. The proof should succeed iff both queries agree and the
/// index lands on the real row.
fn helper_verify_custom_mutation(
    stored_st: &Statement,
    stored_op_type: &OperationType,
    stored_op_args: &[Statement],
    verify_st: &Statement,
    verify_op_type: &OperationType,
    verify_op_args: &[Statement],
    aux_index_value: usize,
) -> Result<()> {
    let params = Params::default();
    let pad = |v: &[Statement]| {
        assert!(v.len() <= BASE_PARAMS.max_operation_args);
        let mut padded = v.to_vec();
        while padded.len() < BASE_PARAMS.max_operation_args {
            padded.push(Statement::None);
        }
        padded
    };
    let stored_op_args = pad(stored_op_args);
    let verify_op_args = pad(verify_op_args);

    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::new(config);

    let stored_st_target = builder.add_virtual_statement(false);
    let stored_op_type_target = builder.add_virtual_operation_type();
    let stored_op_args_target: Vec<_> = (0..BASE_PARAMS.max_operation_args)
        .map(|_| builder.add_virtual_statement(false))
        .collect();
    let stored_st_hash = stored_st_target.hash(&mut builder);
    let stored_op_arg_hashes: Vec<_> = stored_op_args_target
        .iter()
        .map(|op_arg| op_arg.hash(&mut builder))
        .collect();
    let stored_hash = hash_custom_predicate_verify_query(
        &mut builder,
        &stored_st_hash,
        &stored_op_type_target,
        &stored_op_arg_hashes,
    );

    let mut tbl = MuxTableTarget::new(&mut builder, &params);
    tbl.push(stored_hash);

    let verify_st_target = builder.add_virtual_statement(false);
    let verify_op_type_target = builder.add_virtual_operation_type();
    let verify_op_args_target: Vec<_> = (0..BASE_PARAMS.max_operation_args)
        .map(|_| builder.add_virtual_statement(false))
        .collect();
    let verify_st_hash = verify_st_target.hash(&mut builder);
    let verify_op_arg_hashes: Vec<_> = verify_op_args_target
        .iter()
        .map(|op_arg| op_arg.hash(&mut builder))
        .collect();
    let aux_index = IndexTarget::new_virtual(2, &mut builder);
    let resolved_aux = tbl.get(&mut builder, &aux_index);

    let ok = verify_custom_circuit(
        &mut builder,
        &verify_st_hash,
        &verify_op_type_target,
        resolved_aux,
        &verify_op_arg_hashes,
    );
    builder.assert_one(ok.target);

    let mut pw = PartialWitness::<F>::new();
    stored_st_target.set_targets(&mut pw, &stored_st.clone().into())?;
    stored_op_type_target.set_targets(&mut pw, stored_op_type)?;
    for (t, s) in stored_op_args_target.iter().zip(stored_op_args.iter()) {
        t.set_targets(&mut pw, &s.clone().into())?;
    }
    verify_st_target.set_targets(&mut pw, &verify_st.clone().into())?;
    verify_op_type_target.set_targets(&mut pw, verify_op_type)?;
    for (t, s) in verify_op_args_target.iter().zip(verify_op_args.iter()) {
        t.set_targets(&mut pw, &s.clone().into())?;
    }
    aux_index.set_targets(&mut pw, aux_index_value)?;

    let data = builder.build::<C>();
    let proof = data.prove(pw)?;
    data.verify(proof)?;
    Ok(())
}

/// Builds the test predicate `p(id, secret_id) = AND(Equal(id["score"], 42),
/// Equal(secret_id["key"], id["score"]))` and returns the public ref to predicate 0.
fn make_score_key_predicate(params: &Params) -> frontend::Result<CustomPredicateRef> {
    use NativePredicate as NP;
    use StatementTmplBuilder as STB;
    let mut cpb = CustomPredicateBatchBuilder::new(params.clone(), "batch".into());
    let stb0 = STB::new_from_pred(NP::Equal)
        .arg(("id", "score"))
        .arg(literal(42));
    let stb1 = STB::new_from_pred(NP::Equal)
        .arg(("secret_id", "key"))
        .arg(("id", "score"));
    cpb.predicate_and("p", &["id"], &["secret_id"], &[stb0, stb1])?;
    let batch = cpb.finish()?;
    Ok(CustomPredicateRef::new(batch, 0))
}

#[test]
fn test_verify_custom_circuit_hash_binding() -> frontend::Result<()> {
    let params = Params::default();
    let cp = make_score_key_predicate(&params)?;

    let dict = Hash([F(1), F(2), F(3), F(4)]);
    let secret_dict = Hash([F(6), F(7), F(8), F(9)]);
    let op_args = vec![
        Statement::equal(AnchoredKey::new(dict, Key::from("score")), Value::from(42)),
        Statement::equal(
            AnchoredKey::new(secret_dict, Key::from("key")),
            AnchoredKey::new(dict, Key::from("score")),
        ),
    ];
    let st = Statement::Custom(cp.clone(), vec![value_ref(Value::from(dict)), value_ref(0)]);
    let op_type = OperationType::Custom(cp);

    // Positive: identical inputs at the real row.
    helper_verify_custom_mutation(&st, &op_type, &op_args, &st, &op_type, &op_args, 1).unwrap();

    // aux_index points at the sentinel row, whose zero hash can't match the query hash.
    assert!(
        helper_verify_custom_mutation(&st, &op_type, &op_args, &st, &op_type, &op_args, 0).is_err()
    );

    // Swap two op_args -> hash includes positions, must fail.
    let mut swapped = op_args.clone();
    swapped.swap(0, 1);
    assert!(
        helper_verify_custom_mutation(&st, &op_type, &op_args, &st, &op_type, &swapped, 1).is_err()
    );

    // Mutate one op_arg's literal -> hash diverges, must fail.
    let mut bad_arg = op_args.clone();
    bad_arg[0] = Statement::equal(
        AnchoredKey::new(dict, Key::from("score")),
        Value::from(0xbad),
    );
    assert!(
        helper_verify_custom_mutation(&st, &op_type, &op_args, &st, &op_type, &bad_arg, 1).is_err()
    );

    // Mutate the statement -> hash diverges, must fail.
    assert!(helper_verify_custom_mutation(
        &st,
        &op_type,
        &op_args,
        &Statement::None,
        &op_type,
        &op_args,
        1,
    )
    .is_err());

    Ok(())
}

/// Drives `verify_operation_circuit` against a real custom-predicate aux scenario.
/// Builds the predicates table and the split aux tables via the production
/// `build_operation_aux_table_circuit`. Tests vary `aux` to point the operation at
/// different rows in the aux table.
#[allow(clippy::too_many_arguments)]
fn helper_verify_operation_through_aux_table(
    params: &Params,
    custom_predicates: &[CustomPredicateRef],
    custom_predicate_verifications: &[CustomPredicateVerification],
    st: mainpod::Statement,
    op_type: OperationType,
    op_args_indices: Vec<OperationArg>,
    prev_statements: Vec<mainpod::Statement>,
    aux: OperationAux,
) -> Result<()> {
    assert_eq!(custom_predicates.len(), params.max_custom_predicates);
    assert_eq!(
        custom_predicate_verifications.len(),
        params.max_custom_predicate_verification_ops
    );

    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::new(config);

    let st_target = builder.add_virtual_statement(false);
    let op_target = builder.add_virtual_operation(params);
    let prev_statements_target: Vec<_> = (0..prev_statements.len())
        .map(|_| builder.add_virtual_statement(false))
        .collect();
    let prev_statement_flatteneds_target: Vec<Vec<Target>> = prev_statements_target
        .iter()
        .map(|st| st.flatten())
        .collect();
    let prev_statement_hashes_target: Vec<_> = prev_statement_flatteneds_target
        .iter()
        .map(|flat| builder.hash_n_to_hash_no_pad::<PoseidonHash>(flat.clone()))
        .collect();

    let custom_predicates_target: Vec<_> = (0..params.max_custom_predicates)
        .map(|_| CustomPredicateInBatchTarget::new_virtual(&mut builder))
        .collect();
    let custom_predicate_verifications_target: Vec<_> = (0..params
        .max_custom_predicate_verification_ops)
        .map(|_| CustomPredicateVerifyEntryTarget::new_virtual(params, &mut builder))
        .collect();

    let custom_predicate_table =
        build_custom_predicate_table_circuit(params, &mut builder, &custom_predicates_target)?;

    // Construct an AuxTableInputTargets that has only the custom_predicate_verifications populated;
    // the other capacities are zero in this test's params, so the other vectors stay empty.
    let aux_table_input = AuxTableInputTargets {
        merkle_proofs: MerkleProofsTarget::new_virtual(params, &mut builder),
        merkle_transition_proofs: MerkleTransitionProofsTarget::new_virtual(params, &mut builder),
        open_input_statements: (0..params.max_open_input_statement_ops)
            .map(|_| OpenInputStatementTarget::new_virtual(&mut builder))
            .collect(),
        public_key_sks: (0..params.max_public_key_ops)
            .map(|_| builder.add_virtual_biguint320_target())
            .collect(),
        signed_bys: (0..params.max_signed_by_ops)
            .map(|_| SignedByTarget::new_virtual(&mut builder))
            .collect(),
        custom_predicate_verifications: custom_predicate_verifications_target.clone(),
    };

    let aux_tables = build_operation_aux_table_circuit(
        params,
        &mut builder,
        &custom_predicate_table,
        &[],
        &aux_table_input,
    )?;

    let st_hash_target = st_target.hash(&mut builder);
    verify_operation_circuit(
        params,
        &mut builder,
        StatementWithHash {
            statement: &st_target,
            hash: st_hash_target,
        },
        &op_target,
        &prev_statement_flatteneds_target,
        &prev_statement_hashes_target,
        &aux_tables,
    )?;

    let op = mainpod::Operation(op_type, op_args_indices, aux);

    let mut pw = PartialWitness::<F>::new();
    st_target.set_targets(&mut pw, &st)?;
    op_target.set_targets(&mut pw, params, &op)?;
    for (t, s) in prev_statements_target.iter().zip(prev_statements.iter()) {
        t.set_targets(&mut pw, s)?;
    }
    for (cp_target, cpr) in custom_predicates_target
        .iter()
        .zip(custom_predicates.iter())
    {
        let mtp = cpr
            .batch
            .mt()
            .prove(&Value::from(cpr.index as i64).raw())
            .expect("predicate index exists in batch MT")
            .1;
        cp_target.set_targets(&mut pw, cpr, &mtp)?;
    }
    for (cpv_target, cpv) in custom_predicate_verifications_target
        .iter()
        .zip(custom_predicate_verifications.iter())
    {
        cpv_target.set_targets(&mut pw, params, cpv)?;
    }

    let data = builder.build::<C>();
    let proof = data.prove(pw)?;
    data.verify(proof)?;
    Ok(())
}

#[test]
fn test_verify_operation_custom_aux_index_binding() -> frontend::Result<()> {
    let params = Params {
        max_input_pods: 0,
        max_open_input_statement_ops: 0,
        max_custom_predicates: 1,
        max_custom_predicate_verification_ops: 2,
        max_custom_predicate_wildcards: 4,
        max_public_key_ops: 0,
        max_signed_by_ops: 0,
        containers: middleware::ParamsContainers {
            state_ops: middleware::ParamsMerkleProofs {
                max_small: 0,
                max_medium: 0,
            },
            transition_ops: middleware::ParamsMerkleProofs {
                max_small: 0,
                max_medium: 0,
            },
            ..middleware::ParamsContainers::default()
        },
        ..Params::default()
    };
    let cp = make_score_key_predicate(&params)?;

    // Two distinct scenarios that both validate the predicate, so each produces a different
    // CustomPredVerify row in the aux table (different op_args -> different stored hash).
    let scenario = |id_seed: F, secret_seed: F| -> (Statement, Vec<Statement>) {
        let id = Hash([id_seed, F(2), F(3), F(4)]);
        let secret = Hash([secret_seed, F(7), F(8), F(9)]);
        let op_args = vec![
            Statement::equal(AnchoredKey::new(id, Key::from("score")), Value::from(42)),
            Statement::equal(
                AnchoredKey::new(secret, Key::from("key")),
                AnchoredKey::new(id, Key::from("score")),
            ),
        ];
        let st = Statement::Custom(cp.clone(), vec![value_ref(Value::from(id))]);
        (st, op_args)
    };
    let (st_a, op_args_a) = scenario(F(1), F(6));
    let (st_b, op_args_b) = scenario(F(11), F(16));

    // Use the production extraction routines so the test exercises the same wildcard
    // derivation and aux-index assignment as MainPodBuilder.
    let mid_ops = vec![
        crate::middleware::Operation::Custom(cp.clone(), op_args_a.clone()),
        crate::middleware::Operation::Custom(cp.clone(), op_args_b),
    ];
    let mid_sts = vec![st_a.clone(), st_b];
    let custom_predicates = extract_custom_predicates(&params, &mid_ops)?;
    let mut aux_list = vec![OperationAux::None; mid_ops.len()];
    let custom_predicate_verifications = extract_custom_predicate_verifications(
        &params,
        &mut aux_list,
        &mid_ops,
        &mid_sts,
        &custom_predicates,
    )?;

    // prev_statements[0] = Statement::None so that op_arg padding (OperationArg::None,
    // which resolves to Index(0)) matches the Statement::None padding inside the cpv entry.
    let prev_statements: Vec<mainpod::Statement> = std::iter::once(Statement::None)
        .chain(op_args_a.iter().cloned())
        .map(|s| s.into())
        .collect();
    let st_a_mp: mainpod::Statement = st_a.into();
    let op_type = OperationType::Custom(cp);
    let op_args_indices = vec![OperationArg::Index(1), OperationArg::Index(2)];

    // Positive: aux points at the real custom row.
    helper_verify_operation_through_aux_table(
        &params,
        &custom_predicates,
        &custom_predicate_verifications,
        st_a_mp.clone(),
        op_type.clone(),
        op_args_indices.clone(),
        prev_statements.clone(),
        OperationAux::CustomPredVerifyIndex(0),
    )
    .unwrap();

    // Mutation: aux points at the leading sentinel row (non-custom slot), whose zero hash can't
    // match the recomputed query hash.
    assert!(helper_verify_operation_through_aux_table(
        &params,
        &custom_predicates,
        &custom_predicate_verifications,
        st_a_mp.clone(),
        op_type.clone(),
        op_args_indices.clone(),
        prev_statements.clone(),
        OperationAux::None,
    )
    .is_err());

    // Mutation: aux points at the other custom row, whose stored hash binds different op_args, so
    // the recomputed query hash does not match.
    assert!(helper_verify_operation_through_aux_table(
        &params,
        &custom_predicates,
        &custom_predicate_verifications,
        st_a_mp,
        op_type,
        op_args_indices,
        prev_statements,
        OperationAux::CustomPredVerifyIndex(1),
    )
    .is_err());

    Ok(())
}
