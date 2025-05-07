use std::{array, sync::Arc};

use itertools::zip_eq;
use plonky2::{
    hash::{hash_types::HashOutTarget, poseidon::PoseidonHash},
    iop::{
        target::{BoolTarget, Target},
        witness::PartialWitness,
    },
    plonk::circuit_builder::CircuitBuilder,
};

use crate::{
    backends::plonky2::{
        basetypes::D,
        circuits::{
            common::{
                CircuitBuilderPod, CustomPredicateBatchTarget, CustomPredicateTarget, Flattenable,
                MerkleClaimTarget, OperationTarget, PredicateTarget, StatementArgTarget,
                StatementTarget, ValueTarget,
            },
            signedpod::{SignedPodVerifyGadget, SignedPodVerifyTarget},
        },
        error::Result,
        mainpod,
        primitives::merkletree::{
            MerkleClaimAndProof, MerkleClaimAndProofTarget, MerkleProofGadget,
        },
        signedpod::SignedPod,
    },
    middleware::{
        AnchoredKey, CustomPredicateBatch, NativeOperation, NativePredicate, Params, PodType,
        Statement, StatementArg, ToFields, Value, F, KEY_TYPE, SELF, VALUE_SIZE,
    },
};

//
// MainPod verification
//

struct OperationVerifyGadget {
    params: Params,
}

impl OperationVerifyGadget {
    /// Checks whether the first `N` arguments to an op are ValueOf
    /// statements, returning a boolean target indicating whether this
    /// is the case as well as the value targets derived from each
    /// argument.
    fn first_n_args_as_values<const N: usize>(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        resolved_op_args: &[StatementTarget],
    ) -> (BoolTarget, [ValueTarget; N]) {
        let arg_is_valueof = resolved_op_args[..N]
            .iter()
            .map(|arg| {
                let st_type_ok =
                    arg.has_native_type(builder, &self.params, NativePredicate::ValueOf);
                let value_arg_ok = builder.statement_arg_is_value(&arg.args[1]);
                builder.and(st_type_ok, value_arg_ok)
            })
            .collect::<Vec<_>>();
        let first_n_args_are_valueofs = arg_is_valueof
            .into_iter()
            .reduce(|a, b| builder.and(a, b))
            .expect("No args specified.");
        let values = array::from_fn(|i| resolved_op_args[i].args[1].as_value());
        (first_n_args_are_valueofs, values)
    }

    fn eval(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        st: &StatementTarget,
        op: &OperationTarget,
        prev_statements: &[StatementTarget],
        merkle_claims: &[MerkleClaimTarget],
    ) -> Result<()> {
        let _true = builder._true();
        let _false = builder._false();

        // Verify that the operation `op` correctly generates the statement `st`.  The operation
        // can reference any of the `prev_statements`.
        // TODO: Clean this up.
        let resolved_op_args = if prev_statements.is_empty() {
            vec![]
        } else {
            op.args
                .iter()
                .flatten()
                .map(|&i| builder.vec_ref(&self.params, prev_statements, i))
                .collect::<Vec<_>>()
        };
        // Certain operations (Contains/NotContains) will refer to one
        // of the provided Merkle proofs (if any). These proofs have already
        // been verified, so we need only look up the claim.
        let resolved_merkle_claim = (!merkle_claims.is_empty())
            .then(|| builder.vec_ref(&self.params, merkle_claims, op.aux[0]));

        // The verification may require aux data which needs to be stored in the
        // `OperationVerifyTarget` so that we can set during witness generation.

        // For now only support native operations
        // Op checks to carry out. Each 'eval_X' should
        // be thought of as 'eval' restricted to the op of type X,
        // where the returned target is `false` if the input targets
        // lie outside of the domain.
        let op_checks = [
            vec![
                self.eval_none(builder, st, op),
                self.eval_new_entry(builder, st, op, prev_statements),
            ],
            // Skip these if there are no resolved op args
            if resolved_op_args.is_empty() {
                vec![]
            } else {
                vec![
                    self.eval_copy(builder, st, op, &resolved_op_args)?,
                    self.eval_eq_neq_from_entries(builder, st, op, &resolved_op_args),
                    self.eval_lt_lteq_from_entries(builder, st, op, &resolved_op_args),
                    self.eval_transitive_eq(builder, st, op, &resolved_op_args),
                    self.eval_lt_to_neq(builder, st, op, &resolved_op_args),
                    self.eval_hash_of(builder, st, op, &resolved_op_args),
                ]
            },
            // Skip these if there are no resolved Merkle claims
            if let Some(resolved_merkle_claim) = resolved_merkle_claim {
                vec![
                    self.eval_contains_from_entries(
                        builder,
                        st,
                        op,
                        resolved_merkle_claim,
                        &resolved_op_args,
                    ),
                    self.eval_not_contains_from_entries(
                        builder,
                        st,
                        op,
                        resolved_merkle_claim,
                        &resolved_op_args,
                    ),
                ]
            } else {
                vec![]
            },
        ]
        .concat();

        let ok = builder.any(op_checks);

        builder.connect(ok.target, _true.target);

        Ok(())
    }

    fn eval_contains_from_entries(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        st: &StatementTarget,
        op: &OperationTarget,
        resolved_merkle_claim: MerkleClaimTarget,
        resolved_op_args: &[StatementTarget],
    ) -> BoolTarget {
        let op_code_ok = op.has_native_type(builder, NativeOperation::ContainsFromEntries);

        let (arg_types_ok, [merkle_root_value, key_value, value_value]) =
            self.first_n_args_as_values(builder, resolved_op_args);

        // Check Merkle proof (verified elsewhere) against op args.
        let merkle_proof_checks = [
            /* The supplied Merkle proof must be enabled. */
            resolved_merkle_claim.enabled,
            /* ...and it must be an existence proof. */
            resolved_merkle_claim.existence,
            /* ...for the root-key-value triple in the resolved op args. */
            builder.is_equal_slice(
                &merkle_root_value.elements,
                &resolved_merkle_claim.root.elements,
            ),
            builder.is_equal_slice(&key_value.elements, &resolved_merkle_claim.key.elements),
            builder.is_equal_slice(&value_value.elements, &resolved_merkle_claim.value.elements),
        ];

        let merkle_proof_ok = builder.all(merkle_proof_checks);

        // Check output statement
        let arg1_key = resolved_op_args[0].args[0].clone();
        let arg2_key = resolved_op_args[1].args[0].clone();
        let arg3_key = resolved_op_args[2].args[0].clone();
        let expected_statement = StatementTarget::new_native(
            builder,
            &self.params,
            NativePredicate::Contains,
            &[arg1_key, arg2_key, arg3_key],
        );
        let st_ok = builder.is_equal_flattenable(st, &expected_statement);

        builder.all([op_code_ok, arg_types_ok, merkle_proof_ok, st_ok])
    }

    fn eval_not_contains_from_entries(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        st: &StatementTarget,
        op: &OperationTarget,
        resolved_merkle_claim: MerkleClaimTarget,
        resolved_op_args: &[StatementTarget],
    ) -> BoolTarget {
        let op_code_ok = op.has_native_type(builder, NativeOperation::NotContainsFromEntries);

        let (arg_types_ok, [merkle_root_value, key_value]) =
            self.first_n_args_as_values(builder, resolved_op_args);

        // Check Merkle proof (verified elsewhere) against op args.
        let merkle_proof_checks = [
            /* The supplied Merkle proof must be enabled. */
            resolved_merkle_claim.enabled,
            /* ...and it must be a nonexistence proof. */
            builder.not(resolved_merkle_claim.existence),
            /* ...for the root-key pair in the resolved op args. */
            builder.is_equal_slice(
                &merkle_root_value.elements,
                &resolved_merkle_claim.root.elements,
            ),
            builder.is_equal_slice(&key_value.elements, &resolved_merkle_claim.key.elements),
        ];

        let merkle_proof_ok = builder.all(merkle_proof_checks);

        // Check output statement
        let arg1_key = resolved_op_args[0].args[0].clone();
        let arg2_key = resolved_op_args[1].args[0].clone();
        let expected_statement = StatementTarget::new_native(
            builder,
            &self.params,
            NativePredicate::NotContains,
            &[arg1_key, arg2_key],
        );
        let st_ok = builder.is_equal_flattenable(st, &expected_statement);

        builder.all([op_code_ok, arg_types_ok, merkle_proof_ok, st_ok])
    }

    /// Carries out the checks necessary for EqualFromEntries and
    /// NotEqualFromEntries.
    fn eval_eq_neq_from_entries(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        st: &StatementTarget,
        op: &OperationTarget,
        resolved_op_args: &[StatementTarget],
    ) -> BoolTarget {
        let eq_op_st_code_ok = {
            let op_code_ok = op.has_native_type(builder, NativeOperation::EqualFromEntries);
            let st_code_ok = st.has_native_type(builder, &self.params, NativePredicate::Equal);
            builder.and(op_code_ok, st_code_ok)
        };
        let neq_op_st_code_ok = {
            let op_code_ok = op.has_native_type(builder, NativeOperation::NotEqualFromEntries);
            let st_code_ok = st.has_native_type(builder, &self.params, NativePredicate::NotEqual);
            builder.and(op_code_ok, st_code_ok)
        };
        let op_st_code_ok = builder.or(eq_op_st_code_ok, neq_op_st_code_ok);

        let (arg_types_ok, [arg1_value, arg2_value]) =
            self.first_n_args_as_values(builder, resolved_op_args);

        let op_args_eq = builder.is_equal_slice(&arg1_value.elements, &arg2_value.elements);
        let op_args_ok = builder.is_equal(op_args_eq.target, eq_op_st_code_ok.target);

        let arg1_key = resolved_op_args[0].args[0].clone();
        let arg2_key = resolved_op_args[1].args[0].clone();

        let expected_st_args: Vec<_> = [arg1_key, arg2_key]
            .into_iter()
            .chain(std::iter::repeat_with(|| StatementArgTarget::none(builder)))
            .take(self.params.max_statement_args)
            .flat_map(|arg| arg.elements)
            .collect();

        let st_args_ok = builder.is_equal_slice(
            &expected_st_args,
            &st.args
                .iter()
                .flat_map(|arg| arg.elements)
                .collect::<Vec<_>>(),
        );

        builder.all([op_st_code_ok, arg_types_ok, op_args_ok, st_args_ok])
    }

    /// Carries out the checks necessary for LtFromEntries and
    /// LtEqFromEntries.
    fn eval_lt_lteq_from_entries(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        st: &StatementTarget,
        op: &OperationTarget,
        resolved_op_args: &[StatementTarget],
    ) -> BoolTarget {
        let zero = ValueTarget::zero(builder);
        let one = ValueTarget::one(builder);

        let lt_op_st_code_ok = {
            let op_code_ok = op.has_native_type(builder, NativeOperation::LtFromEntries);
            let st_code_ok = st.has_native_type(builder, &self.params, NativePredicate::Lt);
            builder.and(op_code_ok, st_code_ok)
        };
        let lteq_op_st_code_ok = {
            let op_code_ok = op.has_native_type(builder, NativeOperation::LtEqFromEntries);
            let st_code_ok = st.has_native_type(builder, &self.params, NativePredicate::LtEq);
            builder.and(op_code_ok, st_code_ok)
        };
        let op_st_code_ok = builder.or(lt_op_st_code_ok, lteq_op_st_code_ok);

        let (arg_types_ok, [arg1_value, arg2_value]) =
            self.first_n_args_as_values(builder, resolved_op_args);

        // If we are not dealing with the right op & statement types,
        // replace args with dummy values in the following checks.
        let value1 = builder.select_value(op_st_code_ok, arg1_value, zero);
        let value2 = builder.select_value(op_st_code_ok, arg2_value, one);

        // Range check
        builder.assert_i64(value1);
        builder.assert_i64(value2);

        // Check for equality.
        let args_equal = builder.is_equal_slice(&value1.elements, &value2.elements);

        // Check < if applicable.
        let lt_check_flag = {
            let not_args_equal = builder.not(args_equal);
            let lteq_eq_case = builder.and(lteq_op_st_code_ok, not_args_equal);
            builder.or(lt_op_st_code_ok, lteq_eq_case)
        };
        builder.assert_i64_less_if(lt_check_flag, value1, value2);

        let arg1_key = resolved_op_args[0].args[0].clone();
        let arg2_key = resolved_op_args[1].args[0].clone();

        let expected_st_args: Vec<_> = [arg1_key, arg2_key]
            .into_iter()
            .chain(std::iter::repeat_with(|| StatementArgTarget::none(builder)))
            .take(self.params.max_statement_args)
            .flat_map(|arg| arg.elements)
            .collect();

        let st_args_ok = builder.is_equal_slice(
            &expected_st_args,
            &st.args
                .iter()
                .flat_map(|arg| arg.elements)
                .collect::<Vec<_>>(),
        );

        builder.all([op_st_code_ok, arg_types_ok, st_args_ok])
    }

    fn eval_hash_of(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        st: &StatementTarget,
        op: &OperationTarget,
        resolved_op_args: &[StatementTarget],
    ) -> BoolTarget {
        let op_code_ok = op.has_native_type(builder, NativeOperation::HashOf);

        let (arg_types_ok, [arg1_value, arg2_value, arg3_value]) =
            self.first_n_args_as_values(builder, resolved_op_args);

        let expected_hash_value = builder.hash_values(arg2_value, arg3_value);

        let hash_value_ok =
            builder.is_equal_slice(&arg1_value.elements, &expected_hash_value.elements);

        let arg1_key = resolved_op_args[0].args[0].clone();
        let arg2_key = resolved_op_args[1].args[0].clone();
        let arg3_key = resolved_op_args[2].args[0].clone();
        let expected_statement = StatementTarget::new_native(
            builder,
            &self.params,
            NativePredicate::HashOf,
            &[arg1_key, arg2_key, arg3_key],
        );
        let st_ok = builder.is_equal_flattenable(st, &expected_statement);

        builder.all([op_code_ok, arg_types_ok, hash_value_ok, st_ok])
    }

    fn eval_transitive_eq(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        st: &StatementTarget,
        op: &OperationTarget,
        resolved_op_args: &[StatementTarget],
    ) -> BoolTarget {
        let op_code_ok =
            op.has_native_type(builder, NativeOperation::TransitiveEqualFromStatements);

        let arg1_type_ok =
            resolved_op_args[0].has_native_type(builder, &self.params, NativePredicate::Equal);
        let arg2_type_ok =
            resolved_op_args[1].has_native_type(builder, &self.params, NativePredicate::Equal);
        let arg_types_ok = builder.all([arg1_type_ok, arg2_type_ok]);

        let arg1_key1 = &resolved_op_args[0].args[0];
        let arg1_key2 = &resolved_op_args[0].args[1];
        let arg2_key1 = &resolved_op_args[1].args[0];
        let arg2_key2 = &resolved_op_args[1].args[1];

        let inner_keys_match = builder.is_equal_slice(&arg1_key2.elements, &arg2_key1.elements);

        let expected_statement = StatementTarget::new_native(
            builder,
            &self.params,
            NativePredicate::Equal,
            &[arg1_key1.clone(), arg2_key2.clone()],
        );
        let st_ok = builder.is_equal_flattenable(st, &expected_statement);

        builder.all([op_code_ok, arg_types_ok, inner_keys_match, st_ok])
    }
    fn eval_none(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        st: &StatementTarget,
        op: &OperationTarget,
    ) -> BoolTarget {
        let op_code_ok = op.has_native_type(builder, NativeOperation::None);

        let expected_statement =
            StatementTarget::new_native(builder, &self.params, NativePredicate::None, &[]);
        let st_ok = builder.is_equal_flattenable(st, &expected_statement);

        builder.all([op_code_ok, st_ok])
    }

    fn eval_new_entry(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        st: &StatementTarget,
        op: &OperationTarget,
        prev_statements: &[StatementTarget],
    ) -> BoolTarget {
        let op_code_ok = op.has_native_type(builder, NativeOperation::NewEntry);

        let st_code_ok = st.has_native_type(builder, &self.params, NativePredicate::ValueOf);

        let expected_arg_prefix = builder.constants(
            &StatementArg::Key(AnchoredKey::from((SELF, ""))).to_fields(&self.params)[..VALUE_SIZE],
        );
        let arg_prefix_ok =
            builder.is_equal_slice(&st.args[0].elements[..VALUE_SIZE], &expected_arg_prefix);

        let dupe_check = {
            let individual_checks = prev_statements
                .iter()
                .map(|ps| {
                    let same_predicate = builder.is_equal_flattenable(&st.predicate, &ps.predicate);
                    let same_anchored_key =
                        builder.is_equal_slice(&st.args[0].elements, &ps.args[0].elements);
                    builder.and(same_predicate, same_anchored_key)
                })
                .collect::<Vec<_>>();
            builder.any(individual_checks)
        };

        let no_dupes_ok = builder.not(dupe_check);

        builder.all([op_code_ok, st_code_ok, arg_prefix_ok, no_dupes_ok])
    }

    fn eval_lt_to_neq(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        st: &StatementTarget,
        op: &OperationTarget,
        resolved_op_args: &[StatementTarget],
    ) -> BoolTarget {
        let op_code_ok = op.has_native_type(builder, NativeOperation::LtToNotEqual);

        let arg_type_ok =
            resolved_op_args[0].has_native_type(builder, &self.params, NativePredicate::Lt);

        let arg1_key = resolved_op_args[0].args[0].clone();
        let arg2_key = resolved_op_args[0].args[1].clone();

        let expected_statement = StatementTarget::new_native(
            builder,
            &self.params,
            NativePredicate::NotEqual,
            &[arg1_key, arg2_key],
        );
        let st_ok = builder.is_equal_flattenable(st, &expected_statement);

        builder.all([op_code_ok, arg_type_ok, st_ok])
    }

    fn eval_copy(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        st: &StatementTarget,
        op: &OperationTarget,
        resolved_op_args: &[StatementTarget],
    ) -> Result<BoolTarget> {
        let op_code_ok = op.has_native_type(builder, NativeOperation::CopyStatement);

        let expected_statement = &resolved_op_args[0];
        let st_ok = builder.is_equal_flattenable(st, expected_statement);

        Ok(builder.all([op_code_ok, st_ok]))
    }
}

struct CustomOperationVerifyGadget {
    params: Params,
}

struct CustomPredicateEntryTarget {
    id: HashOutTarget,
    index: Target,
    predicate: CustomPredicateTarget,
}

impl CustomOperationVerifyGadget {
    fn eval(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        st: &StatementTarget,
        op: &OperationTarget,
        op_args: &[StatementTarget], // resolved operation arguments
        args: &[ValueTarget],        // arguments to the custom predicate, public and private
        // Resolved custom predicate
        custom_predicate: &CustomPredicateEntryTarget,
    ) -> Result<BoolTarget> {
        // Some sanity checks
        assert_eq!(self.params.max_operation_args, op_args.len());
        assert_eq!(self.params.max_custom_predicate_wildcards, args.len());

        let (op_is_custom, batch_id, index) = op.type_as_custom(builder);
        let id_ok = builder.is_equal_slice(&batch_id.elements, &custom_predicate.id.elements);
        let index_ok = builder.is_equal(index, custom_predicate.index);

        let expected_predicate = PredicateTarget::new_custom(builder, batch_id, index);
        let arg_none = StatementArgTarget::none(builder);
        let expected_args = (0..self.params.max_statement_args)
            .map(|i| todo!())
            .collect();
        let expected_statement = StatementTarget {
            predicate: expected_predicate,
            args: expected_args,
        };
        let st_ok = builder.is_equal_flattenable(st, &expected_statement);
        Ok(builder.all([id_ok, index_ok, op_is_custom, st_ok]))
    }
}

struct MainPodVerifyGadget {
    params: Params,
}

impl MainPodVerifyGadget {
    fn eval(&self, builder: &mut CircuitBuilder<F, D>) -> Result<MainPodVerifyTarget> {
        let params = &self.params;
        // 1. Verify all input signed pods
        let mut signed_pods = Vec::new();
        for _ in 0..params.max_input_signed_pods {
            let signed_pod = SignedPodVerifyGadget {
                params: params.clone(),
            }
            .eval(builder)?;
            signed_pods.push(signed_pod);
        }

        // Build the statement array
        let mut statements = Vec::new();
        for signed_pod in &signed_pods {
            statements.extend_from_slice(signed_pod.pub_statements(builder, false).as_slice());
        }
        debug_assert_eq!(
            statements.len(),
            self.params.max_input_signed_pods * self.params.max_signed_pod_values
        );
        // TODO: Fill with input main pods
        for _main_pod in 0..self.params.max_input_main_pods {
            for _statement in 0..self.params.max_public_statements {
                statements.push(StatementTarget::new_native(
                    builder,
                    &self.params,
                    NativePredicate::None,
                    &[],
                ))
            }
        }

        // Add the input (private and public) statements and corresponding operations
        let mut operations = Vec::new();
        let input_statements_offset = statements.len();
        for _ in 0..params.max_statements {
            statements.push(builder.add_virtual_statement(params));
            operations.push(builder.add_virtual_operation(params));
        }

        let input_statements = &statements[input_statements_offset..];
        let pub_statements =
            &input_statements[input_statements.len() - params.max_public_statements..];

        // Add Merkle claim/proof targets
        let mp_gadget = MerkleProofGadget {
            max_depth: params.max_depth_mt_gadget,
        };
        let merkle_proofs: Vec<_> = (0..params.max_merkle_proofs)
            .map(|_| mp_gadget.eval(builder))
            .collect::<Result<_>>()?;
        let merkle_claims: Vec<_> = merkle_proofs
            .clone()
            .into_iter()
            .map(|pf| pf.into())
            .collect();

        // Add `CustomPredicateBatch` targets
        let custom_predicate_batches: Vec<_> = (0..params.max_custom_predicate_batches)
            .map(|_| builder.add_virtual_custom_predicate_batch(&self.params))
            .collect();
        let custom_predicate_batch_ids: Vec<_> = custom_predicate_batches
            .iter()
            .map(|cpb| cpb.id(builder))
            .collect();

        // 2. Calculate the Pod Id from the public statements
        let pub_statements_flattened = pub_statements.iter().flat_map(|s| s.flatten()).collect();
        let id = builder.hash_n_to_hash_no_pad::<PoseidonHash>(pub_statements_flattened);

        // 4. Verify type
        let type_statement = &pub_statements[0];
        // TODO: Store this hash in a global static with lazy init so that we don't have to
        // compute it every time.
        let expected_type_statement = StatementTarget::from_flattened(
            &self.params,
            &builder.constants(
                &Statement::ValueOf(
                    AnchoredKey::from((SELF, KEY_TYPE)),
                    Value::from(PodType::MockMain),
                )
                .to_fields(params),
            ),
        );
        builder.connect_flattenable(type_statement, &expected_type_statement);

        // 3. check that all `input_statements` of type `ValueOf` with origin=SELF have unique keys
        // (no duplicates).  We do this in the verification of NewEntry operation.
        // 5. Verify input statements
        for (i, (st, op)) in input_statements.iter().zip(operations.iter()).enumerate() {
            let prev_statements = &statements[..input_statements_offset + i];
            OperationVerifyGadget {
                params: params.clone(),
            }
            .eval(builder, st, op, prev_statements, &merkle_claims)?;
        }

        Ok(MainPodVerifyTarget {
            params: params.clone(),
            id,
            signed_pods,
            statements: input_statements.to_vec(),
            operations,
            merkle_proofs,
            custom_predicate_batches,
        })
    }
}

pub struct MainPodVerifyTarget {
    params: Params,
    id: HashOutTarget,
    signed_pods: Vec<SignedPodVerifyTarget>,
    // The KEY_TYPE statement must be the first public one
    statements: Vec<StatementTarget>,
    operations: Vec<OperationTarget>,
    merkle_proofs: Vec<MerkleClaimAndProofTarget>,
    custom_predicate_batches: Vec<CustomPredicateBatchTarget>,
}

pub struct MainPodVerifyInput {
    pub signed_pods: Vec<SignedPod>,
    pub statements: Vec<mainpod::Statement>,
    pub operations: Vec<mainpod::Operation>,
    pub merkle_proofs: Vec<MerkleClaimAndProof>,
    pub custom_predicate_batches: Vec<Arc<CustomPredicateBatch>>,
}

impl MainPodVerifyTarget {
    pub fn set_targets(
        &self,
        pw: &mut PartialWitness<F>,
        input: &MainPodVerifyInput,
    ) -> Result<()> {
        assert!(input.signed_pods.len() <= self.params.max_input_signed_pods);
        for (i, signed_pod) in input.signed_pods.iter().enumerate() {
            self.signed_pods[i].set_targets(pw, signed_pod)?;
        }
        // Padding
        // TODO: Instead of using an input for padding, use a canonical minimal SignedPod
        let pad_pod = &input.signed_pods[0];
        for i in input.signed_pods.len()..self.params.max_input_signed_pods {
            self.signed_pods[i].set_targets(pw, pad_pod)?;
        }
        assert_eq!(input.statements.len(), self.params.max_statements);
        for (i, (st, op)) in zip_eq(&input.statements, &input.operations).enumerate() {
            self.statements[i].set_targets(pw, &self.params, st)?;
            self.operations[i].set_targets(pw, &self.params, op)?;
        }
        assert!(input.merkle_proofs.len() <= self.params.max_merkle_proofs);
        for (i, mp) in input.merkle_proofs.iter().enumerate() {
            self.merkle_proofs[i].set_targets(pw, true, mp)?;
        }
        // Padding
        let pad_mp = MerkleClaimAndProof::empty();
        for i in input.merkle_proofs.len()..self.params.max_merkle_proofs {
            self.merkle_proofs[i].set_targets(pw, false, &pad_mp)?;
        }
        assert!(input.custom_predicate_batches.len() <= self.params.max_custom_predicate_batches);
        for (i, mp) in input.custom_predicate_batches.iter().enumerate() {
            self.custom_predicate_batches[i].set_targets(pw, &self.params, mp)?;
        }
        // Padding
        let pad_cpb = CustomPredicateBatch::new(&self.params, "empty".to_string(), vec![]);
        for i in input.custom_predicate_batches.len()..self.params.max_custom_predicate_batches {
            self.custom_predicate_batches[i].set_targets(pw, &self.params, &pad_cpb)?;
        }

        Ok(())
    }
}

pub struct MainPodVerifyCircuit {
    pub params: Params,
}

impl MainPodVerifyCircuit {
    pub fn eval(&self, builder: &mut CircuitBuilder<F, D>) -> Result<MainPodVerifyTarget> {
        let main_pod = MainPodVerifyGadget {
            params: self.params.clone(),
        }
        .eval(builder)?;
        builder.register_public_inputs(&main_pod.id.elements);
        Ok(main_pod)
    }
}

#[cfg(test)]
mod tests {
    use plonky2::{
        field::{goldilocks_field::GoldilocksField, types::Field},
        plonk::{circuit_builder::CircuitBuilder, circuit_data::CircuitConfig},
    };

    use super::*;
    use crate::{
        backends::plonky2::{
            basetypes::C,
            mainpod::{OperationArg, OperationAux},
            primitives::merkletree::{MerkleClaimAndProof, MerkleTree},
        },
        middleware::{hash_values, Hash, OperationType, PodId, RawValue},
    };

    fn operation_verify(
        st: mainpod::Statement,
        op: mainpod::Operation,
        prev_statements: Vec<mainpod::Statement>,
        merkle_proofs: Vec<MerkleClaimAndProof>,
    ) -> Result<()> {
        let params = Params::default();
        let mp_gadget = MerkleProofGadget {
            max_depth: params.max_depth_mt_gadget,
        };

        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let st_target = builder.add_virtual_statement(&params);
        let op_target = builder.add_virtual_operation(&params);
        let prev_statements_target: Vec<_> = (0..prev_statements.len())
            .map(|_| builder.add_virtual_statement(&params))
            .collect();
        let merkle_proofs_target: Vec<_> = merkle_proofs
            .iter()
            .map(|_| mp_gadget.eval(&mut builder))
            .collect::<Result<_>>()?;
        let merkle_claims_target: Vec<_> = merkle_proofs_target
            .clone()
            .into_iter()
            .map(|pf| pf.into())
            .collect();

        OperationVerifyGadget {
            params: params.clone(),
        }
        .eval(
            &mut builder,
            &st_target,
            &op_target,
            &prev_statements_target,
            &merkle_claims_target,
        )?;

        let mut pw = PartialWitness::<F>::new();
        st_target.set_targets(&mut pw, &params, &st)?;
        op_target.set_targets(&mut pw, &params, &op)?;
        for (prev_st_target, prev_st) in prev_statements_target.iter().zip(prev_statements.iter()) {
            prev_st_target.set_targets(&mut pw, &params, prev_st)?;
        }
        for (merkle_proof_target, merkle_proof) in
            merkle_proofs_target.iter().zip(merkle_proofs.iter())
        {
            merkle_proof_target.set_targets(&mut pw, true, merkle_proof)?
        }

        // generate & verify proof
        let data = builder.build::<C>();
        let proof = data.prove(pw)?;
        data.verify(proof)?;

        Ok(())
    }

    #[test]
    fn test_lt_lteq_verify_failures() {
        let st1: mainpod::Statement =
            Statement::ValueOf(AnchoredKey::from((SELF, "hello")), Value::from(55)).into();
        let st2: mainpod::Statement = Statement::ValueOf(
            AnchoredKey::from((PodId(RawValue::from(75).into()), "world")),
            Value::from(56),
        )
        .into();
        let st3: mainpod::Statement = Statement::ValueOf(
            AnchoredKey::from((PodId(RawValue::from(88).into()), "hola")),
            Value::from(RawValue([
                GoldilocksField::NEG_ONE,
                GoldilocksField::ZERO,
                GoldilocksField::ZERO,
                GoldilocksField::ZERO,
            ])),
        )
        .into();
        let st4: mainpod::Statement = Statement::ValueOf(
            AnchoredKey::from((PodId(RawValue::from(74).into()), "mundo")),
            Value::from(-55),
        )
        .into();
        let st5: mainpod::Statement = Statement::ValueOf(
            AnchoredKey::from((PodId(RawValue::from(70).into()), "que")),
            Value::from(-56),
        )
        .into();

        let prev_statements = [st1, st2, st3, st4, st5];

        [
            // 56 < 55, 55 < 55, 56 <= 55, -55 < -55, -55 < -56, -55 <= -56 should fail to verify
            (
                mainpod::Operation(
                    OperationType::Native(NativeOperation::LtFromEntries),
                    vec![OperationArg::Index(1), OperationArg::Index(0)],
                    OperationAux::None,
                ),
                Statement::Lt(
                    AnchoredKey::from((PodId(RawValue::from(75).into()), "world")),
                    AnchoredKey::from((SELF, "hello")),
                )
                .into(),
            ),
            (
                mainpod::Operation(
                    OperationType::Native(NativeOperation::LtFromEntries),
                    vec![OperationArg::Index(0), OperationArg::Index(0)],
                    OperationAux::None,
                ),
                Statement::Lt(
                    AnchoredKey::from((SELF, "hello")),
                    AnchoredKey::from((SELF, "hello")),
                )
                .into(),
            ),
            (
                mainpod::Operation(
                    OperationType::Native(NativeOperation::LtEqFromEntries),
                    vec![OperationArg::Index(1), OperationArg::Index(0)],
                    OperationAux::None,
                ),
                Statement::LtEq(
                    AnchoredKey::from((PodId(RawValue::from(75).into()), "world")),
                    AnchoredKey::from((SELF, "hello")),
                )
                .into(),
            ),
            (
                mainpod::Operation(
                    OperationType::Native(NativeOperation::LtFromEntries),
                    vec![OperationArg::Index(3), OperationArg::Index(3)],
                    OperationAux::None,
                ),
                Statement::Lt(
                    AnchoredKey::from((PodId(RawValue::from(74).into()), "mundo")),
                    AnchoredKey::from((PodId(RawValue::from(74).into()), "mundo")),
                )
                .into(),
            ),
            (
                mainpod::Operation(
                    OperationType::Native(NativeOperation::LtFromEntries),
                    vec![OperationArg::Index(3), OperationArg::Index(4)],
                    OperationAux::None,
                ),
                Statement::Lt(
                    AnchoredKey::from((PodId(RawValue::from(74).into()), "mundo")),
                    AnchoredKey::from((PodId(RawValue::from(70).into()), "que")),
                )
                .into(),
            ),
            (
                mainpod::Operation(
                    OperationType::Native(NativeOperation::LtEqFromEntries),
                    vec![OperationArg::Index(3), OperationArg::Index(4)],
                    OperationAux::None,
                ),
                Statement::LtEq(
                    AnchoredKey::from((PodId(RawValue::from(74).into()), "mundo")),
                    AnchoredKey::from((PodId(RawValue::from(70).into()), "que")),
                )
                .into(),
            ),
            // 56 < p-1 and p-1 <= p-1 should fail to verify, where p
            // is the Goldilocks prime and 'p-1' occupies a single
            // limb.
            (
                mainpod::Operation(
                    OperationType::Native(NativeOperation::LtFromEntries),
                    vec![OperationArg::Index(1), OperationArg::Index(2)],
                    OperationAux::None,
                ),
                Statement::Lt(
                    AnchoredKey::from((PodId(RawValue::from(75).into()), "world")),
                    AnchoredKey::from((PodId(RawValue::from(88).into()), "hola")),
                )
                .into(),
            ),
            (
                mainpod::Operation(
                    OperationType::Native(NativeOperation::LtEqFromEntries),
                    vec![OperationArg::Index(2), OperationArg::Index(2)],
                    OperationAux::None,
                ),
                Statement::LtEq(
                    AnchoredKey::from((PodId(RawValue::from(88).into()), "hola")),
                    AnchoredKey::from((PodId(RawValue::from(88).into()), "hola")),
                )
                .into(),
            ),
        ]
        .into_iter()
        .for_each(|(op, st)| {
            assert!(operation_verify(st, op, prev_statements.to_vec(), vec![]).is_err())
        });
    }

    #[test]
    fn test_eq_neq_verify_failures() {
        let st1: mainpod::Statement =
            Statement::ValueOf(AnchoredKey::from((SELF, "hello")), Value::from(55)).into();
        let st2: mainpod::Statement = Statement::ValueOf(
            AnchoredKey::from((PodId(RawValue::from(75).into()), "world")),
            Value::from(56),
        )
        .into();
        let st3: mainpod::Statement = Statement::ValueOf(
            AnchoredKey::from((PodId(RawValue::from(88).into()), "hola")),
            Value::from(RawValue([
                GoldilocksField::NEG_ONE,
                GoldilocksField::ZERO,
                GoldilocksField::ZERO,
                GoldilocksField::ZERO,
            ])),
        )
        .into();
        let prev_statements = [st1, st2, st3];

        [
            // 56 == 55, 55 != 55 should fail to verify
            (
                mainpod::Operation(
                    OperationType::Native(NativeOperation::EqualFromEntries),
                    vec![OperationArg::Index(1), OperationArg::Index(0)],
                    OperationAux::None,
                ),
                Statement::Equal(
                    AnchoredKey::from((PodId(RawValue::from(75).into()), "world")),
                    AnchoredKey::from((SELF, "hello")),
                )
                .into(),
            ),
            (
                mainpod::Operation(
                    OperationType::Native(NativeOperation::NotEqualFromEntries),
                    vec![OperationArg::Index(0), OperationArg::Index(0)],
                    OperationAux::None,
                ),
                Statement::NotEqual(
                    AnchoredKey::from((SELF, "hello")),
                    AnchoredKey::from((SELF, "hello")),
                )
                .into(),
            ),
        ]
        .into_iter()
        .for_each(|(op, st)| {
            assert!(operation_verify(st, op, prev_statements.to_vec(), vec![]).is_err())
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
        operation_verify(st, op, prev_statements, vec![])
    }

    #[test]
    fn test_operation_verify_newentry() -> Result<()> {
        let st1: mainpod::Statement =
            Statement::ValueOf(AnchoredKey::from((SELF, "hello")), Value::from(55)).into();
        let st2: mainpod::Statement = Statement::ValueOf(
            AnchoredKey::from((PodId(RawValue::from(75).into()), "hello")),
            Value::from(55),
        )
        .into();
        let prev_statements = vec![st2];
        let op = mainpod::Operation(
            OperationType::Native(NativeOperation::NewEntry),
            vec![],
            OperationAux::None,
        );
        operation_verify(st1, op, prev_statements, vec![])
    }

    #[test]
    fn test_operation_verify_copy() -> Result<()> {
        let st: mainpod::Statement = Statement::None.into();
        let op = mainpod::Operation(
            OperationType::Native(NativeOperation::CopyStatement),
            vec![OperationArg::Index(0)],
            OperationAux::None,
        );
        let prev_statements = vec![Statement::None.into()];
        operation_verify(st, op, prev_statements, vec![])
    }

    #[test]
    fn test_operation_verify_eq() -> Result<()> {
        let st1: mainpod::Statement =
            Statement::ValueOf(AnchoredKey::from((SELF, "hello")), Value::from(55)).into();
        let st2: mainpod::Statement = Statement::ValueOf(
            AnchoredKey::from((PodId(RawValue::from(75).into()), "world")),
            Value::from(55),
        )
        .into();
        let st: mainpod::Statement = Statement::Equal(
            AnchoredKey::from((SELF, "hello")),
            AnchoredKey::from((PodId(RawValue::from(75).into()), "world")),
        )
        .into();
        let op = mainpod::Operation(
            OperationType::Native(NativeOperation::EqualFromEntries),
            vec![OperationArg::Index(0), OperationArg::Index(1)],
            OperationAux::None,
        );
        let prev_statements = vec![st1, st2];
        operation_verify(st, op, prev_statements, vec![])
    }

    #[test]
    fn test_operation_verify_neq() -> Result<()> {
        let st1: mainpod::Statement =
            Statement::ValueOf(AnchoredKey::from((SELF, "hello")), Value::from(55)).into();
        let st2: mainpod::Statement = Statement::ValueOf(
            AnchoredKey::from((PodId(RawValue::from(75).into()), "world")),
            Value::from(58),
        )
        .into();
        let st: mainpod::Statement = Statement::NotEqual(
            AnchoredKey::from((SELF, "hello")),
            AnchoredKey::from((PodId(RawValue::from(75).into()), "world")),
        )
        .into();
        let op = mainpod::Operation(
            OperationType::Native(NativeOperation::NotEqualFromEntries),
            vec![OperationArg::Index(0), OperationArg::Index(1)],
            OperationAux::None,
        );
        let prev_statements = vec![st1, st2];
        operation_verify(st, op, prev_statements, vec![])
    }

    #[test]
    fn test_operation_verify_lt() -> Result<()> {
        let st1: mainpod::Statement =
            Statement::ValueOf(AnchoredKey::from((SELF, "hello")), Value::from(55)).into();
        let st2: mainpod::Statement = Statement::ValueOf(
            AnchoredKey::from((PodId(RawValue::from(88).into()), "hello")),
            Value::from(56),
        )
        .into();
        let st: mainpod::Statement = Statement::Lt(
            AnchoredKey::from((SELF, "hello")),
            AnchoredKey::from((PodId(RawValue::from(88).into()), "hello")),
        )
        .into();
        let op = mainpod::Operation(
            OperationType::Native(NativeOperation::LtFromEntries),
            vec![OperationArg::Index(0), OperationArg::Index(1)],
            OperationAux::None,
        );
        let prev_statements = vec![st1, st2.clone()];
        operation_verify(st, op, prev_statements, vec![])?;

        // Also check negative < negative
        let st3: mainpod::Statement = Statement::ValueOf(
            AnchoredKey::from((PodId(RawValue::from(89).into()), "hola")),
            Value::from(-56),
        )
        .into();
        let st4: mainpod::Statement = Statement::ValueOf(
            AnchoredKey::from((PodId(RawValue::from(84).into()), "mundo")),
            Value::from(-55),
        )
        .into();
        let st: mainpod::Statement = Statement::Lt(
            AnchoredKey::from((PodId(RawValue::from(89).into()), "hola")),
            AnchoredKey::from((PodId(RawValue::from(84).into()), "mundo")),
        )
        .into();
        let op = mainpod::Operation(
            OperationType::Native(NativeOperation::LtFromEntries),
            vec![OperationArg::Index(0), OperationArg::Index(1)],
            OperationAux::None,
        );
        let prev_statements = vec![st3.clone(), st4];
        operation_verify(st, op, prev_statements, vec![])?;

        // Also check negative < positive
        let st: mainpod::Statement = Statement::Lt(
            AnchoredKey::from((PodId(RawValue::from(89).into()), "hola")),
            AnchoredKey::from((PodId(RawValue::from(88).into()), "hello")),
        )
        .into();
        let op = mainpod::Operation(
            OperationType::Native(NativeOperation::LtFromEntries),
            vec![OperationArg::Index(0), OperationArg::Index(1)],
            OperationAux::None,
        );
        let prev_statements = vec![st3, st2];
        operation_verify(st, op, prev_statements, vec![])
    }

    #[test]
    fn test_operation_verify_lteq() -> Result<()> {
        let st1: mainpod::Statement =
            Statement::ValueOf(AnchoredKey::from((SELF, "hello")), Value::from(55)).into();
        let st2: mainpod::Statement = Statement::ValueOf(
            AnchoredKey::from((PodId(RawValue::from(88).into()), "hello")),
            Value::from(56),
        )
        .into();
        let st: mainpod::Statement = Statement::LtEq(
            AnchoredKey::from((SELF, "hello")),
            AnchoredKey::from((PodId(RawValue::from(88).into()), "hello")),
        )
        .into();
        let op = mainpod::Operation(
            OperationType::Native(NativeOperation::LtEqFromEntries),
            vec![OperationArg::Index(0), OperationArg::Index(1)],
            OperationAux::None,
        );
        let prev_statements = vec![st1, st2.clone()];
        operation_verify(st, op, prev_statements, vec![])?;

        // Also check negative <= negative
        let st3: mainpod::Statement = Statement::ValueOf(
            AnchoredKey::from((PodId(RawValue::from(89).into()), "hola")),
            Value::from(-56),
        )
        .into();
        let st4: mainpod::Statement = Statement::ValueOf(
            AnchoredKey::from((PodId(RawValue::from(84).into()), "mundo")),
            Value::from(-55),
        )
        .into();
        let st: mainpod::Statement = Statement::LtEq(
            AnchoredKey::from((PodId(RawValue::from(89).into()), "hola")),
            AnchoredKey::from((PodId(RawValue::from(84).into()), "mundo")),
        )
        .into();
        let op = mainpod::Operation(
            OperationType::Native(NativeOperation::LtEqFromEntries),
            vec![OperationArg::Index(0), OperationArg::Index(1)],
            OperationAux::None,
        );
        let prev_statements = vec![st3.clone(), st4];
        operation_verify(st, op, prev_statements, vec![])?;

        // Also check negative <= positive
        let st: mainpod::Statement = Statement::LtEq(
            AnchoredKey::from((PodId(RawValue::from(89).into()), "hola")),
            AnchoredKey::from((PodId(RawValue::from(88).into()), "hello")),
        )
        .into();
        let op = mainpod::Operation(
            OperationType::Native(NativeOperation::LtEqFromEntries),
            vec![OperationArg::Index(0), OperationArg::Index(1)],
            OperationAux::None,
        );
        let prev_statements = vec![st3, st2];
        operation_verify(st, op, prev_statements.clone(), vec![])?;

        // Also check equality, both positive and negative.
        let st: mainpod::Statement = Statement::LtEq(
            AnchoredKey::from((PodId(RawValue::from(89).into()), "hola")),
            AnchoredKey::from((PodId(RawValue::from(89).into()), "hola")),
        )
        .into();
        let op = mainpod::Operation(
            OperationType::Native(NativeOperation::LtEqFromEntries),
            vec![OperationArg::Index(0), OperationArg::Index(0)],
            OperationAux::None,
        );
        operation_verify(st, op, prev_statements.clone(), vec![])?;
        let st: mainpod::Statement = Statement::LtEq(
            AnchoredKey::from((PodId(RawValue::from(88).into()), "hello")),
            AnchoredKey::from((PodId(RawValue::from(88).into()), "hello")),
        )
        .into();
        let op = mainpod::Operation(
            OperationType::Native(NativeOperation::LtEqFromEntries),
            vec![OperationArg::Index(1), OperationArg::Index(1)],
            OperationAux::None,
        );
        operation_verify(st, op, prev_statements, vec![])
    }

    #[test]
    fn test_operation_verify_hashof() -> Result<()> {
        let input_values = [
            Value::from(RawValue([
                GoldilocksField(1),
                GoldilocksField(2),
                GoldilocksField(3),
                GoldilocksField(4),
            ])),
            Value::from(512),
        ];
        let v1 = hash_values(&input_values);
        let [v2, v3] = input_values;

        let st1: mainpod::Statement = Statement::ValueOf(
            AnchoredKey::from((PodId(RawValue::from(88).into()), "hola")),
            v1.into(),
        )
        .into();
        let st2: mainpod::Statement = Statement::ValueOf(
            AnchoredKey::from((PodId(RawValue::from(128).into()), "mundo")),
            v2,
        )
        .into();
        let st3: mainpod::Statement = Statement::ValueOf(
            AnchoredKey::from((PodId(RawValue::from(256).into()), "!")),
            v3,
        )
        .into();

        let st: mainpod::Statement = Statement::HashOf(
            AnchoredKey::from((PodId(RawValue::from(88).into()), "hola")),
            AnchoredKey::from((PodId(RawValue::from(128).into()), "mundo")),
            AnchoredKey::from((PodId(RawValue::from(256).into()), "!")),
        )
        .into();
        let op = mainpod::Operation(
            OperationType::Native(NativeOperation::HashOf),
            vec![
                OperationArg::Index(0),
                OperationArg::Index(1),
                OperationArg::Index(2),
            ],
            OperationAux::None,
        );
        let prev_statements = vec![st1, st2, st3];
        operation_verify(st, op, prev_statements, vec![])
    }

    #[test]
    fn test_operation_verify_lt_to_neq() -> Result<()> {
        let st: mainpod::Statement = Statement::NotEqual(
            AnchoredKey::from((SELF, "hello")),
            AnchoredKey::from((PodId(RawValue::from(88).into()), "hello")),
        )
        .into();
        let st1: mainpod::Statement = Statement::Lt(
            AnchoredKey::from((SELF, "hello")),
            AnchoredKey::from((PodId(RawValue::from(88).into()), "hello")),
        )
        .into();
        let op = mainpod::Operation(
            OperationType::Native(NativeOperation::LtToNotEqual),
            vec![OperationArg::Index(0)],
            OperationAux::None,
        );
        let prev_statements = vec![st1];
        operation_verify(st, op, prev_statements, vec![])
    }

    #[test]
    fn test_operation_verify_transitive_eq() -> Result<()> {
        let st: mainpod::Statement = Statement::Equal(
            AnchoredKey::from((SELF, "hello")),
            AnchoredKey::from((PodId(RawValue::from(88).into()), "hola")),
        )
        .into();
        let st1: mainpod::Statement = Statement::Equal(
            AnchoredKey::from((SELF, "hello")),
            AnchoredKey::from((PodId(RawValue::from(89).into()), "world")),
        )
        .into();
        let st2: mainpod::Statement = Statement::Equal(
            AnchoredKey::from((PodId(RawValue::from(89).into()), "world")),
            AnchoredKey::from((PodId(RawValue::from(88).into()), "hola")),
        )
        .into();
        let op = mainpod::Operation(
            OperationType::Native(NativeOperation::TransitiveEqualFromStatements),
            vec![OperationArg::Index(0), OperationArg::Index(1)],
            OperationAux::None,
        );
        let prev_statements = vec![st1, st2];
        operation_verify(st, op, prev_statements, vec![])
    }

    #[test]
    fn test_operation_verify_sintains() -> Result<()> {
        let params = Params::default();

        let kvs = [
            (1.into(), 55.into()),
            (2.into(), 88.into()),
            (175.into(), 0.into()),
        ]
        .into_iter()
        .collect();
        let mt = MerkleTree::new(params.max_depth_mt_gadget, &kvs)?;

        let root = Value::from(mt.root());
        let root_ak = AnchoredKey::from((PodId(RawValue::from(88).into()), "merkle root"));

        let key = 5.into();
        let key_ak = AnchoredKey::from((PodId(RawValue::from(88).into()), "key"));

        let no_key_pf = mt.prove_nonexistence(&key)?;

        let root_st: mainpod::Statement = Statement::ValueOf(root_ak.clone(), root.clone()).into();
        let key_st: mainpod::Statement = Statement::ValueOf(key_ak.clone(), key.into()).into();
        let st: mainpod::Statement = Statement::NotContains(root_ak, key_ak).into();
        let op = mainpod::Operation(
            OperationType::Native(NativeOperation::NotContainsFromEntries),
            vec![OperationArg::Index(0), OperationArg::Index(1)],
            OperationAux::MerkleProofIndex(0),
        );

        let merkle_proofs = vec![MerkleClaimAndProof::new(
            Hash::from(root.raw()),
            key,
            None,
            no_key_pf,
        )];
        let prev_statements = vec![root_st, key_st];
        operation_verify(st, op, prev_statements, merkle_proofs)
    }

    #[test]
    fn test_operation_verify_contains() -> Result<()> {
        let params = Params::default();

        let kvs = [
            (1.into(), 55.into()),
            (2.into(), 88.into()),
            (175.into(), 0.into()),
        ]
        .into_iter()
        .collect();
        let mt = MerkleTree::new(params.max_depth_mt_gadget, &kvs)?;

        let root = Value::from(mt.root());
        let root_ak = AnchoredKey::from((PodId(RawValue::from(88).into()), "merkle root"));

        let key = 175.into();
        let key_ak = AnchoredKey::from((PodId(RawValue::from(70).into()), "key"));

        let (value, key_pf) = mt.prove(&key)?;
        let value_ak = AnchoredKey::from((PodId(RawValue::from(72).into()), "value"));

        let root_st: mainpod::Statement = Statement::ValueOf(root_ak.clone(), root.clone()).into();
        let key_st: mainpod::Statement = Statement::ValueOf(key_ak.clone(), key.into()).into();
        let value_st: mainpod::Statement =
            Statement::ValueOf(value_ak.clone(), value.into()).into();

        let st: mainpod::Statement = Statement::Contains(root_ak, key_ak, value_ak).into();
        let op = mainpod::Operation(
            OperationType::Native(NativeOperation::ContainsFromEntries),
            vec![
                OperationArg::Index(0),
                OperationArg::Index(1),
                OperationArg::Index(2),
            ],
            OperationAux::MerkleProofIndex(0),
        );

        let merkle_proofs = vec![MerkleClaimAndProof::new(
            Hash::from(root.raw()),
            key,
            Some(value),
            key_pf,
        )];
        let prev_statements = vec![root_st, key_st, value_st];
        operation_verify(st, op, prev_statements, merkle_proofs)
    }
}
