use std::{array, sync::Arc};

use itertools::{zip_eq, Itertools};
use plonky2::{
    field::types::Field,
    hash::{hash_types::HashOutTarget, poseidon::PoseidonHash},
    iop::{target::BoolTarget, witness::PartialWitness},
    plonk::circuit_builder::CircuitBuilder,
};

use crate::{
    backends::plonky2::{
        basetypes::D,
        circuits::{
            common::{
                CircuitBuilderPod, CustomPredicateBatchTarget, CustomPredicateEntryTarget,
                CustomPredicateVerifyEntryTarget, CustomPredicateVerifyQueryTarget, Flattenable,
                MerkleClaimTarget, OperationTarget, OperationTypeTarget, PredicateTarget,
                StatementArgTarget, StatementTarget, StatementTmplArgTarget, StatementTmplTarget,
                ValueTarget,
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
        AnchoredKey, CustomPredicate, CustomPredicateBatch, CustomPredicateRef, NativeOperation,
        NativePredicate, Params, PodType, Statement, StatementArg, ToFields, Value, WildcardValue,
        F, KEY_TYPE, SELF, VALUE_SIZE,
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
        custom_predicate_verification_table: &[HashOutTarget],
    ) -> Result<()> {
        let _true = builder._true();
        let _false = builder._false();

        // Verify that the operation `op` correctly generates the statement `st`.  The operation
        // can reference any of the `prev_statements`.
        // TODO: Clean this up.
        let resolved_op_args = if prev_statements.is_empty() {
            (0..self.params.max_operation_args)
                .map(|_| {
                    StatementTarget::new_native(builder, &self.params, NativePredicate::None, &[])
                })
                .collect_vec()
        } else {
            op.args
                .iter()
                .flatten()
                .map(|&i| builder.vec_ref(&self.params, prev_statements, i))
                .collect::<Vec<_>>()
        };
        // TODO: Can we have a single table with merkel claims and verified custom predicates
        // together (with an identifying prefix) and then we only need one random access instead of
        // two?
        // Currently we use one slot of aux for the index to merkle claim and another slot of aux
        // for the index to the verified custom predicate.  We can't use the same slot because then
        // if one table is different size the random access to the smaller one may use an index
        // that is too big and not pass the constraints.  Possible solutions to use a single slot
        // are:
        //  - a. Use a single table (mux both tables)
        //  - b. select the index or 0 by checking the operation type here; but that breaks the
        //    current abstraction a little bit.

        // Certain operations (Contains/NotContains) will refer to one
        // of the provided Merkle proofs (if any). These proofs have already
        // been verified, so we need only look up the claim.
        let resolved_merkle_claim = (!merkle_claims.is_empty())
            .then(|| builder.vec_ref(&self.params, merkle_claims, op.aux[0]));

        // Operations from custom statements will refer to one
        // of the provided custom predicates verifications (if any). These operations have already
        // been verified, so we need only look up the entry.
        let resolved_custom_pred_verification = (!custom_predicate_verification_table.is_empty())
            .then(|| builder.vec_ref(&self.params, custom_predicate_verification_table, op.aux[1]));

        // The verification may require aux data which needs to be stored in the
        // `OperationVerifyTarget` so that we can set during witness generation.

        // For now only support native operations
        // Op checks to carry out. Each 'eval_X' should
        // be thought of as 'eval' restricted to the op of type X,
        // where the returned target is `false` if the input targets
        // lie outside of the domain.
        let op_checks = [
            vec![
                self.eval_none(builder, st, &op.op_type),
                self.eval_new_entry(builder, st, &op.op_type, prev_statements),
            ],
            // Skip these if there are no resolved op args
            if resolved_op_args.is_empty() {
                vec![]
            } else {
                vec![
                    self.eval_copy(builder, st, &op.op_type, &resolved_op_args)?,
                    self.eval_eq_neq_from_entries(builder, st, &op.op_type, &resolved_op_args),
                    self.eval_lt_lteq_from_entries(builder, st, &op.op_type, &resolved_op_args),
                    self.eval_transitive_eq(builder, st, &op.op_type, &resolved_op_args),
                    self.eval_lt_to_neq(builder, st, &op.op_type, &resolved_op_args),
                    self.eval_hash_of(builder, st, &op.op_type, &resolved_op_args),
                    self.eval_sum_of(builder, st, &op.op_type, &resolved_op_args),
                    self.eval_product_of(builder, st, &op.op_type, &resolved_op_args),
                    self.eval_max_of(builder, st, &op.op_type, &resolved_op_args),
                ]
            },
            // Skip these if there are no resolved Merkle claims
            if let Some(resolved_merkle_claim) = resolved_merkle_claim {
                vec![
                    self.eval_contains_from_entries(
                        builder,
                        st,
                        &op.op_type,
                        resolved_merkle_claim,
                        &resolved_op_args,
                    ),
                    self.eval_not_contains_from_entries(
                        builder,
                        st,
                        &op.op_type,
                        resolved_merkle_claim,
                        &resolved_op_args,
                    ),
                ]
            } else {
                vec![]
            },
            // Skip these if there are no resolved custom predicate verifications
            if let Some(resolved_custom_pred_verification) = resolved_custom_pred_verification {
                vec![self.eval_custom(
                    builder,
                    st,
                    &op.op_type,
                    resolved_custom_pred_verification,
                    &resolved_op_args,
                )]
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
        op_type: &OperationTypeTarget,
        resolved_merkle_claim: MerkleClaimTarget,
        resolved_op_args: &[StatementTarget],
    ) -> BoolTarget {
        let op_code_ok = op_type.has_native(builder, NativeOperation::ContainsFromEntries);

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
        op_type: &OperationTypeTarget,
        resolved_merkle_claim: MerkleClaimTarget,
        resolved_op_args: &[StatementTarget],
    ) -> BoolTarget {
        let op_code_ok = op_type.has_native(builder, NativeOperation::NotContainsFromEntries);

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

    fn eval_custom(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        st: &StatementTarget,
        op_type: &OperationTypeTarget,
        resolved_custom_pred_verification: HashOutTarget,
        resolved_op_args: &[StatementTarget],
    ) -> BoolTarget {
        let query = CustomPredicateVerifyQueryTarget {
            statement: st.clone(),
            op_type: op_type.clone(),
            op_args: resolved_op_args.to_vec(),
        };
        let out_query_hash = query.hash(builder);
        builder.is_equal_slice(
            &resolved_custom_pred_verification.elements,
            &out_query_hash.elements,
        )
    }

    /// Carries out the checks necessary for EqualFromEntries and
    /// NotEqualFromEntries.
    fn eval_eq_neq_from_entries(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        st: &StatementTarget,
        op_type: &OperationTypeTarget,
        resolved_op_args: &[StatementTarget],
    ) -> BoolTarget {
        let eq_op_st_code_ok = {
            let op_code_ok = op_type.has_native(builder, NativeOperation::EqualFromEntries);
            let st_code_ok = st.has_native_type(builder, &self.params, NativePredicate::Equal);
            builder.and(op_code_ok, st_code_ok)
        };
        let neq_op_st_code_ok = {
            let op_code_ok = op_type.has_native(builder, NativeOperation::NotEqualFromEntries);
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
        op_type: &OperationTypeTarget,
        resolved_op_args: &[StatementTarget],
    ) -> BoolTarget {
        let zero = ValueTarget::zero(builder);
        let one = ValueTarget::one(builder);

        let lt_op_st_code_ok = {
            let op_code_ok = op_type.has_native(builder, NativeOperation::LtFromEntries);
            let st_code_ok = st.has_native_type(builder, &self.params, NativePredicate::Lt);
            builder.and(op_code_ok, st_code_ok)
        };
        let lteq_op_st_code_ok = {
            let op_code_ok = op_type.has_native(builder, NativeOperation::LtEqFromEntries);
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
        op_type: &OperationTypeTarget,
        resolved_op_args: &[StatementTarget],
    ) -> BoolTarget {
        let op_code_ok = op_type.has_native(builder, NativeOperation::HashOf);

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

    fn eval_sum_of(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        st: &StatementTarget,
        op_type: &OperationTypeTarget,
        resolved_op_args: &[StatementTarget],
    ) -> BoolTarget {
        let value_zero = ValueTarget::zero(builder);

        let op_code_ok = op_type.has_native(builder, NativeOperation::SumOf);

        let (arg_types_ok, [arg1_value, arg2_value, arg3_value]) =
            self.first_n_args_as_values(builder, resolved_op_args);

        // Select to avoid overflow.
        let summand1 = builder.select_value(op_code_ok, arg2_value, value_zero);
        let summand2 = builder.select_value(op_code_ok, arg3_value, value_zero);

        let expected_sum = builder.i64_add(summand1, summand2);

        let sum_ok = builder.is_equal_slice(&arg1_value.elements, &expected_sum.elements);

        let arg1_key = resolved_op_args[0].args[0].clone();
        let arg2_key = resolved_op_args[1].args[0].clone();
        let arg3_key = resolved_op_args[2].args[0].clone();
        let expected_statement = StatementTarget::new_native(
            builder,
            &self.params,
            NativePredicate::SumOf,
            &[arg1_key, arg2_key, arg3_key],
        );
        let st_ok = builder.is_equal_flattenable(st, &expected_statement);

        builder.all([op_code_ok, arg_types_ok, sum_ok, st_ok])
    }

    fn eval_product_of(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        st: &StatementTarget,
        op_type: &OperationTypeTarget,
        resolved_op_args: &[StatementTarget],
    ) -> BoolTarget {
        let value_zero = ValueTarget::zero(builder);

        let op_code_ok = op_type.has_native(builder, NativeOperation::ProductOf);

        let (arg_types_ok, [arg1_value, arg2_value, arg3_value]) =
            self.first_n_args_as_values(builder, resolved_op_args);

        // Select to avoid overflow.
        let factor1 = builder.select_value(op_code_ok, arg2_value, value_zero);
        let factor2 = builder.select_value(op_code_ok, arg3_value, value_zero);

        let expected_product = builder.i64_mul(factor1, factor2);

        let product_ok = builder.is_equal_slice(&arg1_value.elements, &expected_product.elements);

        let arg1_key = resolved_op_args[0].args[0].clone();
        let arg2_key = resolved_op_args[1].args[0].clone();
        let arg3_key = resolved_op_args[2].args[0].clone();
        let expected_statement = StatementTarget::new_native(
            builder,
            &self.params,
            NativePredicate::ProductOf,
            &[arg1_key, arg2_key, arg3_key],
        );
        let st_ok = builder.is_equal_flattenable(st, &expected_statement);

        builder.all([op_code_ok, arg_types_ok, product_ok, st_ok])
    }

    fn eval_max_of(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        st: &StatementTarget,
        op_type: &OperationTypeTarget,
        resolved_op_args: &[StatementTarget],
    ) -> BoolTarget {
        let op_code_ok = op_type.has_native(builder, NativeOperation::MaxOf);

        let (arg_types_ok, [arg1_value, arg2_value, arg3_value]) =
            self.first_n_args_as_values(builder, resolved_op_args);

        // Check that arg1_value is equal to one of the other two
        // values.
        let arg1_eq_arg2 = builder.is_equal_slice(&arg1_value.elements, &arg2_value.elements);
        let arg1_eq_arg3 = builder.is_equal_slice(&arg1_value.elements, &arg3_value.elements);

        let all_eq = builder.and(arg1_eq_arg2, arg1_eq_arg3);
        let not_all_eq = builder.not(all_eq);

        let arg1_check = builder.or(arg1_eq_arg2, arg1_eq_arg3);

        // If it is not equal to any of the other two values, it must be greater than it.
        let lower_bound = builder.select_value(arg1_eq_arg2, arg3_value, arg2_value);

        // Only check lower bound if not all args are equal.
        let lt_check_enabled = builder.and(not_all_eq, op_code_ok);
        builder.assert_i64_less_if(lt_check_enabled, lower_bound, arg1_value);

        let arg1_key = resolved_op_args[0].args[0].clone();
        let arg2_key = resolved_op_args[1].args[0].clone();
        let arg3_key = resolved_op_args[2].args[0].clone();
        let expected_statement = StatementTarget::new_native(
            builder,
            &self.params,
            NativePredicate::MaxOf,
            &[arg1_key, arg2_key, arg3_key],
        );
        let st_ok = builder.is_equal_flattenable(st, &expected_statement);

        builder.all([op_code_ok, arg_types_ok, arg1_check, st_ok])
    }

    fn eval_transitive_eq(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        st: &StatementTarget,
        op_type: &OperationTypeTarget,
        resolved_op_args: &[StatementTarget],
    ) -> BoolTarget {
        let op_code_ok =
            op_type.has_native(builder, NativeOperation::TransitiveEqualFromStatements);

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
        op_type: &OperationTypeTarget,
    ) -> BoolTarget {
        let op_code_ok = op_type.has_native(builder, NativeOperation::None);

        let expected_statement =
            StatementTarget::new_native(builder, &self.params, NativePredicate::None, &[]);
        let st_ok = builder.is_equal_flattenable(st, &expected_statement);

        builder.all([op_code_ok, st_ok])
    }

    fn eval_new_entry(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        st: &StatementTarget,
        op_type: &OperationTypeTarget,
        prev_statements: &[StatementTarget],
    ) -> BoolTarget {
        let op_code_ok = op_type.has_native(builder, NativeOperation::NewEntry);

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
        op_type: &OperationTypeTarget,
        resolved_op_args: &[StatementTarget],
    ) -> BoolTarget {
        let op_code_ok = op_type.has_native(builder, NativeOperation::LtToNotEqual);

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
        op_type: &OperationTypeTarget,
        resolved_op_args: &[StatementTarget],
    ) -> Result<BoolTarget> {
        let op_code_ok = op_type.has_native(builder, NativeOperation::CopyStatement);

        let expected_statement = &resolved_op_args[0];
        let st_ok = builder.is_equal_flattenable(st, expected_statement);

        Ok(builder.all([op_code_ok, st_ok]))
    }
}

struct CustomOperationVerifyGadget {
    params: Params,
}

// NOTE: This is a bit messy.  The target types are defined in `common.rs` because they are used in
// `add_virtual_foo` methods in the trait for the `CircuitBuilder`.  But the constraint logic is
// here.  Maybe we want to move everything related to custom predicates to its own module, but then
// should we add a new trait for the `add_virtual_foo` methods so that everything is contained in a
// module?
impl CustomOperationVerifyGadget {
    fn statement_arg_from_template(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        st_tmpl_arg: &StatementTmplArgTarget,
        args: &[ValueTarget],
    ) -> StatementArgTarget {
        let zero = builder.zero();
        let (is_literal, value_literal) = st_tmpl_arg.as_literal(builder);
        let (is_ak, ak_id_wc_index, ak_key_lit_or_wc) = st_tmpl_arg.as_anchored_key(builder);
        let (is_wc_literal, wc_index) = st_tmpl_arg.as_wildcard_literal(builder);

        let ((_is_ak_key_lit, ak_key_lit), (is_ak_key_wc, ak_key_wc_index)) =
            ak_key_lit_or_wc.cases(builder);

        // optimization: ak_id_wc_index and wc_index use the same signals, so we only need to do one
        // random access to resolve both of them
        assert_eq!(ak_id_wc_index, wc_index);
        // If the index is not used, use a 0 instead to still pass the range constraints from
        // vec_ref
        let first_index = ak_id_wc_index;
        let is_first_index_valid = builder.or(is_ak, is_wc_literal);
        let first_index = builder.select(is_first_index_valid, first_index, zero);
        let resolved_ak_id = builder.vec_ref(&self.params, args, first_index);
        let resolved_wc = resolved_ak_id;

        // If the index is not used, use a 0 instead to still pass the range constraints from
        // vec_ref
        let second_index = ak_key_wc_index;
        let is_second_index_valid = builder.and(is_ak, is_ak_key_wc);
        let second_index = builder.select(is_second_index_valid, second_index, zero);
        let resolved_ak_key = builder.vec_ref(&self.params, args, second_index);

        let ak_key = ak_key_lit; // is_ak_key_lit
        let ak_key =
            builder.select_flattenable(&self.params, is_ak_key_wc, &resolved_ak_key, &ak_key);

        let first = ValueTarget::zero(builder); // is_none
        let first = builder.select_flattenable(&self.params, is_literal, &value_literal, &first);
        let first = builder.select_flattenable(&self.params, is_ak, &resolved_ak_id, &first);
        let first = builder.select_flattenable(&self.params, is_wc_literal, &resolved_wc, &first);

        let second = ValueTarget::zero(builder); // is_none or is_literal or is_wc_literal
        let second = builder.select_flattenable(&self.params, is_ak, &ak_key, &second);

        StatementArgTarget::new(first, second)
    }

    fn statement_from_template(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        st_tmpl: &StatementTmplTarget,
        args: &[ValueTarget],
    ) -> StatementTarget {
        let args = st_tmpl
            .args
            .iter()
            .map(|st_tmpl_arg| self.statement_arg_from_template(builder, st_tmpl_arg, args))
            .collect();
        StatementTarget {
            predicate: st_tmpl.pred.clone(),
            args,
        }
    }

    /// Given a custom predicate, a list of operation arguments (statements) and a list of wildcard
    /// values (args):
    /// - Verify that the custom predicate is satisfied with the given statements
    /// - Build the output statement
    /// - Build the expected operation type
    fn eval(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        custom_predicate: &CustomPredicateEntryTarget,
        op_args: &[StatementTarget],
        args: &[ValueTarget], // arguments to the custom predicate, public and private
    ) -> Result<(StatementTarget, OperationTypeTarget)> {
        // Some sanity checks
        assert_eq!(self.params.max_operation_args, op_args.len());
        assert_eq!(self.params.max_custom_predicate_wildcards, args.len());

        let (batch_id, index) = (custom_predicate.id, custom_predicate.index);
        let op_type = OperationTypeTarget::new_custom(builder, batch_id, index);

        // Build the statement
        let st_predicate = PredicateTarget::new_custom(builder, batch_id, index);
        let arg_none = ValueTarget::zero(builder);
        let lt_mask = builder.lt_mask(
            self.params.max_statement_args,
            custom_predicate.predicate.args_len,
        );
        let st_args = (0..self.params.max_statement_args)
            .map(|i| {
                let v = builder.select_flattenable(&self.params, lt_mask[i], &args[i], &arg_none);
                StatementArgTarget::wildcard_literal(builder, &v)
            })
            .collect();
        let statement = StatementTarget {
            predicate: st_predicate,
            args: st_args,
        };

        // Check the operation arguments
        // From each statement template we generate an expected statement using replacing the
        // wildcards by the arguments.  Then we compare the expected statement with the operation
        // argument.
        let expected_sts: Vec<_> = custom_predicate
            .predicate
            .statements
            .iter()
            .map(|st_tmpl| self.statement_from_template(builder, st_tmpl, args))
            .collect();
        // expected_sts.len() == self.params.max_custom_predicate_arity
        // op_args.len() == self.params.max_operation_args;
        assert!(self.params.max_custom_predicate_arity <= self.params.max_operation_args);
        let sts_eq: Vec<_> = expected_sts
            .iter()
            .zip(op_args.iter())
            .map(|(expected_st, st)| builder.is_equal_flattenable(expected_st, st))
            .collect();
        let all_st_eq = builder.all(sts_eq.clone());
        let some_st_eq = builder.any(sts_eq);
        // NOTE: This BoolTarget is safe because both inputs to the select are safe
        let is_op_args_ok = BoolTarget::new_unsafe(builder.select(
            custom_predicate.predicate.conjunction,
            all_st_eq.target,
            some_st_eq.target,
        ));

        builder.assert_one(is_op_args_ok.target);
        Ok((statement, op_type))
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

        // Table of [batch_id, custom_predicate_index, custom_predicate] with queryable part as
        // hash([batch_id, custom_predicate_index, custom_predicate]).  While building the table we
        // calculate the id of each batch.
        let mut custom_predicate_table =
            Vec::with_capacity(params.max_custom_predicate_batches * params.max_custom_batch_size);
        let mut custom_predicate_batches = Vec::with_capacity(params.max_custom_predicate_batches);
        for _ in 0..params.max_custom_predicate_batches {
            let cpb = builder.add_virtual_custom_predicate_batch(&self.params);
            let id = cpb.id(builder); // constrain the id
            for (index, cp) in cpb.predicates.iter().enumerate() {
                let entry = CustomPredicateEntryTarget {
                    id,                                                      // output
                    index: builder.constant(F::from_canonical_usize(index)), // constant
                    predicate: cp.clone(),                                   // input
                };
                let in_query_hash = entry.hash(builder);
                custom_predicate_table.push(in_query_hash);
            }
            custom_predicate_batches.push(cpb); // We keep this for witness assignment
        }

        // Table of [batch_id, custom_predicate_index, custom_predicate, args, st, op, op_args]
        // with queryable part as hash([st, op, op_args]).  While building the table we verify each
        // custom predicate against the operation and statement.
        let mut custom_predicate_verifications =
            Vec::with_capacity(params.max_custom_predicate_verifications);
        let mut custom_predicate_verification_table =
            Vec::with_capacity(params.max_custom_predicate_verifications);
        for _ in 0..params.max_custom_predicate_verifications {
            let custom_predicate_table_index = builder.add_virtual_target();
            let custom_predicate = builder.add_virtual_custom_predicate_entry(&self.params);
            let args = (0..params.max_custom_predicate_wildcards)
                .map(|_| builder.add_virtual_value())
                .collect_vec();
            let op_args = (0..params.max_operation_args)
                .map(|_| builder.add_virtual_statement(&self.params))
                .collect_vec();

            // Verify the custom predicate operation
            let (statement, op_type) = CustomOperationVerifyGadget {
                params: params.clone(),
            }
            .eval(builder, &custom_predicate, &op_args, &args)?;

            // Check that the batch id is correct by querying the custom predicate batches table
            let table_query_hash = builder.vec_ref(
                &self.params,
                &custom_predicate_table,
                custom_predicate_table_index,
            );
            let out_query_hash = custom_predicate.hash(builder);
            builder.connect_array(table_query_hash.elements, out_query_hash.elements);

            let entry = CustomPredicateVerifyEntryTarget {
                custom_predicate_table_index, // input
                custom_predicate,             // input
                args,                         // input
                query: CustomPredicateVerifyQueryTarget {
                    statement, // output
                    op_type,   // output
                    op_args,   // input
                },
            };
            let in_query_hash = entry.query.hash(builder);
            custom_predicate_verification_table.push(in_query_hash);
            custom_predicate_verifications.push(entry); // We keep this for witness assignment
        }

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
            .eval(
                builder,
                st,
                op,
                prev_statements,
                &merkle_claims,
                &custom_predicate_verification_table,
            )?;
        }

        Ok(MainPodVerifyTarget {
            params: params.clone(),
            id,
            signed_pods,
            statements: input_statements.to_vec(),
            operations,
            merkle_proofs,
            custom_predicate_batches,
            custom_predicate_verifications,
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
    custom_predicate_verifications: Vec<CustomPredicateVerifyEntryTarget>,
}

pub struct CustomPredicateVerification {
    pub custom_predicate_table_index: usize,
    pub custom_predicate: CustomPredicateRef,
    pub args: Vec<WildcardValue>,
    pub op_args: Vec<mainpod::Statement>,
}

pub struct MainPodVerifyInput {
    pub signed_pods: Vec<SignedPod>,
    pub statements: Vec<mainpod::Statement>,
    pub operations: Vec<mainpod::Operation>,
    pub merkle_proofs: Vec<MerkleClaimAndProof>,
    pub custom_predicate_batches: Vec<Arc<CustomPredicateBatch>>,
    pub custom_predicate_verifications: Vec<CustomPredicateVerification>,
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
        if self.params.max_input_signed_pods > 0 {
            // TODO: Instead of using an input for padding, use a canonical minimal SignedPod,
            // without it a MainPod configured to support input signed pods must have at least one
            // input signed pod :(
            let pad_pod = &input.signed_pods[0];
            for i in input.signed_pods.len()..self.params.max_input_signed_pods {
                self.signed_pods[i].set_targets(pw, pad_pod)?;
            }
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
        for (i, cpb) in input.custom_predicate_batches.iter().enumerate() {
            self.custom_predicate_batches[i].set_targets(pw, &self.params, cpb)?;
        }
        // Padding
        let pad_cpb = CustomPredicateBatch::new(
            &self.params,
            "empty".to_string(),
            vec![CustomPredicate::empty()],
        );
        for i in input.custom_predicate_batches.len()..self.params.max_custom_predicate_batches {
            self.custom_predicate_batches[i].set_targets(pw, &self.params, &pad_cpb)?;
        }

        assert!(
            input.custom_predicate_verifications.len()
                <= self.params.max_custom_predicate_verifications
        );
        for (i, cpv) in input.custom_predicate_verifications.iter().enumerate() {
            self.custom_predicate_verifications[i].set_targets(pw, &self.params, cpv)?;
        }
        // Padding.  Use the first input if it exists.  If it doesnt, all batches in this MainPod
        // are padding so refer to the first padding entry.
        let empty_cpv = CustomPredicateVerification {
            custom_predicate_table_index: 0,
            custom_predicate: CustomPredicateRef::new(pad_cpb, 0),
            args: vec![],
            op_args: vec![],
        };
        let pad_cpv = input
            .custom_predicate_verifications
            .first()
            .unwrap_or(&empty_cpv);
        for i in input.custom_predicate_verifications.len()
            ..self.params.max_custom_predicate_verifications
        {
            self.custom_predicate_verifications[i].set_targets(pw, &self.params, pad_cpv)?;
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
    use std::ops::Not;

    use plonky2::{
        field::{goldilocks_field::GoldilocksField, types::Field},
        plonk::{circuit_builder::CircuitBuilder, circuit_data::CircuitConfig},
    };

    use super::*;
    use crate::{
        backends::plonky2::{
            basetypes::C,
            circuits::common::tests::I64_TEST_PAIRS,
            mainpod::{OperationArg, OperationAux},
            primitives::merkletree::{MerkleClaimAndProof, MerkleTree},
        },
        frontend::{self, key, literal, CustomPredicateBatchBuilder, StatementTmplBuilder},
        middleware::{
            hash_str, hash_values, Hash, Key, KeyOrWildcard, OperationType, PodId, Predicate,
            RawValue, StatementTmpl, StatementTmplArg, Wildcard, WildcardValue,
        },
    };

    fn operation_verify(
        st: mainpod::Statement,
        op: mainpod::Operation,
        prev_statements: Vec<mainpod::Statement>,
        merkle_proofs: Vec<MerkleClaimAndProof>,
    ) -> Result<()> {
        let params = Params {
            max_custom_predicate_batches: 0,
            max_custom_predicate_verifications: 0,
            ..Default::default()
        };
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
        let custom_predicate_verification_table = vec![];

        OperationVerifyGadget {
            params: params.clone(),
        }
        .eval(
            &mut builder,
            &st_target,
            &op_target,
            &prev_statements_target,
            &merkle_claims_target,
            &custom_predicate_verification_table,
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
    fn test_operation_verify_sumof() -> Result<()> {
        I64_TEST_PAIRS
            .into_iter()
            .flat_map(|(a, b)| {
                let (sum, overflow) = a.overflowing_add(b);
                overflow.not().then_some((a, b, sum))
            })
            .try_for_each(|(a, b, sum)| {
                let st1: mainpod::Statement = Statement::ValueOf(
                    AnchoredKey::from((PodId(RawValue::from(88).into()), "hola")),
                    sum.into(),
                )
                .into();

                let st2: mainpod::Statement = Statement::ValueOf(
                    AnchoredKey::from((PodId(RawValue::from(128).into()), "mundo")),
                    a.into(),
                )
                .into();

                let st3: mainpod::Statement = Statement::ValueOf(
                    AnchoredKey::from((PodId(RawValue::from(256).into()), "!")),
                    b.into(),
                )
                .into();

                let st: mainpod::Statement = Statement::SumOf(
                    AnchoredKey::from((PodId(RawValue::from(88).into()), "hola")),
                    AnchoredKey::from((PodId(RawValue::from(128).into()), "mundo")),
                    AnchoredKey::from((PodId(RawValue::from(256).into()), "!")),
                )
                .into();
                let op = mainpod::Operation(
                    OperationType::Native(NativeOperation::SumOf),
                    vec![
                        OperationArg::Index(0),
                        OperationArg::Index(1),
                        OperationArg::Index(2),
                    ],
                    OperationAux::None,
                );
                let prev_statements = vec![st1, st2, st3];
                operation_verify(st, op, prev_statements, vec![])
            })
    }

    #[test]
    fn test_operation_verify_productof() -> Result<()> {
        I64_TEST_PAIRS
            .into_iter()
            .flat_map(|(a, b)| {
                let (prod, overflow) = a.overflowing_mul(b);
                overflow.not().then_some((a, b, prod))
            })
            .try_for_each(|(a, b, prod)| {
                let st1: mainpod::Statement = Statement::ValueOf(
                    AnchoredKey::from((PodId(RawValue::from(88).into()), "hola")),
                    prod.into(),
                )
                .into();

                let st2: mainpod::Statement = Statement::ValueOf(
                    AnchoredKey::from((PodId(RawValue::from(128).into()), "mundo")),
                    a.into(),
                )
                .into();

                let st3: mainpod::Statement = Statement::ValueOf(
                    AnchoredKey::from((PodId(RawValue::from(256).into()), "!")),
                    b.into(),
                )
                .into();

                let st: mainpod::Statement = Statement::ProductOf(
                    AnchoredKey::from((PodId(RawValue::from(88).into()), "hola")),
                    AnchoredKey::from((PodId(RawValue::from(128).into()), "mundo")),
                    AnchoredKey::from((PodId(RawValue::from(256).into()), "!")),
                )
                .into();
                let op = mainpod::Operation(
                    OperationType::Native(NativeOperation::ProductOf),
                    vec![
                        OperationArg::Index(0),
                        OperationArg::Index(1),
                        OperationArg::Index(2),
                    ],
                    OperationAux::None,
                );
                let prev_statements = vec![st1, st2, st3];
                operation_verify(st, op, prev_statements, vec![])
            })
    }

    #[test]
    fn test_operation_verify_maxof() -> Result<()> {
        I64_TEST_PAIRS.into_iter().try_for_each(|(a, b)| {
            let max = i64::max(a, b);
            let st1: mainpod::Statement = Statement::ValueOf(
                AnchoredKey::from((PodId(RawValue::from(88).into()), "hola")),
                max.into(),
            )
            .into();

            let st2: mainpod::Statement = Statement::ValueOf(
                AnchoredKey::from((PodId(RawValue::from(128).into()), "mundo")),
                a.into(),
            )
            .into();

            let st3: mainpod::Statement = Statement::ValueOf(
                AnchoredKey::from((PodId(RawValue::from(256).into()), "!")),
                b.into(),
            )
            .into();

            let st: mainpod::Statement = Statement::MaxOf(
                AnchoredKey::from((PodId(RawValue::from(88).into()), "hola")),
                AnchoredKey::from((PodId(RawValue::from(128).into()), "mundo")),
                AnchoredKey::from((PodId(RawValue::from(256).into()), "!")),
            )
            .into();
            let op = mainpod::Operation(
                OperationType::Native(NativeOperation::MaxOf),
                vec![
                    OperationArg::Index(0),
                    OperationArg::Index(1),
                    OperationArg::Index(2),
                ],
                OperationAux::None,
            );
            let prev_statements = vec![st1, st2, st3];
            operation_verify(st, op, prev_statements, vec![])
        })
    }

    #[test]
    fn test_operation_verify_maxof_failures() {
        [(5, 3, 4), (5, 5, 8), (3, 4, 5)]
            .into_iter()
            .for_each(|(max, a, b)| {
                let st1: mainpod::Statement = Statement::ValueOf(
                    AnchoredKey::from((PodId(RawValue::from(88).into()), "hola")),
                    max.into(),
                )
                .into();

                let st2: mainpod::Statement = Statement::ValueOf(
                    AnchoredKey::from((PodId(RawValue::from(128).into()), "mundo")),
                    a.into(),
                )
                .into();

                let st3: mainpod::Statement = Statement::ValueOf(
                    AnchoredKey::from((PodId(RawValue::from(256).into()), "!")),
                    b.into(),
                )
                .into();

                let st: mainpod::Statement = Statement::MaxOf(
                    AnchoredKey::from((PodId(RawValue::from(88).into()), "hola")),
                    AnchoredKey::from((PodId(RawValue::from(128).into()), "mundo")),
                    AnchoredKey::from((PodId(RawValue::from(256).into()), "!")),
                )
                .into();
                let op = mainpod::Operation(
                    OperationType::Native(NativeOperation::MaxOf),
                    vec![
                        OperationArg::Index(0),
                        OperationArg::Index(1),
                        OperationArg::Index(2),
                    ],
                    OperationAux::None,
                );
                let prev_statements = vec![st1, st2, st3];
                assert!(operation_verify(st, op, prev_statements, vec![]).is_err())
            })
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

    fn helper_statement_arg_from_template(
        params: &Params,
        st_tmpl_arg: StatementTmplArg,
        args: Vec<Value>,
        expected_st_arg: StatementArg,
    ) -> Result<()> {
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let gadget = CustomOperationVerifyGadget {
            params: params.clone(),
        };

        let st_tmpl_arg_target = builder.add_virtual_statement_tmpl_arg();
        let args_target: Vec<_> = (0..args.len())
            .map(|_| builder.add_virtual_value())
            .collect();
        let st_arg_target =
            gadget.statement_arg_from_template(&mut builder, &st_tmpl_arg_target, &args_target);
        // TODO: Instead of connect, assign witness to result
        let expected_st_arg_target = builder.add_virtual_statement_arg();
        builder.connect_array(expected_st_arg_target.elements, st_arg_target.elements);

        let mut pw = PartialWitness::<F>::new();

        st_tmpl_arg_target.set_targets(&mut pw, params, &st_tmpl_arg)?;
        for (arg_target, arg) in args_target.iter().zip(args.iter()) {
            arg_target.set_targets(&mut pw, arg)?;
        }
        expected_st_arg_target.set_targets(&mut pw, params, &expected_st_arg)?;

        // generate & verify proof
        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();
        data.verify(proof.clone()).unwrap();

        Ok(())
    }

    #[test]
    fn test_statement_arg_from_template() -> Result<()> {
        let params = Params::default();

        let pod_id = PodId(hash_str("pod_id"));

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
        let st_tmpl_arg = StatementTmplArg::AnchoredKey(
            Wildcard::new("a".to_string(), 1),
            KeyOrWildcard::Key(Key::from("foo")),
        );
        let args = vec![Value::from(1), Value::from(pod_id.0), Value::from(3)];
        let expected_st_arg = StatementArg::Key(AnchoredKey::new(pod_id, Key::from("foo")));
        helper_statement_arg_from_template(&params, st_tmpl_arg, args, expected_st_arg)?;

        // case: AnchoredKey(id_wildcard, key_wildcard)
        let st_tmpl_arg = StatementTmplArg::AnchoredKey(
            Wildcard::new("a".to_string(), 1),
            KeyOrWildcard::Wildcard(Wildcard::new("b".to_string(), 2)),
        );
        let args = vec![Value::from(1), Value::from(pod_id.0), Value::from("key")];
        let expected_st_arg = StatementArg::Key(AnchoredKey::new(pod_id, Key::from("key")));
        helper_statement_arg_from_template(&params, st_tmpl_arg, args, expected_st_arg)?;

        // case: WildcardLiteral(wildcard)
        let st_tmpl_arg = StatementTmplArg::WildcardLiteral(Wildcard::new("a".to_string(), 1));
        let args = vec![Value::from(1), Value::from("key"), Value::from(3)];
        let expected_st_arg = StatementArg::WildcardLiteral(WildcardValue::Key(Key::from("key")));
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
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let gadget = CustomOperationVerifyGadget {
            params: params.clone(),
        };

        let st_tmpl_target = builder.add_virtual_statement_tmpl(params);
        let args_target: Vec<_> = (0..args.len())
            .map(|_| builder.add_virtual_value())
            .collect();
        let st_target = gadget.statement_from_template(&mut builder, &st_tmpl_target, &args_target);
        // TODO: Instead of connect, assign witness to result
        let expected_st_target = builder.add_virtual_statement(params);
        builder.connect_flattenable(&expected_st_target, &st_target);

        let mut pw = PartialWitness::<F>::new();

        st_tmpl_target.set_targets(&mut pw, params, &st_tmpl)?;
        for (arg_target, arg) in args_target.iter().zip(args.iter()) {
            arg_target.set_targets(&mut pw, arg)?;
        }
        expected_st_target.set_targets(&mut pw, params, &expected_st.into())?;

        // generate & verify proof
        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();
        data.verify(proof.clone()).unwrap();

        Ok(())
    }

    #[test]
    fn test_statement_from_template() -> Result<()> {
        let params = Params::default();

        let pod_id = PodId(hash_str("pod_id"));

        let st_tmpl = StatementTmpl {
            pred: Predicate::Native(NativePredicate::ValueOf),
            args: vec![
                StatementTmplArg::AnchoredKey(
                    Wildcard::new("a".to_string(), 1),
                    KeyOrWildcard::Key(Key::from("key")),
                ),
                StatementTmplArg::Literal(Value::from("value")),
            ],
        };
        let args = vec![Value::from(1), Value::from(pod_id.0), Value::from(3)];
        let expected_st = Statement::ValueOf(
            AnchoredKey::new(pod_id, Key::from("key")),
            Value::from("value"),
        );
        helper_statement_from_template(&params, st_tmpl, args, expected_st)?;

        Ok(())
    }

    fn helper_custom_operation_verify_gadget(
        params: &Params,
        custom_predicate: CustomPredicateRef,
        op_args: Vec<Statement>,
        args: Vec<WildcardValue>,
        expected_st: Statement,
    ) -> Result<()> {
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let gadget = CustomOperationVerifyGadget {
            params: params.clone(),
        };

        let custom_predicate_target = builder.add_virtual_custom_predicate_entry(params);
        let op_args_target: Vec<_> = (0..args.len())
            .map(|_| builder.add_virtual_statement(params))
            .collect();
        let args_target: Vec<_> = (0..args.len())
            .map(|_| builder.add_virtual_value())
            .collect();
        let (st_target, op_type_target) = gadget.eval(
            &mut builder,
            &custom_predicate_target,
            &op_args_target,
            &args_target,
        )?;

        let mut pw = PartialWitness::<F>::new();

        // Input
        custom_predicate_target.set_targets(&mut pw, params, &custom_predicate)?;
        for (op_arg_target, op_arg) in op_args_target.iter().zip(op_args.into_iter()) {
            op_arg_target.set_targets(&mut pw, params, &op_arg.into())?;
        }
        for (arg_target, arg) in args_target.iter().zip(args.iter()) {
            arg_target.set_targets(&mut pw, &Value::from(arg.raw()))?;
        }
        // Expected Output
        st_target.set_targets(&mut pw, params, &expected_st.into())?;

        let expected_op_type = OperationType::Custom(custom_predicate);
        op_type_target.set_targets(&mut pw, params, &expected_op_type)?;

        // generate & verify proof
        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();
        data.verify(proof.clone()).unwrap();

        Ok(())
    }

    // TODO: Add negative tests
    #[test]
    fn test_custom_operation_verify_gadget() -> frontend::Result<()> {
        // We set the parameters to the exact sizes we have in the test so that we don't have to
        // pad.
        let params = Params {
            max_custom_predicate_arity: 2,
            max_custom_predicate_wildcards: 2,
            max_operation_args: 2,
            max_statement_args: 2,
            ..Default::default()
        };

        use NativePredicate as NP;
        use StatementTmplBuilder as STB;
        let mut builder = CustomPredicateBatchBuilder::new(params.clone(), "batch".into());
        let stb0 = STB::new(NP::ValueOf)
            .arg(("id", key("score")))
            .arg(literal(42));
        let stb1 = STB::new(NP::ValueOf)
            .arg(("id", "secret_key"))
            .arg(literal(1234));
        let _ = builder.predicate_and(
            "pred_and",
            &["id"],
            &["secret_key"],
            &[stb0.clone(), stb1.clone()],
        )?;
        let _ = builder.predicate_or("pred_or", &["id"], &["secret_key"], &[stb0, stb1])?;
        let batch = builder.finish();

        let pod_id = PodId(hash_str("pod_id"));

        // AND
        let custom_predicate = CustomPredicateRef::new(batch.clone(), 0);
        let op_args = vec![
            Statement::ValueOf(
                AnchoredKey::new(pod_id, Key::from("score")),
                Value::from(42),
            ),
            Statement::ValueOf(
                AnchoredKey::new(pod_id, Key::from("foo")),
                Value::from(1234),
            ),
        ];
        let args = vec![
            WildcardValue::PodId(pod_id),
            WildcardValue::Key(Key::from("foo")),
        ];
        let expected_st = Statement::Custom(
            custom_predicate.clone(),
            vec![args[0].clone(), WildcardValue::None],
        );

        helper_custom_operation_verify_gadget(
            &params,
            custom_predicate,
            op_args,
            args,
            expected_st,
        )
        .unwrap();

        // OR (1)
        let custom_predicate = CustomPredicateRef::new(batch.clone(), 1);
        let op_args = vec![
            Statement::ValueOf(
                AnchoredKey::new(pod_id, Key::from("score")),
                Value::from(42),
            ),
            Statement::None,
        ];
        let args = vec![WildcardValue::PodId(pod_id), WildcardValue::None];
        let expected_st = Statement::Custom(
            custom_predicate.clone(),
            vec![args[0].clone(), WildcardValue::None],
        );

        helper_custom_operation_verify_gadget(
            &params,
            custom_predicate,
            op_args,
            args,
            expected_st,
        )
        .unwrap();

        // OR (2)
        let custom_predicate = CustomPredicateRef::new(batch.clone(), 1);
        let op_args = vec![
            Statement::None,
            Statement::ValueOf(
                AnchoredKey::new(pod_id, Key::from("foo")),
                Value::from(1234),
            ),
        ];
        let args = vec![
            WildcardValue::PodId(pod_id),
            WildcardValue::Key(Key::from("foo")),
        ];
        let expected_st = Statement::Custom(
            custom_predicate.clone(),
            vec![args[0].clone(), WildcardValue::None],
        );

        helper_custom_operation_verify_gadget(
            &params,
            custom_predicate,
            op_args,
            args,
            expected_st,
        )
        .unwrap();

        Ok(())
    }
}
