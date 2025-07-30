//! Common functionality to build Pod circuits with plonky2

use std::{array, iter};

use itertools::Itertools;
use plonky2::{
    field::{
        extension::Extendable,
        types::{Field, PrimeField64},
    },
    hash::{
        hash_types::{HashOutTarget, RichField, NUM_HASH_OUT_ELTS},
        poseidon::PoseidonHash,
    },
    iop::{
        generator::{GeneratedValues, SimpleGenerator},
        target::{BoolTarget, Target},
        witness::{PartialWitness, PartitionWitness, Witness, WitnessWrite},
    },
    util::serialization::{Buffer, IoResult, Read, Write},
};
use serde::{Deserialize, Serialize};

use crate::{
    backends::plonky2::{
        basetypes::{CircuitBuilder, CommonCircuitData, D},
        circuits::mainpod::CustomPredicateVerification,
        error::Result,
        mainpod::{Operation, OperationArg, Statement},
        primitives::merkletree::MerkleClaimAndProofTarget,
    },
    middleware::{
        CustomPredicate, CustomPredicateBatch, CustomPredicateRef, NativeOperation,
        NativePredicate, OperationType, Params, Predicate, PredicatePrefix, RawValue, StatementArg,
        StatementTmpl, StatementTmplArg, StatementTmplArgPrefix, ToFields, Value, EMPTY_VALUE, F,
        HASH_SIZE, STATEMENT_ARG_F_LEN, VALUE_SIZE,
    },
};

pub const CODE_SIZE: usize = HASH_SIZE + 2;
const NUM_BITS: usize = 32;

#[derive(Copy, Clone, Debug, Serialize, Deserialize)]
pub struct ValueTarget {
    pub elements: [Target; VALUE_SIZE],
}

impl ValueTarget {
    pub fn zero(builder: &mut CircuitBuilder) -> Self {
        Self {
            elements: [builder.zero(); VALUE_SIZE],
        }
    }

    pub fn one(builder: &mut CircuitBuilder) -> Self {
        Self {
            elements: array::from_fn(|i| {
                if i == 0 {
                    builder.one()
                } else {
                    builder.zero()
                }
            }),
        }
    }

    pub fn from_slice(xs: &[Target]) -> Self {
        assert_eq!(xs.len(), VALUE_SIZE);
        Self {
            elements: array::from_fn(|i| xs[i]),
        }
    }

    pub fn set_targets(&self, pw: &mut PartialWitness<F>, value: &Value) -> Result<()> {
        Ok(pw.set_target_arr(&self.elements, &value.raw().0)?)
    }
}

#[derive(Clone, Serialize, Deserialize)]
pub struct StatementArgTarget {
    #[serde(with = "serde_arrays")]
    pub elements: [Target; STATEMENT_ARG_F_LEN],
}

impl StatementArgTarget {
    pub fn set_targets(
        &self,
        pw: &mut PartialWitness<F>,
        params: &Params,
        arg: &StatementArg,
    ) -> Result<()> {
        Ok(pw.set_target_arr(&self.elements, &arg.to_fields(params))?)
    }

    pub fn new(first: ValueTarget, second: ValueTarget) -> Self {
        let elements: Vec<_> = first.elements.into_iter().chain(second.elements).collect();
        StatementArgTarget {
            elements: elements.try_into().expect("size STATEMENT_ARG_F_LEN"),
        }
    }

    pub fn none(builder: &mut CircuitBuilder) -> Self {
        let empty = builder.constant_value(EMPTY_VALUE);
        Self::new(empty, empty)
    }

    pub fn literal(builder: &mut CircuitBuilder, value: &ValueTarget) -> Self {
        let empty = builder.constant_value(EMPTY_VALUE);
        Self::new(*value, empty)
    }

    pub fn anchored_key(
        _builder: &mut CircuitBuilder,
        pod_id: &ValueTarget,
        key: &ValueTarget,
    ) -> Self {
        Self::new(*pod_id, *key)
    }

    pub fn wildcard_literal(builder: &mut CircuitBuilder, value: &ValueTarget) -> Self {
        let empty = builder.constant_value(EMPTY_VALUE);
        Self::new(*value, empty)
    }

    /// StatementArgTarget to ValueTarget coercion. Make sure to check
    /// that the arg is a value using the `statement_arg_is_value` method
    /// first!
    pub fn as_value(&self) -> ValueTarget {
        ValueTarget::from_slice(&self.elements[..VALUE_SIZE])
    }
}

#[derive(Clone, Serialize, Deserialize)]
pub struct StatementTarget {
    pub predicate: PredicateTarget,
    pub args: Vec<StatementArgTarget>,
}

pub trait Build<T> {
    fn build(self, builder: &mut CircuitBuilder, params: &Params) -> T;
}

impl Build<NativePredicateTarget> for NativePredicate {
    fn build(self, builder: &mut CircuitBuilder, params: &Params) -> NativePredicateTarget {
        NativePredicateTarget::constant(builder, params, self)
    }
}

impl<T> Build<T> for T {
    fn build(self, _builder: &mut CircuitBuilder, _params: &Params) -> T {
        self
    }
}

impl StatementTarget {
    /// Build a new native StatementTarget.  Pads the arguments.
    pub fn new_native(
        builder: &mut CircuitBuilder,
        params: &Params,
        native_predicate: impl Build<NativePredicateTarget>,
        args: &[StatementArgTarget],
    ) -> Self {
        // if native_predicate is const then NativePredicate -> NativePredicateTarget
        // else just use as is
        Self {
            predicate: PredicateTarget::new_native(builder, params, native_predicate),
            args: args
                .iter()
                .cloned()
                .chain(iter::repeat_with(|| StatementArgTarget::none(builder)))
                .take(params.max_statement_args)
                .collect(),
        }
    }

    pub fn set_targets(
        &self,
        pw: &mut PartialWitness<F>,
        params: &Params,
        st: &Statement,
    ) -> Result<()> {
        self.predicate.set_targets(pw, params, st.predicate())?;
        for (i, arg) in st
            .args()
            .iter()
            .chain(iter::repeat(&StatementArg::None))
            .take(params.max_statement_args)
            .enumerate()
        {
            self.args[i].set_targets(pw, params, arg)?;
        }
        Ok(())
    }

    pub fn has_native_type(
        &self,
        builder: &mut CircuitBuilder,
        params: &Params,
        t: NativePredicate,
    ) -> BoolTarget {
        let expected_predicate = PredicateTarget::new_native(builder, params, t);
        builder.is_equal_flattenable(&self.predicate, &expected_predicate)
    }
}

#[derive(Clone, Serialize, Deserialize)]
pub struct OperationTypeTarget {
    #[serde(with = "serde_arrays")]
    pub elements: [Target; Params::operation_type_size()],
}

impl OperationTypeTarget {
    pub fn new_custom(
        builder: &mut CircuitBuilder,
        batch_id: HashOutTarget,
        index: Target,
    ) -> Self {
        // TODO: Use an enum for these prefixes
        let three = builder.constant(F::from_canonical_usize(3));
        let id = batch_id.elements;
        Self {
            elements: [three, id[0], id[1], id[2], id[3], index],
        }
    }

    pub fn as_custom(&self, builder: &mut CircuitBuilder) -> (BoolTarget, HashOutTarget, Target) {
        // TODO: Use an enum for these prefixes
        let three = builder.constant(F::from_canonical_usize(3));
        let op_is_custom = builder.is_equal(self.elements[0], three);
        let batch_id = HashOutTarget::from_vec(self.elements[1..5].to_vec());
        let index = self.elements[5];
        (op_is_custom, batch_id, index)
    }

    pub fn has_native(&self, builder: &mut CircuitBuilder, t: NativeOperation) -> BoolTarget {
        // TODO: Use an enum for these prefixes
        let one = builder.one();
        let op_is_native = builder.is_equal(self.elements[0], one);
        let op_code = builder.constant(F::from_canonical_u64(t as u64));
        let op_code_matches = builder.is_equal(self.elements[1], op_code);
        builder.and(op_is_native, op_code_matches)
    }

    pub fn set_targets(
        &self,
        pw: &mut PartialWitness<F>,
        params: &Params,
        op_type: &OperationType,
    ) -> Result<()> {
        Ok(pw.set_target_arr(&self.elements, &op_type.to_fields(params))?)
    }
}

// TODO: Implement Operation::to_field to determine the size of each element
#[derive(Clone, Serialize, Deserialize)]
pub struct OperationTarget {
    pub op_type: OperationTypeTarget,
    pub args: Vec<IndexTarget>,
    #[serde(with = "serde_arrays")]
    pub aux: [IndexTarget; 2],
}

impl OperationTarget {
    pub fn set_targets(
        &self,
        pw: &mut PartialWitness<F>,
        params: &Params,
        op: &Operation,
    ) -> Result<()> {
        self.op_type.set_targets(pw, params, &op.op_type())?;
        for (i, arg) in op
            .args()
            .iter()
            .chain(iter::repeat(&OperationArg::None))
            .take(params.max_operation_args)
            .enumerate()
        {
            self.args[i].set_targets(pw, arg.as_usize())?;
        }
        let indexes = op.aux().as_usizes();
        for (index_target, index) in self.aux.iter().zip_eq(indexes.iter()) {
            index_target.set_targets(pw, *index)?;
        }
        Ok(())
    }
}

#[derive(Clone)]
pub struct NativePredicateTarget(Target);

impl NativePredicateTarget {
    pub fn constant(
        builder: &mut CircuitBuilder,
        params: &Params,
        native_predicate: NativePredicate,
    ) -> Self {
        let id = native_predicate.to_fields(params);
        assert_eq!(1, id.len());
        Self(builder.constant(id[0]))
    }

    pub fn set_targets(
        &self,
        pw: &mut PartialWitness<F>,
        params: &Params,
        native_predicate: NativePredicate,
    ) -> Result<()> {
        let id = native_predicate.to_fields(params);
        assert_eq!(1, id.len());
        Ok(pw.set_target(self.0, id[0])?)
    }
}

#[derive(Clone, Serialize, Deserialize)]
pub struct PredicateTarget {
    #[serde(with = "serde_arrays")]
    pub(crate) elements: [Target; Params::predicate_size()],
}

impl PredicateTarget {
    pub fn new_native(
        builder: &mut CircuitBuilder,
        params: &Params,
        native_predicate: impl Build<NativePredicateTarget>,
    ) -> Self {
        let prefix = builder.constant(F::from(PredicatePrefix::Native));
        let id = native_predicate.build(builder, params).0;
        let zero = builder.zero();
        Self {
            elements: [prefix, id, zero, zero, zero, zero],
        }
    }

    pub fn new_batch_self(builder: &mut CircuitBuilder, index: Target) -> Self {
        let prefix = builder.constant(F::from(PredicatePrefix::BatchSelf));
        let zero = builder.zero();
        Self {
            elements: [prefix, index, zero, zero, zero, zero],
        }
    }

    pub fn new_custom(
        builder: &mut CircuitBuilder,
        batch_id: HashOutTarget,
        index: Target,
    ) -> Self {
        let prefix = builder.constant(F::from(PredicatePrefix::Custom));
        let id = batch_id.elements;
        Self {
            elements: [prefix, id[0], id[1], id[2], id[3], index],
        }
    }

    pub fn set_targets(
        &self,
        pw: &mut PartialWitness<F>,
        params: &Params,
        predicate: Predicate,
    ) -> Result<()> {
        Ok(pw.set_target_arr(&self.elements, &predicate.to_fields(params))?)
    }
}

/// Mirrors `middleware::KeyOrWildcard`
#[derive(Clone)]
pub struct LiteralOrWildcardTarget {
    pub elements: [Target; VALUE_SIZE],
}

impl LiteralOrWildcardTarget {
    fn from_slice(v: &[Target]) -> Self {
        Self {
            elements: v.try_into().expect("len is VALUE_SIZE"),
        }
    }
    /// cases: ((is_key, key), (is_wildcard, wildcard_index))
    pub fn cases(
        &self,
        builder: &mut CircuitBuilder,
    ) -> ((BoolTarget, ValueTarget), (BoolTarget, Target)) {
        let zero = builder.zero();
        let is_zero_tail: Vec<_> = (1..4)
            .map(|i| builder.is_equal(self.elements[i], zero))
            .collect();
        let is_wildcard = is_zero_tail
            .into_iter()
            .reduce(|acc, x| builder.and(acc, x))
            .expect("len > 1");
        let is_key = builder.not(is_wildcard);
        let key = ValueTarget::from_slice(&self.elements);
        let wildcard_index = self.elements[0];

        ((is_key, key), (is_wildcard, wildcard_index))
    }
}

#[derive(Clone, Serialize, Deserialize)]
pub struct StatementTmplArgTarget {
    #[serde(with = "serde_arrays")]
    pub elements: [Target; Params::statement_tmpl_arg_size()],
}

impl StatementTmplArgTarget {
    pub fn as_none(&self, builder: &mut CircuitBuilder) -> BoolTarget {
        let prefix = builder.constant(F::from(StatementTmplArgPrefix::None));
        builder.is_equal(self.elements[0], prefix)
    }

    pub fn as_literal(&self, builder: &mut CircuitBuilder) -> (BoolTarget, ValueTarget) {
        let prefix = builder.constant(F::from(StatementTmplArgPrefix::Literal));
        let case_ok = builder.is_equal(self.elements[0], prefix);
        let value = ValueTarget::from_slice(&self.elements[1..5]);
        (case_ok, value)
    }

    pub fn as_anchored_key(
        &self,
        builder: &mut CircuitBuilder,
    ) -> (BoolTarget, Target, LiteralOrWildcardTarget) {
        let prefix = builder.constant(F::from(StatementTmplArgPrefix::AnchoredKey));
        let case_ok = builder.is_equal(self.elements[0], prefix);
        let id_wildcard_index = self.elements[1];
        let value_key_or_wildcard = LiteralOrWildcardTarget::from_slice(&self.elements[5..9]);
        (case_ok, id_wildcard_index, value_key_or_wildcard)
    }

    pub fn as_wildcard_literal(&self, builder: &mut CircuitBuilder) -> (BoolTarget, Target) {
        let prefix = builder.constant(F::from(StatementTmplArgPrefix::WildcardLiteral));
        let case_ok = builder.is_equal(self.elements[0], prefix);
        let wildcard_index = self.elements[1];
        (case_ok, wildcard_index)
    }

    pub fn set_targets(
        &self,
        pw: &mut PartialWitness<F>,
        params: &Params,
        st_tmpl_arg: &StatementTmplArg,
    ) -> Result<()> {
        Ok(pw.set_target_arr(&self.elements, &st_tmpl_arg.to_fields(params))?)
    }
}

#[derive(Clone, Serialize, Deserialize)]
pub struct StatementTmplTarget {
    pub pred: PredicateTarget,
    pub args: Vec<StatementTmplArgTarget>,
}

impl StatementTmplTarget {
    pub fn set_targets(
        &self,
        pw: &mut PartialWitness<F>,
        params: &Params,
        st_tmpl: &StatementTmpl,
    ) -> Result<()> {
        Ok(pw.set_target_arr(&self.flatten(), &st_tmpl.to_fields(params))?)
    }
}

#[derive(Clone, Serialize, Deserialize)]
pub struct CustomPredicateTarget {
    pub conjunction: BoolTarget,
    // len = params.max_custom_predicate_arity
    pub statements: Vec<StatementTmplTarget>,
    pub args_len: Target,
}

impl CustomPredicateTarget {
    pub fn set_targets(
        &self,
        pw: &mut PartialWitness<F>,
        params: &Params,
        custom_predicate: &CustomPredicate,
    ) -> Result<()> {
        Ok(pw.set_target_arr(&self.flatten(), &custom_predicate.to_fields(params))?)
    }
}

#[derive(Clone, Serialize, Deserialize)]
pub struct CustomPredicateBatchTarget {
    pub predicates: Vec<CustomPredicateTarget>,
}

impl CustomPredicateBatchTarget {
    pub fn id(&self, builder: &mut CircuitBuilder) -> HashOutTarget {
        let flattened = self.predicates.iter().flat_map(|cp| cp.flatten()).collect();
        builder.hash_n_to_hash_no_pad::<PoseidonHash>(flattened)
    }

    pub fn set_targets(
        &self,
        pw: &mut PartialWitness<F>,
        params: &Params,
        custom_predicate_batch: &CustomPredicateBatch,
    ) -> Result<()> {
        let pad_predicate = CustomPredicate::empty();
        for (i, predicate) in custom_predicate_batch
            .predicates()
            .iter()
            .chain(iter::repeat(&pad_predicate))
            .take(params.max_custom_batch_size)
            .enumerate()
        {
            self.predicates[i].set_targets(pw, params, predicate)?;
        }
        Ok(())
    }
}

/// Custom predicate table entry
#[derive(Clone, Serialize, Deserialize)]
pub struct CustomPredicateEntryTarget {
    pub id: HashOutTarget,
    pub index: Target,
    pub predicate: CustomPredicateTarget,
}

impl CustomPredicateEntryTarget {
    pub fn set_targets(
        &self,
        pw: &mut PartialWitness<F>,
        params: &Params,
        predicate: &CustomPredicateRef,
    ) -> Result<()> {
        pw.set_target_arr(&self.id.elements, &predicate.batch.id().0)?;
        pw.set_target(self.index, F::from_canonical_usize(predicate.index))?;

        // Replace statement templates of batch-self with (id,index)
        let batch = &predicate.batch;
        let predicate = predicate.predicate();
        let statements = predicate
            .statements
            .clone()
            .into_iter()
            .map(|st_tmpl| {
                let pred = match st_tmpl.pred {
                    Predicate::BatchSelf(i) => Predicate::Custom(CustomPredicateRef {
                        batch: batch.clone(),
                        index: i,
                    }),
                    p => p,
                };
                StatementTmpl {
                    pred,
                    args: st_tmpl.args,
                }
            })
            .collect_vec();
        let predicate = CustomPredicate {
            name: predicate.name.clone(),
            conjunction: predicate.conjunction,
            statements,
            args_len: predicate.args_len,
            wildcard_names: predicate.wildcard_names.clone(),
        };
        self.predicate.set_targets(pw, params, &predicate)?;
        Ok(())
    }
}

impl Flattenable for CustomPredicateEntryTarget {
    fn flatten(&self) -> Vec<Target> {
        self.id
            .elements
            .iter()
            .chain(iter::once(&self.index))
            .chain(self.predicate.flatten().iter())
            .cloned()
            .collect()
    }
    fn from_flattened(params: &Params, vs: &[Target]) -> Self {
        Self {
            id: HashOutTarget::from_flattened(params, &vs[0..4]),
            index: vs[4],
            predicate: CustomPredicateTarget::from_flattened(params, &vs[5..]),
        }
    }
}

impl CustomPredicateEntryTarget {
    pub fn hash(&self, builder: &mut CircuitBuilder) -> HashOutTarget {
        builder.hash_n_to_hash_no_pad::<PoseidonHash>(self.flatten())
    }
}

// Custom predicate verification table entry
#[derive(Clone, Serialize, Deserialize)]
pub struct CustomPredicateVerifyEntryTarget {
    pub custom_predicate_table_index: IndexTarget,
    pub custom_predicate: CustomPredicateEntryTarget,
    pub args: Vec<ValueTarget>,
    pub op_args: Vec<StatementTarget>,
}

impl CustomPredicateVerifyEntryTarget {
    pub fn new_virtual(params: &Params, builder: &mut CircuitBuilder) -> Self {
        let custom_predicate_table_len =
            params.max_custom_predicate_batches * params.max_custom_batch_size;
        CustomPredicateVerifyEntryTarget {
            custom_predicate_table_index: IndexTarget::new_virtual(
                custom_predicate_table_len,
                builder,
            ),
            custom_predicate: builder.add_virtual_custom_predicate_entry(params),
            args: (0..params.max_custom_predicate_wildcards)
                .map(|_| builder.add_virtual_value())
                .collect(),
            op_args: (0..params.max_operation_args)
                .map(|_| builder.add_virtual_statement(params))
                .collect(),
        }
    }
    pub fn set_targets(
        &self,
        pw: &mut PartialWitness<F>,
        params: &Params,
        cpv: &CustomPredicateVerification,
    ) -> Result<()> {
        self.custom_predicate_table_index
            .set_targets(pw, cpv.custom_predicate_table_index)?;
        // Replace statement templates of batch-self with (id,index)
        self.custom_predicate
            .set_targets(pw, params, &cpv.custom_predicate)?;
        let pad_arg = Value::from(0);
        for (arg_target, arg) in self.args.iter().zip_eq(
            cpv.args
                .iter()
                .chain(iter::repeat(&pad_arg))
                .take(params.max_custom_predicate_wildcards),
        ) {
            arg_target.set_targets(pw, &Value::from(arg.raw()))?;
        }
        let pad_op_arg = Statement(Predicate::Native(NativePredicate::None), vec![]);
        for (op_arg_target, op_arg) in self.op_args.iter().zip_eq(
            cpv.op_args
                .iter()
                .chain(iter::repeat(&pad_op_arg))
                .take(params.max_operation_args),
        ) {
            op_arg_target.set_targets(pw, params, op_arg)?
        }
        Ok(())
    }
}

/// Query for the custom predicate verification table
#[derive(Clone, Serialize, Deserialize)]
pub struct CustomPredicateVerifyQueryTarget {
    pub statement: StatementTarget,
    pub op_type: OperationTypeTarget,
    pub op_args: Vec<StatementTarget>,
}

impl CustomPredicateVerifyQueryTarget {
    pub fn hash(&self, builder: &mut CircuitBuilder) -> HashOutTarget {
        builder.hash_n_to_hash_no_pad::<PoseidonHash>(self.flatten())
    }
}

impl Flattenable for CustomPredicateVerifyQueryTarget {
    fn flatten(&self) -> Vec<Target> {
        self.statement
            .flatten()
            .iter()
            .chain(self.op_type.elements.iter())
            .cloned()
            .chain(self.op_args.iter().flat_map(|op_arg| op_arg.flatten()))
            .collect()
    }
    fn from_flattened(params: &Params, vs: &[Target]) -> Self {
        let (pos, size) = (0, params.statement_size());
        let statement = StatementTarget::from_flattened(params, &vs[pos..pos + size]);
        let (pos, size) = (pos + size, params.operation_size(IndexTarget::f_len()));
        let op_type = OperationTypeTarget {
            elements: vs[pos..pos + size]
                .try_into()
                .expect("len = operation_type_size"),
        };
        let (pos, size) = (pos + size, params.statement_size());
        let op_args = (0..params.max_operation_args)
            .map(|i| {
                StatementTarget::from_flattened(params, &vs[pos + i * size..pos + (1 + i) * size])
            })
            .collect();
        Self {
            statement,
            op_type,
            op_args,
        }
    }
}

/// Trait for target structs that may be converted to and from vectors
/// of targets.
pub trait Flattenable {
    fn flatten(&self) -> Vec<Target>;
    fn from_flattened(params: &Params, vs: &[Target]) -> Self;
}

/// For the purpose of op verification, we need only look up the
/// Merkle claim rather than the Merkle proof since it is verified
/// elsewhere.
#[derive(Copy, Clone)]
pub struct MerkleClaimTarget {
    pub(crate) enabled: BoolTarget,
    pub(crate) root: HashOutTarget,
    pub(crate) key: ValueTarget,
    pub(crate) value: ValueTarget,
    pub(crate) existence: BoolTarget,
}

impl From<MerkleClaimAndProofTarget> for MerkleClaimTarget {
    fn from(pf: MerkleClaimAndProofTarget) -> Self {
        Self {
            enabled: pf.enabled,
            root: pf.root,
            key: pf.key,
            value: pf.value,
            existence: pf.existence,
        }
    }
}

impl Flattenable for HashOutTarget {
    fn flatten(&self) -> Vec<Target> {
        self.elements.to_vec()
    }
    fn from_flattened(_params: &Params, vs: &[Target]) -> Self {
        assert_eq!(vs.len(), HASH_SIZE);
        Self {
            elements: array::from_fn(|i| vs[i]),
        }
    }
}

impl Flattenable for ValueTarget {
    fn flatten(&self) -> Vec<Target> {
        self.elements.to_vec()
    }
    fn from_flattened(_params: &Params, vs: &[Target]) -> Self {
        Self::from_slice(vs)
    }
}

impl Flattenable for MerkleClaimTarget {
    fn flatten(&self) -> Vec<Target> {
        [
            vec![self.enabled.target],
            self.root.elements.to_vec(),
            self.key.elements.to_vec(),
            self.value.elements.to_vec(),
            vec![self.existence.target],
        ]
        .concat()
    }

    fn from_flattened(_params: &Params, vs: &[Target]) -> Self {
        Self {
            enabled: BoolTarget::new_unsafe(vs[0]),
            root: HashOutTarget::from_vec(vs[1..1 + NUM_HASH_OUT_ELTS].to_vec()),
            key: ValueTarget::from_slice(
                &vs[1 + NUM_HASH_OUT_ELTS..1 + NUM_HASH_OUT_ELTS + VALUE_SIZE],
            ),
            value: ValueTarget::from_slice(
                &vs[1 + NUM_HASH_OUT_ELTS + VALUE_SIZE..1 + NUM_HASH_OUT_ELTS + 2 * VALUE_SIZE],
            ),
            existence: BoolTarget::new_unsafe(vs[1 + NUM_HASH_OUT_ELTS + 2 * VALUE_SIZE]),
        }
    }
}

impl Flattenable for PredicateTarget {
    fn flatten(&self) -> Vec<Target> {
        self.elements.to_vec()
    }

    fn from_flattened(_params: &Params, v: &[Target]) -> Self {
        Self {
            elements: v.try_into().expect("len is predicate_size"),
        }
    }
}

impl Flattenable for StatementTarget {
    fn flatten(&self) -> Vec<Target> {
        self.predicate
            .flatten()
            .into_iter()
            .chain(self.args.iter().flat_map(|a| &a.elements).cloned())
            .collect()
    }

    fn from_flattened(params: &Params, v: &[Target]) -> Self {
        let num_args = (v.len() - Params::predicate_size()) / STATEMENT_ARG_F_LEN;
        assert_eq!(
            v.len(),
            Params::predicate_size() + num_args * STATEMENT_ARG_F_LEN
        );
        let predicate = PredicateTarget::from_flattened(params, &v[..Params::predicate_size()]);
        let args = (0..num_args)
            .map(|i| StatementArgTarget {
                elements: array::from_fn(|j| {
                    v[Params::predicate_size() + i * STATEMENT_ARG_F_LEN + j]
                }),
            })
            .collect();

        Self { predicate, args }
    }
}

impl Flattenable for CustomPredicateTarget {
    fn flatten(&self) -> Vec<Target> {
        iter::once(self.conjunction.target)
            .chain(iter::once(self.args_len))
            .chain(self.statements.iter().flat_map(|s| s.flatten()))
            .collect()
    }

    fn from_flattened(params: &Params, v: &[Target]) -> Self {
        // We assume that `from_flattened` is always called with the output of `flattened`, so
        // this `BoolTarget` should actually safe.
        let conjunction = BoolTarget::new_unsafe(v[0]);
        let args_len = v[1];
        let st_tmpl_size = params.statement_tmpl_size();
        let statements = (0..params.max_custom_predicate_arity)
            .map(|i| {
                let st_v = &v[2 + st_tmpl_size * i..2 + st_tmpl_size * (i + 1)];
                StatementTmplTarget::from_flattened(params, st_v)
            })
            .collect();
        Self {
            conjunction,
            statements,
            args_len,
        }
    }
}

impl Flattenable for StatementTmplTarget {
    fn flatten(&self) -> Vec<Target> {
        self.pred
            .flatten()
            .into_iter()
            .chain(self.args.iter().flat_map(|sta| sta.flatten()))
            .collect()
    }

    fn from_flattened(params: &Params, v: &[Target]) -> Self {
        let pred_end = Params::predicate_size();
        let pred = PredicateTarget::from_flattened(params, &v[..pred_end]);
        let sta_size = Params::statement_tmpl_arg_size();
        let args = (0..params.max_statement_args)
            .map(|i| {
                let sta_v = &v[pred_end + sta_size * i..pred_end + sta_size * (i + 1)];
                StatementTmplArgTarget::from_flattened(params, sta_v)
            })
            .collect();
        Self { pred, args }
    }
}

impl Flattenable for StatementTmplArgTarget {
    fn flatten(&self) -> Vec<Target> {
        self.elements.to_vec()
    }

    fn from_flattened(_params: &Params, v: &[Target]) -> Self {
        Self {
            elements: v.try_into().expect("len is statement_tmpl_arg_size"),
        }
    }
}

/// Index to an array for random access
#[derive(Clone, Serialize, Deserialize)]
pub struct IndexTarget {
    max_array_len: usize,
    low: Target,
    high: Target,
}

impl IndexTarget {
    // Length in field elements
    pub const fn f_len() -> usize {
        2
    }
    pub fn new_virtual(max_array_len: usize, builder: &mut CircuitBuilder) -> Self {
        // Limit the maximum array length to avoid abusing `vec_ref`
        assert!(max_array_len <= 256);
        Self {
            max_array_len,
            low: builder.add_virtual_target(),
            high: if max_array_len > 64 {
                builder.add_virtual_target()
            } else {
                builder.zero()
            },
        }
    }

    pub fn set_targets(&self, pw: &mut PartialWitness<F>, index: usize) -> Result<()> {
        assert!(index == 0 || index < self.max_array_len);
        pw.set_target(self.low, F::from_canonical_usize(index & ((1 << 6) - 1)))?;
        pw.set_target(self.high, F::from_canonical_usize(index >> 6))?;
        Ok(())
    }
}

pub trait CircuitBuilderPod<F: RichField + Extendable<D>, const D: usize> {
    fn connect_values(&mut self, x: ValueTarget, y: ValueTarget);
    fn connect_slice(&mut self, xs: &[Target], ys: &[Target]);
    fn add_virtual_value(&mut self) -> ValueTarget;
    fn add_virtual_statement(&mut self, params: &Params) -> StatementTarget;
    fn add_virtual_statement_arg(&mut self) -> StatementArgTarget;
    fn add_virtual_predicate(&mut self) -> PredicateTarget;
    fn add_virtual_operation_type(&mut self) -> OperationTypeTarget;
    fn add_virtual_operation(&mut self, params: &Params) -> OperationTarget;
    fn add_virtual_statement_tmpl_arg(&mut self) -> StatementTmplArgTarget;
    fn add_virtual_statement_tmpl(&mut self, params: &Params) -> StatementTmplTarget;
    fn add_virtual_custom_predicate(&mut self, params: &Params) -> CustomPredicateTarget;
    fn add_virtual_custom_predicate_batch(&mut self, params: &Params)
        -> CustomPredicateBatchTarget;
    fn add_virtual_custom_predicate_entry(&mut self, params: &Params)
        -> CustomPredicateEntryTarget;
    fn select_value(&mut self, b: BoolTarget, x: ValueTarget, y: ValueTarget) -> ValueTarget;
    fn select_statement_arg(
        &mut self,
        b: BoolTarget,
        x: &StatementArgTarget,
        y: &StatementArgTarget,
    ) -> StatementArgTarget;
    fn select_bool(&mut self, b: BoolTarget, x: BoolTarget, y: BoolTarget) -> BoolTarget;
    fn constant_value(&mut self, v: RawValue) -> ValueTarget;
    fn is_equal_slice(&mut self, xs: &[Target], ys: &[Target]) -> BoolTarget;

    // Convenience methods for checking values.
    /// Checks whether `xs` is right-padded with 0s so as to represent a `Value`.
    fn statement_arg_is_value(&mut self, arg: &StatementArgTarget) -> BoolTarget;

    /// Checks whether `x` is an i64, which involves checking that it
    /// consists of two `u32` limbs.
    fn assert_i64(&mut self, x: ValueTarget);

    /// Checks whether an i64 is negative.
    fn i64_is_negative(&mut self, x: ValueTarget) -> BoolTarget;

    /// Checks whether `x < y` if `b` is true. This assumes that `x`
    /// and `y` each consist of two `u32` limbs.
    fn assert_i64_less_if(&mut self, b: BoolTarget, x: ValueTarget, y: ValueTarget);

    /// Computes `x + y` assuming `x` and `y` are assigned `i64`
    /// values.
    fn i64_wrapping_add(&mut self, x: ValueTarget, y: ValueTarget) -> ValueTarget;

    /// Computes `x + y` assuming `x` and `y` are assigned `i64`
    /// values. Enforces no overflow.
    fn i64_add(&mut self, x: ValueTarget, y: ValueTarget) -> ValueTarget;

    /// Computes `x * y` assuming `x` and `y` are assigned `i64`
    /// values. Enforces no overflow.
    fn i64_mul(&mut self, x: ValueTarget, y: ValueTarget) -> ValueTarget;

    /// Computes the canonical involution of `x` in `i64`, i.e. the
    /// negation of `x` as an `i64`.
    fn i64_inv(&mut self, x: ValueTarget) -> ValueTarget;

    /// Computes the absolute value of `x` *as an element of
    /// `i64`*. Includes sign indicator (true if negative).
    fn i64_abs(&mut self, x: ValueTarget) -> (ValueTarget, BoolTarget);

    /// Creates value target that is a hash of two given values.
    fn hash_values(&mut self, x: ValueTarget, y: ValueTarget) -> ValueTarget;

    /// Like `random_access` but allows using longer arrays.
    fn random_access_long(&mut self, i: &IndexTarget, array: &[Target]) -> Target;

    /// Convenience methods for accessing and connecting elements of
    /// (vectors of) flattenables.
    fn vec_ref<T: Flattenable>(&mut self, params: &Params, ts: &[T], i: &IndexTarget) -> T;
    /// Like `vec_ref` but only supports arrays up to 64 elements and the index is a simple `Target`
    fn vec_ref_small<T: Flattenable>(&mut self, params: &Params, ts: &[T], i: Target) -> T;
    fn select_flattenable<T: Flattenable>(
        &mut self,
        params: &Params,
        b: BoolTarget,
        x: &T,
        y: &T,
    ) -> T;
    fn connect_flattenable<T: Flattenable>(&mut self, xs: &T, ys: &T);
    fn is_equal_flattenable<T: Flattenable>(&mut self, xs: &T, ys: &T) -> BoolTarget;

    /// Convenience methods for Boolean into-iters.
    fn all(&mut self, xs: impl IntoIterator<Item = BoolTarget>) -> BoolTarget;
    fn any(&mut self, xs: impl IntoIterator<Item = BoolTarget>) -> BoolTarget;

    /// Return a bit-mask of size `len` that selects all positions lower than `n`
    fn lt_mask(&mut self, len: usize, n: Target) -> Vec<BoolTarget>;
}

impl CircuitBuilderPod<F, D> for CircuitBuilder {
    fn connect_slice(&mut self, xs: &[Target], ys: &[Target]) {
        assert_eq!(xs.len(), ys.len());
        for (x, y) in xs.iter().zip(ys.iter()) {
            self.connect(*x, *y);
        }
    }

    fn connect_values(&mut self, x: ValueTarget, y: ValueTarget) {
        self.connect_slice(&x.elements, &y.elements);
    }

    fn add_virtual_value(&mut self) -> ValueTarget {
        ValueTarget {
            elements: self.add_virtual_target_arr(),
        }
    }

    fn add_virtual_statement(&mut self, params: &Params) -> StatementTarget {
        let predicate = self.add_virtual_predicate();
        StatementTarget {
            predicate,
            args: (0..params.max_statement_args)
                .map(|_| self.add_virtual_statement_arg())
                .collect(),
        }
    }

    fn add_virtual_statement_arg(&mut self) -> StatementArgTarget {
        StatementArgTarget {
            elements: self.add_virtual_target_arr(),
        }
    }

    fn add_virtual_predicate(&mut self) -> PredicateTarget {
        PredicateTarget {
            elements: self.add_virtual_target_arr(),
        }
    }

    fn add_virtual_operation_type(&mut self) -> OperationTypeTarget {
        OperationTypeTarget {
            elements: self.add_virtual_target_arr(),
        }
    }

    fn add_virtual_operation(&mut self, params: &Params) -> OperationTarget {
        OperationTarget {
            op_type: self.add_virtual_operation_type(),
            args: (0..params.max_operation_args)
                .map(|_| IndexTarget::new_virtual(params.statement_table_size(), self))
                .collect(),
            aux: [
                IndexTarget::new_virtual(params.max_merkle_proofs_containers, self),
                IndexTarget::new_virtual(params.max_custom_predicate_verifications, self),
            ],
        }
    }

    fn add_virtual_statement_tmpl_arg(&mut self) -> StatementTmplArgTarget {
        StatementTmplArgTarget {
            elements: self.add_virtual_target_arr(),
        }
    }

    fn add_virtual_statement_tmpl(&mut self, params: &Params) -> StatementTmplTarget {
        let args = (0..params.max_statement_args)
            .map(|_| self.add_virtual_statement_tmpl_arg())
            .collect();
        StatementTmplTarget {
            pred: self.add_virtual_predicate(),
            args,
        }
    }

    fn add_virtual_custom_predicate(&mut self, params: &Params) -> CustomPredicateTarget {
        let statements = (0..params.max_custom_predicate_arity)
            .map(|_| self.add_virtual_statement_tmpl(params))
            .collect();
        CustomPredicateTarget {
            conjunction: self.add_virtual_bool_target_safe(),
            statements,
            args_len: self.add_virtual_target(),
        }
    }

    fn add_virtual_custom_predicate_batch(
        &mut self,
        params: &Params,
    ) -> CustomPredicateBatchTarget {
        CustomPredicateBatchTarget {
            predicates: (0..params.max_custom_batch_size)
                .map(|_| self.add_virtual_custom_predicate(params))
                .collect(),
        }
    }

    fn add_virtual_custom_predicate_entry(
        &mut self,
        params: &Params,
    ) -> CustomPredicateEntryTarget {
        CustomPredicateEntryTarget {
            id: self.add_virtual_hash(),
            index: self.add_virtual_target(),
            predicate: self.add_virtual_custom_predicate(params),
        }
    }

    fn select_value(&mut self, b: BoolTarget, x: ValueTarget, y: ValueTarget) -> ValueTarget {
        ValueTarget {
            elements: std::array::from_fn(|i| self.select(b, x.elements[i], y.elements[i])),
        }
    }

    fn select_statement_arg(
        &mut self,
        b: BoolTarget,
        x: &StatementArgTarget,
        y: &StatementArgTarget,
    ) -> StatementArgTarget {
        StatementArgTarget {
            elements: std::array::from_fn(|i| self.select(b, x.elements[i], y.elements[i])),
        }
    }

    fn select_bool(&mut self, b: BoolTarget, x: BoolTarget, y: BoolTarget) -> BoolTarget {
        BoolTarget::new_unsafe(self.select(b, x.target, y.target))
    }

    fn constant_value(&mut self, v: RawValue) -> ValueTarget {
        ValueTarget {
            elements: std::array::from_fn(|i| {
                self.constant(F::from_noncanonical_u64(v.0[i].to_noncanonical_u64()))
            }),
        }
    }

    fn is_equal_slice(&mut self, xs: &[Target], ys: &[Target]) -> BoolTarget {
        assert_eq!(xs.len(), ys.len());
        let init = self._true();
        xs.iter().zip(ys.iter()).fold(init, |ok, (x, y)| {
            let is_eq = self.is_equal(*x, *y);
            self.and(ok, is_eq)
        })
    }

    fn statement_arg_is_value(&mut self, arg: &StatementArgTarget) -> BoolTarget {
        let zeros = iter::repeat(self.zero())
            .take(STATEMENT_ARG_F_LEN - VALUE_SIZE)
            .collect::<Vec<_>>();
        self.is_equal_slice(&arg.elements[VALUE_SIZE..], &zeros)
    }

    fn assert_i64(&mut self, x: ValueTarget) {
        // `x` should only have two limbs.
        x.elements
            .into_iter()
            .skip(2)
            .for_each(|l| self.assert_zero(l));

        // 32-bit range check.
        self.range_check(x.elements[0], NUM_BITS);
        self.range_check(x.elements[1], NUM_BITS);
    }

    fn i64_is_negative(&mut self, x: ValueTarget) -> BoolTarget {
        // x is negative if the most significant bit of its most
        // significant limb is 1.
        let high_bits = self.split_le(x.elements[1], NUM_BITS);
        high_bits[31]
    }

    fn assert_i64_less_if(&mut self, b: BoolTarget, x: ValueTarget, y: ValueTarget) {
        // If b is false, replace `x` and `y` with dummy values.
        let zero = ValueTarget::zero(self);
        let one = ValueTarget::one(self);
        let x = self.select_value(b, x, zero);
        let y = self.select_value(b, y, one);

        // Lt assertion.
        let assert_limb_lt = |builder: &mut Self, x, y| {
            // Check that `y-1-x` fits within `NUM_BITS` bits.
            let one = builder.one();
            let y_minus_one = builder.sub(y, one);
            let expr = builder.sub(y_minus_one, x);
            builder.range_check(expr, NUM_BITS);
        };

        // Check if `x` and `y` have the same sign. If not, swap.
        let x_is_negative = self.i64_is_negative(x);
        let y_is_negative = self.i64_is_negative(y);
        let same_sign_ind = self.is_equal(x_is_negative.target, y_is_negative.target);
        let (x, y) = (
            self.select_value(same_sign_ind, x, y),
            self.select_value(same_sign_ind, y, x),
        );

        let big_limbs_eq = self.is_equal(x.elements[1], y.elements[1]);
        let lhs = self.select(big_limbs_eq, x.elements[0], x.elements[1]);
        let rhs = self.select(big_limbs_eq, y.elements[0], y.elements[1]);
        assert_limb_lt(self, lhs, rhs);
    }

    fn i64_wrapping_add(&mut self, x: ValueTarget, y: ValueTarget) -> ValueTarget {
        let zero = self.zero();

        // Add components and carry where appropriate.
        let (_, sum) = std::iter::zip(&x.elements[..2], &y.elements[..2]).fold(
            (zero, vec![]),
            |(carry, out), (&a, &b)| {
                let sum = [a, b, carry]
                    .into_iter()
                    .reduce(|alpha, beta| self.add(alpha, beta))
                    .expect("Iterator should be nonempty.");
                let (sum_residue, sum_quotient) = self.split_low_high(sum, NUM_BITS, F::BITS);
                (sum_quotient, [out, vec![sum_residue]].concat())
            },
        );

        ValueTarget::from_slice(&[sum[0], sum[1], zero, zero])
    }

    fn i64_add(&mut self, x: ValueTarget, y: ValueTarget) -> ValueTarget {
        let zero = self.zero();
        let sum = self.i64_wrapping_add(x, y);

        // Overflow check.
        let x_is_negative = self.i64_is_negative(x);
        let x_is_nonnegative = self.not(x_is_negative);
        let y_is_negative = self.i64_is_negative(y);
        let y_is_nonnegative = self.not(y_is_negative);

        let sum_is_negative = self.i64_is_negative(sum);
        let sum_is_nonnegative = self.not(sum_is_negative);

        let overflow_conditions = [
            self.all([x_is_negative, y_is_negative, sum_is_nonnegative]),
            self.all([x_is_nonnegative, y_is_nonnegative, sum_is_negative]),
        ];

        let overflow = self.any(overflow_conditions);

        self.connect(overflow.target, zero);

        sum
    }

    fn i64_mul(&mut self, x: ValueTarget, y: ValueTarget) -> ValueTarget {
        let zero = self.zero();
        let i64_min = ValueTarget::from_slice(&self.constants(&RawValue::from(i64::MIN).0));
        let (abs_x, x_is_negative) = self.i64_abs(x);
        let (abs_y, y_is_negative) = self.i64_abs(y);

        // Sign indicators.
        let same_sign_ind = self.is_equal(x_is_negative.target, y_is_negative.target);
        let prod_sign = self.not(same_sign_ind);

        // Determine product of absolute values.
        let x = abs_x.elements[..2].to_vec();
        let y = abs_y.elements[..2].to_vec();

        let prods = [
            self.mul(x[0], y[0]),
            self.mul(x[0], y[1]),
            self.mul(x[1], y[0]),
        ]
        .into_iter()
        .map(|p| self.split_low_high(p, NUM_BITS, F::BITS))
        .collect::<Vec<_>>();

        let prod_lower = prods[0].0;

        let (prod_upper, _) = {
            let sum1 = self.add(prods[1].0, prods[2].0);
            let sum2 = self.add(sum1, prods[0].1);
            self.split_low_high(sum2, NUM_BITS, F::BITS)
        };

        let abs_prod = ValueTarget::from_slice(&[prod_lower, prod_upper, zero, zero]);

        // Overflow check: The latter two products in `prods` should
        // have zero higher-order coefficients.
        let no_spillovers = [
            self.is_equal(prods[1].1, zero),
            self.is_equal(prods[2].1, zero),
        ]
        .into_iter()
        .reduce(|a, b| self.and(a, b))
        .expect("Iterator should be nonempty.");

        // Overflow check: The product of the higher-order
        // coefficients should be zero.
        let higher_prod = self.mul(x[1], y[1]);
        let higher_prod_is_zero = self.is_equal(higher_prod, zero);

        // Overflow check: The product of the absolute values is
        // either nonnegative or negative and equal to `i64::MIN`.
        let abs_prod_is_negative = self.i64_is_negative(abs_prod);
        let abs_prod_is_nonnegative = self.not(abs_prod_is_negative);
        let abs_prod_is_min = self.is_equal_slice(&abs_prod.elements, &i64_min.elements);
        let abs_prod_sign_ok = self.and(abs_prod_is_min, prod_sign);
        let abs_prod_sign_ok = self.or(abs_prod_sign_ok, abs_prod_is_nonnegative);

        // Combine the above conditions.
        let no_overflow = self.and(abs_prod_sign_ok, higher_prod_is_zero);
        let no_overflow = self.and(no_overflow, no_spillovers);
        self.assert_one(no_overflow.target);

        // Take sign into account.
        let minus_abs_prod = self.i64_inv(abs_prod);

        self.select_value(prod_sign, minus_abs_prod, abs_prod)
    }

    fn i64_inv(&mut self, x: ValueTarget) -> ValueTarget {
        let zero = self.zero();
        let one = ValueTarget::one(self);
        let u32_max = self.constant(F::from_canonical_u32(u32::MAX));

        let flipped_x = ValueTarget::from_slice(&[
            self.sub(u32_max, x.elements[0]),
            self.sub(u32_max, x.elements[1]),
            zero,
            zero,
        ]);

        self.i64_wrapping_add(one, flipped_x)
    }

    fn i64_abs(&mut self, x: ValueTarget) -> (ValueTarget, BoolTarget) {
        let x_is_negative = self.i64_is_negative(x);
        let minus_x = self.i64_inv(x);
        (self.select_value(x_is_negative, minus_x, x), x_is_negative)
    }

    fn hash_values(&mut self, x: ValueTarget, y: ValueTarget) -> ValueTarget {
        ValueTarget::from_slice(
            &self
                .hash_n_to_hash_no_pad::<PoseidonHash>([x.elements, y.elements].concat())
                .elements,
        )
    }

    fn random_access_long(&mut self, i: &IndexTarget, array: &[Target]) -> Target {
        const CHUNK_LEN: usize = 64; // Max size of a single gate native random access
        assert!(array.len() <= i.max_array_len);
        // Limit to 4 chunks (combination of 4 random_access of CHUNK_LEN elements) to avoid
        // abusing this method.
        assert!(array.len() <= 4 * CHUNK_LEN);

        // We do several random accesses over chunks of CHUNK_LEN using the lowest bits of the
        // index.  Then we combine them using the highest bits of the index.
        let mut chunk_res = Vec::new();
        let num_chunks = array.len().div_ceil(CHUNK_LEN);
        for chunk in array.chunks(CHUNK_LEN) {
            let mut index_chunk = i.low;
            // I we have several chunks and the last one is smaller (it's index needs less than 6
            // bits), make it zero except when it's used so that the range check over the index
            // passes.
            if chunk.len() <= CHUNK_LEN / 2 && num_chunks > 1 {
                let last_chunk_index_high = self.constant(F::from_canonical_usize(num_chunks - 1));
                let selector = self.is_equal(i.high, last_chunk_index_high);
                index_chunk = self.mul(index_chunk, selector.target);
            }
            let res = self.random_access(index_chunk, chunk.to_vec());
            chunk_res.push(res);
        }

        self.random_access(i.high, chunk_res)
    }

    // TODO: Implement a version of vec_ref for types `T` which are big and support hashing.
    // The idea would be the following: Take the array `ts` and hash each element.  Then do the
    // random access on the hash result.  Finally "unhash" to recover the resolved element.
    // We don't want to hash each element from the array each time, so we should cache the hashed
    // result.  For that we can create a wrapper over `T: Flattenable` that caches the hash, and
    // then do `ts: &[HashCache<T>]`.
    fn vec_ref<T: Flattenable>(&mut self, params: &Params, ts: &[T], i: &IndexTarget) -> T {
        let matrix_row_ref = |builder: &mut CircuitBuilder, m: &[Vec<Target>], i| {
            let num_rows = m.len();
            let num_columns = m
                .first()
                .map(|row| {
                    let row_len = row.len();
                    assert!(m.iter().all(|row| row.len() == row_len));
                    row_len
                })
                .unwrap_or(0);
            (0..num_columns)
                .map(|j| {
                    builder
                        .random_access_long(i, &(0..num_rows).map(|i| m[i][j]).collect::<Vec<_>>())
                })
                .collect::<Vec<_>>()
        };

        let flattened_ts = ts.iter().map(|t| t.flatten()).collect::<Vec<_>>();
        T::from_flattened(params, &matrix_row_ref(self, &flattened_ts, i))
    }

    fn vec_ref_small<T: Flattenable>(&mut self, params: &Params, ts: &[T], i: Target) -> T {
        let zero = self.zero();
        self.vec_ref(
            params,
            ts,
            &IndexTarget {
                max_array_len: 64,
                low: i,
                high: zero,
            },
        )
    }

    fn select_flattenable<T: Flattenable>(
        &mut self,
        params: &Params,
        b: BoolTarget,
        x: &T,
        y: &T,
    ) -> T {
        let flattened_x = x.flatten();
        let flattened_y = y.flatten();

        T::from_flattened(
            params,
            &iter::zip(flattened_x, flattened_y)
                .map(|(x, y)| self.select(b, x, y))
                .collect::<Vec<_>>(),
        )
    }

    fn connect_flattenable<T: Flattenable>(&mut self, xs: &T, ys: &T) {
        self.connect_slice(&xs.flatten(), &ys.flatten())
    }

    fn is_equal_flattenable<T: Flattenable>(&mut self, xs: &T, ys: &T) -> BoolTarget {
        self.is_equal_slice(&xs.flatten(), &ys.flatten())
    }

    fn all(&mut self, xs: impl IntoIterator<Item = BoolTarget>) -> BoolTarget {
        xs.into_iter()
            .reduce(|a, b| self.and(a, b))
            .unwrap_or(self._true())
    }

    fn any(&mut self, xs: impl IntoIterator<Item = BoolTarget>) -> BoolTarget {
        xs.into_iter()
            .reduce(|a, b| self.or(a, b))
            .unwrap_or(self._false())
    }

    fn lt_mask(&mut self, len: usize, n: Target) -> Vec<BoolTarget> {
        let zero = self.zero();
        let mask: Vec<_> = (0..len)
            .map(|_| self.add_virtual_bool_target_safe())
            .collect();
        self.add_simple_generator(LtMaskGenerator {
            n,
            mask: mask.iter().map(|bt| bt.target).collect(),
        });
        // We have `n` ones in the mask
        let mask_sum = mask
            .iter()
            .map(|b| b.target)
            .reduce(|acc, x| self.add(acc, x))
            .unwrap_or(zero);
        self.connect(n, mask_sum);

        // The elements in the mask can only transition from 1 to 0 or 0 to 0.
        for i in 0..len - 1 {
            let diff = self.sub(mask[i].target, mask[i + 1].target);
            self.assert_bool(BoolTarget::new_unsafe(diff));
        }

        mask
    }
}

#[derive(Debug, Default, Clone)]
pub struct LtMaskGenerator {
    pub(crate) n: Target,
    pub(crate) mask: Vec<Target>,
}

impl SimpleGenerator<F, D> for LtMaskGenerator {
    fn id(&self) -> String {
        "LtMaskGenerator".to_string()
    }

    fn dependencies(&self) -> Vec<Target> {
        vec![self.n]
    }

    fn run_once(
        &self,
        witness: &PartitionWitness<F>,
        out_buffer: &mut GeneratedValues<F>,
    ) -> anyhow::Result<()> {
        let n = witness.get_target(self.n).to_canonical_u64();

        for (i, mask_i) in self.mask.iter().enumerate() {
            let v = if (i as u64) < n { F::ONE } else { F::ZERO };
            out_buffer.set_target(*mask_i, v)?;
        }
        Ok(())
    }

    fn serialize(&self, dst: &mut Vec<u8>, _common_data: &CommonCircuitData) -> IoResult<()> {
        dst.write_target(self.n)?;
        dst.write_target_vec(&self.mask)
    }

    fn deserialize(src: &mut Buffer, _common_data: &CommonCircuitData) -> IoResult<Self> {
        let n = src.read_target()?;
        let mask = src.read_target_vec()?;
        Ok(Self { n, mask })
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use anyhow::anyhow;
    use itertools::Itertools;
    use plonky2::plonk::{
        circuit_builder::CircuitBuilder, circuit_data::CircuitConfig,
        config::PoseidonGoldilocksConfig,
    };

    use super::*;
    use crate::{
        backends::plonky2::basetypes::C, examples::custom::eth_dos_batch, frontend,
        frontend::CustomPredicateBatchBuilder, middleware::CustomPredicateBatch,
    };

    pub(crate) const I64_TEST_PAIRS: [(i64, i64); 36] = [
        // Nonnegative numbers
        (0, 0),
        (0, 50),
        (35, 50),
        (483748374, 221672),
        (2, 1 << 31),
        (2, 1 << 62),
        (0, 1 << 62),
        (1 << 31, 1 << 62),
        (1 << 32, 1 << 32),
        (1 << 62, 1 << 62),
        (0, i64::MAX),
        (i64::MAX, 1 << 62),
        (i64::MAX, i64::MAX),
        // Negative numbers
        (-35, -50),
        (-483748374, -221672),
        (-(1 << 33), -1),
        (-(1 << 32), -(1 << 32)),
        (-(1 << 33), -(1 << 29)),
        (-(1 << 33), -(1 << 30)),
        (-(1 << 33), -(1 << 62)),
        (-(1 << 62), -(1 << 62)),
        (i64::MIN, -1),
        (i64::MIN, -(1 << 31)),
        (i64::MIN, -(1 << 62)),
        (i64::MIN, i64::MIN),
        // Mix of numbers
        (-35, 50),
        (-483748374, 221672),
        (-(1 << 32), (1 << 32)),
        (-(1 << 33), (1 << 30) - 1),
        (-(1 << 33), (1 << 30)),
        (-(1 << 62), (1 << 62)),
        (i64::MIN, 0),
        (i64::MIN, 1),
        (i64::MIN, 1 << 31),
        (i64::MIN, 1 << 62),
        (i64::MIN, i64::MAX),
    ];

    #[test]
    fn custom_predicate_target() -> frontend::Result<()> {
        let params = Params::default();
        let config = CircuitConfig::standard_recursion_config();

        let custom_predicate_batch = eth_dos_batch(&params)?;

        for (i, cp) in custom_predicate_batch.predicates().iter().enumerate() {
            let mut builder = CircuitBuilder::<F, D>::new(config.clone());
            let flattened = cp.to_fields(&params);
            let flatteend_target = flattened.iter().map(|v| builder.constant(*v)).collect_vec();
            let cp_target = CustomPredicateTarget::from_flattened(&params, &flatteend_target);
            // Round trip of from_flattened to flattened
            let flatteend_target_rt = cp_target.flatten();
            // TODO: Instead of connect, assign witness to result
            builder.connect_slice(&flatteend_target, &flatteend_target_rt);

            let pw = PartialWitness::<F>::new();

            // generate & verify proof
            let data = builder.build::<C>();
            let proof = data.prove(pw).unwrap_or_else(|_| panic!("predicate {}", i));
            data.verify(proof.clone()).unwrap();
        }

        Ok(())
    }

    fn helper_custom_predicate_batch_target_id(
        params: &Params,
        custom_predicate_batch: &CustomPredicateBatch,
    ) -> Result<()> {
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let custom_predicate_batch_target = builder.add_virtual_custom_predicate_batch(params);

        // Calculate the id in constraints and compare it against the id calculated natively
        let id_target = custom_predicate_batch_target.id(&mut builder);

        let mut pw = PartialWitness::<F>::new();
        custom_predicate_batch_target.set_targets(&mut pw, params, custom_predicate_batch)?;
        let id = custom_predicate_batch.id();
        pw.set_target_arr(&id_target.elements, &id.0)?;

        // generate & verify proof
        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();
        data.verify(proof.clone()).unwrap();

        Ok(())
    }

    #[test]
    fn test_custom_predicate_batch_target_id() -> frontend::Result<()> {
        let params = Params {
            max_statement_args: 6,
            max_custom_predicate_wildcards: 12,
            ..Default::default()
        };

        // Empty case
        let mut cpb_builder = CustomPredicateBatchBuilder::new(params.clone(), "empty".into());
        _ = cpb_builder.predicate_and("empty", &[], &[], &[])?;
        let custom_predicate_batch = cpb_builder.finish();
        helper_custom_predicate_batch_target_id(&params, &custom_predicate_batch).unwrap();

        // Some cases from the examples
        let custom_predicate_batch = eth_dos_batch(&params)?;
        helper_custom_predicate_batch_target_id(&params, &custom_predicate_batch).unwrap();

        let custom_predicate_batch =
            CustomPredicateBatch::new(&params, "empty".to_string(), vec![CustomPredicate::empty()]);
        helper_custom_predicate_batch_target_id(&params, &custom_predicate_batch).unwrap();

        Ok(())
    }

    #[test]
    fn test_i64_addition() -> Result<(), anyhow::Error> {
        // Circuit declaration
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let x_target = ValueTarget::from_slice(&builder.add_virtual_target_arr::<VALUE_SIZE>());
        let y_target = ValueTarget::from_slice(&builder.add_virtual_target_arr::<VALUE_SIZE>());

        let sum_target = builder.i64_add(x_target, y_target);

        let data = builder.build::<PoseidonGoldilocksConfig>();
        let params = Params::default();

        I64_TEST_PAIRS.into_iter().try_for_each(|(x, y)| {
            let mut pw = PartialWitness::<F>::new();
            let (sum, overflow) = x.overflowing_add(y);
            pw.set_target_arr(&x_target.elements, &RawValue::from(x).to_fields(&params))?;
            pw.set_target_arr(&y_target.elements, &RawValue::from(y).to_fields(&params))?;
            pw.set_target_arr(
                &sum_target.elements,
                &RawValue::from(sum).to_fields(&params),
            )?;

            let proof = data.prove(pw);

            match (overflow, proof) {
                (false, Ok(pf)) => data.verify(pf),
                (false, Err(e)) => Err(anyhow!("Proof failure despite no overflow: {}", e)),
                (true, Ok(_)) => Err(anyhow!("Proof success despite overflow.")),
                (true, Err(_)) => Ok(()),
            }
        })
    }

    #[test]
    fn test_i64_multiplication() -> Result<(), anyhow::Error> {
        // Circuit declaration
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let x_target = ValueTarget::from_slice(&builder.add_virtual_target_arr::<VALUE_SIZE>());
        let y_target = ValueTarget::from_slice(&builder.add_virtual_target_arr::<VALUE_SIZE>());

        let prod_target = builder.i64_mul(x_target, y_target);

        let data = builder.build::<PoseidonGoldilocksConfig>();
        let params = Params::default();

        I64_TEST_PAIRS.into_iter().try_for_each(|(x, y)| {
            println!("{}, {}", x, y);
            let mut pw = PartialWitness::<F>::new();
            let (prod, overflow) = x.overflowing_mul(y);
            pw.set_target_arr(&x_target.elements, &RawValue::from(x).to_fields(&params))?;
            pw.set_target_arr(&y_target.elements, &RawValue::from(y).to_fields(&params))?;
            pw.set_target_arr(
                &prod_target.elements,
                &RawValue::from(prod).to_fields(&params),
            )?;

            let proof = data.prove(pw);

            match (overflow, proof) {
                (false, Ok(pf)) => data.verify(pf),
                (false, Err(e)) => Err(anyhow!("Proof failure despite no overflow: {}", e)),
                (true, Ok(_)) => Err(anyhow!("Proof success despite overflow.")),
                (true, Err(_)) => Ok(()),
            }
        })
    }

    #[test]
    fn test_random_access_long() -> Result<(), anyhow::Error> {
        let lens: [usize; _] = [10, 60, 64, 96, 126, 159, 190, 256];

        for len in &lens {
            let config = CircuitConfig::standard_recursion_config();
            let mut builder = CircuitBuilder::<F, D>::new(config);

            let array = builder.add_virtual_targets(*len);
            let index_target = IndexTarget::new_virtual(*len, &mut builder);
            let res = builder.random_access_long(&index_target, &array);

            let data = builder.build::<PoseidonGoldilocksConfig>();

            for i in 0..3 {
                let index = (len - 1) * i / 2;
                println!("len={}, index={}", len, index);
                let mut pw = PartialWitness::<F>::new();
                for (j, elem) in array.iter().enumerate() {
                    pw.set_target(*elem, F::from_canonical_usize(j * 11))?;
                }
                index_target.set_targets(&mut pw, index)?;
                pw.set_target(res, F::from_canonical_usize(index * 11))?; // Expected

                let proof = data.prove(pw)?;
                data.verify(proof)?;
            }
        }

        Ok(())
    }
}
