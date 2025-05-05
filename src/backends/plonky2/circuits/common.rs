//! Common functionality to build Pod circuits with plonky2

use std::{array, iter};

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
        target::{BoolTarget, Target},
        witness::{PartialWitness, WitnessWrite},
    },
    plonk::circuit_builder::CircuitBuilder,
};

use crate::{
    backends::plonky2::{
        basetypes::D,
        error::Result,
        mainpod::{Operation, OperationArg, Statement},
        primitives::merkletree::MerkleClaimAndProofTarget,
    },
    middleware::{
        KeyOrWildcard, NativeOperation, NativePredicate, Params, Predicate, RawValue, StatementArg,
        ToFields, EMPTY_VALUE, F, HASH_SIZE, OPERATION_ARG_F_LEN, OPERATION_AUX_F_LEN,
        STATEMENT_ARG_F_LEN, VALUE_SIZE,
    },
};

pub const CODE_SIZE: usize = HASH_SIZE + 2;

#[derive(Copy, Clone)]
pub struct ValueTarget {
    pub elements: [Target; VALUE_SIZE],
}

impl ValueTarget {
    pub fn zero(builder: &mut CircuitBuilder<F, D>) -> Self {
        Self {
            elements: [builder.zero(); VALUE_SIZE],
        }
    }

    pub fn one(builder: &mut CircuitBuilder<F, D>) -> Self {
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
}

#[derive(Clone)]
pub struct StatementArgTarget {
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

    fn new(first: ValueTarget, second: ValueTarget) -> Self {
        let elements: Vec<_> = first.elements.into_iter().chain(second.elements).collect();
        StatementArgTarget {
            elements: elements.try_into().expect("size STATEMENT_ARG_F_LEN"),
        }
    }

    pub fn none(builder: &mut CircuitBuilder<F, D>) -> Self {
        let empty = builder.constant_value(EMPTY_VALUE);
        Self::new(empty, empty)
    }

    pub fn literal(builder: &mut CircuitBuilder<F, D>, value: &ValueTarget) -> Self {
        let empty = builder.constant_value(EMPTY_VALUE);
        Self::new(*value, empty)
    }

    pub fn anchored_key(
        _builder: &mut CircuitBuilder<F, D>,
        pod_id: &ValueTarget,
        key: &ValueTarget,
    ) -> Self {
        Self::new(*pod_id, *key)
    }
}

#[derive(Clone)]
pub struct StatementTarget {
    pub predicate: PredicateTarget,
    pub args: Vec<StatementArgTarget>,
}

trait Build<T> {
    fn build(self, builder: &mut CircuitBuilder<F, D>, params: &Params) -> T;
}

impl Build<NativePredicateTarget> for &NativePredicate {
    fn build(self, builder: &mut CircuitBuilder<F, D>, params: &Params) -> NativePredicateTarget {
        NativePredicateTarget::constant(builder, params, *self)
    }
}

impl<T> Build<T> for T {
    fn build(self, builder: &mut CircuitBuilder<F, D>, params: &Params) -> T {
        self
    }
}

impl StatementTarget {
    pub fn new_native(
        builder: &mut CircuitBuilder<F, D>,
        params: &Params,
        native_predicate: impl Build<NativePredicateTarget>,
        args: &[StatementArgTarget],
    ) -> Self {
        // if native_predicate is const then NativePredicate -> NativePredicateTarget
        // else just use as is
        let native_predicate = native_predicate.build(builder, params);
        Self {
            predicate: PredicateTarget::new_native(builder, &native_predicate),
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
        builder: &mut CircuitBuilder<F, D>,
        params: &Params,
        t: NativePredicate,
    ) -> BoolTarget {
        let expected_t = NativePredicateTarget::constant(builder, params, t);
        let expected_predicate = PredicateTarget::new_native(builder, &expected_t);
        builder.is_equal_flattenable(&self.predicate, &expected_predicate)
    }
}

// TODO: Implement Operation::to_field to determine the size of each element
#[derive(Clone)]
pub struct OperationTarget {
    pub op_type: [Target; Params::operation_type_size()],
    pub args: Vec<[Target; OPERATION_ARG_F_LEN]>,
    pub aux: [Target; OPERATION_AUX_F_LEN],
}

impl OperationTarget {
    pub fn set_targets(
        &self,
        pw: &mut PartialWitness<F>,
        params: &Params,
        op: &Operation,
    ) -> Result<()> {
        pw.set_target_arr(&self.op_type, &op.op_type().to_fields(params))?;
        for (i, arg) in op
            .args()
            .iter()
            .chain(iter::repeat(&OperationArg::None))
            .take(params.max_operation_args)
            .enumerate()
        {
            pw.set_target_arr(&self.args[i], &arg.to_fields(params))?;
        }
        pw.set_target_arr(&self.aux, &op.aux().to_fields(params))?;
        Ok(())
    }

    pub fn has_native_type(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        t: NativeOperation,
    ) -> BoolTarget {
        let one = builder.one();
        let op_is_native = builder.is_equal(self.op_type[0], one);
        let op_code = builder.constant(F::from_canonical_u64(t as u64));
        let op_code_matches = builder.is_equal(self.op_type[1], op_code);
        builder.and(op_is_native, op_code_matches)
    }
}

#[derive(Clone)]
pub struct NativePredicateTarget(Target);

impl NativePredicateTarget {
    pub fn constant(
        builder: &mut CircuitBuilder<F, D>,
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

#[derive(Clone)]
pub struct PredicateTarget {
    elements: [Target; Params::predicate_size()],
}

impl PredicateTarget {
    pub fn new_native(
        builder: &mut CircuitBuilder<F, D>,
        native_predicate: &NativePredicateTarget,
    ) -> Self {
        let prefix = builder.constant(F::from_canonical_usize(1));
        let id = native_predicate.0;
        let zero = builder.zero();
        Self {
            elements: [prefix, id, zero, zero, zero, zero],
        }
    }

    pub fn new_batch_self(builder: &mut CircuitBuilder<F, D>, index: Target) -> Self {
        let prefix = builder.constant(F::from_canonical_usize(2));
        let zero = builder.zero();
        Self {
            elements: [prefix, index, zero, zero, zero, zero],
        }
    }

    pub fn new_custom(
        builder: &mut CircuitBuilder<F, D>,
        batch_id: HashOutTarget,
        index: Target,
    ) -> Self {
        let prefix = builder.constant(F::from_canonical_usize(3));
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

#[derive(Clone)]
pub struct KeyOrWildcardTarget {
    pub elements: [Target; VALUE_SIZE],
}

impl KeyOrWildcardTarget {
    fn from_slice(v: &[Target]) -> Self {
        Self {
            elements: v.try_into().expect("len is VALUE_SIZE"),
        }
    }
}

#[derive(Clone)]
pub struct StatementTmplArgTarget {
    pub elements: [Target; Params::statement_tmpl_arg_size()],
}

impl StatementTmplArgTarget {
    pub fn as_none(&self, builder: &mut CircuitBuilder<F, D>) -> BoolTarget {
        let none_prefix = builder.constant(F::from_canonical_usize(0));
        let case_ok = builder.is_equal(self.elements[0], none_prefix);
        case_ok
    }
    pub fn as_literal(&self, builder: &mut CircuitBuilder<F, D>) -> (BoolTarget, ValueTarget) {
        let none_prefix = builder.constant(F::from_canonical_usize(1));
        let case_ok = builder.is_equal(self.elements[0], none_prefix);
        let value = ValueTarget::from_slice(&self.elements[1..5]);
        (case_ok, value)
    }
    pub fn as_key(
        &self,
        builder: &mut CircuitBuilder<F, D>,
    ) -> (BoolTarget, Target, KeyOrWildcardTarget) {
        let none_prefix = builder.constant(F::from_canonical_usize(2));
        let case_ok = builder.is_equal(self.elements[0], none_prefix);
        let id_wildcard_index = self.elements[1];
        let value_key_or_wildcard = KeyOrWildcardTarget::from_slice(&self.elements[5..9]);
        (case_ok, id_wildcard_index, value_key_or_wildcard)
    }
    pub fn as_wildcard_literal(&self, builder: &mut CircuitBuilder<F, D>) -> (BoolTarget, Target) {
        let none_prefix = builder.constant(F::from_canonical_usize(3));
        let case_ok = builder.is_equal(self.elements[0], none_prefix);
        let wildcard_index = self.elements[1];
        (case_ok, wildcard_index)
    }
}

#[derive(Clone)]
pub struct StatementTmplTarget {
    pub pred: PredicateTarget,
    pub args: Vec<StatementTmplArgTarget>,
}

#[derive(Clone)]
pub struct CustomPredicateTarget {
    pub conjunction: BoolTarget,
    // len = params.max_custom_predicate_arity
    pub statements: Vec<StatementTmplTarget>,
    pub args_len: Target,
}

#[derive(Clone)]
pub struct CustomPredicateBatchTarget {
    pub predicates: Vec<CustomPredicateTarget>,
}

impl CustomPredicateBatchTarget {
    pub fn id(&self, builder: &mut CircuitBuilder<F, D>) -> HashOutTarget {
        let flattened = self.predicates.iter().flat_map(|cp| cp.flatten()).collect();
        builder.hash_n_to_hash_no_pad::<PoseidonHash>(flattened)
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
        let args = (0..params.max_custom_predicate_arity)
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

pub trait CircuitBuilderPod<F: RichField + Extendable<D>, const D: usize> {
    fn connect_values(&mut self, x: ValueTarget, y: ValueTarget);
    fn connect_slice(&mut self, xs: &[Target], ys: &[Target]);
    fn add_virtual_value(&mut self) -> ValueTarget;
    fn add_virtual_statement(&mut self, params: &Params) -> StatementTarget;
    fn add_virtual_predicate(&mut self) -> PredicateTarget;
    fn add_virtual_operation(&mut self, params: &Params) -> OperationTarget;
    fn select_value(&mut self, b: BoolTarget, x: ValueTarget, y: ValueTarget) -> ValueTarget;
    fn select_bool(&mut self, b: BoolTarget, x: BoolTarget, y: BoolTarget) -> BoolTarget;
    fn constant_value(&mut self, v: RawValue) -> ValueTarget;
    fn is_equal_slice(&mut self, xs: &[Target], ys: &[Target]) -> BoolTarget;

    // Convenience methods for checking values.
    /// Checks whether `xs` is right-padded with 0s so as to represent a `Value`.
    fn statement_arg_is_value(&mut self, arg: &StatementArgTarget) -> BoolTarget;
    /// Checks whether `x < y` if `b` is true. This involves checking
    /// that `x` and `y` each consist of two `u32` limbs.
    fn assert_less_if(&mut self, b: BoolTarget, x: ValueTarget, y: ValueTarget);

    // Convenience methods for accessing and connecting elements of
    // (vectors of) flattenables.
    fn vec_ref<T: Flattenable>(&mut self, params: &Params, ts: &[T], i: Target) -> T;
    fn select_flattenable<T: Flattenable>(
        &mut self,
        params: &Params,
        b: BoolTarget,
        x: &T,
        y: &T,
    ) -> T;
    fn connect_flattenable<T: Flattenable>(&mut self, xs: &T, ys: &T);
    fn is_equal_flattenable<T: Flattenable>(&mut self, xs: &T, ys: &T) -> BoolTarget;

    // Convenience methods for Boolean into-iters.
    fn all(&mut self, xs: impl IntoIterator<Item = BoolTarget>) -> BoolTarget;
    fn any(&mut self, xs: impl IntoIterator<Item = BoolTarget>) -> BoolTarget;
}

impl CircuitBuilderPod<F, D> for CircuitBuilder<F, D> {
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
                .map(|_| StatementArgTarget {
                    elements: self.add_virtual_target_arr(),
                })
                .collect(),
        }
    }

    fn add_virtual_predicate(&mut self) -> PredicateTarget {
        PredicateTarget {
            elements: self.add_virtual_target_arr(),
        }
    }

    fn add_virtual_operation(&mut self, params: &Params) -> OperationTarget {
        OperationTarget {
            op_type: self.add_virtual_target_arr(),
            args: (0..params.max_operation_args)
                .map(|_| self.add_virtual_target_arr())
                .collect(),
            aux: self.add_virtual_target_arr(),
        }
    }

    fn select_value(&mut self, b: BoolTarget, x: ValueTarget, y: ValueTarget) -> ValueTarget {
        ValueTarget {
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

    fn assert_less_if(&mut self, b: BoolTarget, x: ValueTarget, y: ValueTarget) {
        const NUM_BITS: usize = 32;

        // Lt assertion with 32-bit range check.
        let assert_limb_lt = |builder: &mut Self, x, y| {
            // Check that targets fit within `NUM_BITS` bits.
            builder.range_check(x, NUM_BITS);
            builder.range_check(y, NUM_BITS);
            // Check that `y-1-x` fits within `NUM_BITS` bits.
            let one = builder.one();
            let y_minus_one = builder.sub(y, one);
            let expr = builder.sub(y_minus_one, x);
            builder.range_check(expr, NUM_BITS);
        };

        // If b is false, replace `x` and `y` with dummy values.
        let zero = ValueTarget::zero(self);
        let one = ValueTarget::one(self);
        let x = self.select_value(b, x, zero);
        let y = self.select_value(b, y, one);

        // `x` and `y` should only have two limbs each.
        x.elements
            .into_iter()
            .skip(2)
            .for_each(|l| self.assert_zero(l));
        y.elements
            .into_iter()
            .skip(2)
            .for_each(|l| self.assert_zero(l));

        let big_limbs_eq = self.is_equal(x.elements[1], y.elements[1]);
        let lhs = self.select(big_limbs_eq, x.elements[0], x.elements[1]);
        let rhs = self.select(big_limbs_eq, y.elements[0], y.elements[1]);
        assert_limb_lt(self, lhs, rhs);
    }

    fn vec_ref<T: Flattenable>(&mut self, params: &Params, ts: &[T], i: Target) -> T {
        // TODO: Revisit this when we need more than 64 statements.
        let vector_ref = |builder: &mut CircuitBuilder<F, D>, v: &[Target], i| {
            assert!(v.len() <= 64);
            builder.random_access(i, v.to_vec())
        };
        let matrix_row_ref = |builder: &mut CircuitBuilder<F, D>, m: &[Vec<Target>], i| {
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
                    vector_ref(
                        builder,
                        &(0..num_rows).map(|i| m[i][j]).collect::<Vec<_>>(),
                        i,
                    )
                })
                .collect::<Vec<_>>()
        };

        let flattened_ts = ts.iter().map(|t| t.flatten()).collect::<Vec<_>>();
        T::from_flattened(params, &matrix_row_ref(self, &flattened_ts, i))
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
}

#[cfg(test)]
mod tests {
    use itertools::Itertools;
    use plonky2::plonk::{circuit_builder::CircuitBuilder, circuit_data::CircuitConfig};

    use super::*;
    use crate::{backends::plonky2::basetypes::C, examples::custom::eth_friend_batch, frontend};

    #[test]
    fn custom_predicate_batch() -> frontend::Result<()> {
        let params = Params::default();
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let custom_predicate_batch = eth_friend_batch(&params)?;
        let predicate_targets = custom_predicate_batch
            .predicates
            .iter()
            .map(|cp| {
                let flattened = cp.to_fields(&params);
                let flatteend_target = flattened.iter().map(|v| builder.constant(*v)).collect_vec();
                CustomPredicateTarget::from_flattened(&params, &flatteend_target)
            })
            .collect();

        let custom_predicate_batch_target = CustomPredicateBatchTarget {
            predicates: predicate_targets,
        };

        let id_target = custom_predicate_batch_target.id(&mut builder);
        let id = custom_predicate_batch.id(&params);

        let id_expected_target = HashOutTarget {
            elements: id
                .to_fields(&params)
                .iter()
                .map(|v| builder.constant(*v))
                .collect_vec()
                .try_into()
                .unwrap(),
        };
        builder.connect_array(id_target.elements, id_expected_target.elements);

        let pw = PartialWitness::<F>::new();

        // generate & verify proof
        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();
        data.verify(proof.clone()).unwrap();

        Ok(())
    }
}
