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
        NativeOperation, NativePredicate, Params, Predicate, RawValue, StatementArg, ToFields,
        EMPTY_VALUE, F, HASH_SIZE, OPERATION_ARG_F_LEN, OPERATION_AUX_F_LEN, STATEMENT_ARG_F_LEN,
        VALUE_SIZE,
    },
};

pub const CODE_SIZE: usize = HASH_SIZE + 2;
const NUM_BITS: usize = 32;

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

    /// StatementArgTarget to ValueTarget coercion. Make sure to check
    /// that the arg is a value using the `statement_arg_is_value` method
    /// first!
    pub fn as_value(&self) -> ValueTarget {
        ValueTarget::from_slice(&self.elements[..VALUE_SIZE])
    }
}

#[derive(Clone)]
pub struct StatementTarget {
    pub predicate: [Target; Params::predicate_size()],
    pub args: Vec<StatementArgTarget>,
}

impl StatementTarget {
    pub fn new_native(
        builder: &mut CircuitBuilder<F, D>,
        params: &Params,
        predicate: NativePredicate,
        args: &[StatementArgTarget],
    ) -> Self {
        let predicate_vec = builder.constants(&Predicate::Native(predicate).to_fields(params));
        Self {
            predicate: array::from_fn(|i| predicate_vec[i]),
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
        pw.set_target_arr(&self.predicate, &st.predicate().to_fields(params))?;
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
        let st_code = builder.constants(&Predicate::Native(t).to_fields(params));
        builder.is_equal_slice(&self.predicate, &st_code)
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

/// Trait for target structs that may be converted to and from vectors
/// of targets.
pub trait Flattenable {
    fn flatten(&self) -> Vec<Target>;
    fn from_flattened(vs: &[Target]) -> Self;
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

    fn from_flattened(vs: &[Target]) -> Self {
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

impl Flattenable for StatementTarget {
    fn flatten(&self) -> Vec<Target> {
        self.predicate
            .iter()
            .chain(self.args.iter().flat_map(|a| &a.elements))
            .cloned()
            .collect()
    }

    fn from_flattened(v: &[Target]) -> Self {
        let num_args = (v.len() - Params::predicate_size()) / STATEMENT_ARG_F_LEN;
        assert_eq!(
            v.len(),
            Params::predicate_size() + num_args * STATEMENT_ARG_F_LEN
        );
        let predicate: [Target; Params::predicate_size()] = array::from_fn(|i| v[i]);
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

pub trait CircuitBuilderPod<F: RichField + Extendable<D>, const D: usize> {
    fn connect_values(&mut self, x: ValueTarget, y: ValueTarget);
    fn connect_slice(&mut self, xs: &[Target], ys: &[Target]);
    fn add_virtual_value(&mut self) -> ValueTarget;
    fn add_virtual_statement(&mut self, params: &Params) -> StatementTarget;
    fn add_virtual_operation(&mut self, params: &Params) -> OperationTarget;
    fn select_value(&mut self, b: BoolTarget, x: ValueTarget, y: ValueTarget) -> ValueTarget;
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

    /// Creates value target that is a hash of two given values.
    fn hash_values(&mut self, x: ValueTarget, y: ValueTarget) -> ValueTarget;

    // Convenience methods for accessing and connecting elements of
    // (vectors of) flattenables.
    fn vec_ref<T: Flattenable>(&mut self, ts: &[T], i: Target) -> T;
    fn select_flattenable<T: Flattenable>(&mut self, b: BoolTarget, x: &T, y: &T) -> T;
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
        StatementTarget {
            predicate: self.add_virtual_target_arr(),
            args: (0..params.max_statement_args)
                .map(|_| StatementArgTarget {
                    elements: self.add_virtual_target_arr(),
                })
                .collect(),
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

    fn hash_values(&mut self, x: ValueTarget, y: ValueTarget) -> ValueTarget {
        ValueTarget::from_slice(
            &self
                .hash_n_to_hash_no_pad::<PoseidonHash>([x.elements, y.elements].concat())
                .elements,
        )
    }

    fn vec_ref<T: Flattenable>(&mut self, ts: &[T], i: Target) -> T {
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
        T::from_flattened(&matrix_row_ref(self, &flattened_ts, i))
    }

    fn select_flattenable<T: Flattenable>(&mut self, b: BoolTarget, x: &T, y: &T) -> T {
        let flattened_x = x.flatten();
        let flattened_y = y.flatten();

        T::from_flattened(
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
