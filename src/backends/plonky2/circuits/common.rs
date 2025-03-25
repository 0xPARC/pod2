//! Common functionality to build Pod circuits with plonky2

use crate::backends::plonky2::basetypes::D;
use crate::backends::plonky2::mock::mainpod::Statement;
use crate::backends::plonky2::mock::mainpod::{Operation, OperationArg};
use crate::middleware::{
    NativeOperation, NativePredicate, Params, Params, Predicate, StatementArg, StatementArg,
    ToFields, ToFields, Value, Value, EMPTY_VALUE, F, F, HASH_SIZE, HASH_SIZE, OPERATION_ARG_F_LEN,
    OPERATION_ARG_F_LEN, STATEMENT_ARG_F_LEN, STATEMENT_ARG_F_LEN, VALUE_SIZE, VALUE_SIZE,
};
use anyhow::Result;
use plonky2::field::extension::Extendable;
use plonky2::field::types::{Field, PrimeField64};
use plonky2::hash::hash_types::RichField;
use plonky2::iop::target::{BoolTarget, Target};
use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use std::{array, iter};

pub const CODE_SIZE: usize = HASH_SIZE + 2;

#[derive(Copy, Clone)]
pub struct ValueTarget {
    pub elements: [Target; VALUE_SIZE],
}

impl ValueTarget {
    pub fn zero<F: RichField + Extendable<D>, const D: usize>(
        builder: &mut CircuitBuilder<F, D>,
    ) -> Self {
        Self {
            elements: [builder.zero(); VALUE_SIZE],
        }
    }

    pub fn one<F: RichField + Extendable<D>, const D: usize>(
        builder: &mut CircuitBuilder<F, D>,
    ) -> Self {
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
        pw.set_target_arr(&self.elements, &arg.to_fields(params))
    }

    fn new(first: ValueTarget, second: ValueTarget) -> Self {
        let elements: Vec<_> = first
            .elements
            .into_iter()
            .chain(second.elements.into_iter())
            .collect();
        StatementArgTarget {
            elements: elements.try_into().expect("size STATEMENT_ARG_F_LEN"),
        }
    }

    pub fn none(builder: &mut CircuitBuilder<F, D>) -> Self {
        let empty = builder.constant_value(EMPTY_VALUE);
        Self::new(empty.clone(), empty)
    }

    pub fn literal(builder: &mut CircuitBuilder<F, D>, value: &ValueTarget) -> Self {
        let empty = builder.constant_value(EMPTY_VALUE);
        Self::new(value.clone(), empty)
    }

    pub fn anchored_key(
        _builder: &mut CircuitBuilder<F, D>,
        pod_id: &ValueTarget,
        key: &ValueTarget,
    ) -> Self {
        Self::new(pod_id.clone(), key.clone())
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
        args: &[[Target; STATEMENT_ARG_F_LEN]],
    ) -> Self {
        let predicate_vec = builder.constants(&Predicate::Native(predicate).to_fields(params));
        Self {
            predicate: array::from_fn(|i| predicate_vec[i]),
            args: args
                .iter()
                .map(|arg| *arg)
                .chain(
                    iter::repeat([builder.zero(); STATEMENT_ARG_F_LEN])
                        .take(params.max_statement_args - args.len()),
                )
                .collect(),
        }
    }
    pub fn to_flattened(&self) -> Vec<Target> {
        self.predicate
            .iter()
            .chain(self.args.iter().flat_map(|arg| &arg.elements))
            .cloned()
            .collect()
    }

    pub fn from_flattened(v: Vec<Target>) -> Self {
        let num_args = (v.len() - Params::predicate_size()) / STATEMENT_ARG_F_LEN;
        assert_eq!(
            v.len(),
            Params::predicate_size() + num_args * STATEMENT_ARG_F_LEN
        );
        let predicate: [Target; Params::predicate_size()] = array::from_fn(|i| v[i]);
        let args = (0..num_args)
            .map(|i| array::from_fn(|j| v[Params::predicate_size() + i * STATEMENT_ARG_F_LEN + j]))
            .collect();

        Self { predicate, args }
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
        Ok(())
    }

    pub fn has_native_type(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        t: NativeOperation,
    ) -> BoolTarget {
        let op_code = builder.constant(F::from_canonical_u64(t as u64));
        builder.is_equal(self.op_type[1], op_code)
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
    fn constant_value(&mut self, v: Value) -> ValueTarget;
    fn is_equal_slice(&mut self, xs: &[Target], ys: &[Target]) -> BoolTarget;

    // Convenience methods for checking values.
    /// Checks whether `xs` is right-padded with 0s so as to represent a `Value`.
    fn is_value(&mut self, xs: &[Target]) -> BoolTarget;
    /// Checks whether `x < y` if `b` is true. This involves checking
    /// that `x` and `y` each consist of two `u32` limbs.
    fn assert_less_if(&mut self, b: BoolTarget, x: ValueTarget, y: ValueTarget);

    // Convenience methods for randomly accessing vector elements and rows of matrices.
    fn vector_ref(&mut self, v: &[Target], i: Target) -> Target;
    fn matrix_row_ref(&mut self, m: &[Vec<Target>], i: Target) -> Vec<Target>;

    // Convenience methods for Boolean into-iters.
    fn all(&mut self, xs: impl IntoIterator<Item = BoolTarget>) -> BoolTarget;
    fn any(&mut self, xs: impl IntoIterator<Item = BoolTarget>) -> BoolTarget;
}

impl<F: RichField + Extendable<D>, const D: usize> CircuitBuilderPod<F, D>
    for CircuitBuilder<F, D>
{
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

    fn constant_value(&mut self, v: Value) -> ValueTarget {
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

    fn is_value(&mut self, xs: &[Target]) -> BoolTarget {
        let zeros = iter::repeat(self.zero())
            .take(STATEMENT_ARG_F_LEN - VALUE_SIZE)
            .collect::<Vec<_>>();
        self.is_equal_slice(&xs[VALUE_SIZE..], &zeros)
    }

    fn assert_less_if(&mut self, b: BoolTarget, x: ValueTarget, y: ValueTarget) {
        const NUM_BITS: usize = 32;

        // LEq assertion with 32-bit range check.
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

    // TODO: Revisit this when we need more than 64 statements.
    fn vector_ref(&mut self, v: &[Target], i: Target) -> Target {
        self.random_access(i, v.to_vec())
    }

    fn matrix_row_ref(&mut self, m: &[Vec<Target>], i: Target) -> Vec<Target> {
        let num_rows = m.len();
        let num_columns = m
            .get(0)
            .map(|row| {
                let row_len = row.len();
                assert!(m.iter().all(|row| row.len() == row_len));
                row_len
            })
            .unwrap_or(0);
        (0..num_columns)
            .map(|j| self.vector_ref(&(0..num_rows).map(|i| m[i][j]).collect::<Vec<_>>(), i))
            .collect()
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
