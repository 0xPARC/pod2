//! Common functionality to build Pod circuits with plonky2

use crate::backends::plonky2::mock_main::Statement;
use crate::backends::plonky2::mock_main::{Operation, OperationArg};
use crate::middleware::{Params, StatementArg, ToFields, Value, F, HASH_SIZE, VALUE_SIZE};
use crate::middleware::{OPERATION_ARG_F_LEN, STATEMENT_ARG_F_LEN};
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

#[derive(Clone)]
pub struct StatementTarget {
    pub predicate: [Target; Params::predicate_size()],
    pub args: Vec<[Target; STATEMENT_ARG_F_LEN]>,
}

impl StatementTarget {
    pub fn to_flattened(&self) -> Vec<Target> {
        self.predicate
            .iter()
            .chain(self.args.iter().flatten())
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
            pw.set_target_arr(&self.args[i], &arg.to_fields(params))?;
        }
        Ok(())
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

    // Convenience methods for randomly accessing vector elements and rows of matrices.
    fn vector_ref(&mut self, v: &[Target], i: Target) -> Target;
    fn matrix_row_ref(&mut self, m: &[Vec<Target>], i: Target) -> Vec<Target>;

    // Convenience methods for Boolean into-iters. Assumes these are non-empty.
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
                .map(|_| self.add_virtual_target_arr())
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
            .expect("Empty iterator")
    }

    fn any(&mut self, xs: impl IntoIterator<Item = BoolTarget>) -> BoolTarget {
        xs.into_iter()
            .reduce(|a, b| self.or(a, b))
            .expect("Empty iterator")
    }
}
