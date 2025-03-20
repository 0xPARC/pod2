//! Common functionality to build Pod circuits with plonky2

use crate::middleware::STATEMENT_ARG_F_LEN;
use crate::middleware::{Params, Value, HASH_SIZE, VALUE_SIZE};
use plonky2::field::extension::Extendable;
use plonky2::field::types::PrimeField64;
use plonky2::hash::hash_types::RichField;
use plonky2::iop::target::{BoolTarget, Target};
use plonky2::plonk::circuit_builder::CircuitBuilder;

#[derive(Copy, Clone)]
pub struct ValueTarget {
    pub elements: [Target; VALUE_SIZE],
}

#[derive(Clone)]
pub struct StatementTarget {
    pub code: [Target; HASH_SIZE + 2],
    pub args: Vec<[Target; STATEMENT_ARG_F_LEN]>,
}

impl StatementTarget {
    pub fn to_flattened(&self) -> Vec<Target> {
        self.code
            .iter()
            .chain(self.args.iter().flatten())
            .cloned()
            .collect()
    }
}

// TODO: Implement Operation::to_field to determine the size of each element
#[derive(Clone)]
pub struct OperationTarget {
    pub code: [Target; 6],
    pub args: Vec<[Target; STATEMENT_ARG_F_LEN]>,
}

pub trait CircuitBuilderPod<F: RichField + Extendable<D>, const D: usize> {
    fn connect_values(&mut self, x: ValueTarget, y: ValueTarget);
    fn connect_slice(&mut self, xs: &[Target], ys: &[Target]);
    fn add_virtual_value(&mut self) -> ValueTarget;
    fn add_virtual_statement(&mut self, params: &Params) -> StatementTarget;
    fn add_virtual_operation(&mut self, params: &Params) -> OperationTarget;
    fn select_value(&mut self, b: BoolTarget, x: ValueTarget, y: ValueTarget) -> ValueTarget;
    fn constant_value(&mut self, v: Value) -> ValueTarget;
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
            code: self.add_virtual_target_arr::<6>(),
            args: (0..params.max_statement_args)
                .map(|_| self.add_virtual_target_arr::<STATEMENT_ARG_F_LEN>())
                .collect(),
        }
    }

    fn add_virtual_operation(&mut self, params: &Params) -> OperationTarget {
        todo!()
    }

    fn select_value(&mut self, b: BoolTarget, x: ValueTarget, y: ValueTarget) -> ValueTarget {
        ValueTarget {
            elements: std::array::from_fn(|i| self.select(b, x.elements[i], y.elements[i])),
        }
    }

    fn constant_value(&mut self, v: Value) -> ValueTarget {
        ValueTarget {
            elements: std::array::from_fn(|i| {
                self.constant(F::from_noncanonical_u64(v.0[i].to_noncanonical_u64()))
            }),
        }
    }
}
