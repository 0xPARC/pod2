use std::fmt;

use plonky2::field::types::Field;
use serde::{Deserialize, Serialize};

use crate::{
    backends::plonky2::{
        error::{Error, Result},
        mainpod::Statement,
        primitives::merkletree::MerkleClaimAndProof,
    },
    middleware::{self, OperationType, Params, ToFields, F},
};

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum OperationArg {
    None,
    Index(usize),
}

impl ToFields for OperationArg {
    fn to_fields(&self, _params: &Params) -> Vec<F> {
        let f = match self {
            Self::None => F::ZERO,
            Self::Index(i) => F::from_canonical_usize(*i),
        };
        vec![f]
    }
}

impl OperationArg {
    pub fn is_none(&self) -> bool {
        matches!(self, OperationArg::None)
    }
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum OperationAux {
    None,
    MerkleProofIndex(usize),
    CustomPredVerifyIndex(usize),
}

impl ToFields for OperationAux {
    fn to_fields(&self, _params: &Params) -> Vec<F> {
        let fs = match self {
            Self::None => [F::ZERO, F::ZERO],
            Self::MerkleProofIndex(i) => [F::from_canonical_usize(*i), F::ZERO],
            Self::CustomPredVerifyIndex(i) => [F::ZERO, F::from_canonical_usize(*i)],
        };
        vec![fs[0], fs[1]]
    }
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Operation(pub OperationType, pub Vec<OperationArg>, pub OperationAux);

impl Operation {
    pub fn op_type(&self) -> OperationType {
        self.0.clone()
    }
    pub fn args(&self) -> &[OperationArg] {
        &self.1
    }
    pub fn aux(&self) -> &OperationAux {
        &self.2
    }
    pub fn deref(
        &self,
        statements: &[Statement],
        merkle_proofs: &[MerkleClaimAndProof],
    ) -> Result<crate::middleware::Operation> {
        let deref_args = self
            .1
            .iter()
            .flat_map(|arg| match arg {
                OperationArg::None => None,
                OperationArg::Index(i) => Some(statements[*i].clone().try_into()),
            })
            .collect::<Result<Vec<_>>>()?;
        let deref_aux = match self.2 {
            OperationAux::None => crate::middleware::OperationAux::None,
            OperationAux::CustomPredVerifyIndex(_) => crate::middleware::OperationAux::None,
            OperationAux::MerkleProofIndex(i) => crate::middleware::OperationAux::MerkleProof(
                merkle_proofs
                    .get(i)
                    .ok_or(Error::custom(format!("Missing Merkle proof index {}", i)))?
                    .proof
                    .clone(),
            ),
        };
        Ok(middleware::Operation::op(
            self.0.clone(),
            &deref_args,
            &deref_aux,
        )?)
    }
}

impl fmt::Display for Operation {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?} ", self.0)?;
        for (i, arg) in self.1.iter().enumerate() {
            if f.alternate() || !arg.is_none() {
                if i != 0 {
                    write!(f, " ")?;
                }
                match arg {
                    OperationArg::None => write!(f, "none")?,
                    OperationArg::Index(i) => write!(f, "{:02}", i)?,
                }
            }
        }
        match self.2 {
            OperationAux::None => (),
            OperationAux::MerkleProofIndex(i) => write!(f, " merkle_proof_{:02}", i)?,
            OperationAux::CustomPredVerifyIndex(i) => write!(f, " custom_pred_verify_{:02}", i)?,
        }
        Ok(())
    }
}
