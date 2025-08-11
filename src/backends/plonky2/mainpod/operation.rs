use std::fmt;

use serde::{Deserialize, Serialize};

use crate::{
    backends::plonky2::{
        error::{Error, Result},
        mainpod::Statement,
        primitives::merkletree::{MerkleClaimAndProof, MerkleTreeStateTransitionProof},
    },
    middleware::{self, OperationType, Params},
};

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum OperationArg {
    None,
    Index(usize),
}

impl OperationArg {
    pub fn is_none(&self) -> bool {
        matches!(self, OperationArg::None)
    }

    pub fn as_usize(&self) -> usize {
        match self {
            Self::None => 0,
            Self::Index(i) => *i,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Serialize, Deserialize)]
pub enum OperationAux {
    None,
    MerkleProofIndex(usize),
    PublicKeyOfIndex(usize),
    MerkleTreeStateTransitionProofIndex(usize),
    CustomPredVerifyIndex(usize),
}

impl OperationAux {
    fn table_offset_merkle_proof(_params: &Params) -> usize {
        // At index 0 we store a zero entry
        1
    }
    fn table_offset_public_key_of(params: &Params) -> usize {
        Self::table_offset_merkle_proof(params) + params.max_merkle_proofs_containers
    }
    fn table_offset_merkle_tree_state_transition_proof(params: &Params) -> usize {
        Self::table_offset_public_key_of(params) + params.max_public_key_of
    }
    fn table_offset_custom_pred_verify(params: &Params) -> usize {
        Self::table_offset_merkle_tree_state_transition_proof(params)
            + params.max_merkle_tree_state_transition_proofs_containers
    }
    pub(crate) fn table_size(params: &Params) -> usize {
        1 + params.max_merkle_proofs_containers
            + params.max_public_key_of
            + params.max_merkle_tree_state_transition_proofs_containers
            + params.max_custom_predicate_verifications
    }
    pub fn table_index(&self, params: &Params) -> usize {
        match self {
            Self::None => 0,
            Self::MerkleProofIndex(i) => Self::table_offset_merkle_proof(params) + *i,
            Self::PublicKeyOfIndex(i) => Self::table_offset_public_key_of(params) + *i,
            Self::MerkleTreeStateTransitionProofIndex(i) => {
                Self::table_offset_merkle_tree_state_transition_proof(params) + *i
            }
            Self::CustomPredVerifyIndex(i) => Self::table_offset_custom_pred_verify(params) + *i,
        }
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
        merkle_tree_state_transition_proofs: &[MerkleTreeStateTransitionProof],
    ) -> Result<crate::middleware::Operation> {
        let deref_args = self
            .1
            .iter()
            .flat_map(|arg| match arg {
                OperationArg::None => None,
                OperationArg::Index(i) => {
                    let st: Result<crate::middleware::Statement> =
                        statements[*i].clone().try_into();
                    Some(st)
                }
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
            OperationAux::MerkleTreeStateTransitionProofIndex(i) => {
                crate::middleware::OperationAux::MerkleTreeStateTransitionProof(
                    merkle_tree_state_transition_proofs
                        .get(i)
                        .ok_or(Error::custom(format!(
                            "Missing Merkle state transition proof index {}",
                            i
                        )))?
                        .clone(),
                )
            }
            OperationAux::PublicKeyOfIndex(_) => crate::middleware::OperationAux::None,
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
            OperationAux::PublicKeyOfIndex(i) => write!(f, " public_key_of_{:02}", i)?,
            OperationAux::MerkleTreeStateTransitionProofIndex(i) => {
                write!(f, " merkle_tree_state_transition_proof_{:02}", i)?
            }
        }
        Ok(())
    }
}
