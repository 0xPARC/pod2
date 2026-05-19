use std::fmt;

use serde::{Deserialize, Serialize};

use crate::{
    backends::plonky2::{
        error::{Error, Result},
        mainpod::{MerkleProofs, MerkleTransitionProofs, SignedBy, Statement},
    },
    middleware::{self, InputPodOpenStatement, OperationType, Params},
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
pub enum Size {
    Small,
    Medium,
}

impl fmt::Display for Size {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Small => write!(f, "small"),
            Self::Medium => write!(f, "medium"),
        }
    }
}

impl Size {
    pub const fn min() -> Self {
        Self::Small
    }
    pub const fn max() -> Self {
        Self::Medium
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Serialize, Deserialize)]
pub enum OperationAux {
    None,
    MerkleProofIndex(Size, usize),
    MerkleTransitionProofIndex(Size, usize),
    OpenInputStatement(usize),
    CustomPredVerifyIndex(usize),
    PublicKeyOfIndex(usize),
    SignedByIndex(usize),
}

impl OperationAux {
    fn table_offset_merkle_proof(params: &Params, size: Size) -> usize {
        match size {
            // At index 0 we store a zero entry
            Size::Small => 1,
            Size::Medium => {
                Self::table_offset_merkle_proof(params, Size::Small)
                    + params.containers.state.max_small
            }
        }
    }
    fn table_offset_merkle_transition_proof(params: &Params, size: Size) -> usize {
        match size {
            Size::Small => {
                Self::table_offset_merkle_proof(params, Size::min())
                    + params.containers.state.max_total()
            }
            Size::Medium => {
                Self::table_offset_merkle_transition_proof(params, Size::Small)
                    + params.containers.transition.max_small
            }
        }
    }
    fn table_offset_open_input_statement(params: &Params) -> usize {
        Self::table_offset_merkle_transition_proof(params, Size::min())
            + params.containers.transition.max_total()
    }
    fn table_offset_custom_pred_verify(params: &Params) -> usize {
        Self::table_offset_open_input_statement(params) + params.max_open_input_statements
    }
    fn table_offset_public_key_of(params: &Params) -> usize {
        Self::table_offset_custom_pred_verify(params) + params.max_custom_predicate_verifications
    }
    fn table_offset_signed_by(params: &Params) -> usize {
        Self::table_offset_public_key_of(params) + params.max_public_key_of
    }
    pub(crate) fn table_size(params: &Params) -> usize {
        1 + params.containers.state.max_total()
            + params.containers.transition.max_total()
            + params.max_open_input_statements
            + params.max_custom_predicate_verifications
            + params.max_public_key_of
            + params.max_signed_by
    }
    pub fn table_index(&self, params: &Params) -> usize {
        match self {
            Self::None => 0,
            Self::MerkleProofIndex(size, i) => Self::table_offset_merkle_proof(params, *size) + *i,
            Self::MerkleTransitionProofIndex(size, i) => {
                Self::table_offset_merkle_transition_proof(params, *size) + *i
            }
            Self::OpenInputStatement(i) => Self::table_offset_open_input_statement(params) + *i,
            Self::CustomPredVerifyIndex(i) => Self::table_offset_custom_pred_verify(params) + *i,
            Self::PublicKeyOfIndex(i) => Self::table_offset_public_key_of(params) + *i,
            Self::SignedByIndex(i) => Self::table_offset_signed_by(params) + *i,
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
        signatures: &[SignedBy],
        merkle_proofs: &MerkleProofs,
        merkle_transition_proofs: &MerkleTransitionProofs,
        open_input_statements: &[InputPodOpenStatement],
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
            OperationAux::MerkleProofIndex(size, i) => {
                let table = match size {
                    Size::Small => &merkle_proofs.small,
                    Size::Medium => &merkle_proofs.medium,
                };
                crate::middleware::OperationAux::MerkleProof(
                    table
                        .get(i)
                        .ok_or(Error::custom(format!("Missing Merkle proof index {}", i)))?
                        .proof
                        .clone(),
                )
            }
            OperationAux::MerkleTransitionProofIndex(size, i) => {
                let table = match size {
                    Size::Small => &merkle_transition_proofs.small,
                    Size::Medium => &merkle_transition_proofs.medium,
                };
                crate::middleware::OperationAux::MerkleTreeStateTransitionProof(
                    table
                        .get(i)
                        .ok_or(Error::custom(format!(
                            "Missing Merkle state transition proof index {}",
                            i
                        )))?
                        .clone(),
                )
            }
            OperationAux::CustomPredVerifyIndex(_) => crate::middleware::OperationAux::None,
            OperationAux::OpenInputStatement(i) => {
                crate::middleware::OperationAux::OpenInputStatement(
                    open_input_statements
                        .get(i)
                        .ok_or(Error::custom(format!(
                            "Missing OpenInputStatement data index {}",
                            i
                        )))?
                        .clone(),
                )
            }
            OperationAux::SignedByIndex(i) => crate::middleware::OperationAux::Signature(
                signatures
                    .get(i)
                    .ok_or(Error::custom(format!("Missing SignedBy data index {}", i)))?
                    .sig
                    .clone(),
            ),
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
            OperationAux::MerkleProofIndex(size, i) => {
                write!(f, " {}_merkle_proof_{:02}", size, i)?
            }
            OperationAux::CustomPredVerifyIndex(i) => write!(f, " custom_pred_verify_{:02}", i)?,
            OperationAux::OpenInputStatement(i) => write!(f, " open_input_statement_{:02}", i)?,
            OperationAux::PublicKeyOfIndex(i) => write!(f, " public_key_of_{:02}", i)?,
            OperationAux::SignedByIndex(i) => write!(f, " signed_by_{:02}", i)?,
            OperationAux::MerkleTransitionProofIndex(size, i) => {
                write!(f, " {}_merkle_transition_proof_{:02}", size, i)?
            }
        }
        Ok(())
    }
}
