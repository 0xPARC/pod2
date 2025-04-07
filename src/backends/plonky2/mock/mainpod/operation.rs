use std::{fmt, iter};

use anyhow::{anyhow, Result};
use plonky2::field::types::Field;
use serde::{Deserialize, Serialize};

use crate::{
    backends::plonky2::{
        mock::mainpod::Statement,
        primitives::merkletree::{self},
    },
    middleware::{self, Hash, OperationType, Params, ToFields, Value, EMPTY_HASH, EMPTY_VALUE, F},
};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
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

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum OperationAux {
    None,
    MerkleProofIndex(usize),
}

impl ToFields for OperationAux {
    fn to_fields(&self, _params: &Params) -> Vec<F> {
        let f = match self {
            Self::None => F::ZERO,
            Self::MerkleProofIndex(i) => F::from_canonical_usize(*i),
        };
        vec![f]
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MerkleClaimAndProof {
    pub enabled: bool,
    pub root: Hash,
    pub key: Value,
    pub value: Value,
    pub existence: bool,
    pub siblings: Vec<Hash>,
    pub case_ii_selector: bool,
    pub other_key: Value,
    pub other_value: Value,
}

impl MerkleClaimAndProof {
    pub fn empty(max_depth: usize) -> Self {
        Self {
            enabled: false,
            root: EMPTY_HASH,
            key: Value::from(1),
            value: EMPTY_VALUE,
            existence: false,
            siblings: iter::repeat(EMPTY_HASH).take(max_depth).collect(),
            case_ii_selector: false,
            other_key: EMPTY_VALUE,
            other_value: EMPTY_VALUE,
        }
    }
    pub fn try_from_middleware(
        params: &Params,
        root: &Value,
        key: &Value,
        value: Option<&Value>,
        mid_mp: &merkletree::MerkleProof,
    ) -> Result<Self> {
        if mid_mp.siblings.len() > params.max_depth_mt_gadget {
            Err(anyhow!(
                "Number of siblings ({}) exceeds maximum depth ({})",
                mid_mp.siblings.len(),
                params.max_depth_mt_gadget
            ))
        } else {
            let (other_key, other_value) = mid_mp.other_leaf.unwrap_or((EMPTY_VALUE, EMPTY_VALUE));
            Ok(Self {
                enabled: true,
                root: (*root).into(),
                key: *key,
                value: value.cloned().unwrap_or(EMPTY_VALUE),
                existence: mid_mp.existence,
                siblings: mid_mp
                    .siblings
                    .iter()
                    .cloned()
                    .chain(iter::repeat(EMPTY_HASH))
                    .take(params.max_depth_mt_gadget)
                    .collect(),
                case_ii_selector: mid_mp.other_leaf.is_some(),
                other_key,
                other_value,
            })
        }
    }
}

impl TryFrom<MerkleClaimAndProof> for merkletree::MerkleProof {
    type Error = anyhow::Error;
    fn try_from(mp: MerkleClaimAndProof) -> Result<Self> {
        if !mp.enabled {
            return Err(anyhow!("Not a valid Merkle proof."));
        }
        let existence = mp.existence;
        let other_leaf = if mp.case_ii_selector {
            Some((mp.other_key, mp.other_value))
        } else {
            None
        };
        // Trim padding (if any).
        let siblings = mp
            .siblings
            .into_iter()
            .rev()
            .skip_while(|s| s == &EMPTY_HASH)
            .collect::<Vec<_>>()
            .into_iter()
            .rev()
            .collect();
        Ok(merkletree::MerkleProof {
            existence,
            siblings,
            other_leaf,
        })
    }
}

impl fmt::Display for MerkleClaimAndProof {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match merkletree::MerkleProof::try_from(self.clone()) {
            Err(_) => write!(f, "∅"),
            Ok(mp) => mp.fmt(f),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
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
            OperationAux::None => Ok(crate::middleware::OperationAux::None),
            OperationAux::MerkleProofIndex(i) => merkle_proofs
                .get(i)
                .cloned()
                .ok_or(anyhow!("Missing Merkle proof index {}", i))
                .and_then(|mp| {
                    mp.try_into()
                        .map(crate::middleware::OperationAux::MerkleProof)
                }),
        }?;
        middleware::Operation::op(self.0.clone(), &deref_args, &deref_aux)
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
            OperationAux::MerkleProofIndex(i) => write!(f, "merkle_proof_{:02}", i)?,
        }
        Ok(())
    }
}
