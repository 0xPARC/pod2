use anyhow::Result;
use std::fmt;

use super::Statement;
use crate::{
    backends::plonky2::primitives::merkletree::MerkleProof,
    middleware::{self, OperationType},
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OperationArg {
    None,
    Index(usize),
    // TODO: Replace with `MerkleProofIndex`.
    MerkleProof(MerkleProof),
}

impl OperationArg {
    pub fn is_none(&self) -> bool {
        matches!(self, OperationArg::None)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Operation(pub OperationType, pub Vec<OperationArg>);

impl Operation {
    pub fn deref(&self, statements: &[Statement]) -> Result<crate::middleware::Operation> {
        let deref_args = self
            .1
            .iter()
            .flat_map(|arg| match arg {
                OperationArg::None => None,
                OperationArg::Index(i) => Some(
                    statements[*i]
                        .clone()
                        .try_into()
                        .map(|s| crate::middleware::OperationArg::Statement(s)),
                ),
                OperationArg::MerkleProof(pf) => {
                    Some(Ok(crate::middleware::OperationArg::MerkleProof(pf.clone())))
                }
            })
            .collect::<Result<Vec<_>>>()?;
        middleware::Operation::op(self.0.clone(), &deref_args)
    }
}

impl fmt::Display for Operation {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?} ", self.0)?;
        for (i, arg) in self.1.iter().enumerate() {
            if !(!f.alternate() && arg.is_none()) {
                if i != 0 {
                    write!(f, " ")?;
                }
                match arg {
                    OperationArg::None => write!(f, "none")?,
                    OperationArg::Index(i) => write!(f, "{:02}", i)?,
                    OperationArg::MerkleProof(pf) => write!(f, "{}", pf)?,
                }
            }
        }
        Ok(())
    }
}
