use anyhow::{anyhow, Result};
use std::{fmt, sync::Arc};

use super::{AnchoredKey, SignedPod, Value};
use crate::{
    frontend::{CustomPredicateBatchBuilder, StatementTmplBuilder},
    middleware::{
        self, CustomPredicateBatch, CustomPredicateRef, NativePredicate, Params, Predicate,
    },
};

/// Frontend statement arguments are either anchored keys or values.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StatementArg {
    Literal(Value),
    Key(AnchoredKey),
}

impl fmt::Display for StatementArg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Literal(v) => write!(f, "{}", v),
            Self::Key(r) => write!(f, "{}.{}", r.0 .1, r.1),
        }
    }
}

/// A frontend statement is a predicate code together with a vector of
/// arguments.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Statement(pub Predicate, pub Vec<StatementArg>);

impl Statement {
    pub fn value(&self) -> Option<Value> {
        match (&self.0, self.1.get(1)) {
            (Predicate::Native(NativePredicate::ValueOf), Some(StatementArg::Literal(v))) => {
                Some(v.clone())
            }
            _ => None,
        }
    }
}

/// Given a signed POD and a key string, we may produce the statement
/// containing this key and its corresponding value from the KV store.
impl From<(&SignedPod, &str)> for Statement {
    fn from((pod, key): (&SignedPod, &str)) -> Self {
        // TODO: TryFrom.
        let value = pod
            .kvs
            .get(key)
            .cloned()
            .unwrap_or_else(|| panic!("Key {} is not present in POD: {}", key, pod));
        Statement(
            Predicate::Native(NativePredicate::ValueOf),
            vec![
                StatementArg::Key(AnchoredKey(pod.origin(), key.to_string())),
                StatementArg::Literal(value),
            ],
        )
    }
}

/// A frontend statement may be converted to a middleware statement
/// provided that it is well-formed.
impl TryFrom<Statement> for middleware::Statement {
    type Error = anyhow::Error;
    fn try_from(s: Statement) -> Result<Self> {
        type MS = middleware::Statement;
        type NP = NativePredicate;
        type SA = StatementArg;
        let args = (
            s.1.first().cloned(),
            s.1.get(1).cloned(),
            s.1.get(2).cloned(),
        );
        Ok(match &s.0 {
            Predicate::Native(np) => match (np, args) {
                (NP::None, (None, None, None)) => MS::None,
                (NP::ValueOf, (Some(SA::Key(ak)), Some(StatementArg::Literal(v)), None)) => {
                    MS::ValueOf(ak.into(), (&v).into())
                }
                (NP::Equal, (Some(SA::Key(ak1)), Some(SA::Key(ak2)), None)) => {
                    MS::Equal(ak1.into(), ak2.into())
                }
                (NP::NotEqual, (Some(SA::Key(ak1)), Some(SA::Key(ak2)), None)) => {
                    MS::NotEqual(ak1.into(), ak2.into())
                }
                (NP::Gt, (Some(SA::Key(ak1)), Some(SA::Key(ak2)), None)) => {
                    MS::Gt(ak1.into(), ak2.into())
                }
                (NP::Lt, (Some(SA::Key(ak1)), Some(SA::Key(ak2)), None)) => {
                    MS::Lt(ak1.into(), ak2.into())
                }
                (NP::Contains, (Some(SA::Key(ak1)), Some(SA::Key(ak2)), None)) => {
                    MS::Contains(ak1.into(), ak2.into())
                }
                (NP::NotContains, (Some(SA::Key(ak1)), Some(SA::Key(ak2)), None)) => {
                    MS::NotContains(ak1.into(), ak2.into())
                }
                (NP::Branches, (Some(SA::Key(ak1)), Some(SA::Key(ak2)), Some(SA::Key(ak3)))) => {
                    MS::Branches(ak1.into(), ak2.into(), ak3.into())
                }
                (NP::Leaf, (Some(SA::Key(ak1)), Some(SA::Key(ak2)), Some(SA::Key(ak3)))) => {
                    MS::Leaf(ak1.into(), ak2.into(), ak3.into())
                }
                (NP::IsNullTree, (Some(SA::Key(ak)), None, None)) => MS::IsNullTree(ak.into()),
                (NP::GoesLeft, (Some(SA::Key(ak)), Some(SA::Literal(depth)), None)) => {
                    MS::GoesLeft(ak.into(), (&depth).into())
                }
                (NP::GoesRight, (Some(SA::Key(ak)), Some(SA::Literal(depth)), None)) => {
                    MS::GoesRight(ak.into(), (&depth).into())
                }
                (NP::SumOf, (Some(SA::Key(ak1)), Some(SA::Key(ak2)), Some(SA::Key(ak3)))) => {
                    MS::SumOf(ak1.into(), ak2.into(), ak3.into())
                }
                (NP::ProductOf, (Some(SA::Key(ak1)), Some(SA::Key(ak2)), Some(SA::Key(ak3)))) => {
                    MS::ProductOf(ak1.into(), ak2.into(), ak3.into())
                }
                (NP::MaxOf, (Some(SA::Key(ak1)), Some(SA::Key(ak2)), Some(SA::Key(ak3)))) => {
                    MS::MaxOf(ak1.into(), ak2.into(), ak3.into())
                }
                _ => Err(anyhow!("Ill-formed statement: {}", s))?,
            },
            Predicate::Custom(cpr) => MS::Custom(
                cpr.clone(),
                s.1.iter()
                    .map(|arg| match arg {
                        StatementArg::Key(ak) => Ok(ak.clone().into()),
                        _ => Err(anyhow!("Invalid statement arg: {}", arg)),
                    })
                    .collect::<Result<Vec<_>>>()?,
            ),
            _ => Err(anyhow!("Ill-formed statement: {}", s))?,
        })
    }
}

impl fmt::Display for Statement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?} ", self.0)?;
        for (i, arg) in self.1.iter().enumerate() {
            if i != 0 {
                write!(f, " ")?;
            }
            write!(f, "{}", arg)?;
        }
        Ok(())
    }
}

// Useful custom predicates follow.

use NativePredicate as NP;
use StatementTmplBuilder as STB;

pub fn merkle_subtree_predicate(params: &Params) -> Result<Predicate> {
    let mut builder = CustomPredicateBatchBuilder::new("merkle_subtree".into());

    let merkle_subtree = Predicate::BatchSelf(3);

    let merkle_subtree_base = builder.predicate_and(
        params,
        &["root_ori", "root_key", "node_ori", "node_key"],
        &[],
        &[STB::new(NP::Equal)
            .arg(("root_ori", "root_key"))
            .arg(("node_ori", "node_key"))],
    )?;
    let merkle_subtree_ind1 = builder.predicate_and(
        params,
        &["root_ori", "root_key", "node_ori", "node_key"],
        &["parent_ori", "parent_key", "other_ori", "other_key"],
        &[
            STB::new(merkle_subtree.clone())
                .arg(("root_ori", "root_key"))
                .arg(("parent_ori", "parent_key")),
            STB::new(NP::Branches)
                .arg(("parent_ori", "parent_key"))
                .arg(("node_ori", "node_key"))
                .arg(("other_ori", "other_key")),
        ],
    )?;
    let merkle_subtree_ind2 = builder.predicate_and(
        params,
        &["root_ori", "root_key", "node_ori", "node_key"],
        &["parent_ori", "parent_key", "other_ori", "other_key"],
        &[
            STB::new(merkle_subtree)
                .arg(("root_ori", "root_key"))
                .arg(("parent_ori", "parent_key")),
            STB::new(NP::Branches)
                .arg(("parent_ori", "parent_key"))
                .arg(("other_ori", "other_key"))
                .arg(("node_ori", "node_key")),
        ],
    )?;
    let _merkle_subtree_general = builder.predicate_or(
        params,
        &["root_ori", "root_key", "node_ori", "node_key"],
        &[],
        &[
            STB::new(merkle_subtree_base)
                .arg(("root_ori", "root_key"))
                .arg(("node_ori", "node_key")),
            STB::new(merkle_subtree_ind1)
                .arg(("root_ori", "root_key"))
                .arg(("node_ori", "node_key")),
            STB::new(merkle_subtree_ind2)
                .arg(("root_ori", "root_key"))
                .arg(("node_ori", "node_key")),
        ],
    )?;
    let batch = builder.finish();

    Ok(Predicate::Custom(CustomPredicateRef(batch, 3)))
}

pub fn merkle_contains_predicate(params: &Params) -> Result<Predicate> {
    let mut builder = CustomPredicateBatchBuilder::new("merkle_subtree".into());
    let merkle_subtree = merkle_subtree_predicate(params)?;

    builder.predicate_and(
        params,
        &[
            "root_ori",
            "root_key",
            "key_ori",
            "key_key",
            "value_ori",
            "value_key",
        ],
        &["node_ori", "node_key"],
        &[
            STB::new(merkle_subtree)
                .arg(("root_ori", "root_key"))
                .arg(("node_ori", "node_key")),
            STB::new(NP::Leaf)
                .arg(("node_ori", "node_key"))
                .arg(("key_ori", "key_key"))
                .arg(("value_ori", "value_key")),
        ],
    )?;

    let batch = builder.finish();

    Ok(Predicate::Custom(CustomPredicateRef(batch, 0)))
}
