use std::{fmt, iter};

use serde::{Deserialize, Serialize};

use crate::{
    backends::plonky2::error::{Error, Result},
    middleware::{self, NativePredicate, Params, Predicate, StatementArg, ToFields, Value},
};

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Statement(pub Predicate, pub Vec<StatementArg>);

impl Eq for Statement {}

impl Statement {
    pub fn is_none(&self) -> bool {
        self.0 == Predicate::Native(NativePredicate::None)
    }
    pub fn predicate(&self) -> Predicate {
        self.0.clone()
    }
    /// Argument method. Trailing Nones are filtered out.
    pub fn args(&self) -> Vec<StatementArg> {
        let maybe_last_arg_index = (0..self.1.len()).rev().find(|i| !self.1[*i].is_none());
        match maybe_last_arg_index {
            None => vec![],
            Some(i) => self.1[0..i + 1].to_vec(),
        }
    }
}

impl ToFields for Statement {
    fn to_fields(&self, params: &Params) -> Vec<middleware::F> {
        let mut fields = self.0.to_fields(params);
        fields.extend(
            self.1
                .iter()
                .chain(iter::repeat(&StatementArg::None))
                .take(params.max_statement_args)
                .flat_map(|arg| arg.to_fields(params)),
        );
        fields
    }
}

impl TryFrom<Statement> for middleware::Statement {
    type Error = Error;
    fn try_from(s: Statement) -> Result<Self> {
        type S = middleware::Statement;
        type NP = NativePredicate;
        type SA = StatementArg;
        let proper_args = s.args();
        Ok(match s.0 {
            Predicate::Native(np) => match (np, &proper_args.as_slice()) {
                (NP::None, &[]) => S::None,
                (NP::Equal, &[a1, a2]) => S::Equal(a1.try_into()?, a2.try_into()?),
                (NP::NotEqual, &[a1, a2]) => S::NotEqual(a1.try_into()?, a2.try_into()?),
                (NP::LtEq, &[a1, a2]) => S::LtEq(a1.try_into()?, a2.try_into()?),
                (NP::Lt, &[a1, a2]) => S::Lt(a1.try_into()?, a2.try_into()?),
                (NP::Contains, &[a1, a2, a3]) => {
                    S::Contains(a1.try_into()?, a2.try_into()?, a3.try_into()?)
                }
                (NP::NotContains, &[a1, a2]) => S::NotContains(a1.try_into()?, a2.try_into()?),
                (NP::SumOf, &[a1, a2, a3]) => {
                    S::SumOf(a1.try_into()?, a2.try_into()?, a3.try_into()?)
                }
                (NP::ProductOf, &[a1, a2, a3]) => {
                    S::ProductOf(a1.try_into()?, a2.try_into()?, a3.try_into()?)
                }
                (NP::MaxOf, &[a1, a2, a3]) => {
                    S::MaxOf(a1.try_into()?, a2.try_into()?, a3.try_into()?)
                }
                (NP::HashOf, &[a1, a2, a3]) => {
                    S::HashOf(a1.try_into()?, a2.try_into()?, a3.try_into()?)
                }
                (NP::PublicKeyOf, &[a1, a2]) => S::PublicKeyOf(a1.try_into()?, a2.try_into()?),
                (NP::ContainerInsert, &[a1, a2, a3, a4]) => S::ContainerInsert(
                    a1.try_into()?,
                    a2.try_into()?,
                    a3.try_into()?,
                    a4.try_into()?,
                ),
                (NP::ContainerUpdate, &[a1, a2, a3, a4]) => S::ContainerUpdate(
                    a1.try_into()?,
                    a2.try_into()?,
                    a3.try_into()?,
                    a4.try_into()?,
                ),
                (NP::ContainerDelete, &[a1, a2, a3]) => {
                    S::ContainerDelete(a1.try_into()?, a2.try_into()?, a3.try_into()?)
                }
                _ => Err(Error::custom(format!(
                    "Ill-formed statement expression {:?}",
                    s
                )))?,
            },
            Predicate::Custom(cpr) => {
                let vs: Vec<Value> = proper_args
                    .into_iter()
                    .filter_map(|arg| match arg {
                        SA::None => None,
                        SA::Literal(v) => Some(v),
                        _ => unreachable!(),
                    })
                    .collect();
                S::Custom(cpr, vs)
            }
            Predicate::BatchSelf(_) => {
                unreachable!()
            }
        })
    }
}

impl From<middleware::Statement> for Statement {
    fn from(s: middleware::Statement) -> Self {
        match s.predicate() {
            middleware::Predicate::Native(c) => Statement(
                middleware::Predicate::Native(c),
                s.args().into_iter().collect(),
            ),
            middleware::Predicate::Custom(cpr) => Statement(
                middleware::Predicate::Custom(cpr),
                s.args().into_iter().collect(),
            ),
            middleware::Predicate::BatchSelf(_) => unreachable!(),
        }
    }
}

impl fmt::Display for Statement {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?} ", self.0)?;
        for (i, arg) in self.1.iter().enumerate() {
            if f.alternate() || !arg.is_none() {
                if i != 0 {
                    write!(f, " ")?;
                }
                arg.fmt(f)?;
            }
        }
        Ok(())
    }
}
