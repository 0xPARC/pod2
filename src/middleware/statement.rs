use anyhow::{anyhow, Result};
use plonky2::field::types::Field;
use std::fmt;
use strum_macros::FromRepr;

use super::{AnchoredKey, CustomPredicateRef, Params, Predicate, ToFields, Value, F};

pub const KEY_SIGNER: &str = "_signer";
pub const KEY_TYPE: &str = "_type";
pub const STATEMENT_ARG_F_LEN: usize = 8;

#[derive(Clone, Copy, Debug, FromRepr, PartialEq, Eq, Hash)]
pub enum NativePredicate {
    None = 0,
    ValueOf = 1,
    Equal = 2,
    NotEqual = 3,
    Gt = 4,
    Lt = 5,
    Contains = 6,
    NotContains = 7,
    SumOf = 8,
    ProductOf = 9,
    MaxOf = 10,
}

impl ToFields for NativePredicate {
    fn to_fields(&self, _params: &Params) -> (Vec<F>, usize) {
        (vec![F::from_canonical_u64(*self as u64)], 1)
    }
}

/// Type encapsulating statements with their associated arguments.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Statement {
    None,
    ValueOf(AnchoredKey, Value),
    Equal(AnchoredKey, AnchoredKey),
    NotEqual(AnchoredKey, AnchoredKey),
    Gt(AnchoredKey, AnchoredKey),
    Lt(AnchoredKey, AnchoredKey),
    Contains(AnchoredKey, AnchoredKey),
    NotContains(AnchoredKey, AnchoredKey),
    SumOf(AnchoredKey, AnchoredKey, AnchoredKey),
    ProductOf(AnchoredKey, AnchoredKey, AnchoredKey),
    MaxOf(AnchoredKey, AnchoredKey, AnchoredKey),
    Custom(CustomPredicateRef, Vec<AnchoredKey>),
}

impl Statement {
    pub fn is_none(&self) -> bool {
        self == &Self::None
    }
    pub fn code(&self) -> Predicate {
        use Predicate::*;
        match self {
            Self::None => Native(NativePredicate::None),
            Self::ValueOf(_, _) => Native(NativePredicate::ValueOf),
            Self::Equal(_, _) => Native(NativePredicate::Equal),
            Self::NotEqual(_, _) => Native(NativePredicate::NotEqual),
            Self::Gt(_, _) => Native(NativePredicate::Gt),
            Self::Lt(_, _) => Native(NativePredicate::Lt),
            Self::Contains(_, _) => Native(NativePredicate::Contains),
            Self::NotContains(_, _) => Native(NativePredicate::NotContains),
            Self::SumOf(_, _, _) => Native(NativePredicate::SumOf),
            Self::ProductOf(_, _, _) => Native(NativePredicate::ProductOf),
            Self::MaxOf(_, _, _) => Native(NativePredicate::MaxOf),
            Self::Custom(cpr, _) => Custom(cpr.clone()),
        }
    }
    pub fn args(&self) -> Vec<StatementArg> {
        use StatementArg::*;
        match self.clone() {
            Self::None => vec![],
            Self::ValueOf(ak, v) => vec![Key(ak), Literal(v)],
            Self::Equal(ak1, ak2) => vec![Key(ak1), Key(ak2)],
            Self::NotEqual(ak1, ak2) => vec![Key(ak1), Key(ak2)],
            Self::Gt(ak1, ak2) => vec![Key(ak1), Key(ak2)],
            Self::Lt(ak1, ak2) => vec![Key(ak1), Key(ak2)],
            Self::Contains(ak1, ak2) => vec![Key(ak1), Key(ak2)],
            Self::NotContains(ak1, ak2) => vec![Key(ak1), Key(ak2)],
            Self::SumOf(ak1, ak2, ak3) => vec![Key(ak1), Key(ak2), Key(ak3)],
            Self::ProductOf(ak1, ak2, ak3) => vec![Key(ak1), Key(ak2), Key(ak3)],
            Self::MaxOf(ak1, ak2, ak3) => vec![Key(ak1), Key(ak2), Key(ak3)],
            Self::Custom(_, args) => Vec::from_iter(args.into_iter().map(|h| Key(h))),
        }
    }
}

impl ToFields for Statement {
    fn to_fields(&self, _params: &Params) -> (Vec<F>, usize) {
        let (native_statement_f, native_statement_f_len) = self.code().to_fields(_params);
        let (vec_statementarg_f, vec_statementarg_f_len) = self
            .args()
            .into_iter()
            .map(|statement_arg| statement_arg.to_fields(_params))
            .fold((Vec::new(), 0), |mut acc, (f, l)| {
                acc.0.extend(f);
                acc.1 += l;
                acc
            });
        (
            [native_statement_f, vec_statementarg_f].concat(),
            native_statement_f_len + vec_statementarg_f_len,
        )
    }
}

impl fmt::Display for Statement {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?} ", self.code())?;
        for (i, arg) in self.args().iter().enumerate() {
            if i != 0 {
                write!(f, " ")?;
            }
            write!(f, "{}", arg)?;
        }
        Ok(())
    }
}

/// Statement argument type. Useful for statement decompositions.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StatementArg {
    None,
    Literal(Value),
    Key(AnchoredKey),
}

impl fmt::Display for StatementArg {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            StatementArg::None => write!(f, "none"),
            StatementArg::Literal(v) => write!(f, "{}", v),
            StatementArg::Key(r) => write!(f, "{}.{}", r.0, r.1),
        }
    }
}

impl StatementArg {
    pub fn is_none(&self) -> bool {
        matches!(self, Self::None)
    }
    pub fn literal(&self) -> Result<Value> {
        match self {
            Self::Literal(value) => Ok(*value),
            _ => Err(anyhow!("Statement argument {:?} is not a literal.", self)),
        }
    }
    pub fn key(&self) -> Result<AnchoredKey> {
        match self {
            Self::Key(ak) => Ok(ak.clone()),
            _ => Err(anyhow!("Statement argument {:?} is not a key.", self)),
        }
    }
}

impl ToFields for StatementArg {
    fn to_fields(&self, _params: &Params) -> (Vec<F>, usize) {
        // NOTE: current version returns always the same amount of field elements in the returned
        // vector, which means that the `None` case is padded with 8 zeroes, and the `Literal` case
        // is padded with 4 zeroes. Since the returned vector will mostly be hashed (and reproduced
        // in-circuit), we might be interested into reducing the length of it. If that's the case,
        // we can check if it makes sense to make it dependant on the concrete StatementArg; that
        // is, when dealing with a `None` it would be a single field element (zero value), and when
        // dealing with `Literal` it would be of length 4.
        let f = match self {
            StatementArg::None => vec![F::ZERO; STATEMENT_ARG_F_LEN],
            StatementArg::Literal(v) => {
                let value_f = v.0.to_vec();
                [
                    value_f.clone(),
                    vec![F::ZERO; STATEMENT_ARG_F_LEN - value_f.len()],
                ]
                .concat()
            }
            StatementArg::Key(ak) => {
                let (podid_f, _) = ak.0.to_fields(_params);
                let (hash_f, _) = ak.1.to_fields(_params);
                [podid_f, hash_f].concat()
            }
        };
        assert_eq!(f.len(), STATEMENT_ARG_F_LEN); // sanity check
        (f, STATEMENT_ARG_F_LEN)
    }
}
