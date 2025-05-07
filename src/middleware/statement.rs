use std::{fmt, iter};

use plonky2::field::types::Field;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
use strum_macros::FromRepr;

use crate::middleware::{
    AnchoredKey, CustomPredicateRef, Error, Key, Params, PodId, RawValue, Result, ToFields, Value,
    F, VALUE_SIZE,
};

// TODO: Maybe store KEY_SIGNER and KEY_TYPE as Key with lazy_static
// hash(KEY_SIGNER) = [2145458785152392366, 15113074911296146791, 15323228995597834291, 11804480340100333725]
pub const KEY_SIGNER: &str = "_signer";
// hash(KEY_TYPE) = [17948789436443445142, 12513915140657440811, 15878361618879468769, 938231894693848619]
pub const KEY_TYPE: &str = "_type";
pub const STATEMENT_ARG_F_LEN: usize = 8;
pub const OPERATION_ARG_F_LEN: usize = 1;
pub const OPERATION_AUX_F_LEN: usize = 1;

#[derive(Clone, Copy, Debug, FromRepr, PartialEq, Eq, Hash, Serialize, Deserialize, JsonSchema)]
pub enum NativePredicate {
    None = 0,
    ValueOf = 1,
    Equal = 2,
    NotEqual = 3,
    LtEq = 4,
    Lt = 5,
    Contains = 6,
    NotContains = 7,
    SumOf = 8,
    ProductOf = 9,
    MaxOf = 10,
    HashOf = 11,

    // Syntactic sugar predicates.  These predicates are not supported by the backend.  The
    // frontend compiler is responsible of translating these predicates into the predicates above.
    DictContains = 1000,
    DictNotContains = 1001,
    SetContains = 1002,
    SetNotContains = 1003,
    ArrayContains = 1004, // there is no ArrayNotContains
    GtEq = 1005,
    Gt = 1006,
}

impl ToFields for NativePredicate {
    fn to_fields(&self, _params: &Params) -> Vec<F> {
        vec![F::from_canonical_u64(*self as u64)]
    }
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize, JsonSchema)]
pub enum WildcardValue {
    PodId(PodId),
    Key(Key),
}

impl WildcardValue {
    pub fn raw(&self) -> RawValue {
        match self {
            WildcardValue::PodId(pod_id) => RawValue::from(pod_id.0),
            WildcardValue::Key(key) => key.raw(),
        }
    }
}

impl fmt::Display for WildcardValue {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            WildcardValue::PodId(pod_id) => write!(f, "{}", pod_id),
            WildcardValue::Key(key) => write!(f, "{}", key),
        }
    }
}

impl ToFields for WildcardValue {
    fn to_fields(&self, params: &Params) -> Vec<F> {
        match self {
            WildcardValue::PodId(pod_id) => pod_id.to_fields(params),
            WildcardValue::Key(key) => key.to_fields(params),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize, JsonSchema)]
#[serde(tag = "type", content = "value")]
pub enum Predicate {
    Native(NativePredicate),
    BatchSelf(usize),
    Custom(CustomPredicateRef),
}

impl From<NativePredicate> for Predicate {
    fn from(v: NativePredicate) -> Self {
        Self::Native(v)
    }
}

#[derive(Clone, Copy)]
pub enum PredicatePrefix {
    Native = 1,
    BatchSelf = 2,
    Custom = 3,
}

impl From<PredicatePrefix> for F {
    fn from(prefix: PredicatePrefix) -> Self {
        Self::from_canonical_usize(prefix as usize)
    }
}

impl ToFields for Predicate {
    fn to_fields(&self, params: &Params) -> Vec<F> {
        // serialize:
        // NativePredicate(id) as (1, id, 0, 0, 0, 0) -- id: usize
        // BatchSelf(i) as (2, i, 0, 0, 0, 0) -- i: usize
        // CustomPredicateRef(pb, i) as
        // (3, [hash of pb], i) -- pb hashes to 4 field elements
        //                      -- i: usize

        // in every case: pad to (hash_size + 2) field elements
        let mut fields: Vec<F> = match self {
            Self::Native(p) => iter::once(F::from(PredicatePrefix::Native))
                .chain(p.to_fields(params))
                .collect(),
            Self::BatchSelf(i) => iter::once(F::from(PredicatePrefix::BatchSelf))
                .chain(iter::once(F::from_canonical_usize(*i)))
                .collect(),
            Self::Custom(CustomPredicateRef { batch, index }) => {
                iter::once(F::from(PredicatePrefix::Custom))
                    .chain(batch.id(params).0)
                    .chain(iter::once(F::from_canonical_usize(*index)))
                    .collect()
            }
        };
        fields.resize_with(Params::predicate_size(), || F::from_canonical_u64(0));
        fields
    }
}

impl fmt::Display for Predicate {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Native(p) => write!(f, "{:?}", p),
            Self::BatchSelf(i) => write!(f, "self.{}", i),
            Self::Custom(CustomPredicateRef { batch, index }) => {
                write!(
                    f,
                    "{}.{}[{}]",
                    batch.name, index, batch.predicates[*index].name
                )
            }
        }
    }
}

/// Type encapsulating statements with their associated arguments.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize, JsonSchema)]
#[serde(tag = "predicate", content = "args")]
pub enum Statement {
    None,
    ValueOf(AnchoredKey, Value),
    Equal(AnchoredKey, AnchoredKey),
    NotEqual(AnchoredKey, AnchoredKey),
    LtEq(AnchoredKey, AnchoredKey),
    Lt(AnchoredKey, AnchoredKey),
    Contains(
        /* root  */ AnchoredKey,
        /* key   */ AnchoredKey,
        /* value */ AnchoredKey,
    ),
    NotContains(/* root  */ AnchoredKey, /* key   */ AnchoredKey),
    SumOf(AnchoredKey, AnchoredKey, AnchoredKey),
    ProductOf(AnchoredKey, AnchoredKey, AnchoredKey),
    MaxOf(AnchoredKey, AnchoredKey, AnchoredKey),
    HashOf(AnchoredKey, AnchoredKey, AnchoredKey),
    Custom(CustomPredicateRef, Vec<WildcardValue>),
}

impl Statement {
    pub fn is_none(&self) -> bool {
        self == &Self::None
    }
    pub fn predicate(&self) -> Predicate {
        use Predicate::*;
        match self {
            Self::None => Native(NativePredicate::None),
            Self::ValueOf(_, _) => Native(NativePredicate::ValueOf),
            Self::Equal(_, _) => Native(NativePredicate::Equal),
            Self::NotEqual(_, _) => Native(NativePredicate::NotEqual),
            Self::LtEq(_, _) => Native(NativePredicate::LtEq),
            Self::Lt(_, _) => Native(NativePredicate::Lt),
            Self::Contains(_, _, _) => Native(NativePredicate::Contains),
            Self::NotContains(_, _) => Native(NativePredicate::NotContains),
            Self::SumOf(_, _, _) => Native(NativePredicate::SumOf),
            Self::ProductOf(_, _, _) => Native(NativePredicate::ProductOf),
            Self::MaxOf(_, _, _) => Native(NativePredicate::MaxOf),
            Self::HashOf(_, _, _) => Native(NativePredicate::HashOf),
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
            Self::LtEq(ak1, ak2) => vec![Key(ak1), Key(ak2)],
            Self::Lt(ak1, ak2) => vec![Key(ak1), Key(ak2)],
            Self::Contains(ak1, ak2, ak3) => vec![Key(ak1), Key(ak2), Key(ak3)],
            Self::NotContains(ak1, ak2) => vec![Key(ak1), Key(ak2)],
            Self::SumOf(ak1, ak2, ak3) => vec![Key(ak1), Key(ak2), Key(ak3)],
            Self::ProductOf(ak1, ak2, ak3) => vec![Key(ak1), Key(ak2), Key(ak3)],
            Self::MaxOf(ak1, ak2, ak3) => vec![Key(ak1), Key(ak2), Key(ak3)],
            Self::HashOf(ak1, ak2, ak3) => vec![Key(ak1), Key(ak2), Key(ak3)],
            Self::Custom(_, args) => Vec::from_iter(args.into_iter().map(WildcardLiteral)),
        }
    }
    pub fn from_args(pred: Predicate, args: Vec<StatementArg>) -> Result<Self> {
        use Predicate::*;
        let st: Result<Self> = match pred {
            Native(NativePredicate::None) => Ok(Self::None),
            Native(NativePredicate::ValueOf) => {
                if let (StatementArg::Key(a0), StatementArg::Literal(v1)) =
                    (args[0].clone(), args[1].clone())
                {
                    Ok(Self::ValueOf(a0, v1))
                } else {
                    Err(Error::incorrect_statements_args())
                }
            }
            Native(NativePredicate::Equal) => {
                if let (StatementArg::Key(a0), StatementArg::Key(a1)) =
                    (args[0].clone(), args[1].clone())
                {
                    Ok(Self::Equal(a0, a1))
                } else {
                    Err(Error::incorrect_statements_args())
                }
            }
            Native(NativePredicate::NotEqual) => {
                if let (StatementArg::Key(a0), StatementArg::Key(a1)) =
                    (args[0].clone(), args[1].clone())
                {
                    Ok(Self::NotEqual(a0, a1))
                } else {
                    Err(Error::incorrect_statements_args())
                }
            }
            Native(NativePredicate::LtEq) => {
                if let (StatementArg::Key(a0), StatementArg::Key(a1)) =
                    (args[0].clone(), args[1].clone())
                {
                    Ok(Self::LtEq(a0, a1))
                } else {
                    Err(Error::incorrect_statements_args())
                }
            }
            Native(NativePredicate::Lt) => {
                if let (StatementArg::Key(a0), StatementArg::Key(a1)) =
                    (args[0].clone(), args[1].clone())
                {
                    Ok(Self::Lt(a0, a1))
                } else {
                    Err(Error::incorrect_statements_args())
                }
            }
            Native(NativePredicate::Contains) => {
                if let (StatementArg::Key(a0), StatementArg::Key(a1), StatementArg::Key(a2)) =
                    (args[0].clone(), args[1].clone(), args[2].clone())
                {
                    Ok(Self::Contains(a0, a1, a2))
                } else {
                    Err(Error::incorrect_statements_args())
                }
            }
            Native(NativePredicate::NotContains) => {
                if let (StatementArg::Key(a0), StatementArg::Key(a1)) =
                    (args[0].clone(), args[1].clone())
                {
                    Ok(Self::NotContains(a0, a1))
                } else {
                    Err(Error::incorrect_statements_args())
                }
            }
            Native(NativePredicate::SumOf) => {
                if let (StatementArg::Key(a0), StatementArg::Key(a1), StatementArg::Key(a2)) =
                    (args[0].clone(), args[1].clone(), args[2].clone())
                {
                    Ok(Self::SumOf(a0, a1, a2))
                } else {
                    Err(Error::incorrect_statements_args())
                }
            }
            Native(NativePredicate::ProductOf) => {
                if let (StatementArg::Key(a0), StatementArg::Key(a1), StatementArg::Key(a2)) =
                    (args[0].clone(), args[1].clone(), args[2].clone())
                {
                    Ok(Self::ProductOf(a0, a1, a2))
                } else {
                    Err(Error::incorrect_statements_args())
                }
            }
            Native(NativePredicate::MaxOf) => {
                if let (StatementArg::Key(a0), StatementArg::Key(a1), StatementArg::Key(a2)) =
                    (args[0].clone(), args[1].clone(), args[2].clone())
                {
                    Ok(Self::MaxOf(a0, a1, a2))
                } else {
                    Err(Error::incorrect_statements_args())
                }
            }
            Native(np) => Err(Error::custom(format!("Predicate {:?} is syntax sugar", np))),
            BatchSelf(_) => unreachable!(),
            Custom(cpr) => {
                let v_args: Result<Vec<WildcardValue>> = args
                    .iter()
                    .map(|x| match x {
                        StatementArg::WildcardLiteral(v) => Ok(v.clone()),
                        _ => Err(Error::incorrect_statements_args()),
                    })
                    .collect();
                Ok(Self::Custom(cpr, v_args?))
            }
        };
        st
    }
}

impl ToFields for Statement {
    fn to_fields(&self, params: &Params) -> Vec<F> {
        let mut fields = self.predicate().to_fields(params);
        fields.extend(self.args().iter().flat_map(|arg| arg.to_fields(params)));
        fields.resize_with(params.statement_size(), || F::ZERO);
        fields
    }
}

impl fmt::Display for Statement {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}(", self.predicate())?;
        for (i, arg) in self.args().iter().enumerate() {
            if i != 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", arg)?;
        }
        write!(f, ")")
    }
}

/// Statement argument type. Useful for statement decompositions.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum StatementArg {
    None,
    Literal(Value),
    Key(AnchoredKey),
    WildcardLiteral(WildcardValue),
}

impl fmt::Display for StatementArg {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            StatementArg::None => write!(f, "none"),
            StatementArg::Literal(v) => write!(f, "{}", v),
            StatementArg::Key(r) => write!(f, "{}.{}", r.pod_id, r.key),
            StatementArg::WildcardLiteral(v) => write!(f, "{}", v),
        }
    }
}

impl StatementArg {
    pub fn is_none(&self) -> bool {
        matches!(self, Self::None)
    }
    pub fn literal(&self) -> Result<Value> {
        match self {
            Self::Literal(value) => Ok(value.clone()),
            _ => Err(Error::invalid_statement_arg(
                self.clone(),
                "literal".to_string(),
            )),
        }
    }
    pub fn key(&self) -> Result<AnchoredKey> {
        match self {
            Self::Key(ak) => Ok(ak.clone()),
            _ => Err(Error::invalid_statement_arg(
                self.clone(),
                "key".to_string(),
            )),
        }
    }
}

impl ToFields for StatementArg {
    fn to_fields(&self, _params: &Params) -> Vec<F> {
        // NOTE: current version returns always the same amount of field elements in the returned
        // vector, which means that the `None` case is padded with 8 zeroes, and the `Literal` case
        // is padded with 4 zeroes. Since the returned vector will mostly be hashed (and reproduced
        // in-circuit), we might be interested into reducing the length of it. If that's the case,
        // we can check if it makes sense to make it dependant on the concrete StatementArg; that
        // is, when dealing with a `None` it would be a single field element (zero value), and when
        // dealing with `Literal` it would be of length 4.
        let f = match self {
            StatementArg::None => vec![F::ZERO; STATEMENT_ARG_F_LEN],
            StatementArg::Literal(v) => v
                .raw()
                .0
                .into_iter()
                .chain(iter::repeat(F::ZERO).take(STATEMENT_ARG_F_LEN - VALUE_SIZE))
                .collect(),
            StatementArg::Key(ak) => {
                let mut fields = ak.pod_id.to_fields(_params);
                fields.extend(ak.key.to_fields(_params));
                fields
            }
            StatementArg::WildcardLiteral(v) => v
                .raw()
                .0
                .into_iter()
                .chain(iter::repeat(F::ZERO).take(STATEMENT_ARG_F_LEN - VALUE_SIZE))
                .collect(),
        };
        assert_eq!(f.len(), STATEMENT_ARG_F_LEN); // sanity check
        f
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::middleware::hash_str;

    #[test]
    fn test_print_special_keys() {
        let key = hash_str(KEY_SIGNER);
        println!("hash(KEY_SIGNER) = {:?}", key);
        let key = hash_str(KEY_TYPE);
        println!("hash(KEY_TYPE) = {:?}", key);
    }
}
