use std::{fmt, iter};

use plonky2::field::types::Field;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
use strum_macros::FromRepr;

use crate::middleware::{
    AnchoredKey, CustomPredicateRef, Error, Params, Result, ToFields, Value, F, VALUE_SIZE,
};

// TODO: Maybe store KEY_SIGNER and KEY_TYPE as Key with lazy_static
// hash(KEY_SIGNER) = [2145458785152392366, 15113074911296146791, 15323228995597834291, 11804480340100333725]
pub const KEY_SIGNER: &str = "_signer";
// hash(KEY_TYPE) = [17948789436443445142, 12513915140657440811, 15878361618879468769, 938231894693848619]
pub const KEY_TYPE: &str = "_type";
pub const STATEMENT_ARG_F_LEN: usize = 8;
pub const OPERATION_ARG_F_LEN: usize = 1;
pub const OPERATION_AUX_F_LEN: usize = 2;

#[derive(Clone, Copy, Debug, FromRepr, PartialEq, Eq, Hash, Serialize, Deserialize, JsonSchema)]
pub enum NativePredicate {
    None = 0,  // Always true
    False = 1, // Always false
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
                    .chain(batch.id().0)
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
                if f.alternate() {
                    write!(
                        f,
                        "{}.{}:{}",
                        batch.name,
                        index,
                        batch.predicates()[*index].name
                    )
                } else {
                    write!(f, "{}", batch.predicates()[*index].name)
                }
            }
        }
    }
}

/// Type encapsulating statements with their associated arguments.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize, JsonSchema)]
#[serde(tag = "predicate", content = "args")]
pub enum Statement {
    None,
    Equal(ValueRef, ValueRef),
    NotEqual(ValueRef, ValueRef),
    LtEq(ValueRef, ValueRef),
    Lt(ValueRef, ValueRef),
    Contains(
        /* root  */ ValueRef,
        /* key   */ ValueRef,
        /* value */ ValueRef,
    ),
    NotContains(/* root  */ ValueRef, /* key   */ ValueRef),
    SumOf(ValueRef, ValueRef, ValueRef),
    ProductOf(ValueRef, ValueRef, ValueRef),
    MaxOf(ValueRef, ValueRef, ValueRef),
    HashOf(ValueRef, ValueRef, ValueRef),
    Custom(CustomPredicateRef, Vec<Value>),
}

macro_rules! statement_constructor {
    ($var_name: ident, $cons_name: ident, 2) => {
        pub fn $var_name(v1: impl Into<ValueRef>, v2: impl Into<ValueRef>) -> Self {
            Self::$cons_name(v1.into(), v2.into())
        }
    };
    ($var_name: ident, $cons_name: ident, 3) => {
        pub fn $var_name(
            v1: impl Into<ValueRef>,
            v2: impl Into<ValueRef>,
            v3: impl Into<ValueRef>,
        ) -> Self {
            Self::$cons_name(v1.into(), v2.into(), v3.into())
        }
    };
}

impl Statement {
    pub fn is_none(&self) -> bool {
        self == &Self::None
    }
    statement_constructor!(equal, Equal, 2);
    statement_constructor!(not_equal, NotEqual, 2);
    statement_constructor!(lt_eq, LtEq, 2);
    statement_constructor!(lt, Lt, 2);
    statement_constructor!(contains, Contains, 3);
    statement_constructor!(not_contains, NotContains, 2);
    statement_constructor!(sum_of, SumOf, 3);
    statement_constructor!(product_of, ProductOf, 3);
    statement_constructor!(max_of, MaxOf, 3);
    statement_constructor!(hash_of, HashOf, 3);
    pub fn predicate(&self) -> Predicate {
        use Predicate::*;
        match self {
            Self::None => Native(NativePredicate::None),
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
            Self::Equal(ak1, ak2) => vec![ak1.into(), ak2.into()],
            Self::NotEqual(ak1, ak2) => vec![ak1.into(), ak2.into()],
            Self::LtEq(ak1, ak2) => vec![ak1.into(), ak2.into()],
            Self::Lt(ak1, ak2) => vec![ak1.into(), ak2.into()],
            Self::Contains(ak1, ak2, ak3) => vec![ak1.into(), ak2.into(), ak3.into()],
            Self::NotContains(ak1, ak2) => vec![ak1.into(), ak2.into()],
            Self::SumOf(ak1, ak2, ak3) => vec![ak1.into(), ak2.into(), ak3.into()],
            Self::ProductOf(ak1, ak2, ak3) => vec![ak1.into(), ak2.into(), ak3.into()],
            Self::MaxOf(ak1, ak2, ak3) => vec![ak1.into(), ak2.into(), ak3.into()],
            Self::HashOf(ak1, ak2, ak3) => vec![ak1.into(), ak2.into(), ak3.into()],
            Self::Custom(_, args) => Vec::from_iter(args.into_iter().map(Literal)),
        }
    }

    pub fn as_entry(&self) -> Option<(&AnchoredKey, &Value)> {
        if let Self::Equal(ValueRef::Key(k), ValueRef::Literal(v)) = self {
            Some((k, v))
        } else {
            None
        }
    }

    pub fn from_args(pred: Predicate, args: Vec<StatementArg>) -> Result<Self> {
        use Predicate::*;
        let st = match (pred, &args.as_slice()) {
            (Native(NativePredicate::None), &[]) => Self::None,
            (Native(NativePredicate::Equal), &[a1, a2]) => {
                Self::Equal(a1.try_into()?, a2.try_into()?)
            }
            (Native(NativePredicate::NotEqual), &[a1, a2]) => {
                Self::NotEqual(a1.try_into()?, a2.try_into()?)
            }
            (Native(NativePredicate::LtEq), &[a1, a2]) => {
                Self::LtEq(a1.try_into()?, a2.try_into()?)
            }
            (Native(NativePredicate::Lt), &[a1, a2]) => Self::Lt(a1.try_into()?, a2.try_into()?),
            (Native(NativePredicate::Contains), &[a1, a2, a3]) => {
                Self::Contains(a1.try_into()?, a2.try_into()?, a3.try_into()?)
            }
            (Native(NativePredicate::NotContains), &[a1, a2]) => {
                Self::NotContains(a1.try_into()?, a2.try_into()?)
            }
            (Native(NativePredicate::SumOf), &[a1, a2, a3]) => {
                Self::SumOf(a1.try_into()?, a2.try_into()?, a3.try_into()?)
            }
            (Native(NativePredicate::ProductOf), &[a1, a2, a3]) => {
                Self::ProductOf(a1.try_into()?, a2.try_into()?, a3.try_into()?)
            }
            (Native(NativePredicate::MaxOf), &[a1, a2, a3]) => {
                Self::MaxOf(a1.try_into()?, a2.try_into()?, a3.try_into()?)
            }
            (Native(NativePredicate::HashOf), &[a1, a2, a3]) => {
                Self::HashOf(a1.try_into()?, a2.try_into()?, a3.try_into()?)
            }

            (Native(np), _) => {
                return Err(Error::custom(format!("Predicate {:?} is syntax sugar", np)))
            }
            (BatchSelf(_), _) => unreachable!(),
            (Custom(cpr), _) => {
                let v_args: Result<Vec<Value>> = args
                    .iter()
                    .map(|x| match x {
                        StatementArg::Literal(v) => Ok(v.clone()),
                        _ => Err(Error::incorrect_statements_args()),
                    })
                    .collect();
                Self::Custom(cpr, v_args?)
            }
        };
        Ok(st)
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
}

impl fmt::Display for StatementArg {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            StatementArg::None => write!(f, "none"),
            StatementArg::Literal(v) => v.fmt(f),
            StatementArg::Key(r) => r.fmt(f),
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
    /// Encoding:
    /// - None => [0, 0, 0, 0, 0, 0, 0, 0]
    /// - Literal(v) => [[v], 0, 0, 0, 0]
    /// - Key(pod_id, key) => [[pod_id], [key]]
    /// - WildcardLiteral(v) => [[v], 0, 0, 0, 0]
    fn to_fields(&self, params: &Params) -> Vec<F> {
        // NOTE for @ax0: I removed the old comment because may `to_fields` implementations do
        // padding and we need fixed output length for the circuits.
        let f = match self {
            StatementArg::None => vec![F::ZERO; STATEMENT_ARG_F_LEN],
            StatementArg::Literal(v) => v
                .raw()
                .0
                .into_iter()
                .chain(iter::repeat(F::ZERO).take(STATEMENT_ARG_F_LEN - VALUE_SIZE))
                .collect(),
            StatementArg::Key(ak) => {
                let mut fields = ak.pod_id.to_fields(params);
                fields.extend(ak.key.to_fields(params));
                fields
            }
        };
        assert_eq!(f.len(), STATEMENT_ARG_F_LEN); // sanity check
        f
    }
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize, JsonSchema)]
pub enum ValueRef {
    Literal(Value),
    Key(AnchoredKey),
}

impl From<ValueRef> for StatementArg {
    fn from(value: ValueRef) -> Self {
        match value {
            ValueRef::Literal(v) => StatementArg::Literal(v),
            ValueRef::Key(v) => StatementArg::Key(v),
        }
    }
}

impl TryFrom<StatementArg> for ValueRef {
    type Error = crate::middleware::Error;
    fn try_from(value: StatementArg) -> std::result::Result<Self, Self::Error> {
        match value {
            StatementArg::Literal(v) => Ok(Self::Literal(v)),
            StatementArg::Key(k) => Ok(Self::Key(k)),
            _ => Err(Self::Error::invalid_statement_arg(
                value,
                "literal or key".to_string(),
            )),
        }
    }
}

impl TryFrom<&StatementArg> for ValueRef {
    type Error = crate::middleware::Error;
    fn try_from(value: &StatementArg) -> std::result::Result<Self, Self::Error> {
        value.clone().try_into()
    }
}

impl From<AnchoredKey> for ValueRef {
    fn from(value: AnchoredKey) -> Self {
        Self::Key(value)
    }
}

impl<T> From<T> for ValueRef
where
    T: Into<Value>,
{
    fn from(value: T) -> Self {
        Self::Literal(value.into())
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
