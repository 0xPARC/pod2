use std::{
    fmt::{self, Display},
    iter,
    str::FromStr,
};

use plonky2::field::types::Field;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
use strum_macros::FromRepr;

use crate::middleware::{
    self, hash_fields, AnchoredKey, CustomPredicateRef, Error, Params, Result, ToFields, Value, F,
    VALUE_SIZE,
};

pub const STATEMENT_ARG_F_LEN: usize = 8;

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
    PublicKeyOf = 12,
    SignedBy = 13,
    ContainerInsert = 14,
    ContainerUpdate = 15,
    ContainerDelete = 16,

    // Syntactic sugar predicates.  These predicates are not supported by the backend.  The
    // frontend compiler is responsible of translating these predicates into the predicates above.
    DictContains = 1000,
    DictNotContains = 1001,
    SetContains = 1002,
    SetNotContains = 1003,
    ArrayContains = 1004, // there is no ArrayNotContains
    GtEq = 1005,
    Gt = 1006,
    DictInsert = 1009,
    DictUpdate = 1010,
    DictDelete = 1011,
    SetInsert = 1012,
    SetDelete = 1013,
    ArrayUpdate = 1014,
}

impl NativePredicate {
    pub fn arity(&self) -> usize {
        match self {
            NativePredicate::None | NativePredicate::False => 0,
            NativePredicate::Equal
            | NativePredicate::NotEqual
            | NativePredicate::Lt
            | NativePredicate::Gt
            | NativePredicate::GtEq
            | NativePredicate::LtEq
            | NativePredicate::NotContains
            | NativePredicate::SetNotContains
            | NativePredicate::DictNotContains
            | NativePredicate::PublicKeyOf
            | NativePredicate::SignedBy
            | NativePredicate::SetContains => 2,
            NativePredicate::Contains
            | NativePredicate::DictContains
            | NativePredicate::ArrayContains
            | NativePredicate::SumOf
            | NativePredicate::ProductOf
            | NativePredicate::MaxOf
            | NativePredicate::HashOf
            | NativePredicate::SetInsert
            | NativePredicate::SetDelete => 3,
            NativePredicate::DictInsert
            | NativePredicate::DictUpdate
            | NativePredicate::DictDelete
            | NativePredicate::ArrayUpdate
            | NativePredicate::ContainerInsert
            | NativePredicate::ContainerUpdate
            | NativePredicate::ContainerDelete => 4,
        }
    }
}

impl Display for NativePredicate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            NativePredicate::None => "None",
            NativePredicate::False => "False",
            NativePredicate::Equal => "Equal",
            NativePredicate::NotEqual => "NotEqual",
            NativePredicate::Lt => "Lt",
            NativePredicate::LtEq => "LtEq",
            NativePredicate::Gt => "Gt",
            NativePredicate::GtEq => "GtEq",
            NativePredicate::Contains => "Contains",
            NativePredicate::NotContains => "NotContains",
            NativePredicate::SumOf => "SumOf",
            NativePredicate::ProductOf => "ProductOf",
            NativePredicate::MaxOf => "MaxOf",
            NativePredicate::HashOf => "HashOf",
            NativePredicate::PublicKeyOf => "PublicKeyOf",
            NativePredicate::SignedBy => "SignedBy",
            NativePredicate::ContainerInsert => "ContainerInsert",
            NativePredicate::ContainerUpdate => "ContainerUpdate",
            NativePredicate::ContainerDelete => "ContainerDelete",
            NativePredicate::DictContains => "DictContains",
            NativePredicate::DictNotContains => "DictNotContains",
            NativePredicate::ArrayContains => "ArrayContains",
            NativePredicate::SetContains => "SetContains",
            NativePredicate::SetNotContains => "SetNotContains",
            NativePredicate::DictInsert => "DictInsert",
            NativePredicate::DictUpdate => "DictUpdate",
            NativePredicate::DictDelete => "DictDelete",
            NativePredicate::SetInsert => "SetInsert",
            NativePredicate::SetDelete => "SetDelete",
            NativePredicate::ArrayUpdate => "ArrayUpdate",
        };
        write!(f, "{}", s)
    }
}

impl ToFields for NativePredicate {
    fn to_fields(&self, _params: &Params) -> Vec<F> {
        vec![F::from_canonical_u64(*self as u64)]
    }
}

impl FromStr for NativePredicate {
    type Err = Error;
    fn from_str(s: &str) -> Result<Self> {
        match s {
            "Equal" => Ok(NativePredicate::Equal),
            "NotEqual" => Ok(NativePredicate::NotEqual),
            "Gt" => Ok(NativePredicate::Gt),
            "GtEq" => Ok(NativePredicate::GtEq),
            "Lt" => Ok(NativePredicate::Lt),
            "LtEq" => Ok(NativePredicate::LtEq),
            "Contains" => Ok(NativePredicate::Contains),
            "NotContains" => Ok(NativePredicate::NotContains),
            "SumOf" => Ok(NativePredicate::SumOf),
            "ProductOf" => Ok(NativePredicate::ProductOf),
            "MaxOf" => Ok(NativePredicate::MaxOf),
            "HashOf" => Ok(NativePredicate::HashOf),
            "PublicKeyOf" => Ok(NativePredicate::PublicKeyOf),
            "SignedBy" => Ok(NativePredicate::SignedBy),
            "ContainerInsert" => Ok(NativePredicate::ContainerInsert),
            "ContainerUpdate" => Ok(NativePredicate::ContainerUpdate),
            "ContainerDelete" => Ok(NativePredicate::ContainerDelete),
            "DictContains" => Ok(NativePredicate::DictContains),
            "DictNotContains" => Ok(NativePredicate::DictNotContains),
            "ArrayContains" => Ok(NativePredicate::ArrayContains),
            "SetContains" => Ok(NativePredicate::SetContains),
            "SetNotContains" => Ok(NativePredicate::SetNotContains),
            "DictInsert" => Ok(NativePredicate::DictInsert),
            "DictUpdate" => Ok(NativePredicate::DictUpdate),
            "DictDelete" => Ok(NativePredicate::DictDelete),
            "SetInsert" => Ok(NativePredicate::SetInsert),
            "SetDelete" => Ok(NativePredicate::SetDelete),
            "ArrayUpdate" => Ok(NativePredicate::ArrayUpdate),
            "None" => Ok(NativePredicate::None),
            "False" => Ok(NativePredicate::False),
            _ => Err(Error::custom(format!("Invalid native predicate: {}", s))),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize, JsonSchema)]
pub struct IntroPredicateRef {
    pub name: String,
    pub args_len: usize,
    pub verifier_data_hash: middleware::Hash,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize, JsonSchema)]
#[serde(tag = "type", content = "value")]
pub enum Predicate {
    Native(NativePredicate),
    BatchSelf(usize),
    Custom(CustomPredicateRef),
    Intro(IntroPredicateRef),
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
    Intro = 4,
}

impl From<PredicatePrefix> for F {
    fn from(prefix: PredicatePrefix) -> Self {
        Self::from_canonical_usize(prefix as usize)
    }
}

impl ToFields for Predicate {
    fn to_fields(&self, params: &Params) -> Vec<F> {
        // serialize:
        // NativePredicate(id) as (1, id, 0...) -- id: usize
        // BatchSelf(i) as (2, i, 0...) -- i: usize
        // CustomPredicateRef(pb, i) as
        // (3, [hash of pb], i, 0...) -- pb hashes to 4 field elements
        //                            -- i: usize
        // IntroPredicateRef(vd_hash) as
        // (4, [vd_hash], 0...)

        // in every case: pad to `Params::predicate_size()` field elements
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
            Self::Intro(IntroPredicateRef {
                verifier_data_hash, ..
            }) => iter::once(F::from(PredicatePrefix::Intro))
                .chain(verifier_data_hash.0)
                .collect(),
        };
        fields.resize_with(Params::predicate_size(), || F::from_canonical_u64(0));
        fields
    }
}

impl Predicate {
    pub fn hash(&self, params: &Params) -> middleware::Hash {
        hash_fields(&self.to_fields(params))
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
            Self::Intro(IntroPredicateRef { name, .. }) => write!(f, "{}", name),
        }
    }
}

/// Type encapsulating statements with their associated arguments.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize, JsonSchema)]
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
    PublicKeyOf(ValueRef, ValueRef),
    SignedBy(ValueRef, ValueRef),
    ContainerInsert(
        /* new_root */ ValueRef,
        /* old_root */ ValueRef,
        /*   key    */ ValueRef,
        /*  value   */ ValueRef,
    ),
    ContainerUpdate(
        /* new_root */ ValueRef,
        /* old_root */ ValueRef,
        /*   key    */ ValueRef,
        /*  value   */ ValueRef,
    ),
    ContainerDelete(
        /* new_root */ ValueRef,
        /* old_root */ ValueRef,
        /*   key    */ ValueRef,
    ),
    Custom(CustomPredicateRef, Vec<Value>),
    Intro(IntroPredicateRef, Vec<Value>),
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
    ($var_name: ident, $cons_name: ident, 4) => {
        pub fn $var_name(
            v1: impl Into<ValueRef>,
            v2: impl Into<ValueRef>,
            v3: impl Into<ValueRef>,
            v4: impl Into<ValueRef>,
        ) -> Self {
            Self::$cons_name(v1.into(), v2.into(), v3.into(), v4.into())
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
    statement_constructor!(public_key_of, PublicKeyOf, 2);
    statement_constructor!(signed_by, SignedBy, 2);
    statement_constructor!(insert, ContainerInsert, 4);
    statement_constructor!(update, ContainerUpdate, 4);
    statement_constructor!(delete, ContainerDelete, 3);
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
            Self::PublicKeyOf(_, _) => Native(NativePredicate::PublicKeyOf),
            Self::SignedBy(_, _) => Native(NativePredicate::SignedBy),
            Self::ContainerInsert(_, _, _, _) => Native(NativePredicate::ContainerInsert),
            Self::ContainerUpdate(_, _, _, _) => Native(NativePredicate::ContainerUpdate),
            Self::ContainerDelete(_, _, _) => Native(NativePredicate::ContainerDelete),
            Self::Custom(cpr, _) => Custom(cpr.clone()),
            Self::Intro(ir, _) => Intro(ir.clone()),
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
            Self::PublicKeyOf(ak1, ak2) => vec![ak1.into(), ak2.into()],
            Self::SignedBy(ak1, ak2) => vec![ak1.into(), ak2.into()],
            Self::ContainerInsert(ak1, ak2, ak3, ak4) => {
                vec![ak1.into(), ak2.into(), ak3.into(), ak4.into()]
            }
            Self::ContainerUpdate(ak1, ak2, ak3, ak4) => {
                vec![ak1.into(), ak2.into(), ak3.into(), ak4.into()]
            }
            Self::ContainerDelete(ak1, ak2, ak3) => vec![ak1.into(), ak2.into(), ak3.into()],
            Self::Custom(_, args) => Vec::from_iter(args.into_iter().map(Literal)),
            Self::Intro(_, args) => Vec::from_iter(args.into_iter().map(Literal)),
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
            (Native(NativePredicate::PublicKeyOf), &[a1, a2]) => {
                Self::PublicKeyOf(a1.try_into()?, a2.try_into()?)
            }
            (Native(NativePredicate::SignedBy), &[a1, a2]) => {
                Self::SignedBy(a1.try_into()?, a2.try_into()?)
            }
            (Native(NativePredicate::ContainerInsert), &[a1, a2, a3, a4]) => Self::ContainerInsert(
                a1.try_into()?,
                a2.try_into()?,
                a3.try_into()?,
                a4.try_into()?,
            ),
            (Native(NativePredicate::ContainerUpdate), &[a1, a2, a3, a4]) => Self::ContainerUpdate(
                a1.try_into()?,
                a2.try_into()?,
                a3.try_into()?,
                a4.try_into()?,
            ),
            (Native(NativePredicate::ContainerDelete), &[a1, a2, a3]) => {
                Self::ContainerDelete(a1.try_into()?, a2.try_into()?, a3.try_into()?)
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
            (Intro(ir), _) => {
                let v_args: Result<Vec<Value>> = args
                    .iter()
                    .map(|x| match x {
                        StatementArg::Literal(v) => Ok(v.clone()),
                        _ => Err(Error::incorrect_statements_args()),
                    })
                    .collect();
                Self::Intro(ir, v_args?)
            }
        };
        Ok(st)
    }
}

impl ToFields for Statement {
    fn to_fields(&self, params: &Params) -> Vec<F> {
        let predicate_hash = hash_fields(&self.predicate().to_fields(params));
        let mut fields = predicate_hash.0.to_vec();
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
    /// - None => `[0, 0, 0, 0, 0, 0, 0, 0]`
    /// - Literal(v) => `[[v], 0, 0, 0, 0]`
    /// - Key(root, key) => `[[root], [key]]`
    /// - WildcardLiteral(v) => `[[v], 0, 0, 0, 0]`
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
                let mut fields = ak.root.to_fields(params);
                fields.extend(ak.key.to_fields(params));
                fields
            }
        };
        assert_eq!(f.len(), STATEMENT_ARG_F_LEN); // sanity check
        f
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize, JsonSchema)]
#[serde(tag = "type", content = "value")]
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
