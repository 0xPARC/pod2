use std::fmt;

use crate::{
    frontend::{MainPod, SignedPod},
    middleware::{
        AnchoredKey, CustomPredicateRef, NativeOperation, OperationAux, OperationType, Statement,
        Value, ValueRef,
    },
};

#[derive(Clone, Debug, PartialEq)]
pub enum OperationArg {
    Statement(Statement),
    Literal(Value),
    Entry(String, Value),
}

impl OperationArg {
    /// Extracts the value underlying literal and `ValueOf` statement
    /// operation args.
    pub(crate) fn value(&self) -> Option<&Value> {
        match self {
            Self::Literal(v) => Some(v),
            Self::Statement(Statement::Equal(_, ValueRef::Literal(v))) => Some(v),
            _ => None,
        }
    }

    pub(crate) fn value_and_ref(&self) -> Option<(ValueRef, &Value)> {
        match self {
            Self::Literal(v) => Some((ValueRef::Literal(v.clone()), v)),
            Self::Statement(Statement::Equal(k, ValueRef::Literal(v))) => Some((k.clone(), v)),
            _ => None,
        }
    }
}

impl fmt::Display for OperationArg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            OperationArg::Statement(s) => write!(f, "{}", s),
            OperationArg::Literal(v) => write!(f, "{}", v),
            OperationArg::Entry(k, v) => write!(f, "({}, {})", k, v),
        }
    }
}

impl From<Value> for OperationArg {
    fn from(v: Value) -> Self {
        Self::Literal(v)
    }
}

impl From<&Value> for OperationArg {
    fn from(v: &Value) -> Self {
        Self::Literal(v.clone())
    }
}

impl From<&str> for OperationArg {
    fn from(s: &str) -> Self {
        Self::Literal(Value::from(s))
    }
}

impl From<i64> for OperationArg {
    fn from(v: i64) -> Self {
        Self::Literal(Value::from(v))
    }
}

impl From<bool> for OperationArg {
    fn from(b: bool) -> Self {
        Self::Literal(Value::from(b))
    }
}

impl From<(&SignedPod, &str)> for OperationArg {
    fn from((pod, key): (&SignedPod, &str)) -> Self {
        // TODO: TryFrom.
        let value = pod
            .kvs()
            .get(&key.into())
            .cloned()
            .unwrap_or_else(|| panic!("Key {} is not present in POD: {}", key, pod));
        Self::Statement(Statement::Equal(
            AnchoredKey::from((pod.id(), key)).into(),
            value.into(),
        ))
    }
}
impl From<(&MainPod, &str)> for OperationArg {
    fn from((pod, key): (&MainPod, &str)) -> Self {
        // TODO: TryFrom.
        let value = pod
            .get(key)
            .unwrap_or_else(|| panic!("Key {} is not present in POD: {}", key, pod));
        Self::Statement(Statement::equal(AnchoredKey::from((pod.id(), key)), value))
    }
}

impl From<Statement> for OperationArg {
    fn from(s: Statement) -> Self {
        Self::Statement(s)
    }
}

impl From<&Statement> for OperationArg {
    fn from(value: &Statement) -> Self {
        value.clone().into()
    }
}

impl<V: Into<Value>> From<(&str, V)> for OperationArg {
    fn from((key, value): (&str, V)) -> Self {
        Self::Entry(key.to_string(), value.into())
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Operation(pub OperationType, pub Vec<OperationArg>, pub OperationAux);

impl fmt::Display for Operation {
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

macro_rules! op_impl_oa {
    ($fn_name: ident, $op_name: ident, 2) => {
        pub fn $fn_name(a1: impl Into<OperationArg>, a2: impl Into<OperationArg>) -> Self {
            Self(
                OperationType::Native(NativeOperation::$op_name),
                vec![a1.into(), a2.into()],
                OperationAux::None,
            )
        }
    };

    ($fn_name: ident, $op_name: ident, 3) => {
        pub fn $fn_name(
            a1: impl Into<OperationArg>,
            a2: impl Into<OperationArg>,
            a3: impl Into<OperationArg>,
        ) -> Self {
            Self(
                OperationType::Native(NativeOperation::$op_name),
                vec![a1.into(), a2.into(), a3.into()],
                OperationAux::None,
            )
        }
    };
}

macro_rules! op_impl_st {
    ($fn_name: ident, $op_name: ident, 1) => {
        pub fn $fn_name(a1: &Statement) -> Self {
            Self(
                OperationType::Native(NativeOperation::$op_name),
                vec![a1.into()],
                OperationAux::None,
            )
        }
    };

    ($fn_name: ident, $op_name: ident, 2) => {
        pub fn $fn_name(a1: &Statement, a2: &Statement) -> Self {
            Self(
                OperationType::Native(NativeOperation::$op_name),
                vec![a1.into(), a2.into()],
                OperationAux::None,
            )
        }
    };
}

impl Operation {
    pub fn new_entry(a1: impl Into<OperationArg>, a2: impl Into<Value>) -> Self {
        Self(
            OperationType::Native(NativeOperation::NewEntry),
            vec![a1.into(), a2.into().into()],
            OperationAux::None,
        )
    }
    op_impl_oa!(eq, EqualFromEntries, 2);
    op_impl_oa!(ne, NotEqualFromEntries, 2);
    op_impl_oa!(gt, GtFromEntries, 2);
    op_impl_oa!(lt, LtFromEntries, 2);
    op_impl_st!(transitive_eq, TransitiveEqualFromStatements, 2);
    op_impl_st!(gt_to_ne, GtToNotEqual, 1);
    op_impl_oa!(sum_of, SumOf, 3);
    op_impl_oa!(product_of, ProductOf, 3);
    op_impl_oa!(max_of, MaxOf, 3);
    pub fn custom(cpr: CustomPredicateRef, args: Vec<OperationArg>) -> Self {
        Self(OperationType::Custom(cpr), args, OperationAux::None)
    }
    op_impl_oa!(dict_contains, DictContainsFromEntries, 3);
    op_impl_oa!(dict_not_contains, DictNotContainsFromEntries, 2);
    op_impl_oa!(set_contains, SetContainsFromEntries, 3);
    op_impl_oa!(set_not_contains, SetNotContainsFromEntries, 2);
    op_impl_oa!(array_contains, ArrayContainsFromEntries, 3);
}
