use std::fmt;

use crate::{
    frontend::SignedDict,
    middleware::{
        containers::Dictionary, root_key_to_ak, CustomPredicateRef, NativeOperation, OperationAux,
        OperationType, Signature, Statement, TypedValue, Value, ValueRef,
    },
};

#[derive(Clone, Debug, PartialEq)]
pub enum OperationArg {
    Statement(Statement),
    Literal(Value),
    Entry(String, Value),
}

impl OperationArg {
    /// Extracts the value underlying literal and `Contains` statement
    /// operation args.
    pub(crate) fn value(&self) -> Option<&Value> {
        match self {
            Self::Literal(v) => Some(v),
            Self::Statement(Statement::Contains(_, _, ValueRef::Literal(v))) => Some(v),
            _ => None,
        }
    }

    pub(crate) fn value_and_ref(&self) -> Option<(ValueRef, &Value)> {
        match self {
            Self::Literal(v) => Some((ValueRef::Literal(v.clone()), v)),
            Self::Statement(Statement::Contains(
                ValueRef::Literal(root),
                ValueRef::Literal(key),
                ValueRef::Literal(v),
            )) => root_key_to_ak(root, key).map(|ak| (ValueRef::Key(ak), v)),
            _ => None,
        }
    }

    pub(crate) fn int_value_and_ref(&self) -> Option<(ValueRef, i64)> {
        self.value_and_ref().and_then(|(r, v)| match v.typed() {
            &TypedValue::Int(i) => Some((r, i)),
            _ => None,
        })
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

impl<V: Into<Value>> From<V> for OperationArg {
    fn from(value: V) -> Self {
        Self::Literal(value.into())
    }
}

impl From<&Value> for OperationArg {
    fn from(v: &Value) -> Self {
        Self::Literal(v.clone())
    }
}

impl From<(&Dictionary, &str)> for OperationArg {
    fn from((dict, key): (&Dictionary, &str)) -> Self {
        // TODO: Use TryFrom
        let value = dict.get(&key.into()).cloned().unwrap();
        Self::Statement(Statement::Contains(
            dict.clone().into(),
            key.into(),
            value.into(),
        ))
    }
}

impl From<(&SignedDict, &str)> for OperationArg {
    fn from((signed_dict, key): (&SignedDict, &str)) -> Self {
        OperationArg::from((&signed_dict.dict, key))
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

    ($fn_name: ident, $op_name: ident, 4) => {
        pub fn $fn_name(
            a1: impl Into<OperationArg>,
            a2: impl Into<OperationArg>,
            a3: impl Into<OperationArg>,
            a4: impl Into<OperationArg>,
        ) -> Self {
            Self(
                OperationType::Native(NativeOperation::$op_name),
                vec![a1.into(), a2.into(), a3.into(), a4.into()],
                OperationAux::None,
            )
        }
    };
}

macro_rules! op_impl_st {
    ($fn_name: ident, $op_name: ident, 1) => {
        pub fn $fn_name(a1: Statement) -> Self {
            Self(
                OperationType::Native(NativeOperation::$op_name),
                vec![a1.into()],
                OperationAux::None,
            )
        }
    };

    ($fn_name: ident, $op_name: ident, 2) => {
        pub fn $fn_name(a1: Statement, a2: Statement) -> Self {
            Self(
                OperationType::Native(NativeOperation::$op_name),
                vec![a1.into(), a2.into()],
                OperationAux::None,
            )
        }
    };
}

impl Operation {
    op_impl_oa!(eq, EqualFromEntries, 2);
    op_impl_oa!(ne, NotEqualFromEntries, 2);
    op_impl_oa!(gt_eq, GtEqFromEntries, 2);
    op_impl_oa!(gt, GtFromEntries, 2);
    op_impl_oa!(lt_eq, LtEqFromEntries, 2);
    op_impl_oa!(lt, LtFromEntries, 2);
    op_impl_st!(copy, CopyStatement, 1);
    op_impl_st!(transitive_eq, TransitiveEqualFromStatements, 2);
    op_impl_st!(lt_to_ne, LtToNotEqual, 1);
    op_impl_st!(gt_to_ne, GtToNotEqual, 1);
    op_impl_oa!(sum_of, SumOf, 3);
    op_impl_oa!(product_of, ProductOf, 3);
    op_impl_oa!(max_of, MaxOf, 3);
    op_impl_oa!(hash_of, HashOf, 3);
    /// Creates a custom operation.
    ///
    /// `args` should contain the statements that are needed to prove the
    /// custom statement.  It should have the same length as
    /// `cpr.predicate().statements()`.  If `cpr` refers to an `or` predicate,
    /// then all but one of the statements should be `Statement::None`.
    pub fn custom(cpr: CustomPredicateRef, args: impl IntoIterator<Item = Statement>) -> Self {
        let op_args = args.into_iter().map(OperationArg::from).collect();
        Self(OperationType::Custom(cpr), op_args, OperationAux::None)
    }
    op_impl_oa!(dict_contains, DictContainsFromEntries, 3);
    op_impl_oa!(dict_not_contains, DictNotContainsFromEntries, 2);
    op_impl_oa!(set_contains, SetContainsFromEntries, 2);
    op_impl_oa!(set_not_contains, SetNotContainsFromEntries, 2);
    op_impl_oa!(array_contains, ArrayContainsFromEntries, 3);
    op_impl_oa!(public_key_of, PublicKeyOf, 2);
    op_impl_oa!(dict_insert, DictInsertFromEntries, 4);
    op_impl_oa!(dict_update, DictUpdateFromEntries, 4);
    op_impl_oa!(dict_delete, DictDeleteFromEntries, 3);
    op_impl_oa!(set_insert, SetInsertFromEntries, 3);
    op_impl_oa!(set_delete, SetDeleteFromEntries, 3);
    op_impl_oa!(array_update, ArrayUpdateFromEntries, 4);
    pub fn signed_by(
        msg: impl Into<OperationArg>,
        pk: impl Into<OperationArg>,
        sig: Signature,
    ) -> Self {
        Self(
            OperationType::Native(NativeOperation::SignedBy),
            vec![msg.into(), pk.into()],
            OperationAux::Signature(sig),
        )
    }
    pub fn dict_signed_by(signed_dict: &SignedDict) -> Self {
        Self::signed_by(
            Value::from(signed_dict.dict.clone()),
            Value::from(signed_dict.public_key),
            signed_dict.signature.clone(),
        )
    }
}
