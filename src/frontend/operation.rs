use std::{fmt, iter};

use crate::{
    frontend::{Error, Result, SignedDict},
    middleware::{
        containers::{Array, Dictionary},
        root_key_to_ak, CustomPredicateRef, NativeOperation, OperationAux, OperationType,
        Signature, Statement, Value, ValueRef, BASE_PARAMS,
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
        self.value_and_ref()
            .and_then(|(r, v)| v.as_int().map(|i| Some((r, i))))
            .flatten()
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

impl TryFrom<(&Dictionary, &str)> for OperationArg {
    type Error = Error;

    fn try_from((dict, key): (&Dictionary, &str)) -> Result<Self> {
        let value = dict
            .get(&key.into())?
            .ok_or_else(|| Error::custom(format!("key {key:?} not found in dictionary")))?;
        Ok(Self::Statement(Statement::Contains(
            dict.clone().into(),
            key.into(),
            value.into(),
        )))
    }
}

impl TryFrom<(&Array, i64)> for OperationArg {
    type Error = Error;

    fn try_from((array, index): (&Array, i64)) -> Result<Self> {
        let array_index = usize::try_from(index)
            .map_err(|_| Error::custom(format!("array index {index} is negative")))?;
        let value = array
            .get(array_index)?
            .ok_or_else(|| Error::custom(format!("index {index} not found in array")))?;
        Ok(Self::Statement(Statement::Contains(
            array.clone().into(),
            Value::from(index).into(),
            value.into(),
        )))
    }
}

impl TryFrom<(&SignedDict, &str)> for OperationArg {
    type Error = Error;

    fn try_from((signed_dict, key): (&SignedDict, &str)) -> Result<Self> {
        Self::try_from((&signed_dict.dict, key))
    }
}

/// Convert a container entry into a resolved operation argument.
pub fn entry<C, K>(container: C, key: K) -> Result<OperationArg>
where
    OperationArg: TryFrom<(C, K), Error = Error>,
{
    OperationArg::try_from((container, key))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dict;

    #[test]
    fn missing_dictionary_entry_returns_error() {
        let dictionary = dict!({"present" => 1});

        entry(&dictionary, "missing").expect_err("missing dictionary key should be rejected");
    }

    #[test]
    fn invalid_array_index_returns_error() {
        let array = Array::new(vec![Value::from(1)]);

        entry(&array, -1).expect_err("negative array index should be rejected");
        entry(&array, 1).expect_err("missing array index should be rejected");
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
    op_impl_st!(transitive_eq, TransitiveEqualFromStatements, 2);
    op_impl_st!(lt_to_ne, LtToNotEqual, 1);
    op_impl_st!(gt_to_ne, GtToNotEqual, 1);
    op_impl_oa!(sum, SumFromEntries, 3);
    op_impl_oa!(product, ProductFromEntries, 3);
    op_impl_oa!(max, MaxFromEntries, 3);
    op_impl_oa!(hash, HashFromEntries, 3);
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
    op_impl_oa!(public_key, PublicKeyFromEntries, 2);
    op_impl_oa!(dict_insert, DictInsertFromEntries, 4);
    op_impl_oa!(dict_update, DictUpdateFromEntries, 4);
    op_impl_oa!(dict_delete, DictDeleteFromEntries, 3);
    op_impl_oa!(set_insert, SetInsertFromEntries, 3);
    op_impl_oa!(set_delete, SetDeleteFromEntries, 3);
    op_impl_oa!(array_update, ArrayUpdateFromEntries, 4);
    pub fn replace_value_with_entry<E: Into<OperationArg>>(
        args: Vec<Option<E>>,
        st: Statement,
    ) -> Self {
        assert!(args.len() <= BASE_PARAMS.max_statement_args);
        let args = args
            .into_iter()
            .map(|a| match a {
                None => OperationArg::Statement(Statement::None),
                Some(entry) => entry.into(),
            })
            .chain(iter::repeat_with(|| {
                OperationArg::Statement(Statement::None)
            }))
            .take(BASE_PARAMS.max_statement_args)
            .chain(iter::once(OperationArg::Statement(st)))
            .collect();
        Self(
            OperationType::Native(NativeOperation::ReplaceValueWithEntry),
            args,
            OperationAux::None,
        )
    }
    pub fn signed_by(
        msg: impl Into<OperationArg>,
        pk: impl Into<OperationArg>,
        sig: Signature,
    ) -> Self {
        Self(
            OperationType::Native(NativeOperation::SignedByFromEntries),
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
