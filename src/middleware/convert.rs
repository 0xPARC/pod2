use std::collections::{HashMap, HashSet};

use crate::{
    backends::plonky2::primitives::ec::{curve::Point, schnorr::SecretKey},
    middleware::{
        containers::{Array, Dictionary, Set},
        value_is_not, Error, Key, Params, RawValue, Result, TypedValue, Value,
    },
};

pub fn try_from_array<C, T>(v: &TypedValue) -> Result<C>
where
    C: FromIterator<T>,
    T: for<'a> TryFrom<&'a TypedValue>,
    for<'a> Error: From<<T as TryFrom<&'a TypedValue>>::Error>,
{
    match v {
        TypedValue::Array(a) => a
            .array()
            .iter()
            .map(|x| T::try_from(x.typed()).map_err(Error::from))
            .collect(),
        _ => value_is_not(v, "an array"),
    }
}

pub fn try_from_set<C, T>(v: &TypedValue) -> Result<C>
where
    C: FromIterator<T>,
    T: for<'a> TryFrom<&'a TypedValue>,
    for<'a> Error: From<<T as TryFrom<&'a TypedValue>>::Error>,
{
    match v {
        TypedValue::Set(s) => s
            .set()
            .iter()
            .map(|x| T::try_from(x.typed()).map_err(Error::from))
            .collect(),
        _ => value_is_not(v, "a set"),
    }
}

pub fn try_from_dict<C, K, V>(v: &TypedValue) -> Result<C>
where
    C: FromIterator<(K, V)>,
    K: TryFrom<String>,
    V: for<'a> TryFrom<&'a TypedValue>,
    Error: From<<K as TryFrom<String>>::Error>,
    for<'a> Error: From<<V as TryFrom<&'a TypedValue>>::Error>,
{
    match v {
        TypedValue::Dictionary(d) => d
            .kvs()
            .iter()
            .map(|(k, v)| Ok((K::try_from(k.name.clone())?, V::try_from(v.typed())?)))
            .collect(),
        _ => value_is_not(v, "a dictionary"),
    }
}

pub trait TryIntoValue {
    type Error;
    fn try_into_value(self, params: &Params) -> std::result::Result<Value, Self::Error>;
}

pub fn try_into_array<C>(c: C, params: &Params) -> Result<Value, Error>
where
    C: IntoIterator,
    C::Item: TryIntoValue,
    Error: From<<C::Item as TryIntoValue>::Error>,
{
    let r: Result<Vec<Value>, <C::Item as TryIntoValue>::Error> =
        c.into_iter().map(|x| x.try_into_value(params)).collect();
    let arr = Array::new(params.max_depth_mt_containers, r?)?;
    Ok(Value::from(arr))
}

pub fn try_into_set<C>(c: C, params: &Params) -> Result<Value, Error>
where
    C: IntoIterator,
    C::Item: TryIntoValue,
    Error: From<<C::Item as TryIntoValue>::Error>,
{
    let r: Result<HashSet<Value>, <C::Item as TryIntoValue>::Error> =
        c.into_iter().map(|x| x.try_into_value(params)).collect();
    let set = Set::new(params.max_depth_mt_containers, r?)?;
    Ok(Value::from(set))
}

pub fn try_into_dict<C, K, V>(c: C, params: &Params) -> Result<Value, Error>
where
    C: IntoIterator<Item = (K, V)>,
    K: Into<String>,
    V: TryIntoValue,
    Error: From<V::Error>,
{
    let r: Result<HashMap<Key, Value>, V::Error> = c
        .into_iter()
        .map(|(k, v)| Ok((Key::from(k.into()), v.try_into_value(params)?)))
        .collect();
    let dict = Dictionary::new(params.max_depth_mt_containers, r?)?;
    Ok(Value::from(dict))
}

#[macro_export]
macro_rules! try_into_using_value_from {
    ($t: ty) => {
        impl $crate::middleware::convert::TryIntoValue for $t {
            type Error = core::convert::Infallible;
            fn try_into_value(
                self,
                _params: &$crate::middleware::Params,
            ) -> std::result::Result<$crate::middleware::Value, Self::Error> {
                Ok($crate::middleware::Value::from(self))
            }
        }
    };
}

try_into_using_value_from!(bool);
try_into_using_value_from!(i64);
try_into_using_value_from!(Array);
try_into_using_value_from!(Dictionary);
try_into_using_value_from!(Point);
try_into_using_value_from!(RawValue);
try_into_using_value_from!(Set);
try_into_using_value_from!(SecretKey);
try_into_using_value_from!(String);

impl<T> TryIntoValue for Vec<T>
where
    T: TryIntoValue,
    Error: From<T::Error>,
{
    type Error = Error;
    fn try_into_value(self, params: &Params) -> std::result::Result<Value, Self::Error> {
        try_into_array(self, params)
    }
}

impl<T> TryIntoValue for HashSet<T>
where
    T: TryIntoValue,
    Error: From<T::Error>,
{
    type Error = Error;
    fn try_into_value(self, params: &Params) -> std::result::Result<Value, Self::Error> {
        try_into_set(self, params)
    }
}

impl<T> TryIntoValue for std::collections::BTreeSet<T>
where
    T: TryIntoValue,
    Error: From<T::Error>,
{
    type Error = Error;
    fn try_into_value(self, params: &Params) -> std::result::Result<Value, Self::Error> {
        try_into_set(self, params)
    }
}

impl<K, V> TryIntoValue for HashMap<K, V>
where
    String: From<K>,
    V: TryIntoValue,
    Error: From<V::Error>,
{
    type Error = Error;
    fn try_into_value(self, params: &Params) -> std::result::Result<Value, Self::Error> {
        try_into_dict(self, params)
    }
}

impl<K, V> TryIntoValue for std::collections::BTreeMap<K, V>
where
    String: From<K>,
    V: TryIntoValue,
    Error: From<V::Error>,
{
    type Error = Error;
    fn try_into_value(self, params: &Params) -> std::result::Result<Value, Self::Error> {
        try_into_dict(self, params)
    }
}
