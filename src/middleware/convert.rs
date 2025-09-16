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

pub trait PodTryInto<T> {
    type Error;
    fn pod_try_into(self, params: &Params) -> std::result::Result<T, Self::Error>;
}

pub fn try_into_array<C>(c: C, params: &Params) -> Result<Array, Error>
where
    C: IntoIterator,
    C::Item: PodTryInto<Value>,
    Error: From<<C::Item as PodTryInto<Value>>::Error>,
{
    let r: Result<Vec<Value>, <C::Item as PodTryInto<Value>>::Error> =
        c.into_iter().map(|x| x.pod_try_into(params)).collect();
    Array::new(params.max_depth_mt_containers, r?)
}

pub fn try_into_array_value<C>(c: C, params: &Params) -> Result<Value, Error>
where
    C: IntoIterator,
    C::Item: PodTryInto<Value>,
    Error: From<<C::Item as PodTryInto<Value>>::Error>,
{
    Ok(Value::from(try_into_array(c, params)?))
}

pub fn try_into_set<C>(c: C, params: &Params) -> Result<Set, Error>
where
    C: IntoIterator,
    C::Item: PodTryInto<Value>,
    Error: From<<C::Item as PodTryInto<Value>>::Error>,
{
    let r: Result<HashSet<Value>, <C::Item as PodTryInto<Value>>::Error> =
        c.into_iter().map(|x| x.pod_try_into(params)).collect();
    Set::new(params.max_depth_mt_containers, r?)
}

pub fn try_into_set_value<C>(c: C, params: &Params) -> Result<Value, Error>
where
    C: IntoIterator,
    C::Item: PodTryInto<Value>,
    Error: From<<C::Item as PodTryInto<Value>>::Error>,
{
    Ok(Value::from(try_into_set(c, params)?))
}

pub fn try_into_dict<C, K, V>(c: C, params: &Params) -> Result<Dictionary, Error>
where
    C: IntoIterator<Item = (K, V)>,
    K: Into<String>,
    V: PodTryInto<Value>,
    Error: From<V::Error>,
{
    let r: Result<HashMap<Key, Value>, V::Error> = c
        .into_iter()
        .map(|(k, v)| Ok((Key::from(k.into()), v.pod_try_into(params)?)))
        .collect();
    Dictionary::new(params.max_depth_mt_containers, r?)
}

pub fn try_into_dict_value<C, K, V>(c: C, params: &Params) -> Result<Value, Error>
where
    C: IntoIterator<Item = (K, V)>,
    K: Into<String>,
    V: PodTryInto<Value>,
    Error: From<V::Error>,
{
    Ok(Value::from(try_into_dict(c, params)?))
}

#[macro_export]
macro_rules! try_into_using_value_from {
    ($t: ty) => {
        impl $crate::middleware::convert::PodTryInto<$crate::middleware::Value> for $t {
            type Error = core::convert::Infallible;
            fn pod_try_into(
                self,
                _params: &$crate::middleware::Params,
            ) -> core::result::Result<$crate::middleware::Value, Self::Error> {
                Ok($crate::middleware::Value::from(self))
            }
        }
    };
}

#[macro_export]
macro_rules! try_into_using_array {
     ($($path:ident)::+ ) => {
        impl<__T> $crate::middleware::convert::PodTryInto<$crate::middleware::containers::Array> for$($path)::+<__T>
        where
            __T: $crate::middleware::convert::PodTryInto<$crate::middleware::Value>,
            $crate::middleware::Error: core::convert::From<__T::Error>,
        {
            type Error = $crate::middleware::Error;
            fn pod_try_into(self, params: &$crate::middleware::Params) -> core::result::Result<$crate::middleware::containers::Array, Self::Error> {
                $crate::middleware::convert::try_into_array(self, params)
            }
        }

        impl<__T> $crate::middleware::convert::PodTryInto<$crate::middleware::Value> for$($path)::+<__T>
        where
            __T: $crate::middleware::convert::PodTryInto<$crate::middleware::Value>,
            $crate::middleware::Error: core::convert::From<__T::Error>,
        {
            type Error = $crate::middleware::Error;
            fn pod_try_into(self, params: &$crate::middleware::Params) -> core::result::Result<$crate::middleware::Value, Self::Error> {
                $crate::middleware::convert::try_into_array_value(self, params)
            }
        }
    };
}

#[macro_export]
macro_rules! try_into_using_set {
     ($($path:ident)::+ ) => {
        impl<__T> $crate::middleware::convert::PodTryInto<$crate::middleware::containers::Set> for$($path)::+<__T>
        where
            __T: $crate::middleware::convert::PodTryInto<$crate::middleware::Value>,
            $crate::middleware::Error: core::convert::From<__T::Error>,
        {
            type Error = $crate::middleware::Error;
            fn pod_try_into(self, params: &$crate::middleware::Params) -> core::result::Result<$crate::middleware::containers::Set, Self::Error> {
                $crate::middleware::convert::try_into_set(self, params)
            }
        }

        impl<__T> $crate::middleware::convert::PodTryInto<$crate::middleware::Value> for$($path)::+<__T>
        where
            __T: $crate::middleware::convert::PodTryInto<$crate::middleware::Value>,
            $crate::middleware::Error: core::convert::From<__T::Error>,
        {
            type Error = $crate::middleware::Error;
            fn pod_try_into(self, params: &$crate::middleware::Params) -> core::result::Result<$crate::middleware::Value, Self::Error> {
                $crate::middleware::convert::try_into_set_value(self, params)
            }
        }
    };
}

#[macro_export]
macro_rules! try_into_using_dict {
     ($($path:ident)::+ ) => {
        impl<__K, __V> $crate::middleware::convert::PodTryInto<$crate::middleware::containers::Dictionary> for$($path)::+<__K, __V>
        where
            __K: core::convert::Into<std::string::String>,
            __V: $crate::middleware::convert::PodTryInto<$crate::middleware::Value>,
            $crate::middleware::Error: core::convert::From<__V::Error>,
        {
            type Error = $crate::middleware::Error;
            fn pod_try_into(self, params: &$crate::middleware::Params) -> core::result::Result<$crate::middleware::containers::Dictionary, Self::Error> {
                $crate::middleware::convert::try_into_dict(self, params)
            }
        }

        impl<__K, __V> $crate::middleware::convert::PodTryInto<$crate::middleware::Value> for$($path)::+<__K, __V>
        where
            __K: core::convert::Into<std::string::String>,
            __V: $crate::middleware::convert::PodTryInto<$crate::middleware::Value>,
            $crate::middleware::Error: core::convert::From<__V::Error>,
        {
            type Error = $crate::middleware::Error;
            fn pod_try_into(self, params: &$crate::middleware::Params) -> core::result::Result<$crate::middleware::Value, Self::Error> {
                $crate::middleware::convert::try_into_dict_value(self, params)
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

try_into_using_array!(Vec);
try_into_using_set!(HashSet);
try_into_using_set!(std::collections::BTreeSet);
try_into_using_dict!(HashMap);
try_into_using_dict!(std::collections::BTreeMap);
