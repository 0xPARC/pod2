use std::{
    collections::{HashMap, HashSet},
    fmt::Write,
    str::FromStr,
};

use plonky2::field::types::Field;
use serde::{
    de::{
        value::{MapDeserializer, SeqDeserializer, StrDeserializer, U32Deserializer},
        IntoDeserializer, Unexpected,
    },
    forward_to_deserialize_any,
    ser::{
        SerializeMap, SerializeSeq, SerializeStruct, SerializeStructVariant, SerializeTuple,
        SerializeTupleStruct, SerializeTupleVariant,
    },
    Deserialize, Serialize, Serializer,
};

use super::{Key, Value};
use crate::{
    backends::plonky2::{
        deserialize_bytes,
        primitives::ec::{curve::Point, schnorr::SecretKey},
        serialize_bytes,
    },
    middleware::{
        containers::{Array, Dictionary},
        RawValue, TypedValue, F, HASH_SIZE, VALUE_SIZE,
    },
};

fn field_array_to_string<const N: usize>(value: &[F; N]) -> String {
    // `value` is little-endian in memory. We serialize it as a big-endian hex string
    // for human readability.
    value
        .iter()
        .rev()
        .fold(String::with_capacity(N * 16), |mut s, limb| {
            write!(s, "{:016x}", limb.0).unwrap();
            s
        })
}

fn serialize_field_tuple<S, const N: usize>(
    value: &[F; N],
    serializer: S,
) -> Result<S::Ok, S::Error>
where
    S: serde::Serializer,
{
    serializer.serialize_str(&field_array_to_string(value))
}

fn deserialize_field_tuple<'de, D, const N: usize>(deserializer: D) -> Result<[F; N], D::Error>
where
    D: serde::Deserializer<'de>,
{
    let hex_str = String::deserialize(deserializer)?;

    let expected_len = N * 16;
    if hex_str.len() != expected_len {
        return Err(serde::de::Error::custom(format!(
            "Invalid hex string length: expected {} characters, found {}",
            expected_len,
            hex_str.len()
        )));
    }
    if !hex_str.chars().all(|c| c.is_ascii_hexdigit()) {
        return Err(serde::de::Error::custom(
            "Invalid hex string format: contains non-hexadecimal characters",
        ));
    }

    let mut v = [F::ZERO; N];
    for i in 0..N {
        let start = i * 16;
        let end = start + 16;
        let hex_part = &hex_str[start..end];
        let u64_val = u64::from_str_radix(hex_part, 16).map_err(serde::de::Error::custom)?;
        // The hex string is big-endian, so the first chunk (i=0) is the most significant.
        // We store it in the last position of our little-endian array `v`.
        v[N - 1 - i] = F::from_canonical_u64(u64_val);
    }
    Ok(v)
}

pub fn serialize_hash_tuple<S>(value: &[F; HASH_SIZE], serializer: S) -> Result<S::Ok, S::Error>
where
    S: serde::Serializer,
{
    serialize_field_tuple::<S, HASH_SIZE>(value, serializer)
}

pub fn deserialize_hash_tuple<'de, D>(deserializer: D) -> Result<[F; HASH_SIZE], D::Error>
where
    D: serde::Deserializer<'de>,
{
    deserialize_field_tuple::<D, HASH_SIZE>(deserializer)
}

pub fn serialize_value_tuple<S>(value: &[F; VALUE_SIZE], serializer: S) -> Result<S::Ok, S::Error>
where
    S: serde::Serializer,
{
    serialize_field_tuple::<S, VALUE_SIZE>(value, serializer)
}

pub fn deserialize_value_tuple<'de, D>(deserializer: D) -> Result<[F; VALUE_SIZE], D::Error>
where
    D: serde::Deserializer<'de>,
{
    deserialize_field_tuple::<D, VALUE_SIZE>(deserializer)
}

pub fn serialize_i64<S>(value: &i64, serializer: S) -> Result<S::Ok, S::Error>
where
    S: serde::Serializer,
{
    serializer.serialize_str(&value.to_string())
}

pub fn deserialize_i64<'de, D>(deserializer: D) -> Result<i64, D::Error>
where
    D: serde::Deserializer<'de>,
{
    String::deserialize(deserializer)?
        .parse()
        .map_err(serde::de::Error::custom)
}

// In order to serialize a Dictionary consistently, we want to order the
// key-value pairs by the key's name field. This has no effect on the hashes
// of the keys and therefore on the Merkle tree, but it makes the serialized
// output deterministic.
pub fn ordered_map<S, V: Serialize>(
    value: &HashMap<Key, V>,
    serializer: S,
) -> Result<S::Ok, S::Error>
where
    S: Serializer,
{
    // Convert to Vec and sort by the key's name field
    let mut pairs: Vec<_> = value.iter().collect();
    pairs.sort_by(|(k1, _), (k2, _)| k1.name.cmp(&k2.name));

    // Serialize as a map
    use serde::ser::SerializeMap;
    let mut map = serializer.serialize_map(Some(pairs.len()))?;
    for (k, v) in pairs {
        map.serialize_entry(k, v)?;
    }
    map.end()
}

// Sets are serialized as sequences of elements, which are not ordered by
// default.  We want to serialize them in a deterministic way, and we can
// achieve this by sorting the elements.
pub fn ordered_set<S>(value: &HashSet<Value>, serializer: S) -> Result<S::Ok, S::Error>
where
    S: Serializer,
{
    let mut sorted_values: Vec<&Value> = value.iter().collect();
    sorted_values.sort_by_key(|v| v.raw());
    serializer.serialize_newtype_struct("Set", &sorted_values)
}

#[derive(Clone, Copy)]
enum ValueSerializerState {
    Default,
    RawValue,
    Point,
    SecretKey,
}

#[derive(Clone, Copy)]
pub struct ValueSerializer {
    container_depth: usize,
    state: ValueSerializerState,
}

pub struct ValueSerializeSeq {
    data: Vec<Value>,
    container_depth: usize,
}

pub struct ValueSerializeTupleVariant {
    name: &'static str,
    inner: ValueSerializeSeq,
}

pub struct ValueSerializeMap {
    kvs: HashMap<Key, Value>,
    next_key: Option<Key>,
    container_depth: usize,
}

pub struct ValueSerializeStructVariant {
    name: &'static str,
    inner: ValueSerializeMap,
}

impl ValueSerializer {
    pub fn new(container_depth: usize) -> Self {
        Self {
            container_depth,
            state: ValueSerializerState::Default,
        }
    }
}

impl Serializer for ValueSerializer {
    type Ok = Value;
    type Error = serde::de::value::Error;
    type SerializeSeq = ValueSerializeSeq;
    type SerializeTuple = ValueSerializeSeq;
    type SerializeTupleStruct = ValueSerializeSeq;
    type SerializeMap = ValueSerializeMap;
    type SerializeStruct = ValueSerializeMap;
    type SerializeTupleVariant = ValueSerializeTupleVariant;
    type SerializeStructVariant = ValueSerializeStructVariant;

    fn serialize_bool(self, v: bool) -> Result<Self::Ok, Self::Error> {
        Ok(Value::from(v))
    }

    fn serialize_i8(self, v: i8) -> Result<Self::Ok, Self::Error> {
        self.serialize_i64(v as i64)
    }

    fn serialize_i16(self, v: i16) -> Result<Self::Ok, Self::Error> {
        self.serialize_i64(v as i64)
    }

    fn serialize_i32(self, v: i32) -> Result<Self::Ok, Self::Error> {
        self.serialize_i64(v as i64)
    }

    fn serialize_i64(self, v: i64) -> Result<Self::Ok, Self::Error> {
        Ok(Value::from(v))
    }

    fn serialize_u8(self, v: u8) -> Result<Self::Ok, Self::Error> {
        self.serialize_i64(v as i64)
    }

    fn serialize_u16(self, v: u16) -> Result<Self::Ok, Self::Error> {
        self.serialize_i64(v as i64)
    }

    fn serialize_u32(self, v: u32) -> Result<Self::Ok, Self::Error> {
        self.serialize_i64(v as i64)
    }

    fn serialize_u64(self, v: u64) -> Result<Self::Ok, Self::Error> {
        self.serialize_i64(v as i64)
    }

    fn serialize_f32(self, v: f32) -> Result<Self::Ok, Self::Error> {
        self.serialize_f64(v as f64)
    }

    fn serialize_f64(self, v: f64) -> Result<Self::Ok, Self::Error> {
        // serialize as string?
        Err(serde::de::Error::invalid_value(
            Unexpected::Float(v),
            &"pod-compatible type",
        ))
    }

    fn serialize_str(self, v: &str) -> Result<Self::Ok, Self::Error> {
        Ok(match self.state {
            ValueSerializerState::RawValue => {
                let arr = deserialize_value_tuple(StrDeserializer::new(v))?;
                Value::from(RawValue(arr))
            }
            ValueSerializerState::Point => {
                Value::from(Point::from_str(v).map_err(serde::ser::Error::custom)?)
            }
            ValueSerializerState::SecretKey => {
                let bytes = deserialize_bytes(v).map_err(serde::ser::Error::custom)?;
                let sk = SecretKey::from_bytes(&bytes).map_err(serde::ser::Error::custom)?;
                Value::from(sk)
            }
            _ => Value::from(v),
        })
    }

    fn serialize_char(self, v: char) -> Result<Self::Ok, Self::Error> {
        self.serialize_str(&String::from(v))
    }

    fn serialize_bytes(self, v: &[u8]) -> Result<Self::Ok, Self::Error> {
        // TODO: serialize as Array, or base64 string?
        Err(serde::de::Error::invalid_value(
            Unexpected::Bytes(v),
            &"pod-compatible type",
        ))
    }

    fn serialize_seq(self, _len: Option<usize>) -> Result<Self::SerializeSeq, Self::Error> {
        Ok(ValueSerializeSeq {
            data: Vec::new(),
            container_depth: self.container_depth,
        })
    }

    fn serialize_tuple(self, len: usize) -> Result<Self::SerializeTuple, Self::Error> {
        self.serialize_seq(Some(len))
    }

    fn serialize_unit(self) -> Result<Self::Ok, Self::Error> {
        SerializeTuple::end(self.serialize_tuple(0)?)
    }

    fn serialize_unit_struct(self, _name: &'static str) -> Result<Self::Ok, Self::Error> {
        self.serialize_unit()
    }

    fn serialize_unit_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        variant: &'static str,
    ) -> Result<Self::Ok, Self::Error> {
        self.serialize_str(variant)
    }

    fn serialize_newtype_struct<T>(
        mut self,
        name: &'static str,
        value: &T,
    ) -> Result<Self::Ok, Self::Error>
    where
        T: ?Sized + Serialize,
    {
        println!("nt struct {name}");
        match name {
            "RawValue" => self.state = ValueSerializerState::RawValue,
            "Point" => self.state = ValueSerializerState::Point,
            "SecretKey" => self.state = ValueSerializerState::SecretKey,
            _ => (),
        }
        value.serialize(self)
    }

    fn serialize_newtype_variant<T>(
        self,
        _name: &'static str,
        _variant_index: u32,
        variant: &'static str,
        value: &T,
    ) -> Result<Self::Ok, Self::Error>
    where
        T: ?Sized + Serialize,
    {
        let ser_value = value.serialize(self)?;
        let mut map = HashMap::new();
        map.insert(Key::from(variant), ser_value);
        Ok(Value::from(
            Dictionary::new(self.container_depth, map).map_err(serde::de::Error::custom)?,
        ))
    }

    fn serialize_some<T>(self, value: &T) -> Result<Self::Ok, Self::Error>
    where
        T: ?Sized + Serialize,
    {
        self.serialize_newtype_variant("Option", 0, "Some", value)
    }

    fn serialize_none(self) -> Result<Self::Ok, Self::Error> {
        self.serialize_unit_variant("Option", 1, "None")
    }

    fn serialize_tuple_struct(
        self,
        _name: &'static str,
        len: usize,
    ) -> Result<Self::SerializeTupleStruct, Self::Error> {
        self.serialize_seq(Some(len))
    }

    fn serialize_tuple_variant(
        self,
        name: &'static str,
        _variant_index: u32,
        _variant: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeTupleVariant, Self::Error> {
        Ok(ValueSerializeTupleVariant {
            name,
            inner: ValueSerializeSeq {
                data: Vec::new(),
                container_depth: self.container_depth,
            },
        })
    }

    fn serialize_map(self, _len: Option<usize>) -> Result<Self::SerializeMap, Self::Error> {
        Ok(ValueSerializeMap {
            kvs: HashMap::new(),
            container_depth: self.container_depth,
            next_key: None,
        })
    }

    fn serialize_struct(
        self,
        _name: &'static str,
        len: usize,
    ) -> Result<Self::SerializeStruct, Self::Error> {
        self.serialize_map(Some(len))
    }

    fn serialize_struct_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        variant: &'static str,
        len: usize,
    ) -> Result<Self::SerializeStructVariant, Self::Error> {
        Ok(ValueSerializeStructVariant {
            name: variant,
            inner: self.serialize_map(Some(len))?,
        })
    }
}

impl SerializeSeq for ValueSerializeSeq {
    type Ok = <ValueSerializer as Serializer>::Ok;
    type Error = <ValueSerializer as Serializer>::Error;

    fn serialize_element<T>(&mut self, value: &T) -> Result<(), Self::Error>
    where
        T: ?Sized + Serialize,
    {
        self.data.push(value.serialize(ValueSerializer {
            container_depth: self.container_depth,
            state: ValueSerializerState::Default,
        })?);
        Ok(())
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        let arr = Array::new(self.container_depth, self.data).map_err(serde::de::Error::custom)?;
        Ok(Value::from(arr))
    }
}

impl SerializeTuple for ValueSerializeSeq {
    type Ok = <ValueSerializer as Serializer>::Ok;
    type Error = <ValueSerializer as Serializer>::Error;

    fn serialize_element<T>(&mut self, value: &T) -> Result<(), Self::Error>
    where
        T: ?Sized + Serialize,
    {
        SerializeSeq::serialize_element(self, value)
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        SerializeSeq::end(self)
    }
}

impl SerializeTupleStruct for ValueSerializeSeq {
    type Ok = <ValueSerializer as Serializer>::Ok;
    type Error = <ValueSerializer as Serializer>::Error;

    fn serialize_field<T>(&mut self, value: &T) -> Result<(), Self::Error>
    where
        T: ?Sized + Serialize,
    {
        SerializeSeq::serialize_element(self, value)
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        SerializeSeq::end(self)
    }
}

impl SerializeTupleVariant for ValueSerializeTupleVariant {
    type Ok = <ValueSerializer as Serializer>::Ok;
    type Error = <ValueSerializer as Serializer>::Error;

    fn serialize_field<T>(&mut self, value: &T) -> Result<(), Self::Error>
    where
        T: ?Sized + Serialize,
    {
        SerializeSeq::serialize_element(&mut self.inner, value)
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        let max_depth = self.inner.container_depth;
        let arr = SerializeSeq::end(self.inner)?;
        let mut map = HashMap::new();
        map.insert(Key::new(self.name.to_string()), arr);
        let dict = Dictionary::new(max_depth, map).map_err(serde::de::Error::custom)?;
        Ok(Value::from(dict))
    }
}

impl SerializeMap for ValueSerializeMap {
    type Ok = <ValueSerializer as Serializer>::Ok;
    type Error = <ValueSerializer as Serializer>::Error;

    fn serialize_key<T>(&mut self, key: &T) -> Result<(), Self::Error>
    where
        T: ?Sized + Serialize,
    {
        let key_ser = key.serialize(ValueSerializer {
            container_depth: self.container_depth,
            state: ValueSerializerState::Default,
        })?;
        if let TypedValue::String(s) = key_ser.typed() {
            self.next_key = Some(Key::new(s.clone()));
            Ok(())
        } else {
            Err(serde::de::Error::invalid_value(
                Unexpected::Other("non-string key in map"),
                &"string",
            ))
        }
    }

    fn serialize_value<T>(&mut self, value: &T) -> Result<(), Self::Error>
    where
        T: ?Sized + Serialize,
    {
        let val_ser = value.serialize(ValueSerializer {
            container_depth: self.container_depth,
            state: ValueSerializerState::Default,
        })?;
        self.kvs.insert(
            self.next_key
                .take()
                .expect("serialize_key should be called before serialize_value"),
            val_ser,
        );
        Ok(())
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        let dict =
            Dictionary::new(self.container_depth, self.kvs).map_err(serde::ser::Error::custom)?;
        Ok(Value::from(dict))
    }
}

impl SerializeStruct for ValueSerializeMap {
    type Ok = <ValueSerializer as Serializer>::Ok;
    type Error = <ValueSerializer as Serializer>::Error;

    fn serialize_field<T>(&mut self, key: &'static str, value: &T) -> Result<(), Self::Error>
    where
        T: ?Sized + Serialize,
    {
        SerializeMap::serialize_entry(self, key, value)
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        SerializeMap::end(self)
    }
}

impl SerializeStructVariant for ValueSerializeStructVariant {
    type Ok = <ValueSerializer as Serializer>::Ok;
    type Error = <ValueSerializer as Serializer>::Error;

    fn serialize_field<T>(&mut self, key: &'static str, value: &T) -> Result<(), Self::Error>
    where
        T: ?Sized + Serialize,
    {
        SerializeMap::serialize_entry(&mut self.inner, key, value)
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        let depth = self.inner.container_depth;
        let value = SerializeMap::end(self.inner)?;
        let mut kvs = HashMap::new();
        kvs.insert(Key::new(self.name.to_string()), value);
        let dict = Dictionary::new(depth, kvs).map_err(serde::ser::Error::custom)?;
        Ok(Value::from(dict))
    }
}

impl<'a, 'de> IntoDeserializer<'de, serde::de::value::Error> for &'a TypedValue {
    type Deserializer = Self;
    fn into_deserializer(self) -> Self::Deserializer {
        self
    }
}

impl<'a, 'de> IntoDeserializer<'de, serde::de::value::Error> for &'a Value {
    type Deserializer = &'a TypedValue;
    fn into_deserializer(self) -> Self::Deserializer {
        self.typed()
    }
}

impl<'a, 'de, E: serde::de::Error> IntoDeserializer<'de, E> for &'a Key {
    type Deserializer = StrDeserializer<'a, E>;
    fn into_deserializer(self) -> Self::Deserializer {
        StrDeserializer::new(&self.name)
    }
}

impl<'de> serde::Deserializer<'de> for &TypedValue {
    type Error = serde::de::value::Error;

    fn deserialize_any<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de>,
    {
        match self {
            TypedValue::Int(i) => visitor.visit_i64(*i),
            TypedValue::Raw(v) => visitor.visit_string(field_array_to_string(&v.0)),
            TypedValue::PublicKey(k) => visitor.visit_string(k.to_string()),
            TypedValue::SecretKey(k) => visitor.visit_string(serialize_bytes(&k.as_bytes())),
            TypedValue::Bool(b) => visitor.visit_bool(*b),
            TypedValue::Array(a) => visitor.visit_seq(SeqDeserializer::new(a.array().iter())),
            TypedValue::Set(s) => visitor.visit_seq(SeqDeserializer::new(s.set().iter())),
            TypedValue::String(s) => visitor.visit_str(s),
            TypedValue::PodId(i) => {
                visitor.visit_seq(SeqDeserializer::new(i.0 .0.iter().map(|x| x.0)))
            }
            TypedValue::Dictionary(d) => visitor.visit_map(MapDeserializer::new(d.kvs().iter())),
        }
    }

    fn deserialize_enum<V>(
        self,
        _name: &'static str,
        _variants: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de>,
    {
        match self {
            TypedValue::String(s) => visitor.visit_enum(StrDeserializer::new(s)),
            TypedValue::Int(i) => {
                if let Ok(u) = u32::try_from(*i) {
                    visitor.visit_enum(U32Deserializer::new(u))
                } else {
                    self.deserialize_any(visitor)
                }
            }
            _ => self.deserialize_any(visitor),
        }
    }

    fn deserialize_newtype_struct<V>(
        self,
        _name: &'static str,
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de>,
    {
        visitor.visit_newtype_struct(self)
    }

    fn deserialize_option<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de>,
    {
        match self {
            TypedValue::String(s) => {
                if s == "None" {
                    visitor.visit_none()
                } else {
                    self.deserialize_any(visitor)
                }
            }
            TypedValue::Dictionary(d) => {
                if let Ok(v) = d.get(&Key::from("Some")) {
                    visitor.visit_some(v.typed())
                } else {
                    self.deserialize_any(visitor)
                }
            }
            _ => self.deserialize_any(visitor),
        }
    }

    fn deserialize_unit<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de>,
    {
        match self {
            TypedValue::Array(a) if a.array().is_empty() => visitor.visit_unit(),
            _ => self.deserialize_any(visitor),
        }
    }

    forward_to_deserialize_any! { bool i8 i16 i32 i64 u8 u16 u32 u64 f32 f64 char str string bytes byte_buf unit_struct seq tuple_struct tuple map struct identifier ignored_any }
}

#[cfg(test)]
mod test {
    use serde::{de::DeserializeOwned, Deserialize, Serialize};

    use crate::{
        backends::plonky2::primitives::ec::{curve::Point, schnorr::SecretKey},
        middleware::{serialization::ValueSerializer, Params, RawValue},
    };

    #[derive(Serialize, Deserialize, PartialEq, Eq, Debug)]
    enum Method {
        Search,
        Mine,
    }

    #[derive(Serialize, Deserialize, PartialEq, Eq, Debug)]
    struct FrogDesc {
        frog_id: i64,
        name: String,
        seed_range: Vec<(Method, RawValue)>,
        option1: Option<i64>,
        option2: Option<i64>,
        unit: (),
        sk: SecretKey,
        pk: Point,
    }

    fn test_roundtrip<T: Serialize + DeserializeOwned + Eq + std::fmt::Debug>(t: T) {
        let depth = Params::default().max_depth_mt_containers;
        let val = t.serialize(ValueSerializer::new(depth)).unwrap();
        println!("{val:?}");
        let out: T = Deserialize::deserialize(val.typed()).unwrap();
        assert_eq!(t, out);
    }

    #[test]
    fn test_frog_desc() {
        let seed_range = vec![
            (Method::Search, RawValue::default()),
            (Method::Mine, RawValue::default()),
        ];
        let sk = SecretKey::new_rand();
        let pk = sk.public_key();
        let desc = FrogDesc {
            frog_id: 1,
            name: "a frog".to_string(),
            seed_range,
            option1: Some(2),
            option2: None,
            unit: (),
            sk,
            pk,
        };
        test_roundtrip(desc);
    }
}
