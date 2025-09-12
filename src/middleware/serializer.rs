use std::{
    collections::{HashMap, HashSet},
    str::FromStr,
};

use base64::{prelude::BASE64_STANDARD, Engine};
use paste::paste;
use serde::{
    de::{
        value::{
            MapAccessDeserializer, MapDeserializer, SeqDeserializer, StrDeserializer,
            U32Deserializer,
        },
        IntoDeserializer, Unexpected,
    },
    forward_to_deserialize_any,
    ser::{
        Impossible, SerializeMap, SerializeSeq, SerializeStruct, SerializeStructVariant,
        SerializeTuple, SerializeTupleStruct, SerializeTupleVariant,
    },
    Serialize, Serializer,
};

use super::{Key, Value};
use crate::{
    backends::plonky2::{
        deserialize_bytes,
        primitives::ec::{curve::Point, schnorr::SecretKey},
        serialize_bytes,
    },
    frontend::SignedDict,
    middleware::{
        containers::{Array, Dictionary, Set},
        field_array_to_string,
        serialization::deserialize_value_tuple,
        RawValue, TypedValue,
    },
};

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

#[derive(Clone, Copy)]
struct OptionValueSerializer(ValueSerializer);

#[derive(Clone, Copy)]
pub struct DictionarySerializer {
    container_depth: usize,
}

pub struct ValueSerializeSeq {
    data: Vec<Value>,
    container_depth: usize,
}

pub struct ValueSerializeTupleVariant(DictionarySerializeTupleVariant);

pub struct ValueSerializeMap(DictionarySerializeMap);

pub struct ValueSerializeStructVariant(DictionarySerializeStructVariant);

pub struct DictionarySerializeTupleVariant {
    name: &'static str,
    inner: ValueSerializeSeq,
}

pub struct DictionarySerializeMap {
    kvs: HashMap<Key, Value>,
    next_key: Option<Key>,
    container_depth: usize,
}

pub struct DictionarySerializeStructVariant {
    name: &'static str,
    inner: ValueSerializeMap,
}

struct OptionValueSerializeSeq(ValueSerializeSeq);
struct OptionValueSerializeMap(ValueSerializeMap);
struct OptionValueSerializeStructVariant(ValueSerializeStructVariant);
struct OptionValueSerializeTupleVariant(ValueSerializeTupleVariant);

impl ValueSerializer {
    pub fn new(container_depth: usize) -> Self {
        Self {
            container_depth,
            state: ValueSerializerState::Default,
        }
    }

    fn dictionary_serializer(self) -> DictionarySerializer {
        DictionarySerializer {
            container_depth: self.container_depth,
        }
    }

    fn update_state_newtype(&mut self, name: &'static str) {
        match name {
            "pod2::RawValue" => self.state = ValueSerializerState::RawValue,
            "pod2::Point" => self.state = ValueSerializerState::Point,
            "pod2::SecretKey" => self.state = ValueSerializerState::SecretKey,
            _ => (),
        }
    }
}

impl DictionarySerializer {
    pub fn new(container_depth: usize) -> Self {
        Self { container_depth }
    }

    fn value_serializer(self) -> ValueSerializer {
        ValueSerializer {
            container_depth: self.container_depth,
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
        let s = format!("{v:.8e}");
        self.serialize_str(&s)
    }

    fn serialize_f64(self, v: f64) -> Result<Self::Ok, Self::Error> {
        let s = format!("{v:.16e}");
        self.serialize_str(&s)
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
        let s = BASE64_STANDARD.encode(v);
        self.serialize_str(&s)
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
        Ok(Value::from(false))
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
        self.update_state_newtype(name);
        value.serialize(self)
    }

    fn serialize_newtype_variant<T>(
        self,
        name: &'static str,
        variant_index: u32,
        variant: &'static str,
        value: &T,
    ) -> Result<Self::Ok, Self::Error>
    where
        T: ?Sized + Serialize,
    {
        self.dictionary_serializer()
            .serialize_newtype_variant(name, variant_index, variant, value)
            .map(Value::from)
    }

    fn serialize_some<T>(self, value: &T) -> Result<Self::Ok, Self::Error>
    where
        T: ?Sized + Serialize,
    {
        let value_serialized = value.serialize(self)?;
        let mut hash_set = HashSet::new();
        hash_set.insert(value_serialized);
        let set = Set::new(self.container_depth, hash_set).map_err(serde::ser::Error::custom)?;
        Ok(Value::from(set))
    }

    fn serialize_none(self) -> Result<Self::Ok, Self::Error> {
        let set =
            Set::new(self.container_depth, HashSet::new()).map_err(serde::ser::Error::custom)?;
        Ok(Value::from(set))
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
        variant_index: u32,
        variant: &'static str,
        len: usize,
    ) -> Result<Self::SerializeTupleVariant, Self::Error> {
        self.dictionary_serializer()
            .serialize_tuple_variant(name, variant_index, variant, len)
            .map(ValueSerializeTupleVariant)
    }

    fn serialize_map(self, len: Option<usize>) -> Result<Self::SerializeMap, Self::Error> {
        self.dictionary_serializer()
            .serialize_map(len)
            .map(ValueSerializeMap)
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
        name: &'static str,
        variant_index: u32,
        variant: &'static str,
        len: usize,
    ) -> Result<Self::SerializeStructVariant, Self::Error> {
        self.dictionary_serializer()
            .serialize_struct_variant(name, variant_index, variant, len)
            .map(ValueSerializeStructVariant)
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
        self.0.serialize_field(value)
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        SerializeTupleVariant::end(self.0).map(Value::from)
    }
}

impl SerializeMap for ValueSerializeMap {
    type Ok = <ValueSerializer as Serializer>::Ok;
    type Error = <ValueSerializer as Serializer>::Error;

    fn serialize_key<T>(&mut self, key: &T) -> Result<(), Self::Error>
    where
        T: ?Sized + Serialize,
    {
        self.0.serialize_key(key)
    }

    fn serialize_value<T>(&mut self, value: &T) -> Result<(), Self::Error>
    where
        T: ?Sized + Serialize,
    {
        self.0.serialize_value(value)
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        SerializeMap::end(self.0).map(Value::from)
    }
}

impl SerializeStruct for ValueSerializeMap {
    type Ok = <ValueSerializer as Serializer>::Ok;
    type Error = <ValueSerializer as Serializer>::Error;

    fn serialize_field<T>(&mut self, key: &'static str, value: &T) -> Result<(), Self::Error>
    where
        T: ?Sized + Serialize,
    {
        SerializeStruct::serialize_field(&mut self.0, key, value)
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        SerializeStruct::end(self.0).map(Value::from)
    }
}

impl SerializeStructVariant for ValueSerializeStructVariant {
    type Ok = <ValueSerializer as Serializer>::Ok;
    type Error = <ValueSerializer as Serializer>::Error;

    fn serialize_field<T>(&mut self, key: &'static str, value: &T) -> Result<(), Self::Error>
    where
        T: ?Sized + Serialize,
    {
        self.0.serialize_field(key, value)
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        SerializeStructVariant::end(self.0).map(Value::from)
    }
}

macro_rules! serialize_type {
    ( bytes ) => {
        &[u8]
    };
    ( str ) => {
        &str
    };
    ( unit_struct ) => {
        &'static str
    };
    ( $name: ident ) => {
        $name
    };
}

macro_rules! map_expected {
    ( $($item: ident )* ) => {
        $(
            paste! {
                fn [<serialize_ $item>](self, _: serialize_type!($item)) -> Result<Self::Ok, Self::Error> {
                    Err(serde::ser::Error::custom("expected a map"))
                }
            }
        )*
    }
}

impl Serializer for DictionarySerializer {
    type Ok = Dictionary;
    type Error = serde::de::value::Error;
    type SerializeSeq = Impossible<Self::Ok, Self::Error>;
    type SerializeTuple = Impossible<Self::Ok, Self::Error>;
    type SerializeTupleStruct = Impossible<Self::Ok, Self::Error>;
    type SerializeTupleVariant = DictionarySerializeTupleVariant;
    type SerializeMap = DictionarySerializeMap;
    type SerializeStruct = DictionarySerializeMap;
    type SerializeStructVariant = DictionarySerializeStructVariant;

    map_expected!(bool i8 i16 i32 i64 u8 u16 u32 u64 f32 f64 bytes str char unit_struct);

    fn serialize_none(self) -> Result<Self::Ok, Self::Error> {
        Err(serde::ser::Error::custom("expected a map"))
    }

    fn serialize_some<T>(self, _value: &T) -> Result<Self::Ok, Self::Error>
    where
        T: ?Sized + Serialize,
    {
        Err(serde::ser::Error::custom("expected a map"))
    }

    fn serialize_unit(self) -> Result<Self::Ok, Self::Error> {
        Err(serde::ser::Error::custom("expected a map"))
    }

    fn serialize_unit_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        _variant: &'static str,
    ) -> Result<Self::Ok, Self::Error> {
        Err(serde::ser::Error::custom("expected a map"))
    }

    fn serialize_newtype_struct<T>(
        self,
        _name: &'static str,
        value: &T,
    ) -> Result<Self::Ok, Self::Error>
    where
        T: ?Sized + Serialize,
    {
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
        let ser_value = value.serialize(self.value_serializer())?;
        let mut map = HashMap::new();
        map.insert(Key::from(variant), ser_value);
        Dictionary::new(self.container_depth, map).map_err(serde::ser::Error::custom)
    }

    fn serialize_seq(self, _len: Option<usize>) -> Result<Self::SerializeSeq, Self::Error> {
        Err(serde::ser::Error::custom("expected a map"))
    }

    fn serialize_tuple(self, _len: usize) -> Result<Self::SerializeTuple, Self::Error> {
        Err(serde::ser::Error::custom("expected a map"))
    }

    fn serialize_tuple_struct(
        self,
        _name: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeTupleStruct, Self::Error> {
        Err(serde::ser::Error::custom("expected a map"))
    }

    fn serialize_tuple_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        variant: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeTupleVariant, Self::Error> {
        Ok(DictionarySerializeTupleVariant {
            name: variant,
            inner: ValueSerializeSeq {
                data: Vec::new(),
                container_depth: self.container_depth,
            },
        })
    }

    fn serialize_map(self, _len: Option<usize>) -> Result<Self::SerializeMap, Self::Error> {
        Ok(DictionarySerializeMap {
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
        Ok(DictionarySerializeStructVariant {
            name: variant,
            inner: ValueSerializeMap(self.serialize_map(Some(len))?),
        })
    }
}

impl SerializeTupleVariant for DictionarySerializeTupleVariant {
    type Ok = <DictionarySerializer as Serializer>::Ok;
    type Error = <DictionarySerializer as Serializer>::Error;

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
        Ok(dict)
    }
}

impl DictionarySerializeMap {
    fn convert_key<T>(&self, key: &T) -> Result<Key, <DictionarySerializer as Serializer>::Error>
    where
        T: ?Sized + Serialize,
    {
        let key_ser = key.serialize(ValueSerializer {
            container_depth: self.container_depth,
            state: ValueSerializerState::Default,
        })?;
        if let TypedValue::String(s) = key_ser.typed() {
            Ok(Key::new(s.clone()))
        } else {
            Err(serde::de::Error::invalid_value(
                Unexpected::Other("non-string key in map"),
                &"string",
            ))
        }
    }
}

impl SerializeMap for DictionarySerializeMap {
    type Ok = <DictionarySerializer as Serializer>::Ok;
    type Error = <DictionarySerializer as Serializer>::Error;

    fn serialize_key<T>(&mut self, key: &T) -> Result<(), Self::Error>
    where
        T: ?Sized + Serialize,
    {
        self.next_key = Some(self.convert_key(key)?);
        Ok(())
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
        Ok(dict)
    }
}

impl SerializeStruct for DictionarySerializeMap {
    type Ok = <DictionarySerializer as Serializer>::Ok;
    type Error = <DictionarySerializer as Serializer>::Error;

    fn serialize_field<T>(&mut self, key: &'static str, value: &T) -> Result<(), Self::Error>
    where
        T: ?Sized + Serialize,
    {
        //SerializeMap::serialize_entry(self, key, value)
        let opt_ser = value.serialize(OptionValueSerializer(ValueSerializer {
            container_depth: self.container_depth,
            state: ValueSerializerState::Default,
        }))?;
        if let Some(val_ser) = opt_ser {
            let key = self.convert_key(key)?;
            self.kvs.insert(key, val_ser);
        }
        Ok(())
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        SerializeMap::end(self)
    }
}

impl SerializeStructVariant for DictionarySerializeStructVariant {
    type Ok = <DictionarySerializer as Serializer>::Ok;
    type Error = <DictionarySerializer as Serializer>::Error;

    fn serialize_field<T>(&mut self, key: &'static str, value: &T) -> Result<(), Self::Error>
    where
        T: ?Sized + Serialize,
    {
        SerializeMap::serialize_entry(&mut self.inner, key, value)
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        let depth = self.inner.0.container_depth;
        let value = SerializeMap::end(self.inner)?;
        let mut kvs = HashMap::new();
        kvs.insert(Key::new(self.name.to_string()), value);
        let dict = Dictionary::new(depth, kvs).map_err(serde::ser::Error::custom)?;
        Ok(dict)
    }
}

macro_rules! option_serializer_forward {
    ( $($item: ident )* ) => {
        $(
            paste! {
                fn [<serialize_ $item>](self, v: serialize_type!($item)) -> Result<Self::Ok, Self::Error> {
                    self.0.[<serialize_ $item>](v).map(Some)
                }
            }
        )*
    }
}

impl Serializer for OptionValueSerializer {
    type Ok = Option<Value>;
    type Error = <ValueSerializer as Serializer>::Error;
    type SerializeSeq = OptionValueSerializeSeq;
    type SerializeTuple = OptionValueSerializeSeq;
    type SerializeTupleStruct = OptionValueSerializeSeq;
    type SerializeMap = OptionValueSerializeMap;
    type SerializeStruct = OptionValueSerializeMap;
    type SerializeTupleVariant = OptionValueSerializeTupleVariant;
    type SerializeStructVariant = OptionValueSerializeStructVariant;

    option_serializer_forward!(bool i8 i16 i32 i64 u8 u16 u32 u64 f32 f64 char bytes str);

    fn serialize_none(self) -> Result<Self::Ok, Self::Error> {
        Ok(None)
    }

    fn serialize_some<T>(self, value: &T) -> Result<Self::Ok, Self::Error>
    where
        T: ?Sized + Serialize,
    {
        value.serialize(self.0).map(Some)
    }

    fn serialize_unit(self) -> Result<Self::Ok, Self::Error> {
        self.0.serialize_unit().map(Some)
    }

    fn serialize_unit_struct(self, name: &'static str) -> Result<Self::Ok, Self::Error> {
        self.0.serialize_unit_struct(name).map(Some)
    }

    fn serialize_unit_variant(
        self,
        name: &'static str,
        variant_index: u32,
        variant: &'static str,
    ) -> Result<Self::Ok, Self::Error> {
        self.0
            .serialize_unit_variant(name, variant_index, variant)
            .map(Some)
    }

    fn serialize_newtype_struct<T>(
        mut self,
        name: &'static str,
        value: &T,
    ) -> Result<Self::Ok, Self::Error>
    where
        T: ?Sized + Serialize,
    {
        self.0.update_state_newtype(name);
        value.serialize(self)
    }

    fn serialize_newtype_variant<T>(
        self,
        name: &'static str,
        variant_index: u32,
        variant: &'static str,
        value: &T,
    ) -> Result<Self::Ok, Self::Error>
    where
        T: ?Sized + Serialize,
    {
        self.0
            .serialize_newtype_variant(name, variant_index, variant, value)
            .map(Some)
    }

    fn serialize_seq(self, len: Option<usize>) -> Result<Self::SerializeSeq, Self::Error> {
        self.0.serialize_seq(len).map(OptionValueSerializeSeq)
    }

    fn serialize_tuple(self, len: usize) -> Result<Self::SerializeTuple, Self::Error> {
        self.0.serialize_tuple(len).map(OptionValueSerializeSeq)
    }

    fn serialize_tuple_struct(
        self,
        name: &'static str,
        len: usize,
    ) -> Result<Self::SerializeTupleStruct, Self::Error> {
        self.0
            .serialize_tuple_struct(name, len)
            .map(OptionValueSerializeSeq)
    }

    fn serialize_tuple_variant(
        self,
        name: &'static str,
        variant_index: u32,
        variant: &'static str,
        len: usize,
    ) -> Result<Self::SerializeTupleVariant, Self::Error> {
        self.0
            .serialize_tuple_variant(name, variant_index, variant, len)
            .map(OptionValueSerializeTupleVariant)
    }

    fn serialize_struct(
        self,
        name: &'static str,
        len: usize,
    ) -> Result<Self::SerializeStruct, Self::Error> {
        self.0
            .serialize_struct(name, len)
            .map(OptionValueSerializeMap)
    }

    fn serialize_map(self, len: Option<usize>) -> Result<Self::SerializeMap, Self::Error> {
        self.0.serialize_map(len).map(OptionValueSerializeMap)
    }

    fn serialize_struct_variant(
        self,
        name: &'static str,
        variant_index: u32,
        variant: &'static str,
        len: usize,
    ) -> Result<Self::SerializeStructVariant, Self::Error> {
        self.0
            .serialize_struct_variant(name, variant_index, variant, len)
            .map(OptionValueSerializeStructVariant)
    }
}

impl SerializeSeq for OptionValueSerializeSeq {
    type Ok = <OptionValueSerializer as Serializer>::Ok;
    type Error = <OptionValueSerializer as Serializer>::Error;

    fn serialize_element<T>(&mut self, value: &T) -> Result<(), Self::Error>
    where
        T: ?Sized + Serialize,
    {
        SerializeSeq::serialize_element(&mut self.0, value)
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        SerializeSeq::end(self.0).map(Some)
    }
}

impl SerializeTuple for OptionValueSerializeSeq {
    type Ok = <OptionValueSerializer as Serializer>::Ok;
    type Error = <OptionValueSerializer as Serializer>::Error;

    fn serialize_element<T>(&mut self, value: &T) -> Result<(), Self::Error>
    where
        T: ?Sized + Serialize,
    {
        SerializeTuple::serialize_element(&mut self.0, value)
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        SerializeTuple::end(self.0).map(Some)
    }
}

impl SerializeTupleStruct for OptionValueSerializeSeq {
    type Ok = <OptionValueSerializer as Serializer>::Ok;
    type Error = <OptionValueSerializer as Serializer>::Error;

    fn serialize_field<T>(&mut self, value: &T) -> Result<(), Self::Error>
    where
        T: ?Sized + Serialize,
    {
        self.0.serialize_field(value)
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        SerializeTupleStruct::end(self.0).map(Some)
    }
}

impl SerializeMap for OptionValueSerializeMap {
    type Ok = <OptionValueSerializer as Serializer>::Ok;
    type Error = <OptionValueSerializer as Serializer>::Error;

    fn serialize_key<T>(&mut self, key: &T) -> Result<(), Self::Error>
    where
        T: ?Sized + Serialize,
    {
        self.0.serialize_key(key)
    }

    fn serialize_value<T>(&mut self, value: &T) -> Result<(), Self::Error>
    where
        T: ?Sized + Serialize,
    {
        self.0.serialize_value(value)
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        SerializeMap::end(self.0).map(Some)
    }
}

impl SerializeStruct for OptionValueSerializeMap {
    type Ok = <OptionValueSerializer as Serializer>::Ok;
    type Error = <OptionValueSerializer as Serializer>::Error;

    fn serialize_field<T>(&mut self, key: &'static str, value: &T) -> Result<(), Self::Error>
    where
        T: ?Sized + Serialize,
    {
        self.0.serialize_field(key, value)
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        SerializeStruct::end(self.0).map(Some)
    }
}

impl SerializeStructVariant for OptionValueSerializeStructVariant {
    type Ok = <OptionValueSerializer as Serializer>::Ok;
    type Error = <OptionValueSerializer as Serializer>::Error;

    fn serialize_field<T>(&mut self, key: &'static str, value: &T) -> Result<(), Self::Error>
    where
        T: ?Sized + Serialize,
    {
        self.0.serialize_field(key, value)
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        self.0.end().map(Some)
    }
}

impl SerializeTupleVariant for OptionValueSerializeTupleVariant {
    type Ok = <OptionValueSerializer as Serializer>::Ok;
    type Error = <OptionValueSerializer as Serializer>::Error;

    fn serialize_field<T>(&mut self, value: &T) -> Result<(), Self::Error>
    where
        T: ?Sized + Serialize,
    {
        self.0.serialize_field(value)
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        self.0.end().map(Some)
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

impl<'a, 'de> IntoDeserializer<'de, serde::de::value::Error> for &'a Dictionary {
    type Deserializer = Self;
    fn into_deserializer(self) -> Self::Deserializer {
        self
    }
}

impl<'a, 'de> IntoDeserializer<'de, serde::de::value::Error> for &'a SignedDict {
    type Deserializer = &'a Dictionary;
    fn into_deserializer(self) -> Self::Deserializer {
        &self.dict
    }
}

impl<'de> serde::Deserializer<'de> for &Dictionary {
    type Error = serde::de::value::Error;

    fn deserialize_any<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de>,
    {
        visitor.visit_map(MapDeserializer::new(self.kvs().iter()))
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
        visitor.visit_enum(MapAccessDeserializer::new(MapDeserializer::new(
            self.kvs().iter(),
        )))
    }

    fn deserialize_ignored_any<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de>,
    {
        visitor.visit_unit()
    }

    fn deserialize_struct<V>(
        self,
        _name: &'static str,
        _fields: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de>,
    {
        visitor.visit_map(MapDeserializer::new(
            self.kvs().iter().map(|(k, v)| (k, StructField(v.typed()))),
        ))
    }

    forward_to_deserialize_any! { bool i8 i16 i32 i64 f32 f64 u8 u16 u32 u64 char str bytes byte_buf string option unit unit_struct seq tuple_struct tuple map newtype_struct identifier }
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
            TypedValue::Dictionary(d) => d.deserialize_any(visitor),
        }
    }

    fn deserialize_enum<V>(
        self,
        name: &'static str,
        variants: &'static [&'static str],
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
            TypedValue::Dictionary(d) => d.deserialize_enum(name, variants, visitor),
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
            TypedValue::Set(s) if s.set().len() <= 1 => match s.set().iter().next() {
                Some(x) => visitor.visit_some(x.typed()),
                None => visitor.visit_none(),
            },
            _ => self.deserialize_any(visitor),
        }
    }

    fn deserialize_unit<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de>,
    {
        visitor.visit_unit()
    }

    fn deserialize_bytes<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de>,
    {
        match self {
            TypedValue::String(s) => {
                let b = BASE64_STANDARD
                    .decode(s)
                    .map_err(|e| serde::de::Error::custom(e.to_string()))?;
                visitor.visit_bytes(&b)
            }
            _ => self.deserialize_any(visitor),
        }
    }

    fn deserialize_byte_buf<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de>,
    {
        match self {
            TypedValue::String(s) => {
                let b = BASE64_STANDARD
                    .decode(s)
                    .map_err(|e| serde::de::Error::custom(e.to_string()))?;
                visitor.visit_byte_buf(b)
            }
            _ => self.deserialize_any(visitor),
        }
    }

    fn deserialize_f32<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de>,
    {
        match self {
            TypedValue::String(s) => {
                if let Ok(f) = f32::from_str(s) {
                    visitor.visit_f32(f)
                } else {
                    self.deserialize_any(visitor)
                }
            }
            _ => self.deserialize_any(visitor),
        }
    }

    fn deserialize_f64<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de>,
    {
        match self {
            TypedValue::String(s) => {
                if let Ok(f) = f64::from_str(s) {
                    visitor.visit_f64(f)
                } else {
                    self.deserialize_any(visitor)
                }
            }
            _ => self.deserialize_any(visitor),
        }
    }

    fn deserialize_struct<V>(
        self,
        name: &'static str,
        fields: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de>,
    {
        match self {
            TypedValue::Dictionary(d) => d.deserialize_struct(name, fields, visitor),
            _ => self.deserialize_any(visitor),
        }
    }

    forward_to_deserialize_any! { bool i8 i16 i32 i64 u8 u16 u32 u64 char str string unit_struct seq tuple_struct tuple map identifier ignored_any }
}

struct StructField<'a>(&'a TypedValue);

impl<'a, 'de> IntoDeserializer<'de, serde::de::value::Error> for StructField<'a> {
    type Deserializer = Self;
    fn into_deserializer(self) -> Self::Deserializer {
        self
    }
}

macro_rules! deserialize_forward {
    ( $($item: ident )* ) => {
        $(
            paste! {
                fn [<deserialize_ $item>]<V>(self, visitor: V) -> Result<V::Value, Self::Error>
                where
                    V: serde::de::Visitor<'de>,
                {
                    self.0.[<deserialize_ $item>](visitor)
                }
            }
        )*
    }
}

impl<'de> serde::Deserializer<'de> for StructField<'_> {
    type Error = serde::de::value::Error;

    deserialize_forward!(any bool i8 i16 i32 i64 u8 u16 u32 u64 f32 f64 str char string bytes byte_buf unit seq ignored_any map identifier);

    fn deserialize_unit_struct<V>(
        self,
        name: &'static str,
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de>,
    {
        self.0.deserialize_unit_struct(name, visitor)
    }

    fn deserialize_newtype_struct<V>(
        self,
        name: &'static str,
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de>,
    {
        self.0.deserialize_newtype_struct(name, visitor)
    }

    fn deserialize_tuple<V>(self, len: usize, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de>,
    {
        self.0.deserialize_tuple(len, visitor)
    }

    fn deserialize_struct<V>(
        self,
        name: &'static str,
        fields: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de>,
    {
        self.0.deserialize_struct(name, fields, visitor)
    }

    fn deserialize_tuple_struct<V>(
        self,
        name: &'static str,
        len: usize,
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de>,
    {
        self.0.deserialize_tuple_struct(name, len, visitor)
    }

    fn deserialize_enum<V>(
        self,
        name: &'static str,
        variants: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de>,
    {
        self.0.deserialize_enum(name, variants, visitor)
    }

    fn deserialize_option<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de>,
    {
        visitor.visit_some(self.0)
    }
}

#[cfg(test)]
mod test {

    use std::collections::HashMap;

    use serde::{
        de::{DeserializeOwned, Visitor},
        Deserialize, Serialize,
    };

    use crate::{
        backends::plonky2::primitives::ec::{curve::Point, schnorr::SecretKey},
        middleware::{
            serializer::{DictionarySerializer, ValueSerializer},
            Params, RawValue, TypedValue, Value,
        },
    };

    #[derive(Serialize, Deserialize, PartialEq, Eq, Debug, Clone)]
    enum Method {
        Search,
        Mine,
    }

    #[derive(Serialize, Deserialize, PartialEq, Eq, Debug, Clone)]
    struct Inner {
        ch: char,
        b: bool,
    }

    #[derive(Serialize, Deserialize, PartialEq, Eq, Debug, Clone)]
    struct Tuple(u8, u32);

    #[derive(PartialEq, Eq, Debug, Clone)]
    struct Bytes(Vec<u8>);

    struct BytesVisitor;

    impl<'de> Visitor<'de> for BytesVisitor {
        type Value = Bytes;

        fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
            write!(formatter, "a byte buffer")
        }

        fn visit_byte_buf<E>(self, v: Vec<u8>) -> Result<Self::Value, E>
        where
            E: serde::de::Error,
        {
            Ok(Bytes(v))
        }
    }

    impl Serialize for Bytes {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: serde::Serializer,
        {
            serializer.serialize_bytes(&self.0)
        }
    }

    impl<'de> Deserialize<'de> for Bytes {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: serde::Deserializer<'de>,
        {
            deserializer.deserialize_byte_buf(BytesVisitor)
        }
    }

    #[derive(Serialize, Deserialize, Debug, Clone)]
    struct Float(f32);

    impl PartialEq for Float {
        fn eq(&self, other: &Self) -> bool {
            self.0 == other.0 || (self.0.is_nan() && other.0.is_nan())
        }
    }

    impl Eq for Float {}

    #[derive(Serialize, Deserialize, PartialEq, Eq, Debug, Clone)]
    enum Fancy {
        B(i64, i64),
        C { x: i64, y: Vec<i64> },
    }

    #[derive(Serialize, Deserialize, PartialEq, Eq, Debug, Clone)]
    struct ComplicatedStruct {
        id: i64,
        name: String,
        seed_range: Vec<(Method, RawValue)>,
        option1: Option<i64>,
        option2: Option<i64>,
        vec_opt: Vec<Option<i64>>,
        optopt1: Option<Option<i64>>,
        optopt2: Option<Option<i64>>,
        optopt3: Option<Option<i64>>,
        unit: (),
        sk: SecretKey,
        pk: Point,
        fancy1: Fancy,
        fancy2: Fancy,
        inner: Inner,
        tuple: Tuple,
        bytes: Bytes,
        float: Float,
        inf: Float,
        nan: Float,
        map: HashMap<String, i64>,
    }

    fn test_roundtrip<T: Serialize + DeserializeOwned + Eq + std::fmt::Debug>(t: T) {
        let depth = Params::default().max_depth_mt_containers;
        let val = t.serialize(ValueSerializer::new(depth)).unwrap();
        let out: T = Deserialize::deserialize(val.typed()).unwrap();
        assert_eq!(t, out);
    }

    fn test_roundtrip_dict<T: Serialize + DeserializeOwned + Eq + std::fmt::Debug>(t: T) {
        let depth = Params::default().max_depth_mt_containers;
        let dict = t.serialize(DictionarySerializer::new(depth)).unwrap();
        let out: T = Deserialize::deserialize(&dict).unwrap();
        assert_eq!(t, out);
    }

    fn test_dict_consistency<T: Serialize>(t: T) {
        let depth = Params::default().max_depth_mt_containers;
        let val = t.serialize(ValueSerializer::new(depth)).unwrap();
        let dict = t.serialize(DictionarySerializer::new(depth)).unwrap();
        assert_eq!(val, Value::from(dict));
    }

    fn test_dict_consistency_and_roundtrip<
        T: Serialize + DeserializeOwned + Eq + Clone + std::fmt::Debug,
    >(
        t: T,
    ) {
        test_dict_consistency(t.clone());
        test_roundtrip_dict(t)
    }

    fn test_preserved_ser<T: Serialize>(t: T)
    where
        TypedValue: From<T>,
    {
        let depth = Params::default().max_depth_mt_containers;
        let ser = t.serialize(ValueSerializer::new(depth)).unwrap();
        let val = Value::from(TypedValue::from(t));
        assert_eq!(ser, val);
    }

    fn test_preserved_de<T: DeserializeOwned + Eq + Clone + std::fmt::Debug>(t: T)
    where
        TypedValue: From<T>,
    {
        let de = T::deserialize(&TypedValue::from(t.clone())).unwrap();
        assert_eq!(de, t);
    }

    fn test_preserved<T: Serialize + DeserializeOwned + Eq + Clone + std::fmt::Debug>(t: T)
    where
        TypedValue: From<T>,
    {
        test_preserved_ser(t.clone());
        test_preserved_de(t);
    }

    fn a_hash_map() -> HashMap<String, i64> {
        let mut map = HashMap::new();
        map.insert("a".to_string(), 1);
        map.insert("b".to_string(), 2);
        map
    }

    #[test]
    fn test_complicated_struct() {
        let seed_range = vec![
            (Method::Search, RawValue::default()),
            (Method::Mine, RawValue::default()),
        ];
        let sk = SecretKey::new_rand();
        let pk = sk.public_key();
        let desc = ComplicatedStruct {
            id: 1,
            name: "a frog".to_string(),
            seed_range,
            option1: Some(2),
            option2: None,
            optopt1: Some(Some(4)),
            optopt2: Some(None),
            optopt3: None,
            vec_opt: vec![Some(3), None],
            unit: (),
            sk,
            pk,
            fancy1: Fancy::B(0, 1),
            fancy2: Fancy::C {
                x: 1,
                y: vec![2, 3],
            },
            inner: Inner {
                ch: '\u{200b}',
                b: true,
            },
            tuple: Tuple(5, 6),
            bytes: Bytes(b"abc".to_vec()),
            float: Float(3.0),
            inf: Float(f32::NEG_INFINITY),
            nan: Float(f32::NAN),
            map: a_hash_map(),
        };
        test_roundtrip(desc.clone());
        test_dict_consistency_and_roundtrip(desc);
    }

    #[test]
    fn test_dict_serialization() {
        test_dict_consistency_and_roundtrip(Fancy::B(0, 1));
        test_dict_consistency_and_roundtrip(Fancy::C {
            x: 1,
            y: vec![2, 3],
        });
        test_dict_consistency_and_roundtrip(a_hash_map());
    }

    #[test]
    fn test_pod_types() {
        let raw = RawValue::default();
        let sk = SecretKey::new_rand();
        let pt = sk.public_key();
        test_preserved(raw);
        test_preserved(sk);
        test_preserved(pt);
    }
}
