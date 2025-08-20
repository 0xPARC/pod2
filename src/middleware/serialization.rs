use std::{
    collections::{HashMap, HashSet},
    fmt::Write,
};

use plonky2::field::types::Field;
use serde::{ser::SerializeSeq, Deserialize, Serialize, Serializer};

use super::{Key, Value};
use crate::middleware::{F, HASH_SIZE, VALUE_SIZE};

fn serialize_field_tuple<S, const N: usize>(
    value: &[F; N],
    serializer: S,
) -> Result<S::Ok, S::Error>
where
    S: serde::Serializer,
{
    // `value` is little-endian in memory. We serialize it as a big-endian hex string
    // for human readability.
    let s = value
        .iter()
        .rev()
        .fold(String::with_capacity(N * 16), |mut s, limb| {
            write!(s, "{:016x}", limb.0).unwrap();
            s
        });
    serializer.serialize_str(&s)
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
// achieve this by sorting the elements. This takes advantage of the fact that
// Value implements Ord.
pub fn ordered_set<S>(value: &HashSet<Value>, serializer: S) -> Result<S::Ok, S::Error>
where
    S: Serializer,
{
    let mut set = serializer.serialize_seq(Some(value.len()))?;
    let mut sorted_values: Vec<&Value> = value.iter().collect();
    sorted_values.sort_by_key(|v| v.raw());
    for v in sorted_values {
        set.serialize_element(v)?;
    }
    set.end()
}
