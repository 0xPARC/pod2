use std::fmt::Write;

use plonky2::field::types::{Field, Field64, PrimeField64};
use serde::Deserialize;

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
    //
    // A limb below 2^32 - 1 has two possible stored forms: its value, or its value
    // plus the field's order. plonky2 skips the final reduction for speed, so hash
    // outputs hold such limbs in the second form. We always write the value, so each
    // value has exactly one encoding, and reading the hex as a number gives the value
    // the circuit sees.
    let s = value
        .iter()
        .rev()
        .fold(String::with_capacity(N * 16), |mut s, limb| {
            write!(s, "{:016x}", limb.to_canonical_u64()).unwrap();
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
        // The input may hold a limb at or above the order; reduce it like the encoder does.
        v[N - 1 - i] = F::from_canonical_u64(u64_val % F::ORDER);
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
