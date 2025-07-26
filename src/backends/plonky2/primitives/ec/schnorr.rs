use std::{array, fmt, str::FromStr};

use num::BigUint;
use num_bigint::RandBigInt;
use plonky2::{
    field::{
        extension::FieldExtension,
        goldilocks_field::GoldilocksField,
        types::{Field, PrimeField, PrimeField64},
    },
    hash::{
        hash_types::HashOutTarget,
        hashing::hash_n_to_m_no_pad,
        poseidon::{PoseidonHash, PoseidonPermutation},
    },
    iop::{
        target::{BoolTarget, Target},
        witness::WitnessWrite,
    },
    plonk::circuit_builder::CircuitBuilder,
};
use rand::rngs::OsRng;
use serde::{Deserialize, Deserializer, Serialize, Serializer};

use super::curve::Point;
use crate::{
    backends::plonky2::{
        circuits::common::CircuitBuilderPod,
        deserialize_bytes,
        primitives::ec::{
            bits::{BigUInt320Target, CircuitBuilderBits},
            curve::{CircuitBuilderElliptic, PointTarget, WitnessWriteCurve, GROUP_ORDER},
        },
        serialize_bytes, Error,
    },
    middleware::RawValue,
};

/// Schnorr signature over ecGFp5.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Signature {
    pub s: BigUint,
    pub e: BigUint,
}

impl Signature {
    pub fn verify(&self, public_key: Point, msg: RawValue) -> bool {
        let r = &self.s * Point::generator() + &self.e * public_key;
        let e = convert_hash_to_biguint(&hash(msg, r));
        e == self.e
    }
    pub fn as_bytes(&self) -> Vec<u8> {
        let s_bytes = self
            .s
            .to_bytes_le()
            .into_iter()
            .chain(std::iter::repeat(0u8))
            .take(40);
        let e_bytes = self
            .e
            .to_bytes_le()
            .into_iter()
            .chain(std::iter::repeat(0u8))
            .take(40);
        s_bytes.chain(e_bytes).collect()
    }
    pub fn from_bytes(sig_bytes: &[u8]) -> Result<Self, Error> {
        if sig_bytes.len() != 80 {
            return Err(Error::custom(
                "Invalid byte encoding of Schnorr signature.".to_string(),
            ));
        }

        let s = BigUint::from_bytes_le(&sig_bytes[..40]);
        let e = BigUint::from_bytes_le(&sig_bytes[40..]);

        Ok(Self { s, e })
    }
}

impl Serialize for Signature {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let signature_b64 = serialize_bytes(&self.as_bytes());
        serializer.serialize_str(&signature_b64)
    }
}

impl<'de> Deserialize<'de> for Signature {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let signature_b64 = String::deserialize(deserializer)?;
        let signature_bytes =
            deserialize_bytes(&signature_b64).map_err(serde::de::Error::custom)?;
        Signature::from_bytes(&signature_bytes).map_err(serde::de::Error::custom)
    }
}

/// Targets for Schnorr signature over ecGFp5.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SignatureTarget {
    pub s: BigUInt320Target,
    pub e: BigUInt320Target,
}

pub trait CircuitBuilderSchnorr {
    fn add_virtual_schnorr_signature_target(&mut self) -> SignatureTarget;
}

impl CircuitBuilderSchnorr for CircuitBuilder<GoldilocksField, 2> {
    fn add_virtual_schnorr_signature_target(&mut self) -> SignatureTarget {
        SignatureTarget {
            s: self.add_virtual_biguint320_target(),
            e: self.add_virtual_biguint320_target(),
        }
    }
}

pub trait WitnessWriteSchnorr: WitnessWrite<GoldilocksField> + WitnessWriteCurve {
    fn set_signature_target(
        &mut self,
        target: &SignatureTarget,
        value: &Signature,
    ) -> anyhow::Result<()> {
        self.set_biguint320_target(&target.s, &value.s)?;
        self.set_biguint320_target(&target.e, &value.e)
    }
}

impl<W: WitnessWrite<GoldilocksField>> WitnessWriteSchnorr for W {}

// TODO: Rename this to a function `verify_signature_circuit`?  I think this convention is also
// nice as an object-oriented alternative to `verb_object_circuit` methods.  It's clear that this
// is constraining vs native operation because the type is `*Target`.  But of course this
// convention doesn't work for all situations.
impl SignatureTarget {
    pub fn verify(
        &self,
        builder: &mut CircuitBuilder<GoldilocksField, 2>,
        msg: HashOutTarget,
        public_key: &PointTarget,
    ) -> BoolTarget {
        let g = builder.constant_point(Point::generator());
        let sig1_bits = self.s.bits;
        let sig2_bits = self.e.bits;
        let r = builder.linear_combination_points(&sig1_bits, &sig2_bits, &g, public_key);
        let u_arr = r.u.components;
        let inputs = u_arr.into_iter().chain(msg.elements).collect::<Vec<_>>();
        let e_hash = hash_array_circuit(builder, &inputs);
        let e = builder.field_elements_to_biguint(&e_hash);
        builder.is_equal_slice(&self.e.limbs, &e.limbs)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SecretKey(pub BigUint);

impl SecretKey {
    pub fn new_rand() -> Self {
        Self(OsRng.gen_biguint_below(&GROUP_ORDER))
    }
    pub fn public_key(&self) -> Point {
        &self.0 * Point::generator().inverse()
    }

    pub fn sign(&self, msg: RawValue, nonce: &BigUint) -> Signature {
        let r = nonce * Point::generator();
        let e = convert_hash_to_biguint(&hash(msg, r));
        let s = (nonce + &self.0 * &e) % &*GROUP_ORDER;
        Signature { s, e }
    }

    pub fn as_bytes(&self) -> Vec<u8> {
        let bytes = self.0.to_bytes_le();
        assert!(bytes.len() <= 40);
        bytes
            .into_iter()
            .chain(std::iter::repeat(0u8))
            .take(40)
            .collect()
    }

    pub fn from_bytes(sk_bytes: &[u8]) -> Result<Self, Error> {
        if sk_bytes.len() != 40 {
            return Err(Error::custom(
                "Invalid byte encoding of Schnorr secret key.".to_string(),
            ));
        }

        let big_uint = BigUint::from_bytes_le(sk_bytes);

        if big_uint >= *GROUP_ORDER {
            return Err(Error::custom(
                "Invalid Schnorr secret key - not less than group order.".to_string(),
            ));
        }

        Ok(Self(big_uint))
    }

    pub fn to_limbs(&self) -> [GoldilocksField; 10] {
        assert!(self.0.bits() <= 320);
        let digits = self.0.to_u32_digits();
        array::from_fn(|i| {
            let d = digits.get(i).copied().unwrap_or(0);
            GoldilocksField::from_canonical_u32(d)
        })
    }

    pub fn from_limbs(limbs: [GoldilocksField; 10]) -> Result<Self, Error> {
        let mut limb_vec = vec![];
        for gl in limbs.iter() {
            let g64 = gl.to_canonical_u64();
            if g64 >= (1 << 32) {
                return Err(Error::custom(
                    "Invalid limb value in Schnorr secret key.".to_string(),
                ));
            }
            limb_vec.push(g64 as u32);
        }

        Ok(Self(BigUint::from_slice(&limb_vec)))
    }
}

impl Serialize for SecretKey {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let sk_b64 = serialize_bytes(&self.as_bytes());
        serializer.serialize_str(&sk_b64)
    }
}

impl<'de> Deserialize<'de> for SecretKey {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let sk_b64 = String::deserialize(deserializer)?;
        let sk_bytes = deserialize_bytes(&sk_b64).map_err(serde::de::Error::custom)?;
        SecretKey::from_bytes(&sk_bytes).map_err(serde::de::Error::custom)
    }
}

impl fmt::Display for SecretKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", serialize_bytes(self.as_bytes().as_slice()))
    }
}

impl FromStr for SecretKey {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let sk_bytes = deserialize_bytes(s)?;
        SecretKey::from_bytes(&sk_bytes)
    }
}

impl SignatureTarget {
    pub fn add_virtual_target(builder: &mut CircuitBuilder<GoldilocksField, 2>) -> Self {
        Self {
            s: builder.add_virtual_biguint320_target(),
            e: builder.add_virtual_biguint320_target(),
        }
    }
}

fn hash_array(values: &[GoldilocksField]) -> [GoldilocksField; 5] {
    let hash = hash_n_to_m_no_pad::<_, PoseidonPermutation<_>>(values, 5);
    std::array::from_fn(|i| hash[i])
}

fn hash(msg: RawValue, point: Point) -> [GoldilocksField; 5] {
    // The elements of the group have distinct u-coordinates; see the comment in
    // CircuitBuilderEllptic::connect_point.  So we don't need to hash the
    // x-coordinate.
    let u_arr: [GoldilocksField; 5] = point.u.to_basefield_array();
    let values: Vec<_> = u_arr.into_iter().chain(msg.0).collect();
    hash_array(&values)
}

fn convert_hash_to_biguint(hash: &[GoldilocksField; 5]) -> BigUint {
    let mut ans = BigUint::ZERO;
    for val in hash.iter().rev() {
        ans *= GoldilocksField::order();
        ans += val.to_canonical_biguint();
    }
    ans
}

fn hash_array_circuit(
    builder: &mut CircuitBuilder<GoldilocksField, 2>,
    inputs: &[Target],
) -> [Target; 5] {
    let input_vec = inputs.to_owned();
    let hash = builder.hash_n_to_m_no_pad::<PoseidonHash>(input_vec, 5);
    array::from_fn(|i| hash[i])
}

#[cfg(test)]
mod test {
    use itertools::Itertools;
    use num::BigUint;
    use num_bigint::RandBigInt;
    use plonky2::{
        field::{
            goldilocks_field::GoldilocksField,
            types::{Field, Sample},
        },
        iop::{
            target::Target,
            witness::{PartialWitness, WitnessWrite},
        },
        plonk::{
            circuit_builder::CircuitBuilder, circuit_data::CircuitConfig,
            config::PoseidonGoldilocksConfig,
        },
    };
    use rand::rngs::OsRng;

    use crate::{
        backends::plonky2::primitives::ec::{
            bits::CircuitBuilderBits,
            curve::{CircuitBuilderElliptic, Point, WitnessWriteCurve, GROUP_ORDER},
            schnorr::{
                convert_hash_to_biguint, hash_array, hash_array_circuit, SecretKey, Signature,
                SignatureTarget,
            },
        },
        middleware::RawValue,
    };

    fn gen_signed_message() -> (Point, RawValue, Signature) {
        let msg = RawValue(GoldilocksField::rand_array());
        let private_key = SecretKey(OsRng.gen_biguint_below(&GROUP_ORDER));
        let nonce = OsRng.gen_biguint_below(&GROUP_ORDER);
        let public_key = private_key.public_key();
        let sig = private_key.sign(msg, &nonce);
        (public_key, msg, sig)
    }

    #[test]
    fn test_key_pairs() -> Result<(), anyhow::Error> {
        let fixed_sk = SecretKey(BigUint::from(0x1234567890abcdefu64));
        let fixed_sk_expected_str = "782rkHhWNBIAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA==";
        assert_eq!(fixed_sk.to_string(), fixed_sk_expected_str);
        let parsed_sk = fixed_sk_expected_str.parse::<SecretKey>()?;
        assert_eq!(fixed_sk, parsed_sk);

        let fixed_pk = fixed_sk.public_key();
        let fixed_pk_expected_str = "8sctoHc2aduKbYtZwo7Z3v7YugSuimLUMAhE95V18CWU55tWMvZxEqA";
        assert_eq!(fixed_pk.to_string(), fixed_pk_expected_str);
        let parsed_pk = fixed_pk_expected_str.parse::<Point>()?;
        assert_eq!(fixed_pk, parsed_pk);

        let rand_sk = SecretKey::new_rand();
        assert_ne!(fixed_sk, rand_sk);
        assert_eq!(rand_sk, rand_sk.to_string().parse::<SecretKey>()?);
        let rand_pk = rand_sk.public_key();
        assert_ne!(fixed_pk, rand_pk);

        Ok(())
    }

    #[test]
    fn test_verify_signature() {
        let (public_key, msg, sig) = gen_signed_message();
        assert!(&sig.s < &GROUP_ORDER);
        assert!(sig.verify(public_key, msg));
    }

    #[test]
    fn test_reject_bogus_signature() {
        let msg = RawValue(GoldilocksField::rand_array());
        let private_key = SecretKey(OsRng.gen_biguint_below(&GROUP_ORDER));
        let nonce = OsRng.gen_biguint_below(&GROUP_ORDER);
        let public_key = private_key.public_key();
        let sig = private_key.sign(msg, &nonce);
        let junk = OsRng.gen_biguint_below(&GROUP_ORDER);
        assert!(!Signature {
            s: sig.s.clone(),
            e: junk.clone()
        }
        .verify(public_key, msg));
        assert!(!Signature { s: junk, e: sig.e }.verify(public_key, msg));
    }

    #[test]
    fn test_verify_signature_circuit() -> Result<(), anyhow::Error> {
        let (public_key, msg, sig) = gen_signed_message();
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<GoldilocksField, 2>::new(config);
        let key_t = builder.add_virtual_point_target();
        let msg_t = builder.add_virtual_hash();
        let sig_t = SignatureTarget::add_virtual_target(&mut builder);
        let verified = sig_t.verify(&mut builder, msg_t, &key_t);
        builder.assert_one(verified.target);
        let mut pw = PartialWitness::new();
        pw.set_point_target(&key_t, &public_key)?;
        pw.set_hash_target(msg_t, msg.0.into())?;
        pw.set_biguint320_target(&sig_t.s, &sig.s)?;
        pw.set_biguint320_target(&sig_t.e, &sig.e)?;
        let data = builder.build::<PoseidonGoldilocksConfig>();
        let proof = data.prove(pw)?;
        data.verify(proof)?;
        Ok(())
    }

    #[test]
    fn test_reject_bogus_signature_circuit() {
        let (public_key, msg, sig) = gen_signed_message();
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<GoldilocksField, 2>::new(config);
        let key_t = builder.constant_point(public_key);
        let msg_t = builder.constant_hash(msg.0.into());
        // sig.s and sig.e are passed out of order
        let sig_t = SignatureTarget {
            s: builder.constant_biguint320(&sig.e),
            e: builder.constant_biguint320(&sig.s),
        };
        let verified = sig_t.verify(&mut builder, msg_t, &key_t);
        builder.assert_one(verified.target);
        let pw = PartialWitness::new();
        let data = builder.build::<PoseidonGoldilocksConfig>();
        assert!(data.prove(pw).is_err());
    }

    #[test]
    fn test_hash_consistency() -> Result<(), anyhow::Error> {
        let values = GoldilocksField::rand_array::<9>();
        let hash = hash_array(&values);
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<GoldilocksField, 2>::new(config);
        let values_const = values.map(|v| builder.constant(v));
        let hash_const = hash.map(|v| builder.constant(v));
        let hash_circuit = hash_array_circuit(&mut builder, &values_const);
        for i in 0..5 {
            builder.connect(hash_const[i], hash_circuit[i]);
        }
        let pw = PartialWitness::new();
        let data = builder.build::<PoseidonGoldilocksConfig>();
        let proof = data.prove(pw)?;
        data.verify(proof)?;
        Ok(())
    }

    #[test]
    fn test_hash_to_bigint_consistency() -> Result<(), anyhow::Error> {
        let hash = GoldilocksField::rand_array();
        let hash_int = convert_hash_to_biguint(&hash);
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<GoldilocksField, 2>::new(config);
        let hash_const: [Target; 5] = std::array::from_fn(|i| builder.constant(hash[i]));
        let int_const = builder.constant_biguint320(&hash_int);
        let int_circuit = builder.field_elements_to_biguint(&hash_const);
        builder.connect_biguint320(&int_const, &int_circuit);
        println!("{}", builder.num_gates());
        let pw = PartialWitness::new();
        let data = builder.build::<PoseidonGoldilocksConfig>();
        let proof = data.prove(pw)?;
        data.verify(proof)?;
        Ok(())
    }

    #[test]
    fn test_secret_key_serialization() -> Result<(), anyhow::Error> {
        let sk_123 = SecretKey(BigUint::from(123u32));
        let str_123 = serde_json::to_string(&sk_123).unwrap();
        let deser_123 = serde_json::from_str(&str_123).unwrap();
        assert_eq!(sk_123, deser_123);

        let sk_rand = SecretKey::new_rand();
        assert_ne!(sk_123, sk_rand);
        let str_rand = serde_json::to_string(&sk_rand).unwrap();
        let deser_rand = serde_json::from_str(&str_rand).unwrap();
        assert_eq!(sk_rand, deser_rand);

        let sk_max = SecretKey(&*GROUP_ORDER - 1u32);
        assert_ne!(sk_123, sk_max);
        let str_max = serde_json::to_string(&sk_max).unwrap();
        let deser_max = serde_json::from_str(&str_max).unwrap();
        assert_eq!(sk_max, deser_max);

        // Value is too big for group but fits within 320 bits.  Thus it
        // survives the assert in as_bytes(), but gets caught during deserialization.
        let sk_toobig = SecretKey(GROUP_ORDER.clone());
        assert_ne!(sk_toobig, sk_123);
        let str_toobig = serde_json::to_string(&sk_toobig).unwrap();
        assert!(serde_json::from_str::<SecretKey>(&str_toobig).is_err());

        Ok(())
    }

    #[test]
    fn test_secret_key_limbs() -> Result<(), anyhow::Error> {
        let sk_0 = SecretKey(BigUint::from(0u32));
        let limbs_0 = sk_0.to_limbs();
        assert_eq!(limbs_0, [GoldilocksField::from_canonical_u32(0); 10]);
        let rsk_0 = SecretKey::from_limbs(limbs_0).unwrap();
        assert_eq!(sk_0, rsk_0);

        let sk_n: SecretKey = SecretKey(BigUint::from_slice((0..10).collect_vec().as_slice()));
        let limbs_n = sk_n.to_limbs();
        assert_eq!(
            limbs_n.as_slice(),
            (0..10)
                .map(GoldilocksField::from_canonical_u32)
                .collect_vec()
                .as_slice()
        );
        let rsk_n = SecretKey::from_limbs(limbs_n).unwrap();
        assert_eq!(sk_n, rsk_n);

        assert!(SecretKey::from_limbs(
            (0..9)
                .chain([9u64 << 32])
                .map(GoldilocksField::from_canonical_u64)
                .collect_vec()
                .as_slice()
                .try_into()
                .unwrap(),
        )
        .is_err());

        Ok(())
    }
}
