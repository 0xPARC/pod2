use std::array;

use num::BigUint;
use plonky2::{
    field::{
        extension::FieldExtension,
        goldilocks_field::GoldilocksField,
        types::{Field, PrimeField},
    },
    hash::{
        hash_types::HashOutTarget,
        hashing::hash_n_to_m_no_pad,
        poseidon::{PoseidonHash, PoseidonPermutation},
    },
    iop::target::Target,
    plonk::circuit_builder::CircuitBuilder,
};

use super::curve::Point;
use crate::{
    backends::plonky2::primitives::ec::{
        bits::{BigUInt320Target, CircuitBuilderBits},
        curve::{CircuitBuilderElliptic, PointTarget, GROUP_ORDER},
    },
    middleware::RawValue,
};

pub fn make_public_key(private_key: &BigUint) -> Point {
    private_key * Point::generator().inverse()
}

fn hash_array(values: &[GoldilocksField; 9]) -> [GoldilocksField; 5] {
    let hash = hash_n_to_m_no_pad::<_, PoseidonPermutation<_>>(values, 5);
    std::array::from_fn(|i| hash[i])
}

fn hash(msg: RawValue, point: Point) -> [GoldilocksField; 5] {
    // The elements of the group have distinct u-coordinates; see the comment in
    // CircuitBuilderEllptic::connect_point.  So we don't need to hash the
    // x-coordinate.
    let u_arr: [GoldilocksField; 5] = point.u.to_basefield_array();
    let values = [
        u_arr[0], u_arr[1], u_arr[2], u_arr[3], u_arr[4], msg.0[0], msg.0[1], msg.0[2], msg.0[3],
    ];
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

pub fn sign(msg: RawValue, private_key: &BigUint, nonce: &BigUint) -> (BigUint, BigUint) {
    let r = nonce * Point::generator();
    let e = convert_hash_to_biguint(&hash(msg, r));
    let s = (nonce + private_key * &e) % &*GROUP_ORDER;
    (s, e)
}

pub fn verify_signature(msg: RawValue, public_key: Point, sig1: &BigUint, sig2: &BigUint) -> bool {
    let r = sig1 * Point::generator() + sig2 * public_key;
    let e = convert_hash_to_biguint(&hash(msg, r));
    &e == sig2
}

fn hash_array_circuit(
    builder: &mut CircuitBuilder<GoldilocksField, 2>,
    inputs: &[Target; 9],
) -> [Target; 5] {
    let input_vec = inputs.as_slice().to_owned();
    let hash = builder.hash_n_to_m_no_pad::<PoseidonHash>(input_vec, 5);
    array::from_fn(|i| hash[i])
}

pub fn verify_signature_circuit(
    builder: &mut CircuitBuilder<GoldilocksField, 2>,
    msg: HashOutTarget,
    public_key: &PointTarget,
    sig1: &BigUInt320Target,
    sig2: &BigUInt320Target,
) {
    let g = builder.constant_point(Point::generator());
    let sig1_bits = builder.biguint_bits(sig1);
    let sig2_bits = builder.biguint_bits(sig2);
    let r = builder.linear_combination_points(&sig1_bits, &sig2_bits, &g, public_key);
    let u_arr = r.u.components;
    let inputs = [
        u_arr[0],
        u_arr[1],
        u_arr[2],
        u_arr[3],
        u_arr[4],
        msg.elements[0],
        msg.elements[1],
        msg.elements[2],
        msg.elements[3],
    ];
    let e_hash = hash_array_circuit(builder, &inputs);
    let e = builder.field_elements_to_biguint(&e_hash);
    builder.connect_biguint320(sig2, &e);
}

#[cfg(test)]
mod test {
    use num::BigUint;
    use num_bigint::RandBigInt;
    use plonky2::{
        field::{goldilocks_field::GoldilocksField, types::Sample},
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
                convert_hash_to_biguint, hash_array, hash_array_circuit, make_public_key, sign,
                verify_signature, verify_signature_circuit,
            },
        },
        middleware::RawValue,
    };

    fn gen_signed_message() -> (Point, RawValue, BigUint, BigUint) {
        let msg = RawValue(GoldilocksField::rand_array());
        let private_key = OsRng.gen_biguint_below(&GROUP_ORDER);
        let nonce = OsRng.gen_biguint_below(&GROUP_ORDER);
        let public_key = make_public_key(&private_key);
        let (sig1, sig2) = sign(msg, &private_key, &nonce);
        (public_key, msg, sig1, sig2)
    }

    #[test]
    fn test_verify_signature() {
        let (public_key, msg, sig1, sig2) = gen_signed_message();
        assert!(&sig1 < &GROUP_ORDER);
        assert!(verify_signature(msg, public_key, &sig1, &sig2));
    }

    #[test]
    fn test_reject_bogus_signature() {
        let msg = RawValue(GoldilocksField::rand_array());
        let private_key = OsRng.gen_biguint_below(&GROUP_ORDER);
        let nonce = OsRng.gen_biguint_below(&GROUP_ORDER);
        let public_key = make_public_key(&private_key);
        let (sig1, sig2) = sign(msg, &private_key, &nonce);
        let junk = OsRng.gen_biguint_below(&GROUP_ORDER);
        assert!(!verify_signature(msg, public_key, &sig1, &junk));
        assert!(!verify_signature(msg, public_key, &junk, &sig2));
    }

    #[test]
    fn test_verify_signature_circuit() -> Result<(), anyhow::Error> {
        let (public_key, msg, sig1, sig2) = gen_signed_message();
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<GoldilocksField, 2>::new(config);
        let key_t = builder.add_virtual_point_target();
        let msg_t = builder.add_virtual_hash();
        let sig1_t = builder.add_virtual_biguint320_target();
        let sig2_t = builder.add_virtual_biguint320_target();
        verify_signature_circuit(&mut builder, msg_t, &key_t, &sig1_t, &sig2_t);
        let mut pw = PartialWitness::new();
        pw.set_point_target(&key_t, &public_key)?;
        pw.set_hash_target(msg_t, msg.0.into())?;
        pw.set_biguint320_target(&sig1_t, &sig1)?;
        pw.set_biguint320_target(&sig2_t, &sig2)?;
        let data = builder.build::<PoseidonGoldilocksConfig>();
        let proof = data.prove(pw)?;
        data.verify(proof)?;
        Ok(())
    }

    #[test]
    fn test_reject_bogus_signature_circuit() {
        let (public_key, msg, sig1, sig2) = gen_signed_message();
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<GoldilocksField, 2>::new(config);
        let key_t = builder.constant_point(public_key);
        let msg_t = builder.constant_hash(msg.0.into());
        let sig1_t = builder.constant_biguint320(&sig1);
        let sig2_t = builder.constant_biguint320(&sig2);
        // sig1 and sig2 are passed out of order
        verify_signature_circuit(&mut builder, msg_t, &key_t, &sig2_t, &sig1_t);
        let pw = PartialWitness::new();
        let data = builder.build::<PoseidonGoldilocksConfig>();
        assert!(data.prove(pw).is_err());
    }

    #[test]
    fn test_hash_consistency() -> Result<(), anyhow::Error> {
        let values = GoldilocksField::rand_array();
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
        let pw = PartialWitness::new();
        let data = builder.build::<PoseidonGoldilocksConfig>();
        let proof = data.prove(pw)?;
        data.verify(proof)?;
        Ok(())
    }
}
