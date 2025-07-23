use std::ops::Deref;

use plonky2::{
    field::extension::quintic::QuinticExtension,
    gates::{
        arithmetic_base::ArithmeticGate, arithmetic_extension::ArithmeticExtensionGate,
        base_sum::BaseSumGate, constant::ConstantGate, coset_interpolation::CosetInterpolationGate,
        exponentiation::ExponentiationGate, lookup::LookupGate, lookup_table::LookupTableGate,
        multiplication_extension::MulExtensionGate, noop::NoopGate, poseidon::PoseidonGate,
        poseidon_mds::PoseidonMdsGate, public_input::PublicInputGate,
        random_access::RandomAccessGate, reducing::ReducingGate,
        reducing_extension::ReducingExtensionGate,
    },
    get_gate_tag_impl, impl_gate_serializer, read_gate_impl,
    util::serialization::GateSerializer,
};
use serde::{de, ser, Deserialize, Serialize};

use crate::backends::plonky2::{
    basetypes::{CircuitData, CommonCircuitData, VerifierCircuitData, C, D, F},
    circuits::{common::LtMaskGenerator, utils::DebugGenerator},
    primitives::ec::{
        bits::ConditionalZeroGenerator,
        curve::PointSquareRootGenerator,
        field::QuotientGeneratorOEF,
        gates::{
            curve::ECAddHomogOffset,
            field::NNFMulSimple,
            generic::{GateAdapter, RecursiveGateAdapter, RecursiveGenerator},
        },
    },
};

#[derive(Debug)]
pub(crate) struct Pod2GateSerializer;
impl GateSerializer<F, D> for Pod2GateSerializer {
    impl_gate_serializer! {
        Pod2GateSerializer,
        ArithmeticGate,
        ArithmeticExtensionGate<D>,
        BaseSumGate<2>,
        ConstantGate,
        CosetInterpolationGate<F, D>,
        ExponentiationGate<F, D>,
        LookupGate,
        LookupTableGate,
        MulExtensionGate<D>,
        NoopGate,
        PoseidonMdsGate<F, D>,
        PoseidonGate<F, D>,
        PublicInputGate,
        RandomAccessGate<F, D>,
        ReducingExtensionGate<D>,
        ReducingGate<D>,
        // pod2 custom gates
        GateAdapter::<NNFMulSimple<5, QuinticExtension<F>>>,
        RecursiveGateAdapter::<D, NNFMulSimple<5, QuinticExtension<F>>>,
        GateAdapter::<ECAddHomogOffset>,
        RecursiveGateAdapter::<D, ECAddHomogOffset>
    }
}

use plonky2::{
    gadgets::{
        arithmetic::EqualityGenerator,
        arithmetic_extension::QuotientGeneratorExtension,
        range_check::LowHighGenerator,
        split_base::BaseSumGenerator,
        split_join::{SplitGenerator, WireSplitGenerator},
    },
    gates::{
        arithmetic_base::ArithmeticBaseGenerator,
        arithmetic_extension::ArithmeticExtensionGenerator, base_sum::BaseSplitGenerator,
        coset_interpolation::InterpolationGenerator, exponentiation::ExponentiationGenerator,
        lookup::LookupGenerator, lookup_table::LookupTableGenerator,
        multiplication_extension::MulExtensionGenerator, poseidon::PoseidonGenerator,
        poseidon_mds::PoseidonMdsGenerator, random_access::RandomAccessGenerator,
        reducing::ReducingGenerator,
        reducing_extension::ReducingGenerator as ReducingExtensionGenerator,
    },
    get_generator_tag_impl, impl_generator_serializer,
    iop::generator::{
        ConstantGenerator, CopyGenerator, NonzeroTestGenerator, RandomValueGenerator,
    },
    read_generator_impl,
    recursion::dummy_circuit::DummyProofGenerator,
    util::serialization::WitnessGeneratorSerializer,
};

#[derive(Debug)]
pub(crate) struct Pod2GeneratorSerializer {}

// TODO: Add pod2 custom generators
impl WitnessGeneratorSerializer<F, D> for Pod2GeneratorSerializer {
    impl_generator_serializer! {
        Pod2GeneratorSerializer,
        ArithmeticBaseGenerator<F, D>,
        ArithmeticExtensionGenerator<F, D>,
        BaseSplitGenerator<2>,
        BaseSumGenerator<2>,
        ConstantGenerator<F>,
        CopyGenerator,
        DummyProofGenerator<F, C, D>,
        EqualityGenerator,
        ExponentiationGenerator<F, D>,
        InterpolationGenerator<F, D>,
        LookupGenerator,
        LookupTableGenerator,
        LowHighGenerator,
        MulExtensionGenerator<F, D>,
        NonzeroTestGenerator,
        PoseidonGenerator<F, D>,
        PoseidonMdsGenerator<D>,
        QuotientGeneratorExtension<D>,
        RandomAccessGenerator<F, D>,
        RandomValueGenerator,
        ReducingGenerator<D>,
        ReducingExtensionGenerator<D>,
        SplitGenerator,
        WireSplitGenerator,
        // pod2 custom generators
        DebugGenerator,
        LtMaskGenerator,
        QuotientGeneratorOEF<5, QuinticExtension<F>>,
        PointSquareRootGenerator,
        ConditionalZeroGenerator<F, D>,
        RecursiveGenerator<D, NNFMulSimple<5, QuinticExtension<F>>>,
        RecursiveGenerator<1, NNFMulSimple<5, QuinticExtension<F>>>,
        RecursiveGenerator<D, ECAddHomogOffset>,
        RecursiveGenerator<1, ECAddHomogOffset>
    }
}

/// Helper type to serialize and deserialize the pod2 `CircuitData` using serde traits.
#[derive(Clone)]
pub struct CircuitDataSerializer(pub(crate) CircuitData);

impl Deref for CircuitDataSerializer {
    type Target = CircuitData;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl Serialize for CircuitDataSerializer {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let gate_serializer = Pod2GateSerializer {};
        let generator_serializer = Pod2GeneratorSerializer {};
        let bytes = self
            .0
            .to_bytes(&gate_serializer, &generator_serializer)
            .map_err(ser::Error::custom)?;
        serde_bytes::ByteBuf::from(bytes).serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for CircuitDataSerializer {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let bytes = <&'de serde_bytes::Bytes>::deserialize(deserializer)?;
        let gate_serializer = Pod2GateSerializer {};
        let generator_serializer = Pod2GeneratorSerializer {};
        let circuit_data = CircuitData::from_bytes(bytes, &gate_serializer, &generator_serializer)
            .map_err(de::Error::custom)?;
        Ok(CircuitDataSerializer(circuit_data))
    }
}

/// Helper type to serialize and deserialize the pod2 `CommonCircuitData` using serde traits.
#[derive(Clone)]
pub struct CommonCircuitDataSerializer(pub(crate) CommonCircuitData);

impl Deref for CommonCircuitDataSerializer {
    type Target = CommonCircuitData;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl Serialize for CommonCircuitDataSerializer {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let gate_serializer = Pod2GateSerializer {};
        let bytes = self
            .0
            .to_bytes(&gate_serializer)
            .map_err(ser::Error::custom)?;
        serde_bytes::ByteBuf::from(bytes).serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for CommonCircuitDataSerializer {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let bytes = <&'de serde_bytes::Bytes>::deserialize(deserializer)?;
        let gate_serializer = Pod2GateSerializer {};
        let circuit_data =
            CommonCircuitData::from_bytes(bytes, &gate_serializer).map_err(de::Error::custom)?;
        Ok(CommonCircuitDataSerializer(circuit_data))
    }
}

/// Helper type to serialize and deserialize the pod2 `VerifierCircuitData` using serde traits.
#[derive(Clone)]
pub struct VerifierCircuitDataSerializer(pub(crate) VerifierCircuitData);

impl Deref for VerifierCircuitDataSerializer {
    type Target = VerifierCircuitData;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl Serialize for VerifierCircuitDataSerializer {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let gate_serializer = Pod2GateSerializer {};
        let bytes = self
            .0
            .to_bytes(&gate_serializer)
            .map_err(ser::Error::custom)?;
        serde_bytes::ByteBuf::from(bytes).serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for VerifierCircuitDataSerializer {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let bytes = <&'de serde_bytes::Bytes>::deserialize(deserializer)?;

        let gate_serializer = Pod2GateSerializer {};
        let circuit_data =
            VerifierCircuitData::from_bytes(bytes, &gate_serializer).map_err(de::Error::custom)?;
        Ok(VerifierCircuitDataSerializer(circuit_data))
    }
}
