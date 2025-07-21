use plonky2::{
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

use crate::backends::plonky2::basetypes::{CircuitData, C, D, F};

// TODO: Add pod2 custom gates
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
        ReducingGate<D>
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
        WireSplitGenerator
    }
}

#[derive(Clone)]
pub(crate) struct CircuitDataSerializer(pub(crate) CircuitData);

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
        serializer.serialize_bytes(&bytes)
    }
}

impl<'de> Deserialize<'de> for CircuitDataSerializer {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let gate_serializer = Pod2GateSerializer {};
        let generator_serializer = Pod2GeneratorSerializer {};
        let bytes = Vec::<u8>::deserialize(deserializer)?;
        let circuit_data = CircuitData::from_bytes(&bytes, &gate_serializer, &generator_serializer)
            .map_err(de::Error::custom)?;
        Ok(CircuitDataSerializer(circuit_data))
    }
}
