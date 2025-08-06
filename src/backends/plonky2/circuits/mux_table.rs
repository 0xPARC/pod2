use std::iter;

use itertools::Itertools;
use plonky2::{
    field::{extension::Extendable, types::Field},
    hash::{
        hash_types::{HashOutTarget, RichField},
        poseidon::{PoseidonHash, PoseidonPermutation},
    },
    iop::{
        generator::{GeneratedValues, SimpleGenerator},
        target::{BoolTarget, Target},
        witness::{PartitionWitness, Witness, WitnessWrite},
    },
    plonk::circuit_data::CommonCircuitData,
    util::serialization::{Buffer, IoResult, Read, Write},
};

use crate::{
    backends::plonky2::{
        basetypes::CircuitBuilder,
        circuits::{
            common::{CircuitBuilderPod, Flattenable, IndexTarget},
            hash::{hash_from_state_circuit, precompute_hash_state},
        },
    },
    measure_gates_begin, measure_gates_end,
    middleware::{Params, F},
};

// This structure allows multiplexing multiple tables into one by using tags.  The table entries
// are computed by hashing the concatenation of the tag with the flattened target, with zero
// padding to normalize the size of all flattened entries.  We use zero-padding on then reverse the
// array so that smaller entries can skip the initial hashes by using the precomputed hash state of
// the prefixed zeroes.
// The table offers an indexing API that returns a flattened entry that includes the "unhashing",
// this allows doing a single lookup for different possible tagged entries at the same time.
pub struct MuxTableTarget {
    params: Params,
    max_flattened_entry_len: usize,
    hashed_tagged_entries: Vec<HashOutTarget>,
    tagged_entries: Vec<Vec<Target>>,
}

impl MuxTableTarget {
    pub fn new(params: &Params, max_flattened_entry_len: usize) -> Self {
        Self {
            params: params.clone(),
            max_flattened_entry_len,
            hashed_tagged_entries: Vec::new(),
            tagged_entries: Vec::new(),
        }
    }

    #[allow(clippy::len_without_is_empty)]
    pub fn len(&self) -> usize {
        self.hashed_tagged_entries.len()
    }

    pub fn push<T: Flattenable>(&mut self, builder: &mut CircuitBuilder, tag: u32, entry: &T) {
        let flattened_entry = entry.flatten();
        self.push_flattened(builder, tag, &flattened_entry);
    }

    pub fn push_flattened(
        &mut self,
        builder: &mut CircuitBuilder,
        tag: u32,
        flattened_entry: &[Target],
    ) {
        let measure = measure_gates_begin!(builder, "HashTaggedTblEntry");
        assert!(flattened_entry.len() <= self.max_flattened_entry_len);
        let flattened = [&[builder.constant(F(tag as u64))], flattened_entry].concat();
        self.tagged_entries.push(flattened.clone());

        let tagged_entry_max_len = 1 + self.max_flattened_entry_len;
        let front_pad_elts = iter::repeat(F::ZERO)
            .take(tagged_entry_max_len - flattened.len())
            .collect_vec();

        let (perm, front_pad_elts_rem) =
            precompute_hash_state::<F, PoseidonPermutation<F>>(&front_pad_elts);

        let rev_flattened = flattened.iter().rev().copied();
        // Precompute the Poseidon state for the initial padding chunks
        let inputs = front_pad_elts_rem
            .iter()
            .map(|v| builder.constant(*v))
            .chain(rev_flattened)
            .collect_vec();
        let hash =
            hash_from_state_circuit::<PoseidonHash, PoseidonPermutation<F>>(builder, perm, &inputs);

        measure_gates_end!(builder, measure);
        self.hashed_tagged_entries.push(hash);
    }

    pub fn get(&self, builder: &mut CircuitBuilder, index: &IndexTarget) -> TableEntryTarget {
        let measure = measure_gates_begin!(builder, "GetTaggedTblEntry");
        let entry_hash = builder.vec_ref(&self.params, &self.hashed_tagged_entries, index);

        let mut rev_resolved_tagged_flattened =
            builder.add_virtual_targets(1 + self.max_flattened_entry_len);
        let query_hash =
            builder.hash_n_to_hash_no_pad::<PoseidonHash>(rev_resolved_tagged_flattened.clone());
        builder.connect_flattenable(&entry_hash, &query_hash);
        rev_resolved_tagged_flattened.reverse();
        let resolved_tagged_flattened = rev_resolved_tagged_flattened;

        builder.add_simple_generator(TableGetGenerator {
            index: index.clone(),
            tagged_entries: self.tagged_entries.clone(),
            get_tagged_entry: resolved_tagged_flattened.clone(),
        });
        measure_gates_end!(builder, measure);
        TableEntryTarget {
            params: self.params.clone(),
            tagged_flattened_entry: resolved_tagged_flattened,
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct TableGetGenerator {
    index: IndexTarget,
    tagged_entries: Vec<Vec<Target>>,
    get_tagged_entry: Vec<Target>,
}

impl<F: RichField + Extendable<D>, const D: usize> SimpleGenerator<F, D> for TableGetGenerator {
    fn id(&self) -> String {
        "TableGetGenerator".to_string()
    }

    fn dependencies(&self) -> Vec<Target> {
        [self.index.low, self.index.high]
            .into_iter()
            .chain(self.tagged_entries.iter().flatten().copied())
            .collect()
    }

    fn run_once(
        &self,
        witness: &PartitionWitness<F>,
        out_buffer: &mut GeneratedValues<F>,
    ) -> anyhow::Result<()> {
        let index_low = witness.get_target(self.index.low);
        let index_high = witness.get_target(self.index.high);
        let index = (index_low + index_high * F::from_canonical_usize(1 << 6)).to_canonical_u64();

        let entry = witness.get_targets(&self.tagged_entries[index as usize]);

        for (target, value) in self.get_tagged_entry.iter().zip(
            entry
                .iter()
                .chain(iter::repeat(&F::ZERO).take(self.get_tagged_entry.len())),
        ) {
            out_buffer.set_target(*target, *value)?;
        }

        Ok(())
    }

    fn serialize(&self, dst: &mut Vec<u8>, _common_data: &CommonCircuitData<F, D>) -> IoResult<()> {
        dst.write_usize(self.index.max_array_len)?;
        dst.write_target(self.index.low)?;
        dst.write_target(self.index.high)?;

        dst.write_usize(self.tagged_entries.len())?;
        for tagged_entry in &self.tagged_entries {
            dst.write_target_vec(tagged_entry)?;
        }

        dst.write_target_vec(&self.get_tagged_entry)
    }

    fn deserialize(src: &mut Buffer, _common_data: &CommonCircuitData<F, D>) -> IoResult<Self> {
        let index = IndexTarget {
            max_array_len: src.read_usize()?,
            low: src.read_target()?,
            high: src.read_target()?,
        };
        let len = src.read_usize()?;
        let mut tagged_entries = Vec::with_capacity(len);
        for _ in 0..len {
            tagged_entries.push(src.read_target_vec()?);
        }
        let get_tagged_entry = src.read_target_vec()?;

        Ok(Self {
            index,
            tagged_entries,
            get_tagged_entry,
        })
    }
}

pub struct TableEntryTarget {
    params: Params,
    tagged_flattened_entry: Vec<Target>,
}

impl TableEntryTarget {
    pub fn as_type<T: Flattenable>(
        &self,
        builder: &mut CircuitBuilder,
        tag: u32,
    ) -> (BoolTarget, T) {
        let tag_target = self.tagged_flattened_entry[0];
        let flattened_entry = &self.tagged_flattened_entry[1..];
        let entry = T::from_flattened(&self.params, &flattened_entry[..T::size(&self.params)]);
        let tag_expect = builder.constant(F(tag as u64));
        let tag_ok = builder.is_equal(tag_expect, tag_target);
        (tag_ok, entry)
    }
}
