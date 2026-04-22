use std::iter;

use plonky2::{
    field::extension::Extendable,
    hash::hash_types::{HashOut, HashOutTarget, RichField},
    iop::{
        generator::{GeneratedValues, SimpleGenerator},
        target::Target,
        witness::{PartitionWitness, Witness, WitnessWrite},
    },
    plonk::circuit_data::CommonCircuitData,
    util::serialization::{Buffer, IoResult, Read, Write},
};

use crate::{
    backends::plonky2::{
        basetypes::CircuitBuilder,
        circuits::common::{CircuitBuilderPod, IndexTarget},
    },
    measure_gates_begin, measure_gates_end,
    middleware::Params,
};

// A table of aux query hashes addressed by index. Each operation hashes its query inputs into a
// single `HashOutTarget` (with a domain-separation kind folded in, so hashes from different op
// kinds can't be confused) and pushes it here; a verify circuit looks up a row by index and
// compares it against the hash it recomputes from the operation's inputs.
pub struct MuxTableTarget {
    params: Params,
    entries: Vec<HashOutTarget>,
}

impl MuxTableTarget {
    /// Create a table seeded with the sentinel row at index 0. The sentinel hashes to zero, which
    /// no real query hash can equal, so an operation with no aux data points at index 0 and never
    /// matches a verify circuit. Real rows are pushed after it, starting at index 1.
    pub fn new(builder: &mut CircuitBuilder, params: &Params) -> Self {
        Self {
            params: params.clone(),
            entries: vec![builder.constant_hash(HashOut::ZERO)],
        }
    }

    #[allow(clippy::len_without_is_empty)]
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn push(&mut self, query_hash: HashOutTarget) {
        self.entries.push(query_hash);
    }

    pub fn get(&self, builder: &mut CircuitBuilder, index: &IndexTarget) -> HashOutTarget {
        let measure = measure_gates_begin!(builder, "GetAuxTblEntry");
        let entry = builder.vec_ref(&self.params, &self.entries, index);
        measure_gates_end!(builder, measure);
        entry
    }

    pub fn lookup(
        &self,
        builder: &mut CircuitBuilder,
        index: &IndexTarget,
    ) -> Option<HashOutTarget> {
        (self.len() > 1).then(|| self.get(builder, index))
    }
}

#[derive(Debug, Clone, Default)]
pub struct TableGetGenerator {
    index: IndexTarget,
    entries: Vec<Vec<Target>>,
    revealed_entry: Vec<Target>,
}

impl TableGetGenerator {
    pub fn new(index: IndexTarget, entries: Vec<Vec<Target>>, revealed_entry: Vec<Target>) -> Self {
        Self {
            index,
            entries,
            revealed_entry,
        }
    }
}

impl<F: RichField + Extendable<D>, const D: usize> SimpleGenerator<F, D> for TableGetGenerator {
    fn id(&self) -> String {
        "TableGetGenerator".to_string()
    }

    fn dependencies(&self) -> Vec<Target> {
        [self.index.low, self.index.high]
            .into_iter()
            .chain(self.entries.iter().flatten().copied())
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

        let entry = witness.get_targets(&self.entries[index as usize]);

        for (target, value) in self.revealed_entry.iter().zip(
            entry
                .iter()
                .chain(iter::repeat(&F::ZERO).take(self.revealed_entry.len())),
        ) {
            out_buffer.set_target(*target, *value)?;
        }

        Ok(())
    }

    fn serialize(&self, dst: &mut Vec<u8>, _common_data: &CommonCircuitData<F, D>) -> IoResult<()> {
        dst.write_usize(self.index.max_array_len)?;
        dst.write_target(self.index.low)?;
        dst.write_target(self.index.high)?;

        dst.write_usize(self.entries.len())?;
        for entry in &self.entries {
            dst.write_target_vec(entry)?;
        }

        dst.write_target_vec(&self.revealed_entry)
    }

    fn deserialize(src: &mut Buffer, _common_data: &CommonCircuitData<F, D>) -> IoResult<Self> {
        let index = IndexTarget {
            max_array_len: src.read_usize()?,
            low: src.read_target()?,
            high: src.read_target()?,
        };
        let len = src.read_usize()?;
        let mut entries = Vec::with_capacity(len);
        for _ in 0..len {
            entries.push(src.read_target_vec()?);
        }
        let revealed_entry = src.read_target_vec()?;

        Ok(Self {
            index,
            entries,
            revealed_entry,
        })
    }
}
