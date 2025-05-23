use plonky2::{
    field::extension::Extendable,
    hash::hash_types::RichField,
    iop::{
        generator::{GeneratedValues, SimpleGenerator},
        target::Target,
        witness::{PartitionWitness, Witness},
    },
    plonk::circuit_data::CommonCircuitData,
    util::serialization::{Buffer, IoResult, Read, Write},
};

/// Plonky2 generator that allows debugging values assigned to targets.  This generator doesn't
/// actually generate any value and doesn't assign any witness.  Instead it can be registered to
/// monitor targets and print their values once they are available.
///
/// Example usage:
/// ```rust,ignore
/// builder.add_simple_generator(DebugGenerator::new(
///     format!("values_{}", i),
///     vec![v1, v2, v3],
/// ));
/// ```
#[derive(Debug, Default)]
pub struct DebugGenerator {
    pub(crate) name: String,
    pub(crate) xs: Vec<Target>,
}

impl DebugGenerator {
    pub fn new(name: String, xs: Vec<Target>) -> Self {
        Self { name, xs }
    }
}

impl<F: RichField + Extendable<D>, const D: usize> SimpleGenerator<F, D> for DebugGenerator {
    fn id(&self) -> String {
        "DebugGenerator".to_string()
    }

    fn dependencies(&self) -> Vec<Target> {
        self.xs.clone()
    }

    fn run_once(
        &self,
        witness: &PartitionWitness<F>,
        _out_buffer: &mut GeneratedValues<F>,
    ) -> anyhow::Result<()> {
        let xs = witness.get_targets(&self.xs);

        println!("debug: values of {}", self.name);
        for (i, x) in xs.iter().enumerate() {
            println!("- {:03}: {}", i, x);
        }
        Ok(())
    }

    fn serialize(&self, dst: &mut Vec<u8>, _common_data: &CommonCircuitData<F, D>) -> IoResult<()> {
        dst.write_usize(self.name.len())?;
        dst.write_all(self.name.as_bytes())?;
        dst.write_target_vec(&self.xs)
    }

    fn deserialize(src: &mut Buffer, _common_data: &CommonCircuitData<F, D>) -> IoResult<Self> {
        let name_len = src.read_usize()?;
        let mut name_buf = vec![0; name_len];
        src.read_exact(&mut name_buf)?;
        let name = unsafe { String::from_utf8_unchecked(name_buf) };
        let xs = src.read_target_vec()?;
        Ok(Self { name, xs })
    }
}
