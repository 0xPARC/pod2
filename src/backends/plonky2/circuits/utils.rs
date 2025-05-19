use std::collections::HashMap;

use plonky2::{
    field::extension::Extendable,
    hash::hash_types::RichField,
    iop::{
        generator::{GeneratedValues, SimpleGenerator},
        target::Target,
        witness::{PartitionWitness, Witness},
    },
    plonk::{circuit_builder::CircuitBuilder, circuit_data::CommonCircuitData},
    util::serialization::{Buffer, IoResult, Read, Write},
};

use crate::{backends::plonky2::basetypes::D, middleware::F};

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

use std::sync::{LazyLock, Mutex};

pub static METRICS: LazyLock<Mutex<Metrics>> = LazyLock::new(|| Mutex::new(Metrics::default()));

#[derive(Default)]
pub struct Metrics {
    gates: Vec<(String, usize)>,
    stack: Vec<String>,
}

pub struct MetricsMeasure {
    name: String,
    start_num_gates: usize,
    ended: bool,
}

impl Drop for MetricsMeasure {
    fn drop(&mut self) {
        if !self.ended {
            panic!("Measure \"{}\" not ended", self.name);
        }
    }
}

impl Metrics {
    #[must_use]
    pub fn begin(
        &mut self,
        builder: &CircuitBuilder<F, D>,
        name: impl Into<String>,
    ) -> MetricsMeasure {
        let name = name.into();
        self.stack.push(name);
        MetricsMeasure {
            name: self.stack.join("/"),
            start_num_gates: builder.num_gates(),
            ended: false,
        }
    }
    pub fn end(&mut self, builder: &CircuitBuilder<F, D>, mut measure: MetricsMeasure) {
        self.stack.pop();
        measure.ended = true;
        let num_gates = builder.num_gates();
        let delta_gates = num_gates - measure.start_num_gates;
        self.gates.push((measure.name.clone(), delta_gates));
    }
    pub fn print(&self) {
        println!("Gate count:");
        let mut count = HashMap::new();
        for (name, num_gates) in &self.gates {
            let n = count.entry(name).or_insert(0);
            *n += 1;
            println!("- {} [{}]: {}", name, *n, num_gates);
        }
    }
}

#[cfg(feature = "metrics")]
pub mod measure_macros {
    #[macro_export]
    macro_rules! measure_gates_begin {
        ($builder:expr, $name:expr) => {{
            use $crate::backends::plonky2::circuits::utils::METRICS;
            let mut metrics = METRICS.lock().unwrap();
            metrics.begin($builder, $name)
        }};
    }

    #[macro_export]
    macro_rules! measure_gates_end {
        ($builder:expr, $measure:expr) => {{
            use $crate::backends::plonky2::circuits::utils::METRICS;
            let mut metrics = METRICS.lock().unwrap();
            metrics.end($builder, $measure);
        }};
    }

    #[macro_export]
    macro_rules! measure_gates_print {
        () => {{
            use $crate::backends::plonky2::circuits::utils::METRICS;
            let metrics = METRICS.lock().unwrap();
            metrics.print();
        }};
    }
}

#[cfg(not(feature = "metrics"))]
pub mod measure_macros {
    #[macro_export]
    macro_rules! measure_gates_begin {
        ($builder:expr, $name:expr) => {
            ()
        };
    }

    #[macro_export]
    macro_rules! measure_gates_end {
        ($builder:expr, $measure:expr) => {
            let _ = $measure;
        };
    }

    #[macro_export]
    macro_rules! measure_gates_print {
        () => {{
            println!("Gate count disabled: \"metrics\" feature not enabled.");
        }};
    }
}
