use std::{
    collections::HashMap,
    sync::{LazyLock, Mutex},
};

use plonky2::plonk::circuit_builder::CircuitBuilder;

use crate::{backends::plonky2::basetypes::D, middleware::F};

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
            use $crate::backends::plonky2::circuits::metrics::METRICS;
            let mut metrics = METRICS.lock().unwrap();
            metrics.begin($builder, $name)
        }};
    }

    #[macro_export]
    macro_rules! measure_gates_end {
        ($builder:expr, $measure:expr) => {{
            use $crate::backends::plonky2::circuits::metrics::METRICS;
            let mut metrics = METRICS.lock().unwrap();
            metrics.end($builder, $measure);
        }};
    }

    #[macro_export]
    macro_rules! measure_gates_print {
        () => {{
            use $crate::backends::plonky2::circuits::metrics::METRICS;
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
