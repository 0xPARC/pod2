//! Optional compiled witness generation, prepared through plonky2's public API.
//!
//! POD2 requests preparation on first use, or during `mainpod::prepare`.
//! plonky2 owns compilation, persistent executor caching, validation and host
//! preparation. `PLONKY2_EXECUTOR_CACHE_DIR` enables its cache independently of
//! POD2's `disk_cache`, which still owns circuit data and padding proofs.
//!
//! Applications control deployment policy through plonky2's environment
//! settings, applied after POD2 defaults. `set_witness_thread_pool` optionally
//! supplies an application-owned resource before preparation/proving. Unsupported generators keep the worklist under
//! the default fallback policy; invalid configuration and unexpected preparation
//! errors are returned to the caller. Strict fallback also rejects unsupported
//! circuits, so it cannot silently change latency on a later proof.
use std::sync::{Arc, Mutex};

use plonky2::{
    iop::{target::Target, witness::PartialWitness},
    plonk::{
        circuit_data::{CircuitData, ProverCircuitData},
        witness_program::{
            WitnessConfig, WitnessFallback, WitnessPreparation, WitnessProgramError,
            WitnessProgramStatus,
        },
    },
};

use crate::middleware::{C, D, F};

#[derive(Default)]
struct Settings {
    config: Option<WitnessConfig>,
    thread_pool: Option<Arc<rayon::ThreadPool>>,
    started: bool,
}
static SETTINGS: Mutex<Settings> = Mutex::new(Settings {
    config: None,
    thread_pool: None,
    started: false,
});

/// Share an application-owned CPU witness pool across POD2's cached circuits.
/// Call before the first preparation/proof. This explicit application resource
/// takes precedence over the environment thread-count hint. Policy and budgets
/// remain controlled through `PLONKY2_EXECUTOR_*`; no plonky2 config is required.
/// The handle is retained with process-wide cached circuits and cannot be
/// replaced after preparation starts. Other proving CPU work uses its usual pool.
pub fn set_thread_pool(pool: Arc<rayon::ThreadPool>) -> anyhow::Result<()> {
    SETTINGS
        .lock()
        .unwrap_or_else(|e| e.into_inner())
        .set_thread_pool(pool)
}
fn configuration() -> Result<WitnessConfig, WitnessProgramError> {
    SETTINGS.lock().unwrap_or_else(|e| e.into_inner()).resolve()
}

impl Settings {
    fn set_thread_pool(&mut self, pool: Arc<rayon::ThreadPool>) -> anyhow::Result<()> {
        anyhow::ensure!(
            !self.started,
            "POD2 witness thread pool must be set before preparation or proving"
        );
        self.thread_pool = Some(pool);
        Ok(())
    }
    fn resolve(&mut self) -> Result<WitnessConfig, WitnessProgramError> {
        if self.config.is_none() {
            let defaults = WitnessConfig::default();
            let mut config = WitnessConfig::from_env_with_defaults(defaults)?;
            // An explicit application-owned handle is above deployment hints.
            if let Some(pool) = &self.thread_pool {
                config.thread_pool = Some(pool.clone());
            }
            self.config = Some(config);
        }
        self.started = true;
        Ok(self
            .config
            .as_ref()
            .expect("initialized witness configuration")
            .clone())
    }
}

pub(crate) trait WitnessProgramHost {
    fn status(&self) -> WitnessProgramStatus;
    fn prepare(
        &self,
        targets: &[Target],
        config: WitnessConfig,
    ) -> Result<WitnessPreparation, WitnessProgramError>;
}
macro_rules! host {
    ($ty:ty) => {
        impl WitnessProgramHost for $ty {
            fn status(&self) -> WitnessProgramStatus {
                self.witness_program_status()
            }
            fn prepare(
                &self,
                targets: &[Target],
                config: WitnessConfig,
            ) -> Result<WitnessPreparation, WitnessProgramError> {
                self.prepare_witness_program_with_config(targets, config)
            }
        }
    };
}
host!(CircuitData<F,C,D>);
host!(ProverCircuitData<F,C,D>);

pub(crate) fn ensure_installed(
    data: &impl WitnessProgramHost,
    pw: &PartialWitness<F>,
) -> anyhow::Result<()> {
    let status = data.status();
    if status == WitnessProgramStatus::Ready {
        return Ok(());
    }
    ensure_with_config(data, pw, status, configuration()?)
}
fn ensure_with_config(
    data: &impl WitnessProgramHost,
    pw: &PartialWitness<F>,
    status: WitnessProgramStatus,
    config: WitnessConfig,
) -> anyhow::Result<()> {
    let required = config.fallback == WitnessFallback::Error;
    // A memoized unsupported circuit returns before inspecting targets. Avoid
    // allocating/copying a large input schema for every subsequent proof.
    let targets = if status == WitnessProgramStatus::Unsupported {
        Vec::new()
    } else {
        pw.target_values.keys().copied().collect()
    };
    match data.prepare(&targets, config) {
        Ok(prepared) => {
            log::debug!("POD2 witness executor {:?}, ready in {:?} (read {:?}, compile {:?}, write {:?}, host {:?})",prepared.source,prepared.elapsed,prepared.cache_read,prepared.compile,prepared.cache_write,prepared.host_prepare);
            Ok(())
        }
        Err(error)
            if !required
                && matches!(
                    error,
                    WitnessProgramError::UnsupportedField
                        | WitnessProgramError::Lookups
                        | WitnessProgramError::UnsupportedGenerator { .. }
                ) =>
        {
            Ok(())
        }
        Err(error) => Err(error.into()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    struct Unsupported;
    impl WitnessProgramHost for Unsupported {
        fn status(&self) -> WitnessProgramStatus {
            WitnessProgramStatus::Unsupported
        }
        fn prepare(
            &self,
            targets: &[Target],
            _: WitnessConfig,
        ) -> Result<WitnessPreparation, WitnessProgramError> {
            assert!(targets.is_empty());
            Err(WitnessProgramError::UnsupportedGenerator {
                index: 0,
                id: "application generator".into(),
            })
        }
    }
    #[test]
    fn unsupported_generators_fall_back_unless_compiled_execution_is_required() {
        let inputs = PartialWitness::new();
        let status = WitnessProgramStatus::Unsupported;
        ensure_with_config(&Unsupported, &inputs, status, WitnessConfig::default()).unwrap();
        let mut config = WitnessConfig::default();
        config.fallback = WitnessFallback::Error;
        assert!(ensure_with_config(&Unsupported, &inputs, status, config)
            .unwrap_err()
            .to_string()
            .contains("application generator"));
    }
    #[test]
    fn application_pool_is_shared_and_fixed_before_preparation() {
        const CHILD: &str = "POD2_WITNESS_POOL_TEST_CHILD";
        if std::env::var_os(CHILD).is_some() {
            let pool = Arc::new(
                rayon::ThreadPoolBuilder::new()
                    .num_threads(2)
                    .build()
                    .unwrap(),
            );
            let mut settings = Settings::default();
            settings.set_thread_pool(pool.clone()).unwrap();
            let config = settings.resolve().unwrap();
            assert_eq!(config.threads, 1);
            assert_eq!(
                config.buffers,
                plonky2::plonk::witness_program::WitnessBuffers::Reuse { max_bytes: 4096 }
            );
            assert!(Arc::ptr_eq(config.thread_pool.as_ref().unwrap(), &pool));
            assert!(Arc::ptr_eq(
                settings.resolve().unwrap().thread_pool.as_ref().unwrap(),
                &pool
            ));
            assert!(settings
                .set_thread_pool(pool)
                .unwrap_err()
                .to_string()
                .contains("before preparation"));
            return;
        }
        let result = std::process::Command::new(std::env::current_exe().unwrap())
            .args(["--exact", "backends::plonky2::witness_program::tests::application_pool_is_shared_and_fixed_before_preparation"])
            .env(CHILD, "1").env("PLONKY2_EXECUTOR_THREADS", "1")
            .env("PLONKY2_EXECUTOR_BUFFER_BYTES", "4096").status().unwrap();
        assert!(result.success());
    }
}
