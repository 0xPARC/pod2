//! Prove and verify MainPods, for measurement: one proof by default, a
//! sequence with `--proofs`, or a throughput run with `--workers`.
//! Preparation always runs and is timed separately before the first proof.
//! `RUST_LOG` selects plonky2's diagnostics.
use pod2::{
    backends::plonky2::{
        basetypes::DEFAULT_VD_SET,
        mainpod::{self, Prover},
    },
    frontend::MainPodBuilder,
    middleware::Params,
};

const USAGE: &str = "usage: mainpod_prove [--proofs N] [--workers N] [--pause-ms MS] [--prepare]
  --proofs N     verified MainPod proofs to make (1 to 40, default 1)
  --workers N    proofs made concurrently after the first (1 to 8, default 1)
  --pause-ms MS  sleep after each proof, so a sampler can read resting memory
  --prepare      accepted for compatibility; preparation always runs";

struct Args {
    proofs: usize,
    workers: usize,
    pause: Option<std::time::Duration>,
}

fn parse_args() -> anyhow::Result<Args> {
    let mut parsed = Args {
        proofs: 1,
        workers: 1,
        pause: None,
    };
    let mut args = std::env::args().skip(1);
    while let Some(arg) = args.next() {
        let mut value = |name: &str| -> anyhow::Result<u64> {
            let value = args
                .next()
                .ok_or_else(|| anyhow::anyhow!("{name} needs a value\n{USAGE}"))?;
            value
                .parse()
                .map_err(|_| anyhow::anyhow!("{name}: not a number: {value}\n{USAGE}"))
        };
        match arg.as_str() {
            "--proofs" => parsed.proofs = value("--proofs")? as usize,
            "--workers" => parsed.workers = value("--workers")? as usize,
            "--pause-ms" => {
                parsed.pause = Some(std::time::Duration::from_millis(value("--pause-ms")?))
            }
            // Preparation is now automatic; preserve existing invocations.
            "--prepare" => {}
            "-h" | "--help" => {
                println!("{USAGE}");
                std::process::exit(0);
            }
            other => anyhow::bail!("unknown argument {other}\n{USAGE}"),
        }
    }
    anyhow::ensure!(
        (1..=40).contains(&parsed.proofs),
        "--proofs must be 1 to 40"
    );
    anyhow::ensure!(
        (1..=8).contains(&parsed.workers),
        "--workers must be 1 to 8"
    );
    anyhow::ensure!(
        parsed.workers == 1 || parsed.proofs >= 2,
        "--workers needs at least two proofs: the first warms the circuit alone"
    );
    Ok(parsed)
}

fn main() -> anyhow::Result<()> {
    let _ = env_logger::try_init();
    let result = run(parse_args()?);
    #[cfg(feature = "gpu")]
    {
        plonky2::gpu::shutdown()?;
        println!("orderly GPU shutdown completed");
    }
    result
}

fn run(args: Args) -> anyhow::Result<()> {
    // Concurrent proofs share the GPU context's retained budget and quotient
    // share adaptation, sized by the worker count. Set before anything builds
    // a circuit, which creates the context.
    #[cfg(feature = "gpu")]
    {
        let mut config = plonky2::gpu::GpuConfig::from_env()?;
        config.proving_workers = args.workers;
        plonky2::gpu::configure(config)?;
    }
    let params = Params::default();
    println!("Preparing MainPod proving artifacts...");
    let started = std::time::Instant::now();
    mainpod::prepare(&params, &DEFAULT_VD_SET)?;
    println!("MainPod preparation completed in {:?}.", started.elapsed());
    #[cfg(feature = "disk_cache")]
    println!("Circuit construction and padding proofs are cached on disk, so generating them is normally a one-time cost per compatible build/configuration.");
    #[cfg(not(feature = "disk_cache"))]
    println!("Circuit construction and padding proofs are reused within this process. Select disk_cache instead of mem_cache to cache them across runs and make generation normally a one-time cost per compatible build/configuration.");
    #[cfg(feature = "witness_executor")]
    println!("Executor compilation is cacheable across runs with PLONKY2_EXECUTOR_CACHE_DIR. Cache loading, validation and runtime setup still run each process.");
    let builder = MainPodBuilder::new(&params, &DEFAULT_VD_SET);
    let prove_one = |i: usize| -> anyhow::Result<()> {
        let started = std::time::Instant::now();
        let pod = builder.prove(&Prover {})?;
        pod.pod.verify()?;
        println!(
            "verified MainPod proof run {} in {:?}",
            i + 1,
            started.elapsed()
        );
        if let Some(pause) = args.pause {
            std::thread::sleep(pause);
        }
        Ok(())
    };
    if args.workers == 1 {
        for i in 0..args.proofs {
            prove_one(i)?;
        }
        return Ok(());
    }
    // Throughput: the first proof warms the circuit alone, then the
    // remaining proofs are shared among the workers and every proof is
    // verified before the clock stops.
    prove_one(0)?;
    let next = std::sync::atomic::AtomicUsize::new(1);
    let started = std::time::Instant::now();
    std::thread::scope(|scope| -> anyhow::Result<()> {
        let handles = (0..args.workers)
            .map(|_| {
                let next = &next;
                let prove_one = &prove_one;
                scope.spawn(move || -> anyhow::Result<()> {
                    loop {
                        let i = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                        if i >= args.proofs {
                            return Ok(());
                        }
                        prove_one(i)?;
                    }
                })
            })
            .collect::<Vec<_>>();
        let mut failure = None;
        for handle in handles {
            if let Err(error) = handle.join().expect("proving worker panicked") {
                failure = Some(error);
            }
        }
        failure.map_or(Ok(()), Err)
    })?;
    let seconds = started.elapsed().as_secs_f64();
    println!(
        "throughput: workers={} proofs={} seconds={seconds:.6} proofs_per_second={:.6} verify=true",
        args.workers,
        args.proofs - 1,
        (args.proofs - 1) as f64 / seconds
    );
    Ok(())
}
