# POD2

## Usage
- Run tests: `cargo test --release`
- Rustfmt: `cargo fmt`
- Check [typos](https://github.com/crate-ci/typos): `typos -c .github/workflows/typos.toml`

## GPU proving
pod2 uses the GPU fork of plonky2 ([robknight/plonky2](https://github.com/robknight/plonky2/tree/gpu)), which adds GPU proving through wgpu without changing proofs, circuit data or the verifier (see its [docs/gpu.md](https://github.com/robknight/plonky2/blob/gpu/docs/gpu.md)). With the `gpu` feature, proofs run on a GPU when one is usable (Metal, Vulkan or DirectX 12, chosen at run time) and on the CPU otherwise; set typed `PLONKY2_GPU_*` environment defaults without passing plonky2 configuration through POD2. For example, `PLONKY2_GPU_PROVING_WORKERS=4` sizes resources for four concurrent proofs, `PLONKY2_GPU_RETAINED_BYTES=0` disables retained GPU caches, and `PLONKY2_GPU_ENABLED=false` keeps proving on the CPU. Programmatic overrides remain available through `plonky2::gpu::configure` before the first proof. `gpu-profiling` adds plonky2's GPU diagnostics.

See plonky2's `docs/runtime-configuration.md` for the complete GPU/executor environment contract, precedence and startup validation. `examples/mainpod_prove.rs` preserves those environment defaults while overriding its known actual worker count from the CLI. It always calls `mainpod::prepare` before proving and reports preparation time separately. With persistent caches configured, expensive generation is normally a one-time cost per compatible build/configuration; cache loading and runtime setup still occur each process. The old `--prepare` flag remains accepted.

## Faster witness generation
With `witness_executor`, POD2 prepares plonky2's compiled witness executor for each circuit before its first proof. The measured fast defaults apply automatically. The plonky2-u32 fork must describe its comparison generator's witness operation; unsupported circuits use the ordinary worklist by default.

Ready-chunk dependency scheduling and hardware-eligible Poseidon batching are automatic. Portable x86 builds detect AVX-512 support at runtime; other machines retain the scalar path. No circuit-specific generated Rust or external compiler is required.

Set `PLONKY2_EXECUTOR_CACHE_DIR` to enable compiled-executor caching across processes. plonky2 owns identity, validation, loading, compilation, atomic replacement and concurrent preparation. This does not require POD2's `disk_cache` feature. That separate feature still caches POD2 circuit data and padding proofs.

`backends::plonky2::mainpod::prepare(&params, &vd_set)` prepares the circuit, padding proof and witness executor before accepting proof requests. Host executor tables are initialized before it returns. Measure total preparation and first-proof time as well as warm proof time.

Applications control only cache location (`CACHE_DIR`), CPU allocation (`THREADS`), retained-buffer budget (`BUFFER_BYTES`) and fallback (`FALLBACK`) through `PLONKY2_EXECUTOR_*`; plonky2 applies it after POD2's defaults. POD2 does not re-export plonky2 configuration structs or policy enums. For an application-owned Rayon witness pool, call `backends::plonky2::set_witness_thread_pool(Arc<rayon::ThreadPool>)` before the first preparation or proof. That explicit resource takes precedence over the environment thread-count hint while other environment settings remain effective. The pool is retained with POD2's process-wide circuit caches and cannot be replaced after preparation begins; other CPU proving work uses its usual pool. Without a supplied pool, default witness work inherits the current Rayon pool (or uses the environment's program-owned pool setting).

For example, an application can inject a shared CPU witness resource using POD2 and Rayon APIs:

```rust,ignore
let pool = std::sync::Arc::new(
    rayon::ThreadPoolBuilder::new().num_threads(2).build()?
);
pod2::backends::plonky2::set_witness_thread_pool(pool)?;
// Prepare or prove using POD2 normally; policy still comes from the environment.
```

Invalid settings and unexpected preparation errors are returned; cache I/O failures allow memory-only preparation. `PLONKY2_EXECUTOR_FALLBACK=error` requires compiled execution, including rejecting unsupported circuits. POD2 leaves global GPU settings to plonky2 and the application's environment. A private plonky2 GPU context does not select the device for POD2 proofs.

To persist both circuit/padding artifacts and executor plans, select `disk_cache` instead of the default `mem_cache`:

```sh
PLONKY2_EXECUTOR_CACHE_DIR=.cache/executors \
cargo run --release --no-default-features \
  --features backend_plonky2,zk,gpu,witness_executor,disk_cache \
  --example mainpod_prove -- --proofs 4
```

See plonky2's `docs/witness-executor.md` for configuration, resource ownership, compatibility, custom-generator checks and the explicit preparation API.

## Book
The `book` contains the specification of POD2. A rendered version of the site can be found at: https://0xparc.github.io/pod2/

To run it locally:
- Requirements
	- [mdbook](https://github.com/rust-lang/mdBook): `cargo install mdbook`
	- [mdbook-katex](https://github.com/lzanini/mdbook-katex): `cargo install mdbook-katex`
- Go to the book directory: `cd book`
- Run the mdbook: `mdbook serve`

## License

MIT
