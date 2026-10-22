# POD2

## Usage
- Run tests: `cargo test --release`
- Rustfmt: `cargo fmt`
- Check [typos](https://github.com/crate-ci/typos): `typos -c .github/workflows/typos.toml`

## GPU proving
pod2 uses the GPU fork of plonky2 ([robknight/plonky2](https://github.com/robknight/plonky2/tree/gpu)), which adds GPU proving through wgpu without changing proofs, circuit data or the verifier (see its [docs/gpu.md](https://github.com/robknight/plonky2/blob/gpu/docs/gpu.md)). With the `gpu` feature, proofs run on a GPU when one is usable (Metal, Vulkan or DirectX 12, chosen at run time) and on the CPU otherwise; configure it with `plonky2::gpu::configure` before the first proof if the defaults do not suit, for example for several concurrent proofs. `gpu-profiling` adds plonky2's GPU diagnostics.

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
