# scip-sys
[![tests](https://github.com/scipopt/scip-sys/actions/workflows/build_and_test.yml/badge.svg)](https://github.com/scipopt/scip-sys/actions/workflows/build_and_test.yml)
[![][img_crates]][crates] [![][img_doc]][doc] 

[img_crates]: https://img.shields.io/crates/v/scip-sys.svg
[crates]: https://crates.io/crates/scip-sys
[img_doc]: https://img.shields.io/badge/rust-documentation-blue.svg
[doc]: https://docs.rs/scip-sys/

Raw rust bindings to [SCIP](https://scipopt.org/)'s C-API. The bindings are automatically generated using [bindgen](https://github.com/rust-lang/rust-bindgen). 
Meant to provide full control over SCIP's API, for a more restricted memory-safe API see [russcip](https://github.com/scipopt/russcip).

## Dependencies 
This crate depends on SCIP at runtime, the crate provides optional features ([bundled](#bundled-feature), [from-source](#from-source-feature)) to install SCIP.
If no feature is enabled, it will look for a scip installation in the current conda environment, if it is not found it will look for the `SCIPOPTDIR` environment variable.
to install SCIP using conda run the following command 
```bash
conda install --channel conda-forge scip
```

### `bundled` feature
The crate provides the `bundled` feature that tries to download a precompiled binary for your OS and architecture
run the following command to add the crate with the `bundled` feature
```bash
cargo add scip-sys --features bundled
```

Because the bundled SCIP release is pinned, the bindings are deterministic per
platform and are shipped prebuilt in `src/bindings/`. The default build still
keeps `bindgen` enabled (the system/`SCIPOPTDIR`/`from-source` paths need it),
but the bundled path uses the prebuilt bindings and never runs `bindgen`. For
the leanest build, disable default features to drop `bindgen` (and its
`libclang` requirement) entirely:
```bash
cargo add scip-sys --no-default-features --features bundled
```
The prebuilt bindings are regenerated per platform by the `generate-bindings`
GitHub Actions workflow; a CI check fails if they drift from the pinned release.

### `from-source` feature
The crate provides the `from-source` feature that tries to download the source code and compile it. This provides the most flexibility but the compilation process can be slow. 
run the following command to add the crate with the `from-source` feature
```bash
cargo add scip-sys --features from-source
```

### Finding libscip at runtime 
`scip-sys` will emit the path where it found libscip in the environment variable `DEP_SCIP_LIBDIR` at build time.
You can use this variable to find the path to the shared library at runtime. You can do so by adding the following to your `build.rs`
```rust
fn main() {
    let libscip_dir = std::env::var("DEP_SCIP_LIBDIR").unwrap();
    println!("cargo:rustc-link-arg=-Wl,-rpath,{}", libscip_dir);
}
```


## License
This repo is distributed under the open-source Apache 2.0 [license](https://www.apache.org/licenses/LICENSE-2.0). 