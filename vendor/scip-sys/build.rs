mod bundled;
#[cfg(feature = "bindgen")]
mod callback;
// `from_source` is only needed by the from-source build and by the generated
// (bindgen, non-bundled) path that checks the from-source flag.
#[cfg(any(
    feature = "from-source",
    all(feature = "bindgen", not(feature = "bundled"))
))]
mod from_source;

#[cfg(any(feature = "bundled", feature = "from-source"))]
mod download;

use std::env;
use std::error::Error;
use std::path::{Path, PathBuf};

/// Emit the `cargo:` link-search / rpath directives for a SCIP install directory
/// (one containing `lib/` and `include/`). This is independent of bindgen and is
/// shared by every path that links against SCIP.
#[cfg(any(feature = "bundled", feature = "bindgen"))]
fn emit_link_search(path: &str) {
    let lib_dir = PathBuf::from(&path).join("lib");
    let lib_dir_path = lib_dir.to_str().unwrap();

    if lib_dir.exists() {
        println!("cargo:warning=Using SCIP from {}", lib_dir_path);
        println!("cargo:rustc-link-search={}", lib_dir_path);
        println!("cargo:libdir={}", lib_dir_path);

        #[cfg(windows)]
        let lib_dir_path = PathBuf::from(&path).join("bin");
        #[cfg(windows)]
        println!("cargo:rustc-link-search={}", lib_dir_path.to_str().unwrap());
    } else {
        panic!(
            "{}/lib does not exist, please check your SCIP installation",
            path
        );
    }

    println!("cargo:rustc-link-arg=-Wl,-rpath,{}", lib_dir_path);
}

/// Emit the `cargo:` link-lib directives: the SCIP library itself, plus the C++
/// runtime and SoPlex when building from source.
#[cfg(any(feature = "bundled", feature = "bindgen"))]
fn emit_link_libs() {
    #[cfg(windows)]
    {
        println!("cargo:rustc-link-lib=libscip");
    }
    #[cfg(not(windows))]
    {
        println!("cargo:rustc-link-lib=scip");
    }

    #[cfg(feature = "from-source")]
    {
        let target = env::var("TARGET").unwrap();
        let apple = target.contains("apple");
        let linux = target.contains("linux");
        let mingw = target.contains("pc-windows-gnu");
        if apple {
            println!("cargo:rustc-link-lib=dylib=c++");
        } else if linux || mingw {
            println!("cargo:rustc-link-lib=dylib=stdc++");
        }

        #[cfg(windows)]
        {
            println!("cargo:rustc-link-lib=libsoplex");
        }
        #[cfg(not(windows))]
        {
            println!("cargo:rustc-link-lib=soplex");
        }
    }
}

/// Build a bindgen `Builder` pointed at the SCIP headers inside an install
/// directory (`<path>/include/scip/{scip,scipdefplugins,def}.h`).
#[cfg(feature = "bindgen")]
fn scip_dir_bindgen_builder(path: &str) -> bindgen::Builder {
    let include_dir = PathBuf::from(&path).join("include");
    let include_dir_path = include_dir.to_str().unwrap();
    let scip_header_file = PathBuf::from(&path)
        .join("include")
        .join("scip")
        .join("scip.h")
        .to_str()
        .unwrap()
        .to_owned();
    let scipdefplugins_header_file = PathBuf::from(&path)
        .join("include")
        .join("scip")
        .join("scipdefplugins.h")
        .to_str()
        .unwrap()
        .to_owned();
    let scipdef_file = PathBuf::from(&path)
        .join("include")
        .join("scip")
        .join("def.h")
        .to_str()
        .unwrap()
        .to_owned();

    bindgen::Builder::default()
        .header(scip_header_file)
        .header(scipdefplugins_header_file)
        .header(scipdef_file)
        .parse_callbacks(Box::new(bindgen::CargoCallbacks::new()))
        .clang_arg(format!("-I{}", include_dir_path))
}

/// Apply the SCIP-specific bindgen tweaks, generate the bindings and write them
/// to `<out_path>/bindings.rs`.
#[cfg(feature = "bindgen")]
fn finalize_and_generate(builder: bindgen::Builder, out_path: &Path) -> Result<(), Box<dyn Error>> {
    use callback::DeriveCastedConstant;

    // Setup the DeriveCastedConstant callback to target SCIP_INVALID
    let derive_casted_constant = DeriveCastedConstant::new().target("SCIP_INVALID");

    let builder = builder
        // SCIP 10 annotates the deprecated `SCIP_VARTYPE_IMPLINT` enumerator with
        // `SCIP_DEPRECATED`. On Windows that expands to `__declspec(deprecated)`,
        // which clang cannot parse inside an enum; neutralize the macro for bindgen.
        .clang_arg("-DSCIP_DEPRECATED=")
        .blocklist_item("FP_NAN")
        .blocklist_item("FP_INFINITE")
        .blocklist_item("FP_ZERO")
        .blocklist_item("FP_SUBNORMAL")
        .blocklist_item("FP_NORMAL")
        .parse_callbacks(Box::new(bindgen::CargoCallbacks::new()))
        .parse_callbacks(Box::new(derive_casted_constant));

    let bindings = builder.generate()?;
    bindings.write_to_file(out_path.join("bindings.rs"))?;
    Ok(())
}

#[cfg(all(feature = "bindgen", not(feature = "bundled")))]
fn lib_scip_in_dir(path: &str) -> bool {
    use glob::glob;
    glob(&format!("{}/lib/libscip*", path)).unwrap().count() > 0
}

#[cfg(all(feature = "bindgen", not(feature = "bundled")))]
fn look_in_scipoptdir_and_conda_env() -> Option<bindgen::Builder> {
    let env_vars = vec!["SCIPOPTDIR", "CONDA_PREFIX"];

    for env_var_name in env_vars {
        println!("cargo:rerun-if-env-changed={}", env_var_name);
        let env_var = env::var(env_var_name);
        if let Ok(scip_dir) = env_var {
            println!("cargo:warning=Looking for SCIP in {}", scip_dir);
            if lib_scip_in_dir(&scip_dir) {
                emit_link_search(&scip_dir);
                return Some(scip_dir_bindgen_builder(&scip_dir));
            } else {
                println!("cargo:warning=SCIP was not found in {}", scip_dir);
            }
        } else {
            println!("cargo:warning={} is not set", env_var_name);
        }
    }

    None
}

#[cfg(all(feature = "bindgen", not(feature = "bundled")))]
fn try_system_include_paths() -> Option<bindgen::Builder> {
    println!("cargo:warning=Searching for SCIP in standard system directories");

    // Common system include paths
    let search_paths = vec![
        "/usr/include",
        "/usr/local/include",
        "/opt/local/include",          // MacPorts
        "/opt/homebrew/include",       // Homebrew ARM Mac
        "/usr/local/opt/scip/include", // Homebrew Intel Mac
    ];

    for base_path in search_paths {
        let base = PathBuf::from(base_path);
        let scip_h = base.join("scip").join("scip.h");
        let scipdefplugins_h = base.join("scip").join("scipdefplugins.h");
        let def_h = base.join("scip").join("def.h");

        if scip_h.exists() && scipdefplugins_h.exists() && def_h.exists() {
            println!("cargo:warning=Found SCIP headers in {}", base_path);

            return Some(
                bindgen::Builder::default()
                    .header(scip_h.to_str().unwrap())
                    .header(scipdefplugins_h.to_str().unwrap())
                    .header(def_h.to_str().unwrap())
                    .parse_callbacks(Box::new(bindgen::CargoCallbacks::new()))
                    .clang_arg(format!("-I{}", base_path)),
            );
        }
    }

    println!("cargo:warning=Could not find SCIP headers in standard system directories");
    None
}

/// Produce `<out_path>/bindings.rs` for the bundled path.
///
/// The bundled SCIP release is pinned, so the generated bindings are
/// deterministic for a given target and are committed under
/// `src/bindings/<target>.rs`. Copying the prebuilt file lets the bundled build
/// skip bindgen (and libclang) entirely. If no prebuilt file is committed for
/// this target yet, we fall back to bindgen when that feature is available so
/// the build still succeeds.
#[cfg(feature = "bundled")]
fn write_bundled_bindings(scip_install: &Path, out_path: &Path) -> Result<(), Box<dyn Error>> {
    let target = bundled::target_string();
    let manifest_dir = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap());
    let prebuilt = manifest_dir
        .join("src")
        .join("bindings")
        .join(format!("{target}.rs"));

    // Opt-in escape hatch (used by the `generate-bindings` CI job): force bindgen
    // to regenerate and write the result back into the committed source tree.
    println!("cargo:rerun-if-env-changed=SCIP_SYS_REGENERATE_BINDINGS");
    let regenerate = env::var_os("SCIP_SYS_REGENERATE_BINDINGS").is_some();

    if prebuilt.exists() && !regenerate {
        println!("cargo:warning=Using prebuilt bundled bindings src/bindings/{target}.rs");
        println!("cargo:rerun-if-changed={}", prebuilt.to_str().unwrap());
        std::fs::copy(&prebuilt, out_path.join("bindings.rs"))?;
        return Ok(());
    }

    #[cfg(feature = "bindgen")]
    {
        if regenerate {
            println!("cargo:warning=Regenerating bundled bindings for target '{target}'");
        } else {
            println!(
                "cargo:warning=No prebuilt bindings for target '{target}'; generating with bindgen. \
                 Run the generate-bindings workflow and commit src/bindings/{target}.rs to skip this."
            );
        }

        let builder = scip_dir_bindgen_builder(scip_install.to_str().unwrap());
        finalize_and_generate(builder, out_path)?;

        if regenerate {
            std::fs::create_dir_all(prebuilt.parent().unwrap())?;
            std::fs::copy(out_path.join("bindings.rs"), &prebuilt)?;
            println!("cargo:warning=Wrote src/bindings/{target}.rs");
        }
        return Ok(());
    }

    #[cfg(not(feature = "bindgen"))]
    {
        let _ = scip_install;
        panic!(
            "scip-sys: prebuilt bundled bindings for target '{target}' are missing (or \
             regeneration was requested), and the `bindgen` feature is disabled so they \
             cannot be generated.\n\
             Either build with default features enabled, or commit src/bindings/{target}.rs."
        );
    }
}

fn main() -> Result<(), Box<dyn Error>> {
    let out_path = PathBuf::from(env::var("OUT_DIR").unwrap());

    // Detect docs.rs build environment (no network access)
    if env::var("DOCS_RS").is_ok() {
        println!("cargo:warning=Building on docs.rs, using pre-generated bindings");
        std::fs::copy("src/bindings_pregenerated.rs", out_path.join("bindings.rs"))?;
        return Ok(());
    }

    // Bundled path: the SCIP version is pinned, so bindings are deterministic per
    // target. Use the committed prebuilt bindings and skip bindgen/libclang.
    #[cfg(feature = "bundled")]
    {
        bundled::download_scip();
        let path = out_path.join("scip_install");
        emit_link_search(path.to_str().unwrap());
        emit_link_libs();
        write_bundled_bindings(&path, &out_path)?;
        return Ok(());
    }

    // Every other path (from-source, SCIPOPTDIR/conda, system) targets a SCIP
    // whose ABI is not known ahead of time, so the bindings must be generated.
    #[cfg(all(feature = "bindgen", not(feature = "bundled")))]
    {
        use crate::from_source::is_from_source_feature_enabled;

        let builder = if is_from_source_feature_enabled() {
            let source_path = crate::from_source::download_scip_source();
            let build_path = crate::from_source::compile_scip(source_path);
            emit_link_search(build_path.to_str().unwrap());
            scip_dir_bindgen_builder(build_path.to_str().unwrap())
        } else {
            look_in_scipoptdir_and_conda_env().unwrap_or_else(|| {
                println!("cargo:warning=SCIP was not found in SCIPOPTDIR or in Conda environment");
                println!("cargo:warning=Looking for SCIP in system libraries");

                try_system_include_paths().unwrap_or_else(|| {
                    panic!(
                        "Could not find SCIP installation.\n\
                        Please either:\n\
                        - Set SCIPOPTDIR environment variable to point to your SCIP installation\n\
                        - Install SCIP system-wide (headers in /usr/include or /usr/local/include)\n\
                        - Use --features bundled to download and use a bundled version\n\
                        - Use --features from-source to build SCIP from source"
                    )
                })
            })
        };

        emit_link_libs();
        finalize_and_generate(builder, &out_path)?;
        return Ok(());
    }

    // Neither `bundled` nor `bindgen` is enabled: there is no way to obtain
    // bindings. (Reachable only with `--no-default-features` and no path feature.)
    #[cfg(all(not(feature = "bundled"), not(feature = "bindgen")))]
    {
        panic!(
            "scip-sys: built without `bundled` and without the `bindgen` feature, so no SCIP \
             bindings can be produced.\n\
             Enable default features, or use `--features bundled` / `--features from-source`."
        );
    }
}
