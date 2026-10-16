#[cfg(feature = "bundled")]
use crate::download::download_and_extract_zip;
#[cfg(feature = "bundled")]
use std::env;
#[cfg(feature = "bundled")]
use std::path::PathBuf;

/// Map the current target OS/arch to the platform tag used both for the
/// prebuilt SCIP download and for selecting the matching prebuilt bindings in
/// `src/bindings/<tag>.rs`. Keeping a single source of truth ensures the
/// downloaded library and the committed bindings always refer to the same
/// platform.
#[cfg(feature = "bundled")]
pub fn target_string() -> String {
    let os = std::env::var("CARGO_CFG_TARGET_OS").unwrap();
    let arch = std::env::var("CARGO_CFG_TARGET_ARCH").unwrap();

    let os_string = if os == "linux" && arch == "x86_64" {
        "linux"
    } else if os == "linux" && arch == "aarch64" {
        "linux-arm"
    } else if os == "macos" && arch == "x86_64" {
        "macos-intel"
    } else if os == "macos" && arch == "aarch64" {
        "macos-arm"
    } else if os == "windows" && arch == "x86_64" {
        "windows"
    } else {
        panic!("Unsupported OS-arch combination: {}-{}", os, arch);
    };

    os_string.to_string()
}

#[cfg(feature = "bundled")]
pub fn download_scip() {
    let extract_path = PathBuf::from(env::var("OUT_DIR").unwrap());

    if extract_path.join("scip_install").exists() {
        println!("cargo:warning=SCIP was previously downloaded, skipping download");
        return;
    }

    let os = std::env::var("CARGO_CFG_TARGET_OS").unwrap();
    let arch = std::env::var("CARGO_CFG_TARGET_ARCH").unwrap();
    println!("cargo:warning=Detected OS: {}", os);
    println!("cargo:warning=Detected arch: {}", arch);

    let os_string = target_string();

    // if debug mode is enabled, download the debug version of SCIP
    #[cfg(debug_assertions)]
    let debug_str = "-debug";
    #[cfg(not(debug_assertions))]
    let debug_str = "";
    // Only consumed by the (currently disabled) debug-build URL below.
    let _ = debug_str;

    // TODO: enable this when debug builds are available
    // let url = format!(
    //     "https://github.com/scipopt/scipoptsuite-deploy/releases/download/v0.12.0/libscip-{os_string}{debug_str}.zip",
    // );
    // v0.12.0 ships SCIP 10.0.2 / SoPlex 8.0.2 / GCG 4.0.2 / IPOPT 3.14.19.
    let url = format!(
        "https://github.com/scipopt/scipoptsuite-deploy/releases/download/v0.12.0/libscip-{os_string}.zip",
    );

    download_and_extract_zip(&url, &extract_path)
        .unwrap_or_else(|e| panic!("Failed to download and extract SCIP: {}", e));
}
