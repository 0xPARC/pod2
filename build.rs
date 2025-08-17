#[cfg(feature = "mem_cache")]
fn main() {}

#[cfg(feature = "disk_cache")]
fn main() -> Result<(), Box<dyn std::error::Error>> {
    use vergen_gitcl::{Emitter, GitclBuilder};
    // Example of injected vars:
    // cargo:rustc-env=VERGEN_GIT_BRANCH=master
    // cargo:rustc-env=VERGEN_GIT_COMMIT_AUTHOR_EMAIL=emitter@vergen.com
    // cargo:rustc-env=VERGEN_GIT_COMMIT_AUTHOR_NAME=Jason Ozias
    // cargo:rustc-env=VERGEN_GIT_COMMIT_COUNT=44
    // cargo:rustc-env=VERGEN_GIT_COMMIT_DATE=2024-01-30
    // cargo:rustc-env=VERGEN_GIT_COMMIT_MESSAGE=depsup
    // cargo:rustc-env=VERGEN_GIT_COMMIT_TIMESTAMP=2024-01-30T21:43:43.000000000Z
    // cargo:rustc-env=VERGEN_GIT_DESCRIBE=0.1.0-beta.1-15-g728e25c
    // cargo:rustc-env=VERGEN_GIT_SHA=728e25ca5bb7edbbc505f12b28c66b2b27883cf1
    let gitcl = GitclBuilder::all_git()?;
    Emitter::default().add_instructions(&gitcl)?.emit()?;

    Ok(())
}
