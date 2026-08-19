#![allow(clippy::get_first)]
#![allow(clippy::uninlined_format_args)] // TODO: Remove this in another PR
#![allow(clippy::manual_repeat_n)] // TODO: Remove this in another PR
#![allow(clippy::large_enum_variant)] // TODO: Remove this in another PR
#![feature(mapped_lock_guards)]

// Alternative global allocators (#398). Gated on `cfg(test)` so this applies
// only to pod2's own test harness: a library has no business choosing the
// allocator for the programs that depend on it.
#[cfg(all(feature = "mimalloc", feature = "jemalloc"))]
compile_error!("features `mimalloc` and `jemalloc` are mutually exclusive");

#[cfg(all(test, feature = "mimalloc"))]
#[global_allocator]
static GLOBAL_ALLOC: mimalloc::MiMalloc = mimalloc::MiMalloc;

#[cfg(all(test, feature = "jemalloc"))]
#[global_allocator]
static GLOBAL_ALLOC: tikv_jemallocator::Jemalloc = tikv_jemallocator::Jemalloc;

pub mod backends;
pub mod cache;
pub mod frontend;
pub mod lang;
pub mod middleware;

#[cfg(any(test, feature = "examples"))]
pub mod examples;

#[cfg(feature = "time")]
pub mod time_macros {
    #[macro_export]
    macro_rules! timed {
        ($ctx:expr, $exp:expr) => {{
            let start = std::time::Instant::now();
            let res = $exp;
            println!(
                "timed \"{}\": {:?}",
                $ctx,
                std::time::Instant::now() - start
            );
            res
        }};
    }
}

#[cfg(not(feature = "time"))]
pub mod time_macros {
    #[macro_export]
    macro_rules! timed {
        ($ctx:expr, $exp:expr) => {{
            $exp
        }};
    }
}
