#![allow(clippy::get_first)]
#![allow(clippy::uninlined_format_args)] // TODO: Remove this in another PR
#![allow(clippy::manual_repeat_n)] // TODO: Remove this in another PR
#![allow(clippy::large_enum_variant)] // TODO: Remove this in another PR
#![feature(mapped_lock_guards)]

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
