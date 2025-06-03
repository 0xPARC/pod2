#![allow(clippy::get_first)]
#![feature(trait_upcasting)]
#![feature(mapped_lock_guards)]

pub mod backends;
pub mod constants;
pub mod frontend;
pub mod middleware;

#[cfg(test)]
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
