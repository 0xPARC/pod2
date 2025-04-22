#![allow(clippy::get_first)]
#![feature(trait_upcasting)]

pub mod backends;
pub mod constants;
pub mod frontend;
pub mod middleware;

#[cfg(test)]
pub mod examples;
