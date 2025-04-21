#![allow(clippy::get_first)]
#![feature(error_generic_member_access)] // Required for backtrace support in thiserror

pub mod backends;
pub mod constants;
pub mod frontend;
pub mod middleware;

#[cfg(test)]
pub mod examples;
