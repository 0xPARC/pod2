//! This module allows to count operations involved in tests, isolating by test.
//!
//! Example of usage:
//! ```rust
//! #[test]
//! fn test_example() {
//!     // [...]
//!     println!("{}", counter::counter_get());
//! }
//! ```
//!
use std::{cell::RefCell, fmt, thread_local};

thread_local! {
    static COUNTER: RefCell<Counter> = RefCell::new(Counter::new());
}

#[derive(Clone, Debug)]
pub(crate) struct Counter {
    hash: usize,
    tree_insert: usize,
    tree_proof_gen: usize,
}

impl Counter {
    const fn new() -> Self {
        Counter {
            hash: 0,
            tree_insert: 0,
            tree_proof_gen: 0,
        }
    }
}

impl fmt::Display for Counter {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let counter = counter_get();
        write!(f, "Counter:\n")?;
        write!(f, "  hashes: {},\n", counter.hash)?;
        write!(f, "  tree_inserts: {},\n", counter.tree_insert)?;
        write!(f, "  tree_proof_gens: {}\n", counter.tree_proof_gen)?;
        Ok(())
    }
}

pub(crate) fn count_hash() {
    #[cfg(test)]
    COUNTER.with(|c| c.borrow_mut().hash += 1);
}

pub(crate) fn count_tree_insert() {
    #[cfg(test)]
    COUNTER.with(|c| c.borrow_mut().tree_insert += 1);
}

pub(crate) fn count_tree_proof_gen() {
    #[cfg(test)]
    COUNTER.with(|c| c.borrow_mut().tree_proof_gen += 1);
}

pub(crate) fn counter_get() -> Counter {
    COUNTER.with(|c| c.borrow().clone())
}

pub(crate) fn counter_reset() {
    COUNTER.with(|c| {
        c.borrow_mut().hash = 0;
        c.borrow_mut().tree_insert = 0;
        c.borrow_mut().tree_proof_gen = 0;
    });
}
