#[cfg(feature = "disk_cache")]
mod disk;
#[cfg(feature = "disk_cache")]
pub use disk::{get, CacheEntry};

#[cfg(feature = "mem_cache")]
mod mem;
#[cfg(feature = "mem_cache")]
pub use mem::{get, CacheEntry};
