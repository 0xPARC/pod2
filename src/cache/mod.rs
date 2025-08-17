#[cfg(feature = "disk_cache")]
mod disk;
#[cfg(feature = "disk_cache")]
pub(crate) use disk::{get, CacheEntry};

#[cfg(feature = "mem_cache")]
mod mem;
#[cfg(feature = "mem_cache")]
pub(crate) use mem::{get, CacheEntry};
