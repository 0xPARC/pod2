use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::Hash;

use anyhow::{anyhow, Result};

pub(crate) fn hashmap_insert_no_dupe<S: Clone + Debug + Eq + Hash, T: Clone + Debug + Eq>(
    hm: &mut HashMap<S, T>,
    kv: (S, T),
) -> Result<()> {
    let (k, v) = kv.clone();
    let res = hm.insert(kv.0, kv.1);
    match res {
        Some(w) if w != v => Err(anyhow!(
            "Key {:?} exists in table with value {:?} != {:?}.",
            k,
            w,
            v
        )),
        _ => Ok(()),
    }
}
