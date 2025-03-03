# How to hash a custom predicate

Every predicate, native or custom, is identified on the backend by a predicate ID.

The native predicates are numbered with small integers, sequentially.  The ID of a custom predicate is a hash of its definition; this guarantees that two different predicates cannot have the same ID (aside from the miniscule probability of a hash collision).

This document explains in some detail how the definition of a custom predicate is serialized and hashed.

Custom predicates are defined in _groups_ (also known as _batches_); see an [example](./customexample.md).  The definition of a custom predicate in a group involves other predicates, which may include:
- native predicates
- previously-defined custom predicates
- other predicates in the same group.

Predicate hashing is recursive: in order to hash a group of custom predicates, we need to know IDs for all the previously-defined custom predicates it depends on.

The definition of the whole group of custom predicates is serialized (as explained below), and that serialization is hashed (using a zk-friendly hash -- in the case of the plonky2 backend, Poseidon) to give a _group ID_.  Each predicate in the group is then referenced by
```
predicate_ID = (group_ID, idx)
```
(here `idx` is simply the index of the predicate in the group).
