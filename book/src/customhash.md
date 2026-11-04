# How to hash a custom predicate

Every predicate, native or custom, is identified on the backend by a predicate ID.

The native predicates are numbered with small integers, sequentially.  The ID of a custom predicate is derived from a hash of its definition; this guarantees that two different predicates cannot have the same ID (aside from the miniscule probability of a hash collision).

This document explains how the definition of a custom predicate is serialized and hashed.

Custom predicates are defined in _batches_; see an [example](./customexample.md).  The definition of a custom predicate in a batch involves other predicates, which may include:
- native predicates
- previously-defined custom predicates
- introduction predicates
- other predicates in the same batch.

Predicate hashing is recursive: in order to hash a batch of custom predicates, we need to know IDs for all the previously-defined custom predicates it depends on.  Predicates in the same batch are referenced by their index in the batch, which avoids the circular dependency.

Each predicate in the batch is serialized (as explained below) and hashed (using a zk-friendly hash -- in the case of the plonky2 backend, Poseidon).  These hashes are put in a [Merkle tree](./merkletree.md) with the predicate index as key, and its root is the _batch ID_.  Each predicate in the batch is then referenced by
```
predicate_ID = (batch_ID, idx)
```
(here `idx` is simply the index of the predicate in the batch).

## Serialization

A predicate is serialized into field elements as follows:
```
Native(id)          => (1, id, 0, ...)
BatchSelf(idx)      => (2, idx, 0, ...)
Custom(batch_ID, i) => (3, [batch_ID], i, 0, ...)
Intro(vd_hash)      => (4, [vd_hash], 0, ...)
```
and in statements and statement templates the predicate is represented by the hash of this serialization.

A custom predicate definition is serialized as
```
(conjunction, args_len, [st_tmpl_1], ..., [st_tmpl_n])
```
where `conjunction` is 1 for AND and 0 for OR, `args_len` is the number of public arguments, and the list of statement templates is padded to the maximum arity (5) with `None` templates for an AND and `False` templates for an OR.

A statement template is serialized as its predicate (`(0, [predicate hash])`, or `(1, wildcard_index, 0, ...)` for a wildcard predicate) followed by its arguments, each padded to 9 field elements:
```
None                     => (0, 0, ...)
Literal(v)               => (1, [v], 0, ...)
AnchoredKey(?i, key)     => (2, i, 0, 0, 0, [key])
Wildcard(?i)             => (3, i, 0, ...)
SelfPredicateHash(idx)   => (4, idx, 0, ...)
```
