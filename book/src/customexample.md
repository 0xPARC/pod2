
# Ethdos custom predicate, using binary AND and OR: example of a recursive batch

```
eth_friend(src, dst, private: attestation) = AND(
    SignedBy(attestation, src)
    Contains(attestation, "attestation", dst)
)

eth_dos_base(src, dst, distance) = AND(
    Equal(src, dst)
    Equal(distance, 0)
)

eth_dos_ind(src, dst, distance, private: shorter_distance, intermed) = AND(
    eth_dos(src, intermed, shorter_distance)
    // distance == shorter_distance + 1
    Sum(shorter_distance, 1, distance)
    // intermed is a friend of dst
    eth_friend(intermed, dst)
)

eth_dos(src, dst, distance) = OR(
    eth_dos_base(src, dst, distance)
    eth_dos_ind(src, dst, distance)
)
```

This batch includes four predicates.

When the definition is serialized for hashing, references to predicates in the same batch are replaced by their index in the batch: `self.0`, `self.1`, `self.2`, `self.3`.

With this renaming and the wildcards, the last of the four definitions becomes:
```
self.3(?0, ?1, ?2) = OR(
    self.1(?0, ?1, ?2)
    self.2(?0, ?1, ?2)
)
```
and similarly for the other definitions.

Each definition is serialized and hashed, and the hashes are merkelized with a zk-friendly hash to generate the "batch ID", a unique cryptographic identifier for the batch.

Then the individual predicates in the batch are identified as:
```
eth_friend = (batchID, 0)
eth_dos_base = (batchID, 1)
eth_dos_ind = (batchID, 2)
eth_dos = (batchID, 3)
```
