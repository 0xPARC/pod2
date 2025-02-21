
# Ethdos custom predicate, using binary AND and OR: example of a direct definition and a recursive group

## Direct definition
(DEPRECATED: All predicates must be defined as part of a group.)
```
eth_friend(src_or, src_key, dst_or, dst_key) = and<
    // there is an attestation pod that's a SIGNATURE POD
    ValueOf(attestation_pod, "type", SIGNATURE)     
    
    // the attestation pod is signed by (src_or, src_key)
    Equal((attestation_pod, "signer"), (src_or, src_key))  

    // that same attestation pod has an "attestation"
    Equal((attestation_pod, "attestation"), (dst_or, dst_key))
>

On the backend, this is converted to a rule where all the arguments are either wildcards or literals:
eth_friend(*1, *2, *3, *4) = and<
    // there is an attestation pod that's a SIGNATURE POD
    ValueOf(*5, "type", SIGNATURE)     
    
    // the attestation pod is signed by (src_or, src_key)
    Equal((*5, "signer"), (*1, *2))  

    // that same attestation pod has an "attestation"
    Equal((*5, "attestation"), (*3, *4))
>

This backend definition is then hashed in the obvious way.

```

## Recursive group definition

```
eth_dos_distance(src_or, src_key, dst_or, dst_key, distance_or, distance_key) = or<
   eth_dos_distance_ind_0(src_or, src_key, dst_or, dst_key, distance_or, distance_key),
   eth_dos_distance_base(src_or, src_key, dst_or, dst_key, distance_or, distance_key)
   >

eth_dos_distance_base(src_or, src_key, dst_or, dst_key, distance_or, distance_key) = and<
   eq(src_or, src_key, dst_or, dst_key),
   ValueOf(distance_or, distance_key, 0)
   >


eth_dos_distance_ind_0(src_or, src_key, dst_or, dst_key, distance_or, distance_key) = and<
   eth_dos_distance(src_or, src_key, intermed_or, intermed_key, shorter_distance_or, shorter_distance_key)

   // distance == shorter_distance + 1
   ValueOf(one_or, one_key, 1)
   SumOf(distance_or, distance_key, shorter_distance_or, shorter_distance_key, one_or, one_key)

   // intermed is a friend of dst
   eth_friend(intermed_or, intermed_key, dst_or, dst_key)
   >
```

This group includes three statements.

When the definition is serialized for hashing, the statements are renamed to SELF.1, SELF.2, SELF.3.

With this renaming and the wildcards, the first of the three definitions becomes:
```
SELF.1( *1, *2, *3, *4, *5, *6 ) = or<
   SELF.2( *1, *2, *3, *4, *5, *6 ) ,
   SELF.3( *1, *2, *3, *4, *5, *6 ) 
   >
```
and similarly for the other two definitions.

The above definition is serialized in-circuit and hashed with a zk-friendly hash to generate the "group hash", a unique cryptographic identifier for the group.

Then the individual statements in the group are identified as:
```
eth_dos_distance = groupHASH.1
eth_dos_distance_base = groupHASH.2
eth_dos_distance_ind = groupHASH.3
```
