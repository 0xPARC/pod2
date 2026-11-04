# Operations
The mechanism by which statements are derived is furnished by *operations*. Roughly speaking, with few exceptions, an operation deduces a statement from one or more existing statements according to some relation that must be satisfied between these statements. For example, if `Equal(a1, a2)` and `Equal(a2, a3)` hold true, then the operation `TransitiveEqualFromStatements` applied to these statements yields `Equal(a1, a3)`.

More precisely, an operation is a code (or, in the frontend, string identifier) followed by 0 or more arguments. These arguments are previously proved statements (up to 6) and, depending on the operation, an auxiliary witness: a Merkle proof, a Merkle state transition proof or a signature.

Most operations are of the form `XFromEntries`.  Each of their statement arguments `s_i` corresponds to the argument `a_i` of the output statement, and determines its value `value_i`:
- if `a_i` is a literal value `v`, then `s_i = None` and `value_i = v`;
- if `a_i` is the anchored key `root[key]`, then `s_i = Contains(root, key, v)` (with literal arguments) and `value_i = v`.

This is how anchored keys are introduced in statements: from a `Contains` statement, which is itself backed by a Merkle proof.

The following table summarises the natively-supported operations:

| Code | Identifier            | Args                | Condition                                                                                                             | Output                                                         |
|------|-----------------------|---------------------|-----------------------------------------------------------------------------------------------------------------------|----------------------------------------------------------------|
| 0    | `None`                |                     |                                                                                                                       | `None`                                                         |
| 2    | `EqualFromEntries`    | `s1`, `s2`          | `value1 = value2`                                   | `Equal(a1, a2)`                                              |
| 3    | `NotEqualFromEntries` | `s1`, `s2`          | `value1 != value2`                                  | `NotEqual(a1, a2)`                                           |
| 4    | `LtEqFromEntries`     | `s1`, `s2`          | `value1 <= value2`                                  | `LtEq(a1, a2)`                                               |
| 5    | `LtFromEntries`       | `s1`, `s2`          | `value1 < value2`                                   | `Lt(a1, a2)`                                                 |
| 6    | `TransitiveEqualFromStatements` | `s1`, `s2` | `s1 = Equal(a1, a2)`, `s2 = Equal(a3, a4)`, `a2 = a3`                                                          | `Equal(a1, a4)`                                              |
| 7    | `LtToNotEqual`        | `s`                 | `s = Lt(a1, a2)`                                                                                                    | `NotEqual(a1, a2)`                                           |
| 8   | `ContainsFromEntries`  | `s1`, `s2`, `s3`, `proof` | `merkle_includes(value1, value2, value3, proof) = true`             | `Contains(a1, a2, a3)` |
| 9   | `NotContainsFromEntries` | `s1`, `s2`, `proof` | `merkle_excludes(value1, value2, proof) = true`   | `NotContains(a1, a2)`                                        |
| 10   | `SumFromEntries`               | `s1`, `s2`, `s3`    | `value1 + value2 = value3`     | `Sum(a1, a2, a3)`                             |
| 11   | `ProductFromEntries`           | `s1`, `s2`, `s3`    | `value1 * value2 = value3`     | `Product(a1, a2, a3)`                         |
| 12   | `MaxFromEntries`               | `s1`, `s2`, `s3`    | `max(value1, value2) = value3` | `Max(a1, a2, a3)`                             |
| 13   | `HashFromEntries`              | `s1`, `s2`, `s3`    | `hash(value1, value2) = value3` | `Hash(a1, a2, a3)`                            |
| 14   | `PublicKeyFromEntries`         | `s1`, `s2`          | `derive_public_key(value1) = value2 `                | `PublicKey(a1, a2)`                                        |
| 15   | `SignedByFromEntries`            | `s1`, `s2`, `sig`   | `verify_signature(msg: value1, pk: value2, sig) = true` | `SignedBy(a1, a2)`                                       |
| 16   | `ContainerInsertFromEntries` | `s1`, `s2`, `s3`, `s4`, `proof` | `merkle_insert(value1, value2, value3, value4, proof) = true`    | `ContainerInsert(a1, a2, a3, a4)` |
| 17   | `ContainerUpdateFromEntries` | `s1`, `s2`, `s3`, `s4`, `proof` | `merkle_update(value1, value2, value3, value4, proof) = true`    | `ContainerUpdate(a1, a2, a3, a4)` |
| 18   | `ContainerDeleteFromEntries` | `s1`, `s2`, `s3`, `proof` | `merkle_delete(value1, value2, value3, proof) = true`    | `ContainerDelete(a1, a2, a3)` |
| 19   | `ReplaceValueWithEntry` | `[args]` `s` | `args[i] = None \| Contains, s' = s with literal arguments replaced by entries following args`    | `s'` |
| 20   | `OpenInputStatement` |  | `s` is a public statement of an input POD, proved by a Merkle proof against the input POD's statements root | `s` |

In addition, a statement of a custom predicate is proved by a custom operation, which takes as arguments the statements that satisfy the predicate definition (see [custom predicates](./custom.md)).  Custom operations output statements with literal arguments; these can then be converted to use anchored keys with `ReplaceValueWithEntry`.

<br><br>

The following table summarizes "syntactic sugar" operations.  These operations are not supported by the backend.  The frontend compiler is responsible for translating these operations into the operations above.

| Code | Identifier            | Args and desugaring              |
|------|-----------------------|---------------------|
| 1001 | DictContainsFromEntries | `DictContainsFromEntries(dict_st, key_st, value_st, proof) -> ContainsFromEntries(dict_st, key_st, value_st, proof)` |
| 1002 | DictNotContainsFromEntries | `DictNotContainsFromEntries(dict_st, key_st, proof) -> NotContainsFromEntries(dict_st, key_st, proof)` |
| 1003 | SetContainsFromEntries | `SetContainsFromEntries(set_st, value_st, proof) -> ContainsFromEntries(set_st, value_st, value_st, proof)` |
| 1004 | SetNotContainsFromEntries | `SetNotContainsFromEntries(set_st, value_st, proof) -> NotContainsFromEntries(set_st, value_st, proof)` |
| 1005 | ArrayContainsFromEntries | `ArrayContainsFromEntries(array_st, index_st, value_st, proof) -> ContainsFromEntries(array_st, index_st, value_st, proof)` |
| 1006 | GtEqFromEntries | `GtEqFromEntries(s1, s2) -> LtEqFromEntries(s2, s1)` |
| 1007 | GtFromEntries | `GtFromEntries(s1, s2) -> LtFromEntries(s2, s1)` |
| 1008 | GtToNotEqual | `GtToNotEqual(s) -> LtToNotEqual(s)` |
| 1009 | DictInsertFromEntries | `DictInsertFromEntries(old_dict_st, key_st, value_st, new_dict_st, proof) -> ContainerInsertFromEntries(old_dict_st, key_st, value_st, new_dict_st, proof)` |
| 1010 | DictUpdateFromEntries | `DictUpdateFromEntries(old_dict_st, key_st, value_st, new_dict_st, proof) -> ContainerUpdateFromEntries(old_dict_st, key_st, value_st, new_dict_st, proof)` |
| 1011 | DictDeleteFromEntries | `DictDeleteFromEntries(old_dict_st, key_st, new_dict_st, proof) -> ContainerDeleteFromEntries(old_dict_st, key_st, new_dict_st, proof)` |
| 1012 | SetInsertFromEntries | `SetInsertFromEntries(old_set_st, value_st, new_set_st, proof) -> ContainerInsertFromEntries(old_set_st, value_st, value_st, new_set_st, proof)` |
| 1013 | SetDeleteFromEntries | `SetDeleteFromEntries(old_set_st, value_st, new_set_st, proof) -> ContainerDeleteFromEntries(old_set_st, value_st, new_set_st, proof)` |
| 1014 | ArrayUpdateFromEntries | `ArrayUpdateFromEntries(old_array_st, index_st, value_st, new_array_st, proof) -> ContainerUpdateFromEntries(old_array_st, index_st, value_st, new_array_st, proof)` |
