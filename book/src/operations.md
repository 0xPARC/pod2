# Operations
The mechanism by which statements are derived is furnished by *operations*. Roughly speaking, with few exceptions, an operation deduces a statement from one or more existing statements according to some relation that must be satisfied between these statements. For example, if `Equal(ak1, ak2)` holds true, then the operation `SymmetricEq` applied to this statement yields `Equal(ak2, ak1)`.

More precisely, an operation is a code (or, in the frontend, string identifier) followed by 0 or more arguments. These arguments may consist of up to three statements, up to one key-value pair and up to one Merkle proof.

The following table summarises the natively-supported operations:

| Code | Identifier            | Args                | Condition                                                                                                             | Output                                                         |
|------|-----------------------|---------------------|-----------------------------------------------------------------------------------------------------------------------|----------------------------------------------------------------|
| 0    | `None`                |                     |                                                                                                                       | `None`                                                         |
| 1    | `NewEntry`[^newentry] | `(key, value)`      |                                                                                                                       | `ValueOf(ak, value)`, where `ak` has key `key` and origin ID 1 |
| 2    | `CopyStatement`       | `s`                 |                                                                                                                       |                                                                |
| 3    | `EqualFromEntries`             | `s1`, `s2`          | `s1 = ValueOf(ak1, value1)`, `s2 = ValueOf(ak2, value2)`, `value1 = value2`                                           | `Equal(ak1, ak2)`                                                 |
| 4    | `NotEqualFromEntries`            | `s1`, `s2`          | `s1 = ValueOf(ak1, value1)`, `s2 = ValueOf(ak2, value2)`, `value1 != value2`                                          | `NotEqual(ak1, ak2)`                                                |
| 5    | `LtEqFromEntries`             | `s1`, `s2`          | `s1 = ValueOf(ak1, value1)`, `s2 = ValueOf(ak2, value2)`, `value1 <= value2`                                           | `LtEq(ak1, ak2)`                                                 |
| 6    | `LtFromEntries`            | `s1`, `s2`          | `s1 = ValueOf(ak1, value1)`, `s2 = ValueOf(ak2, value2)`, `value1 < value2`                                          | `Lt(ak1, ak2)`                                                |
| 7    | `TransitiveEqualFromStatements`        | `s1`, `s2`          | `s1 = Equal(ak1, ak2)`, `s2 = Equal(ak3, ak4)`, `ak2 = ak3`                                                           | `Equal(ak1, ak4)`                                                 |
| 8    | `LtToNotEqual`             | `s`                 | `s = Lt(ak1, ak2)`                                                                                                    | `NotEqual(ak1, ak2)`                                                |
| 9   | `ContainsFromEntries`       | `s1`, `s2`, `s3`, `proof` | `s1 = ValueOf(ak1, value1)`, `s2 = ValueOf(ak2, value2)`, `s3 = ValueOf(ak3, value3)`, `merkle_includes(value1, value2, value3, proof) = true`             | `Contains(ak1, ak2, ak3)`                                           |
| 10   | `NotContainsFromEntries`       | `s1`, `s2`, `proof` | `s1 = ValueOf(ak1, value1)`, `s2 = ValueOf(ak2, value2)`, `merkle_excludes(value1, value2, proof) = true`             | `NotContains(ak1, ak2)`                                           |
| 11   | `SumOf`               | `s1`, `s2`, `s3`    | `s1 = ValueOf(ak1, value1)`, `s2 = ValueOf(ak2, value2)`, `s3 = ValueOf(ak3, value3)`, `value1 = value2 + value3`     | `SumOf(ak1, ak2, ak3)`                                         |
| 12   | `ProductOf`           | `s1`, `s2`, `s3`    | `s1 = ValueOf(ak1, value1)`, `s2 = ValueOf(ak2, value2)`, `s3 = ValueOf(ak3, value3)`, `value1 = value2 * value3`     | `ProductOf(ak1, ak2, ak3)`                                     |
| 13   | `MaxOf`               | `s1`, `s2`, `s3`    | `s1 = ValueOf(ak1, value1)`, `s2 = ValueOf(ak2, value2)`, `s3 = ValueOf(ak3, value3)`, `value1 = max(value2, value3)` | `MaxOf(ak1, ak2, ak3)`                                         |
| 14   | `HashOf`              | `s1`, `s2`, `s3`    | `s1 = ValueOf(ak1, value1)`, `s2 = ValueOf(ak2, value2)`, `s3 = ValueOf(ak3, value3)`, `value1 = hash(value2, value3)`| `HashOf(ak1, ak2, ak3)`                                        |
| 15   | `PublicKeyOf`         | `s1`, `s2`          | `s1 = ValueOf(ak1, value1)`, `s2 = ValueOf(ak2, value2)`, `value1 = derive_public_key(value2)`                        | `PublicKeyOf(ak1, ak2)`                                        |

<br><br>

The following table summarizes "syntactic sugar" operations.  These operations are not supported by the backend.  The frontend compiler is responsible for translating these operations into the operations above.

| Code | Identifier            | Args and desugaring              | 
|------|-----------------------|---------------------|
| 1001 | DictContainsFromEntries | `DictContainsFromEntries(dict_st, key_st, value_st) -> ContainsFromEntries(dict_st, key_st, value_st)` |
| 1002 | DictNotContainsFromEntries | `DictNotContainsFromEntries(dict_st, key_st, value_st) -> NotContainsFromEntries(dict_st, key_st, value_st)` |
| 1003 | SetContainsFromEntries | `SetContainsFromEntries(set_st, value_st) -> ContainsFromEntries(set_st, value_st, value_st)` |
| 1004 | SetNotContainsFromEntries | `SetNotContainsFromEntries(set_st, value_st) -> NotContainsFromEntries(set_st, value_st, value_st)` |
| 1005 | ArrayContainsFromEntries | `ArrayContainsFromEntries(array_st, index_st, value_st) -> ContainsFromEntries(array_st, index_st, value_st)` |
| 1006 | GtEqFromEntries | `GtEqFromEntries(s1, s2) -> LtEqFromEntries(s2, s1)` |
| 1007 | GtFromEntries | `GtFromEntries(s1, s2) -> LtFromEntries(s2, s1)` |
| 1008 | GtToNotEqual | `GtToNotEqual(s1, s2) -> LtToNotEqual(s1, s2)` |

<br><br>

<span style="color:green"><b>WIP</b>. The following table defines more operations that are not yet [implemented](https://github.com/0xPARC/pod2/blob/main/src/middleware/operation.rs#L20).<br>
Issue keeping track of the operations: [#108](https://github.com/0xPARC/pod2/issues/108).
</span><br>
| Code | Identifier       | Args       | Condition                                                      | Output               |
|------|------------------|------------|----------------------------------------------------------------|----------------------|
|      | `SymmetricEq`    | `s`        | `s = Equal(ak1, ak2)`                                          | `Eq(ak2, ak1)`       |
|      | `SymmetricNEq`   | `s`        | `s = NotEqual(ak1, ak2)`                                       | `NEq(ak2, ak1)`      |
|      | `RenameSintains` | `s1`, `s2` | `s1 = Sintains(ak1, ak2)`, `s2 = Equal(ak3, ak4)`, `ak1 = ak3` | `Sintains(ak4, ak2)` |
|      | `TransitiveEq`   | `s1`, `s2` | `s1 = Equal(ak1, ak2)`, `s2 = Equal(ak3, ak4)`, `ak2 = ak3`    | `Eq(ak1, ak4)`       |
|      | `TransitiveGt`   | `s1`, `s2` | `s1 = Gt(ak1, ak2)`, `s2 = Gt(ak3, ak4)`, `ak2 = ak3`          | `Gt(ak1, ak4)`       |
|      | `TransitiveLEq`  | `s1`, `s2` | `s1 = LEq(ak1, ak2)`, `s2 = LEq(ak3, ak4)`, `ak2 = ak3`        | `LEq(ak1, ak4)`      |
|      | `LEqToNEq`       | `s`        | `s = LEq(ak1, ak2)`                                            | `NEq(ak1, ak2)`      |


[^newentry]: Since new key-value pairs are not constrained, this operation will have no arguments in-circuit.
