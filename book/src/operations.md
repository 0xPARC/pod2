# Operations
The mechanism by which statements are derived is furnished by *operations*. Roughly speaking, with few exceptions, an operation deduces a statement from one or more existing statements according to some relation that must be satisfied between these statements. For example, if `Equal(ak1, ak2)` holds true, then the operation `SymmetricEq` applied to this statement yields `Equal(ak2, ak1)`.

More precisely, an operation is a code (or, in the frontend, string identifier) followed by 0 or more arguments. These arguments may consist of up to three statements, up to one key-value pair and up to one Merkle proof.

The following table summarises the natively-supported operations:

| Code | Identifier            | Args                | Condition                                                                                                             | Output                                                         |
|------|-----------------------|---------------------|-----------------------------------------------------------------------------------------------------------------------|----------------------------------------------------------------|
| 0    | `None`                |                     |                                                                                                                       | `None`                                                         |
| 1    | `NewEntry`[^newentry] | `(key, value)`      |                                                                                                                       | `ValueOf(ak, value)`, where `ak` has key `key` and origin ID 1 |
| 2    | `CopyStatement`       | `s`                 |                                                                                                                       |                                                                |
| 3    | `EntryEq`             | `s1`, `s2`          | `s1 = ValueOf(ak1, value1)`, `s2 = ValueOf(ak2, value2)`, `value1 = value2`                                           | `Eq(ak1, ak2)`                                                 |
| 4    | `EntryNEq`            | `s1`, `s2`          | `s1 = ValueOf(ak1, value1)`, `s2 = ValueOf(ak2, value2)`, `value1 != value2`                                          | `NEq(ak1, ak2)`                                                |
| 5    | `EntryGt`             | `s1`, `s2`          | `s1 = ValueOf(ak1, value1)`, `s2 = ValueOf(ak2, value2)`, `value1 > value2`                                           | `Gt(ak1, ak2)`                                                 |
| 6    | `EntryLEq`            | `s1`, `s2`          | `s1 = ValueOf(ak1, value1)`, `s2 = ValueOf(ak2, value2)`, `value1 <= value2`                                          | `LEq(ak1, ak2)`                                                |
| 7    | `TransitiveEq`        | `s1`, `s2`          | `s1 = Equal(ak1, ak2)`, `s2 = Equal(ak3, ak4)`, `ak2 = ak3`                                                           | `Eq(ak1, ak4)`                                                 |
| 8    | `GtToNEq`             | `s`                 | `s = Gt(ak1, ak2)`                                                                                                    | `NEq(ak1, ak2)`                                                |
| 9    | `LtToNEq`             | `s`                 | `s = Lt(ak1, ak2)`                                                                                                    | `NEq(ak1, ak2)`                                                |
| 10   | `EntryContains`       | `s1`, `s2`, `proof` | `s1 = ValueOf(ak1, value1)`, `s2 = ValueOf(ak2, value2)`, `merkle_includes(value1, value2, proof) = true`             | `Contains(ak1, ak2)`                                           |
| 11   | `EntrySintains`       | `s1`, `s2`, `proof` | `s1 = ValueOf(ak1, value1)`, `s2 = ValueOf(ak2, value2)`, `merkle_excludes(value1, value2, proof) = true`             | `Sintains(ak1, ak2)`                                           |
| 12   | `RenameContains`      | `s1`, `s2`          | `s1 = Contains(ak1, ak2)`, `s2 = Equal(ak3, ak4)`, `ak1 = ak3`                                                        | `Contains(ak4, ak2)`                                           |
| 13   | `SumOf`               | `s1`, `s2`, `s3`    | `s1 = ValueOf(ak1, value1)`, `s2 = ValueOf(ak2, value2)`, `s3 = ValueOf(ak3, value3)`, `value1 = value2 + value3`     | `SumOf(ak1, ak2, ak3)`                                         |
| 14   | `ProductOf`           | `s1`, `s2`, `s3`    | `s1 = ValueOf(ak1, value1)`, `s2 = ValueOf(ak2, value2)`, `s3 = ValueOf(ak3, value3)`, `value1 = value2 * value3`     | `ProductOf(ak1, ak2, ak3)`                                     |
| 15   | `MaxOf`               | `s1`, `s2`, `s3`    | `s1 = ValueOf(ak1, value1)`, `s2 = ValueOf(ak2, value2)`, `s3 = ValueOf(ak3, value3)`, `value1 = max(value2, value3)` | `MaxOf(ak1, ak2, ak3)`                                         |

<!-- NOTE: should we 'uniformize' the names? eg. currently we have `EntryGt` and `GtToNEq` -->

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
