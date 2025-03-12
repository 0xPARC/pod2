# Operations
The mechanism by which statements are derived is furnished by *operations*. Roughly speaking, with few exceptions, an operation deduces a statement from one or more existing statements according to some relation that must be satisfied between these statements. For example, if `Equal(ak1, ak2)` holds true, then the operation `SymmetricEq` applied to this statement yields `Equal(ak2, ak1)`.

More precisely, an operation is a code (or, in the frontend, string identifier) followed by 0 or more arguments. These arguments may consist of up to three statements, up to one key-value pair and up to one Merkle proof.

The following tables summarize the natively-supported operations:

Operations that produce new entries:
| Identifier | Args | Condition | Output |
| -- | -- | -- | -- |
| `*NewEntryFromValueOf` | - | | `ValueOf(new_ak, value)`, where `new_ak` has key `key` and origin ID 1, and `key` has not yet been used |
| `*NewEntryFromEq` | - | | `Eq(new_ak, old_ak)`, where `new_ak` has key `key` and origin ID 1, and `key` has not yet been used |
| `*NewEntryFromSum` | `IsInt(old_ak1), IsInt(old_ak2)` | | `SumOf(new_ak, old_ak1, old_ak2)`, where `new_ak` has key `key` and origin ID 1, and `key` has not yet been used |
| `*NewEntryFromDiff` | `IsInt(old_ak1), IsInt(old_ak2)` | | `SumOf(old_ak1, new_ak, old_ak2)`, where `new_ak` has key `key` and origin ID 1, and `key` has not yet been used |
| `*NewEntryFromProduct` | `IsInt(old_ak1), IsInt(old_ak2)` | | `ProductOf(new_ak, old_ak1, old_ak2)`, where `new_ak` has key `key` and origin ID 1, and `key` has not yet been used |

Copying statements, and the substitution principle of equality:
| Identifier | Args | Condition | Output |
| -- | -- | -- | -- |
| `*CopyStatement` | `AnyStatement(args...)` | (copy the same statement) | `AnyStatement(args...)` |
| `*SubstituteEqual` | `Eq(ak1, ak2)`, `AnyStatement(old_args...)` | `new_args` is the same as `old_args` except that one instance of `ak1` is replaced by `ak2` | `AnyStatement(new_args...)` |

Note: Since a statement can take a literal as an argument in place of an anchored key, `SubstituteEqual` should be able to take `ValueOf` in place of `Eq`, and perform the substitution in either direction...

Further properties of equality:
| Identifier | Args | Condition | Output |
| -- | -- | -- | -- |
| `ReflexiveEquality` | | `IsDefined(x)` | `Eq(x, x)`, where `x` is any anchored key |
| `SymmetricEquality` | `Eq(x, y)` | | `Eq(y, x)`, where `x` and `y` are any anchored keys |

Notes:
- `SymmetricEquality` is not required: it could be derived from `ReflexiveEquality` and `SubstituteEqual`.  We include it because we prefer to have one statement than two.
- Transitivity (if `Eq(x, y)` and `Eq(y, z)`, then `Eq(x, z)`) is not included, because it is nothing more than a special case of `SubstituteEqual`.

Other ways to prove equality:
| Identifier | Args | Condition | Output |
| -- | -- | -- | -- |
| `EqFromSum` | `SumOf(x, ak1, ak2), SumOf(y, ak1, ak2)` | `Eq(x, y)` |
| `EqFromDiff` | `SumOf(ak1, x, ak2), SumOf(ak1, y, ak2)` | `Eq(x, y)` |
| `EqFromProduct` | `ProductOf(x, ak1, ak2), ProductOf(y, ak1, ak2)` | `Eq(x, y)` |

Statements directly from values:
| Identifier | Args | Condition | Output |
| -- | -- | -- | -- |
| `IsDefinedFromValue` | `ValueOf(ak1, value1)` | | `IsDefined(ak1)` |
| `*IsIntFromValue` | `ValueOf(ak1, value1)` | `value1` is in the integer range | `IsInt(ak1)` |
| `*EqFromValues`| `ValueOf(ak1, value1), ValueOf(ak2, value2)` | `value1 = value2` | `Eq(ak1, ak2) |
| `*NeqFromValues`| `ValueOf(ak1, value1), ValueOf(ak2, value2)` | `value1 != value2` | `Neq(ak1, ak2) |
| `*GtFromValues`| `ValueOf(ak1, value1), ValueOf(ak2, value2)` | `value1 > value2` | `Gt(ak1, ak2) |
| `*GeqFromValues`| `ValueOf(ak1, value1), ValueOf(ak2, value2)` | `value1 >= value2` | `Geq(ak1, ak2) |
| `*SumOfFromValues`  | `ValueOf(ak1, value1)`, `ValueOf(ak2, value2)`, `ValueOf(ak3, value3)`    |  `value1 = value2 + value3`, `value1`, `value2`, `value3` are in the integer range     | `SumOf(ak1, ak2, ak3)` |
| `*ProductOfFromValues`  | `ValueOf(ak1, value1)`, `ValueOf(ak2, value2)`, `ValueOf(ak3, value3)`    |  `value1 = value2 * value3`, `value1`, `value2`, `value3` are in the integer range     | `ProductOf(ak1, ak2, ak3)` |


Implications about inequalities:
| Identifier | Args | Condition | Output |
| -- | -- | -- | -- |
| `GeqFromGt` | `Gt(ak1, ak2)` | | `Geq(ak1, ak2)` |
| `NeqFromGt` | `Gt(ak1, ak2)` | | `Neq(ak1, ak2)` |
| `GeqFromEq` | `Eq(ak1, ak2)` | | `Geq(ak1, ak2)` |
| `SymmetricNeq` | `Neq(ak1, ak2)` | | `Neq(ak2, ak1)` |
| `GtFromGeqAndNeq` | `Geq(ak1, ak2), Neq(ak1, ak2)` | | `Gt(ak1, ak2)` |
| `EqFromGeqAndGeq` | `Geq(ak1, ak2), Geq(ak2, ak1)` | | `Eq(ak1, ak2)` |

Transitivity for inequalities:
| Identifier | Args | Condition | Output |
| -- | -- | -- | -- |
| `TransitiveGtGeq` | `Gt(ak1, ak2), Geq(ak2, ak3)` | | `Gt(ak1, ak3)` |
| `TransitiveGeqGt` | `Geq(ak1, ak2), Gt(ak2, ak3)` | | `Gt(ak1, ak3)` |
| `TransitiveGeqGeq` | `Geq(ak1, ak2), Geq(ak2, ak3)` | | `Geq(ak1, ak3)` |


Deducing `IsInt` and `IsDefined`:
| Identifier | Args | Condition | Output |
| -- | -- | -- | -- |
| `IsDefinedFromIsInt` | `IsInt(ak1)` | | `IsDefined(ak1)` |
| `IsIntFromEq` | `Eq(x, y), IsInt(y)` | | `IsInt(x)` |
| `IsIntFromGt1` | `Gt(x, y)` | | `IsInt(x)` |
| `IsIntFromGt2` | `Gt(x, y)` | | `IsInt(y)` |
| `IsIntFromGeq1` | `Geq(x, y)` | | `IsInt(x)` |
| `IsIntFromGeq2` | `Geq(x, y)` | | `IsInt(y)` |
| `IsIntFromNeq` | `Neq(x, y)` | | `IsInt(x)` |
| `IsIntFromSum` | `SumOf(x, y, z)` | (note that SumOf implies that all its arguments are ints) | `IsInt(x)` |
| `IsIntFromDiff` | `SumOf(x, y, z)` | | `IsInt(y)` |
| `IsIntFromProduct` | `ProductOf(x, y, z)` | (same with ProductOf) | `IsInt(x)` |
| `IsIntFromQuotient` | `ProductOf(x, y, z)` | | `IsInt(y)` |

Ring axioms
| Identifier | Args | Condition | Output |
| -- | -- | -- | -- |
| `ZeroAddition` | `IsInt(x)` | `x` is an anchored key | `SumOf(x, x, 0)` |
| `CommutativeAddition` | `SumOf(s1, x, y), SumOf(s2, y, x)` | | `Eq(s1, s2)` |
| `AssociativeAddition` | `SumOf(xy, x, y), SumOf(s1, xy, z), SumOf(yz, y, z), SumOf(s2, x, yz)` | | `Eq(s1, s2)` |
| `ZeroMultiplication` | `IsInt(x)` | `x` is an anchored key | `ProductOf(0, 0, x)` |
| `OneMultiplication` | `IsInt(x)` | `x` is an anchored key | `ProductOf(x, 1, x)` |
| `CommutativeMultiplication` | `ProductOf(p1, x, y), ProductOf(p2, y, x)` | | `Eq(p1, p2)` |
| `AssociativeMultiplication` | `ProductOf(xy, x, y), ProductOf(p1, xy, z), ProductOf(yz, y, z), ProductOf(p2, x, yz)` | | `Eq(p1, p2)` |
| `Distributive` | `SumOf(yplusz, y, z), ProductOf(res1, x, yplusz), ProductOf(xy, x, y), ProductOf(xz, x, z), SumOf(res2, xy, xz)` | | `Eq(res1, res2)` |

Note: `ZeroAddition` and `ZeroMultiplication` can be derived from other statements but we include them for simplicity.

Order axioms
| Identifier | Args | Condition | Output |
| -- | -- | -- | -- |
| `AddGt` | `Gt(x1, y1), SumOf(x2, x1, c), SumOf(y2, y1, c)` | | `Gt(x2, y2)` |
| `AddGeq` | `Geq(x1, y1), SumOf(x2, x1, c), SumOf(y2, y1, c)` | | `Geq(x2, y2)` |
| `AddNeq` | `Neq(x1, y1), SumOf(x2, x1, c), SumOf(y2, y1, c)` | | `Neq(x2, y2)` |
| `MulPosGt`  | `Gt(x1, y1), Gt(c, 0), ProductOf(x2, x1, c), ProductOf(y2, y1, c)` | | `Gt(x2, y2)` |
| `MulPosGeq`  | `Geq(x1, y1), Geq(c, 0), ProductOf(x2, x1, c), ProductOf(y2, y1, c)` | | `Geq(x2, y2)` |
| `MulNonzeroNeq`  | `Neq(x1, y1), Neq(c, 0), ProductOf(x2, x1, c), ProductOf(y2, y1, c)` | | `Neq(x2, y2)` |


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
