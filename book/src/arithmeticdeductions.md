# Arithmetic deductions

Here are some examples of deductions using the arithmetic operations -- these should help to illustrate completeness.

## Right distributivity

Given integers `x, y, z`, `(x+y) * z == x*z + y*z`.

| Line | Statement | Operation that produces it |
| -- | -- | -- |
| ST0 | `SumOf(xplusy, x, y)` | `CopyStatement` (assuming these first 5 statements are known already) |
| ST1 | `ProductOf(res1, xplusy, z)` | `CopyStatement` |
| ST2 | `ProductOf(xz, x, z)` | `CopyStatement` |
| ST3 | `ProductOf(yz, y, z)` | `CopyStatement` |
| ST4 | `SumOf(res2, xz, yz)` | `CopyStatement` |
| ST5 | `ProductOf(res1, z, xplusy)` | `CommutativeMultiplication(ST1)` |
| ST6 | `ProductOf(xz, z, x)` | `CommutativeMultiplication(ST2)` |
| ST7 | `ProductOf(yz, z, y)` | `CommutativeMultiplication(ST3)` |
| ST8 | `Eq(res1, res2)` | `Distributive(ST0, ST5, ST6, ST7, ST4)` |

## Addition of inequalities

This is motivated by Transitively Rich Girl: I want to prove I have two friends whose incomes add up to more than 12.  My friends don't reveal their incomes, only lower bounds.

| Line | Statement | Operation that produces it |
| -- | -- | -- |
| ST0 | `Gt(inc1, five)` | `CopyStatement` (assuming these first 4 statements are known already) |
| ST1 | `Gt(inc2, seven)` | `CopyStatement` |
| ST2 | `ValueOf(five, 5)` | `CopyStatement` |
| ST3 | `ValueOf(seven, 7)` | `CopyStatement` |
| ST4 | `IsInt(inc1)` | `IsIntFromGt1(ST0)` |
| ST5 | `IsInt(inc2)` | `IsIntFromGt1(ST1)` |
| ST6 | `SumOf(totinc, inc1, inc2)` | `NewEntryFromSum(ST4, ST5)` |
| ST7 | `ValueOf(twelve, 12)` | `NewEntryFromValueOf` |
| ST8 | `SumOf(twelve, five, seven)` | `SumOfFromValues(ST7, ST2, ST3)` |
| ST9 | `IsInt(seven)` | `IsIntFromValue(ST3)` |
| ST10 | `SumOf(inc1plusseven, inc1, seven)` | `NewEntryFromSum(ST4, ST9)` |
| ST11 | `Gt(inc1plusseven, twelve)` | `AddGt(ST0, ST10, ST8)` |
| ST12 | `SumOf(totinc, inc2, inc1)` | `CommutativeAddition(ST6)` |
| ST13 | `SumOf(inc1plusseven, seven, inc1)` | `CommutativeAddition(ST10)` |
| ST14 | `Gt(totinc, inc1plusseven)` | `AddGt(ST1, ST12, ST13)` |
| ST15 | `Geq(totinc, inc1plusseven)` | `GeqFromGt(ST14)` |
| ST16 | `Gt(totinc, twelve)` | `TransitiveGeqGt(ST15, ST11)` |

