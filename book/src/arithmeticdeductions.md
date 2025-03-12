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

(Public output is statements `ST6, ST16`)

## Multiplication by a negative number flips the order of an inequality

Gt(x1, y1), Gt(c, 0), ProductOf(x2, x1, c), ProductOf(y2, y1, c)

| Line | Statement | Operation that produces it |
| -- | -- | -- |
| ST0 | `Gt(x1, y1)` | `CopyStatement` (assuming first 4 statements known) |
| ST1 | `Gt(0, c)` | `CopyStatement` |
| ST2 | `ProductOf(x2, x1, c)` | `CopyStatement` |
| ST3 | `ProductOf(y2, y1, c)` | `CopyStatement` |
| ST4 | `IsInt(c)` | `IsIntFromGt(ST1)` |
| ST5 | `ValueOf(zero, 0)` | `NewEntryFromValueOf` |
| ST6 | `IsInt(zero)` | `IsIntFromValue(ST5)` |
| ST7 | `SumOf(zero, negc, c)` | `NewEntryFromDiff(ST4, ST6)` // let negc = -c |
| ST8 | `SumOf(zero, c, negc)` | `CommutativeAddition(ST7)` |
| ST9 | `IsInt(negc)` | `IsIntFromDiff(ST7)` |
| ST10 | `SumOf(negc, negc, zero)` | `ZeroAddition(ST5, ST9)` |
| ST11 | `SumOf(negc, zero, negc)` | `CommutativeAddition(ST10)` |
| ST12 | `Gt(zero, c)` | `SubstituteEquality(ST5, ST1)` |
| ST13 | `Gt(negc, zero)` | `AddGt(ST12, ST11, ST8)` // negc > 0 -- wow it sure took long enough to get here |
| ST14 | `IsInt(x1)` | `IsIntFromGt(ST0)` |
| ST15 | `IsInt(y1)` | `IsIntFromGt(ST0)` |
| ST16 | `ProductOf(x3, x1, negc)` | `NewEntryFromProduct(ST14, ST9)` // let x3 = x1 * (-c) | 
| ST17 | `ProductOf(y3, y1, negc)` | `NewEntryFromProduct(ST15, ST9)` // let y3 = y1 * (-c) |
// next let's prove that x3 = -x2
| ST18 | `IsInt(x2)` | `IsIntFromProduct(ST2)` |
| ST19 | `IsInt(x3)` | `IsIntFromProducte(ST16)` |
| ST20 | `SumOf(zero_a, x3, x2)` | `NewEntryFromSum(ST19, ST18)` // we will show that zero_a is 0 |
| ST21 | `ProductOf(zero_b, x1, zero)` | `NewEntryFromProduct(ST14, ST6)` // and zero_b is 0 too |
| ST22 | `Eq(zero_a, zero_b)` | `Distributive(ST7, ST21, ST2, ST16, ST7)` |
| ST23 | `ProductOf(zero, zero, x1)` | `ZeroMultiplication(ST5, ST14)` |
| ST24 | `ProductOf(zero, x1, zero)` | `CommutativeMultiplication(ST23)` |
| ST25 | `Eq(zero, zero_b)` | `EqFromProduct(ST24, ST22)` |
| ST26 | `Eq(zero_b, zero)` | `SymmetricEquality(ST25)` |
| ST27 | `Eq(zero_a, zero)` | `SubstituteEquality(ST26, ST22)` |
| ST28 | `SumOf(zero, x3, x2)` | `SubstituteEquality(ST27, ST20)` |
// eleven more lines will prove that y3 = -y2
// it's exactly like the last 11 lines, but with y's instead of x's
| ST29 | `IsInt(y2)` | `IsIntFromProduct(ST3)` | 
| ST30 | `IsInt(y3)` | `IsIntFromProducte(ST17)` |
| ... | ... | ... |
| ST39 | `SumOf(zero, y3, y2)` | (ten lines of tedious and unenlightening intermediate steps omitted) |
// next we show that x3 > y3, this is easy
// in other wrods, -x2 > -y2
| ST40 | `Gt(x3, y3)` | `MulPosGt(ST0, ST13, ST16, ST17)` |
// finally we need to get y2 > x2
// this is just a matter of adding (x2 + x2)  to both sides of -x2 > -y2
// but it's gonna take a few steps
// first let's prove y3 + z2 = x2
| ST41 | `SumOf(z2, x2, y2)` | `NewEntryFromSum(ST18, ST29)` |
| ST42 | `SumOf(x2, x2, zero)` | `ZeroAddition(ST18)` |
| ST43 | `SumOf(zero, y2, y3)` | `CommutativeAddition(ST39)` |
| ST44 | `IsInt(z2)` | `IsIntFromSum(ST41)` |
| ST45 | `SumOf(temp_x2_copy, z2, y3)` | `NewEntryFromSum(ST44, ST30)` // soon we will see temp_x2_copy is x2 |
| ST46 | `Eq(temp_x2_copy, x2)` | `AssociativeAddition(ST41, ST45, ST42, ST43)` |
| ST47 | `SumOf(x2, z2, y3)` | `SubstituteEquality(ST46, ST45)` |
| ST48 | `SumOf(x2, y3, z2)` | `CommutativeAddition(ST47)` |
// next let's prove x3 + z2 = y2
// it's exactly analogous, just swap the x's and the y's
| ... | ... | ...
| ST56 | `SumOf(y2, x3, z2)` | `SubstituteEquality(ST46, ST45)` |
// finally we can finish, woo hoo!
| ST57 | `Gt(y2, x2)` | `AddGt(ST40, ST48, ST56)` |

What a mess!
