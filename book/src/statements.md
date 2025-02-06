# Statements
The claims asserted by a POD are referred to as its *statements*. These statements introduce values and express relations between them, where the values may or may not be part of the same POD. The mechanism for referring to values in arbitrary PODs is furnished by [anchored keys](./anchoredkeys.md).

A statement is a code (or, in the frontend, string identifier) followed by 0 or more arguments. These arguments may consist of up to three anchored keys and up to one POD value.

Statements come in two types: _built-in_ and _custom_.  There is a short list of built-in statements (see below). [^builtin]
In addition, users can freely define custom statements.

From the user (front-end) perspective, a statement represents a claim about the values of some number of entries -- the statement can only be proved if the claim is true.

From the circuit (back-end) perspective, a statement can be proved either:
- by direct in-circuit verification, or
- by an operation (aka deduction rule).

## Native statement types

### Frontend native statements

The frontend language exposes the following natively-supported statements.  The arguments to each statement are either [anchored keys](./anchoredkeys.md) (i.e. references to entries) or value literals.

Native statements that apply to arbitrary types.
```
ValueOf(ak1, lit)    // Entry ak1 has value lit
Eq(ak1, ak2)         // Entries ak1 and ak2 have the same value
NEq(ak1, ak2)        // Entries ak1 and ak2 have different values (and may or may not be of the same type)
```

Native statements that apply to ```Integer``` only.
These statements imply that both entries they refer to are of type ```Integer``` -- so for example, ```Gt(ak1, ak2)``` means that both ```value_of(ak1)``` and ```value_of(ak2)``` are of type ```Integer``` (within the bounds specified in the [Integer type documentation](./values.md)), and ```value_of(ak1) > value_of(ak2)```.
```
Gt(ak1, ak2)                // value_of(ak1) > value_of(ak2)
GEq(ak1, ak2)                // value_of(ak1) >= value_of(ak2)
Lt(ak1, ak2)                // value_of(ak1) < value_of(ak2)
LEq(ak1, ak2)                // value_of(ak1) <= value_of(ak2)
SumOf(ak1, ak2, ak3)        // value_of(ak1) = value_of(ak2) + value_of(ak3)
ProductOf(ak1, ak2, ak3)    // value_of(ak1) = value_of(ak2) * value_of(ak3)
MaxOf(ak1, ak2, ak3)        // value_of(ak1) = max(value_of(ak2), value_of(ak3))
```

Native statements that apply to Merkle trees.[^merk]
```
Contains(root, key, value)          // value_of(root) is a Merkle root, and (value_of(key), value_of(value)) appears as a key-value pair in the Merkle tree
NotContains(root, key)    // value_of(root) is a Merkle root, and (value_of(key)) is not the key of any key-value pair in the Merkle tree
```

### Backend native statements

On the backend, each native statement is identified by a numerical "code" for use in-circuit.

The list of backend native statements is slightly different from the list of front-end native statements: the former is optimized for in-circuit computation, the latter for usability by developers.  The middleware compiler takes care of the conversion from frontend to backend statements.

The following table summarises the natively-supported statements in the backend, where we write `value_of(ak)` for 'the value anchored key `ak` maps to', which is of type `PODValue`, and `key_of(ak)` for the key part of `ak`:

| Code | Identifier  | Args                | Meaning                                                           |
|------|-------------|---------------------|-------------------------------------------------------------------|
| 0    | `None`      |                     | no statement (useful for padding)                                 |
| 1    | `ValueOf`   | `ak`, `value`       | `value_of(ak) = value`                                            |
| 2    | `Eq`        | `ak1`, `ak2`        | `value_of(ak1) = value_of(ak2)`                                   |
| 3    | `NEq`       | `ak1`, `ak2`        | `value_of(ak1) != value_of(ak2)`                                  |
| 4    | `Gt`        | `ak1`, `ak2`        | `value_of(ak1) > value_of(ak2)`                                   |
| 5    | `LEq`       | `ak1`, `ak2`        | `value_of(ak1) <= value_of(ak2)`                                  |
| 6    | `Contains`  | `ak1`, `ak2`        | `(key_of(ak2), value_of(ak2)) ∈ value_of(ak1)` (Merkle inclusion) |
| 7    |`NotContains`| `ak1`, `ak2`        | `(key_of(ak2), value_of(ak2)) ∉ value_of(ak1)` (Merkle exclusion) |
| 8    | `SumOf`     | `ak1`, `ak2`, `ak3` | `value_of(ak1) = value_of(ak2) + value_of(ak3)`                   |
| 9    | `ProductOf` | `ak1`, `ak2`, `ak3` | `value_of(ak1) = value_of(ak2) * value_of(ak3)`                   |
| 10   | `MaxOf`     | `ak1`, `ak2`, `ak3` | `value_of(ak1) = max(value_of(ak2), value_of(ak3))`               |

### Middleware for statements

The middleware compiler is responsible for the following changes from frontend to backend statements.

- Pad with ```None``` to fill the length of the statement list
- Convert inequality statements ```Lt``` to ```Gt``` and ```GEq``` to ```LEq```
- To be added[^merk]: Convert Merkle statements ```Contains``` and ```NotContains``` to low-level statements.

[^content-id]: <font color="red">TODO</font> Refer to this when it is documented.

[^merk]: <font color="red">TODO</font> More native statements will be added for Merkle trees.