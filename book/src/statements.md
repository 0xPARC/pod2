# Statements

A _statement_ is any sort of claim about values: for example, that two values are equal, or that one entry is contained in a dictionary.

Statements come in three types: _built-in_ (native), _custom_ and _introduction_.  There is a short list of built-in statements (see below).
In addition, users can freely define [custom statements](./custom.md), and [Introduction PODs](./introductionpods.md) can output their own introduction statements.

From the user (front-end) perspective, a statement represents a claim about some values -- the statement can only be proved if the claim is true.  On the front end, a statement is identified by its _name_ (`Equal`, `Contains`, etc.).

From the circuit (back-end) perspective, a statement can be proved either:
- by direct in-circuit verification, or
- by an operation (aka deduction rule).
On the back end, a statement is identified by the hash of its _predicate_.

## Built-in statements

The POD system has several builtin statements. These statements are associated to a reserved set of statement IDs.

### Backend statements

A statement is a code (or, in the frontend, string identifier) followed by 0 or more arguments, up to a maximum of 5.  Each argument is either a literal value or an [anchored key](./anchoredkeys.md).

The following table summarises the natively-supported statements, where we write `value_of(a)` for the value of the argument `a`: the literal value itself, or the value that the anchored key `a` maps to.

| Code | Identifier    | Args                | Meaning                                                           |
|------|---------------|---------------------|-------------------------------------------------------------------|
| 0    | `None`        |                     | no statement, always true (useful for padding)                    |
| 1    | `False`       |                     | always false (useful for padding disjunctions)                    |
| 2    | `Equal`       | `a1`, `a2`        | `value_of(a1) = value_of(a2)`                                   |
| 3    | `NotEqual`    | `a1`, `a2`        | `value_of(a1) != value_of(a2)`                                  |
| 4    | `LtEq`        | `a1`, `a2`        | `value_of(a1) <= value_of(a2)`                                  |
| 5    | `Lt`          | `a1`, `a2`        | `value_of(a1) < value_of(a2)`                                   |
| 6    | `Contains`    | `a1`, `a2`, `a3` | `(value_of(a2), value_of(a3)) ∈ value_of(a1)` (Merkle inclusion) |
| 7    | `NotContains` | `a1`, `a2`        | `(value_of(a2), _) ∉ value_of(a1)` (Merkle exclusion) |
| 8    | `Sum`       | `a1`, `a2`, `a3` | `value_of(a3) = value_of(a1) + value_of(a2)`                   |
| 9    | `Product`   | `a1`, `a2`, `a3` | `value_of(a3) = value_of(a1) * value_of(a2)`                   |
| 10   | `Max`       | `a1`, `a2`, `a3` | `value_of(a3) = max(value_of(a1), value_of(a2))`               |
| 11   | `Hash`      | `a1`, `a2`, `a3` | `value_of(a3) = hash(value_of(a1), value_of(a2))`              |
| 12   | `PublicKey` | `a1`, `a2`        | `value_of(a2) = derive_public_key(value_of(a1))`                |
| 13   | `SignedBy`    | `a1`, `a2`        | `value_of(a1)` is signed by  `value_of(a2)`                     |
| 14   | `ContainerInsert` | `a1`, `a2`, `a3`, `a4` | `(value_of(a2), _) ∉ value_of(a1) ∧ value_of(a4) = value_of(a1) ∪ {(value_of(a2), value_of(a3))}` (Merkle insert) |
| 15   | `ContainerUpdate` | `a1`, `a2`, `a3`, `a4` | `(value_of(a2), v) ∈ value_of(a1) ∧ value_of(a4) = (value_of(a1) - {(value_of(a2), v)}) ∪ {(value_of(a2), value_of(a3))}` (Merkle update) |
| 16   | `ContainerDelete` | `a1`, `a2`, `a3`        | `(value_of(a2), v) ∈ value_of(a1) ∧ value_of(a3) = value_of(a1) - {(value_of(a2), v)}` (Merkle delete) |

### Frontend statements

The frontend also exposes the following syntactic sugar predicates.  These predicates are not supported by the backend.  The frontend compiler is responsible for translating these predicates into the predicates above.

| Code | Identifier    | Args and desugaring                |
|------|---------------|---------------------|
| 1000 | DictContains | `DictContains(root, key, val) -> Contains(root, key, val)` |
| 1001 | DictNotContains | `DictNotContains(root, key) -> NotContains(root, key)` |
| 1002 | SetContains | `SetContains(root, val) -> Contains(root, val, val)` |
| 1003 | SetNotContains | `SetNotContains(root, val) -> NotContains(root, val)` |
| 1004 | ArrayContains | `ArrayContains(root, idx, val) -> Contains(root, idx, val)` |
| 1005 | GtEq | `GtEq(a, b) -> LtEq(b, a)`|
| 1006 | Gt | `Gt(a, b) -> Lt(b, a)` |
| 1009 | DictInsert | `DictInsert(old_root, key, val, new_root) -> ContainerInsert(old_root, key, val, new_root)` |
| 1010 | DictUpdate | `DictUpdate(old_root, key, val, new_root) -> ContainerUpdate(old_root, key, val, new_root)` |
| 1011 | DictDelete | `DictDelete(old_root, key, new_root) -> ContainerDelete(old_root, key, new_root)` |
| 1012 | SetInsert | `SetInsert(old_root, val, new_root) -> ContainerInsert(old_root, val, val, new_root)` |
| 1013 | SetDelete | `SetDelete(old_root, val, new_root) -> ContainerDelete(old_root, val, new_root)` |
| 1014 | ArrayUpdate | `ArrayUpdate(old_root, idx, val, new_root) -> ContainerUpdate(old_root, idx, val, new_root)` |


### Notes on the built-in statements

A ```Contains``` statement asserts that an entry has a certain value.
```
Contains(A, "name", "Arthur")
```
Implies that the entry `A["name"]` exists with the value `"Arthur"`.

An ```Equal``` statement asserts that two values are the same.  (Technical note: The circuit only proves equality of field elements; no type checking is performed.  For strings or Merkle roots, collision-resistance of the hash gives a cryptographic guarantee of equality.  However, note both Arrays and Sets are implemented as Merkle trees in the backend, like Dictionaries; the backend cannot type-check, so it is possible to prove an equality between an Array or Set and a Dictionary.)
```
Equal(A["name"], B["name"])
```

A ```NotEqual``` statement asserts that two values are different, for arbitrary types.

The comparison and arithmetic statements (```Lt```, ```LtEq```, ```Sum```, ```Product```, ```Max```) only hold for values of type ```Int```.  Each argument can be an anchored key or a literal.
```
Lt(100, A["price"])
Lt(A["price"], B["balance"])
Sum(A["price"], A["fee"], B["total"])
```

```Hash(a, b, c)``` asserts that ```c``` is the Poseidon hash of ```a``` and ```b```.

```PublicKey(sk, pk)``` asserts that ```pk``` is the public key corresponding to the secret key ```sk```, and ```SignedBy(msg, pk)``` asserts that ```msg``` is [signed](./signature.md) by ```pk```.
