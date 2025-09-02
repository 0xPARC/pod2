# Statements

A _statement_ is any sort of claim about the values of entries: for example, that two values are equal, or that one entry is contained in another.

Statements come in two types: _built-in_ and _custom_.  There is a short list of built-in statements (see below). [^builtin]
In addition, users can freely define custom statements.

From the user (front-end) perspective, a statement represents a claim about the values of some number of entries -- the statement can only be proved if the claim is true.  On the front end, a statement is identified by its _name_ (`ValueOf`, `Equal`, etc.).

From the circuit (back-end) perspective, a statement can be proved either:
- by direct in-circuit verification, or
- by an operation (aka deduction rule).
On the back end, a statement is identified by a unique numerical _identifier_.

## Built-in statements

The POD system has several builtin statements. These statements are associated to a reserved set of statement IDs.

### Backend statements

A statement is a code (or, in the frontend, string identifier) followed by 0 or more arguments. These arguments may consist of up to three anchored keys and up to one POD value.

The following table summarises the natively-supported statements, where we write `value_of(ak)` for 'the value anchored key `ak` maps to', which is of type `PODValue`, and `key_of(ak)` for the key part of `ak`:

| Code | Identifier    | Args                | Meaning                                                           |
|------|---------------|---------------------|-------------------------------------------------------------------|
| 0    | `None`        |                     | no statement, always true (useful for padding)                    |
| 1    | `False`       |                     | always false (useful for padding disjunctions)                    |
| 2    | `Equal`       | `ak1`, `ak2`        | `value_of(ak1) = value_of(ak2)`                                   |
| 3    | `NotEqual`    | `ak1`, `ak2`        | `value_of(ak1) != value_of(ak2)`                                  |
| 4    | `LtEq`        | `ak1`, `ak2`        | `value_of(ak1) <= value_of(ak2)`                                  |
| 5    | `Lt`          | `ak1`, `ak2`        | `value_of(ak1) < value_of(ak2)`                                   |
| 6    | `Contains`    | `ak1`, `ak2`, `ak3` | `(value_of(ak2), value_of(ak3)) ∈ value_of(ak1)` (Merkle inclusion) |
| 7    | `NotContains` | `ak1`, `ak2`        | `(value_of(ak2), _) ∉ value_of(ak1)` (Merkle exclusion) |
| 8    | `SumOf`       | `ak1`, `ak2`, `ak3` | `value_of(ak1) = value_of(ak2) + value_of(ak3)`                   |
| 9    | `ProductOf`   | `ak1`, `ak2`, `ak3` | `value_of(ak1) = value_of(ak2) * value_of(ak3)`                   |
| 10   | `MaxOf`       | `ak1`, `ak2`, `ak3` | `value_of(ak1) = max(value_of(ak2), value_of(ak3))`               |
| 11   | `HashOf`      | `ak1`, `ak2`, `ak3` | `value_of(ak1) = hash(value_of(ak2), value_of(ak3))`              |
| 12   | `PublicKeyOf` | `ak1`, `ak2`        | `value_of(ak1) = derive_public_key(value_of(ak2))`                |
| 13   | `SignedBy`    | `ak1`, `ak2`        | `value_of(ak1)` is signed by  `value_of(ak2)`                     |
| 14   | `ContainerInsert` | `ak1`, `ak2`, `ak3`, `ak4` | `(value_of(ak3), _) ∉ value_of(ak2) ∧ value_of(ak1) = value_of(ak2) ∪ {(value_of(ak3), value_of(ak4))}` (Merkle insert) |
| 15   | `ContainerUpdate` | `ak1`, `ak2`, `ak3`, `ak4` | `(value_of(ak3), v) ∈ value_of(ak2) ∧ value_of(ak1) = (value_of(ak2) - {(value_of(ak3), v)}) ∪ {(value_of(ak3), value_of(ak4))}` (Merkle update) |
| 16   | `ContainerDelete` | `ak1`, `ak2`, `ak3`        | `(value_of(ak3), v) ∈ value_of(ak2) ∧ value_of(ak1) = value_of(ak2) - {(value_of(ak3), v)}` (Merkle delete) |

### Frontend statements

The frontend also exposes the following syntactic sugar predicates.  These predicates are not supported by the backend.  The frontend compiler is responsible for translating these predicates into the predicates above.

| Code | Identifier    | Args and desugaring                | 
|------|---------------|---------------------|
| 1000 | DictContains | `DictContains(root, key, val) -> Contains(root, key, val)` |
| 1001 | DictNotContains | `DictNotContains(root, key, val) -> NotContains(root, key, val)` |
| 1002 | SetContains | `SetContains(root, val) -> Contains(root, val, val)` |
| 1003 | SetNotContains | `SetNotContains(root, val) -> Contains(root, val, val)` |
| 1004 | ArrayContains | `ArrayContains(root, idx, val) -> Contains(root, idx, val)` |
| 1005 | GtEq | `GtEq(a, b) -> LtEq(b, a)`|
| 1006 | Gt | `Gt(a, b) -> Lt(b, a)` |
| 1009 | DictInsert | `DictInsert(new_root, old_root, key, val) -> ContainerInsert(new_root, old_root, key, val)` |
| 1010 | DictUpdate | `DictUpdate(new_root, old_root, key, val) -> ContainerUpdate(new_root, old_root, key, val)` |
| 1011 | DictDelete | `DictDelete(new_root, old_root, key) -> ContainerDelete(new_root, old_root, key)` |
| 1012 | SetInsert | `SetInsert(new_root, old_root, val) -> ContainerInsert(new_root, old_root, val, val)` |
| 1013 | SetDelete | `SetDelete(new_root, old_root, val) -> ContainerDelete(new_root, old_root, val)` |
| 1014 | ArrayUpdate | `ArrayUpdate(new_root, old_root, idx, val) -> ContainerUpdate(new_root, old_root, idx, val)` |


### Built-in statements for entries of any type

A ```DictContains``` statement asserts that an entry has a certain value.
```
DictContains(A, "name", "Arthur")
```
Implies that the entry `A["name"]` exists with the value `"Arthur"`.

An ```Equal``` statement asserts that two entries have the same value.  (Technical note: The circuit only proves equality of field elements; no type checking is performed.  For strings or Merkle roots, collision-resistance of the hash gives a cryptographic guarantee of equality.  However, note both Arrays and Sets are implemented as dictionaries in the backend; the backend cannot type-check, so it is possible to prove an equality between an Array or Set and a Dictionary.)
```
Equal(A["name"], B["name"])
```

An ```NotEqual``` statement asserts that two entries have different values.
```
NotEqual   (for arbitrary types)
```

##### Built-in Statements for Numerical Types
An ```Gt(x, y)``` statement asserts that ```x``` is an entry of type ```Integer```, ```y``` is an entry or constant of type ```Integer```, and ```x > y```.
```
Gt    (for numerical types only)
Gt(A["price"], 100)
Gt(A["price"], B["balance"])
```

The statements ```Lt```, ```GEq```, ```Leq``` are defined analogously.

```SumOf(x, y, z)``` asserts that ```x```, ```y```, ```z``` are entries of type ```Integer```, and ```x = y + z```

```ProductOf``` and ```MaxOf``` are defined analogously.

The two items below may be added in the future:
```
poseidon_hash_of(A["hash"], B["preimage"]) // perhaps a hash_of predicate can be parametrized by an enum representing the hash scheme; rather than having a bunch of specific things like SHA256_hash_of and poseidon_hash_of etc.
```

```
ecdsa_priv_to_pub_of(A["pubkey"], B["privkey"])
```



[^builtin]: <font color="red">TODO</font> List of built-in statements is not yet complete.
