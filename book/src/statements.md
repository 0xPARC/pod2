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
| 0    | `None`        |                     | no statement (useful for padding)                                 |
| 1    | `ValueOf`     | `ak`, `value`       | `value_of(ak) = value`                                            |
| 2    | `Eq`          | `ak1`, `ak2`        | `value_of(ak1) = value_of(ak2)`                                   |
| 3    | `NEq`         | `ak1`, `ak2`        | `value_of(ak1) != value_of(ak2)`                                  |
| 4    | `Gt`          | `ak1`, `ak2`        | `value_of(ak1) > value_of(ak2)`                                   |
| 5    | `LEq`         | `ak1`, `ak2`        | `value_of(ak1) <= value_of(ak2)`                                  |
| 6    | `Contains`    | `ak1`, `ak2`        | `(key_of(ak2), value_of(ak2)) ∈ value_of(ak1)` (Merkle inclusion) |
| 7    | `NotContains` | `ak1`, `ak2`        | `(key_of(ak2), value_of(ak2)) ∉ value_of(ak1)` (Merkle exclusion) |
| 8    | `SumOf`       | `ak1`, `ak2`, `ak3` | `value_of(ak1) = value_of(ak2) + value_of(ak3)`                   |
| 9    | `ProductOf`   | `ak1`, `ak2`, `ak3` | `value_of(ak1) = value_of(ak2) * value_of(ak3)`                   |
| 10   | `MaxOf`       | `ak1`, `ak2`, `ak3` | `value_of(ak1) = max(value_of(ak2), value_of(ak3))`               |

### Frontend statements

<span style="color:red">TODO: Current implementation frontend Statements reuse the middleware Statements, which:</span><br>
<span style="color:red">- 1: GEq & LEq don't appear in the frontend impl</span><br>
<span style="color:red">- 2: frontend impl has Contains & NotContains, which don't appear at the following block</span>
```
ValueOf(key: AnchoredKey, value: ScalarOrVec)

Equal(ak1: AnchoredKey, ak2: AnchoredKey)

NotEqual(ak1: AnchoredKey, ak2: AnchoredKey)

Gt(ak1: AnchoredKey::Integer, ak2: AnchoredKey::Integer)

Lt(ak1: AnchoredKey::Integer, ak2: AnchoredKey::Integer)

GEq(ak1: AnchoredKey::Integer, ak2: AnchoredKey::Integer)

LEq(ak1: AnchoredKey::Integer, ak2: AnchoredKey::Integer)

SumOf(sum: AnchoredKey::Integer, arg1: AnchoredKey::Integer, arg2: 
AnchoredKey::Integer)

ProductOf(prod: AnchoredKey::Integer, arg1: AnchoredKey::Integer, arg2: AnchoredKey::Integer)

MaxOf(max: AnchoredKey::Integer, arg1: AnchoredKey::Integer, arg2: AnchoredKey::Integer)
```

The following statements relate to Merkle trees and compound types; they are explained in detail on a [separate page](./merklestatements.md).
```
Branches(parent: AnchoredKey::MerkleTree, left: AnchoredKey::MerkleTree, right: AnchoredKey::MerkleTree)

Leaf(node: AnchoredKey::MerkleTree, key: AnchoredKey, value: AnchoredKey)

IsNullTree(node: AnchoredKey::MerkleTree)

GoesLeft(key: AnchoredKey, depth: Value::Integer)

GoesRight(key: AnchoredKey, depth: Value::Integer)

Contains(root: AnchoredKey::MerkleTree, key: AnchoredKey, value: AnchoredKey)

MerkleSubtree(root: AnchoredKey::MerkleTree, node: AnchoredKey::MerkleTree)

MerkleCorrectPath(root: AnchoredKey::MerkleTree, node: AnchoredKey::MerkleTree, key: AnchoredKey, depth: Value::Integer)

Contains(root: AnchoredKey::MerkleTree, key: AnchoredKey, value: AnchoredKey)

NotContains(root: AnchoredKey::MerkleTree, key: AnchoredKey)

ContainsHashedKey(root: AnchoredKey::DictOrSet, key: AnchoredKey)

NotContainsHashedKey(root: AnchoredKey::DictOrSet, key: AnchoredKey)

ContainsValue(root: AnchoredKey::Array, value: AnchoredKey)
```


In the future, we may also reserve statement IDs for "precompiles" such as:
```
PoseidonHashOf(A.hash, B.preimage) // perhaps a hash_of predicate can be parametrized by an enum representing the hash scheme; rather than having a bunch of specific things like SHA256_hash_of and poseidon_hash_of etc.
```

```
EcdsaPrivToPubOf(A.pubkey, B.privkey)
```

### Built-in statements for entries of any type

A ```ValueOf``` statement asserts that an entry has a certain value.
```
ValueOf(A.name, "Arthur") 
```

An ```Equal``` statement asserts that two entries have the same value.  (Technical note: The circuit only proves equality of field elements; no type checking is performed.  For strings or Merkle roots, collision-resistance of the hash gives a cryptographic guarantee of equality.  However, note both Arrays and Sets are implemented as dictionaries in the backend; the backend cannot type-check, so it is possible to prove an equality between an Array or Set and a Dictionary.)
```
Equal(A.name, B.name)
```

An ```NotEqual``` statement asserts that two entries have different values.
```
NotEqual   (for arbitrary types)
```

##### Built-in Statements for Numerical Types
An ```Gt(x, y)``` statement asserts that ```x``` is an entry of type ```Integer```, ```y``` is an entry or constant of type ```Integer```, and ```x > y```.
```
Gt    (for numerical types only)
Gt(A.price, 100)
Gt(A.price, B.balance)
```

The statements ```Lt```, ```GEq```, ```Leq``` are defined analogously.

```SumOf(x, y, z)``` asserts that ```x```, ```y```, ```z``` are entries of type ```Integer```, and [^fillsum]

```ProductOf``` and ```MaxOf``` are defined analogously.

The two items below may be added in the future:
```
poseidon_hash_of(A.hash, B.preimage) // perhaps a hash_of predicate can be parametrized by an enum representing the hash scheme; rather than having a bunch of specific things like SHA256_hash_of and poseidon_hash_of etc.
```

```
ecdsa_priv_to_pub_of(A.pubkey, B.privkey)
```

##### Primitive Built-in Statements for Merkle Roots

[See separate page](./merklestatements.md).



[^builtin]: <font color="red">TODO</font> List of built-in statements is not yet complete.

[^fillsum]: <font color="red">TODO</font> Does sum mean x+y = z or x = y+z?
