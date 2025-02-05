# Statements

A _statement_ is any sort of claim about the values of entries: for example, that two values are equal, or that one entry is contained in another.

Statements come in two types: _built-in_ and _custom_.  There is a short list of built-in statements (see below). [^builtin]
In addition, users can freely define custom statements.

From the user (front-end) perspective, a statement represents a claim about the values of some number of entries -- the statement can only be proved if the claim is true.

From the circuit (back-end) perspective, a statement can be proved either:
- by direct in-circuit verification, or
- by an operation (aka deduction rule).

## Built-in statements

The POD system has several builtin statements. These statements are associated to a reserved set of statement IDs.

```
ValueOf(AnchoredKey, ScalarOrVec),
Equal(AnchoredKey, AnchoredKey),
NotEqual(AnchoredKey, AnchoredKey),
IsGreater(AnchoredKey, AnchoredKey),
IsLess(AnchoredKey, AnchoredKey),
IsGreaterOrEqual(AnchoredKey, AnchoredKey),
IsLessOrEqual(AnchoredKey, AnchoredKey),
SumOf(AnchoredKey, AnchoredKey, AnchoredKey),
ProductOf(AnchoredKey, AnchoredKey, AnchoredKey),
MaxOf(AnchoredKey, AnchoredKey, AnchoredKey),
Branches(AnchoredKey, AnchoredKey, AnchoredKey),
Leaf(AnchoredKey, AnchoredKey),
GoesLeft(AnchoredKey, AnchoredKey),
GoesRight(AnchoredKey, AnchoredKey),
Contains(AnchoredKey, AnchoredKey)
DoesNotContain(AnchoredKey, AnchoredKey)
```


In the future, we may also reserve statement IDs for "precompiles" such as:
```
poseidon_hash_of(A.hash, B.preimage) // perhaps a hash_of predicate can be parametrized by an enum representing the hash scheme; rather than having a bunch of specific things like SHA256_hash_of and poseidon_hash_of etc.
```

```
ecdsa_priv_to_pub_of(A.pubkey, B.privkey)
```

### Built-in statements for entries of any type

A ```ValueOf``` statement asserts that an entry has a certain value.
```
ValueOf(A.name, "Arthur") 
```

An ```IsEqual``` statement asserts that two entries have the same value.  (Technical note: The circuit only proves equality of field elements; no type checking is performed.  For strings or Merkle roots, collision-resistance of the hash gives a cryptographic guarantee of equality.)
```
IsEqual(A.name, B.name)
```

An ```IsUnequal``` statement asserts that two entries have different values.
```
IsUnequal   (for arbitary types)
```

##### Built-in Statements for Numerical Types
An ```IsGreater(x, y)``` statement asserts that ```x``` is an entry of type ```Integer```, ```y``` is an entry or constant of type ```Integer```, and ```x > y```.
```
is_greater    (for numerical types only)
is_greater(A.price, 100)
is_greater(A.price, B.balance)
```

The statements ```IsLess```, ```IsGreaterOrEqual```, ```IsLessOrEqual``` are defined analogously.

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

Every Merkle root either:
- is a special type of Merkle tree called a "leaf", which just has a single element, or
- has two branches, left and right -- each of which is itself a Merkle tree.  Such a tree is called a "non-leaf" Merkle tree.

There are six built-in statements involving Merkle roots:
```
Branches(node, left, right, depth)
```
means that ```node``` is a non-leaf Merkle node at depth ```depth```, and ```left``` and ```right``` are its branches.
```
Leaf(node, item)
```
means that ```node``` is a leaf Merkle node, whose single item is ```item```.

```
GoesLeft(node, item, depth)
```
means that ```node``` is a non-leaf Merkle node at depth ```depth```, and if ```item``` is contained under ```node```, it must be in the left branch.

```
GoesRight(node, item, depth)
```
means that ```tree``` is a non-leaf Merkle node at depth ```depth```, and if ```item``` is contained under ```node```, it must be in the right branch.


```
Contains(tree, item)
```
means that ```item``` is contained in the Merkle tree ```tree```.

```
DoesNotContain(tree, item)
```
means that ```item``` is not contained in the Merkle tree ```tree```.


[^builtin]: <font color="red">TODO</font> List of built-in statements is not yet complete.

[^fillsum]: <font color="red">TODO</font> Does sum mean x+y = z or x = y+z?