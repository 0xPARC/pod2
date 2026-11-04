# Anchored keys
Rather than dealing with just keys, we introduce the notion of an *anchored key*, which is a pair consisting of a container (identified by its Merkle root) and a key, i.e.

```
type AnchoredKey = (Root, Key)
type Key = String | Int
```

String keys are used for dictionaries, and integer keys for arrays.

Statements can use anchored keys or literal values as arguments.  Since our
system uses constructive logic, if a statement that uses an anchored key in
some of its arguments is proved, it means that a valid Merkle proof of the
value behind it exists and was used at some point to construct a `Contains`
statement that introduced that anchored key.

In PODLang, anchored key indexing can use subscript syntax `foo["bar"]` which
allows any string key, or dot syntax `foo.bar` if the key is a valid identifier.

For example:
```
0: None
1: Contains(foo, "bar", 42) <- ContainsFromEntries 0 0 0 mt_proof
2: Lt(foo["bar"], 100) <- LtFromEntries 1 0
3: NotEqual(foo.bar, 100) <- LtToNotEqual 2
```

A statement with literal arguments can also be converted into one that uses
anchored keys with the `ReplaceValueWithEntry` [operation](./operations.md),
given the `Contains` statements that introduce those anchored keys.
