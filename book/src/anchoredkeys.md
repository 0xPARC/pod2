# Anchored keys
Rather than dealing with just keys, we introduce the notion of an *anchored key*, which is a pair consisting of an dictionary specifier and a key, i.e.

```
type AnchoredKey = (Dict, Key)
type Key = String
```

Statements can use anchored keys or literal values as arguments.  Since our
system uses constructive logic, if a statement that uses an anchored key in
some of its arguments is proved, it means that a valid Merkle proof of the
value behind it exists and was used at some point to construct a `Contains`
statement that introduced that anchored key.

For example:
```
0: None
1: Contains(foo, bar, 42) <- ContainsFromEntries 0 0 0 mt_proof
2: Lt(foo[bar], 100) <- LtFromEntries 1 0
3: NotEqual(foo[bar], 100) <- LtToNotEqual 2
```
