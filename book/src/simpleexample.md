# Simple example

This page shows how the circuit verifies a deduction rule, using the last row
of the [two-column proof example](./deductions.md):
```
STATEMENT1 = Equal(olddict["name"], otherdict["field"])
STATEMENT2 = Equal(otherdict["field"], newdict["result"])
STATEMENT3 = Equal(olddict["name"], newdict["result"])  <- transitive property on STATEMENT1 and STATEMENT2
```

## A simple example of a deduction rule

Here is the transitive property of equality, in human-readable form.
```
if
Equal(a, b) and Equal(b, c)
then
Equal(a, c)
```

In-circuit, all these identifiers are replaced with wildcards, which come in numerical order (because they will be used as array indices).  So the backend representation is:
```
IF
Equal( ?0, ?1 ) and Equal( ?1, ?2 )
THEN
Equal( ?0, ?2 )
```

## What does the reason look like in-circuit?

Native operations such as `TransitiveEqualFromStatements` are implemented directly in the circuit, but [custom operations](./custom.md) are verified following exactly these steps.

- Repeat deduction rule
 ```
IF
Equal( ?0, ?1 ) and Equal( ?1, ?2 )
THEN
Equal( ?0, ?2 )
```
- Say what the wildcards are
```
?0 -- olddict["name"]
?1 -- otherdict["field"]
?2 -- newdict["result"]
```
- Substitute the wildcards into the deduction rule
```
IF
Equal( olddict["name"], otherdict["field"] ) and
Equal( otherdict["field"], newdict["result"] )
THEN
Equal( olddict["name"], newdict["result"] )
```
- Say where to find the previous statements (indices in the list), and check that they are above this one.
```
Statement1
Statement2
```
- Check that the input statements match (for an OR, at least one of them).  Check that the output statement matches.

## Anchored keys in deduction rules

Sometimes a deduction rule requires different anchored keys to come from the same dictionary.  Here's an example from the [GoodBoy predicate](./custompred.md).

The wildcard system handles this very naturally, since the dictionary of an anchored key is itself a wildcard.

```
good_boy(receiver, good_boy_issuers, private: signed_dict, signer) = AND(
    // the dict is signed by signer
    SignedBy(signed_dict, signer)
    SetContains(good_boy_issuers, signer)
    // that same dict has a "friend" entry equal to receiver
    Equal(signed_dict["friend"], receiver)
)
```

The dictionary `signed_dict` shows up twice: once as a value and once as the root of the anchored key `signed_dict["friend"]`.  Both uses must refer to the same dictionary.

WILDCARD matching takes care of it.

```
good_boy(?0, ?1, private: ?2, ?3) = AND(
    SignedBy(?2, ?3)
    Contains(?1, ?3, ?3)
    Equal(?2["friend"], ?0)
)
```
