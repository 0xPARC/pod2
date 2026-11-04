# Simple example


## Circuit structure, two-column proof

A "proof" is a table that looks like
| STATEMENT | REASON |
| --- | --- |
| STATEMENT1 | REASON1 |
| STATEMENT2 | REASON2 |
...

In other words:

A "proof" is an ordered list of proof-rows, with a fixed maximum length given by the circuit parameters.

Each "row" is a pair (statement, reason).

The statement is the statement.

The reason is everything the circuit needs to verify that the statement is true.

Example:

```
STATEMENT1 = Equal(olddict["name"], otherdict["field"])

STATEMENT2 = Equal(otherdict["field"], newdict["result"])

STATEMENT3 = Equal(olddict["name"], newdict["result"])
```

The reasons in human-readable simplified format:

```
REASON1 -- "came from previous pod"

REASON2 -- "came from previous pod"

REASON3 -- "use transitive property on STATEMENT1 and STATEMENT2"
```

## What does the reason look like in circuit?

Let's look at what REASON3 has to look like.

First, the operation (deduction rule).

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

Native operations such as `TransitiveEqualFromStatements` are implemented directly in the circuit, but [custom operations](./custom.md) are verified following exactly these steps.

## What does REASON3 need to look like in-circuit?

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
- Check that the input statements match.  Check that the output statement matches.



## Anchored keys in deduction rules

Sometimes a deduction rule requires different anchored keys to come from the same dictionary.  Here's an example from Ethdos.

The wildcard system handles this very naturally, since the dictionary of an anchored key is itself a wildcard.

```
eth_friend(src, dst, private: attestation) = AND(
    // the attestation dict is signed by src
    SignedBy(attestation, src)

    // that same attestation dict has an "attestation" entry equal to dst
    Equal(attestation["attestation"], dst)
)
```

The dictionary `attestation` shows up twice: once as a value and once as the root of the anchored key `attestation["attestation"]`.  Both uses must refer to the same dictionary.

WILDCARD matching takes care of it.

```
eth_friend(?0, ?1, private: ?2) = AND(
    SignedBy(?2, ?0)
    Equal(?2["attestation"], ?1)
)
```

## Another perspective
When working with statements and operations, it might be useful to see them from another perspective:

- A *predicate* is a relation formula, which when filled with values becomes a
  *statement*.
- A *statement* can be seen as the *constraints* of a traditional zk-circuit,
  which can be true or false.
- An *operation* comprises the deduction rules, which are rules used to deduce
  new statements from previous statements or used to construct new statements
  from values.

$$
predicate \cong circuit/relation~to~be~fulfilled\\
statement \cong constraints~filled~with~the~witness\\
operations \cong deduction~rules
$$


For example,
- `Equal` for integers is a *predicate*
- `st_1 = Equal(A, B)` is a *statement*
- `st_2 = Equal(B, C)` is a *statement*
- `st_3 = TransitiveEqualFromStatements(st_1, st_2)` is an *operation*, which yields the statement `st_3 = Equal(A, C)`




<div style="display:flex;">
<div style="padding:10px;max-width:50%; border-right:1px solid #ccc;">

So, for example, for the given predicate:

```
is_composite(n, private: a, b) = AND(
  Product(a, b, n)
  Gt(a, 1)
  Gt(b, 1)
)
```

</div>
<div style="padding:10px;max-width:45%;">

We can view it as:

The *statement* `is_composite(n)` is `true` if and only if $\exists$ `a`, `b`
 such that the following statements hold:
- $n = a \cdot b$
- $a > 1$
- $b > 1$

</div>
</div>
