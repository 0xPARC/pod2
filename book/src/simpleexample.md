# Simple example


## Circuit structure, two-column proof

A "proof" is a table that looks like
| STATEMENT | REASON |
| --- | --- |
| STATEMENT1 | REASON1 |
| STATEMENT2 | REASON2 |
...

In other words:

A "proof" is an ordered list of 100 proof-rows.

Each "row" is a pair (statement, reason).

The statement is the statement.

The reason is everything the circuit needs to verify that the statement is true.

Example:

```
STATEMENT1 = Equals(olddict["name"], otherdict["field"])

STATEMENT2 = Equals(otherdict["field"], newdict["result"])

STATEMENT3 = Equals(olddict["name"], newdict["result"])
```

The reasons in human-readable simplified format:

```
REASON1 -- "came from previous pod"

REASON2 -- "came from previous pod"

REASON3 -- "use transitive property on STATEMENT1 and STATEMENT2"
```

## What does the reason look like in circuit?

It won't be so simple.  I'll just explain what REASON3 has to look like.

First, the operation (deduction rule).

## A simple example of a deduction rule

Here is the transitive property of equality, in human-readable form.
```
if
Equals(a, b) and Equals(b, c)
then
Equals(a, c)
```

First, we need to decompose all the anchored keys as (dict, key) pairs.  This is the frontend description of the deduction rule.
```
IF
Equals(a_or[a_key], b_or[b_key])
AND
Equals(b_or[b_key], c_or[c_key])
THEN
Equals(a_or[a_key], c_or[c_key])
```

In-circuit, all these identifiers are replaced with wildcards, which come in numerical order (because they will be used as array indices).  So the backend representation is:
```
IF
Equals( ?1[?2], ?3[?4] ) and Equals ( ?3[?4], ?5[?6] )
THEN
Equals( ?1[?2], ?5[?6] )
```


## What does REASON3 need to look like in-circuit?

- Repeat deduction rule
 ```
IF
Equals( ?1[?2], ?3[?4] ) and Equals ( ?3[?4], ?5[?6] )
THEN
Equals( ?1[?2], ?5[?6] )
```
- Say what the wildcards are
```
?1 -- olddict
?2 -- "name"
?3 -- otherdict
...
```
- Substitute the wildcards into the deduction rule
```
IF
Equals( olddict["name"], ... ) ...
Equals( otherdict["value"])
THEN
Equals( olddict["name"] newdict[...] )
...
```
- Say where to find the previous statements (indices in the list), and check that they are above this one.
```
Statement1
Statement2
```
- Check that the input statements match.  Check that the output statement matches.



## Decomposing anchored keys

Sometimes a deduction rule requires different anchored keys to come from the same dictionary.  Here's an example from Ethdos.

The wildcard system handles this very naturally, since the dict of the anchored key can use its own wildcard.

```
eth_friend(src_or, src_key, dst_or, dst_key) = and<
    // the attestation dict is signed by (src_or, src_key)
    SignedBy(attestation_dict, src_or[src_key])

    // that same attestation pod has an "attestation"
    Equal(attestation_dict["attestation"], dst_or[dst_key])
>
```

In terms of anchored keys, it would be a little more complicated. five anchored keys show up in this deduction rule:
```
AK1 = src
AK2 = dst
AK3 = attestation_dict["attestation"]
```

and we need to force AK3, AK4, AK5 to come from the same origin.

WILDCARD matching takes care of it.

```
eth_friend(?1, ?2, ?3, ?4) = and<
    // the attestation dict is signed by (src_or, src_key)
    SignedBy(?5, ?1[?2])

    // that same attestation pod has an "attestation"
    Equal(?5["attestation"], ?3[?4])
>
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
IsComposite(n, private: a, b) = AND(
  ProductOf(n, a, b)
  GtFromEntries(a, 1)
  GtFromEntries(b, 1)
)
```

</div>
<div style="padding:10px;max-width:45%;">
    
We can view it as:

The *statement* `IsComposite(n)` is `true` if and only if $\exists$ `n`, `a`, `b`
 such that the following statements hold:
- $n = a \cdot b$
- $a > 1$
- $b > 1$

</div>
</div>
