# Deductions

A POD proves a list of statements.  Each statement is deduced from previously
proved statements by an _operation_ (a deduction rule), so that a POD contains
a "two-column proof": a table where each row has a [statement](./statements.md)
and the [operation](./operations.md) that justifies it.  The operation (the
"reason") is everything the circuit needs to verify that the statement is true.

```
| STATEMENT                                    | REASON                                    |
| -------------------------------------------- | ----------------------------------------- |
| Equal(olddict["name"], otherdict["field"])   | OpenInputStatement (from an input POD)    |
| Equal(otherdict["field"], newdict["result"]) | OpenInputStatement (from an input POD)    |
| Equal(olddict["name"], newdict["result"])    | TransitiveEqualFromStatements(row 1, row 2) |
```

Statements can come from three sources:
- statements derived directly from values (e.g. `Contains` from a Merkle
  proof, or `SignedBy` from a signature);
- public statements of input PODs, imported with `OpenInputStatement`;
- statements derived from previous rows of the table, by native operations or
  by [custom operations](./custom.md).

Each statement is marked as public or private.  Only the public statements are
exposed by the resulting POD.

The table has a fixed maximum length, given by the circuit parameters (see
[MainPOD](./mainpod.md)).

## Predicates, statements and operations

When working with statements and operations, it might be useful to see them
from another perspective:

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
