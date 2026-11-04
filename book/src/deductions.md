# Deductions

A POD proves a list of statements.  Each statement is deduced from previously
proved statements by an _operation_ (a deduction rule), so that a POD contains
a "two-column proof": a table where each row has a [statement](./statements.md)
and the [operation](./operations.md) that justifies it.

```
| STATEMENT                      | REASON                                    |
| ------------------------------ | ----------------------------------------- |
| Contains(d, "age", 25)         | ContainsFromEntries(None, None, None, mt_proof) |
| Lt(18, d["age"])               | LtFromEntries(None, row 1)                |
```

Statements can come from three sources:
- statements derived directly from values (e.g. `Contains` from a Merkle
  proof, or `SignedBy` from a signature);
- public statements of input PODs, imported with `OpenInputStatement`;
- statements derived from previous rows of the table, by native operations or
  by [custom operations](./custom.md).

Each statement is marked as public or private.  Only the public statements are
exposed by the resulting POD.
