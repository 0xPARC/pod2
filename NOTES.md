# Explain Statement

A predicate with arguments.
A claim about a relation between data.
Can be true or false.

```
Lt(4, 5)
SumOf(10, 4, 6)

Lt(x.a, 5)
SumOf(x.b, x.a, 1)
```

## Ref

Statement: src/middleware/statement.rs:272
NativePredicate: src/middleware/statement.rs:19

# Explain Operation

Take statements or values as inputs and produce a statement.
If the input statements are true, the output statement is true.

## FromEntries

```
Lt(4, 5) <- LtFromEntries(4, 5)
SumOf(10, 4, 6) <- SumOfFromEntries(10, 4, 6)
```

### Special case for dictionary entries

```
Contains(x, "a", 2) <- ContainsFromEntries(x, "a", 2)
Lt(x.a, 5) <- LtFromEntries(Contains(x, "a", 2), 5)
Contains(x, "b", 3) <- ContainsFromEntries(x, "b", 3)
SumOf(x.b, x.a, 1) <- SumOfFromEntries((Contains(x, "b", 3), Contains(x, "a", 2), 1)
```

## From statements
```
NotEqual(x.a, 5) <- LtToNotEqual Lt(x.a, 5)
```

## Ref

Operation: src/middleware/operation.rs:178
NativeOperation: src/middleware/operation.rs:74

# Custom Predicate

Predicates that combine conjunctions and disjunctions of statements with
pattern matching arguments.
User defined and supported by our standard MainPod circuit.

Predicate:
```
ValidDict(d, private: secret) = AND(
	HashOf(d.secret, "", secret)
	Equal(d.foo, "bar")
) 
```

Statement and Operation:
```
HashOf(d.secret, "", "abcd") <- HashOfFromEntries(Contains(d, "secret", 0x123), "", "abcd")
Equal(d.foo, "bar") <- EqualFromEntries(Contains(d, "foo", "bar"), "bar")
ValidDict(d) <- Custom[ValidDict](HashOf(d.secret, "", "abcd"), Equal(d.foo, "bar"))
```

Naming:
- Wildcard: Arguments in a custom predicate definition
	- `d`
	- `secret`
- Statement Template: Statements with patterns to match in a custom predicate definition
	- `HashOf(d.secret, "", secret)`
	- `Equal(d.foo, "bar")`

## Ref

CustomPredicate: src/middleware/custom.rs:186

# Introduction pods

Define your own predicate logic with a custom circuit.
A consumer needs to understand (and trust) what the custom circuit does.

# POD

A Pod proves that all the statements it generates are true (by verifying the
operations that generate them).
A Pod can take input statements from a recursively verified Pod.

Not all statements need to be public (pod output)
Not all data needs to be public (see private wildcards in custom predicates)

In general:
- Define relations between data (usually stored in dictionaries)
- Choose which relations and which data to reveal
