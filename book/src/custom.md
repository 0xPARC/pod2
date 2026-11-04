# Custom statements and custom operations

Users of the POD system can introduce _custom predicates_ to express complex logical relations not available in the built-in predicates.  Every custom predicate is defined as the conjunction (AND) or disjunction (OR) of a small number of other statements.

On the frontend, a custom predicate is defined in [Podlang](./podlang.md) as a conjunction or disjunction of statements.  The definition can be recursive: the definition of a predicate can involve the predicate itself, or the definitions of several predicates can depend on each other.

At the backend level, every definition of a predicate is either a conjunction or a disjunction of at most 5 statements.  To convert a larger frontend custom predicate to the backend, the frontend automatically splits it into a chain of _sub-predicates_.

On the backend, custom predicates are defined in _batches_ (called _modules_ in Podlang).  A batch can contain one or more custom predicates and their associated sub-predicates.  Recursive definition is only possible within a batch: the definition of a predicate in a batch can only depend on previously existing predicates, itself, and other predicates in the same batch.

A custom predicate is identified by the batch ID and its index in the batch, so it can be used in any MainPOD: the definition of the batch is provided to the circuit as a witness, and the circuit checks that it hashes to the batch ID.

## Arguments of custom predicates

The definition of a custom predicate might also be called an _operation_ or _deduction rule_.  It includes up to 5 statement templates as conditions.  The arguments of the predicate are _wildcards_, which are either public (they appear as arguments of the output statement, up to 5) or private (they only appear in the statement templates).  In the backend, the wildcards are identified by their index: ?0, ?1, ?2, ....

Each argument to a statement template is one of:
- a literal value;
- a wildcard `?i`, which is bound to a value;
- an anchored key `?i["key"]`, where the root is a wildcard and the key is a literal.

The predicate of a statement template can also be a wildcard, which allows a custom predicate to take another predicate as an argument.

## Examples

See [examples](./customexample.md)

## Hashing and predicate IDs

Each custom predicate is defined as part of a _batch_ of predicates. The definitions of all predicates in the batch are merklelized (using sequential indices as keys) (see [examples](./customexample.md)) and the root of the merkle tree is used as the identifier.  For more details, see the pages on [hashing custom statements](./customhash.md) and [custom predicates](./custompred.md).

## How to prove an application of an operation

The POD proof format is inspired by "two-column proofs" (for an example, see [Wikipedia](https://en.wikipedia.org/wiki/Mathematical_proof)).  A POD contains a "tabular proof", in which each row includes a "statement" and an "operation".  The "operation" is the "reason" that justifies the statement: it is everything the circuit needs as a witness to verify the statement.

For a custom statement, the "reason" includes the following witnesses and verifications:
- the definition of the predicate, serialized (see [examples](./customexample.md)), together with the definition of the full batch it belongs to
- verify that the hash of the batch definition is the batch ID
- the definition will have some number of "wildcards" (?0, ?1, ...) as arguments to statement templates; a value for each wildcard must be provided as a witness
- the circuit must substitute the claimed values for the wildcards, and the resulting statements will appear as witnesses
- the circuit must verify that all the input statement templates (for an OR, at least one of them) appear in the previous statements (in higher rows of the table)
- the circuit also substitutes the claimed values for the public wildcards in the output statement, and verifies that it matches the claimed output statement
