# Custom statements and custom operations

Users of the POD system can introduce _custom predicates_ (previously called _custom statements_) to express complex logical relations not available in the built-in predicates.  Every custom predicate is defined as the conjunction (AND) or disjunction (OR) of a small number of other statements.

When a custom predicate is introduced in a MainPod, it becomes available for use in that POD and all PODs that inherit[^inherit] from it.

On the frontend, a custom predicate is defined as a collection of conjunctions and disjunctions of statements.  The definition can be recursive: the definition of a predicate can involve the predicate itself, or the definitions of several predicates can depend on each other.  

At the backend level, every definition of a predicate is either a conjunction or a disjunction of statements.  To convert a frontend custom predicate to the backend, the middleware may need to introduce _sub-predicates_.

On the backend, custom predicates are defined in _groups_.  A group can contain one or more custom predicates and their associated sub-predicates.  Recursive definition is only possible within a group: the definition of a predicate in a group can only depend on previously existing predicates, itself, and other predicates in the same group.

## Arguments of custom predicates

The definition of a custom predicate might also be called an _operation_ or _deduction rule_.  It includes two (or, potentially, say, five) statement templates as conditions.  The arguments to the statement templates are decomposed as (origin, key) pairs: if statements are allowed to have arity at most 4, then the statement templates in a deduction rule will have at most 8 arguments (4 origins and 4 keys).  The same holds for the output statement.

Each argument (origin or key) to an statement template is either a wildcard or a literal.  In the backend, the wildcard arguments will be identified as ?1, ?2, ?3, ....

## Examples

See [examples](./customexample.md)

## Hashing and predicate IDs

Each custom predicate is defined as part of a _group_ of predicates. The definitions of all statements in the group are laid out consecutively (see [examples](./customexample.md)) and hashed.  For more details, see the pages on [hashing custom statements](./customhash.md) and [custom predicates](./custompred.md).

## How to prove an application of an operation

The POD proof format is inspired by "two-column proofs" (for an example, see [Wikipedia](https://en.wikipedia.org/wiki/Mathematical_proof)).  A POD contains a "tabular proof", in which each row includes a "statement" and an "operation".  The "operation" is the "reason" that justifies the statement: it is everything the circuit needs as a witness to verify the statement.

For a custom statement, the "reason" includes the following witnesses and verifications:
- the definition of the statement, serialized (see [examples](./customexample.md))
  - if the statement is part of a group, the definition of the full group, serialized
- verify that the hash of the definition is the statement ID
- the definition will have some number of "wildcards" (?1, ?2, ...) as arguments to statement templates; a value for each wildcard must be provided as a witness (each will be either an origin ID or key)
- the circuit must substitute the claimed values for the wildcards, and the resulting statements (true statements with origins and keys) will appear as witnesses
- the circuit must verify that all the input statement templates (with origins and keys) appear in the previous statements (in higher rows of the table)
- the circuit also substitutes the claimed values for the wildcards in the output statement, and verifies that it matches the claimed output statement



[^inherit]: What to call this?  One POD "inherits" from another?

