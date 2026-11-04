# Custom statements and custom operations

Users of the POD system can introduce _custom predicates_ to express complex logical relations not available in the built-in predicates.  Every custom predicate is defined as the conjunction (AND) or disjunction (OR) of a small number of other statements.

On the frontend, a custom predicate is defined in [Podlang](./podlang.md) as a conjunction or disjunction of statements.  The definition can be recursive: the definition of a predicate can involve the predicate itself, or the definitions of several predicates can depend on each other.

At the backend level, every definition of a predicate is either a conjunction or a disjunction of at most 5 statements.  To convert a larger frontend custom predicate to the backend, the frontend automatically splits it into a chain of _sub-predicates_.

On the backend, custom predicates are defined in _batches_ (called _modules_ in Podlang).  A batch can contain one or more custom predicates and their associated sub-predicates.  Recursive definition is only possible within a batch: the definition of a predicate in a batch can only depend on previously existing predicates, itself, and other predicates in the same batch.

A custom predicate is identified by the _batch ID_ (the root of a Merkle tree of the hashes of the predicate definitions in the batch) and its index in the batch, so it can be used in any MainPOD.  See [how to hash a custom predicate](./customhash.md).

## Arguments of custom predicates

The definition of a custom predicate might also be called an _operation_ or _deduction rule_.  It includes up to 5 statement templates as conditions.  The arguments of the predicate are _wildcards_, which are either public (they appear as arguments of the output statement, up to 5) or private (they only appear in the statement templates).  In the backend, the wildcards are identified by their index: ?0, ?1, ?2, ....

Each argument to a statement template is one of:
- a literal value;
- a wildcard `?i`, which is bound to a value;
- an anchored key `?i["key"]`, where the root is a wildcard and the key is a literal.

The predicate of a statement template can also be a wildcard, which allows a custom predicate to take another predicate as an argument.

## How to prove an application of an operation

A custom statement is proved by a custom operation, which the circuit verifies
following the steps described in the [simple example](./simpleexample.md): the
prover provides the predicate definition and a value for each wildcard, and the
circuit substitutes the values into the statement templates and checks that the
resulting statements appear in previous rows of the table.  In addition, the
prover provides the definition of the full batch, and the circuit verifies that
it hashes to the batch ID.
