# Custom statements and custom operations

Users of the POD system can introduce _custom predicates_ (previously called _custom statements_) to express complex logical relations not available in the built-in predicates.  Every custom predicate is defined as the conjunction (AND) or disjunction (OR) of a small number of other statements.

When a custom predicate is introduced in a MainPod, it becomes available for use in that POD and all PODs that inherit[^inherit] from it.

On the frontend, a custom predicate is defined as a collection of conjunctions and disjunctions of statements.  The definition can be recursive: the definition of a predicate can involve the predicate itself, or the definitions of several predicates can depend on each other.  

At the backend level, every definition of a predicate is either a conjunction or a disjunction of statements.  To convert a frontend custom predicate to the backend, the middleware may need to introduce _sub-predicates_.

On the backend, custom predicates are defined in _groups_.  A group can contain one or more custom predicates and their associated sub-predicates.  Recursive definition is only possible within a group: the definition of a predicate in a group can only depend on previously existing predicates, itself, and other predicates in the same group.

## Custom predicates and their IDs

A custom predicate, like a built-in predicate, is identified by a _name_ on the front end and an _identifier_ on the back end.  The identifier is a cryptographic hash of the definition of the group.


[^inherit]: What to call this?  One POD "inherits" from another?

