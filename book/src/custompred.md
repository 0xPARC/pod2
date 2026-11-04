# Defining custom predicates

A custom operation is a rule that allows one to deduce a custom statement from one or more existing statements according to a logical rule, described below.  A custom operation is exactly the same thing as the definition of a custom predicate.

> Note: Unlike built-in operations, it is not possible to perform arbitrary calculations inside a custom operation.

The syntax of a custom operation is best explained with an example, written in [Podlang](./podlang.md):

```
good_boy(receiver, good_boy_issuers, private: signed_dict, signer) = AND(
    SignedBy(signed_dict, signer)
    SetContains(good_boy_issuers, signer)
    Equal(signed_dict["friend"], receiver)
)
```

A custom operation accepts as input a number of statements (the conditions);
each statement has a number of arguments, which may be constants, wildcards, or [anchored keys](./anchoredkeys.md) whose root is a wildcard.

In the example above, `signed_dict["friend"]` is an anchored key.  The purpose of using it, in this case, is to use an entry of a dictionary that has been signed.

In general, the "arguments" to an operation define a list of identifiers.  Every statement in the conditions must have valid arguments: either constants, or identifiers defined in the "arguments" (or anchored keys on them).  The arguments before `private:` are public and appear in the output statement; the private ones are only used in the conditions.

In order to apply the operation, the user who wants to create a POD must give acceptable values for all the arguments.  The POD prover will substitute those values for all the statements in the conditions and check that all substituted statements previously appear in the POD.  If this check passes, the output statement is then a valid statement.

## What applying the operation looks like on the back end

On the back end the deduction rule is converted to a sort of "template", where sugar predicates have been desugared and identifiers are replaced by numbered wildcards:

| Args | Condition            | Output                      |
|------------|-----------------------------------------|----|
| ?0 (receiver), <br> ?1 (good_boy_issuers), <br> ?2 (signed_dict), <br> ?3 (signer) | SignedBy(?2, ?3), <br> Contains(?1, ?3, ?3), <br> Equal(?2["friend"], ?0) | good_boy(?0, ?1) |

If you want to apply this deduction rule to prove a `good_boy` statement,
you have to provide the following witnesses in-circuit.

- Copy of the deduction rule
- Values for ?0, ?1, ?2, ?3.
- Indices of the three statements `SignedBy`, `Contains`, `Equal` in the list of previous statements.

And the circuit will verify:
- ?0, ?1, ?2, ?3 were correctly substituted into the statements
- The three statements `SignedBy`, `Contains`, `Equal` do indeed appear at the claimed indices.
