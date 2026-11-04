# Defining custom predicates

A custom operation is a rule that allows one to deduce a custom statement from one or more existing statements according to a logical rule.  A custom operation is exactly the same thing as the definition of a custom predicate.

> Note: Unlike built-in operations, it is not possible to perform arbitrary calculations inside a custom operation.

The syntax of a custom operation is best explained with an example, written in [Podlang](./podlang.md):

```
good_boy(receiver, good_boy_issuers, private: signed_dict, signer) = AND(
    SignedBy(signed_dict, signer)
    SetContains(good_boy_issuers, signer)
    Equal(signed_dict["friend"], receiver)
)
```

In the example above, `signed_dict["friend"]` is an [anchored key](./anchoredkeys.md).  The purpose of using it, in this case, is to use an entry of a dictionary that has been signed.

In order to apply the operation, the user who wants to create a POD must give acceptable values for all the arguments.  If all the conditions, with these values substituted, previously appear in the POD, the output statement is a valid statement.

## What applying the operation looks like on the back end

On the back end the deduction rule is converted to a sort of "template", where sugar predicates have been desugared and identifiers are replaced by numbered wildcards:

| Args | Condition            | Output                      |
|------------|-----------------------------------------|----|
| ?0 (receiver), <br> ?1 (good_boy_issuers), <br> ?2 (signed_dict), <br> ?3 (signer) | SignedBy(?2, ?3), <br> Contains(?1, ?3, ?3), <br> Equal(?2["friend"], ?0) | good_boy(?0, ?1) |

To apply it in-circuit, the prover provides the template, the values for ?0, ?1, ?2, ?3 and the indices of the three condition statements, and the circuit verifies them as described in the [simple example](./simpleexample.md).
