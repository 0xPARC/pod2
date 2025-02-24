# Custom operations (or: how to define a custom predicate): VERSION 1

(Note: At the moment, we consider a "custom operation" to be exactly the same thing as the "definition of a custom predicate.")

A custom operation [^operation] is a rule that allows one to deduce a custom statement from one or more existing statements according to a logical rule, described below.

> Note: Unlike built-in operations, it is not possible to perform arbitrary calculations inside a custom operation.

The syntax of a custom operation is best explained with an example.

Original example with anchored keys, origins, and keys.
| Args | Condition            | Output                      |
|------------|-----------------------------------------|----|
| pod: Origin, <br> good_boy_issuers: AnchoredKey::MerkleRoot, <br> receiver: AnchoredKey | ValueOf(AK(pod, "_type"), SIGNATURE), <br> Contains(good_boy_issuers, AK(pod,"_signer")), <br> Equals(AK(pod, "friend"), receiver) | GoodBoy(receiver, good_boy_issuers) |

Compiled example with only origins and keys.
| Args | Condition            | Output                      |
|------------|-----------------------------------------|----|
| pod: Origin, <br> good_boy_issuers_origin: Origin, <br> good_boy_issuers_key: Key::MerkleRoot, <br> receiver_origin: Origin, <br> receiver_key: Key | ValueOf(AK(pod, "_type"), SIGNATURE), <br> Contains(AK(good_boy_issuers_origin, good_boy_issuers_key), AK(pod,"_signer")), <br> Equals(AK(pod, "friend"), AK(receiver_origin, receiver_key)) | GoodBoy(AK(receiver_origin, receiver_key), AK(good_boy_issuers_origin, good_boy_issuers_key)) |

A custom operation accepts as input a number of statements (the `Condition`); 
each statement has a number of arguments, which may be constants or anchored keys; and an [anchored key](./anchoredkeys.md) in turn can optionally be decomposed as a pair of an Origin and a Key.

In the "original example" above, the anchored keys `good_boy_issuers` and `receiver` are not broken down, but `AK(pod, "_type"), AK(pod, "_signer"), AK(pod, "friend")` are.  The purpose of breaking them down, in this case, is to force the three anchored keys to come from the same pod.

In the "compiled example", all the anchored keys have been broken down into origins and keys.

In general, in the front-end language, the "arguments" to an operation define a list of identifiers with types.  Every statement in the "condition" must have valid arguments of the correct types: either constants, or identifiers defined in the "arguments".

In order to apply the operation, the user who wants to create a POD must give acceptable values for all the arguments.  The POD prover will substitute those values for all the statements in the "Condition" and check that all substituted statements previously appear in the POD.  If this check passes, the output statement is then a valid statement.

## What applying the operation looks like on the back end

On the back end the "compiled example" deduction rule is converted to a sort of "template":

| Args | Condition            | Output                      |
|------------|-----------------------------------------|----|
| *1 (pod), <br> *2 (good_boy_issuers_origin), <br> *3 (good_boy_issuers_key), <br> *4 (receiver_origin), <br> *5 (receiver_key) | ValueOf(AK(*1, "_type"), SIGNATURE), <br> Contains(AK(*2, *3), AK(*1,"_signer")), <br> Equals(AK(*1, "friend"), AK(*4, *5)) | GoodBoy(AK(*4, *5), AK(*2, *3)) |

If you want to apply this deduction rule to prove a `GoodBoy` statement,
you have to provide the following witnesses in-circuit.

- Copy of the deduction rule
- Values for *1, *2, *3, *4, *5.
- Copy of the three statements in the deduction rule with *1, *2, *3, *4, *5 filled in
- Indices of the three statements `ValueOf`, `Contains`, `Equals` in the list of previous statements.

And the circuit will verify:
- *1, *2, *3, *4, *5 were correctly substituted into the statements
- The three statements `ValueOf`, `Contains`, `Equals` do indeed appear at the claimed indices.

[^operation]: In previous versions of these docs, "operations" were called "deduction rules".
