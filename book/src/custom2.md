# Custom operations (or: how to define a custom predicate): VERSION 2

# DO NOT USE THIS DOC
# SAVING IN THE GITHUB JUST SO WE HAVE A COPY
# WE ARE NOT USING THIS SPEC
# DO NOT USE

## The local variable requirement

This spec differs from the main spec in that there are no anchored keys.  However, there are still types `Origin` and `Key`.

An `Origin` refers to an input POD; in-circuit, the `Origin` is the pod ID of the pod.

A `Key` refers to a value within a POD.

With the exception of the special statement `ValueFromPodKey`, a key always refers to a value within the POD _self.  In other words, a statement (except for `ValueFromPodKey`) cannot refer to a value from a previous POD, only to a value in the "namespace" of the current POD.

Roughly speaking, the statement
```
ValueFromPodKey(local_key, origin_id, key)
```
means that the value of `local_key` on the current POD (_self) is the same as the value of `key` on the POD `origin_id` -- in other words, it is basically the same as 
```
Equals(AnchoredKey(_SELF, local_key), AnchoredKey(origin_id, key)).
```

I say "basically the same" because, in this spec, it is possible to refer to both keys and origin IDs by reference.

## Referencing

Recall that in the front-end, a `Key` is a string that functions as an identifier (like a variable name in other languages), and a `Value` is the value of that variable -- an `Integer`, `String`, or compound value.

In the back-end, a `Key` is four field elements (computed as a hash of the front-end key); and a `Value` is again four field elements.  Again, each `Key` has a unique `Value`.

A `Reference` statement allows a key to be reinterpreted as a value; it is analogous to a pointer in C.

The statement
```
Reference(reference_key, key)
```
means that `reference_key` is a key, whose associated value is the same as the key `key`.

## ValueFromPodKey, precisely this time

```
ValueFromPodKey(local_key: KeyOrLiteral::String, origin_id: KeyOrLiteral::OriginID, key: KeyOrLiteral::String).
```

means that the _values_ of `local_key` and `key` are _keys_, the _value_ of `origin_id` is an _origin ID_, and the value assigned to the key `local_key` on the present POD is the same as the value assigned to the key `key` on the pod `origin_ID`.

An example with literals:
```
ValueFromPodKey("local_ssn", 0x4030, "ssn")
```
means that the pod `0x4030` has a key called `ssn`, the local pod has a key `local_ssn`, and they have the same value.

An example with keys, that expresses the same semantic meaning:
```
ValueOf(local_varname, "local_ssn")
ValueOf(remote_varname, "ssn")
ValueOf(gov_id_root, 0x4030)
ValueFromPodKey(local_varname, gov_id_root, remote_varname)
```

## Summary of additional statements in this spec

```
ValueFromPodKey(local_key: KeyOrLiteral::String, origin_id: KeyOrLiteral::OriginID, key: KeyOrLiteral::String).
```


In addition to the built-in statements in the [main spec](./statements.md):

There is one additional front-end type: `OriginID`.  As the name suggests, it contains the "origin ID" of a POD.

There are two additional built-in statements:
```
Reference(reference_key: Key::String, key: Key)

ValueFromPodKey(local_key: KeyOrLiteral::String, origin_id: KeyOrLiteral::OriginID, key: KeyOrLiteral::String).
```

```
Reference(reference_key, key)
```
means that the *value* of `reference key` is the *key name* of `key`.

```
ValueFromPodKey(local_key, origin_id, key)
```
means that the key `local_key` in the local scope has the same value as the key `key` in the scope of the pod `origin_id`.

## How to work with the local variable requirement

To make a statement about an inherited value (a value introduced in an ancestor POD), the value must be copied to a local value:

The statements below assert that "name" on pod1 and "friend" on pod2 are assigned the same value.
```
ValueFromPodKey(name_from_pod1, pod1, "name")
ValueFromPodKey(friend_from_pod2, pod2, "friend")
Equal(name_from_pod1, friend_from_pod2)
```

## How to inherit local variables from a previous POD

In this design, an additional complication arises when you
carry a value from one POD to another,
and you want to keep track of the origin POD on which it originated.

To allow this operation, we introduce an additional deduction rule
```
InheritValueFromPodKey,
```
which works as follows.

Suppose "self" is the current POD and "parent_id" is the POD id of one of the input PODs to "self".

Suppose "parent" has, among its public statements, the statement
```
ValueFromPodKey(parent_name, origin, original_name)
```
and "self" has the statement (public or private)
```
ValueFromPodKey(self_name, parent_id, parent_name).
```

Then ```InheritValueFromPodKey``` allows you to generate the following statement on "self":
```
ValueFromPodKey(self_name, origin, original_name).
```
