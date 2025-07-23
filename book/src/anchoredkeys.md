# Anchored keys
Rather than dealing with just keys, we introduce the notion of an *anchored key*, which is a pair consisting of an origin specifier and a key, i.e.

```
type AnchoredKey = (Origin, Key)
type Key = String
```

FIXME: This description is incorrect.  We don't have *gadget ID*.  And we don't think of *origin* as a triple, we just see it as a single value that encodes the *pod ID* or SELF.

An *origin* is a triple consisting of a numeric identifier called the *origin ID*, a string called the *origin name* (omitted in the backend) and another numeric identifier called the *gadget ID*, which identifies the means by which the value corresponding to a given key is produced.

The origin ID is defined to be 0 for 'no origin' and 1 for 'self origin', otherwise it is the content ID[^content-id] of the POD to which it refers. The origin name is not cryptographically significant and is merely a convenience for the frontend.

The gadget ID takes on the values in the following table:

| Gadget ID | Meaning                                                                                   |
|-----------|-------------------------------------------------------------------------------------------|
| 0         | no gadget                                                                                 |
| 1         | `SignedPOD` gadget: The key-value pair was produced in the construction of a `SignedPOD`. |
| 2         | `MainPOD` gadget: The key-value pair was produced in the construction of a `MainPOD`.     |

For example, a gadget ID of 1 implies that the key-value pair in question was produced in the process of constructing a `SignedPOD`.
[^content-id]: <font color="red">TODO</font> Refer to this when it is documented.
