# Example of a custom statement involving Merkle trees

This custom statement lets you insert a key-value pair into a Merkle tree that does not already contain the key.
```
Insert(oldroot, k, v, newroot)
```
means: `oldroot` is a Merkle root that does not contain the key `k`, and `newroot` is the result of inserting `(k, v)` into it. 

The definition of `Insert` takes a bit of work.

First, to handle the base case, we define a simple custom predicate for small trees:
```
// `root` is a Merkle node at depth `depth`. the tree has just two key-value pairs.  One pair is `(k, v)`; the other one hashes to a leaf node of `leaf`
// This statement checks that (k, v) is assigned to the correct branch
// but it does not check `leaf`

// There are four cases, depending which way the two entries go -- left or right
TwoEntries(node, k, v, leaf, depth) = OR <
    // both (k, v) and leaf go left
    AND <
        Branches(node, l_node, r_node),
        GoesLeft(k, depth),
        TwoEntries(l_node, k, v, l, depth + 1),
        IsNullTree(r_node)
    >
    // (k, v) goes left, leaf goes right
    AND <
        Branches(node, l_node, r_node),
        GoesLeft(k, depth),
        Leaf(l_node, k, v),
        Eq(r_node, leaf)
    >
    // (k, v) goes right, leaf goes left
    AND <
        Branches(node, l_node, r_node),
        GoesRight(k, depth),
        Eq(l_node, leaf),
        Leaf(r_node, k, v)
    >
    // both (k, v) and leaf go right
    AND <
        Branches(node, l_node, r_node),
        GoesRight(k, depth),
        IsNullTree(l_node)
        TwoEntries(r_node, k, v, l, depth + 1),
    >
>
```

To do the recursion, we need a more general custom statement `InsertAtDepth` -- the definition is the same as insert, except that `oldnode` and `newnode` are nodes at the given depth `depth`.
```
InsertAtDepth(oldnode, k, v, newnode, depth::Integer) = OR <
    // both sides are merkle roots in the original tree;
    // k goes left
    AND <
        Branches(oldnode, l_old, r_old),
        Branches(newnode, l_new, r_new),
        Eq(r_old, r_new),
        GoesLeft(k, depth),
        InsertAtDepth(l_old, k, v, l_new, depth + 1)
    >

    // both sides are merkle roots in the original tree;
    // k goes right
    AND <
        Branches(oldnode, l_old, r_old),
        Branches(newnode, l_new, r_new),
        Eq(l_old, l_new),
        GoesRight(k, depth),
        InsertAtDepth(r_old, k, v, r_new, depth + 1)
    >

    // oldnode is a leaf; 
    // newnode is a tree with two entries
    AND <
        Leaf(oldnode, oldkey, oldval)
        TwoEntries(newnode, k, v, oldnode, depth)
    >

    // oldnode is null;
    // newnode is a leaf
    AND <
        IsNullTree(oldnode),
        Leaf(newnode, k, v)
    >
>
```

Finally, `Insert` is just the special case of `InsertAtDepth` at depth zero.
```
Insert(oldroot, k, v, newroot) = InsertAtDepth(oldroot, k, v, newroot, depth = 0).
```
