# POD value types
From the frontend perspective, POD values may be one of three[^type] types:
- `Integer`
- `String`
- `Dictionary`

From the backend perspective, however, these types will all be encoded as a fixed number of field elements, the number being chosen so as to accommodate the `Integer` type as well as hashes to represent the `String` and `Dictionary` types with the appropriate level of security.

In the case of the Plonky2 backend with 100 bits of security, all of these types are represented as 4 field elements, the output of the Poseidon hash function used there being

$$\texttt{HashOut<GoldilocksField>}\simeq\texttt{[GoldilocksField; 4]}.$$

## `Integer`
In the frontend, this type is none other than `u64`[^i64]. In the backend, it will be appropriately embedded into the codomain of the canonical hash function.

In the case of the Plonky2 backend, this is done by decomposing such an integer $x$ as
$$x = x_0 + x_1 \cdot 2^{32}$$
with $0 \leq x_0, x_1 < 2^{32}$ and representing it as
$$\texttt{map}\ \iota\ [x_0, x_1, 0, 0],$$
where $\iota:\mathbb{N}\rightarrow\texttt{GoldilocksField}$ is the canonical projection.

## `String`
In the frontend, this type corresponds to the usual `String`. In the backend, the string will be mapped to a sequence of field elements[^String] and hashed with the hash function employed there, thus being represented by its hash.

## `Dictionary`
In the front end, a `Dictionary` is simply an unordered set of key-value pairs, in which all keys are distinct.  Every key and every value is a string, integer, or dictionary.

A `Dictionary` is supposed to act like a Python dictionary or a JSON object.

An example of a `Dictionary`:
```
{
    "name": "Aard",
    "ID": 123,
    "attributes": {
        height: 7,
        strength: 12,
        friendly: "no"
    }
}
```

A `Dictionary` cannot involve circular references: a `Dictionary` cannot appear in itself -- or any subobject of itself -- as a key or value.

In the back end, a dictionary will be represented as a Merkle root, which will be of the type of the output of the hash function employed.  The conversion from dictionary to Merkle root is a recursive process, explained in the [Encoding Dictionaries](encodingdictionaries.md) page.

[^type]: <font color="red">TODO</font> In POD 1, there is the `cryptographic` type, which has the same type of the output of the hash function employed there. It is useful for representing arbitrary hashes. Do we want to expand our type list to include a similar type, which would correspond to the `HashOut` type in the case of Plonky2? This would not have a uniform representation in the frontend if we continue to be backend agnostic unless we fix the number of bits to e.g. 256, in which case we would actually need one more field element in the case of Plonky2.
[^i64]: <font color="red">TODO</font> Replace this with `i64` once operational details have been worked out.
[^String]: <font color="red">TODO</font> Adopt or recommend a particular approach, e.g. mapping the string to bytes and separating it into chunks with appropriate padding.
