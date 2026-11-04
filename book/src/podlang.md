# Podlang

Podlang is the language used to define [custom predicates](./custom.md) and to
describe proof requests.  The grammar can be found at
[pod2/src/lang/grammar.pest](https://github.com/0xPARC/pod2/blob/main/src/lang/grammar.pest).

There are two kinds of Podlang documents:
- **modules**, which contain predicate definitions (and imports), and are
  compiled into a batch of custom predicates;
- **requests**, which contain a `REQUEST` block (and imports), describing the
  statements that a POD must expose.

## Predicate definitions

```
over_18(person, private: age) = AND(
    Contains(person, "age", age)
    Lt(18, age)
)
```

A predicate definition has a name, a list of public arguments, an optional list
of private arguments after `private:`, and a body which is either `AND` or `OR`
of a list of statements.  Statements are separated by whitespace.  Comments use
`//` or `/* ... */`.

The arguments of a statement can be:
- an argument of the predicate (a wildcard);
- a literal value;
- an anchored key, written `dict["key"]` or `dict.key`.

The predicate of a statement can be a native predicate, a predicate defined in
the same module (in any order, which allows recursion), a predicate from an
imported module, an imported introduction predicate, or an argument of the
predicate (a wildcard predicate, which is bound to a `Predicate` value).

Large predicates are automatically split into a chain of smaller predicates to
fit the backend limits.

## Literals

| Type | Syntax |
| --- | --- |
| `Int` | `42`, `-1` |
| `Bool` | `true`, `false` |
| `String` | `"hello"` |
| `Untyped` | `Untyped(0x0000...0001)` (64 hex digits) |
| `PublicKey` | `PublicKey(<base58>)` |
| `SecretKey` | `SecretKey(<base64>)` |
| `Array` | `[1, 2, 3]` |
| `Set` | `#[1, 2, 3]` |
| `Dictionary` | `{"name": "Alice", "age": 30}` |
| `Predicate` | `@native_predicate(Equal)`, `@external_predicate(module, pred)`, `@self_predicate(pred)` |

## Imports

```
use module 0x<batch_id> as identity
use intro ecdsa_verified(pk, msg) from 0x<verifier_data_hash>
```

A module is imported by its batch ID, and its predicates are referenced as
`identity::pred`.  An [introduction predicate](./introductionpods.md) is imported
by the hash of the verifier data of the Introduction POD circuit.

## Records

A record declares named entries of an `Array`:
```
record Person = (name, age)

adult(p Person) = AND(
    Lt(17, p.age)
)
```
`p.age` is lowered to the anchored key `p[1]`.  Record literals are written
`Person(name: "Alice", age: 30)`, and `Person::age` evaluates to the entry index.

## Requests

A request lists the statements that a POD must expose:
```
use module 0x<batch_id> as eth_dos

REQUEST(
    eth_dos::eth_dos(src, dst, distance)
)
```
The identifiers in the request are wildcards that are matched against the
arguments of the public statements of the POD.
