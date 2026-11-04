# Examples

Examples of POD2 use cases, written in [Podlang](./podlang.md).  Names in
uppercase (`ZOO_GOV`, `SANCTION_LIST`, ...) stand for literal values.

## EthDos

An EthDos POD exposes a single custom statement with two custom deduction
rules, the inductive case and the base case.  The four predicates form a
recursive batch (see [how it is hashed](./customhash.md#example)).

```
// src, dst: PublicKey, attestation: Dictionary
eth_friend(src, dst, private: attestation) = AND(
    SignedBy(attestation, src)
    Contains(attestation, "attestation", dst)
)

// src, intermed, dst: PublicKey, distance, shorter_distance: Int
eth_dos_base(src, dst, distance) = AND(
    Equal(src, dst)
    Equal(distance, 0)
)

eth_dos_ind(src, dst, distance, private: shorter_distance, intermed) = AND(
    eth_dos(src, intermed, shorter_distance)
    // distance == shorter_distance + 1
    Sum(shorter_distance, 1, distance)
    // intermed is a friend of dst
    eth_friend(intermed, dst)
)

eth_dos(src, dst, distance) = OR(
    eth_dos_base(src, dst, distance)
    eth_dos_ind(src, dst, distance)
)
```

## ZuKYC

Original using GPC https://github.com/proofcarryingdata/zukyc

Authority public keys:
- `ZOO_GOV`: PublicKey, issues IDs
- `ZOO_DEEL`: PublicKey, issues bank statements

Authority lists:
- `SANCTION_LIST`: Set of sanctioned ID numbers
    - values: `#["G2345678", "G1987654", "G1657678"]`

Date values:
- `NOW_MINUS_18Y`: Int, 18 years ago
- `NOW_MINUS_1Y`: Int, 1 year ago
- `NOW_MINUS_7D`: Int, 7 days ago

A ZuKYC POD exposes a single custom statement with one custom deduction rule.

```
// receiver: PublicKey, gov_id, paystub: Dictionary, sk: SecretKey, nullifier: Untyped
loan_check(receiver, nullifier, private: gov_id, paystub, sk) = AND(
    Equal(gov_id["pk"], receiver)
    // Not in the sanction list
    SetNotContains(SANCTION_LIST, gov_id["id_number"])
    // Valid government-issued ID
    SignedBy(gov_id, ZOO_GOV)
    // At least 18 years old
    Lt(gov_id["date_of_birth"], NOW_MINUS_18Y)
    // Valid paystub for the same person
    SignedBy(paystub, ZOO_DEEL)
    Equal(paystub["ssn"], gov_id["ssn"])
    // At least one year of consistent employment with your current employer
    Lt(paystub["start_date"], NOW_MINUS_1Y)
    Gt(paystub["issue_date"], NOW_MINUS_7D)
    // Annual salary is at least $20,000
    Gt(paystub["annual_salary"], 20000)
    // Private key knowledge
    PublicKey(sk, receiver)
    // Nullifier
    Hash("ZUKYC_V1_NULLIFIER", sk, nullifier)
)
```

## GreatBoy

A Good Boy POD exposes one custom statement with one custom deduction rule.

```
// user: PublicKey, good_boy_issuers: Set, attestation: Dictionary, issuer: PublicKey
is_good_boy(user, good_boy_issuers, private: attestation, issuer) = AND(
    SetContains(good_boy_issuers, issuer)
    // A good boy issuer says this user is a good boy
    SignedBy(attestation, issuer)
    Equal(attestation["user"], user)
)
```

A Friend POD exposes one custom statement with one custom deduction rule.

```
// good_boy, friend: PublicKey, good_boy_issuers: Set, attestation: Dictionary
is_friend(good_boy, friend, good_boy_issuers, private: attestation) = AND(
    // The issuer is a good boy
    is_good_boy(good_boy, good_boy_issuers)
    // A good boy says this is their friend
    SignedBy(attestation, good_boy)
    Equal(attestation["friend"], friend)
)
```

A Great Boy POD exposes (in addition to the above) one new custom statement
with one custom deduction rule.

```
// great_boy: PublicKey, good_boy_issuers: Set, friend_0, friend_1: PublicKey
is_great_boy(great_boy, good_boy_issuers, private: friend_0, friend_1) = AND(
    // Two good boys consider this user their friend
    is_friend(friend_0, great_boy, good_boy_issuers)
    is_friend(friend_1, great_boy, good_boy_issuers)
    // good boy 0 != good boy 1
    NotEqual(friend_0, friend_1)
)
```

## Attested GreatBoy

An Attested Great Boy POD is like a Great Boy POD, but the friends are revealed.

```
// great_boy, friend_0, friend_1: PublicKey, good_boy_issuers: Set
is_attested_great_boy(great_boy, friend_0, friend_1, good_boy_issuers) = AND(
    // Two good boys consider this user their friend
    is_friend(friend_0, great_boy, good_boy_issuers)
    is_friend(friend_1, great_boy, good_boy_issuers)
    // good boy 0 != good boy 1
    NotEqual(friend_0, friend_1)
)
```

## Posts and comments

The goal of this example is to model a social network, where posts and comments are signed dictionaries.

A Post is a signed dictionary with the following fields:
```
content: String
poster: String
timestamp: Int
```

A Comment is a signed dictionary with the following fields:
```
content: String
referenced_post: Dictionary (the root of the post)
timestamp: Int
```

A post is popular if it has at least two comments from different signers.

```
// post, comment1, comment2: Dictionary, signer1, signer2: PublicKey
is_popular(post, private: comment1, comment2, signer1, signer2) = AND(
    SignedBy(comment1, signer1)
    SignedBy(comment2, signer2)
    Equal(comment1["referenced_post"], post)
    Equal(comment2["referenced_post"], post)
    NotEqual(signer1, signer2)
)
```

## Multiple people over 18

Suppose I want to prove that two different people are over 18, and a third person is under 18, using the custom predicates `over_18` and `under_18`.
```
// age: Int
over_18(age) = AND(
    GtEq(age, 18)
)
```

```
// age: Int
under_18(age) = AND(
    Lt(age, 18)
)
```

With wildcards:
```
over_18(?0) = AND(
    LtEq(18, ?0)
)
```

Maybe I have three dictionaries `gov_id1`, `gov_id2` and `gov_id3`, and I want to prove that the first two refer to two different people, both of whom are over 18; and the third one refers to someone under 18.  So in my public output statements, I want to have:
```
NotEqual(gov_id1["name"], gov_id2["name"])
over_18(gov_id1["age"])
over_18(gov_id2["age"])
under_18(gov_id3["age"]).
```

I would prove this with the following sequence of deductions:
| Statement | Reason |
| --- | --- |
| over_18(gov_id1["age"]) | over_18, <br> ?0 = gov_id1["age"] |
| over_18(gov_id2["age"]) | over_18, <br> ?0 = gov_id2["age"] |
| under_18(gov_id3["age"]) | under_18, <br> ?0 = gov_id3["age"] |
| NotEqual(gov_id1["name"], gov_id2["name"]) | NotEqualFromEntries |

Each custom operation outputs a statement with the literal value of the age; it is then converted to use the anchored key with `ReplaceValueWithEntry`.
