# Examples

Examples of POD2 use cases

## EthDos
*Check also the [custom statement example](./customexample.md) section.*

Original in prolog https://gist.github.com/ludns/f84b379ec8c53c97b7f95630e16cc39c#file-eth_dos-pl

An EthDos Pod exposes a single custom statement with two custom deduction
rules, the inductive case and the base case.

```
// src, dst: PubKey, attetation_pod: Pod
eth_dos_friend(src, dst, private: attestation_pod) = AND(
    ValueOf(attestation_pod[KEY_TYPE], SIGNATURE)
    Equal(attestation_pod[KEY_SIGNER], src)
    Equal(attestation_pod["attestation"], dst) 
)

// src, intermed, dst: PubKey, distance, shorter_distance: Int
eth_dos_distance(src, dst, distance, private: shorter_distance, intermed) = OR(
    AND(
        eth_dos_distance(src, intermed, shorter)
        SumOf(distance, shorter_distance, 1)
        eth_friend(intermed, dst)
    )
    AND(
        Equal(src, dst)
        Equal(distance, 0)
    )
)
```

## ZuKYC (classic)

Original using GPC https://github.com/proofcarryingdata/zukyc

Authority public keys:
- `ZOO_GOV`: PubKey, issues IDs
- `ZOO_DEEL`: PubKey, issues bank statements
Authority lists:
- `SANCTION_LIST`: Set, Merkle Tree Root of set of sanctioned public keys
    - values: `["G2345678", "G1987654", "G1657678"]`
Date values:
- `NOW_MINUS_18Y`: Int, 18 years ago
- `NOW_MINUS_1Y`: Int, 1 year ago
- `NOW_MINUS_7D`: Int, 7 days ago

A ZuKYC Pod exposes a single custom statement with one custom deduction rule.

```
// receiver: PubKey, gov_id, paystub, sk_pok: Pod, nullifier, sk: Raw
loan_check(receiver, private: gov_id, paystub, nullifier, sk, sk_pok) = AND(
    Equal(gov_id["pk"], receiver)
    // Not in the sanction list
    SetNotContains(SANCTION_LIST, receiver)
    // Valid government-issued ID
    Equal(gov_id[KEY_SIGNER], ZOO_GOV)
    Equal(gov_id[KEY_TYPE], SIGNATURE)
    // At least 18 years old
    Lt(gov_id["date_of_birth"], NOW_MINUS_18Y) # date_of_birdth is more than 18y old
    Equal(paystub[KEY_SIGNER], ZOO_DEEL)
    Equal(paystub[KEY_TYPE], SIGNATURE)
    Equal(paystub[ssn], gov_id["ssn"])
    // At least one year of consistent employment with your current employer
    Lt(paystub["start_date"], NOW_MINUS_1Y) # start_date is more than 1y old
    Gt(paystub["issue_date"], NOW_MINUS_7D) # issue_date is less than 7d old
    // Annual salary is at least $20,000
    Gt(paystub["annual_salary"], 20000)
    // Private key knowledge
    Equal(sk_pok[KEY_SIGNER], receiver)
    Equal(sk_pok[KEY_TYPE], SIGNATURE)
    Equal(sk_pok["auth"], "ZUKYC_V1_AUTH")
    HashOf(, 0, sk)
    // Nullifier
    HashOf(nullifier, "ZUKYC_V1_NULLIFIER", sk)
)
```

## ZuKYC (simplified for P1)

This simplified version uses less statements but requires a very similar set of
features.

Authority lists:
- `SANCTION_LIST`: Set, Merkle Tree Root of set of sanctioned public keys
    - values: `["G2345678", "G1987654", "G1657678"]`
Date values:
- `NOW_MINUS_18Y`: Int, 18 years ago
- `NOW_MINUS_1Y`: Int, 1 year ago

A ZuKYC Pod exposes a single custom statement with one custom deduction rule.

```
// receiver: String, gov_pk, paystub_pk: PubKey, gov_id, paystub: Pod
loan_check(receiver, gov_pk, paystub_pk, private: gov_id, paystub) = AND(
    Equal(gov_id["id_number"], receiver)
    // Not in the sanction list
    SetNotContains(SANCTION_LIST, gov_id["id_number"])
    // Valid government-issued ID
    ValueOf(gov_id[KEY_SIGNER], gov_pk)
    Equal(gov_id[KEY_TYPE], SIGNATURE)
    // At least 18 years old
    Lt(gov_id["date_of_birth"], NOW_MINUS_18Y) # date_of_birdth is more than 18y old
    ValueOf(paystub[KEY_SIGNER], paystub_pk)
    Equal(paystub[KEY_TYPE], SIGNATURE)
    Equal(paystub["ssn"], gov_id["ssn"])
    // At least one year of consistent employment with your current employer
    Lt(paystub["start_date"], NOW_MINUS_1Y) # start_date is more than 1y old
)
```

## GreatBoy

A Good Boy Pod exposes one custom statement with one custom deduction rule.

```
// user: PubKey, good_boy_issuers: Set, pod: Pod, age: Int
is_good_boy(user, good_boy_issuers, private: pod, age) = AND(
    Equal(pod[KEY_TYPE], SIGNATURE)
    SetContains(good_boy_issuers, pod[KEY_SIGNER])
    // A good boy issuer says this user is a good boy
    Equal(pod["user"], user)
    Equal(pod["age"], age)
)
```

A Friend Pod exposes one custom statement with one custom deduction rule.

```
// good_boy, friend: PubKey, good_boy_issuers: Set, friend_pod: Pod
is_friend(good_boy, friend, good_boy_issuers, friend_pod) = AND(
    Equal(pod[KEY_TYPE], SIGNATURE)
    // The issuer is a good boy
    is_good_boy(good_boy, good_boy_issuers)
    // A good boy says this is their friend
    Equal(pod[KEY_SIGNER], good_boy)
    Equal(pod["friend"], friend)
)
```

A Great Boy Pod exposes (in addition to the above) one new custom statement
with one custom deduction rule.

```
great_boy: PubKey, good_boy_issuers: Set, friend_pod_0, friend_pod_1: Pod
is_great_boy(great_boy, good_boy_issuers, private: friend_pod_0, friend_pod_1) = AND
    // Two good boys consider this user their friend
    is_friend(friend_pod_0[KEY_SIGNER], great_boy)
    is_friend(friend_pod_1[KEY_SIGNER], great_boy)
    // good boy 0 != good boy 1
    NotEqual(friend_pod_0[KEY_SIGNER], friend_pod_1[KEY_SIGNER])
``` 

## Attested GreatBoy

An Attested Great Boy Pod is like a Great Boy Pod, but the names of the signers are revealed.

```
// great_boy: PubKey, friend0, friend1: String, good_boy_issuers: Set, friend_pod_0, friend_pod_1: Pod
is_great_boy(great_boy, friend0, friend1, good_boy_issuers, private: friend_pod_0, friend_pod_1) = AND
    // Two good boys consider this user their friend
    is_friend(friend_pod_0[KEY_SIGNER], great_boy)
    is_friend(friend_pod_1[KEY_SIGNER], great_boy)
    // good boy 0 != good boy 1
    NotEqual(friend_pod_0[KEY_SIGNER], friend_pod_1[KEY_SIGNER])
    // publicize signer names
    ValueOf(friend_pod_0["name"], friend0)
    ValueOf(friend_pod_1["name"], friend1)
``` 

To produce a Great Boy Pod, you need two Friend Pods, `friend_pod0` and `friend_pod1`, each of which reveals its `signer`.

## Tracking PodIDs: Posts and comments

The goal of this example is to model a social network, where posts and comments are pods.

A Post is a signature pod with the following fields:
```
content: String
poster: String
signer: PubKey
timestamp: Int
```

A Comment is a signature pod with the following fields:
```
content: String
referenced_post: PodID
signer: PubKey
timestamp: Int
```

A post is popular if it has at least two comments from different signers.

```
// post, comment1, comment2: Pod
statement is_popular(post, private: comment1, comment2) = AND(
    IsEqual(comment1["referenced_post"], post)
    IsEqual(comment2["referenced_post"], post)
    NotEqual(comment1[KEY_SIGNER], comment2[KEY_SIGNER])
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
over_18(?1) = AND(
    GtEq(?1, 18)
)
```

Maybe I have two input pods `gov_id1` and `gov_id2`, and I want to prove that these pods refer to two different people, both of whom are over 18; and a third pods `gov_id3` refers to someone under 18.  So in my public output statements, I want to have:
```
NotEqual(gov_id1["name"], gov_id2["name"])
over_18(gov_id1["age"])
over_18(gov_id2["age"])
under_18(gov_id3["age"]).
```

I would prove this with the following sequence of deductions:
| Statement | Reason |
| --- | --- |
| over_18(gov_id1["age"]) | over_18, <br> ?1 = gov_id1["age"] |
| over_18(gov_id2["age"]) | over_18, <br> ?1 = gov_id2["age"] |
| under_18(gov_id3["age"]) | under_18, <br> ?1 = gov_id3["age"] |
| NotEqual(gov_id1["name"], gov_id2["name"]) | (not equal from entries) |

