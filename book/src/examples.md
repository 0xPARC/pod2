# Examples

Examples of POD2 use cases

## EthDos
*Check also the [custom statement example](./customexample.md) section.*

Original in prolog https://gist.github.com/ludns/f84b379ec8c53c97b7f95630e16cc39c#file-eth_dos-pl

An EthDos Pod exposes a single custom statement with two custom deduction
rules, the inductive case and the base case.

```
statement eth_dos_distance(src: PubKey, dst: PubKey, distance: Int):
   - OR():
      - AND(attestation_pod: Pod, intermediate: PubKey, n: int):
         - eq(attetation_pod.attestation, dst)
         - eq(attetation_pod.type, SIGNATURE)
         - sum_of(distance, 1, n)
         - eth_dos_distance(src, attetation_pod.signer, n)
      - AND():
         - eq(src, dst)
         - eq(distance, 0)
```

## ZuKYC (classic)

Original using GPC https://github.com/proofcarryingdata/zukyc

Authority public keys:
- `ZOO_GOV`: PubKey, issues IDs
- `ZOO_DEEL`: PubKey, issues bank statements
Authority lists:
- `SANCTION_LIST`: Hash, Merkle Tree Root of set of sanctioned public keys
    - values: `["G2345678", "G1987654", "G1657678"]`
Date values:
- `NOW_MINUS_18Y`: Int, 18 years ago
- `NOW_MINUS_1Y`: Int, 1 year ago
- `NOW_MINUS_7D`: Int, 7 days ago

A ZuKYC Pod exposes a single custom statement with one custom deduction rule.

```
statement loan_check(receiver: PubKey):
   - OR():
      - AND(gov_id: Pod, paystub: Pod):
         - eq(gov_id.pk, receiver)
         # Not in the sanction list
         - does_not_contain(SANCTION_LIST, gov_id.pk)
         # Valid government-issued ID
         - eq(gov_id.signer, ZOO_GOV)
         - eq(gov_id.type, SIGNATURE)
         # At least 18 years old
         - lt(gov_id.date_of_birth, NOW_MINUS_18Y) # date_of_birdth is more than 18y old
         - eq(paystub.signer, ZOO_DEEL)
         - eq(paystub.type, SIGNATURE)
         - eq(paystub.ssn, gov_id.ssn)
         # At least one year of consistent employment with your current employer
         - lt(paystub.start_date, NOW_MINUS_1Y) # start_date is more than 1y old
         - gt(paystub.issue_date, NOW_MINUS_7D) # issue_date is less than 7d old
         # Annual salary is at least $20,000
         - gt(paystub.annual_salary, 20000)
```

## ZuKYC (simplified for P1)

This simplified version uses less statements but requires a very similar set of
features.

Authority lists:
- `SANCTION_LIST`: Hash, Merkle Tree Root of set of sanctioned public keys
    - values: `["G2345678", "G1987654", "G1657678"]`
Date values:
- `NOW_MINUS_18Y`: Int, 18 years ago
- `NOW_MINUS_1Y`: Int, 1 year ago

A ZuKYC Pod exposes a single custom statement with one custom deduction rule.

```
statement loan_check(receiver: string):
   - OR():
      - AND(gov_id: Pod, paystub: Pod):
         - eq(gov_id.id_number, receiver)
         # Not in the sanction list
         - does_not_contain(SANCTION_LIST, gov_id.id_number)
         # Valid government-issued ID
         - reveal(gov_id.signer)
         - eq(gov_id.type, SIGNATURE)
         # At least 18 years old
         - lt(gov_id.date_of_birth, NOW_MINUS_18Y) # date_of_birdth is more than 18y old
         - reveal(paystub.signer)
         - eq(paystub.type, SIGNATURE)
         - eq(paystub.ssn, gov_id.ssn)
         # At least one year of consistent employment with your current employer
         - lt(paystub.start_date, NOW_MINUS_1Y) # start_date is more than 1y old
```

## GreatBoy

A Good Boy Pod exposes one custom statement with one custom deduction rule.

```
statement is_good_boy(user: PubKey, good_boy_issuers: MerkleTree):
   - OR():
      - AND(pod: Pod, age: Int):
         - eq(pod.type, SIGNATURE)
         - contains(good_boy_issuers, pod.signer)
         # A good boy issuer says this user is a good boy
         - eq(pod.user, user)
         - eq(pod.age, age)
```

A Friend Pod exposes one custom statement with one custom deduction rule.

```
statement is_friend(good_boy: PubKey, friend: PubKey, good_boy_issuers: MerkleTree):
   - OR():
      - AND(friend_pod: Pod):
         - eq(pod.type, SIGNATURE)
         # The issuer is a good boy
         - is_good_boy(good_boy, good_boy_issuers)
         # A good boy says this is their friend
         - eq(pod.signer, good_boy)
         - eq(pod.friend, friend)
```

A Great Boy Pod exposes (in addition to the above) one new custom statement
with one custom deduction rule.

```
statement is_great_boy(great_boy: PubKey, good_boy_issuers: MerkleTree):
   - OR():
      - AND(friend_pod_0: Pod, friend_pod_1: Pod):
         # Two good boys consider this user their friend
         - is_friend(friend_pod_0.signer, great_boy)
         - is_friend(friend_pod_1.signer, great_boy)
         # good boy 0 != good boy 1
         - neq(friend_pod_0.signer, friend_pod_1.signer)
``` 

## Attested GreatBoy

An Attested Great Boy Pod is like a Great Boy Pod, but the names of the signers are revealed.

```
statement is_great_boy(great_boy: PubKey, friend0: String, friend1: String, good_boy_issuers: MerkleTree):
   - OR():
      - AND(friend_pod_0: Pod, friend_pod_1: Pod):
         # Two good boys consider this user their friend
         - is_friend(friend_pod_0.signer, great_boy)
         - is_friend(friend_pod_1.signer, great_boy)
         # good boy 0 != good boy 1
         - neq(friend_pod_0.signer, friend_pod_1.signer)
         # publicize signer names
         - value_of(friend_pod_0.name, friend0)
         - value_of(friend_pod_1.name, friend1)
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
statement is_popular(post: PodID):
   - AND():
      - IsEqual(comment1.referenced_post, post)
      - IsEqual(comment2.referenced_post, post)
      - NotEqual(comment1.signer, comment2.signer)
```

## Multiple people over 18

Suppose I want to prove that two different people are over 18, and a third person is under 18, using the custom predicates `over_18` and `under_18`.
```
statement over_18(age):
   - AND():
      - ValueOf(eighteen, 18)
      - GEq(age, eighteen)
```

```
statement under_18(age):
   - AND():
      - ValueOf(eighteen, 18)
      - Lt(age, eighteen)
```

With wildcards:
```
statement over_18(*1, *2):
   - AND():
      - ValueOf(*3, *4, 18)
      - GEq(*1, *2, *3, *4)
```

Maybe I have two input pods `gov_id1` and `gov_id2`, and I want to prove that these pods refer to two different people, both of whom are over 18; and a third pods `gov_id3` refers to someone under 18.  So in my public output statements, I want to have:
```
IsUnequal(gov_id1.name, gov_id2.name)
over_18(gov_id1.age)
over_18(gov_id2.age)
under_18(gov_id3.age).
```

I would prove this with the following sequence of deductions:
| Statement | Reason |
| --- | --- |
| ValueOf(local_eighteen, 18) | (new entry) |
| over_18(gov_id1.age) | over_18, <br> *1 = _SELF, <br> *2 = "local_eighteen", <br> *3 = gov_id1, <br> *4 = "age" |
| over_18(gov_id2.age) | over_18, <br> *1 = _SELF, <br> *2 = "local_eighteen", <br> *3 = gov_id2, <br> *4 = "age" |
| under_18(gov_id3.age) | under_18, <br> *1 = _SELF, <br> *2 = "local_eighteen", <br> *3 = gov_id3, <br> *4 = "age" |
| IsUnequal(gov_id1.name, gov_id2.name) | (is unequal from entries) |

