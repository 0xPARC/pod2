# Introduction

POD2 is a cryptographic standard that lets users share data together with
proofs of relations about that data, while choosing what to reveal in a
privacy-preserving way.

A POD is a set of statements together with a proof that they are valid.  PODs
can bring external data into the system, such as signed data
([Introduction PODs](./introductionpods.md)), or be derived from other PODs
([MainPODs](./mainpod.md)).  A POD2 proof can consume statements from other
PODs and derive new, logically valid statements.  The statements themselves
express relations between units of data.  When deriving a new POD, a user
chooses which statements to expose as public and which to keep private,
allowing fine-grained control over their privacy.

The POD2 stack consists of the following layers, from highest to lowest level:

| Concept                     | Implementation                          |
| --------------------------- | --------------------------------------- |
| predicate language          | podlang                                 |
| statement derivation kernel | [MainPOD](./mainpod.md) plonky2 circuit |
| ZK proving system           | plonky2                                 |

- The predicate language allows the definition of the set of relations that a
  statement fulfills, and is the user-programmable part of the system.
- The statement derivation kernel verifies that new statements are derived
  from other existing valid statements following logical rules.
- The ZK proving system is the underlying mechanism used to obtain proofs of
  correct statement derivation that are succinct (small and fast to verify)
  and zero-knowledge (they hide private statements and intermediate results).

The [Specification](./front_and_back.md) section describes the data model,
statements and operations in detail, and the
[Architecture](./architecture.md) section describes how the implementation is
organized.
