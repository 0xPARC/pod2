# Introduction

pod2 is a cryptographic standard that allows sharing data with mathematically proven relations in a privacy preserving way.

At its core, a pod2 proof can consume statements from other pod2 proofs and derive new logically valid statements.  The statements themselves express relations between units of data.  At any point a user can choose to hide or reveal statements to control their privacy.

The pod2 stack follows these layers:
| Concept                    | Implementation          |
| -------------------------- | ----------------------- |
| predicate language         | podlang                 |
| statement derivation kernel | MainPod plonky2 circuit |
| zk proving system          | plonky2                 |

- The predicate language allows the definition of the set of relations that a
  statement fulfills and is the fully programable part of the system
- The statement derivation kernel is the piece that verifies that new
  statements are generated following logical rules from other existing valid
  statements
- The zk proving system is the underlaying mechanism used to obtain succint
  proofs of correct statement derivation while hiding intermediate results.
