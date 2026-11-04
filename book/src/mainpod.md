# MainPOD

The MainPOD is the recursive POD of the system: a Plonky2 proof that verifies a
[two-column proof](./deductions.md) of statements, together with the proofs of
its input PODs.

## Inputs

A MainPOD takes as inputs:
- up to `max_input_pods` input PODs, which are recursively verified in-circuit.
  These can be other MainPODs or [Introduction PODs](./introductionpods.md).
  Unused slots are padded with an `EmptyPod`.
- the list of statements and operations to verify, each statement marked as
  public or private.
- the definitions of the [custom predicate batches](./custom.md) used by the
  custom operations.

## Statement table

The circuit lays out the statements in a table with the following regions:
1. a `None` statement at index 0, used for padding operation arguments;
2. `max_open_input_statement_ops` rows of statements imported from the input
   PODs with `OpenInputStatement`;
3. `max_statements` rows of statements derived by operations.

An operation can only use as arguments statements that appear in a previous row
of the table.

## Public statements

The public statements of a POD are put in an `Array` (a [Merkle
tree](./merkletree.md) with the statement index as key and the statement hash as
value).  Its root is the _statements root_ of the POD, which identifies the POD's
claims: two PODs that expose the same public statements have the same
statements root.

A statement of an input POD is imported by providing a Merkle proof of its hash
against the input POD's statements root.  This way, a POD can use any public
statement of its input PODs without the circuit having to process all of them.

Optionally, a MainPOD can extend the public statements of its first input POD
(if it's a MainPOD) instead of starting from an empty list, which allows
building a long list of public statements across several PODs.

## Verifier data set

To support recursion with more than one circuit, each MainPOD commits to a
_verifier data set_ (`VDSet`): a Merkle tree of the hashes of the verifier data
of the allowed circuits.  The MainPOD verifies that each input MainPOD was proved
with one of the circuits in the set, and that it uses the same set.

Introduction PODs are not checked against the set; instead, their verifier data
hash is embedded in the introduction statements they output.

## Public inputs

The public inputs of the MainPOD proof are:
- the statements root (4 field elements);
- the root of the verifier data set (4 field elements);
- an `is_main` flag, which distinguishes MainPODs from Introduction PODs.

## Parameters

The size of the circuit is defined by a set of parameters (`Params`), such as
`max_input_pods`, `max_statements`, `max_public_statements`,
`max_open_input_statement_ops`, the maximum number of custom predicates and
custom predicate operations, the number of Merkle proofs of each size, and the
maximum number of signature verifications and public key derivations.  If a
proof needs more resources than one MainPOD provides, the frontend can split it
into several chained MainPODs automatically.
