# Average income example

There's a famous toy example of an MPC protocol.  A group of people want to learn the average of their incomes -- without revealing how much money they make themselves.  The protocol is simple:
- The people sit in a circle.
- The first person writes a random number on a sheet of paper, and passes it to the second person.
- The second person adds her own income to the number, writes the result on a new sheet of paper, and passes it to the third person.
- The third person adds her income... and so forth, until the paper comes back around to the first person.
- The first person adds his income and subtracts the original random number; this is the sum of the incomes.  He divides by the number of people and announces the result.

This protocol works as long as everybody follows the protocol honestly.  With PODs, we can prove that everyone has honestly reported their incomes.  The POD protocol goes as follows.

- Each person has a signed POD from some central authority (the "bank") attesting to their income.
- The first person chooses a value (at random), creates a signed POD with the single value `RandomPOD.random`, and gives a copy of this POD to the second person.
- The second person creates a POD `POD1` proving that she added her income to `RandomPOD.random`, revealing the sum without revealing either value, and gives this POD to the third person.
- The third person creates a POD... and so forth, until the result comes back around to the first person.
- The first person creates a POD `PODn` proving that he added his income to `PODn-1.cmlsum` and subtracted `RandomPOD.random`.

Notice: since it is not possible for two different PODs to have the same ID, we are guaranteed that the same value `RandomPOD.random` was added at the beginning and subtracted at the end.

## Simple implementation, no custom statements

```
RandomPOD: SignedPod
ValueOf(_self.random, 10)
```

```
IncomePOD1: SignedPod
ValueOf(_self.signer, FellsWargo)
ValueOf(_self.name, "Jane")
ValueOf(_self.income, 12)
```

```
SumPOD1: MainPod
ValueOf(IncomePOD1.signer, FellsWargo)
ValueOf(IncomePOD1.name, "Jane")
SumOf(_self.cmlsum, RandomPOD.random, IncomePOD1.income)
ValueOf(_self.cmlsum, 22)
```

```
IncomePOD2: SignedPOD
ValueOf(_self.signer, BankOfSanFrancisco)
ValueOf(_self.name, "Carol")
ValueOf(_self.income, 35)
```

```
SumPOD2: MainPod
ValueOf(IncomePOD1.signer, FellsWargo)
ValueOf(IncomePOD1.name, "Jane")
ValueOf(IncomePOD2.signer, BankOfSanFrancisco)
ValueOf(IncomePOD2.name, "Carol")
SumOf(SumPOD2.cmlsum, RandomPOD.random, IncomePOD1.income)
SumOf(_self.cmlsum, SumPOD2.cmlsum, IncomePOD2.income)
ValueOf(cmlsum3, 57)
```

```
IncomePOD3: SignedPOD
ValueOf(_self.signer, MonteDeiPaschi)
ValueOf(_self.name, "Andrew")
ValueOf(_self.income, 1)
```

```
SumPOD3: MainPod
ValueOf(IncomePOD1.signer, FellsWargo)
ValueOf(IncomePOD1.name, "Jane")
ValueOf(IncomePOD2.signer, BankOfSanFrancisco)
ValueOf(IncomePOD2.name, "Carol")
ValueOf(IncomePOD3.signer, MonteDeiPaschi)
ValueOf(IncomePOD3.name, "Andrew")
SumOf(SumPOD1.cmlsum, RandomPOD.random, IncomePOD1.income)
SumOf(SumPOD2.cmlsum, SumPOD1.cmlsum, IncomePOD2.income)
SumOf(_self.cmlsum, SumPOD2.cmlsum, IncomePOD3.income)
SumOf(_self.result, _self.cmlsum, RandomPOD.random)
ValueOf(_self.result, 48)
```

This last POD, `SumPOD3`, is revealed to the whole group.

## Fancy implementation with custom predicates.

With custom predicates, we can simplify the code, and make it so the size of the POD does not grow with the size of the group.

This example builds on the custom statement `Insert` on the [Merkle example page](./merkleexample.md).

First, the `LegitBanksPOD` defines the list of recognized banks as a global constant.
```
LegitBanksPOD: SignedPOD
banks = {FellsWargo, BankOfSanFrancisco, MonteDeiPaschi}.
```

Next, the `IncomeOf` custom statement.
```
IncomeOf(name: AnchoredKey::String, amount: AnchoredKey::Integer) = AND <
        WILDCARD IncomePOD
        // all other originIDs and keys are hard-coded
    Contains(LegitBanksPOD.banks, IncomePOD.signer)
    Equals(IncomePOD.name, name)
    Equals(IncomePOD.income, amount)
>
```

The recursive step is the `CmlSum` custom statement.  It keeps track of:
- the list of names of people who have added their incomes (to prevent repeats)
- the number of people in the list of names
- the sum of values added so far
- the anchored key giving the initial random value

```
CmlSum(
    names: AnchoredKey::Set,
    n_people: AnchoredKey::Integer,
    cmlsum: AnchoredKey::Integer,
    random: AnchoredKey::Integer,
) = OR <
    // initialization
    AND <
        IsNullTree(names), // Technically we only defined this statement for MerkleTree, not for Set
        ValueOf(n_people, 0),
        Eq(cmlsum, random),
        IsInt(random),
    >

    // add one person
    AND <
            // the anchored key `random` must be the same anchored key
        CmlSum(old_names, old_n_people, old_cmlsum, random),
        IncomeOf(new_name: AnchoredKey::String, new_income: AnchoredKey::Integer),
            // Insert works with Merkle trees, not Sets
            // so it requires a key-value pair.
            // We use NULL for the value.
            // Note that Insert proves that new_name is not already contained in old_names.
        Insert(old_names, new_name, NULL, names),
        SumOf(n_people, old_n_people, 1),
        SumOf(cmlsum, old_cmlsum, new_income)
    >
>
```

At the end, the first player can subtract off the random value to prove a `SumOfIncomes` statement.

```
SumOfIncomes (
    names: AnchoredKey::Set,
    n_people: AnchoredKey::Integer,
    sum: AnchoredKey::Integer,
) = AND <
    CmlSum(names, n_people, cmlsum, random),
    SumOf(cmlsum, sum, random)
>
```

Simple.
