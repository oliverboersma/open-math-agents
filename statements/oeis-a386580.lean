import Mathlib

/-!
# Distinct run lengths versus disjoint strict partitions (OEIS A386580)

Source: https://oeis.org/A386580 (Gus Wiseman, OEIS Foundation, CC BY-SA 4.0).

A normal multiset of size n contains each of 1, ..., k at least once and has n elements;
it is determined by its multiplicity vector, a composition (c_1, ..., c_k) of n. A386580(n)
counts the normal multisets of size n having a permutation whose maximal runs have pairwise
distinct lengths.

Conjecture (in the entry): A386580(n) is also the number of normal multisets of size n having
a disjoint family of strict integer partitions, one of each multiplicity: pairwise disjoint
finite sets of positive integers, the i-th summing to c_i.

Formalization: multisets are indexed by `Composition n`; a permutation of the multiset is a
word over `Fin k` in which the letter i occurs exactly c_i times; its maximal runs are the
blocks of `List.splitBy (· == ·)`.
-/

namespace OMA.S_oeis_a386580

/-- The multiset with multiplicity vector `c` has a permutation with pairwise distinct
run lengths. -/
def HasDistinctRunPerm {n : ℕ} (c : Composition n) : Prop :=
  ∃ w : List (Fin c.length), (∀ i : Fin c.length, w.count i = c.blocks.get (i.cast c.blocks_length.symm)) ∧
    ((w.splitBy (· == ·)).map List.length).Nodup

/-- The multiset with multiplicity vector `c` has a disjoint family of strict partitions, one
of each multiplicity. -/
def HasDisjointStrictParts {n : ℕ} (c : Composition n) : Prop :=
  ∃ S : Fin c.length → Finset ℕ, (∀ i, 0 ∉ S i) ∧
    (∀ i, ∑ x ∈ S i, x = c.blocks.get (i.cast c.blocks_length.symm)) ∧
    ∀ i j, i ≠ j → Disjoint (S i) (S j)

/-- Wiseman's conjecture on A386580: the two counts agree for every size `n`. -/
theorem main : ∀ n : ℕ,
    Nat.card {c : Composition n // HasDistinctRunPerm c} =
      Nat.card {c : Composition n // HasDisjointStrictParts c} := by
  sorry

end OMA.S_oeis_a386580
