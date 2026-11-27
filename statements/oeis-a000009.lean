import Mathlib

/-!
The two conjectures of Zhi-Wei Sun recorded in OEIS A000009 on April 14 and May 20, 2023.
Source: https://oeis.org/A000009/internal
The first conjecture is also stated at https://mathoverflow.net/questions/444761.
Credit: @dhairyajangir
-/

namespace OMA.S_oeis_a000009

open scoped BigOperators

/-- OEIS A000009 counts partitions into distinct parts. -/
def strictPartitionCount (n : ℕ) : ℕ := (Nat.Partition.distincts n).card

/-- OEIS A000041 counts all partitions. -/
def partitionCount (n : ℕ) : ℕ := Fintype.card (Nat.Partition n)

theorem main :
    (∀ n : ℕ, 0 < n → ∃ k : ℕ, ∃ terms : Fin k → ℕ,
      (∀ i, ∃ m : ℕ, 0 < m ∧ terms i = strictPartitionCount m) ∧
      (∑ i, terms i) = n ∧
      (∀ i j, i ≠ j → ¬ terms i ∣ terms j)) ∧
    (∀ n : ℕ, 7 < n →
      (¬ strictPartitionCount n ∣ partitionCount n) ∧
      (¬ strictPartitionCount n ∣ partitionCount n - 1) ∧
      (¬ strictPartitionCount n ∣ partitionCount n + 1)) := by
  sorry

end OMA.S_oeis_a000009
