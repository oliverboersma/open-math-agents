import Mathlib.Combinatorics.Enumerative.Partition.Basic

/-! Beck's partition identity in OEIS A026796, with its corrected shift. -/

namespace OMA.S_oeis_a026796

open Multiset

abbrev LeastThree (n : ℕ) :=
  {p : Nat.Partition n // 3 ∈ p.parts ∧ ∀ x ∈ p.parts, 3 ≤ x}

abbrev Balanced (n : ℕ) :=
  {p : Nat.Partition n // 2 * p.parts.count 1 = p.parts.card}

instance (n : ℕ) : Fintype (LeastThree n) := by
  unfold LeastThree
  infer_instance

instance (n : ℕ) : Fintype (Balanced n) := by
  unfold Balanced
  infer_instance

def a (n : ℕ) : ℕ := Fintype.card (LeastThree n)

def b (n : ℕ) : ℕ := Fintype.card (Balanced n)

theorem main : ∀ n : ℕ, a (n + 4) = b n := by
  sorry

end OMA.S_oeis_a026796
