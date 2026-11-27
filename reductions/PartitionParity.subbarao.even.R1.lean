import FormalConjectures.Paper.PartitionParity
import Mathlib

/-! Subbarao's conjecture for even values from Ahlgren's quantitative bound. Ahlgren,
Distribution of parity of the partition function in arithmetic progressions, Indag. Math. 10
(1999), shows that in every progression r mod t the number of n ≤ X with p(n) even is at
least of order sqrt X; this is the catalogue's PartitionParity.ahlgren.even. A set of natural
numbers whose counting function dominates sqrt X cannot be finite, which is a statement
about sets and real functions only. -/

namespace OMA.R_PartitionParity_subbarao_even_R1
open Filter Asymptotics

/-- Ahlgren's lower bound for even values of p(n) in arithmetic progressions. -/
def H1 : Prop := ∀ r t : ℕ, 0 < t →
  (fun X : ℝ ↦ Real.sqrt X) =O[atTop]
    fun X : ℝ ↦ ({n : ℕ | (n : ℝ) ≤ X ∧ n ≡ r [MOD t] ∧ Even (Nat.partitionNumber n)}.ncard : ℝ)

/-- A set of natural numbers whose counting function dominates sqrt X is infinite. -/
def H2 : Prop := ∀ S : Set ℕ,
  (fun X : ℝ ↦ Real.sqrt X) =O[atTop]
    (fun X : ℝ ↦ ({n : ℕ | (n : ℝ) ≤ X ∧ n ∈ S}.ncard : ℝ)) → S.Infinite

theorem main : H1 → H2 → type_of% @PartitionParity.subbarao.even := by
  intro h1 h2 r t ht
  exact h2 {n : ℕ | n ≡ r [MOD t] ∧ Even (Nat.partitionNumber n)} (h1 r t ht)

end OMA.R_PartitionParity_subbarao_even_R1
