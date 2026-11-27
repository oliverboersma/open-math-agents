import FormalConjectures.Paper.PartitionParity
import Mathlib

/-! The Bellaïche, Green and Soundararajan lower bound of order sqrt X / log log X for the
number of n ≤ X with p(n) odd, from Zheng's stronger bound of order sqrt X, which is the
catalogue's PartitionParity.zheng.odd. Since log log X is eventually at least 1,
sqrt X / log log X is O(sqrt X); that comparison is a statement about real functions only. -/

namespace OMA.R_PartitionParity_bellaiche_green_soundararajan_odd_R1
open Filter Asymptotics

/-- Zheng's lower bound of order sqrt X for odd values of p(n). -/
def H1 : Prop := (fun X : ℝ ↦ Real.sqrt X) =O[atTop]
  fun X : ℝ ↦ ({n : ℕ | (n : ℝ) ≤ X ∧ Odd (Nat.partitionNumber n)}.ncard : ℝ)

/-- sqrt X / log log X is O(sqrt X). -/
def H2 : Prop := (fun X : ℝ ↦ Real.sqrt X / Real.log (Real.log X)) =O[atTop]
  (fun X : ℝ ↦ Real.sqrt X)

theorem main : H1 → H2 →
    type_of% @PartitionParity.bellaiche_green_soundararajan.odd := by
  intro h1 h2
  exact h2.trans h1

end OMA.R_PartitionParity_bellaiche_green_soundararajan_odd_R1
