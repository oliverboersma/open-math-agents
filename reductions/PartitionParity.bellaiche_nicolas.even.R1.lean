import FormalConjectures.Paper.PartitionParity
import Mathlib

/-! The Bellaïche and Nicolas lower bound of order sqrt X log log X for the number of n ≤ X
with p(n) even, from its explicit form: Bellaïche and Nicolas, Parité des coefficients de
formes modulaires, Ramanujan J. 40 (2016), give at least 0.069 sqrt x log log x such n for
every x > 1, which is the catalogue's PartitionParity.bellaiche_nicolas.even_explicit. A
pointwise lower bound c g(x) ≤ F(x) for x > 1 with g(x) = sqrt x log log x gives g = O(F),
because g is eventually nonnegative; that is a statement about real functions only. -/

namespace OMA.R_PartitionParity_bellaiche_nicolas_even_R1
open Filter Asymptotics

/-- The explicit Bellaïche and Nicolas bound. -/
def H1 : Prop := ∀ x : ℝ, 1 < x →
  0.069 * Real.sqrt x * Real.log (Real.log x) ≤
    ({n : ℕ | (n : ℝ) ≤ x ∧ Even (Nat.partitionNumber n)}.ncard : ℝ)

/-- A pointwise bound c sqrt x log log x ≤ F(x) for x > 1 gives sqrt X log log X = O(F). -/
def H2 : Prop := ∀ (c : ℝ) (F : ℝ → ℝ), 0 < c →
  (∀ x : ℝ, 1 < x → c * Real.sqrt x * Real.log (Real.log x) ≤ F x) →
  (fun X : ℝ ↦ Real.sqrt X * Real.log (Real.log X)) =O[atTop] F

theorem main : H1 → H2 → type_of% @PartitionParity.bellaiche_nicolas.even := by
  intro h1 h2
  exact h2 0.069 _ (by norm_num) h1

end OMA.R_PartitionParity_bellaiche_nicolas_even_R1
