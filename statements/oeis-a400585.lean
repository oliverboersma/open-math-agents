import Mathlib

/-!
# Summatory growth of OEIS A400585

Source: https://oeis.org/A400585
Credit: @Iraeeee
-/

namespace OMA.S_oeis_a400585

/-- Index the divisors by their cofactors j. The corresponding divisor is n/j. -/
def a (n : ℕ) : ℕ :=
  ∑ j ∈ n.divisors, if Odd j then (n/j).choose 2 else 0

/-- The defining Dirichlet series at 3. The n=0 summand is zero in Lean. -/
noncomputable def zetaThree : ℝ := ∑' j : ℕ, ((j:ℝ)^3)⁻¹

theorem main : Filter.Tendsto
    (fun n : ℕ => (∑ k ∈ Finset.range (n+1), (a k : ℝ))/(n:ℝ)^3)
    Filter.atTop (nhds (7*zetaThree/48)) := by
  sorry

end OMA.S_oeis_a400585
