import Mathlib

/-!
# A192205 and coefficient growth

The polynomial has integer coefficients, so their complex norms are their
usual absolute values. Its nth power has degree 3n.

Source: https://oeis.org/A192205
Credit: @Iraeeee
-/

namespace OMA.S_oeis_a192205
open Polynomial

noncomputable def P : ℂ[X] := 1-X-X^2+X^3

/-- Sum of absolute values of all the coefficients of the nth power. -/
noncomputable def a (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (3*n+1), ‖(P^n).coeff i‖

theorem main : Filter.Tendsto (fun n : ℕ => (a n) ^ (1/(n:ℝ)))
    Filter.atTop (nhds (16*Real.sqrt 3/9)) := by
  sorry

end OMA.S_oeis_a192205
