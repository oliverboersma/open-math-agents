import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The logarithmic error bound for OEIS A076902

The sequence begins at index one. The value at zero is an auxiliary
extension, never reached by the recurrence at n≥2. Integer subtraction
here is the subtraction in the entry. The logarithm is natural.
We include the stated asymptotic together with the conjectured strict bound.

Source: https://oeis.org/A076902
Credit: @KoaOkano
-/

namespace OMA.S_oeis_a076902

def a (n : ℕ) : ℤ :=
  if n ≤ 1 then (n : ℤ) else ((n/2 : ℕ) : ℤ) - a (n/2)
termination_by n
decreasing_by omega

open Filter Topology

theorem main :
    (∀ n : ℕ, 0 < n → |(a n:ℝ)-(n:ℝ)/3| < Real.log ((n:ℝ)+1)) ∧
    Tendsto (fun n : ℕ => (a n:ℝ)/((n:ℝ)/3)) atTop (𝓝 1) := by
  sorry

end OMA.S_oeis_a076902
