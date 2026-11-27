import Mathlib

/-!
# A000122: Expansion of Jacobi theta function theta3(x) = Sum{m =-oo..oo} x^(m^2) (number of integer solutions to k^2 = n).

Source: https://oeis.org/A000122
Credit: @rot13maxi

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a000122

/-- A000122: coefficients of the Jacobi theta function `theta_3`,
i.e. the number of integer solutions of `k^2 = n`.
OEIS gives `a(0) = 1`, and for `n > 0`, `a(n) = 2` if `n` is a square and `0` otherwise.
`Nat.sqrt n ^ 2 = n` is the standard decidable test for `n` being a square. -/
def a (n : ℕ) : ℕ :=
  if n = 0 then 1 else if Nat.sqrt n ^ 2 = n then 2 else 0

/-- Simon Plouffe's conjecture (OEIS A000122, Sep 09 2025):
`Sum_{k>=0} a(k) / exp(k*Pi) = Pi^(1/4) / Gamma(3/4)`. -/
theorem main :
    (∑' k : ℕ, (a k : ℝ) / Real.exp (k * Real.pi)) =
      Real.pi ^ (1 / 4 : ℝ) / Real.Gamma (3 / 4 : ℝ) := by
  sorry

end OMA.S_oeis_a000122

