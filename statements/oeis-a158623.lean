import Mathlib

/-!
# OEIS A158623: recurrence for the cubic-product denominators

The sequence starts at index 2. The recurrence is written with forward
indices so that all four sequence terms lie in the source domain.

Source: https://oeis.org/A158623
Conjecture: R. J. Mathar, March 27, 2009.
Formalization: @senamakel
-/

namespace OMA.S_oeis_a158623

/-- The product of the ratios of neighboring cubes. -/
def fraction (n : ℕ) : ℚ :=
  ∏ k ∈ Finset.Icc 2 n, (((k : ℚ)^3 - 1) / ((k : ℚ)^3 + 1))

/-- The reduced denominator of the product. -/
def term (n : ℕ) : ℕ := (fraction n).den

theorem main : ∀ n : ℕ, 2 ≤ n →
    (term (n+9) : ℤ) = 3*(term (n+6) : ℤ)-3*(term (n+3) : ℤ)+(term n : ℤ) := by
  sorry

end OMA.S_oeis_a158623
