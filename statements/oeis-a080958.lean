import Mathlib

/-!
# A080958: a(n) = n!*(2/1 - 3/2 + 4/3 - ... + s*(n+1)/n), where s = (-1)^(n+1)

Source: https://oeis.org/A080958
Credit: @ivillar

Paul Barry's sequence (offset 1): a(n) = n! * Sum_{j=1..n} (-1)^(j+1) * (j+1)/j.

Conjecture (R. J. Mathar, Sep 27 2012, corrected for offset 1 by Robert Israel, Dec 26 2018):
  -(n+1)*a(n+1) + a(n) + n^2*(n+2)*a(n-1) = 0.
It is stated for every n ≥ 2, so that all indices are at least the offset 1. The values are
integers; they are computed in ℚ.
-/

namespace OMA.S_oeis_a080958

/-- a(n) = n! * Sum_{j=1..n} (-1)^(j+1) * (j+1)/j. -/
noncomputable def a (n : ℕ) : ℚ :=
  (n.factorial : ℚ) * ∑ j ∈ Finset.Icc 1 n, (-1 : ℚ) ^ (j + 1) * ((j : ℚ) + 1) / j

/-- Mathar's recurrence, for every n ≥ 2. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    -((n : ℚ) + 1) * a (n + 1) + a n + (n : ℚ) ^ 2 * ((n : ℚ) + 2) * a (n - 1) = 0 := by
  sorry

end OMA.S_oeis_a080958
