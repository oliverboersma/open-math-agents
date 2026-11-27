import Mathlib

/-!
# The conjectured recurrence for OEIS A383702

Seiichi Manyama defined the sequence as the coefficient of degree two in a
product of linear factors. R. J. Mathar proposed the recurrence on May 7, 2025.
The first index at which all four terms are defined is three.

Source: https://oeis.org/A383702
Credit: @mmiranda2
-/

namespace OMA.S_oeis_a383702

open Polynomial

noncomputable def row (n : ℕ) : Polynomial ℤ :=
  ∏ j ∈ Finset.range n, (X + C (4 * (j : ℤ) + 3))

noncomputable def a (n : ℕ) : ℤ := (row n).coeff 2

theorem main : ∀ n : ℕ, 3 ≤ n →
    a n + 3 * (-4 * (n : ℤ) + 5) * a (n - 1) +
      (48 * (n : ℤ) ^ 2 - 168 * n + 151) * a (n - 2) -
      (4 * (n : ℤ) - 9) ^ 3 * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a383702
