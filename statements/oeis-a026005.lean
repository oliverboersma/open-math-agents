import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Cast.Defs

/-!
# A recurrence for OEIS A026005

This is R. J. Mathar's May 2013 conjecture for the Catalan-triangle sequence
A026005. We use Ralf Stephan's binomial formula, recorded in the same entry.
Both the coefficients and the terms are viewed in ℚ so that subtraction is exact.
The substitution n = k + 2 runs through every index for which the three terms exist.

Source: https://oeis.org/A026005
Credit: @erood (Lean formalization with Codex)
-/

namespace OMA.S_oeis_a026005

def a (n : ℕ) : ℚ :=
  (2 * (n : ℚ) + 2) / (3 * (n : ℚ) + 2) * ((4 * n + 1).choose n : ℚ)

theorem main : ∀ k : ℕ, let n : ℚ := (k : ℚ) + 2
    9 * n * (3 * n + 2) * (3 * n + 1) * a (k + 2) +
    12 * (-55 * n ^ 3 - 59 * n ^ 2 + 65 * n - 11) * a (k + 1) -
    32 * (4 * n - 5) * (4 * n - 3) * (2 * n - 3) * a k = 0 := by
  sorry

end OMA.S_oeis_a026005
