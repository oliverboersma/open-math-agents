import Mathlib

/-!
# A129194: a(n) = (n/2)^2*(3 - (-1)^n).

Source: https://oeis.org/A129194
Credit: @marcelopierry

Wesley Ivan Hurt (Jul 11 2016), in the comments of A129194:
  Conjecture: denominator of 4/n - 2/n^2.
The sequence has offset 0, and 4/n - 2/n^2 is defined only for n ≥ 1, so the conjecture is
stated for n ≥ 1. The denominator is the reduced positive denominator (Rat.den).
-/

namespace OMA.S_oeis_a129194

/-- A129194: a(n) = (n/2)^2 * (3 - (-1)^n), computed in ℚ (its values are integers). -/
def a (n : ℕ) : ℚ := ((n : ℚ) / 2) ^ 2 * (3 - (-1) ^ n)

/-- Hurt's conjecture: for n ≥ 1, a(n) is the denominator of 4/n - 2/n^2. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n = (((4 : ℚ) / n - 2 / (n : ℚ) ^ 2).den : ℚ) := by
  sorry

end OMA.S_oeis_a129194
