import Mathlib

/-!
# A152020: Denominator of 8/(9*n^2) divided by 9.

Source: https://oeis.org/A152020
Credit: @marcelopierry

Andres Cicuttin (Sep 19 2017), in the formula section of A152020:
  Conjecture: a(n) = denominator((n-2)^3/n^2).
The sequence has offset 1, so the conjecture is stated for n ≥ 1. Denominators are reduced
positive denominators (Rat.den); (n-2)^3 is computed in ℚ, so n = 1 gives (-1)^3/1.
-/

namespace OMA.S_oeis_a152020

/-- A152020(n): the denominator of 8/(9*n^2), divided by 9. -/
def a (n : ℕ) : ℚ := (((8 : ℚ) / (9 * (n : ℚ) ^ 2)).den : ℚ) / 9

/-- Cicuttin's conjecture: for n ≥ 1, a(n) is the denominator of (n-2)^3/n^2. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n = (((((n : ℚ) - 2) ^ 3) / (n : ℚ) ^ 2).den : ℚ) := by
  sorry

end OMA.S_oeis_a152020
