import Mathlib

/-!
# Divisor of given order in short intervals

Source: https://mathoverflow.net/questions/437849 (G. Melfi, 2022).
Credit: @prasledi

The source asks: for sufficiently large x, is there at least one positive integer in the interval
[x, x + log^2 x] that has a divisor in the interval [x^(1/3), 2 x^(1/3)]?
The statement is the affirmative form. We read x as a real number, log as the natural logarithm,
and both intervals as closed, as written in the source. The weaker variants suggested at the end
of the post are not included.
-/

namespace OMA.S_mo_437849

theorem main : ∀ᶠ x : ℝ in Filter.atTop,
    ∃ n d : ℕ, 0 < n ∧ x ≤ (n : ℝ) ∧ (n : ℝ) ≤ x + Real.log x ^ 2 ∧
      d ∣ n ∧ x ^ ((1 : ℝ) / 3) ≤ (d : ℝ) ∧ (d : ℝ) ≤ 2 * x ^ ((1 : ℝ) / 3) := by
  sorry

end OMA.S_mo_437849
