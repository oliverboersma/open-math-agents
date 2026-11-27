import Mathlib

/-!
# Erdős Problem 1150

Source: https://www.erdosproblems.com/1150
Credit: @mattdorman

The source asks: does there exist a constant `c > 0` such that, for all large `n` and all
polynomials `P` of degree `n` with coefficients `±1`,
`max_{|z| = 1} |P(z)| > (1 + c) √n`?

Reading used here: `P` has degree `n` and each of its `n + 1` coefficients (of `z⁰, …, zⁿ`) is
`1` or `-1`. The maximum over the unit circle is attained (the circle is compact), so
`max_{|z|=1} |P(z)| > X` is stated as the existence of `z` with `‖z‖ = 1` and `‖P(z)‖ > X`.
The statement below is the affirmative answer.
-/

open Filter

namespace OMA.S_erdos_1150

theorem main :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, ∀ P : Polynomial ℂ, P.natDegree = n →
      (∀ i ≤ n, P.coeff i = 1 ∨ P.coeff i = -1) →
        ∃ z : ℂ, ‖z‖ = 1 ∧ (1 + c) * Real.sqrt n < ‖P.eval z‖ := by
  sorry

end OMA.S_erdos_1150
