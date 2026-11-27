import Mathlib

/-!
# A341254: a(n) = floor(r * floor(r * n)), where r = (2 + sqrt(5)) / 2

Source: https://oeis.org/A341254
Credit: @AkiRA-COM-FP

Formalizes the OEIS A341254 conjecture: for every `n >= 1`,
`1/4 < n * r^2 - a(n) < 3`, where `r = (2 + sqrt(5)) / 2` and `a(n) = floor(r * floor(r * n))`.
-/

namespace OMA.S_oeis_a341254

/-- Constant `r = (2 + sqrt(5)) / 2`. -/
noncomputable def r : ℝ :=
  (2 + Real.sqrt 5) / 2

/-- Sequence `a(n) = floor(r * floor(r * n))`. -/
noncomputable def a (n : ℕ) : ℤ :=
  ⌊r * (⌊r * (n : ℝ)⌋ : ℝ)⌋

/-- For every `n >= 1`, `1/4 < n * r^2 - a(n) < 3`. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n →
      (1 : ℝ) / 4 < (n : ℝ) * r ^ 2 - (a n : ℝ) ∧
        (n : ℝ) * r ^ 2 - (a n : ℝ) < 3 := by
  sorry

end OMA.S_oeis_a341254
