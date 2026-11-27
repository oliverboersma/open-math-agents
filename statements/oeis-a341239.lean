import Mathlib

/-!
# A341239: a(n) = floor(r*floor(s*n)), where r = 1 + sqrt(2) and s = sqrt(2)

Source: https://oeis.org/A341239
Credit: @xor2k

Formalizes the OEIS A341239 conjecture (offset 1): 1 < r*s*n - a(n) < 3 for n >= 1.

Conventions: `r = 1 + √2` and `s = √2` are real numbers (`Real.sqrt 2`), `floor` is
Mathlib's `Int.floor` on `ℝ`, and `a n` is an integer. The inner floor `⌊s*n⌋` is cast
back to `ℝ` before multiplying by `r`. The quantity `r*s*n - a(n)` is computed in `ℝ`,
and both strict inequalities are asserted for every `n : ℕ` with `1 ≤ n` (offset 1).
-/

namespace OMA.S_oeis_a341239

/-- `r = 1 + sqrt(2)`. -/
noncomputable def r : ℝ :=
  1 + Real.sqrt 2

/-- `s = sqrt(2)`. -/
noncomputable def s : ℝ :=
  Real.sqrt 2

/-- `a(n) = floor(r * floor(s * n))`. -/
noncomputable def a (n : ℕ) : ℤ :=
  ⌊r * (⌊s * (n : ℝ)⌋ : ℝ)⌋

/-- For every `n ≥ 1`, `1 < r*s*n - a(n) < 3`. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n → 1 < r * s * (n : ℝ) - (a n : ℝ) ∧ r * s * (n : ℝ) - (a n : ℝ) < 3 := by
  sorry

end OMA.S_oeis_a341239
