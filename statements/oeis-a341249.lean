import Mathlib

/-!
# A341249: a(n) = floor(r*floor(s*n)), where r = 2 + sqrt(2) and s = sqrt(2).

Source: https://oeis.org/A341249
Credit: @canneyi

Conjecture (in the entry): `1 < r*s*n - a(n) < 2` for `n >= 1`.

Formalization notes:
* `r` and `s` are real numbers. `a n` is an integer: the floor of the real number
  `r * floor(s * n)`.
* Offset 1, as in the entry (data: 3, 6, 13, 17, 23, ...), so the statement is for `1 ≤ n`.
-/

namespace OMA.S_oeis_a341249

/-- `r = 2 + sqrt 2`. -/
noncomputable def r : ℝ := 2 + Real.sqrt 2

/-- `s = sqrt 2`. -/
noncomputable def s : ℝ := Real.sqrt 2

/-- `a(n) = floor(r * floor(s * n))`. -/
noncomputable def a (n : ℕ) : ℤ := ⌊r * (⌊s * (n : ℝ)⌋ : ℝ)⌋

theorem main : ∀ n : ℕ, 1 ≤ n →
    1 < r * s * (n : ℝ) - (a n : ℝ) ∧ r * s * (n : ℝ) - (a n : ℝ) < 2 := by
  sorry

end OMA.S_oeis_a341249
