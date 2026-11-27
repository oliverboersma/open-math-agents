import Mathlib

/-!
# Palindromicity of the Verlinde-number polynomials in OEIS A398690

Source: https://oeis.org/A398690
Credit: @dwilfand-sys
-/

namespace OMA.S_oeis_a398690

/-- The coefficient `A(n + 3, k)` of the row generating series in the source. -/
noncomputable def rowValue (n k : ℕ) : ℝ :=
  (∑ j ∈ Finset.range (2 * k + 1),
    (-1 : ℝ) ^ ((n + 3) * j) /
      (Real.sin ((2 * (j : ℝ) + 1) * (2 * Real.pi) / (8 * (k : ℝ) + 4))) ^ (n + 1)) /
    (2 * (k : ℝ) + 1)

/-- The coefficient of degree `j` in the numerator obtained by multiplying the row
series by `(1 - z) ^ (n + 1)`. -/
noncomputable def numeratorCoeff (n j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (j + 1),
    (-1 : ℝ) ^ i * ((n + 1).choose i : ℝ) * rowValue n (j - i)

/-- The numerator in row `n` is supported in degrees `0` through `n`, as in the
source triangle, and its coefficients on that interval are symmetric. -/
theorem main : ∀ n j : ℕ,
    numeratorCoeff n j = if j ≤ n then numeratorCoeff n (n - j) else 0 := by
  sorry

end OMA.S_oeis_a398690
