import Mathlib

/-!
# OEIS A119936: row denominator LCM of the cubic Cesàro matrix

A119936 is the least common multiple of the reduced denominators in row
`n` of the cube of the lower triangular matrix whose nonzero row-`i`
entries are all `1/i`. Indices start at 1.

Source: https://oeis.org/A119936
Formalization: @senamakel
-/

namespace OMA.S_oeis_a119936

/-- The entry in row `n` and column `j` of the matrix cube. -/
def entry (n j : ℕ) : ℚ :=
  (1 / (n : ℚ)) * ∑ i ∈ Finset.Icc j n,
    (1 / (i : ℚ)) * ∑ k ∈ Finset.Icc j i, (1 / (k : ℚ))

/-- The conjecture after clearing the factor `n^3`, using `n ∣ lcm(1,...,n)`. -/
theorem main : ∀ n : ℕ, 0 < n →
    (Finset.Icc 1 n).lcm (fun j => (entry n j).den) =
      n * ((Finset.Icc 1 n).lcm id)^2 := by
  sorry

end OMA.S_oeis_a119936
