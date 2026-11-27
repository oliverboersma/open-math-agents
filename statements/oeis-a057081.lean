import Mathlib

/-!
# A057081 and Peter Bala's alternating series

The sequence consists of the even-indexed Chebyshev polynomials of the second
kind evaluated at sqrt(11)/2. Its first terms, starting at index 0, are 1,
10, 89 and 791. Peter Bala stated the general alternating-series conjecture
on 8 June 2025. The summation index in the source starts at 1, so the term
indexed by j in the finite sum below is the source term with n = j + 1.

Source: https://oeis.org/A057081
Credit: @ecirak42
-/

namespace OMA.S_oeis_a057081

noncomputable def a (n : ℕ) : ℝ :=
  (Polynomial.Chebyshev.U ℝ (2 * (n : ℤ))).eval (Real.sqrt 11 / 2)

noncomputable def s (k : ℕ) : ℝ := ∑ j ∈ Finset.range k, a j

noncomputable def term (k n : ℕ) : ℝ :=
  (-1 : ℝ) ^ (n + 1) / (a (k * n) - s k / a (k * n))

/-- The partial sums of Bala's series converge to the stated value for every positive k. -/
theorem main : ∀ k : ℕ, 1 ≤ k →
    Filter.Tendsto (fun N => ∑ j ∈ Finset.range N, term k (j + 1))
      Filter.atTop (nhds (1 / (1 + a k))) := by
  sorry

end OMA.S_oeis_a057081
