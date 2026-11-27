import Mathlib

/-!
# OEIS A355175

Sun's closed formula for the determinant of a quadratic Toeplitz matrix
with one added to each diagonal entry. See Sela Fried, Section 3.9 of
https://arxiv.org/abs/2606.09913.
-/

open scoped BigOperators Matrix

namespace OMA.S_oeis_a355175

/-- The matrix whose determinant defines A355175. -/
def quadraticToeplitz (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => ((i.val : ℚ)-j.val)^2 + if i=j then 1 else 0

/-- The determinant sequence A355175. -/
def a (n : ℕ) : ℚ := (quadraticToeplitz n).det

/-- Sun's closed determinant formula for each size n, including the empty matrix. -/
theorem main :
    ∀ n : ℕ, a n =
      (((n:ℚ)^2-4)*((n:ℚ)^2+2*(n:ℚ)+3)*
        ((n:ℚ)^5-2*(n:ℚ)^4-(n:ℚ)^3-28*(n:ℚ)^2+60*(n:ℚ)-90))/1080 := by
  sorry

end OMA.S_oeis_a355175
