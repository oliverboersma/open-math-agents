import Mathlib

/-!
# OEIS A355326

Sun's cubic determinant formula and the general polynomial conjecture.
Both are proved in Sela Fried, Section 3.9 of https://arxiv.org/abs/2606.09913.
-/

open scoped BigOperators Matrix Polynomial

namespace OMA.S_oeis_a355326

/-- The Toeplitz matrix with its diagonal increased by one. -/
def powerToeplitz (m n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => ((i.val:ℚ)-j.val)^m + if i=j then 1 else 0

/-- The cubic determinant sequence in A355326. -/
def a (n : ℕ) : ℚ := (powerToeplitz 3 n).det

/-- The polynomial in the first conjecture, evaluated at a rational number. -/
def cubicQuotient (x : ℚ) : ℚ :=
  x^6-19*x^5+123*x^4-337*x^3+12376*x^2-44144*x+40000

/-- The explicit cubic determinant formula and the general degree and factorization. -/
theorem main :
    (∀ n : ℕ, a n = 1 + cubicQuotient ((n:ℚ)^2)*(n:ℚ)^2*((n:ℚ)^2-1)/672000) ∧
    (∀ m : ℕ, 0 < m → ∃ P : ℚ[X], P ≠ 0 ∧ P.natDegree = (m+1)^2-4 ∧
      ∀ n : ℕ, 0 < n → (powerToeplitz m n).det =
        1 + (n:ℚ)^2*((n:ℚ)^2-1)*P.eval (n:ℚ)) := by
  sorry

end OMA.S_oeis_a355326
