import Mathlib

/-!
# A204235: Permanent of the n-th principal submatrix of A143182.

Source: https://oeis.org/A204235
Credit: @bnb9001

The n-th principal submatrix of A143182 is the `n × n` symmetric Toeplitz matrix whose first
row is 1, 2, ..., n, that is, the matrix with entries `|i - j| + 1` (Stefano Spezia). The
sequence has offset 1 and starts 1, 5, 42, 632, ...

Conjecture (Stefano Spezia, 2018): a(1) and a(2) are the only terms that are odd numbers.
Sela Fried notes that the conjecture is true.
-/

namespace OMA.S_oeis_a204235

/-- The `n × n` symmetric Toeplitz matrix with entries `|i - j| + 1`. -/
def toep (n : ℕ) : Matrix (Fin n) (Fin n) ℕ :=
  Matrix.of fun i j => Int.natAbs ((i : ℤ) - j) + 1

/-- A204235: the permanent of `toep n`. -/
def a (n : ℕ) : ℕ := (toep n).permanent

/-- For `n ≥ 1`, `a n` is odd exactly when `n = 1` or `n = 2`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → (Odd (a n) ↔ n = 1 ∨ n = 2) := by
  sorry

end OMA.S_oeis_a204235
