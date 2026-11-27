import Mathlib

/-!
# A356493: Permanent of a symmetric Toeplitz matrix whose first row consists of prime(n), prime(n-1), ..., prime(1).

Source: https://oeis.org/A356493
Credit: @bnb9001

The sequence has offset 0 (1, 2, 13, 271, ...). `M(n)` is the `n × n` symmetric Toeplitz matrix
with first row prime(n), prime(n-1), ..., prime(1), so its entry in row `i`, column `j` is
prime(n - |i - j|). With Mathlib's 0-indexed `Nat.nth Nat.Prime` (so prime(k) is
`Nat.nth Nat.Prime (k - 1)`), that entry is `Nat.nth Nat.Prime (n - 1 - |i - j|)`.

Conjecture: a(n) is prime only for n = 1, 2, and 3. Robert Israel notes that the conjecture is
true.
-/

namespace OMA.S_oeis_a356493

/-- The symmetric Toeplitz matrix whose first row is `prime(n), prime(n-1), ..., prime(1)`. -/
noncomputable def toep (n : ℕ) : Matrix (Fin n) (Fin n) ℕ :=
  Matrix.of fun i j => Nat.nth Nat.Prime (n - 1 - Int.natAbs ((i : ℤ) - j))

/-- A356493: the permanent of `toep n`. -/
noncomputable def a (n : ℕ) : ℕ := (toep n).permanent

/-- `a n` is prime exactly when `n = 1`, `2` or `3`. -/
theorem main : ∀ n : ℕ, (a n).Prime ↔ n = 1 ∨ n = 2 ∨ n = 3 := by
  sorry

end OMA.S_oeis_a356493
