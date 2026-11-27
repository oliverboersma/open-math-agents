import Mathlib.Data.Nat.Fib.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Integrality of the inverse Fibonacci triangle (OEIS A127711)

Paul Barry, January 24, 2007. Source: https://oeis.org/A127711
Lean formalization by @DomTheDeveloper.

Rows and columns start at zero. The finite leading blocks of a lower triangular
matrix with nonzero diagonal have compatible inverses, so every entry of the
infinite inverse occurs in a finite leading block.
-/

namespace OMA.S_oeis_a127711

/-- Rows 0 through N and columns 0 through N of Barry's rational triangle. -/
def triangle (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℚ := fun i j =>
  if j.val ≤ i.val ∧ i.val ≤ 2 * j.val then (Nat.fib (i.val + 1) : ℚ)⁻¹ else 0

/-- Every entry of every leading block's rational inverse is an integer. -/
theorem main : ∀ (N : ℕ) (i j : Fin (N + 1)),
    ∃ z : ℤ, (triangle N)⁻¹ i j = (z : ℚ) := by
  sorry

end OMA.S_oeis_a127711
