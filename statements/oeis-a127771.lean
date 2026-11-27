import Mathlib

/-!
# OEIS A127771: the inverse of the triangle 1/phi(n+1) [k <= n <= 2k] has integer entries

Source: https://oeis.org/A127771 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A127771 (Paul Barry, Jan 28 2007), offset 0: Inverse of number triangle A(n,k) =
1/Euler_phi(n+1) if k <= n <= 2k, 0 otherwise. Comment: It is conjectured that all elements of the
triangle are integers.

Formalization notes:
* The triangle A(n,k), n, k >= 0, is lower triangular with diagonal entries 1/phi(n+1), which are
  nonzero, so it has a lower triangular inverse, and entry (n,k) of that inverse depends only on
  the rows and columns 0..N of A for any N >= n. The conjecture is therefore stated for every
  truncation: for every N, every entry of the inverse of the matrix A N with rows and columns
  0..N is an integer. Each A N is invertible, so the inverse `⁻¹` is the true inverse.
* Controls from the entry: the inverse of A 4 is the matrix of the listed rows 0..4, namely
  [1], [0, 1], [0, -1, 2], [0, 1, -2, 2], [0, 0, 0, -2, 4].
-/

namespace OMA.S_oeis_a127771

variable (N : ℕ)

/-- The truncation to rows and columns 0..N of the triangle 1/phi(n+1) if k <= n <= 2k. -/
def A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℚ := fun i j =>
  if (j : ℕ) ≤ i ∧ (i : ℕ) ≤ 2 * j then 1 / ((i : ℕ) + 1).totient else 0

/-- Barry's conjecture: all elements of the inverse triangle are integers. -/
theorem main : ∀ N : ℕ, ∀ i j : Fin (N + 1), ∃ z : ℤ, (A N)⁻¹ i j = z := by
  sorry

end OMA.S_oeis_a127771
