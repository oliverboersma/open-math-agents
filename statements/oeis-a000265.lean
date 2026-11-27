import Mathlib

/-!
# A000265: Remove all factors of 2 from n; or largest odd divisor of n; or odd part of n.

Source: https://oeis.org/A000265
Credit: @iskan-ai

Paul Barry (Jan 29 2007), in the formula section of A000265:
  a(n) = Sum_{k=0..n} A127793(n,k)*floor((k+2)/2) (conjecture).
Sela Fried (Nov 14 2025) notes that the conjecture is true (Notes Num. Theor. Disc. Math. 32(2), 2026).

A127793 (offset 0, rows n ≥ 0, columns 0 ≤ k ≤ n) is the inverse of the lower triangular matrix
  t(n,k) = 1/floor((n+2)/2) if k ≤ n ≤ 2k, and 0 otherwise.
Since t is lower triangular with nonzero diagonal, row n of its inverse depends only on the
leading (n+1) × (n+1) block. So A127793(n,k) is read off the inverse of that block.

Indexing: A000265 has offset 1, while the triangle row n starts at n = 0. With these offsets the
identity holds as a(n+1) = Sum_{k=0..n} A127793(n,k)*floor((k+2)/2) for all n ≥ 0
(row 0 gives a(1) = 1, row 2 gives -1*1 + 2*2 = 3 = a(3)); the literal a(n) reading fails at n = 2,
where the sum is 3 but a(2) = 1. We state the shifted form, which the OEIS data confirms.
-/

namespace OMA.S_oeis_a000265

/-- A000265: the odd part of `n` (remove all factors of 2). -/
def a (n : ℕ) : ℕ := n / 2 ^ (n.factorization 2)

/-- The leading `N × N` block of the triangle `t(n,k) = 1/floor((n+2)/2)` if `k ≤ n ≤ 2k`, else 0. -/
def t (N : ℕ) : Matrix (Fin N) (Fin N) ℚ := fun i j =>
  if (j : ℕ) ≤ i ∧ (i : ℕ) ≤ 2 * j then 1 / (((i : ℕ) + 2) / 2 : ℕ) else 0

/-- A127793(n,k): entry `(n,k)` of the inverse of `t`, read off the leading `(n+1) × (n+1)` block. -/
noncomputable def A127793 (n k : ℕ) : ℚ :=
  if h : k ≤ n then (t (n + 1))⁻¹ ⟨n, Nat.lt_succ_self n⟩ ⟨k, Nat.lt_succ_of_le h⟩ else 0

/-- Barry's conjecture (proved by Fried), with the offsets of A000265 (1) and A127793 (0). -/
theorem main : ∀ n : ℕ,
    (a (n + 1) : ℚ) = ∑ k ∈ Finset.range (n + 1), A127793 n k * (((k + 2) / 2 : ℕ) : ℚ) := by
  sorry

end OMA.S_oeis_a000265
