import Mathlib

/-!
# A174349: Square array: row n gives the indices i for which prime(i+1) = prime(i) + 2n; read by falling antidiagonals.

Source: https://oeis.org/A174349
Credit: @max-otc

Row n (n ≥ 1) of the array lists the indices i ≥ 1 with prime(i+1) = prime(i) + 2n, where prime(i) is the
i-th prime (prime(1) = 2, OEIS indexing; here prime(i) = Nat.nth Nat.Prime (i - 1)).
Statement: every positive integer except 1 occurs in the array, i.e. a positive integer i lies in some
row n ≥ 1 exactly when i ≠ 1. (M. F. Hasler, Oct 19 2018, notes that i appears in row
(prime(i+1) - prime(i))/2. The remark on Polignac's conjecture, that every row is infinite, is not part of
this statement.)
-/

namespace OMA.S_oeis_a174349

/-- The i-th prime, 1-indexed: prime 1 = 2, prime 2 = 3, prime 3 = 5, ... -/
noncomputable def prime (i : ℕ) : ℕ := Nat.nth Nat.Prime (i - 1)

/-- Row n of A174349: the indices i ≥ 1 with prime(i+1) = prime(i) + 2n. -/
def row (n : ℕ) : Set ℕ := {i | 1 ≤ i ∧ prime (i + 1) = prime i + 2 * n}

/-- Every positive integer except 1 occurs in some row n ≥ 1 of the array. -/
theorem main : ∀ i : ℕ, 1 ≤ i → ((∃ n : ℕ, 1 ≤ n ∧ i ∈ row n) ↔ i ≠ 1) := by
  sorry

end OMA.S_oeis_a174349
