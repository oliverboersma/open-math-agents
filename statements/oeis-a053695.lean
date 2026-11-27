import Mathlib

/-!
# A053695: Differences between record prime gaps.

Source: https://oeis.org/A053695
Credit: @mbilenko03

Conjecture (John W. Nicholson, Dec 30 2015): `a(n) ≤ A005250(n)`, where A005250 is the sequence
of record gaps between primes and `a(n) = A005250(n+1) - A005250(n)`. The entry notes that this is
equivalent to `A005250(n+1) / A005250(n) ≤ 2`, and it is stated in that form:
`A005250(n+1) ≤ 2 * A005250(n)` for every `n`.

Conventions:
- As in A005250, a gap is `prime(k+1) - prime(k)` (not `prime(k+1) - prime(k) - 1`). Here
  `prime k = Nat.nth Nat.Prime k`, so `prime 0 = 2` and `gap 0 = 1`.
- A gap `gap k` is a record when it is larger than every earlier gap `gap i`, `i < k`.
  Record gaps increase strictly with `k`, so enumerating the set of record values in increasing
  order with `Nat.nth` gives A005250 in order: `recordGap 0 = 1`, `recordGap 1 = 2`,
  `recordGap 2 = 4`, … (A005250 has offset 1, so `recordGap n = A005250(n+1)`; the shift does not
  affect a statement quantified over all `n`).
-/

namespace OMA.S_oeis_a053695

/-- The gap `prime(k+1) - prime(k)` after the `k`-th prime (0-indexed: `prime 0 = 2`). -/
noncomputable def gap (k : ℕ) : ℕ := Nat.nth Nat.Prime (k + 1) - Nat.nth Nat.Prime k

/-- `gap k` is a record: it exceeds every earlier gap. -/
def IsRecord (k : ℕ) : Prop := ∀ i < k, gap i < gap k

/-- The record gaps between primes in increasing order (OEIS A005250, shifted to start at 0). -/
noncomputable def recordGap (n : ℕ) : ℕ := Nat.nth (fun g => ∃ k, IsRecord k ∧ gap k = g) n

theorem main : ∀ n : ℕ, recordGap (n + 1) ≤ 2 * recordGap n := by
  sorry

end OMA.S_oeis_a053695
