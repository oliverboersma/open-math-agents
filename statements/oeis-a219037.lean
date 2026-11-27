import Mathlib

/-!
# A219037: Numbers k such that k divides 2^k + 2 and (k-1) divides 2^k + 1.

Source: https://oeis.org/A219037
Credit: @mbilenko03

Conjecture (from the entry): `a(n+1) = 2^a(n) + 2` for all `n`.

The known terms are `2, 6, 66, 73786976294838206466 = 2^66 + 2`; the entry notes the sequence is
infinite (if `m` is a term then so is `2^m + 2`), so the conjecture says the terms are exactly the
iterates of `x ↦ 2^x + 2` starting from 2, with no other terms in between.

Conventions:
- A term is a natural number `k` with `k ∣ 2^k + 2` and `k - 1 ∣ 2^k + 1`. This excludes `k = 0`
  (`0 ∣ 3` fails) and `k = 1` (`0 ∣ 3` fails), so the smallest term is 2.
- `a(n)` (offset 1) is the `n`-th term in increasing order; with Mathlib's 0-indexed `Nat.nth`
  it is `Nat.nth IsTerm (n - 1)`. The index shift does not matter for a statement over all `n`.
-/

namespace OMA.S_oeis_a219037

/-- `k` divides `2^k + 2` and `k - 1` divides `2^k + 1`. -/
def IsTerm (k : ℕ) : Prop := k ∣ 2 ^ k + 2 ∧ k - 1 ∣ 2 ^ k + 1

theorem main : ∀ n : ℕ, Nat.nth IsTerm (n + 1) = 2 ^ Nat.nth IsTerm n + 2 := by
  sorry

end OMA.S_oeis_a219037
