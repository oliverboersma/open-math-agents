import Mathlib

/-!
# A224274: a(n) = binomial(4*n,n)/4

Source: https://oeis.org/A224274
Credit: @niclorusso

Conjecture (in the comments of A224274): a(n) == 1 (mod n^3) iff n is an odd prime.

Conventions:
* The sequence has offset 1: a(n) = binomial(4n, n) / 4 for n >= 1. The division is exact, since
  binomial(4n, n) = 4 * binomial(4n - 1, n - 1).
* The congruence is `Nat.ModEq (n ^ 3) (a n) 1`.
* n ranges over n >= 2. For n = 1 every integer is congruent to 1 modulo 1^3 = 1, so the
  equivalence would fail for the trivial reason that 1 is not prime; the conjecture is about the
  moduli n^3 with n > 1.
-/

namespace OMA.S_oeis_a224274

/-- A224274: `a n = binomial(4n, n) / 4` (an exact division for `n >= 1`). -/
def a (n : ℕ) : ℕ := (4 * n).choose n / 4

/-- The conjecture on A224274: for `n >= 2`, `a(n) == 1 (mod n^3)` if and only if `n` is an odd
prime. -/
theorem main : ∀ n : ℕ, 2 ≤ n → ((a n ≡ 1 [MOD n ^ 3]) ↔ (n.Prime ∧ Odd n)) := by
  sorry

end OMA.S_oeis_a224274
