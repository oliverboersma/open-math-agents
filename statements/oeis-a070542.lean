import Mathlib

/-!
# A070542: Numbers n such that binomial(2n,n) does not have two prime factors that add to 2n.

Source: https://oeis.org/A070542
Credit: @divmxnd0x

Conjecture (T. D. Noe, Dec 23 2004): there are no other `n` with this property than the terms
1, 2, 3, 4, 6, 10, 15, 26, 28, 64 (none for `n < 10^8`).

Formalization notes:
* "Two prime factors" means two distinct primes `p ≠ q` dividing `binomial(2n, n)`: with `p = q`
  allowed, `n = 2` (where `2 + 2 = 4` and `2 ∣ 6`) would not be a term, but it is listed.
* The sequence consists of positive integers, so `n ≥ 1`.
* With this definition the `n` in `1 ≤ n ≤ 400` without such primes are exactly 1, 2, 3, 4, 6, 10,
  15, 26, 28, 64.
-/

namespace OMA.S_oeis_a070542

/-- Noe's conjecture: the `n ≥ 1` such that `binomial(2n, n)` has no two distinct prime factors
adding up to `2n` are exactly 1, 2, 3, 4, 6, 10, 15, 26, 28, 64. -/
theorem main :
    {n : ℕ | 1 ≤ n ∧ ¬ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p ∣ Nat.choose (2 * n) n ∧
        q ∣ Nat.choose (2 * n) n ∧ p + q = 2 * n} =
      {1, 2, 3, 4, 6, 10, 15, 26, 28, 64} := by
  sorry

end OMA.S_oeis_a070542
