import Mathlib

/-!
# A261437: Least positive integer k such that k*n+1 = prime(p) and k^2*n+1 = prime(q) for some pair of primes p and q.

Source: https://oeis.org/A261437
Credit: @divmxnd0x

Conjecture (Zhi-Wei Sun, stated in A261437):
(i) If `n > 0` and `r` are relatively prime integers, then there are infinitely many positive
integers `k` such that `k n + r = prime(p)` for some prime `p`.
(ii) Let `r` be 1 or -1. For any integer `n > 0`, there is a positive integer `k` such that
`k n + r = prime(p)` and `k^2 n + 1 = prime(q)` for some primes `p` and `q`.

(For `r = 1`, part (ii) says that `a(n)` exists for every `n > 0`.)

Formalization notes:
* `prime(t)` is the `t`-th prime with `prime(1) = 2`, i.e. `Nat.nth Nat.Prime (t - 1)`; the
  statements are taken in `ℤ`.
* With this definition `a(1), ..., a(4)` = 2, 1, 286, 1, matching the data of A261437.
-/

namespace OMA.S_oeis_a261437

/-- `x` is a prime whose index is prime: `x = prime(p)` with `p` prime. -/
def IsPrimeIndexedPrime (x : ℤ) : Prop :=
  ∃ p : ℕ, p.Prime ∧ x = (Nat.nth Nat.Prime (p - 1) : ℤ)

/-- Sun's conjectures of A261437, parts (i) and (ii). -/
theorem main :
    (∀ n : ℕ, 0 < n → ∀ r : ℤ, Int.gcd n r = 1 →
        {k : ℕ | 0 < k ∧ IsPrimeIndexedPrime ((k : ℤ) * n + r)}.Infinite) ∧
      ∀ r : ℤ, (r = 1 ∨ r = -1) → ∀ n : ℕ, 0 < n →
        ∃ k : ℕ, 0 < k ∧ IsPrimeIndexedPrime ((k : ℤ) * n + r) ∧
          IsPrimeIndexedPrime ((k : ℤ) ^ 2 * n + 1) := by
  sorry

end OMA.S_oeis_a261437
