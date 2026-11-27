import Mathlib

/-!
# A387043: Number of ways to write n as (1 + (n mod 2))*p + prime(k) + prime(k+1) + prime(k+2), where p is a prime and k is a positive integer.

Source: https://oeis.org/A387043
Credit: @divmxnd0x

Conjecture (Zhi-Wei Sun, stated in A387043):
(i) `a(2n) > 0` for all `n > 12`. In other words, any even number greater than 25 is the sum of a
prime and three consecutive primes.
(ii) `a(2n+1) > 0` for all `n > 135`. In other words, any odd number greater than 272 can be written
as the sum of twice a prime and three consecutive primes.

Formalization notes:
* `prime(k)` is the `k`-th prime with `prime(1) = 2`, i.e. `Nat.nth Nat.Prime (k - 1)`, and `k ≥ 1`.
* With this definition `a(1), ..., a(40)` agree with the data of A387043, and no `2n` with
  `13 ≤ n < 1513` and no `2n + 1` with `136 ≤ n < 1536` lacks a representation.
-/

namespace OMA.S_oeis_a387043

/-- The `k`-th prime, `prime 1 = 2`. -/
noncomputable def prime (k : ℕ) : ℕ :=
  Nat.nth Nat.Prime (k - 1)

/-- Sun's conjecture, parts (i) and (ii). -/
theorem main :
    (∀ n : ℕ, 12 < n → ∃ p k : ℕ, p.Prime ∧ 1 ≤ k ∧
        2 * n = p + prime k + prime (k + 1) + prime (k + 2)) ∧
      ∀ n : ℕ, 135 < n → ∃ p k : ℕ, p.Prime ∧ 1 ≤ k ∧
        2 * n + 1 = 2 * p + prime k + prime (k + 1) + prime (k + 2) := by
  sorry

end OMA.S_oeis_a387043
