import Mathlib

/-!
# A389789: Number of ways to write n as (2-(n mod 2))*p + q + q', where p and q are primes, and q' is the first prime after q.

Source: https://oeis.org/A389789
Credit: @divmxnd0x

Conjecture (Zhi-Wei Sun, stated in A389789):
(i) `a(2n+1) > 0` for all `n > 4`. In other words, any odd integer greater than 10 can be written as
the sum of a prime and two consecutive primes.
(ii) `a(2n) > 0` for all `n > 426`. In other words, any even number greater than 853 can be written
as `2p + q + q'`, where `p` and `q` are primes (and `q'` is the first prime after `q`).

Formalization notes:
* Two consecutive primes `q, q'` are `prime(k), prime(k+1)` for some `k ≥ 1`, where `prime(k)` is the
  `k`-th prime with `prime(1) = 2`, i.e. `Nat.nth Nat.Prime (k - 1)`.
* With this definition `a(1), ..., a(30)` agree with the data of A389789, and no `2n + 1` with
  `5 ≤ n < 1505` and no `2n` with `427 ≤ n < 1427` lacks a representation.
-/

namespace OMA.S_oeis_a389789

/-- The `k`-th prime, `prime 1 = 2`. -/
noncomputable def prime (k : ℕ) : ℕ :=
  Nat.nth Nat.Prime (k - 1)

/-- Sun's conjecture, parts (i) and (ii). -/
theorem main :
    (∀ n : ℕ, 4 < n → ∃ p k : ℕ, p.Prime ∧ 1 ≤ k ∧ 2 * n + 1 = p + prime k + prime (k + 1)) ∧
      ∀ n : ℕ, 426 < n → ∃ p k : ℕ, p.Prime ∧ 1 ≤ k ∧ 2 * n = 2 * p + prime k + prime (k + 1) := by
  sorry

end OMA.S_oeis_a389789
