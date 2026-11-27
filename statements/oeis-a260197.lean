import Mathlib

/-!
# A260197: Least prime p such that pi(p*n) = prime(q*n) for some prime q, where pi(x) denotes the number of primes not exceeding x.

Source: https://oeis.org/A260197
Credit: @divmxnd0x

Conjecture (Zhi-Wei Sun, stated in A260197): `a(n)` exists for any `n > 0`, i.e. for every `n ≥ 1`
there are primes `p` and `q` with `π(p n) = prime(q n)`. Also, for any `n > 0`, there are primes
`p` and `q` such that `π(p n) = q n`.

Formalization notes:
* `π(x)` is `Nat.primeCounting x`; `prime(m)` is the `m`-th prime with `prime(1) = 2`, i.e.
  `Nat.nth Nat.Prime (m - 1)`.
* With this definition `a(1), ..., a(4)` = 5, 277, 29, 17, matching the data of A260197.
-/

namespace OMA.S_oeis_a260197

/-- Sun's conjectures of A260197. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧
        Nat.primeCounting (p * n) = Nat.nth Nat.Prime (q * n - 1)) ∧
      ∀ n : ℕ, 1 ≤ n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ Nat.primeCounting (p * n) = q * n := by
  sorry

end OMA.S_oeis_a260197
