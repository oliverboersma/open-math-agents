import Mathlib

/-!
# A257928: Least prime p such that pi(p*n) = pi(q*n)*pi(r*n) for some primes q and r with p > q > r, where pi(x) denotes the number of primes not exceeding x.

Source: https://oeis.org/A257928
Credit: @divmxnd0x

Conjecture (Zhi-Wei Sun, stated in A257928): `a(n)` exists for any `n > 0`, i.e. for every `n ≥ 1`
there are primes `p > q > r` with `π(p n) = π(q n) π(r n)`. Also, for each positive integer `n`
there are distinct primes `p, q` and `r` such that `π(p n) = π(q n) + π(r n)`.

Formalization notes:
* `π(x)`, the number of primes not exceeding `x`, is `Nat.primeCounting x`.
* With this definition `a(1), ..., a(4)` = 13, 7, 13, 67, matching the data of A257928.
-/

namespace OMA.S_oeis_a257928

/-- Sun's conjectures of A257928. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ r < q ∧ q < p ∧
        Nat.primeCounting (p * n) = Nat.primeCounting (q * n) * Nat.primeCounting (r * n)) ∧
      ∀ n : ℕ, 1 ≤ n → ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p ≠ q ∧ p ≠ r ∧ q ≠ r ∧
        Nat.primeCounting (p * n) = Nat.primeCounting (q * n) + Nat.primeCounting (r * n) := by
  sorry

end OMA.S_oeis_a257928
