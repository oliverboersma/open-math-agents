import Mathlib

/-!
# A257364: Least prime p such that pi(p*n)^2 = pi(q*n)^2 + pi(r*n)^2 for some primes q and r, where pi(x) denotes the number of primes not exceeding x.

Source: https://oeis.org/A257364
Credit: @divmxnd0x

Conjecture (Zhi-Wei Sun, stated in A257364): `a(n)` exists for any `n > 0`. In other words, for each
fixed positive integer `n` the sequence `π(p n)` with `p` prime contains a Pythagorean triple.

Formalization notes:
* `π(x)` is `Nat.primeCounting x`.
* With this definition `a(1), ..., a(4)` = 11, 59, 47, 211, matching the data of A257364.
-/

namespace OMA.S_oeis_a257364

/-- Sun's conjecture: for every `n ≥ 1` there are primes `p, q, r` with
`π(p n)^2 = π(q n)^2 + π(r n)^2`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧
    Nat.primeCounting (p * n) ^ 2 = Nat.primeCounting (q * n) ^ 2 + Nat.primeCounting (r * n) ^ 2 := by
  sorry

end OMA.S_oeis_a257364
