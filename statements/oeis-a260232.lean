import Mathlib

/-!
# A260232: Least prime p such that pi(p*n) = n*pi(q*n) for some prime q.

Source: https://oeis.org/A260232
Credit: @divmxnd0x

Conjecture (Zhi-Wei Sun, stated in A260232): For any positive integer `n`, each rational number
`r > 0` can be written as `π(p n)/π(q n)` with `p` and `q` both prime. (The existence of `a(n)` is
the case `r = n`.)

Formalization notes:
* `π(x)` is `Nat.primeCounting x`; for primes `q` and `n ≥ 1`, `π(q n) ≥ 1`, so the quotient is a
  well-defined rational number.
* With this definition the least prime `p` with `π(p n) = n π(q n)` for some prime `q` is
  2, 5, 13, 67 for `n = 1, 2, 3, 4`, matching the data of A260232.
-/

namespace OMA.S_oeis_a260232

/-- Sun's conjecture: for every `n ≥ 1`, every positive rational is `π(p n)/π(q n)` with `p, q`
prime. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∀ r : ℚ, 0 < r →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ r = (Nat.primeCounting (p * n) : ℚ) / Nat.primeCounting (q * n) := by
  sorry

end OMA.S_oeis_a260232
