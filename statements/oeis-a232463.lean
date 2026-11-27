import Mathlib

/-!
# A232463: Number of ways to write n = p + q - pi(q), where p and q are odd primes not exceeding n.

Source: https://oeis.org/A232463
Credit: @sntntHb

Here `pi(q)` is the number of primes not exceeding `q`.

Data: 0, 0, 0, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 3, ...

Conjecture (Zhi-Wei Sun, stated on the OEIS page): `a(n) > 0` for all `n > 3`, i.e. every
`n ≥ 4` can be written as `n = p + q - pi(q)` with `p` and `q` odd primes not exceeding `n`.

Conventions: `n = p + q - pi(q)` is written without truncated subtraction as
`n + pi(q) = p + q`.
-/

namespace OMA.S_oeis_a232463

theorem main :
    ∀ n : ℕ, 3 < n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ 2 ∧ q ≠ 2 ∧ p ≤ n ∧ q ≤ n ∧
      n + Nat.primeCounting q = p + q := by
  sorry

end OMA.S_oeis_a232463
