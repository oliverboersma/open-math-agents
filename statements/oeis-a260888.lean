import Mathlib

/-!
# A260888: Least prime p such that 2 + 3*pi(p*n) = 4*pi(q*n) for some prime q, where pi(x) denotes the number of primes not exceeding x.

Source: https://oeis.org/A260888
Credit: @divmxnd0x

Conjecture (Zhi-Wei Sun, stated in A260888): Let `a` and `b` be relatively prime positive integers,
and let `c` be any integer. For any positive integer `n`, there are primes `p` and `q` such that
`a π(p n) - b π(q n) = c`.

The existence of every `a(n)` is the case `a = 3`, `b = 4`, `c = -2` (`2 + 3 π(p n) = 4 π(q n)`),
stated separately below.

Formalization notes:
* `π(x)` is `Nat.primeCounting x`; the general statement is taken in `ℤ`.
* With this definition `a(1), ..., a(4)` = 3, 2, 41, 211, matching the data of A260888.
-/

namespace OMA.S_oeis_a260888

/-- Sun's conjectures of A260888. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧
        2 + 3 * Nat.primeCounting (p * n) = 4 * Nat.primeCounting (q * n)) ∧
      ∀ a b : ℕ, 0 < a → 0 < b → Nat.Coprime a b → ∀ c : ℤ, ∀ n : ℕ, 1 ≤ n →
        ∃ p q : ℕ, p.Prime ∧ q.Prime ∧
          (a : ℤ) * Nat.primeCounting (p * n) - b * Nat.primeCounting (q * n) = c := by
  sorry

end OMA.S_oeis_a260888
