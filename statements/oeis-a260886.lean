import Mathlib

/-!
# A260886: Least prime p such that 3 + 4*prime(p*n) = 5*prime(q*n) for some prime q.

Source: https://oeis.org/A260886
Credit: @divmxnd0x

Conjecture (Zhi-Wei Sun, stated in A260886): Let `a, b, c` be pairwise relatively prime positive
integers with `a + b + c` even and `a ≠ b`. Then, for any positive integer `n`, there are primes `p`
and `q` such that `a prime(p n) - b prime(q n) = c`.

The existence of every `a(n)` (`3 + 4 prime(p n) = 5 prime(q n)`, i.e.
`5 prime(q n) - 4 prime(p n) = 3`) is the case `a = 5`, `b = 4`, `c = 3` of the general statement
(with the names of the two primes exchanged); it is stated separately below.

Formalization notes:
* `prime(t)` is the `t`-th prime with `prime(1) = 2`, i.e. `Nat.nth Nat.Prime (t - 1)`; the general
  statement is taken in `ℤ`.
* With this definition `a(1), a(2), a(3)` = 2, 157, 199, matching the data of A260886.
-/

namespace OMA.S_oeis_a260886

/-- The `t`-th prime, `prime 1 = 2`. -/
noncomputable def prime (t : ℕ) : ℕ :=
  Nat.nth Nat.Prime (t - 1)

/-- Sun's conjectures of A260886. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 3 + 4 * prime (p * n) = 5 * prime (q * n)) ∧
      ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c → Nat.Coprime a b → Nat.Coprime a c → Nat.Coprime b c →
        Even (a + b + c) → a ≠ b → ∀ n : ℕ, 1 ≤ n →
          ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ (a : ℤ) * prime (p * n) - b * prime (q * n) = c := by
  sorry

end OMA.S_oeis_a260886
