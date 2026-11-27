import Mathlib

/-!
# A261361: Primes p such that 2*prime(p) + 1 = prime(q) for some prime q.

Source: https://oeis.org/A261361
Credit: @divmxnd0x

Conjecture (Zhi-Wei Sun, stated in A261361): The sequence contains infinitely many terms. In
general, if `a, b, c` are positive integers with `gcd(a, b) = gcd(a, c) = gcd(b, c) = 1`, and
`a + b + c` is even and `a` is not equal to `b`, then there are infinitely many prime pairs `{p, q}`
such that `a prime(p) - b prime(q) = c`.

Formalization notes:
* `prime(k)` is the `k`-th prime with `prime(1) = 2`, i.e. `Nat.nth Nat.Prime (k - 1)`. The general
  statement is taken in `ℤ`.
* "Infinitely many prime pairs `{p, q}`" is stated as: the set of pairs `(p, q)` of primes satisfying
  the equation is infinite.
* With this definition the terms below 600 are 3, 13, 173, 463, 523, matching the data of A261361.
-/

namespace OMA.S_oeis_a261361

/-- The `k`-th prime, `prime 1 = 2`. -/
noncomputable def prime (k : ℕ) : ℕ :=
  Nat.nth Nat.Prime (k - 1)

/-- Sun's conjectures of A261361. -/
theorem main :
    {p : ℕ | p.Prime ∧ ∃ q : ℕ, q.Prime ∧ 2 * prime p + 1 = prime q}.Infinite ∧
      ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c → Nat.Coprime a b → Nat.Coprime a c → Nat.Coprime b c →
        Even (a + b + c) → a ≠ b →
          {pq : ℕ × ℕ | pq.1.Prime ∧ pq.2.Prime ∧
            (a : ℤ) * prime pq.1 - b * prime pq.2 = c}.Infinite := by
  sorry

end OMA.S_oeis_a261361
