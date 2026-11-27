import Mathlib

/-!
# A260219: Least prime p such that pi(p*n)^2 + 1 = prime(q*n) for some prime q.

Source: https://oeis.org/A260219
Credit: @divmxnd0x

Conjecture (Zhi-Wei Sun, stated in A260219): `a(n)` exists for any `n > 0`, i.e. for every `n ≥ 1`
there are primes `p, q` with `π(p n)^2 + 1 = prime(q n)`. In general, if `a, b, c` are integers with
`a > 0` and `gcd(a, b, c) = 1`, and `a + b` or `c` is odd, and `b^2 - 4ac` is not a square, then
there are primes `p` and `q` such that `a π(p n)^2 + b π(p n) + c = prime(q n)` (for every
positive integer `n`).

Formalization notes:
* `π(x)` is `Nat.primeCounting x`; `prime(t)` is the `t`-th prime with `prime(1) = 2`, i.e.
  `Nat.nth Nat.Prime (t - 1)`. The general statement is taken in `ℤ`.
* `gcd(a, b, c) = 1` is `Int.gcd (Int.gcd a b) c = 1`; "`a + b` or `c` is odd" is
  `Odd (a + b) ∨ Odd c`.
* With this definition `a(1), a(2), a(3)` = 3, 47, 229, matching the data of A260219.
-/

namespace OMA.S_oeis_a260219

/-- Sun's conjectures of A260219. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧
        Nat.primeCounting (p * n) ^ 2 + 1 = Nat.nth Nat.Prime (q * n - 1)) ∧
      ∀ a b c : ℤ, 0 < a → Int.gcd (Int.gcd a b) c = 1 → (Odd (a + b) ∨ Odd c) →
        ¬ IsSquare (b ^ 2 - 4 * a * c) → ∀ n : ℕ, 1 ≤ n →
          ∃ p q : ℕ, p.Prime ∧ q.Prime ∧
            a * Nat.primeCounting (p * n) ^ 2 + b * Nat.primeCounting (p * n) + c =
              (Nat.nth Nat.Prime (q * n - 1) : ℤ) := by
  sorry

end OMA.S_oeis_a260219
