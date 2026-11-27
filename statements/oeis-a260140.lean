import Mathlib

/-!
# A260140: Least prime p such that pi(p*n) = pi(q*n)^2 for some prime q, where pi(x) denotes the number of primes not exceeding x.

Source: https://oeis.org/A260140
Credit: @divmxnd0x

Let `T(n) = {π(p n) : p is prime}`.

Conjecture (Zhi-Wei Sun, stated in A260140): `a(n)` exists for any `n > 0`, i.e. for every `n ≥ 1`
there are primes `p, q` with `π(p n) = π(q n)^2`. In general, for any integers `a, b, c, n` with
`a > 0` and `n > 0`, there are two elements `x` and `y` of `T(n)` with `a x^2 + b x + c = y`.
Supplement (Sun, Aug 02 2015): for any integers `b, c, n` with `b > 0` and `n > 0`, we have
`b x + c = y` for some elements `x` and `y` of `T(n)`.

Formalization notes:
* `π(x)` is `Nat.primeCounting x`; the general statements are taken in `ℤ`.
* With this definition `a(1), a(2), a(3)` = 2, 5, 19, matching the data of A260140.
-/

namespace OMA.S_oeis_a260140

/-- The set `{π(p n) : p prime}` as a set of integers. -/
def T (n : ℕ) : Set ℤ :=
  {x | ∃ p : ℕ, p.Prime ∧ x = Nat.primeCounting (p * n)}

/-- Sun's conjectures of A260140. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧
        Nat.primeCounting (p * n) = Nat.primeCounting (q * n) ^ 2) ∧
      (∀ a b c : ℤ, 0 < a → ∀ n : ℕ, 1 ≤ n →
        ∃ x ∈ T n, ∃ y ∈ T n, a * x ^ 2 + b * x + c = y) ∧
      ∀ b c : ℤ, 0 < b → ∀ n : ℕ, 1 ≤ n → ∃ x ∈ T n, ∃ y ∈ T n, b * x + c = y := by
  sorry

end OMA.S_oeis_a260140
