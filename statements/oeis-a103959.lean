import Mathlib

/-!
# OEIS A103959: minimum prime p such that prime(n)*p - 2 is prime

Source: https://oeis.org/A103959 (OEIS Foundation, CC BY-SA 4.0)
Credit: @sntntHb

The sequence (offset 1) gives the minimum prime `p` such that `prime(n)*p - 2` is prime
(e.g. `a(1) = 2` because `2*2 - 2 = 2` is prime). The entry records the comment:

  Conjecture: a(n) <= prime(n). Tested to n=10000.

Since `a(n)` is the least prime with the property, the conjecture says exactly that some
prime `p ≤ prime(n)` has the property. We formalize it that way, with `prime(n)` the `n`-th
prime (`Nat.nth Nat.Prime (n - 1)`, so that `prime(1) = 2`).
-/

namespace OMA.S_oeis_a103959

/-- The `n`-th prime, one-indexed: `prime 1 = 2`. -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- For every `n ≥ 1` there is a prime `p ≤ prime(n)` with `prime(n)*p - 2` prime. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    ∃ p : ℕ, p.Prime ∧ p ≤ prime n ∧ (prime n * p - 2).Prime := by
  sorry

end OMA.S_oeis_a103959
