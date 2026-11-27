import Mathlib

/-!
# A225004: a(n) is the largest multiple of n with fewer than twice as many divisors as n.

Source: https://oeis.org/A225004
Credit: @LAPRAI

Formalizes the OEIS comment: Conjecture: a(n) is always a divisor of n^2.

Conventions: offset 1. The number of divisors is `Nat.divisors.card`. `a(n)` is stated through
`IsGreatest`: any greatest element of the set of multiples `m` of `n` with
`#divisors(m) < 2 * #divisors(n)` divides `n^2`.
-/

namespace OMA.S_oeis_a225004

/-- Multiples of `n` with fewer than twice as many divisors as `n`. -/
def S (n : ℕ) : Set ℕ :=
  {m | n ∣ m ∧ 0 < m ∧ m.divisors.card < 2 * n.divisors.card}

/-- For every `n ≥ 1`, the largest element of `S n` divides `n^2`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∀ m : ℕ, IsGreatest (S n) m → m ∣ n ^ 2 := by
  sorry

end OMA.S_oeis_a225004
