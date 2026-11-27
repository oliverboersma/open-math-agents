import Mathlib

/-!
# OEIS A086222

John W. Layman's two conjectures of September 1, 2003 count positive triples
in nondecreasing order with a prescribed least common multiple. The first
case uses distinct primes, since the second case treats their squares.

Source: https://oeis.org/A086222
Credit: @Iraeeee
-/

namespace OMA.S_oeis_a086222

/-- Every coordinate of a positive triple with lcm n divides n. -/
def a (n : ℕ) : ℕ :=
  ∑ x ∈ n.divisors, ∑ y ∈ n.divisors, ∑ z ∈ n.divisors,
    if x ≤ y ∧ y ≤ z ∧ Nat.lcm x (Nat.lcm y z) = n then 1 else 0

theorem main :
    (∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → a (p*q) = 13) ∧
    (∀ p : ℕ, p.Prime → a (p^2) = 6) := by
  sorry

end OMA.S_oeis_a086222
