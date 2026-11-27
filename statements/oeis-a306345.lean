import Mathlib

/-!
# Equal numbers of prime and composite divisors

Source: https://oeis.org/A306345
Credit: @anmolspace

A306345, contributed by Felix Fröhlich, counts the absolute difference between the
numbers of distinct prime and composite divisors of a positive integer. Its zero
set is conjectured to consist of 1 and the squares of primes (A001248). Charlie
Neder gave a divisor-count argument for this characterization in the entry in 2019.
-/

namespace OMA.S_oeis_a306345

/-- Removing 1 and the prime divisors from all positive divisors leaves the composites. -/
def a (n : ℕ) : ℕ :=
  Nat.dist n.primeFactors.card ((n.divisors.erase 1) \ n.primeFactors).card

/-- The zero terms occur exactly at 1 and at squares of primes. -/
theorem main : ∀ n : ℕ, 0 < n →
    (a n = 0 ↔ n = 1 ∨ ∃ p : ℕ, p.Prime ∧ n = p ^ 2) := by
  sorry

end OMA.S_oeis_a306345
