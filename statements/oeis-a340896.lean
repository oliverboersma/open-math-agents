import Mathlib.NumberTheory.Divisors

/-!
# Squares in the divisor-count triangle A340896

Source: https://oeis.org/A340896 (J. Lowell, OEIS Foundation, CC BY-SA 4.0).

Row n consists of the positive multiples of n having fewer than twice as
many positive divisors as n. The entry conjectures that the row contains
n² precisely when n is a power of a prime. The cited sequence A000961
includes 1, so the exponent may be zero.
-/

namespace OMA.S_oeis_a340896

def row (n : ℕ) : Set ℕ :=
  {m | 0 < m ∧ n ∣ m ∧ m.divisors.card < 2 * n.divisors.card}

theorem main : ∀ n : ℕ, 0 < n →
    (n ^ 2 ∈ row n ↔ ∃ p e : ℕ, p.Prime ∧ n = p ^ e) := by
  sorry

end OMA.S_oeis_a340896
