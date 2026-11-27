import Mathlib

/-!
# A361904: Odd numbers k such that for all even divisors d of k^2+1, d^2+1 is a prime number.

Source: https://oeis.org/A361904
Credit: @LAPRAI

Formalizes the OEIS comment: Conjecture: the sequence is infinite.

Conventions: divisors are positive divisors of `k^2 + 1` (natural numbers dividing it).
-/

namespace OMA.S_oeis_a361904

/-- There are infinitely many odd `k` such that `d^2 + 1` is prime for every even divisor `d` of `k^2 + 1`. -/
theorem main : {k : ℕ | Odd k ∧ ∀ d : ℕ, d ∣ k ^ 2 + 1 → Even d → (d ^ 2 + 1).Prime}.Infinite := by
  sorry

end OMA.S_oeis_a361904
