import Mathlib

/-!
# A292082: Primes p such that (p^2 - 1) / 2 is a square (A000290).

Source: https://oeis.org/A292082
Credit: @LAPRAI

Formalizes the OEIS comment: Conjecture: sequence is finite.

Conventions: `(p^2 - 1) / 2` is a square means `p^2 - 1 = 2 * k^2` for some natural `k`
(for an odd prime this is an exact division; for `p = 2` the quotient is not an integer).
-/

namespace OMA.S_oeis_a292082

/-- The set of primes `p` such that `(p^2 - 1) / 2` is a perfect square is finite. -/
theorem main : {p : ℕ | p.Prime ∧ ∃ k : ℕ, p ^ 2 - 1 = 2 * k ^ 2}.Finite := by
  sorry

end OMA.S_oeis_a292082
