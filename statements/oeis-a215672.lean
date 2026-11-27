import Mathlib

/-!
# A215672: Fermat pseudoprimes to base 2 with three prime factors

Source: https://oeis.org/A215672
Credit: @AkiRA-COM-FP

Formalizes the OEIS A215672 conjecture: every Poulet number `P` (composite `P >= 2`
with `2^(P - 1) ≡ 1 [MOD P]`) having at least three distinct prime divisors admits a
prime divisor `q` and a natural number `r` with `P = q * ((r + 1) * q - r)`.
(Known to fail at `P = 617093 = 43 * 113 * 127`.)
-/

namespace OMA.S_oeis_a215672

/-- A Poulet number is a composite integer `P >= 2` satisfying `2^(P - 1) ≡ 1 [MOD P]`. -/
def IsPoulet (P : ℕ) : Prop :=
  2 ≤ P ∧ ¬ P.Prime ∧ 2 ^ (P - 1) ≡ 1 [MOD P]

/-- Conjecture: every Poulet number with at least three distinct prime divisors has a
prime divisor `q` and `r : ℕ` such that `P = q * ((r + 1) * q - r)`. -/
theorem main :
    ∀ P : ℕ, IsPoulet P → 3 ≤ P.primeFactors.card →
      ∃ q ∈ P.primeFactors, ∃ r : ℕ, P = q * ((r + 1) * q - r) := by
  sorry

end OMA.S_oeis_a215672
