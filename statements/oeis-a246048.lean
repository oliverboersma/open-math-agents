import Mathlib.Data.Nat.Choose.Factorization

/-!
# OEIS A246048

The sequence comprises the positive integers n such that
(n!)^n * (2n)! divides (n²)!. Its OEIS entry reports Farideh
Firoozbakht's observation that its terms are composite and asks
whether all prime powers are absent. The exponent k+1 below
includes primes themselves at k=0.

Source: https://oeis.org/A246048
Formalization: @ecirak42.
-/

namespace OMA.S_oeis_a246048

def isTerm (n : ℕ) : Prop :=
  n.factorial ^ n * (2 * n).factorial ∣ (n ^ 2).factorial

theorem main : ∀ p k : ℕ, p.Prime → ¬ isTerm (p ^ (k + 1)) := by
  sorry

end OMA.S_oeis_a246048
