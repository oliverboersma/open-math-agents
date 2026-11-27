import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.IsPrimePow

/-!
# OEIS A096127, exact powers of a factorial dividing the square-index factorial
Source: https://oeis.org/A096127 (Murthy, 2004; offset 2).
Credit: @garrytaulu

For n ≥ 2, the largest admissible exponent is n+1 precisely when n+1 is
admissible and n+2 is not. All admissible exponents form an initial segment.
The conjecture in this entry states the forward implication.
-/

namespace OMA.S_oeis_a096127

theorem main : ∀ n : ℕ, 2 ≤ n →
    (n.factorial ^ (n + 1) ∣ (n ^ 2).factorial) →
    ¬ (n.factorial ^ (n + 2) ∣ (n ^ 2).factorial) →
    IsPrimePow n := by
  sorry

end OMA.S_oeis_a096127
