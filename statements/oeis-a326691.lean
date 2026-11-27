import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Rat.Cast.Order

/-!
# Karttunen's gcd formula for the denominator of a prime reciprocal sum

Source: https://oeis.org/A326691
Credit: @anmolspace

The factorization formula for the arithmetic derivative is the one given
in OEIS A003415. In the reciprocal sum, each distinct prime occurs once.
-/

namespace OMA.S_oeis_a326691

open Finset

/-- The arithmetic derivative, using the prime multiplicities of n. -/
def arithmeticDerivative (n : ℕ) : ℕ :=
  ∑ p ∈ n.primeFactors, n.factorization p * (n / p)

/-- The defining quotient for A326691 uses the positive reduced denominator. -/
def sequence (n : ℕ) : ℕ :=
  n / ((∑ p ∈ n.primeFactors, (1 : ℚ) / p) - 1 / (n : ℚ)).den

/-- Karttunen's formula for every index of the sequence, beginning with 1. -/
theorem main : ∀ n : ℕ, 0 < n →
    sequence n = Nat.gcd n (1 + (n - 1) * arithmeticDerivative n) := by
  sorry

end OMA.S_oeis_a326691
