import Mathlib

/-!
# An ordinary divisor-sum formula for the unitary divisor sum

Source: https://oeis.org/A034448
Credit: @anmolspace

A unitary divisor d of n is a positive divisor coprime to its complementary
divisor n/d. For positive n, Velin Yanev conjectured in 2017 that the sum of
the unitary divisors equals σ(n² / rad(n)) / σ(n / rad(n)). Juan José Alba
González gave the multiplicative prime-power argument in the OEIS entry in 2021.
-/

namespace OMA.S_oeis_a034448

/-- Sum of the positive unitary divisors of n. -/
def unitarySum (n : ℕ) : ℕ :=
  ∑ d ∈ n.divisors with d.Coprime (n / d), d

/-- Yanev's exact ratio, cross-multiplied by its positive denominator. -/
theorem main : ∀ n : ℕ, 0 < n →
    unitarySum n * ArithmeticFunction.sigma 1 (n / UniqueFactorizationMonoid.radical n) =
      ArithmeticFunction.sigma 1 (n ^ 2 / UniqueFactorizationMonoid.radical n) := by
  sorry

end OMA.S_oeis_a034448
