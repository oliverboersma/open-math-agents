import Mathlib

/-!
# A divisor-sum formula for totients of square divisors

Source: https://oeis.org/A055210
Credit: @anmolspace

For a positive integer n, A055210 sums Euler's totient over its square divisors.
In 2019 Velin Yanev conjectured that this equals the sum of the squared divisors
of its largest square divisor, divided by the sum of the divisors of that same square.
The largest square divisor is A008833. The OEIS gives a prime-power evaluation
of A055210 due to Vladeta Jovovic (2001).
-/

namespace OMA.S_oeis_a055210

/-- The largest square divisor, obtained by rounding every prime exponent down
to the nearest even integer. -/
def squarePart (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors, p ^ (2 * (n.factorization p / 2))

/-- The sum of Euler's totient over all square divisors. -/
noncomputable def a (n : ℕ) : ℕ := by
  classical
  exact ∑ d ∈ n.divisors with IsSquare d, d.totient

/-- Yanev's formula in cross-multiplied form. The divisor sum in the
denominator is positive for every positive input. -/
theorem main : ∀ n : ℕ, 0 < n →
    a n * ArithmeticFunction.sigma 1 (squarePart n) = ArithmeticFunction.sigma 2 (squarePart n) := by
  sorry

end OMA.S_oeis_a055210
