import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Factorization.Basic

/-!
# The arithmetic derivative of a hyperfactorial

Source: https://oeis.org/A260619
Credit: @anmolspace

Matthew Campbell's sequence differentiates the hyperfactorial H(n).
The conjectured formula is H(n) times the sum of the arithmetic derivatives
of the integers from 1 to n. The empty sum extends the formula to H(0) = 1.
-/

namespace OMA.S_oeis_a260619

/-- The arithmetic derivative, expressed using the exponent of each prime divisor. -/
def arithmeticDerivative (n : ℕ) : ℕ :=
  ∑ p ∈ n.primeFactors, n.factorization p * (n / p)

/-- A002109, the product of `k ^ k` for `1 ≤ k ≤ n`. -/
def hyperfactorial : ℕ → ℕ
  | 0 => 1
  | n + 1 => hyperfactorial n * (n + 1) ^ (n + 1)

/-- The partial sums A190121, with value zero for the empty sum. -/
def derivativeSum (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, arithmeticDerivative (i + 1)

theorem main : ∀ n : ℕ,
    arithmeticDerivative (hyperfactorial n) = hyperfactorial n * derivativeSum n := by
  sorry

end OMA.S_oeis_a260619
