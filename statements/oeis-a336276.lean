import Mathlib

/-!
# A336276: a(n) = Sum_{k=1..n} mu(k)*k^2.

Source: https://oeis.org/A336276
Credit: @LAPRAI

Formalizes the OEIS comment: Conjecture: a(n) changes sign infinitely often.

Conventions: offset 1; `mu` is `ArithmeticFunction.moebius`. Changing sign infinitely often is
stated as: `a(n) > 0` for arbitrarily large `n` and `a(n) < 0` for arbitrarily large `n`.
-/

namespace OMA.S_oeis_a336276

/-- `a(n) = Sum_{k=1..n} mu(k) * k^2`. -/
def a (n : ℕ) : ℤ := ∑ k ∈ Finset.Icc 1 n, ArithmeticFunction.moebius k * (k : ℤ) ^ 2

/-- `a(n)` takes positive values and negative values for arbitrarily large `n`. -/
theorem main : (∀ N : ℕ, ∃ n : ℕ, N < n ∧ 0 < a n) ∧ (∀ N : ℕ, ∃ n : ℕ, N < n ∧ a n < 0) := by
  sorry

end OMA.S_oeis_a336276
