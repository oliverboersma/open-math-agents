import Mathlib

/-!
# Fractional parts of partial sums of natural logarithms

E. Joseph asked whether, for every positive ε, infinitely many N have
fractional part of the sum of log n from n = 2 to N less than ε.
Infinitely many natural indices are expressed by the existence of a witness
above every bound.

Source: https://math.stackexchange.com/q/2172922 (2017, CC BY-SA 3.0)
Credit: @ecirak42
-/

namespace OMA.S_mse_2172922

/-- The sum of log 2, ..., log N. -/
noncomputable def logSum (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 2 N, Real.log (j : ℝ)

theorem main : ∀ ε : ℝ, 0 < ε → ∀ B : ℕ, ∃ N : ℕ,
    B < N ∧ Int.fract (logSum N) < ε := by
  sorry

end OMA.S_mse_2172922
