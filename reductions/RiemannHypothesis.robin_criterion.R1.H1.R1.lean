import OMAReductions.R_RiemannHypothesis_robin_criterion_R1

/-!
# Finite and analytic ranges of Robin's forward implication

The finite certificate concerns the divisor-sum inequality through the
cutoff used in the existing Robin formalization. Beyond that cutoff it
suffices to bound the logarithm of the divisor-sum ratio under RH.
-/

namespace OMA.R_RiemannHypothesis_robin_criterion_R1_H1_R1

open Real
open scoped ArithmeticFunction.sigma

def H1 : Prop :=
  ∀ n : ℕ, 5040 < n → log n ≤ exp 30 →
    σ 1 n < exp eulerMascheroniConstant * n * log (log n)

def H2 : Prop :=
  RiemannHypothesis → ∀ n : ℕ, 5040 < n → exp 30 < log n →
    log ((σ 1 n : ℝ) / n) < eulerMascheroniConstant + log (log (log n))

theorem main : H1 → H2 → OMA.R_RiemannHypothesis_robin_criterion_R1.H1 := by
  intro hfinite hanalytic hRH n hn
  by_cases h : log n ≤ exp 30
  · exact hfinite n hn h
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hσpos : (0 : ℝ) < σ 1 n := by
    have : 0 < σ 1 n := by rw [ArithmeticFunction.sigma_pos_iff]; omega
    exact_mod_cast this
  have hlog : 1 < log n := by
    have hexp := add_one_le_exp (30 : ℝ)
    linarith [lt_of_not_ge h]
  have hlt := exp_lt_exp.mpr (hanalytic hRH n hn (lt_of_not_ge h))
  rw [exp_log (div_pos hσpos hn0), exp_add, exp_log (log_pos hlog)] at hlt
  rw [div_lt_iff₀ hn0] at hlt
  simpa only [mul_assoc, mul_comm (log (log n)) (n : ℝ)] using hlt

end OMA.R_RiemannHypothesis_robin_criterion_R1_H1_R1
