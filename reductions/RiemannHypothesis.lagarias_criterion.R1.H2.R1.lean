import OMAReductions.R_RiemannHypothesis_lagarias_criterion_R1
import Mathlib

/-! Lagarias' converse follows from the power-scale oscillation in Robin's
1984 theorem and an elementary upper bound for the harmonic expression.
Their remainders differ by a power of log n. -/
namespace OMA.R_RiemannHypothesis_lagarias_criterion_R1_H2_R1

open Real Filter
open scoped ArithmeticFunction.sigma

/-- Positive excursions of the divisor sum under failure of RH, in the form
of the oscillation conclusion of Robin's Theorem 1. -/
def H1 : Prop := ¬ RiemannHypothesis → ∃ b c : ℝ, 0 < b ∧ b < 1/2 ∧ 0 < c ∧
    ∃ᶠ n : ℕ in atTop, exp eulerMascheroniConstant * n * log (log n) +
      c * n / (log n)^b ≤ (σ 1 n : ℝ)

/-- The uniform elementary harmonic-number bound from the converse argument. -/
def H2 : Prop := ∀ n : ℕ, 20 ≤ n →
    (harmonic n : ℝ) + exp (harmonic n) * log (harmonic n) ≤
    exp eulerMascheroniConstant * n * log (log n) + 24 * n / log n

theorem main : H1 → H2 → OMA.R_RiemannHypothesis_lagarias_criterion_R1.H2 := by
  intro oscillation upper lag
  by_contra neg
  obtain ⟨b,c,_,hb,hc,large⟩ := oscillation neg
  have hl : Tendsto (fun n : ℕ => log (n : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hp : Tendsto (fun n : ℕ => (log (n : ℝ))^(1-b)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith : 0 < 1-b)).comp hl
  obtain ⟨n,hosc,hn,hs⟩ := (large.and_eventually
    ((eventually_ge_atTop 20).and (hp.eventually_gt_atTop (24/c)))).exists
  have hn1 : 1 < n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hx : 0 < log (n : ℝ) := log_pos (by exact_mod_cast hn1)
  have hxb := Real.rpow_pos_of_pos hx b
  have hsplit : (log (n : ℝ))^(1-b) = log n / (log n)^b := by
    rw [Real.rpow_sub hx, Real.rpow_one]
  change 24 / c < (log (n : ℝ))^(1-b) at hs
  rw [hsplit, div_lt_div_iff₀ hc hxb] at hs
  have hcmp : 24 * (n : ℝ) / log n < c*n/(log n)^b := by
    apply (div_lt_div_iff₀ hx hxb).mpr
    have := mul_lt_mul_of_pos_right hs hn0
    linarith only [this]
  linarith [lag n hn1, upper n hn]

end OMA.R_RiemannHypothesis_lagarias_criterion_R1_H2_R1
