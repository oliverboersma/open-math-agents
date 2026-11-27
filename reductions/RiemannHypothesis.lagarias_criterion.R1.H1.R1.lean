import OMAReductions.R_RiemannHypothesis_lagarias_criterion_R1
import Mathlib

/- Copyright (c) 2026 Jonas Whidden. All rights reserved.
Adapted from kimihiro64/Robin1984, e3697139babfe0f6cc7a76a08bf41a92aa7a2978,
Lagarias/Elementary.lean and Mathlib/Analysis/SpecialFunctions/Log/RatBounds.lean,
under the Apache-2.0 license.
-/
namespace OMA.R_RiemannHypothesis_lagarias_criterion_R1_H1_R1

open Real
open scoped ArithmeticFunction.sigma

/-- The forward Robin inequality in its standard form. -/
def H1 : Prop := RiemannHypothesis → ∀ n : ℕ, 5040 < n →
    (σ 1 n : ℝ) < exp eulerMascheroniConstant * n * log (log n)

/-- A finite rational certificate. The exponential truncation has 24 terms and the
logarithm is evaluated with 12 positive terms of the atanh expansion. -/
def H2 : Prop := ∀ n : ℕ, 2 ≤ n → n ≤ 5040 → ∃ q : ℚ, 1 ≤ q ∧ q ≤ harmonic n ∧
    (σ 1 n : ℚ) < q + (∑ i ∈ Finset.range 24, q^i / (i.factorial : ℚ)) *
      (2 * ∑ i ∈ Finset.range 12, ((q-1)/(q+1))^(2*i+1) / ((2*i+1 : ℕ) : ℚ))

theorem robinBound_le_exp_harmonic_mul_log_harmonic
    {n : Nat} (hn : 3 <= n) :
    Real.exp Real.eulerMascheroniConstant * (n : Real) *
        Real.log (Real.log (n : Real)) <=
      Real.exp (harmonic n : Real) * Real.log (harmonic n : Real) := by
  have hnPos : (0 : Real) < (n : Real) := by
    exact_mod_cast (by omega : 0 < n)
  have hnNe : Not (n = 0) := by omega
  have hGamma := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' n
  rw [Real.eulerMascheroniSeq', if_neg hnNe] at hGamma
  have hHarmonic :
      Real.log (n : Real) + Real.eulerMascheroniConstant <
        (harmonic n : Real) := by
    linarith
  have hExp :
      Real.exp Real.eulerMascheroniConstant * (n : Real) <=
        Real.exp (harmonic n : Real) := by
    calc
      Real.exp Real.eulerMascheroniConstant * (n : Real) =
          Real.exp (Real.eulerMascheroniConstant + Real.log (n : Real)) := by
        rw [Real.exp_add, Real.exp_log hnPos]
      _ <= Real.exp (harmonic n : Real) :=
        Real.exp_le_exp.mpr (by linarith)
  have hLogNOne : (1 : Real) < Real.log (n : Real) := by
    rw [Real.lt_log_iff_exp_lt hnPos]
    exact Real.exp_one_lt_three.trans_le (by exact_mod_cast hn)
  have hLogNPos : (0 : Real) < Real.log (n : Real) :=
    lt_trans zero_lt_one hLogNOne
  have hLogNLeHarmonic :
      Real.log (n : Real) <= (harmonic n : Real) := by
    have hCast : (n : Real) <= ((n + 1 : Nat) : Real) := by
      exact_mod_cast Nat.le_succ n
    exact (Real.log_le_log hnPos hCast).trans (log_add_one_le_harmonic n)
  have hLog :
      Real.log (Real.log (n : Real)) <=
        Real.log (harmonic n : Real) :=
    Real.log_le_log hLogNPos hLogNLeHarmonic
  exact mul_le_mul hExp hLog (Real.log_pos hLogNOne).le
    (Real.exp_pos _).le

theorem logSeriesLower_le_log {q : Rat} (hq : 1 ≤ q) (N : Nat) :
    ((2 * ∑ i ∈ Finset.range N, ((q - 1) / (q + 1)) ^ (2*i+1) / ((2*i+1 : ℕ) : ℚ) : ℚ) : ℝ) ≤ Real.log (q : Real) := by
  have hqR : (1 : Real) ≤ q := by exact_mod_cast hq
  have hDen : (0 : Real) < (q : Real) + 1 := by linarith
  have hz0 : (0 : Real) ≤ ((q : Real) - 1) / ((q : Real) + 1) :=
    div_nonneg (by linarith) hDen.le
  have hz1 : ((q : Real) - 1) / ((q : Real) + 1) < 1 := by
    apply (div_lt_one hDen).mpr
    linarith
  have hRatio :
      (1 + ((q : Real) - 1) / ((q : Real) + 1)) /
        (1 - ((q : Real) - 1) / ((q : Real) + 1)) = (q : Real) := by
    field_simp
    ring
  have h := Real.sum_range_le_log_div hz0 hz1 N
  rw [hRatio] at h
  push_cast
  linarith

theorem main : H1 → H2 → OMA.R_RiemannHypothesis_lagarias_criterion_R1.H1 := by
  intro robin cert rh n hn
  by_cases h : 5040 < n
  · have cmp := robinBound_le_exp_harmonic_mul_log_harmonic (n := n) (by omega)
    have hp : (0 : ℝ) ≤ harmonic n := by
      have : (0 : ℚ) ≤ harmonic n := by unfold harmonic; positivity
      exact_mod_cast this
    linarith [robin rh n h]
  · obtain ⟨q,hq,hqn,hnum⟩ := cert n (by omega) (by omega)
    have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hqH : (q : ℝ) ≤ harmonic n := by exact_mod_cast hqn
    let e : ℚ := ∑ i ∈ Finset.range 24, q^i / (i.factorial : ℚ)
    let l : ℚ := 2 * ∑ i ∈ Finset.range 12, ((q-1)/(q+1))^(2*i+1) / ((2*i+1 : ℕ) : ℚ)
    change (σ 1 n : ℚ) < q + e*l at hnum
    have he : (e : ℝ) ≤ exp (harmonic n) := by
      apply le_trans _ (exp_le_exp.mpr hqH)
      dsimp [e]
      push_cast
      exact sum_le_exp_of_nonneg (by linarith : (0 : ℝ) ≤ q) 24
    have hl : (l : ℝ) ≤ log (harmonic n) :=
      (logSeriesLower_le_log hq 12).trans (log_le_log (by linarith) hqH)
    have hl0 : (0 : ℝ) ≤ l := by
      have : 0 ≤ l := by
        dsimp [l]
        have : 0 ≤ (q-1)/(q+1) := div_nonneg (by linarith) (by linarith)
        positivity
      exact_mod_cast this
    have hm := mul_le_mul he hl hl0 (exp_pos _).le
    have hnumR : (σ 1 n : ℝ) < (q : ℝ) + (e : ℝ)*(l : ℝ) := by exact_mod_cast hnum
    linarith

end OMA.R_RiemannHypothesis_lagarias_criterion_R1_H1_R1
