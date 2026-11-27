import OMAReductions.R_Transcendental_transcendental_eulerMascheroniConstant_or_gompertzConstant_R1

-- Step Transcendental.transcendental_eulerMascheroniConstant_or_gompertzConstant.R1.H1: hypothesis H1 of reduction Transcendental.transcendental_eulerMascheroniConstant_or_gompertzConstant.R1

/-!
Expand `exp (-t) = ∑ (-t)^n / n!` and integrate term by term over `(0, 1]` (dominated
convergence with the bound `|log t| / n!`). By the fundamental theorem of calculus applied to
`t^(n+1) log t / (n+1) - t^(n+1) / (n+1)^2`, which is continuous on `[0, 1]`,
`∫₀¹ t^n log t = -1 / (n+1)^2`, so the `n`-th term is `(-1)^(n+1) / ((n+1) (n+1)!)`.
-/

open MeasureTheory

namespace OMA

theorem integral_pow_mul_log (n : ℕ) :
    ∫ t in (0 : ℝ)..1, t ^ n * Real.log t = -1 / ((n : ℝ) + 1) ^ 2 := by
  have hn0 : (n : ℝ) + 1 ≠ 0 := by positivity
  have hcont : ContinuousOn (fun t : ℝ =>
      t ^ (n + 1) * Real.log t / ((n : ℝ) + 1) - t ^ (n + 1) / ((n : ℝ) + 1) ^ 2)
      (Set.Icc 0 1) := by
    have hG : (fun t : ℝ =>
        t ^ (n + 1) * Real.log t / ((n : ℝ) + 1) - t ^ (n + 1) / ((n : ℝ) + 1) ^ 2) =
        fun t : ℝ => t ^ n * (t * Real.log t) / ((n : ℝ) + 1) -
          t ^ (n + 1) / ((n : ℝ) + 1) ^ 2 := by
      funext t
      ring
    rw [hG]
    exact ((((continuous_pow n).mul Real.continuous_mul_log).div_const _).sub
      ((continuous_pow (n + 1)).div_const _)).continuousOn
  have hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt (fun t : ℝ =>
      t ^ (n + 1) * Real.log t / ((n : ℝ) + 1) - t ^ (n + 1) / ((n : ℝ) + 1) ^ 2)
      (t ^ n * Real.log t) t := by
    intro t ht
    have ht0 : t ≠ 0 := ht.1.ne'
    have h1 : HasDerivAt (fun t : ℝ => t ^ (n + 1)) (((n : ℝ) + 1) * t ^ n) t := by
      simpa using hasDerivAt_pow (n + 1) t
    have h2 := Real.hasDerivAt_log ht0
    have h5 := ((h1.mul h2).div_const ((n : ℝ) + 1)).sub (h1.div_const (((n : ℝ) + 1) ^ 2))
    have ht1 : t ^ (n + 1) * t⁻¹ = t ^ n := by
      rw [pow_succ, mul_assoc, mul_inv_cancel₀ ht0, mul_one]
    have hd : (((n : ℝ) + 1) * t ^ n * Real.log t + t ^ (n + 1) * t⁻¹) / ((n : ℝ) + 1) -
        ((n : ℝ) + 1) * t ^ n / ((n : ℝ) + 1) ^ 2 = t ^ n * Real.log t := by
      rw [ht1]
      field_simp <;> ring
    rw [← hd]
    exact h5
  have hint : IntervalIntegrable (fun t : ℝ => t ^ n * Real.log t) volume 0 1 :=
    intervalIntegral.intervalIntegrable_log'.continuousOn_mul (continuous_pow n).continuousOn
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont hderiv hint]
  show (1 : ℝ) ^ (n + 1) * Real.log 1 / ((n : ℝ) + 1) - (1 : ℝ) ^ (n + 1) / ((n : ℝ) + 1) ^ 2 -
      ((0 : ℝ) ^ (n + 1) * Real.log 0 / ((n : ℝ) + 1) - (0 : ℝ) ^ (n + 1) / ((n : ℝ) + 1) ^ 2) =
      -1 / ((n : ℝ) + 1) ^ 2
  rw [one_pow, Real.log_one, zero_pow (Nat.succ_ne_zero n)]
  ring

end OMA

theorem OMA.solution :
    OMA.R_Transcendental_transcendental_eulerMascheroniConstant_or_gompertzConstant_R1.H1 := by
  unfold OMA.R_Transcendental_transcendental_eulerMascheroniConstant_or_gompertzConstant_R1.H1
  have hsum : HasSum
      (fun n : ℕ => ∫ t in (0 : ℝ)..1, Real.log t * ((-t) ^ n / (n.factorial : ℝ)))
      (∫ t in (0 : ℝ)..1, Real.log t * Real.exp (-t)) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun (n : ℕ) (t : ℝ) => |Real.log t| * ((1 : ℝ) ^ n / (n.factorial : ℝ))) ?_ ?_ ?_ ?_ ?_
    · intro n
      exact (Real.measurable_log.mul
        ((measurable_neg.pow_const n).div_const _)).aestronglyMeasurable
    · intro n
      refine Filter.Eventually.of_forall (fun t ht => ?_)
      rw [Set.uIoc_of_le zero_le_one] at ht
      have hfac : (0 : ℝ) < (n.factorial : ℝ) := by positivity
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_div, abs_pow, abs_neg,
        Nat.abs_cast]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      rw [div_le_div_iff₀ hfac hfac]
      apply mul_le_mul_of_nonneg_right _ hfac.le
      apply pow_le_pow_left₀ (abs_nonneg t)
      rw [abs_of_pos ht.1]
      exact ht.2
    · exact Filter.Eventually.of_forall
        (fun t _ => (Real.summable_pow_div_factorial 1).mul_left _)
    · have e : (fun t : ℝ => ∑' n : ℕ, |Real.log t| * ((1 : ℝ) ^ n / (n.factorial : ℝ))) =
          fun t : ℝ => |Real.log t| * ∑' n : ℕ, (1 : ℝ) ^ n / (n.factorial : ℝ) := by
        funext t
        exact tsum_mul_left
      rw [e]
      exact (intervalIntegral.intervalIntegrable_log'.abs).mul_const _
    · refine Filter.Eventually.of_forall (fun t _ => ?_)
      have h := NormedSpace.expSeries_div_hasSum_exp (-t)
      rw [← Real.exp_eq_exp_ℝ] at h
      exact h.mul_left (Real.log t)
  have hterm : ∀ n : ℕ, ∫ t in (0 : ℝ)..1, Real.log t * ((-t) ^ n / (n.factorial : ℝ)) =
      (-1 : ℝ) ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1).factorial : ℝ)) := by
    intro n
    have e : (fun t : ℝ => Real.log t * ((-t) ^ n / (n.factorial : ℝ))) =
        fun t : ℝ => ((-1 : ℝ) ^ n / (n.factorial : ℝ)) * (t ^ n * Real.log t) := by
      funext t
      rw [neg_pow]
      ring
    rw [e, intervalIntegral.integral_const_mul, OMA.integral_pow_mul_log]
    have hf : ((n + 1).factorial : ℝ) = ((n : ℝ) + 1) * (n.factorial : ℝ) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    have hfac : (0 : ℝ) < (n.factorial : ℝ) := by positivity
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [hf, pow_succ, div_mul_div_comm, div_eq_div_iff (by positivity) (by positivity)]
    ring
  have hfun : (fun n : ℕ => ∫ t in (0 : ℝ)..1, Real.log t * ((-t) ^ n / (n.factorial : ℝ))) =
      fun n : ℕ => (-1 : ℝ) ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1).factorial : ℝ)) :=
    funext hterm
  rw [hfun, intervalIntegral.integral_of_le zero_le_one] at hsum
  exact hsum
