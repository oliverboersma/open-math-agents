import OMAReductions.R_SkewesNumber_littlewood_pi_minus_li_infinite_sign_changes_R1
import Mathlib

/-!
Step SkewesNumber.littlewood_pi_minus_li_infinite_sign_changes.R1.H2

For `x ≥ 3` put `n = ⌊x⌋₊`, so `3 ≤ n ≤ x < n + 1`. The two values of the logarithmic
integral share the constant `logIntegralTwo` and differ by the integral of `1 / log t` over
`[n, x]`. On that interval the integrand lies between `0` and `1`, because `log t ≥ log 3 > 1`,
so the integral lies between `0` and `x - n < 1`.
-/

theorem OMA.solution : OMA.R_SkewesNumber_littlewood_pi_minus_li_infinite_sign_changes_R1.H2 := by
  intro x hx
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hn3 : (3 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by
    have h : (3 : ℕ) ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
    exact_mod_cast h
  have hnx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0
  have hxn : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
  -- The integrand is continuous, hence integrable, on every interval to the right of 2.
  have hint : ∀ a b : ℝ, 2 ≤ a → a ≤ b →
      IntervalIntegrable (fun t : ℝ => 1 / Real.log t) MeasureTheory.volume a b := by
    intro a b ha hab
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hab]
    refine ContinuousOn.div continuousOn_const (Real.continuousOn_log.mono ?_) ?_
    · intro t ht
      have h0 : (0 : ℝ) < t := by linarith [ht.1]
      exact Set.mem_compl_singleton_iff.mpr h0.ne'
    · intro t ht
      exact (Real.log_pos (by linarith [ht.1])).ne'
  -- The difference is the integral over the interval from the floor to `x`.
  have hdiff : Real.logIntegral x - Real.logIntegral (⌊x⌋₊ : ℝ) =
      ∫ t in ((⌊x⌋₊ : ℝ))..x, 1 / Real.log t := by
    unfold Real.logIntegral
    rw [add_sub_add_left_eq_sub]
    exact intervalIntegral.integral_interval_sub_left (hint 2 x le_rfl (by linarith))
      (hint 2 _ le_rfl (by linarith))
  rw [hdiff]
  have hlog3 : (1 : ℝ) < Real.log 3 :=
    (Real.lt_log_iff_exp_lt (by norm_num)).mpr (by linarith [Real.exp_one_lt_d9])
  constructor
  · refine intervalIntegral.integral_nonneg hnx fun t ht => ?_
    have h0 : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
    exact div_nonneg zero_le_one h0.le
  · have hmono : ∫ t in ((⌊x⌋₊ : ℝ))..x, 1 / Real.log t ≤
        ∫ _t in ((⌊x⌋₊ : ℝ))..x, (1 : ℝ) := by
      refine intervalIntegral.integral_mono_on hnx (hint _ _ (by linarith) hnx)
        intervalIntegrable_const fun t ht => ?_
      have h3t : (3 : ℝ) ≤ t := by linarith [ht.1]
      have h1 : Real.log 3 ≤ Real.log t := Real.log_le_log (by norm_num) h3t
      rw [div_le_one (by linarith)]
      linarith
    have hconst : ∫ _t in ((⌊x⌋₊ : ℝ))..x, (1 : ℝ) = x - (⌊x⌋₊ : ℝ) := by simp
    linarith
