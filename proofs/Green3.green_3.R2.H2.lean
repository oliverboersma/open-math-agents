import OMAReductions.R_Green3_green_3_R2
import Mathlib

/-! The integral argument of Franchi, Gowers and Yip (Section 2): write the measure of
`exp(-B)` as the integral of `e^{-b}` over `B`, integrate the hypothesis against `e^{-u}`
over `u > 0`, and swap the integrals; the three shifted terms give `e^{-δ}`, `1` and `e^{δ}`
times that integral, while the right side gives `Γ(2) = 1`. -/

open Set MeasureTheory Real Filter

namespace G3R2H2

lemma lint_exp_Ioi (a : ℝ) :
    ∫⁻ u in Ioi a, ENNReal.ofReal (rexp (-u)) = ENNReal.ofReal (rexp (-a)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_neg_Ioi a)
    (ae_of_all _ fun u => (exp_pos _).le), integral_exp_neg_Ioi]

lemma shift (B : Set ℝ) (hB : MeasurableSet B) (hB0 : ∀ b ∈ B, 0 ≤ b) (c : ℝ) :
    ∫⁻ u in Ioi 0, ENNReal.ofReal (rexp (-u)) * volume (B ∩ Icc 0 (u + c)) =
      ∫⁻ b in B, ENNReal.ofReal (rexp (-max 0 (b - c))) := by
  have h1 : ∀ u : ℝ, volume (B ∩ Icc 0 (u + c)) = ∫⁻ b in B, (Iic (u + c)).indicator 1 b := by
    intro u
    rw [lintegral_indicator_one measurableSet_Iic, Measure.restrict_apply measurableSet_Iic]
    congr 1
    ext b
    constructor
    · rintro ⟨hb, _, hle⟩
      exact ⟨hle, hb⟩
    · rintro ⟨hle, hb⟩
      exact ⟨hb, hB0 b hb, hle⟩
  simp_rw [h1, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [lintegral_lintegral_swap]
  · apply setLIntegral_congr_fun hB
    intro b _
    have e : (fun u : ℝ => ENNReal.ofReal (rexp (-u)) * (Iic (u + c)).indicator 1 b) =
        (Ici (b - c)).indicator (fun u => ENNReal.ofReal (rexp (-u))) := by
      funext u
      simp only [Set.indicator_apply, Set.mem_Ici, Set.mem_Iic, Pi.one_apply]
      by_cases h : b - c ≤ u
      · rw [if_pos (by linarith), if_pos h, mul_one]
      · rw [if_neg (by linarith), if_neg h, mul_zero]
    dsimp only
    rw [e, lintegral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici]
    rcases le_or_gt (b - c) 0 with h | h
    · have hs : Ici (b - c) ∩ Ioi 0 = Ioi 0 := by
        ext u
        simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ioi]
        constructor
        · exact fun hu => hu.2
        · exact fun hu => ⟨by linarith, hu⟩
      rw [hs, lint_exp_Ioi, max_eq_left h]
    · have hs : Ici (b - c) ∩ Ioi 0 = Ici (b - c) := by
        ext u
        simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ioi]
        constructor
        · exact fun hu => hu.1
        · exact fun hu => ⟨hu, by linarith⟩
      rw [hs, setLIntegral_congr Ioi_ae_eq_Ici.symm, lint_exp_Ioi, max_eq_right h.le]
  · apply Measurable.aemeasurable
    apply Measurable.mul
    · exact (measurable_exp.comp measurable_fst.neg).ennreal_ofReal
    · have hm : MeasurableSet {p : ℝ × ℝ | p.2 ≤ p.1 + c} :=
        measurableSet_le measurable_snd (measurable_fst.add_const c)
      have e : (fun a : ℝ × ℝ => (Iic (a.1 + c)).indicator (1 : ℝ → ENNReal) a.2) =
          {p : ℝ × ℝ | p.2 ≤ p.1 + c}.indicator (fun _ => (1 : ENNReal)) := by
        funext p
        by_cases h : p.2 ≤ p.1 + c <;> simp [Set.indicator, h]
      rw [e]
      exact measurable_const.indicator hm

lemma vol_mono_meas (B : Set ℝ) (c : ℝ) :
    Measurable fun u : ℝ => ENNReal.ofReal (rexp (-u)) * volume (B ∩ Icc 0 (u + c)) := by
  apply Measurable.mul (measurable_exp.comp measurable_neg).ennreal_ofReal
  apply Monotone.measurable
  intro u v huv
  apply measure_mono
  intro b hb
  exact ⟨hb.1, hb.2.1, by linarith [hb.2.2]⟩

end G3R2H2

open G3R2H2 in
theorem OMA.solution : OMA.R_Green3_green_3_R2.H2 := by
  intro B δ ⟨s, hs⟩ hleast hδ hineq
  have hBm : MeasurableSet B := by
    rw [hs]
    exact Finset.measurableSet_biUnion s (fun p _ => measurableSet_Icc)
  have hBδ : ∀ b ∈ B, δ ≤ b := fun b hb => hleast.2 hb
  have hB0 : ∀ b ∈ B, 0 ≤ b := fun b hb => hδ.le.trans (hBδ b hb)
  set F : ℝ → ENNReal := fun v => volume (B ∩ Icc 0 v) with hF
  have hFfin : ∀ v, F v ≠ ⊤ := by
    intro v
    exact ne_top_of_le_ne_top (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
      (measure_mono inter_subset_right)
  set W : ENNReal := ∫⁻ b in B, ENNReal.ofReal (rexp (-b)) with hW
  -- pointwise inequality in ENNReal
  have hpt : ∀ u ∈ Ioi (0:ℝ), ENNReal.ofReal (rexp (-u)) * (F (u + -δ) + F (u + 0) + F (u + δ)) ≤
      ENNReal.ofReal (rexp (-u) * u ^ ((2:ℝ) - 1)) := by
    intro u hu
    have hu0 : (0:ℝ) ≤ u := le_of_lt hu
    have h := hineq u hu0
    simp only [Measure.real] at h
    have e1 : F (u + -δ) + F (u + 0) + F (u + δ) =
        ENNReal.ofReal ((F (u + -δ)).toReal + (F (u + 0)).toReal + (F (u + δ)).toReal) := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_toReal (hFfin _), ENNReal.ofReal_toReal (hFfin _),
        ENNReal.ofReal_toReal (hFfin _)]
    rw [e1, ← ENNReal.ofReal_mul (exp_pos _).le]
    apply ENNReal.ofReal_le_ofReal
    have : (2:ℝ) - 1 = 1 := by norm_num
    rw [this, Real.rpow_one]
    apply mul_le_mul_of_nonneg_left _ (exp_pos _).le
    simpa only [hF, add_zero, ← sub_eq_add_neg] using h
  have hint : ∫⁻ u in Ioi (0:ℝ), ENNReal.ofReal (rexp (-u) * u ^ ((2:ℝ) - 1)) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal (Real.GammaIntegral_convergent (by norm_num))
      ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun u hu => by
        have : (0:ℝ) < u := hu
        positivity)),
      ← Real.Gamma_eq_integral (by norm_num), Real.Gamma_two, ENNReal.ofReal_one]
  have hle : ∫⁻ u in Ioi (0:ℝ), ENNReal.ofReal (rexp (-u)) * (F (u + -δ) + F (u + 0) + F (u + δ))
      ≤ 1 := by
    rw [← hint]
    exact setLIntegral_mono' measurableSet_Ioi hpt
  have hsplit : ∫⁻ u in Ioi (0:ℝ), ENNReal.ofReal (rexp (-u)) * (F (u + -δ) + F (u + 0) + F (u + δ))
      = (∫⁻ u in Ioi (0:ℝ), ENNReal.ofReal (rexp (-u)) * F (u + -δ)) +
        (∫⁻ u in Ioi (0:ℝ), ENNReal.ofReal (rexp (-u)) * F (u + 0)) +
        (∫⁻ u in Ioi (0:ℝ), ENNReal.ofReal (rexp (-u)) * F (u + δ)) := by
    simp_rw [mul_add]
    rw [lintegral_add_right _ (vol_mono_meas B δ), lintegral_add_right _ (vol_mono_meas B 0)]
  have hm1 : ∫⁻ u in Ioi (0:ℝ), ENNReal.ofReal (rexp (-u)) * F (u + -δ) =
      ENNReal.ofReal (rexp (-δ)) * W := by
    rw [shift B hBm hB0, hW, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply setLIntegral_congr_fun hBm
    intro b hb
    have hb0 := hB0 b hb
    dsimp only
    rw [← ENNReal.ofReal_mul (exp_pos _).le, ← Real.exp_add, max_eq_right (by linarith)]
    congr 2
    ring
  have hm2 : ∫⁻ u in Ioi (0:ℝ), ENNReal.ofReal (rexp (-u)) * F (u + 0) = W := by
    rw [shift B hBm hB0, hW]
    apply setLIntegral_congr_fun hBm
    intro b hb
    dsimp only
    rw [sub_zero, max_eq_right (hB0 b hb)]
  have hm3 : ∫⁻ u in Ioi (0:ℝ), ENNReal.ofReal (rexp (-u)) * F (u + δ) =
      ENNReal.ofReal (rexp δ) * W := by
    rw [shift B hBm hB0, hW, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply setLIntegral_congr_fun hBm
    intro b hb
    have hb1 := hBδ b hb
    dsimp only
    rw [← ENNReal.ofReal_mul (exp_pos _).le, ← Real.exp_add, max_eq_right (by linarith)]
    congr 2
    ring
  rw [hsplit, hm1, hm2, hm3] at hle
  have h3 : (3:ENNReal) * W ≤ 1 := by
    refine le_trans ?_ hle
    have hsum : (3:ℝ) ≤ rexp (-δ) + 1 + rexp δ := by
      have := Real.add_one_le_exp δ
      have := Real.add_one_le_exp (-δ)
      linarith
    have e3 : ENNReal.ofReal (rexp (-δ)) * W + W + ENNReal.ofReal (rexp δ) * W =
        ENNReal.ofReal (rexp (-δ) + 1 + rexp δ) * W := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_one]
      ring
    rw [e3]
    have h3le : (3:ENNReal) ≤ ENNReal.ofReal (rexp (-δ) + 1 + rexp δ) := by
      calc (3:ENNReal) = ENNReal.ofReal 3 := by norm_num
        _ ≤ _ := ENNReal.ofReal_le_ofReal hsum
    gcongr
  -- the measure of the image
  have himg : volume ((fun u => rexp (-u)) '' B) = W := by
    have := lintegral_image_eq_lintegral_abs_deriv_mul hBm
      (f := fun u => rexp (-u)) (f' := fun x => rexp (-x) * (-1))
      (fun x _ => ((hasDerivAt_neg x).exp).hasDerivWithinAt)
      (fun a _ b _ h => by simpa using h) (fun _ => 1)
    rw [setLIntegral_one] at this
    rw [this, hW]
    apply setLIntegral_congr_fun hBm
    intro x _
    dsimp only
    rw [mul_one, abs_mul, abs_neg, abs_one, mul_one, abs_of_pos (exp_pos _)]
  have hW3 : W ≤ ENNReal.ofReal (1 / 3) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one]
    rw [ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)]
    calc W * ENNReal.ofReal 3 = 3 * W := by rw [mul_comm]; norm_num
      _ ≤ 1 := h3
  simp only [Measure.real]
  rw [himg]
  exact ENNReal.toReal_le_of_le_ofReal (by norm_num) hW3
