import FormalConjectures.GreensOpenProblems.«35»

-- Problem: Ben Green's Open Problem 35 — c inf lower young
-- Upstream: formal-conjectures FormalConjectures/GreensOpenProblems/35.lean (declaration Green35.variants.c_inf_lower_young)
-- Credit: @Genbox (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open MeasureTheory
open scoped Convolution ENNReal

/-- For a nonnegative integrable function with integral `1`, `‖g‖₂² ≤ ‖g‖_∞ · ‖g‖₁ = ‖g‖_∞`. -/
theorem OMA.l2_sq_le_top (g : ℝ → ℝ) (hg : Integrable g) (h0 : ∀ x, 0 ≤ g x)
    (h1 : ∫ x, g x = 1) : eLpNorm g 2 volume ^ 2 ≤ eLpNorm g ⊤ volume := by
  have hL1 : ∫⁻ x, ‖g x‖ₑ = 1 := by
    rw [show (fun x => ‖g x‖ₑ) = fun x => ENNReal.ofReal (g x) from
          funext (fun x => Real.enorm_eq_ofReal (h0 x)),
      ← ofReal_integral_eq_lintegral_ofReal hg (Filter.Eventually.of_forall h0), h1,
      ENNReal.ofReal_one]
  have h2 : eLpNorm g 2 volume ^ 2 = ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    rw [show (2 : ℝ≥0∞).toReal = 2 by norm_num, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  rw [h2, eLpNorm_exponent_top]
  calc ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ)
      ≤ ∫⁻ x, eLpNormEssSup g volume * ‖g x‖ₑ := by
        apply lintegral_mono_ae
        filter_upwards [ae_le_eLpNormEssSup (μ := volume) (f := g)] with x hx
        rw [ENNReal.rpow_two, sq]
        gcongr
    _ = eLpNormEssSup g volume * ∫⁻ x, ‖g x‖ₑ :=
        lintegral_const_mul'' _ hg.aemeasurable.enorm
    _ = eLpNormEssSup g volume := by rw [hL1, mul_one]

theorem OMA.solution : type_of% @Green35.variants.c_inf_lower_young := by
  unfold Green35.c
  apply le_sInf
  rintro r ⟨f, hf, rfl⟩
  have hc : Green35.c 2 ≤ eLpNorm (f ⋆ f) 2 := sInf_le ⟨f, hf, rfl⟩
  obtain ⟨hfi, hf0, -, hf1⟩ := hf
  have hgi : Integrable (f ⋆ f) := hfi.integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hfi
  have hg0 : ∀ x, 0 ≤ (f ⋆ f) x := by
    intro x
    rw [convolution_lsmul]
    exact integral_nonneg fun t => mul_nonneg (hf0 t) (hf0 _)
  have hg1 : ∫ x, (f ⋆ f) x = 1 := by
    rw [integral_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hfi hfi, hf1]
    simp
  calc (Green35.c 2) ^ 2 ≤ eLpNorm (f ⋆ f) 2 volume ^ 2 := by gcongr
    _ ≤ _ := OMA.l2_sq_le_top _ hgi hg0 hg1
