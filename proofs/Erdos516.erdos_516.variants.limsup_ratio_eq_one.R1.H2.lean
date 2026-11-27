import OMAReductions.R_Erdos516_erdos_516_variants_limsup_ratio_eq_one_R1
import Mathlib

-- Step Erdos516.erdos_516.variants.limsup_ratio_eq_one.R1.H2: hypothesis H2 of reduction
-- Erdos516.erdos_516.variants.limsup_ratio_eq_one.R1
-- Credit: @ivillar

/-!
Reindex the lacunary series as a power series `∑ c_m z^m` (with `c_{n_k} = a_k`). It converges
everywhere, so its radius is infinite and `f` is entire, with `f^{(n_1)}(0) = n_1! a_1`. If
`‖f‖ ≤ 1` on the circle of radius `R`, Cauchy's estimate gives `n_1! ‖a_1‖ ≤ n_1! / R^{n_1}`, i.e.
`‖a_1‖ R^{n_1} ≤ 1`, which fails once `R ≥ max 2 (2 / ‖a_1‖)` (note `n_1 ≥ 1`).
-/

open Filter

namespace OMA.Erdos516H2

theorem main_lemma (n : ℕ → ℕ) (a : ℕ → ℂ) (f : ℂ → ℂ) (hn : StrictMono n)
    (hf : ∀ z : ℂ, HasSum (fun k => a k * z ^ (n k)) (f z)) (R : ℝ) (hR : 0 < R)
    (hbd : ∀ z ∈ Metric.sphere (0 : ℂ) R, ‖f z‖ ≤ 1) : ‖a 1‖ * R ^ (n 1) ≤ 1 := by
  classical
  let c : ℕ → ℂ := fun m => if h : ∃ k, n k = m then a (Classical.choose h) else 0
  have hc : ∀ k, c (n k) = a k := by
    intro k
    have h : ∃ j, n j = n k := ⟨k, rfl⟩
    simp only [c, dif_pos h]
    congr 1
    exact hn.injective (Classical.choose_spec h)
  have hc0 : ∀ m, m ∉ Set.range n → c m = 0 := by
    intro m hm
    simp only [c]
    rw [dif_neg]
    rintro ⟨k, rfl⟩
    exact hm ⟨k, rfl⟩
  have hsum : ∀ z : ℂ, HasSum (fun m => c m * z ^ m) (f z) := by
    intro z
    rw [← hn.injective.hasSum_iff (f := fun m => c m * z ^ m) (fun m hm => by simp [hc0 m hm])]
    simpa [Function.comp_def, hc] using hf z
  let p := FormalMultilinearSeries.ofScalars ℂ c
  have hrad : p.radius = ⊤ := by
    apply ENNReal.eq_top_of_forall_nnreal_le
    intro r
    apply p.le_radius_of_tendsto (l := 0)
    have h2 := ((hsum (r : ℂ)).summable.tendsto_atTop_zero).norm
    rw [norm_zero] at h2
    refine h2.congr (fun m => ?_)
    rw [FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, NNReal.abs_eq]
  have hps : HasFPowerSeriesOnBall f p 0 ⊤ := by
    have h := p.hasFPowerSeriesOnBall (by rw [hrad]; exact ENNReal.zero_lt_top)
    rw [hrad] at h
    have heq : p.sum = f := by
      funext z
      show FormalMultilinearSeries.ofScalarsSum c z = f z
      rw [FormalMultilinearSeries.ofScalars_sum_eq]
      simpa [smul_eq_mul] using (hsum z).tsum_eq
    rwa [heq] at h
  have hdiff : Differentiable ℂ f := fun z =>
    (hps.analyticAt_of_mem (Metric.mem_eball.mpr (edist_lt_top _ _))).differentiableAt
  have hA : AnalyticAt ℂ f 0 := hps.analyticAt
  have huniq := hps.hasFPowerSeriesAt.eq_formalMultilinearSeries hA.hasFPowerSeriesAt
  have hcoef : c (n 1) = iteratedDeriv (n 1) f 0 / ((n 1).factorial : ℂ) := by
    have h := congrArg (fun q => FormalMultilinearSeries.coeff q (n 1)) huniq
    simpa [p, FormalMultilinearSeries.coeff_ofScalars] using h
  rw [hc 1] at hcoef
  have hfac : (0 : ℝ) < (n 1).factorial := by exact_mod_cast Nat.factorial_pos _
  have hfacC : ((n 1).factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hid : iteratedDeriv (n 1) f 0 = ((n 1).factorial : ℂ) * a 1 := by
    rw [hcoef]
    field_simp
  have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (n 1) hR
    hdiff.diffContOnCl hbd
  rw [hid, norm_mul, Complex.norm_natCast, le_div_iff₀ (pow_pos hR _)] at hcauchy
  have h3 : ((n 1).factorial : ℝ) * (‖a 1‖ * R ^ (n 1)) ≤ ((n 1).factorial : ℝ) * 1 := by
    nlinarith
  exact le_of_mul_le_mul_left h3 hfac

end OMA.Erdos516H2

open Filter in
theorem OMA.solution : OMA.R_Erdos516_erdos_516_variants_limsup_ratio_eq_one_R1.H2 := by
  unfold OMA.R_Erdos516_erdos_516_variants_limsup_ratio_eq_one_R1.H2
  intro n a f hn ha hf
  have hm : 1 ≤ n 1 := by
    have := hn Nat.zero_lt_one
    omega
  have hapos : 0 < ‖a 1‖ := norm_pos_iff.mpr ha
  filter_upwards [eventually_ge_atTop (max 2 (2 / ‖a 1‖))] with r hr
  by_contra hcon
  push Not at hcon
  have hr2 : 2 ≤ r := le_trans (le_max_left _ _) hr
  have hr0 : 0 < r := by linarith
  have h := OMA.Erdos516H2.main_lemma n a f hn hf r hr0
    (fun z hz => hcon z (by simpa using hz))
  have hrm : r ≤ r ^ (n 1) := by
    calc r = r ^ 1 := (pow_one r).symm
      _ ≤ r ^ (n 1) := pow_le_pow_right₀ (by linarith) hm
  have h2 : 2 / ‖a 1‖ ≤ r := le_trans (le_max_right _ _) hr
  have h3 : 2 ≤ ‖a 1‖ * r := by
    rw [div_le_iff₀ hapos] at h2
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hrm hapos.le]
