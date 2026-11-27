import OMAReductions.R_ERH_extended_riemann_hypothesis_R1_H1_R1
import Mathlib.Analysis.MellinInversion
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.NumberTheory.NumberField.Discriminant.Basic

/-! For signature (0, 1), identify the inverse Mellin kernel with the sum of the
theta series of normalized ideal lattices. Planar Poisson summation gives the
reciprocal identity with constant twice the class number divided by the number
of roots of unity. The two remaining cases are real quadratic fields and fields
of degree at least three, each restricted to the half-line beginning at one. -/

-- Reduction ERH.extended_riemann_hypothesis.R1.H1.R1.H2.R1 of step ERH.extended_riemann_hypothesis.R1.H1.R1.H2
-- Credit: @STARDUSTLC666

namespace OMA.R_ERH_extended_riemann_hypothesis_R1_H1_R1_H2_R1

open Complex Filter Set Asymptotics NumberField NumberField.Units NumberField.InfinitePlace
open NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone MeasureTheory HurwitzZeta Module Submodule
open scoped NumberField nonZeroDivisors Topology Classical

/-- The remaining real quadratic transformation on the half-line from one. -/
def H1 : Prop := ∀ (K : Type) [Field K] [NumberField K],
    Module.finrank ℚ K = 2 → nrComplexPlaces K = 0 →
    let f := mellinInv 2 (fun s => exp (s * (Real.log (discr K).natAbs / 2 : ℝ)) *
      Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K * dedekindZeta K s)
    let c : ℂ := ((4 : ℝ) * regulator K * classNumber K / torsionOrder K : ℝ)
    ∀ x : ℝ, 1 ≤ x → f (1 / x) + c = (x : ℂ) * (f x + c)

/-- The same half-line identity in degrees at least three, with its class-number constant. -/
def H2 : Prop := ∀ (K : Type) [Field K] [NumberField K],
    3 ≤ Module.finrank ℚ K →
    let f := mellinInv 2 (fun s => exp (s * (Real.log (discr K).natAbs / 2 : ℝ)) *
      Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K * dedekindZeta K s)
    let c : ℂ := ((2 : ℝ) ^ (nrRealPlaces K + nrComplexPlaces K) * regulator K * classNumber K / torsionOrder K : ℝ)
    ∀ x : ℝ, 1 ≤ x → f (1 / x) + c = (x : ℂ) * (f x + c)

theorem norm_Gamma_le_real {s : ℂ} (hs : 0 < s.re) : ‖Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Gamma_eq_integral hs, GammaIntegral, Real.Gamma_eq_integral hs]
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  rw [norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le, norm_cpow_eq_rpow_re_of_pos hx]
  simp

theorem gamma_shift_bound {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    |s.im| ^ n * ‖Gamma s‖ ≤ Real.Gamma (s.re + n) := by
  induction n generalizing s with
  | zero => simpa using norm_Gamma_le_real hs
  | succ n ih =>
    have hpos : 0 < (s + 1).re := by rw [add_re, one_re]; linarith
    have hstep : |s.im| * ‖Gamma s‖ ≤ ‖Gamma (s + 1)‖ := by
      rw [Gamma_add_one s (ne_zero_of_re_pos hs), norm_mul]
      exact mul_le_mul_of_nonneg_right (abs_im_le_norm s) (norm_nonneg _)
    calc |s.im| ^ (n + 1) * ‖Gamma s‖ = |s.im| ^ n * (|s.im| * ‖Gamma s‖) := by ring
         _ ≤ |s.im| ^ n * ‖Gamma (s + 1)‖ := by gcongr
         _ ≤ Real.Gamma ((s + 1).re + n) := by simpa using ih (s := s + 1) hpos
         _ = Real.Gamma (s.re + (n + 1 : ℕ)) := by push_cast; congr 1; simp; ring

theorem gamma_vertical : VerticalIntegrable Gamma 2 := by
  have hcont : Continuous (fun y : ℝ => Gamma ((2 : ℂ) + y * I)) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    apply (continuousAt_Gamma _ (fun n => ?_)).comp (f := fun t : ℝ => (2 : ℂ) + t * I) (by fun_prop)
    intro h
    have hr := congrArg re h
    simp at hr
    linarith [Nat.cast_nonneg (α := ℝ) n]
  apply (integrable_inv_one_add_sq.const_mul (Real.Gamma 2 + Real.Gamma 4)).mono' hcont.aestronglyMeasurable
  filter_upwards with y
  change ‖Gamma ((2 : ℂ) + y * I)‖ ≤ _ * (1 + y ^ 2)⁻¹
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  have h₀ := norm_Gamma_le_real (s := (2 : ℂ) + y * I) (by simp)
  have h₂ := gamma_shift_bound (s := (2 : ℂ) + y * I) (by simp) 2
  norm_num [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, sq_abs] at h₀ h₂ ⊢
  linarith

theorem inverse_gamma {x : ℝ} (hx : 0 < x) : mellinInv 2 Gamma x = (Real.exp (-x) : ℂ) := by
  let f (t : ℝ) : ℂ := Real.exp (-t)
  have heq (y : ℝ) : mellin f (2 + y * I) = Gamma (2 + y * I) := by
    rw [Gamma_eq_integral (by simp : 0 < ((2 : ℂ) + y * I).re), GammaIntegral_eq_mellin]
  have hm : MellinConvergent f 2 := by
    change IntegrableOn (fun t : ℝ => (t : ℂ) ^ ((2 : ℂ) - 1) • f t) (Ioi 0)
    simpa only [f, smul_eq_mul, mul_comm] using GammaIntegral_convergent (s := (2 : ℂ)) (by norm_num)
  have hF : VerticalIntegrable (mellin f) 2 := by
    change Integrable (fun y : ℝ => mellin f ((2 : ℝ) + y * I))
    simpa only [VerticalIntegrable, ofReal_ofNat, heq] using gamma_vertical
  change mellinInv 2 Gamma x = f x
  rw [← mellinInv_mellin_eq 2 f hx hm hF (by dsimp [f]; fun_prop)]
  unfold mellinInv
  simp only [ofReal_ofNat, heq]

theorem inverse_gamma_series (K : Type*) [Field K] [NumberField K] {x : ℝ} (hx : 0 < x) :
    mellinInv 2 (fun s => Gamma s * dedekindZeta K s) x =
      ∑' n : ℕ, if n = 0 then 0 else ((Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n}) : ℂ) * (Real.exp (-(x * n)) : ℂ) := by
  let aN (n : ℕ) := Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n}
  have coeff_mean :
      Tendsto (fun n : ℕ => (∑ k ∈ Finset.Icc 1 n, (aN k : ℝ)) / n) atTop
        (𝓝 (dedekindZeta_residue K)) := by
    refine ((Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop).congr fun n => ?_
    simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum, aN]
    congr
    rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
      show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
      show 1 = Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 0} by simp [Ideal.absNorm_eq_zero_iff],
      Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
      ← Finset.card_preimage_eq_sum_card_image_eq (fun k _ => Ideal.finite_setOfPred_absNorm_eq k)]
    simp [Set.coe_eq_subtype]
  have hDirichlet {s : ℂ} (hs : 1 < s.re) :
      LSeriesSummable (fun n => (aN n : ℂ)) s := by
    have h := LSeriesSummable_of_sum_norm_bigO_and_nonneg (f := fun n => (aN n : ℝ))
      (r := 1) (isBigO_atTop_natCast_rpow_of_tendsto_div_rpow (by simpa using coeff_mean))
      (fun n => Nat.cast_nonneg _) zero_le_one hs
    simpa only [ofReal_natCast] using h
  let z (y : ℝ) : ℂ := 2 + y * I
  let a (n : ℕ) : ℂ := aN n
  let G (n : ℕ) (y : ℝ) := (x : ℂ) ^ (-(z y)) * Gamma (z y) * LSeries.term a (z y) n
  let w (n : ℕ) := ‖LSeries.term a 2 n‖
  have hw (n : ℕ) (y : ℝ) : ‖G n y‖ = (x ^ (-(2 : ℝ)) * w n) * ‖Gamma (z y)‖ := by
    simp only [G, w, norm_mul, LSeries.norm_term_eq, norm_cpow_eq_rpow_re_of_pos hx, neg_re]
    simp [z, mul_right_comm]
  have hG (n : ℕ) : Integrable (G n) := by
    apply ((gamma_vertical.norm).const_mul (x ^ (-(2 : ℝ)) * w n)).mono'
    · by_cases hn : n = 0
      · subst n; simpa [G, LSeries.term] using (aestronglyMeasurable_const (b := (0 : ℂ)) (μ := (volume : Measure ℝ)))
      · have hz : Continuous z := by dsimp [z]; fun_prop
        have hp : Continuous (fun y : ℝ => (x : ℂ) ^ (-z y)) := hz.neg.const_cpow (Or.inl (ofReal_ne_zero.mpr hx.ne'))
        have hg : Continuous (fun y : ℝ => Gamma (z y)) := by
          apply continuous_iff_continuousAt.mpr
          intro y
          apply (continuousAt_Gamma _ (fun m => ?_)).comp (f := z) (by dsimp [z]; fun_prop)
          intro h
          have hr := congrArg re h
          simp [z] at hr
          linarith [Nat.cast_nonneg (α := ℝ) m]
        have ht : Continuous (fun y => LSeries.term a (z y) n) := by
          simp only [LSeries.term_of_ne_zero hn]
          have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
          exact continuous_const.div₀ (hz.const_cpow (Or.inl hn')) (fun y => cpow_ne_zero_iff.mpr (Or.inl hn'))
        exact ((hp.fun_mul hg).fun_mul ht).aestronglyMeasurable
    · exact Eventually.of_forall fun y => (hw n y).le
  have hsum : Summable fun n => ∫ y : ℝ, ‖G n y‖ := by
    simp_rw [hw, integral_const_mul, mul_assoc]
    exact (((hDirichlet (s := 2) (by norm_num)).norm.mul_right _).mul_left _)
  have hex (y : ℝ) : (x : ℂ) ^ (-z y) • (Gamma (z y) * dedekindZeta K (z y)) = ∑' n, G n y := by
    simp only [G, dedekindZeta, LSeries, ← tsum_mul_left, smul_eq_mul, mul_assoc, a, aN]
  unfold mellinInv
  change (1 / (2 * Real.pi) : ℝ) • (∫ y : ℝ, (x : ℂ) ^ (-z y) • (Gamma (z y) * dedekindZeta K (z y))) = _
  simp_rw [hex]
  rw [← integral_tsum_of_summable_integral_norm hG hsum, ← tsum_const_smul'']
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · subst n; simp [G, LSeries.term]
  · rw [if_neg hn]
    have hterm (y : ℝ) : G n y = a n * ((↑(x * n) : ℂ) ^ (-z y) • Gamma (z y)) := by
      dsimp only [G]
      rw [LSeries.term_of_ne_zero hn, ofReal_mul, mul_cpow_ofReal_nonneg hx.le (Nat.cast_nonneg _), ofReal_natCast]
      simp only [cpow_neg, smul_eq_mul, div_eq_mul_inv]
      ring
    simp_rw [hterm, integral_const_mul]
    have hx' : 0 < x * n := mul_pos hx (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))
    rw [← inverse_gamma hx']
    unfold mellinInv
    simp [z, a, aN, Algebra.smul_def, mul_left_comm, mul_assoc]

theorem inverse_scaled (F : ℂ → ℂ) (σ : ℝ) {q x : ℝ} (hq : 0 < q) (hx : 0 < x) (c : ℂ) :
    mellinInv σ (fun s => c * ((q : ℂ) ^ (-s) * F s)) x = c * mellinInv σ F (q * x) := by
  let z (y : ℝ) : ℂ := σ + y * I
  have h (y : ℝ) : (x : ℂ) ^ (-z y) • (c * ((q : ℂ) ^ (-z y) * F (z y))) =
      c * ((↑(q * x) : ℂ) ^ (-z y) • F (z y)) := by
    rw [ofReal_mul, mul_cpow_ofReal_nonneg hq.le hx.le]; simp only [smul_eq_mul]; ring
  unfold mellinInv
  change (1 / (2 * Real.pi) : ℝ) • (∫ y : ℝ, (x : ℂ) ^ (-z y) • (c * ((q : ℂ) ^ (-z y) * F (z y)))) = _
  simp_rw [h, integral_const_mul]
  simp [Algebra.smul_def, mul_left_comm, z]

theorem kernel_expansion_of_signature (K : Type*) [Field K] [NumberField K]
    (hR : nrRealPlaces K = 0) (hC : nrComplexPlaces K = 1) {x : ℝ} (hx : 0 < x) :
    let q := 2 * Real.pi / Real.sqrt ((discr K).natAbs : ℝ)
    mellinInv 2 (fun s => exp (s * (Real.log (discr K).natAbs / 2 : ℝ)) * Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K * dedekindZeta K s) x = 2 * ∑' n : ℕ, if n = 0 then 0 else ((Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n}) : ℂ) * (Real.exp (-(q * x * n)) : ℂ) := by
  let l := Real.log (discr K).natAbs / 2
  let q := 2 * Real.pi / Real.exp l
  have hd : 0 < ((discr K).natAbs : ℝ) := by exact_mod_cast Int.natAbs_pos.mpr (discr_ne_zero K)
  have hl : Real.exp l = Real.sqrt ((discr K).natAbs : ℝ) := by dsimp [l]; rw [Real.exp_half, Real.exp_log hd]
  have hp : 0 < 2 * Real.pi := by positivity
  have hq : 0 < q := div_pos hp (Real.exp_pos _)
  have hc (s : ℂ) (b : ℝ) (hb : 0 < b) : (b : ℂ) ^ (-s) = exp (-((Real.log b : ℂ) * s)) := by
    rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hb.ne'), ← ofReal_log hb.le]; congr 1; ring
  have hfac (s : ℂ) : exp (s * (l : ℂ)) * ((2 * Real.pi : ℝ) : ℂ) ^ (-s) = (q : ℂ) ^ (-s) := by
    rw [hc s _ hp, hc s _ hq, ← exp_add]
    dsimp only [q]
    rw [Real.log_div hp.ne' (Real.exp_pos _).ne', Real.log_exp, ofReal_sub]
    congr 1; ring
  have hcomp : (fun s : ℂ => exp (s * (Real.log (discr K).natAbs / 2 : ℝ)) * Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K * dedekindZeta K s) = fun s => 2 * ((q : ℂ) ^ (-s) * (Gamma s * dedekindZeta K s)) := by
    funext s
    simp only [hR, pow_zero, mul_one, hC, pow_one, Gammaℂ_def]
    change exp (s * (l : ℂ)) * (2 * ((2 : ℂ) * Real.pi) ^ (-s) * Gamma s) * dedekindZeta K s = _
    rw [← hfac s, ofReal_mul, ofReal_ofNat]
    ring
  dsimp only
  rw [hcomp, inverse_scaled _ _ hq hx _, inverse_gamma_series K (mul_pos hq hx)]
  rw [show q = 2 * Real.pi / Real.sqrt ((discr K).natAbs : ℝ) by rw [← hl]]

/-- Poisson summation in the horizontal coordinate makes the Fourier phase symmetric
in the two integer indices. The positive quadratic form also gives absolute convergence. -/
theorem planar_gaussian (u v : ℝ) (hv : 0 < v) :
    let W (t : ℝ) (p : ℤ × ℤ) : ℂ := Real.exp (-Real.pi * (((p.2 : ℝ) + u * p.1) ^ 2 / v + v * (p.1 : ℝ) ^ 2) * t)
    (∀ t : ℝ, 0 < t → Summable (W t)) ∧
      ∀ t : ℝ, 0 < t → ∑' p, W (1 / t) p = (t : ℂ) * ∑' p, W t p := by
  let gaussian (b : ℝ) (n : ℤ) : ℂ := Real.exp (-Real.pi * (n : ℝ) ^ 2 * b)
  let rows (u a b : ℝ) : ℂ :=
    ∑' n : ℤ, gaussian b n * (evenKernel (u * (n : ℝ) : ℝ) a : ℂ)
  let term (u b d : ℝ) (n m : ℤ) : ℂ :=
    gaussian b n * exp (2 * Real.pi * I * (u * (n : ℝ) : ℝ) * m) * gaussian d m
  have gaussian_summable {b : ℝ} (hb : 0 < b) : Summable (fun n : ℤ => ‖gaussian b n‖) := by
    have h (n : ℤ) : ‖gaussian b n‖ = Real.exp (-Real.pi * (n : ℝ) ^ 2 * b) :=
      Complex.norm_of_nonneg (Real.exp_pos _).le
    simp_rw [h]
    simpa using (hasSum_int_evenKernel 0 hb).summable
  have term_norm (u b d : ℝ) (n m : ℤ) : ‖term u b d n m‖ = ‖gaussian b n‖ * ‖gaussian d m‖ := by
    simp [term, norm_exp, mul_re, mul_im]
  have term_swap (u b d : ℝ) (n m : ℤ) : term u b d n m = term u d b m n := by
    have hf : (2 : ℂ) * Real.pi * I * ((u * (n : ℝ) : ℝ) : ℂ) * m =
        2 * Real.pi * I * ((u * (m : ℝ) : ℝ) : ℂ) * n := by push_cast; ring
    dsimp only [term]; rw [hf]; ring
  have double_swap (u : ℝ) {b d : ℝ} (hb : 0 < b) (hd : 0 < d) :
      (∑' n : ℤ, ∑' m : ℤ, term u b d n m) = ∑' m : ℤ, ∑' n : ℤ, term u d b m n := by
    have hS : Summable (Function.uncurry (term u b d)) := by
      apply Summable.of_norm
      change Summable (fun p : ℤ × ℤ => ‖term u b d p.1 p.2‖)
      simp_rw [term_norm]
      exact (gaussian_summable hb).mul_of_nonneg (gaussian_summable hd) (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    rw [← hS.tsum_comm]
    exact tsum_congr fun m => tsum_congr fun n => term_swap u b d n m
  have rows_fourier (u b : ℝ) {a : ℝ} (ha : 0 < a) :
      rows u a b = ((1 / Real.sqrt a : ℝ) : ℂ) * ∑' n : ℤ, ∑' m : ℤ, term u b (1 / a) n m := by
    dsimp only [rows]
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    have hs := (hasSum_int_cosKernel (u * (n : ℝ)) (one_div_pos.mpr ha)).tsum_eq
    have hinner : (∑' m : ℤ, term u b (1 / a) n m) = gaussian b n * (cosKernel (u * (n : ℝ) : ℝ) (1 / a) : ℂ) := by
      rw [← hs, ← tsum_mul_left]
      apply tsum_congr; intro m; dsimp only [term, gaussian]; ring
    rw [hinner, evenKernel_functional_equation, ← Real.sqrt_eq_rpow, ofReal_mul]
    ring
  have rows_dual (u : ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
      rows u a b = ((1 / (Real.sqrt a * Real.sqrt b) : ℝ) : ℂ) * rows u (1 / b) (1 / a) := by
    rw [rows_fourier u b ha, rows_fourier u (1 / a) (one_div_pos.mpr hb), double_swap u hb (one_div_pos.mpr ha)]
    simp only [one_div_one_div, Real.sqrt_div (show 0 ≤ (1 : ℝ) by norm_num), Real.sqrt_one, ofReal_div, ofReal_one, ofReal_mul]
    field_simp [ofReal_ne_zero.mpr (Real.sqrt_pos.mpr ha).ne', ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hb).ne']
  let theta (u v t : ℝ) : ℂ := rows u (t / v) (t * v)
  have theta_inv (u : ℝ) {v t : ℝ} (hv : 0 < v) (ht : 0 < t) :
      theta u v (1 / t) = (t : ℂ) * theta u v t := by
    have h := rows_dual u (div_pos ht hv) (mul_pos ht hv)
    have h1 : 1 / (t * v) = 1 / t / v := by ring
    have h2 : 1 / (t / v) = 1 / t * v := by field_simp
    have hdet : Real.sqrt (t / v) * Real.sqrt (t * v) = t := by
      rw [← Real.sqrt_mul (div_pos ht hv).le, show t / v * (t * v) = t ^ 2 by field_simp, Real.sqrt_sq ht.le]
    rw [h1, h2, hdet, ofReal_div, ofReal_one] at h
    dsimp only [theta]
    rw [h, ← mul_assoc, mul_one_div_cancel (ofReal_ne_zero.mpr ht.ne'), one_mul]
  have theta_eq_sum (u v t : ℝ) (hv : 0 < v) (ht : 0 < t) :
      theta u v t = ∑' n : ℤ, ∑' m : ℤ,
        (Real.exp (-Real.pi * (((m : ℝ) + u * n) ^ 2 / v + v * n ^ 2) * t) : ℂ) := by
    dsimp only [theta, rows]
    apply tsum_congr; intro n
    rw [← (hasSum_int_evenKernel (u * n) (div_pos ht hv)).tsum_eq, ofReal_tsum, ← tsum_mul_left]
    apply tsum_congr; intro m; dsimp only [gaussian]
    rw [← ofReal_mul, ← Real.exp_add]
    congr 2; ring
  let form (u v : ℝ) (p : ℤ × ℤ) : ℝ :=
    ((p.2 : ℝ) + u * p.1) ^ 2 / v + v * (p.1 : ℝ) ^ 2
  have coercive (u : ℝ) {v : ℝ} (hv : 0 < v) :
      ∃ d : ℝ, 0 < d ∧ ∀ p : ℤ × ℤ, d * ((p.2 : ℝ) ^ 2 + (p.1 : ℝ) ^ 2) ≤ form u v p := by
    let d := min (v⁻¹ / 2) (v / (2 * u ^ 2 + 1))
    have hden : 0 < 2 * u ^ 2 + 1 := by positivity
    have hd : 0 < d := lt_min (by positivity) (div_pos hv hden)
    have h₁ : d * 2 ≤ v⁻¹ := (le_div_iff₀ (by norm_num)).mp (min_le_left ..)
    have h₂ : d * (2 * u ^ 2 + 1) ≤ v := (le_div_iff₀ hden).mp (min_le_right ..)
    refine ⟨d, hd, fun ⟨n, m⟩ => ?_⟩
    let M : ℝ := m
    let N : ℝ := n
    change d * (M ^ 2 + N ^ 2) ≤ (M + u * N) ^ 2 / v + v * N ^ 2
    calc
      _ ≤ d * (2 * (M + u * N) ^ 2 + (2 * u ^ 2 + 1) * N ^ 2) :=
        mul_le_mul_of_nonneg_left (by nlinarith only [sq_nonneg (M + 2 * u * N)]) hd.le
      _ = (d * 2) * (M + u * N) ^ 2 + (d * (2 * u ^ 2 + 1)) * N ^ 2 := by ring
      _ ≤ v⁻¹ * (M + u * N) ^ 2 + v * N ^ 2 :=
        add_le_add (mul_le_mul_of_nonneg_right h₁ (sq_nonneg _)) (mul_le_mul_of_nonneg_right h₂ (sq_nonneg _))
      _ = _ := by ring
  let weight (u v t : ℝ) (p : ℤ × ℤ) : ℂ := Real.exp (-Real.pi * form u v p * t)
  have total_summable (u : ℝ) {v t : ℝ} (hv : 0 < v) (ht : 0 < t) : Summable (weight u v t) := by
    obtain ⟨d, hd, hform⟩ := coercive u hv
    let g (i : ℤ) := Real.exp (-Real.pi * (i : ℝ) ^ 2 * (d * t))
    have hg : Summable g := by simpa [g] using (HurwitzZeta.hasSum_int_evenKernel 0 (mul_pos hd ht)).summable
    apply Complex.summable_ofReal.mpr
    apply Summable.of_nonneg_of_le (fun p => (Real.exp_pos _).le) _ (hg.mul_of_nonneg hg (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le))
    intro p
    change Real.exp _ ≤ Real.exp _ * Real.exp _
    rw [← Real.exp_add, Real.exp_le_exp]
    have h := mul_le_mul_of_nonneg_left (hform p) (mul_pos Real.pi_pos ht).le
    linarith only [h]
  have theta_eq (u : ℝ) {v t : ℝ} (hv : 0 < v) (ht : 0 < t) :
      theta u v t = ∑' p, weight u v t p := by
    rw [(total_summable u hv ht).tsum_prod]
    exact theta_eq_sum u v t hv ht
  refine ⟨fun t ht => total_summable u hv ht, fun t ht => ?_⟩
  change (∑' p, weight u v (1 / t) p) = (t : ℂ) * ∑' p, weight u v t p
  rw [← theta_eq u hv (one_div_pos.mpr ht), ← theta_eq u hv ht, theta_inv u hv ht]

/-- Coordinates of a planar lattice in the basis given by the two complex vectors. -/
theorem shape (a b : ℂ) {A : ℝ} (hA : 0 < A) (hdet : A = |a.re * b.im - a.im * b.re|) :
    ∃ u v : ℝ, 0 < v ∧ ∀ m n : ℤ, Complex.normSq ((m : ℂ) * a + (n : ℂ) * b) / A =
      ((m : ℝ) + u * n) ^ 2 / v + v * (n : ℝ) ^ 2 := by
  have ha : a ≠ 0 := by
    rintro rfl
    simp at hdet
    linarith
  have hN := Complex.normSq_pos.mpr ha
  have hcross : (b / a).im * Complex.normSq a = a.re * b.im - a.im * b.re := by
    rw [Complex.div_im]; field_simp
  have hscale : A = |(b / a).im| * Complex.normSq a := by
    rw [hdet, ← hcross, abs_mul, abs_of_pos hN]
  have hv : 0 < |(b / a).im| := by
    apply pos_of_mul_pos_left (hscale ▸ hA) hN.le
  refine ⟨(b / a).re, |(b / a).im|, hv, fun m n => ?_⟩
  rw [show (m : ℂ) * a + (n : ℂ) * b = ((m : ℂ) + b / a * n) * a by field_simp,
    map_mul, Complex.normSq_apply ((m : ℂ) + b / a * n), hscale]
  simp only [Complex.add_re, Complex.add_im, Complex.intCast_re, Complex.intCast_im,
    Complex.mul_re, Complex.mul_im, mul_zero, sub_zero, zero_add]
  field_simp [hv.ne', hN.ne']
  nlinarith only [sq_abs (b / a).im, congrArg (fun t : ℝ => t * (n : ℝ) ^ 2) (sq_abs (b / a).im)]

variable (K : Type*) [Field K] [NumberField K]

theorem area (hC : nrComplexPlaces K = 1) (J : (Ideal (𝓞 K))⁰) :
    ZLattice.covolume ((idealLattice K (FractionalIdeal.mk0 K J))) = (Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ) *
      Real.sqrt ((discr K).natAbs : ℝ) / 2 := by
  rw [mixedEmbedding.covolume_idealLattice, hC, pow_one, FractionalIdeal.coe_mk0,
    FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast, Nat.cast_natAbs, Int.cast_abs]
  ring

theorem model (hR : nrRealPlaces K = 0) (hC : nrComplexPlaces K = 1) (J : (Ideal (𝓞 K))⁰) :
    ∃ u v : ℝ, 0 < v ∧ ∃ e : ℤ × ℤ ≃ (idealLattice K (FractionalIdeal.mk0 K J)), ∀ p : ℤ × ℤ,
      mixedEmbedding.norm (e p : mixedSpace K) / ZLattice.covolume ((idealLattice K (FractionalIdeal.mk0 K J))) =
        ((p.2 : ℝ) + u * p.1) ^ 2 / v + v * (p.1 : ℝ) ^ 2 := by
  classical
  let : IsEmpty {w : InfinitePlace K // IsReal w} := Fintype.card_eq_zero_iff.mp hR
  let : Unique {w : InfinitePlace K // IsComplex w} := (Fintype.card_eq_one_iff_nonempty_unique.mp hC).some
  have hc : Fintype.card (InfinitePlace K) = 1 := by rw [card_eq_nrRealPlaces_add_nrComplexPlaces, hR, hC]
  let : Unique (InfinitePlace K) := (Fintype.card_eq_one_iff_nonempty_unique.mp hc).some
  let w : {w : InfinitePlace K // IsComplex w} := default
  let idx : Fin 2 ≃ index K := {
    toFun := fun i => Sum.inr (w, i)
    invFun := Sum.elim isEmptyElim Prod.snd
    left_inv := fun _ => rfl
    right_inv := fun j => by
      rcases j with r | ⟨c, i⟩
      · exact isEmptyElim r
      · exact congrArg (fun d => Sum.inr (d, i)) (Subsingleton.elim w c) }
  let s := (stdBasis K).reindex idx.symm
  let L := (idealLattice K (FractionalIdeal.mk0 K J))
  have hrank : finrank ℤ L = 2 := by
    rw [ZLattice.rank ℝ L, finrank_eq_card_basis s, Fintype.card_fin]
  let b := finBasisOfFinrankEq ℤ L hrank
  let a₀ := ((b 0 : L) : mixedSpace K).2 w
  let a₁ := ((b 1 : L) : mixedSpace K).2 w
  have hvol : volume.real (ZSpan.fundamentalDomain s) = 1 := by
    rw [measureReal_def, ZSpan.fundamentalDomain_reindex, volume_fundamentalDomain_stdBasis]; simp
  have hdet : ZLattice.covolume L = |a₀.re * a₁.im - a₀.im * a₁.re| := by
    rw [ZLattice.covolume_eq_det_mul_measureReal L volume b s, hvol, mul_one, Basis.det_apply, Matrix.det_fin_two]
    change |a₀.re * a₁.im - a₁.re * a₀.im| = _
    rw [mul_comm a₁.re a₀.im]
  obtain ⟨u, v, hv, hshape⟩ := shape a₀ a₁ (ZLattice.covolume_pos L) hdet
  let e : ℤ × ℤ ≃ L := (Equiv.prodComm ℤ ℤ).trans ((finTwoArrowEquiv ℤ).symm.trans b.equivFun.toEquiv.symm)
  refine ⟨u, v, hv, e, fun p => ?_⟩
  have hcoord : e p = p.2 • b 0 + p.1 • b 1 := by
    change b.equivFun.symm ((finTwoArrowEquiv ℤ).symm (p.2, p.1)) = _
    rw [Basis.equivFun_symm_apply, Fin.sum_univ_two]; rfl
  have hnorm (x : mixedSpace K) : mixedEmbedding.norm x = Complex.normSq (x.2 w) := by
    rw [mixedEmbedding.norm_apply, Fintype.prod_unique, show (default : InfinitePlace K) = w.1 from Subsingleton.elim _ _,
      w.2.mult_eq_two, normAtPlace_apply_of_isComplex w.2, Complex.sq_norm]
  rw [hnorm, hcoord]
  change Complex.normSq (p.2 • a₀ + p.1 • a₁) / _ = _
  simpa only [zsmul_eq_mul] using hshape p.2 p.1

/-- Summing over inverse class representatives counts each ideal once for each root of unity. -/
theorem lattice_coeff_sum (hc : Fintype.card (InfinitePlace K) = 1)
    (J : ClassGroup (𝓞 K) → (Ideal (𝓞 K))⁰) (hJ : ∀ C, ClassGroup.mk0 (J C) = C⁻¹) {n : ℕ} (hn : 0 < n) :
    (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n}) * torsionOrder K =
      ∑ C : ClassGroup (𝓞 K), Nat.card {x : mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K (J C)) //
        mixedEmbedding.norm (x : mixedSpace K) = (Ideal.absNorm ((J C) : Ideal (𝓞 K)) * n : ℕ)} := by
  let ClassFiber (C : ClassGroup (𝓞 K)) (n : ℕ) :=
    {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) = n ∧ ClassGroup.mk0 I = C}
  have class_norm_to_principal {C : ClassGroup (𝓞 K)} (J : (Ideal (𝓞 K))⁰)
      (hJ : ClassGroup.mk0 J = C⁻¹) (n : ℕ) :
      Nat.card (ClassFiber C n) = Nat.card {I : (Ideal (𝓞 K))⁰ //
        (J : Ideal (𝓞 K)) ∣ I ∧ IsPrincipal (I : Ideal (𝓞 K)) ∧
        Ideal.absNorm (I : Ideal (𝓞 K)) = Ideal.absNorm (J : Ideal (𝓞 K)) * n} := by
    simp_rw [← nonZeroDivisors_dvd_iff_dvd_coe]
    apply Nat.card_congr
    refine ((Equiv.dvd J).subtypeEquiv (p := fun I : (Ideal (𝓞 K))⁰ => Ideal.absNorm (I : Ideal (𝓞 K)) = n ∧ ClassGroup.mk0 I = C) ?_).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter (fun I : (Ideal (𝓞 K))⁰ => J ∣ I) _)
    intro I
    rw [← ClassGroup.mk0_eq_one_iff (SetLike.coe_mem _)]
    simp only [Equiv.dvd_apply, Submonoid.coe_mul, ← Submonoid.mul_def, _root_.map_mul, hJ, inv_mul_eq_one,
      Nat.mul_right_inj (Ideal.absNorm_pos_of_nonZeroDivisors J).ne']
    tauto
  have class_count (C : ClassGroup (𝓞 K)) (J : (Ideal (𝓞 K))⁰) (hJ : ClassGroup.mk0 J = C⁻¹) (n : ℕ) :
      Nat.card (ClassFiber C n) * torsionOrder K =
        Nat.card {x : idealSet K J // mixedEmbedding.norm (x : mixedSpace K) =
          (Ideal.absNorm (J : Ideal (𝓞 K)) * n : ℕ)} := by
    rw [class_norm_to_principal J hJ n, torsionOrder, ← Nat.card_prod]
    exact Nat.card_congr (idealSetEquivNorm (K := K) (J := J) _).symm
  have coeff_eq_sum_classes {n : ℕ} (hn : n ≠ 0) :
      (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n}) = ∑ C : ClassGroup (𝓞 K), Nat.card (ClassFiber C n) := by
    classical
    let A := {I : Ideal (𝓞 K) // Ideal.absNorm I = n}
    let asNonzero (x : A) : (Ideal (𝓞 K))⁰ := ⟨x.1, mem_nonZeroDivisors_iff_ne_zero.mpr (by
      intro h; apply hn; rw [← x.2, h]; exact map_zero _)⟩
    let fieldClass (x : A) := ClassGroup.mk0 (asNonzero x)
    let e (C : ClassGroup (𝓞 K)) : {x : A // fieldClass x = C} ≃ ClassFiber C n := {
      toFun := fun x => ⟨asNonzero x.1, x.1.2, x.2⟩
      invFun := fun I => ⟨⟨I.1.1, I.2.1⟩, I.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    let : Finite A := (Ideal.finite_setOfPred_absNorm_eq n).to_subtype
    let (C : ClassGroup (𝓞 K)) : Finite (ClassFiber C n) := Finite.of_equiv _ (e C)
    rw [← Nat.card_sigma]
    exact Nat.card_congr ((Equiv.sigmaFiberEquiv fieldClass).symm.trans (Equiv.sigmaCongrRight e))
  have norm_cone_of_unique_place (hc : Fintype.card (InfinitePlace K) = 1) (x : mixedSpace K) :
      x ∈ fundamentalCone K ↔ mixedEmbedding.norm x ≠ 0 := by
    classical
    have hr : Units.rank K = 0 := by simp [Units.rank, hc]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      change logMap x ∈ ZSpan.fundamentalDomain _
      intro i
      have hi := i.isLt
      omega
  have lattice_count_single_place (hc : Fintype.card (InfinitePlace K) = 1)
      (C : ClassGroup (𝓞 K)) (J : (Ideal (𝓞 K))⁰) (hJ : ClassGroup.mk0 J = C⁻¹) {n : ℕ} (hn : 0 < n) :
      Nat.card (ClassFiber C n) * torsionOrder K =
        Nat.card {x : mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K J) //
          mixedEmbedding.norm (x : mixedSpace K) = (Ideal.absNorm (J : Ideal (𝓞 K)) * n : ℕ)} := by
    rw [class_count C J hJ n]
    have hpos : 0 < ((Ideal.absNorm (J : Ideal (𝓞 K)) * n : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_pos (Ideal.absNorm_pos_of_nonZeroDivisors J) hn
    apply Nat.card_congr
    exact {
      toFun := fun z => ⟨⟨z.1.1, z.1.2.2⟩, z.2⟩
      invFun := fun z => ⟨⟨z.1.1, (norm_cone_of_unique_place hc _).2 (z.2.trans_ne hpos.ne'), z.1.2⟩, z.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [coeff_eq_sum_classes hn.ne', Finset.sum_mul]
  exact Finset.sum_congr rfl fun C _ => lattice_count_single_place hc C (J C) (hJ C) hn

theorem exists_grade (J : (Ideal (𝓞 K))⁰) (x : (idealLattice K (FractionalIdeal.mk0 K J))) :
    ∃ n : ℕ, mixedEmbedding.norm (x : mixedSpace K) = (Ideal.absNorm (J : Ideal (𝓞 K)) * n : ℕ) := by
  obtain ⟨y, hy, hyx⟩ := (mem_idealLattice K _).mp x.2
  change y ∈ ((FractionalIdeal.mk0 K J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) at hy
  rw [FractionalIdeal.coe_mk0, FractionalIdeal.mem_coeIdeal] at hy
  obtain ⟨a, ha, rfl⟩ := hy
  obtain ⟨n, hn⟩ := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).mpr ha)
  refine ⟨n, ?_⟩
  rw [← hyx, mixedEmbedding.norm_eq_norm, ← hn, Ideal.absNorm_span_singleton]
  change ((|Algebra.norm ℚ (a : K)| : ℚ) : ℝ) = _
  simp [← Algebra.coe_norm_int, Nat.cast_natAbs, Int.cast_abs]

theorem fiber_zero (J : (Ideal (𝓞 K))⁰) : Nat.card {x : idealLattice K (FractionalIdeal.mk0 K J) // mixedEmbedding.norm (x : mixedSpace K) = (Ideal.absNorm (J : Ideal (𝓞 K)) * 0 : ℕ)} = 1 := by
  let : Unique {x : idealLattice K (FractionalIdeal.mk0 K J) // mixedEmbedding.norm (x : mixedSpace K) = (Ideal.absNorm (J : Ideal (𝓞 K)) * 0 : ℕ)} := {
    default := ⟨0, by simp⟩
    uniq := fun x => by
      apply Subtype.ext
      apply Subtype.ext
      obtain ⟨y, _, hy⟩ := (mem_idealLattice K _).mp x.1.2
      apply (mixedEmbedding.norm_eq_zero_iff' ⟨y, hy⟩).mp
      simpa using x.2 }
  exact Nat.card_unique

/-- Each class theta series is reciprocal and has a norm expansion including its origin. -/
theorem ideal_theta_data (hR : nrRealPlaces K = 0) (hC : nrComplexPlaces K = 1) (J : (Ideal (𝓞 K))⁰) :
    let q := 2 * Real.pi / Real.sqrt ((discr K).natAbs : ℝ)
    ∃ T : ℝ → ℂ, (∀ t : ℝ, 0 < t → T (1 / t) = (t : ℂ) * T t) ∧
      ∀ t : ℝ, 0 < t → HasSum (fun n : ℕ =>
        (Nat.card {x : idealLattice K (FractionalIdeal.mk0 K J) // mixedEmbedding.norm (x : mixedSpace K) = (Ideal.absNorm (J : Ideal (𝓞 K)) * n : ℕ)} : ℂ) * (Real.exp (-(q * t * n)) : ℂ)) (T t) := by
  let grade (J : (Ideal (𝓞 K))⁰) (x : (idealLattice K (FractionalIdeal.mk0 K J))) : ℕ := (exists_grade K J x).choose
  have grade_eq_iff (J : (Ideal (𝓞 K))⁰) (x : (idealLattice K (FractionalIdeal.mk0 K J))) (n : ℕ) :
      grade J x = n ↔ mixedEmbedding.norm (x : mixedSpace K) = (Ideal.absNorm (J : Ideal (𝓞 K)) * n : ℕ) := by
    rw [(exists_grade K J x).choose_spec, Nat.cast_inj, Nat.mul_right_inj (Ideal.absNorm_pos_of_nonZeroDivisors J).ne']
  let scale : ℝ := 2 * Real.pi / Real.sqrt ((discr K).natAbs : ℝ)
  let gaussian (J : (Ideal (𝓞 K))⁰) (t : ℝ) (x : (idealLattice K (FractionalIdeal.mk0 K J))) : ℂ :=
    Real.exp (-Real.pi * (mixedEmbedding.norm (x : mixedSpace K) / ZLattice.covolume ((idealLattice K (FractionalIdeal.mk0 K J)))) * t)
  let theta (J : (Ideal (𝓞 K))⁰) (t : ℝ) : ℂ := ∑' x, gaussian J t x
  have theta_spec (J : (Ideal (𝓞 K))⁰) {t : ℝ} (ht : 0 < t) :
      Summable (gaussian J t) ∧ theta J (1 / t) = (t : ℂ) * theta J t := by
    obtain ⟨u, v, hv, e, he⟩ := model K hR hC J
    let W (s : ℝ) (p : ℤ × ℤ) : ℂ := Real.exp (-Real.pi * (((p.2 : ℝ) + u * p.1) ^ 2 / v + v * (p.1 : ℝ) ^ 2) * s)
    obtain ⟨hS, hI⟩ := planar_gaussian u v hv
    have hw (s : ℝ) (p : ℤ × ℤ) : gaussian J s (e p) = W s p := by simp only [gaussian, he p, W]
    have heq (s : ℝ) : theta J s = ∑' p, W s p := by
      dsimp only [theta]
      rw [← e.tsum_eq]
      exact tsum_congr (hw s)
    exact ⟨e.summable_iff.mp ((hS t ht).congr fun p => (hw t p).symm), by rw [heq, heq, hI t ht]⟩
  let Fiber (J : (Ideal (𝓞 K))⁰) (n : ℕ) := {x : (idealLattice K (FractionalIdeal.mk0 K J)) //
    mixedEmbedding.norm (x : mixedSpace K) = (Ideal.absNorm (J : Ideal (𝓞 K)) * n : ℕ)}
  let coeffTerm (J : (Ideal (𝓞 K))⁰) (t : ℝ) (n : ℕ) : ℂ :=
    (Nat.card (Fiber J n) : ℂ) * (Real.exp (-(scale * t * n)) : ℂ)
  have theta_series (J : (Ideal (𝓞 K))⁰)
      {t : ℝ} (ht : 0 < t) : HasSum (coeffTerm J t) (theta J t) := by
    have hS := ((theta_spec J ht).1.hasSum.tsum_fiberwise (grade J))
    have hN : (Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ) ≠ 0 := by exact_mod_cast (Ideal.absNorm_pos_of_nonZeroDivisors J).ne'
    have hD : Real.sqrt ((discr K).natAbs : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast Int.natAbs_pos.mpr (discr_ne_zero K))).ne'
    have hw (n : ℕ) (x : grade J ⁻¹' {n}) : gaussian J t x.1 = (Real.exp (-(scale * t * n)) : ℂ) := by
      have hx := (grade_eq_iff J x.1 n).mp x.2
      simp only [gaussian, hx, area K hC J, scale, Nat.cast_mul]
      congr 2; field_simp
    apply hS.congr_fun
    intro n
    simp_rw [hw n]
    rw [tsum_const, nsmul_eq_mul]
    dsimp only [coeffTerm]
    congr 2
    exact Nat.card_congr (Equiv.subtypeEquivRight (fun x => (grade_eq_iff J x n).symm))
  exact ⟨theta J, fun t ht => (theta_spec J ht).2, fun t ht => theta_series J ht⟩

/-- The constant comes from the single origin in each class and the unit multiplicity. -/
theorem imaginary_quadratic_poisson (hR : nrRealPlaces K = 0) (hC : nrComplexPlaces K = 1) {x : ℝ} (hx : 0 < x) :
    let f := mellinInv 2 (fun s => exp (s * (Real.log (discr K).natAbs / 2 : ℝ)) * Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K * dedekindZeta K s)
    f (1 / x) + 2 * classNumber K / torsionOrder K = (x : ℂ) * (f x + 2 * classNumber K / torsionOrder K) := by
  let f := mellinInv 2 (fun s => exp (s * (Real.log (discr K).natAbs / 2 : ℝ)) * Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K * dedekindZeta K s)
  let scale := 2 * Real.pi / Real.sqrt ((discr K).natAbs : ℝ)
  let coeff (n : ℕ) := Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n}
  let fiber (J : (Ideal (𝓞 K))⁰) (n : ℕ) := {x : idealLattice K (FractionalIdeal.mk0 K J) // mixedEmbedding.norm (x : mixedSpace K) = (Ideal.absNorm (J : Ideal (𝓞 K)) * n : ℕ)}
  let term (J : (Ideal (𝓞 K))⁰) (t : ℝ) (n : ℕ) : ℂ := (Nat.card (fiber J n) : ℂ) * (Real.exp (-(scale * t * n)) : ℂ)
  choose J hJ using fun C : ClassGroup (𝓞 K) => ClassGroup.mk0_surjective C⁻¹
  choose T hInv hSer using fun C => ideal_theta_data K hR hC (J C)
  have all_classes
      {t : ℝ} (ht : 0 < t) :
      ∑ C, T C t = (classNumber K : ℂ) + (torsionOrder K : ℂ) *
        ∑' n : ℕ, if n = 0 then 0 else (coeff n : ℂ) * (Real.exp (-(scale * t * n)) : ℂ) := by
    have hc : Fintype.card (InfinitePlace K) = 1 := by rw [card_eq_nrRealPlaces_add_nrComplexPlaces, hR, hC]
    let a (n : ℕ) : ℂ := if n = 0 then classNumber K else
      (torsionOrder K : ℂ) * (coeff n : ℂ) * (Real.exp (-(scale * t * n)) : ℂ)
    have hsum : HasSum (fun n => ∑ C, term (J C) t n) (∑ C, T C t) :=
      hasSum_sum fun C _ => hSer C t ht
    have ha : HasSum a (∑ C, T C t) := by
      apply hsum.congr_fun
      intro n
      by_cases hn : n = 0
      · subst n
        have hzero (C : ClassGroup (𝓞 K)) : Nat.card (fiber (J C) 0) = 1 := fiber_zero K (J C)
        simp [a, term, hzero, classNumber]
      · simp only [a, if_neg hn, term, ← Finset.sum_mul]
        congr 1
        rw [← Nat.cast_sum, ← lattice_coeff_sum K hc J hJ (Nat.pos_of_ne_zero hn), Nat.cast_mul, mul_comm]
    rw [← ha.tsum_eq, ha.summable.tsum_eq_add_tsum_ite 0, show a 0 = (classNumber K : ℂ) by simp [a], ← tsum_mul_left]
    congr 1
    apply tsum_congr
    intro n
    by_cases hn : n = 0 <;> simp [a, hn, mul_assoc]
  have kernel_theta
      {t : ℝ} (ht : 0 < t) :
      f t + 2 * classNumber K / torsionOrder K = (2 / (torsionOrder K : ℂ)) * ∑ C, T C t := by
    dsimp only [f]
    rw [all_classes ht, kernel_expansion_of_signature K hR hC ht]
    dsimp only [scale, coeff]
    have hw : (torsionOrder K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (torsionOrder_ne_zero K)
    field_simp
    exact add_comm _ _
  change f (1 / x) + _ = (x : ℂ) * (f x + _)
  rw [kernel_theta (one_div_pos.mpr hx), kernel_theta hx]
  simp_rw [hInv _ x hx]
  rw [← Finset.mul_sum, mul_left_comm]

theorem inversion_of_one_le {f : ℝ → ℂ} {c : ℂ}
    (h : ∀ x : ℝ, 1 ≤ x → f (1 / x) + c = (x : ℂ) * (f x + c)) :
    ∀ x : ℝ, 0 < x → f (1 / x) + c = (x : ℂ) * (f x + c) := by
  intro x hx
  rcases le_total 1 x with hx' | hx'
  · exact h x hx'
  · have he := h x⁻¹ ((one_le_inv₀ hx).mpr hx')
    simp only [one_div, inv_inv, ofReal_inv] at he ⊢
    simpa only [← mul_assoc, mul_inv_cancel₀ (ofReal_ne_zero.mpr hx.ne'), one_mul] using (congrArg ((x : ℂ) * ·) he).symm

theorem main : H1 → H2 → OMA.R_ERH_extended_riemann_hypothesis_R1_H1_R1.H2 := by
  intro hReal hHigher K _ _ hdeg
  by_cases hd : 3 ≤ Module.finrank ℚ K
  · exact ⟨_, inversion_of_one_le (hHigher K hd)⟩
  have htwo : Module.finrank ℚ K = 2 := by omega
  by_cases hC : nrComplexPlaces K = 0
  · exact ⟨_, inversion_of_one_le (hReal K htwo hC)⟩
  have hdSig := card_add_two_mul_card_eq_rank K
  have hR : nrRealPlaces K = 0 := by omega
  have hOne : nrComplexPlaces K = 1 := by omega
  exact ⟨_, fun x hx => imaginary_quadratic_poisson K hR hOne hx⟩

end OMA.R_ERH_extended_riemann_hypothesis_R1_H1_R1_H2_R1
