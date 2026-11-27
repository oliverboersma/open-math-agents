import FormalConjectures.GreensOpenProblems.«54»
import Mathlib

/-!
# Counterexample to the 2-summand version of Talagrand's convexity conjecture

We prove `Green54.green_54_known_case`: there exists a compact balanced set `K ⊂ ℝ^ℕ` with
`γ_∞(K) ≥ 0.99` such that `K + K` contains no compact convex set `C` with `γ_∞(C) ≥ 0.01`.

## Proof outline
1. Fix `c = √(2 / π)` (the mean of `|Z|` for `Z ~ N(0, 1)`) and `α = exp(-π² / (2c²)) / 2 > 0`.
2. In `ℝ^N` (for large `N`), let
   `A = { x : I → ℝ | ∀ λ ∈ [-1, 1], (1 / N) ∑ i, cos(π λ x_i / c) ≥ α }`.
   Then `A` is closed (hence measurable) and balanced. By the characteristic function of `N(0, 1)`,
   Chebyshev's inequality, and a finite net on `[-1, 1]`, `γ_N(A) > 0.99` for large `N`.
3. For every `u = x + y ∈ A + A`, the identity `cos a + cos b = 2 cos((a+b)/2) cos((a-b)/2)`
   implies `(1 / N) ∑ i, |cos(π u_i / (2c))| ≥ α`.
4. Conversely, for any compact convex `C ⊂ ℝ^N` with `γ_N(C) ≥ 0.01`, pigeonhole over the `2^N`
   orthants gives a sign vector `ε ∈ {±1}^N` such that `D = Φ_ε⁻¹(C) ∩ [0, ∞)^N` has conditioned
   measure `ν_+(D) ≥ 0.01`. The barycenter `y₀` of `ν_+|_D` satisfies `u := Φ_ε(y₀) ∈ C` and,
   by Cauchy–Schwarz on `L²(ν_+)`, `∑_i (y₀ i - c)² ≤ 100`. Since `cos(±π/2) = 0`, Lipschitzness
   of `cos` gives `(1 / N) ∑ i, |cos(π u_i / (2c))| ≤ 5π / (c √N) < α` for large `N`,
   contradicting `C ⊆ A + A`.
5. Inner regularity of `γ_∞` on the Polish space `ℝ^ℕ` produces a compact balanced `K` inside the
   cylinder over `A` with `γ_∞(K) ≥ 0.99`.
-/

namespace Green54Counterexample

open MeasureTheory ProbabilityTheory Set Filter
open scoped Pointwise ENNReal BigOperators

/- ### Section 1: 1D standard Gaussian integrals -/

noncomputable abbrev γ1 : Measure ℝ := gaussianReal 0 1

noncomputable def c0 : ℝ := Real.sqrt (2 / Real.pi)

noncomputable def α0 : ℝ := Real.exp (-(Real.pi ^ 2 / (2 * c0 ^ 2))) / 2

lemma c0_pos : 0 < c0 := by
  unfold c0
  exact Real.sqrt_pos.mpr (div_pos (by norm_num) Real.pi_pos)

lemma α0_pos : 0 < α0 := by
  unfold α0
  positivity

lemma γ1_map_neg : Measure.map (fun x : ℝ => -x) γ1 = γ1 := by
  unfold γ1
  rw [gaussianReal_map_neg, neg_zero]

lemma γ1_singleton_zero : γ1 ({0} : Set ℝ) = 0 := by
  unfold γ1
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero]
  rw [withDensity_apply _ (measurableSet_singleton 0)]
  simp

lemma γ1_Ici_zero : γ1 (Ici (0 : ℝ)) = 1 / 2 := by
  have hsym : γ1 (Iic (0 : ℝ)) = γ1 (Ici (0 : ℝ)) := by
    have hpre : (fun x : ℝ => -x) ⁻¹' Ici (0 : ℝ) = Iic (0 : ℝ) := by
      ext x; simp
    rw [← hpre, ← Measure.map_apply measurable_neg measurableSet_Ici, γ1_map_neg]
  have hunion : Ici (0 : ℝ) ∪ Iic (0 : ℝ) = univ := by
    ext x; simp
  have hinter : Ici (0 : ℝ) ∩ Iic (0 : ℝ) = {0} := by
    ext x; simp [le_antisymm_iff, and_comm]
  have hadd : γ1 (Ici (0 : ℝ)) + γ1 (Iic (0 : ℝ)) = 1 := by
    have h1 := measure_union_add_inter (μ := γ1) (s := Ici (0 : ℝ)) (t := Iic (0 : ℝ))
      measurableSet_Iic
    rw [hunion, hinter, γ1_singleton_zero, add_zero, measure_univ] at h1
    exact h1.symm
  rw [hsym] at hadd
  have h2 : (2 : ℝ≥0∞) * γ1 (Ici (0 : ℝ)) = 1 := by
    rw [two_mul]; exact hadd
  have hne2 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have htop2 : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  calc γ1 (Ici (0 : ℝ)) = (2 : ℝ≥0∞)⁻¹ * ((2 : ℝ≥0∞) * γ1 (Ici (0 : ℝ))) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hne2 htop2, one_mul]
    _ = (2 : ℝ≥0∞)⁻¹ * 1 := by rw [h2]
    _ = 1 / 2 := by rw [mul_one, one_div]

lemma integral_cos_γ1 (t : ℝ) : ∫ x, Real.cos (t * x) ∂γ1 = Real.exp (-(t ^ 2 / 2)) := by
  have hcf := ProbabilityTheory.charFun_gaussianReal (μ := (0 : ℝ)) (v := (1 : NNReal)) t
  have h1 : (MeasureTheory.charFun γ1 t).re = Real.exp (-(t ^ 2 / 2)) := by
    rw [show γ1 = gaussianReal 0 1 from rfl, hcf]
    simp only [Complex.ofReal_zero, mul_zero, zero_mul, zero_sub, NNReal.coe_one,
      Complex.ofReal_one, one_mul]
    rw [show -((t : ℂ) ^ 2 / 2) = ((-(t ^ 2 / 2) : ℝ) : ℂ) by push_cast; ring]
    rw [← Complex.ofReal_exp, Complex.ofReal_re]
  rw [← h1, MeasureTheory.charFun_apply_real]
  have hint : Integrable (fun x : ℝ => Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)) γ1 := by
    refine Integrable.of_bound (by fun_prop) 1 (Filter.Eventually.of_forall fun x => ?_)
    rw [← Complex.ofReal_mul, Complex.norm_exp_ofReal_mul_I]
  change ∫ x, Real.cos (t * x) ∂γ1 = RCLike.re (∫ x, Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) ∂γ1)
  rw [← integral_re hint]
  congr 1; ext x
  change Real.cos (t * x) = (Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)).re
  rw [← Complex.ofReal_mul, Complex.exp_mul_I, Complex.add_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.cos_ofReal_re, Complex.sin_ofReal_im]
  ring

lemma integrable_id_γ1 : Integrable (fun x : ℝ => x) γ1 :=
  (memLp_id_gaussianReal 1).integrable le_rfl

lemma integrable_sq_γ1 : Integrable (fun x : ℝ => x ^ 2) γ1 := by
  have h := memLp_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : NNReal)) 2
  simpa [sq] using h.integrable_sq

lemma integral_sq_γ1 : ∫ x : ℝ, x ^ 2 ∂γ1 = 1 := by
  have hv := ProbabilityTheory.variance_fun_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : NNReal))
  rw [ProbabilityTheory.variance_eq_integral (by fun_prop)] at hv
  have hm : ∫ x : ℝ, x ∂γ1 = 0 := by
    simp [γ1]
  simpa [γ1, hm] using hv

lemma integral_Ici_id_γ1 : ∫ x in Ici (0 : ℝ), x ∂γ1 = c0 / 2 := by
  have hpdf : γ1 = volume.withDensity (gaussianPDF 0 1) :=
    gaussianReal_of_var_ne_zero 0 one_ne_zero
  rw [hpdf, restrict_withDensity measurableSet_Ici,
    integral_withDensity_eq_integral_toReal_smul (measurable_gaussianPDF 0 1)
      (ae_of_all _ fun _ => gaussianPDF_lt_top)]
  have hrew : ∫ x in Ici (0 : ℝ), (gaussianPDF 0 1 x).toReal • x =
      (Real.sqrt (2 * Real.pi))⁻¹ * ∫ x in Ioi (0 : ℝ), x * Real.exp (-(x ^ 2 / 2)) := by
    rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
    rw [← MeasureTheory.integral_const_mul]
    congr 1; ext x
    simp only [smul_eq_mul, ProbabilityTheory.gaussianPDF, ProbabilityTheory.gaussianPDFReal_def,
      NNReal.coe_one, mul_one, sub_zero]
    rw [ENNReal.toReal_ofReal (by positivity)]
    ring
  rw [hrew]
  have hderiv : ∀ x ∈ Ici (0 : ℝ),
      HasDerivAt (fun t : ℝ => -Real.exp (-(t ^ 2 / 2))) (x * Real.exp (-(x ^ 2 / 2))) x := by
    intro x _
    have h1 : HasDerivAt (fun t : ℝ => -(t ^ 2 / 2)) (-x) x := by
      have h := ((hasDerivAt_pow 2 x).div_const 2).fun_neg
      simpa [show -((2 : ℝ) * x ^ (2 - 1) / 2) = -x by norm_num] using h
    have h2 := ((Real.hasDerivAt_exp (-(x ^ 2 / 2))).comp x h1).fun_neg
    simpa [mul_comm] using h2
  have htend : Tendsto (fun t : ℝ => -Real.exp (-(t ^ 2 / 2))) atTop (nhds 0) := by
    rw [show (0 : ℝ) = -0 by ring]
    refine Filter.Tendsto.neg ?_
    refine Real.tendsto_exp_atBot.comp ?_
    have hsq : Tendsto (fun t : ℝ => t ^ 2 / 2) atTop atTop :=
      (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).atTop_div_const (by norm_num : (0 : ℝ) < 2)
    exact Filter.tendsto_neg_atTop_atBot.comp hsq
  have hint_pos : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ x * Real.exp (-(x ^ 2 / 2)) := fun x hx =>
    mul_nonneg (le_of_lt hx) (Real.exp_pos _).le
  have hval : ∫ x in Ioi (0 : ℝ), x * Real.exp (-(x ^ 2 / 2)) = 0 - (-Real.exp (-(0 ^ 2 / 2))) :=
    integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hint_pos htend
  rw [hval]
  simp only [sq, mul_zero, zero_div, neg_zero, Real.exp_zero, sub_neg_eq_add, zero_add, mul_one]
  unfold c0
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  field_simp
  nlinarith [hsq2, Real.sqrt_pos.mpr hpi]

lemma integral_Ici_sq_γ1 : ∫ x in Ici (0 : ℝ), x ^ 2 ∂γ1 = 1 / 2 := by
  have hsym : ∫ x in Iic (0 : ℝ), x ^ 2 ∂γ1 = ∫ x in Ici (0 : ℝ), x ^ 2 ∂γ1 := by
    have hpre : (fun x : ℝ => -x) ⁻¹' Ici (0 : ℝ) = Iic (0 : ℝ) := by ext x; simp
    have hmp : MeasurePreserving (fun x : ℝ => -x) γ1 γ1 := ⟨measurable_neg, γ1_map_neg⟩
    have h := hmp.setIntegral_preimage_emb (MeasurableEquiv.neg ℝ).measurableEmbedding
      (fun x => x ^ 2) (Ici 0)
    rw [hpre] at h
    simpa [sq] using h
  have hunion : Ici (0 : ℝ) ∪ Iic (0 : ℝ) = univ := by ext x; simp
  have hae : AEDisjoint γ1 (Ici (0 : ℝ)) (Iic (0 : ℝ)) := by
    change γ1 (Ici (0 : ℝ) ∩ Iic (0 : ℝ)) = 0
    have hinter : Ici (0 : ℝ) ∩ Iic (0 : ℝ) = {0} := by ext x; simp [le_antisymm_iff, and_comm]
    rw [hinter, γ1_singleton_zero]
  have hsum := MeasureTheory.integral_union_ae hae measurableSet_Iic.nullMeasurableSet
    integrable_sq_γ1.integrableOn integrable_sq_γ1.integrableOn
  rw [hunion, MeasureTheory.setIntegral_univ, integral_sq_γ1, hsym] at hsum
  linarith

/- ### Section 2: Conditioned 1D measure `γ1Plus` on `[0, ∞)` -/

noncomputable def γ1Plus : Measure ℝ := (2 : ℝ≥0∞) • γ1.restrict (Ici (0 : ℝ))

instance : IsProbabilityMeasure γ1Plus := by
  constructor
  unfold γ1Plus
  rw [Measure.smul_apply, Measure.restrict_apply_univ, γ1_Ici_zero, smul_eq_mul]
  rw [one_div, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]

lemma integral_γ1Plus (f : ℝ → ℝ) :
    ∫ x, f x ∂γ1Plus = 2 * ∫ x in Ici (0 : ℝ), f x ∂γ1 := by
  unfold γ1Plus
  rw [integral_smul_measure]
  simp

lemma integrable_id_γ1Plus : Integrable (fun x : ℝ => x) γ1Plus := by
  unfold γ1Plus
  exact integrable_id_γ1.integrableOn.smul_measure (by norm_num)

lemma integrable_sq_γ1Plus : Integrable (fun x : ℝ => x ^ 2) γ1Plus := by
  unfold γ1Plus
  exact integrable_sq_γ1.integrableOn.smul_measure (by norm_num)

lemma integral_sub_c0_γ1Plus : ∫ x, (x - c0) ∂γ1Plus = 0 := by
  rw [integral_sub integrable_id_γ1Plus (integrable_const c0)]
  rw [integral_γ1Plus, integral_Ici_id_γ1, integral_const, probReal_univ, one_smul]
  ring

lemma integral_sub_c0_sq_γ1Plus : ∫ x, (x - c0) ^ 2 ∂γ1Plus ≤ 1 := by
  have h1 : ∀ x : ℝ, (x - c0) ^ 2 = x ^ 2 - 2 * c0 * x + c0 ^ 2 := fun x => by ring
  simp_rw [h1]
  have hint1 : Integrable (fun x : ℝ => x ^ 2 - 2 * c0 * x) γ1Plus :=
    integrable_sq_γ1Plus.sub (integrable_id_γ1Plus.const_mul (2 * c0))
  rw [integral_add hint1 (integrable_const (c0 ^ 2))]
  rw [integral_sub integrable_sq_γ1Plus (integrable_id_γ1Plus.const_mul (2 * c0))]
  rw [integral_const_mul, integral_γ1Plus, integral_γ1Plus, integral_Ici_sq_γ1, integral_Ici_id_γ1]
  rw [integral_const, probReal_univ, one_smul]
  nlinarith [sq_nonneg c0]

/- ### Section 3: Product measures `μN` and `νPlus` on `I → ℝ` -/

noncomputable def μN (I : Finset ℕ) : Measure (I → ℝ) :=
  Measure.pi (fun _ : I => γ1)

noncomputable def νPlus (I : Finset ℕ) : Measure (I → ℝ) :=
  Measure.pi (fun _ : I => γ1Plus)

instance (I : Finset ℕ) : IsProbabilityMeasure (μN I) := by
  unfold μN; infer_instance

instance (I : Finset ℕ) : IsProbabilityMeasure (νPlus I) := by
  unfold νPlus; infer_instance

lemma integral_eval_pi {I : Finset ℕ} {ν : Measure ℝ} [IsProbabilityMeasure ν] (i : I)
    {f : ℝ → ℝ} (hf : AEStronglyMeasurable f ν) :
    ∫ x, f (x i) ∂(Measure.pi fun _ : I => ν) = ∫ t, f t ∂ν := by
  have hmp : MeasurePreserving (Function.eval i) (Measure.pi fun _ : I => ν) ν :=
    MeasureTheory.measurePreserving_eval (fun _ : I => ν) i
  have hmap : Measure.map (fun x : I → ℝ => x i) (Measure.pi fun _ : I => ν) = ν := hmp.map_eq
  conv_rhs => rw [← hmap]
  exact (MeasureTheory.integral_map (measurable_pi_apply i).aemeasurable (by rwa [hmap])).symm

lemma integrable_eval_pi {I : Finset ℕ} {ν : Measure ℝ} [IsProbabilityMeasure ν] (i : I)
    {f : ℝ → ℝ} (hf : Integrable f ν) :
    Integrable (fun x : I → ℝ => f (x i)) (Measure.pi fun _ : I => ν) := by
  have hmap : Measure.map (fun x : I → ℝ => x i) (Measure.pi fun _ : I => ν) = ν :=
    (MeasureTheory.measurePreserving_eval (fun _ : I => ν) i).map_eq
  rw [← hmap] at hf
  exact (integrable_map_measure hf.aestronglyMeasurable (measurable_pi_apply i).aemeasurable).mp hf

lemma integral_eval_μN (I : Finset ℕ) (i : I) {f : ℝ → ℝ} (hf : AEStronglyMeasurable f γ1) :
    ∫ x, f (x i) ∂(μN I) = ∫ t, f t ∂γ1 :=
  integral_eval_pi i hf

lemma integral_eval_νPlus (I : Finset ℕ) (i : I) {f : ℝ → ℝ} (hf : AEStronglyMeasurable f γ1Plus) :
    ∫ x, f (x i) ∂(νPlus I) = ∫ t, f t ∂γ1Plus :=
  integral_eval_pi i hf

lemma integrable_eval_μN (I : Finset ℕ) (i : I) {f : ℝ → ℝ} (hf : Integrable f γ1) :
    Integrable (fun x : I → ℝ => f (x i)) (μN I) :=
  integrable_eval_pi i hf

lemma integrable_eval_νPlus (I : Finset ℕ) (i : I) {f : ℝ → ℝ} (hf : Integrable f γ1Plus) :
    Integrable (fun x : I → ℝ => f (x i)) (νPlus I) :=
  integrable_eval_pi i hf

lemma integral_mul_eval_of_ne {I : Finset ℕ} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {i j : I} (hij : i ≠ j) {f g : ℝ → ℝ} (hf : Measurable f) (hg : Measurable g) :
    ∫ x, f (x i) * g (x j) ∂(Measure.pi fun _ : I => ν) =
      (∫ t, f t ∂ν) * (∫ t, g t ∂ν) := by
  have hind : iIndepFun (fun k (x : I → ℝ) => x k) (Measure.pi fun _ : I => ν) :=
    ProbabilityTheory.iIndepFun_pi (fun _ => aemeasurable_id)
  have hpair : IndepFun (fun x : I → ℝ => f (x i)) (fun x : I → ℝ => g (x j))
      (Measure.pi fun _ : I => ν) :=
    (hind.indepFun hij).comp hf hg
  rw [hpair.integral_fun_mul_eq_mul_integral (hf.comp (measurable_pi_apply i)).aestronglyMeasurable
    (hg.comp (measurable_pi_apply j)).aestronglyMeasurable]
  rw [integral_eval_pi i hf.aestronglyMeasurable, integral_eval_pi j hg.aestronglyMeasurable]

/- ### Section 4: Definition of `goodSet I` and proof that `μN I (goodSet I) > 0.99` -/

noncomputable def avgCos (I : Finset ℕ) (t : ℝ) (x : I → ℝ) : ℝ :=
  (I.card : ℝ)⁻¹ * ∑ i : I, Real.cos (t * x i)

def goodSet (I : Finset ℕ) : Set (I → ℝ) :=
  { x | ∀ lam ∈ Icc (-1 : ℝ) 1, α0 ≤ avgCos I (Real.pi * lam / c0) x }

lemma isClosed_goodSet (I : Finset ℕ) : IsClosed (goodSet I) := by
  have h : goodSet I = ⋂ lam ∈ Icc (-1 : ℝ) 1,
      { x : I → ℝ | α0 ≤ avgCos I (Real.pi * lam / c0) x } := by
    ext x; simp [goodSet]
  rw [h]
  refine isClosed_biInter fun lam _ => isClosed_le continuous_const ?_
  unfold avgCos
  fun_prop

lemma measurableSet_goodSet (I : Finset ℕ) : MeasurableSet (goodSet I) :=
  (isClosed_goodSet I).measurableSet

lemma balanced_goodSet (I : Finset ℕ) : Balanced ℝ (goodSet I) := by
  intro a ha
  rintro _ ⟨x, hx, rfl⟩ lam hlam
  have ha_abs : |a| ≤ 1 := by simpa [Real.norm_eq_abs] using ha
  have hlam_abs : |lam| ≤ 1 := abs_le.mpr (mem_Icc.mp hlam)
  have hmul : lam * a ∈ Icc (-1 : ℝ) 1 := by
    apply mem_Icc.mpr (abs_le.mp _)
    calc |lam * a| = |lam| * |a| := abs_mul lam a
      _ ≤ 1 * 1 := mul_le_mul hlam_abs ha_abs (abs_nonneg a) zero_le_one
      _ = 1 := one_mul 1
  have hstep := hx (lam * a) hmul
  convert hstep using 1
  unfold avgCos
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring_nf

lemma integral_avgCos_sub_sq_le (I : Finset ℕ) (hI : 0 < I.card) (t : ℝ) :
    ∫ x, (avgCos I t x - Real.exp (-(t ^ 2 / 2))) ^ 2 ∂(μN I) ≤ (I.card : ℝ)⁻¹ := by
  set m : ℝ := Real.exp (-(t ^ 2 / 2))
  set N : ℝ := (I.card : ℝ)
  have hN : 0 < N := Nat.cast_pos.mpr hI
  let f : ℝ → ℝ := fun s => Real.cos (t * s) - m
  have hf_meas : Measurable f := by fun_prop
  have hf_bd : ∀ s : ℝ, ‖f s‖ ≤ 1 + |m| := fun s => by
    calc ‖Real.cos (t * s) - m‖ ≤ ‖Real.cos (t * s)‖ + ‖m‖ := norm_sub_le _ _
      _ ≤ 1 + |m| := by
        rw [Real.norm_eq_abs, Real.norm_eq_abs]
        linarith [Real.abs_cos_le_one (t * s)]
  have hf_mean : ∫ s, f s ∂γ1 = 0 := by
    simp only [f]
    rw [integral_sub (Integrable.of_bound (by fun_prop) 1 (Filter.Eventually.of_forall fun s => by
      simpa [Real.norm_eq_abs] using Real.abs_cos_le_one (t * s))) (integrable_const m)]
    rw [integral_cos_γ1, integral_const, probReal_univ, one_smul, sub_self]
  have hf_sq_le : ∫ s, f s ^ 2 ∂γ1 ≤ 1 := by
    have hcos_int : Integrable (fun s => Real.cos (t * s)) γ1 :=
      Integrable.of_bound (by fun_prop) 1 (Filter.Eventually.of_forall fun s => by
        simpa [Real.norm_eq_abs] using Real.abs_cos_le_one (t * s))
    have hcos2_int : Integrable (fun s => Real.cos (t * s) ^ 2) γ1 :=
      Integrable.of_bound (by fun_prop) 1 (Filter.Eventually.of_forall fun s => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        nlinarith [abs_le.mp (Real.abs_cos_le_one (t * s))])
    have hsub_int : Integrable (fun s => Real.cos (t * s) ^ 2 - 2 * m * Real.cos (t * s)) γ1 :=
      hcos2_int.sub (hcos_int.const_mul (2 * m))
    have hexp : ∀ s, f s ^ 2 = (Real.cos (t * s) ^ 2 - 2 * m * Real.cos (t * s)) + m ^ 2 :=
      fun s => by simp only [f]; ring
    simp_rw [hexp]
    rw [integral_add hsub_int (integrable_const (m ^ 2))]
    rw [integral_sub hcos2_int (hcos_int.const_mul (2 * m)), integral_const_mul, integral_cos_γ1]
    rw [integral_const, probReal_univ, one_smul]
    have hle1 : ∫ s, Real.cos (t * s) ^ 2 ∂γ1 ≤ ∫ _ : ℝ, (1 : ℝ) ∂γ1 :=
      integral_mono hcos2_int (integrable_const 1) fun s => by
        nlinarith [abs_le.mp (Real.abs_cos_le_one (t * s))]
    rw [integral_const, probReal_univ, one_smul] at hle1
    nlinarith [sq_nonneg m]
  have hrew : ∀ x : I → ℝ, (avgCos I t x - m) ^ 2 =
      N⁻¹ ^ 2 * ∑ i : I, ∑ j : I, f (x i) * f (x j) := by
    intro x
    have hsum_m : ∑ _ : I, m = N * m := by simp [N]
    have hdiff : avgCos I t x - m = N⁻¹ * ∑ i : I, f (x i) := by
      unfold avgCos
      simp only [f, Finset.sum_sub_distrib, hsum_m, mul_sub]
      rw [inv_mul_cancel_left₀ hN.ne']
    rw [hdiff, mul_pow, sq (∑ i : I, f (x i)), Finset.sum_mul_sum]
  simp_rw [hrew]
  rw [integral_const_mul]
  have hint_prod : ∀ i j : I, Integrable (fun x : I → ℝ => f (x i) * f (x j)) (μN I) := by
    intro i j
    refine Integrable.of_bound (by fun_prop) ((1 + |m|) * (1 + |m|)) (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul]
    exact mul_le_mul (hf_bd (x i)) (hf_bd (x j)) (norm_nonneg _) (by positivity)
  rw [integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => hint_prod i j]
  have hinner : ∀ i : I, ∫ x, (∑ j : I, f (x i) * f (x j)) ∂(μN I) = ∫ s, f s ^ 2 ∂γ1 := by
    intro i
    rw [integral_finset_sum _ fun j _ => hint_prod i j]
    rw [Finset.sum_eq_single i]
    · simp_rw [← sq]
      exact integral_eval_μN I i (f := fun s => f s ^ 2) (by fun_prop)
    · intro j _ hji
      rw [μN, integral_mul_eval_of_ne hji.symm hf_meas hf_meas, hf_mean, mul_zero]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  simp_rw [hinner]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
  calc N⁻¹ ^ 2 * (N * ∫ s, f s ^ 2 ∂γ1) ≤ N⁻¹ ^ 2 * (N * 1) := by gcongr
    _ = N⁻¹ := by field_simp [hN.ne']

lemma measure_avgCos_lt_le (I : Finset ℕ) (hI : 0 < I.card) (lam : ℝ) (hlam : lam ∈ Icc (-1 : ℝ) 1) :
    μN I { x | avgCos I (Real.pi * lam / c0) x < 3 / 2 * α0 } ≤
      ENNReal.ofReal (4 / (α0 ^ 2 * (I.card : ℝ))) := by
  set t : ℝ := Real.pi * lam / c0
  set m : ℝ := Real.exp (-(t ^ 2 / 2))
  have hc0 : 0 < c0 := c0_pos
  have hα0 : 0 < α0 := α0_pos
  have hN_pos : (0 : ℝ) < I.card := Nat.cast_pos.mpr hI
  have hm_ge : 2 * α0 ≤ m := by
    unfold α0
    have hlam2 : lam ^ 2 ≤ 1 := by
      have h1 := mem_Icc.mp hlam
      nlinarith
    have hdiv : t ^ 2 / 2 ≤ Real.pi ^ 2 / (2 * c0 ^ 2) := by
      simp only [t]
      rw [div_pow, mul_pow, div_div, mul_comm (c0 ^ 2) 2]
      have hden : 0 < 2 * c0 ^ 2 := by positivity
      rw [div_le_div_iff_of_pos_right hden]
      nlinarith [sq_nonneg Real.pi]
    have hexp := Real.exp_le_exp.mpr (neg_le_neg hdiv)
    linarith
  have hsub : { x : I → ℝ | avgCos I t x < 3 / 2 * α0 } ⊆
      { x : I → ℝ | (α0 / 2) ^ 2 ≤ (avgCos I t x - m) ^ 2 } := by
    intro x hx
    simp only [mem_setOf_eq] at hx ⊢
    have h1 : α0 / 2 ≤ m - avgCos I t x := by linarith
    have h2 : 0 ≤ α0 / 2 := by linarith
    nlinarith
  refine (measure_mono hsub).trans ?_
  have hsq_int : Integrable (fun x : I → ℝ => (avgCos I t x - m) ^ 2) (μN I) := by
    have hcont : Continuous (fun x : I → ℝ => (avgCos I t x - m) ^ 2) := by
      unfold avgCos; fun_prop
    refine Integrable.of_bound hcont.aestronglyMeasurable ((1 + |m|) ^ 2) (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have havg : |avgCos I t x| ≤ 1 := by
      unfold avgCos
      rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
      calc (I.card : ℝ)⁻¹ * |∑ i : I, Real.cos (t * x i)|
          ≤ (I.card : ℝ)⁻¹ * ∑ i : I, |Real.cos (t * x i)| := by
            gcongr; exact Finset.abs_sum_le_sum_abs _ _
        _ ≤ (I.card : ℝ)⁻¹ * ∑ _ : I, (1 : ℝ) := by
            gcongr with i _; exact Real.abs_cos_le_one _
        _ = 1 := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul, mul_one]
            exact inv_mul_cancel₀ hN_pos.ne'
    have hle : |avgCos I t x - m| ≤ 1 + |m| := by
      calc |avgCos I t x - m| ≤ |avgCos I t x| + |m| := abs_sub _ _
        _ ≤ 1 + |m| := by linarith
    nlinarith [abs_nonneg (avgCos I t x - m), sq_abs (avgCos I t x - m)]
  have hmarkov := mul_meas_ge_le_integral_of_nonneg (μ := μN I) (f := fun x => (avgCos I t x - m) ^ 2)
    (Filter.Eventually.of_forall fun x => sq_nonneg _) hsq_int ((α0 / 2) ^ 2)
  have hpos : 0 < (α0 / 2) ^ 2 := by positivity
  have hreal : (μN I).real { x | (α0 / 2) ^ 2 ≤ (avgCos I t x - m) ^ 2 } ≤
      4 / (α0 ^ 2 * (I.card : ℝ)) := by
    have h1 := hmarkov.trans (integral_avgCos_sub_sq_le I hI t)
    have h2 : (μN I).real { x | (α0 / 2) ^ 2 ≤ (avgCos I t x - m) ^ 2 } ≤
        (I.card : ℝ)⁻¹ / (α0 / 2) ^ 2 := (le_div_iff₀' hpos).mpr h1
    refine h2.trans_eq ?_
    field_simp [hα0.ne', hN_pos.ne']
    ring
  rw [← ENNReal.ofReal_toReal (measure_ne_top (μN I) _)]
  exact ENNReal.ofReal_le_ofReal hreal

lemma measure_sq_avg_gt_le (I : Finset ℕ) (hI : 0 < I.card) :
    μN I { x | (200 : ℝ) < (I.card : ℝ)⁻¹ * ∑ i : I, x i ^ 2 } ≤ ENNReal.ofReal (1 / 200) := by
  have hN_pos : (0 : ℝ) < I.card := Nat.cast_pos.mpr hI
  set g : (I → ℝ) → ℝ := fun x => (I.card : ℝ)⁻¹ * ∑ i : I, x i ^ 2
  have hg_int : Integrable g (μN I) :=
    (integrable_finset_sum _ fun i _ => integrable_eval_μN I i integrable_sq_γ1).const_mul _
  have hg_mean : ∫ x, g x ∂(μN I) = 1 := by
    simp only [g]
    rw [integral_const_mul, integral_finset_sum _ fun i _ => integrable_eval_μN I i integrable_sq_γ1]
    simp_rw [integral_eval_μN I _ (by fun_prop : AEStronglyMeasurable (fun s : ℝ => s ^ 2) γ1),
      integral_sq_γ1]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul, mul_one]
    exact inv_mul_cancel₀ hN_pos.ne'
  have hsub : { x : I → ℝ | (200 : ℝ) < g x } ⊆ { x : I → ℝ | (200 : ℝ) ≤ g x } := by
    intro x hx; exact le_of_lt (by simpa using hx)
  refine (measure_mono hsub).trans ?_
  have hmarkov := mul_meas_ge_le_integral_of_nonneg (μ := μN I) (f := g)
    (Filter.Eventually.of_forall fun x => mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun i _ => sq_nonneg _)) hg_int 200
  rw [hg_mean] at hmarkov
  have hreal : (μN I).real { x | (200 : ℝ) ≤ g x } ≤ 1 / 200 := by linarith
  rw [← ENNReal.ofReal_toReal (measure_ne_top (μN I) _)]
  exact ENNReal.ofReal_le_ofReal hreal

lemma exists_N_measure_goodSet_gt :
    ∃ N₀ : ℕ, ∀ I : Finset ℕ, N₀ ≤ I.card → (0.99 : ℝ≥0∞) < μN I (goodSet I) := by
  have hc0 : 0 < c0 := c0_pos
  have hα0 : 0 < α0 := α0_pos
  have hpi : 0 < Real.pi := Real.pi_pos
  set L : ℝ := 15 * Real.pi / c0
  have hL : 0 < L := by positivity
  obtain ⟨M, hM⟩ := exists_nat_gt (2 * L / α0)
  have hM_pos : 0 < M := by
    have : (0 : ℝ) < M := (by positivity : (0 : ℝ) < 2 * L / α0).trans hM
    exact Nat.cast_pos.mp this
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (((M : ℝ) + 1) * 4 / (α0 ^ 2 * 0.004))
  refine ⟨max N₀ 1, fun I hI => ?_⟩
  have hI_pos : 0 < I.card := lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_right _ _) hI)
  have hI_N0 : N₀ ≤ I.card := le_trans (le_max_left _ _) hI
  have hN_pos : (0 : ℝ) < I.card := Nat.cast_pos.mpr hI_pos
  let grid : Fin (M + 1) → ℝ := fun k => -1 + 2 * (k : ℝ) / (M : ℝ)
  have hgrid_mem : ∀ k : Fin (M + 1), grid k ∈ Icc (-1 : ℝ) 1 := by
    intro k
    simp only [grid, mem_Icc]
    have hk : (k : ℝ) ≤ (M : ℝ) := Nat.cast_le.mpr (Nat.le_of_lt_succ k.isLt)
    have hMp : (0 : ℝ) < M := Nat.cast_pos.mpr hM_pos
    constructor
    · have : 0 ≤ 2 * (k : ℝ) / (M : ℝ) := by positivity
      linarith
    · have : 2 * (k : ℝ) / (M : ℝ) ≤ 2 := by
        rw [div_le_iff₀ hMp]; linarith
      linarith
  let B0 : Set (I → ℝ) := { x | (200 : ℝ) < (I.card : ℝ)⁻¹ * ∑ i : I, x i ^ 2 }
  let Bk : Fin (M + 1) → Set (I → ℝ) := fun k =>
    { x | avgCos I (Real.pi * grid k / c0) x < 3 / 2 * α0 }
  have hcompl_sub : (goodSet I)ᶜ ⊆ B0 ∪ ⋃ k : Fin (M + 1), Bk k := by
    intro x hx
    by_contra hnot
    simp only [mem_union, mem_iUnion, not_or, not_exists] at hnot
    obtain ⟨hxB0, hxBk⟩ := hnot
    apply hx
    intro lam hlam
    have hMp : (0 : ℝ) < M := Nat.cast_pos.mpr hM_pos
    have hscaled_nonneg : 0 ≤ (lam + 1) * (M : ℝ) / 2 := by
      have := hlam.1; nlinarith
    have hscaled_le : (lam + 1) * (M : ℝ) / 2 ≤ (M : ℝ) := by
      have := hlam.2; nlinarith
    set j : ℕ := min M ⌊(lam + 1) * (M : ℝ) / 2 + 1 / 2⌋₊
    let k : Fin (M + 1) := ⟨j, Nat.lt_succ_of_le (min_le_left _ _)⟩
    have hdist : |lam - grid k| ≤ 1 / (M : ℝ) := by
      have hfloor_le : (⌊(lam + 1) * (M : ℝ) / 2 + 1 / 2⌋₊ : ℝ) ≤ (lam + 1) * (M : ℝ) / 2 + 1 / 2 :=
        Nat.floor_le (by linarith)
      have hlt_floor : (lam + 1) * (M : ℝ) / 2 + 1 / 2 < (⌊(lam + 1) * (M : ℝ) / 2 + 1 / 2⌋₊ : ℝ) + 1 :=
        Nat.lt_floor_add_one _
      have hj_diff : |(j : ℝ) - (lam + 1) * (M : ℝ) / 2| ≤ 1 / 2 := by
        by_cases hle : ⌊(lam + 1) * (M : ℝ) / 2 + 1 / 2⌋₊ ≤ M
        · have hj_eq : j = ⌊(lam + 1) * (M : ℝ) / 2 + 1 / 2⌋₊ := min_eq_right hle
          rw [hj_eq, abs_le]; constructor <;> linarith
        · have hj_eq : j = M := min_eq_left (le_of_not_ge hle)
          have hMlt : (M : ℝ) < (⌊(lam + 1) * (M : ℝ) / 2 + 1 / 2⌋₊ : ℝ) :=
            Nat.cast_lt.mpr (lt_of_not_ge hle)
          rw [hj_eq, abs_le]; constructor <;> linarith
      have hrewrite : lam - grid k = 2 / (M : ℝ) * ((lam + 1) * (M : ℝ) / 2 - (j : ℝ)) := by
        simp only [grid, k]; field_simp [hMp.ne']; ring
      rw [hrewrite, abs_mul, abs_of_pos (by positivity : 0 < 2 / (M : ℝ)), abs_sub_comm]
      calc 2 / (M : ℝ) * |(j : ℝ) - (lam + 1) * (M : ℝ) / 2|
          ≤ 2 / (M : ℝ) * (1 / 2) := by gcongr
        _ = 1 / (M : ℝ) := by ring
    have hsq_le : (I.card : ℝ)⁻¹ * ∑ i : I, x i ^ 2 ≤ 200 := not_lt.mp hxB0
    have hl1_le : (I.card : ℝ)⁻¹ * ∑ i : I, |x i| ≤ 15 := by
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset I) (fun _ => (1 : ℝ)) (fun i => |x i|)
      simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_coe,
        nsmul_eq_mul, mul_one, sq_abs] at hcs
      have hsq_sum : ∑ i : I, x i ^ 2 ≤ 200 * (I.card : ℝ) := by
        rwa [inv_mul_le_iff₀ hN_pos, mul_comm] at hsq_le
      have h1 : (∑ i : I, |x i|) ^ 2 ≤ (15 * (I.card : ℝ)) ^ 2 := by nlinarith
      have h2 : ∑ i : I, |x i| ≤ 15 * (I.card : ℝ) := by
        nlinarith [Finset.sum_nonneg (s := (Finset.univ : Finset I)) (fun i _ => abs_nonneg (x i))]
      rwa [inv_mul_le_iff₀ hN_pos, mul_comm]
    have hlip : |avgCos I (Real.pi * lam / c0) x - avgCos I (Real.pi * grid k / c0) x| ≤ α0 / 2 := by
      unfold avgCos
      rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul,
        abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
      calc (I.card : ℝ)⁻¹ * |∑ i : I, (Real.cos (Real.pi * lam / c0 * x i) -
              Real.cos (Real.pi * grid k / c0 * x i))|
          ≤ (I.card : ℝ)⁻¹ * ∑ i : I, |Real.cos (Real.pi * lam / c0 * x i) -
              Real.cos (Real.pi * grid k / c0 * x i)| := by
            gcongr; exact Finset.abs_sum_le_sum_abs _ _
        _ ≤ (I.card : ℝ)⁻¹ * ∑ i : I, |Real.pi * lam / c0 * x i - Real.pi * grid k / c0 * x i| := by
            refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (Nat.cast_nonneg _))
            exact Finset.sum_le_sum fun i _ => Real.abs_cos_sub_cos_le _ _
        _ = (Real.pi / c0 * |lam - grid k|) * ((I.card : ℝ)⁻¹ * ∑ i : I, |x i|) := by
            have hterm : ∀ i : I, |Real.pi * lam / c0 * x i - Real.pi * grid k / c0 * x i| =
                (Real.pi / c0 * |lam - grid k|) * |x i| := by
              intro i
              rw [show Real.pi * lam / c0 * x i - Real.pi * grid k / c0 * x i =
                (Real.pi / c0 * (lam - grid k)) * x i by ring]
              rw [abs_mul, abs_mul, abs_of_pos (div_pos Real.pi_pos c0_pos)]
            simp_rw [hterm, ← Finset.mul_sum]
            ring
        _ ≤ (Real.pi / c0 * (1 / (M : ℝ))) * 15 := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left hdist (by positivity)) hl1_le
              (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
                (Finset.sum_nonneg fun i _ => abs_nonneg _)) (by positivity)
        _ = L / (M : ℝ) := by simp only [L]; ring
        _ ≤ α0 / 2 := by
            rw [div_le_iff₀ hMp]
            have := (div_lt_iff₀ hα0).mp hM
            linarith
    have hgk : 3 / 2 * α0 ≤ avgCos I (Real.pi * grid k / c0) x := not_lt.mp (hxBk k)
    have hdiff := (abs_le.mp hlip).1
    linarith
  have hcompl_lt : μN I (goodSet I)ᶜ < (0.01 : ℝ≥0∞) := by
    have h001 : ENNReal.ofReal (0.01 : ℝ) = (0.01 : ℝ≥0∞) := by
      have h1 : (0.01 : ℝ) = ((0.01 : NNReal) : ℝ) := rfl
      rw [h1, ENNReal.ofReal_coe_nnreal]
      rfl
    calc μN I (goodSet I)ᶜ
        ≤ μN I (B0 ∪ ⋃ k : Fin (M + 1), Bk k) := measure_mono hcompl_sub
      _ ≤ μN I B0 + μN I (⋃ k : Fin (M + 1), Bk k) := measure_union_le _ _
      _ ≤ μN I B0 + ∑ k : Fin (M + 1), μN I (Bk k) := by
          gcongr; exact measure_iUnion_fintype_le _ _
      _ ≤ ENNReal.ofReal (1 / 200) + ∑ _ : Fin (M + 1), ENNReal.ofReal (4 / (α0 ^ 2 * (I.card : ℝ))) := by
          gcongr with k _
          · exact measure_sq_avg_gt_le I hI_pos
          · exact measure_avgCos_lt_le I hI_pos (grid k) (hgrid_mem k)
      _ = ENNReal.ofReal (1 / 200 + ((M : ℝ) + 1) * (4 / (α0 ^ 2 * (I.card : ℝ)))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
          rw [← ENNReal.ofReal_add (by norm_num) (by positivity)]
          push_cast; rfl
      _ < ENNReal.ofReal (0.01 : ℝ) := by
          apply (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr
          have hN_gt : ((M : ℝ) + 1) * 4 / (α0 ^ 2 * 0.004) < (I.card : ℝ) :=
            hN₀.trans_le (Nat.cast_le.mpr hI_N0)
          have h1 : ((M : ℝ) + 1) * (4 / (α0 ^ 2 * (I.card : ℝ))) < 0.004 := by
            have hden : 0 < α0 ^ 2 * (I.card : ℝ) := by positivity
            rw [← mul_div_assoc, div_lt_iff₀ hden]
            have h2 := (div_lt_iff₀ (by positivity : 0 < α0 ^ 2 * 0.004)).mp hN_gt
            linarith
          linarith
      _ = (0.01 : ℝ≥0∞) := h001
  have hsum : μN I (goodSet I) + μN I (goodSet I)ᶜ = 1 := by
    rw [measure_add_measure_compl (measurableSet_goodSet I), measure_univ]
  have h099 : (0.99 : ℝ≥0∞) + (0.01 : ℝ≥0∞) = 1 := by
    have h1 : (0.99 : ℝ≥0∞) = ((0.99 : NNReal) : ℝ≥0∞) := rfl
    have h2 : (0.01 : ℝ≥0∞) = ((0.01 : NNReal) : ℝ≥0∞) := rfl
    rw [h1, h2, ← ENNReal.coe_add]
    exact_mod_cast (by norm_num : (0.99 : NNReal) + 0.01 = 1)
  by_contra hle
  push Not at hle
  have hlt : μN I (goodSet I) + μN I (goodSet I)ᶜ < (0.99 : ℝ≥0∞) + (0.01 : ℝ≥0∞) :=
    ENNReal.add_lt_add_of_le_of_lt (measure_ne_top _ _) hle hcompl_lt
  rw [hsum, h099] at hlt
  exact lt_irrefl 1 hlt

/- ### Section 5: Sumset lower bound on `goodSet I + goodSet I` -/

lemma sum_abs_cos_ge_of_mem_add {I : Finset ℕ} {u : I → ℝ} (hu : u ∈ goodSet I + goodSet I) :
    α0 ≤ (I.card : ℝ)⁻¹ * ∑ i : I, |Real.cos (Real.pi * u i / (2 * c0))| := by
  obtain ⟨x, hx, y, hy, rfl⟩ := hu
  have hx1 := hx 1 (by simp)
  have hy1 := hy 1 (by simp)
  unfold avgCos at hx1 hy1
  have havg : α0 ≤ (I.card : ℝ)⁻¹ * ∑ i : I,
      (Real.cos (Real.pi * 1 / c0 * x i) + Real.cos (Real.pi * 1 / c0 * y i)) / 2 := by
    have h1 : 2 * α0 ≤ (I.card : ℝ)⁻¹ * ∑ i : I,
        (Real.cos (Real.pi * 1 / c0 * x i) + Real.cos (Real.pi * 1 / c0 * y i)) := by
      rw [Finset.sum_add_distrib, mul_add]
      linarith
    have h2 : ∑ i : I, (Real.cos (Real.pi * 1 / c0 * x i) + Real.cos (Real.pi * 1 / c0 * y i)) / 2 =
        (∑ i : I, (Real.cos (Real.pi * 1 / c0 * x i) + Real.cos (Real.pi * 1 / c0 * y i))) / 2 := by
      rw [Finset.sum_div]
    rw [h2]; linarith
  refine havg.trans ?_
  gcongr with i _
  rw [Real.cos_add_cos]
  have harg : (Real.pi * 1 / c0 * x i + Real.pi * 1 / c0 * y i) / 2 =
      Real.pi * (x + y) i / (2 * c0) := by
    simp only [Pi.add_apply]; ring
  rw [mul_assoc, mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0), harg]
  calc Real.cos (Real.pi * (x + y) i / (2 * c0)) *
        Real.cos ((Real.pi * 1 / c0 * x i - Real.pi * 1 / c0 * y i) / 2)
      ≤ |Real.cos (Real.pi * (x + y) i / (2 * c0)) *
          Real.cos ((Real.pi * 1 / c0 * x i - Real.pi * 1 / c0 * y i) / 2)| := le_abs_self _
    _ = |Real.cos (Real.pi * (x + y) i / (2 * c0))| *
          |Real.cos ((Real.pi * 1 / c0 * x i - Real.pi * 1 / c0 * y i) / 2)| := abs_mul _ _
    _ ≤ |Real.cos (Real.pi * (x + y) i / (2 * c0))| * 1 := by
          gcongr; exact Real.abs_cos_le_one _
    _ = |Real.cos (Real.pi * (x + y) i / (2 * c0))| := mul_one _

/- ### Section 6: Barycenter in a compact convex set and upper bound -/

def signVal (b : Bool) : ℝ := if b then 1 else -1

lemma signVal_sq (b : Bool) : signVal b ^ 2 = 1 := by cases b <;> norm_num [signVal]

lemma abs_signVal (b : Bool) : |signVal b| = 1 := by cases b <;> norm_num [signVal]

def flipMap {I : Finset ℕ} (ε : I → Bool) : (I → ℝ) ≃L[ℝ] (I → ℝ) :=
  { toFun := fun x i => signVal (ε i) * x i
    invFun := fun x i => signVal (ε i) * x i
    map_add' := fun x y => by ext i; simp [mul_add]
    map_smul' := fun r x => by ext i; simp [mul_left_comm]
    left_inv := fun x => by
      ext i; simp only [← mul_assoc, ← sq, signVal_sq, one_mul]
    right_inv := fun x => by
      ext i; simp only [← mul_assoc, ← sq, signVal_sq, one_mul]
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }

lemma measurePreserving_flipMap {I : Finset ℕ} (ε : I → Bool) :
    MeasurePreserving (flipMap ε) (μN I) (μN I) := by
  have hcoord : ∀ i : I, MeasurePreserving (fun t : ℝ => signVal (ε i) * t) γ1 γ1 := by
    intro i
    cases h : ε i
    · simp only [signVal, Bool.false_eq_true, ↓reduceIte, neg_mul, one_mul]
      exact ⟨measurable_neg, γ1_map_neg⟩
    · simp only [signVal, ↓reduceIte, one_mul]
      exact MeasurePreserving.id γ1
  exact MeasureTheory.measurePreserving_pi _ _ hcoord

def posOrthant (I : Finset ℕ) : Set (I → ℝ) :=
  Set.univ.pi (fun _ : I => Ici (0 : ℝ))

lemma measurableSet_posOrthant (I : Finset ℕ) : MeasurableSet (posOrthant I) :=
  MeasurableSet.univ_pi (fun _ => measurableSet_Ici)

lemma νPlus_eq_smul_restrict (I : Finset ℕ) :
    νPlus I = ((2 : ℝ≥0∞) ^ I.card) • (μN I).restrict (posOrthant I) := by
  unfold νPlus
  exact Measure.pi_eq (μ := fun _ : I => γ1Plus) fun s hs => by
    rw [Measure.smul_apply, Measure.restrict_apply (MeasurableSet.univ_pi hs), smul_eq_mul]
    have hinter : Set.univ.pi s ∩ posOrthant I = Set.univ.pi (fun i : I => s i ∩ Ici (0 : ℝ)) := by
      ext x; simp only [posOrthant, mem_inter_iff, Set.mem_pi, mem_univ, forall_true_left,
        mem_Ici, forall_and]
    rw [hinter, μN, Measure.pi_pi]
    have hprod : (2 : ℝ≥0∞) ^ I.card = ∏ _ : I, (2 : ℝ≥0∞) := by simp
    rw [hprod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    unfold γ1Plus
    rw [Measure.smul_apply, Measure.restrict_apply (hs i), smul_eq_mul]

lemma barycenter_mem_closed_convex {I : Finset ℕ} {K : Set (I → ℝ)} (hKc : IsClosed K)
    (hKv : Convex ℝ K) {ν : Measure (I → ℝ)} [IsFiniteMeasure ν]
    (hpos : 0 < ν.real univ) (hsupp : ν Kᶜ = 0) (hint : Integrable (fun x : I → ℝ => x) ν) :
    (ν.real univ)⁻¹ • ∫ x, x ∂ν ∈ K := by
  set y : I → ℝ := (ν.real univ)⁻¹ • ∫ x, x ∂ν
  by_contra hy
  obtain ⟨L, u, hLy, hLK⟩ := geometric_hahn_banach_point_closed hKv hKc hy
  have hLy_eq : L y = (ν.real univ)⁻¹ * ∫ x, L x ∂ν := by
    simp only [y, map_smul, smul_eq_mul]
    rw [ContinuousLinearMap.integral_comp_comm L hint]
  have hae : ∀ᵐ x ∂ν, u ≤ L x := by
    have hKae : ∀ᵐ x ∂ν, x ∈ K := by
      rw [ae_iff]; exact hsupp
    exact hKae.mono fun x hx => le_of_lt (hLK x hx)
  have hintL : Integrable (fun x => L x) ν := L.integrable_comp hint
  have hge : ∫ _ : I → ℝ, u ∂ν ≤ ∫ x, L x ∂ν :=
    integral_mono_ae (integrable_const u) hintL hae
  rw [integral_const, smul_eq_mul] at hge
  have hge' : u ≤ (ν.real univ)⁻¹ * ∫ x, L x ∂ν := by
    rw [le_inv_mul_iff₀ hpos]
    exact hge
  linarith

lemma exists_mem_convex_small_avgCos {I : Finset ℕ} (hI : 0 < I.card) {C : Set (I → ℝ)}
    (hCc : IsCompact C) (hCv : Convex ℝ C) (hCm : (0.01 : ℝ≥0∞) ≤ μN I C) :
    ∃ u ∈ C, (I.card : ℝ)⁻¹ * ∑ i : I, |Real.cos (Real.pi * u i / (2 * c0))| ≤
      5 * Real.pi / (c0 * Real.sqrt (I.card : ℝ)) := by
  have hc0 : 0 < c0 := c0_pos
  have hpi : 0 < Real.pi := Real.pi_pos
  -- Step 1: Pigeonhole over the 2^|I| orthants
  have hcover : C ⊆ ⋃ ε : I → Bool, C ∩ (flipMap ε) '' (posOrthant I) := by
    intro x hx
    rw [mem_iUnion]
    let ε : I → Bool := fun i => decide (0 ≤ x i)
    refine ⟨ε, hx, (flipMap ε).symm x, ?_, (flipMap ε).apply_symm_apply x⟩
    intro i _
    change 0 ≤ signVal (ε i) * x i
    by_cases hxi : 0 ≤ x i
    · simp [ε, hxi, signVal]
    · simp only [ε, hxi, decide_false, signVal, Bool.false_eq_true, ↓reduceIte, neg_mul, one_mul]
      linarith
  have hsum_ge : (0.01 : ℝ≥0∞) ≤ ∑ ε : I → Bool, μN I (C ∩ (flipMap ε) '' (posOrthant I)) :=
    hCm.trans ((measure_mono hcover).trans (measure_iUnion_fintype_le _ _))
  have hsum_real : (0.01 : ℝ) ≤ ∑ ε : I → Bool, (μN I).real (C ∩ (flipMap ε) '' (posOrthant I)) := by
    have h1 := ENNReal.toReal_mono (ENNReal.sum_lt_top.mpr fun ε _ => measure_lt_top _ _).ne hsum_ge
    rw [ENNReal.toReal_sum fun ε _ => measure_ne_top _ _] at h1
    have h001 : (0.01 : ℝ≥0∞).toReal = (0.01 : ℝ) := by
      change ((0.01 : NNReal) : ℝ≥0∞).toReal = (0.01 : ℝ)
      rw [ENNReal.coe_toReal]
      rfl
    simpa [Measure.real, h001] using h1
  have hex_eps : ∃ ε : I → Bool,
      (0.01 : ℝ) ≤ (2 : ℝ) ^ I.card * (μN I).real (C ∩ (flipMap ε) '' (posOrthant I)) := by
    by_contra hnot
    push Not at hnot
    have hlt : ∑ ε : I → Bool, (μN I).real (C ∩ (flipMap ε) '' (posOrthant I)) <
        ∑ _ : I → Bool, ((0.01 : ℝ) / (2 : ℝ) ^ I.card) := by
      refine Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun ε _ => ?_
      rw [lt_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ I.card), mul_comm]
      exact hnot ε
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hlt
    have hcard_bool : (Fintype.card (I → Bool) : ℝ) = (2 : ℝ) ^ I.card := by simp
    rw [hcard_bool, mul_div_cancel₀ _ (by positivity : (2 : ℝ) ^ I.card ≠ 0)] at hlt
    linarith
  obtain ⟨ε, hε_real⟩ := hex_eps
  -- Step 2: Pull back by flipMap ε into the positive orthant
  set K : Set (I → ℝ) := (flipMap ε) ⁻¹' C
  set D : Set (I → ℝ) := K ∩ posOrthant I
  have hKc : IsClosed K := hCc.isClosed.preimage (flipMap ε).continuous
  have hKv : Convex ℝ K := hCv.linear_preimage (flipMap ε).toLinearMap
  have hDm : MeasurableSet D := hKc.measurableSet.inter (measurableSet_posOrthant I)
  have hmap_eq : (flipMap ε) ⁻¹' (C ∩ (flipMap ε) '' (posOrthant I)) = D := by
    ext x
    simp only [mem_preimage, mem_inter_iff, mem_image, D, K]
    constructor
    · rintro ⟨hxC, y, hy, hxy⟩
      have hyeq : y = x := (flipMap ε).injective hxy
      exact ⟨hxC, hyeq ▸ hy⟩
    · rintro ⟨hxC, hxP⟩
      exact ⟨hxC, x, hxP, rfl⟩
  have hμD : μN I D = μN I (C ∩ (flipMap ε) '' (posOrthant I)) := by
    rw [← hmap_eq]
    have hmeas_rhs : MeasurableSet (C ∩ (flipMap ε) '' (posOrthant I)) := by
      have h1 : (flipMap ε) '' (posOrthant I) = (flipMap ε).symm ⁻¹' (posOrthant I) := by
        ext x; constructor
        · rintro ⟨y, hy, rfl⟩; simpa using hy
        · intro hx; exact ⟨(flipMap ε).symm x, hx, (flipMap ε).apply_symm_apply x⟩
      rw [h1]
      exact hCc.measurableSet.inter
        ((measurableSet_posOrthant I).preimage (flipMap ε).symm.continuous.measurable)
    rw [← (measurePreserving_flipMap ε).measure_preimage hmeas_rhs.nullMeasurableSet]
  have hνD_real_ge : (0.01 : ℝ) ≤ (νPlus I).real D := by
    have hνD_eq : νPlus I D = ((2 : ℝ≥0∞) ^ I.card) * μN I (C ∩ (flipMap ε) '' (posOrthant I)) := by
      rw [νPlus_eq_smul_restrict, Measure.smul_apply, Measure.restrict_apply hDm, smul_eq_mul]
      have hDD : D ∩ posOrthant I = D := inter_eq_left.mpr inter_subset_right
      rw [hDD, hμD]
    rw [Measure.real, hνD_eq, ENNReal.toReal_mul, ENNReal.toReal_pow]
    simpa [Measure.real] using hε_real
  have hνD_pos : 0 < (νPlus I).real D := lt_of_lt_of_le (by norm_num) hνD_real_ge
  -- Step 3: Barycenter y0 of ν := (νPlus I).restrict D
  set ν : Measure (I → ℝ) := (νPlus I).restrict D
  have hν_univ : ν.real univ = (νPlus I).real D := by
    simp [ν, Measure.real]
  have hν_supp : ν Kᶜ = 0 := by
    simp only [ν, Measure.restrict_apply hKc.measurableSet.compl]
    have hempty : Kᶜ ∩ D = ∅ := by
      ext x; simp only [D, mem_inter_iff, mem_compl_iff, mem_empty_iff_false, iff_false, not_and]
      intro h1 h2 _; exact h1 h2
    rw [hempty, measure_empty]
  have hint_id_νPlus : Integrable (fun x : I → ℝ => x) (νPlus I) := by
    rw [integrable_pi_iff]
    intro i
    exact integrable_eval_νPlus I i integrable_id_γ1Plus
  have hint_id_ν : Integrable (fun x : I → ℝ => x) ν := hint_id_νPlus.restrict
  set y0 : I → ℝ := (ν.real univ)⁻¹ • ∫ x, x ∂ν
  have hy0K : y0 ∈ K :=
    barycenter_mem_closed_convex hKc hKv (by rwa [hν_univ]) hν_supp hint_id_ν
  have huC : flipMap ε y0 ∈ C := hy0K
  have hy0_coord : ∀ i : I, y0 i = ((νPlus I).real D)⁻¹ * ∫ x in D, x i ∂(νPlus I) := by
    intro i
    have heval := ContinuousLinearMap.integral_comp_comm (ContinuousLinearMap.proj (R := ℝ) i) hint_id_ν
    simp only [y0, hν_univ, Pi.smul_apply, smul_eq_mul]
    congr 1
    exact heval.symm
  -- Step 4: L2 bound ∑ i, (y0 i - c0)^2 ≤ 100
  set v : I → ℝ := fun i => y0 i - c0
  have hv_eq : ∀ i : I, v i = ((νPlus I).real D)⁻¹ * ∫ x in D, (x i - c0) ∂(νPlus I) := by
    intro i
    simp only [v, hy0_coord i]
    rw [integral_sub (integrable_eval_νPlus I i integrable_id_γ1Plus).integrableOn
      (integrable_const c0)]
    rw [setIntegral_const, smul_eq_mul, mul_sub]
    rw [inv_mul_cancel_left₀ hνD_pos.ne']
  set g : (I → ℝ) → ℝ := fun x => ∑ i : I, v i * (x i - c0)
  have hint_term : ∀ i : I, Integrable (fun x : I → ℝ => v i * (x i - c0)) (νPlus I) := fun i =>
    ((integrable_eval_νPlus I i integrable_id_γ1Plus).sub (integrable_const c0)).const_mul (v i)
  have hg_sum : ∑ i : I, v i ^ 2 = ((νPlus I).real D)⁻¹ * ∫ x in D, g x ∂(νPlus I) := by
    simp only [g]
    rw [integral_finset_sum _ fun i _ => (hint_term i).integrableOn]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul, sq, hv_eq i]
    ring
  have hprod_int : ∀ i j : I,
      Integrable (fun x : I → ℝ => (v i * v j) * ((x i - c0) * (x j - c0))) (νPlus I) := by
    intro i j
    apply Integrable.const_mul
    by_cases hij : i = j
    · subst hij
      simp_rw [← sq]
      have hsq : Integrable (fun t : ℝ => (t - c0) ^ 2) γ1Plus := by
        have : ∀ t : ℝ, (t - c0) ^ 2 = t ^ 2 - 2 * c0 * t + c0 ^ 2 := fun t => by ring
        simp_rw [this]
        exact (integrable_sq_γ1Plus.sub (integrable_id_γ1Plus.const_mul _)).add (integrable_const _)
      exact integrable_eval_νPlus I i hsq
    · have hind : iIndepFun (fun k (x : I → ℝ) => x k) (νPlus I) :=
        ProbabilityTheory.iIndepFun_pi (fun _ => aemeasurable_id)
      have hpair : IndepFun (fun x : I → ℝ => x i - c0) (fun x : I → ℝ => x j - c0) (νPlus I) :=
        (hind.indepFun hij).comp (measurable_id.sub_const c0) (measurable_id.sub_const c0)
      exact hpair.integrable_mul
        ((integrable_eval_νPlus I i integrable_id_γ1Plus).sub (integrable_const c0))
        ((integrable_eval_νPlus I j integrable_id_γ1Plus).sub (integrable_const c0))
  have hg_sq_rew : ∀ x : I → ℝ, g x ^ 2 = ∑ i : I, ∑ j : I, (v i * v j) * ((x i - c0) * (x j - c0)) := by
    intro x
    simp only [g, sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hg_sq_int : Integrable (fun x => g x ^ 2) (νPlus I) := by
    simp_rw [hg_sq_rew]
    exact integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => hprod_int i j
  have hcs_int : (∫ x in D, g x ∂(νPlus I)) ^ 2 ≤ (νPlus I).real D * ∫ x, g x ^ 2 ∂(νPlus I) := by
    have hnonneg : ∀ t : ℝ, 0 ≤ ∫ x, (t * D.indicator (fun _ => (1 : ℝ)) x - g x) ^ 2 ∂(νPlus I) :=
      fun t => integral_nonneg fun x => sq_nonneg _
    have hind_int : Integrable (D.indicator (fun _ : I → ℝ => (1 : ℝ))) (νPlus I) :=
      (integrable_const (1 : ℝ)).indicator hDm
    have hind_sq : ∀ x, (D.indicator (fun _ : I → ℝ => (1 : ℝ)) x) ^ 2 =
        D.indicator (fun _ : I → ℝ => (1 : ℝ)) x := fun x => by
      by_cases hx : x ∈ D <;> simp [hx]
    have hg_int : Integrable g (νPlus I) :=
      integrable_finset_sum _ fun i _ => hint_term i
    have hprod_ind : Integrable (fun x => D.indicator (fun _ => (1 : ℝ)) x * g x) (νPlus I) := by
      have hrew : (fun x => D.indicator (fun _ => (1 : ℝ)) x * g x) = D.indicator g := by
        ext x; by_cases hx : x ∈ D <;> simp [hx]
      rw [hrew]; exact hg_int.indicator hDm
    have hquad : ∀ t : ℝ, 0 ≤ t ^ 2 * (νPlus I).real D - 2 * t * (∫ x in D, g x ∂(νPlus I)) +
        ∫ x, g x ^ 2 ∂(νPlus I) := by
      intro t
      have h := hnonneg t
      have hexp : ∀ x, (t * D.indicator (fun _ : I → ℝ => (1 : ℝ)) x - g x) ^ 2 =
          (t ^ 2 * D.indicator (fun _ : I → ℝ => (1 : ℝ)) x -
          2 * t * (D.indicator (fun _ : I → ℝ => (1 : ℝ)) x * g x)) + g x ^ 2 := by
        intro x; linear_combination t ^ 2 * (hind_sq x)
      simp_rw [hexp] at h
      have hsub_i : Integrable (fun x => t ^ 2 * D.indicator (fun _ => (1 : ℝ)) x -
          2 * t * (D.indicator (fun _ => (1 : ℝ)) x * g x)) (νPlus I) :=
        (hind_int.const_mul (t ^ 2)).sub (hprod_ind.const_mul (2 * t))
      rw [integral_add hsub_i hg_sq_int] at h
      rw [integral_sub (hind_int.const_mul (t ^ 2)) (hprod_ind.const_mul (2 * t))] at h
      rw [integral_const_mul, integral_const_mul] at h
      rw [integral_indicator_const (1 : ℝ) hDm, smul_eq_mul, mul_one] at h
      have hrew : (fun x => D.indicator (fun _ => (1 : ℝ)) x * g x) = D.indicator g := by
        ext x; by_cases hx : x ∈ D <;> simp [hx]
      rw [hrew, integral_indicator hDm] at h
      exact h
    have h0 := hquad ((∫ x in D, g x ∂(νPlus I)) / (νPlus I).real D)
    have hsimp : ((∫ x in D, g x ∂(νPlus I)) / (νPlus I).real D) ^ 2 * (νPlus I).real D -
        2 * ((∫ x in D, g x ∂(νPlus I)) / (νPlus I).real D) * (∫ x in D, g x ∂(νPlus I)) +
        ∫ x, g x ^ 2 ∂(νPlus I) =
        ∫ x, g x ^ 2 ∂(νPlus I) - (∫ x in D, g x ∂(νPlus I)) ^ 2 / (νPlus I).real D := by
      field_simp [hνD_pos.ne']; ring
    rw [hsimp] at h0
    have h3 : (∫ x in D, g x ∂(νPlus I)) ^ 2 / (νPlus I).real D ≤ ∫ x, g x ^ 2 ∂(νPlus I) := by linarith
    rwa [div_le_iff₀ hνD_pos, mul_comm] at h3
  have hg_sq_le : ∫ x, g x ^ 2 ∂(νPlus I) ≤ ∑ i : I, v i ^ 2 := by
    simp_rw [hg_sq_rew]
    rw [integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => hprod_int i j]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [integral_finset_sum _ fun j _ => hprod_int i j]
    rw [Finset.sum_eq_single i]
    · rw [integral_const_mul]
      simp_rw [← sq]
      rw [integral_eval_νPlus I i (f := fun t => (t - c0) ^ 2) (by fun_prop)]
      calc v i ^ 2 * ∫ t, (t - c0) ^ 2 ∂γ1Plus ≤ v i ^ 2 * 1 := by
            gcongr; exact integral_sub_c0_sq_γ1Plus
        _ = v i ^ 2 := mul_one _
    · intro j _ hji
      rw [integral_const_mul, νPlus]
      rw [integral_mul_eval_of_ne hji.symm (f := fun t => t - c0) (g := fun t => t - c0)
        (by fun_prop) (by fun_prop)]
      rw [integral_sub_c0_γ1Plus, mul_zero, mul_zero]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  have hv_sq_le : ∑ i : I, v i ^ 2 ≤ 100 := by
    have h1 : (∑ i : I, v i ^ 2) ^ 2 ≤ ((νPlus I).real D)⁻¹ * (∑ i : I, v i ^ 2) := by
      calc (∑ i : I, v i ^ 2) ^ 2
          = (((νPlus I).real D)⁻¹) ^ 2 * (∫ x in D, g x ∂(νPlus I)) ^ 2 := by
            rw [hg_sum, mul_pow]
        _ ≤ (((νPlus I).real D)⁻¹) ^ 2 * ((νPlus I).real D * ∫ x, g x ^ 2 ∂(νPlus I)) := by
            gcongr
        _ = ((νPlus I).real D)⁻¹ * ∫ x, g x ^ 2 ∂(νPlus I) := by
            field_simp [hνD_pos.ne']
        _ ≤ ((νPlus I).real D)⁻¹ * ∑ i : I, v i ^ 2 := by
            gcongr
    have hinv : ((νPlus I).real D)⁻¹ ≤ 100 := by
      rw [inv_le_iff_one_le_mul₀ hνD_pos]; linarith
    by_cases h0 : ∑ i : I, v i ^ 2 = 0
    · rw [h0]; norm_num
    · have hpos_v : 0 < ∑ i : I, v i ^ 2 :=
        lt_of_le_of_ne (Finset.sum_nonneg fun i _ => sq_nonneg _) (Ne.symm h0)
      have h2 : ∑ i : I, v i ^ 2 ≤ ((νPlus I).real D)⁻¹ := by nlinarith
      exact h2.trans hinv
  -- Step 5: Bound (1/N) ∑ |cos(π u_i / (2 c0))| ≤ 5 π / (c0 √N)
  refine ⟨flipMap ε y0, huC, ?_⟩
  have hcos_le : ∀ i : I, |Real.cos (Real.pi * (flipMap ε y0) i / (2 * c0))| ≤
      Real.pi / (2 * c0) * |v i| := by
    intro i
    have hzero : Real.cos (Real.pi * (signVal (ε i) * c0) / (2 * c0)) = 0 := by
      have harg : Real.pi * (signVal (ε i) * c0) / (2 * c0) = signVal (ε i) * (Real.pi / 2) := by
        field_simp [hc0.ne']
      rw [harg]
      cases ε i <;> simp [signVal, Real.cos_pi_div_two]
    rw [← sub_zero (Real.cos _), ← hzero]
    calc |Real.cos (Real.pi * (flipMap ε y0) i / (2 * c0)) -
            Real.cos (Real.pi * (signVal (ε i) * c0) / (2 * c0))|
        ≤ |Real.pi * (flipMap ε y0) i / (2 * c0) -
            Real.pi * (signVal (ε i) * c0) / (2 * c0)| := Real.abs_cos_sub_cos_le _ _
      _ = Real.pi / (2 * c0) * |v i| := by
          have harg : Real.pi * (flipMap ε y0) i / (2 * c0) -
              Real.pi * (signVal (ε i) * c0) / (2 * c0) =
              Real.pi / (2 * c0) * (signVal (ε i) * v i) := by
            simp only [flipMap, v, ContinuousLinearEquiv.coe_mk, LinearEquiv.coe_mk,
              LinearMap.coe_mk, AddHom.coe_mk]
            ring
          rw [harg, abs_mul, abs_mul, abs_signVal, one_mul,
            abs_of_pos (div_pos hpi (by positivity))]
  have hl1_le : ∑ i : I, |v i| ≤ 10 * Real.sqrt (I.card : ℝ) := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset I) (fun _ => (1 : ℝ)) (fun i => |v i|)
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_coe,
      nsmul_eq_mul, mul_one, sq_abs] at hcs
    have h1 : (∑ i : I, |v i|) ^ 2 ≤ (10 * Real.sqrt (I.card : ℝ)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      nlinarith
    nlinarith [Finset.sum_nonneg (s := (Finset.univ : Finset I)) (fun i _ => abs_nonneg (v i)),
      Real.sqrt_nonneg (I.card : ℝ)]
  have hN_pos : (0 : ℝ) < I.card := Nat.cast_pos.mpr hI
  calc (I.card : ℝ)⁻¹ * ∑ i : I, |Real.cos (Real.pi * (flipMap ε y0) i / (2 * c0))|
      ≤ (I.card : ℝ)⁻¹ * ∑ i : I, (Real.pi / (2 * c0) * |v i|) := by
        gcongr with i _; exact hcos_le i
    _ = (I.card : ℝ)⁻¹ * (Real.pi / (2 * c0) * ∑ i : I, |v i|) := by
        rw [← Finset.mul_sum]
    _ ≤ (I.card : ℝ)⁻¹ * (Real.pi / (2 * c0) * (10 * Real.sqrt (I.card : ℝ))) := by
        refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (Nat.cast_nonneg _))
        exact mul_le_mul_of_nonneg_left hl1_le (by positivity)
    _ = 5 * Real.pi / (c0 * Real.sqrt (I.card : ℝ)) := by
        have hsq : Real.sqrt (I.card : ℝ) * Real.sqrt (I.card : ℝ) = (I.card : ℝ) :=
          Real.mul_self_sqrt (Nat.cast_nonneg _)
        have hsq_pos : 0 < Real.sqrt (I.card : ℝ) := Real.sqrt_pos.mpr hN_pos
        field_simp [hN_pos.ne', hc0.ne', hsq_pos.ne']
        nlinarith [hsq]

/- ### Section 7: Finite-dimensional obstruction and lift to `ℝ^ℕ` -/

lemma finite_dim_obstruction :
    ∃ (I : Finset ℕ) (A : Set (I → ℝ)), MeasurableSet A ∧ Balanced ℝ A ∧
      (0.99 : ℝ≥0∞) < μN I A ∧
      ∀ C : Set (I → ℝ), IsCompact C → Convex ℝ C → C ⊆ A + A → μN I C < (0.01 : ℝ≥0∞) := by
  have hc0 : 0 < c0 := c0_pos
  have hα0 : 0 < α0 := α0_pos
  have hpi : 0 < Real.pi := Real.pi_pos
  obtain ⟨N₀, hN₀⟩ := exists_N_measure_goodSet_gt
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt ((5 * Real.pi / (c0 * α0)) ^ 2)
  set N : ℕ := max (max N₀ N₁) 1
  set I : Finset ℕ := Finset.range N
  have hcard : I.card = N := Finset.card_range N
  have hI_pos : 0 < I.card := by rw [hcard]; exact lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)
  refine ⟨I, goodSet I, measurableSet_goodSet I, balanced_goodSet I,
    hN₀ I (by rw [hcard]; exact le_trans (le_max_left _ _) (le_max_left _ _)), ?_⟩
  intro C hCc hCv hCsub
  by_contra hge
  push Not at hge
  obtain ⟨u, huC, hu_le⟩ := exists_mem_convex_small_avgCos hI_pos hCc hCv hge
  have hu_ge := sum_abs_cos_ge_of_mem_add (hCsub huC)
  have hN1_lt : (5 * Real.pi / (c0 * α0)) ^ 2 < (I.card : ℝ) := by
    rw [hcard]
    exact hN₁.trans_le (Nat.cast_le.mpr (le_trans (le_max_right _ _) (le_max_left _ _)))
  have hsqrt_gt : 5 * Real.pi / (c0 * α0) < Real.sqrt (I.card : ℝ) := by
    rw [← Real.sqrt_sq (x := 5 * Real.pi / (c0 * α0)) (by positivity)]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) hN1_lt
  have hlt : 5 * Real.pi / (c0 * Real.sqrt (I.card : ℝ)) < α0 := by
    have hden1 : 0 < c0 * Real.sqrt (I.card : ℝ) := by
      have : 0 < Real.sqrt (I.card : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hI_pos)
      positivity
    have hden2 : 0 < c0 * α0 := by positivity
    rw [div_lt_iff₀ hden1]
    have h2 := (div_lt_iff₀ hden2).mp hsqrt_gt
    nlinarith
  linarith

lemma cylinder_measure (I : Finset ℕ) (A : Set (I → ℝ)) (hA : MeasurableSet A) :
    Green54.gaussianMeasureInf (I.restrict ⁻¹' A) = μN I A := by
  rw [← Measure.map_apply I.continuous_restrict.measurable hA]
  rw [Green54.gaussianMeasureInf, Measure.infinitePi_map_restrict]
  rfl

theorem main : type_of% @Green54.green_54_known_case := by
  obtain ⟨I, A, hAm, hAbal, hAgt, hsmall⟩ := finite_dim_obstruction
  intro hall
  have hprob : IsProbabilityMeasure Green54.gaussianMeasureInf := by
    unfold Green54.gaussianMeasureInf; infer_instance
  have hS : MeasurableSet (I.restrict (π := fun _ : ℕ => ℝ) ⁻¹' A) :=
    hAm.preimage (Finset.continuous_restrict (A := fun _ : ℕ => ℝ) I).measurable
  have hmeas := cylinder_measure I A hAm
  obtain ⟨K₀, hK₀A, hK₀, hrK₀⟩ := hS.exists_lt_isCompact_of_ne_top
    (μ := Green54.gaussianMeasureInf) (measure_ne_top _ _) (by rw [hmeas]; exact hAgt)
  let K : Set (ℕ → ℝ) :=
    (fun p : ℝ × (ℕ → ℝ) => p.1 • p.2) '' (Metric.closedBall (0 : ℝ) 1 ×ˢ K₀)
  have hKc : IsCompact K := ((isCompact_closedBall (0 : ℝ) 1).prod hK₀).image continuous_smul
  have hKbal : Balanced ℝ K := by
    intro a ha
    rintro _ ⟨_, ⟨⟨b, x⟩, ⟨hb, hx⟩, rfl⟩, rfl⟩
    refine ⟨(a * b, x), ⟨?_, hx⟩, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right] at hb ⊢
      calc ‖a * b‖ = ‖a‖ * ‖b‖ := norm_mul a b
        _ ≤ 1 := mul_le_one₀ ha (norm_nonneg _) hb
    · show (a * b) • x = a • b • x
      rw [mul_smul]
  have hKm : (0.99 : ℝ≥0∞) ≤ Green54.gaussianMeasureInf K := by
    refine hrK₀.le.trans (measure_mono ?_)
    intro x hx
    exact ⟨(1, x), ⟨by simp, hx⟩, by simp⟩
  have hKA : K ⊆ I.restrict ⁻¹' A := by
    rintro _ ⟨⟨b, x⟩, ⟨hb, hx⟩, rfl⟩
    have hxA : I.restrict x ∈ A := hK₀A hx
    have hb' : ‖b‖ ≤ 1 := by rwa [Metric.mem_closedBall, dist_zero_right] at hb
    exact hAbal b hb' (Set.smul_mem_smul_set hxA)
  obtain ⟨C, hCc, hCv, hCsub, hCm⟩ := hall K hKc hKbal hKm
  let D : Set (I → ℝ) := I.restrict '' C
  have hDc : IsCompact D := hCc.image I.continuous_restrict
  have hDv : Convex ℝ D := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ a b ha hb hab
    exact ⟨_, hCv hx hy ha hb hab, rfl⟩
  have hDA : D ⊆ A + A := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨u, hu, v, hv, rfl⟩ := hCsub hx
    exact ⟨_, hKA hu, _, hKA hv, rfl⟩
  apply (hsmall D hDc hDv hDA).not_ge
  rw [← cylinder_measure I D hDc.measurableSet]
  exact hCm.trans (measure_mono (Set.subset_preimage_image _ _))

end Green54Counterexample

theorem OMA.solution : type_of% @Green54.green_54_known_case :=
  Green54Counterexample.main
