import FormalConjectures.ErdosProblems.«786»

-- Credit: @senamakel
import Mathlib
/- Adapted from github.com/daizisheng/erdos-786 (commit 496a7cc69e5d2c5c113e08ca184b706e1dd7d76f), (c) daizisheng, no licence file in the source repository; ported with the permission of the porting account owner.
   Vendored Mertens and EulerMaclaurin parts come from github.com/AlexKontorovich/PrimeNumberTheoremAnd, Apache-2.0 (Apache License 2.0 notice kept: licensed under the Apache License, Version 2.0, http://www.apache.org/licenses/LICENSE-2.0).
   The underlying result is the source author's unrefereed work. -/

-- ==== Vendor/EulerMaclaurin
section
/-
Vendored from PrimeNumberTheoremAnd (https://github.com/AlexKontorovich/PrimeNumberTheoremAnd),
file `PrimeNumberTheoremAnd/EulerMaclaurin.lean` (fork kimihiro64/PrimeNumberTheoremAnd, rev 0f15a38),
Apache License 2.0. Changes: converted from the module system to plain imports, blueprint annotations
(`@[blueprint ...]`, `blueprint_comment`) removed, namespaced imports adjusted. No mathematical changes.
-/




open Finset Interval MeasureTheory


variable {𝕜 : Type*} [RCLike 𝕜] {f : ℝ → 𝕜} {a b : ℝ}

/-- The 1st Bernoulli function. -/
noncomputable def B1 (x : ℝ) : ℝ := x - ⌊x⌋₊ - 1 / 2

lemma aestronglyMeasurable_B1 : AEStronglyMeasurable B1 := by
  unfold B1
  fun_prop

lemma abs_B1_le_half {x : ℝ} (hx : 0 ≤ x) : |B1 x| ≤ 1 / 2 := by
  unfold B1
  refine abs_le.mpr ⟨?_, ?_⟩
  · grind [Nat.floor_le hx]
  · grind [Nat.lt_succ_floor x]

lemma integral_deriv_mul_add_const (c : 𝕜) (hab : a ≤ b) (h_int : IntervalIntegrable (deriv f) volume a b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t) :
    ∫ t in a..b, (t + c) * deriv f t = (b + c) * f b - (a + c) * f a - ∫ t in a..b, f t := by
  rw [← Set.uIcc_of_le hab] at hf_diff
  have : ∀ t ∈ [[a, b]], HasDerivAt (fun (t : ℝ) ↦ t + c) 1 t := by
    intro t ht
    simp only [hasDerivAt_add_const_iff]
    convert! ContinuousLinearMap.hasDerivAt (RCLike.ofRealCLM (K := 𝕜)) using 1
    simp
  replace hf_diff := fun t ht ↦ (hf_diff t ht).hasDerivAt
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul this hf_diff (by simp) h_int]
  simp

lemma intervalIntegrable_deriv_mul_B1 (ha : 0 ≤ a) (hab : a ≤ b) (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    IntervalIntegrable (fun t ↦ deriv f t * B1 t) volume a b := by
  refine IntervalIntegrable.continuousOn_mul ?_ h_cont
  rw [intervalIntegrable_iff']
  apply MeasureTheory.Measure.integrableOn_of_bounded (by simp) (RCLike.continuous_ofReal.comp_aestronglyMeasurable aestronglyMeasurable_B1) (M := 1 / 2)
  filter_upwards [self_mem_ae_restrict (by measurability)] with x hx
  rw [Set.uIcc_of_le hab, Set.mem_Icc] at hx
  norm_cast
  exact abs_B1_le_half (by linarith)

lemma integral_deriv_mul_floor_add_one (ha : 0 ≤ a) (hab : a ≤ b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t) (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    ∫ t in a..b, deriv f t * (⌊t⌋₊ + 1) = (b + 1 / 2) * f b - (a + 1 / 2) * f a - (∫ t in a..b, f t) - ∫ t in a..b, deriv f t * B1 t := by
  calc
  _ = ∫ t in a..b, (deriv f t * (t + 1 / 2) -deriv f t * B1 t) := by
    congr
    ext
    simp only [B1]
    push_cast
    ring
  _ = (∫ t in a..b, deriv f t * (t + 1 / 2)) - ∫ t in a..b, deriv f t * B1 t := by
    exact intervalIntegral.integral_sub (ContinuousOn.intervalIntegrable (by fun_prop)) (intervalIntegrable_deriv_mul_B1 ha hab h_cont)
  _ = _ := by
    conv => lhs; arg 1; arg 1; ext; rw [mul_comm]
    rw [integral_deriv_mul_add_const _ hab h_cont.intervalIntegrable hf_diff]

theorem sum_eq_integral_add_integral_deriv (ha : 0 ≤ a) (hab : a ≤ b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    ∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f k =
      f a * B1 a - f b * B1 b + (∫ t in a..b, f t) + ∫ t in a..b, deriv f t * B1 t  := by
  have := sum_mul_eq_sub_sub_integral_mul (fun _ ↦ 1) ha hab hf_diff (Set.uIcc_of_le hab ▸ h_cont).integrableOn_Icc
  simp only [mul_one, sum_const, Nat.card_Icc, tsub_zero, nsmul_eq_mul, Nat.cast_add,
    Nat.cast_one] at this
  rw [this, ← intervalIntegral.integral_of_le hab]
  rw [integral_deriv_mul_floor_add_one ha hab hf_diff h_cont]
  unfold B1
  push_cast
  ring

end

-- ==== Vendor/Mertens
section
/-
Vendored from PrimeNumberTheoremAnd (https://github.com/AlexKontorovich/PrimeNumberTheoremAnd),
file `PrimeNumberTheoremAnd/IEANTN/Mertens.lean` (fork kimihiro64/PrimeNumberTheoremAnd, rev 0f15a38),
Apache License 2.0. Changes: converted from the module system to plain imports, blueprint annotations
(`@[blueprint ...]`, `blueprint_comment`) removed, namespaced imports adjusted. No mathematical changes.
-/


theorem Filter.EventuallyEq.iff_eventually {α : Type _} {β : Type _} {l : Filter α} {f g : α → β} : f =ᶠ[l] g ↔ ∀ᶠ (x : α) in l, f x = g x := by rfl


namespace Real

open Filter Asymptotics

theorem inv_log_eq_o_one : (fun x ↦ 1 / log x) =o[atTop] (fun _ ↦ (1:ℝ)) := by
    rw [isLittleO_one_iff]
    convert tendsto_log_atTop.inv_tendsto_atTop using 1
    ext; simp

theorem one_eq_o_log_log : (fun _ ↦ (1:ℝ)) =o[atTop] (fun x ↦ log (log x)) := by
    simp only [isLittleO_one_left_iff, norm_eq_abs]
    exact tendsto_abs_atTop_atTop.comp (tendsto_log_atTop.comp tendsto_log_atTop)

end Real

section Issue1584
open MeasureTheory Set Filter Topology

/-- The integrand `log v * exp (-v)` is integrable on `Ioi 0`. -/
private lemma integrableOn_log_mul_exp_neg :
    IntegrableOn (fun v : ℝ => Real.log v * Real.exp (-v)) (Ioi 0) := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ), integrableOn_union]
  constructor
  · -- On `Ioc 0 1`: dominate by `|log v|`, which is integrable.
    have hlog : IntegrableOn (fun v : ℝ => Real.log v) (Ioc 0 1) volume := by
      have := (intervalIntegral.intervalIntegrable_log' (a := 0) (b := 1))
      rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le (zero_le_one' ℝ)] at this
    apply Integrable.mono' hlog.norm
    · apply (Measurable.aestronglyMeasurable ?_)
      exact (Real.measurable_log.mul (Real.measurable_exp.comp measurable_neg))
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with v hv
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have h1 : |Real.exp (-v)| = Real.exp (-v) := abs_of_pos (Real.exp_pos _)
      have h2 : Real.exp (-v) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hv.1])
      rw [h1]
      nlinarith [abs_nonneg (Real.log v), Real.exp_pos (-v)]
  · -- On `Ioi 1`: dominate by `2 * exp (-v/2)`, integrable.
    have hexp : IntegrableOn (fun v : ℝ => (2 : ℝ) * Real.exp ((-1/2) * v)) (Ioi 1) volume := by
      exact (integrableOn_exp_mul_Ioi (by norm_num : (-1/2 : ℝ) < 0) 1).const_mul 2
    apply Integrable.mono' hexp
    · apply (Measurable.aestronglyMeasurable ?_)
      exact (Real.measurable_log.mul (Real.measurable_exp.comp measurable_neg))
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with v hv
      have hv1 : (1 : ℝ) ≤ v := le_of_lt hv
      have hvpos : (0 : ℝ) < v := by linarith
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have hlogabs : |Real.log v| = Real.log v :=
        abs_of_nonneg (Real.log_nonneg hv1)
      have hexpabs : |Real.exp (-v)| = Real.exp (-v) := abs_of_pos (Real.exp_pos _)
      rw [hlogabs, hexpabs]
      -- `log v ≤ v`
      have hlogv : Real.log v ≤ v := (Real.log_le_sub_one_of_pos hvpos).trans (by linarith)
      -- `v ≤ 2 * exp (v/2)`
      have hvexp : v ≤ 2 * Real.exp (v/2) := by
        have := Real.add_one_le_exp (v/2)
        nlinarith [Real.exp_pos (v/2)]
      -- combine: log v * exp(-v) ≤ v * exp(-v) ≤ 2 exp(v/2) exp(-v) = 2 exp(-v/2)
      have hstep : Real.log v * Real.exp (-v) ≤ 2 * Real.exp (v/2) * Real.exp (-v) := by
        apply mul_le_mul_of_nonneg_right (hlogv.trans hvexp) (le_of_lt (Real.exp_pos _))
      have heq : 2 * Real.exp (v/2) * Real.exp (-v) = 2 * Real.exp ((-1/2) * v) := by
        rw [mul_assoc, ← Real.exp_add]
        ring_nf
      rw [heq] at hstep
      exact hstep

/-- Helper: `∫_0^∞ log t · e^{-t} dt = Γ'(1)` (real). -/
private lemma integral_log_mul_exp_neg_eq_deriv_Gamma :
    ∫ t in Ioi (0:ℝ), Real.log t * Real.exp (-t) = deriv Real.Gamma 1 := by
  set I : ℝ := ∫ t in Ioi (0:ℝ), Real.log t * Real.exp (-t) with hI
  -- Step 1: derivative of GammaIntegral at 1.
  have h1 := Complex.hasDerivAt_GammaIntegral (s := (1 : ℂ)) (by norm_num)
  -- Step 2: simplify the integrand to `↑(log t * exp (-t))` and pull out `ofReal`.
  have hval : (∫ t : ℝ in Ioi 0, (↑t : ℂ) ^ ((1 : ℂ) - 1) * (↑(Real.log t) * ↑(Real.exp (-t))))
      = (I : ℂ) := by
    have key : ∀ t : ℝ, (↑t : ℂ) ^ ((1 : ℂ) - 1) * (↑(Real.log t) * ↑(Real.exp (-t)))
        = ((Real.log t * Real.exp (-t) : ℝ) : ℂ) := by
      intro t
      rw [sub_self, Complex.cpow_zero, one_mul, Complex.ofReal_mul]
    simp_rw [key]
    rw [integral_complex_ofReal, hI]
  rw [hval] at h1
  -- Step 3: transfer to Complex.Gamma (agrees with GammaIntegral on `{re > 0}`).
  have h2 : HasDerivAt Complex.Gamma (I : ℂ) 1 := by
    apply h1.congr_of_eventuallyEq
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (0:ℝ) < (1:ℂ).re by norm_num)] with z hz
    exact Complex.Gamma_eq_integral hz
  -- Step 4: transfer ℂ → ℝ.
  have h3 := h2.real_of_complex
  have h4 : HasDerivAt Real.Gamma I 1 := by
    have hcongr : (fun x : ℝ => (Complex.Gamma ↑x).re) = Real.Gamma := by
      funext x
      rw [Complex.Gamma_ofReal, Complex.ofReal_re]
    rw [hcongr, Complex.ofReal_re] at h3
    exact h3
  rw [← h4.deriv]

/-- Core of #1584, stated with explicit qualifiers (outside `namespace Mertens`,
where `Finset` is open and would clash with `Set.Ioi`). -/
private theorem mul_integ_log_log_eq_aux (s : ℝ) (hs : 1 < s) :
    (s - 1) * ∫ x in Ioi (1:ℝ), Real.log (Real.log x) * x ^ (-s) =
      - Real.log (s - 1) + deriv Real.Gamma 1 := by
  have hs0 : 0 < s - 1 := by linarith
  set f : ℝ → ℝ := fun x => (s - 1) * Real.log x with hf_def
  set f' : ℝ → ℝ := fun x => (s - 1) / x with hf'_def
  set g : ℝ → ℝ := fun u => (Real.log u - Real.log (s - 1)) * Real.exp (-u) with hg_def
  -- f 1 = 0
  have hf1 : f 1 = 0 := by simp [hf_def]
  -- ContinuousOn f (Ici 1)
  have hf_cont : ContinuousOn f (Ici 1) := by
    apply ContinuousOn.mul continuousOn_const
    apply Real.continuousOn_log.mono
    intro x hx
    simp only [mem_Ici] at hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    linarith
  -- Tendsto f atTop atTop
  have hft : Tendsto f atTop atTop := by
    apply Filter.Tendsto.const_mul_atTop hs0
    exact Real.tendsto_log_atTop
  -- HasDerivWithinAt f (f' x) (Ioi x) x for x ∈ Ioi 1
  have hff' : ∀ x ∈ Ioi (1:ℝ), HasDerivWithinAt f (f' x) (Ioi x) x := by
    intro x hx
    simp only [mem_Ioi] at hx
    have hxne : x ≠ 0 := by linarith
    have := (Real.hasDerivAt_log hxne).const_mul (s - 1)
    have h2 : HasDerivAt f ((s - 1) * x⁻¹) x := this
    have : (s - 1) * x⁻¹ = f' x := by rw [hf'_def]; field_simp
    rw [this] at h2
    exact h2.hasDerivWithinAt
  -- image facts: f strictly mono on Ici 1
  have hmono : StrictMonoOn f (Ici 1) := by
    intro a ha b hb hab
    simp only [mem_Ici] at ha hb
    apply mul_lt_mul_of_pos_left _ hs0
    exact Real.log_lt_log (by linarith) hab
  have himg_Ioi : f '' Ioi 1 = Ioi 0 := by
    ext y
    simp only [Set.mem_image, mem_Ioi]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have : 0 < Real.log x := Real.log_pos hx
      positivity
    · intro hy
      refine ⟨Real.exp (y / (s - 1)), ?_, ?_⟩
      · exact Real.one_lt_exp_iff.mpr (div_pos hy hs0)
      · rw [hf_def]
        simp only [Real.log_exp]
        field_simp
  have himg_Ici : f '' Ici 1 = Ici 0 := by
    ext y
    simp only [Set.mem_image, mem_Ici]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have : 0 ≤ Real.log x := Real.log_nonneg hx
      rw [hf_def]; positivity
    · intro hy
      refine ⟨Real.exp (y / (s - 1)), ?_, ?_⟩
      · exact Real.one_le_exp_iff.mpr (div_nonneg hy hs0.le)
      · rw [hf_def]
        simp only [Real.log_exp]
        field_simp
  -- ContinuousOn g (f '' Ioi 1) = ContinuousOn g (Ioi 0)
  have hg_cont : ContinuousOn g (f '' Ioi 1) := by
    rw [himg_Ioi]
    apply ContinuousOn.mul
    · apply ContinuousOn.sub _ continuousOn_const
      apply Real.continuousOn_log.mono
      intro u hu
      simp only [mem_Ioi] at hu
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      linarith
    · exact (Real.continuous_exp.comp continuous_neg).continuousOn
  -- IntegrableOn g (f '' Ici 1) = IntegrableOn g (Ici 0)
  have hg1 : IntegrableOn g (f '' Ici 1) := by
    rw [himg_Ici, integrableOn_Ici_iff_integrableOn_Ioi]
    have e1 : IntegrableOn (fun u => Real.log u * Real.exp (-u)) (Ioi 0) :=
      integrableOn_log_mul_exp_neg
    have e2 : IntegrableOn (fun u => Real.log (s - 1) * Real.exp (-u)) (Ioi 0) :=
      (integrableOn_exp_neg_Ioi 0).const_mul _
    have : g = fun u => Real.log u * Real.exp (-u) - Real.log (s - 1) * Real.exp (-u) := by
      funext u; rw [hg_def]; ring
    rw [this]
    exact e1.sub e2
  -- IntegrableOn (fun x => (g ∘ f) x * f' x) (Ici 1)
  have hg2 : IntegrableOn (fun x => (g ∘ f) x * f' x) (Ici 1) := by
    -- HasDerivWithinAt f (f' x) (Ici 1) x for x ∈ Ici 1.
    have hff'_Ici : ∀ x ∈ Ici (1:ℝ), HasDerivWithinAt f (f' x) (Ici 1) x := by
      intro x hx
      simp only [mem_Ici] at hx
      have hxne : x ≠ 0 := by linarith
      have hd : HasDerivAt f ((s - 1) * x⁻¹) x := (Real.hasDerivAt_log hxne).const_mul (s - 1)
      have heq : (s - 1) * x⁻¹ = f' x := by rw [hf'_def]; field_simp
      rw [heq] at hd
      exact hd.hasDerivWithinAt
    -- f injective on Ici 1.
    have hinj : InjOn f (Ici 1) := hmono.injOn
    -- transfer hg1 through the integrability change of variables.
    have hiff := integrableOn_image_iff_integrableOn_abs_deriv_smul
      (s := Ici (1:ℝ)) (f := f) (f' := f') measurableSet_Ici hff'_Ici hinj g
    rw [hiff] at hg1
    -- relate to our integrand on Ici 1.
    apply hg1.congr
    filter_upwards [self_mem_ae_restrict measurableSet_Ici] with x hx
    simp only [mem_Ici] at hx
    have hxpos : (0:ℝ) < x := by linarith
    have hf'pos : 0 < f' x := by rw [hf'_def]; positivity
    simp only [smul_eq_mul, Function.comp, abs_of_pos hf'pos]
    ring
  -- Apply change of variables.
  have hcov := integral_comp_mul_deriv_Ioi hf_cont hft hff' hg_cont hg1 hg2
  rw [hf1] at hcov
  -- RHS: ∫ u in Ioi 0, g u = deriv Gamma 1 - log (s-1)
  have hrhs : ∫ u in Ioi (0:ℝ), g u = deriv Real.Gamma 1 - Real.log (s - 1) := by
    have e1 : IntegrableOn (fun u => Real.log u * Real.exp (-u)) (Ioi 0) :=
      integrableOn_log_mul_exp_neg
    have e2 : IntegrableOn (fun u => Real.log (s - 1) * Real.exp (-u)) (Ioi 0) :=
      (integrableOn_exp_neg_Ioi 0).const_mul _
    have hsplit : (fun u => g u)
        = fun u => Real.log u * Real.exp (-u) - Real.log (s - 1) * Real.exp (-u) := by
      funext u; rw [hg_def]; ring
    rw [show (∫ u in Ioi (0:ℝ), g u)
        = ∫ u in Ioi (0:ℝ), (Real.log u * Real.exp (-u) - Real.log (s - 1) * Real.exp (-u))
        from by rw [hsplit]]
    rw [integral_sub e1 e2, integral_log_mul_exp_neg_eq_deriv_Gamma]
    rw [integral_const_mul, integral_exp_neg_Ioi_zero, mul_one]
  -- LHS: ∫ x in Ioi 1, (g∘f) x * f' x = (s-1) * ∫ x in Ioi 1, log(log x) * x^(-s)
  have hlhs : ∫ x in Ioi (1:ℝ), (g ∘ f) x * f' x
      = (s - 1) * ∫ x in Ioi (1:ℝ), Real.log (Real.log x) * x ^ (-s) := by
    have hpt : ∀ x ∈ Ioi (1:ℝ), (g ∘ f) x * f' x
        = (s - 1) * (Real.log (Real.log x) * x ^ (-s)) := by
      intro x hx
      simp only [mem_Ioi] at hx
      have hxpos : (0:ℝ) < x := by linarith
      have hlogpos : 0 < Real.log x := Real.log_pos hx
      have hlogne : Real.log x ≠ 0 := ne_of_gt hlogpos
      have hs1ne : s - 1 ≠ 0 := ne_of_gt hs0
      simp only [Function.comp, hf_def, hg_def, hf'_def]
      -- log ((s-1) * log x) - log (s-1) = log (log x)
      rw [Real.log_mul hs1ne hlogne]
      -- exp (-((s-1) * log x)) = x ^ (-(s-1))
      have hexp : Real.exp (-((s - 1) * Real.log x)) = x ^ (-(s - 1)) := by
        rw [Real.rpow_def_of_pos hxpos]
        ring_nf
      rw [hexp]
      -- x ^ (-(s-1)) * ((s-1)/x) = (s-1) * x^(-s)
      have hx1 : x ^ (-(s - 1)) * ((s - 1) / x) = (s - 1) * x ^ (-s) := by
        rw [div_eq_mul_inv, ← Real.rpow_neg_one x]
        rw [show x ^ (-(s - 1)) * ((s - 1) * x ^ (-1 : ℝ))
            = (s - 1) * (x ^ (-(s - 1)) * x ^ (-1 : ℝ)) by ring]
        rw [← Real.rpow_add hxpos]
        ring_nf
      rw [show (Real.log (s - 1) + Real.log (Real.log x) - Real.log (s - 1))
          = Real.log (Real.log x) by ring]
      linear_combination Real.log (Real.log x) * hx1
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul]
  rw [hlhs, hrhs] at hcov
  rw [hcov]
  ring

end Issue1584

namespace Mertens



open Real Finset Filter Asymptotics Topology
open ArithmeticFunction hiding log

lemma sum_Ioc_one_eq_sum_Ioc_zero {f : ℕ → ℝ} {x : ℕ} (hx : 1 ≤ x) (hf : f 1 = 0) :
    ∑ n ∈ Ioc 1 x, f n = ∑ n ∈ Ioc 0 x, f n := by
  rw [(by rfl : Ioc 0 x = Icc 1 x), ← add_sum_Ioc_eq_sum_Icc hx]
  simpa

theorem sum_log_eq {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n =
      x * log x - (x - ⌊x⌋₊ - 1 / 2) * log x - x + 1 + ∫ t in 1..x, (t - ⌊t⌋₊ - 1 / 2) / t := by
  rw [← sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp)]
  have : 1 = ⌊(1 : ℝ)⌋₊ := by simp
  nth_rw 1 [this]
  rw [sum_eq_integral_add_integral_deriv (by norm_num) hx (fun _ _ ↦ (by fun_prop (disch := grind)))]
  · simp only [log_one, B1, Nat.floor_one, Nat.cast_one, sub_self, zero_sub,
    RCLike.ofReal_real_eq_id, id_eq, mul_neg, zero_mul, neg_zero, integral_log, mul_zero, sub_zero,
    deriv_log']
    ring_nf
    congr
    ext
    ring
  · simp only [deriv_log', Set.uIcc_of_le hx]
    fun_prop (disch := grind)

theorem sum_log_le {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n ≤ x * log x := by
  calc
  _ ≤ ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log x := by
    refine sum_le_sum fun n hn ↦ ?_
    simp only [mem_Ioc] at hn
    exact log_le_log (by exact_mod_cast hn.1) (Nat.le_floor_iff (by linarith)|>.mp hn.2)
  _ = ⌊x⌋₊ * log x := by simp
  _ ≤ _ := by
    gcongr
    · exact log_nonneg hx
    · exact Nat.floor_le (by linarith)


lemma integral_log_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∫ t in a..b, log t ≤ log b * (b - a) := by
  apply le_of_abs_le
  have : ∀ t ∈ Set.uIoc a b, ‖log t‖ ≤ log b := by
    intro t ht
    rw [Set.uIoc_of_le hab, Set.mem_Ioc] at ht
    rw [norm_of_nonneg <| log_nonneg (by linarith)]
    gcongr <;> linarith
  grw [← norm_eq_abs, intervalIntegral.norm_integral_le_of_norm_le_const this,
    abs_of_nonneg (by linarith)]

theorem sum_log_ge {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n ≥ x * log x - 2 * x := by
  have one_le_floor : 1 ≤ ⌊x⌋₊ := by simpa
  calc
  _ = ∑ n ∈ Icc 1 ⌊ x ⌋₊, log n := by rfl
  _ = ∑ n ∈ Ico (1 + 1) (⌊ x ⌋₊ + 1), log n := by
    rw [← add_sum_Ioc_eq_sum_Icc one_le_floor]
    simp
    rfl
  _ = ∑ n ∈ Ico 1 ⌊ x ⌋₊, log ((n + 1 : ℕ)) := by
    rw [← Finset.sum_Ico_add']
  _ ≥ ∫ t in 1..⌊x⌋₊, log t := by
    convert MonotoneOn.integral_le_sum_Ico one_le_floor ?_|>.ge
    · norm_cast
    · exact StrictMonoOn.monotoneOn (strictMonoOn_log.mono fun y hy ↦ (by simp_all; linarith))
  _ = (∫ t in 1..x, log t) - ∫ t in ⌊x⌋₊..x, log t := by
    nth_rw 3 [intervalIntegral.integral_symm]
    rw [sub_neg_eq_add, intervalIntegral.integral_add_adjacent_intervals] <;> exact intervalIntegral.intervalIntegrable_log'
  _ ≥ (∫ t in 1..x, log t) - log x := by
    gcongr
    grw [integral_log_le (by simpa) (Nat.floor_le (by linarith))]
    nth_rw 2 [← mul_one (log x)]
    gcongr
    · exact log_nonneg hx
    · linarith [Nat.lt_floor_add_one x]
  _ ≥ x * log x - x - log x := by simp only [integral_log, log_one, mul_zero, sub_zero, ge_iff_le,
    tsub_le_iff_right, sub_add_cancel, le_add_iff_nonneg_right, zero_le_one]
  _ ≥ _ := by linarith [log_le_self (by linarith : 0 ≤ x)]

theorem sum_log_eq_log_factorial (x : ℝ) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n = log (Nat.floor x).factorial := by
    rw [←prod_Ico_id_eq_factorial, ←log_prod, prod_natCast]
    · congr
    intro x hx
    simp at hx ⊢; grind

theorem sum_log_eq_sum_mangoldt {x : ℝ} :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, log n = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
  have : ∀ n : ℕ, log n = (Λ * zeta) n := by simp [vonMangoldt_mul_zeta]
  simp_rw [this, sum_Ioc_mul_zeta_eq_sum, ← Nat.floor_div_natCast]

noncomputable abbrev E₁Λ (x : ℝ) : ℝ := ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d - log x

theorem sum_mangoldt_div_eq (x : ℝ) : ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d = log x + E₁Λ x := by
    grind

theorem E₁Λ.ge {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x  ≥ -2 := by
  unfold E₁Λ
  suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d  ≥ x * (log x - 2) by
    linarith [le_of_mul_le_mul_left this (by linarith)]
  calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [Finset.mul_sum]
    ring_nf
  _ ≥ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
    gcongr
    exact Nat.floor_le <| div_nonneg (by linarith) (by linarith)
  _ ≥ x * log x - 2 * x :=
    sum_log_eq_sum_mangoldt ▸ sum_log_ge hx
  _ = _ := by ring



theorem E₁Λ.le {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x ≤ log 4 + 4 := by
  unfold E₁Λ
  suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ x * (log x + log 4 + 4) by
    linarith [le_of_mul_le_mul_left this (by linarith)]
  calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [Finset.mul_sum]
    ring_nf
  _ ≤ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (⌊x / d⌋₊ + 1) := by
    gcongr
    exact Nat.lt_floor_add_one _|>.le
  _ = (∑ d ∈ Ioc 0 ⌊x⌋₊, log d) + ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d := by
    simp_rw [mul_add, mul_one]
    rw [Finset.sum_add_distrib, sum_log_eq_sum_mangoldt]
  _ ≤ x * log x + (log 4 + 4) * x := by
    gcongr
    · exact sum_log_le hx
    · exact Chebyshev.psi_le_const_mul_self (by linarith)
  _ = _ := by ring

theorem sum_mangoldt_div_eq_log {x : ℝ} (hx : 1 ≤ x) :
    |∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d - log x| ≤ log 4 + 4 := by
  grind [E₁Λ.le hx, E₁Λ.ge hx, log_nonneg]

theorem E₁Λ.bounded' : ∃ c > 0, ∀ x ≥ 1, |E₁Λ x| ≤ c := by
  exact ⟨log 4 + 4, (by positivity), fun x hx ↦ sum_mangoldt_div_eq_log hx⟩



theorem E₁Λ.bounded : E₁Λ =O[atTop] (fun _ ↦ (1:ℝ)) := by
  simp only [isBigO_iff, norm_eq_abs, norm_one, mul_one,
    eventually_atTop]
  exact ⟨log 4 + 4, 1, fun _ hx ↦ sum_mangoldt_div_eq_log hx⟩

theorem one_eq_o_log : (fun _ ↦ (1:ℝ)) =o[atTop] (fun x ↦ log x) := by
    simp only [isLittleO_one_left_iff, norm_eq_abs]
    exact tendsto_abs_atTop_atTop.comp tendsto_log_atTop

theorem sum_mangoldt_div_eq_log' :
    (fun x ↦ ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d) ~[atTop] (fun x ↦ log x) := by
    apply IsLittleO.isEquivalent (IsBigO.trans_isLittleO _ one_eq_o_log)
    convert! E₁Λ.bounded using 1

noncomputable abbrev E₁p (x : ℝ) : ℝ := ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p - log x

theorem sum_log_prime_div_eq (x : ℝ) : ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p = log x + E₁p x := by
    grind

theorem E₁p.le_E₁Λ (x : ℝ) :
    E₁p x ≤ E₁Λ x := by
    unfold E₁p E₁Λ; rw [sum_filter]
    gcongr with p _
    split_ifs with hp
    · simp [vonMangoldt_apply_prime hp]
    have : 0 ≤ Λ p := vonMangoldt_nonneg
    positivity

theorem E₁p.le {x : ℝ} (hx : 1 ≤ x) :
    E₁p x ≤ log 4 + 4 := by
    linarith [E₁Λ.le hx, E₁p.le_E₁Λ x]

noncomputable abbrev E₁ : ℝ := ∑' p : ℕ, if p.Prime then (log p) / (p*(p-1)) else 0

lemma E₁.summand_nonneg (p : ℕ) : 0 ≤ if p.Prime then (log p) / (p*(p-1)) else 0 := by
  split_ifs with h
  · refine div_nonneg (log_natCast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) ?_)
    suffices 1 ≤ (p : ℝ) by linarith
    exact_mod_cast h.one_le
  · rfl

theorem E₁.summable : Summable (fun p : ℕ ↦ if p.Prime then (log p) / (p*(p-1)) else 0) := by
  refine (Real.summable_one_div_nat_rpow.mpr (by norm_num: 1 < (3 : ℝ) / 2)|>.const_div
    4).of_nonneg_of_le E₁.summand_nonneg fun n ↦ ?_
  split_ifs with h
  · grw [Real.log_le_rpow_div (Nat.cast_nonneg _) (by norm_num : 0 < (1 : ℝ) / 2)]
    · have denom : (n : ℝ) * ((n : ℝ) - 1) ≥ n ^ 2/ 2 := by
        rw [sq, mul_div_assoc]
        gcongr
        suffices (n : ℝ) ≥ 2 by linarith
        exact_mod_cast h.two_le
      grw [denom]
      · apply le_of_eq
        rw [← Real.rpow_natCast]
        field_simp
        rw [mul_div_assoc, ← Real.rpow_sub (mod_cast h.pos)]
        norm_num
        rw [Real.rpow_neg (Nat.cast_nonneg _)]
        field
      · exact div_pos (pow_pos (mod_cast h.pos) _) (by norm_num)
    · apply mul_nonneg (Nat.cast_nonneg _)
      suffices 1 ≤ (n : ℝ) by linarith
      exact_mod_cast h.one_le
  · positivity

private lemma antitoneOn_log_div_sq :
    AntitoneOn (fun t ↦ log (t + 2) / (t + 2) ^ 2) (Set.Ici 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
  · refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
    simp at ht
    have : (t + 2) ≠ 0 := by simp; linarith
    fun_prop (disch := grind)
  · refine fun t ht ↦ DifferentiableAt.differentiableWithinAt ?_
    simp at ht
    have : (t + 2) ^ 2 ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · intro t ht
    simp at ht
    rw [deriv_fun_div (by fun_prop (disch := grind)) (by fun_prop) (by simp; grind), deriv_comp_add_const, deriv_log]
    simp
    field_simp
    simp only [mul_zero, tsub_le_iff_right, zero_add]
    rw [← log_rpow (by linarith), ← log_exp 1, rpow_ofNat]
    gcongr
    nlinarith [exp_one_lt_three]

private lemma log_div_sq_nonneg :
    ∀ t ∈ Set.Ioi 0, 0 ≤ log (t + 2) / (t + 2) ^ 2 := by
  exact fun t ht ↦  div_nonneg (log_nonneg (by simp_all; linarith)) (by positivity)

private lemma log_div_sq_is_deriv :
    ∀ x ∈ Set.Ici 0, HasDerivAt (fun t ↦ (-log (t + 2) - 1) / (t + 2)) (log (x + 2) / (x + 2) ^ 2) x := by
  intro t ht
  simp at ht
  apply HasDerivAt.comp_add_const (f := (fun t ↦ (-log t - 1)/ t)) t 2
  convert! HasDerivAt.fun_div (c' := -1 / (t + 2)) (d' := (1 : ℝ)) _ _  _ using 1
  · field
  · apply HasDerivAt.sub_const
    convert! (hasDerivAt_log (by linarith : t + 2 ≠ 0)).neg using 1
    ring_nf
  · exact hasDerivAt_id _
  · linarith

private lemma tendsto_antideriv_log_div_sq :
    Tendsto (fun t ↦ (-log (t + 2) - 1) / (t + 2)) atTop (nhds 0) := by
  have : Tendsto (fun (t : ℝ) ↦ t + 2) atTop atTop := by exact tendsto_atTop_add_const_right atTop 2 tendsto_id
  apply Tendsto.comp (g := (fun t ↦ (-log t - 1) / t)) _ this
  convert! Tendsto.sub (f := (fun t ↦ -log t / t)) (a := 0) _ tendsto_inv_atTop_zero using 1
  · ring_nf
  · ring_nf
  · convert! (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by linarith)).neg using 1
    · ext; ring
    · simp

private lemma integrableOn_log_div_sq :
    MeasureTheory.IntegrableOn (fun t ↦ log (t + 2) / (t + 2) ^ 2) (Set.Ioi 0) := by
  exact MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' log_div_sq_is_deriv log_div_sq_nonneg tendsto_antideriv_log_div_sq

private lemma integral_log_div_sq :
    ∫ t in Set.Ioi 0, log (t + 2) / (t + 2) ^ 2 = (log 2 + 1) / 2 := by
  rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' log_div_sq_is_deriv log_div_sq_nonneg tendsto_antideriv_log_div_sq]
  ring_nf

private lemma summable_log_div_sq :
    Summable (fun (n : ℕ)↦ log (n + 3) / (n + 3) ^ 2) := by
  let g : ℝ → ℝ := (fun n ↦ log (n + 2) / (n + 2) ^ 2)
  suffices Summable (fun (n : ℕ) ↦ g n ) by
    convert! summable_nat_add_iff 1|>.mpr this using 2
    unfold g
    push_cast
    ring_nf
  exact antitoneOn_log_div_sq.summable_of_integrableOn_Ioi_zero integrableOn_log_div_sq log_div_sq_nonneg

private lemma sum_log_div_sq_le :
    ∑' (n : ℕ), log (n + 3) / (n + 3) ^2 ≤ (log 2 + 1) / 2 := by
  let g : ℝ → ℝ := (fun n ↦ log (n + 2) / (n + 2) ^ 2)
  calc
  _ = ∑' (n : ℕ), g (n + 1 : ℕ):= by
    unfold g
    congr
    push_cast
    ring_nf
  _ ≤ ∫ x in Set.Ioi 0, g x := by
    exact antitoneOn_log_div_sq.tsum_add_one_le_integral integrableOn_log_div_sq log_div_sq_nonneg
  _ = _ := by
    exact integral_log_div_sq

theorem E₁.le : E₁ ≤ (5 * log 2 + 3) / 4 := by
  unfold E₁
  calc
  _ = log 2 / 2 + ∑' (n : ℕ), if (n + 3).Prime then log (n + 3) / ((n + 3) * (n + 2)) else 0 := by
    rw [← E₁.summable.sum_add_tsum_nat_add 3, (by rfl : range 3 = {0, 1, 2})]
    simp [Nat.prime_two]
    ring_nf
  _ ≤ log 2 / 2 + ∑' (n : ℕ), (3 / 2) * (log (n + 3) / (n + 3) ^ 2) := by
    gcongr with n
    · convert! summable_nat_add_iff 3|>.mpr E₁.summable using 4
      · norm_cast
      · push_cast; ring
    · exact summable_log_div_sq.mul_left _
    · split_ifs with h
      · grw [(by linarith : (n + 2 : ℝ) ≥ 2 * (n + 3) / 3)]
        · field_simp
          rfl
        · exact log_nonneg (by grind)
      · exact mul_nonneg (by norm_num) (div_nonneg (log_nonneg (by grind)) (by positivity))
  _ = log 2 / 2 + (3 / 2) * ∑' (n : ℕ), log (n + 3) / (n + 3) ^ 2 := by
    rw [tsum_mul_left]
  _ ≤ _ := by
    grw [sum_log_div_sq_le]
    ring_nf
    rfl

theorem E₁.nonneg : E₁ ≥ 0 :=
  tsum_nonneg E₁.summand_nonneg

theorem E₁Λ.le_E₁p_add_E₁ {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x ≤ E₁p x + E₁ := by
  unfold E₁Λ E₁p
  suffices ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / p + E₁ by linarith
  simp_rw [vonMangoldt_apply, ite_div, zero_div, ← sum_filter, Chebyshev.sum_PrimePow_eq_sum_sum _ (by linarith)]
  calc
  _ = ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ Ioc 0 ⌊x ^ (1 / (k : ℝ))⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    refine sum_congr rfl fun k hk ↦ sum_congr rfl fun p hp ↦ ?_
    rw [Nat.Prime.pow_minFac (by simp_all) (by simp_all; linarith)]
  _ ≤ ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    gcongr with k hk
    apply rpow_le_self_of_one_le hx
    simp only [mem_Icc] at hk
    exact div_le_one₀ (by norm_cast; linarith)|>.mpr (mod_cast hk.1)
  _ ≤ ∑ k ∈ Icc 1 (max 1 ⌊log x / log 2⌋₊), ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    apply sum_le_sum_of_subset_of_nonneg
    · gcongr
      exact le_max_right ..
    · exact fun _ _ _ ↦ sum_nonneg fun _ _ ↦ (by positivity)
  _ = ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, (log p / p) + ∑ k ∈ Ioc 1 (max 1 ⌊log x / log 2⌋₊), ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    rw [← add_sum_Ioc_eq_sum_Icc (le_max_left ..)]
    simp
  _ ≤ _ := by
    gcongr
    rw [sum_comm]
    conv => lhs; arg 2; ext p; arg 2; ext k; rw [← mul_one_div, Nat.cast_pow, ← one_div_pow]
    simp_rw [← mul_sum]
    calc
    _ ≤ ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p * (p - 1)) := by
      gcongr with p hp
      simp only [mem_filter, mem_Ioc] at hp
      conv => rhs; rw [← mul_one_div]
      gcongr
      rw [(by rfl : Ioc 1 (max 1 ⌊log x / log 2⌋₊) = Ico 2 (max 1 ⌊log x / log 2⌋₊  + 1))]
      grw [geom_sum_Ico_le_of_lt_one (by simp)]
      · apply le_of_eq
        have : (p : ℝ) ≠ 0 := by exact_mod_cast hp.1.1.ne.symm
        field
      · simpa using inv_lt_one_of_one_lt₀ (mod_cast hp.2.one_lt)
    _ ≤ _ := by
      rw [sum_filter]
      exact E₁.summable.sum_le_tsum _ fun p hp ↦ E₁.summand_nonneg p

theorem E₁p.ge {x : ℝ} (hx : 1 ≤ x) :
    E₁p x ≥ -2 - E₁ := by
    linarith [E₁Λ.le_E₁p_add_E₁ hx, E₁Λ.ge hx]


theorem sum_log_prime_div_eq_log {x : ℝ} (hx : 1 ≤ x) :
    |∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p - log x| ≤ log 4 + 4 := by
    rw [abs_le']
    refine ⟨ E₁p.le hx, ?_ ⟩
    have : log 2 > 0 := by apply log_pos; norm_num
    have : log 4 = 2 * log 2 := by rw [←Real.log_rpow (by norm_num)]; norm_num
    grind [E₁p.ge hx, E₁.le]

theorem E₁p.bounded : ∃ c > 0, ∀ x ≥ 1, |E₁p x| ≤ c := by
  exact ⟨log 4 + 4, (by positivity), fun _ hx ↦ sum_log_prime_div_eq_log  hx⟩

theorem sum_log_prime_div_eq_log' : E₁p =O[atTop] (fun _ ↦ (1:ℝ)) := by
    simp only [isBigO_iff, norm_eq_abs, one_mem, CStarRing.norm_of_mem_unitary, mul_one,
      eventually_atTop, E₁p]
    exact ⟨ log 4 + 4, 1, fun _ ↦ sum_log_prime_div_eq_log ⟩

theorem sum_log_prime_div_eq_log'' : (fun x ↦ ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p) ~[atTop] (fun x ↦ log x) := by
    apply IsLittleO.isEquivalent (IsBigO.trans_isLittleO _ one_eq_o_log)
    convert! sum_log_prime_div_eq_log' using 1

noncomputable abbrev γ : ℝ := (∫ t in Set.Ioi 2, E₁Λ t / (t * log t^2)) + 1 - log (log 2)

noncomputable abbrev E₂Λ (x : ℝ) : ℝ := ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / (d * log d) - log (log x) - γ

lemma sum_Ioc_one_eq_sum_Icc_zero {f : ℕ → ℝ} {x : ℕ} (hx : 1 ≤ x) (hf1 : f 1 = 0) (hf0 : f 0 = 0) :
    ∑ n ∈ Ioc 1 x, f n = ∑ n ∈ Icc 0 x, f n := by
  rw [sum_Ioc_one_eq_sum_Ioc_zero hx hf1, ← add_sum_Ioc_eq_sum_Icc (by linarith)]
  simpa

private theorem sum_div_log_eq {x : ℝ} (hx : 2 ≤ x) (f : ℕ → ℝ) :
    ∑ n ∈ Ioc 1 ⌊ x ⌋₊, f n / log n =
      (∑ n ∈ Ioc 1 ⌊ x ⌋₊, f n) / log x + ∫ t in 2..x, (∑ n ∈ Ioc 1 ⌊ t ⌋₊, f n) / (t * log t^2) := by
  let g : ℕ → ℝ := (fun n ↦ if n < 2 then 0 else f n)
  trans ∑ n ∈ Icc 0 ⌊ x ⌋₊, (log n)⁻¹ * g n
  · rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp) (by simp)]
    refine sum_congr rfl fun n hn ↦ ?_
    have : ¬(n ≤ 1) := by simp_all
    simp [g, this]
    field
  rw [sum_mul_eq_sub_integral_mul₁ g (f := (fun n ↦ (log n)⁻¹)) (by simp [g]) (by simp [g])]
  · rw [intervalIntegral.integral_of_le hx, mul_comm, ← div_eq_mul_inv, ← sub_neg_eq_add]
    simp_rw [deriv_inv_log]
    congr 1
    · rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp [g]) (by simp [g])]
      congr 1
      refine sum_congr rfl fun n hn ↦ ?_
      simp only [mem_Ioc] at hn
      have : ¬(n ≤ 1) := by linarith
      simp [g, this]
    · rw [← MeasureTheory.integral_neg]
      refine  MeasureTheory.setIntegral_congr_fun (by measurability) fun t ht ↦ ?_
      simp only [Set.mem_Ioc] at ht
      rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp [g]) (by simp [g])]
      field_simp
      congr 2
      refine sum_congr rfl fun n hn ↦ ?_
      simp only [mem_Ioc] at hn
      have : ¬(n ≤ 1) := by linarith
      simp [g, this]
  · intro t ht
    simp only [Set.mem_Icc] at ht
    have : log t ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · refine ContinuousOn.integrableOn_Icc fun t ht ↦ ContinuousAt.continuousWithinAt ?_
    simp only [Set.mem_Icc] at ht
    conv => arg 1; ext x; rw [deriv_inv_log]
    have : log t ^2 ≠ 0 := by simp; grind
    fun_prop (disch := grind)

private theorem integrable_const_div_mul_log_sq {x : ℝ} (c : ℝ) (hx : 2 ≤ x) :
    MeasureTheory.IntegrableOn (fun x ↦ c / (x * log x ^ 2)) (Set.Ioi x) MeasureTheory.volume := by
  conv => arg 1; ext t; rw [← mul_one_div]
  apply MeasureTheory.Integrable.const_mul
  refine MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' ?_ ?_ tendsto_log_atTop.inv_tendsto_atTop.neg
  · intro t ht
    simp only [Set.mem_Ici] at ht
    have : log t ≠ 0 := by simp; grind
    have : DifferentiableAt ℝ (fun t ↦ -(log t)⁻¹) t := by
      fun_prop (disch := grind)
    convert! this.hasDerivAt using 1
    simp [deriv_inv_log]
    field
  · intro t ht
    simp only [Set.mem_Ioi] at ht
    exact one_div_nonneg.mpr <| mul_nonneg (by linarith) (sq_nonneg _)


private theorem integrable_E₁Λ_div_mul_log_sq {x : ℝ} (hx : 2 ≤ x) :
    MeasureTheory.IntegrableOn (fun x ↦ E₁Λ x / (x * log x ^ 2)) (Set.Ioi x) MeasureTheory.volume := by
  obtain ⟨c, hc1, hc2⟩ := E₁Λ.bounded'
  apply MeasureTheory.Integrable.mono (integrable_const_div_mul_log_sq c hx)
  · exact Measurable.aestronglyMeasurable (by fun_prop)
  · filter_upwards [MeasureTheory.ae_restrict_mem (by measurability)] with t ht
    simp only [Set.mem_Ioi] at ht
    simp only [norm_div, norm_eq_abs, norm_mul, norm_pow, sq_abs, abs_of_pos hc1]
    gcongr
    exact hc2 t (by linarith)

private theorem integrable_E₁p_div_mul_log_sq {x : ℝ} (hx : 2 ≤ x) :
    MeasureTheory.IntegrableOn (fun x ↦ E₁p x / (x * log x ^ 2)) (Set.Ioi x) MeasureTheory.volume := by
  obtain ⟨c, hc1, hc2⟩ := E₁p.bounded
  apply MeasureTheory.Integrable.mono (integrable_const_div_mul_log_sq c hx)
  · exact Measurable.aestronglyMeasurable (by fun_prop)
  · filter_upwards [MeasureTheory.ae_restrict_mem (by measurability)] with t ht
    simp only [Set.mem_Ioi] at ht
    simp only [norm_div, norm_eq_abs, norm_mul, norm_pow, sq_abs, abs_of_pos hc1]
    gcongr
    exact hc2 t (by linarith)

lemma deriv_log_log {x : ℝ} (hx : 1 < x) :
    deriv (fun t ↦ log (log t)) x = 1 / (x * log x) := by
  rw [deriv.log (differentiableAt_log (by linarith)) (by simp; grind), deriv_log]
  field

lemma integral_one_div_mul_log {x : ℝ} (hx : 2 ≤ x) :
    ∫ t in 2..x, 1 / (t * log t) = log (log x) - log (log 2) := by
  rw [← intervalIntegral.integral_deriv_eq_sub (f := fun t ↦ log (log t))]
  · refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [deriv_log_log]
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    linarith
  · intro t ht
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    have : log t ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · refine ContinuousOn.intervalIntegrable ?_
    apply ContinuousOn.congr (f := (fun t ↦ 1 / (t * log t)))
    · refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
      rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
      have : log t ≠ 0 := by simp; grind
      fun_prop (disch := grind)
    · intro t ht
      rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
      exact deriv_log_log (by linarith)

lemma intervalIntegrable_one_div_mul_log {x : ℝ} (hx : 2 ≤ x) :
    IntervalIntegrable (fun t ↦ 1 / (t * log t)) MeasureTheory.volume 2 x := by
  refine ContinuousOn.intervalIntegrable fun t ht ↦ ContinuousAt.continuousWithinAt ?_
  rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
  have : log t ≠ 0 := by simp; grind
  fun_prop (disch := grind)

theorem E₂Λ.eq {x : ℝ} (hx : 2 ≤ x) :
    E₂Λ x = E₁Λ x / log x - ∫ t in Set.Ioi x, E₁Λ t / (t * log t^2) := by
  unfold E₂Λ
  rw [← sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp)]
  conv => lhs; arg 1; arg 1; arg 2; ext n; rw [(by field : Λ n / (n * log n) = (Λ n / n) / log n)]
  rw [sum_div_log_eq hx]
  rw [sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), sum_mangoldt_div_eq]
  have : ∫ t in 2..x, (∑ n ∈ Ioc 1 ⌊t⌋₊, Λ n / n) / (t * log t ^ 2) = ∫ t in 2..x, (1 / (t * log t) + E₁Λ t / (t * log t ^ 2)) := by
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    rw [sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), sum_mangoldt_div_eq]
    field
  rw [this, intervalIntegral.integral_add]
  · rw [integral_one_div_mul_log hx, add_div, div_self (by simp; grind)]
    unfold γ
    calc
    _ = E₁Λ x / log x + (∫ (x : ℝ) in 2..x, E₁Λ x / (x * log x ^ 2)) -
      ((∫ (t : ℝ) in Set.Ioi 2, E₁Λ t / (t * log t ^ 2))) := by ring
    _ = _ := by
      rw [← intervalIntegral.integral_interval_add_Ioi (integrable_E₁Λ_div_mul_log_sq (by rfl)) (integrable_E₁Λ_div_mul_log_sq hx)]
      ring
  · exact intervalIntegrable_one_div_mul_log hx
  · rw [intervalIntegrable_iff, Set.uIoc_of_le hx]
    exact integrable_E₁Λ_div_mul_log_sq (x := 2) (by rfl)|>.mono (by grind) (by rfl)

private theorem integ_div_mul_log_sq {x : ℝ} (c : ℝ) (hx : 2 ≤ x) :
    ∫ t in Set.Ioi x, c / (t * log t^2) = c / log x := by
    convert! MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' (m := 0) (f := fun x ↦ - c / log x) ?_
      (integrable_const_div_mul_log_sq c hx) ?_ using 1
    · grind
    · intro t ht; simp at ht
      convert! HasDerivAt.fun_div (hasDerivAt_const _ (-c)) (hasDerivAt_log (by linarith)) ?_ using 1
      · grind
      simp; grind
    convert! tendsto_log_atTop.inv_tendsto_atTop.const_mul (-c) using 1
    simp

theorem E₂Λ.abs_le {x : ℝ} (hx : 2 ≤ x) :
    |E₂Λ x| ≤ (log 4 + 6) / log x := by
    have : 0 < log x := by apply log_pos; linarith
    rw [E₂Λ.eq hx, abs_le']
    constructor
    · grw [E₁Λ.le (by linarith)]
      have : ∫ t in Set.Ioi x, E₁Λ t / (t * log t^2) ≥ - 2 / log x := calc
        _ ≥ ∫ t in Set.Ioi x, (-2) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_const_div_mul_log_sq (-2) hx)
            (integrable_E₁Λ_div_mul_log_sq hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := log_pos this
          gcongr; exact E₁Λ.ge (by linarith)
        _ = _ := integ_div_mul_log_sq (-2) hx
      grw [this]
      grind
    grw [E₁Λ.ge (by linarith)]
    have : ∫ t in Set.Ioi x, E₁Λ t / (t * log t^2) ≤ (log 4 + 4) / log x := calc
        _ ≤ ∫ t in Set.Ioi x, (log 4 + 4) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_E₁Λ_div_mul_log_sq hx)
            (integrable_const_div_mul_log_sq (log 4 + 4) hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := log_pos this
          gcongr; exact E₁Λ.le (by linarith)
        _ = _ := integ_div_mul_log_sq (log 4 + 4) hx
    grw [this]
    grind


theorem E₂Λ.bound : E₂Λ =O[atTop] (fun x ↦ 1 / log x) := by
    simp only [one_div, isBigO_iff, norm_eq_abs, norm_inv, eventually_atTop]
    use log 4 + 6, 2
    intro x hx
    convert E₂Λ.abs_le hx using 1
    have : 0 < log x := by apply log_pos; linarith
    grind [abs_of_pos this]

theorem E₂Λ.bound' : E₂Λ =o[atTop] (fun _ ↦ (1:ℝ)) := E₂Λ.bound.trans_isLittleO inv_log_eq_o_one

theorem log_zeta_eq_sum (s : ℝ) (hs : 1 < s) :
    log (riemannZeta (s:ℂ)).re = ∑' n, Λ n / (n^s * log n) := by
  have hsc : (1 : ℝ) < ((s : ℂ)).re := by simpa using hs
  -- (II) Euler log product
  have hep := riemannZeta_eulerProduct_exp_log (s := (s : ℂ)) hsc
  set S : ℂ := ∑' p : Nat.Primes, -Complex.log (1 - (p : ℂ) ^ (-(s : ℂ))) with hS
  -- bridge: prime cpow equals real rpow
  have hcpow : ∀ p : Nat.Primes, (p : ℂ) ^ (-(s : ℂ)) = (((p : ℝ) ^ (-s) : ℝ) : ℂ) := by
    intro p
    rw [Complex.ofReal_cpow (by positivity)]
    push_cast; ring_nf
  -- the real value of each prime term
  set z : Nat.Primes → ℝ := fun p => (p : ℝ) ^ (-s) with hz
  -- z p ∈ (0,1)
  have hz_pos : ∀ p : Nat.Primes, 0 < z p := fun p => by
    have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.pos
    positivity
  have hz_lt_one : ∀ p : Nat.Primes, z p < 1 := by
    intro p
    have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
    change (p : ℝ) ^ (-s) < 1
    rw [Real.rpow_neg (by positivity), inv_lt_one_iff₀]
    right
    exact (Real.one_lt_rpow_iff_of_pos (by positivity)).mpr (Or.inl ⟨hp1, by linarith⟩)
  -- each summand is the ofReal of a real number
  have hterm : ∀ p : Nat.Primes,
      -Complex.log (1 - (p : ℂ) ^ (-(s : ℂ))) = ((-Real.log (1 - z p) : ℝ) : ℂ) := by
    intro p
    rw [hcpow p]
    have h1z : (0 : ℝ) < 1 - z p := by have := hz_lt_one p; linarith
    rw [show (1 : ℂ) - ((z p : ℝ) : ℂ) = (((1 - z p : ℝ)) : ℂ) by push_cast; ring]
    rw [← Complex.ofReal_log h1z.le]
    push_cast; ring
  -- (III) S is real: S = (Sr : ℂ) with Sr the real sum
  set Sr : ℝ := ∑' p : Nat.Primes, -Real.log (1 - z p) with hSr
  have hSeq : S = (Sr : ℂ) := by
    rw [hS, hSr, Complex.ofReal_tsum]
    exact tsum_congr hterm
  have hSim : S.im = 0 := by rw [hSeq]; exact Complex.ofReal_im _
  have hSre : S.re = Sr := by rw [hSeq]; exact Complex.ofReal_re _
  -- (IV) invert exp: log ζ = S
  have hlog_zeta : Complex.log (riemannZeta (s : ℂ)) = S := by
    rw [← hep, Complex.log_exp (by rw [hSim]; exact neg_lt_zero.mpr Real.pi_pos)
      (by rw [hSim]; exact Real.pi_pos.le)]
  -- relate Real.log ζ.re to S.re = Sr
  have hkey : Real.log (riemannZeta (s : ℂ)).re = Sr := by
    have hζim : (riemannZeta (s : ℂ)).im = 0 := riemannZeta_im_eq_zero_of_one_lt hs
    have hζeq : riemannZeta (s : ℂ) = ((riemannZeta (s : ℂ)).re : ℂ) := by
      apply Complex.ext <;> simp [hζim]
    have : Real.log (riemannZeta (s : ℂ)).re
        = (Complex.log (riemannZeta (s : ℂ))).re := by
      conv_rhs => rw [hζeq]
      rw [Complex.log_ofReal_re]
    rw [this, hlog_zeta, hSre]
  rw [hkey]
  -- now goal: Sr = ∑' n, Λ n / (n^s * log n)
  -- (V) expand each prime term via real Taylor series
  have habs : ∀ p : Nat.Primes, |z p| < 1 := by
    intro p
    rw [abs_of_pos (hz_pos p)]; exact hz_lt_one p
  have htaylor : ∀ p : Nat.Primes,
      HasSum (fun n : ℕ => (z p) ^ (n + 1) / (n + 1)) (-Real.log (1 - z p)) :=
    fun p => hasSum_pow_div_log_of_abs_lt_one (habs p)
  have hSr_double : Sr = ∑' (p : Nat.Primes) (n : ℕ), (z p) ^ (n + 1) / (n + 1) := by
    rw [hSr]
    exact tsum_congr fun p => ((htaylor p).tsum_eq).symm
  -- summability of the prime sum ∑ z p
  have hsummable_z : Summable z := Nat.Primes.summable_rpow.mpr (by linarith)
  -- summability of ∑ p, -log(1 - z p)
  have hsummable_prime : Summable (fun p : Nat.Primes => -Real.log (1 - z p)) := by
    have := Real.summable_log_one_add_of_summable hsummable_z.neg
    convert! this.neg using 1
  -- summability of g over the product
  have hg_nonneg : ∀ pk : Nat.Primes × ℕ, 0 ≤ (z pk.1) ^ (pk.2 + 1) / (pk.2 + 1) := by
    intro pk; positivity [hz_pos pk.1]
  have hsummable_g : Summable (fun pk : Nat.Primes × ℕ => (z pk.1) ^ (pk.2 + 1) / (pk.2 + 1)) := by
    rw [summable_prod_of_nonneg hg_nonneg]
    refine ⟨fun p => (htaylor p).summable, ?_⟩
    refine hsummable_prime.congr (fun p => ?_)
    exact ((htaylor p).tsum_eq).symm
  -- pointwise: F (p^(n+1)) = g (p, n)
  have hpoint : ∀ (p : Nat.Primes) (n : ℕ),
      Λ ((p : ℕ) ^ (n + 1)) /
        ((((p : ℕ) ^ (n + 1) : ℕ) : ℝ) ^ s * Real.log (((p : ℕ) ^ (n + 1) : ℕ) : ℝ))
      = (z p) ^ (n + 1) / (n + 1) := by
    intro p n
    have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
    have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hp1
    rw [vonMangoldt_apply_pow (Nat.succ_ne_zero n), vonMangoldt_apply_prime p.prop]
    have hcast : (((p : ℕ) ^ (n + 1) : ℕ) : ℝ) = (p : ℝ) ^ (n + 1) := by push_cast; ring
    rw [hcast, Real.log_pow]
    rw [show (z p) ^ (n + 1) = ((p : ℝ) ^ (n + 1)) ^ (-s) by
      rw [hz]; rw [← Real.rpow_natCast ((p : ℝ) ^ (-s)) (n + 1),
        ← Real.rpow_natCast ((p : ℝ)) (n + 1), ← Real.rpow_mul (by positivity),
        ← Real.rpow_mul (by positivity)]; ring_nf]
    rw [Real.rpow_neg (by positivity)]
    field_simp
    push_cast
    ring
  -- (VI) reindex via the prime-power equivalence
  set F : ℕ → ℝ := fun n => Λ n / ((n : ℝ) ^ s * Real.log n) with hF
  -- support of F is contained in prime powers
  have hsupp : Function.support F ⊆ {n : ℕ | IsPrimePow n} := by
    intro n hn
    rw [Function.mem_support] at hn
    simp only [Set.mem_ofPred_eq]
    by_contra hpp
    apply hn
    simp only [hF, vonMangoldt_eq_zero_iff.mpr hpp, zero_div]
  -- the product sum equals the subtype sum
  have hprod_eq : (∑' pk : Nat.Primes × ℕ, (z pk.1) ^ (pk.2 + 1) / (pk.2 + 1))
      = ∑' m : {n : ℕ // IsPrimePow n}, F m.val := by
    rw [← Equiv.tsum_eq Nat.Primes.prodNatEquiv (fun m : {n : ℕ // IsPrimePow n} => F m.val)]
    apply tsum_congr
    intro pk
    rw [Nat.Primes.coe_prodNatEquiv_apply, hF]
    exact (hpoint pk.1 pk.2).symm
  -- assemble
  rw [hSr_double, ← hsummable_g.tsum_prod' (fun p => (htaylor p).summable), hprod_eq]
  exact tsum_subtype_eq_of_support_subset hsupp

section
open MeasureTheory Set

-- Helpers for `log_zeta_eq_integ` (#1583): Abel summation / sum-integral interchange.
namespace LogZetaInteg

/-- The summatory coefficient `Λ d / (d log d)`. -/
private noncomputable def c (d : ℕ) : ℝ := Λ d / (d * Real.log d)

/-- The per-index integrand: `c d` times the rpow restricted to `Ici (d:ℝ)`. -/
private noncomputable def f (s : ℝ) (d : ℕ) (x : ℝ) : ℝ :=
    c d * (Set.Ici (d:ℝ)).indicator (fun x => x ^ (-s)) x

private lemma c_zero : c 0 = 0 := by simp [c]
private lemma c_one : c 1 = 0 := by simp [c, vonMangoldt_apply_one]

/-- `c d ≥ 0` for all `d`. -/
private lemma c_nonneg (d : ℕ) : 0 ≤ c d := by
  unfold c
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd; simp
  · apply div_nonneg vonMangoldt_nonneg
    have : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg d
    have hlog : 0 ≤ Real.log d := Real.log_natCast_nonneg d
    positivity

/-- General comparison majorant: `(log n)^a / n^s` is summable for any real `a` and `s > 1`,
since `(log x)^a = o(x^ε)` for every `ε > 0`. All the summability conditions below reduce to
this by domination. -/
private lemma summable_log_rpow_div_rpow (a : ℝ) {s : ℝ} (hs : 1 < s) :
    Summable (fun n : ℕ => (Real.log n) ^ a / (n:ℝ) ^ s) := by
  have hε : (0:ℝ) < (s - 1) / 2 := by linarith
  refine summable_of_isBigO_nat (g := fun n : ℕ => (n:ℝ) ^ ((s - 1) / 2 - s)) ?_ ?_
  · rw [Real.summable_nat_rpow]; linarith
  · have ho : (fun x : ℝ => (Real.log x) ^ a) =O[atTop] (fun x : ℝ => x ^ ((s - 1) / 2)) :=
      (isLittleO_log_rpow_rpow_atTop a hε).isBigO
    have hmul : (fun x : ℝ => (Real.log x) ^ a / x ^ s)
        =O[atTop] (fun x : ℝ => x ^ ((s - 1) / 2) / x ^ s) := by
      simpa only [div_eq_mul_inv] using ho.mul (isBigO_refl (fun x : ℝ => (x ^ s)⁻¹) atTop)
    have heq : (fun x : ℝ => x ^ ((s - 1) / 2) / x ^ s)
        =ᶠ[atTop] (fun x : ℝ => x ^ ((s - 1) / 2 - s)) := by
      filter_upwards [eventually_gt_atTop 0] with x hx
      rw [← Real.rpow_sub hx]
    exact (hmul.trans_eventuallyEq heq).natCast_atTop

/-- Real summability of `Λ n / n^s` for `s > 1`: dominated by `log n / n^s` via `Λ n ≤ log n`. -/
private lemma summable_vonMangoldt_div_rpow (s : ℝ) (hs : 1 < s) :
    Summable (fun n : ℕ => (Λ n : ℝ) / (n:ℝ) ^ s) := by
  refine Summable.of_nonneg_of_le (fun n => div_nonneg vonMangoldt_nonneg (by positivity)) ?_
    (summable_log_rpow_div_rpow 1 hs)
  intro n
  rw [Real.rpow_one]
  gcongr
  exact vonMangoldt_le_log

/-- Real summability of `Λ n / (n^s * log n)` for `s > 1` (compare with the previous lemma). -/
private lemma summable_c_term (s : ℝ) (hs : 1 < s) :
    Summable (fun d : ℕ => c d * ((d:ℝ) ^ (1 - s) / (s - 1))) := by
  have hs1 : (0:ℝ) < s - 1 := by linarith
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- Majorise by `(1/(log 2·(s-1)))·(Λ d/d^s)`, summable by `summable_vonMangoldt_div_rpow`.
  refine Summable.of_nonneg_of_le (fun d => ?_) (fun d => ?_)
    ((summable_vonMangoldt_div_rpow s hs).mul_left (1 / (Real.log 2 * (s - 1))))
  · -- `0 ≤ c d * (d^(1-s)/(s-1))`
    refine mul_nonneg (c_nonneg d) (div_nonneg ?_ hs1.le)
    rcases eq_or_ne (d:ℝ) 0 with hd | hd
    · rw [hd, Real.zero_rpow (by linarith : (1 - s) ≠ 0)]
    · positivity
  · -- `c d * (d^(1-s)/(s-1)) ≤ (1/(log 2·(s-1)))·(Λ d/d^s)`
    rcases lt_or_ge d 2 with hd | hd
    · have hc : c d = 0 := by interval_cases d <;> simp [c_zero, c_one]
      rw [hc, zero_mul]
      exact mul_nonneg (by positivity) (div_nonneg vonMangoldt_nonneg (by positivity))
    · have hd2 : (2:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
      have hd0 : (0:ℝ) < (d:ℝ) := by linarith
      have hlogge : Real.log 2 ≤ Real.log d := Real.log_le_log (by norm_num) hd2
      have hds : (0:ℝ) < (d:ℝ) ^ s := Real.rpow_pos_of_pos hd0 s
      have hkey : c d * ((d:ℝ) ^ (1 - s) / (s - 1)) = Λ d / ((d:ℝ) ^ s * Real.log d * (s - 1)) := by
        unfold c
        rw [show (1 - s : ℝ) = -s + 1 by ring, Real.rpow_add hd0, Real.rpow_one, Real.rpow_neg hd0.le]
        field_simp
      -- `Λ d / (d^s·log d·(s-1)) ≤ Λ d / (d^s·log 2·(s-1))` since `log 2 ≤ log d`.
      have hcb : (d:ℝ) ^ s * Real.log 2 * (s - 1) ≤ (d:ℝ) ^ s * Real.log d * (s - 1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlogge hds.le) hs1.le
      rw [hkey, show (1 / (Real.log 2 * (s - 1))) * ((Λ d : ℝ) / (d:ℝ) ^ s)
          = Λ d / ((d:ℝ) ^ s * Real.log 2 * (s - 1)) from by field_simp]
      exact div_le_div_of_nonneg_left vonMangoldt_nonneg (by positivity) hcb

/-- The integration-by-parts identity (#1583), with explicit qualifiers. -/
theorem log_zeta_eq_integ_aux (s : ℝ) (hs : 1 < s) :
    Real.log (riemannZeta (s:ℂ)).re =
      (s - 1) * ∫ x in Set.Ioi 1, (Real.log (Real.log x) + γ + E₂Λ x) * x ^ (-s) := by
  rw [Mertens.log_zeta_eq_sum s hs]
  symm
  have hstep1 : ∀ x ∈ Set.Ioi (1:ℝ),
      (Real.log (Real.log x) + γ + E₂Λ x) * x ^ (-s)
        = (∑ d ∈ Finset.Ioc 0 ⌊x⌋₊, c d) * x ^ (-s) := by
    intro x hx
    simp only [Mertens.E₂Λ, c]
    ring
  have hstep2 : ∀ x ∈ Set.Ioi (1:ℝ),
      (Real.log (Real.log x) + γ + E₂Λ x) * x ^ (-s) = ∑' d : ℕ, f s d x := by
    intro x hx
    rw [hstep1 x hx]
    simp only [f]
    rw [Finset.sum_mul]
    have hx0 : (0:ℝ) ≤ x := by have := hx; simp only [Set.mem_Ioi] at this; linarith
    rw [tsum_eq_sum (s := Finset.Ioc 0 ⌊x⌋₊) ?_]
    · apply Finset.sum_congr rfl
      intro d hd
      simp only [Finset.mem_Ioc] at hd
      have hdx : (d:ℝ) ≤ x := by
        rw [← Nat.le_floor_iff hx0]; exact hd.2
      rw [Set.indicator_of_mem (by simpa using hdx)]
    · intro d hd
      simp only [Finset.mem_Ioc, not_and, not_le] at hd
      rcases Nat.eq_zero_or_pos d with hd0 | hd0
      · subst hd0; simp [c_zero]
      · have hfloor : ⌊x⌋₊ < d := hd hd0
        have hdx : x < (d:ℝ) := by
          rw [← Nat.floor_lt hx0]; exact hfloor
        rw [Set.indicator_of_notMem (by simpa using not_le.mpr hdx)]
        ring
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hstep2]
  have hperterm : ∀ d : ℕ, ∫ x in Set.Ioi (1:ℝ), f s d x = c d * ((d:ℝ) ^ (1 - s) / (s - 1)) := by
    intro d
    rcases Nat.eq_zero_or_pos d with hd0 | hd0
    · subst hd0; simp [f, c_zero]
    simp only [f]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.setIntegral_indicator measurableSet_Ici]
    congr 1
    have hdR : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd0
    have hdR0 : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd0
    set A : Set ℝ := Set.Ioi (1:ℝ) ∩ Set.Ici (d:ℝ) with hA
    have hae : A =ᵐ[volume] Set.Ioi (d:ℝ) := by
      have h1 : A =ᵐ[volume] (Set.Ici (1:ℝ) ∩ Set.Ici (d:ℝ) : Set ℝ) :=
        MeasureTheory.ae_eq_set_inter MeasureTheory.Ioi_ae_eq_Ici (ae_eq_refl _)
      rw [Set.Ici_inter_Ici, max_eq_right hdR] at h1
      exact h1.trans MeasureTheory.Ioi_ae_eq_Ici.symm
    rw [MeasureTheory.setIntegral_congr_set hae]
    rw [integral_Ioi_rpow_of_lt (by linarith : (-s:ℝ) < -1) hdR0,
      show (-s + 1 : ℝ) = 1 - s by ring]
    have hs1 : (1 - s) ≠ 0 := by linarith
    have hs2 : (s - 1) ≠ 0 := by linarith
    field_simp
    ring
  have hint : ∀ d : ℕ, MeasureTheory.IntegrableOn (f s d) (Set.Ioi (1:ℝ)) := by
    intro d
    unfold f
    apply MeasureTheory.Integrable.const_mul
    rw [show MeasureTheory.Integrable ((Set.Ici (d:ℝ)).indicator fun x => x ^ (-s))
        (volume.restrict (Set.Ioi (1:ℝ)))
      ↔ MeasureTheory.IntegrableOn ((Set.Ici (d:ℝ)).indicator fun x => x ^ (-s))
          (Set.Ioi (1:ℝ)) volume from Iff.rfl,
      MeasureTheory.integrableOn_indicator_iff measurableSet_Ici]
    apply MeasureTheory.IntegrableOn.mono_set
      (integrableOn_Ioi_rpow_of_lt (by linarith : (-s:ℝ) < -1) (by norm_num : (0:ℝ) < 1/2))
    intro x hx
    simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ioi] at hx ⊢
    linarith [hx.2]
  have hnorm_int : ∀ d : ℕ,
      ∫ x in Set.Ioi (1:ℝ), ‖f s d x‖ = c d * ((d:ℝ) ^ (1 - s) / (s - 1)) := by
    intro d
    rw [← hperterm d]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    simp only [Set.mem_Ioi] at hx
    have hfnn : 0 ≤ f s d x := by
      simp only [f]
      apply mul_nonneg (c_nonneg d)
      by_cases hxd : (d:ℝ) ≤ x
      · rw [Set.indicator_of_mem (by simpa using hxd)]
        exact le_of_lt (Real.rpow_pos_of_pos (by linarith) _)
      · rw [Set.indicator_of_notMem (by simpa using hxd)]
    change ‖f s d x‖ = f s d x
    rw [Real.norm_eq_abs, abs_of_nonneg hfnn]
  have hinterchange : ∫ x in Set.Ioi (1:ℝ), ∑' d : ℕ, f s d x
      = ∑' d : ℕ, ∫ x in Set.Ioi (1:ℝ), f s d x := by
    refine (MeasureTheory.integral_tsum_of_summable_integral_norm hint ?_).symm
    apply (summable_c_term s hs).congr
    intro d
    exact (hnorm_int d).symm
  rw [hinterchange]
  simp_rw [hperterm]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro d
  rcases Nat.eq_zero_or_pos d with hd0 | hd0
  · subst hd0; simp [c_zero]
  · have hdR : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd0
    have hsub : (d:ℝ) ^ (1 - s) = (d:ℝ) ^ (-s) * (d:ℝ) := by
      rw [show (1 - s : ℝ) = -s + 1 by ring, Real.rpow_add hdR, Real.rpow_one]
    have hs1 : s - 1 ≠ 0 := by linarith
    have hneg : (d:ℝ) ^ (-s) = ((d:ℝ) ^ s)⁻¹ := by
      rw [Real.rpow_neg (le_of_lt hdR)]
    unfold c
    rw [hsub, hneg]
    field_simp

end LogZetaInteg
end

private theorem log_zeta_eq_integ (s : ℝ) (hs : 1 < s) :
    log (riemannZeta (s:ℂ)).re = (s - 1) * ∫ x in .Ioi 1, (log (log x) + γ + E₂Λ x) * x^(-s) :=
  LogZetaInteg.log_zeta_eq_integ_aux s hs

private theorem mul_integ_log_log_eq (s : ℝ) (hs : 1 < s) :
    (s - 1) * ∫ x in .Ioi 1, log (log x) * x^(-s) = - log (s - 1) + deriv Gamma 1 :=
  mul_integ_log_log_eq_aux s hs

private theorem mul_integ_gamma_eq (s) (hs : 1 < s) : (s - 1) * ∫ x in .Ioi 1, γ * x^(-s) = γ := by
  rw [MeasureTheory.integral_const_mul γ (· ^ (-s)), @integral_Ioi_rpow_of_lt (-s), one_rpow] <;>
    grind

-- Integrability helpers for the integral splitting in `log_zeta_eq` (#1319).
-- Each summand of `(log (log x) + γ + E₂Λ x) * x^(-s)` is separately integrable on `Ioi 1`.

/-- Comparison test for `x ^ (-s)` decay: if `f` is measurable and dominated by `B * x ^ a` on
`Set.Ioi c` (with `0 < c` and `a + 1 < s`), then `fun x ↦ f x * x ^ (-s)` is integrable there.
This is the integral analogue of the summability of `O(x ^ a / x ^ s)` series and packages the
decay estimate reused for each tail in `log_zeta_eq`. -/
private theorem integrableOn_Ioi_mul_rpow_neg_of_abs_le
    {c B a s : ℝ} (hc : 0 < c) (has : a + 1 < s) {f : ℝ → ℝ} (hf : Measurable f)
    (hbound : ∀ x ∈ Set.Ioi c, |f x| ≤ B * x ^ a) :
    MeasureTheory.IntegrableOn (fun x => f x * x ^ (-s)) (Set.Ioi c) := by
  have hg : MeasureTheory.IntegrableOn (fun x => B * x ^ (a - s)) (Set.Ioi c) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : a - s < -1) hc).const_mul B
  refine MeasureTheory.Integrable.mono' hg
    (hf.mul (measurable_id.pow_const (-s))).aestronglyMeasurable ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
  have hxpos : (0:ℝ) < x := hc.trans hx
  have hxs : (0:ℝ) < x ^ (-s) := Real.rpow_pos_of_pos hxpos _
  rw [norm_mul, norm_eq_abs, norm_eq_abs, abs_of_pos hxs]
  calc |f x| * x ^ (-s) ≤ B * x ^ a * x ^ (-s) :=
        mul_le_mul_of_nonneg_right (hbound x hx) hxs.le
    _ = B * x ^ (a - s) := by rw [mul_assoc, ← Real.rpow_add hxpos, sub_eq_add_neg]

/-- `log (log x) * x ^ (-s)` is integrable on `Ioi 1` for `s > 1`
(log-log singularity at `1` is integrable; `x^(-s)` gives decay). -/
private theorem integrableOn_log_log_mul_rpow (s : ℝ) (hs : 1 < s) :
    MeasureTheory.IntegrableOn (fun x => log (log x) * x ^ (-s)) (Set.Ioi 1) := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (1:ℝ) ≤ 2)]
  apply MeasureTheory.IntegrableOn.union
  · -- Near `1`: `log (log x)` is integrable (log-log singularity) and `x^(-s) ≤ 1`.
    have hll : MeasureTheory.IntegrableOn (fun x => log (log x)) (Set.Ioc 1 2) := by
      have h : IntervalIntegrable (log ∘ log) MeasureTheory.volume 1 2 := by
        apply MeromorphicOn.intervalIntegrable_log
        intro x hx
        rw [Set.uIcc_of_le (by norm_num : (1:ℝ) ≤ 2)] at hx
        exact (analyticAt_log (by linarith [hx.1] : 0 < x)).meromorphicAt
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp h
    have hmul : MeasureTheory.IntegrableOn (fun x => x ^ (-s) * log (log x)) (Set.Ioc 1 2) := by
      apply hll.bdd_mul (c := 1)
      · fun_prop
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
        rw [norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith [hx.1] : (0:ℝ) ≤ x) _)]
        calc x ^ (-s) ≤ (1:ℝ) ^ (-s) :=
              Real.rpow_le_rpow_of_nonpos (by norm_num) hx.1.le (by linarith)
          _ = 1 := Real.one_rpow _
    simpa [mul_comm] using hmul
  · -- Tail (`Ioi 2`): `|log (log x)| ≤ (1/ε + |log (log 2)|)·x^ε` with `ε = (s-1)/2`, `ε + 1 < s`.
    set ε := (s - 1) / 2 with hε
    have hεpos : 0 < ε := by rw [hε]; linarith
    refine integrableOn_Ioi_mul_rpow_neg_of_abs_le (a := ε) (B := 1 / ε + |log (log 2)|)
      (by norm_num) (by rw [hε]; linarith) (Real.measurable_log.comp Real.measurable_log) ?_
    intro x hx
    simp only [Set.mem_Ioi] at hx
    have hx1 : (1:ℝ) ≤ x ^ ε := Real.one_le_rpow (by linarith) hεpos.le
    have hlogx : 0 < log x := Real.log_pos (by linarith)
    have hlog2 : 0 < log 2 := Real.log_pos (by norm_num)
    have hmono : log 2 ≤ log x := Real.log_le_log (by norm_num) (by linarith)
    have hub : log (log x) ≤ x ^ ε / ε :=
      calc log (log x) ≤ log x := (Real.log_le_sub_one_of_pos hlogx).trans (by linarith)
        _ ≤ x ^ ε / ε := Real.log_le_rpow_div (by linarith) hεpos
    have hlb : log (log 2) ≤ log (log x) := Real.log_le_log hlog2 hmono
    have hxε : 0 ≤ x ^ ε / ε := by positivity
    calc |log (log x)| ≤ x ^ ε / ε + |log (log 2)| := by
          rw [abs_le]
          exact ⟨by linarith [neg_abs_le (log (log 2))],
            by linarith [abs_nonneg (log (log 2))]⟩
      _ ≤ (1 / ε + |log (log 2)|) * x ^ ε := by
          have h2 : |log (log 2)| ≤ |log (log 2)| * x ^ ε := le_mul_of_one_le_right (abs_nonneg _) hx1
          have h1 : x ^ ε / ε = 1 / ε * x ^ ε := by ring
          rw [add_mul]; linarith

/-- `γ * x ^ (-s)` is integrable on `Ioi 1` for `s > 1`. -/
private theorem integrableOn_γ_mul_rpow (s : ℝ) (hs : 1 < s) :
    MeasureTheory.IntegrableOn (fun x => γ * x ^ (-s)) (Set.Ioi 1) := by
  exact (integrableOn_Ioi_rpow_of_lt (by linarith : -s < -1) one_pos).const_mul γ

/-- `E₂Λ x * x ^ (-s)` is integrable on `Ioi 1` for `s > 1`
(`E₂Λ ~ -log(log x)` near `1`, and `E₂Λ = O(1/log x)` at `∞`). -/
private theorem integrableOn_E₂Λ_mul_rpow (s : ℝ) (hs : 1 < s) :
    MeasureTheory.IntegrableOn (fun x => E₂Λ x * x ^ (-s)) (Set.Ioi 1) := by
  rw [← Set.Ioo_union_Ici_eq_Ioi (by norm_num : (1:ℝ) < 2)]
  apply MeasureTheory.IntegrableOn.union
  · -- Near `1`: `⌊x⌋₊ = 1`, the sum is `0`, so `E₂Λ x = -log (log x) - γ`.
    have hsub : Set.Ioo (1:ℝ) 2 ⊆ Set.Ioi 1 := fun x hx => hx.1
    have h1 := (integrableOn_γ_mul_rpow s hs).mono_set hsub
    have h2 := (integrableOn_log_log_mul_rpow s hs).mono_set hsub
    have hb : MeasureTheory.IntegrableOn
        (fun x => -(log (log x) * x ^ (-s)) - γ * x ^ (-s)) (Set.Ioo 1 2) :=
      h2.neg.sub h1
    apply hb.congr_fun _ measurableSet_Ioo
    intro x hx
    simp only [Set.mem_Ioo] at hx
    have hfloor : ⌊ x ⌋₊ = 1 := by
      rw [Nat.floor_eq_iff (by linarith)]
      exact ⟨by push_cast; linarith [hx.1], by push_cast; linarith [hx.2]⟩
    have hsum : (∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / ((d:ℝ) * log d)) = 0 := by rw [hfloor]; norm_num
    change -(log (log x) * x ^ (-s)) - γ * x ^ (-s)
        = (∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / (d * log d) - log (log x) - γ) * x ^ (-s)
    rw [hsum]; ring
  · -- Tail: `|E₂Λ x| ≤ (log 4 + 6)/log x ≤ (log 4 + 6)/log 2` is bounded (`a = 0`), times decay.
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    refine integrableOn_Ioi_mul_rpow_neg_of_abs_le (a := 0) (B := (log 4 + 6) / log 2)
      (by norm_num) (by linarith) (by fun_prop) ?_
    intro x hx
    simp only [Set.mem_Ioi] at hx
    have hlog2 : 0 < log 2 := Real.log_pos (by norm_num)
    have hc : 0 ≤ log 4 + 6 := by positivity
    rw [Real.rpow_zero, mul_one]
    have hb2 : (log 4 + 6) / log x ≤ (log 4 + 6) / log 2 :=
      div_le_div_of_nonneg_left hc hlog2 (Real.log_le_log (by norm_num) (le_of_lt hx))
    exact (E₂Λ.abs_le (le_of_lt hx)).trans hb2

private theorem log_zeta_eq (s : ℝ) (hs : 1 < s) :
    log (riemannZeta (s:ℂ)).re = - log (s - 1) + deriv Gamma 1 + γ + (s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x^(-s) := by
  -- Start from the integration-by-parts identity (#1583).
  rw [log_zeta_eq_integ s hs]
  -- Linearity of the integral: split into the three summands (uses the integrability helpers).
  have key : (∫ x in Set.Ioi 1, (log (log x) + γ + E₂Λ x) * x ^ (-s))
      = (∫ x in Set.Ioi 1, log (log x) * x ^ (-s))
        + (∫ x in Set.Ioi 1, γ * x ^ (-s))
        + (∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s)) := by
    rw [← MeasureTheory.integral_add (integrableOn_log_log_mul_rpow s hs)
      (integrableOn_γ_mul_rpow s hs)]
    rw [← MeasureTheory.integral_add (f := fun x => log (log x) * x ^ (-s) + γ * x ^ (-s))
      (g := fun x => E₂Λ x * x ^ (-s))
      ((integrableOn_log_log_mul_rpow s hs).add (integrableOn_γ_mul_rpow s hs))
      (integrableOn_E₂Λ_mul_rpow s hs)]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x _
    ring
  -- Apply sublemmas #1584 and #1585, then finish algebraically.
  rw [key, mul_add, mul_add, mul_integ_log_log_eq s hs, mul_integ_gamma_eq s hs]

private lemma zeta_pole_mul_re_tendsto_one :
    Filter.Tendsto (fun s : ℝ => (s - 1) * (riemannZeta (s : ℂ)).re)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) := by
  have hofReal :
      Filter.Tendsto (fun s : ℝ => (s : ℂ)) (nhdsWithin 1 (Set.Ioi 1))
        (nhdsWithin (1 : ℂ) ({1} : Set ℂ)ᶜ) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact (Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact Set.mem_compl_singleton_iff.mpr (by
        norm_num
        exact ne_of_gt (Set.mem_Ioi.mp hs))
  have hcomplex :
      Filter.Tendsto (fun s : ℝ => ((s : ℂ) - 1) * riemannZeta (s : ℂ))
        (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) :=
    riemannZeta_residue_one.comp hofReal
  have hreal :
      Filter.Tendsto
        (fun s : ℝ => (((s : ℂ) - 1) * riemannZeta (s : ℂ)).re)
        (nhdsWithin 1 (Set.Ioi 1)) (nhds (1 : ℝ)) :=
    (Complex.continuous_re.tendsto (1 : ℂ)).comp hcomplex
  simpa [Complex.ofReal_sub, Complex.ofReal_mul] using hreal

private theorem log_zeta_limit :
    Filter.Tendsto
      (fun s : ℝ => Real.log (riemannZeta (s : ℂ)).re + Real.log (s - 1))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := by
  have hlog :
      Filter.Tendsto
        (fun s : ℝ => Real.log ((s - 1) * (riemannZeta (s : ℂ)).re))
        (nhdsWithin 1 (Set.Ioi 1)) (nhds (Real.log 1)) :=
    (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp
      zeta_pole_mul_re_tendsto_one
  have hEq :
      (fun s : ℝ => Real.log (riemannZeta (s : ℂ)).re + Real.log (s - 1))
        =ᶠ[nhdsWithin 1 (Set.Ioi 1)]
      fun s : ℝ => Real.log ((s - 1) * (riemannZeta (s : ℂ)).re) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hspos : 0 < s - 1 := sub_pos.mpr (Set.mem_Ioi.mp hs)
    have hzpos : 0 < (riemannZeta (s : ℂ)).re :=
      riemannZeta_re_pos_of_one_lt (Set.mem_Ioi.mp hs)
    rw [Real.log_mul hspos.ne' hzpos.ne']
    ring
  simpa using hlog.congr' (hEq.mono fun s hs => hs.symm)

-- Helpers for `deriv_gamma_add_γ_eq_zero` (#1320): take `s → 1⁺` in `log_zeta_eq`.
section
open MeasureTheory Set

/-- `E₂Λ` is measurable: its Mangoldt-sum part factors through `⌊·⌋₊` and the rest is
continuous/measurable. -/
private lemma measurable_E₂Λ : Measurable E₂Λ := by fun_prop

/-- On `(1,2)` the Mangoldt sum is empty (`⌊x⌋₊ = 1`), so `E₂Λ x = - log (log x) - γ`. -/
private lemma E₂Λ_eq_on_Ioo {x : ℝ} (hx : x ∈ Set.Ioo (1 : ℝ) 2) :
    E₂Λ x = - log (log x) - γ := by
  obtain ⟨h1, h2⟩ := hx
  have hf : ⌊x⌋₊ = 1 := by
    rw [Nat.floor_eq_iff (by linarith)]
    exact ⟨by exact_mod_cast h1.le, by exact_mod_cast h2⟩
  unfold E₂Λ
  rw [hf]
  simp

/-- Domination of `|E₂Λ|` near `1`: for `x ∈ (1,2)`, `|E₂Λ x| ≤ |log (x-1)| + log 2 + |γ|`,
the RHS being integrable on `(1,2)` (the `log (x-1)` is integrable across the singularity at `1`). -/
private lemma abs_E₂Λ_le_on_Ioo {x : ℝ} (hx : x ∈ Set.Ioo (1 : ℝ) 2) :
    |E₂Λ x| ≤ |log (x - 1)| + log 2 + |γ| := by
  obtain ⟨hx1, hx2⟩ := hx
  have hloglog : |log (log x)| ≤ |log (x - 1)| + log 2 := by
    have hxpos : (0:ℝ) < x := by linarith
    have hlogx_pos : 0 < log x := Real.log_pos hx1
    have hxm1 : 0 < x - 1 := by linarith
    have hub : log x ≤ x - 1 := by have := Real.log_le_sub_one_of_pos hxpos; linarith
    have hlb2 : (x - 1) / 2 ≤ log x := by
      have h := Real.log_le_sub_one_of_pos (x := 1 / x) (by positivity)
      rw [Real.log_div one_ne_zero (by positivity), Real.log_one] at h
      simp only [zero_sub] at h
      have h12 : (x - 1) / 2 ≤ 1 - 1 / x := by
        rw [← sub_nonneg]
        have e : (1 - 1 / x) - (x - 1) / 2 = (3 * x - 2 - x ^ 2) / (2 * x) := by field_simp; ring
        rw [e]; exact div_nonneg (by nlinarith [hx1, hx2]) (by positivity)
      linarith
    have hupper : log (log x) ≤ log (x - 1) := Real.log_le_log hlogx_pos hub
    have hlower : log (x - 1) - log 2 ≤ log (log x) := by
      have := Real.log_le_log (show (0:ℝ) < (x - 1) / 2 by positivity) hlb2
      rwa [Real.log_div (by linarith) (by norm_num)] at this
    have h2 : (0:ℝ) ≤ log 2 := Real.log_nonneg (by norm_num)
    rw [abs_le]
    exact ⟨by have := neg_abs_le (log (x - 1)); linarith,
          by have := le_abs_self (log (x - 1)); linarith⟩
  rw [E₂Λ_eq_on_Ioo ⟨hx1, hx2⟩]
  have htri : |(- log (log x) - γ)| ≤ |log (log x)| + |γ| := by
    have h := abs_sub (-log (log x)) γ
    rwa [abs_neg] at h
  linarith

/-- Constant bound on `|E₂Λ|` for `2 ≤ x`, sharpening `E₂Λ.abs_le` via `log 2 ≤ log x`. -/
private lemma abs_E₂Λ_le_const {x : ℝ} (hx : 2 ≤ x) :
    |E₂Λ x| ≤ (log 4 + 6) / log 2 :=
  (E₂Λ.abs_le hx).trans <| div_le_div_of_nonneg_left (by positivity)
    (Real.log_pos (by norm_num)) (Real.log_le_log (by norm_num) hx)

/-- The near-1 dominating function `|log (x-1)| + log 2 + |γ|` is integrable on `(1,2)`
(it dominates `|E₂Λ|` there, handling the log-log singularity at `1`). -/
private lemma integrableOn_log_sub_one_bound :
    IntegrableOn (fun x => |log (x - 1)| + log 2 + |γ|) (Set.Ioo 1 2) volume := by
  have hlog : IntegrableOn (fun x => |log (x - 1)|) (Set.Ioo 1 2) volume := by
    have h0 : IntervalIntegrable (fun x => log x) volume 0 1 :=
      intervalIntegral.intervalIntegrable_log'
    have h1 : IntervalIntegrable (fun x => log (x - 1)) volume (0 + 1) (1 + 1) :=
      h0.comp_sub_right 1
    norm_num at h1
    exact (h1.1.mono_set Set.Ioo_subset_Ioc_self).abs
  have hc : IntegrableOn (fun _ : ℝ => log 2 + |γ|) (Set.Ioo (1 : ℝ) 2) volume :=
    integrableOn_const (measure_Ioo_lt_top).ne (by finiteness)
  have hsum : IntegrableOn (fun x => |log (x - 1)| + (log 2 + |γ|)) (Set.Ioo 1 2) volume :=
    hlog.add hc
  exact hsum.congr_fun (fun x _ => by ring) measurableSet_Ioo

/-- `E₂Λ` is integrable on every bounded interval `(1, X)` (`X ≥ 2`): log-log singularity near
`1` plus boundedness on `[2, X]`. -/
private lemma integrableOn_E₂Λ_Ioo {X : ℝ} (_hX : 2 ≤ X) :
    IntegrableOn E₂Λ (Set.Ioo 1 X) volume := by
  have hsub : Set.Ioo (1 : ℝ) X ⊆ Set.Ioo 1 2 ∪ Set.Icc 2 X := by
    intro x hx; simp only [Set.mem_Ioo, Set.mem_union, Set.mem_Icc] at *
    rcases lt_or_ge x 2 with h | h
    · exact Or.inl ⟨hx.1, h⟩
    · exact Or.inr ⟨h, hx.2.le⟩
  apply IntegrableOn.mono_set _ hsub
  apply IntegrableOn.union
  · have hg := integrableOn_log_sub_one_bound
    refine Integrable.mono' hg measurable_E₂Λ.aestronglyMeasurable ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with x hx
    rw [Real.norm_eq_abs]; exact abs_E₂Λ_le_on_Ioo hx
  · refine Integrable.mono' (g := fun _ => (log 4 + 6) / log 2) ?_
      measurable_E₂Λ.aestronglyMeasurable ?_
    · exact integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (by finiteness)
    · filter_upwards [self_mem_ae_restrict measurableSet_Icc] with x hx
      rw [Real.norm_eq_abs]; exact abs_E₂Λ_le_const hx.1

/-- The error integral, scaled by `(s-1)`, vanishes as `s → 1⁺` (uses `E₂Λ =o(1)`). -/
private lemma sub_one_mul_integral_E₂Λ_tendsto :
    Filter.Tendsto (fun s : ℝ => (s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  -- Choose `X ≥ 2` so that `|E₂Λ x| ≤ ε/2` for `x ≥ X` (from `E₂Λ =o(1)`).
  obtain ⟨X₀, hX₀⟩ : ∃ X, ∀ x ≥ X, |E₂Λ x| ≤ ε / 2 := by
    have := E₂Λ.bound'.def (by positivity : (0:ℝ) < ε / 2)
    simp only [Real.norm_eq_abs, abs_one, mul_one] at this
    rw [Filter.eventually_atTop] at this; exact this
  set X := max X₀ 2 with hXdef
  have hX2 : 2 ≤ X := le_max_right _ _
  have hXge : ∀ x ≥ X, |E₂Λ x| ≤ ε / 2 := fun x hx => hX₀ x (le_trans (le_max_left _ _) hx)
  -- `B` is the (finite) mass of `|E₂Λ|` on `(1, X)`.
  set B := ∫ x in Set.Ioo 1 X, |E₂Λ x| with hBdef
  have hB0 : 0 ≤ B := setIntegral_nonneg measurableSet_Ioo (fun x _ => abs_nonneg _)
  refine ⟨min 1 (ε / 2 / (B + 1)), by positivity, ?_⟩
  intro s hs hdist
  simp only [Set.mem_Ioi] at hs
  rw [Real.dist_eq] at hdist
  have hs1 : s - 1 < min 1 (ε / 2 / (B + 1)) := by
    rw [abs_of_pos (by linarith)] at hdist; exact hdist
  have hsm1 : 0 < s - 1 := by linarith
  -- `|E₂Λ|·x^(-s)` is integrable on `(1,∞)` and its subintervals.
  have hintAbs : IntegrableOn (fun x => |E₂Λ x| * x ^ (-s)) (Set.Ioi 1) volume := by
    have h2 : IntegrableOn (fun x => |E₂Λ x * x ^ (-s)|) (Set.Ioi 1) volume :=
      (integrableOn_E₂Λ_mul_rpow s hs).abs
    refine h2.congr_fun ?_ measurableSet_Ioi
    intro x hx; simp only [Set.mem_Ioi] at hx
    change |E₂Λ x * x ^ (-s)| = |E₂Λ x| * x ^ (-s)
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
  have hintAbsIoc : IntegrableOn (fun x => |E₂Λ x| * x ^ (-s)) (Set.Ioc 1 X) volume :=
    hintAbs.mono_set Set.Ioc_subset_Ioi_self
  have hintAbsIoiX : IntegrableOn (fun x => |E₂Λ x| * x ^ (-s)) (Set.Ioi X) volume :=
    hintAbs.mono_set (Set.Ioi_subset_Ioi (by linarith))
  -- Split `∫_{(1,∞)} = ∫_{(1,X]} + ∫_{(X,∞)}`.
  have hsplit : ∫ x in Set.Ioi 1, |E₂Λ x| * x ^ (-s) =
      (∫ x in Set.Ioc 1 X, |E₂Λ x| * x ^ (-s)) + ∫ x in Set.Ioi X, |E₂Λ x| * x ^ (-s) := by
    have hu : Set.Ioi (1:ℝ) = Set.Ioc 1 X ∪ Set.Ioi X :=
      (Set.Ioc_union_Ioi_eq_Ioi (by linarith)).symm
    rw [hu, setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hintAbs.mono_set (by rw [hu]; exact Set.subset_union_left))
      (hintAbs.mono_set (by rw [hu]; exact Set.subset_union_right))]
  -- Piece 1: on `(1,X]`, `x^(-s) ≤ 1`, so the integral is `≤ B`.
  have hp1 : ∫ x in Set.Ioc 1 X, |E₂Λ x| * x ^ (-s) ≤ B := by
    rw [hBdef]
    have ha : IntegrableOn (fun x => |E₂Λ x|) (Set.Ioo 1 X) volume := (integrableOn_E₂Λ_Ioo hX2).abs
    have habsIoc : IntegrableOn (fun x => |E₂Λ x|) (Set.Ioc 1 X) volume :=
      ha.congr_set_ae (Ioo_ae_eq_Ioc).symm
    rw [← integral_Ioc_eq_integral_Ioo]
    apply setIntegral_mono_on hintAbsIoc habsIoc measurableSet_Ioc
    intro x hx
    have hx1 : (1:ℝ) ≤ x := by have := hx.1; linarith
    have hle1 : x ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
    calc |E₂Λ x| * x ^ (-s) ≤ |E₂Λ x| * 1 := by gcongr
      _ = |E₂Λ x| := mul_one _
  -- Piece 2: on `(X,∞)`, `|E₂Λ| ≤ ε/2`, and `∫_{(X,∞)} x^(-s) = X^(1-s)/(s-1)`.
  have hp2 : ∫ x in Set.Ioi X, |E₂Λ x| * x ^ (-s) ≤ (ε / 2) * (X ^ (1 - s) / (s - 1)) := by
    have hrpow_int : IntegrableOn (fun x : ℝ => x ^ (-s)) (Set.Ioi X) volume :=
      integrableOn_Ioi_rpow_of_lt (by linarith) (by linarith : (0:ℝ) < X)
    have hval : ∫ x in Set.Ioi X, x ^ (-s) = X ^ (1 - s) / (s - 1) := by
      rw [integral_Ioi_rpow_of_lt (by linarith) (by linarith : (0:ℝ) < X),
        show -s + 1 = 1 - s by ring, show (1:ℝ) - s = -(s - 1) by ring]
      rw [div_neg, neg_div, neg_neg]
    rw [← hval, ← integral_const_mul]
    apply setIntegral_mono_on hintAbsIoiX (hrpow_int.const_mul (ε / 2)) measurableSet_Ioi
    intro x hx
    have hxpos : (0:ℝ) < x := by simp only [Set.mem_Ioi] at hx; linarith
    have hnn : 0 ≤ x ^ (-s) := Real.rpow_nonneg hxpos.le _
    have hb : |E₂Λ x| ≤ ε / 2 := hXge x (by simp only [Set.mem_Ioi] at hx; linarith)
    gcongr
  have hXpow : X ^ (1 - s) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  -- Assemble: `(s-1)·∫|E₂Λ|·x^(-s) ≤ (s-1)·B + ε/2`.
  have hbound : (s - 1) * ∫ x in Set.Ioi 1, |E₂Λ x| * x ^ (-s) ≤ (s - 1) * B + ε / 2 := by
    rw [hsplit, mul_add]
    have ht2 : (s - 1) * ∫ x in Set.Ioi X, |E₂Λ x| * x ^ (-s) ≤ ε / 2 := by
      calc (s - 1) * ∫ x in Set.Ioi X, |E₂Λ x| * x ^ (-s)
          ≤ (s - 1) * ((ε / 2) * (X ^ (1 - s) / (s - 1))) :=
            mul_le_mul_of_nonneg_left hp2 hsm1.le
        _ = (ε / 2) * X ^ (1 - s) := by
              have hne : s - 1 ≠ 0 := by linarith
              field_simp
        _ ≤ (ε / 2) * 1 := by gcongr
        _ = ε / 2 := mul_one _
    have ht1 : (s - 1) * ∫ x in Set.Ioc 1 X, |E₂Λ x| * x ^ (-s) ≤ (s - 1) * B :=
      mul_le_mul_of_nonneg_left hp1 hsm1.le
    linarith
  -- `|(s-1)·∫ E₂Λ·x^(-s)| ≤ (s-1)·∫|E₂Λ|·x^(-s)`.
  have habs_le : |(s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s)|
      ≤ (s - 1) * ∫ x in Set.Ioi 1, |E₂Λ x| * x ^ (-s) := by
    rw [abs_mul, abs_of_pos hsm1]
    gcongr
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans_eq ?_
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    simp only [Set.mem_Ioi] at hx
    change ‖E₂Λ x * x ^ (-s)‖ = |E₂Λ x| * x ^ (-s)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
  rw [Real.dist_eq, sub_zero]
  -- `(s-1)·B + ε/2 < ε` since `s - 1 < ε/2/(B+1)`.
  have hfin : (s - 1) * B + ε / 2 < ε := by
    have hlt : s - 1 < ε / 2 / (B + 1) := lt_of_lt_of_le hs1 (min_le_right _ _)
    have hBp : 0 < B + 1 := by linarith
    have h1 : (s - 1) * B ≤ (s - 1) * (B + 1) := by nlinarith
    have h2 : (s - 1) * (B + 1) < (ε / 2 / (B + 1)) * (B + 1) := mul_lt_mul_of_pos_right hlt hBp
    have h3 : (ε / 2 / (B + 1)) * (B + 1) = ε / 2 := by field_simp
    linarith
  calc |(s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s)|
      ≤ (s - 1) * ∫ x in Set.Ioi 1, |E₂Λ x| * x ^ (-s) := habs_le
    _ ≤ (s - 1) * B + ε / 2 := hbound
    _ < ε := hfin

end

theorem deriv_gamma_add_γ_eq_zero : deriv Gamma 1 + γ = 0 := by
  -- For `s > 1`, `log_zeta_eq` rearranges to a constant identity.
  have key : ∀ s : ℝ, 1 < s →
      (Real.log (riemannZeta (s:ℂ)).re + Real.log (s - 1))
        - (s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s) = deriv Gamma 1 + γ := by
    intro s hs
    have h := log_zeta_eq s hs
    linarith
  -- The LHS is eventually constant, so its limit is that constant.
  have hconst : Filter.Tendsto
      (fun s : ℝ => (Real.log (riemannZeta (s:ℂ)).re + Real.log (s - 1))
        - (s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (deriv Gamma 1 + γ)) := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (key s hs).symm
  -- But the same function tends to `0 - 0` by the two limit lemmas.
  have hlim := log_zeta_limit.sub sub_one_mul_integral_E₂Λ_tendsto
  rw [sub_zero] at hlim
  exact tendsto_nhds_unique hconst hlim

theorem γ.eq_eulerMascheroni : γ = eulerMascheroniConstant := by
  linarith [Real.eulerMascheroniConstant_eq_neg_deriv, deriv_gamma_add_γ_eq_zero]

theorem gamma_eq_eulerMascheroni : γ = eulerMascheroniConstant :=
  γ.eq_eulerMascheroni

theorem sum_mangoldt_div_log_eq (x : ℝ) : ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / (d * log d) = log (log x) + eulerMascheroniConstant + E₂Λ x := by
    grind [γ.eq_eulerMascheroni]

theorem sum_mangoldt_div_log_eq_log_log : ∃ C, ∀ x, 2 ≤ x →
    |∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / (d * log d) - log (log x)| ≤ C := by
    use (log 4 + 6)/log 2 + |eulerMascheroniConstant|
    intro x hx
    rw [sum_mangoldt_div_log_eq]
    calc
      _ = |E₂Λ x + eulerMascheroniConstant| := by ring_nf
      _ ≤ (log 4 + 6)/log x + |eulerMascheroniConstant| := by grw [abs_add_le, E₂Λ.abs_le hx]
      _ ≤ _ := by gcongr

theorem sum_mangoldt_div_log_eq_log_log' : (fun x ↦ ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / (d * log d) - log (log x)) =O[atTop] (fun _ ↦ (1:ℝ)) := by
    simp only [isBigO_iff, norm_eq_abs, one_mem, CStarRing.norm_of_mem_unitary, mul_one,
      eventually_atTop]
    obtain ⟨ C, _ ⟩ := sum_mangoldt_div_log_eq_log_log
    use C, 2


theorem sum_mangoldt_div_log_eq_log_log'' : (fun x ↦ ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / (d * log d)) ~[atTop] (fun x ↦ log (log x)) := by
    apply IsLittleO.isEquivalent (IsBigO.trans_isLittleO _ one_eq_o_log_log)
    convert! sum_mangoldt_div_log_eq_log_log' using 1

noncomputable def M : ℝ := (∫ t in Set.Ioi 2, E₁p t / (t * log t^2)) + 1 - log (log 2)

theorem M.le : M ≤ (log 4 + 4) / log 2 + 1 - log (log 2) := calc
    _ ≤ (∫ t in Set.Ioi 2, (log 4 + 4) / (t * log t^2)) + 1 - log (log 2) := by
      unfold M; gcongr with x hx
      · exact integrable_E₁p_div_mul_log_sq (by norm_num)
      · exact integrable_const_div_mul_log_sq _ (by norm_num)
      · measurability
      · simp at hx; positivity
      simp at hx; exact E₁p.le (by linarith)
    _ = _ := by rw [integ_div_mul_log_sq _ (by norm_num)]

theorem M.ge : M ≥ (-2 - E₁) / log 2 + 1 - log (log 2) := calc
    _ ≥ (∫ t in Set.Ioi 2, (-2 - E₁) / (t * log t^2)) + 1 - log (log 2) := by
      unfold M; gcongr with x hx
      · exact integrable_const_div_mul_log_sq _ (by norm_num)
      · exact integrable_E₁p_div_mul_log_sq (by norm_num)
      · measurability
      · simp at hx; positivity
      simp at hx; exact E₁p.ge (by linarith)
    _ = _ := by rw [integ_div_mul_log_sq _ (by norm_num)]

noncomputable abbrev E₂p (x : ℝ) : ℝ := ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (1:ℝ) / p - log (log x) - M

theorem sum_prime_div_eq (x : ℝ) : ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (1:ℝ) / p = log (log x) + M + E₂p x := by
    ring

theorem E₂p.eq {x : ℝ} (hx : 2 ≤ x) :
    E₂p x = E₁p x / log x - ∫ t in Set.Ioi x, E₁p t / (t * log t^2) := by
  unfold E₂p
  rw [sum_filter, ← sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp [Nat.not_prime_one])]
  have (n : ℕ) : (if Nat.Prime n then (1 : ℝ) / n else 0) = (if Nat.Prime n then log n / n else 0) / log n := by
    split_ifs with h
    · have : log n ≠ 0 := by simp; grind [h.two_le]
      field
    · simp
  simp_rw [this]
  rw [sum_div_log_eq hx, sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), ← sum_filter]
  rw [sum_log_prime_div_eq]
  have : ∫ t in 2..x, (∑ n ∈ Ioc 1 ⌊t⌋₊, if Nat.Prime n then log ↑n / ↑n else 0) / (t * log t ^ 2) = ∫ t in 2..x, (1 / (t * log t) + E₁p t / (t * log t ^2)) := by
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    rw [sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), ← sum_filter, sum_log_prime_div_eq]
    field
  rw [this, intervalIntegral.integral_add]
  · rw [integral_one_div_mul_log hx, add_div, div_self (by simp; grind)]
    unfold M
    calc
    _ = E₁p x / log x + (∫ (x : ℝ) in 2..x, E₁p x / (x * log x ^ 2)) -
      ((∫ (t : ℝ) in Set.Ioi 2, E₁p t / (t * log t ^ 2))) := by ring
    _ = _ := by
      rw [← intervalIntegral.integral_interval_add_Ioi (integrable_E₁p_div_mul_log_sq (by rfl)) (integrable_E₁p_div_mul_log_sq hx)]
      ring
  · exact intervalIntegrable_one_div_mul_log hx
  · rw [intervalIntegrable_iff, Set.uIoc_of_le hx]
    exact integrable_E₁p_div_mul_log_sq (x := 2) (by rfl)|>.mono (by grind) (by rfl)

theorem E₂p.abs_le {x : ℝ} (hx : 2 ≤ x) :
    |E₂p x| ≤ (log 4 + 6 + E₁) / log x := by
    have : 0 < log x := by apply log_pos; linarith
    rw [E₂p.eq hx, abs_le']
    constructor
    · grw [E₁p.le (by linarith)]
      have : ∫ t in Set.Ioi x, E₁p t / (t * log t^2) ≥ (- 2 - E₁) / log x := calc
        _ ≥ ∫ t in Set.Ioi x, (-2 - E₁) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_const_div_mul_log_sq (-2 - E₁) hx)
            (integrable_E₁p_div_mul_log_sq hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := log_pos this
          gcongr; exact E₁p.ge (by linarith)
        _ = _ := integ_div_mul_log_sq (-2 - E₁) hx
      grw [this]
      grind
    grw [E₁p.ge (by linarith)]
    have : ∫ t in Set.Ioi x, E₁p t / (t * log t^2) ≤ (log 4 + 4) / log x := calc
        _ ≤ ∫ t in Set.Ioi x, (log 4 + 4) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_E₁p_div_mul_log_sq hx)
            (integrable_const_div_mul_log_sq (log 4 + 4) hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := log_pos this
          gcongr; exact E₁p.le (by linarith)
        _ = _ := integ_div_mul_log_sq (log 4 + 4) hx
    grw [this]
    grind

theorem E₂p.bound : E₂p =O[atTop] (fun x ↦ 1 / log x) := by
    simp only [one_div, isBigO_iff, norm_eq_abs, norm_inv, eventually_atTop]
    use log 4 + 6 + E₁, 2
    intro x hx
    convert E₂p.abs_le hx using 1
    have : 0 < log x := by apply log_pos; linarith
    grind [abs_of_pos this]

theorem E₂p.bound' : E₂p =o[atTop] (fun _ ↦ (1:ℝ)) := E₂p.bound.trans_isLittleO inv_log_eq_o_one

theorem primeReciprocalError_primesLE_isLittleO_one :
    (fun x : ℝ =>
      ∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) / p - log (log x) - M) =o[atTop]
        (fun _ => (1 : ℝ)) := by
  simpa only [E₂p, Nat.primesLE_eq_filter_Ioc_zero] using E₂p.bound'

theorem sum_prime_div_eq_log_log : ∃ C, ∀ x, 2 ≤ x →
    |∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1:ℝ) / p - log (log x)| ≤ C := by
    use |M| + (log 4 + 6 + E₁) / log 2
    intro x hx
    rw [sum_prime_div_eq]
    calc
      _ = |M + E₂p x| := by ring_nf
      _ ≤ |M| + (log 4 + 6 + E₁) / log x := by grw [abs_add_le, E₂p.abs_le hx]
      _ ≤ _ := by
        gcongr
        have : 0 < log 4 := by apply log_pos; norm_num
        linarith [E₁.nonneg]

theorem sum_prime_div_eq_log_log' : (fun x ↦ ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1:ℝ) / p - log (log x)) =O[atTop] (fun _ ↦ (1:ℝ)) := by
    simp only [isBigO_iff, norm_eq_abs, one_mem, CStarRing.norm_of_mem_unitary, mul_one,
      eventually_atTop]
    obtain ⟨ C, hC ⟩ := sum_prime_div_eq_log_log
    use C, 2

theorem sum_prime_div_eq_log_log'' : (fun x ↦ ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1:ℝ) / p) ~[atTop] (fun x ↦ log (log x)) := by
    apply IsLittleO.isEquivalent (IsBigO.trans_isLittleO _ one_eq_o_log_log)
    convert! sum_prime_div_eq_log_log' using 1

lemma HasSum_log_one_sub_one_div_prime {p : ℕ} (hp : p.Prime) :
    HasSum (fun n : ℕ ↦ (-1 : ℝ) / (( n + 1) * p ^ (n + 1))) (log (1 - 1 / p)) := by
  convert! Real.hasSum_pow_div_log_of_abs_lt_one (x := 1 / p) _|>.neg using 1
  · ext
    rw [div_pow, one_pow, div_div]
    ring
  · ring
  · simp only [one_div, abs_inv, Nat.abs_cast]
    exact inv_lt_one_of_one_lt₀ (mod_cast hp.one_lt)

lemma E₂Λ_sub_E₂p_tendsto :
    Tendsto (E₂Λ - E₂p) atTop (nhds 0) := by
  exact isLittleO_one_iff ℝ|>.mp <| E₂Λ.bound'.sub E₂p.bound'

/-- Function used in the proof of `M.eq`, `Λ n / n * log n` restricted to not primes. -/
noncomputable abbrev M_eq_f (n : ℕ) :=
    if ¬n.Prime then Λ n /(n * log n) else 0

lemma E₂Λ_sub_E₂p_eq (x : ℝ) :
    E₂Λ x - E₂p x = ∑ n ∈ Ioc 0 ⌊x⌋₊, M_eq_f n - (γ - M) := by
  calc
  _ = ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / (n * log n) - ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1 : ℝ) / p - (γ - M) := by ring
  _ = _ := by
    rw [sum_filter, ← sum_sub_distrib]
    congr
    ext n
    split_ifs with hn
    · rw [vonMangoldt_apply_prime hn]
      have : log n ≠ 0 := by simp; grind [hn.two_le]
      field
    · ring

lemma M_eq_f.sum_tendsto :
    Tendsto (fun (x : ℝ) ↦ ∑ n ∈ Ioc 0 ⌊x⌋₊, M_eq_f n) atTop (nhds (γ - M)) := by
  apply tendsto_sub_nhds_zero_iff.mp
  convert E₂Λ_sub_E₂p_tendsto using 1
  ext
  rw [← E₂Λ_sub_E₂p_eq]
  simp

lemma M_eq_f.sum_tendsto' :
    Tendsto (fun (N : ℕ) ↦ ∑ n ∈ range N, M_eq_f n) atTop (nhds (γ - M)) := by
  have : Tendsto (fun (N : ℕ) ↦ (∑ n ∈ Ioc 0 ⌊(N : ℝ)⌋₊, M_eq_f n)) atTop (nhds (γ - M)) := M_eq_f.sum_tendsto.comp tendsto_natCast_atTop_atTop
  simp_rw [Nat.floor_natCast] at this
  apply (this.comp (tendsto_sub_atTop_nat 1)).congr'
  filter_upwards [eventually_ge_atTop 1] with N hn
  rw [Nat.range_eq_Icc_zero_sub_one, ← add_sum_Ioc_eq_sum_Icc] <;> grind

lemma M_eq_f.HasSum :
    HasSum M_eq_f (γ - M) := by
  refine hasSum_iff_tendsto_nat_of_nonneg (fun n ↦ ?_) _|>.mpr M_eq_f.sum_tendsto'
  unfold M_eq_f
  split_ifs with hn
  · rfl
  · exact div_nonneg vonMangoldt_nonneg (by positivity)

lemma M_eq_f.sum_primes :
    ∑' (p : Nat.Primes), M_eq_f p = 0 := by
  convert! tsum_zero with p
  grind

lemma tsum_primes_eq_tsum_ite (f : ℕ → ℝ) :
    ∑' (n : Nat.Primes), f n = ∑' (n : ℕ), if n.Prime then f n else 0 := by
  convert! _root_.tsum_subtype Nat.Prime f using 2
  ext
  simp [Set.indicator]
  congr

lemma tsum_M_eq_f_eq_tsum :
    -∑' (n : ℕ), M_eq_f n = ∑' p : ℕ, if p.Prime then log (1 - 1 / p) + 1 / p else 0 := by
  rw [tsum_eq_tsum_primes_add_tsum_primes_of_support_subset_prime_powers M_eq_f.HasSum.summable
    (fun n hn ↦ (by simp_all [vonMangoldt_ne_zero_iff])), M_eq_f.sum_primes, zero_add,
    tsum_primes_eq_tsum_ite (fun p ↦ ∑' (k : ℕ), M_eq_f (p ^ (k + 2))), ← tsum_neg]
  refine tsum_congr fun n ↦ ?_
  split_ifs with hn
  · rw [← HasSum_log_one_sub_one_div_prime hn|>.tsum_eq, HasSum_log_one_sub_one_div_prime hn|>.summable.tsum_eq_zero_add]
    simp only [ite_not, Nat.cast_pow, log_pow, Nat.cast_add, Nat.cast_ofNat, CharP.cast_eq_zero,
      zero_add, pow_one, one_mul, Nat.cast_one, one_div]
    trans -∑' (k : ℕ), (1 : ℝ) / ((k + 2) * n ^ (k + 2))
    · congr
      ext k
      have : ¬(Nat.Prime (n ^ (k + 2))) := by exact Nat.Prime.not_prime_pow (by grind)
      simp only [this, ↓reduceIte, one_div, mul_inv_rev]
      rw [vonMangoldt_apply_pow (by grind), vonMangoldt_apply_prime hn]
      have : log n ≠ 0 := by simp; grind [hn.two_le]
      field
    · rw [← tsum_neg]
      ring_nf
      congr
      ext
      ring_nf
  · ring

theorem M.eq : M = γ + ∑' p : ℕ, if p.Prime then log (1 - 1 / p) + 1 / p else 0 := by
  rw [← tsum_M_eq_f_eq_tsum, M_eq_f.HasSum.tsum_eq]
  ring

noncomputable def E₃ (x : ℝ) : ℝ := ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, log (1 - (1:ℝ) / p) + log (log x) + eulerMascheroniConstant

theorem prod_one_minus_div_prime_eq {x : ℝ} (hx : 1 < x) :
    ∏ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1 - (1 : ℝ) / p) =
      exp (-eulerMascheroniConstant) * exp (E₃ x) / log x := by
  have hlog : 0 < log x := log_pos hx
  have hpos : ∀ {p : ℕ}, p.Prime → (0 : ℝ) < 1 - 1 / p := fun {p} hp ↦ by
    have : (2 : ℝ) ≤ p := mod_cast hp.two_le
    grind [one_div_le_one_div_of_le two_pos this]
  rw [E₃, exp_add, exp_add, exp_sum, exp_log hlog, exp_neg,
    prod_congr rfl fun p hp ↦ exp_log (hpos (mem_filter.mp hp).2)]
  field_simp

noncomputable abbrev M_eq_summand (p : ℕ) := if p.Prime then log (1 - 1 / p) + 1 / p else 0

lemma M_eq_summand_bound (n : ℕ) :
    |M_eq_summand n| ≤ 2 / n ^ 2 := by
  unfold M_eq_summand
  split_ifs with h
  · trans 1 / n ^ 2 / (1 - 1 / n)
    · convert abs_log_sub_add_sum_range_le (x := 1 / n) _ 1 using 1
      · rw [add_comm]
        simp
      · rw [abs_of_nonneg (by simp)]
        ring
      · simpa using inv_lt_one_of_one_lt₀ (mod_cast h.one_lt)
    rw [(by ring : (2 : ℝ) / n ^ 2 = 1 / n ^ 2 / (1 / 2))]
    gcongr
    suffices (1 : ℝ) / n ≤ 1 / 2 by linarith
    gcongr
    exact_mod_cast h.two_le
  · rw [abs_zero]
    positivity

lemma M_eq_summable : Summable M_eq_summand := by
  apply Summable.of_abs
  exact Summable.of_nonneg_of_le (by simp) M_eq_summand_bound (Summable.const_div (by simp) _)

lemma tsum_M_eq_summand_eq :
    ∑' (n : ℕ), M_eq_summand n = M - γ := by
  rw [M.eq]
  grind

lemma sum_one_div_sq_le {N : ℝ} (hN : 1 ≤ N) :
    ∑' (n : ℕ), (1 : ℝ) / (n + N) ^ 2 ≤ 2 / N := by
  grw [AntitoneOn.tsum_le_integral (f := (fun t ↦ 1 / (t + N) ^ 2))]
  · have hd : ∀ x ∈ Set.Ici 0, HasDerivAt (fun t ↦ -1 / (t + N)) (1 / (x + N) ^ 2) x := by
      intro t ht
      convert! HasDerivAt.fun_div (d' := (1 : ℝ)) (hasDerivAt_const ..) _ _ using 1
      · ring
      · simpa using hasDerivAt_id' t
      · simp at ht
        linarith
    have lim : Tendsto (fun t ↦ -1 / (t + N)) atTop (nhds 0) := by
      exact (tendsto_atTop_add_const_right atTop N tendsto_id).const_div_atTop _
    rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' hd (fun _ _ ↦ (by positivity)) lim]
    ring_nf
    rw [mul_two]
    gcongr
    field_simp
    exact hN
  · unfold AntitoneOn
    intro a ha b hb h
    beta_reduce
    simp at ha hb
    gcongr
  · convert! integrableOn_add_rpow_Ioi_of_lt (by norm_num : (-2 : ℝ) < -1) (by linarith : -N < 0) using 2
    simp
  · exact fun _ _ ↦ (by positivity)

lemma sum_M_eq_summand_le {N : ℕ} (hN : 0 < N) :
    |∑ n ∈ range N, M_eq_summand n - (M - γ)| ≤ 4 / N := by
  rw [← tsum_M_eq_summand_eq, ← M_eq_summable.sum_add_tsum_nat_add N]
  simp only [sub_add_cancel_left, abs_neg]
  rw [← norm_eq_abs]
  have summable := summable_nat_add_iff N|>.mpr M_eq_summable.norm
  apply norm_tsum_le_tsum_norm summable|>.trans
  apply Summable.tsum_le_tsum (fun _ ↦ M_eq_summand_bound _) summable _|>.trans
  · conv => lhs; arg 1; ext; rw [← mul_one_div]
    rw [tsum_mul_left]
    push_cast
    grw [sum_one_div_sq_le (mod_cast hN)]
    ring_nf
    rfl
  · exact (summable_nat_add_iff N|>.mpr (summable_one_div_nat_pow.mpr one_lt_two))|>.const_div _

lemma sum_M_eq_summand_le' {x : ℝ} (hx : 2 ≤ x) :
    |∑ n ∈ Ioc 0 ⌊x⌋₊, M_eq_summand n - (M - γ)| ≤ 4 / x := by
  have := sum_M_eq_summand_le (by grind : 0 < ⌊x⌋₊ + 1)
  rw [Nat.range_eq_Icc_zero_sub_one _ (by grind), ← add_sum_Ioc_eq_sum_Icc (by grind),
    (by simp : M_eq_summand 0 = 0), zero_add] at this
  simp only [add_tsub_cancel_right, Nat.cast_add, Nat.cast_one] at this
  grw [this]
  gcongr
  exact Nat.lt_floor_add_one _|>.le

theorem E₃.abs_le : ∃ C, ∀ x, 2 ≤ x → |E₃ x| ≤ C / log x := by
  unfold E₃
  refine ⟨4 + (log 4 + 6 + E₁), fun x hx ↦ ?_⟩
  calc
  _ = |(∑ n ∈ Ioc 0 ⌊x⌋₊, M_eq_summand n - (M - γ)) - E₂p x| := by
    unfold E₂p
    have (n : ℕ) : M_eq_summand n = (if n.Prime then log (1 - 1 / n) else 0) + (if n.Prime then (1 : ℝ) / n else 0) := by
      unfold M_eq_summand
      split_ifs
      · rfl
      · ring
    simp_rw [this]
    rw [sum_filter, sum_filter, sum_add_distrib, γ.eq_eulerMascheroni]
    ring_nf
  _ ≤ _ := by
    grw [abs_sub, E₂p.abs_le hx, sum_M_eq_summand_le' hx]
    have : 4 / x ≤ 4 / log x := by
      gcongr
      · exact log_pos (by linarith)
      · exact log_le_self (by linarith)
    grw [this]
    rw [← add_div]

theorem E₃.bound : E₃ =O[atTop] (fun x ↦ 1 / log x) := by
    simp only [isBigO_iff, norm_eq_abs, eventually_atTop]
    obtain ⟨ C, hC ⟩ := E₃.abs_le
    use C, 2
    convert hC using 3 with x hx
    have : 0 < log x := by apply log_pos; linarith
    have : 0 < 1 / log x := by positivity
    grind [abs_of_pos this]

theorem E₃.bound' : E₃ =o[atTop] (fun _ ↦ (1:ℝ)) := E₃.bound.trans_isLittleO inv_log_eq_o_one

theorem E₃.bound'' : (fun x ↦ ∏ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (1 - (1:ℝ) / p)) ~[atTop] (fun x ↦ exp (-eulerMascheroniConstant) / log x) := by
   rw [isEquivalent_iff_tendsto_one]
   · convert Tendsto.congr' ?_ (Tendsto.rexp ((isLittleO_one_iff ℝ).mp E₃.bound')) using 2 with x
     · simp
     simp only [EventuallyEq.iff_eventually, Pi.div_apply, eventually_atTop]; use 2; intro x hx
     rw [prod_one_minus_div_prime_eq (by linarith)]
     have : 0 < log x := by apply log_pos; linarith
     field_simp
   simp only [ne_eq, div_eq_zero_iff, exp_ne_zero, log_eq_zero, eventually_atTop]; use 2
   grind

theorem E₃.bound''' : (fun x ↦ ∏ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (1 - (1:ℝ) / p) - exp (-eulerMascheroniConstant) / log x) =O[atTop] (fun x ↦ 1 / (log x)^2) := by
  obtain ⟨c, hc⟩ := E₃.abs_le
  rw [isBigO_iff]
  refine ⟨exp (-eulerMascheroniConstant) * 2 * c, ?_⟩
  filter_upwards [eventually_ge_atTop 2, eventually_ge_atTop c.exp] with x hx hx2
  rw [prod_one_minus_div_prime_eq (by linarith)]
  specialize hc x hx
  rw [norm_eq_abs, norm_eq_abs]
  calc
  _ = |exp (-eulerMascheroniConstant) / log x * (exp (E₃ x) - 1)| := by ring_nf
  _ = |exp (-eulerMascheroniConstant) / log x| * |exp (E₃ x) - 1| := by rw [abs_mul]
  _ ≤ _ := by
    have : |E₃ x| ≤ 1 := by
      apply hc.trans
      have := log_le_log (exp_pos _) hx2
      rw [log_exp] at this
      apply div_le_one_iff.mpr <| Or.inl ⟨log_pos (by linarith), this⟩
    grw [abs_exp_sub_one_le this, hc]
    apply le_of_eq
    rw [abs_div, abs_div, abs_one, abs_of_nonneg (exp_nonneg _), abs_of_nonneg (log_nonneg (by linarith)), abs_of_nonneg (sq_nonneg _)]
    ring

end Mertens

end

-- ==== Defs
section



open Finset

namespace OMA.Port8

/-- A violation of the property. -/
def Violation (A : Set ℕ) : Prop :=
  ∃ s t : Finset ℕ, ↑s ⊆ A ∧ ↑t ⊆ A ∧ s.prod id = t.prod id ∧ s.card ≠ t.card

lemma isMulCardSet_iff_not_violation (A : _root_.Set ℕ) : Erdos786.Set.IsMulCardSet A ↔ ¬ Violation A := by
  unfold Erdos786.Set.IsMulCardSet Violation
  constructor
  · rintro h ⟨s, t, hs, ht, hp, hc⟩
    exact hc (h s t hs ht hp)
  · intro h s t hs ht hp
    by_contra hc
    exact h ⟨s, t, hs, ht, hp, hc⟩

/-- `S` is a matching of `q`-pairs `(x, q x)` inside `A`: every pair lies in `A`, has ratio `q`,
and all `2 |S|` endpoints are distinct. -/
structure IsQMatching (A : Set ℕ) (q : ℚ) (S : Finset (ℕ × ℕ)) : Prop where
  mem : ∀ e ∈ S, e.1 ∈ A ∧ e.2 ∈ A
  ratio : ∀ e ∈ S, (e.2 : ℚ) = q * e.1
  disj : (S.image Prod.fst ∪ S.image Prod.snd).card = 2 * S.card

/-- `q` is `M`-rich for `A`: the `q`-pairs in `A` contain a matching of size at least `M`. -/
def Rich (A : Set ℕ) (q : ℚ) (M : ℕ) : Prop :=
  ∃ S : Finset (ℕ × ℕ), IsQMatching A q S ∧ M ≤ S.card

/-- The largest divisor of `z` composed of primes in `Q`. -/
noncomputable def qPart (Q : Finset ℕ) (z : ℕ) : ℕ :=
  ∏ q ∈ Q, q ^ z.factorization q

end OMA.Port8

end

-- ==== Heavy
section



open Finset

namespace OMA.Port8

lemma card_Icc_filter_dvd (N d : ℕ) : ((Icc 1 N).filter (fun n => d ∣ n)).card = N / d := by
  have : Icc 1 N = Ioc 0 N := by ext x; simp; omega
  rw [this, Nat.Ioc_filter_dvd_card_eq_div]

lemma card_Icc_filter_dvd_le (N d : ℕ) :
    ((((Icc 1 N).filter (fun n => d ∣ n)).card : ℕ) : ℝ) ≤ (N : ℝ) / d := by
  rw [card_Icc_filter_dvd]; exact Nat.cast_div_le

lemma card_Icc_filter_dvd_ge (N d : ℕ) (hd : 0 < d) :
    (N : ℝ) / d - 1 ≤ ((((Icc 1 N).filter (fun n => d ∣ n)).card : ℕ) : ℝ) := by
  rw [card_Icc_filter_dvd]
  have h := Nat.lt_div_mul_add (a := N) hd
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have h' : (N : ℝ) < ((N / d : ℕ) : ℝ) * d + d := by exact_mod_cast h
  rw [div_sub_one hd'.ne', div_le_iff₀ hd']
  linarith

/-- Number of elements of `H` dividing `n`, as a real number. -/
noncomputable def omegaH (H : Finset ℕ) (n : ℕ) : ℝ := ∑ p ∈ H, if p ∣ n then (1 : ℝ) else 0

lemma sum_omegaH (H : Finset ℕ) (s : Finset ℕ) :
    ∑ n ∈ s, omegaH H n = ∑ p ∈ H, (((s.filter (fun n => p ∣ n)).card : ℕ) : ℝ) := by
  unfold omegaH
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_boole]

lemma sum_omegaH_sq_le (N : ℕ) (H : Finset ℕ) (hH : ∀ p ∈ H, p.Prime) :
    ∑ n ∈ Icc 1 N, omegaH H n ^ 2 ≤
      N * (∑ p ∈ H, (1 : ℝ) / p) + N * (∑ p ∈ H, (1 : ℝ) / p) ^ 2 := by
  have expand : ∀ n, omegaH H n ^ 2 =
      ∑ p ∈ H, ∑ q ∈ H, (if p ∣ n ∧ q ∣ n then (1 : ℝ) else 0) := by
    intro n
    unfold omegaH
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    by_cases hp : p ∣ n <;> by_cases hq : q ∣ n <;> simp [hp, hq]
  simp_rw [expand]
  rw [Finset.sum_comm]
  have pair : ∀ p ∈ H, ∀ q ∈ H,
      ∑ n ∈ Icc 1 N, (if p ∣ n ∧ q ∣ n then (1 : ℝ) else 0) ≤
        (N : ℝ) / (p * q) + (if p = q then (N : ℝ) / p else 0) := by
    intro p hp q hq
    rw [Finset.sum_boole]
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hH p hp).pos
    have hq0 : (0 : ℝ) < q := by exact_mod_cast (hH q hq).pos
    by_cases hpq : p = q
    · subst hpq
      simp only [and_self, if_true]
      have := card_Icc_filter_dvd_le N p
      have : (0 : ℝ) ≤ (N : ℝ) / (p * p) := by positivity
      linarith
    · rw [if_neg hpq]
      have hcop : Nat.Coprime p q := (Nat.coprime_primes (hH p hp) (hH q hq)).2 hpq
      have : (Icc 1 N).filter (fun n => p ∣ n ∧ q ∣ n) =
          (Icc 1 N).filter (fun n => p * q ∣ n) := by
        ext n
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨h1, h2, h3⟩; exact ⟨h1, hcop.mul_dvd_of_dvd_of_dvd h2 h3⟩
        · rintro ⟨h1, h2⟩
          exact ⟨h1, (Nat.dvd_mul_right p q).trans h2, (Nat.dvd_mul_left q p).trans h2⟩
      rw [this]
      have := card_Icc_filter_dvd_le N (p * q)
      push_cast at this
      linarith
  calc ∑ p ∈ H, ∑ n ∈ Icc 1 N, ∑ q ∈ H, (if p ∣ n ∧ q ∣ n then (1 : ℝ) else 0)
      ≤ ∑ p ∈ H, ∑ q ∈ H, ((N : ℝ) / (p * q) + (if p = q then (N : ℝ) / p else 0)) := by
        refine Finset.sum_le_sum fun p hp => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_le_sum fun q hq => pair p hp q hq
    _ = N * (∑ p ∈ H, (1 : ℝ) / p) + N * (∑ p ∈ H, (1 : ℝ) / p) ^ 2 := by
        simp_rw [Finset.sum_add_distrib, Finset.sum_ite_eq, sq, Finset.sum_mul_sum,
          Finset.mul_sum]
        rw [add_comm]
        congr 1
        · refine Finset.sum_congr rfl fun p hp => ?_
          rw [if_pos hp]; ring
        · refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
          field_simp

/-- Paper Lemma 6.2. `E ⊆ [1,N]`, `|E| ≤ N/32`; every `p ∈ H` is a prime `≤ N` with
`|E ∩ pℕ| ≥ N/(16p)`. Then `∑_{p ∈ H} 1/p ≤ 3072 |E| / N`. -/
theorem heavy_recip_sum_le (N : ℕ) (hN : 0 < N) (E : Finset ℕ) (hE : E ⊆ Icc 1 N)
    (hD : 32 * E.card ≤ N) (H : Finset ℕ)
    (hH : ∀ p ∈ H, p.Prime ∧ p ≤ N ∧ (N : ℝ) ≤ 16 * p * (E.filter (fun n => p ∣ n)).card) :
    ∑ p ∈ H, (1 : ℝ) / p ≤ 3072 * E.card / N := by
  set S : ℝ := ∑ p ∈ H, (1 : ℝ) / p with hSdef
  have hHp : ∀ p ∈ H, p.Prime := fun p hp => (hH p hp).1
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun p _ => by positivity
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  -- |H| ≤ N
  have hm : (H.card : ℝ) ≤ N := by
    have hsub : H ⊆ Icc 1 N := fun p hp => by
      simp only [Finset.mem_Icc]; exact ⟨(hH p hp).1.one_le, (hH p hp).2.1⟩
    have := Finset.card_le_card hsub
    simp only [Nat.card_Icc, add_tsub_cancel_right] at this
    exact_mod_cast this
  -- first moment
  have hB : (N : ℝ) * S - H.card ≤ ∑ n ∈ Icc 1 N, omegaH H n := by
    rw [sum_omegaH, hSdef, Finset.mul_sum, Finset.card_eq_sum_ones, Nat.cast_sum,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun p hp => ?_
    have := card_Icc_filter_dvd_ge N p (hHp p hp).pos
    push_cast
    rw [mul_one_div]
    exact this
  -- second moment
  have hA := sum_omegaH_sq_le N H hHp
  rw [← hSdef] at hA
  -- variance over [1,N]
  have hV : ∑ n ∈ Icc 1 N, (omegaH H n - S) ^ 2 ≤ 3 * N * S := by
    have e : ∀ n, (omegaH H n - S) ^ 2 = omegaH H n ^ 2 - 2 * S * omegaH H n + S ^ 2 := by
      intro n; ring
    simp_rw [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul]
    nlinarith [mul_le_mul_of_nonneg_left hB (by linarith : (0 : ℝ) ≤ 2 * S),
      mul_le_mul_of_nonneg_left hm hS0]
  -- restrict to E
  have hVE : ∑ n ∈ E, (omegaH H n - S) ^ 2 ≤ 3 * N * S :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg hE fun n _ _ => sq_nonneg _) hV
  have hCS := sq_sum_le_card_mul_sum_sq (s := E) (f := fun n => omegaH H n - S)
  -- heaviness
  have hheavy : (N : ℝ) * S / 16 ≤ ∑ n ∈ E, omegaH H n := by
    rw [sum_omegaH, hSdef, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_le_sum fun p hp => ?_
    have h3 := (hH p hp).2.2
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hHp p hp).pos
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 16), mul_one_div, div_le_iff₀ hp0]
    linarith
  have hX : ∑ n ∈ E, (omegaH H n - S) = ∑ n ∈ E, omegaH H n - E.card * S := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  have hDr : 32 * (E.card : ℝ) ≤ N := by exact_mod_cast hD
  have hD0 : (0 : ℝ) ≤ E.card := Nat.cast_nonneg _
  have hXlow : (N : ℝ) * S / 32 ≤ ∑ n ∈ E, (omegaH H n - S) := by
    rw [hX]; nlinarith
  have hsq : ((N : ℝ) * S / 32) ^ 2 ≤ E.card * (3 * N * S) := by
    have h1 : ((N : ℝ) * S / 32) ^ 2 ≤ (∑ n ∈ E, (omegaH H n - S)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hXlow 2
    have h2 := mul_le_mul_of_nonneg_left hVE hD0
    linarith
  rw [le_div_iff₀ hNr]
  rcases hS0.eq_or_lt with h0 | hpos
  · rw [← h0, zero_mul]; positivity
  · have : S * ((N : ℝ) * (S * N) / 1024) ≤ S * (3 * E.card * N) := by nlinarith
    have h4 := le_of_mul_le_mul_left this hpos
    have h5 : (S * N) * N ≤ (3072 * E.card) * N := by nlinarith
    exact le_of_mul_le_mul_right h5 hNr

end OMA.Port8

end

-- ==== Smooth
section



open Finset Real
open scoped Classical

namespace OMA.Port8

/-- The constant in the explicit Mertens error bound. -/
noncomputable def mC : ℝ := log 4 + 6 + Mertens.E₁

lemma mC_nonneg : 0 ≤ mC := by
  unfold mC
  have := Mertens.E₁.nonneg
  have : 0 < log (4:ℝ) := log_pos (by norm_num)
  linarith

/-- Threshold on `log y`. -/
noncomputable def mK : ℝ := max 100 (3552 * mC)

lemma sum_filter_prime_split (A B : ℝ) (hAB : A ≤ B) :
    ∑ p ∈ Ioc 0 ⌊B⌋₊ with p.Prime, (1:ℝ) / p =
      (∑ p ∈ Ioc 0 ⌊A⌋₊ with p.Prime, (1:ℝ) / p) +
        ∑ p ∈ Ioc ⌊A⌋₊ ⌊B⌋₊ with p.Prime, (1:ℝ) / p := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_Ioc_consecutive _ (Nat.zero_le _) (Nat.floor_mono hAB)]

/-- Mertens on a short multiplicative interval. -/
lemma mertens_interval (l L : ℝ) (hl : mK ≤ l) (h16 : 16 * l ≤ L) (h56 : L ≤ 56 * l) :
    (1:ℝ) / 222 ≤ ∑ p ∈ Ioc ⌊exp ((L - l) / 112)⌋₊ ⌊exp ((L - l / 2) / 112)⌋₊ with p.Prime,
      (1:ℝ) / p := by
  set A := exp ((L - l) / 112) with hA
  set B := exp ((L - l / 2) / 112) with hB
  have hl100 : 100 ≤ l := le_trans (le_max_left _ _) hl
  have hlC : 3552 * mC ≤ l := le_trans (le_max_right _ _) hl
  have hlogA : log A = (L - l) / 112 := log_exp _
  have hlogB : log B = (L - l / 2) / 112 := log_exp _
  have hlA8 : l / 8 ≤ log A := by rw [hlogA]; linarith
  have hlAB : log A ≤ log B := by rw [hlogA, hlogB]; linarith
  have hAB : A ≤ B := exp_le_exp.mpr (by linarith)
  have hA2 : 2 ≤ A := by
    have := add_one_le_exp ((L - l) / 112)
    rw [← hA] at this; linarith
  have hB2 : 2 ≤ B := le_trans hA2 hAB
  have hsplit := sum_filter_prime_split A B hAB
  rw [Mertens.sum_prime_div_eq B, Mertens.sum_prime_div_eq A] at hsplit
  have hEA := Mertens.E₂p.abs_le hA2
  have hEB := Mertens.E₂p.abs_le hB2
  have hposA : 0 < log A := by linarith
  have hposB : 0 < log B := by linarith
  have hEA' : |Mertens.E₂p A| ≤ 8 * mC / l := by
    refine le_trans hEA ?_
    rw [div_le_div_iff₀ hposA (by linarith)]
    have := mC_nonneg
    unfold mC at this ⊢
    nlinarith
  have hEB' : |Mertens.E₂p B| ≤ 8 * mC / l := by
    refine le_trans hEB ?_
    rw [div_le_div_iff₀ hposB (by linarith)]
    have := mC_nonneg
    unfold mC at this ⊢
    nlinarith
  have hsmall : 16 * mC / l ≤ 1 / 222 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hlog : (1:ℝ) / 111 ≤ log (log B) - log (log A) := by
    rw [← log_div hposB.ne' hposA.ne']
    refine le_trans ?_ (one_sub_inv_le_log_of_pos (div_pos hposB hposA))
    rw [inv_div, le_sub_comm, div_le_iff₀ hposB, hlogA, hlogB]
    linarith
  have h1 := (abs_le.mp hEA').1
  have h2 := (abs_le.mp hEB').1
  have h3 := (abs_le.mp hEA').2
  have : 16 * mC / l = 8 * mC / l + 8 * mC / l := by ring
  linarith


lemma card_Icc_half_ge (t : ℝ) (ht : 6 ≤ t) :
    t / 3 ≤ ((Icc ⌈t / 2⌉₊ ⌊t⌋₊).card : ℝ) := by
  rw [Nat.card_Icc]
  have h1 : (⌈t / 2⌉₊ : ℝ) < t / 2 + 1 := Nat.ceil_lt_add_one (by linarith)
  have h2 : t < (⌊t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one t
  have hle : ⌈t / 2⌉₊ ≤ ⌊t⌋₊ + 1 := by
    have : (⌈t / 2⌉₊ : ℝ) ≤ (⌊t⌋₊ : ℝ) + 1 := by linarith
    exact_mod_cast this
  rw [Nat.cast_sub hle]
  push_cast
  linarith

lemma card_big_primeFactors (n : ℕ) (hn : n ≠ 0) (A X : ℝ) (hA : 1 < A) (hnX : (n : ℝ) ≤ X)
    (hXA : X ≤ A ^ 448) : (n.primeFactors.filter (fun p : ℕ => A < (p : ℝ))).card ≤ 448 := by
  set F := n.primeFactors.filter (fun p : ℕ => A < (p : ℝ))
  have hdvd : ∏ p ∈ F, p ∣ n :=
    (Finset.prod_dvd_prod_of_subset F n.primeFactors id (Finset.filter_subset _ _)).trans
      (Nat.prod_primeFactors_dvd n)
  have hle : ∏ p ∈ F, p ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd
  have hpow : A ^ F.card ≤ ((∏ p ∈ F, p : ℕ) : ℝ) := by
    rw [← Finset.prod_const, Nat.cast_prod]
    refine Finset.prod_le_prod (fun _ _ => by linarith) (fun p hp => ?_)
    exact le_of_lt (Finset.mem_filter.mp hp).2
  have : A ^ F.card ≤ A ^ 448 := by
    refine le_trans hpow (le_trans ?_ (le_trans hnX hXA))
    exact_mod_cast hle
  exact (pow_le_pow_iff_right₀ hA).mp this

/-- The core counting estimate, in logarithmic coordinates. -/
lemma main_count (y X : ℝ) (hy : 0 < y) (hX : 0 < X) (hl : mK ≤ log y)
    (h16 : 16 * log y ≤ log X) (h56 : log X ≤ 56 * log y) :
    X / 3 * ((1:ℝ) / 222) ^ 112 ≤ (448 ^ 112 : ℝ) *
      (((Icc ⌈X / 2⌉₊ ⌊X⌋₊).filter (fun n => ∀ p ∈ n.primeFactors, ((p : ℕ) : ℝ) ≤ y)).card : ℝ) := by
  set l := log y with hl_def
  set L := log X with hL_def
  set A := exp ((L - l) / 112) with hA
  set B := exp ((L - l / 2) / 112) with hB
  set S := (Icc ⌈X / 2⌉₊ ⌊X⌋₊).filter (fun n => ∀ p ∈ n.primeFactors, ((p : ℕ) : ℝ) ≤ y)
  set I := (Ioc ⌊A⌋₊ ⌊B⌋₊).filter Nat.Prime with hI
  have hmert : (1:ℝ) / 222 ≤ ∑ p ∈ I, (1:ℝ) / p := mertens_interval l L hl h16 h56
  have hl100 : 100 ≤ l := le_trans (le_max_left _ _) hl
  have hyexp : exp l = y := exp_log hy
  have hXexp : exp L = X := exp_log hX
  have hA112 : A ^ 112 = X / y := by
    rw [hA, ← exp_nat_mul, ← hyexp, ← hXexp, ← exp_sub]; congr 1; push_cast; ring
  have hB112 : B ^ 112 = X / exp (l / 2) := by
    rw [hB, ← exp_nat_mul, ← hXexp, ← exp_sub]; congr 1; push_cast; ring
  have hA448 : X ≤ A ^ 448 := by
    rw [hA, ← exp_nat_mul, ← hXexp]; apply exp_le_exp.mpr; push_cast; linarith
  have hBy : B ≤ y := by rw [← hyexp, hB]; apply exp_le_exp.mpr; linarith
  have hA1 : 1 < A := by rw [hA]; linarith [add_one_le_exp ((L - l) / 112)]
  have hsq6 : 6 ≤ exp (l / 2) := by have := add_one_le_exp (l / 2); linarith
  have hsqpos : 0 < exp (l / 2) := exp_pos _
  -- tuples
  set T := Fintype.piFinset (fun _ : Fin 112 => I) with hT
  let Qn : (Fin 112 → ℕ) → ℕ := fun q => ∏ i, q i
  have hQcast : ∀ q, (Qn q : ℝ) = ∏ i, (q i : ℝ) := fun q => Nat.cast_prod _ _
  have hmemI : ∀ q ∈ T, ∀ i, q i ∈ I := fun q hq i => Fintype.mem_piFinset.mp hq i
  have hqA : ∀ q ∈ T, ∀ i, A < (q i : ℝ) := fun q hq i => by
    have := (Finset.mem_filter.mp (hmemI q hq i)).1
    exact Nat.lt_of_floor_lt (Finset.mem_Ioc.mp this).1
  have hqB : ∀ q ∈ T, ∀ i, (q i : ℝ) ≤ B := fun q hq i => by
    have := (Finset.mem_filter.mp (hmemI q hq i)).1
    exact (Nat.le_floor_iff (by positivity)).mp (Finset.mem_Ioc.mp this).2
  have hqprime : ∀ q ∈ T, ∀ i, (q i).Prime := fun q hq i => (Finset.mem_filter.mp (hmemI q hq i)).2
  have hQlow : ∀ q ∈ T, X / y < (Qn q : ℝ) := fun q hq => by
    rw [← hA112, hQcast]
    have := Finset.prod_lt_prod_of_nonempty (s := (Finset.univ : Finset (Fin 112)))
      (f := fun _ => A) (g := fun i => (q i : ℝ)) (fun _ _ => by linarith)
      (fun i _ => hqA q hq i) Finset.univ_nonempty
    rwa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
  have hQup : ∀ q ∈ T, (Qn q : ℝ) ≤ X / exp (l / 2) := fun q hq => by
    rw [← hB112, hQcast]
    have := Finset.prod_le_prod (s := (Finset.univ : Finset (Fin 112)))
      (f := fun i => (q i : ℝ)) (g := fun _ => B) (fun _ _ => by positivity)
      (fun i _ => hqB q hq i)
    rwa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
  have hQpos : ∀ q ∈ T, 0 < (Qn q : ℝ) := fun q hq => lt_trans (by positivity) (hQlow q hq)
  have htlow : ∀ q ∈ T, exp (l / 2) ≤ X / (Qn q : ℝ) := fun q hq => by
    rw [le_div_iff₀ (hQpos q hq)]
    have := hQup q hq
    rw [le_div_iff₀ hsqpos] at this; linarith
  have htup : ∀ q ∈ T, X / (Qn q : ℝ) < y := fun q hq => by
    rw [div_lt_iff₀ (hQpos q hq)]
    have := hQlow q hq
    rw [div_lt_iff₀ hy] at this; linarith
  -- pairs
  let R : (Fin 112 → ℕ) → Finset ℕ := fun q => Icc ⌈X / (Qn q : ℝ) / 2⌉₊ ⌊X / (Qn q : ℝ)⌋₊
  set P := T.sigma R with hP
  let f : (Σ _ : Fin 112 → ℕ, ℕ) → ℕ := fun x => x.2 * Qn x.1
  have hmaps : ∀ x ∈ P, f x ∈ S := by
    rintro ⟨q, r⟩ hx
    rw [Finset.mem_sigma] at hx
    obtain ⟨hq, hr⟩ := hx
    have hr' := Finset.mem_Icc.mp hr
    have hQ := hQpos q hq
    have ht6 : 6 ≤ X / (Qn q : ℝ) := le_trans hsq6 (htlow q hq)
    have hrlow : X / (Qn q : ℝ) / 2 ≤ r := Nat.ceil_le.mp hr'.1
    have hrup : (r : ℝ) ≤ X / (Qn q : ℝ) := (Nat.le_floor_iff (by linarith)).mp hr'.2
    have hrpos : 0 < r := by
      have : (0:ℝ) < r := by linarith
      exact_mod_cast this
    show r * Qn q ∈ S
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · apply Nat.ceil_le.mpr
      push_cast
      rw [div_div, div_le_iff₀ (by linarith)] at hrlow
      linarith
    · apply Nat.le_floor
      push_cast
      rw [le_div_iff₀ hQ] at hrup
      linarith
    · intro p hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hpd := Nat.dvd_of_mem_primeFactors hp
      rcases (Nat.Prime.dvd_mul hpp).mp hpd with h | h
      · have : p ≤ r := Nat.le_of_dvd hrpos h
        have : (p : ℝ) ≤ r := by exact_mod_cast this
        linarith [htup q hq]
      · obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff hpp.prime _).mp h
        have : p ≤ q i := Nat.le_of_dvd (hqprime q hq i).pos hi
        have : (p : ℝ) ≤ q i := by exact_mod_cast this
        linarith [hqB q hq i]
  have hfib : ∀ n ∈ S, (P.filter (fun x => f x = n)).card ≤ 448 ^ 112 := by
    intro n hn
    have hn' := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
    have hnX : (n : ℝ) ≤ X := (Nat.le_floor_iff hX.le).mp hn'.2
    have hn0 : n ≠ 0 := by
      intro h0
      have : ⌈X / 2⌉₊ = 0 := by omega
      rw [Nat.ceil_eq_zero] at this; linarith
    set F := n.primeFactors.filter (fun p : ℕ => A < (p : ℝ))
    have hF := card_big_primeFactors n hn0 A X hA1 hnX hA448
    calc (P.filter (fun x => f x = n)).card
        ≤ (Fintype.piFinset (fun _ : Fin 112 => F)).card := by
          refine Finset.card_le_card_of_injOn (fun x => x.1) ?_ ?_
          · rintro ⟨q, r⟩ hx
            rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_sigma] at hx
            obtain ⟨⟨hq, hr⟩, hfx⟩ := hx
            rw [Finset.mem_coe, Fintype.mem_piFinset]
            intro i
            rw [Finset.mem_filter, Nat.mem_primeFactors]
            refine ⟨⟨hqprime q hq i, ?_, hn0⟩, hqA q hq i⟩
            rw [← hfx]
            exact Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)) _
          · rintro ⟨q, r⟩ hx ⟨q', r'⟩ hx' (hqq : q = q')
            subst hqq
            rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_sigma] at hx hx'
            have hQ := hQpos q hx.1.1
            have hQn : 0 < Qn q := by exact_mod_cast hQ
            have : r * Qn q = r' * Qn q := by
              have h1 := hx.2; have h2 := hx'.2
              simp only [f] at h1 h2; rw [h1, h2]
            have := Nat.eq_of_mul_eq_mul_right hQn this
            subst this; rfl
      _ = F.card ^ 112 := Fintype.card_piFinset_const F 112
      _ ≤ 448 ^ 112 := Nat.pow_le_pow_left hF 112
  have hkey : P.card ≤ 448 ^ 112 * S.card :=
    Finset.card_le_mul_card_image_of_maps_to hmaps _ hfib
  have hlower : X / 3 * ((1:ℝ) / 222) ^ 112 ≤ (P.card : ℝ) := by
    rw [hP, Finset.card_sigma, Nat.cast_sum]
    calc X / 3 * ((1:ℝ) / 222) ^ 112
        ≤ X / 3 * (∑ p ∈ I, (1:ℝ) / p) ^ 112 := by
          gcongr
      _ = X / 3 * ∏ _i : Fin 112, ∑ p ∈ I, (1:ℝ) / p := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ = ∑ q ∈ T, X / 3 * ∏ i, (1:ℝ) / (q i) := by
          rw [Finset.prod_univ_sum, Finset.mul_sum]
      _ = ∑ q ∈ T, X / (Qn q : ℝ) / 3 := by
          refine Finset.sum_congr rfl (fun q hq => ?_)
          rw [hQcast, Finset.prod_div_distrib, Finset.prod_const_one]
          ring
      _ ≤ ∑ q ∈ T, ((R q).card : ℝ) := by
          refine Finset.sum_le_sum (fun q hq => ?_)
          exact card_Icc_half_ge _ (le_trans hsq6 (htlow q hq))
  have : (P.card : ℝ) ≤ 448 ^ 112 * (S.card : ℝ) := by exact_mod_cast hkey
  linarith

/-- Paper Lemma 6.3 (with an unspecified constant). -/
theorem smooth_count : ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ X : ℝ, y ^ 16 ≤ X → X ≤ y ^ 56 →
    c₀ * X ≤ (((Icc ⌈X / 2⌉₊ ⌊X⌋₊).filter (fun n => ∀ p ∈ n.primeFactors, ((p : ℕ) : ℝ) ≤ y)).card : ℝ) := by
  refine ⟨((1:ℝ) / 222) ^ 112 / 3 / 448 ^ 112, by positivity, exp mK, ?_⟩
  intro y hy X hX1 hX2
  have hypos : 0 < y := lt_of_lt_of_le (exp_pos _) hy
  have hl : mK ≤ log y := by rw [← log_exp mK]; exact log_le_log (exp_pos _) hy
  have hXpos : 0 < X := lt_of_lt_of_le (by positivity) hX1
  have h16 : 16 * log y ≤ log X := by
    have := log_le_log (by positivity) hX1
    rwa [log_pow] at this
  have h56 : log X ≤ 56 * log y := by
    have := log_le_log hXpos hX2
    rwa [log_pow] at this
  have key := main_count y X hypos hXpos hl (by exact_mod_cast h16) (by exact_mod_cast h56)
  have h448 : (0:ℝ) < 448 ^ 112 := by positivity
  calc ((1:ℝ) / 222) ^ 112 / 3 / 448 ^ 112 * X = X / 3 * ((1:ℝ) / 222) ^ 112 / 448 ^ 112 := by
        ring
    _ ≤ _ := by rw [div_le_iff₀ h448]; linarith

end OMA.Port8

end

-- ==== QPart
section



open Finset Real
open scoped Classical

namespace OMA.Port8

lemma sum_factorization_Icc_eq (q : ℕ) (T : ℕ) :
    ∑ z ∈ Icc 1 T, z.factorization q = (T.factorial).factorization q := by
  induction T with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Nat.factorial_succ,
      Nat.factorization_mul (by omega) (Nat.factorial_ne_zero n)]
    simp [add_comm]

lemma sub_one_mul_sum_factorization_le {q : ℕ} (hq : q.Prime) (T : ℕ) :
    ((q : ℝ) - 1) * ∑ z ∈ Icc 1 T, (z.factorization q : ℝ) ≤ T := by
  have h1 : (q - 1) * (T.factorial).factorization q ≤ T := by
    have := Fact.mk hq
    rw [Nat.factorization_def _ hq, sub_one_mul_padicValNat_factorial]
    exact Nat.sub_le _ _
  have h2 : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
    rw [Nat.cast_sub hq.one_le]; simp
  rw [← h2, ← Nat.cast_sum, sum_factorization_Icc_eq, ← Nat.cast_mul]
  exact_mod_cast h1

lemma log_qPart {Q : Finset ℕ} (hQ : ∀ q ∈ Q, q.Prime) (z : ℕ) :
    Real.log (qPart Q z) = ∑ q ∈ Q, (z.factorization q : ℝ) * Real.log q := by
  unfold qPart
  push_cast
  rw [Real.log_prod]
  · refine Finset.sum_congr rfl fun q _ => ?_
    rw [Real.log_pow]
  · intro q hq
    exact pow_ne_zero _ (by exact_mod_cast (hQ q hq).ne_zero)

lemma one_le_qPart {Q : Finset ℕ} (hQ : ∀ q ∈ Q, q.Prime) (z : ℕ) : 1 ≤ qPart Q z := by
  unfold qPart
  rw [Nat.one_le_iff_ne_zero, Finset.prod_ne_zero_iff]
  intro q hq
  exact pow_ne_zero _ (hQ q hq).ne_zero

lemma sum_log_div_sub_one_le {y : ℝ} (hy1 : 1 ≤ y) (hy : 7 ≤ Real.log y) (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, q.Prime ∧ (q : ℝ) ≤ y) :
    ∑ q ∈ Q, Real.log q / ((q : ℝ) - 1) ≤ 4 * Real.log y := by
  calc ∑ q ∈ Q, Real.log q / ((q : ℝ) - 1)
      ≤ ∑ q ∈ Q, 2 * (Real.log q / q) := by
        refine Finset.sum_le_sum fun q hq => ?_
        have h2 : (2 : ℝ) ≤ q := by exact_mod_cast (hQ q hq).1.two_le
        have hl : 0 ≤ Real.log q := Real.log_natCast_nonneg q
        rw [div_le_iff₀ (by linarith), mul_comm, ← mul_assoc, mul_div_assoc']
        rw [le_div_iff₀ (by linarith)]
        nlinarith
    _ = 2 * ∑ q ∈ Q, Real.log q / q := by rw [Finset.mul_sum]
    _ ≤ 2 * ∑ p ∈ Ioc 0 ⌊y⌋₊ with p.Prime, Real.log p / p := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) (by norm_num)
        · intro q hq
          simp only [Finset.mem_filter, Finset.mem_Ioc]
          exact ⟨⟨(hQ q hq).1.pos, Nat.le_floor (hQ q hq).2⟩, (hQ q hq).1⟩
        · intro p _ _
          exact div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
    _ = 2 * (Real.log y + Mertens.E₁p y) := by rw [Mertens.sum_log_prime_div_eq]
    _ ≤ 4 * Real.log y := by
        have hE := Mertens.E₁p.le hy1
        have h4 : Real.log 4 ≤ 4 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
        linarith

/-- Paper Lemma 6.4. -/
theorem qPart_tail : ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ Q : Finset ℕ, (∀ q ∈ Q, q.Prime ∧ (q : ℝ) ≤ y) →
    ∀ T : ℕ, (((Icc 1 T).filter (fun z => y ^ 40 < (qPart Q z : ℝ))).card : ℝ) ≤ T / 10 := by
  refine ⟨Real.exp 7, fun y hy Q hQ T => ?_⟩
  have hy0 : 0 < y := lt_of_lt_of_le (Real.exp_pos 7) hy
  have hlog : 7 ≤ Real.log y := by
    rw [← Real.log_exp 7]; exact Real.log_le_log (Real.exp_pos 7) hy
  have hQp : ∀ q ∈ Q, q.Prime := fun q hq => (hQ q hq).1
  set F := (Icc 1 T).filter (fun z => y ^ 40 < (qPart Q z : ℝ))
  have key2 : ∑ z ∈ Icc 1 T, Real.log (qPart Q z) ≤ T * (4 * Real.log y) := by
    simp_rw [log_qPart hQp]
    rw [Finset.sum_comm]
    calc ∑ q ∈ Q, ∑ z ∈ Icc 1 T, (z.factorization q : ℝ) * Real.log q
        = ∑ q ∈ Q, Real.log q / ((q : ℝ) - 1) *
            (((q : ℝ) - 1) * ∑ z ∈ Icc 1 T, (z.factorization q : ℝ)) := by
          refine Finset.sum_congr rfl fun q hq => ?_
          have h2 : (2 : ℝ) ≤ q := by exact_mod_cast (hQp q hq).two_le
          have hne : (q : ℝ) - 1 ≠ 0 := by linarith
          rw [← Finset.sum_mul]
          field_simp
      _ ≤ ∑ q ∈ Q, Real.log q / ((q : ℝ) - 1) * T := by
          refine Finset.sum_le_sum fun q hq => ?_
          have h2 : (2 : ℝ) ≤ q := by exact_mod_cast (hQp q hq).two_le
          exact mul_le_mul_of_nonneg_left (sub_one_mul_sum_factorization_le (hQp q hq) T)
            (div_nonneg (Real.log_natCast_nonneg q) (by linarith))
      _ = T * ∑ q ∈ Q, Real.log q / ((q : ℝ) - 1) := by
          rw [← Finset.sum_mul, mul_comm]
      _ ≤ T * (4 * Real.log y) :=
          mul_le_mul_of_nonneg_left (sum_log_div_sub_one_le (le_trans (Real.one_le_exp (by norm_num)) hy) hlog Q hQ) (Nat.cast_nonneg T)
  have key3 : (F.card : ℝ) * (40 * Real.log y) ≤ ∑ z ∈ Icc 1 T, Real.log (qPart Q z) := by
    calc (F.card : ℝ) * (40 * Real.log y) = ∑ z ∈ F, 40 * Real.log y := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ z ∈ F, Real.log (qPart Q z) := by
          refine Finset.sum_le_sum fun z hz => ?_
          have hz' := (Finset.mem_filter.1 hz).2
          have : Real.log (y ^ 40) = 40 * Real.log y := by rw [Real.log_pow]; norm_num
          rw [← this]
          exact (Real.log_lt_log (by positivity) hz').le
      _ ≤ ∑ z ∈ Icc 1 T, Real.log (qPart Q z) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun z _ _ => Real.log_natCast_nonneg _)
  have hl0 : 0 < Real.log y := by linarith
  have : (F.card : ℝ) * (40 * Real.log y) ≤ (T / 10) * (40 * Real.log y) := by
    calc _ ≤ _ := key3
      _ ≤ _ := key2
      _ = _ := by ring
  exact le_of_mul_le_mul_right this (by positivity)

end OMA.Port8

end

-- ==== Lifting
section



open Finset

namespace OMA.Port8

theorem Rich.mono {A : Set ℕ} {q : ℚ} {M M' : ℕ} (h : Rich A q M) (hM : M' ≤ M) : Rich A q M' := by
  obtain ⟨S, hS, hc⟩ := h
  exact ⟨S, hS, hM.trans hc⟩

/-- The endpoint-distinctness condition of a matching, unpacked: lower endpoints are distinct,
upper endpoints are distinct, and no lower endpoint equals an upper endpoint. -/
lemma disj_iff (S : Finset (ℕ × ℕ)) :
    (S.image Prod.fst ∪ S.image Prod.snd).card = 2 * S.card ↔
      ((∀ e ∈ S, ∀ e' ∈ S, e.1 = e'.1 → e = e') ∧ (∀ e ∈ S, ∀ e' ∈ S, e.2 = e'.2 → e = e') ∧
        (∀ e ∈ S, ∀ e' ∈ S, e.1 ≠ e'.2)) := by
  constructor
  · intro h
    have h1 := card_union_add_card_inter (S.image Prod.fst) (S.image Prod.snd)
    have h2 := card_image_le (s := S) (f := Prod.fst)
    have h3 := card_image_le (s := S) (f := Prod.snd)
    have hf : (S.image Prod.fst).card = S.card := by omega
    have hs : (S.image Prod.snd).card = S.card := by omega
    have hi : (S.image Prod.fst ∩ S.image Prod.snd).card = 0 := by omega
    rw [card_image_iff] at hf hs
    rw [card_eq_zero] at hi
    refine ⟨fun e he e' he' h => hf he he' h, fun e he e' he' h => hs he he' h, ?_⟩
    intro e he e' he' h
    have : e.1 ∈ S.image Prod.fst ∩ S.image Prod.snd :=
      mem_inter.2 ⟨mem_image_of_mem _ he, h ▸ mem_image_of_mem _ he'⟩
    rw [hi] at this
    simp at this
  · rintro ⟨hf, hs, hd⟩
    rw [card_union_of_disjoint, card_image_of_injOn, card_image_of_injOn]
    · ring
    · intro e he e' he' h; exact hs e he e' he' h
    · intro e he e' he' h; exact hf e he e' he' h
    · rw [disjoint_left]
      intro z hz hz'
      obtain ⟨e, he, rfl⟩ := mem_image.1 hz
      obtain ⟨e', he', h⟩ := mem_image.1 hz'
      exact hd e he e' he' h.symm

/-- Richness is invariant under inversion of the ratio. -/
theorem Rich.inv {A : Set ℕ} {q : ℚ} {M : ℕ} (hq : q ≠ 0) (h : Rich A q M) : Rich A q⁻¹ M := by
  obtain ⟨S, hS, hc⟩ := h
  refine ⟨S.image Prod.swap, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro e he'
    obtain ⟨e, he, rfl⟩ := mem_image.1 he'
    exact ⟨(hS.mem e he).2, (hS.mem e he).1⟩
  · intro e he'
    obtain ⟨e, he, rfl⟩ := mem_image.1 he'
    simp only [Prod.fst_swap, Prod.snd_swap]
    rw [hS.ratio e he, ← mul_assoc, inv_mul_cancel₀ hq, one_mul]
  · obtain ⟨hf, hs, hd⟩ := (disj_iff S).1 hS.disj
    rw [disj_iff]
    refine ⟨?_, ?_, ?_⟩
    · intro e0 he0 e0' he0' h
      obtain ⟨e, he, rfl⟩ := mem_image.1 he0
      obtain ⟨e', he', rfl⟩ := mem_image.1 he0'
      rw [hs e he e' he' h]
    · intro e0 he0 e0' he0' h
      obtain ⟨e, he, rfl⟩ := mem_image.1 he0
      obtain ⟨e', he', rfl⟩ := mem_image.1 he0'
      rw [hf e he e' he' h]
    · intro e0 he0 e0' he0' h
      obtain ⟨e, he, rfl⟩ := mem_image.1 he0
      obtain ⟨e', he', rfl⟩ := mem_image.1 he0'
      exact hd e' he' e he h.symm
  · rw [card_image_of_injective _ Prod.swap_injective]; exact hc

/-- In a matching of size exceeding `|F|`, some pair avoids the finite set `F`. -/
lemma exists_pair_avoiding {A : Set ℕ} {q : ℚ} {S : Finset (ℕ × ℕ)} (hS : IsQMatching A q S)
    (F : Finset ℕ) (hF : F.card < S.card) : ∃ e ∈ S, e.1 ∉ F ∧ e.2 ∉ F := by
  obtain ⟨hf, hs, hd⟩ := (disj_iff S).1 hS.disj
  classical
  by_contra hcon
  push Not at hcon
  have : S.card ≤ F.card := by
    refine card_le_card_of_injOn (fun e => if e.1 ∈ F then e.1 else e.2) ?_ ?_
    · intro e he
      by_cases h1 : e.1 ∈ F
      · simp [h1]
      · simp [h1, hcon e he h1]
    · intro e he e' he' h
      simp only at h
      have he := mem_coe.1 he
      have he' := mem_coe.1 he'
      split_ifs at h with h1 h2 h2
      · exact hf e he e' he' h
      · exact absurd h (hd e he e' he')
      · exact absurd h.symm (hd e' he' e he)
      · exact hs e he e' he' h
  omega

/-- Generalised lifting: choose, for each ratio in `qs`, a pair avoiding `F` and all previously
chosen endpoints. -/
lemma lift_aux (A : Set ℕ) (N : ℕ) : ∀ (qs : List ℚ) (F : Finset ℕ),
    (∀ q ∈ qs, Rich A q N) → F.card + 2 * qs.length ≤ N + 1 →
    ∃ X Y : Finset ℕ, (↑X : Set ℕ) ⊆ A ∧ (↑Y : Set ℕ) ⊆ A ∧ Disjoint X Y ∧ Disjoint F X ∧
      Disjoint F Y ∧ X.card = qs.length ∧ Y.card = qs.length ∧
      (∏ y ∈ Y, (y : ℚ)) = qs.prod * ∏ x ∈ X, (x : ℚ) := by
  intro qs
  induction qs with
  | nil =>
    intro F _ _
    exact ⟨∅, ∅, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp⟩
  | cons q rest ih =>
    intro F hrich hcard
    obtain ⟨S, hS, hSc⟩ := hrich q (List.mem_cons_self ..)
    simp only [List.length_cons] at hcard
    obtain ⟨e, he, h1, h2⟩ := exists_pair_avoiding hS F (by omega)
    obtain ⟨hf, hs, hd⟩ := (disj_iff S).1 hS.disj
    have hxy : e.1 ≠ e.2 := hd e he e he
    obtain ⟨X, Y, hXA, hYA, hXY, hFX, hFY, hXc, hYc, hprod⟩ :=
      ih (insert e.1 (insert e.2 F)) (fun q' hq' => hrich q' (List.mem_cons_of_mem _ hq'))
        (by
          have := card_insert_le e.1 (insert e.2 F)
          have := card_insert_le e.2 F
          omega)
    simp only [disjoint_insert_left] at hFX hFY
    have hxX : e.1 ∉ X := hFX.1
    have hyY : e.2 ∉ Y := hFY.2.1
    have hxY : e.1 ∉ Y := hFY.1
    have hyX : e.2 ∉ X := hFX.2.1
    refine ⟨insert e.1 X, insert e.2 Y, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [coe_insert]; exact Set.insert_subset (hS.mem e he).1 hXA
    · rw [coe_insert]; exact Set.insert_subset (hS.mem e he).2 hYA
    · rw [disjoint_insert_left, disjoint_insert_right]
      exact ⟨by simp [hxy, hxY], hyX, hXY⟩
    · rw [disjoint_insert_right]
      exact ⟨h1, hFX.2.2⟩
    · rw [disjoint_insert_right]
      exact ⟨h2, hFY.2.2⟩
    · rw [card_insert_of_notMem hxX, hXc]; simp
    · rw [card_insert_of_notMem hyY, hYc]; simp
    · rw [prod_insert hxX, prod_insert hyY, hprod, hS.ratio e he, List.prod_cons]
      ring

/-- **Lifting lemma.** If `a ∈ A` is a product of rationals `q₁ ⋯ qₜ`, each of which has a matching
of size `2t` in `A`, then `A` contains a violation (`a·x₁⋯xₜ = y₁⋯yₜ`, all distinct). -/
theorem violation_of_word (A : Set ℕ) (h0 : 0 ∉ A) (a : ℕ) (ha : a ∈ A) (qs : List ℚ)
    (hprod : (a : ℚ) = qs.prod) (hrich : ∀ q ∈ qs, Rich A q (2 * qs.length)) : Violation A := by
  obtain ⟨X, Y, hXA, hYA, _, hFX, _, hXc, hYc, hp⟩ :=
    lift_aux A (2 * qs.length) qs {a} hrich (by simp only [card_singleton]; omega)
  have haX : a ∉ X := by
    rw [disjoint_singleton_left] at hFX; exact hFX
  refine ⟨insert a X, Y, ?_, hYA, ?_, ?_⟩
  · rw [coe_insert]; exact Set.insert_subset ha hXA
  · rw [prod_insert haX]
    have : ((a * X.prod id : ℕ) : ℚ) = ((Y.prod id : ℕ) : ℚ) := by
      push_cast
      simp only [id]
      rw [hp, hprod]
    exact_mod_cast this
  · rw [card_insert_of_notMem haX, hXc, hYc]; omega

/-- Generalised version of `rich_of_pairs`, also recording that lower endpoints lie in `L`. -/
lemma rich_of_pairs_aux (A : Set ℕ) (h0 : 0 ∉ A) (q : ℚ) (hq : 1 < q) : ∀ (n : ℕ) (L : Finset ℕ),
    L.card = n → (∀ x ∈ L, x ∈ A ∧ ∃ y ∈ A, (y : ℚ) = q * x) →
    ∃ S : Finset (ℕ × ℕ), IsQMatching A q S ∧ L.card / 3 ≤ S.card ∧ ∀ e ∈ S, e.1 ∈ L := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro L hLn hL
  rcases L.eq_empty_or_nonempty with hE | hne
  · subst hE
    refine ⟨∅, ⟨by simp, by simp, by simp⟩, by simp, by simp⟩
  classical
  set x := L.min' hne with hxdef
  have hxL : x ∈ L := min'_mem L hne
  obtain ⟨hxA, y, hyA, hy⟩ := hL x hxL
  set L' := (L.erase x).erase y with hL'
  have hL'sub : L' ⊆ L := (erase_subset _ _).trans (erase_subset _ _)
  have hL'c : L.card ≤ L'.card + 2 := by
    have h1 : (L.erase x).card - 1 ≤ L'.card := pred_card_le_card_erase
    have h2 : (L.erase x).card = L.card - 1 := card_erase_of_mem hxL
    have h3 : 0 < L.card := card_pos.2 hne
    omega
  have hL'lt : L'.card < n := by
    have : L'.card < L.card :=
      lt_of_le_of_lt (card_le_card (erase_subset _ _)) (card_erase_lt_of_mem hxL)
    omega
  obtain ⟨S', hS', hS'c, hS'L⟩ := ih _ hL'lt L' rfl (fun z hz => hL z (hL'sub hz))
  have hxpos : (0 : ℚ) < x := by
    have : x ≠ 0 := fun h => h0 (h ▸ hxA)
    exact_mod_cast Nat.pos_of_ne_zero this
  -- every lower endpoint in `L'` exceeds `x`
  have hgt : ∀ z ∈ L', x < z := by
    intro z hz
    have hz1 : z ≠ x := by
      intro h; rw [hL', mem_erase, mem_erase] at hz; exact hz.2.1 h
    exact lt_of_le_of_ne (min'_le L z (hL'sub hz)) (Ne.symm hz1)
  have hxy_lt : (x : ℚ) < y := by rw [hy]; nlinarith
  have hxy : x ≠ y := by intro h; rw [h] at hxy_lt; exact lt_irrefl _ hxy_lt
  obtain ⟨hf, hs, hd⟩ := (disj_iff S').1 hS'.disj
  have hnot : (x, y) ∉ S' := by
    intro h
    have := hS'L _ h
    exact lt_irrefl _ (hgt x this)
  refine ⟨insert (x, y) S', ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro e he
    rcases mem_insert.1 he with rfl | he
    · exact ⟨hxA, hyA⟩
    · exact hS'.mem e he
  · intro e he
    rcases mem_insert.1 he with rfl | he
    · exact hy
    · exact hS'.ratio e he
  · -- facts about pairs of `S'`
    have hlow : ∀ e ∈ S', x < e.1 ∧ e.1 ≠ y := by
      intro e he
      have h1 := hS'L e he
      refine ⟨hgt _ h1, ?_⟩
      intro h
      rw [hL', mem_erase] at h1
      exact h1.1 h
    have hup : ∀ e ∈ S', x < e.2 ∧ e.2 ≠ y := by
      intro e he
      have hl := hlow e he
      have hr := hS'.ratio e he
      have hx1 : (x : ℚ) < e.1 := by exact_mod_cast hl.1
      refine ⟨?_, ?_⟩
      · have : (x : ℚ) < e.2 := by rw [hr]; nlinarith
        exact_mod_cast this
      · intro h
        have h2 : (e.2 : ℚ) = y := by rw [h]
        rw [hr, hy] at h2
        have h3 : (e.1 : ℚ) = x := mul_left_cancel₀ (by linarith : q ≠ 0) h2
        have h4 : e.1 = x := by exact_mod_cast h3
        rw [h4] at hl
        exact lt_irrefl _ hl.1
    rw [disj_iff]
    refine ⟨?_, ?_, ?_⟩
    · intro e he e' he' h
      rcases mem_insert.1 he with rfl | he <;> rcases mem_insert.1 he' with rfl | he'
      · rfl
      · exact absurd h (ne_of_lt (hlow e' he').1)
      · exact absurd h.symm (ne_of_lt (hlow e he).1)
      · exact hf e he e' he' h
    · intro e he e' he' h
      rcases mem_insert.1 he with rfl | he <;> rcases mem_insert.1 he' with rfl | he'
      · rfl
      · exact absurd h.symm (hup e' he').2
      · exact absurd h (hup e he).2
      · exact hs e he e' he' h
    · intro e he e' he'
      rcases mem_insert.1 he with rfl | he <;> rcases mem_insert.1 he' with rfl | he'
      · exact hxy
      · exact ne_of_lt (hup e' he').1
      · exact (hlow e he).2
      · exact hd e he e' he'
  · rw [card_insert_of_notMem hnot]; omega
  · intro e he
    rcases mem_insert.1 he with rfl | he
    · exact hxL
    · exact hL'sub (hS'L e he)

/-- **Many pairs give a matching.** For a fixed ratio `q > 1`, a set `L` of lower endpoints of
`q`-pairs in `A` yields a matching of size at least `|L| / 3` (each pair meets at most two others). -/
theorem rich_of_pairs (A : Set ℕ) (h0 : 0 ∉ A) (q : ℚ) (hq : 1 < q) (L : Finset ℕ)
    (hL : ∀ x ∈ L, x ∈ A ∧ ∃ y ∈ A, (y : ℚ) = q * x) : Rich A q (L.card / 3) := by
  obtain ⟨S, hS, hc, -⟩ := rich_of_pairs_aux A h0 q hq _ L rfl hL
  exact ⟨S, hS, hc⟩

end OMA.Port8

end

-- ==== Coupling
section



open Finset

namespace OMA.Port8

lemma qPart_factorization {Q : Finset ℕ} (hQ : ∀ q ∈ Q, q.Prime) (z r : ℕ) :
    (qPart Q z).factorization r = if r ∈ Q then z.factorization r else 0 := by
  unfold qPart
  rw [Nat.factorization_prod (fun q hq => pow_ne_zero _ (hQ q hq).ne_zero)]
  rw [Finsupp.finsetSum_apply]
  rw [Finset.sum_congr rfl (fun q hq => by rw [(hQ q hq).factorization_pow])]
  simp only [Finsupp.single_apply]
  rw [Finset.sum_ite_eq']

lemma qPart_ne_zero {Q : Finset ℕ} (hQ : ∀ q ∈ Q, q.Prime) (z : ℕ) : qPart Q z ≠ 0 := by
  unfold qPart
  rw [Finset.prod_ne_zero_iff]
  intro q hq
  exact pow_ne_zero _ (hQ q hq).ne_zero

lemma qPart_dvd {Q : Finset ℕ} (hQ : ∀ q ∈ Q, q.Prime) {z : ℕ} (hz : z ≠ 0) : qPart Q z ∣ z := by
  rw [← Nat.factorization_le_iff_dvd (qPart_ne_zero hQ z) hz]
  intro r
  rw [qPart_factorization hQ]
  split_ifs <;> simp

lemma qPart_mem {Q : Finset ℕ} (hQ : ∀ q ∈ Q, q.Prime) (z : ℕ) : qPart Q z ∈ Nat.factoredNumbers Q := by
  rw [Nat.mem_factoredNumbers']
  intro r hr hdvd
  have hpos := hr.factorization_pos_of_dvd (qPart_ne_zero hQ z) hdvd
  rw [qPart_factorization hQ] at hpos
  by_contra h
  simp [h] at hpos

lemma qPart_of_mem {Q : Finset ℕ} (hQ : ∀ q ∈ Q, q.Prime) {m : ℕ} (hm : m ∈ Nat.factoredNumbers Q) :
    qPart Q m = m := by
  apply Nat.eq_of_factorization_eq (qPart_ne_zero hQ m) (Nat.ne_zero_of_mem_factoredNumbers hm)
  intro r
  rw [qPart_factorization hQ]
  split_ifs with h
  · rfl
  · symm
    by_contra h0
    have hr : r.Prime := Nat.prime_of_mem_primeFactors (Nat.support_factorization m ▸ Finsupp.mem_support_iff.2 h0)
    have hd : r ∣ m := Nat.dvd_of_mem_primeFactors (Nat.support_factorization m ▸ Finsupp.mem_support_iff.2 h0)
    exact h (Nat.mem_factoredNumbers'.1 hm r hr hd)

lemma qPart_mul (Q : Finset ℕ) {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    qPart Q (a * b) = qPart Q a * qPart Q b := by
  unfold qPart
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun q _ => ?_
  rw [Nat.factorization_mul ha hb, Finsupp.add_apply, pow_add]

lemma qPart_div_qPart {Q : Finset ℕ} (hQ : ∀ q ∈ Q, q.Prime) {z : ℕ} (hz : z ≠ 0) :
    qPart Q (z / qPart Q z) = 1 := by
  have hd := qPart_dvd hQ hz
  show ∏ q ∈ Q, q ^ (z / qPart Q z).factorization q = 1
  refine Finset.prod_eq_one fun q hq => ?_
  have : (z / qPart Q z).factorization q = 0 := by
    rw [Nat.factorization_div hd, Finsupp.tsub_apply, qPart_factorization hQ, if_pos hq]
    simp
  rw [this, pow_zero]

lemma qPart_mul_div_eq {Q : Finset ℕ} (hQ : ∀ q ∈ Q, q.Prime) {z : ℕ} (hz : z ≠ 0) :
    qPart Q z * (z / qPart Q z) = z :=
  Nat.mul_div_cancel' (qPart_dvd hQ hz)

lemma div_qPart_ne_zero {Q : Finset ℕ} (hQ : ∀ q ∈ Q, q.Prime) {z : ℕ} (hz : z ≠ 0) :
    z / qPart Q z ≠ 0 := by
  intro h
  have := qPart_mul_div_eq hQ hz
  rw [h, mul_zero] at this
  exact hz this.symm

lemma qPart_smooth_mul {Q : Finset ℕ} (hQ : ∀ q ∈ Q, q.Prime) {m z : ℕ}
    (hm : m ∈ Nat.factoredNumbers Q) (hz : z ≠ 0) : qPart Q (m * (z / qPart Q z)) = m := by
  rw [qPart_mul Q (Nat.ne_zero_of_mem_factoredNumbers hm) (div_qPart_ne_zero hQ hz),
    qPart_div_qPart hQ hz, qPart_of_mem hQ hm, mul_one]


/-- Paper Lemma 6.6, counting form.
* `A ⊆ [1,N]`, `E = [1,N] \ A`, `p` prime, `p ∉ Q`, `Q` a finite set of primes, `2p ≤ N`, `T = N / p`;
* (tail) at most `T/10` of `z ∈ [1,T]` have `qPart Q z > K`;
* (nonheavy) `16 p |E ∩ pℕ| < N`;
* (reservoir) for every `Q`-smooth `1 ≤ k ≤ K`, the set `M_k` of `Q`-smooth `m` with `pk ≤ 2m ≤ 2pk`
  has at least `γ p k` elements;
* (small deficit) `32 |E| ≤ γ N`.
Then some `Q`-smooth `k ≤ K`, `m` with `pk ≤ 2m`, `m < pk` admit at least `T / (2K)` values `u` with
`m u ∈ A` and `p k u ∈ A`. -/
theorem core_pairs (N p K : ℕ) (γ : ℝ) (hγ : 0 < γ) (A : Finset ℕ) (hA : A ⊆ Icc 1 N)
    (Q : Finset ℕ) (hQ : ∀ q ∈ Q, q.Prime) (hp : p.Prime) (hpQ : p ∉ Q) (hpN : 2 * p ≤ N) (hK : 1 ≤ K)
    (htail : (((Icc 1 (N / p)).filter (fun z => K < qPart Q z)).card : ℝ) ≤ (N / p : ℕ) / 10)
    (hnonheavy : 16 * p * ((Icc 1 N \ A).filter (fun n => p ∣ n)).card < N)
    (hres : ∀ k ∈ Nat.factoredNumbers Q, 1 ≤ k → k ≤ K →
      γ * p * k ≤ (((Icc 1 (p * k)).filter (fun m => m ∈ Nat.factoredNumbers Q ∧ p * k ≤ 2 * m)).card : ℝ))
    (hdef : 32 * ((Icc 1 N \ A).card : ℝ) ≤ γ * N) :
    ∃ k m : ℕ, k ∈ Nat.factoredNumbers Q ∧ m ∈ Nat.factoredNumbers Q ∧ 1 ≤ k ∧ k ≤ K ∧
      p * k ≤ 2 * m ∧ m < p * k ∧
      ∃ U : Finset ℕ, ((N / p : ℕ) : ℝ) / (2 * K) ≤ U.card ∧ ∀ u ∈ U, m * u ∈ A ∧ p * k * u ∈ A := by
  obtain ⟨M, hM⟩ : ∃ M : ℕ → Finset ℕ, ∀ k, M k =
      (Icc 1 (p * k)).filter (fun m => m ∈ Nat.factoredNumbers Q ∧ p * k ≤ 2 * m) :=
    ⟨_, fun _ => rfl⟩
  have hres' : ∀ k ∈ Nat.factoredNumbers Q, 1 ≤ k → k ≤ K → γ * p * k ≤ ((M k).card : ℝ) := by
    intro k h1 h2 h3; rw [hM]; exact hres k h1 h2 h3
  set T := N / p with hT
  have hp0 : 0 < p := hp.pos
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  have hT2 : 2 ≤ T := (Nat.le_div_iff_mul_le hp0).2 (by linarith)
  have hTN : p * T ≤ N := Nat.mul_div_le N p
  have hNT : N < p * (T + 1) := Nat.lt_mul_div_succ N hp0
  have hγp : 0 < γ * p := mul_pos hγ hpR
  set E := Icc 1 N \ A with hE
  set G := (Icc 1 T).filter (fun z => qPart Q z ≤ K) with hG
  have hGmem : ∀ z ∈ G, 1 ≤ z ∧ z ≤ T ∧ qPart Q z ≤ K := by
    intro z hz
    simp only [hG, Finset.mem_filter, Finset.mem_Icc] at hz
    exact ⟨hz.1.1, hz.1.2, hz.2⟩
  have hk1 : ∀ z, (1 : ℝ) ≤ qPart Q z := fun z => by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (qPart_ne_zero hQ z)
  have hcG : ∀ z ∈ G, γ * p * (qPart Q z) ≤ ((M (qPart Q z)).card : ℝ) := by
    intro z hz
    exact hres' _ (qPart_mem hQ z) (Nat.one_le_iff_ne_zero.2 (qPart_ne_zero hQ z)) (hGmem z hz).2.2
  have hcpos : ∀ z ∈ G, 0 < ((M (qPart Q z)).card : ℝ) := by
    intro z hz
    have := hcG z hz
    have : 0 < γ * p * (qPart Q z : ℝ) := mul_pos hγp (by linarith [hk1 z])
    linarith
  -- size of G
  have hGcard : (T : ℝ) - T / 10 ≤ G.card := by
    have h := Finset.card_filter_add_card_filter_not (s := Icc 1 T) (fun z => qPart Q z ≤ K)
    have h2 : ((Icc 1 T).filter (fun z => ¬ qPart Q z ≤ K)) =
        (Icc 1 T).filter (fun z => K < qPart Q z) := by
      apply Finset.filter_congr; intro z _; exact not_le
    rw [h2, Nat.card_Icc] at h
    have h3 : (G.card : ℝ) + (((Icc 1 T).filter (fun z => K < qPart Q z)).card : ℝ) = T := by
      norm_cast
    linarith
  -- failure (b)
  have hFb : 16 * ((G.filter (fun z => p * z ∉ A)).card) ≤ T := by
    have hinj : (G.filter (fun z => p * z ∉ A)).card ≤ (E.filter (fun n => p ∣ n)).card := by
      apply Finset.card_le_card_of_injOn (fun z => p * z)
      · intro z hz
        simp only [Finset.mem_coe, Finset.mem_filter] at hz ⊢
        obtain ⟨h1, h2, -⟩ := hGmem z hz.1
        simp only [hE, Finset.mem_sdiff, Finset.mem_Icc]
        refine ⟨⟨⟨?_, ?_⟩, hz.2⟩, dvd_mul_right p z⟩
        · nlinarith
        · calc p * z ≤ p * T := Nat.mul_le_mul_left p h2
            _ ≤ N := hTN
      · intro z _ z' _ h
        exact Nat.eq_of_mul_eq_mul_left hp0 h
    have h1 : p * (16 * (G.filter (fun z => p * z ∉ A)).card) < p * (T + 1) := by
      calc p * (16 * (G.filter (fun z => p * z ∉ A)).card)
          = 16 * p * (G.filter (fun z => p * z ∉ A)).card := by ring
        _ ≤ 16 * p * (E.filter (fun n => p ∣ n)).card := Nat.mul_le_mul_left _ hinj
        _ < N := hnonheavy
        _ < p * (T + 1) := hNT
    have := Nat.lt_of_mul_lt_mul_left h1
    omega
  -- failure (c), per point of E
  have hper : ∀ b ∈ E, ∑ z ∈ G, ∑ m ∈ M (qPart Q z),
      (if b = m * (z / qPart Q z) then 1 / ((M (qPart Q z)).card : ℝ) else 0) ≤ 3 / (γ * p) := by
    intro b _
    obtain ⟨m₀, hm₀⟩ : ∃ m₀, m₀ = qPart Q b := ⟨_, rfl⟩
    have hm₀0 : m₀ ≠ 0 := hm₀ ▸ qPart_ne_zero hQ b
    obtain ⟨x, hx⟩ : ∃ x : ℝ, x = (m₀ : ℝ) / p := ⟨_, rfl⟩
    have hx0 : 0 ≤ x := by rw [hx]; positivity
    obtain ⟨Z, hZ⟩ : ∃ Z : Finset ℕ,
        Z = G.filter (fun z => m₀ ∈ M (qPart Q z) ∧ b = m₀ * (z / qPart Q z)) := ⟨_, rfl⟩
    have step1 : ∑ z ∈ G, ∑ m ∈ M (qPart Q z),
        (if b = m * (z / qPart Q z) then 1 / ((M (qPart Q z)).card : ℝ) else 0)
        = ∑ z ∈ Z, 1 / ((M (qPart Q z)).card : ℝ) := by
      rw [hZ, Finset.sum_filter (s := G)]
      refine Finset.sum_congr rfl fun z hz => ?_
      have hz0 : z ≠ 0 := by have := (hGmem z hz).1; omega
      rw [ite_and, ← Finset.sum_ite_eq' (M (qPart Q z)) m₀
        (fun _ => if b = m₀ * (z / qPart Q z) then 1 / ((M (qPart Q z)).card : ℝ) else 0)]
      refine Finset.sum_congr rfl fun m hm => ?_
      have hmF : m ∈ Nat.factoredNumbers Q := by
        rw [hM] at hm; exact (Finset.mem_filter.1 hm).2.1
      by_cases hmm : m = m₀
      · rw [if_pos hmm, hmm]
      · rw [if_neg hmm, if_neg]
        intro hbm
        apply hmm
        rw [hm₀, hbm, qPart_smooth_mul hQ hmF hz0]
    have hmx : 0 < max 1 x := lt_of_lt_of_le one_pos (le_max_left _ _)
    have step2 : ∑ z ∈ Z, 1 / ((M (qPart Q z)).card : ℝ) ≤ Z.card * (1 / (γ * p * max 1 x)) := by
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      refine Finset.sum_le_sum fun z hz => ?_
      rw [hZ, Finset.mem_filter] at hz
      obtain ⟨hzG, hmem, -⟩ := hz
      rw [hM, Finset.mem_filter, Finset.mem_Icc] at hmem
      have hkx : x ≤ qPart Q z := by
        rw [hx, div_le_iff₀ hpR]
        have : (m₀ : ℝ) ≤ p * qPart Q z := by exact_mod_cast hmem.1.2
        linarith
      apply one_div_le_one_div_of_le (mul_pos hγp hmx)
      calc γ * p * max 1 x ≤ γ * p * qPart Q z :=
            mul_le_mul_of_nonneg_left (max_le (hk1 z) hkx) hγp.le
        _ ≤ _ := hcG z hzG
    have step3 : (Z.card : ℝ) ≤ x + 2 := by
      have hcard : Z.card ≤ (Icc (m₀ / p) (2 * m₀ / p)).card := by
        apply Finset.card_le_card_of_injOn (fun z => qPart Q z)
        · intro z hz
          simp only [Finset.mem_coe, hZ, Finset.mem_filter] at hz
          obtain ⟨-, hmem, -⟩ := hz
          rw [hM, Finset.mem_filter, Finset.mem_Icc] at hmem
          simp only [Finset.mem_coe, Finset.mem_Icc]
          constructor
          · calc m₀ / p ≤ (p * qPart Q z) / p := Nat.div_le_div_right hmem.1.2
              _ = qPart Q z := Nat.mul_div_cancel_left _ hp0
          · exact (Nat.le_div_iff_mul_le hp0).2 (by rw [mul_comm]; exact hmem.2.2)
        · intro z hz z' hz' hzz
          simp only [Finset.mem_coe, hZ, Finset.mem_filter] at hz hz'
          have hz0 : z ≠ 0 := by have := (hGmem z hz.1).1; omega
          have hz0' : z' ≠ 0 := by have := (hGmem z' hz'.1).1; omega
          have hu : z / qPart Q z = z' / qPart Q z' :=
            Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hm₀0) (hz.2.2.symm.trans hz'.2.2)
          simp only at hzz
          calc z = qPart Q z * (z / qPart Q z) := (qPart_mul_div_eq hQ hz0).symm
            _ = qPart Q z' * (z' / qPart Q z') := by rw [hu, hzz]
            _ = z' := qPart_mul_div_eq hQ hz0'
      rw [Nat.card_Icc] at hcard
      have ha : (m₀ : ℝ) / p - 1 ≤ ((m₀ / p : ℕ) : ℝ) := by
        have h := Nat.lt_mul_div_succ m₀ hp0
        have h' : (m₀ : ℝ) < p * (((m₀ / p : ℕ) : ℝ) + 1) := by exact_mod_cast h
        rw [div_sub_one hpR.ne', div_le_iff₀ hpR]
        linarith
      have hc : ((2 * m₀ / p : ℕ) : ℝ) ≤ 2 * ((m₀ : ℝ) / p) := by
        have := Nat.cast_div_le (m := 2 * m₀) (n := p) (α := ℝ)
        push_cast at this
        rw [mul_div_assoc] at this
        exact this
      rcases le_total (m₀ / p) (2 * m₀ / p + 1) with h | h
      · have h4 : ((Z.card : ℕ) : ℝ) ≤ ((2 * m₀ / p + 1 - m₀ / p : ℕ) : ℝ) := by exact_mod_cast hcard
        rw [Nat.cast_sub h] at h4
        push_cast at h4
        rw [hx]
        linarith
      · rw [Nat.sub_eq_zero_of_le h, Nat.le_zero] at hcard
        rw [hcard]
        simp only [Nat.cast_zero]
        linarith
    have hx3 : x + 2 ≤ 3 * max 1 x := by
      rcases le_total x 1 with h | h
      · rw [max_eq_left h]; linarith
      · rw [max_eq_right h]; linarith
    rw [step1]
    calc _ ≤ _ := step2
      _ ≤ (x + 2) * (1 / (γ * p * max 1 x)) :=
          mul_le_mul_of_nonneg_right step3 (one_div_pos.2 (mul_pos hγp hmx)).le
      _ ≤ 3 / (γ * p) := by
          rw [mul_one_div, div_le_div_iff₀ (mul_pos hγp hmx) hγp]
          have := mul_le_mul_of_nonneg_left hx3 hγp.le
          nlinarith
  -- failure (c), total
  have hFc : ∑ z ∈ G, (((M (qPart Q z)).filter (fun m => m * (z / qPart Q z) ∉ A)).card : ℝ)
      / (M (qPart Q z)).card ≤ E.card * (3 / (γ * p)) := by
    calc _ ≤ ∑ z ∈ G, ∑ m ∈ M (qPart Q z), ∑ b ∈ E,
          (if b = m * (z / qPart Q z) then 1 / ((M (qPart Q z)).card : ℝ) else 0) := by
          refine Finset.sum_le_sum fun z hz => ?_
          have hz0 : z ≠ 0 := by have := (hGmem z hz).1; omega
          have hzT := (hGmem z hz).2.1
          rw [← Finset.sum_boole, Finset.sum_div]
          refine Finset.sum_le_sum fun m hm => ?_
          rw [Finset.sum_ite_eq']
          have hmM := hm
          rw [hM, Finset.mem_filter, Finset.mem_Icc] at hmM
          by_cases hA' : m * (z / qPart Q z) ∈ A
          · rw [if_neg (not_not.2 hA'), zero_div]
            split_ifs <;> positivity
          · have hEm : m * (z / qPart Q z) ∈ E := by
              simp only [hE, Finset.mem_sdiff, Finset.mem_Icc]
              refine ⟨⟨?_, ?_⟩, hA'⟩
              · have := Nat.pos_of_ne_zero (div_qPart_ne_zero hQ hz0)
                nlinarith [hmM.1.1]
              · calc m * (z / qPart Q z) ≤ (p * qPart Q z) * (z / qPart Q z) :=
                      Nat.mul_le_mul_right _ hmM.1.2
                  _ = p * z := by rw [mul_assoc, qPart_mul_div_eq hQ hz0]
                  _ ≤ p * T := Nat.mul_le_mul_left p hzT
                  _ ≤ N := hTN
            rw [if_pos hA', if_pos hEm]
      _ = ∑ b ∈ E, ∑ z ∈ G, ∑ m ∈ M (qPart Q z),
          (if b = m * (z / qPart Q z) then 1 / ((M (qPart Q z)).card : ℝ) else 0) :=
          (Finset.sum_congr rfl fun z _ => Finset.sum_comm).trans Finset.sum_comm
      _ ≤ ∑ b ∈ E, 3 / (γ * p) := Finset.sum_le_sum hper
      _ = E.card * (3 / (γ * p)) := by rw [Finset.sum_const, nsmul_eq_mul]
  -- pointwise lower bound for the success weight
  have hlow : ∀ z ∈ G, 1 - (if p * z ∉ A then (1 : ℝ) else 0)
      - (((M (qPart Q z)).filter (fun m => m * (z / qPart Q z) ∉ A)).card : ℝ) / (M (qPart Q z)).card
      ≤ (((M (qPart Q z)).filter (fun m => m * (z / qPart Q z) ∈ A ∧ p * z ∈ A)).card : ℝ)
        / (M (qPart Q z)).card := by
    intro z hz
    have hc := hcpos z hz
    by_cases hpz : p * z ∈ A
    · have hsplit := Finset.card_filter_add_card_filter_not (s := M (qPart Q z))
        (fun m => m * (z / qPart Q z) ∈ A)
      have hf : (M (qPart Q z)).filter (fun m => m * (z / qPart Q z) ∈ A ∧ p * z ∈ A)
          = (M (qPart Q z)).filter (fun m => m * (z / qPart Q z) ∈ A) := by
        apply Finset.filter_congr; intro m _; simp [hpz]
      rw [hf, if_neg (not_not.2 hpz)]
      have h2 : (((M (qPart Q z)).filter (fun m => m * (z / qPart Q z) ∈ A)).card : ℝ)
          + (((M (qPart Q z)).filter (fun m => m * (z / qPart Q z) ∉ A)).card : ℝ)
          = (M (qPart Q z)).card := by exact_mod_cast hsplit
      have h3 : (((M (qPart Q z)).filter (fun m => m * (z / qPart Q z) ∈ A)).card : ℝ)
            / (M (qPart Q z)).card
          + (((M (qPart Q z)).filter (fun m => m * (z / qPart Q z) ∉ A)).card : ℝ)
            / (M (qPart Q z)).card = 1 := by
        rw [← add_div, h2, div_self hc.ne']
      linarith
    · rw [if_pos hpz]
      have : 0 ≤ (((M (qPart Q z)).filter (fun m => m * (z / qPart Q z) ∉ A)).card : ℝ)
          / (M (qPart Q z)).card := by positivity
      have : 0 ≤ (((M (qPart Q z)).filter (fun m => m * (z / qPart Q z) ∈ A ∧ p * z ∈ A)).card : ℝ)
          / (M (qPart Q z)).card := by positivity
      linarith
  have hSlow : (G.card : ℝ) - (G.filter (fun z => p * z ∉ A)).card
      - ∑ z ∈ G, (((M (qPart Q z)).filter (fun m => m * (z / qPart Q z) ∉ A)).card : ℝ)
          / (M (qPart Q z)).card
      ≤ ∑ z ∈ G, (((M (qPart Q z)).filter (fun m => m * (z / qPart Q z) ∈ A ∧ p * z ∈ A)).card : ℝ)
          / (M (qPart Q z)).card := by
    calc _ = ∑ z ∈ G, (1 - (if p * z ∉ A then (1 : ℝ) else 0)
          - (((M (qPart Q z)).filter (fun m => m * (z / qPart Q z) ∉ A)).card : ℝ)
            / (M (qPart Q z)).card) := by
          rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_boole,
            nsmul_eq_mul, mul_one]
      _ ≤ _ := Finset.sum_le_sum hlow
  -- the conclusion, by contradiction
  by_contra hcon
  obtain ⟨Ks, hKs⟩ : ∃ Ks : Finset ℕ, Ks = (Icc 1 K).filter (fun k => k ∈ Nat.factoredNumbers Q) :=
    ⟨_, rfl⟩
  have hsmall : ∀ k ∈ Ks, ∀ m ∈ M k,
      ((G.filter (fun z => qPart Q z = k ∧ m * (z / k) ∈ A ∧ p * z ∈ A)).card : ℝ) < T / (2 * K) := by
    intro k hk m hm
    by_contra hge
    replace hge := not_lt.1 hge
    apply hcon
    rw [hKs, Finset.mem_filter, Finset.mem_Icc] at hk
    have hm' := hm
    rw [hM, Finset.mem_filter, Finset.mem_Icc] at hm'
    have hdz : ∀ z ∈ G.filter (fun z => qPart Q z = k ∧ m * (z / k) ∈ A ∧ p * z ∈ A), k ∣ z := by
      intro z hz
      rw [Finset.mem_filter] at hz
      have hz0 : z ≠ 0 := by have := (hGmem z hz.1).1; omega
      rw [← hz.2.1]; exact qPart_dvd hQ hz0
    refine ⟨k, m, hk.2, hm'.2.1, hk.1.1, hk.1.2, hm'.2.2, ?_,
      (G.filter (fun z => qPart Q z = k ∧ m * (z / k) ∈ A ∧ p * z ∈ A)).image (fun z => z / k), ?_, ?_⟩
    · refine lt_of_le_of_ne hm'.1.2 ?_
      intro hmk
      apply hpQ
      exact Nat.mem_factoredNumbers'.1 hm'.2.1 p hp (by rw [hmk]; exact dvd_mul_right p k)
    · rw [Finset.card_image_of_injOn]
      · exact hge
      · intro z hz z' hz' h
        have h1 := hdz z hz
        have h2 := hdz z' hz'
        simp only at h
        calc z = k * (z / k) := (Nat.mul_div_cancel' h1).symm
          _ = k * (z' / k) := by rw [h]
          _ = z' := Nat.mul_div_cancel' h2
    · intro u hu
      rw [Finset.mem_image] at hu
      obtain ⟨z, hz, rfl⟩ := hu
      have h1 := hdz z hz
      rw [Finset.mem_filter] at hz
      refine ⟨hz.2.2.1, ?_⟩
      rw [mul_assoc, Nat.mul_div_cancel' h1]
      exact hz.2.2.2
  have hKpos : ∀ k ∈ Ks, 0 < ((M k).card : ℝ) := by
    intro k hk
    rw [hKs, Finset.mem_filter, Finset.mem_Icc] at hk
    have := hres' k hk.2 hk.1.1 hk.1.2
    have h1 : (1 : ℝ) ≤ k := by exact_mod_cast hk.1.1
    have : 0 < γ * p * (k : ℝ) := mul_pos hγp (by linarith)
    linarith
  have hmaps : ∀ z ∈ G, qPart Q z ∈ Ks := by
    intro z hz
    rw [hKs, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨Nat.one_le_iff_ne_zero.2 (qPart_ne_zero hQ z), (hGmem z hz).2.2⟩, qPart_mem hQ z⟩
  have hKsK : (Ks.card : ℝ) ≤ K := by
    have : Ks.card ≤ K := by
      rw [hKs]
      calc _ ≤ (Icc 1 K).card := Finset.card_filter_le _ _
        _ = K := by simp
    exact_mod_cast this
  have hSup : ∑ z ∈ G, (((M (qPart Q z)).filter (fun m => m * (z / qPart Q z) ∈ A ∧ p * z ∈ A)).card : ℝ)
      / (M (qPart Q z)).card ≤ T / 2 := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    calc _ = ∑ k ∈ Ks, (∑ m ∈ M k,
          ((G.filter (fun z => qPart Q z = k ∧ m * (z / k) ∈ A ∧ p * z ∈ A)).card : ℝ))
            / (M k).card := by
          refine Finset.sum_congr rfl fun k _ => ?_
          have e1 : ∑ z ∈ G.filter (fun z => qPart Q z = k),
              (((M (qPart Q z)).filter (fun m => m * (z / qPart Q z) ∈ A ∧ p * z ∈ A)).card : ℝ)
                / (M (qPart Q z)).card
              = ∑ z ∈ G.filter (fun z => qPart Q z = k),
                (((M k).filter (fun m => m * (z / k) ∈ A ∧ p * z ∈ A)).card : ℝ) / (M k).card :=
            Finset.sum_congr rfl fun z hz => by rw [(Finset.mem_filter.1 hz).2]
          have e2 : ∑ z ∈ G.filter (fun z => qPart Q z = k),
                ((M k).filter (fun m => m * (z / k) ∈ A ∧ p * z ∈ A)).card
              = ∑ m ∈ M k, (G.filter (fun z => qPart Q z = k ∧ m * (z / k) ∈ A ∧ p * z ∈ A)).card := by
            simp only [Finset.card_filter]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun m _ => ?_
            rw [Finset.sum_filter]
            refine Finset.sum_congr rfl fun z _ => ?_
            by_cases h : qPart Q z = k <;> simp [h]
          rw [e1, ← Finset.sum_div]
          congr 1
          exact_mod_cast e2
      _ ≤ ∑ k ∈ Ks, (∑ m ∈ M k, ((T : ℝ) / (2 * K))) / (M k).card := by
          refine Finset.sum_le_sum fun k hk => ?_
          apply div_le_div_of_nonneg_right _ (hKpos k hk).le
          exact Finset.sum_le_sum fun m hm => (hsmall k hk m hm).le
      _ = ∑ k ∈ Ks, ((T : ℝ) / (2 * K)) := by
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [Finset.sum_const, nsmul_eq_mul, mul_div_right_comm, div_self (hKpos k hk).ne', one_mul]
      _ = Ks.card * ((T : ℝ) / (2 * K)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ K * ((T : ℝ) / (2 * K)) :=
          mul_le_mul_of_nonneg_right hKsK (by positivity)
      _ = T / 2 := by
          have : (K : ℝ) ≠ 0 := by have : (1 : ℝ) ≤ K := by exact_mod_cast hK
                                   linarith
          field_simp
  -- numerics
  have hTR : (2 : ℝ) ≤ T := by exact_mod_cast hT2
  have hFbR : 16 * (((G.filter (fun z => p * z ∉ A)).card : ℕ) : ℝ) ≤ T := by exact_mod_cast hFb
  have hNTR : (N : ℝ) < p * (T + 1) := by exact_mod_cast hNT
  have hEc : E.card * (3 / (γ * p)) ≤ 3 * (T + 1) / 32 := by
    rw [mul_div_assoc', div_le_div_iff₀ hγp (by norm_num)]
    have : (E.card : ℝ) * 32 ≤ γ * N := by linarith
    nlinarith
  linarith

end OMA.Port8

end

-- ==== Words
section



open Finset Real

namespace OMA.Port8

/-- Product of the entrywise inverses of a list of rationals. -/
lemma prod_map_inv_rat (l : List ℚ) : (l.map (·⁻¹)).prod = l.prod⁻¹ := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.prod_cons, ih, mul_comm]

/-- Words for all prime factors of `v` (of length `≤ log q · L`) concatenate to a word for `v` of
length `≤ log v · L`. -/
lemma word_of_factors (R : ℚ → Prop) (Q : ℕ → Prop) (L : ℝ)
    (hQ : ∀ q, q.Prime → Q q → ∃ w : List ℚ, w.prod = q ∧ (∀ x ∈ w, R x) ∧
      (w.length : ℝ) ≤ Real.log q * L) :
    ∀ v : ℕ, v ≠ 0 → (∀ q ∈ v.primeFactors, Q q) →
      ∃ w : List ℚ, w.prod = v ∧ (∀ x ∈ w, R x) ∧ (w.length : ℝ) ≤ Real.log v * L := by
  intro v
  induction v using Nat.recOnMul with
  | zero => intro h; exact absurd rfl h
  | one => intro _ _; exact ⟨[], by simp, by simp, by simp⟩
  | prime p hp =>
    intro _ h
    exact hQ p hp (h p (Nat.mem_primeFactors.2 ⟨hp, dvd_rfl, hp.ne_zero⟩))
  | mul a b iha ihb =>
    intro hab h
    have ha : a ≠ 0 := left_ne_zero_of_mul hab
    have hb : b ≠ 0 := right_ne_zero_of_mul hab
    rw [Nat.primeFactors_mul ha hb] at h
    obtain ⟨wa, hwa, hRa, hla⟩ := iha ha (fun q hq => h q (Finset.mem_union_left _ hq))
    obtain ⟨wb, hwb, hRb, hlb⟩ := ihb hb (fun q hq => h q (Finset.mem_union_right _ hq))
    refine ⟨wa ++ wb, ?_, ?_, ?_⟩
    · rw [List.prod_append, hwa, hwb]; push_cast; ring
    · intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact hRa x hx
      · exact hRb x hx
    · rw [List.length_append]
      push_cast
      rw [Real.log_mul (by exact_mod_cast ha) (by exact_mod_cast hb)]
      linarith

/-- Paper Lemma 6.7, abstract form. `good` is the set of admissible primes (nonheavy, `≤ P`).
Small primes (`≤ p₀`) are rich; every good prime `p > p₀` has a replacement `p = (pk/m)·m·k⁻¹`
with `pk/m` rich, `k, m` composed of good primes `q` with `q^16 ≤ p`, `k ≤ p^(5/2)`, `m ≤ pk`.
Then every good prime is a product of at most `16 (log p)^2` rich ratios (or their inverses). -/
theorem short_word (A : Set ℕ) (M p₀ : ℕ) (good : ℕ → Prop)
    (hsmall : ∀ p, p.Prime → p ≤ p₀ → Rich A p M)
    (hstep : ∀ p, p.Prime → good p → p₀ < p → ∃ k m : ℕ, 1 ≤ k ∧ 1 ≤ m ∧
      (∀ q ∈ k.primeFactors, good q ∧ q ^ 16 ≤ p) ∧ (∀ q ∈ m.primeFactors, good q ∧ q ^ 16 ≤ p) ∧
      (k : ℝ) ^ 2 ≤ (p : ℝ) ^ 5 ∧ m ≤ p * k ∧ Rich A ((p * k : ℕ) / (m : ℚ)) M) :
    ∀ p, p.Prime → (good p ∨ p ≤ p₀) →
      ∃ w : List ℚ, w.prod = p ∧ (∀ q ∈ w, Rich A q M) ∧ (w.length : ℝ) ≤ 16 * (Real.log p) ^ 2 := by
  -- strengthened statement: all entries are also nonzero
  have key : ∀ p, p.Prime → (good p ∨ p ≤ p₀) →
      ∃ w : List ℚ, w.prod = p ∧ (∀ q ∈ w, Rich A q M ∧ q ≠ 0) ∧
        (w.length : ℝ) ≤ 16 * (Real.log p) ^ 2 := by
    intro p
    induction p using Nat.strong_induction_on with
    | _ p ih =>
    intro hp hgp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hlogp : 0.6931471803 < Real.log p :=
      lt_of_lt_of_le Real.log_two_gt_d9 (Real.log_le_log (by norm_num) hp2)
    by_cases hsm : p ≤ p₀
    · refine ⟨[(p : ℚ)], by simp, ?_, ?_⟩
      · intro q hq
        rw [List.mem_singleton] at hq
        subst hq
        exact ⟨hsmall p hp hsm, by exact_mod_cast hp.ne_zero⟩
      · simp only [List.length_singleton, Nat.cast_one]
        nlinarith
    have hgood : good p := hgp.resolve_right hsm
    obtain ⟨k, m, hk1, hm1, hkf, hmf, hk2, hmk, hr⟩ := hstep p hp hgood (by omega)
    -- words for the small prime factors, with length `≤ log q · log p`
    have hQ : ∀ q, q.Prime → (good q ∧ q ^ 16 ≤ p) →
        ∃ w : List ℚ, w.prod = q ∧ (∀ x ∈ w, Rich A x M ∧ x ≠ 0) ∧
          (w.length : ℝ) ≤ Real.log q * Real.log p := by
      rintro q hq ⟨hgq, hq16⟩
      have hqlt : q < p := by
        have : q ^ 1 < q ^ 16 := Nat.pow_lt_pow_right hq.one_lt (by norm_num)
        rw [pow_one] at this
        omega
      obtain ⟨w, hw, hR, hl⟩ := ih q hqlt hq (Or.inl hgq)
      refine ⟨w, hw, hR, hl.trans ?_⟩
      have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq.one_lt.le
      have hlq : 0 ≤ Real.log q := Real.log_nonneg hq1
      have h16 : 16 * Real.log q ≤ Real.log p := by
        have : ((q : ℝ) ^ 16) ≤ p := by exact_mod_cast hq16
        have := Real.log_le_log (by positivity) this
        rw [Real.log_pow] at this
        push_cast at this
        linarith
      nlinarith
    obtain ⟨wk, hwk, hRk, hlk⟩ := word_of_factors _ _ _ hQ k (by omega) hkf
    obtain ⟨wm, hwm, hRm, hlm⟩ := word_of_factors _ _ _ hQ m (by omega) hmf
    have hkpos : (0 : ℚ) < k := by exact_mod_cast hk1
    have hmpos : (0 : ℚ) < m := by exact_mod_cast hm1
    have hppos : (0 : ℚ) < p := by exact_mod_cast hp.pos
    refine ⟨[((p * k : ℕ) : ℚ) / (m : ℚ)] ++ wm ++ wk.map (·⁻¹), ?_, ?_, ?_⟩
    · rw [List.prod_append, List.prod_append, prod_map_inv_rat, hwm, hwk]
      simp only [List.prod_singleton]
      push_cast
      field_simp
    · intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · rcases List.mem_append.1 hx with hx | hx
        · rw [List.mem_singleton] at hx
          subst hx
          refine ⟨hr, ?_⟩
          push_cast
          positivity
        · exact hRm x hx
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
        exact ⟨Rich.inv (hRk y hy).2 (hRk y hy).1, inv_ne_zero (hRk y hy).2⟩
    · simp only [List.length_append, List.length_singleton, List.length_map]
      push_cast
      have hk1r : (1 : ℝ) ≤ k := by exact_mod_cast hk1
      have hm1r : (1 : ℝ) ≤ m := by exact_mod_cast hm1
      have hlk0 : 0 ≤ Real.log k := Real.log_nonneg hk1r
      have hlogk : 2 * Real.log k ≤ 5 * Real.log p := by
        have := Real.log_le_log (by positivity) hk2
        rw [Real.log_pow, Real.log_pow] at this
        push_cast at this
        linarith
      have hlogm : Real.log m ≤ Real.log p + Real.log k := by
        have hmr : (m : ℝ) ≤ p * k := by exact_mod_cast hmk
        have := Real.log_le_log (by positivity) hmr
        rw [Real.log_mul (by positivity) (by positivity)] at this
        exact this
      have hsum : Real.log m + Real.log k ≤ 6 * Real.log p := by linarith
      have hlp0 : 0 ≤ Real.log p := by linarith
      nlinarith
  intro p hp hgp
  obtain ⟨w, hw, hR, hl⟩ := key p hp hgp
  exact ⟨w, hw, fun q hq => (hR q hq).1, hl⟩

end OMA.Port8

end

-- ==== Reduction
section



open Finset Filter Topology

namespace OMA.Port8

/-- The shape of the main theorem (`Erdos786.main`). -/
def MainStatement : Prop :=
  ∃ η : ℝ, 0 < η ∧ ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℕ, A ⊆ Icc 1 N →
    (1 - η) * N ≤ A.card → Violation (A : _root_.Set ℕ)

lemma violation_mono {A B : _root_.Set ℕ} (h : A ⊆ B) (hA : Violation A) : Violation B := by
  obtain ⟨s, t, hs, ht, hp, hc⟩ := hA
  exact ⟨s, t, hs.trans h, ht.trans h, hp, hc⟩

theorem not_partII_of_main (hmain : MainStatement) : ¬ (∃ (A : ℕ → _root_.Set ℕ) (f : ℕ → ℝ) (_ : f =o[atTop] (1 : ℕ → ℝ)),
    ∀ N, A N ⊆ _root_.Set.Icc 1 (N + 1) ∧ (1 - f N) * N ≤ (A N).ncard ∧ Erdos786.Set.IsMulCardSet (A N)) := by
  obtain ⟨η, hη, hev⟩ := hmain
  rintro ⟨A, f, hf, hA⟩
  have hf0 : Tendsto f atTop (𝓝 0) := by
    have := hf.tendsto_div_nhds_zero
    simpa using this
  have hsmall : ∀ᶠ N : ℕ in atTop, f N ≤ η / 2 :=
    (hf0.eventually (gt_mem_nhds (by linarith : (0:ℝ) < η / 2))).mono fun _ h => h.le
  have hbig : ∀ᶠ N : ℕ in atTop, 2 / η ≤ (N : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  have hev' := (tendsto_add_atTop_nat 1).eventually hev
  obtain ⟨N, hN1, hN2, hN3⟩ := (hev'.and (hsmall.and hbig)).exists
  obtain ⟨hsub, hcard, hP⟩ := hA N
  have hfin : (A N).Finite := (Set.finite_Icc 1 (N + 1)).subset hsub
  set F := hfin.toFinset with hF
  have hFsub : F ⊆ Icc 1 (N + 1) := by
    intro x hx
    have : x ∈ A N := hfin.mem_toFinset.mp hx
    simpa using hsub this
  have hFcard : (F.card : ℝ) = (A N).ncard := by
    rw [Set.ncard_eq_toFinset_card _ hfin]
  have hNpos : (0 : ℝ) < N := by
    have : (0:ℝ) < 2 / η := by positivity
    linarith
  have hkey : (1 - η) * ((N + 1 : ℕ) : ℝ) ≤ F.card := by
    rw [hFcard]
    have h1 : (1 - f N) * N ≤ (A N).ncard := hcard
    have h2 : (1 - η / 2) * (N : ℝ) ≤ (1 - f N) * N := by
      apply mul_le_mul_of_nonneg_right _ hNpos.le; linarith
    have h3 : (1 - η) * ((N + 1 : ℕ) : ℝ) ≤ (1 - η / 2) * N := by
      push_cast
      have : 2 ≤ η * N := by
        have := (div_le_iff₀ hη).mp hN3; linarith
      nlinarith
    linarith
  have hviol := hN1 F hFsub hkey
  have hcoe : ((F : Set ℕ)) = A N := by simp [hF]
  rw [hcoe] at hviol
  exact (isMulCardSet_iff_not_violation _).mp hP hviol

end OMA.Port8

end

-- ==== Assembly
section



open Finset Real Filter

namespace OMA.Port8

def LiftStmt : Prop := ∀ (A : _root_.Set ℕ), 0 ∉ A → ∀ (a : ℕ), a ∈ A → ∀ (qs : List ℚ),
  (a : ℚ) = qs.prod → (∀ q ∈ qs, Rich A q (2 * qs.length)) → Violation A

def PairsStmt : Prop := ∀ (A : _root_.Set ℕ), 0 ∉ A → ∀ (q : ℚ), 1 < q → ∀ (L : Finset ℕ),
  (∀ x ∈ L, x ∈ A ∧ ∃ y ∈ A, (y : ℚ) = q * x) → Rich A q (L.card / 3)

def HeavyStmt : Prop := ∀ (N : ℕ), 0 < N → ∀ (E : Finset ℕ), E ⊆ Icc 1 N → 32 * E.card ≤ N →
  ∀ (H : Finset ℕ), (∀ p ∈ H, p.Prime ∧ p ≤ N ∧ (N : ℝ) ≤ 16 * p * (E.filter (fun n => p ∣ n)).card) →
    ∑ p ∈ H, (1 : ℝ) / p ≤ 3072 * E.card / N

def SmoothStmt : Prop := ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ X : ℝ, y ^ 16 ≤ X → X ≤ y ^ 56 →
  c₀ * X ≤ (((Icc ⌈X / 2⌉₊ ⌊X⌋₊).filter (fun n => ∀ p ∈ n.primeFactors, ((p : ℕ) : ℝ) ≤ y)).card : ℝ)

def QPartStmt : Prop := ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ Q : Finset ℕ, (∀ q ∈ Q, q.Prime ∧ (q : ℝ) ≤ y) →
  ∀ T : ℕ, (((Icc 1 T).filter (fun z => y ^ 40 < (qPart Q z : ℝ))).card : ℝ) ≤ T / 10

def CoreStmt : Prop := ∀ (N p K : ℕ) (γ : ℝ), 0 < γ → ∀ (A : Finset ℕ), A ⊆ Icc 1 N →
  ∀ (Q : Finset ℕ), (∀ q ∈ Q, q.Prime) → p.Prime → p ∉ Q → 2 * p ≤ N → 1 ≤ K →
  (((Icc 1 (N / p)).filter (fun z => K < qPart Q z)).card : ℝ) ≤ (N / p : ℕ) / 10 →
  16 * p * ((Icc 1 N \ A).filter (fun n => p ∣ n)).card < N →
  (∀ k ∈ Nat.factoredNumbers Q, 1 ≤ k → k ≤ K →
    γ * p * k ≤ (((Icc 1 (p * k)).filter (fun m => m ∈ Nat.factoredNumbers Q ∧ p * k ≤ 2 * m)).card : ℝ)) →
  32 * ((Icc 1 N \ A).card : ℝ) ≤ γ * N →
  ∃ k m : ℕ, k ∈ Nat.factoredNumbers Q ∧ m ∈ Nat.factoredNumbers Q ∧ 1 ≤ k ∧ k ≤ K ∧
    p * k ≤ 2 * m ∧ m < p * k ∧
    ∃ U : Finset ℕ, ((N / p : ℕ) : ℝ) / (2 * K) ≤ U.card ∧ ∀ u ∈ U, m * u ∈ A ∧ p * k * u ∈ A

def WordsStmt : Prop := ∀ (A : _root_.Set ℕ) (M p₀ : ℕ) (good : ℕ → Prop),
  (∀ p, p.Prime → p ≤ p₀ → Rich A p M) →
  (∀ p, p.Prime → good p → p₀ < p → ∃ k m : ℕ, 1 ≤ k ∧ 1 ≤ m ∧
      (∀ q ∈ k.primeFactors, good q ∧ q ^ 16 ≤ p) ∧ (∀ q ∈ m.primeFactors, good q ∧ q ^ 16 ≤ p) ∧
      (k : ℝ) ^ 2 ≤ (p : ℝ) ^ 5 ∧ m ≤ p * k ∧ Rich A ((p * k : ℕ) / (m : ℚ)) M) →
  ∀ p, p.Prime → (good p ∨ p ≤ p₀) →
    ∃ w : List ℚ, w.prod = p ∧ (∀ q ∈ w, Rich A q M) ∧ (w.length : ℝ) ≤ 16 * (Real.log p) ^ 2




lemma rich_mono {A : _root_.Set ℕ} {q : ℚ} {M M' : ℕ} (h : Rich A q M) (hM : M' ≤ M) :
    Rich A q M' := by
  obtain ⟨S, hS, hc⟩ := h
  exact ⟨S, hS, hM.trans hc⟩

/-- `p` is heavy for the exceptional set `E ⊆ [1, N]`. -/
def Heavy (N : ℕ) (E : Finset ℕ) (p : ℕ) : Prop :=
  (N : ℝ) ≤ 16 * p * (E.filter (fun n => p ∣ n)).card

lemma heavy_le {N : ℕ} {E : Finset ℕ} (hN : 0 < N) (hE : E ⊆ Icc 1 N) {p : ℕ}
    (h : Heavy N E p) : p ≤ N := by
  by_contra hp
  push Not at hp
  have h0 : E.filter (fun n => p ∣ n) = ∅ := by
    apply Finset.filter_false_of_mem
    intro n hn hd
    have := hE hn
    simp only [Finset.mem_Icc] at this
    have := Nat.le_of_dvd (by omega) hd
    omega
  unfold Heavy at h
  rw [h0] at h
  simp only [Finset.card_empty, Nat.cast_zero, mul_zero] at h
  have : (0:ℝ) < N := by exact_mod_cast hN
  linarith

open scoped Classical in
lemma heavy_sum (hHeavy : HeavyStmt) {N : ℕ} {E : Finset ℕ} (hN : 0 < N) (hE : E ⊆ Icc 1 N)
    (h32 : 32 * E.card ≤ N) (H : Finset ℕ) (hH : ∀ p ∈ H, p.Prime ∧ Heavy N E p) :
    ∑ p ∈ H, (1 : ℝ) / p ≤ 3072 * E.card / N :=
  hHeavy N hN E hE h32 H (fun p hp => ⟨(hH p hp).1, heavy_le hN hE (hH p hp).2, (hH p hp).2⟩)

lemma card_multiples_le (B q : ℕ) :
    (((Icc 1 B).filter (fun n => q ∣ n)).card : ℝ) ≤ (B : ℝ) / q := by
  have h : (Icc 1 B) = Ioc 0 B := by ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [h, Nat.Ioc_filter_dvd_card_eq_div]
  exact Nat.cast_div_le

open scoped Classical in
lemma heavy_count (hHeavy : HeavyStmt) {N : ℕ} {E : Finset ℕ} (hN : 0 < N) (hE : E ⊆ Icc 1 N)
    (h32 : 32 * E.card ≤ N) (B : ℕ) :
    (((Icc 1 B).filter (fun n => ∃ q ∈ n.primeFactors, Heavy N E q)).card : ℝ)
      ≤ B * (3072 * E.card / N) := by
  set H := (range (B+1)).filter (fun q => q.Prime ∧ Heavy N E q) with hHdef
  have hsub : (Icc 1 B).filter (fun n => ∃ q ∈ n.primeFactors, Heavy N E q) ⊆
      H.biUnion (fun q => (Icc 1 B).filter (fun n => q ∣ n)) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨h1, h2⟩, q, hq, hqh⟩ := hn
    rw [Nat.mem_primeFactors] at hq
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_Icc, hHdef, Finset.mem_range]
    exact ⟨q, ⟨by have := Nat.le_of_dvd (by omega) hq.2.1; omega, hq.1, hqh⟩, ⟨h1, h2⟩, hq.2.1⟩
  calc _ ≤ (((H.biUnion (fun q => (Icc 1 B).filter (fun n => q ∣ n)))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ q ∈ H, (((Icc 1 B).filter (fun n => q ∣ n)).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ q ∈ H, (B : ℝ) * (1 / q) := by
        apply Finset.sum_le_sum; intro q _; rw [mul_one_div]; exact card_multiples_le B q
    _ = B * ∑ q ∈ H, (1:ℝ) / q := by rw [Finset.mul_sum]
    _ ≤ B * (3072 * E.card / N) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        apply heavy_sum hHeavy hN hE h32
        intro p hp; simp only [hHdef, Finset.mem_filter] at hp; exact hp.2

open scoped Classical in
lemma smooth_good (hHeavy : HeavyStmt) {c₀ y₀ : ℝ}
    (hsm : ∀ y : ℝ, y₀ ≤ y → ∀ X : ℝ, y ^ 16 ≤ X → X ≤ y ^ 56 →
      c₀ * X ≤ (((Icc ⌈X / 2⌉₊ ⌊X⌋₊).filter
        (fun n => ∀ p ∈ n.primeFactors, ((p : ℕ) : ℝ) ≤ y)).card : ℝ))
    {N : ℕ} {E : Finset ℕ} (hN : 0 < N) (hE : E ⊆ Icc 1 N) (h32 : 32 * E.card ≤ N)
    (hS : 3072 * (E.card : ℝ) / N ≤ c₀ / 2)
    (y : ℝ) (hy : y₀ ≤ y) (X : ℝ) (hX0 : 0 < X) (hX1 : y ^ 16 ≤ X) (hX2 : X ≤ y ^ 56) :
    c₀ / 2 * X ≤ (((Icc ⌈X / 2⌉₊ ⌊X⌋₊).filter
      (fun n => ∀ p ∈ n.primeFactors, ((p : ℕ) : ℝ) ≤ y ∧ ¬ Heavy N E p)).card : ℝ) := by
  have h1 := hsm y hy X hX1 hX2
  set S := (Icc ⌈X / 2⌉₊ ⌊X⌋₊).filter (fun n => ∀ p ∈ n.primeFactors, ((p : ℕ) : ℝ) ≤ y)
  set G := (Icc ⌈X / 2⌉₊ ⌊X⌋₊).filter
    (fun n => ∀ p ∈ n.primeFactors, ((p : ℕ) : ℝ) ≤ y ∧ ¬ Heavy N E p)
  set Bd := (Icc 1 ⌊X⌋₊).filter (fun n => ∃ q ∈ n.primeFactors, Heavy N E q)
  have hsub : S ⊆ G ∪ Bd := by
    intro n hn
    simp only [S, Finset.mem_filter, Finset.mem_Icc] at hn
    by_cases hh : ∃ q ∈ n.primeFactors, Heavy N E q
    · apply Finset.mem_union_right
      simp only [Bd, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨?_, hn.1.2⟩, hh⟩
      have : 0 < ⌈X / 2⌉₊ := Nat.ceil_pos.mpr (by positivity)
      omega
    · push Not at hh
      apply Finset.mem_union_left
      simp only [G, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨hn.1, fun p hp => ⟨hn.2 p hp, hh p hp⟩⟩
  have hc := Finset.card_le_card hsub
  have hu := Finset.card_union_le G Bd
  have hb := heavy_count hHeavy hN hE h32 ⌊X⌋₊
  have hfl : (⌊X⌋₊ : ℝ) ≤ X := Nat.floor_le hX0.le
  have hSn : 0 ≤ 3072 * (E.card : ℝ) / N := by positivity
  have : (⌊X⌋₊ : ℝ) * (3072 * E.card / N) ≤ X * (c₀ / 2) :=
    mul_le_mul hfl hS hSn hX0.le
  have hc' : (S.card : ℝ) ≤ G.card + Bd.card := by exact_mod_cast hc.trans hu
  nlinarith


lemma card_E_le {N : ℕ} {A : Finset ℕ} {η : ℝ} (hA : A ⊆ Icc 1 N)
    (hcard : (1 - η) * N ≤ A.card) : ((Icc 1 N \ A).card : ℝ) ≤ η * N := by
  have h1 : (Icc 1 N \ A).card = N - A.card := by
    rw [Finset.card_sdiff_of_subset hA, Nat.card_Icc]; omega
  have h2 : A.card ≤ N := by
    have := Finset.card_le_card hA
    rw [Nat.card_Icc] at this; omega
  rw [h1, Nat.cast_sub h2]
  linarith

lemma small_prime_count {N : ℕ} {A : Finset ℕ} (p : ℕ) (hp : 0 < p) :
    N / p ≤ ((Icc 1 (N / p)).filter (fun x => x ∈ A ∧ p * x ∈ A)).card
      + 2 * (Icc 1 N \ A).card := by
  set E := Icc 1 N \ A with hEdef
  set I := Icc 1 (N / p) with hI
  have hmul : ∀ x ∈ I, 1 ≤ x ∧ x ≤ N ∧ p * x ≤ N := by
    intro x hx
    simp only [hI, Finset.mem_Icc] at hx
    have h1 : x * p ≤ N := (Nat.le_div_iff_mul_le hp).mp hx.2
    refine ⟨hx.1, ?_, by linarith⟩
    nlinarith
  have hsub : I ⊆ I.filter (fun x => x ∈ A ∧ p * x ∈ A) ∪ (E ∪ I.filter (fun x => p * x ∉ A)) := by
    intro x hx
    obtain ⟨h1, h2, h3⟩ := hmul x hx
    simp only [Finset.mem_union, Finset.mem_filter, hEdef, Finset.mem_sdiff, Finset.mem_Icc]
    by_cases hxA : x ∈ A
    · by_cases hpx : p * x ∈ A
      · exact Or.inl ⟨hx, hxA, hpx⟩
      · exact Or.inr (Or.inr ⟨hx, hpx⟩)
    · exact Or.inr (Or.inl ⟨⟨h1, h2⟩, hxA⟩)
  have h2 : (I.filter (fun x => p * x ∉ A)).card ≤ E.card := by
    rw [← Finset.card_image_of_injective _ (fun a b h => Nat.eq_of_mul_eq_mul_left hp h)]
    apply Finset.card_le_card
    intro n hn
    simp only [Finset.mem_image, Finset.mem_filter] at hn
    obtain ⟨x, ⟨hx, hxA⟩, rfl⟩ := hn
    obtain ⟨h1, _, h3⟩ := hmul x hx
    simp only [hEdef, Finset.mem_sdiff, Finset.mem_Icc]
    exact ⟨⟨by nlinarith, h3⟩, hxA⟩
  have hc := Finset.card_le_card hsub
  have hu1 := Finset.card_union_le (I.filter (fun x => x ∈ A ∧ p * x ∈ A))
    (E ∪ I.filter (fun x => p * x ∉ A))
  have hu2 := Finset.card_union_le E (I.filter (fun x => p * x ∉ A))
  have hIc : I.card = N / p := by simp [hI]
  rw [hIc] at hc
  omega

lemma small_prime_rich (hPairs : PairsStmt) {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Icc 1 N)
    (p p₀ M : ℕ) (hp : p.Prime) (hpp₀ : p ≤ p₀)
    (hbig : 3 * (M : ℝ) + 2 * (Icc 1 N \ A).card + 1 ≤ (N : ℝ) / p₀) :
    Rich (A : _root_.Set ℕ) (p : ℚ) M := by
  have h0 : (0 : ℕ) ∉ (A : _root_.Set ℕ) := by
    intro h; have := hA (Finset.mem_coe.mp h); simp at this
  have hp0 : 0 < p := hp.pos
  have hR := hPairs (A : _root_.Set ℕ) h0 (p : ℚ) (by exact_mod_cast hp.one_lt)
    ((Icc 1 (N / p)).filter (fun x => x ∈ A ∧ p * x ∈ A)) (by
      intro x hx
      simp only [Finset.mem_filter] at hx
      exact ⟨Finset.mem_coe.mpr hx.2.1, p * x, Finset.mem_coe.mpr hx.2.2, by push_cast; ring⟩)
  apply rich_mono hR
  have hc := small_prime_count (N := N) (A := A) p hp0
  have hdiv : N / p₀ ≤ N / p := Nat.div_le_div_left hpp₀ hp0
  have hlt := Nat.lt_mul_div_succ N (lt_of_lt_of_le hp0 hpp₀)
  have hp₀r : (0 : ℝ) < p₀ := by exact_mod_cast lt_of_lt_of_le hp0 hpp₀
  have hlt' : (N : ℝ) / p₀ < (N / p₀ : ℕ) + 1 := by
    rw [div_lt_iff₀ hp₀r]
    have : (N : ℝ) < (p₀ : ℝ) * ((N / p₀ : ℕ) + 1) := by exact_mod_cast hlt
    linarith
  have hreal : 3 * (M : ℝ) ≤ (((Icc 1 (N / p)).filter (fun x => x ∈ A ∧ p * x ∈ A)).card : ℝ) := by
    have h1 : ((N / p : ℕ) : ℝ) ≤ (((Icc 1 (N / p)).filter (fun x => x ∈ A ∧ p * x ∈ A)).card : ℝ)
      + 2 * (Icc 1 N \ A).card := by exact_mod_cast hc
    have h2 : ((N / p₀ : ℕ) : ℝ) ≤ ((N / p : ℕ) : ℝ) := by exact_mod_cast hdiv
    linarith
  have : 3 * M ≤ ((Icc 1 (N / p)).filter (fun x => x ∈ A ∧ p * x ∈ A)).card := by
    exact_mod_cast hreal
  omega


open scoped Classical in
lemma replacement (hPairs : PairsStmt) (hHeavy : HeavyStmt) (hCore : CoreStmt) {c₀ y₀ y₂ : ℝ}
    (hc₀ : 0 < c₀)
    (hsm : ∀ y : ℝ, y₀ ≤ y → ∀ X : ℝ, y ^ 16 ≤ X → X ≤ y ^ 56 →
      c₀ * X ≤ (((Icc ⌈X / 2⌉₊ ⌊X⌋₊).filter
        (fun n => ∀ p ∈ n.primeFactors, ((p : ℕ) : ℝ) ≤ y)).card : ℝ))
    (hqp : ∀ y : ℝ, y₂ ≤ y → ∀ Q : Finset ℕ, (∀ q ∈ Q, q.Prime ∧ (q : ℝ) ≤ y) →
      ∀ T : ℕ, (((Icc 1 T).filter (fun z => y ^ 40 < (qPart Q z : ℝ))).card : ℝ) ≤ T / 10)
    {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Icc 1 N) (hN : 0 < N)
    (h32 : 32 * (Icc 1 N \ A).card ≤ N)
    (hS : 3072 * ((Icc 1 N \ A).card : ℝ) / N ≤ c₀ / 2)
    (hdef : 32 * ((Icc 1 N \ A).card : ℝ) ≤ c₀ / 2 * N)
    (p : ℕ) (hp : p.Prime) (hnh : ¬ Heavy N (Icc 1 N \ A) p) (h2p : 2 * p ≤ N)
    (y : ℝ) (hyp : y ^ 16 = p) (hy0 : y₀ ≤ y) (hy2 : y₂ ≤ y) (hy1 : 2 ≤ y) :
    ∃ k m : ℕ, 1 ≤ k ∧ 1 ≤ m ∧
      (∀ q ∈ k.primeFactors, q.Prime ∧ ¬ Heavy N (Icc 1 N \ A) q ∧ (q : ℝ) ≤ y) ∧
      (∀ q ∈ m.primeFactors, q.Prime ∧ ¬ Heavy N (Icc 1 N \ A) q ∧ (q : ℝ) ≤ y) ∧
      (k : ℝ) ^ 2 ≤ (p : ℝ) ^ 5 ∧ m ≤ p * k ∧
      ∃ c : ℕ, ((N / p : ℕ) : ℝ) / (2 * y ^ 40) ≤ c ∧
        Rich (A : _root_.Set ℕ) (((p * k : ℕ) : ℚ) / (m : ℚ)) (c / 3) := by
  have hE : Icc 1 N \ A ⊆ Icc 1 N := Finset.sdiff_subset
  have hyn : 0 ≤ y := by linarith
  set K := ⌊y ^ 40⌋₊ with hK
  set Q := (range (⌊y⌋₊ + 1)).filter (fun q => q.Prime ∧ ¬ Heavy N (Icc 1 N \ A) q) with hQ
  have hQmem : ∀ q ∈ Q, q.Prime ∧ ¬ Heavy N (Icc 1 N \ A) q ∧ (q:ℝ) ≤ y := by
    intro q hq
    simp only [hQ, Finset.mem_filter, Finset.mem_range] at hq
    refine ⟨hq.2.1, hq.2.2, ?_⟩
    have : q ≤ ⌊y⌋₊ := by omega
    exact (Nat.le_floor_iff hyn).mp this
  have hpy : (p:ℝ) = y ^ 16 := hyp.symm
  have hy40 : (1:ℝ) ≤ y ^ 40 := one_le_pow₀ (by linarith)
  have hK1 : 1 ≤ K := Nat.le_floor (by simpa using hy40)
  have hKle : (K:ℝ) ≤ y ^ 40 := Nat.floor_le (by positivity)
  have hpQ : p ∉ Q := by
    intro h
    have h1 := (hQmem p h).2.2
    rw [hpy] at h1
    have : y < y ^ 16 := lt_self_pow₀ (by linarith) (by norm_num)
    linarith
  have htail : (((Icc 1 (N / p)).filter (fun z => K < qPart Q z)).card : ℝ)
      ≤ (N / p : ℕ) / 10 := by
    have h := hqp y hy2 Q (fun q hq => ⟨(hQmem q hq).1, (hQmem q hq).2.2⟩) (N / p)
    refine le_trans ?_ h
    have hsub : (Icc 1 (N / p)).filter (fun z => K < qPart Q z) ⊆
        (Icc 1 (N / p)).filter (fun z => y ^ 40 < (qPart Q z : ℝ)) := by
      intro z hz
      simp only [Finset.mem_filter] at hz ⊢
      refine ⟨hz.1, ?_⟩
      have h1 : ((K + 1 : ℕ) : ℝ) ≤ (qPart Q z : ℝ) := by exact_mod_cast hz.2
      have h2 : y ^ 40 < (K : ℝ) + 1 := Nat.lt_floor_add_one _
      push_cast at h1
      linarith
    exact_mod_cast Finset.card_le_card hsub
  have hnh' : 16 * p * ((Icc 1 N \ A).filter (fun n => p ∣ n)).card < N := by
    unfold Heavy at hnh
    push Not at hnh
    exact_mod_cast hnh
  have hres : ∀ k ∈ Nat.factoredNumbers Q, 1 ≤ k → k ≤ K →
      c₀ / 2 * p * k ≤ (((Icc 1 (p * k)).filter
        (fun m => m ∈ Nat.factoredNumbers Q ∧ p * k ≤ 2 * m)).card : ℝ) := by
    intro k _ hk1 hkK
    have hkr : (k:ℝ) ≤ y ^ 40 := le_trans (by exact_mod_cast hkK) hKle
    have hk1r : (1:ℝ) ≤ k := by exact_mod_cast hk1
    set X : ℝ := ((p * k : ℕ) : ℝ) with hX
    have hXe : X = y ^ 16 * k := by rw [hX]; push_cast; rw [hpy]
    have hy16 : 0 < y ^ 16 := by positivity
    have h := smooth_good hHeavy hsm hN hE h32 hS y hy0 X (by rw [hXe]; positivity)
      (by rw [hXe]; nlinarith)
      (by rw [hXe]; calc y ^ 16 * k ≤ y ^ 16 * y ^ 40 := by gcongr
                  _ = y ^ 56 := by ring)
    have hfl : ⌊X⌋₊ = p * k := by rw [hX]; exact Nat.floor_natCast _
    rw [hfl] at h
    have hX0 : 0 < X := by rw [hXe]; positivity
    calc c₀ / 2 * p * k = c₀ / 2 * X := by rw [hX]; push_cast; ring
      _ ≤ _ := h
      _ ≤ _ := by
        apply Nat.cast_le.mpr
        apply Finset.card_le_card
        intro n hn
        simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
        obtain ⟨⟨hn1, hn2⟩, hn3⟩ := hn
        have hc1 : 0 < ⌈X / 2⌉₊ := Nat.ceil_pos.mpr (by positivity)
        have hn0 : n ≠ 0 := by omega
        refine ⟨⟨by omega, hn2⟩, ?_, ?_⟩
        · rw [Nat.mem_factoredNumbers']
          intro q hq hqn
          have hqf : q ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hq, hqn, hn0⟩
          obtain ⟨hqy, hqh⟩ := hn3 q hqf
          simp only [hQ, Finset.mem_filter, Finset.mem_range]
          exact ⟨by have := Nat.le_floor hqy; omega, hq, hqh⟩
        · have h1 : X / 2 ≤ (n : ℝ) := Nat.ceil_le.mp hn1
          have h2 : ((p * k : ℕ) : ℝ) ≤ ((2 * n : ℕ) : ℝ) := by
            push_cast; rw [hX] at h1; push_cast at h1; linarith
          exact_mod_cast h2
  obtain ⟨k, m, hkQ, hmQ, hk1, hkK, _, hmpk, U, hU, hUA⟩ :=
    hCore N p K (c₀ / 2) (by positivity) A hA Q (fun q hq => (hQmem q hq).1) hp hpQ h2p hK1
      htail hnh' hres hdef
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (Nat.mem_factoredNumbers.mp hmQ).1
  have hfac : ∀ j ∈ Nat.factoredNumbers Q, ∀ q ∈ j.primeFactors,
      q.Prime ∧ ¬ Heavy N (Icc 1 N \ A) q ∧ (q : ℝ) ≤ y := by
    intro j hj q hq
    exact hQmem q (Nat.mem_factoredNumbers'.mp hj q (Nat.prime_of_mem_primeFactors hq)
      (Nat.dvd_of_mem_primeFactors hq))
  have hkr : (k:ℝ) ≤ y ^ 40 := le_trans (by exact_mod_cast hkK) hKle
  have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg _
  refine ⟨k, m, hk1, hm1, hfac k hkQ, hfac m hmQ, ?_, hmpk.le, U.card, ?_, ?_⟩
  · rw [hpy]
    calc (k:ℝ) ^ 2 ≤ (y ^ 40) ^ 2 := by gcongr
      _ = (y ^ 16) ^ 5 := by ring
  · have hK0 : (0:ℝ) < K := by exact_mod_cast hK1
    refine le_trans ?_ hU
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
    linarith
  · have h0 : (0 : ℕ) ∉ (A : _root_.Set ℕ) := by
      intro h; have := hA (Finset.mem_coe.mp h); simp at this
    have hinj : Function.Injective (fun u => m * u) :=
      fun a b h => Nat.eq_of_mul_eq_mul_left (by omega) h
    rw [← Finset.card_image_of_injective U hinj]
    apply hPairs (A : _root_.Set ℕ) h0
    · rw [one_lt_div (by exact_mod_cast hm1)]
      exact_mod_cast hmpk
    · intro x hx
      simp only [Finset.mem_image] at hx
      obtain ⟨u, hu, rfl⟩ := hx
      refine ⟨Finset.mem_coe.mpr (hUA u hu).1, p * k * u, Finset.mem_coe.mpr (hUA u hu).2, ?_⟩
      have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
      push_cast
      field_simp


open scoped Classical in
lemma exists_good (hHeavy : HeavyStmt) {c₀ y₀ : ℝ}
    (hsm : ∀ y : ℝ, y₀ ≤ y → ∀ X : ℝ, y ^ 16 ≤ X → X ≤ y ^ 56 →
      c₀ * X ≤ (((Icc ⌈X / 2⌉₊ ⌊X⌋₊).filter
        (fun n => ∀ p ∈ n.primeFactors, ((p : ℕ) : ℝ) ≤ y)).card : ℝ))
    {N : ℕ} {A : Finset ℕ} (hN : 0 < N)
    (h32 : 32 * (Icc 1 N \ A).card ≤ N)
    (hS : 3072 * ((Icc 1 N \ A).card : ℝ) / N ≤ c₀ / 2)
    (hsmall : ((Icc 1 N \ A).card : ℝ) < c₀ / 2 * N)
    (P : ℝ) (hP : y₀ ≤ P) (hP1 : P ^ 16 ≤ N) (hP2 : (N : ℝ) ≤ P ^ 56) :
    ∃ a ∈ A, ∀ q ∈ a.primeFactors, (q : ℝ) ≤ P ∧ ¬ Heavy N (Icc 1 N \ A) q := by
  have hE : Icc 1 N \ A ⊆ Icc 1 N := Finset.sdiff_subset
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have h := smooth_good hHeavy hsm hN hE h32 hS P hP (N : ℝ) hN0 hP1 hP2
  rw [Nat.floor_natCast] at h
  set G := (Icc ⌈(N : ℝ) / 2⌉₊ N).filter
    (fun n => ∀ p ∈ n.primeFactors, ((p : ℕ) : ℝ) ≤ P ∧ ¬ Heavy N (Icc 1 N \ A) p) with hG
  by_contra hcon
  push Not at hcon
  have hsub : G ⊆ Icc 1 N \ A := by
    intro n hn
    have hn' := hn
    simp only [hG, Finset.mem_filter, Finset.mem_Icc] at hn'
    have hc1 : 0 < ⌈(N : ℝ) / 2⌉₊ := Nat.ceil_pos.mpr (by positivity)
    rw [Finset.mem_sdiff, Finset.mem_Icc]
    refine ⟨⟨by omega, hn'.1.2⟩, fun hnA => ?_⟩
    obtain ⟨q, hq, hq'⟩ := hcon n hnA
    exact (hn'.2 q hq).2 (hq' (hn'.2 q hq).1)
  have := Finset.card_le_card hsub
  have : (G.card : ℝ) ≤ (Icc 1 N \ A).card := by exact_mod_cast this
  linarith

lemma word_concat (l : List ℕ) (W : ℕ → List ℚ) (c : ℝ)
    (h : ∀ q ∈ l, 1 ≤ q ∧ (W q).prod = q ∧ ((W q).length : ℝ) ≤ 16 * Real.log q ^ 2 ∧
      Real.log q ≤ c) :
    (l.flatMap W).prod = ((l.prod : ℕ) : ℚ) ∧
      ((l.flatMap W).length : ℝ) ≤ 16 * c * Real.log (l.prod : ℕ) := by
  induction l with
  | nil => simp
  | cons q l ih =>
    have hq := h q (by simp)
    obtain ⟨ih1, ih2⟩ := ih (fun r hr => h r (by simp [hr]))
    have hl0 : l.prod ≠ 0 := by
      rw [Ne, List.prod_eq_zero_iff]
      intro h0
      have := (h 0 (by simp [h0])).1
      omega
    have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
    have hl0' : ((l.prod : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hl0
    have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq.1)
    refine ⟨?_, ?_⟩
    · rw [List.flatMap_cons, List.prod_append, hq.2.1, ih1, List.prod_cons]
      push_cast; ring
    · rw [List.flatMap_cons, List.length_append, List.prod_cons, Nat.cast_mul,
        Real.log_mul hq0 hl0']
      push_cast
      have h3 := hq.2.2.1
      have h4 : 16 * Real.log q ^ 2 ≤ 16 * c * Real.log q := by
        have := mul_le_mul_of_nonneg_left hq.2.2.2 hlogq
        nlinarith
      push_cast at ih2
      linarith

lemma eventually_B (C : ℝ) : ∀ᶠ N : ℕ in atTop,
    ∃ B : ℝ, 0 ≤ B ∧ B ^ 64 = (N : ℝ) ∧ C ≤ B ∧ Real.log N ^ 2 ≤ B := by
  have h1 : Tendsto (fun x : ℝ => x ^ ((64:ℕ):ℝ)⁻¹) atTop atTop :=
    tendsto_rpow_atTop (by positivity)
  have h2 := (isLittleO_log_rpow_rpow_atTop (2:ℝ) (s := ((64:ℕ):ℝ)⁻¹) (by positivity)).bound
    one_pos
  have h3 := (h1.eventually_ge_atTop C).and (h2.and (eventually_ge_atTop 0))
  filter_upwards [tendsto_natCast_atTop_atTop.eventually h3] with N hN
  obtain ⟨hC, hlo, h0⟩ := hN
  refine ⟨_, Real.rpow_nonneg h0 _, Real.rpow_inv_natCast_pow h0 (by norm_num), hC, ?_⟩
  rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul, Real.rpow_two,
    abs_of_nonneg (Real.rpow_nonneg h0 _)] at hlo
  exact (le_abs_self _).trans hlo

lemma poly_big {B M u v : ℝ} (hB : 2 ≤ B) (hM : M ≤ B + 1) (hu0 : 0 ≤ u)
    (hu : u ≤ B ^ 7) (hv : v ≤ B ^ 2) : 6 * M * u + v ≤ B ^ 64 := by
  have hB1 : 1 ≤ B := by linarith
  have h7 : 0 ≤ B ^ 7 := by positivity
  have h1 : 6 * M * u ≤ 6 * (B + 1) * B ^ 7 := by
    have := mul_le_mul hM hu hu0 (by linarith)
    nlinarith
  have h2 : B ^ 2 ≤ B ^ 8 := pow_le_pow_right₀ hB1 (by norm_num)
  have h3 : 16 ≤ B ^ 4 := by
    have : (2:ℝ) ^ 4 ≤ B ^ 4 := by gcongr
    norm_num at this; linarith
  have h4 : B ^ 12 ≤ B ^ 64 := pow_le_pow_right₀ hB1 (by norm_num)
  have h5 : B ^ 12 = B ^ 4 * B ^ 8 := by ring
  have h6 : B * B ^ 7 = B ^ 8 := by ring
  have h8 : 0 ≤ B ^ 8 := by positivity
  nlinarith

lemma main_small (hPairs : PairsStmt) {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Icc 1 N)
    {p₀ M : ℕ} {η B : ℝ} (hp₀pos : (0:ℝ) < p₀) (hB0 : 0 ≤ B) (hB1 : 1 ≤ B)
    (hBp₀ : 14 * (p₀:ℝ) ≤ B) (hNr : (N:ℝ) = B ^ 64)
    (hEc : ((Icc 1 N \ A).card : ℝ) ≤ η * N) (hη3 : η ≤ 1 / (4 * p₀))
    (hM2 : (M:ℝ) ≤ B + 1) :
    ∀ p, p.Prime → p ≤ p₀ → Rich (A : _root_.Set ℕ) p M := by
  intro p hp hpp
  have hNr0 : (0:ℝ) ≤ N := Nat.cast_nonneg _
  apply small_prime_rich hPairs hA p p₀ M hp hpp
  rw [le_div_iff₀ hp₀pos]
  have h1 : 2 * ((Icc 1 N \ A).card:ℝ) * p₀ ≤ N / 2 := by
    have h4 : η * (4 * p₀) ≤ 1 := by rwa [le_div_iff₀ (by positivity)] at hη3
    have h5 : ((Icc 1 N \ A).card:ℝ) * p₀ ≤ η * N * p₀ :=
      mul_le_mul_of_nonneg_right hEc hp₀pos.le
    have h6 : η * (4 * p₀) * N ≤ 1 * N := mul_le_mul_of_nonneg_right h4 hNr0
    nlinarith
  have h2 : (3 * M + 1) * (p₀:ℝ) ≤ N / 2 := by
    have h3 : (3 * M + 1) * (p₀:ℝ) ≤ (3 * B + 4) * p₀ :=
      mul_le_mul_of_nonneg_right (by linarith) hp₀pos.le
    have h4 : (3 * B + 4) * (p₀:ℝ) ≤ B * B / 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hBp₀) hB0]
    have h5 : B ^ 2 ≤ B ^ 64 := pow_le_pow_right₀ hB1 (by norm_num)
    rw [hNr]; nlinarith
  nlinarith

lemma main_repl (hPairs : PairsStmt) (hHeavy : HeavyStmt) (hCore : CoreStmt) {c₀ y₀ y₂ : ℝ}
    (hc₀ : 0 < c₀)
    (hsm : ∀ y : ℝ, y₀ ≤ y → ∀ X : ℝ, y ^ 16 ≤ X → X ≤ y ^ 56 →
      c₀ * X ≤ (((Icc ⌈X / 2⌉₊ ⌊X⌋₊).filter
        (fun n => ∀ p ∈ n.primeFactors, ((p : ℕ) : ℝ) ≤ y)).card : ℝ))
    (hqp : ∀ y : ℝ, y₂ ≤ y → ∀ Q : Finset ℕ, (∀ q ∈ Q, q.Prime ∧ (q : ℝ) ≤ y) →
      ∀ T : ℕ, (((Icc 1 T).filter (fun z => y ^ 40 < (qPart Q z : ℝ))).card : ℝ) ≤ T / 10)
    {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Icc 1 N) (hN : 0 < N)
    (h32 : 32 * (Icc 1 N \ A).card ≤ N)
    (hS : 3072 * ((Icc 1 N \ A).card : ℝ) / N ≤ c₀ / 2)
    (hdef : 32 * ((Icc 1 N \ A).card : ℝ) ≤ c₀ / 2 * N)
    {ys B : ℝ} {p₀ M : ℕ} (hys1 : y₀ ≤ ys) (hys2 : y₂ ≤ ys) (hys3 : 2 ≤ ys)
    (hp₀ : ys ^ 16 ≤ p₀) (hB0 : 0 ≤ B) (hB2 : 2 ≤ B) (hNr : (N:ℝ) = B ^ 64)
    (hM2 : (M:ℝ) ≤ B + 1) :
    ∀ p, p.Prime → (p.Prime ∧ ¬ Heavy N (Icc 1 N \ A) p ∧ (p:ℝ) ≤ B ^ 2) → p₀ < p →
      ∃ k m : ℕ, 1 ≤ k ∧ 1 ≤ m ∧
      (∀ q ∈ k.primeFactors,
        (q.Prime ∧ ¬ Heavy N (Icc 1 N \ A) q ∧ (q:ℝ) ≤ B ^ 2) ∧ q ^ 16 ≤ p) ∧
      (∀ q ∈ m.primeFactors,
        (q.Prime ∧ ¬ Heavy N (Icc 1 N \ A) q ∧ (q:ℝ) ≤ B ^ 2) ∧ q ^ 16 ≤ p) ∧
      (k : ℝ) ^ 2 ≤ (p : ℝ) ^ 5 ∧ m ≤ p * k ∧
      Rich (A : _root_.Set ℕ) ((p * k : ℕ) / (m : ℚ)) M := by
  intro p hp hgp hpp₀
  obtain ⟨_, hnh, hpB⟩ := hgp
  have hB1 : 1 ≤ B := by linarith
  have hp0 : (0:ℝ) ≤ p := Nat.cast_nonneg _
  obtain ⟨y, hy0, hyp⟩ : ∃ y : ℝ, 0 ≤ y ∧ y ^ 16 = p :=
    ⟨(p:ℝ) ^ ((16:ℕ):ℝ)⁻¹, Real.rpow_nonneg hp0 _, Real.rpow_inv_natCast_pow hp0 (by norm_num)⟩
  have hysy : ys ≤ y := by
    have h1 : ys ^ 16 ≤ p := by
      have : (p₀ : ℝ) < p := by exact_mod_cast hpp₀
      linarith
    rw [← hyp] at h1
    exact (pow_le_pow_iff_left₀ (by linarith) hy0 (by norm_num)).mp h1
  have h2p : 2 * p ≤ N := by
    have : 2 * (p:ℝ) ≤ N := by
      rw [hNr]
      have h5 : B ^ 3 ≤ B ^ 64 := pow_le_pow_right₀ hB1 (by norm_num)
      have h6 : 2 * B ^ 2 ≤ B ^ 3 := by
        have : B ^ 3 = B * B ^ 2 := by ring
        rw [this]; exact mul_le_mul_of_nonneg_right hB2 (sq_nonneg B)
      linarith
    exact_mod_cast this
  obtain ⟨k, m, hk1, hm1, hkf, hmf, hk2, hmk, c, hc, hR⟩ :=
    replacement hPairs hHeavy hCore hc₀ hsm hqp hA hN h32 hS hdef p hp hnh h2p y hyp
      (hys1.trans hysy) (hys2.trans hysy) (hys3.trans hysy)
  have hy1 : 1 ≤ y := by linarith
  have hyp' : y ≤ (p:ℝ) := by rw [← hyp]; exact le_self_pow₀ hy1 (by norm_num)
  have hfac : ∀ j : ℕ,
      (∀ q ∈ j.primeFactors, q.Prime ∧ ¬ Heavy N (Icc 1 N \ A) q ∧ (q : ℝ) ≤ y) →
      ∀ q ∈ j.primeFactors,
        (q.Prime ∧ ¬ Heavy N (Icc 1 N \ A) q ∧ (q:ℝ) ≤ B ^ 2) ∧ q ^ 16 ≤ p := by
    intro j hj q hq
    obtain ⟨h1, h2, h3⟩ := hj q hq
    refine ⟨⟨h1, h2, by linarith⟩, ?_⟩
    have : (q:ℝ) ^ 16 ≤ p := by
      rw [← hyp]; exact pow_le_pow_left₀ (Nat.cast_nonneg _) h3 16
    exact_mod_cast this
  refine ⟨k, m, hk1, hm1, hfac k hkf, hfac m hmf, hk2, hmk, rich_mono hR ?_⟩
  have hstep : 3 * (M:ℝ) ≤ c := by
    have hq' := Nat.lt_mul_div_succ N hp.pos
    have hq'r : (N:ℝ) < p * ((N / p : ℕ) + 1) := by exact_mod_cast hq'
    have hy8 : y ^ 8 ≤ B := by
      have : (y ^ 8) ^ 2 ≤ B ^ 2 := by
        rw [← pow_mul, hyp]; exact hpB
      exact (pow_le_pow_iff_left₀ (by positivity) hB0 (by norm_num)).mp this
    have hu : y ^ 56 ≤ B ^ 7 := by
      calc y ^ 56 = (y ^ 8) ^ 7 := by ring
        _ ≤ B ^ 7 := pow_le_pow_left₀ (by positivity) hy8 7
    have hM0 : (0:ℝ) ≤ M := Nat.cast_nonneg _
    have hpoly := poly_big hB2 hM2 (by positivity : (0:ℝ) ≤ y ^ 56) hu hpB
    have hp0' : (0:ℝ) < p := by exact_mod_cast hp.pos
    have hy40 : 0 < y ^ 40 := by positivity
    have hkey : 3 * (M:ℝ) * (2 * y ^ 40) ≤ ((N / p : ℕ) : ℝ) := by
      have h6 : (p:ℝ) * (3 * M * (2 * y ^ 40)) = 6 * M * y ^ 56 := by
        rw [← hyp]; ring
      have : (p:ℝ) * (3 * M * (2 * y ^ 40)) < p * ((N / p : ℕ) : ℝ) := by
        rw [h6]; linarith
      exact le_of_lt (lt_of_mul_lt_mul_left this hp0'.le)
    calc 3 * (M:ℝ) ≤ ((N / p : ℕ) : ℝ) / (2 * y ^ 40) := by
          rw [le_div_iff₀ (by positivity)]; exact hkey
      _ ≤ c := hc
  have : 3 * M ≤ c := by exact_mod_cast hstep
  omega

lemma main_final (hLift : LiftStmt) (hHeavy : HeavyStmt) {c₀ y₀ : ℝ}
    (hsm : ∀ y : ℝ, y₀ ≤ y → ∀ X : ℝ, y ^ 16 ≤ X → X ≤ y ^ 56 →
      c₀ * X ≤ (((Icc ⌈X / 2⌉₊ ⌊X⌋₊).filter
        (fun n => ∀ p ∈ n.primeFactors, ((p : ℕ) : ℝ) ≤ y)).card : ℝ))
    {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Icc 1 N) (hN : 0 < N)
    (h32 : 32 * (Icc 1 N \ A).card ≤ N)
    (hS : 3072 * ((Icc 1 N \ A).card : ℝ) / N ≤ c₀ / 2)
    (hEsmall : ((Icc 1 N \ A).card : ℝ) < c₀ / 2 * N)
    {B : ℝ} {p₀ M : ℕ} (hB1 : 1 ≤ B) (hy₀B : y₀ ≤ B ^ 2) (hNr : (N:ℝ) = B ^ 64)
    (hM1 : Real.log N ^ 2 ≤ M)
    (hW : ∀ p, p.Prime → ((p.Prime ∧ ¬ Heavy N (Icc 1 N \ A) p ∧ (p:ℝ) ≤ B ^ 2) ∨ p ≤ p₀) →
      ∃ w : List ℚ, w.prod = p ∧ (∀ q ∈ w, Rich (A : _root_.Set ℕ) q M) ∧
        (w.length : ℝ) ≤ 16 * (Real.log p) ^ 2) :
    Violation (A : _root_.Set ℕ) := by
  have h0 : (0 : ℕ) ∉ (A : _root_.Set ℕ) := by
    intro h; have := hA (Finset.mem_coe.mp h); simp at this
  obtain ⟨a, haA, ha⟩ := exists_good hHeavy hsm hN h32 hS hEsmall (B ^ 2) hy₀B
    (by rw [hNr, ← pow_mul]; exact pow_le_pow_right₀ hB1 (by norm_num))
    (by rw [hNr, ← pow_mul]; exact pow_le_pow_right₀ hB1 (by norm_num))
  have ha0 : a ≠ 0 := by have := hA haA; simp at this; omega
  have hWq : ∀ q, ∃ w : List ℚ, q ∈ a.primeFactorsList → (w.prod = q ∧
      (∀ r ∈ w, Rich (A : _root_.Set ℕ) r M) ∧ (w.length : ℝ) ≤ 16 * Real.log q ^ 2) := by
    intro q
    by_cases hq : q ∈ a.primeFactorsList
    · have hqp := Nat.prime_of_mem_primeFactorsList hq
      have hqf : q ∈ a.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hqp, Nat.dvd_of_mem_primeFactorsList hq, ha0⟩
      obtain ⟨h1, h2⟩ := ha q hqf
      obtain ⟨w, hw1, hw2, hw3⟩ := hW q hqp (Or.inl ⟨hqp, h2, h1⟩)
      exact ⟨w, fun _ => ⟨hw1, hw2, hw3⟩⟩
    · exact ⟨[], fun h => absurd h hq⟩
  choose W hW' using hWq
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB1
  have hcw := word_concat a.primeFactorsList W (Real.log (B ^ 2)) (fun q hq => by
      obtain ⟨h1, _, h3⟩ := hW' q hq
      have hqp := Nat.prime_of_mem_primeFactorsList hq
      have hqf : q ∈ a.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hqp, Nat.dvd_of_mem_primeFactorsList hq, ha0⟩
      refine ⟨hqp.one_lt.le, h1, h3, ?_⟩
      exact Real.log_le_log (by exact_mod_cast hqp.pos) (ha q hqf).1)
  rw [Nat.prod_primeFactorsList ha0] at hcw
  obtain ⟨hprod, hlen⟩ := hcw
  have haN : a ≤ N := (Finset.mem_Icc.mp (hA haA)).2
  have ha1 : (1:ℝ) ≤ a := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr ha0
  have hloga : Real.log a ≤ Real.log N :=
    Real.log_le_log (by linarith) (by exact_mod_cast haN)
  have hlogN : Real.log N = 64 * Real.log B := by rw [hNr, Real.log_pow]; norm_num
  have hlogB2 : Real.log (B ^ 2) = 2 * Real.log B := by rw [Real.log_pow]; norm_num
  have h2t : 2 * ((a.primeFactorsList.flatMap W).length : ℝ) ≤ M := by
    rw [hlogB2] at hlen
    have : 16 * (2 * Real.log B) * Real.log a ≤ 16 * (2 * Real.log B) * Real.log N :=
      mul_le_mul_of_nonneg_left hloga (by positivity)
    rw [hlogN] at this hM1
    nlinarith
  have h2t' : 2 * (a.primeFactorsList.flatMap W).length ≤ M := by exact_mod_cast h2t
  apply hLift (A : _root_.Set ℕ) h0 a (Finset.mem_coe.mpr haA) _ hprod.symm
  intro r hr
  obtain ⟨q, hq, hrq⟩ := List.mem_flatMap.mp hr
  exact rich_mono ((hW' q hq).2.1 r hrq) h2t'

theorem main_of (hLift : LiftStmt) (hPairs : PairsStmt) (hHeavy : HeavyStmt) (hSmooth : SmoothStmt)
    (hQPart : QPartStmt) (hCore : CoreStmt) (hWords : WordsStmt) : MainStatement := by
  obtain ⟨c₀, hc₀, y₁, hsm⟩ := hSmooth
  obtain ⟨y₂, hqp⟩ := hQPart
  obtain ⟨ys, hys1, hys2, hys3⟩ : ∃ ys : ℝ, y₁ ≤ ys ∧ y₂ ≤ ys ∧ 2 ≤ ys :=
    ⟨max y₁ (max y₂ 2), le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _),
      (le_max_right _ _).trans (le_max_right _ _)⟩
  obtain ⟨p₀, hp₀pos, hp₀⟩ : ∃ p₀ : ℕ, (0:ℝ) < p₀ ∧ ys ^ 16 ≤ p₀ :=
    ⟨⌈ys ^ 16⌉₊ + 1, by positivity, by push_cast; linarith [Nat.le_ceil (ys ^ 16)]⟩
  obtain ⟨η, hη0, hη1, hη2, hη3⟩ : ∃ η : ℝ, 0 < η ∧ η ≤ c₀ / 6144 ∧ η ≤ 1 / 32 ∧
      η ≤ 1 / (4 * p₀) :=
    ⟨min (min (c₀ / 6144) (1/32)) (1 / (4 * p₀)),
      lt_min (lt_min (by positivity) (by norm_num)) (by positivity),
      (min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _),
      min_le_right _ _⟩
  refine ⟨η, hη0, ?_⟩
  filter_upwards [eventually_B (|y₁| + 14 * p₀ + 2)] with N hB
  obtain ⟨B, hB0, hBN, hBC, hlog⟩ := hB
  intro A hA hcard
  have hy₁B : y₁ ≤ B := by have := le_abs_self y₁; linarith
  have hB2 : 2 ≤ B := by have := abs_nonneg y₁; linarith
  have hBp₀ : 14 * (p₀:ℝ) ≤ B := by have := abs_nonneg y₁; linarith
  have hB1 : 1 ≤ B := by linarith
  have hNr : (N:ℝ) = B ^ 64 := hBN.symm
  have hNr0 : (0:ℝ) < N := by rw [hNr]; positivity
  have hN : 0 < N := by exact_mod_cast hNr0
  have hEc : ((Icc 1 N \ A).card : ℝ) ≤ η * N := card_E_le hA hcard
  have hE0 : (0:ℝ) ≤ (Icc 1 N \ A).card := Nat.cast_nonneg _
  have hηN1 : η * N ≤ c₀ / 6144 * N := mul_le_mul_of_nonneg_right hη1 hNr0.le
  have hηN2 : η * N ≤ 1 / 32 * N := mul_le_mul_of_nonneg_right hη2 hNr0.le
  have hc₀N : 0 < c₀ * N := mul_pos hc₀ hNr0
  have h32r : 32 * ((Icc 1 N \ A).card : ℝ) ≤ N := by linarith
  have h32 : 32 * (Icc 1 N \ A).card ≤ N := by exact_mod_cast h32r
  have hS : 3072 * ((Icc 1 N \ A).card : ℝ) / N ≤ c₀ / 2 := by
    rw [div_le_iff₀ hNr0]; linarith
  have hdef : 32 * ((Icc 1 N \ A).card : ℝ) ≤ c₀ / 2 * N := by linarith
  have hEsmall : ((Icc 1 N \ A).card : ℝ) < c₀ / 2 * N := by linarith
  have hM1 : Real.log N ^ 2 ≤ (⌈Real.log N ^ 2⌉₊ : ℕ) := Nat.le_ceil _
  have hM2 : ((⌈Real.log N ^ 2⌉₊ : ℕ) : ℝ) ≤ B + 1 := by
    have := Nat.ceil_lt_add_one (sq_nonneg (Real.log N)); linarith
  have hsmall := main_small hPairs hA hp₀pos hB0 hB1 hBp₀ hNr hEc hη3 hM2
  have hrepl := main_repl hPairs hHeavy hCore hc₀ hsm hqp hA hN h32 hS hdef hys1 hys2 hys3 hp₀
    hB0 hB2 hNr hM2
  have hW := hWords (A : _root_.Set ℕ) ⌈Real.log N ^ 2⌉₊ p₀
    (fun q => q.Prime ∧ ¬ Heavy N (Icc 1 N \ A) q ∧ (q:ℝ) ≤ B ^ 2) hsmall hrepl
  exact main_final hLift hHeavy hsm hA hN h32 hS hEsmall hB1 (by nlinarith) hNr hM1 hW

end OMA.Port8

end

-- ==== Main
section



open Finset Real Filter

namespace OMA.Port8

/-- **Main theorem (question (ii), distinct-factor version).** There is an absolute `η > 0` such that
for all large `N`, every `A ⊆ [1,N]` with `|A| ≥ (1-η)N` contains a violation. -/
theorem main : ∃ η : ℝ, 0 < η ∧ ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℕ, A ⊆ Icc 1 N →
    (1 - η) * N ≤ A.card → Violation (A : Set ℕ) :=
  main_of
    (fun A h0 a ha qs hp hr => violation_of_word A h0 a ha qs hp hr)
    (fun A h0 q hq L hL => rich_of_pairs A h0 q hq L hL)
    (fun N hN E hE hD H hH => heavy_recip_sum_le N hN E hE hD H hH)
    smooth_count qPart_tail
    (fun N p K γ hγ A hA Q hQ hp hpQ hpN hK ht hn hr hd =>
      core_pairs N p K γ hγ A hA Q hQ hp hpQ hpN hK ht hn hr hd)
    (fun A M p₀ good hs hst => short_word A M p₀ good hs hst)

end OMA.Port8

end

theorem OMA.disproof : ¬ (type_of% @Erdos786.erdos_786.parts.ii) :=
  OMA.Port8.not_partII_of_main OMA.Port8.main
