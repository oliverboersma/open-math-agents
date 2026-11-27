import FormalConjectures.GreensOpenProblems.«35»
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Nat.Log

/-!
# Improved Lower Bound for Ben Green's Open Problem 35 at p = 2

We establish `Green35.c 2 ≥ 473 / 625 = 0.7568`, strictly improving Ben Green's 2001 bound
`√(4 / 7) ≈ 0.7559289`, by pairing unit-interval densities on `AddCircle (2 : ℝ)` against a
bimodal degree-10 even polynomial kernel

  `kernP(t) = 63 / 25 - (6 / 5) * (2 * t) ^ 2 - (33 / 25) * (2 * t) ^ 10`

on `[-1 / 2, 1 / 2]`, and bounding the resulting Fourier series via an algebraic `rpow`-free
quartic Young inequality combined with a 63-term rational certificate, a dyadic geometric bound on
even frequencies, and a telescoping bound on odd frequencies.
-/

namespace BimodalKernelBound

open MeasureTheory Filter Topology
open scoped Convolution ENNReal Real

private instance : Fact ((0 : ℝ) < 2) := ⟨by norm_num⟩

/- ## Circle characters on `AddCircle (2 : ℝ)` -/

private lemma char2_coe (n : ℤ) (x : ℝ) :
    @fourier 2 n (x : AddCircle (2 : ℝ)) = Complex.exp (Real.pi * Complex.I * n * x) := by
  rw [fourier_coe_apply]
  congr 1
  push_cast; ring

private lemma char2_norm (n : ℤ) (x : ℝ) :
    ‖@fourier 2 n (x : AddCircle (2 : ℝ))‖ = 1 := by
  rw [fourier_apply, Circle.norm_coe]

private lemma char2_zero (x : ℝ) :
    @fourier 2 0 (x : AddCircle (2 : ℝ)) = 1 := by
  simp

private lemma char2_add (n : ℤ) (x y : ℝ) :
    @fourier 2 n ((x + y : ℝ) : AddCircle (2 : ℝ)) =
      @fourier 2 n (x : AddCircle (2 : ℝ)) * @fourier 2 n (y : AddCircle (2 : ℝ)) := by
  rw [char2_coe, char2_coe, char2_coe, ← Complex.exp_add]
  congr 1; push_cast; ring

private lemma char2_mul_conj (n m : ℤ) (x : ℝ) :
    @fourier 2 (-n) (x : AddCircle (2 : ℝ)) *
        starRingEnd ℂ (@fourier 2 (-m) (x : AddCircle (2 : ℝ))) =
      @fourier 2 (m - n) (x : AddCircle (2 : ℝ)) := by
  rw [← fourier_neg, neg_neg, char2_coe, char2_coe, char2_coe, ← Complex.exp_add]
  congr 1; push_cast; ring

private lemma intervalIntegral_char2 (k : ℤ) :
    ∫ x in (0 : ℝ)..2, @fourier 2 k (x : AddCircle (2 : ℝ)) = if k = 0 then (2 : ℂ) else 0 := by
  split_ifs with hk
  · subst hk
    simp_rw [char2_zero]
    simp
  · simp_rw [char2_coe]
    let z : ℂ := Real.pi * Complex.I * (k : ℂ)
    have hz : z ≠ 0 := by
      simp only [z, ne_eq, mul_eq_zero, Complex.ofReal_eq_zero, Real.pi_ne_zero,
        Complex.I_ne_zero, Int.cast_eq_zero, hk, or_self, not_false_eq_true]
    have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) 2,
        HasDerivAt (fun t : ℝ => Complex.exp (z * t) / z) (Complex.exp (z * x)) x := by
      intro x _
      have h1 : HasDerivAt (fun t : ℝ => z * (t : ℂ)) (z * 1) x :=
        (Complex.ofRealCLM.hasDerivAt).const_mul z
      rw [mul_one] at h1
      have h2 := h1.cexp.div_const z
      rwa [mul_div_cancel_right₀ _ hz] at h2
    have hint : IntervalIntegrable (fun x : ℝ => Complex.exp (z * (x : ℂ))) volume 0 2 :=
      Continuous.intervalIntegrable (by fun_prop) 0 2
    have hval := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    have hrew : (fun x : ℝ => Complex.exp (Real.pi * Complex.I * (k : ℂ) * (x : ℂ))) =
        (fun x : ℝ => Complex.exp (z * (x : ℂ))) := rfl
    rw [hrew, hval]
    have hexp2 : Complex.exp (z * (2 : ℂ)) = 1 := by
      have : z * (2 : ℂ) = (k : ℂ) * (2 * Real.pi * Complex.I) := by simp only [z]; ring
      rw [this, Complex.exp_int_mul_two_pi_mul_I]
    simp [hexp2]

/- ## Bimodal even polynomial kernel `kernP` and circle test function `V` -/

private noncomputable def kernP (t : ℝ) : ℝ :=
  (63 / 25 : ℝ) - (6 / 5 : ℝ) * (2 * t) ^ 2 - (33 / 25 : ℝ) * (2 * t) ^ 10

private lemma kernP_even (t : ℝ) : kernP (-t) = kernP t := by
  unfold kernP; ring

private lemma kernP_neg_half : kernP (-1 / 2) = 0 := by
  unfold kernP; norm_num

private lemma kernP_pos_half : kernP (1 / 2) = 0 := by
  unfold kernP; norm_num

private lemma integral_kernP : ∫ t in (-1 / 2 : ℝ)..(1 / 2), kernP t = 2 := by
  have hrew : (fun t : ℝ => kernP t) =
      fun t : ℝ => ((63 / 25 : ℝ) - (24 / 5 : ℝ) * t ^ 2) - (33792 / 25 : ℝ) * t ^ 10 := by
    funext t; unfold kernP; ring
  have hi2 : IntervalIntegrable (fun t : ℝ => (24 / 5 : ℝ) * t ^ 2) volume (-1 / 2) (1 / 2) :=
    ((continuous_pow 2).intervalIntegrable _ _).const_mul _
  have hi10 : IntervalIntegrable (fun t : ℝ => (33792 / 25 : ℝ) * t ^ 10) volume (-1 / 2) (1 / 2) :=
    ((continuous_pow 10).intervalIntegrable _ _).const_mul _
  rw [hrew, intervalIntegral.integral_sub (intervalIntegrable_const.sub hi2) hi10,
    intervalIntegral.integral_sub intervalIntegrable_const hi2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const, integral_pow, integral_pow]
  norm_num

private noncomputable def vRaw (x : ℝ) : ℂ :=
  if x ≤ 1 then (1 : ℂ) else ((1 - kernP (x - 3 / 2) : ℝ) : ℂ)

private lemma vRaw_zero : vRaw 0 = 1 := by
  simp [vRaw]

private lemma vRaw_two : vRaw 2 = 1 := by
  have h2 : ¬ ((2 : ℝ) ≤ 1) := by norm_num
  have hsub : (2 : ℝ) - 3 / 2 = 1 / 2 := by norm_num
  simp only [vRaw, h2, ↓reduceIte, hsub, kernP_pos_half, sub_zero, Complex.ofReal_one]

private lemma vRaw_continuous : Continuous vRaw := by
  have hc1 : Continuous (fun _ : ℝ => (1 : ℂ)) := continuous_const
  have hc2 : Continuous (fun x : ℝ => ((1 - kernP (x - 3 / 2) : ℝ) : ℂ)) := by
    unfold kernP; fun_prop
  refine Continuous.if_le hc1 hc2 continuous_id continuous_const ?_
  intro x hx
  subst hx
  have hsub : (1 : ℝ) - 3 / 2 = -1 / 2 := by norm_num
  simp [hsub, kernP_neg_half]

private noncomputable def V : C(AddCircle (2 : ℝ), ℂ) :=
  ⟨AddCircle.liftIco (2 : ℝ) 0 vRaw,
    AddCircle.liftIco_zero_continuous (by rw [vRaw_zero, vRaw_two]) vRaw_continuous.continuousOn⟩

private lemma V_coe_of_mem_Ico {x : ℝ} (hx : x ∈ Set.Ico (0 : ℝ) 2) :
    V (x : AddCircle (2 : ℝ)) = vRaw x := by
  change AddCircle.liftIco (2 : ℝ) 0 vRaw x = vRaw x
  exact AddCircle.liftIco_zero_coe_apply hx

private lemma V_coe_of_mem_Icc01 {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    V (x : AddCircle (2 : ℝ)) = 1 := by
  rw [V_coe_of_mem_Ico ⟨hx.1, by linarith [hx.2]⟩]
  simp [vRaw, hx.2]

private lemma V_coe_two : V ((2 : ℝ) : AddCircle (2 : ℝ)) = 1 := by
  have h0 : ((2 : ℝ) : AddCircle (2 : ℝ)) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨1, by norm_num⟩
  rw [h0, ← QuotientAddGroup.mk_zero, V_coe_of_mem_Ico ⟨le_rfl, by norm_num⟩, vRaw_zero]

private lemma V_coe_eq_vRaw_on_Icc {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 2) :
    V (x : AddCircle (2 : ℝ)) = vRaw x := by
  by_cases hlt : x < 2
  · exact V_coe_of_mem_Ico ⟨hx.1, hlt⟩
  · have hx2 : x = 2 := le_antisymm hx.2 (le_of_not_gt hlt)
    subst hx2
    rw [V_coe_two, vRaw_two]

/- ## Fourier coefficients of `V` -/

private noncomputable def kernHat (r : ℕ) : ℝ :=
  |∫ t in (-1 / 2 : ℝ)..(1 / 2), kernP t * Real.cos (Real.pi * (r : ℝ) * t)|

private lemma integral_kernP_mul_exp (n : ℤ) :
    ∫ t in (-1 / 2 : ℝ)..(1 / 2),
        (kernP t : ℂ) * Complex.exp (-(Real.pi * Complex.I * (n : ℂ) * (t : ℂ))) =
      ((∫ t in (-1 / 2 : ℝ)..(1 / 2), kernP t * Real.cos (Real.pi * (n : ℝ) * t) : ℝ) : ℂ) := by
  have hsplit : ∀ t : ℝ,
      (kernP t : ℂ) * Complex.exp (-(Real.pi * Complex.I * (n : ℂ) * (t : ℂ))) =
        ((kernP t * Real.cos (Real.pi * (n : ℝ) * t) : ℝ) : ℂ) -
        Complex.I * ((kernP t * Real.sin (Real.pi * (n : ℝ) * t) : ℝ) : ℂ) := by
    intro t
    have harg : -(Real.pi * Complex.I * (n : ℂ) * (t : ℂ)) =
        ((-(Real.pi * (n : ℝ) * t) : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [harg, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_neg, Real.sin_neg]
    push_cast; ring
  simp_rw [hsplit]
  have hi_cos : IntervalIntegrable
      (fun t : ℝ => ((kernP t * Real.cos (Real.pi * (n : ℝ) * t) : ℝ) : ℂ))
      volume (-1 / 2) (1 / 2) :=
    Continuous.intervalIntegrable (by unfold kernP; fun_prop) _ _
  have hi_sin : IntervalIntegrable
      (fun t : ℝ => Complex.I * ((kernP t * Real.sin (Real.pi * (n : ℝ) * t) : ℝ) : ℂ))
      volume (-1 / 2) (1 / 2) :=
    Continuous.intervalIntegrable (by unfold kernP; fun_prop) _ _
  rw [intervalIntegral.integral_sub hi_cos hi_sin, intervalIntegral.integral_const_mul]
  have hsin_zero : ∫ t in (-1 / 2 : ℝ)..(1 / 2), kernP t * Real.sin (Real.pi * (n : ℝ) * t) = 0 := by
    have hneg : ∫ t in (-1 / 2 : ℝ)..(1 / 2), kernP t * Real.sin (Real.pi * (n : ℝ) * t) =
        ∫ t in (-1 / 2 : ℝ)..(1 / 2), kernP (-t) * Real.sin (Real.pi * (n : ℝ) * (-t)) := by
      have h := intervalIntegral.integral_comp_neg
        (f := fun t : ℝ => kernP t * Real.sin (Real.pi * (n : ℝ) * t))
        (a := (-1 / 2 : ℝ)) (b := 1 / 2)
      rw [show -(-1 / 2 : ℝ) = 1 / 2 by norm_num, show -(1 / 2 : ℝ) = -1 / 2 by norm_num] at h
      exact h.symm
    have hodd : (fun t : ℝ => kernP (-t) * Real.sin (Real.pi * (n : ℝ) * (-t))) =
        fun t : ℝ => -(kernP t * Real.sin (Real.pi * (n : ℝ) * t)) := by
      funext t; rw [kernP_even, mul_neg, Real.sin_neg]; ring
    rw [hodd, intervalIntegral.integral_neg] at hneg
    linarith
  rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal, hsin_zero]
  simp

private lemma fourierCoeff_V_zero : fourierCoeff V 0 = 0 := by
  rw [fourierCoeff_eq_intervalIntegral V 0 0, show (0 : ℝ) + 2 = 2 by norm_num]
  have heq : Set.EqOn (fun x : ℝ => @fourier 2 (-0) (x : AddCircle (2 : ℝ)) • V x)
      vRaw (Set.uIcc 0 2) := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] at hx
    simp only [neg_zero, char2_zero, smul_eq_mul, one_mul, V_coe_eq_vRaw_on_Icc hx]
  rw [intervalIntegral.integral_congr heq]
  have hi1 : IntervalIntegrable vRaw volume 0 1 := vRaw_continuous.intervalIntegrable 0 1
  have hi2 : IntervalIntegrable vRaw volume 1 2 := vRaw_continuous.intervalIntegrable 1 2
  rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
  have hpart1 : ∫ x in (0 : ℝ)..1, vRaw x = 1 := by
    have h1 : Set.EqOn vRaw (fun _ => (1 : ℂ)) (Set.uIcc 0 1) := by
      intro x hx
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
      simp [vRaw, hx.2]
    rw [intervalIntegral.integral_congr h1]
    simp
  have hpart2 : ∫ x in (1 : ℝ)..2, vRaw x = -1 := by
    have h2 : Set.EqOn vRaw (fun x : ℝ => ((1 - kernP (x - 3 / 2) : ℝ) : ℂ)) (Set.uIcc 1 2) := by
      intro x hx
      rw [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at hx
      by_cases hx1 : x ≤ 1
      · have hx_eq : x = 1 := le_antisymm hx1 hx.1
        subst hx_eq
        have hsub : (1 : ℝ) - 3 / 2 = -1 / 2 := by norm_num
        simp [vRaw, hsub, kernP_neg_half]
      · simp [vRaw, hx1]
    rw [intervalIntegral.integral_congr h2, intervalIntegral.integral_ofReal]
    have hr : ∫ x in (1 : ℝ)..2, (1 - kernP (x - 3 / 2)) = -1 := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const
        (Continuous.intervalIntegrable (by unfold kernP; fun_prop) 1 2)]
      have hshift := intervalIntegral.integral_comp_sub_right kernP (3 / 2 : ℝ) (a := (1 : ℝ)) (b := 2)
      rw [show (1 : ℝ) - 3 / 2 = -1 / 2 by norm_num, show (2 : ℝ) - 3 / 2 = 1 / 2 by norm_num] at hshift
      rw [hshift, integral_kernP]
      norm_num
    rw [hr]; norm_num
  rw [hpart1, hpart2]; simp

private lemma norm_fourierCoeff_V (n : ℤ) (hn : n ≠ 0) :
    ‖fourierCoeff V n‖ = kernHat n.natAbs / 2 := by
  rw [fourierCoeff_eq_intervalIntegral V n 0, show (0 : ℝ) + 2 = 2 by norm_num]
  have heq : Set.EqOn (fun x : ℝ => @fourier 2 (-n) (x : AddCircle (2 : ℝ)) • V x)
      (fun x : ℝ => @fourier 2 (-n) (x : AddCircle (2 : ℝ)) * vRaw x) (Set.uIcc 0 2) := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] at hx
    simp only [smul_eq_mul, V_coe_eq_vRaw_on_Icc hx]
  rw [intervalIntegral.integral_congr heq]
  have hcont_f : Continuous (fun x : ℝ => @fourier 2 (-n) (x : AddCircle (2 : ℝ))) := by
    simp_rw [char2_coe]; fun_prop
  have hsplit : ∫ x in (0 : ℝ)..2, @fourier 2 (-n) (x : AddCircle (2 : ℝ)) * vRaw x =
      (∫ x in (0 : ℝ)..2, @fourier 2 (-n) (x : AddCircle (2 : ℝ))) -
      ∫ x in (1 : ℝ)..2, @fourier 2 (-n) (x : AddCircle (2 : ℝ)) * (kernP (x - 3 / 2) : ℂ) := by
    have hi1 : IntervalIntegrable
        (fun x : ℝ => @fourier 2 (-n) (x : AddCircle (2 : ℝ)) * vRaw x) volume 0 1 :=
      (hcont_f.mul vRaw_continuous).intervalIntegrable 0 1
    have hi2 : IntervalIntegrable
        (fun x : ℝ => @fourier 2 (-n) (x : AddCircle (2 : ℝ)) * vRaw x) volume 1 2 :=
      (hcont_f.mul vRaw_continuous).intervalIntegrable 1 2
    rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
    have hi_f1 : IntervalIntegrable
        (fun x : ℝ => @fourier 2 (-n) (x : AddCircle (2 : ℝ))) volume 0 1 :=
      hcont_f.intervalIntegrable 0 1
    have hi_f2 : IntervalIntegrable
        (fun x : ℝ => @fourier 2 (-n) (x : AddCircle (2 : ℝ))) volume 1 2 :=
      hcont_f.intervalIntegrable 1 2
    rw [← intervalIntegral.integral_add_adjacent_intervals hi_f1 hi_f2]
    have hpart1 : ∫ x in (0 : ℝ)..1, @fourier 2 (-n) (x : AddCircle (2 : ℝ)) * vRaw x =
        ∫ x in (0 : ℝ)..1, @fourier 2 (-n) (x : AddCircle (2 : ℝ)) := by
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
      simp [vRaw, hx.2]
    have hpart2 : ∫ x in (1 : ℝ)..2, @fourier 2 (-n) (x : AddCircle (2 : ℝ)) * vRaw x =
        (∫ x in (1 : ℝ)..2, @fourier 2 (-n) (x : AddCircle (2 : ℝ))) -
        ∫ x in (1 : ℝ)..2, @fourier 2 (-n) (x : AddCircle (2 : ℝ)) * (kernP (x - 3 / 2) : ℂ) := by
      have hcongr : Set.EqOn
          (fun x : ℝ => @fourier 2 (-n) (x : AddCircle (2 : ℝ)) * vRaw x)
          (fun x : ℝ => @fourier 2 (-n) (x : AddCircle (2 : ℝ)) -
            @fourier 2 (-n) (x : AddCircle (2 : ℝ)) * (kernP (x - 3 / 2) : ℂ))
          (Set.uIcc 1 2) := by
        intro x hx
        rw [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at hx
        by_cases hx1 : x ≤ 1
        · have hx_eq : x = 1 := le_antisymm hx1 hx.1
          subst hx_eq
          have hsub : (1 : ℝ) - 3 / 2 = -1 / 2 := by norm_num
          simp [vRaw, hsub, kernP_neg_half]
        · simp [vRaw, hx1]; ring
      rw [intervalIntegral.integral_congr hcongr]
      exact intervalIntegral.integral_sub hi_f2
        (Continuous.intervalIntegrable (by unfold kernP; fun_prop) 1 2)
    rw [hpart1, hpart2]; ring
  rw [hsplit, intervalIntegral_char2 (-n), if_neg (neg_ne_zero.mpr hn), zero_sub]
  have hshift : ∫ x in (1 : ℝ)..2,
        @fourier 2 (-n) (x : AddCircle (2 : ℝ)) * (kernP (x - 3 / 2) : ℂ) =
      Complex.exp (-(Real.pi * Complex.I * (n : ℂ) * (3 / 2 : ℂ))) *
      ∫ t in (-1 / 2 : ℝ)..(1 / 2),
        (kernP t : ℂ) * Complex.exp (-(Real.pi * Complex.I * (n : ℂ) * (t : ℂ))) := by
    have hstep : ∀ x : ℝ,
        @fourier 2 (-n) (x : AddCircle (2 : ℝ)) * (kernP (x - 3 / 2) : ℂ) =
          Complex.exp (-(Real.pi * Complex.I * (n : ℂ) * (3 / 2 : ℂ))) *
          ((kernP (x - 3 / 2) : ℂ) *
            Complex.exp (-(Real.pi * Complex.I * (n : ℂ) * ((x - 3 / 2 : ℝ) : ℂ)))) := by
      intro x
      rw [char2_coe]
      have hexp : Complex.exp (Real.pi * Complex.I * ((-n : ℤ) : ℂ) * (x : ℂ)) =
          Complex.exp (-(Real.pi * Complex.I * (n : ℂ) * (3 / 2 : ℂ))) *
          Complex.exp (-(Real.pi * Complex.I * (n : ℂ) * ((x - 3 / 2 : ℝ) : ℂ))) := by
        rw [← Complex.exp_add]; congr 1; push_cast; ring
      rw [hexp]; ring
    simp_rw [hstep]
    rw [intervalIntegral.integral_const_mul]
    congr 1
    have hcomp := intervalIntegral.integral_comp_sub_right
      (fun t : ℝ => (kernP t : ℂ) * Complex.exp (-(Real.pi * Complex.I * (n : ℂ) * (t : ℂ))))
      (3 / 2 : ℝ) (a := (1 : ℝ)) (b := 2)
    rw [show (1 : ℝ) - 3 / 2 = -1 / 2 by norm_num, show (2 : ℝ) - 3 / 2 = 1 / 2 by norm_num] at hcomp
    exact hcomp
  rw [hshift, integral_kernP_mul_exp]
  rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2), norm_neg, norm_mul]
  have hexp_norm : ‖Complex.exp (-(Real.pi * Complex.I * (n : ℂ) * (3 / 2 : ℂ)))‖ = 1 := by
    have : -(Real.pi * Complex.I * (n : ℂ) * (3 / 2 : ℂ)) =
        ((-(Real.pi * (n : ℝ) * (3 / 2)) : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  rw [hexp_norm, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have hcos_abs :
      (fun t : ℝ => kernP t * Real.cos (Real.pi * (n : ℝ) * t)) =
      (fun t : ℝ => kernP t * Real.cos (Real.pi * (n.natAbs : ℝ) * t)) := by
    funext t
    rcases Int.natAbs_eq n with h | h
    · have hn' : (n : ℝ) = (n.natAbs : ℝ) := by conv_lhs => rw [h]; rw [Int.cast_natCast]
      rw [hn']
    · have hn' : (n : ℝ) = -(n.natAbs : ℝ) := by
        conv_lhs => rw [h]; rw [Int.cast_neg, Int.cast_natCast]
      rw [hn', show Real.pi * -(n.natAbs : ℝ) * t = -(Real.pi * (n.natAbs : ℝ) * t) by ring,
        Real.cos_neg]
  rw [hcos_abs]
  unfold kernHat; ring

/- ## Exact integration by parts and bounds for `kernHat` -/

private lemma pi_gt_d9 : (3141592653 / 10 ^ 9 : ℝ) < Real.pi := by
  linarith [Real.pi_gt_d20]

private lemma pi_lt_d9 : Real.pi < (3141592654 / 10 ^ 9 : ℝ) := by
  linarith [Real.pi_lt_d20]

private lemma integral_kernP_cos (x : ℝ) (hx : x ≠ 0) :
    ∫ t in (-1 / 2 : ℝ)..(1 / 2), kernP t * Real.cos (x * t) =
      ((4848 / 5) / x ^ 3 - (1064448 / 5) / x ^ 5 + 25546752 / x ^ 7 -
        1226244096 / x ^ 9 + 9809952768 / x ^ 11) * Real.sin (x / 2) +
      (-(312 / 5) / x ^ 2 + (76032 / 5) / x ^ 4 - (12773376 / 5) / x ^ 6 +
        204374016 / x ^ 8 - 4904976384 / x ^ 10) * Real.cos (x / 2) := by
  let a0 : ℝ := (63 / 25) / x + (48 / 5) / x ^ 3 + 4904976384 / x ^ 11
  let a2 : ℝ := -(24 / 5) / x - 2452488192 / x ^ 9
  let a4 : ℝ := 204374016 / x ^ 7
  let a6 : ℝ := -(34062336 / 5) / x ^ 5
  let a8 : ℝ := (608256 / 5) / x ^ 3
  let a10 : ℝ := -(33792 / 25) / x
  let b1 : ℝ := -(48 / 5) / x ^ 2 - 4904976384 / x ^ 10
  let b3 : ℝ := 817496064 / x ^ 8
  let b5 : ℝ := -(204374016 / 5) / x ^ 6
  let b7 : ℝ := (4866048 / 5) / x ^ 4
  let b9 : ℝ := -(67584 / 5) / x ^ 2
  let A : ℝ → ℝ := fun t =>
    a0 + a2 * t ^ 2 + a4 * t ^ 4 + a6 * t ^ 6 + a8 * t ^ 8 + a10 * t ^ 10
  let B : ℝ → ℝ := fun t =>
    b1 * t + b3 * t ^ 3 + b5 * t ^ 5 + b7 * t ^ 7 + b9 * t ^ 9
  let F : ℝ → ℝ := fun t => A t * Real.sin (x * t) + B t * Real.cos (x * t)
  have hderiv : ∀ t ∈ Set.uIcc (-1 / 2 : ℝ) (1 / 2),
      HasDerivAt F (kernP t * Real.cos (x * t)) t := by
    intro t _
    have hA : HasDerivAt A
        (0 + a2 * ((2 : ℕ) * t ^ 1) + a4 * ((4 : ℕ) * t ^ 3) +
          a6 * ((6 : ℕ) * t ^ 5) + a8 * ((8 : ℕ) * t ^ 7) + a10 * ((10 : ℕ) * t ^ 9)) t :=
      (((((hasDerivAt_const t a0).add ((hasDerivAt_pow 2 t).const_mul a2)).add
        ((hasDerivAt_pow 4 t).const_mul a4)).add
        ((hasDerivAt_pow 6 t).const_mul a6)).add
        ((hasDerivAt_pow 8 t).const_mul a8)).add
        ((hasDerivAt_pow 10 t).const_mul a10)
    have hB : HasDerivAt B
        (b1 * 1 + b3 * ((3 : ℕ) * t ^ 2) + b5 * ((5 : ℕ) * t ^ 4) +
          b7 * ((7 : ℕ) * t ^ 6) + b9 * ((9 : ℕ) * t ^ 8)) t :=
      ((((hasDerivAt_id t).const_mul b1).add
        ((hasDerivAt_pow 3 t).const_mul b3)).add
        ((hasDerivAt_pow 5 t).const_mul b5)).add
        ((hasDerivAt_pow 7 t).const_mul b7) |>.add
        ((hasDerivAt_pow 9 t).const_mul b9)
    have hxt : HasDerivAt (fun u : ℝ => x * u) x t := by
      simpa using (hasDerivAt_id t).const_mul x
    have hsin : HasDerivAt (fun u : ℝ => Real.sin (x * u)) (Real.cos (x * t) * x) t :=
      (Real.hasDerivAt_sin (x * t)).comp t hxt
    have hcos : HasDerivAt (fun u : ℝ => Real.cos (x * u)) (-Real.sin (x * t) * x) t :=
      (Real.hasDerivAt_cos (x * t)).comp t hxt
    exact ((hA.mul hsin).add (hB.mul hcos)).congr_deriv (by
      unfold kernP
      dsimp only [A, B, a0, a2, a4, a6, a8, a10, b1, b3, b5, b7, b9]
      push_cast
      field_simp [hx]
      ring)
  have hint : IntervalIntegrable (fun t : ℝ => kernP t * Real.cos (x * t))
      volume (-1 / 2) (1 / 2) :=
    Continuous.intervalIntegrable (by unfold kernP; fun_prop) _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have h1 : x * (-1 / 2 : ℝ) = -(x / 2) := by ring
  have h2 : x * (1 / 2 : ℝ) = x / 2 := by ring
  dsimp only [F, A, B, a0, a2, a4, a6, a8, a10, b1, b3, b5, b7, b9]
  rw [h1, h2, Real.sin_neg, Real.cos_neg]
  ring

private lemma kernHat_even_eq (m : ℕ) (hm : 1 ≤ m) :
    kernHat (2 * m) =
      (312 / 5) / (Real.pi * (2 * m : ℝ)) ^ 2 -
      (76032 / 5) / (Real.pi * (2 * m : ℝ)) ^ 4 +
      (12773376 / 5) / (Real.pi * (2 * m : ℝ)) ^ 6 -
      204374016 / (Real.pi * (2 * m : ℝ)) ^ 8 +
      4904976384 / (Real.pi * (2 * m : ℝ)) ^ 10 := by
  have hx : Real.pi * ((2 * m : ℕ) : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (2 * m : ℕ) := by exact_mod_cast (by omega : 0 < 2 * m)
    exact mul_ne_zero Real.pi_ne_zero this.ne'
  unfold kernHat
  rw [integral_kernP_cos _ hx]
  have harg : Real.pi * ((2 * m : ℕ) : ℝ) / 2 = (m : ℝ) * Real.pi := by push_cast; ring
  rw [harg, Real.sin_nat_mul_pi, mul_zero, zero_add, Real.cos_nat_mul_pi]
  have hcast : ((2 * m : ℕ) : ℝ) = (2 * m : ℝ) := by push_cast; ring
  rw [hcast]
  set x : ℝ := Real.pi * (2 * m : ℝ)
  have hxpos : 0 < x := by
    have : (0 : ℝ) < m := by exact_mod_cast hm
    positivity
  have hval_pos : 0 < (312 / 5) / x ^ 2 - (76032 / 5) / x ^ 4 +
      (12773376 / 5) / x ^ 6 - 204374016 / x ^ 8 + 4904976384 / x ^ 10 := by
    by_cases hm1 : m = 1
    · subst hm1
      have hlo : (3141592653 / 10 ^ 9 : ℝ) * (2 * (1 : ℕ) : ℝ) < x := by
        simp only [x]; nlinarith [pi_gt_d9]
      have hhi : x < (3141592654 / 10 ^ 9 : ℝ) * (2 * (1 : ℕ) : ℝ) := by
        simp only [x]; nlinarith [pi_lt_d9]
      have hb1 : (312 / 5 : ℝ) / ((3141592654 / 10 ^ 9 : ℝ) * 2) ^ 2 ≤ (312 / 5) / x ^ 2 := by
        gcongr; simpa using hhi.le
      have hb2 : (76032 / 5 : ℝ) / x ^ 4 ≤ (76032 / 5) / ((3141592653 / 10 ^ 9 : ℝ) * 2) ^ 4 := by
        gcongr; simpa using hlo.le
      have hb3 : (12773376 / 5 : ℝ) / ((3141592654 / 10 ^ 9 : ℝ) * 2) ^ 6 ≤
          (12773376 / 5) / x ^ 6 := by
        gcongr; simpa using hhi.le
      have hb4 : (204374016 : ℝ) / x ^ 8 ≤ 204374016 / ((3141592653 / 10 ^ 9 : ℝ) * 2) ^ 8 := by
        gcongr; simpa using hlo.le
      have hb5 : (4904976384 : ℝ) / ((3141592654 / 10 ^ 9 : ℝ) * 2) ^ 10 ≤
          4904976384 / x ^ 10 := by
        gcongr; simpa using hhi.le
      have hnum : (0 : ℝ) < (312 / 5) / ((3141592654 / 10 ^ 9 : ℝ) * 2) ^ 2 -
          (76032 / 5) / ((3141592653 / 10 ^ 9 : ℝ) * 2) ^ 4 +
          (12773376 / 5) / ((3141592654 / 10 ^ 9 : ℝ) * 2) ^ 6 -
          204374016 / ((3141592653 / 10 ^ 9 : ℝ) * 2) ^ 8 +
          4904976384 / ((3141592654 / 10 ^ 9 : ℝ) * 2) ^ 10 := by norm_num
      linarith
    · have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 2 ≤ m)
      have hx_ge : (1256 / 100 : ℝ) ≤ x := by simp only [x]; nlinarith [pi_gt_d9]
      set u : ℝ := x ^ 2 - 155
      have hu : 0 ≤ u := by simp only [u]; nlinarith
      have hfac : (312 / 5) / x ^ 2 - (76032 / 5) / x ^ 4 +
          (12773376 / 5) / x ^ 6 - 204374016 / x ^ 8 + 4904976384 / x ^ 10 =
          (312 * u ^ 4 + 117408 * u ^ 3 + 22393296 * u ^ 2 +
            2105266080 * u + 69968308920) / (5 * x ^ 10) := by
        simp only [u]; field_simp [hxpos.ne']; ring
      rw [hfac]
      positivity
  have hrew : (-(312 / 5) / x ^ 2 + (76032 / 5) / x ^ 4 - (12773376 / 5) / x ^ 6 +
        204374016 / x ^ 8 - 4904976384 / x ^ 10) * (-1) ^ m =
      -((-1) ^ m * ((312 / 5) / x ^ 2 - (76032 / 5) / x ^ 4 + (12773376 / 5) / x ^ 6 -
        204374016 / x ^ 8 + 4904976384 / x ^ 10)) := by ring
  rw [hrew, abs_neg, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_pos hval_pos]

private lemma kernHat_odd_eq (k : ℕ) :
    kernHat (2 * k + 1) =
      (4848 / 5) / (Real.pi * (2 * k + 1 : ℝ)) ^ 3 -
      (1064448 / 5) / (Real.pi * (2 * k + 1 : ℝ)) ^ 5 +
      25546752 / (Real.pi * (2 * k + 1 : ℝ)) ^ 7 -
      1226244096 / (Real.pi * (2 * k + 1 : ℝ)) ^ 9 +
      9809952768 / (Real.pi * (2 * k + 1 : ℝ)) ^ 11 := by
  have hx : Real.pi * ((2 * k + 1 : ℕ) : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (2 * k + 1 : ℕ) := by exact_mod_cast (Nat.succ_pos (2 * k))
    exact mul_ne_zero Real.pi_ne_zero this.ne'
  unfold kernHat
  rw [integral_kernP_cos _ hx]
  have harg : Real.pi * ((2 * k + 1 : ℕ) : ℝ) / 2 = (k : ℝ) * Real.pi + Real.pi / 2 := by
    push_cast; ring
  rw [harg, Real.sin_add_pi_div_two, Real.cos_add_pi_div_two,
    Real.sin_nat_mul_pi, Real.cos_nat_mul_pi, neg_zero, mul_zero, add_zero]
  have hcast : ((2 * k + 1 : ℕ) : ℝ) = (2 * k + 1 : ℝ) := by push_cast; ring
  rw [hcast]
  set x : ℝ := Real.pi * (2 * k + 1 : ℝ)
  have hxpos : 0 < x := mul_pos Real.pi_pos (by positivity)
  have hval_pos : 0 < (4848 / 5) / x ^ 3 - (1064448 / 5) / x ^ 5 +
      25546752 / x ^ 7 - 1226244096 / x ^ 9 + 9809952768 / x ^ 11 := by
    by_cases hk0 : k = 0
    · subst hk0
      have hx_eq : x = Real.pi := by simp [x]
      have hlo := pi_gt_d9
      have hhi := pi_lt_d9
      rw [hx_eq] at hxpos ⊢
      have hb1 : (4848 / 5 : ℝ) / (3141592654 / 10 ^ 9 : ℝ) ^ 3 ≤ (4848 / 5) / Real.pi ^ 3 := by
        gcongr
      have hb2 : (1064448 / 5 : ℝ) / Real.pi ^ 5 ≤
          (1064448 / 5) / (3141592653 / 10 ^ 9 : ℝ) ^ 5 := by gcongr
      have hb3 : (25546752 : ℝ) / (3141592654 / 10 ^ 9 : ℝ) ^ 7 ≤ 25546752 / Real.pi ^ 7 := by
        gcongr
      have hb4 : (1226244096 : ℝ) / Real.pi ^ 9 ≤
          1226244096 / (3141592653 / 10 ^ 9 : ℝ) ^ 9 := by gcongr
      have hb5 : (9809952768 : ℝ) / (3141592654 / 10 ^ 9 : ℝ) ^ 11 ≤
          9809952768 / Real.pi ^ 11 := by gcongr
      have hnum : (0 : ℝ) < (4848 / 5) / (3141592654 / 10 ^ 9 : ℝ) ^ 3 -
          (1064448 / 5) / (3141592653 / 10 ^ 9 : ℝ) ^ 5 +
          25546752 / (3141592654 / 10 ^ 9 : ℝ) ^ 7 -
          1226244096 / (3141592653 / 10 ^ 9 : ℝ) ^ 9 +
          9809952768 / (3141592654 / 10 ^ 9 : ℝ) ^ 11 := by norm_num
      linarith
    · have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
      have hx_ge : (942 / 100 : ℝ) ≤ x := by simp only [x]; nlinarith [pi_gt_d9]
      set u : ℝ := x ^ 2 - 88
      have hu : 0 ≤ u := by simp only [u]; nlinarith
      have hfac : (4848 / 5) / x ^ 3 - (1064448 / 5) / x ^ 5 +
          25546752 / x ^ 7 - 1226244096 / x ^ 9 + 9809952768 / x ^ 11 =
          (4848 * u ^ 4 + 642048 * u ^ 3 + 71976960 * u ^ 2 +
            4835770368 * u + 64013402112) / (5 * x ^ 11) := by
        simp only [u]; field_simp [hxpos.ne']; ring
      rw [hfac]
      positivity
  have hrew : ((4848 / 5) / x ^ 3 - (1064448 / 5) / x ^ 5 + 25546752 / x ^ 7 -
        1226244096 / x ^ 9 + 9809952768 / x ^ 11) * (-1) ^ k =
      (-1) ^ k * ((4848 / 5) / x ^ 3 - (1064448 / 5) / x ^ 5 + 25546752 / x ^ 7 -
        1226244096 / x ^ 9 + 9809952768 / x ^ 11) := by ring
  rw [hrew, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_pos hval_pos]

private lemma kernHat_even_le_main (m : ℕ) (hm : 1 ≤ m) :
    kernHat (2 * m) ≤ (78 / 5) / (Real.pi ^ 2 * (m : ℝ) ^ 2) := by
  set x : ℝ := Real.pi * (2 * m : ℝ)
  have hm_ge : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hx_ge : (628 / 100 : ℝ) ≤ x := by simp only [x]; nlinarith [pi_gt_d9]
  have hxpos : 0 < x := by linarith
  set u : ℝ := x ^ 2 - 39
  have hu : 0 ≤ u := by simp only [u]; nlinarith
  have hdiff : (312 / 5) / x ^ 2 - kernHat (2 * m) =
      (76032 * u * (u - 26) ^ 2 + 76032 * u ^ 2 + 321083136 * u + 409888512) / (5 * x ^ 10) := by
    rw [kernHat_even_eq m hm]
    simp only [x, u]
    field_simp [hxpos.ne']
    ring
  have hnn : 0 ≤ (312 / 5) / x ^ 2 - kernHat (2 * m) := by rw [hdiff]; positivity
  have hlead : (312 / 5) / x ^ 2 = (78 / 5) / (Real.pi ^ 2 * (m : ℝ) ^ 2) := by
    simp only [x]; field_simp [Real.pi_ne_zero, (by linarith : (m : ℝ) ≠ 0)]; ring
  linarith

private lemma kernHat_odd_le_main (k : ℕ) :
    kernHat (2 * k + 1) ≤ (4848 / 5) / (Real.pi ^ 3 * (2 * k + 1 : ℝ) ^ 3) := by
  rw [kernHat_odd_eq k]
  set x : ℝ := Real.pi * (2 * k + 1 : ℝ)
  have hxpos : 0 < x := mul_pos Real.pi_pos (by positivity)
  have hlead : (4848 / 5) / x ^ 3 = (4848 / 5) / (Real.pi ^ 3 * (2 * k + 1 : ℝ) ^ 3) := by
    simp only [x]; ring
  by_cases hk0 : k = 0
  · subst hk0
    have hx_eq : x = Real.pi := by simp [x]
    have hlo := pi_gt_d9
    have hhi := pi_lt_d9
    rw [← hlead, hx_eq]
    have hb2 : (1064448 / 5 : ℝ) / (3141592654 / 10 ^ 9 : ℝ) ^ 5 ≤
        (1064448 / 5) / Real.pi ^ 5 := by gcongr
    have hb3 : (25546752 : ℝ) / Real.pi ^ 7 ≤
        25546752 / (3141592653 / 10 ^ 9 : ℝ) ^ 7 := by gcongr
    have hb4 : (1226244096 : ℝ) / (3141592654 / 10 ^ 9 : ℝ) ^ 9 ≤
        1226244096 / Real.pi ^ 9 := by gcongr
    have hb5 : (9809952768 : ℝ) / Real.pi ^ 11 ≤
        9809952768 / (3141592653 / 10 ^ 9 : ℝ) ^ 11 := by gcongr
    have hnum : -(1064448 / 5 : ℝ) / (3141592654 / 10 ^ 9 : ℝ) ^ 5 +
        25546752 / (3141592653 / 10 ^ 9 : ℝ) ^ 7 -
        1226244096 / (3141592654 / 10 ^ 9 : ℝ) ^ 9 +
        9809952768 / (3141592653 / 10 ^ 9 : ℝ) ^ 11 ≤ 0 := by norm_num
    linarith
  · have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
    have hx_ge : (942 / 100 : ℝ) ≤ x := by simp only [x]; nlinarith [pi_gt_d9]
    set u : ℝ := x ^ 2 - 88
    have hu : 0 ≤ u := by simp only [u]; nlinarith
    have hdiff : (4848 / 5) / x ^ 3 -
        ((4848 / 5) / x ^ 3 - (1064448 / 5) / x ^ 5 + 25546752 / x ^ 7 -
          1226244096 / x ^ 9 + 9809952768 / x ^ 11) =
        (1064448 * u ^ 3 + 153280512 * u ^ 2 + 8379334656 * u + 226718908416) /
          (5 * x ^ 11) := by
      simp only [u]; field_simp [hxpos.ne']; ring
    have hnn : 0 ≤ (4848 / 5) / x ^ 3 -
        ((4848 / 5) / x ^ 3 - (1064448 / 5) / x ^ 5 + 25546752 / x ^ 7 -
          1226244096 / x ^ 9 + 9809952768 / x ^ 11) := by
      rw [hdiff]; positivity
    linarith

private lemma kernHat_le_forty_div_sq (r : ℕ) (hr : 1 ≤ r) :
    kernHat r ≤ 40 / (r : ℝ) ^ 2 := by
  have hpi : (3 : ℝ) ≤ Real.pi := by linarith [pi_gt_d9]
  have hpi2 : (9 : ℝ) ≤ Real.pi ^ 2 := by nlinarith
  have hpi3 : (27 : ℝ) ≤ Real.pi ^ 3 := by nlinarith
  rcases Nat.even_or_odd r with ⟨m, rfl⟩ | ⟨k, rfl⟩
  · have hm : 1 ≤ m := by omega
    rw [show m + m = 2 * m by omega]
    have hm_pos : (0 : ℝ) < m := by exact_mod_cast hm
    calc kernHat (2 * m) ≤ (78 / 5) / (Real.pi ^ 2 * (m : ℝ) ^ 2) := kernHat_even_le_main m hm
      _ ≤ 40 / ((2 * m : ℕ) : ℝ) ^ 2 := by
        push_cast
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have hm2 : (0 : ℝ) < (m : ℝ) ^ 2 := sq_pos_of_pos hm_pos
        nlinarith
  · calc kernHat (2 * k + 1) ≤ (4848 / 5) / (Real.pi ^ 3 * (2 * k + 1 : ℝ) ^ 3) :=
          kernHat_odd_le_main k
      _ ≤ 40 / ((2 * k + 1 : ℕ) : ℝ) ^ 2 := by
        push_cast
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have hk_ge : (1 : ℝ) ≤ 2 * (k : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
        have h2 : (0 : ℝ) < (2 * (k : ℝ) + 1) ^ 2 := by positivity
        have h3 : (2 * (k : ℝ) + 1) ^ 2 ≤ (2 * (k : ℝ) + 1) ^ 3 := by nlinarith
        nlinarith

private lemma summable_fourierCoeff_V : Summable (fourierCoeff V) := by
  refine Summable.of_norm ?_
  have hnat : Summable (fun n : ℕ => ‖fourierCoeff V n‖) := by
    have hdom : Summable (fun n : ℕ => (20 : ℝ) * (1 / (n : ℝ) ^ 2)) :=
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)).mul_left 20
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_ hdom
    intro n
    rcases n with _ | n
    · simp [fourierCoeff_V_zero]
    · rw [norm_fourierCoeff_V (n + 1 : ℕ) (by positivity)]
      have hle := kernHat_le_forty_div_sq (n + 1) (by omega)
      rw [Int.natAbs_natCast]
      linarith [show 40 / ((n + 1 : ℕ) : ℝ) ^ 2 / 2 = 20 * (1 / ((n + 1 : ℕ) : ℝ) ^ 2) by ring]
  have hneg : Summable (fun n : ℕ => ‖fourierCoeff V (-((n : ℤ) + 1))‖) := by
    have heq : (fun n : ℕ => ‖fourierCoeff V (-((n : ℤ) + 1))‖) =
        (fun n : ℕ => ‖fourierCoeff V ((n + 1 : ℕ) : ℤ)‖) := by
      funext n
      rw [norm_fourierCoeff_V (-((n : ℤ) + 1)) (by omega),
        norm_fourierCoeff_V ((n + 1 : ℕ) : ℤ) (by omega)]
      congr 2
    rw [heq]
    exact hnat.comp_injective Nat.succ_injective
  exact Summable.of_nat_of_neg_add_one hnat hneg

/- ## Purely algebraic `rpow`-free weight sequence `w` and sum bounds -/

private def wHeadInt (r : ℕ) : ℕ :=
  if r < 32 then
    if r < 16 then
      if r < 8 then
        if r < 4 then
          if r < 2 then
            if r < 1 then
              0
            else
              113035
          else
            if r < 3 then
              70870
            else
              63923
        else
          if r < 6 then
            if r < 5 then
              53764
            else
              48693
          else
            if r < 7 then
              46443
            else
              38942
      else
        if r < 12 then
          if r < 10 then
            if r < 9 then
              41131
            else
              32005
          else
            if r < 11 then
              36857
            else
              26960
        else
          if r < 14 then
            if r < 13 then
              33389
            else
              23204
          else
            if r < 15 then
              30559
            else
              20328
    else
      if r < 24 then
        if r < 20 then
          if r < 18 then
            if r < 17 then
              28219
            else
              18066
          else
            if r < 19 then
              26259
            else
              16247
        else
          if r < 22 then
            if r < 21 then
              24593
            else
              14754
          else
            if r < 23 then
              23160
            else
              13509
      else
        if r < 28 then
          if r < 26 then
            if r < 25 then
              21913
            else
              12455
          else
            if r < 27 then
              20817
            else
              11552
        else
          if r < 30 then
            if r < 29 then
              19847
            else
              10770
          else
            if r < 31 then
              18980
            else
              10086
  else
    if r < 48 then
      if r < 40 then
        if r < 36 then
          if r < 34 then
            if r < 33 then
              18201
            else
              9484
          else
            if r < 35 then
              17496
            else
              8949
        else
          if r < 38 then
            if r < 37 then
              16855
            else
              8470
          else
            if r < 39 then
              16268
            else
              8040
      else
        if r < 44 then
          if r < 42 then
            if r < 41 then
              15730
            else
              7652
          else
            if r < 43 then
              15234
            else
              7299
        else
          if r < 46 then
            if r < 45 then
              14775
            else
              6977
          else
            if r < 47 then
              14349
            else
              6682
    else
      if r < 56 then
        if r < 52 then
          if r < 50 then
            if r < 49 then
              13952
            else
              6411
          else
            if r < 51 then
              13581
            else
              6161
        else
          if r < 54 then
            if r < 53 then
              13234
            else
              5930
          else
            if r < 55 then
              12908
            else
              5716
      else
        if r < 60 then
          if r < 58 then
            if r < 57 then
              12601
            else
              5516
          else
            if r < 59 then
              12312
            else
              5330
        else
          if r < 62 then
            if r < 61 then
              12039
            else
              5156
          else
            if r < 63 then
              11780
            else
              4993

private noncomputable def w (r : ℕ) : ℝ :=
  if r ≤ 63 then (wHeadInt r : ℝ) / 100000
  else if r % 2 = 0 then (5779 / 50000 : ℝ) * (7 / 11 : ℝ) ^ Nat.log 2 (r / 64)
  else (79 / 25 : ℝ) / (r : ℝ)

private lemma w_nonneg (r : ℕ) : 0 ≤ w r := by
  unfold w
  split_ifs <;> positivity

private lemma kernHat_even_le_cube (m : ℕ) (hm : 1 ≤ m) (q : ℝ)
    (hnum : (312 / 5 : ℝ) / ((3141592653 / 10 ^ 9 : ℝ) * (2 * m : ℝ)) ^ 2 -
      (76032 / 5) / ((3141592654 / 10 ^ 9 : ℝ) * (2 * m : ℝ)) ^ 4 +
      (12773376 / 5) / ((3141592653 / 10 ^ 9 : ℝ) * (2 * m : ℝ)) ^ 6 -
      204374016 / ((3141592654 / 10 ^ 9 : ℝ) * (2 * m : ℝ)) ^ 8 +
      4904976384 / ((3141592653 / 10 ^ 9 : ℝ) * (2 * m : ℝ)) ^ 10 ≤ q ^ 3) :
    kernHat (2 * m) ≤ q ^ 3 := by
  have hlo := pi_gt_d9
  have hhi := pi_lt_d9
  have hm_pos : (0 : ℝ) < 2 * m := by
    have : (0 : ℝ) < m := by exact_mod_cast hm
    positivity
  have h1 : (312 / 5 : ℝ) / (Real.pi * (2 * m : ℝ)) ^ 2 ≤
      (312 / 5) / ((3141592653 / 10 ^ 9 : ℝ) * (2 * m : ℝ)) ^ 2 := by gcongr
  have h2 : (76032 / 5 : ℝ) / ((3141592654 / 10 ^ 9 : ℝ) * (2 * m : ℝ)) ^ 4 ≤
      (76032 / 5) / (Real.pi * (2 * m : ℝ)) ^ 4 := by gcongr
  have h3 : (12773376 / 5 : ℝ) / (Real.pi * (2 * m : ℝ)) ^ 6 ≤
      (12773376 / 5) / ((3141592653 / 10 ^ 9 : ℝ) * (2 * m : ℝ)) ^ 6 := by gcongr
  have h4 : (204374016 : ℝ) / ((3141592654 / 10 ^ 9 : ℝ) * (2 * m : ℝ)) ^ 8 ≤
      204374016 / (Real.pi * (2 * m : ℝ)) ^ 8 := by gcongr
  have h5 : (4904976384 : ℝ) / (Real.pi * (2 * m : ℝ)) ^ 10 ≤
      4904976384 / ((3141592653 / 10 ^ 9 : ℝ) * (2 * m : ℝ)) ^ 10 := by gcongr
  rw [kernHat_even_eq m hm]
  linarith

private lemma kernHat_odd_le_cube (k : ℕ) (q : ℝ)
    (hnum : (4848 / 5 : ℝ) / ((3141592653 / 10 ^ 9 : ℝ) * (2 * k + 1 : ℝ)) ^ 3 -
      (1064448 / 5) / ((3141592654 / 10 ^ 9 : ℝ) * (2 * k + 1 : ℝ)) ^ 5 +
      25546752 / ((3141592653 / 10 ^ 9 : ℝ) * (2 * k + 1 : ℝ)) ^ 7 -
      1226244096 / ((3141592654 / 10 ^ 9 : ℝ) * (2 * k + 1 : ℝ)) ^ 9 +
      9809952768 / ((3141592653 / 10 ^ 9 : ℝ) * (2 * k + 1 : ℝ)) ^ 11 ≤ q ^ 3) :
    kernHat (2 * k + 1) ≤ q ^ 3 := by
  have hlo := pi_gt_d9
  have hhi := pi_lt_d9
  have hk_pos : (0 : ℝ) < 2 * k + 1 := by positivity
  have h1 : (4848 / 5 : ℝ) / (Real.pi * (2 * k + 1 : ℝ)) ^ 3 ≤
      (4848 / 5) / ((3141592653 / 10 ^ 9 : ℝ) * (2 * k + 1 : ℝ)) ^ 3 := by gcongr
  have h2 : (1064448 / 5 : ℝ) / ((3141592654 / 10 ^ 9 : ℝ) * (2 * k + 1 : ℝ)) ^ 5 ≤
      (1064448 / 5) / (Real.pi * (2 * k + 1 : ℝ)) ^ 5 := by gcongr
  have h3 : (25546752 : ℝ) / (Real.pi * (2 * k + 1 : ℝ)) ^ 7 ≤
      25546752 / ((3141592653 / 10 ^ 9 : ℝ) * (2 * k + 1 : ℝ)) ^ 7 := by gcongr
  have h4 : (1226244096 : ℝ) / ((3141592654 / 10 ^ 9 : ℝ) * (2 * k + 1 : ℝ)) ^ 9 ≤
      1226244096 / (Real.pi * (2 * k + 1 : ℝ)) ^ 9 := by gcongr
  have h5 : (9809952768 : ℝ) / (Real.pi * (2 * k + 1 : ℝ)) ^ 11 ≤
      9809952768 / ((3141592653 / 10 ^ 9 : ℝ) * (2 * k + 1 : ℝ)) ^ 11 := by gcongr
  rw [kernHat_odd_eq k]
  linarith

set_option maxHeartbeats 800000 in
private lemma kernHat_le_w_cube_head (r : ℕ) (hr1 : 1 ≤ r) (hr63 : r ≤ 63) :
    kernHat r ≤ w r ^ 3 := by
  rw [w, if_pos hr63]
  interval_cases r
  · exact kernHat_odd_le_cube 0 (113035 / 100000) (by norm_num)
  · exact kernHat_even_le_cube 1 (by omega) (70870 / 100000) (by norm_num)
  · exact kernHat_odd_le_cube 1 (63923 / 100000) (by norm_num)
  · exact kernHat_even_le_cube 2 (by omega) (53764 / 100000) (by norm_num)
  · exact kernHat_odd_le_cube 2 (48693 / 100000) (by norm_num)
  · exact kernHat_even_le_cube 3 (by omega) (46443 / 100000) (by norm_num)
  · exact kernHat_odd_le_cube 3 (38942 / 100000) (by norm_num)
  · exact kernHat_even_le_cube 4 (by omega) (41131 / 100000) (by norm_num)
  · exact kernHat_odd_le_cube 4 (32005 / 100000) (by norm_num)
  · exact kernHat_even_le_cube 5 (by omega) (36857 / 100000) (by norm_num)
  · exact kernHat_odd_le_cube 5 (26960 / 100000) (by norm_num)
  · exact kernHat_even_le_cube 6 (by omega) (33389 / 100000) (by norm_num)
  · exact kernHat_odd_le_cube 6 (23204 / 100000) (by norm_num)
  · exact kernHat_even_le_cube 7 (by omega) (30559 / 100000) (by norm_num)
  · exact kernHat_odd_le_cube 7 (20328 / 100000) (by norm_num)
  · exact kernHat_even_le_cube 8 (by omega) (28219 / 100000) (by norm_num)
  · exact kernHat_odd_le_cube 8 (18066 / 100000) (by norm_num)
  · exact kernHat_even_le_cube 9 (by omega) (26259 / 100000) (by norm_num)
  · exact kernHat_odd_le_cube 9 (16247 / 100000) (by norm_num)
  · exact kernHat_even_le_cube 10 (by omega) (24593 / 100000) (by norm_num)
  · exact kernHat_odd_le_cube 10 (14754 / 100000) (by norm_num)
  · exact kernHat_even_le_cube 11 (by omega) (23160 / 100000) (by norm_num)
  · exact kernHat_odd_le_cube 11 (13509 / 100000) (by norm_num)
  · exact kernHat_even_le_cube 12 (by omega) (21913 / 100000) (by norm_num)
  · exact kernHat_odd_le_cube 12 (12455 / 100000) (by norm_num)
  · exact kernHat_even_le_cube 13 (by omega) (20817 / 100000) (by norm_num)
  · exact kernHat_odd_le_cube 13 (11552 / 100000) (by norm_num)
  · exact kernHat_even_le_cube 14 (by omega) (19847 / 100000) (by norm_num)
  · exact kernHat_odd_le_cube 14 (10770 / 100000) (by norm_num)
  · exact kernHat_even_le_cube 15 (by omega) (18980 / 100000) (by norm_num)
  · exact kernHat_odd_le_cube 15 (10086 / 100000) (by norm_num)
  · exact kernHat_even_le_cube 16 (by omega) (18201 / 100000) (by norm_num)
  · exact kernHat_odd_le_cube 16 (9484 / 100000) (by norm_num)
  · exact kernHat_even_le_cube 17 (by omega) (17496 / 100000) (by norm_num)
  · exact kernHat_odd_le_cube 17 (8949 / 100000) (by norm_num)
  · exact kernHat_even_le_cube 18 (by omega) (16855 / 100000) (by norm_num)
  · exact kernHat_odd_le_cube 18 (8470 / 100000) (by norm_num)
  · exact kernHat_even_le_cube 19 (by omega) (16268 / 100000) (by norm_num)
  · exact kernHat_odd_le_cube 19 (8040 / 100000) (by norm_num)
  · exact kernHat_even_le_cube 20 (by omega) (15730 / 100000) (by norm_num)
  · exact kernHat_odd_le_cube 20 (7652 / 100000) (by norm_num)
  · exact kernHat_even_le_cube 21 (by omega) (15234 / 100000) (by norm_num)
  · exact kernHat_odd_le_cube 21 (7299 / 100000) (by norm_num)
  · exact kernHat_even_le_cube 22 (by omega) (14775 / 100000) (by norm_num)
  · exact kernHat_odd_le_cube 22 (6977 / 100000) (by norm_num)
  · exact kernHat_even_le_cube 23 (by omega) (14349 / 100000) (by norm_num)
  · exact kernHat_odd_le_cube 23 (6682 / 100000) (by norm_num)
  · exact kernHat_even_le_cube 24 (by omega) (13952 / 100000) (by norm_num)
  · exact kernHat_odd_le_cube 24 (6411 / 100000) (by norm_num)
  · exact kernHat_even_le_cube 25 (by omega) (13581 / 100000) (by norm_num)
  · exact kernHat_odd_le_cube 25 (6161 / 100000) (by norm_num)
  · exact kernHat_even_le_cube 26 (by omega) (13234 / 100000) (by norm_num)
  · exact kernHat_odd_le_cube 26 (5930 / 100000) (by norm_num)
  · exact kernHat_even_le_cube 27 (by omega) (12908 / 100000) (by norm_num)
  · exact kernHat_odd_le_cube 27 (5716 / 100000) (by norm_num)
  · exact kernHat_even_le_cube 28 (by omega) (12601 / 100000) (by norm_num)
  · exact kernHat_odd_le_cube 28 (5516 / 100000) (by norm_num)
  · exact kernHat_even_le_cube 29 (by omega) (12312 / 100000) (by norm_num)
  · exact kernHat_odd_le_cube 29 (5330 / 100000) (by norm_num)
  · exact kernHat_even_le_cube 30 (by omega) (12039 / 100000) (by norm_num)
  · exact kernHat_odd_le_cube 30 (5156 / 100000) (by norm_num)
  · exact kernHat_even_le_cube 31 (by omega) (11780 / 100000) (by norm_num)
  · exact kernHat_odd_le_cube 31 (4993 / 100000) (by norm_num)

private lemma kernHat_le_w_cube (r : ℕ) (hr : 1 ≤ r) :
    kernHat r ≤ w r ^ 3 := by
  by_cases hr63 : r ≤ 63
  · exact kernHat_le_w_cube_head r hr hr63
  · rcases Nat.even_or_odd r with ⟨m, rfl⟩ | ⟨k, rfl⟩
    · rw [show m + m = 2 * m by omega] at hr63 ⊢
      have hm32 : 32 ≤ m := by omega
      have hw : w (2 * m) = (5779 / 50000 : ℝ) * (7 / 11 : ℝ) ^ Nat.log 2 (m / 32) := by
        rw [w, if_neg hr63, if_pos (by omega),
          show 2 * m / 64 = m / 32 by omega]
      rw [hw]
      set j : ℕ := Nat.log 2 (m / 32)
      have hpow_le : 32 * 2 ^ j ≤ m := by
        have h1 : 2 ^ j ≤ m / 32 := Nat.pow_log_le_self 2 (by omega)
        have h2 : m / 32 * 32 ≤ m := Nat.div_mul_le_self m 32
        omega
      have hm_real : (32 : ℝ) * (2 : ℝ) ^ j ≤ (m : ℝ) := by exact_mod_cast hpow_le
      have hm_sq : (1024 : ℝ) * (4 : ℝ) ^ j ≤ (m : ℝ) ^ 2 := by
        have hsq := pow_le_pow_left₀ (by positivity) hm_real 2
        have hlhs : ((32 : ℝ) * (2 : ℝ) ^ j) ^ 2 = (1024 : ℝ) * (4 : ℝ) ^ j := by
          rw [mul_pow, pow_right_comm]
          norm_num
        linarith
      have hpi2 : (3141592653 / 10 ^ 9 : ℝ) ^ 2 ≤ Real.pi ^ 2 :=
        pow_le_pow_left₀ (by norm_num) pi_gt_d9.le 2
      have hden : (3141592653 / 10 ^ 9 : ℝ) ^ 2 * ((1024 : ℝ) * (4 : ℝ) ^ j) ≤
          Real.pi ^ 2 * (m : ℝ) ^ 2 :=
        mul_le_mul hpi2 hm_sq (by positivity) (by positivity)
      calc kernHat (2 * m)
          ≤ (78 / 5) / (Real.pi ^ 2 * (m : ℝ) ^ 2) := kernHat_even_le_main m (by omega)
        _ ≤ (78 / 5) / ((3141592653 / 10 ^ 9 : ℝ) ^ 2 * ((1024 : ℝ) * (4 : ℝ) ^ j)) :=
            div_le_div_of_nonneg_left (by norm_num) (by positivity) hden
        _ = ((78 / 5 : ℝ) / ((3141592653 / 10 ^ 9 : ℝ) ^ 2 * 1024)) * (1 / 4 : ℝ) ^ j := by
            rw [one_div, inv_pow]; field_simp
        _ ≤ (5779 / 50000 : ℝ) ^ 3 * ((7 / 11 : ℝ) ^ 3) ^ j := by
            refine mul_le_mul (by norm_num) ?_ (by positivity) (by positivity)
            exact pow_le_pow_left₀ (by norm_num) (by norm_num) j
        _ = ((5779 / 50000 : ℝ) * (7 / 11 : ℝ) ^ j) ^ 3 := by
            rw [mul_pow, pow_right_comm]
    · have hk32 : 32 ≤ k := by omega
      have hw : w (2 * k + 1) = (79 / 25 : ℝ) / ((2 * k + 1 : ℕ) : ℝ) := by
        rw [w, if_neg hr63, if_neg (by omega)]
      rw [hw, div_pow, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
      have hpi3 : (3141592653 / 10 ^ 9 : ℝ) ^ 3 ≤ Real.pi ^ 3 :=
        pow_le_pow_left₀ (by norm_num) pi_gt_d9.le 3
      calc kernHat (2 * k + 1)
          ≤ (4848 / 5) / (Real.pi ^ 3 * (2 * k + 1 : ℝ) ^ 3) := kernHat_odd_le_main k
        _ = ((4848 / 5 : ℝ) / Real.pi ^ 3) / (2 * k + 1 : ℝ) ^ 3 :=
            div_mul_eq_div_div _ _ _
        _ ≤ ((4848 / 5 : ℝ) / (3141592653 / 10 ^ 9 : ℝ) ^ 3) / (2 * k + 1 : ℝ) ^ 3 := by
            gcongr
        _ ≤ (79 / 25 : ℝ) ^ 3 / (2 * k + 1 : ℝ) ^ 3 := by
            gcongr; norm_num

private lemma log2_eq_of_bounds {x j : ℕ} (h1 : 2 ^ j ≤ x) (h2 : x < 2 ^ (j + 1)) :
    Nat.log 2 x = j := by
  have hx : x ≠ 0 := by
    have : 0 < 2 ^ j := by positivity
    omega
  have hlo : 2 ^ Nat.log 2 x ≤ x := Nat.pow_log_le_self 2 hx
  have hhi : x < 2 ^ (Nat.log 2 x + 1) := Nat.lt_pow_succ_log_self (by norm_num) x
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hle : 2 ^ (Nat.log 2 x + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · have hle : 2 ^ (j + 1) ≤ 2 ^ Nat.log 2 x := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

private lemma lt_two_pow_self (j : ℕ) : j < 2 ^ j := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    rw [pow_succ]
    omega

private lemma sum_w_head_eq :
    ∑ r ∈ Finset.range 63, w (r + 1) ^ 4 =
      238571904961805557567 / 100000000000000000000 := by
  have hterm : ∀ r ∈ Finset.range 63,
      w (r + 1) ^ 4 = ((wHeadInt (r + 1) ^ 4 : ℕ) : ℝ) / 100000000000000000000 := by
    intro r hr
    rw [Finset.mem_range] at hr
    rw [w, if_pos (by omega), div_pow]
    push_cast
    norm_num
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, ← Nat.cast_sum]
  have hnat : ∑ r ∈ Finset.range 63, wHeadInt (r + 1) ^ 4 = 238571904961805557567 := by
    decide
  rw [hnat]
  norm_num

private lemma sum_w_even_tail_le (M : ℕ) :
    ∑ m ∈ Finset.Ico 32 (32 + M), w (2 * m) ^ 4 ≤
      32 * (5779 / 50000 : ℝ) ^ 4 / (1 - 2 * (7 / 11 : ℝ) ^ 4) := by
  let block : ℕ → Finset ℕ := fun j => Finset.Ico (32 * 2 ^ j) (32 * 2 ^ (j + 1))
  have hsub : Finset.Ico 32 (32 + M) ⊆ (Finset.range (M + 1)).biUnion block := by
    intro m hm
    rw [Finset.mem_Ico] at hm
    rw [Finset.mem_biUnion]
    refine ⟨Nat.log 2 (m / 32), ?_, ?_⟩
    · rw [Finset.mem_range]
      have h1 : 2 ^ Nat.log 2 (m / 32) ≤ m / 32 := Nat.pow_log_le_self 2 (by omega)
      have h2 : Nat.log 2 (m / 32) < 2 ^ Nat.log 2 (m / 32) := lt_two_pow_self _
      omega
    · rw [Finset.mem_Ico]
      have h1 : 2 ^ Nat.log 2 (m / 32) ≤ m / 32 := Nat.pow_log_le_self 2 (by omega)
      have h2 : m / 32 < 2 ^ (Nat.log 2 (m / 32) + 1) :=
        Nat.lt_pow_succ_log_self (by norm_num) (m / 32)
      omega
  have hdisj : (↑(Finset.range (M + 1)) : Set ℕ).PairwiseDisjoint block := by
    intro j1 _ j2 _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro m hm1 hm2
    rw [Finset.mem_Ico] at hm1 hm2
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hle : 2 ^ (j1 + 1) ≤ 2 ^ j2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    · have hle : 2 ^ (j2 + 1) ≤ 2 ^ j1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  have hblock_sum : ∀ j : ℕ,
      ∑ m ∈ block j, w (2 * m) ^ 4 =
        (32 * (5779 / 50000 : ℝ) ^ 4) * (2 * (7 / 11 : ℝ) ^ 4) ^ j := by
    intro j
    have hconst : ∀ m ∈ block j,
        w (2 * m) ^ 4 = (5779 / 50000 : ℝ) ^ 4 * ((7 / 11 : ℝ) ^ 4) ^ j := by
      intro m hm
      rw [Finset.mem_Ico] at hm
      have h2j : 1 ≤ 2 ^ j := Nat.one_le_pow j 2 (by norm_num)
      have hm63 : ¬ (2 * m ≤ 63) := by omega
      rw [w, if_neg hm63, if_pos (by omega), show 2 * m / 64 = m / 32 by omega]
      have hlog : Nat.log 2 (m / 32) = j := log2_eq_of_bounds (by omega) (by omega)
      rw [hlog, mul_pow, pow_right_comm]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
    have hcard : (block j).card = 32 * 2 ^ j := by
      dsimp only [block]
      rw [Nat.card_Ico, pow_succ]
      omega
    rw [hcard]
    push_cast
    rw [mul_pow]
    ring
  calc ∑ m ∈ Finset.Ico 32 (32 + M), w (2 * m) ^ 4
      ≤ ∑ m ∈ (Finset.range (M + 1)).biUnion block, w (2 * m) ^ 4 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = ∑ j ∈ Finset.range (M + 1), ∑ m ∈ block j, w (2 * m) ^ 4 :=
        Finset.sum_biUnion hdisj
    _ = (32 * (5779 / 50000 : ℝ) ^ 4) *
          ∑ j ∈ Finset.range (M + 1), (2 * (7 / 11 : ℝ) ^ 4) ^ j := by
        simp_rw [hblock_sum, ← Finset.mul_sum]
    _ ≤ (32 * (5779 / 50000 : ℝ) ^ 4) * (1 / (1 - 2 * (7 / 11 : ℝ) ^ 4)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        set q : ℝ := 2 * (7 / 11 : ℝ) ^ 4
        have hq_lt : q < 1 := by simp only [q]; norm_num
        have hq_nn : 0 ≤ q ^ (M + 1) := by simp only [q]; positivity
        rw [geom_sum_eq hq_lt.ne (M + 1)]
        have hrew : (q ^ (M + 1) - 1) / (q - 1) = (1 - q ^ (M + 1)) / (1 - q) := by
          field_simp [sub_ne_zero.mpr hq_lt.ne, sub_ne_zero.mpr hq_lt.ne']; ring
        rw [hrew]
        exact div_le_div_of_nonneg_right (by linarith) (by linarith)
    _ = 32 * (5779 / 50000 : ℝ) ^ 4 / (1 - 2 * (7 / 11 : ℝ) ^ 4) := by ring

private lemma inv_pow4_le_diff_pow3 (r : ℝ) (hr : 2 < r) :
    1 / r ^ 4 ≤ (1 / 6 : ℝ) * (1 / (r - 2) ^ 3 - 1 / r ^ 3) := by
  have hr0 : 0 < r := by linarith
  have hr2 : 0 < r - 2 := by linarith
  have h1 : (1 / 6 : ℝ) * (1 / (r - 2) ^ 3 - 1 / r ^ 3) - 1 / r ^ 4 =
      (24 * r ^ 2 - 64 * r + 48) / (6 * (r - 2) ^ 3 * r ^ 4) := by
    field_simp [hr0.ne', hr2.ne']; ring
  have hpos : 0 ≤ (24 * r ^ 2 - 64 * r + 48) / (6 * (r - 2) ^ 3 * r ^ 4) :=
    div_nonneg (by nlinarith [sq_nonneg (3 * r - 4)]) (by positivity)
  linarith

private lemma sum_w_odd_tail_le (M : ℕ) :
    ∑ k ∈ Finset.range M, w (2 * k + 65) ^ 4 ≤
      (79 / 25 : ℝ) ^ 4 * (1 / 6 : ℝ) / (63 : ℝ) ^ 3 := by
  have hterm : ∀ k ∈ Finset.range M,
      w (2 * k + 65) ^ 4 ≤
        (79 / 25 : ℝ) ^ 4 * (1 / 6 : ℝ) *
          (1 / (2 * (k : ℝ) + 63) ^ 3 - 1 / (2 * (k : ℝ) + 65) ^ 3) := by
    intro k _
    have hw : w (2 * k + 65) = (79 / 25 : ℝ) / (2 * (k : ℝ) + 65) := by
      rw [w, if_neg (by omega), if_neg (by omega)]
      push_cast; ring
    rw [hw, show ((79 / 25 : ℝ) / (2 * (k : ℝ) + 65)) ^ 4 =
        (79 / 25 : ℝ) ^ 4 * (1 / (2 * (k : ℝ) + 65) ^ 4) by rw [div_pow]; ring]
    have hinv := inv_pow4_le_diff_pow3 (2 * (k : ℝ) + 65)
      (by linarith [Nat.cast_nonneg (α := ℝ) k])
    rw [show 2 * (k : ℝ) + 65 - 2 = 2 * (k : ℝ) + 63 by ring] at hinv
    calc (79 / 25 : ℝ) ^ 4 * (1 / (2 * (k : ℝ) + 65) ^ 4)
        ≤ (79 / 25 : ℝ) ^ 4 *
            ((1 / 6 : ℝ) * (1 / (2 * (k : ℝ) + 63) ^ 3 - 1 / (2 * (k : ℝ) + 65) ^ 3)) :=
          mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = (79 / 25 : ℝ) ^ 4 * (1 / 6 : ℝ) *
            (1 / (2 * (k : ℝ) + 63) ^ 3 - 1 / (2 * (k : ℝ) + 65) ^ 3) := by ring
  calc ∑ k ∈ Finset.range M, w (2 * k + 65) ^ 4
      ≤ ∑ k ∈ Finset.range M, (79 / 25 : ℝ) ^ 4 * (1 / 6 : ℝ) *
          (1 / (2 * (k : ℝ) + 63) ^ 3 - 1 / (2 * (k : ℝ) + 65) ^ 3) :=
        Finset.sum_le_sum hterm
    _ = (79 / 25 : ℝ) ^ 4 * (1 / 6 : ℝ) *
          ∑ k ∈ Finset.range M, (1 / (2 * (k : ℝ) + 63) ^ 3 - 1 / (2 * (k : ℝ) + 65) ^ 3) := by
        rw [← Finset.mul_sum]
    _ = (79 / 25 : ℝ) ^ 4 * (1 / 6 : ℝ) *
          (1 / (63 : ℝ) ^ 3 - 1 / (2 * (M : ℝ) + 63) ^ 3) := by
        congr 1
        have htel := Finset.sum_range_sub' (fun k : ℕ => (1 : ℝ) / (2 * (k : ℝ) + 63) ^ 3) M
        have heq : (fun k : ℕ => (1 : ℝ) / (2 * (k : ℝ) + 63) ^ 3 -
            1 / (2 * ((k + 1 : ℕ) : ℝ) + 63) ^ 3) =
          (fun k : ℕ => (1 : ℝ) / (2 * (k : ℝ) + 63) ^ 3 - 1 / (2 * (k : ℝ) + 65) ^ 3) := by
          funext k; push_cast; ring
        rw [heq] at htel
        simpa using htel
    _ ≤ (79 / 25 : ℝ) ^ 4 * (1 / 6 : ℝ) / (63 : ℝ) ^ 3 := by
        have hnn : 0 ≤ (1 : ℝ) / (2 * (M : ℝ) + 63) ^ 3 := by positivity
        linarith [mul_nonneg (by positivity : (0 : ℝ) ≤ (79 / 25 : ℝ) ^ 4 * (1 / 6 : ℝ)) hnn]

private lemma sum_w_pow4_le (M : ℕ) :
    ∑ r ∈ Finset.range M, w (r + 1) ^ 4 ≤ 23945 / 10000 := by
  let S1 : Finset ℕ := (Finset.range 63).image (fun r => r + 1)
  let S2 : Finset ℕ := (Finset.Ico 32 (32 + M)).image (fun m => 2 * m)
  let S3 : Finset ℕ := (Finset.range M).image (fun k => 2 * k + 65)
  have hinj0 : Set.InjOn (fun r : ℕ => r + 1) ↑(Finset.range M) :=
    fun a _ b _ h => by dsimp only at h; omega
  have hinj1 : Set.InjOn (fun r : ℕ => r + 1) ↑(Finset.range 63) :=
    fun a _ b _ h => by dsimp only at h; omega
  have hinj2 : Set.InjOn (fun m : ℕ => 2 * m) ↑(Finset.Ico 32 (32 + M)) :=
    fun a _ b _ h => by dsimp only at h; omega
  have hinj3 : Set.InjOn (fun k : ℕ => 2 * k + 65) ↑(Finset.range M) :=
    fun a _ b _ h => by dsimp only at h; omega
  rw [← Finset.sum_image (f := fun n => w n ^ 4) hinj0]
  have hsub : (Finset.range M).image (fun r => r + 1) ⊆ S1 ∪ (S2 ∪ S3) := by
    intro n hn
    rw [Finset.mem_image] at hn
    obtain ⟨r, hr, rfl⟩ := hn
    rw [Finset.mem_range] at hr
    simp only [S1, S2, S3, Finset.mem_union, Finset.mem_image, Finset.mem_range, Finset.mem_Ico]
    by_cases h63 : r + 1 ≤ 63
    · left; exact ⟨r, by omega, rfl⟩
    · right
      rcases Nat.even_or_odd (r + 1) with ⟨m, hm⟩ | ⟨q, hq⟩
      · left; exact ⟨m, ⟨by omega, by omega⟩, by omega⟩
      · right; exact ⟨q - 32, by omega, by omega⟩
  have hd23 : Disjoint S2 S3 := by
    rw [Finset.disjoint_left]
    intro x hx2 hx3
    simp only [S2, S3, Finset.mem_image] at hx2 hx3
    obtain ⟨m, _, rfl⟩ := hx2
    obtain ⟨k, _, hk⟩ := hx3
    omega
  have hd123 : Disjoint S1 (S2 ∪ S3) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx23
    simp only [S1, S2, S3, Finset.mem_union, Finset.mem_image, Finset.mem_range,
      Finset.mem_Ico] at hx1 hx23
    obtain ⟨r, hr, rfl⟩ := hx1
    rcases hx23 with ⟨m, hm, hm_eq⟩ | ⟨k, _, hk_eq⟩ <;> omega
  calc ∑ n ∈ (Finset.range M).image (fun r => r + 1), w n ^ 4
      ≤ ∑ n ∈ S1 ∪ (S2 ∪ S3), w n ^ 4 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = (∑ n ∈ S1, w n ^ 4) + ((∑ n ∈ S2, w n ^ 4) + (∑ n ∈ S3, w n ^ 4)) := by
        rw [Finset.sum_union hd123, Finset.sum_union hd23]
    _ = (∑ r ∈ Finset.range 63, w (r + 1) ^ 4) +
        ((∑ m ∈ Finset.Ico 32 (32 + M), w (2 * m) ^ 4) +
          (∑ k ∈ Finset.range M, w (2 * k + 65) ^ 4)) := by
        dsimp only [S1, S2, S3]
        rw [Finset.sum_image hinj1, Finset.sum_image hinj2, Finset.sum_image hinj3]
    _ ≤ (238571904961805557567 / 100000000000000000000 : ℝ) +
        ((32 * (5779 / 50000 : ℝ) ^ 4 / (1 - 2 * (7 / 11 : ℝ) ^ 4)) +
          ((79 / 25 : ℝ) ^ 4 * (1 / 6 : ℝ) / (63 : ℝ) ^ 3)) := by
        linarith [sum_w_head_eq, sum_w_even_tail_le M, sum_w_odd_tail_le M]
    _ ≤ 23945 / 10000 := by norm_num

private lemma summable_w_pow4 : Summable (fun r : ℕ => w (r + 1) ^ 4) :=
  summable_of_sum_range_le (fun _ => by positivity) sum_w_pow4_le

private lemma tsum_w_pow4_le : ∑' r : ℕ, w (r + 1) ^ 4 ≤ 23945 / 10000 :=
  summable_w_pow4.tsum_le_of_sum_range_le sum_w_pow4_le

private lemma quartic_young (u v : ℝ) : 4 * u ^ 3 * v ≤ 3 * u ^ 4 + v ^ 4 := by
  have h1 : 0 ≤ (v + u) ^ 2 + 2 * u ^ 2 := by positivity
  have h2 : 0 ≤ (v - u) ^ 2 * ((v + u) ^ 2 + 2 * u ^ 2) := mul_nonneg (sq_nonneg _) h1
  linarith [show (v - u) ^ 2 * ((v + u) ^ 2 + 2 * u ^ 2) = 3 * u ^ 4 + v ^ 4 - 4 * u ^ 3 * v
    by ring]

/- ## Convolution Fourier analysis and Bessel inequality on `[0, 2]` -/

private lemma convolution_support_subset {f : ℝ → ℝ}
    (hsupp : Function.support f ⊆ Set.Icc (0 : ℝ) 1) :
    Function.support (f ⋆ f) ⊆ Set.Icc (0 : ℝ) 2 := by
  intro z hz
  by_contra hnot
  apply hz
  rw [convolution_lsmul]
  have hzero : ∀ t : ℝ, f t * f (z - t) = 0 := by
    intro t
    by_cases ht : t ∈ Set.Icc (0 : ℝ) 1
    · have hzt : z - t ∉ Set.Icc (0 : ℝ) 1 := fun h =>
        hnot ⟨by linarith [ht.1, h.1], by linarith [ht.2, h.2]⟩
      have hfz : f (z - t) = 0 := by by_contra hne; exact hzt (hsupp hne)
      rw [hfz, mul_zero]
    · have hft : f t = 0 := by by_contra hne; exact ht (hsupp hne)
      rw [hft, zero_mul]
  simp [hzero]

private lemma fourier_coeff_conv {f : ℝ → ℝ} (hfi : Integrable f)
    (hsupp : Function.support f ⊆ Set.Icc (0 : ℝ) 1) (n : ℤ) :
    ∫ z in Set.Ioc (0 : ℝ) 2, ((f ⋆ f) z : ℂ) * @fourier 2 n (z : AddCircle (2 : ℝ)) =
      (∫ x, (f x : ℂ) * @fourier 2 n (x : AddCircle (2 : ℝ))) ^ 2 := by
  have hgsupp := convolution_support_subset hsupp
  have hIoc : ∫ z in Set.Ioc (0 : ℝ) 2, ((f ⋆ f) z : ℂ) * @fourier 2 n (z : AddCircle (2 : ℝ)) =
      ∫ z, ((f ⋆ f) z : ℂ) * @fourier 2 n (z : AddCircle (2 : ℝ)) := by
    rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
    refine integral_congr_ae ?_
    have hne0 : ∀ᵐ z : ℝ ∂volume, z ≠ 0 := by rw [ae_iff]; simp
    filter_upwards [hne0] with z hz0
    by_cases hz : z ∈ Set.Ioc (0 : ℝ) 2
    · simp [Set.indicator_of_mem hz]
    · simp only [Set.indicator_of_notMem hz]
      have hnotIcc : z ∉ Set.Icc (0 : ℝ) 2 := fun h => hz ⟨lt_of_le_of_ne h.1 hz0.symm, h.2⟩
      have hg0 : (f ⋆ f) z = 0 := by by_contra hne; exact hnotIcc (hgsupp hne)
      simp [hg0]
  rw [hIoc]
  let φ : ℝ → ℂ := fun x => (f x : ℂ) * @fourier 2 n (x : AddCircle (2 : ℝ))
  have hφ_int : Integrable φ := by
    refine Integrable.mono' hfi.norm ?_ ?_
    · have hcont : Continuous (fun x : ℝ => @fourier 2 n (x : AddCircle (2 : ℝ))) := by
        simp_rw [char2_coe]; fun_prop
      exact (Complex.continuous_ofReal.comp_aestronglyMeasurable hfi.aestronglyMeasurable).mul
        hcont.aestronglyMeasurable
    · filter_upwards with x
      simp only [φ, norm_mul, Complex.norm_real, char2_norm, mul_one, le_refl]
  have hconv_eq : ∀ z : ℝ,
      ((f ⋆ f) z : ℂ) * @fourier 2 n (z : AddCircle (2 : ℝ)) =
        (φ ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] φ) z := by
    intro z
    rw [convolution_lsmul, convolution_def]
    simp only [ContinuousLinearMap.mul_apply', φ]
    have hofReal : ((∫ t : ℝ, f t * f (z - t) : ℝ) : ℂ) =
        ∫ t : ℝ, ((f t * f (z - t) : ℝ) : ℂ) := by
      simp_rw [← Complex.coe_algebraMap]
      exact (integral_ofReal (𝕜 := ℂ)).symm
    simp only [smul_eq_mul]
    rw [hofReal, ← integral_mul_const]
    congr 1; funext t
    have hsplit : @fourier 2 n (z : AddCircle (2 : ℝ)) =
        @fourier 2 n (t : AddCircle (2 : ℝ)) * @fourier 2 n ((z - t : ℝ) : AddCircle (2 : ℝ)) := by
      conv_lhs => rw [show z = t + (z - t) by ring]
      exact char2_add n t (z - t)
    rw [hsplit]
    push_cast; ring
  simp_rw [hconv_eq]
  rw [integral_convolution (ContinuousLinearMap.mul ℝ ℂ) hφ_int hφ_int]
  simp only [ContinuousLinearMap.mul_apply', sq, φ]

private lemma bessel_Ioc_two {g : ℝ → ℝ} (hgi : Integrable g)
    (hg_sq : Integrable (fun z => (g z) ^ 2))
    (c : ℤ → ℂ)
    (hc : ∀ n : ℤ, ∫ z in Set.Ioc (0 : ℝ) 2,
      (g z : ℂ) * @fourier 2 n (z : AddCircle (2 : ℝ)) = c n)
    (F : Finset ℤ) :
    (1 / 2 : ℝ) * ∑ n ∈ F, ‖c n‖ ^ 2 ≤ ∫ z in Set.Ioc (0 : ℝ) 2, (g z) ^ 2 := by
  let S : ℝ → ℂ := fun z => (1 / 2 : ℂ) * ∑ n ∈ F, c n * @fourier 2 (-n) (z : AddCircle (2 : ℝ))
  have hS_cont : Continuous S := by
    simp only [S]
    refine continuous_const.mul (continuous_finsetSum F fun n _ => ?_)
    simp_rw [char2_coe]; fun_prop
  have hS2_int : IntegrableOn (fun z => ‖S z‖ ^ 2) (Set.Ioc (0 : ℝ) 2) volume :=
    (hS_cont.norm.pow 2).continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hg2_int : IntegrableOn (fun z => (g z) ^ 2) (Set.Ioc (0 : ℝ) 2) volume :=
    hg_sq.integrableOn
  have hcross_int : IntegrableOn (fun z => (g z : ℂ) * starRingEnd ℂ (S z))
      (Set.Ioc (0 : ℝ) 2) volume := by
    refine Integrable.mono' (hg2_int.add hS2_int) ?_ ?_
    · exact (Complex.continuous_ofReal.comp_aestronglyMeasurable
        hgi.aestronglyMeasurable.restrict).mul
        (Complex.continuous_conj.comp hS_cont).aestronglyMeasurable
    · filter_upwards with z
      simp only [Pi.add_apply]
      rw [norm_mul, Complex.norm_real, Complex.norm_conj, Real.norm_eq_abs]
      nlinarith [sq_nonneg (|g z| - ‖S z‖), sq_abs (g z)]
  have hcross_re_int : IntegrableOn (fun z => ((g z : ℂ) * starRingEnd ℂ (S z)).re)
      (Set.Ioc (0 : ℝ) 2) volume :=
    Complex.reCLM.integrable_comp hcross_int
  have hexpand : ∀ z : ℝ,
      ‖(g z : ℂ) - S z‖ ^ 2 =
        (g z) ^ 2 - 2 * ((g z : ℂ) * starRingEnd ℂ (S z)).re + ‖S z‖ ^ 2 := by
    intro z
    rw [Complex.sq_norm, Complex.sq_norm]
    simp [Complex.normSq_apply]
    ring
  have hnonneg : 0 ≤ ∫ z in Set.Ioc (0 : ℝ) 2, ‖(g z : ℂ) - S z‖ ^ 2 :=
    integral_nonneg (fun _ => sq_nonneg _)
  simp_rw [hexpand] at hnonneg
  have hsplit_int :
      ∫ z in Set.Ioc (0 : ℝ) 2,
          ((g z) ^ 2 - 2 * ((g z : ℂ) * starRingEnd ℂ (S z)).re + ‖S z‖ ^ 2) =
        (∫ z in Set.Ioc (0 : ℝ) 2, (g z) ^ 2) -
        2 * (∫ z in Set.Ioc (0 : ℝ) 2, ((g z : ℂ) * starRingEnd ℂ (S z)).re) +
        (∫ z in Set.Ioc (0 : ℝ) 2, ‖S z‖ ^ 2) := by
    have hadd := integral_add (hg2_int.sub (hcross_re_int.const_mul 2)) hS2_int
    have hsub := integral_sub hg2_int (hcross_re_int.const_mul 2)
    have hmul := integral_const_mul (μ := volume.restrict (Set.Ioc (0 : ℝ) 2))
      (2 : ℝ) (fun z => ((g z : ℂ) * starRingEnd ℂ (S z)).re)
    dsimp only [Pi.add_apply, Pi.sub_apply] at hadd hsub
    rw [hadd, hsub, hmul]
  rw [hsplit_int] at hnonneg
  have hcross_val :
      ∫ z in Set.Ioc (0 : ℝ) 2, ((g z : ℂ) * starRingEnd ℂ (S z)).re =
        (1 / 2 : ℝ) * ∑ n ∈ F, ‖c n‖ ^ 2 := by
    have hre1 : ∫ z in Set.Ioc (0 : ℝ) 2, ((g z : ℂ) * starRingEnd ℂ (S z)).re =
        (∫ z in Set.Ioc (0 : ℝ) 2, (g z : ℂ) * starRingEnd ℂ (S z)).re :=
      Complex.reCLM.integral_comp_comm hcross_int
    rw [hre1]
    have hpt : (fun z : ℝ => (g z : ℂ) * starRingEnd ℂ (S z)) =
        fun z : ℝ => (1 / 2 : ℂ) * ∑ n ∈ F,
          starRingEnd ℂ (c n) * ((g z : ℂ) * @fourier 2 n (z : AddCircle (2 : ℝ))) := by
      funext z
      simp only [S, map_mul, map_div₀, map_one, map_ofNat, map_sum, ← fourier_neg, neg_neg,
        Finset.mul_sum]
      ring_nf
    rw [hpt, integral_const_mul, integral_finsetSum]
    · have hterm : ∀ n ∈ F,
          ∫ z in Set.Ioc (0 : ℝ) 2,
            starRingEnd ℂ (c n) * ((g z : ℂ) * @fourier 2 n (z : AddCircle (2 : ℝ))) =
          starRingEnd ℂ (c n) * c n := by
        intro n _
        rw [integral_const_mul, hc n]
      rw [Finset.sum_congr rfl hterm]
      have hdiv : ((1 / 2 : ℂ) * ∑ n ∈ F, starRingEnd ℂ (c n) * c n).re =
          (1 / 2 : ℝ) * (∑ n ∈ F, starRingEnd ℂ (c n) * c n).re := by
        simp [Complex.mul_re]
      rw [hdiv, Complex.re_sum]
      congr 1
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Complex.sq_norm]
      simp [Complex.normSq_apply]
    · intro n _
      have hcont : Continuous (fun z : ℝ => @fourier 2 n (z : AddCircle (2 : ℝ))) := by
        simp_rw [char2_coe]; fun_prop
      have hgn : IntegrableOn (fun z : ℝ => (g z : ℂ) * @fourier 2 n (z : AddCircle (2 : ℝ)))
          (Set.Ioc (0 : ℝ) 2) volume := by
        refine Integrable.mono' hgi.norm.integrableOn ?_ ?_
        · exact (Complex.continuous_ofReal.comp_aestronglyMeasurable
            hgi.aestronglyMeasurable.restrict).mul hcont.aestronglyMeasurable
        · filter_upwards with z
          simp only [norm_mul, Complex.norm_real, char2_norm, mul_one, le_refl]
      exact hgn.const_mul _
  have hS2_val :
      ∫ z in Set.Ioc (0 : ℝ) 2, ‖S z‖ ^ 2 = (1 / 2 : ℝ) * ∑ n ∈ F, ‖c n‖ ^ 2 := by
    have hpt : (fun z : ℝ => ‖S z‖ ^ 2) = fun z : ℝ => (S z * starRingEnd ℂ (S z)).re := by
      funext z; rw [Complex.sq_norm]; simp [Complex.normSq_apply]
    rw [hpt]
    have hSS_int : IntegrableOn (fun z : ℝ => S z * starRingEnd ℂ (S z))
        (Set.Ioc (0 : ℝ) 2) volume :=
      (hS_cont.mul (Complex.continuous_conj.comp hS_cont)).continuousOn.integrableOn_Icc.mono_set
        Set.Ioc_subset_Icc_self
    have hre2 : ∫ z in Set.Ioc (0 : ℝ) 2, (S z * starRingEnd ℂ (S z)).re =
        (∫ z in Set.Ioc (0 : ℝ) 2, S z * starRingEnd ℂ (S z)).re :=
      Complex.reCLM.integral_comp_comm hSS_int
    rw [hre2]
    have hexp : (fun z : ℝ => S z * starRingEnd ℂ (S z)) =
        fun z : ℝ => (1 / 4 : ℂ) * ∑ n ∈ F, ∑ m ∈ F,
          (c n * starRingEnd ℂ (c m)) * @fourier 2 (m - n) (z : AddCircle (2 : ℝ)) := by
      funext z
      simp only [S, map_mul, map_div₀, map_one, map_ofNat, map_sum]
      calc (1 / 2 : ℂ) * (∑ n ∈ F, c n * @fourier 2 (-n) (z : AddCircle (2 : ℝ))) *
            ((1 / 2 : ℂ) * ∑ m ∈ F, starRingEnd ℂ (c m) *
              starRingEnd ℂ (@fourier 2 (-m) (z : AddCircle (2 : ℝ))))
          = (1 / 4 : ℂ) * ((∑ n ∈ F, c n * @fourier 2 (-n) (z : AddCircle (2 : ℝ))) *
              (∑ m ∈ F, starRingEnd ℂ (c m) *
                starRingEnd ℂ (@fourier 2 (-m) (z : AddCircle (2 : ℝ))))) := by ring
        _ = (1 / 4 : ℂ) * ∑ n ∈ F, ∑ m ∈ F,
              (c n * starRingEnd ℂ (c m)) * @fourier 2 (m - n) (z : AddCircle (2 : ℝ)) := by
            congr 1
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun n _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun m _ => ?_
            rw [← char2_mul_conj n m z]; ring
    rw [hexp, integral_const_mul, integral_finsetSum]
    · have hinner : ∀ n ∈ F,
          ∫ z in Set.Ioc (0 : ℝ) 2, ∑ m ∈ F,
            (c n * starRingEnd ℂ (c m)) * @fourier 2 (m - n) (z : AddCircle (2 : ℝ)) =
          (c n * starRingEnd ℂ (c n)) * (2 : ℂ) := by
        intro n hn
        rw [integral_finsetSum]
        · have hterm : ∀ m ∈ F,
              ∫ z in Set.Ioc (0 : ℝ) 2,
                (c n * starRingEnd ℂ (c m)) * @fourier 2 (m - n) (z : AddCircle (2 : ℝ)) =
              if m = n then (c n * starRingEnd ℂ (c m)) * (2 : ℂ) else 0 := by
            intro m _
            rw [integral_const_mul, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 2),
              intervalIntegral_char2 (m - n)]
            by_cases hmn : m = n
            · subst hmn; simp
            · have : m - n ≠ 0 := sub_ne_zero.mpr hmn
              simp [hmn, this]
          rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' F n, if_pos hn]
        · intro m _
          have hcont : Continuous (fun z : ℝ =>
              (c n * starRingEnd ℂ (c m)) * @fourier 2 (m - n) (z : AddCircle (2 : ℝ))) := by
            simp_rw [char2_coe]; fun_prop
          exact hcont.continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
      rw [Finset.sum_congr rfl hinner]
      have hdiv : ((1 / 4 : ℂ) * ∑ n ∈ F, c n * starRingEnd ℂ (c n) * 2).re =
          (1 / 2 : ℝ) * (∑ n ∈ F, c n * starRingEnd ℂ (c n)).re := by
        rw [← Finset.sum_mul, show (1 / 4 : ℂ) * ((∑ n ∈ F, c n * starRingEnd ℂ (c n)) * 2) =
            (1 / 2 : ℂ) * ∑ n ∈ F, c n * starRingEnd ℂ (c n) by ring]
        simp [Complex.mul_re]
      rw [hdiv, Complex.re_sum]
      congr 1
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Complex.sq_norm]
      simp [Complex.normSq_apply]
    · intro n _
      have hcont : Continuous (fun z : ℝ => ∑ m ∈ F,
          (c n * starRingEnd ℂ (c m)) * @fourier 2 (m - n) (z : AddCircle (2 : ℝ))) := by
        refine continuous_finsetSum F fun m _ => ?_
        simp_rw [char2_coe]; fun_prop
      exact hcont.continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  linarith

private lemma integral_sq_conv_ge {f : ℝ → ℝ} (hf : Green35.IsUnitIntervalDensity f)
    (hgi : Integrable (f ⋆ f))
    (hgsq : Integrable (fun z => ((f ⋆ f) z) ^ 2)) :
    (473 / 625 : ℝ) ^ 2 ≤ ∫ z, ((f ⋆ f) z) ^ 2 := by
  obtain ⟨hfi, hf0, hfsupp, hf1⟩ := hf
  let c : ℤ → ℂ := fun n => ∫ x, (f x : ℂ) * @fourier 2 n (x : AddCircle (2 : ℝ))
  have hc0 : c 0 = 1 := by
    simp only [c, char2_zero, mul_one]
    have h1 : ∫ x : ℝ, (f x : ℂ) = ((∫ x : ℝ, f x : ℝ) : ℂ) :=
      Complex.ofRealCLM.integral_comp_comm hfi
    rw [h1, hf1, Complex.ofReal_one]
  have hc_neg : ∀ n : ℤ, ‖c (-n)‖ = ‖c n‖ := by
    intro n
    have hconj : c (-n) = starRingEnd ℂ (c n) := by
      simp only [c]
      rw [← integral_conj]
      congr 1; funext x
      rw [map_mul, Complex.conj_ofReal, fourier_neg]
    rw [hconj, Complex.norm_conj]
  have hg_Ioc : ∫ z in Set.Ioc (0 : ℝ) 2, ((f ⋆ f) z) ^ 2 = ∫ z, ((f ⋆ f) z) ^ 2 := by
    have hgsupp := convolution_support_subset hfsupp
    rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
    refine integral_congr_ae ?_
    have hne0 : ∀ᵐ z : ℝ ∂volume, z ≠ 0 := by rw [ae_iff]; simp
    filter_upwards [hne0] with z hz0
    by_cases hz : z ∈ Set.Ioc (0 : ℝ) 2
    · simp [Set.indicator_of_mem hz]
    · simp only [Set.indicator_of_notMem hz]
      have hnotIcc : z ∉ Set.Icc (0 : ℝ) 2 := fun h => hz ⟨lt_of_le_of_ne h.1 hz0.symm, h.2⟩
      have hg0 : (f ⋆ f) z = 0 := by by_contra hne; exact hnotIcc (hgsupp hne)
      simp [hg0]
  have hbessel_fin : ∀ N : ℕ,
      ∑ r ∈ Finset.range N, ‖c ((r + 1 : ℕ) : ℤ)‖ ^ 4 ≤ (∫ z, ((f ⋆ f) z) ^ 2) - 1 / 2 := by
    intro N
    let F : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)
    have hb := bessel_Ioc_two hgi hgsq (fun n => c n ^ 2) (fourier_coeff_conv hfi hfsupp) F
    rw [hg_Ioc] at hb
    have hsum_F : ∑ n ∈ F, ‖c n ^ 2‖ ^ 2 =
        1 + 2 * ∑ r ∈ Finset.range N, ‖c ((r + 1 : ℕ) : ℤ)‖ ^ 4 := by
      have hF_eq : F = insert (0 : ℤ)
          ((Finset.range N).image (fun r : ℕ => ((r + 1 : ℕ) : ℤ)) ∪
           (Finset.range N).image (fun r : ℕ => -((r + 1 : ℕ) : ℤ))) := by
        ext n
        simp only [F, Finset.mem_Icc, Finset.mem_insert, Finset.mem_union, Finset.mem_image,
          Finset.mem_range]
        constructor
        · intro ⟨_, _⟩
          by_cases hn0 : n = 0
          · exact Or.inl hn0
          · right
            by_cases hpos : 0 < n
            · left; exact ⟨(n - 1).toNat, by omega, by omega⟩
            · right; exact ⟨(-n - 1).toNat, by omega, by omega⟩
        · rintro (rfl | ⟨r, _, rfl⟩ | ⟨r, _, rfl⟩) <;> omega
      rw [hF_eq, Finset.sum_insert (by
        simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range]
        rintro (⟨r, _, hr⟩ | ⟨r, _, hr⟩) <;> omega)]
      have hdisj : Disjoint ((Finset.range N).image (fun r : ℕ => ((r + 1 : ℕ) : ℤ)))
          ((Finset.range N).image (fun r : ℕ => -((r + 1 : ℕ) : ℤ))) := by
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        rw [Finset.mem_image] at hx1 hx2
        obtain ⟨a, _, rfl⟩ := hx1
        obtain ⟨b, _, hb⟩ := hx2
        omega
      rw [Finset.sum_union hdisj,
        Finset.sum_image (by intro a _ b _ h; dsimp at h; omega),
        Finset.sum_image (by intro a _ b _ h; dsimp at h; omega)]
      simp only [hc0, one_pow, norm_one, norm_pow]
      have hpow4 : ∀ z : ℂ, (‖z‖ ^ 2) ^ 2 = ‖z‖ ^ 4 := fun _ => by ring
      simp_rw [hpow4, hc_neg]
      ring
    rw [hsum_F] at hb
    linarith
  have hc_summable : Summable (fun r : ℕ => ‖c ((r + 1 : ℕ) : ℤ)‖ ^ 4) :=
    summable_of_sum_range_le (fun _ => by positivity) hbessel_fin
  have hc_tsum_le : ∑' r : ℕ, ‖c ((r + 1 : ℕ) : ℤ)‖ ^ 4 ≤ (∫ z, ((f ⋆ f) z) ^ 2) - 1 / 2 :=
    hc_summable.tsum_le_of_sum_range_le hbessel_fin
  have hpair : (1 : ℂ) = ∑' n : ℤ, fourierCoeff V n * c n := by
    have hF_int : ∀ n : ℤ,
        Integrable (fun x : ℝ =>
          (f x : ℂ) * (fourierCoeff V n * @fourier 2 n (x : AddCircle (2 : ℝ)))) := by
      intro n
      have hcont : Continuous
          (fun x : ℝ => fourierCoeff V n * @fourier 2 n (x : AddCircle (2 : ℝ))) := by
        simp_rw [char2_coe]; fun_prop
      refine Integrable.mono' (hfi.norm.const_mul ‖fourierCoeff V n‖) ?_ ?_
      · exact (Complex.continuous_ofReal.comp_aestronglyMeasurable hfi.aestronglyMeasurable).mul
          hcont.aestronglyMeasurable
      · filter_upwards with x
        rw [norm_mul, norm_mul, Complex.norm_real, char2_norm, mul_one, mul_comm]
    have hF_norm_eq : ∀ n : ℤ,
        ∫ x : ℝ, ‖(f x : ℂ) * (fourierCoeff V n * @fourier 2 n (x : AddCircle (2 : ℝ)))‖ =
          ‖fourierCoeff V n‖ := by
      intro n
      have hpt : (fun x : ℝ =>
            ‖(f x : ℂ) * (fourierCoeff V n * @fourier 2 n (x : AddCircle (2 : ℝ)))‖) =
          (fun x : ℝ => ‖fourierCoeff V n‖ * f x) := by
        funext x
        rw [norm_mul, norm_mul, char2_norm, mul_one, Complex.norm_real,
          Real.norm_of_nonneg (hf0 x), mul_comm]
      rw [hpt, integral_const_mul, hf1, mul_one]
    have hF_sum : Summable (fun n : ℤ =>
        ∫ x : ℝ, ‖(f x : ℂ) * (fourierCoeff V n * @fourier 2 n (x : AddCircle (2 : ℝ)))‖) := by
      simp_rw [hF_norm_eq]
      exact summable_fourierCoeff_V.norm
    have hhas := hasSum_integral_of_summable_integral_norm hF_int hF_sum
    have htsum_pt : ∀ x : ℝ,
        (∑' n : ℤ, (f x : ℂ) * (fourierCoeff V n * @fourier 2 n (x : AddCircle (2 : ℝ)))) =
          (f x : ℂ) := by
      intro x
      by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
      · have hV := has_pointwise_sum_fourier_series_of_summable summable_fourierCoeff_V
            (x : AddCircle (2 : ℝ))
        rw [V_coe_of_mem_Icc01 hx] at hV
        simpa [smul_eq_mul] using (hV.mul_left (f x : ℂ)).tsum_eq
      · have hfx : f x = 0 := by by_contra hne; exact hx (hfsupp hne)
        simp [hfx]
    simp_rw [htsum_pt] at hhas
    have hint1 : ∫ x : ℝ, (f x : ℂ) = 1 := by
      have h1 : ∫ x : ℝ, (f x : ℂ) = ((∫ x : ℝ, f x : ℝ) : ℂ) :=
        Complex.ofRealCLM.integral_comp_comm hfi
      rw [h1, hf1, Complex.ofReal_one]
    rw [hint1] at hhas
    have hterm_eq : ∀ n : ℤ,
        ∫ x : ℝ, (f x : ℂ) * (fourierCoeff V n * @fourier 2 n (x : AddCircle (2 : ℝ))) =
          fourierCoeff V n * c n := by
      intro n
      have hmul : (fun x : ℝ =>
            (f x : ℂ) * (fourierCoeff V n * @fourier 2 n (x : AddCircle (2 : ℝ)))) =
          (fun x : ℝ =>
            fourierCoeff V n * ((f x : ℂ) * @fourier 2 n (x : AddCircle (2 : ℝ)))) := by
        funext x; ring
      rw [hmul, integral_const_mul]
    simp_rw [hterm_eq] at hhas
    exact hhas.tsum_eq.symm
  have hnorm_sum : Summable (fun n : ℤ => ‖fourierCoeff V n * c n‖) := by
    have hcn_le : ∀ n : ℤ, ‖c n‖ ≤ 1 := by
      intro n
      calc ‖c n‖ ≤ ∫ x, ‖(f x : ℂ) * @fourier 2 n (x : AddCircle (2 : ℝ))‖ :=
            norm_integral_le_integral_norm _
        _ = ∫ x, f x := by
            congr 1; funext x
            rw [norm_mul, char2_norm, mul_one, Complex.norm_real, Real.norm_of_nonneg (hf0 x)]
        _ = 1 := hf1
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_ summable_fourierCoeff_V.norm
    intro n
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hcn_le n)
  have h1_le_int : (1 : ℝ) ≤ ∑' n : ℤ, ‖fourierCoeff V n‖ * ‖c n‖ := by
    calc (1 : ℝ) = ‖(1 : ℂ)‖ := by simp
      _ = ‖∑' n : ℤ, fourierCoeff V n * c n‖ := by rw [hpair]
      _ ≤ ∑' n : ℤ, ‖fourierCoeff V n * c n‖ := norm_tsum_le_tsum_norm hnorm_sum
      _ = ∑' n : ℤ, ‖fourierCoeff V n‖ * ‖c n‖ := by simp_rw [norm_mul]
  have hfold : ∑' n : ℤ, ‖fourierCoeff V n‖ * ‖c n‖ =
      ∑' r : ℕ, kernHat (r + 1) * ‖c ((r + 1 : ℕ) : ℤ)‖ := by
    let g_int : ℤ → ℝ := fun n => ‖fourierCoeff V n‖ * ‖c n‖
    have hs_int : Summable g_int := by simpa [g_int, norm_mul] using hnorm_sum
    have hs_nat : Summable (fun n : ℕ => g_int n) := hs_int.comp_injective Int.ofNat_injective
    have hs_neg : Summable (fun n : ℕ => g_int (-((n : ℤ) + 1))) :=
      hs_int.comp_injective (by intro a b h; dsimp at h; omega)
    change ∑' n : ℤ, g_int n = _
    rw [tsum_of_nat_of_neg_add_one hs_nat hs_neg]
    have hnat_succ : ∑' n : ℕ, g_int n = ∑' r : ℕ, g_int ((r + 1 : ℕ) : ℤ) := by
      rw [hs_nat.tsum_eq_zero_add]
      simp [g_int, fourierCoeff_V_zero]
    rw [hnat_succ]
    have hneg_eq : (fun r : ℕ => g_int (-((r : ℤ) + 1))) =
        (fun r : ℕ => g_int ((r + 1 : ℕ) : ℤ)) := by
      funext r
      have hcast : -((r : ℤ) + 1) = -((r + 1 : ℕ) : ℤ) := by push_cast; ring
      simp only [g_int, hcast, hc_neg]
      rw [norm_fourierCoeff_V (-((r + 1 : ℕ) : ℤ)) (by omega),
        norm_fourierCoeff_V ((r + 1 : ℕ) : ℤ) (by omega), Int.natAbs_neg]
    rw [hneg_eq, ← two_mul, ← tsum_mul_left]
    congr 1; funext r
    simp only [g_int]
    rw [norm_fourierCoeff_V ((r + 1 : ℕ) : ℤ) (by omega)]
    simp only [Int.natAbs_natCast]
    ring
  have h1_le_nat : (1 : ℝ) ≤ ∑' r : ℕ, kernHat (r + 1) * ‖c ((r + 1 : ℕ) : ℤ)‖ := by
    linarith
  set lam : ℝ := (10000 / 23945 : ℝ)
  have hpt_young : ∀ r : ℕ,
      4 * lam ^ 3 * (kernHat (r + 1) * ‖c ((r + 1 : ℕ) : ℤ)‖) ≤
        3 * lam ^ 4 * w (r + 1) ^ 4 + ‖c ((r + 1 : ℕ) : ℤ)‖ ^ 4 := by
    intro r
    have hle_w := kernHat_le_w_cube (r + 1) (Nat.succ_pos r)
    calc 4 * lam ^ 3 * (kernHat (r + 1) * ‖c ((r + 1 : ℕ) : ℤ)‖)
        ≤ 4 * lam ^ 3 * (w (r + 1) ^ 3 * ‖c ((r + 1 : ℕ) : ℤ)‖) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hle_w (norm_nonneg _)) (by positivity)
      _ = 4 * (lam * w (r + 1)) ^ 3 * ‖c ((r + 1 : ℕ) : ℤ)‖ := by ring
      _ ≤ 3 * (lam * w (r + 1)) ^ 4 + ‖c ((r + 1 : ℕ) : ℤ)‖ ^ 4 :=
          quartic_young (lam * w (r + 1)) ‖c ((r + 1 : ℕ) : ℤ)‖
      _ = 3 * lam ^ 4 * w (r + 1) ^ 4 + ‖c ((r + 1 : ℕ) : ℤ)‖ ^ 4 := by ring
  have hrhs_sum : Summable (fun r : ℕ =>
      3 * lam ^ 4 * w (r + 1) ^ 4 + ‖c ((r + 1 : ℕ) : ℤ)‖ ^ 4) :=
    (summable_w_pow4.mul_left (3 * lam ^ 4)).add hc_summable
  have hlhs_sum : Summable (fun r : ℕ =>
      4 * lam ^ 3 * (kernHat (r + 1) * ‖c ((r + 1 : ℕ) : ℤ)‖)) :=
    Summable.of_nonneg_of_le
      (fun _ => mul_nonneg (by positivity) (mul_nonneg (abs_nonneg _) (norm_nonneg _)))
      hpt_young hrhs_sum
  have hsum_young :
      4 * lam ^ 3 * (∑' r : ℕ, kernHat (r + 1) * ‖c ((r + 1 : ℕ) : ℤ)‖) ≤
        3 * lam ^ 4 * (∑' r : ℕ, w (r + 1) ^ 4) + ∑' r : ℕ, ‖c ((r + 1 : ℕ) : ℤ)‖ ^ 4 := by
    rw [← tsum_mul_left]
    calc ∑' r : ℕ, 4 * lam ^ 3 * (kernHat (r + 1) * ‖c ((r + 1 : ℕ) : ℤ)‖)
        ≤ ∑' r : ℕ, (3 * lam ^ 4 * w (r + 1) ^ 4 + ‖c ((r + 1 : ℕ) : ℤ)‖ ^ 4) :=
          hlhs_sum.tsum_le_tsum hpt_young hrhs_sum
      _ = 3 * lam ^ 4 * (∑' r : ℕ, w (r + 1) ^ 4) + ∑' r : ℕ, ‖c ((r + 1 : ℕ) : ℤ)‖ ^ 4 := by
          rw [(summable_w_pow4.mul_left (3 * lam ^ 4)).tsum_add hc_summable, tsum_mul_left]
  have hchain : 4 * lam ^ 3 * 1 ≤
      3 * lam ^ 4 * (23945 / 10000 : ℝ) + ((∫ z, ((f ⋆ f) z) ^ 2) - 1 / 2) :=
    calc 4 * lam ^ 3 * 1
        ≤ 4 * lam ^ 3 * (∑' r : ℕ, kernHat (r + 1) * ‖c ((r + 1 : ℕ) : ℤ)‖) :=
          mul_le_mul_of_nonneg_left h1_le_nat (by positivity)
      _ ≤ 3 * lam ^ 4 * (∑' r : ℕ, w (r + 1) ^ 4) + ∑' r : ℕ, ‖c ((r + 1 : ℕ) : ℤ)‖ ^ 4 :=
          hsum_young
      _ ≤ 3 * lam ^ 4 * (23945 / 10000 : ℝ) + ((∫ z, ((f ⋆ f) z) ^ 2) - 1 / 2) :=
          add_le_add (mul_le_mul_of_nonneg_left tsum_w_pow4_le (by positivity)) hc_tsum_le
  dsimp only [lam] at hchain
  have hnum : (473 / 625 : ℝ) ^ 2 ≤
      1 / 2 + (4 * (10000 / 23945 : ℝ) ^ 3 * 1 -
        3 * (10000 / 23945 : ℝ) ^ 4 * (23945 / 10000 : ℝ)) := by
    norm_num
  linarith

end BimodalKernelBound

open scoped ENNReal

noncomputable def OMA.answer : ℝ≥0∞ → ℝ≥0∞ :=
  fun p => if p = 2 then (473 / 625 : ℝ≥0∞) else 0

open scoped Convolution ENNReal in
theorem OMA.solution : Green35.green_35.lower.answer = OMA.answer → type_of% @Green35.green_35.lower := by
  intro h_ans
  rw [h_ans]
  refine ⟨?_, Or.inl ?_⟩
  · intro p _
    dsimp only [OMA.answer]
    split_ifs with hp2
    · subst hp2
      unfold Green35.c
      apply le_sInf
      rintro r ⟨f, hf, rfl⟩
      by_cases htop : MeasureTheory.eLpNorm (f ⋆ f) 2 MeasureTheory.volume = ⊤
      · rw [htop]; exact le_top
      · have hgi : MeasureTheory.Integrable (f ⋆ f) :=
          hf.1.integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hf.1
        have h2 : MeasureTheory.eLpNorm (f ⋆ f) 2 MeasureTheory.volume ^ 2 =
            ∫⁻ z, ‖(f ⋆ f) z‖ₑ ^ (2 : ℝ) := by
          rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
          have ht : (2 : ℝ≥0∞).toReal = 2 := by norm_num
          rw [ht, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
          norm_num
        have hfin : ∫⁻ z, ‖(f ⋆ f) z‖ₑ ^ (2 : ℝ) ≠ ⊤ := by
          rw [← h2]
          exact ENNReal.pow_ne_top htop
        have hgsq_eq : ∀ z, ‖(f ⋆ f) z‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (((f ⋆ f) z) ^ 2) := by
          intro z
          rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast,
            ← enorm_pow, Real.enorm_eq_ofReal (sq_nonneg _)]
        have hgsq : MeasureTheory.Integrable (fun z => ((f ⋆ f) z) ^ 2) := by
          refine ⟨hgi.aestronglyMeasurable.pow 2, ?_⟩
          rw [MeasureTheory.hasFiniteIntegral_iff_enorm]
          have hconv : (fun z => ‖((f ⋆ f) z) ^ 2‖ₑ) = fun z => ‖(f ⋆ f) z‖ₑ ^ (2 : ℝ) := by
            funext z
            rw [hgsq_eq, Real.enorm_eq_ofReal (sq_nonneg _)]
          rw [hconv]
          exact lt_top_iff_ne_top.mpr hfin
        have hge := BimodalKernelBound.integral_sq_conv_ge hf hgi hgsq
        have hof : (473 / 625 : ℝ≥0∞) = ENNReal.ofReal (473 / 625 : ℝ) := by
          rw [ENNReal.ofReal_div_of_pos (by norm_num)]
          norm_num
        rw [hof]
        have hsq_le : ENNReal.ofReal (473 / 625 : ℝ) ^ 2 ≤
            MeasureTheory.eLpNorm (f ⋆ f) 2 MeasureTheory.volume ^ 2 := by
          rw [← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 473 / 625), h2]
          simp_rw [hgsq_eq]
          rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hgsq
            (Filter.Eventually.of_forall (fun _ => sq_nonneg _))]
          exact ENNReal.ofReal_le_ofReal hge
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast] at hsq_le
        exact (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < (2 : ℕ))).mp hsq_le
    · exact zero_le
  · dsimp only [OMA.answer]
    rw [if_pos rfl]
    have h1 : Real.sqrt (4 / 7) < (473 / 625 : ℝ) := by
      rw [Real.sqrt_lt' (by norm_num)]
      norm_num
    have h2 : ENNReal.ofReal (473 / 625 : ℝ) = (473 / 625 : ℝ≥0∞) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]
      norm_num
    rw [← h2]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr h1
