import OMAReductions.R_Erdos338_erdos_338_variants_triangular_R1_H1_R1_H1_R1_H1_R1_H1_R1
import Mathlib

/-!
# Siegel lower bound for the Jacobi L-series

Analytic estimates are adapted from @nil-commits, Arithmetica4, commit
023f6441c22a9ca0db1670e351e8ac44f00555ea, used under Apache-2.0.
The source modules cover partial summation, analytic continuation for Dirichlet
L-functions, the Landau bound for two real characters, and the argument of
Tatuzawa and Siegel. The proof here constructs the Jacobi character at the
given squarefree modulus and identifies its real harmonic sum with the L-value.
-/
noncomputable section

open scoped ArithmeticFunction.vonMangoldt

open Complex NumberField

namespace RHDirect

structure PChar where
  N : ℕ
  [ne : NeZero N]
  χ : DirichletCharacter ℂ N
  prim : χ.IsPrimitive

instance (ψ : PChar) : NeZero ψ.N := ψ.ne

namespace PChar

def one : PChar := ⟨1, 1, DirichletCharacter.isPrimitive_one_level_one⟩

def inv (ψ : PChar) : PChar :=
  ⟨ψ.N, ψ.χ⁻¹, by
    have h : ψ.χ.conductor = ψ.N := ψ.prim
    exact (DirichletCharacter.conductor_inv ψ.χ).trans h⟩

def of {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : PChar :=
  @PChar.mk χ.conductor ⟨χ.conductor_ne_zero⟩ χ.primitiveCharacter χ.primitiveCharacter_isPrimitive

def IsReal (ψ : PChar) : Prop := ∀ a : ZMod ψ.N, (ψ.χ a).im = 0

private theorem mk_eq_of_changeLevel_eq_self {N d : ℕ} [NeZero N] [NeZero d]
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ d)
    (hd : d ∣ N) (hc : DirichletCharacter.changeLevel hd ψ = χ)
    (h1 : ψ.IsPrimitive) (h2 : χ.IsPrimitive) (he : d = N) :
    PChar.mk d ψ h1 = PChar.mk N χ h2 := by
  subst he
  rw [DirichletCharacter.changeLevel_self] at hc
  subst hc
  rfl

theorem of_self (ψ : PChar) : PChar.of ψ.χ = ψ := by
  have : NeZero ψ.χ.conductor := ⟨ψ.χ.conductor_ne_zero⟩
  exact mk_eq_of_changeLevel_eq_self ψ.χ ψ.χ.primitiveCharacter ψ.χ.conductor_dvd_level
    ψ.χ.changeLevel_primitiveCharacter ψ.χ.primitiveCharacter_isPrimitive ψ.prim ψ.prim

end PChar
end RHDirect
end

noncomputable section

open Complex DirichletCharacter Filter Topology

open scoped ArithmeticFunction.vonMangoldt

namespace RHDirect

theorem LSeries_vonMangoldt_eq_neg_deriv_zeta_div {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (Λ n : ℂ)) s = -deriv riemannZeta s / riemannZeta s := by
  simpa using ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs

theorem LSeries_twist_vonMangoldt_eq_neg_deriv_LFunction_div {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => χ n * (Λ n : ℂ)) s =
      -deriv (LFunction χ) s / LFunction χ s := by
  rw [LFunction_eq_LSeries χ hs, deriv_LFunction_eq_deriv_LSeries χ hs]
  exact LSeries_twist_vonMangoldt_eq χ hs

end RHDirect

end

noncomputable section

open Complex DirichletCharacter Finset RHDirect

open scoped ArithmeticFunction.vonMangoldt

namespace RHDirect.Stage2DirichletAP

theorem LFunction_ne_zero_of_one_le_re_bridge {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hχs : χ ≠ 1 ∨ s ≠ 1) (hs : 1 ≤ s.re) :
    LFunction χ s ≠ 0 :=
  DirichletCharacter.LFunction_ne_zero_of_one_le_re χ hχs hs

theorem LFunction_apply_one_ne_zero_bridge {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) : LFunction χ 1 ≠ 0 :=
  DirichletCharacter.LFunction_apply_one_ne_zero hχ

end RHDirect.Stage2DirichletAP

end

noncomputable section

open Complex MeasureTheory Set Filter Topology

open scoped ArithmeticFunction.vonMangoldt BigOperators

namespace RHDirect.Stage3RealAnalyticLandau

def dirSeries (a : ℕ → ℝ) (s : ℂ) : ℂ :=
  ∑' n : ℕ, if n = 0 then (0 : ℂ) else (a n : ℂ) * (n : ℂ) ^ (-s)

theorem dirSeries_eq_LSeries (a : ℕ → ℝ) (s : ℂ) :
    dirSeries a s = LSeries (fun n => (a n : ℂ)) s := by
  unfold dirSeries LSeries
  refine tsum_congr fun n => ?_
  by_cases hn : n = 0
  · simp [hn, LSeries.term_zero]
  · simp [hn, Complex.cpow_neg, div_eq_mul_inv]

theorem dirSeriesSummable_iff_real {a : ℕ → ℝ} (ha0 : a 0 = 0) (ha : ∀ n, 0 ≤ a n) (s : ℂ) :
    LSeriesSummable (fun n => (a n : ℂ)) s ↔ Summable (fun n : ℕ => a n * (n : ℝ) ^ (-s.re)) := by
  rw [LSeriesSummable, ← summable_norm_iff]
  refine summable_congr fun n => ?_
  by_cases hn : n = 0
  · subst hn
    simp [LSeries.term_zero, ha0]
  · have hpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    rw [LSeries.term_of_ne_zero hn, norm_div, Complex.norm_real, Real.norm_of_nonneg (ha n),
      Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn), Real.rpow_neg hpos.le,
      div_eq_mul_inv]

private lemma logMul_iterate_apply (f : ℕ → ℂ) (k n : ℕ) :
    (LSeries.logMul^[k] f) n = (Complex.log (n : ℂ)) ^ k * f n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', LSeries.logMul, ih, pow_succ]
    ring

theorem summable_log_pow_mul_rpow {a : ℕ → ℝ} (ha0 : a 0 = 0) (ha : ∀ n, 0 ≤ a n)
    {σ₀ σ : ℝ} (hconv : ∀ x : ℝ, σ₀ < x → LSeriesSummable (fun n => (a n : ℂ)) (x : ℂ))
    (hσ : σ₀ < σ) (k : ℕ) :
    Summable (fun n : ℕ => a n * (Real.log (n : ℝ)) ^ k * (n : ℝ) ^ (-σ)) := by
  set ε : ℝ := (σ - σ₀) / 2 with hε_def
  have hε0 : 0 < ε := by linarith
  have hσ' : σ₀ < σ - ε := by linarith
  have hbase : Summable (fun n : ℕ => a n * (n : ℝ) ^ (-(σ - ε))) :=
    (dirSeriesSummable_iff_real ha0 ha ((σ - ε : ℝ) : ℂ)).mp (hconv (σ - ε) hσ')
  have hC : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → (Real.log (n : ℝ)) ^ k ≤ C * (n : ℝ) ^ ε := by
    by_cases hk : k = 0
    · subst hk
      refine ⟨1, one_pos, fun n hn => ?_⟩
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr hn
      simp [Real.one_le_rpow hn1 hε0.le]
    · have hkpos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
      set α : ℝ := ε / (k : ℝ) with hα_def
      have hα0 : 0 < α := div_pos hε0 hkpos
      refine ⟨(1 / α) ^ k, by positivity, fun n hn => ?_⟩
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr hn
      have hn0 : (0 : ℝ) < (n : ℝ) := zero_lt_one.trans_le hn1
      have hlog : Real.log (n : ℝ) ≤ (1 / α) * (n : ℝ) ^ α := by
        have h := Real.log_le_rpow_div hn0.le hα0
        linarith [show (n : ℝ) ^ α / α = (1 / α) * (n : ℝ) ^ α by ring]
      calc (Real.log (n : ℝ)) ^ k
          ≤ ((1 / α) * (n : ℝ) ^ α) ^ k :=
            pow_le_pow_left₀ (Real.log_nonneg hn1) hlog k
        _ = (1 / α) ^ k * ((n : ℝ) ^ α) ^ k := mul_pow _ _ k
        _ = (1 / α) ^ k * (n : ℝ) ^ (α * (k : ℝ)) := by
            rw [← Real.rpow_natCast ((n : ℝ) ^ α) k, ← Real.rpow_mul hn0.le]
        _ = (1 / α) ^ k * (n : ℝ) ^ ε := by
            rw [hα_def, div_mul_cancel₀ _ hkpos.ne']
  obtain ⟨C, hC0, hCbd⟩ := hC
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) (hbase.mul_left C)
  · by_cases hn : n = 0
    · subst hn; simp [ha0]
    · have hn1 : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr (Nat.pos_of_ne_zero hn)
      exact mul_nonneg (mul_nonneg (ha n) (pow_nonneg (Real.log_nonneg hn1) k))
        (Real.rpow_nonneg (zero_le_one.trans hn1) (-σ))
  · by_cases hn : n = 0
    · subst hn; simp [ha0]
    · have hn1 : 1 ≤ n := Nat.pos_of_ne_zero hn
      have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn1
      have h1 := hCbd n hn1
      have hpow : (n : ℝ) ^ ε * (n : ℝ) ^ (-σ) = (n : ℝ) ^ (-(σ - ε)) := by
        rw [← Real.rpow_add hn0]
        congr 1; ring
      calc a n * (Real.log (n : ℝ)) ^ k * (n : ℝ) ^ (-σ)
          ≤ a n * (C * (n : ℝ) ^ ε) * (n : ℝ) ^ (-σ) := by
            gcongr
            exact ha n
        _ = C * (a n * ((n : ℝ) ^ ε * (n : ℝ) ^ (-σ))) := by ring
        _ = C * (a n * (n : ℝ) ^ (-(σ - ε))) := by rw [hpow]

theorem alternating_iteratedDeriv_dirSeries_real {a : ℕ → ℝ} (ha0 : a 0 = 0)
    {σ₀ σ : ℝ} (hconv : ∀ x : ℝ, σ₀ < x → LSeriesSummable (fun n => (a n : ℂ)) (x : ℂ))
    (hσ : σ₀ < σ) (k : ℕ) :
    (-1 : ℂ) ^ k * iteratedDeriv k (dirSeries a) (σ : ℂ) =
      ((∑' n : ℕ, a n * (Real.log (n : ℝ)) ^ k * (n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
  have hfun : dirSeries a = LSeries (fun n => (a n : ℂ)) := funext (dirSeries_eq_LSeries a)
  rw [hfun]
  have habs : LSeries.abscissaOfAbsConv (fun n => (a n : ℂ)) ≤ (σ₀ : EReal) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable hconv
  have hlt : LSeries.abscissaOfAbsConv (fun n => (a n : ℂ)) < ((σ : ℂ).re : EReal) := by
    rw [Complex.ofReal_re]
    exact lt_of_le_of_lt habs (EReal.coe_lt_coe_iff.mpr hσ)
  rw [LSeries_iteratedDeriv k hlt, ← mul_assoc, ← mul_pow]
  have hsign : ((-1 : ℂ) * (-1 : ℂ)) ^ k = 1 := by norm_num
  rw [hsign, one_mul, LSeries, Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  by_cases hn : n = 0
  · subst hn
    simp [LSeries.term_zero, ha0]
  · have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    rw [LSeries.term_of_ne_zero hn, logMul_iterate_apply]
    have hlog : Complex.log (n : ℂ) = (Real.log (n : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast, Complex.ofReal_log hn0.le]
    have hcpow : (n : ℂ) ^ (σ : ℂ) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast, Complex.ofReal_cpow hn0.le]
    rw [hlog, hcpow, Real.rpow_neg hn0.le]
    push_cast
    rw [div_eq_mul_inv]
    ring

def stepSum (a : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n

theorem stepSum_const_on_Ico (a : ℕ → ℂ) (k : ℕ) {t : ℝ} (ht1 : (k : ℝ) ≤ t)
    (ht2 : t < ((k + 1 : ℕ) : ℝ)) :
    stepSum a t = stepSum a (k : ℝ) := by
  unfold stepSum
  have hfl : ⌊t⌋₊ = k := (Nat.floor_eq_iff (le_trans (Nat.cast_nonneg k) ht1)).mpr
    ⟨ht1, by exact_mod_cast ht2⟩
  rw [hfl, Nat.floor_natCast]

theorem measurable_stepSum (a : ℕ → ℂ) : Measurable (stepSum a) := by
  have h : stepSum a = (fun k : ℕ => ∑ n ∈ Finset.Icc 1 k, a n) ∘ Nat.floor := rfl
  rw [h]
  exact Measurable.comp (measurable_of_countable _) Nat.measurable_floor

private lemma intervalIntegral_stepSum_unit (a : ℕ → ℂ) (k : ℕ) {φ φ' : ℝ → ℂ}
    (hd : ∀ t ∈ Set.uIcc (k : ℝ) ((k + 1 : ℕ) : ℝ), HasDerivAt φ (φ' t) t)
    (hc : ContinuousOn φ' (Set.uIcc (k : ℝ) ((k + 1 : ℕ) : ℝ))) :
    ∫ t in (k : ℝ)..((k + 1 : ℕ) : ℝ), stepSum a t * φ' t =
      stepSum a (k : ℝ) * (φ ((k + 1 : ℕ) : ℝ) - φ (k : ℝ)) := by
  have hle : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hae : ∀ᵐ t ∂volume, t ∈ Set.uIoc (k : ℝ) ((k + 1 : ℕ) : ℝ) →
      stepSum a t * φ' t = stepSum a (k : ℝ) * φ' t := by
    have hne : ∀ᵐ t ∂volume, t ≠ ((k + 1 : ℕ) : ℝ) := by
      rw [ae_iff]; simp
    filter_upwards [hne] with t hne ht
    rw [Set.uIoc_of_le hle, Set.mem_Ioc] at ht
    rw [stepSum_const_on_Ico a k ht.1.le (lt_of_le_of_ne ht.2 hne)]
  rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable)]

private lemma intervalIntegrable_stepSum_mul_unit (a : ℕ → ℂ) (k : ℕ) {φ' : ℝ → ℂ}
    (hc : ContinuousOn φ' (Set.uIcc (k : ℝ) ((k + 1 : ℕ) : ℝ))) :
    IntervalIntegrable (fun t => stepSum a t * φ' t) volume (k : ℝ) ((k + 1 : ℕ) : ℝ) := by
  have hle : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hconst : IntervalIntegrable (fun t => stepSum a (k : ℝ) * φ' t) volume (k : ℝ)
      ((k + 1 : ℕ) : ℝ) :=
    (hc.intervalIntegrable).const_mul _
  refine hconst.congr_ae ?_
  have hne : ∀ᵐ t ∂volume, t ≠ ((k + 1 : ℕ) : ℝ) := by rw [ae_iff]; simp
  refine (ae_restrict_iff' measurableSet_uIoc).mpr ?_
  filter_upwards [hne] with t hne ht
  rw [Set.uIoc_of_le hle, Set.mem_Ioc] at ht
  exact (congrArg (· * φ' t) (stepSum_const_on_Ico a k ht.1.le (lt_of_le_of_ne ht.2 hne))).symm

theorem abel_summation_general (a : ℕ → ℂ) {x : ℝ} (hx : 1 ≤ x) {φ φ' : ℝ → ℂ}
    (hd : ∀ t ∈ Set.Icc (1 : ℝ) x, HasDerivAt φ (φ' t) t)
    (hc : ContinuousOn φ' (Set.Icc (1 : ℝ) x)) :
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n * φ (n : ℝ) =
      stepSum a x * φ x - ∫ t in (1 : ℝ)..x, stepSum a t * φ' t := by
  have hN1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have hfl_le : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (zero_le_one.trans hx)
  
  have hint_nat : ∀ N : ℕ, 1 ≤ N → (N : ℝ) ≤ x →
      IntervalIntegrable (fun t => stepSum a t * φ' t) volume (1 : ℝ) (N : ℝ) ∧
      ∑ n ∈ Finset.Icc 1 N, a n * φ (n : ℝ) =
        stepSum a (N : ℝ) * φ (N : ℝ) - ∫ t in (1 : ℝ)..(N : ℝ), stepSum a t * φ' t := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base =>
      intro _
      simp [stepSum]
    | succ m hm ih =>
      intro hm1
      have hm_le : (m : ℝ) ≤ x := le_trans (by push_cast; linarith) hm1
      obtain ⟨hint_m, heq_m⟩ := ih hm_le
      have hsub_u : Set.uIcc (m : ℝ) ((m + 1 : ℕ) : ℝ) ⊆ Set.Icc (1 : ℝ) x := by
        rw [Set.uIcc_of_le (by push_cast; linarith)]
        intro t ht
        have hm1R : (1 : ℝ) ≤ (m : ℝ) := Nat.one_le_cast.mpr hm
        exact ⟨le_trans hm1R ht.1, le_trans ht.2 hm1⟩
      have hint_step := intervalIntegrable_stepSum_mul_unit a m (hc.mono hsub_u)
      have hval_step := intervalIntegral_stepSum_unit a m (fun t ht => hd t (hsub_u ht))
        (hc.mono hsub_u)
      refine ⟨hint_m.trans hint_step, ?_⟩
      rw [← intervalIntegral.integral_add_adjacent_intervals hint_m hint_step, hval_step]
      have hIcc : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hnot : m + 1 ∉ Finset.Icc 1 m := by simp
      have hstep_succ : stepSum a ((m + 1 : ℕ) : ℝ) = stepSum a (m : ℝ) + a (m + 1) := by
        unfold stepSum
        rw [Nat.floor_natCast, Nat.floor_natCast, hIcc, Finset.sum_insert hnot]
        ring
      rw [hIcc, Finset.sum_insert hnot, heq_m, hstep_succ]
      ring
  obtain ⟨hint_N, heq_N⟩ := hint_nat ⌊x⌋₊ hN1 hfl_le
  
  have hsub_tail : Set.uIcc (⌊x⌋₊ : ℝ) x ⊆ Set.Icc (1 : ℝ) x := by
    rw [Set.uIcc_of_le hfl_le]
    intro t ht
    exact ⟨le_trans (Nat.one_le_cast.mpr hN1) ht.1, ht.2⟩
  have htail_ae : ∀ᵐ t ∂volume, t ∈ Set.uIoc (⌊x⌋₊ : ℝ) x →
      stepSum a t * φ' t = stepSum a (⌊x⌋₊ : ℝ) * φ' t := by
    have hne : ∀ᵐ t ∂volume, t ≠ x := by rw [ae_iff]; simp
    filter_upwards [hne] with t hne ht
    rw [Set.uIoc_of_le hfl_le, Set.mem_Ioc] at ht
    have hlt : t < ((⌊x⌋₊ + 1 : ℕ) : ℝ) := lt_trans (lt_of_le_of_ne ht.2 hne) (by
      push_cast; exact Nat.lt_floor_add_one x)
    rw [stepSum_const_on_Ico a ⌊x⌋₊ ht.1.le hlt]
  have hint_tail : IntervalIntegrable (fun t => stepSum a t * φ' t) volume (⌊x⌋₊ : ℝ) x := by
    refine ((hc.mono hsub_tail).intervalIntegrable.const_mul (stepSum a (⌊x⌋₊ : ℝ))).congr_ae ?_
    refine (ae_restrict_iff' measurableSet_uIoc).mpr ?_
    filter_upwards [htail_ae] with t ht hmem using (ht hmem).symm
  have hval_tail : ∫ t in (⌊x⌋₊ : ℝ)..x, stepSum a t * φ' t =
      stepSum a (⌊x⌋₊ : ℝ) * (φ x - φ (⌊x⌋₊ : ℝ)) := by
    rw [intervalIntegral.integral_congr_ae htail_ae, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hd t (hsub_tail ht))
        (hc.mono hsub_tail).intervalIntegrable]
  have hstep_x : stepSum a x = stepSum a (⌊x⌋₊ : ℝ) := by
    unfold stepSum; rw [Nat.floor_natCast]
  rw [← intervalIntegral.integral_add_adjacent_intervals hint_N hint_tail, hval_tail, heq_N,
    hstep_x]
  ring

theorem abel_summation_dirichlet (a : ℕ → ℂ) {x : ℝ} (hx : 1 ≤ x) (s : ℂ) :
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n * (n : ℂ) ^ (-s) =
      stepSum a x * (x : ℂ) ^ (-s) + s * ∫ t in (1 : ℝ)..x, stepSum a t * (t : ℂ) ^ (-s - 1) := by
  have hd : ∀ t ∈ Set.Icc (1 : ℝ) x,
      HasDerivAt (fun u : ℝ => (u : ℂ) ^ (-s)) ((-s) * (t : ℂ) ^ (-s - 1)) t := by
    intro t ht
    have ht0 : (0 : ℝ) < t := zero_lt_one.trans_le ht.1
    have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
    have hfun : (fun u : ℝ => (u : ℂ) ^ (-s)) =ᶠ[𝓝 t]
        fun u : ℝ => cexp ((Real.log u : ℂ) * (-s)) := by
      filter_upwards [isOpen_Ioi.mem_nhds ht0] with u hu
      have huC : (u : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
      rw [Complex.cpow_def_of_ne_zero huC, Complex.ofReal_log hu.le]
    have h1 : HasDerivAt (fun u : ℝ => cexp ((Real.log u : ℂ) * (-s)))
        (cexp ((Real.log t : ℂ) * (-s)) * (((t⁻¹ : ℝ) : ℂ) * (-s))) t := by
      exact (((Real.hasDerivAt_log ht0.ne').ofReal_comp).mul_const (-s)).cexp
    refine (h1.congr_of_eventuallyEq hfun).congr_deriv ?_
    have hcp : cexp ((Real.log t : ℂ) * (-s)) = (t : ℂ) ^ (-s) := by
      rw [Complex.cpow_def_of_ne_zero htC, Complex.ofReal_log ht0.le]
    rw [hcp, Complex.cpow_sub _ _ htC, Complex.cpow_one]
    push_cast; field_simp
  have hc : ContinuousOn (fun t : ℝ => (-s) * (t : ℂ) ^ (-s - 1)) (Set.Icc (1 : ℝ) x) := by
    refine continuousOn_const.mul ?_
    have hcont_exp : ContinuousOn (fun t : ℝ => cexp ((Real.log t : ℂ) * (-s - 1))) (Set.Icc (1 : ℝ) x) := by
      refine ContinuousOn.cexp (ContinuousOn.mul ?_ continuousOn_const)
      refine Complex.continuous_ofReal.comp_continuousOn ?_
      exact Real.continuousOn_log.mono fun t ht => (zero_lt_one.trans_le ht.1).ne'
    refine hcont_exp.congr fun t ht => ?_
    have ht0 : (0 : ℝ) < t := zero_lt_one.trans_le ht.1
    have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
    dsimp only
    rw [Complex.cpow_def_of_ne_zero htC, ← Complex.ofReal_log ht0.le]
  have hab := abel_summation_general a hx hd hc
  have hcast : ∀ n ∈ Finset.Icc 1 ⌊x⌋₊, a n * ((n : ℝ) : ℂ) ^ (-s) = a n * (n : ℂ) ^ (-s) := by
    intro n _; push_cast; rfl
  rw [Finset.sum_congr rfl hcast] at hab
  rw [hab]
  have hint : ∫ t in (1 : ℝ)..x, stepSum a t * ((-s) * (t : ℂ) ^ (-s - 1)) =
      (-s) * ∫ t in (1 : ℝ)..x, stepSum a t * (t : ℂ) ^ (-s - 1) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => by ring
  rw [hint]
  ring

theorem integrableOn_mellin_of_rpow_bound {E : ℝ → ℂ} (hE : Measurable E) {C θ : ℝ}
    (hbd : ∀ t : ℝ, 1 ≤ t → ‖E t‖ ≤ C * t ^ θ) {s : ℂ} (hs : θ < s.re) :
    IntegrableOn (fun t : ℝ => E t * (t : ℂ) ^ (-s - 1)) (Ioi (1 : ℝ)) := by
  have hexp : θ - s.re - 1 < -1 := by linarith
  refine Integrable.mono' ((integrableOn_Ioi_rpow_of_lt hexp zero_lt_one).const_mul C) ?_ ?_
  · have hpow : Measurable (fun t : ℝ => (t : ℂ) ^ (-s - 1)) :=
      Complex.measurable_ofReal.pow_const (-s - 1)
    exact (hE.mul hpow).aestronglyMeasurable
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
    have ht0 : (0 : ℝ) < t := zero_lt_one.trans ht
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    have hre : (-s - 1).re = -s.re - 1 := by simp
    rw [hre]
    calc ‖E t‖ * t ^ (-s.re - 1)
        ≤ (C * t ^ θ) * t ^ (-s.re - 1) :=
          mul_le_mul_of_nonneg_right (hbd t ht.le) (Real.rpow_nonneg ht0.le _)
      _ = C * (t ^ θ * t ^ (-s.re - 1)) := by ring
      _ = C * t ^ (θ - s.re - 1) := by
          rw [← Real.rpow_add ht0]; congr 2; ring

theorem hasDerivAt_mellin_of_rpow_bound {E : ℝ → ℂ} (hE : Measurable E) {C θ : ℝ} (hC : 0 ≤ C)
    (hbd : ∀ t : ℝ, 1 ≤ t → ‖E t‖ ≤ C * t ^ θ) {s : ℂ} (hs : θ < s.re) :
    HasDerivAt (fun z : ℂ => ∫ t in Ioi (1 : ℝ), E t * (t : ℂ) ^ (-z - 1))
      (∫ t in Ioi (1 : ℝ), E t * (-(Real.log t : ℂ) * (t : ℂ) ^ (-s - 1))) s := by
  set δ : ℝ := (s.re - θ) / 2 with hδ_def
  have hδ0 : 0 < δ := by linarith
  set e : ℝ := δ / 2 with he_def
  have he0 : 0 < e := by linarith
  have hre : ∀ z ∈ Metric.ball s δ, θ + δ ≤ z.re := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have h1 := (abs_le.mp ((Complex.abs_re_le_norm (z - s)).trans hz.le)).1
    rw [Complex.sub_re] at h1
    linarith
  have hmeasF : ∀ z : ℂ, AEStronglyMeasurable (fun t : ℝ => E t * (t : ℂ) ^ (-z - 1))
      (volume.restrict (Ioi 1)) := fun z =>
    (hE.mul (Complex.measurable_ofReal.pow_const (-z - 1))).aestronglyMeasurable
  have hmeasF' : AEStronglyMeasurable
      (fun t : ℝ => E t * (-(Real.log t : ℂ) * (t : ℂ) ^ (-s - 1)))
      (volume.restrict (Ioi 1)) :=
    (hE.mul (((Complex.measurable_ofReal.comp Real.measurable_log).neg).mul
      (Complex.measurable_ofReal.pow_const (-s - 1)))).aestronglyMeasurable
  have hint := integrableOn_mellin_of_rpow_bound hE hbd hs
  have hdom_int : Integrable (fun t : ℝ => C * e⁻¹ * t ^ (-1 - δ / 2))
      (volume.restrict (Ioi 1)) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : -1 - δ / 2 < -1) zero_lt_one).const_mul _
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z t => E t * (t : ℂ) ^ (-z - 1))
    (F' := fun z t => E t * (-(Real.log t : ℂ) * (t : ℂ) ^ (-z - 1)))
    (Metric.ball_mem_nhds s hδ0)
    (Eventually.of_forall hmeasF) hint hmeasF' ?_ hdom_int ?_).2
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht z hz => ?_)
    have ht1 : (1 : ℝ) < t := ht
    have ht0 : (0 : ℝ) < t := zero_lt_one.trans ht1
    have hzr : θ + δ ≤ z.re := hre z hz
    have hlog : Real.log t ≤ e⁻¹ * t ^ e := by
      have := Real.log_le_rpow_div ht0.le he0
      linarith [show t ^ e / e = e⁻¹ * t ^ e by ring]
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_real,
      Real.norm_of_nonneg (Real.log_nonneg ht1.le),
      Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    have hre_z : (-z - 1).re = -z.re - 1 := by simp
    rw [hre_z]
    have hz_pow : t ^ (-z.re - 1) ≤ t ^ (-(θ + δ) - 1) :=
      Real.rpow_le_rpow_of_exponent_le ht1.le (by linarith)
    have hcomb : t ^ θ * (t ^ e * t ^ (-(θ + δ) - 1)) = t ^ (-1 - δ / 2) := by
      rw [← Real.rpow_add ht0, ← Real.rpow_add ht0]
      congr 1; linarith
    calc ‖E t‖ * (Real.log t * t ^ (-z.re - 1))
        ≤ (C * t ^ θ) * ((e⁻¹ * t ^ e) * t ^ (-(θ + δ) - 1)) := by
          refine mul_le_mul (hbd t ht1.le) ?_ (mul_nonneg (Real.log_nonneg ht1.le) (Real.rpow_nonneg ht0.le _))
            (mul_nonneg hC (Real.rpow_nonneg ht0.le _))
          exact mul_le_mul hlog hz_pow (Real.rpow_nonneg ht0.le _) (by positivity)
      _ = C * e⁻¹ * (t ^ θ * (t ^ e * t ^ (-(θ + δ) - 1))) := by ring
      _ = C * e⁻¹ * t ^ (-1 - δ / 2) := by rw [hcomb]
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht z _ => ?_)
    have ht0 : (0 : ℝ) < t := zero_lt_one.trans ht
    have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
    have hfun : (fun w : ℂ => E t * (t : ℂ) ^ (-w - 1)) =
        fun w : ℂ => E t * cexp ((Real.log t : ℂ) * (-w - 1)) := by
      funext w
      rw [Complex.cpow_def_of_ne_zero htC, Complex.ofReal_log ht0.le]
    rw [hfun]
    have h1 : HasDerivAt (fun w : ℂ => (Real.log t : ℂ) * (-w - 1)) (-(Real.log t : ℂ)) z := by
      have h0 : HasDerivAt (fun w : ℂ => -w - 1) (-1 : ℂ) z := by
        simpa using (hasDerivAt_id' z).neg.sub_const (1 : ℂ)
      simpa using h0.const_mul (Real.log t : ℂ)
    refine (h1.cexp.const_mul (E t)).congr_deriv ?_
    rw [Complex.cpow_def_of_ne_zero htC, Complex.ofReal_log ht0.le]
    ring

theorem analyticOnNhd_mellin_of_rpow_bound {E : ℝ → ℂ} (hE : Measurable E) {C θ : ℝ} (hC : 0 ≤ C)
    (hbd : ∀ t : ℝ, 1 ≤ t → ‖E t‖ ≤ C * t ^ θ) :
    AnalyticOnNhd ℂ (fun s : ℂ => 1 + s * ∫ t in Ioi (1 : ℝ), E t * (t : ℂ) ^ (-s - 1))
      {s : ℂ | θ < s.re} := by
  have hopen : IsOpen {s : ℂ | θ < s.re} := isOpen_lt continuous_const Complex.continuous_re
  refine DifferentiableOn.analyticOnNhd (fun s hs => ?_) hopen
  have hd := hasDerivAt_mellin_of_rpow_bound hE hC hbd hs
  exact (differentiableAt_const (1 : ℂ)).add
    (differentiableAt_id.mul hd.differentiableAt) |>.differentiableWithinAt

theorem LSeries_eq_mul_mellin_stepSum {a : ℕ → ℂ} {C θ : ℝ}
    (hbd : ∀ t : ℝ, 1 ≤ t → ‖stepSum a t‖ ≤ C * t ^ θ) {s : ℂ} (hs : θ < s.re)
    (hsum : LSeriesSummable a s) :
    LSeries a s = s * ∫ t in Ioi (1 : ℝ), stepSum a t * (t : ℂ) ^ (-s - 1) := by
  
  have hLHS : Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-s)) atTop
      (𝓝 (LSeries a s)) := by
    have h1 := hsum.hasSum.tendsto_sum_nat
    have h2 : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range (N + 1), LSeries.term a s n) atTop
        (𝓝 (LSeries a s)) :=
      h1.comp (tendsto_add_atTop_nat 1)
    refine h2.congr fun N => ?_
    have hset : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
      ext n; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
    rw [hset, Finset.sum_insert (by simp : (0 : ℕ) ∉ Finset.Icc 1 N), LSeries.term_zero, zero_add]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 : n ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp hn).1
    rw [LSeries.term_of_ne_zero hn0, Complex.cpow_neg, div_eq_mul_inv]
  
  have hBdry : Tendsto (fun N : ℕ => stepSum a (N : ℝ) * (N : ℂ) ^ (-s)) atTop (𝓝 0) := by
    have hpow : Tendsto (fun N : ℕ => C * ((N : ℝ) ^ (-(s.re - θ)))) atTop (𝓝 0) := by
      have h := ((tendsto_rpow_neg_atTop (sub_pos.mpr hs)).comp
        tendsto_natCast_atTop_atTop).const_mul C
      simpa using h
    refine squeeze_zero_norm' ?_ hpow
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := Nat.one_le_cast.mpr hN
    have hN0 : (0 : ℝ) < (N : ℝ) := zero_lt_one.trans_le hN1
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hN, neg_re]
    calc ‖stepSum a (N : ℝ)‖ * (N : ℝ) ^ (-s.re)
        ≤ (C * (N : ℝ) ^ θ) * (N : ℝ) ^ (-s.re) :=
          mul_le_mul_of_nonneg_right (hbd (N : ℝ) hN1) (Real.rpow_nonneg hN0.le _)
      _ = C * ((N : ℝ) ^ θ * (N : ℝ) ^ (-s.re)) := by ring
      _ = C * (N : ℝ) ^ (-(s.re - θ)) := by
          rw [← Real.rpow_add hN0]; congr 2; ring
  
  have hint := integrableOn_mellin_of_rpow_bound (measurable_stepSum a) hbd hs
  have hInt : Tendsto (fun N : ℕ => ∫ t in (1 : ℝ)..(N : ℝ), stepSum a t * (t : ℂ) ^ (-s - 1))
      atTop (𝓝 (∫ t in Ioi (1 : ℝ), stepSum a t * (t : ℂ) ^ (-s - 1))) :=
    (intervalIntegral_tendsto_integral_Ioi 1 hint tendsto_id).comp tendsto_natCast_atTop_atTop
  have hRHS : Tendsto (fun N : ℕ =>
      stepSum a (N : ℝ) * (N : ℂ) ^ (-s) +
        s * ∫ t in (1 : ℝ)..(N : ℝ), stepSum a t * (t : ℂ) ^ (-s - 1))
      atTop (𝓝 (0 + s * ∫ t in Ioi (1 : ℝ), stepSum a t * (t : ℂ) ^ (-s - 1))) :=
    hBdry.add (hInt.const_mul s)
  have hEq : (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-s)) =ᶠ[atTop]
      (fun N : ℕ => stepSum a (N : ℝ) * (N : ℂ) ^ (-s) +
        s * ∫ t in (1 : ℝ)..(N : ℝ), stepSum a t * (t : ℂ) ^ (-s - 1)) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have h := abel_summation_dirichlet a (Nat.one_le_cast.mpr hN) s
    simpa [Nat.floor_natCast] using h
  simpa using tendsto_nhds_unique (hLHS.congr' hEq) hRHS

theorem LSeries_sub_pole_eq_mellin_error {a : ℕ → ℂ} {C : ℝ}
    (hbd : ∀ t : ℝ, 1 ≤ t → ‖stepSum a t‖ ≤ C * t) {s : ℂ} (hs : 1 < s.re)
    (hsum : LSeriesSummable a s) :
    LSeries a s - 1 / (s - 1) =
      1 + s * ∫ t in Ioi (1 : ℝ), (stepSum a t - (t : ℂ)) * (t : ℂ) ^ (-s - 1) := by
  have hs1 : s - 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have ha_pow : (-s).re < -1 := by simp; linarith
  have hlin_int : IntegrableOn (fun t : ℝ => (t : ℂ) * (t : ℂ) ^ (-s - 1)) (Ioi (1 : ℝ)) := by
    refine (integrableOn_Ioi_cpow_of_lt ha_pow zero_lt_one).congr_fun (fun t ht => ?_)
      measurableSet_Ioi
    have htC : (t : ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans ht).ne'
    dsimp only
    rw [Complex.cpow_sub _ _ htC, Complex.cpow_one]; field_simp
  have hlin_val : ∫ t in Ioi (1 : ℝ), (t : ℂ) * (t : ℂ) ^ (-s - 1) = 1 / (s - 1) := by
    have hcongr : EqOn (fun t : ℝ => (t : ℂ) * (t : ℂ) ^ (-s - 1))
        (fun t : ℝ => (t : ℂ) ^ (-s)) (Ioi (1 : ℝ)) := fun t ht => by
      have htC : (t : ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans ht).ne'
      dsimp only
      rw [Complex.cpow_sub _ _ htC, Complex.cpow_one]; field_simp
    rw [setIntegral_congr_fun measurableSet_Ioi hcongr,
      integral_Ioi_cpow_of_lt ha_pow zero_lt_one, Complex.ofReal_one, Complex.one_cpow]
    have h1s : -s + 1 = -(s - 1) := by ring
    rw [h1s]; field_simp
  have hstep_int : IntegrableOn (fun t : ℝ => stepSum a t * (t : ℂ) ^ (-s - 1)) (Ioi (1 : ℝ)) :=
    integrableOn_mellin_of_rpow_bound (measurable_stepSum a)
      (fun t ht => by simpa [Real.rpow_one] using hbd t ht) hs
  have hL := LSeries_eq_mul_mellin_stepSum
    (fun t ht => by simpa [Real.rpow_one] using hbd t ht) hs hsum
  have hsub_eq : ∫ t in Ioi (1 : ℝ), (stepSum a t - (t : ℂ)) * (t : ℂ) ^ (-s - 1) =
      (∫ t in Ioi (1 : ℝ), stepSum a t * (t : ℂ) ^ (-s - 1)) - 1 / (s - 1) := by
    have hpt : (fun t : ℝ => (stepSum a t - (t : ℂ)) * (t : ℂ) ^ (-s - 1)) =
        fun t : ℝ => stepSum a t * (t : ℂ) ^ (-s - 1) - (t : ℂ) * (t : ℂ) ^ (-s - 1) := by
      funext t; ring
    rw [hpt, integral_sub hstep_int hlin_int, hlin_val]
  rw [hL, hsub_eq]
  field_simp
  ring

end RHDirect.Stage3RealAnalyticLandau
end

noncomputable section

open Complex DirichletCharacter Finset RHDirect

open scoped ArithmeticFunction.vonMangoldt

namespace RHDirect.Stage3ZeroFreeRegion

def negLogDerivZeta (s : ℂ) : ℂ :=
  -deriv riemannZeta s / riemannZeta s

def negLogDerivL {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  -deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s

def IsRealChar {q : ℕ} (χ : DirichletCharacter ℂ q) : Prop :=
  ∀ a : ZMod q, (χ a).im = 0

def prodChar {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂) :
    DirichletCharacter ℂ (q₁ * q₂) :=
  DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁ *
    DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂

theorem four_char_real_nonneg {a b : ℝ} (ha : -1 ≤ a) (hb : -1 ≤ b) :
    0 ≤ 1 + a + b + a * b := by
  have h : 1 + a + b + a * b = (1 + a) * (1 + b) := by ring
  rw [h]
  exact mul_nonneg (by linarith) (by linarith)

theorem isRealChar_inv_eq_self {q : ℕ} {χ : DirichletCharacter ℂ q} (hχ : IsRealChar χ) :
    χ⁻¹ = χ := by
  ext a
  have hstar : starRingEnd ℂ (χ a) = χ⁻¹ a := by
    simpa [RCLike.star_def] using MulChar.star_apply' χ a
  rw [← hstar]
  apply Complex.ext
  · simp
  · simp [hχ a]

theorem isRealChar_sq_eq_one {q : ℕ} {χ : DirichletCharacter ℂ q} (hχ : IsRealChar χ) :
    χ ^ 2 = 1 := by
  calc χ ^ 2 = χ⁻¹ * χ := by rw [sq, isRealChar_inv_eq_self hχ]
    _ = 1 := inv_mul_cancel χ

theorem isRealChar_apply_re_bounds {q : ℕ} {χ : DirichletCharacter ℂ q} (a : ZMod q) :
    -1 ≤ (χ a).re ∧ (χ a).re ≤ 1 := by
  have h1 : |(χ a).re| ≤ 1 := (Complex.abs_re_le_norm (χ a)).trans (χ.norm_le_one a)
  exact abs_le.mp h1

theorem isRealChar_of_sq_eq_one {q : ℕ} {χ : DirichletCharacter ℂ q} (hsq : χ ^ 2 = 1) :
    IsRealChar χ := by
  intro a
  have hinv : χ⁻¹ = χ := by
    have h1 : χ⁻¹ * (χ * χ) = χ⁻¹ * 1 := congrArg (χ⁻¹ * ·) (by simpa [sq] using hsq)
    simpa [mul_assoc] using h1.symm
  have hstar : starRingEnd ℂ (χ a) = χ a := by
    have h1 : starRingEnd ℂ (χ a) = χ⁻¹ a := by
      simpa [RCLike.star_def] using MulChar.star_apply' χ a
    rw [h1, hinv]
  have him := congrArg Complex.im hstar
  simp only [Complex.conj_im] at him
  linarith

theorem prodChar_apply_nat {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂) (n : ℕ) :
    prodChar χ₁ χ₂ (n : ZMod (q₁ * q₂)) = χ₁ (n : ZMod q₁) * χ₂ (n : ZMod q₂) := by
  unfold prodChar
  rw [MulChar.mul_apply]
  by_cases hcop : Nat.Coprime n (q₁ * q₂)
  · have hcop1 : Nat.Coprime n q₁ := hcop.coprime_mul_right_right
    have hcop2 : Nat.Coprime n q₂ := hcop.coprime_mul_left_right
    have hu : IsUnit (n : ZMod (q₁ * q₂)) := (ZMod.isUnit_iff_coprime n (q₁ * q₂)).mpr hcop
    have h1 : DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁ (n : ZMod (q₁ * q₂)) =
        χ₁ (n : ZMod q₁) := by
      obtain ⟨u, hu_eq⟩ := hu
      rw [← hu_eq, DirichletCharacter.changeLevel_eq_cast_of_dvd χ₁ (dvd_mul_right q₁ q₂) u,
        hu_eq, ZMod.cast_natCast (dvd_mul_right q₁ q₂)]
    have h2 : DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂ (n : ZMod (q₁ * q₂)) =
        χ₂ (n : ZMod q₂) := by
      obtain ⟨u, hu_eq⟩ := hu
      rw [← hu_eq, DirichletCharacter.changeLevel_eq_cast_of_dvd χ₂ (dvd_mul_left q₂ q₁) u,
        hu_eq, ZMod.cast_natCast (dvd_mul_left q₂ q₁)]
    rw [h1, h2]
  · have hnu : ¬ IsUnit (n : ZMod (q₁ * q₂)) :=
      fun hu => hcop ((ZMod.isUnit_iff_coprime n (q₁ * q₂)).mp hu)
    rw [MulChar.map_nonunit _ hnu, MulChar.map_nonunit _ hnu, zero_mul]
    by_cases h1 : Nat.Coprime n q₁
    · have h2 : ¬ Nat.Coprime n q₂ := fun h2 => hcop (h1.mul_right h2)
      have hnu2 : ¬ IsUnit (n : ZMod q₂) := fun hu => h2 ((ZMod.isUnit_iff_coprime n q₂).mp hu)
      rw [MulChar.map_nonunit _ hnu2, mul_zero]
    · have hnu1 : ¬ IsUnit (n : ZMod q₁) := fun hu => h1 ((ZMod.isUnit_iff_coprime n q₁).mp hu)
      rw [MulChar.map_nonunit _ hnu1, zero_mul]

private lemma pchar_of_changeLevel {d N : ℕ} [NeZero d] [NeZero N] (hd : d ∣ N)
    (χ : DirichletCharacter ℂ d) (hprim : χ.IsPrimitive) :
    PChar.of (DirichletCharacter.changeLevel hd χ) = PChar.mk d χ hprim := by
  set η : DirichletCharacter ℂ N := DirichletCharacter.changeLevel hd χ
  have hcond : η.conductor = d := (DirichletCharacter.conductor_changeLevel χ hd).trans hprim
  have : NeZero η.conductor := ⟨η.conductor_ne_zero⟩
  have aux : ∀ (e : ℕ) [NeZero e] (φ : DirichletCharacter ℂ e) (he : e ∣ N) (hed : e = d)
      (hφ : DirichletCharacter.changeLevel he φ = DirichletCharacter.changeLevel hd χ)
      (hp : φ.IsPrimitive), PChar.mk e φ hp = PChar.mk d χ hprim := by
    intro e _ φ he hed hφ hp
    subst hed
    have hq : φ = χ := DirichletCharacter.changeLevel_injective hd hφ
    subst hq
    rfl
  exact aux η.conductor η.primitiveCharacter η.conductor_dvd_level hcond
    η.changeLevel_primitiveCharacter η.primitiveCharacter_isPrimitive

theorem prodChar_ne_one_of_distinct_primitive_real {ψ₁ ψ₂ : PChar}
    (h1 : ψ₁.IsReal) (hne : ψ₁ ≠ ψ₂) :
    prodChar ψ₁.χ ψ₂.χ ≠ 1 := by
  intro hprod
  unfold prodChar at hprod
  have hsq1 : DirichletCharacter.changeLevel (dvd_mul_right ψ₁.N ψ₂.N) ψ₁.χ *
      DirichletCharacter.changeLevel (dvd_mul_right ψ₁.N ψ₂.N) ψ₁.χ = 1 := by
    rw [← map_mul, ← sq, isRealChar_sq_eq_one h1, map_one]
  have heq :
      DirichletCharacter.changeLevel (dvd_mul_left ψ₂.N ψ₁.N) ψ₂.χ =
        DirichletCharacter.changeLevel (dvd_mul_right ψ₁.N ψ₂.N) ψ₁.χ := by
    calc DirichletCharacter.changeLevel (dvd_mul_left ψ₂.N ψ₁.N) ψ₂.χ
        = 1 * DirichletCharacter.changeLevel (dvd_mul_left ψ₂.N ψ₁.N) ψ₂.χ := (one_mul _).symm
      _ = (DirichletCharacter.changeLevel (dvd_mul_right ψ₁.N ψ₂.N) ψ₁.χ *
            DirichletCharacter.changeLevel (dvd_mul_right ψ₁.N ψ₂.N) ψ₁.χ) *
            DirichletCharacter.changeLevel (dvd_mul_left ψ₂.N ψ₁.N) ψ₂.χ := by rw [hsq1]
      _ = DirichletCharacter.changeLevel (dvd_mul_right ψ₁.N ψ₂.N) ψ₁.χ *
            (DirichletCharacter.changeLevel (dvd_mul_right ψ₁.N ψ₂.N) ψ₁.χ *
              DirichletCharacter.changeLevel (dvd_mul_left ψ₂.N ψ₁.N) ψ₂.χ) := mul_assoc _ _ _
      _ = DirichletCharacter.changeLevel (dvd_mul_right ψ₁.N ψ₂.N) ψ₁.χ * 1 := by rw [hprod]
      _ = DirichletCharacter.changeLevel (dvd_mul_right ψ₁.N ψ₂.N) ψ₁.χ := mul_one _
  have hof := congrArg PChar.of heq
  rw [pchar_of_changeLevel (dvd_mul_left ψ₂.N ψ₁.N) ψ₂.χ ψ₂.prim,
      pchar_of_changeLevel (dvd_mul_right ψ₁.N ψ₂.N) ψ₁.χ ψ₁.prim] at hof
  exact hne hof.symm

theorem negLogDerivZeta_eq_LSeries {s : ℂ} (hs : 1 < s.re) :
    negLogDerivZeta s = LSeries (fun n => (Λ n : ℂ)) s :=
  (RHDirect.LSeries_vonMangoldt_eq_neg_deriv_zeta_div hs).symm

theorem negLogDerivL_eq_LSeries {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    negLogDerivL χ s = LSeries (fun n => χ n * (Λ n : ℂ)) s :=
  (RHDirect.LSeries_twist_vonMangoldt_eq_neg_deriv_LFunction_div χ hs).symm

private lemma real_tsum_nonneg_of_complex {f : ℕ → ℂ} (hf : Summable f)
    (hre : ∀ n, 0 ≤ (f n).re) : 0 ≤ (∑' n, f n).re := by
  have hsum_re : Summable (fun n => (f n).re) := Complex.reCLM.summable hf
  have heq : (∑' n, f n).re = ∑' n, (f n).re := by
    simpa [Complex.reCLM_apply] using Complex.reCLM.map_tsum hf
  rw [heq]
  exact tsum_nonneg hre

theorem four_char_real_negLogDeriv_re_nonneg {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    {χ₁ : DirichletCharacter ℂ q₁} {χ₂ : DirichletCharacter ℂ q₂}
    (h1 : IsRealChar χ₁) (h2 : IsRealChar χ₂) {σ : ℝ} (hσ : 1 < σ) :
    0 ≤ (negLogDerivZeta (σ : ℂ)).re + (negLogDerivL χ₁ (σ : ℂ)).re +
        (negLogDerivL χ₂ (σ : ℂ)).re + (negLogDerivL (prodChar χ₁ χ₂) (σ : ℂ)).re := by
  have hs : 1 < (σ : ℂ).re := by simpa using hσ
  rw [negLogDerivZeta_eq_LSeries hs, negLogDerivL_eq_LSeries χ₁ hs,
      negLogDerivL_eq_LSeries χ₂ hs, negLogDerivL_eq_LSeries (prodChar χ₁ χ₂) hs]
  have hsumZ : LSeriesSummable (fun n => (Λ n : ℂ)) (σ : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have hsum1 : LSeriesSummable (fun n => χ₁ n * (Λ n : ℂ)) (σ : ℂ) :=
    χ₁.LSeriesSummable_twist_vonMangoldt hs
  have hsum2 : LSeriesSummable (fun n => χ₂ n * (Λ n : ℂ)) (σ : ℂ) :=
    χ₂.LSeriesSummable_twist_vonMangoldt hs
  have hsum12 : LSeriesSummable (fun n => (prodChar χ₁ χ₂) n * (Λ n : ℂ)) (σ : ℂ) :=
    (prodChar χ₁ χ₂).LSeriesSummable_twist_vonMangoldt hs
  rw [← Complex.add_re, ← Complex.add_re, ← Complex.add_re]
  unfold LSeries
  have hsumZ1 : Summable (fun n => LSeries.term (fun m => (Λ m : ℂ)) (σ : ℂ) n +
      LSeries.term (fun m => χ₁ m * (Λ m : ℂ)) (σ : ℂ) n) := Summable.add hsumZ hsum1
  have hsumZ12 : Summable (fun n => (LSeries.term (fun m => (Λ m : ℂ)) (σ : ℂ) n +
      LSeries.term (fun m => χ₁ m * (Λ m : ℂ)) (σ : ℂ) n) +
      LSeries.term (fun m => χ₂ m * (Λ m : ℂ)) (σ : ℂ) n) := Summable.add hsumZ1 hsum2
  rw [← Summable.tsum_add hsumZ hsum1, ← Summable.tsum_add hsumZ1 hsum2,
      ← Summable.tsum_add hsumZ12 hsum12]
  refine real_tsum_nonneg_of_complex (Summable.add hsumZ12 hsum12) fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term]
  · simp only [LSeries.term, hn.ne', ↓reduceIte]
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hcpow : ((n : ℂ) ^ (σ : ℂ)) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast, Complex.ofReal_cpow hnR.le]
    rw [hcpow, prodChar_apply_nat]
    have hfac :
        (Λ n : ℂ) / (((n : ℝ) ^ σ : ℝ) : ℂ) +
            χ₁ (n : ZMod q₁) * (Λ n : ℂ) / (((n : ℝ) ^ σ : ℝ) : ℂ) +
            χ₂ (n : ZMod q₂) * (Λ n : ℂ) / (((n : ℝ) ^ σ : ℝ) : ℂ) +
            χ₁ (n : ZMod q₁) * χ₂ (n : ZMod q₂) * (Λ n : ℂ) / (((n : ℝ) ^ σ : ℝ) : ℂ) =
          (((Λ n / (n : ℝ) ^ σ : ℝ) : ℂ)) *
            (1 + χ₁ (n : ZMod q₁) + χ₂ (n : ZMod q₂) + χ₁ (n : ZMod q₁) * χ₂ (n : ZMod q₂)) := by
      push_cast; ring
    rw [hfac, Complex.re_ofReal_mul]
    have hre :
        (1 + χ₁ (n : ZMod q₁) + χ₂ (n : ZMod q₂) + χ₁ (n : ZMod q₁) * χ₂ (n : ZMod q₂)).re =
          1 + (χ₁ (n : ZMod q₁)).re + (χ₂ (n : ZMod q₂)).re +
            (χ₁ (n : ZMod q₁)).re * (χ₂ (n : ZMod q₂)).re := by
      simp [Complex.mul_re, h1 (n : ZMod q₁), h2 (n : ZMod q₂)]
    rw [hre]
    exact mul_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg hnR.le σ))
      (four_char_real_nonneg
        (isRealChar_apply_re_bounds (χ := χ₁) (n : ZMod q₁)).1
        (isRealChar_apply_re_bounds (χ := χ₂) (n : ZMod q₂)).1)

end RHDirect.Stage3ZeroFreeRegion

end

noncomputable section

open Complex MeasureTheory Set Filter Topology

open scoped ArithmeticFunction.vonMangoldt BigOperators

namespace RHDirect.Stage5ZetaZeroFree

theorem borelCaratheodory_sub_center {f : ℂ → ℂ} {z₀ z : ℂ} {M R r : ℝ}
    (hR : 0 < R) (hrR : r < R)
    (hf : DifferentiableOn ℂ f (Metric.ball z₀ R))
    (hre : ∀ w ∈ Metric.ball z₀ R, (f w).re ≤ M)
    (hz : ‖z - z₀‖ ≤ r) :
    ‖f z - f z₀‖ ≤ (2 * r / (R - r)) * (M - (f z₀).re) := by
  have hz_ball : z - z₀ ∈ Metric.ball (0 : ℂ) R := by
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_le_of_lt hz hrR
  have hz₀_mem : z₀ ∈ Metric.ball z₀ R := Metric.mem_ball_self hR
  have hA_nonneg : 0 ≤ M - (f z₀).re := sub_nonneg.mpr (hre z₀ hz₀_mem)
  set g : ℂ → ℂ := fun w => f (z₀ + w) - f z₀
  have hg_diff : DifferentiableOn ℂ g (Metric.ball (0 : ℂ) R) := by
    refine (hf.comp (differentiableOn_const z₀ |>.fun_add differentiableOn_id) ?_).sub
      (differentiableOn_const (f z₀))
    intro w hw
    simpa [Metric.mem_ball, dist_eq_norm] using hw
  have hg0 : g 0 = 0 := by simp [g]
  
  have hε : ∀ ε : ℝ, 0 < ε →
      ‖f z - f z₀‖ ≤ (2 * r / (R - r)) * (M - (f z₀).re + ε) := by
    intro ε hε0
    have hM' : 0 < M - (f z₀).re + ε := by linarith
    have hmaps : Set.MapsTo g (Metric.ball (0 : ℂ) R) {w : ℂ | w.re ≤ M - (f z₀).re + ε} := by
      intro w hw
      have hw' : z₀ + w ∈ Metric.ball z₀ R := by
        rw [Metric.mem_ball, dist_zero_right] at hw
        rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
        exact hw
      show (f (z₀ + w) - f z₀).re ≤ M - (f z₀).re + ε
      rw [Complex.sub_re]
      linarith [hre (z₀ + w) hw']
    have hbc := Complex.borelCaratheodory_zero hM' hg_diff hmaps hR hz_ball hg0
    have hgz : g (z - z₀) = f z - f z₀ := by simp [g]
    rw [hgz] at hbc
    have hmono : 2 * (M - (f z₀).re + ε) * ‖z - z₀‖ / (R - ‖z - z₀‖) ≤
        (2 * r / (R - r)) * (M - (f z₀).re + ε) := by
      have hden1 : 0 < R - ‖z - z₀‖ := by linarith
      have hden2 : 0 < R - r := by linarith
      have h1 : ‖z - z₀‖ / (R - ‖z - z₀‖) ≤ r / (R - r) := by
        rw [div_le_div_iff₀ hden1 hden2]
        nlinarith [norm_nonneg (z - z₀)]
      have h2 := mul_le_mul_of_nonneg_left h1 (by linarith : 0 ≤ 2 * (M - (f z₀).re + ε))
      linarith [show 2 * (M - (f z₀).re + ε) * (‖z - z₀‖ / (R - ‖z - z₀‖)) =
          2 * (M - (f z₀).re + ε) * ‖z - z₀‖ / (R - ‖z - z₀‖) by ring,
        show 2 * (M - (f z₀).re + ε) * (r / (R - r)) =
          (2 * r / (R - r)) * (M - (f z₀).re + ε) by ring]
    exact hbc.trans hmono
  
  by_contra hlt
  push Not at hlt
  set gap : ℝ := ‖f z - f z₀‖ - (2 * r / (R - r)) * (M - (f z₀).re)
  have hgap : 0 < gap := sub_pos.mpr hlt
  have hr_nonneg : 0 ≤ r := le_trans (norm_nonneg (z - z₀)) hz
  have hcoeff_nonneg : 0 ≤ 2 * r / (R - r) := div_nonneg (by linarith) (by linarith)
  set ε : ℝ := gap / (2 * (2 * r / (R - r) + 1))
  have hε0 : 0 < ε := by positivity
  have hbd := hε ε hε0
  have hmul : (2 * r / (R - r)) * ε ≤ gap / 2 := by
    dsimp only [ε]
    have hden : 0 < 2 * (2 * r / (R - r) + 1) := by positivity
    rw [mul_div_assoc', div_le_div_iff₀ hden two_pos]
    nlinarith
  linarith [show (2 * r / (R - r)) * (M - (f z₀).re + ε) =
      (2 * r / (R - r)) * (M - (f z₀).re) + (2 * r / (R - r)) * ε by ring]

theorem borelCaratheodory_deriv_at_center {f : ℂ → ℂ} {z₀ : ℂ} {M R : ℝ}
    (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (Metric.ball z₀ R))
    (hre : ∀ w ∈ Metric.ball z₀ R, (f w).re ≤ M) :
    ‖deriv f z₀‖ ≤ (2 / R) * (M - (f z₀).re) := by
  have hd : HasDerivAt f (deriv f z₀) z₀ :=
    (hf.differentiableAt (Metric.ball_mem_nhds z₀ hR)).hasDerivAt
  have hlim : Tendsto (fun t : ℝ => ‖(f (z₀ + (t : ℂ)) - f z₀) / (t : ℂ)‖)
      (𝓝[>] (0 : ℝ)) (𝓝 ‖deriv f z₀‖) := by
    have h1 : Tendsto (fun w : ℂ => (f (z₀ + w) - f z₀) / w) (𝓝[≠] (0 : ℂ)) (𝓝 (deriv f z₀)) := by
      have hs := hd.tendsto_slope_zero
      refine hs.congr' (Eventually.of_forall fun w => ?_)
      simp [div_eq_inv_mul]
    have h2 : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (by simpa using (Complex.continuous_ofReal.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds) ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
    exact (h1.comp h2).norm
  have hlim_rhs : Tendsto (fun t : ℝ => (2 / (R - t)) * (M - (f z₀).re))
      (𝓝[>] (0 : ℝ)) (𝓝 ((2 / R) * (M - (f z₀).re))) := by
    have hcont : ContinuousAt (fun t : ℝ => (2 / (R - t)) * (M - (f z₀).re)) 0 := by
      have hsub : ContinuousAt (fun t : ℝ => R - t) 0 := continuousAt_const.sub continuousAt_id
      have hne : R - (0 : ℝ) ≠ 0 := by simpa using hR.ne'
      exact ((continuousAt_const.div hsub hne).mul continuousAt_const)
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  refine le_of_tendsto_of_tendsto hlim hlim_rhs ?_
  filter_upwards [Ioo_mem_nhdsGT hR] with t ht
  have ht0 : 0 < t := ht.1
  have htR : t < R := ht.2
  have hbc := borelCaratheodory_sub_center hR htR hf hre
    (z := z₀ + (t : ℂ)) (r := t) (by simp [Real.norm_of_nonneg ht0.le])
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg ht0.le, div_le_iff₀ ht0]
  have hmul : (2 / (R - t)) * (M - (f z₀).re) * t = (2 * t / (R - t)) * (M - (f z₀).re) := by
    ring
  linarith

def blaschkeFactor (s₀ : ℂ) (R : ℝ) (ρ z : ℂ) : ℂ :=
  (R : ℂ) * (z - ρ) / ((R : ℂ) ^ 2 - starRingEnd ℂ (ρ - s₀) * (z - s₀))

lemma blaschkeFactor_denom_ne_zero {s₀ ρ z : ℂ} {R : ℝ}
    (hR : 0 < R) (hρ : ‖ρ - s₀‖ < R) (hz : ‖z - s₀‖ ≤ R) :
    (R : ℂ) ^ 2 - starRingEnd ℂ (ρ - s₀) * (z - s₀) ≠ 0 := by
  intro h0
  have heq : (R : ℂ) ^ 2 = starRingEnd ℂ (ρ - s₀) * (z - s₀) := sub_eq_zero.mp h0
  have hn := congrArg norm heq
  rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hR.le, norm_mul, Complex.norm_conj] at hn
  have hlt : ‖ρ - s₀‖ * ‖z - s₀‖ < R ^ 2 := by nlinarith [norm_nonneg (ρ - s₀), norm_nonneg (z - s₀)]
  linarith

theorem blaschkeFactor_norm_eq_one_on_sphere {s₀ ρ z : ℂ} {R : ℝ}
    (hR : 0 < R) (hρ : ‖ρ - s₀‖ < R) (hz : z ∈ Metric.sphere s₀ R) :
    ‖blaschkeFactor s₀ R ρ z‖ = 1 := by
  rw [Metric.mem_sphere, dist_eq_norm] at hz
  have hden := blaschkeFactor_denom_ne_zero hR hρ hz.le
  unfold blaschkeFactor
  rw [norm_div, div_eq_one_iff_eq (norm_ne_zero_iff.mpr hden)]
  
  have hsq : ‖(R : ℂ) * (z - ρ)‖ ^ 2 = ‖(R : ℂ) ^ 2 - starRingEnd ℂ (ρ - s₀) * (z - s₀)‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    set a : ℂ := ρ - s₀
    set w : ℂ := z - s₀
    have hzr : z - ρ = w - a := by simp [a, w]
    have hw_sq : Complex.normSq w = R ^ 2 := by
      rw [Complex.normSq_eq_norm_sq, hz]
    rw [hzr, map_mul, Complex.normSq_ofReal]
    have h1 : Complex.normSq (w - a) = Complex.normSq w - 2 * (w * starRingEnd ℂ a).re + Complex.normSq a := by
      rw [Complex.normSq_sub, Complex.normSq_apply, Complex.normSq_apply]
      simp [Complex.mul_re]; ring
    have h2 : Complex.normSq ((R : ℂ) ^ 2 - starRingEnd ℂ a * w) =
        R ^ 4 - 2 * R ^ 2 * (w * starRingEnd ℂ a).re + Complex.normSq a * Complex.normSq w := by
      rw [Complex.normSq_sub, map_pow, Complex.normSq_ofReal, map_mul, Complex.normSq_conj]
      have hre : ((R : ℂ) ^ 2 * starRingEnd ℂ (starRingEnd ℂ a * w)).re =
          R ^ 2 * (w * starRingEnd ℂ a).re := by
        rw [map_mul, Complex.conj_conj]
        have hR2 : ((R : ℂ) ^ 2) = ((R ^ 2 : ℝ) : ℂ) := by push_cast; rfl
        rw [hR2, Complex.re_ofReal_mul]
        have hconj : (a * starRingEnd ℂ w).re = (w * starRingEnd ℂ a).re := by
          have := Complex.conj_re (a * starRingEnd ℂ w)
          rw [map_mul, Complex.conj_conj, mul_comm] at this
          exact this.symm
        rw [hconj]
      rw [hre]; ring
    rw [h1, h2, hw_sq]; ring
  nlinarith [norm_nonneg ((R : ℂ) * (z - ρ)),
    norm_nonneg ((R : ℂ) ^ 2 - starRingEnd ℂ (ρ - s₀) * (z - s₀))]

theorem blaschkeFactor_eval_center {s₀ ρ : ℂ} {R : ℝ} (hR : 0 < R) :
    blaschkeFactor s₀ R ρ s₀ = -(ρ - s₀) / (R : ℂ) := by
  unfold blaschkeFactor
  have hRne : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  simp only [sub_self, mul_zero, sub_zero]
  field_simp [hRne]
  ring

theorem blaschkeFactor_norm_center {s₀ ρ : ℂ} {R : ℝ} (hR : 0 < R) :
    ‖blaschkeFactor s₀ R ρ s₀‖ = ‖ρ - s₀‖ / R := by
  rw [blaschkeFactor_eval_center hR, norm_div, norm_neg, Complex.norm_real,
    Real.norm_of_nonneg hR.le]

theorem blaschkeFactor_hasDerivAt_center {s₀ ρ : ℂ} {R : ℝ} (hR : 0 < R) :
    HasDerivAt (blaschkeFactor s₀ R ρ)
      (1 / (R : ℂ) - (ρ - s₀) * starRingEnd ℂ (ρ - s₀) / (R : ℂ) ^ 3) s₀ := by
  have hRne : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  have hnum : HasDerivAt (fun z : ℂ => (R : ℂ) * (z - ρ)) (R : ℂ) s₀ := by
    simpa using ((hasDerivAt_id s₀).sub_const ρ).const_mul (R : ℂ)
  have hden : HasDerivAt (fun z : ℂ => (R : ℂ) ^ 2 - starRingEnd ℂ (ρ - s₀) * (z - s₀))
      (-(starRingEnd ℂ (ρ - s₀))) s₀ := by
    have h1 := ((hasDerivAt_id s₀).sub_const s₀).const_mul (starRingEnd ℂ (ρ - s₀))
    simpa using (hasDerivAt_const s₀ ((R : ℂ) ^ 2)).fun_sub h1
  have hden_ne : (R : ℂ) ^ 2 - starRingEnd ℂ (ρ - s₀) * (s₀ - s₀) ≠ 0 := by
    simp [pow_ne_zero 2 hRne]
  refine (hnum.div hden hden_ne).congr_deriv ?_
  simp only [sub_self, mul_zero, sub_zero]
  field_simp [hRne]
  ring

theorem blaschkeFactor_logDeriv_center {s₀ ρ : ℂ} {R : ℝ} (hR : 0 < R) (hne : ρ ≠ s₀) :
    deriv (blaschkeFactor s₀ R ρ) s₀ / blaschkeFactor s₀ R ρ s₀ =
      1 / (s₀ - ρ) - starRingEnd ℂ (s₀ - ρ) / (R : ℂ) ^ 2 := by
  rw [(blaschkeFactor_hasDerivAt_center hR).deriv, blaschkeFactor_eval_center hR]
  have hRne : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  have hsub : s₀ - ρ ≠ 0 := sub_ne_zero.mpr hne.symm
  have hsub' : ρ - s₀ ≠ 0 := sub_ne_zero.mpr hne
  have hneg : starRingEnd ℂ (ρ - s₀) = -starRingEnd ℂ (s₀ - ρ) := by
    rw [← map_neg]; congr 1; ring
  rw [hneg]
  field_simp [hRne, hsub, hsub']
  ring

theorem blaschkeFactor_logDeriv_center_re {s₀ ρ : ℂ} {R : ℝ} (hR : 0 < R) (hne : ρ ≠ s₀) :
    (deriv (blaschkeFactor s₀ R ρ) s₀ / blaschkeFactor s₀ R ρ s₀).re =
      (s₀ - ρ).re * (1 / ‖s₀ - ρ‖ ^ 2 - 1 / R ^ 2) := by
  rw [blaschkeFactor_logDeriv_center hR hne, Complex.sub_re, one_div, Complex.inv_re,
    Complex.normSq_eq_norm_sq]
  have hR2 : ((R : ℂ) ^ 2) = ((R ^ 2 : ℝ) : ℂ) := by push_cast; rfl
  rw [hR2, Complex.div_ofReal_re, Complex.conj_re]
  ring

lemma blaschkeFactor_logDeriv_center_re_nonneg {s₀ ρ : ℂ} {R : ℝ}
    (hR : 0 < R) (hne : ρ ≠ s₀) (hρR : ‖ρ - s₀‖ < R) (hre : ρ.re ≤ s₀.re) :
    0 ≤ (deriv (blaschkeFactor s₀ R ρ) s₀ / blaschkeFactor s₀ R ρ s₀).re := by
  rw [blaschkeFactor_logDeriv_center_re hR hne]
  have hpos : 0 < ‖s₀ - ρ‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne.symm)
  have hnorm_lt : ‖s₀ - ρ‖ < R := by rwa [norm_sub_rev]
  have h1 : 1 / R ^ 2 ≤ 1 / ‖s₀ - ρ‖ ^ 2 := by
    rw [one_div, one_div]
    exact inv_anti₀ (sq_pos_of_pos hpos) (pow_le_pow_left₀ hpos.le hnorm_lt.le 2)
  exact mul_nonneg (by simp [hre]) (sub_nonneg.mpr h1)

set_option maxHeartbeats 2000000 in
theorem exists_blaschke_factorization {g : ℂ → ℂ} {s₀ : ℂ} {R r M₀ : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hg : AnalyticOnNhd ℂ g (Metric.closedBall s₀ R))
    (hg0 : g s₀ ≠ 0)
    (hM₀ : ∀ z ∈ Metric.sphere s₀ R, ‖g z‖ ≤ M₀) :
    ∃ (L : List ℂ) (h : ℂ → ℂ),
      (∀ ρ ∈ L, ρ ∈ Metric.closedBall s₀ r ∧ ρ ≠ s₀ ∧ g ρ = 0) ∧
      (∀ ρ ∈ Metric.closedBall s₀ r, g ρ = 0 → ρ ∈ L) ∧
      AnalyticOnNhd ℂ h (Metric.closedBall s₀ R) ∧
      (∀ z ∈ Metric.closedBall s₀ r, h z ≠ 0) ∧
      (∀ z ∈ Metric.closedBall s₀ R,
        g z = h z * (L.map (fun ρ => blaschkeFactor s₀ R ρ z)).prod) ∧
      (∀ z ∈ Metric.closedBall s₀ R, ‖h z‖ ≤ M₀) := by
  have hR : 0 < R := lt_trans hr hrR
  set q : ℝ := R / r with hq_def
  have hq1 : 1 < q := (one_lt_div hr).mpr hrR
  have hg0_pos : 0 < ‖g s₀‖ := norm_pos_iff.mpr hg0
  
  obtain ⟨N, hN⟩ : ∃ N : ℕ, M₀ < ‖g s₀‖ * q ^ N := by
    have hev := (tendsto_pow_atTop_atTop_of_one_lt hq1).eventually
      (Filter.eventually_gt_atTop (M₀ / ‖g s₀‖))
    obtain ⟨N, hN⟩ := hev.exists
    exact ⟨N, by have := (div_lt_iff₀ hg0_pos).mp hN; linarith⟩
  have hfr_sub : frontier (Metric.ball s₀ R) ⊆ Metric.sphere s₀ R := by
    intro z hz
    rw [Metric.mem_sphere]
    have hcl : z ∈ Metric.closedBall s₀ R := by
      rw [← closure_ball s₀ hR.ne']
      exact hz.1
    have hnot : z ∉ Metric.ball s₀ R := by
      rw [← interior_eq_iff_isOpen.mpr Metric.isOpen_ball]
      exact hz.2
    rw [Metric.mem_closedBall] at hcl
    rw [Metric.mem_ball, not_lt] at hnot
    exact le_antisymm hcl hnot
  
  have hpeel : ∀ (n : ℕ) (f : ℂ → ℂ),
      AnalyticOnNhd ℂ f (Metric.closedBall s₀ R) →
      f s₀ ≠ 0 →
      (∀ z ∈ Metric.sphere s₀ R, ‖f z‖ ≤ M₀) →
      M₀ < ‖f s₀‖ * q ^ n →
      ∃ (L : List ℂ) (h : ℂ → ℂ),
        (∀ ρ ∈ L, ρ ∈ Metric.closedBall s₀ r ∧ ρ ≠ s₀) ∧
        AnalyticOnNhd ℂ h (Metric.closedBall s₀ R) ∧
        (∀ z ∈ Metric.closedBall s₀ r, h z ≠ 0) ∧
        (∀ z ∈ Metric.closedBall s₀ R,
          f z = h z * (L.map (fun ρ => blaschkeFactor s₀ R ρ z)).prod) ∧
        (∀ z ∈ Metric.closedBall s₀ R, ‖h z‖ ≤ M₀) := by
    intro n
    induction n with
    | zero =>
      intro f hf _ hfM hlt
      simp only [pow_zero, mul_one] at hlt
      
      have hdc : DiffContOnCl ℂ f (Metric.ball s₀ R) := by
        refine ⟨(hf.mono Metric.ball_subset_closedBall).differentiableOn, ?_⟩
        rw [closure_ball s₀ hR.ne']
        exact hf.continuousOn
      have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hdc
        (fun z hz => hfM z (hfr_sub hz))
        (by rw [closure_ball s₀ hR.ne']; exact Metric.mem_closedBall_self hR.le)
      linarith
    | succ k ih =>
      intro f hf hf0 hfM hlt
      by_cases hnz : ∀ z ∈ Metric.closedBall s₀ r, f z ≠ 0
      · 
        have hdc : DiffContOnCl ℂ f (Metric.ball s₀ R) := by
          refine ⟨(hf.mono Metric.ball_subset_closedBall).differentiableOn, ?_⟩
          rw [closure_ball s₀ hR.ne']
          exact hf.continuousOn
        have hmax : ∀ z ∈ Metric.closedBall s₀ R, ‖f z‖ ≤ M₀ := fun z hz =>
          Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hdc
            (fun w hw => hfM w (hfr_sub hw))
            (by rwa [closure_ball s₀ hR.ne'])
        exact ⟨[], f, by simp, hf, hnz, fun z _ => by simp, hmax⟩
      · 
        push Not at hnz
        obtain ⟨ρ, hρ_mem, hρ_zero⟩ := hnz
        have hρ_ne : ρ ≠ s₀ := fun h => hf0 (h ▸ hρ_zero)
        have hρ_norm : ‖ρ - s₀‖ ≤ r := by simpa [Metric.mem_closedBall, dist_eq_norm] using hρ_mem
        have hρ_lt : ‖ρ - s₀‖ < R := lt_of_le_of_lt hρ_norm hrR
        set f₁ : ℂ → ℂ := fun z =>
          (((R : ℂ) ^ 2 - starRingEnd ℂ (ρ - s₀) * (z - s₀)) / (R : ℂ)) * dslope f ρ z
        have hf₁_an : AnalyticOnNhd ℂ f₁ (Metric.closedBall s₀ R) := by
          
          have hopen_ex : ∃ U : Set ℂ, IsOpen U ∧ Metric.closedBall s₀ R ⊆ U ∧
              DifferentiableOn ℂ f U := by
            refine ⟨{z | AnalyticAt ℂ f z}, isOpen_analyticAt ℂ f, fun z hz => hf z hz,
              fun z hz => hz.differentiableAt.differentiableWithinAt⟩
          obtain ⟨U, hU_open, hU_sub, hfU⟩ := hopen_ex
          have hρU : U ∈ 𝓝 ρ :=
            hU_open.mem_nhds (hU_sub (Metric.closedBall_subset_closedBall hrR.le hρ_mem))
          have hdsU : DifferentiableOn ℂ (dslope f ρ) U :=
            (Complex.differentiableOn_dslope hρU).mpr hfU
          have hds_an : AnalyticOnNhd ℂ (dslope f ρ) (Metric.closedBall s₀ R) :=
            (hdsU.analyticOnNhd hU_open).mono hU_sub
          have hlin_an : AnalyticOnNhd ℂ
              (fun z : ℂ => ((R : ℂ) ^ 2 - starRingEnd ℂ (ρ - s₀) * (z - s₀)) / (R : ℂ))
              (Metric.closedBall s₀ R) := by
            refine (((analyticOnNhd_const.sub
              (analyticOnNhd_const.mul (analyticOnNhd_id.sub analyticOnNhd_const))).div
              analyticOnNhd_const) fun z _ => Complex.ofReal_ne_zero.mpr hR.ne')
          exact hlin_an.mul hds_an
        have hfac : ∀ z ∈ Metric.closedBall s₀ R, f z = f₁ z * blaschkeFactor s₀ R ρ z := by
          intro z hz
          have hRne : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
          have hden := blaschkeFactor_denom_ne_zero hR hρ_lt
            (by simpa [Metric.mem_closedBall, dist_eq_norm] using hz)
          have hds_eq : (z - ρ) * dslope f ρ z = f z := by
            have := sub_smul_dslope f ρ z
            rw [hρ_zero, sub_zero, smul_eq_mul] at this
            exact this
          dsimp only [f₁, blaschkeFactor]
          calc f z = (z - ρ) * dslope f ρ z := hds_eq.symm
            _ = (((R : ℂ) ^ 2 - starRingEnd ℂ (ρ - s₀) * (z - s₀)) / (R : ℂ) * dslope f ρ z) *
                ((R : ℂ) * (z - ρ) / ((R : ℂ) ^ 2 - starRingEnd ℂ (ρ - s₀) * (z - s₀))) := by
                field_simp [hRne, hden]
        have hf₁0 : f₁ s₀ ≠ 0 := by
          intro h0
          have := hfac s₀ (Metric.mem_closedBall_self hR.le)
          rw [h0, zero_mul] at this
          exact hf0 this
        have hf₁M : ∀ z ∈ Metric.sphere s₀ R, ‖f₁ z‖ ≤ M₀ := by
          intro z hz
          have h1 := congrArg norm (hfac z (Metric.sphere_subset_closedBall hz))
          rw [norm_mul, blaschkeFactor_norm_eq_one_on_sphere hR hρ_lt hz, mul_one] at h1
          rw [← h1]
          exact hfM z hz
        have hgrowth : ‖f s₀‖ * q ≤ ‖f₁ s₀‖ := by
          have h1 := congrArg norm (hfac s₀ (Metric.mem_closedBall_self hR.le))
          rw [norm_mul, blaschkeFactor_norm_center hR] at h1
          have hpos_ρ : 0 < ‖ρ - s₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hρ_ne)
          have hle : ‖ρ - s₀‖ / R ≤ r / R := div_le_div_of_nonneg_right hρ_norm hR.le
          have h2 : ‖f s₀‖ ≤ ‖f₁ s₀‖ * (r / R) := by
            rw [h1]
            exact mul_le_mul_of_nonneg_left hle (norm_nonneg _)
          rw [hq_def, mul_div_assoc', div_le_iff₀ hr]
          have h3 := mul_le_mul_of_nonneg_right h2 hR.le
          have h4 : ‖f₁ s₀‖ * (r / R) * R = ‖f₁ s₀‖ * r := by field_simp [hR.ne']
          linarith
        have hlt₁ : M₀ < ‖f₁ s₀‖ * q ^ k := by
          have hq_pow_nonneg : 0 ≤ q ^ k := pow_nonneg (by positivity) k
          calc M₀ < ‖f s₀‖ * q ^ (k + 1) := hlt
            _ = (‖f s₀‖ * q) * q ^ k := by rw [pow_succ']; ring
            _ ≤ ‖f₁ s₀‖ * q ^ k := mul_le_mul_of_nonneg_right hgrowth hq_pow_nonneg
        obtain ⟨L₁, h, hL₁, hh_an, hh_nz, hh_eq, hh_M⟩ := ih f₁ hf₁_an hf₁0 hf₁M hlt₁
        refine ⟨ρ :: L₁, h, ?_, hh_an, hh_nz, ?_, hh_M⟩
        · intro w hw
          rcases List.mem_cons.mp hw with rfl | hw'
          · exact ⟨hρ_mem, hρ_ne⟩
          · exact hL₁ w hw'
        · intro z hz
          rw [hfac z hz, hh_eq z hz, List.map_cons, List.prod_cons]
          ring
  obtain ⟨L, h, hL, hh_an, hh_nz, hh_eq, hh_M⟩ := hpeel N g hg hg0 hM₀ hN
  refine ⟨L, h, ?_, ?_, hh_an, hh_nz, hh_eq, hh_M⟩
  · intro ρ hρ
    obtain ⟨hρ_mem, hρ_ne⟩ := hL ρ hρ
    refine ⟨hρ_mem, hρ_ne, ?_⟩
    rw [hh_eq ρ (Metric.closedBall_subset_closedBall hrR.le hρ_mem)]
    have hzero_fac : blaschkeFactor s₀ R ρ ρ = 0 := by simp [blaschkeFactor]
    have hprod_zero : (L.map (fun w => blaschkeFactor s₀ R w ρ)).prod = 0 :=
      List.prod_eq_zero (List.mem_map.mpr ⟨ρ, hρ, hzero_fac⟩)
    rw [hprod_zero, mul_zero]
  · intro ρ hρ_mem hρ_zero
    have hprod := hh_eq ρ (Metric.closedBall_subset_closedBall hrR.le hρ_mem)
    rw [hρ_zero] at hprod
    have h0 : (L.map (fun w => blaschkeFactor s₀ R w ρ)).prod = 0 :=
      (mul_eq_zero.mp hprod.symm).resolve_left (hh_nz ρ hρ_mem)
    obtain ⟨w, hwL, hBw⟩ := List.mem_map.mp (List.prod_eq_zero_iff.mp h0)
    have hden := blaschkeFactor_denom_ne_zero hR
      (lt_of_le_of_lt (by simpa [Metric.mem_closedBall, dist_eq_norm] using (hL w hwL).1) hrR)
      (by simpa [Metric.mem_closedBall, dist_eq_norm] using
        Metric.closedBall_subset_closedBall hrR.le hρ_mem)
    unfold blaschkeFactor at hBw
    have hnum : (R : ℂ) * (ρ - w) = 0 := (div_eq_zero_iff.mp hBw).resolve_right hden
    have hρw : ρ = w := sub_eq_zero.mp ((mul_eq_zero.mp hnum).resolve_left
      (Complex.ofReal_ne_zero.mpr hR.ne'))
    exact hρw ▸ hwL

set_option maxHeartbeats 2000000 in
theorem hasDerivAt_radial_primitive_ball {H : ℂ → ℂ} {s₀ z : ℂ} {r : ℝ}
    (hH : DifferentiableOn ℂ H (Metric.ball s₀ r)) (hz : z ∈ Metric.ball s₀ r) :
    HasDerivAt (fun w : ℂ => ∫ u in (0 : ℝ)..1, (w - s₀) * H (s₀ + (u : ℂ) * (w - s₀))) (H z) z := by
  have hH_an : AnalyticOnNhd ℂ H (Metric.ball s₀ r) := hH.analyticOnNhd Metric.isOpen_ball
  have hH_cont : ContinuousOn H (Metric.ball s₀ r) := hH_an.continuousOn
  have hH'_an : AnalyticOnNhd ℂ (deriv H) (Metric.ball s₀ r) := fun w hw => (hH_an w hw).deriv
  have hH'_cont : ContinuousOn (deriv H) (Metric.ball s₀ r) := hH'_an.continuousOn
  set δ : ℝ := (r - ‖z - s₀‖) / 2 with hδ_def
  have hδ0 : 0 < δ := by
    rw [Metric.mem_ball, dist_eq_norm] at hz
    linarith
  have hmem_ball : ∀ w ∈ Metric.closedBall z δ, ∀ u ∈ Set.Icc (0 : ℝ) 1,
      s₀ + (u : ℂ) * (w - s₀) ∈ Metric.ball s₀ r := by
    intro w hw u hu
    rw [Metric.mem_closedBall, dist_eq_norm] at hw
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hu.1]
    have hws : ‖w - s₀‖ ≤ ‖z - s₀‖ + δ := by
      have htri := norm_add_le (w - z) (z - s₀)
      rw [sub_add_sub_cancel] at htri
      linarith
    have hlt : ‖z - s₀‖ + δ < r := by
      rw [Metric.mem_ball, dist_eq_norm] at hz; linarith
    calc u * ‖w - s₀‖ ≤ 1 * ‖w - s₀‖ := mul_le_mul_of_nonneg_right hu.2 (norm_nonneg _)
      _ = ‖w - s₀‖ := one_mul _
      _ ≤ ‖z - s₀‖ + δ := hws
      _ < r := hlt
  set Φ : ℂ × ℝ → ℂ := fun p => s₀ + (p.2 : ℂ) * (p.1 - s₀)
  have hΦ_cont : Continuous Φ := by fun_prop
  set K : Set ℂ := Φ '' (Metric.closedBall z δ ×ˢ Set.Icc (0 : ℝ) 1)
  have hK_comp : IsCompact K := ((isCompact_closedBall z δ).prod isCompact_Icc).image hΦ_cont
  have hK_sub : K ⊆ Metric.ball s₀ r := by
    rintro _ ⟨⟨w, u⟩, ⟨hw, hu⟩, rfl⟩
    exact hmem_ball w hw u hu
  obtain ⟨M₁, hM₁⟩ := hK_comp.exists_bound_of_continuousOn (hH_cont.mono hK_sub)
  obtain ⟨M₂, hM₂⟩ := hK_comp.exists_bound_of_continuousOn (hH'_cont.mono hK_sub)
  set B : ℝ := |M₁| + (‖z - s₀‖ + δ) * |M₂|
  have hstep : HasDerivAt
      (fun w : ℂ => ∫ u in (0 : ℝ)..1, (w - s₀) * H (s₀ + (u : ℂ) * (w - s₀)))
      (∫ u in (0 : ℝ)..1,
        (H (s₀ + (u : ℂ) * (z - s₀)) + (z - s₀) * ((u : ℂ) * deriv H (s₀ + (u : ℂ) * (z - s₀))))) z := by
    refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun w u => (w - s₀) * H (s₀ + (u : ℂ) * (w - s₀)))
      (F' := fun w u => H (s₀ + (u : ℂ) * (w - s₀)) +
        (w - s₀) * ((u : ℂ) * deriv H (s₀ + (u : ℂ) * (w - s₀))))
      (bound := fun _ : ℝ => B)
      (Metric.ball_mem_nhds z hδ0) ?_ ?_ ?_ ?_ (intervalIntegrable_const (c := B)) ?_).2
    · filter_upwards [Metric.ball_mem_nhds z hδ0] with w hw
      have hcw : ContinuousOn (fun u : ℝ => (w - s₀) * H (s₀ + (u : ℂ) * (w - s₀))) (Set.uIcc 0 1) := by
        rw [Set.uIcc_of_le zero_le_one]
        refine continuousOn_const.mul (hH_cont.comp ?_ fun u hu =>
          hmem_ball w (Metric.ball_subset_closedBall hw) u hu)
        exact continuousOn_const.add (Complex.continuous_ofReal.continuousOn.mul continuousOn_const)
      exact (hcw.mono Set.uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
    · have hcz : ContinuousOn (fun u : ℝ => (z - s₀) * H (s₀ + (u : ℂ) * (z - s₀))) (Set.uIcc 0 1) := by
        rw [Set.uIcc_of_le zero_le_one]
        refine continuousOn_const.mul (hH_cont.comp ?_ fun u hu =>
          hmem_ball z (Metric.mem_closedBall_self hδ0.le) u hu)
        exact continuousOn_const.add (Complex.continuous_ofReal.continuousOn.mul continuousOn_const)
      exact hcz.intervalIntegrable
    · have hcz' : ContinuousOn (fun u : ℝ =>
          H (s₀ + (u : ℂ) * (z - s₀)) +
            (z - s₀) * ((u : ℂ) * deriv H (s₀ + (u : ℂ) * (z - s₀)))) (Set.uIcc 0 1) := by
        rw [Set.uIcc_of_le zero_le_one]
        have hcomp : ContinuousOn (fun u : ℝ => s₀ + (u : ℂ) * (z - s₀)) (Set.Icc 0 1) :=
          continuousOn_const.add (Complex.continuous_ofReal.continuousOn.mul continuousOn_const)
        exact (hH_cont.comp hcomp fun u hu => hmem_ball z (Metric.mem_closedBall_self hδ0.le) u hu).add
          (continuousOn_const.mul (Complex.continuous_ofReal.continuousOn.mul
            (hH'_cont.comp hcomp fun u hu => hmem_ball z (Metric.mem_closedBall_self hδ0.le) u hu)))
      exact (hcz'.mono Set.uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
    · refine Eventually.of_forall fun u hu w hw => ?_
      rw [Set.uIoc_of_le zero_le_one] at hu
      have hu_cc : u ∈ Set.Icc (0 : ℝ) 1 := ⟨hu.1.le, hu.2⟩
      have hw_cb : w ∈ Metric.closedBall z δ := Metric.ball_subset_closedBall hw
      have hKmem : s₀ + (u : ℂ) * (w - s₀) ∈ K :=
        ⟨(w, u), ⟨hw_cb, hu_cc⟩, rfl⟩
      have h1 : ‖H (s₀ + (u : ℂ) * (w - s₀))‖ ≤ |M₁| :=
        (hM₁ _ hKmem).trans (le_abs_self M₁)
      have h2 : ‖deriv H (s₀ + (u : ℂ) * (w - s₀))‖ ≤ |M₂| :=
        (hM₂ _ hKmem).trans (le_abs_self M₂)
      have hws : ‖w - s₀‖ ≤ ‖z - s₀‖ + δ := by
        have htri := norm_add_le (w - z) (z - s₀)
        rw [sub_add_sub_cancel] at htri
        rw [Metric.mem_closedBall, dist_eq_norm] at hw_cb
        linarith
      have huM2 : u * ‖deriv H (s₀ + (u : ℂ) * (w - s₀))‖ ≤ 1 * |M₂| :=
        mul_le_mul hu_cc.2 h2 (norm_nonneg _) zero_le_one
      calc ‖H (s₀ + (u : ℂ) * (w - s₀)) +
              (w - s₀) * ((u : ℂ) * deriv H (s₀ + (u : ℂ) * (w - s₀)))‖
          ≤ ‖H (s₀ + (u : ℂ) * (w - s₀))‖ +
            ‖w - s₀‖ * (u * ‖deriv H (s₀ + (u : ℂ) * (w - s₀))‖) := by
            refine (norm_add_le _ _).trans ?_
            rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hu_cc.1]
        _ ≤ |M₁| + (‖z - s₀‖ + δ) * (1 * |M₂|) := by
            gcongr
            exact mul_nonneg hu_cc.1 (norm_nonneg _)
        _ = B := by dsimp only [B]; ring
    · refine Eventually.of_forall fun u hu w hw => ?_
      rw [Set.uIoc_of_le zero_le_one] at hu
      have hu_cc : u ∈ Set.Icc (0 : ℝ) 1 := ⟨hu.1.le, hu.2⟩
      have hmem := hmem_ball w (Metric.ball_subset_closedBall hw) u hu_cc
      have hH_at : HasDerivAt H (deriv H (s₀ + (u : ℂ) * (w - s₀))) (s₀ + (u : ℂ) * (w - s₀)) :=
        (hH.differentiableAt (Metric.isOpen_ball.mem_nhds hmem)).hasDerivAt
      have hlin : HasDerivAt (fun x : ℂ => s₀ + (u : ℂ) * (x - s₀)) (u : ℂ) w := by
        simpa using (hasDerivAt_const w s₀).fun_add (((hasDerivAt_id w).sub_const s₀).const_mul (u : ℂ))
      have hcomp := hH_at.comp w hlin
      have hmul := ((hasDerivAt_id w).sub_const s₀).fun_mul hcomp
      refine hmul.congr_deriv ?_
      dsimp [Function.comp]
      ring
  
  have hftc : ∫ u in (0 : ℝ)..1,
      (H (s₀ + (u : ℂ) * (z - s₀)) + (z - s₀) * ((u : ℂ) * deriv H (s₀ + (u : ℂ) * (z - s₀)))) =
      H z := by
    have hderiv_u : ∀ u ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun t : ℝ => (t : ℂ) * H (s₀ + (t : ℂ) * (z - s₀)))
          (H (s₀ + (u : ℂ) * (z - s₀)) + (z - s₀) * ((u : ℂ) * deriv H (s₀ + (u : ℂ) * (z - s₀)))) u := by
      intro u hu
      rw [Set.uIcc_of_le zero_le_one] at hu
      have hmem := hmem_ball z (Metric.mem_closedBall_self hδ0.le) u hu
      have hH_at : HasDerivAt H (deriv H (s₀ + (u : ℂ) * (z - s₀))) (s₀ + (u : ℂ) * (z - s₀)) :=
        (hH.differentiableAt (Metric.isOpen_ball.mem_nhds hmem)).hasDerivAt
      have hlin : HasDerivAt (fun t : ℝ => s₀ + (t : ℂ) * (z - s₀)) (z - s₀) u := by
        have hof : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 u := (hasDerivAt_id u).ofReal_comp
        simpa using (hasDerivAt_const u s₀).fun_add (hof.mul_const (z - s₀))
      have hcomp : HasDerivAt (fun t : ℝ => H (s₀ + (t : ℂ) * (z - s₀)))
          (deriv H (s₀ + (u : ℂ) * (z - s₀)) * (z - s₀)) u :=
        HasDerivAt.comp u hH_at hlin
      have hof : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 u := (hasDerivAt_id u).ofReal_comp
      refine (hof.fun_mul hcomp).congr_deriv ?_
      ring
    have hcont_u : ContinuousOn (fun u : ℝ =>
        H (s₀ + (u : ℂ) * (z - s₀)) + (z - s₀) * ((u : ℂ) * deriv H (s₀ + (u : ℂ) * (z - s₀))))
        (Set.uIcc 0 1) := by
      rw [Set.uIcc_of_le zero_le_one]
      have hcomp : ContinuousOn (fun u : ℝ => s₀ + (u : ℂ) * (z - s₀)) (Set.Icc 0 1) :=
        continuousOn_const.add (Complex.continuous_ofReal.continuousOn.mul continuousOn_const)
      exact (hH_cont.comp hcomp fun u hu => hmem_ball z (Metric.mem_closedBall_self hδ0.le) u hu).add
        (continuousOn_const.mul (Complex.continuous_ofReal.continuousOn.mul
          (hH'_cont.comp hcomp fun u hu => hmem_ball z (Metric.mem_closedBall_self hδ0.le) u hu)))
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv_u hcont_u.intervalIntegrable
    simpa using h
  rwa [hftc] at hstep

theorem exists_holomorphic_log_ball {h : ℂ → ℂ} {s₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hh : DifferentiableOn ℂ h (Metric.ball s₀ r))
    (hnz : ∀ z ∈ Metric.ball s₀ r, h z ≠ 0) :
    ∃ L : ℂ → ℂ, L s₀ = 0 ∧
      (∀ z ∈ Metric.ball s₀ r, HasDerivAt L (deriv h z / h z) z) ∧
      (∀ z ∈ Metric.ball s₀ r, cexp (L z) = h z / h s₀) := by
  set H : ℂ → ℂ := fun z => deriv h z / h z
  have hH_diff : DifferentiableOn ℂ H (Metric.ball s₀ r) :=
    (hh.deriv Metric.isOpen_ball).div hh hnz
  set L : ℂ → ℂ := fun w => ∫ u in (0 : ℝ)..1, (w - s₀) * H (s₀ + (u : ℂ) * (w - s₀))
  have hL0 : L s₀ = 0 := by simp [L]
  have hL_deriv : ∀ z ∈ Metric.ball s₀ r, HasDerivAt L (H z) z :=
    fun z hz => hasDerivAt_radial_primitive_ball hH_diff hz
  refine ⟨L, hL0, hL_deriv, fun z hz => ?_⟩
  
  set q : ℂ → ℂ := fun w => h w * cexp (-L w)
  have hq_deriv : ∀ w ∈ Metric.ball s₀ r, HasDerivAt q 0 w := by
    intro w hw
    have hh_at : HasDerivAt h (deriv h w) w :=
      (hh.differentiableAt (Metric.isOpen_ball.mem_nhds hw)).hasDerivAt
    have hL_at : HasDerivAt L (deriv h w / h w) w := hL_deriv w hw
    have hexp : HasDerivAt (fun x => cexp (-L x)) (cexp (-L w) * -(deriv h w / h w)) w :=
      hL_at.neg.cexp
    refine (hh_at.mul hexp).congr_deriv ?_
    have hne := hnz w hw
    field_simp [hne]
    ring
  have hq_const : q z = q s₀ := by
    have hconv : Convex ℝ (Metric.ball s₀ r) := convex_ball s₀ r
    refine hconv.is_const_of_fderivWithin_eq_zero
      (fun w hw => ((hq_deriv w hw).hasFDerivAt.restrictScalars ℝ).differentiableAt.differentiableWithinAt) ?_
      hz (Metric.mem_ball_self hr)
    intro w hw
    rw [fderivWithin_of_isOpen Metric.isOpen_ball hw,
      ((hq_deriv w hw).hasFDerivAt.restrictScalars ℝ).fderiv]
    simp
  have hqs₀ : q s₀ = h s₀ := by simp [q, hL0]
  have hhz₀ : h s₀ ≠ 0 := hnz s₀ (Metric.mem_ball_self hr)
  rw [hqs₀] at hq_const
  dsimp only [q] at hq_const
  have hmul : h z = h s₀ * cexp (L z) := by
    calc h z = (h z * cexp (-L z)) * cexp (L z) := by
          rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
      _ = h s₀ * cexp (L z) := by rw [hq_const]
  rw [hmul, mul_div_cancel_left₀ _ hhz₀]

private lemma hasDerivAt_logDeriv_list_prod {s₀ : ℂ} {L : List ℂ} {F : ℂ → ℂ → ℂ} {F' : ℂ → ℂ}
    (hd : ∀ ρ ∈ L, HasDerivAt (F ρ) (F' ρ) s₀)
    (hnz : ∀ ρ ∈ L, F ρ s₀ ≠ 0) :
    HasDerivAt (fun z => (L.map (fun ρ => F ρ z)).prod)
      ((L.map (fun ρ => F ρ s₀)).prod * (L.map (fun ρ => F' ρ / F ρ s₀)).sum) s₀ := by
  induction L with
  | nil => simp [hasDerivAt_const]
  | cons a t ih =>
    have ha_d : HasDerivAt (F a) (F' a) s₀ := hd a (List.mem_cons_self ..)
    have ha_nz : F a s₀ ≠ 0 := hnz a (List.mem_cons_self ..)
    have ht_ih := ih (fun ρ hρ => hd ρ (List.mem_cons_of_mem a hρ))
      (fun ρ hρ => hnz ρ (List.mem_cons_of_mem a hρ))
    have hfun : (fun z => ((a :: t).map (fun ρ => F ρ z)).prod) =
        fun z => F a z * (t.map (fun ρ => F ρ z)).prod := by
      funext z; simp
    rw [hfun]
    refine (ha_d.fun_mul ht_ih).congr_deriv ?_
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    field_simp [ha_nz]

set_option maxHeartbeats 2000000 in
theorem landau_negLogDeriv_full {g : ℂ → ℂ} {s₀ : ℂ} {R r M : ℝ}
    (hr : 0 < r) (hrR : r < R) (hM : 1 ≤ M)
    (hg : AnalyticOnNhd ℂ g (Metric.closedBall s₀ R))
    (hg0 : g s₀ ≠ 0)
    (hbd : ∀ z ∈ Metric.closedBall s₀ R, ‖g z‖ ≤ M * ‖g s₀‖) :
    ∃ L : List ℂ,
      (∀ ρ ∈ L, ρ ∈ Metric.closedBall s₀ r ∧ ρ ≠ s₀ ∧ g ρ = 0) ∧
      (∀ ρ ∈ Metric.closedBall s₀ r, g ρ = 0 → ρ ∈ L) ∧
      (-deriv g s₀ / g s₀).re ≤
        (2 / r) * Real.log M -
          (L.map (fun ρ => (s₀ - ρ).re * (1 / ‖s₀ - ρ‖ ^ 2 - 1 / R ^ 2))).sum := by
  have hR : 0 < R := lt_trans hr hrR
  obtain ⟨L, h, hL, hL_cov, hh_an, hh_nz, hh_eq, hh_M⟩ :=
    exists_blaschke_factorization hr hrR hg hg0
      (fun z hz => hbd z (Metric.sphere_subset_closedBall hz))
  
  have hprod_le_one : ‖(L.map (fun ρ => blaschkeFactor s₀ R ρ s₀)).prod‖ ≤ 1 := by
    have haux : ∀ (l : List ℂ), (∀ ρ ∈ l, ‖ρ - s₀‖ ≤ R) →
        ‖(l.map (fun ρ => blaschkeFactor s₀ R ρ s₀)).prod‖ ≤ 1 := by
      intro l
      induction l with
      | nil => intro _; simp
      | cons a t ih =>
        intro hl
        simp only [List.map_cons, List.prod_cons, norm_mul]
        have ha : ‖blaschkeFactor s₀ R a s₀‖ ≤ 1 := by
          rw [blaschkeFactor_norm_center hR]
          exact (div_le_one hR).mpr (hl a (List.mem_cons_self ..))
        have ht := ih (fun ρ hρ => hl ρ (List.mem_cons_of_mem a hρ))
        nlinarith [norm_nonneg (blaschkeFactor s₀ R a s₀),
          norm_nonneg (t.map (fun ρ => blaschkeFactor s₀ R ρ s₀)).prod]
    refine haux L fun ρ hρ => ?_
    have h1 : ‖ρ - s₀‖ ≤ r := by simpa [Metric.mem_closedBall, dist_eq_norm] using (hL ρ hρ).1
    exact h1.trans hrR.le
  have hh0_ge : ‖g s₀‖ ≤ ‖h s₀‖ := by
    have h1 := congrArg norm (hh_eq s₀ (Metric.mem_closedBall_self hR.le))
    rw [norm_mul] at h1
    rw [h1]
    exact mul_le_of_le_one_right (norm_nonneg _) hprod_le_one
  have hh0_ne : h s₀ ≠ 0 := hh_nz s₀ (Metric.mem_closedBall_self hr.le)
  have hh0_pos : 0 < ‖h s₀‖ := norm_pos_iff.mpr hh0_ne
  
  have hh_diff : DifferentiableOn ℂ h (Metric.ball s₀ r) :=
    (hh_an.mono (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall hrR.le))).differentiableOn
  obtain ⟨Log, hLog0, hLog_d, hLog_exp⟩ :=
    exists_holomorphic_log_ball hr hh_diff (fun z hz => hh_nz z (Metric.ball_subset_closedBall hz))
  have hLog_diff : DifferentiableOn ℂ Log (Metric.ball s₀ r) :=
    fun z hz => (hLog_d z hz).differentiableAt.differentiableWithinAt
  have hLog_re : ∀ z ∈ Metric.ball s₀ r, (Log z).re ≤ Real.log M := by
    intro z hz
    have h1 : Real.exp (Log z).re = ‖h z / h s₀‖ := by
      rw [← Complex.norm_exp, hLog_exp z hz]
    have h2 : ‖h z / h s₀‖ ≤ M := by
      rw [norm_div, div_le_iff₀ hh0_pos]
      have hhz : ‖h z‖ ≤ M * ‖g s₀‖ :=
        hh_M z (Metric.closedBall_subset_closedBall hrR.le (Metric.ball_subset_closedBall hz))
      have hM0 : 0 ≤ M := by linarith
      exact hhz.trans (mul_le_mul_of_nonneg_left hh0_ge hM0)
    have h3 : (Log z).re = Real.log ‖h z / h s₀‖ := by
      rw [← h1, Real.log_exp]
    rw [h3]
    have hpos : 0 < ‖h z / h s₀‖ := by
      rw [norm_div]
      exact div_pos (norm_pos_iff.mpr (hh_nz z (Metric.ball_subset_closedBall hz))) hh0_pos
    exact Real.log_le_log hpos h2
  have hbc_h : ‖deriv h s₀ / h s₀‖ ≤ (2 / r) * Real.log M := by
    have h1 := borelCaratheodory_deriv_at_center hr hLog_diff hLog_re
    rw [(hLog_d s₀ (Metric.mem_ball_self hr)).deriv, hLog0, Complex.zero_re, sub_zero] at h1
    exact h1
  
  have hB_nz : ∀ ρ ∈ L, blaschkeFactor s₀ R ρ s₀ ≠ 0 := by
    intro ρ hρ
    rw [blaschkeFactor_eval_center hR]
    exact div_ne_zero (neg_ne_zero.mpr (sub_ne_zero.mpr (hL ρ hρ).2.1))
      (Complex.ofReal_ne_zero.mpr hR.ne')
  have hP_d := hasDerivAt_logDeriv_list_prod (s₀ := s₀) (L := L)
    (F := fun ρ z => blaschkeFactor s₀ R ρ z)
    (F' := fun ρ => deriv (blaschkeFactor s₀ R ρ) s₀)
    (fun ρ _ => (blaschkeFactor_hasDerivAt_center hR).congr_deriv
      (blaschkeFactor_hasDerivAt_center hR).deriv.symm)
    hB_nz
  have hh_at : HasDerivAt h (deriv h s₀) s₀ :=
    (hh_an s₀ (Metric.mem_closedBall_self hR.le)).differentiableAt.hasDerivAt
  have hmul_d := hh_at.fun_mul hP_d
  have hEq_nhds : g =ᶠ[𝓝 s₀] fun z => h z * (L.map (fun ρ => blaschkeFactor s₀ R ρ z)).prod := by
    filter_upwards [Metric.closedBall_mem_nhds s₀ hR] with z hz
    exact hh_eq z hz
  have hg_d : deriv g s₀ =
      deriv h s₀ * (L.map (fun ρ => blaschkeFactor s₀ R ρ s₀)).prod +
      h s₀ * ((L.map (fun ρ => blaschkeFactor s₀ R ρ s₀)).prod *
        (L.map (fun ρ => deriv (blaschkeFactor s₀ R ρ) s₀ / blaschkeFactor s₀ R ρ s₀)).sum) := by
    rw [hEq_nhds.deriv_eq, hmul_d.deriv]
  have hP_ne : (L.map (fun ρ => blaschkeFactor s₀ R ρ s₀)).prod ≠ 0 :=
    List.prod_ne_zero (by
      intro hmem
      obtain ⟨ρ, hρL, h0⟩ := List.mem_map.mp hmem
      exact hB_nz ρ hρL h0)
  have hlogd : deriv g s₀ / g s₀ =
      deriv h s₀ / h s₀ +
        (L.map (fun ρ => deriv (blaschkeFactor s₀ R ρ) s₀ / blaschkeFactor s₀ R ρ s₀)).sum := by
    rw [hg_d, hh_eq s₀ (Metric.mem_closedBall_self hR.le)]
    field_simp [hh0_ne, hP_ne]
  have hre_sum :
      ((L.map (fun ρ => deriv (blaschkeFactor s₀ R ρ) s₀ / blaschkeFactor s₀ R ρ s₀)).sum).re =
      (L.map (fun ρ => (s₀ - ρ).re * (1 / ‖s₀ - ρ‖ ^ 2 - 1 / R ^ 2))).sum := by
    have hmap_re : ∀ (l : List ℂ), (∀ ρ ∈ l, ρ ≠ s₀) →
        ((l.map (fun ρ => deriv (blaschkeFactor s₀ R ρ) s₀ / blaschkeFactor s₀ R ρ s₀)).sum).re =
        (l.map (fun ρ => (s₀ - ρ).re * (1 / ‖s₀ - ρ‖ ^ 2 - 1 / R ^ 2))).sum := by
      intro l
      induction l with
      | nil => intro _; simp
      | cons a t ih =>
        intro hl
        simp only [List.map_cons, List.sum_cons, Complex.add_re]
        rw [blaschkeFactor_logDeriv_center_re hR (hl a (List.mem_cons_self ..)),
          ih (fun ρ hρ => hl ρ (List.mem_cons_of_mem a hρ))]
    exact hmap_re L (fun ρ hρ => (hL ρ hρ).2.1)
  have hneg_le : (-(deriv h s₀ / h s₀)).re ≤ (2 / r) * Real.log M := by
    rw [Complex.neg_re]
    have h1 := (abs_le.mp (Complex.abs_re_le_norm (deriv h s₀ / h s₀))).1
    linarith
  refine ⟨L, hL, hL_cov, ?_⟩
  have hneg_eq : -deriv g s₀ / g s₀ = -(deriv g s₀ / g s₀) := by ring
  rw [hneg_eq, hlogd, neg_add, Complex.add_re, Complex.neg_re, Complex.neg_re, hre_sum]
  rw [Complex.neg_re] at hneg_le
  linarith

theorem landau_negLogDeriv_le {g : ℂ → ℂ} {s₀ : ℂ} {R r M : ℝ}
    (hr : 0 < r) (hrR : r < R) (hM : 1 ≤ M)
    (hg : AnalyticOnNhd ℂ g (Metric.closedBall s₀ R))
    (hg0 : g s₀ ≠ 0)
    (hbd : ∀ z ∈ Metric.closedBall s₀ R, ‖g z‖ ≤ M * ‖g s₀‖)
    (hzeros : ∀ ρ ∈ Metric.closedBall s₀ r, g ρ = 0 → ρ.re ≤ s₀.re) :
    (-deriv g s₀ / g s₀).re ≤ (2 / r) * Real.log M := by
  have hR : 0 < R := lt_trans hr hrR
  obtain ⟨L, hL, _, hle⟩ := landau_negLogDeriv_full hr hrR hM hg hg0 hbd
  have hsum_nonneg :
      0 ≤ (L.map (fun ρ => (s₀ - ρ).re * (1 / ‖s₀ - ρ‖ ^ 2 - 1 / R ^ 2))).sum := by
    refine List.sum_nonneg ?_
    intro x hx
    obtain ⟨ρ, hρL, rfl⟩ := List.mem_map.mp hx
    obtain ⟨hρ_mem, hρ_ne, hρ_zero⟩ := hL ρ hρL
    have hρR : ‖ρ - s₀‖ < R := lt_of_le_of_lt
      (by simpa [Metric.mem_closedBall, dist_eq_norm] using hρ_mem) hrR
    rw [← blaschkeFactor_logDeriv_center_re hR hρ_ne]
    exact blaschkeFactor_logDeriv_center_re_nonneg hR hρ_ne hρR (hzeros ρ hρ_mem hρ_zero)
  linarith

theorem landau_negLogDeriv_le_one_zero {g : ℂ → ℂ} {s₀ ρ₀ : ℂ} {R r M : ℝ}
    (hr : 0 < r) (hrR : r < R) (hM : 1 ≤ M)
    (hg : AnalyticOnNhd ℂ g (Metric.closedBall s₀ R))
    (hg0 : g s₀ ≠ 0)
    (hbd : ∀ z ∈ Metric.closedBall s₀ R, ‖g z‖ ≤ M * ‖g s₀‖)
    (hzeros : ∀ ρ ∈ Metric.closedBall s₀ r, g ρ = 0 → ρ.re ≤ s₀.re)
    (hρ₀_mem : ρ₀ ∈ Metric.closedBall s₀ r) (hρ₀_zero : g ρ₀ = 0) :
    (-deriv g s₀ / g s₀).re ≤
      (2 / r) * Real.log M + (s₀ - ρ₀).re / R ^ 2 - (1 / (s₀ - ρ₀)).re := by
  have hR : 0 < R := lt_trans hr hrR
  obtain ⟨L, hL, hL_cov, hle⟩ := landau_negLogDeriv_full hr hrR hM hg hg0 hbd
  have hρ₀L : ρ₀ ∈ L := hL_cov ρ₀ hρ₀_mem hρ₀_zero
  set φ : ℂ → ℝ := fun ρ => (s₀ - ρ).re * (1 / ‖s₀ - ρ‖ ^ 2 - 1 / R ^ 2)
  have hφ_nonneg : ∀ ρ ∈ L, 0 ≤ φ ρ := by
    intro ρ hρL
    obtain ⟨hρ_mem, hρ_ne, hρ_zero⟩ := hL ρ hρL
    have hρR : ‖ρ - s₀‖ < R := lt_of_le_of_lt
      (by simpa [Metric.mem_closedBall, dist_eq_norm] using hρ_mem) hrR
    dsimp only [φ]
    rw [← blaschkeFactor_logDeriv_center_re hR hρ_ne]
    exact blaschkeFactor_logDeriv_center_re_nonneg hR hρ_ne hρR (hzeros ρ hρ_mem hρ_zero)
  have hterm_le : φ ρ₀ ≤ (L.map φ).sum := by
    have haux : ∀ (l : List ℂ), (∀ ρ ∈ l, 0 ≤ φ ρ) → ρ₀ ∈ l → φ ρ₀ ≤ (l.map φ).sum := by
      intro l
      induction l with
      | nil => intro _ h; simp at h
      | cons a t ih =>
        intro hl hmem
        simp only [List.map_cons, List.sum_cons]
        rcases List.mem_cons.mp hmem with rfl | ht
        · have ht_nn : 0 ≤ (t.map φ).sum := List.sum_nonneg fun x hx => by
            obtain ⟨ρ, hρt, rfl⟩ := List.mem_map.mp hx
            exact hl ρ (List.mem_cons_of_mem _ hρt)
          linarith
        · have ha_nn : 0 ≤ φ a := hl a (List.mem_cons_self ..)
          have hih := ih (fun ρ hρ => hl ρ (List.mem_cons_of_mem a hρ)) ht
          linarith
    exact haux L hφ_nonneg hρ₀L
  have hφ_eq : φ ρ₀ = (1 / (s₀ - ρ₀)).re - (s₀ - ρ₀).re / R ^ 2 := by
    dsimp only [φ]
    have hre1 : (1 / (s₀ - ρ₀)).re = (s₀ - ρ₀).re / ‖s₀ - ρ₀‖ ^ 2 := by
      rw [one_div, Complex.inv_re, Complex.normSq_eq_norm_sq]
    rw [hre1]
    ring
  linarith

def fractNat (t : ℝ) : ℝ := t - (⌊t⌋₊ : ℝ)

lemma fractNat_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ fractNat t :=
  sub_nonneg.mpr (Nat.floor_le ht)

lemma fractNat_lt_one (t : ℝ) : fractNat t < 1 := by
  unfold fractNat
  linarith [Nat.lt_floor_add_one t]

lemma norm_fractNat_le_one {t : ℝ} (ht : 0 ≤ t) : ‖((fractNat t : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_of_nonneg (fractNat_nonneg ht)]
  exact (fractNat_lt_one t).le

lemma measurable_fractNat : Measurable fractNat :=
  measurable_id.sub (measurable_from_top.comp Nat.measurable_floor)

private lemma stepSum_const_one (t : ℝ) :
    Stage3RealAnalyticLandau.stepSum (fun _ : ℕ => (1 : ℂ)) t = (⌊t⌋₊ : ℂ) := by
  unfold Stage3RealAnalyticLandau.stepSum
  simp

private lemma isPreconnected_re_pos_sdiff_one :
    IsPreconnected ({s : ℂ | 0 < s.re} \ {(1 : ℂ)}) := by
  
  set U : Set ℂ := {s : ℂ | 0 < s.re} \ {(1 : ℂ)}
  have h2U : (2 : ℂ) ∈ U := by
    refine ⟨by norm_num, ?_⟩
    intro h; have := congrArg Complex.re h; norm_num at this
  have hseg : ∀ a b : ℂ, a ∈ U → b ∈ U →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, (1 - (t : ℂ)) * a + (t : ℂ) * b ∈ U) →
      JoinedIn U a b := by
    intro a b ha hb hmem
    refine ⟨{
      toFun := fun t => (1 - ((t : ℝ) : ℂ)) * a + ((t : ℝ) : ℂ) * b
      continuous_toFun := by fun_prop
      source' := by simp
      target' := by simp
    }, fun t => hmem t t.2⟩
  have hjoin2 : ∀ z ∈ U, JoinedIn U z (2 : ℂ) := by
    intro z hz
    have hz_re : 0 < z.re := hz.1
    have hz_ne : z ≠ 1 := hz.2
    by_cases him : z.im = 0
    · by_cases hgt : 1 < z.re
      · refine hseg z 2 hz h2U fun t ht => ?_
        have hre : ((1 - (t : ℂ)) * z + (t : ℂ) * 2).re = (1 - t) * z.re + 2 * t := by
          simp [Complex.mul_re]; ring
        refine ⟨show 0 < ((1 - (t : ℂ)) * z + (t : ℂ) * 2).re by rw [hre]; nlinarith [ht.1, ht.2], ?_⟩
        intro h1
        have h1' : ((1 - (t : ℂ)) * z + (t : ℂ) * 2).re = 1 := by
          rw [Set.mem_singleton_iff] at h1; rw [h1, Complex.one_re]
        rw [hre] at h1'
        have hnn : 0 ≤ (1 - t) * (z.re - 1) := mul_nonneg (by linarith [ht.2]) (by linarith)
        rcases eq_or_lt_of_le ht.1 with rfl | ht0
        · linarith
        · nlinarith
      · 
        have hlt : z.re < 1 := lt_of_le_of_ne (le_of_not_gt hgt) fun heq =>
          hz_ne (Complex.ext heq (by simpa using him))
        have hzI : z + I ∈ U := by
          refine ⟨by simpa using hz_re, ?_⟩
          intro h1; have := congrArg Complex.im h1; simp [him] at this
        have h2I : (2 : ℂ) + I ∈ U := by
          refine ⟨by norm_num, ?_⟩
          intro h1; have := congrArg Complex.im h1; simp at this
        have h1 : JoinedIn U z (z + I) := hseg z (z + I) hz hzI fun t ht => by
          have hre : ((1 - (t : ℂ)) * z + (t : ℂ) * (z + I)).re = z.re := by
            simp [Complex.mul_re]; ring
          refine ⟨show 0 < ((1 - (t : ℂ)) * z + (t : ℂ) * (z + I)).re by rw [hre]; exact hz_re, ?_⟩
          intro h1; rw [Set.mem_singleton_iff] at h1
          have := congrArg Complex.re h1; rw [hre, Complex.one_re] at this; linarith
        have h2 : JoinedIn U (z + I) (2 + I) := hseg (z + I) (2 + I) hzI h2I fun t ht => by
          have hre : ((1 - (t : ℂ)) * (z + I) + (t : ℂ) * (2 + I)).re = (1 - t) * z.re + 2 * t := by
            simp [Complex.mul_re]; ring
          have him' : ((1 - (t : ℂ)) * (z + I) + (t : ℂ) * (2 + I)).im = 1 := by
            simp [Complex.mul_im, him]
          refine ⟨show 0 < ((1 - (t : ℂ)) * (z + I) + (t : ℂ) * (2 + I)).re by
            rw [hre]; nlinarith [ht.1, ht.2], ?_⟩
          intro h1; rw [Set.mem_singleton_iff] at h1
          have := congrArg Complex.im h1; rw [him', Complex.one_im] at this; norm_num at this
        have h3 : JoinedIn U (2 + I) 2 := hseg (2 + I) 2 h2I h2U fun t ht => by
          have hre : ((1 - (t : ℂ)) * (2 + I) + (t : ℂ) * 2).re = 2 := by
            simp [Complex.mul_re]; ring
          refine ⟨show 0 < ((1 - (t : ℂ)) * (2 + I) + (t : ℂ) * 2).re by rw [hre]; norm_num, ?_⟩
          intro h1; rw [Set.mem_singleton_iff] at h1
          have := congrArg Complex.re h1; rw [hre, Complex.one_re] at this; norm_num at this
        exact (h1.trans h2).trans h3
    · 
      set w : ℂ := (2 : ℂ) + I * (z.im : ℂ)
      have hw : w ∈ U := by
        refine ⟨by simp [w], ?_⟩
        intro h1; have := congrArg Complex.re h1; simp [w] at this
      have h1 : JoinedIn U z w := hseg z w hz hw fun t ht => by
        have hre : ((1 - (t : ℂ)) * z + (t : ℂ) * w).re = (1 - t) * z.re + 2 * t := by
          simp [w, Complex.mul_re]; ring
        have him' : ((1 - (t : ℂ)) * z + (t : ℂ) * w).im = z.im := by
          simp [w, Complex.mul_im]; ring
        refine ⟨show 0 < ((1 - (t : ℂ)) * z + (t : ℂ) * w).re by
          rw [hre]; rcases eq_or_lt_of_le ht.1 with rfl | ht0 <;> nlinarith [ht.1, ht.2], ?_⟩
        intro h1; rw [Set.mem_singleton_iff] at h1
        have := congrArg Complex.im h1; rw [him', Complex.one_im] at this; exact him this
      have h2 : JoinedIn U w 2 := hseg w 2 hw h2U fun t ht => by
        have hre : ((1 - (t : ℂ)) * w + (t : ℂ) * 2).re = 2 := by
          simp [w, Complex.mul_re]; ring
        refine ⟨show 0 < ((1 - (t : ℂ)) * w + (t : ℂ) * 2).re by rw [hre]; norm_num, ?_⟩
        intro h1; rw [Set.mem_singleton_iff] at h1
        have := congrArg Complex.re h1; rw [hre, Complex.one_re] at this; norm_num at this
      exact h1.trans h2
  have hpc : IsPathConnected U := ⟨2, h2U, fun z hz => (hjoin2 z hz).symm⟩
  exact hpc.isConnected.isPreconnected

theorem riemannZeta_sub_pole_eq_eulerMaclaurin {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s - 1 / (s - 1) =
      1 - s * ∫ t in Ioi (1 : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1) := by
  set U : Set ℂ := {z : ℂ | 0 < z.re} \ {(1 : ℂ)}
  have hU_open : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).sdiff isClosed_singleton
  have hLHS_an : AnalyticOnNhd ℂ (fun z : ℂ => riemannZeta z - 1 / (z - 1)) U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hU_open
    have hz1 : z ≠ 1 := hz.2
    exact ((differentiableAt_riemannZeta hz1).sub
      ((differentiableAt_const (1 : ℂ)).div ((differentiableAt_id).sub (differentiableAt_const 1))
        (sub_ne_zero.mpr hz1))).differentiableWithinAt
  have hE_meas : Measurable (fun t : ℝ => -((fractNat t : ℝ) : ℂ)) :=
    (Complex.measurable_ofReal.comp measurable_fractNat).neg
  have hE_bd : ∀ t : ℝ, 1 ≤ t → ‖-((fractNat t : ℝ) : ℂ)‖ ≤ 1 * t ^ (0 : ℝ) := by
    intro t ht
    rw [norm_neg, Real.rpow_zero, mul_one]
    exact norm_fractNat_le_one (zero_le_one.trans ht)
  have hRHS_an : AnalyticOnNhd ℂ
      (fun z : ℂ => 1 - z * ∫ t in Ioi (1 : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-z - 1)) U := by
    have h1 := Stage3RealAnalyticLandau.analyticOnNhd_mellin_of_rpow_bound hE_meas zero_le_one hE_bd
    have hEq : (fun z : ℂ => 1 + z * ∫ t in Ioi (1 : ℝ), (-((fractNat t : ℝ) : ℂ)) * (t : ℂ) ^ (-z - 1)) =
        fun z : ℂ => 1 - z * ∫ t in Ioi (1 : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-z - 1) := by
      funext z
      have hneg : (fun t : ℝ => (-((fractNat t : ℝ) : ℂ)) * (t : ℂ) ^ (-z - 1)) =
          fun t : ℝ => -(((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-z - 1)) := by funext t; ring
      rw [hneg, integral_neg]
      ring
    rw [hEq] at h1
    exact h1.mono (fun z hz => hz.1)
  have hEq_gt1 : ∀ z : ℂ, 1 < z.re →
      riemannZeta z - 1 / (z - 1) =
        1 - z * ∫ t in Ioi (1 : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-z - 1) := by
    intro z hz
    have hL_eq : LSeries (fun _ : ℕ => (1 : ℂ)) z = riemannZeta z := by
      have h1 := ArithmeticFunction.LSeries_zeta_eq_riemannZeta hz
      rw [ArithmeticFunction.LSeries_zeta_eq] at h1
      exact h1
    have hsum : LSeriesSummable (fun _ : ℕ => (1 : ℂ)) z := by
      have h1 := ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hz
      refine h1.congr fun n => ?_
      rcases eq_or_ne n 0 with rfl | hn
      · simp [LSeries.term]
      · simp [LSeries.term, hn, ArithmeticFunction.zeta_apply]
    have hbd_step : ∀ t : ℝ, 1 ≤ t → ‖Stage3RealAnalyticLandau.stepSum (fun _ : ℕ => (1 : ℂ)) t‖ ≤ 1 * t := by
      intro t ht
      rw [stepSum_const_one, one_mul, Complex.norm_natCast]
      exact Nat.floor_le (zero_le_one.trans ht)
    have hmel := Stage3RealAnalyticLandau.LSeries_sub_pole_eq_mellin_error hbd_step hz hsum
    rw [hL_eq] at hmel
    rw [hmel]
    have hpt : (fun t : ℝ => (Stage3RealAnalyticLandau.stepSum (fun _ : ℕ => (1 : ℂ)) t - (t : ℂ)) *
          (t : ℂ) ^ (-z - 1)) =
        fun t : ℝ => -(((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-z - 1)) := by
      funext t
      rw [stepSum_const_one]
      unfold fractNat
      push_cast
      ring
    rw [hpt, integral_neg]
    ring
  have hEv : (fun z : ℂ => riemannZeta z - 1 / (z - 1)) =ᶠ[𝓝 (2 : ℂ)]
      (fun z : ℂ => 1 - z * ∫ t in Ioi (1 : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-z - 1)) := by
    have hopen1 : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen1.mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with z hz
    exact hEq_gt1 z hz
  have h2U : (2 : ℂ) ∈ U := ⟨by norm_num, fun h => by
    have := congrArg Complex.re h; norm_num at this⟩
  exact hLHS_an.eqOn_of_preconnected_of_eventuallyEq hRHS_an isPreconnected_re_pos_sdiff_one
    h2U hEv ⟨hs, hs1⟩

lemma norm_eulerMaclaurin_tail_le {a : ℝ} (ha : 1 ≤ a) {s : ℂ} (hs : 0 < s.re) :
    ‖∫ t in Ioi a, ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)‖ ≤ a ^ (-s.re) / s.re := by
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  have hre : -s.re - 1 < -1 := by linarith
  have hint_dom : IntegrableOn (fun t : ℝ => t ^ (-s.re - 1)) (Ioi a) :=
    integrableOn_Ioi_rpow_of_lt hre ha0
  have hint_val : ∫ t in Ioi a, t ^ (-s.re - 1) = a ^ (-s.re) / s.re := by
    rw [integral_Ioi_rpow_of_lt hre ha0]
    have h1 : -s.re - 1 + 1 = -s.re := by ring
    rw [h1]; field_simp [hs.ne']
  calc ‖∫ t in Ioi a, ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)‖
      ≤ ∫ t in Ioi a, ‖((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi a, t ^ (-s.re - 1) := by
        refine setIntegral_mono_on ?_ hint_dom measurableSet_Ioi fun t ht => ?_
        · have hint_full : IntegrableOn (fun t : ℝ => ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)) (Ioi (1 : ℝ)) :=
            Stage3RealAnalyticLandau.integrableOn_mellin_of_rpow_bound
              (Complex.measurable_ofReal.comp measurable_fractNat)
              (fun u hu => by simpa [Real.rpow_zero] using norm_fractNat_le_one (zero_le_one.trans hu)) hs
          exact (hint_full.mono_set (Ioi_subset_Ioi ha)).norm
        · have ht0 : 0 < t := ha0.trans ht
          rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
          have hre' : (-s - 1).re = -s.re - 1 := by simp
          rw [hre']
          exact mul_le_of_le_one_left (Real.rpow_nonneg ht0.le _) (norm_fractNat_le_one ht0.le)
    _ = a ^ (-s.re) / s.re := hint_val

theorem riemannZeta_real_bounds {σ : ℝ} (hσ : 1 < σ) :
    (riemannZeta (σ : ℂ)).im = 0 ∧
    1 / (σ - 1) ≤ (riemannZeta (σ : ℂ)).re ∧
    (riemannZeta (σ : ℂ)).re ≤ σ / (σ - 1) := by
  have hs0 : 0 < (σ : ℂ).re := by simp; linarith
  have hs1 : (σ : ℂ) ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hem := riemannZeta_sub_pole_eq_eulerMaclaurin hs0 hs1
  have hreal_int : ∫ t in Ioi (1 : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-(σ : ℂ) - 1) =
      (((∫ t in Ioi (1 : ℝ), fractNat t * t ^ (-σ - 1) : ℝ) : ℂ)) := by
    have hpt : EqOn (fun t : ℝ => ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-(σ : ℂ) - 1))
        (fun t : ℝ => (((fractNat t * t ^ (-σ - 1) : ℝ) : ℂ))) (Ioi (1 : ℝ)) := by
      intro t ht
      have ht0 : 0 < t := zero_lt_one.trans ht
      dsimp only
      have hexp : -(σ : ℂ) - 1 = (((-σ - 1 : ℝ) : ℂ)) := by push_cast; ring
      rw [hexp, ← Complex.ofReal_cpow ht0.le, Complex.ofReal_mul]
    rw [setIntegral_congr_fun measurableSet_Ioi hpt]
    exact Complex.ofRealCLM.integral_comp_comm (by
      have hre : -σ - 1 < -1 := by linarith
      refine (integrableOn_Ioi_rpow_of_lt hre zero_lt_one).mono'
        ((measurable_fractNat.mul (measurable_id.pow_const _)).aestronglyMeasurable) ?_
      refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
      have ht0 : 0 < t := zero_lt_one.trans ht
      change ‖fractNat t * t ^ (-σ - 1)‖ ≤ t ^ (-σ - 1)
      rw [Real.norm_of_nonneg (mul_nonneg (fractNat_nonneg ht0.le) (Real.rpow_nonneg ht0.le _))]
      exact mul_le_of_le_one_left (Real.rpow_nonneg ht0.le _) (fractNat_lt_one t).le)
  have hzeta_real : riemannZeta (σ : ℂ) =
      (((1 / (σ - 1) + 1 - σ * ∫ t in Ioi (1 : ℝ), fractNat t * t ^ (-σ - 1) : ℝ) : ℂ)) := by
    have h1 : riemannZeta (σ : ℂ) =
        1 / ((σ : ℂ) - 1) + 1 - (σ : ℂ) * ∫ t in Ioi (1 : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-(σ : ℂ) - 1) := by
      linear_combination hem
    rw [h1, hreal_int]
    push_cast; rfl
  have hint_nn : 0 ≤ ∫ t in Ioi (1 : ℝ), fractNat t * t ^ (-σ - 1) := by
    refine setIntegral_nonneg measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := zero_lt_one.trans ht
    exact mul_nonneg (fractNat_nonneg ht0.le) (Real.rpow_nonneg ht0.le _)
  have hint_le : ∫ t in Ioi (1 : ℝ), fractNat t * t ^ (-σ - 1) ≤ 1 / σ := by
    have hre : -σ - 1 < -1 := by linarith
    have hint_dom : IntegrableOn (fun t : ℝ => t ^ (-σ - 1)) (Ioi (1 : ℝ)) :=
      integrableOn_Ioi_rpow_of_lt hre zero_lt_one
    have hint_f : IntegrableOn (fun t : ℝ => fractNat t * t ^ (-σ - 1)) (Ioi (1 : ℝ)) := by
      refine hint_dom.mono' ((measurable_fractNat.mul (measurable_id.pow_const _)).aestronglyMeasurable) ?_
      refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
      have ht0 : 0 < t := zero_lt_one.trans ht
      change ‖fractNat t * t ^ (-σ - 1)‖ ≤ t ^ (-σ - 1)
      rw [Real.norm_of_nonneg (mul_nonneg (fractNat_nonneg ht0.le) (Real.rpow_nonneg ht0.le _))]
      exact mul_le_of_le_one_left (Real.rpow_nonneg ht0.le _) (fractNat_lt_one t).le
    have hval : ∫ t in Ioi (1 : ℝ), t ^ (-σ - 1) = 1 / σ := by
      rw [integral_Ioi_rpow_of_lt hre zero_lt_one, Real.one_rpow]
      have h1 : -σ - 1 + 1 = -σ := by ring
      rw [h1]; field_simp [(by linarith : σ ≠ 0)]
    rw [← hval]
    refine setIntegral_mono_on hint_f hint_dom measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := zero_lt_one.trans ht
    exact mul_le_of_le_one_left (Real.rpow_nonneg ht0.le _) (fractNat_lt_one t).le
  rw [hzeta_real, Complex.ofReal_im, Complex.ofReal_re]
  have hσ_pos : 0 < σ := by linarith
  have hσ1_ne : σ - 1 ≠ 0 := by linarith
  have hupper : 1 / (σ - 1) + 1 = σ / (σ - 1) := by field_simp [hσ1_ne]; ring
  have hmul_le : σ * ∫ t in Ioi (1 : ℝ), fractNat t * t ^ (-σ - 1) ≤ 1 := by
    have h1 := mul_le_mul_of_nonneg_left hint_le hσ_pos.le
    rw [mul_one_div_cancel hσ_pos.ne'] at h1
    exact h1
  refine ⟨rfl, ?_, ?_⟩
  · linarith
  · linarith [mul_nonneg hσ_pos.le hint_nn]

private lemma norm_LSeries_le_riemannZeta_real {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1)
    {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    ‖LSeries f ((σ : ℂ) + I * (t : ℂ))‖ ≤ (riemannZeta (σ : ℂ)).re := by
  have hs : 1 < ((σ : ℂ) + I * (t : ℂ)).re := by simp [hσ]
  have hsσ : 1 < (σ : ℂ).re := by simp [hσ]
  have hsum_z : Summable (fun n : ℕ => if n = 0 then (0 : ℝ) else (n : ℝ) ^ (-σ)) := by
    have h1 := (ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hsσ).norm
    refine h1.congr fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term]
    · rw [LSeries.term_of_ne_zero hn, ArithmeticFunction.zeta_apply, if_neg hn, Nat.cast_one,
        norm_div, norm_one, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn),
        Complex.ofReal_re, if_neg hn, one_div, Real.rpow_neg (Nat.cast_nonneg n)]
  have hsum_f : Summable (fun n : ℕ => ‖LSeries.term f ((σ : ℂ) + I * (t : ℂ)) n‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) hsum_z
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term]
    · rw [LSeries.term_of_ne_zero hn, norm_div,
        Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn),
        show ((σ : ℂ) + I * (t : ℂ)).re = σ by simp, if_neg hn,
        Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
      exact mul_le_of_le_one_left (inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg n) σ)) (hf n)
  have hzeta_re : (riemannZeta (σ : ℂ)).re = ∑' n : ℕ, if n = 0 then (0 : ℝ) else (n : ℝ) ^ (-σ) := by
    rw [← ArithmeticFunction.LSeries_zeta_eq_riemannZeta hsσ]
    unfold LSeries
    have hsumZ := ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hsσ
    rw [← Complex.reCLM_apply, Complex.reCLM.map_tsum hsumZ]
    refine tsum_congr fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term]
    · have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      simp only [LSeries.term, hn, ↓reduceIte, ArithmeticFunction.zeta_apply, Nat.cast_one,
        Complex.reCLM_apply]
      have hcpow : ((n : ℂ) ^ (σ : ℂ)) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
        rw [← Complex.ofReal_natCast, Complex.ofReal_cpow hn0.le]
      rw [hcpow, ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re, one_div,
        Real.rpow_neg hn0.le]
  rw [hzeta_re]
  unfold LSeries
  refine (norm_tsum_le_tsum_norm hsum_f).trans ?_
  refine hsum_f.tsum_le_tsum (fun n => ?_) hsum_z
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term]
  · rw [LSeries.term_of_ne_zero hn, norm_div,
      Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn),
      show ((σ : ℂ) + I * (t : ℂ)).re = σ by simp, if_neg hn,
      Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
    exact mul_le_of_le_one_left (inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg n) σ)) (hf n)

private lemma norm_moebius_le_one (n : ℕ) : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
  by_cases h : Squarefree n
  · rw [ArithmeticFunction.moebius_apply_of_squarefree h]
    push_cast
    rw [norm_pow, norm_neg, norm_one, one_pow]
  · simp [ArithmeticFunction.moebius, h]

set_option maxHeartbeats 2000000 in
theorem negLogDerivZeta_real_le {σ : ℝ} (hσ : 1 < σ) :
    (Stage3ZeroFreeRegion.negLogDerivZeta (σ : ℂ)).re ≤ 1 / (σ - 1) + 1 := by
  have hs0 : 0 < (σ : ℂ).re := by simp; linarith
  have hs1 : (σ : ℂ) ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hE_meas : Measurable (fun t : ℝ => ((fractNat t : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp measurable_fractNat
  have hE_bd : ∀ t : ℝ, 1 ≤ t → ‖((fractNat t : ℝ) : ℂ)‖ ≤ 1 * t ^ (0 : ℝ) := by
    intro t ht; simpa [Real.rpow_zero] using norm_fractNat_le_one (zero_le_one.trans ht)
  
  have hI_d := Stage3RealAnalyticLandau.hasDerivAt_mellin_of_rpow_bound hE_meas zero_le_one hE_bd hs0
  have hEq : riemannZeta =ᶠ[𝓝 (σ : ℂ)] fun z : ℂ =>
      1 / (z - 1) + 1 - z * ∫ t in Ioi (1 : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-z - 1) := by
    have hopen : IsOpen ({z : ℂ | 0 < z.re} \ {(1 : ℂ)}) :=
      (isOpen_lt continuous_const Complex.continuous_re).sdiff isClosed_singleton
    filter_upwards [hopen.mem_nhds ⟨hs0, hs1⟩] with z hz
    linear_combination riemannZeta_sub_pole_eq_eulerMaclaurin hz.1 hz.2
  have hpole_d : HasDerivAt (fun z : ℂ => 1 / (z - 1)) (-1 / ((σ : ℂ) - 1) ^ 2) (σ : ℂ) := by
    have h1 := ((hasDerivAt_id' (σ : ℂ)).sub_const 1).inv (sub_ne_zero.mpr hs1)
    refine (h1.congr_of_eventuallyEq (Eventually.of_forall fun z => by simp [one_div])).congr_deriv ?_
    ring
  have hzeta_d : deriv riemannZeta (σ : ℂ) =
      -1 / ((σ : ℂ) - 1) ^ 2 -
        (∫ t in Ioi (1 : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-(σ : ℂ) - 1)) -
        (σ : ℂ) * (∫ t in Ioi (1 : ℝ), ((fractNat t : ℝ) : ℂ) *
          (-(Real.log t : ℂ) * (t : ℂ) ^ (-(σ : ℂ) - 1))) := by
    rw [hEq.deriv_eq]
    have h1 := (hpole_d.add_const (1 : ℂ)).fun_sub ((hasDerivAt_id' (σ : ℂ)).fun_mul hI_d)
    rw [h1.deriv]
    ring
  
  have hint_real1 : IntegrableOn (fun t : ℝ => fractNat t * t ^ (-σ - 1)) (Ioi (1 : ℝ)) := by
    have hre : -σ - 1 < -1 := by linarith
    refine (integrableOn_Ioi_rpow_of_lt hre zero_lt_one).mono'
      ((measurable_fractNat.mul (measurable_id.pow_const _)).aestronglyMeasurable) ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := zero_lt_one.trans ht
    rw [Real.norm_of_nonneg (mul_nonneg (fractNat_nonneg ht0.le) (Real.rpow_nonneg ht0.le _))]
    exact mul_le_of_le_one_left (Real.rpow_nonneg ht0.le _) (fractNat_lt_one t).le
  have hreal1 : (∫ t in Ioi (1 : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-(σ : ℂ) - 1)).re =
      ∫ t in Ioi (1 : ℝ), fractNat t * t ^ (-σ - 1) := by
    have hpt : EqOn (fun t : ℝ => ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-(σ : ℂ) - 1))
        (fun t : ℝ => (((fractNat t * t ^ (-σ - 1) : ℝ) : ℂ))) (Ioi (1 : ℝ)) := by
      intro t ht
      have ht0 : 0 < t := zero_lt_one.trans ht
      dsimp only
      have hexp : -(σ : ℂ) - 1 = (((-σ - 1 : ℝ) : ℂ)) := by push_cast; ring
      rw [hexp, ← Complex.ofReal_cpow ht0.le, Complex.ofReal_mul]
    rw [setIntegral_congr_fun measurableSet_Ioi hpt]
    have hcomm := Complex.ofRealCLM.integral_comp_comm hint_real1
    simpa [Complex.ofRealCLM_apply] using congrArg Complex.re hcomm
  have hint_real2 : IntegrableOn (fun t : ℝ => -(fractNat t * Real.log t * t ^ (-σ - 1))) (Ioi (1 : ℝ)) := by
    set e : ℝ := (σ - 1) / 2
    have he0 : 0 < e := by dsimp only [e]; linarith
    have hre : e - σ - 1 < -1 := by dsimp only [e]; linarith
    refine ((integrableOn_Ioi_rpow_of_lt hre zero_lt_one).const_mul e⁻¹).mono'
      (((measurable_fractNat.mul Real.measurable_log).mul (measurable_id.pow_const _)).neg.aestronglyMeasurable) ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
    have ht1 : 1 < t := ht
    have ht0 : 0 < t := zero_lt_one.trans ht1
    rw [norm_neg, Real.norm_of_nonneg (mul_nonneg (mul_nonneg (fractNat_nonneg ht0.le)
      (Real.log_nonneg ht1.le)) (Real.rpow_nonneg ht0.le _))]
    have hlog : Real.log t ≤ e⁻¹ * t ^ e := by
      have := Real.log_le_rpow_div ht0.le he0
      linarith [show t ^ e / e = e⁻¹ * t ^ e by ring]
    have hcomb : t ^ e * t ^ (-σ - 1) = t ^ (e - σ - 1) := by
      rw [← Real.rpow_add ht0]; congr 1; ring
    have h1 : fractNat t * Real.log t ≤ 1 * (e⁻¹ * t ^ e) :=
      mul_le_mul (fractNat_lt_one t).le hlog (Real.log_nonneg ht1.le) zero_le_one
    calc fractNat t * Real.log t * t ^ (-σ - 1)
        ≤ (1 * (e⁻¹ * t ^ e)) * t ^ (-σ - 1) :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg ht0.le _)
      _ = e⁻¹ * (t ^ e * t ^ (-σ - 1)) := by ring
      _ = e⁻¹ * t ^ (e - σ - 1) := by rw [hcomb]
  have hreal2 : (∫ t in Ioi (1 : ℝ), ((fractNat t : ℝ) : ℂ) *
        (-(Real.log t : ℂ) * (t : ℂ) ^ (-(σ : ℂ) - 1))).re =
      -(∫ t in Ioi (1 : ℝ), fractNat t * Real.log t * t ^ (-σ - 1)) := by
    have hpt : EqOn (fun t : ℝ => ((fractNat t : ℝ) : ℂ) *
          (-(Real.log t : ℂ) * (t : ℂ) ^ (-(σ : ℂ) - 1)))
        (fun t : ℝ => (((-(fractNat t * Real.log t * t ^ (-σ - 1)) : ℝ) : ℂ))) (Ioi (1 : ℝ)) := by
      intro t ht
      have ht0 : 0 < t := zero_lt_one.trans ht
      dsimp only
      have hexp : -(σ : ℂ) - 1 = (((-σ - 1 : ℝ) : ℂ)) := by push_cast; ring
      rw [hexp, ← Complex.ofReal_cpow ht0.le]
      push_cast; ring
    rw [setIntegral_congr_fun measurableSet_Ioi hpt]
    have hcomm := Complex.ofRealCLM.integral_comp_comm hint_real2
    simpa [Complex.ofRealCLM_apply, integral_neg] using congrArg Complex.re hcomm
  have hneg_deriv_re : (-deriv riemannZeta (σ : ℂ)).re ≤ 1 / (σ - 1) ^ 2 + 1 / σ := by
    have h1 : (-deriv riemannZeta (σ : ℂ)).re =
        1 / (σ - 1) ^ 2 +
          (∫ t in Ioi (1 : ℝ), fractNat t * t ^ (-σ - 1)) -
          σ * (∫ t in Ioi (1 : ℝ), fractNat t * Real.log t * t ^ (-σ - 1)) := by
      rw [hzeta_d]
      have hp : (1 / ((σ : ℂ) - 1) ^ 2).re = 1 / (σ - 1) ^ 2 := by
        have hcast : ((σ : ℂ) - 1) ^ 2 = ((((σ - 1) ^ 2 : ℝ) : ℂ)) := by push_cast; ring
        rw [hcast, ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
      simp only [neg_sub, Complex.sub_re, Complex.re_ofReal_mul, hreal1, hreal2]
      have hp' : (-1 / ((σ : ℂ) - 1) ^ 2).re = -(1 / (σ - 1) ^ 2) := by
        rw [neg_div, Complex.neg_re, hp]
      rw [hp']
      ring
    rw [h1]
    have hint1_le : ∫ t in Ioi (1 : ℝ), fractNat t * t ^ (-σ - 1) ≤ 1 / σ := by
      have hre : -σ - 1 < -1 := by linarith
      have hint_dom : IntegrableOn (fun t : ℝ => t ^ (-σ - 1)) (Ioi (1 : ℝ)) :=
        integrableOn_Ioi_rpow_of_lt hre zero_lt_one
      have hint_f : IntegrableOn (fun t : ℝ => fractNat t * t ^ (-σ - 1)) (Ioi (1 : ℝ)) := by
        refine hint_dom.mono' ((measurable_fractNat.mul (measurable_id.pow_const _)).aestronglyMeasurable) ?_
        refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
        have ht0 : 0 < t := zero_lt_one.trans ht
        change ‖fractNat t * t ^ (-σ - 1)‖ ≤ t ^ (-σ - 1)
        rw [Real.norm_of_nonneg (mul_nonneg (fractNat_nonneg ht0.le) (Real.rpow_nonneg ht0.le _))]
        exact mul_le_of_le_one_left (Real.rpow_nonneg ht0.le _) (fractNat_lt_one t).le
      have hval : ∫ t in Ioi (1 : ℝ), t ^ (-σ - 1) = 1 / σ := by
        rw [integral_Ioi_rpow_of_lt hre zero_lt_one, Real.one_rpow]
        have h2 : -σ - 1 + 1 = -σ := by ring
        rw [h2]; field_simp [(by linarith : σ ≠ 0)]
      rw [← hval]
      refine setIntegral_mono_on hint_f hint_dom measurableSet_Ioi fun t ht => ?_
      have ht0 : 0 < t := zero_lt_one.trans ht
      exact mul_le_of_le_one_left (Real.rpow_nonneg ht0.le _) (fractNat_lt_one t).le
    have hint2_nn : 0 ≤ ∫ t in Ioi (1 : ℝ), fractNat t * Real.log t * t ^ (-σ - 1) := by
      refine setIntegral_nonneg measurableSet_Ioi fun t ht => ?_
      have ht1 : 1 < t := ht
      have ht0 : 0 < t := zero_lt_one.trans ht1
      exact mul_nonneg (mul_nonneg (fractNat_nonneg ht0.le) (Real.log_nonneg ht1.le))
        (Real.rpow_nonneg ht0.le _)
    nlinarith
  
  obtain ⟨hz_im, hz_ge, _⟩ := riemannZeta_real_bounds hσ
  have hz_pos : 0 < (riemannZeta (σ : ℂ)).re := lt_of_lt_of_le (by positivity) hz_ge
  have hz_eq : riemannZeta (σ : ℂ) = (((riemannZeta (σ : ℂ)).re : ℝ) : ℂ) :=
    Complex.ext (by simp) (by simp [hz_im])
  unfold Stage3ZeroFreeRegion.negLogDerivZeta
  rw [hz_eq, Complex.div_ofReal_re]
  have hσ1_pos : 0 < σ - 1 := by linarith
  have hσ_pos : 0 < σ := by linarith
  calc (-deriv riemannZeta (σ : ℂ)).re / (riemannZeta (σ : ℂ)).re
      ≤ (1 / (σ - 1) ^ 2 + 1 / σ) / (1 / (σ - 1)) := by
        refine div_le_div₀ (by positivity) hneg_deriv_re (by positivity) hz_ge
    _ = 1 / (σ - 1) + (σ - 1) / σ := by
        field_simp [hσ1_pos.ne', hσ_pos.ne']
    _ ≤ 1 / (σ - 1) + 1 := by
        have hfrac : (σ - 1) / σ ≤ 1 := (div_le_one hσ_pos).mpr (by linarith)
        linarith

theorem norm_LFunction_and_inv_and_logDeriv_of_one_lt_re {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    ‖DirichletCharacter.LFunction χ ((σ : ℂ) + I * (t : ℂ))‖ ≤ σ / (σ - 1) ∧
    ‖1 / DirichletCharacter.LFunction χ ((σ : ℂ) + I * (t : ℂ))‖ ≤ σ / (σ - 1) ∧
    ‖Stage3ZeroFreeRegion.negLogDerivL χ ((σ : ℂ) + I * (t : ℂ))‖ ≤ 1 / (σ - 1) + 1 := by
  have hs : 1 < ((σ : ℂ) + I * (t : ℂ)).re := by simp [hσ]
  have hsσ : 1 < (σ : ℂ).re := by simp [hσ]
  have hζ_le := (riemannZeta_real_bounds hσ).2.2
  have h1 : ‖DirichletCharacter.LFunction χ ((σ : ℂ) + I * (t : ℂ))‖ ≤ σ / (σ - 1) := by
    rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
    exact (norm_LSeries_le_riemannZeta_real (fun n => χ.norm_le_one _) hσ t).trans hζ_le
  have h2 : ‖1 / DirichletCharacter.LFunction χ ((σ : ℂ) + I * (t : ℂ))‖ ≤ σ / (σ - 1) := by
    have hmul := DirichletCharacter.LSeries.mul_mu_eq_one χ hs
    rw [← DirichletCharacter.LFunction_eq_LSeries χ hs] at hmul
    have hne : DirichletCharacter.LFunction χ ((σ : ℂ) + I * (t : ℂ)) ≠ 0 :=
      DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inr (by
        intro h; have := congrArg Complex.re h; simp at this; linarith)) hs.le
    have hinv : 1 / DirichletCharacter.LFunction χ ((σ : ℂ) + I * (t : ℂ)) =
        LSeries ((fun n : ℕ => χ (n : ZMod q)) * fun n : ℕ => (ArithmeticFunction.moebius n : ℂ))
          ((σ : ℂ) + I * (t : ℂ)) := by
      rw [div_eq_iff hne, mul_comm, hmul]
    rw [hinv]
    refine (norm_LSeries_le_riemannZeta_real (fun n => ?_) hσ t).trans hζ_le
    dsimp [Pi.mul_apply]
    rw [norm_mul]
    exact mul_le_one₀ (χ.norm_le_one _) (norm_nonneg _) (norm_moebius_le_one n)
  have h3 : ‖Stage3ZeroFreeRegion.negLogDerivL χ ((σ : ℂ) + I * (t : ℂ))‖ ≤ 1 / (σ - 1) + 1 := by
    refine le_trans ?_ (negLogDerivZeta_real_le hσ)
    rw [Stage3ZeroFreeRegion.negLogDerivL_eq_LSeries χ hs,
      Stage3ZeroFreeRegion.negLogDerivZeta_eq_LSeries hsσ]
    have hsumσ := ArithmeticFunction.LSeriesSummable_vonMangoldt hsσ
    have hsumt := χ.LSeriesSummable_twist_vonMangoldt hs
    unfold LSeries
    rw [← Complex.reCLM_apply, Complex.reCLM.map_tsum hsumσ]
    refine (norm_tsum_le_tsum_norm hsumt.norm).trans ?_
    refine hsumt.norm.tsum_le_tsum (fun n => ?_) (Complex.reCLM.summable hsumσ)
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term]
    · have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, Complex.reCLM_apply,
        norm_div, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn),
        show ((σ : ℂ) + I * (t : ℂ)).re = σ by simp]
      have hcpow : ((n : ℂ) ^ (σ : ℂ)) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
        rw [← Complex.ofReal_natCast, Complex.ofReal_cpow hn0.le]
      rw [hcpow, ← Complex.ofReal_div, Complex.ofReal_re]
      gcongr
      dsimp [Pi.mul_apply]
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      exact mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg (χ.norm_le_one _)
  exact ⟨h1, h2, h3⟩

theorem norm_stepSum_dirichletChar_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (t : ℝ) :
    ‖Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t‖ ≤ (q : ℝ) := by
  unfold Stage3RealAnalyticLandau.stepSum
  have hq0 : 0 < q := NeZero.pos q
  have hblock : ∀ k : ℕ, ∑ n ∈ Finset.Icc 1 (k * q), χ (n : ZMod q) = 0 := by
    intro k
    induction k with
    | zero => simp
    | succ m ih =>
      have hmq : (m + 1) * q = m * q + q := by ring
      have hsplit : Finset.Icc 1 ((m + 1) * q) =
          Finset.Icc 1 (m * q) ∪ Finset.Icc (m * q + 1) ((m + 1) * q) := by
        ext n; simp only [Finset.mem_Icc, Finset.mem_union]; omega
      have hdisj : Disjoint (Finset.Icc 1 (m * q)) (Finset.Icc (m * q + 1) ((m + 1) * q)) := by
        rw [Finset.disjoint_left]; intro n hn1 hn2
        simp only [Finset.mem_Icc] at hn1 hn2; omega
      rw [hsplit, Finset.sum_union hdisj, ih, zero_add]
      have hfull : ∑ n ∈ Finset.Icc (m * q + 1) ((m + 1) * q), χ (n : ZMod q) =
          ∑ a : ZMod q, χ a := by
        refine Finset.sum_bij (fun n _ => (n : ZMod q)) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
        · intro n₁ hn₁ n₂ hn₂ heq
          simp only [Finset.mem_Icc] at hn₁ hn₂
          have hdvd : (q : ℤ) ∣ ((n₁ : ℤ) - (n₂ : ℤ)) := by
            have h0 : (((n₁ : ℤ) - (n₂ : ℤ) : ℤ) : ZMod q) = 0 := by
              push_cast; exact sub_eq_zero.mpr heq
            exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp h0
          obtain ⟨c, hc⟩ := hdvd
          have hlt1 : (n₁ : ℤ) - (n₂ : ℤ) < (q : ℤ) := by omega
          have hgt1 : -(q : ℤ) < (n₁ : ℤ) - (n₂ : ℤ) := by omega
          have hc0 : c = 0 := by nlinarith
          have hsub0 : (n₁ : ℤ) - (n₂ : ℤ) = 0 := by rw [hc, hc0, mul_zero]
          omega
        · intro a _
          set r : ℕ := a.val with hr_def
          have hr : r < q := a.val_lt
          by_cases hr0 : r = 0
          · refine ⟨(m + 1) * q, ?_, ?_⟩
            · simp only [Finset.mem_Icc]; omega
            · have ha0 : a = 0 := by
                have := ZMod.natCast_zmod_val a
                rw [← this, ← hr_def, hr0, Nat.cast_zero]
              rw [ha0]; push_cast; simp
          · refine ⟨m * q + r, ?_, ?_⟩
            · simp only [Finset.mem_Icc]; omega
            · push_cast; simp [hr_def]
        · intro _ _; rfl
      rw [hfull]
      exact MulChar.sum_eq_zero_of_ne_one hχ
  set N : ℕ := ⌊t⌋₊
  set k : ℕ := N / q
  set r : ℕ := N % q
  have hdiv : N = k * q + r := by
    rw [mul_comm]; exact (Nat.div_add_mod N q).symm
  have hr_lt : r < q := Nat.mod_lt N hq0
  have hsplit : Finset.Icc 1 N = Finset.Icc 1 (k * q) ∪ Finset.Icc (k * q + 1) N := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  have hdisj : Disjoint (Finset.Icc 1 (k * q)) (Finset.Icc (k * q + 1) N) := by
    rw [Finset.disjoint_left]; intro n hn1 hn2
    simp only [Finset.mem_Icc] at hn1 hn2; omega
  rw [hsplit, Finset.sum_union hdisj, hblock k, zero_add]
  calc ‖∑ n ∈ Finset.Icc (k * q + 1) N, χ (n : ZMod q)‖
      ≤ ∑ n ∈ Finset.Icc (k * q + 1) N, ‖χ (n : ZMod q)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Icc (k * q + 1) N, (1 : ℝ) :=
        Finset.sum_le_sum fun n _ => χ.norm_le_one _
    _ = ((Finset.Icc (k * q + 1) N).card : ℝ) := by simp
    _ ≤ (q : ℝ) := by
        rw [Nat.card_Icc]
        have hle : N + 1 - (k * q + 1) ≤ q := by omega
        exact_mod_cast hle

theorem LFunction_eq_mellin_of_ne_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.LFunction χ s =
      s * ∫ t in Ioi (1 : ℝ),
        Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-s - 1) := by
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hpc : IsPreconnected {z : ℂ | 0 < z.re} :=
    (convex_halfSpace_re_gt 0).isPreconnected
  have hLHS_an : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) {z : ℂ | 0 < z.re} := by
    refine DifferentiableOn.analyticOnNhd (fun z _ => ?_) hopen
    exact (DirichletCharacter.differentiableAt_LFunction χ z (.inr hχ)).differentiableWithinAt
  have hE_meas : Measurable (Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q))) :=
    Stage3RealAnalyticLandau.measurable_stepSum _
  have hE_bd : ∀ t : ℝ, 1 ≤ t →
      ‖Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t‖ ≤ (q : ℝ) * t ^ (0 : ℝ) := by
    intro t _; simpa [Real.rpow_zero] using norm_stepSum_dirichletChar_le hχ t
  have hRHS_an : AnalyticOnNhd ℂ
      (fun z : ℂ => z * ∫ t in Ioi (1 : ℝ),
        Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-z - 1))
      {z : ℂ | 0 < z.re} := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hopen
    have hd := Stage3RealAnalyticLandau.hasDerivAt_mellin_of_rpow_bound hE_meas (Nat.cast_nonneg q)
      hE_bd hz
    exact (differentiableAt_id.mul hd.differentiableAt).differentiableWithinAt
  have hEv : DirichletCharacter.LFunction χ =ᶠ[𝓝 (2 : ℂ)]
      (fun z : ℂ => z * ∫ t in Ioi (1 : ℝ),
        Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-z - 1)) := by
    have hopen1 : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen1.mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with z hz
    rw [DirichletCharacter.LFunction_eq_LSeries χ hz]
    have hsum : LSeriesSummable (fun n => χ (n : ZMod q)) z := by
      have h1 := ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hz
      refine (h1.norm).of_norm_bounded fun n => ?_
      rcases eq_or_ne n 0 with rfl | hn
      · simp [LSeries.term]
      · simp only [LSeries.term, hn, ↓reduceIte, ArithmeticFunction.zeta_apply, Nat.cast_one,
          norm_div, norm_one]
        gcongr
        exact χ.norm_le_one _
    exact Stage3RealAnalyticLandau.LSeries_eq_mul_mellin_stepSum hE_bd (by linarith) hsum
  exact hLHS_an.eqOn_of_preconnected_of_eventuallyEq hRHS_an hpc (by norm_num : (0 : ℝ) < (2 : ℂ).re)
    hEv hs

theorem norm_LFunction_le_of_re_pos {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    ‖DirichletCharacter.LFunction χ s‖ ≤ (q : ℝ) * ‖s‖ / s.re := by
  rw [LFunction_eq_mellin_of_ne_one hχ hs, norm_mul]
  have hre : -s.re - 1 < -1 := by linarith
  have hint_dom : IntegrableOn (fun t : ℝ => (q : ℝ) * t ^ (-s.re - 1)) (Ioi (1 : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt hre zero_lt_one).const_mul (q : ℝ)
  have hint_val : ∫ t in Ioi (1 : ℝ), (q : ℝ) * t ^ (-s.re - 1) = (q : ℝ) / s.re := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt hre zero_lt_one, Real.one_rpow]
    have h1 : -s.re - 1 + 1 = -s.re := by ring
    rw [h1]; field_simp [hs.ne']
  have hint_f : IntegrableOn (fun t : ℝ =>
      Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-s - 1)) (Ioi (1 : ℝ)) :=
    Stage3RealAnalyticLandau.integrableOn_mellin_of_rpow_bound
      (Stage3RealAnalyticLandau.measurable_stepSum _)
      (fun t _ => by simpa [Real.rpow_zero] using norm_stepSum_dirichletChar_le hχ t) hs
  have hint_le : ‖∫ t in Ioi (1 : ℝ),
      Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-s - 1)‖ ≤
      (q : ℝ) / s.re := by
    rw [← hint_val]
    refine (norm_integral_le_integral_norm _).trans ?_
    refine setIntegral_mono_on hint_f.norm hint_dom measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := zero_lt_one.trans ht
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    have hre' : (-s - 1).re = -s.re - 1 := by simp
    rw [hre']
    exact mul_le_mul_of_nonneg_right (norm_stepSum_dirichletChar_le hχ t) (Real.rpow_nonneg ht0.le _)
  calc ‖s‖ * ‖∫ t in Ioi (1 : ℝ),
        Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-s - 1)‖
      ≤ ‖s‖ * ((q : ℝ) / s.re) := mul_le_mul_of_nonneg_left hint_le (norm_nonneg s)
    _ = (q : ℝ) * ‖s‖ / s.re := by ring

theorem norm_LFunction_strip_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {s : ℂ} (hlo : 1 / 2 ≤ s.re) (hhi : s.re ≤ 2) :
    ‖DirichletCharacter.LFunction χ s‖ ≤ 2 * (q : ℝ) * (|s.im| + 2) := by
  have hs0 : 0 < s.re := by linarith
  have hbd := norm_LFunction_le_of_re_pos hχ hs0
  have hnorm_s : ‖s‖ ≤ |s.im| + 2 := by
    have h1 := Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_pos hs0] at h1
    linarith
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  calc ‖DirichletCharacter.LFunction χ s‖
      ≤ (q : ℝ) * ‖s‖ / s.re := hbd
    _ ≤ (q : ℝ) * (|s.im| + 2) / (1 / 2) := by
        refine div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hnorm_s hq0) (by positivity) hlo
    _ = 2 * (q : ℝ) * (|s.im| + 2) := by ring

end RHDirect.Stage5ZetaZeroFree
end

noncomputable section

open Complex DirichletCharacter Finset MeasureTheory Set Filter Topology

open scoped BigOperators ArithmeticFunction.vonMangoldt

namespace RHDirect.Stage5DirichletLZeroFree

theorem harmonic_sum_le_log_add_one {m : ℕ} (hm : 1 ≤ m) :
    ∑ k ∈ Finset.Icc 1 m, ((k : ℝ))⁻¹ ≤ Real.log (m : ℝ) + 1 := by
  induction m, hm using Nat.le_induction with
  | base =>
    simp
  | succ k hk ih =>
    have hIcc : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
      ext n; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot : k + 1 ∉ Finset.Icc 1 k := by simp
    rw [hIcc, Finset.sum_insert hnot]
    have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
    have hk1_pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    have hstep : (((k + 1 : ℕ) : ℝ))⁻¹ ≤ Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ) := by
      have hexp := Real.add_one_le_exp (-(((k + 1 : ℕ) : ℝ))⁻¹)
      have hdiv : (k : ℝ) / ((k + 1 : ℕ) : ℝ) = -(((k + 1 : ℕ) : ℝ))⁻¹ + 1 := by
        push_cast
        field_simp [hk1_pos.ne']
        ring
      rw [← hdiv] at hexp
      have hlog := Real.log_le_log (div_pos hk_pos hk1_pos) hexp
      rw [Real.log_div hk_pos.ne' hk1_pos.ne', Real.log_exp] at hlog
      linarith
    linarith

theorem two_le_of_dirichletChar_ne_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) : 2 ≤ q := by
  have hq0 : q ≠ 0 := NeZero.ne q
  by_contra hlt
  have hq1 : q = 1 := by omega
  subst hq1
  exact hχ (DirichletCharacter.level_one χ)

theorem sum_dirichletChar_zmod_eq_zero {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) : ∑ a : ZMod q, χ a = 0 := by
  have hex : ∃ u : (ZMod q)ˣ, χ (u : ZMod q) ≠ 1 := by
    by_contra hall
    push Not at hall
    apply hχ
    ext a
    rw [hall a, MulChar.one_apply a.isUnit]
  obtain ⟨u, hu⟩ := hex
  set S : ℂ := ∑ a : ZMod q, χ a
  have hshift : χ (u : ZMod q) * S = S := by
    dsimp only [S]
    rw [Finset.mul_sum]
    calc ∑ a : ZMod q, χ (u : ZMod q) * χ a
        = ∑ a : ZMod q, χ ((u : ZMod q) * a) := by
          refine Finset.sum_congr rfl fun a _ => (map_mul χ _ _).symm
      _ = ∑ a : ZMod q, χ a :=
          Fintype.sum_equiv (MulAction.toPerm u) _ _ fun _ => rfl
  have hmul : (χ (u : ZMod q) - 1) * S = 0 := by linear_combination hshift
  exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hu)

theorem sum_dirichletChar_Ico_period {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (M : ℕ) :
    ∑ n ∈ Finset.Ico M (M + q), χ (n : ZMod q) = 0 := by
  have hbij :
      ∑ n ∈ Finset.Ico M (M + q), χ (n : ZMod q) = ∑ a : ZMod q, χ a := by
    have hshift :
        ∑ n ∈ Finset.Ico M (M + q), χ (n : ZMod q) =
          ∑ k ∈ Finset.range q, χ ((M + k : ℕ) : ZMod q) := by
      refine Finset.sum_bij (fun n _ => n - M) ?_ ?_ ?_ ?_
      · intro n hn; simp only [Finset.mem_Ico] at hn; exact Finset.mem_range.mpr (by omega)
      · intro n₁ hn₁ n₂ hn₂ h; simp only [Finset.mem_Ico] at hn₁ hn₂; omega
      · intro k hk; simp only [Finset.mem_range] at hk
        exact ⟨M + k, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro n hn; simp only [Finset.mem_Ico] at hn; congr 2; omega
    rw [hshift]
    have hrange :
        ∑ k ∈ Finset.range q, χ ((M + k : ℕ) : ZMod q) =
          ∑ a : ZMod q, χ ((M : ZMod q) + a) := by
      refine Finset.sum_bij (fun k _ => (k : ZMod q)) ?_ ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro k₁ hk₁ k₂ hk₂ h
        simp only [Finset.mem_range] at hk₁ hk₂
        have hv := congrArg ZMod.val h
        rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hk₁, Nat.mod_eq_of_lt hk₂] at hv
        exact hv
      · intro a _
        exact ⟨a.val, Finset.mem_range.mpr (ZMod.val_lt a), ZMod.natCast_zmod_val a⟩
      · intro k _; simp [Nat.cast_add]
    rw [hrange]
    exact Fintype.sum_equiv (Equiv.addLeft (M : ZMod q)) _ _ fun _ => rfl
  rw [hbij, sum_dirichletChar_zmod_eq_zero hχ]

theorem norm_sum_dirichletChar_Ico_le_modulus {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (M N : ℕ) :
    ‖∑ n ∈ Finset.Ico M (M + N), χ (n : ZMod q)‖ ≤ (q : ℝ) := by
  have hq_pos : 0 < q := NeZero.pos q
  have hperiod_mul : ∀ m : ℕ, ∑ n ∈ Finset.Ico M (M + q * m), χ (n : ZMod q) = 0 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hqm : q * (m + 1) = q * m + q := by ring
      have hsplit : Finset.Ico M (M + q * (m + 1)) =
          Finset.Ico M (M + q * m) ∪ Finset.Ico (M + q * m) (M + q * m + q) := by
        ext n; simp only [Finset.mem_Ico, Finset.mem_union]; omega
      have hdisj : Disjoint (Finset.Ico M (M + q * m)) (Finset.Ico (M + q * m) (M + q * m + q)) := by
        rw [Finset.disjoint_left]
        intro n h1 h2; simp only [Finset.mem_Ico] at h1 h2; omega
      rw [hsplit, Finset.sum_union hdisj, ih, sum_dirichletChar_Ico_period hχ (M + q * m), add_zero]
  set m := N / q
  set r := N % q
  have hN : N = q * m + r := (Nat.div_add_mod N q).symm
  have hr : r < q := Nat.mod_lt N hq_pos
  have hsplit : Finset.Ico M (M + N) =
      Finset.Ico M (M + q * m) ∪ Finset.Ico (M + q * m) (M + N) := by
    ext n; simp only [Finset.mem_Ico, Finset.mem_union]; omega
  have hdisj : Disjoint (Finset.Ico M (M + q * m)) (Finset.Ico (M + q * m) (M + N)) := by
    rw [Finset.disjoint_left]
    intro n h1 h2; simp only [Finset.mem_Ico] at h1 h2; omega
  rw [hsplit, Finset.sum_union hdisj, hperiod_mul m, zero_add]
  calc ‖∑ n ∈ Finset.Ico (M + q * m) (M + N), χ (n : ZMod q)‖
      ≤ ∑ n ∈ Finset.Ico (M + q * m) (M + N), ‖χ (n : ZMod q)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Ico (M + q * m) (M + N), (1 : ℝ) :=
        Finset.sum_le_sum fun n _ => χ.norm_le_one _
    _ = ((Finset.Ico (M + q * m) (M + N)).card : ℝ) := by simp
    _ = (r : ℝ) := by
        rw [Nat.card_Ico]
        exact_mod_cast (by omega : M + N - (M + q * m) = r)
    _ ≤ (q : ℝ) := by exact_mod_cast hr.le

theorem norm_stepSum_dirichletChar_le_modulus {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (x : ℝ) :
    ‖Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) x‖ ≤ (q : ℝ) := by
  unfold Stage3RealAnalyticLandau.stepSum
  have hIcc : Finset.Icc 1 ⌊x⌋₊ = Finset.Ico 1 (1 + ⌊x⌋₊) := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hIcc]
  exact norm_sum_dirichletChar_Ico_le_modulus hχ 1 ⌊x⌋₊

theorem LFunction_eq_mul_mellin_of_ne_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    LFunction χ s =
      s * ∫ t in Ioi (1 : ℝ),
        Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-s - 1) := by
  set U : Set ℂ := {z : ℂ | 0 < z.re}
  have hU_open : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hU_conv : Convex ℝ U := by
    intro x hx y hy a b ha hb hab
    show 0 < (a • x + b • y).re
    simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    rcases eq_or_lt_of_le ha with rfl | ha_pos
    · have hb1 : b = 1 := by linarith
      subst hb1
      have hy0 : 0 < y.re := hy
      simpa using hy0
    · have hx0 : 0 < x.re := hx
      have hy0 : 0 < y.re := hy
      have h1 : 0 < a * x.re := mul_pos ha_pos hx0
      have h2 : 0 ≤ b * y.re := mul_nonneg hb (le_of_lt hy0)
      linarith
  have hU_pre : IsPreconnected U := hU_conv.isPreconnected
  have hbd : ∀ t : ℝ, 1 ≤ t →
      ‖Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t‖ ≤ (q : ℝ) * t ^ (0 : ℝ) := by
    intro t _
    simpa using norm_stepSum_dirichletChar_le_modulus hχ t
  have hLHS_an : AnalyticOnNhd ℂ (LFunction χ) U :=
    (DirichletCharacter.differentiable_LFunction hχ).differentiableOn.analyticOnNhd hU_open
  have hRHS_an : AnalyticOnNhd ℂ
      (fun z : ℂ => z * ∫ t in Ioi (1 : ℝ),
        Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-z - 1)) U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hU_open
    have hd := Stage3RealAnalyticLandau.hasDerivAt_mellin_of_rpow_bound
      (Stage3RealAnalyticLandau.measurable_stepSum (fun n => χ (n : ZMod q)))
      (Nat.cast_nonneg q) hbd hz
    exact (differentiableAt_id.mul hd.differentiableAt).differentiableWithinAt
  have h2U : (2 : ℂ) ∈ U := by simp [U]
  have hEv : LFunction χ =ᶠ[𝓝 (2 : ℂ)]
      (fun z : ℂ => z * ∫ t in Ioi (1 : ℝ),
        Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-z - 1)) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (by simp : 1 < (2 : ℂ).re)] with z (hz : 1 < z.re)
    have hz0 : 0 < z.re := by linarith
    rw [DirichletCharacter.LFunction_eq_LSeries χ hz]
    exact Stage3RealAnalyticLandau.LSeries_eq_mul_mellin_stepSum hbd hz0
      (DirichletCharacter.LSeriesSummable_of_one_lt_re χ hz)
  exact hLHS_an.eqOn_of_preconnected_of_eventuallyEq hRHS_an hU_pre h2U hEv hs

private lemma integral_Ioi_one_eq_interval_add_Ioi {f : ℝ → ℂ} {a : ℝ} (ha : 1 ≤ a)
    (hint : IntegrableOn f (Ioi (1 : ℝ))) :
    ∫ t in Ioi (1 : ℝ), f t =
      (∫ t in (1 : ℝ)..a, f t) + ∫ t in Ioi a, f t := by
  have hunion : Ioi (1 : ℝ) = Ioc (1 : ℝ) a ∪ Ioi a := (Ioc_union_Ioi_eq_Ioi ha).symm
  have hdisj : Disjoint (Ioc (1 : ℝ) a) (Ioi a) := Ioc_disjoint_Ioi_same
  have hsub1 : Ioc (1 : ℝ) a ⊆ Ioi (1 : ℝ) := Ioc_subset_Ioi_self
  have hsub2 : Ioi a ⊆ Ioi (1 : ℝ) := Ioi_subset_Ioi ha
  rw [hunion, setIntegral_union hdisj measurableSet_Ioi (hint.mono_set hsub1) (hint.mono_set hsub2),
    intervalIntegral.integral_of_le ha]

theorem LFunction_eq_partialSum_add_tail {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {N : ℕ} (hN : 1 ≤ N) {s : ℂ} (hs : 0 < s.re) :
    LFunction χ s =
      (∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (n : ℂ) ^ (-s)) -
        Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) (N : ℝ) * (N : ℂ) ^ (-s) +
        s * ∫ t in Ioi (N : ℝ),
          Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-s - 1) := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := Nat.one_le_cast.mpr hN
  have hbd : ∀ t : ℝ, 1 ≤ t →
      ‖Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t‖ ≤ (q : ℝ) * t ^ (0 : ℝ) := by
    intro t _
    simpa using norm_stepSum_dirichletChar_le_modulus hχ t
  have hint : IntegrableOn
      (fun t : ℝ => Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-s - 1))
      (Ioi (1 : ℝ)) :=
    Stage3RealAnalyticLandau.integrableOn_mellin_of_rpow_bound
      (Stage3RealAnalyticLandau.measurable_stepSum _) hbd hs
  rw [LFunction_eq_mul_mellin_of_ne_one hχ hs, integral_Ioi_one_eq_interval_add_Ioi hN1 hint,
    mul_add]
  have hab := Stage3RealAnalyticLandau.abel_summation_dirichlet
    (fun n => χ (n : ZMod q)) hN1 s
  rw [Nat.floor_natCast] at hab
  linear_combination -hab

private lemma log_four_gt : (1.38 : ℝ) < Real.log 4 := by
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  linarith [Real.log_two_gt_d9]

private lemma log_q_mul_abs_add_two_ge {q : ℕ} (hq : 2 ≤ q) (t : ℝ) :
    (1.38 : ℝ) < Real.log ((q : ℝ) * (|t| + 2)) := by
  have h4le : (4 : ℝ) ≤ (q : ℝ) * (|t| + 2) := by
    have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    have htR : (2 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
    nlinarith
  exact lt_of_lt_of_le log_four_gt (Real.log_le_log (by norm_num) h4le)

set_option maxHeartbeats 2000000 in
theorem norm_LFunction_le_log_of_one_le_re {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {s : ℂ} (hs1 : 1 ≤ s.re) (hs2 : s.re ≤ 2) :
    ‖LFunction χ s‖ ≤ 5 * Real.log ((q : ℝ) * (|s.im| + 2)) := by
  have hq2 : 2 ≤ q := two_le_of_dirichletChar_ne_one hχ
  have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (by omega)
  have hs0 : 0 < s.re := by linarith
  set L : ℝ := Real.log ((q : ℝ) * (|s.im| + 2))
  have hL : (1.38 : ℝ) < L := log_q_mul_abs_add_two_ge hq2 s.im
  set X : ℝ := (q : ℝ) * (|s.im| + 2)
  have hX4 : (4 : ℝ) ≤ X := by
    have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
    nlinarith [abs_nonneg s.im]
  set N : ℕ := ⌊X⌋₊ + 1
  have hN1 : 1 ≤ N := Nat.succ_le_succ (Nat.zero_le _)
  have hN_ge : X ≤ (N : ℝ) := by
    dsimp only [N]; push_cast; exact (Nat.lt_floor_add_one X).le
  have hN_le : (N : ℝ) ≤ 2 * X := by
    dsimp only [N]; push_cast
    have hfl : (⌊X⌋₊ : ℝ) ≤ X := Nat.floor_le (by linarith)
    linarith
  have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN1
  rw [LFunction_eq_partialSum_add_tail hχ hN1 hs0]
  
  have hT1 : ‖∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (n : ℂ) ^ (-s)‖ ≤ Real.log (N : ℝ) + 1 := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ n ∈ Finset.Icc 1 N, ‖χ (n : ZMod q) * (n : ℂ) ^ (-s)‖
        ≤ ∑ n ∈ Finset.Icc 1 N, ((n : ℝ))⁻¹ := by
          refine Finset.sum_le_sum fun n hn => ?_
          have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
          have hn1R : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr hn1
          rw [norm_mul, Complex.norm_natCast_cpow_of_pos hn1, neg_re]
          calc ‖χ (n : ZMod q)‖ * (n : ℝ) ^ (-s.re)
              ≤ 1 * (n : ℝ) ^ (-s.re) :=
                mul_le_mul_of_nonneg_right (χ.norm_le_one _) (Real.rpow_nonneg (by positivity) _)
            _ = (n : ℝ) ^ (-s.re) := one_mul _
            _ ≤ (n : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn1R (by linarith)
            _ = ((n : ℝ))⁻¹ := Real.rpow_neg_one _
      _ ≤ Real.log (N : ℝ) + 1 := harmonic_sum_le_log_add_one hN1
  
  have hT2 : ‖Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) (N : ℝ) * (N : ℂ) ^ (-s)‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hN1, neg_re]
    have hpow : (N : ℝ) ^ (-s.re) ≤ ((N : ℝ))⁻¹ := by
      rw [← Real.rpow_neg_one (N : ℝ)]
      exact Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr hN1) (by linarith)
    calc ‖Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) (N : ℝ)‖ * (N : ℝ) ^ (-s.re)
        ≤ (q : ℝ) * ((N : ℝ))⁻¹ :=
          mul_le_mul (norm_stepSum_dirichletChar_le_modulus hχ (N : ℝ)) hpow
            (Real.rpow_nonneg hN_pos.le _) hq_pos.le
      _ = (q : ℝ) / (N : ℝ) := by rw [div_eq_mul_inv]
      _ ≤ 1 := by
          rw [div_le_one hN_pos]
          have : (q : ℝ) ≤ X := by dsimp only [X]; nlinarith [abs_nonneg s.im]
          linarith
  
  have hT3 : ‖s * ∫ t in Ioi (N : ℝ),
      Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-s - 1)‖ ≤ 1 := by
    rw [norm_mul]
    have hdom : IntegrableOn (fun t : ℝ => (q : ℝ) * t ^ (-s.re - 1)) (Ioi (N : ℝ)) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) hN_pos).const_mul (q : ℝ)
    have hint_le :
        ‖∫ t in Ioi (N : ℝ),
          Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-s - 1)‖ ≤
        (q : ℝ) * (N : ℝ) ^ (-s.re) / s.re := by
      have h1 :
          ‖∫ t in Ioi (N : ℝ),
            Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-s - 1)‖ ≤
          ∫ t in Ioi (N : ℝ), (q : ℝ) * t ^ (-s.re - 1) := by
        refine (norm_integral_le_integral_norm _).trans ?_
        refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) hdom ?_
        refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
        have ht0 : 0 < t := hN_pos.trans ht
        dsimp only
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
        have hre : (-s - 1).re = -s.re - 1 := by simp
        rw [hre]
        exact mul_le_mul_of_nonneg_right (norm_stepSum_dirichletChar_le_modulus hχ t)
          (Real.rpow_nonneg ht0.le _)
      have heval : ∫ t in Ioi (N : ℝ), (q : ℝ) * t ^ (-s.re - 1) = (q : ℝ) * (N : ℝ) ^ (-s.re) / s.re := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hN_pos]
        have hden : -s.re - 1 + 1 = -s.re := by ring
        rw [hden]; field_simp [hs0.ne']
      exact h1.trans_eq heval
    have hns : ‖s‖ ≤ |s.im| + 2 := by
      have h := Complex.norm_le_abs_re_add_abs_im s
      rw [abs_of_pos hs0] at h
      linarith
    have hpow : (N : ℝ) ^ (-s.re) ≤ ((N : ℝ))⁻¹ := by
      rw [← Real.rpow_neg_one (N : ℝ)]
      exact Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr hN1) (by linarith)
    calc ‖s‖ *
          ‖∫ t in Ioi (N : ℝ),
            Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-s - 1)‖
        ≤ (|s.im| + 2) * ((q : ℝ) * (N : ℝ) ^ (-s.re) / s.re) :=
          mul_le_mul hns hint_le (norm_nonneg _) (by positivity)
      _ ≤ (|s.im| + 2) * ((q : ℝ) * ((N : ℝ))⁻¹ / 1) := by
          gcongr
      _ = X / (N : ℝ) := by dsimp only [X]; field_simp [hN_pos.ne']
      _ ≤ 1 := (div_le_one hN_pos).mpr hN_ge
  have hlogN : Real.log (N : ℝ) ≤ L + Real.log 2 := by
    have h1 := Real.log_le_log hN_pos hN_le
    rw [Real.log_mul (by norm_num) (by linarith : X ≠ 0)] at h1
    linarith
  have hlog2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  calc ‖(∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (n : ℂ) ^ (-s)) -
          Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) (N : ℝ) * (N : ℂ) ^ (-s) +
          s * ∫ t in Ioi (N : ℝ),
            Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-s - 1)‖
      ≤ ‖(∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (n : ℂ) ^ (-s)) -
            Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) (N : ℝ) * (N : ℂ) ^ (-s)‖ +
          ‖s * ∫ t in Ioi (N : ℝ),
            Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-s - 1)‖ :=
        norm_add_le _ _
    _ ≤ (‖∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (n : ℂ) ^ (-s)‖ +
          ‖Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) (N : ℝ) * (N : ℂ) ^ (-s)‖) +
          ‖s * ∫ t in Ioi (N : ℝ),
            Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-s - 1)‖ := by
        gcongr; exact norm_sub_le _ _
    _ ≤ (Real.log (N : ℝ) + 1 + 1) + 1 := by linarith
    _ ≤ 5 * L := by linarith

end RHDirect.Stage5DirichletLZeroFree
end

noncomputable section

open Complex MeasureTheory Set Filter Topology

open scoped ArithmeticFunction.vonMangoldt BigOperators

namespace RHDirect.Stage6EffectivePNT

def zetaReg (z : ℂ) : ℂ :=
  1 + (z - 1) *
    (1 - z * ∫ t in Ioi (1 : ℝ),
      ((Stage5ZetaZeroFree.fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-z - 1))

theorem zetaReg_one : zetaReg 1 = 1 := by
  simp [zetaReg]

theorem zetaReg_eq_mul_riemannZeta {z : ℂ} (hz : 0 < z.re) (hz1 : z ≠ 1) :
    zetaReg z = (z - 1) * riemannZeta z := by
  unfold zetaReg
  rw [← Stage5ZetaZeroFree.riemannZeta_sub_pole_eq_eulerMaclaurin hz hz1]
  have hne : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  field_simp [hne]
  ring

theorem differentiableOn_zetaReg : DifferentiableOn ℂ zetaReg {z : ℂ | 0 < z.re} := by
  have hE_meas : Measurable (fun t : ℝ => -((Stage5ZetaZeroFree.fractNat t : ℝ) : ℂ)) :=
    (Complex.measurable_ofReal.comp Stage5ZetaZeroFree.measurable_fractNat).neg
  have hE_bd : ∀ t : ℝ, 1 ≤ t →
      ‖-((Stage5ZetaZeroFree.fractNat t : ℝ) : ℂ)‖ ≤ 1 * t ^ (0 : ℝ) := by
    intro t ht
    rw [norm_neg, Real.rpow_zero, mul_one]
    exact Stage5ZetaZeroFree.norm_fractNat_le_one (zero_le_one.trans ht)
  have hH_an := Stage3RealAnalyticLandau.analyticOnNhd_mellin_of_rpow_bound hE_meas zero_le_one hE_bd
  have hEq : (fun z : ℂ => 1 + z * ∫ t in Ioi (1 : ℝ),
        (-((Stage5ZetaZeroFree.fractNat t : ℝ) : ℂ)) * (t : ℂ) ^ (-z - 1)) =
      fun z : ℂ => 1 - z * ∫ t in Ioi (1 : ℝ),
        ((Stage5ZetaZeroFree.fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-z - 1) := by
    funext z
    have hneg : (fun t : ℝ => (-((Stage5ZetaZeroFree.fractNat t : ℝ) : ℂ)) * (t : ℂ) ^ (-z - 1)) =
        fun t : ℝ => -(((Stage5ZetaZeroFree.fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-z - 1)) := by
      funext t; ring
    rw [hneg, integral_neg]; ring
  rw [hEq] at hH_an
  have hH_diff : DifferentiableOn ℂ
      (fun z : ℂ => 1 - z * ∫ t in Ioi (1 : ℝ),
        ((Stage5ZetaZeroFree.fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-z - 1)) {z : ℂ | 0 < z.re} :=
    hH_an.differentiableOn
  unfold zetaReg
  exact (differentiableOn_const 1).add ((differentiableOn_id.sub (differentiableOn_const 1)).mul hH_diff)

end RHDirect.Stage6EffectivePNT
end

noncomputable section

open Complex DirichletCharacter Finset MeasureTheory Set Filter Topology

open RHDirect.Stage5DirichletLZeroFree

open scoped BigOperators

namespace RHDirect.Stage6ClassNumberFormula

theorem norm_LFunction_one_sub_partialSum_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {N : ℕ} (hN : 1 ≤ N) :
    ‖LFunction χ 1 - ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) / (n : ℂ)‖ ≤
      2 * (q : ℝ) / (N : ℝ) := by
  have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
  have hs : (0 : ℝ) < (1 : ℂ).re := by simp
  have hsplit := LFunction_eq_partialSum_add_tail hχ hN hs
  have hsum_eq :
      ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (n : ℂ) ^ (-(1 : ℂ)) =
        ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) / (n : ℂ) := by
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Complex.cpow_neg_one, div_eq_mul_inv]
  rw [hsplit, hsum_eq]
  have hdiff :
      ((∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) / (n : ℂ)) -
        Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) (N : ℝ) * (N : ℂ) ^ (-(1 : ℂ)) +
        (1 : ℂ) * ∫ t in Ioi (N : ℝ),
          Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t *
            (t : ℂ) ^ (-(1 : ℂ) - 1)) -
        ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) / (n : ℂ) =
      -(Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) (N : ℝ) * (N : ℂ) ^ (-(1 : ℂ))) +
        ∫ t in Ioi (N : ℝ),
          Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t *
            (t : ℂ) ^ (-(1 : ℂ) - 1) := by
    ring
  rw [hdiff]
  have hT1 :
      ‖-(Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) (N : ℝ) *
          (N : ℂ) ^ (-(1 : ℂ)))‖ ≤ (q : ℝ) / (N : ℝ) := by
    rw [norm_neg, norm_mul, Complex.cpow_neg_one, norm_inv, Complex.norm_natCast,
      ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_right (norm_stepSum_dirichletChar_le_modulus hχ (N : ℝ)) hN_pos.le
  have hT2 :
      ‖∫ t in Ioi (N : ℝ),
        Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t *
          (t : ℂ) ^ (-(1 : ℂ) - 1)‖ ≤ (q : ℝ) / (N : ℝ) := by
    have hdom : IntegrableOn (fun t : ℝ => (q : ℝ) * t ^ (-2 : ℝ)) (Ioi (N : ℝ)) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num) hN_pos).const_mul (q : ℝ)
    have h1 :
        ‖∫ t in Ioi (N : ℝ),
          Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t *
            (t : ℂ) ^ (-(1 : ℂ) - 1)‖ ≤
        ∫ t in Ioi (N : ℝ), (q : ℝ) * t ^ (-2 : ℝ) := by
      refine (norm_integral_le_integral_norm _).trans ?_
      refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) hdom ?_
      refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
      have ht0 : 0 < t := hN_pos.trans ht
      dsimp only
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
      have hre : (-(1 : ℂ) - 1).re = (-2 : ℝ) := by norm_num
      rw [hre]
      exact mul_le_mul_of_nonneg_right (norm_stepSum_dirichletChar_le_modulus hχ t)
        (Real.rpow_nonneg ht0.le _)
    have heval : ∫ t in Ioi (N : ℝ), (q : ℝ) * t ^ (-2 : ℝ) = (q : ℝ) / (N : ℝ) := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hN_pos]
      have hexp : (-2 : ℝ) + 1 = -1 := by norm_num
      rw [hexp, Real.rpow_neg_one]
      field_simp [hN_pos.ne']
    exact h1.trans_eq heval
  calc ‖-(Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) (N : ℝ) *
            (N : ℂ) ^ (-(1 : ℂ))) +
          ∫ t in Ioi (N : ℝ),
            Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t *
              (t : ℂ) ^ (-(1 : ℂ) - 1)‖
      ≤ ‖-(Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) (N : ℝ) *
            (N : ℂ) ^ (-(1 : ℂ)))‖ +
        ‖∫ t in Ioi (N : ℝ),
          Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t *
            (t : ℂ) ^ (-(1 : ℂ) - 1)‖ := norm_add_le _ _
    _ ≤ (q : ℝ) / (N : ℝ) + (q : ℝ) / (N : ℝ) := add_le_add hT1 hT2
    _ = 2 * (q : ℝ) / (N : ℝ) := by ring

theorem tendsto_partialSum_LFunction_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) / (n : ℂ))
      atTop (nhds (LFunction χ 1)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hzero : Tendsto (fun N : ℕ => 2 * (q : ℝ) / (N : ℝ)) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul (2 * (q : ℝ))
  refine squeeze_zero_norm' ?_ hzero
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), norm_sub_rev]
  exact norm_LFunction_one_sub_partialSum_le hχ hN

theorem LFunction_im_eq_zero_of_real {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (hreal : ∀ a : ZMod q, (χ a).im = 0) {σ : ℝ} (hσ : 0 < σ) :
    (LFunction χ (σ : ℂ)).im = 0 := by
  have hs : 0 < (σ : ℂ).re := by simpa using hσ
  rw [LFunction_eq_mul_mellin_of_ne_one hχ hs]
  have hstep_real : ∀ t : ℝ,
      Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t =
        ((∑ n ∈ Finset.Icc 1 ⌊t⌋₊, (χ (n : ZMod q)).re : ℝ) : ℂ) := by
    intro t
    unfold Stage3RealAnalyticLandau.stepSum
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    exact Complex.ext (by simp) (by simpa using hreal _)
  have hint_eq :
      ∫ t in Ioi (1 : ℝ),
        Stage3RealAnalyticLandau.stepSum (fun n => χ (n : ZMod q)) t * (t : ℂ) ^ (-(σ : ℂ) - 1) =
      ((∫ t in Ioi (1 : ℝ),
        (∑ n ∈ Finset.Icc 1 ⌊t⌋₊, (χ (n : ZMod q)).re) * t ^ (-σ - 1) : ℝ) : ℂ) := by
    have hof :
        ∫ t in Ioi (1 : ℝ),
          (((∑ n ∈ Finset.Icc 1 ⌊t⌋₊, (χ (n : ZMod q)).re) * t ^ (-σ - 1) : ℝ) : ℂ) =
        ((∫ t in Ioi (1 : ℝ),
          (∑ n ∈ Finset.Icc 1 ⌊t⌋₊, (χ (n : ZMod q)).re) * t ^ (-σ - 1) : ℝ) : ℂ) :=
      integral_ofReal
    rw [← hof]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := zero_lt_one.trans ht
    rw [hstep_real t, Complex.ofReal_mul, show -(σ : ℂ) - 1 = ((-σ - 1 : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_cpow ht0.le]
  rw [hint_eq, ← Complex.ofReal_mul, Complex.ofReal_im]

theorem LFunction_re_pos_of_real_of_one_lt {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hreal : ∀ a : ZMod q, (χ a).im = 0) {σ : ℝ} (hσ : 1 < σ) :
    0 < (LFunction χ (σ : ℂ)).re := by
  have hs : 1 < (σ : ℂ).re := by simpa using hσ
  have heuler := DirichletCharacter.LSeries_eulerProduct χ hs
  rw [← DirichletCharacter.LFunction_eq_LSeries χ hs] at heuler
  
  have hfin_pos : ∀ N : ℕ,
      (∏ p ∈ N.primesBelow, (1 - χ (p : ZMod q) * (p : ℂ) ^ (-(σ : ℂ)))⁻¹).im = 0 ∧
      0 < (∏ p ∈ N.primesBelow, (1 - χ (p : ZMod q) * (p : ℂ) ^ (-(σ : ℂ)))⁻¹).re := by
    intro N
    have hprod_real :
        ∏ p ∈ N.primesBelow, (1 - χ (p : ZMod q) * (p : ℂ) ^ (-(σ : ℂ)))⁻¹ =
          ((∏ p ∈ N.primesBelow, (1 - (χ (p : ZMod q)).re * (p : ℝ) ^ (-σ))⁻¹ : ℝ) : ℂ) := by
      rw [Complex.ofReal_prod]
      refine Finset.prod_congr rfl fun p hp => ?_
      have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr (Nat.prime_of_mem_primesBelow hp).pos
      have hχp : χ (p : ZMod q) = ((χ (p : ZMod q)).re : ℂ) :=
        Complex.ext (by simp) (by simpa using hreal _)
      have hpow : (p : ℂ) ^ (-(σ : ℂ)) = (((p : ℝ) ^ (-σ) : ℝ) : ℂ) := by
        rw [← Complex.ofReal_natCast, show -(σ : ℂ) = ((-σ : ℝ) : ℂ) by push_cast; ring,
          Complex.ofReal_cpow hp_pos.le]
      rw [hχp, hpow]
      push_cast; rfl
    rw [hprod_real, Complex.ofReal_im, Complex.ofReal_re]
    refine ⟨rfl, Finset.prod_pos fun p hp => inv_pos.mpr ?_⟩
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primesBelow hp).two_le
    have hp_pos : (0 : ℝ) < (p : ℝ) := by positivity
    have hp_gt1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
    have hpow_lt1 : (p : ℝ) ^ (-σ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp_gt1 (by linarith)
    have hre_le1 : (χ (p : ZMod q)).re ≤ 1 := by
      have h1 : |(χ (p : ZMod q)).re| ≤ ‖χ (p : ZMod q)‖ := Complex.abs_re_le_norm _
      have h2 : ‖χ (p : ZMod q)‖ ≤ 1 := χ.norm_le_one _
      linarith [(le_abs_self _).trans (h1.trans h2)]
    have hmul_lt1 : (χ (p : ZMod q)).re * (p : ℝ) ^ (-σ) < 1 := by
      have hpow_pos : 0 < (p : ℝ) ^ (-σ) := Real.rpow_pos_of_pos hp_pos _
      calc (χ (p : ZMod q)).re * (p : ℝ) ^ (-σ)
          ≤ 1 * (p : ℝ) ^ (-σ) := mul_le_mul_of_nonneg_right hre_le1 hpow_pos.le
        _ = (p : ℝ) ^ (-σ) := one_mul _
        _ < 1 := hpow_lt1
    linarith
  have hre_ge : 0 ≤ (LFunction χ (σ : ℂ)).re :=
    ge_of_tendsto (Complex.continuous_re.continuousAt.tendsto.comp heuler)
      (Eventually.of_forall fun N => (hfin_pos N).2.le)
  have him_zero : (LFunction χ (σ : ℂ)).im = 0 :=
    tendsto_nhds_unique (Complex.continuous_im.continuousAt.tendsto.comp heuler)
      (tendsto_const_nhds.congr fun N => (hfin_pos N).1.symm)
  have hne : LFunction χ (σ : ℂ) ≠ 0 :=
    Stage2DirichletAP.LFunction_ne_zero_of_one_le_re_bridge χ
      (Or.inr (by intro h1; have := congrArg Complex.re h1; simp at this; linarith))
      (by simpa using hσ.le)
  have hre_ne : (LFunction χ (σ : ℂ)).re ≠ 0 := fun h0 =>
    hne (Complex.ext (by simpa using h0) (by simpa using him_zero))
  exact lt_of_le_of_ne hre_ge hre_ne.symm

theorem LFunction_one_pos_of_real {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (hreal : ∀ a : ZMod q, (χ a).im = 0) :
    0 < (DirichletCharacter.LFunction χ 1).re ∧ (DirichletCharacter.LFunction χ 1).im = 0 := by
  have him : (DirichletCharacter.LFunction χ 1).im = 0 := by
    simpa only [Complex.ofReal_one] using LFunction_im_eq_zero_of_real hχ hreal zero_lt_one
  have hcont : Continuous (fun σ : ℝ => (DirichletCharacter.LFunction χ (σ : ℂ)).re) :=
    Complex.continuous_re.comp ((DirichletCharacter.differentiable_LFunction hχ).continuous.comp
      Complex.continuous_ofReal)
  have hseq_tend : Tendsto (fun n : ℕ => (1 : ℝ) + ((n + 1 : ℕ) : ℝ)⁻¹) atTop (nhds 1) := by
    have hinv : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹) atTop (nhds 0) :=
      (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).comp (tendsto_add_atTop_nat 1)
    simpa only [add_zero] using tendsto_const_nhds.add hinv
  have hre_ge : 0 ≤ (DirichletCharacter.LFunction χ 1).re := by
    have ht := (hcont.tendsto 1).comp hseq_tend
    simp only [Complex.ofReal_one] at ht
    refine ge_of_tendsto ht (Eventually.of_forall fun n => ?_)
    have hgt : (1 : ℝ) < 1 + ((n + 1 : ℕ) : ℝ)⁻¹ := by
      have : (0 : ℝ) < ((n + 1 : ℕ) : ℝ)⁻¹ := inv_pos.mpr (by positivity)
      linarith
    exact (LFunction_re_pos_of_real_of_one_lt hreal hgt).le
  have hne : DirichletCharacter.LFunction χ 1 ≠ 0 :=
    Stage2DirichletAP.LFunction_apply_one_ne_zero_bridge hχ
  have hre_ne : (DirichletCharacter.LFunction χ 1).re ≠ 0 := fun h0 =>
    hne (Complex.ext (by simpa using h0) (by simpa using him))
  exact ⟨lt_of_le_of_ne hre_ge hre_ne.symm, him⟩

end RHDirect.Stage6ClassNumberFormula
end

noncomputable section

open Complex DirichletCharacter Finset RHDirect

open RHDirect.Stage3ZeroFreeRegion RHDirect.Stage5ZetaZeroFree

open RHDirect.Stage5DirichletLZeroFree RHDirect.Stage6ClassNumberFormula

open scoped BigOperators

namespace RHDirect.Stage7SiegelWalfisz

theorem real_char_apply_trichotomy {q : ℕ} {χ : DirichletCharacter ℂ q}
    (hreal : ∀ a : ZMod q, (χ a).im = 0) (a : ZMod q) :
    χ a = 0 ∨ χ a = 1 ∨ χ a = -1 := by
  by_cases hu : IsUnit a
  · right
    have hsq : χ a * χ a = 1 := by
      have h1 : (χ ^ 2) a = (1 : DirichletCharacter ℂ q) a := by
        rw [isRealChar_sq_eq_one hreal]
      rw [sq, MulChar.mul_apply, MulChar.one_apply hu] at h1
      exact h1
    have hfac : (χ a - 1) * (χ a + 1) = 0 := by linear_combination hsq
    rcases mul_eq_zero.mp hfac with h1 | hm1
    · left; exact sub_eq_zero.mp h1
    · right; linear_combination hm1
  · left; exact MulChar.map_nonunit χ hu

private lemma LFunction_landau_setup_real {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {B δ : ℝ} (hB : (q : ℝ) ≤ B) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 4) :
    let σ : ℝ := 1 + δ
    let M : ℝ := 12 * B / δ
    1 ≤ M ∧
    AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) (Metric.closedBall (σ : ℂ) (1 / 2)) ∧
    DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0 ∧
    (∀ z ∈ Metric.closedBall (σ : ℂ) (1 / 2),
      ‖DirichletCharacter.LFunction χ z‖ ≤ M * ‖DirichletCharacter.LFunction χ (σ : ℂ)‖) ∧
    (∀ ρ ∈ Metric.closedBall (σ : ℂ) (1 / 4),
      DirichletCharacter.LFunction χ ρ = 0 → ρ.re ≤ (σ : ℂ).re) := by
  intro σ M
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast NeZero.pos q
  have hB1 : 1 ≤ B := hq1.trans hB
  have hσ1 : 1 < σ := by dsimp only [σ]; linarith
  have hσ2 : σ ≤ 5 / 4 := by dsimp only [σ]; linarith
  have hM_ge1 : 1 ≤ M := by
    dsimp only [M]
    rw [le_div_iff₀ hδ0]
    linarith
  have han : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) (Metric.closedBall (σ : ℂ) (1 / 2)) :=
    (DifferentiableOn.analyticOnNhd
      (fun z _ => (DirichletCharacter.differentiableAt_LFunction χ z (.inr hχ)).differentiableWithinAt)
      isOpen_univ).mono (Set.subset_univ _)
  have hnz : DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ) (by simp [hσ1.le])
  have hbd : ∀ z ∈ Metric.closedBall (σ : ℂ) (1 / 2),
      ‖DirichletCharacter.LFunction χ z‖ ≤ M * ‖DirichletCharacter.LFunction χ (σ : ℂ)‖ := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have hre_diff := abs_le.mp ((Complex.abs_re_le_norm (z - (σ : ℂ))).trans hz)
    have him_diff := abs_le.mp ((Complex.abs_im_le_norm (z - (σ : ℂ))).trans hz)
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im,
      sub_zero] at hre_diff him_diff
    have hz_strip : ‖DirichletCharacter.LFunction χ z‖ ≤ 6 * B := by
      have h := norm_LFunction_strip_le hχ (by linarith : 1 / 2 ≤ z.re) (by linarith : z.re ≤ 2)
      have him_abs : |z.im| ≤ 1 / 2 := abs_le.mpr him_diff
      have hq_nn : (0 : ℝ) ≤ (q : ℝ) := by linarith
      nlinarith
    have hinv : ‖1 / DirichletCharacter.LFunction χ (σ : ℂ)‖ ≤ 2 / δ := by
      have h := (norm_LFunction_and_inv_and_logDeriv_of_one_lt_re χ hσ1 0).2.1
      simp only [Complex.ofReal_zero, mul_zero, add_zero] at h
      have hσ_sub : σ - 1 = δ := by dsimp only [σ]; ring
      rw [hσ_sub] at h
      exact h.trans (div_le_div_of_nonneg_right (by linarith) hδ0.le)
    have h1 : ‖DirichletCharacter.LFunction χ z‖ / ‖DirichletCharacter.LFunction χ (σ : ℂ)‖ ≤ M := by
      rw [← norm_div, show DirichletCharacter.LFunction χ z / DirichletCharacter.LFunction χ (σ : ℂ) =
          DirichletCharacter.LFunction χ z * (1 / DirichletCharacter.LFunction χ (σ : ℂ)) by ring,
        norm_mul]
      calc ‖DirichletCharacter.LFunction χ z‖ * ‖1 / DirichletCharacter.LFunction χ (σ : ℂ)‖
          ≤ (6 * B) * (2 / δ) := mul_le_mul hz_strip hinv (norm_nonneg _) (by positivity)
        _ = M := by dsimp only [M]; ring
    exact (div_le_iff₀ (norm_pos_iff.mpr hnz)).mp h1
  have hzeros : ∀ ρ ∈ Metric.closedBall (σ : ℂ) (1 / 4),
      DirichletCharacter.LFunction χ ρ = 0 → ρ.re ≤ (σ : ℂ).re := by
    intro ρ _ hρ0
    by_contra hgt; push Not at hgt
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ)
      (by simp only [Complex.ofReal_re] at hgt; linarith) hρ0
  exact ⟨hM_ge1, han, hnz, hbd, hzeros⟩

private lemma numerical_page_closing : 59 + 24 * Real.log (12000 : ℝ) < 500 := by
  have h1 := Real.log_le_log (by norm_num : (0 : ℝ) < 12000) (by norm_num : (12000 : ℝ) ≤ 2 ^ 14)
  rw [Real.log_pow] at h1
  norm_num at h1
  have hlog2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  linarith

set_option maxHeartbeats 2000000 in
theorem page_landau_two_distinct_nonprincipal_real_explicit {Q : ℝ} (hQ : 2 ≤ Q)
    {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    {χ₁ : DirichletCharacter ℂ q₁} {χ₂ : DirichletCharacter ℂ q₂}
    (hq1 : (q₁ : ℝ) ≤ Q) (hq2 : (q₂ : ℝ) ≤ Q)
    (hprim1 : χ₁.IsPrimitive) (hprim2 : χ₂.IsPrimitive)
    (h1_ne : χ₁ ≠ 1) (h2_ne : χ₂ ≠ 1)
    (hreal1 : ∀ a, (χ₁ a).im = 0) (hreal2 : ∀ a, (χ₂ a).im = 0)
    (hne : PChar.of χ₁ ≠ PChar.of χ₂)
    {β₁ β₂ : ℝ}
    (hz1 : DirichletCharacter.LFunction χ₁ (β₁ : ℂ) = 0)
    (hz2 : DirichletCharacter.LFunction χ₂ (β₂ : ℂ) = 0) :
    min β₁ β₂ ≤ 1 - 1 / (3000 * Real.log (2 * Q)) := by
  by_contra hgt; push Not at hgt
  have hlog4 : (1.38 : ℝ) < Real.log 4 := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    linarith [Real.log_two_gt_d9]
  set L : ℝ := Real.log (2 * Q)
  have hL : (1.38 : ℝ) < L := lt_of_lt_of_le hlog4 (Real.log_le_log (by norm_num) (by linarith))
  have hL_pos : 0 < L := by linarith
  set δ : ℝ := 1 / (1000 * L)
  have hδ0 : 0 < δ := by positivity
  have hδ_le : δ ≤ 1 / 4 := by
    dsimp only [δ]; rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hδ_small : δ < 1 / 1000 := by
    dsimp only [δ]; rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; linarith
  set σ : ℝ := 1 + δ
  have hσ1 : 1 < σ := by linarith
  have hβ1_lt1 : β₁ < 1 := by
    by_contra h; push Not at h
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ₁ (.inl h1_ne) (by simpa using h) hz1
  have hβ2_lt1 : β₂ < 1 := by
    by_contra h; push Not at h
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ₂ (.inl h2_ne) (by simpa using h) hz2
  set β : ℝ := min β₁ β₂
  have hβ_gt : 1 - δ / 3 < β := by
    have hδ3 : δ / 3 = 1 / (3000 * L) := by dsimp only [δ]; field_simp [hL_pos.ne']; ring
    linarith
  have hσβ1_le : σ - β₁ ≤ 1 / 4 := by
    have : β ≤ β₁ := min_le_left β₁ β₂
    dsimp only [σ]; linarith
  have hσβ2_le : σ - β₂ ≤ 1 / 4 := by
    have : β ≤ β₂ := min_le_right β₁ β₂
    dsimp only [σ]; linarith
  have hβ1_mem : (β₁ : ℂ) ∈ Metric.closedBall (σ : ℂ) (1 / 4) := by
    rw [Metric.mem_closedBall, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_neg (by linarith)]
    linarith
  have hβ2_mem : (β₂ : ℂ) ∈ Metric.closedBall (σ : ℂ) (1 / 4) := by
    rw [Metric.mem_closedBall, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_neg (by linarith)]
    linarith
  
  set ψ₁ : PChar := ⟨q₁, χ₁, hprim1⟩
  set ψ₂ : PChar := ⟨q₂, χ₂, hprim2⟩
  have hψ_ne : ψ₁ ≠ ψ₂ := by
    intro heq
    apply hne
    rw [show PChar.of χ₁ = ψ₁ from PChar.of_self ψ₁,
      show PChar.of χ₂ = ψ₂ from PChar.of_self ψ₂, heq]
  have h12_ne : prodChar χ₁ χ₂ ≠ 1 :=
    prodChar_ne_one_of_distinct_primitive_real (ψ₁ := ψ₁) (ψ₂ := ψ₂) hreal1 hψ_ne
  
  obtain ⟨hM1_ge1, han1, hnz1, hbd1, hzeros1⟩ :=
    LFunction_landau_setup_real h1_ne hq1 hδ0 hδ_le
  obtain ⟨hM2_ge1, han2, hnz2, hbd2, hzeros2⟩ :=
    LFunction_landau_setup_real h2_ne hq2 hδ0 hδ_le
  have hq12 : ((q₁ * q₂ : ℕ) : ℝ) ≤ Q ^ 2 := by
    push_cast
    have hq1_nn : (0 : ℝ) ≤ (q₁ : ℝ) := Nat.cast_nonneg q₁
    have hq2_nn : (0 : ℝ) ≤ (q₂ : ℝ) := Nat.cast_nonneg q₂
    nlinarith
  obtain ⟨hM12_ge1, han12, hnz12, hbd12, hzeros12⟩ :=
    LFunction_landau_setup_real h12_ne hq12 hδ0 hδ_le
  set M₁ : ℝ := 12 * Q / δ
  set M₁₂ : ℝ := 12 * Q ^ 2 / δ
  have hlandau1 := landau_negLogDeriv_le_one_zero (r := 1 / 4) (R := 1 / 2)
    (by norm_num) (by norm_num) hM1_ge1 han1 hnz1 hbd1 hzeros1 hβ1_mem hz1
  have hlandau2 := landau_negLogDeriv_le_one_zero (r := 1 / 4) (R := 1 / 2)
    (by norm_num) (by norm_num) hM2_ge1 han2 hnz2 hbd2 hzeros2 hβ2_mem hz2
  have hlandau12 := landau_negLogDeriv_le (r := 1 / 4) (R := 1 / 2)
    (by norm_num) (by norm_num) hM12_ge1 han12 hnz12 hbd12 hzeros12
  have hre_inv1 : (1 / ((σ : ℂ) - (β₁ : ℂ))).re = 1 / (σ - β₁) := by
    rw [← Complex.ofReal_sub, ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
  have hre_inv2 : (1 / ((σ : ℂ) - (β₂ : ℂ))).re = 1 / (σ - β₂) := by
    rw [← Complex.ofReal_sub, ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
  have herr1 : ((σ : ℂ) - (β₁ : ℂ)).re / (1 / 2 : ℝ) ^ 2 ≤ 1 := by
    simp only [Complex.sub_re, Complex.ofReal_re]; norm_num; linarith
  have herr2 : ((σ : ℂ) - (β₂ : ℂ)).re / (1 / 2 : ℝ) ^ 2 ≤ 1 := by
    simp only [Complex.sub_re, Complex.ofReal_re]; norm_num; linarith
  have h8 : (2 : ℝ) / (1 / 4) = 8 := by norm_num
  have hbound1 : (negLogDerivL χ₁ (σ : ℂ)).re ≤ 8 * Real.log M₁ + 1 - 1 / (σ - β₁) := by
    unfold negLogDerivL; rw [hre_inv1, h8] at hlandau1; linarith
  have hbound2 : (negLogDerivL χ₂ (σ : ℂ)).re ≤ 8 * Real.log M₁ + 1 - 1 / (σ - β₂) := by
    unfold negLogDerivL; rw [hre_inv2, h8] at hlandau2; linarith
  have hbound12 : (negLogDerivL (prodChar χ₁ χ₂) (σ : ℂ)).re ≤ 8 * Real.log M₁₂ := by
    unfold negLogDerivL; rwa [h8] at hlandau12
  have hboundZ : (negLogDerivZeta (σ : ℂ)).re ≤ 1 / δ + 1 := by
    have h := negLogDerivZeta_real_le hσ1
    have hσ_sub : σ - 1 = δ := by dsimp only [σ]; ring
    rwa [hσ_sub] at h
  
  have hpos := four_char_real_negLogDeriv_re_nonneg hreal1 hreal2 hσ1
  
  have hL_le_2Q : L ≤ 2 * Q := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hlogM1 : Real.log M₁ ≤ Real.log 12000 + 2 * L := by
    have hM1_eq : M₁ = 12000 * Q * L := by dsimp only [M₁, δ]; field_simp [hL_pos.ne']; ring
    have hM1_le : M₁ ≤ 12000 * (2 * Q) ^ 2 := by rw [hM1_eq]; nlinarith
    calc Real.log M₁ ≤ Real.log (12000 * (2 * Q) ^ 2) := Real.log_le_log (by linarith) hM1_le
      _ = Real.log 12000 + Real.log ((2 * Q) ^ 2) := Real.log_mul (by norm_num) (by positivity)
      _ = Real.log 12000 + 2 * L := by rw [Real.log_pow]; push_cast; rfl
  have hlogM12 : Real.log M₁₂ ≤ Real.log 12000 + 3 * L := by
    have hM12_eq : M₁₂ = 12000 * Q ^ 2 * L := by dsimp only [M₁₂, δ]; field_simp [hL_pos.ne']; ring
    have hM12_le : M₁₂ ≤ 12000 * (2 * Q) ^ 3 := by rw [hM12_eq]; nlinarith [sq_nonneg Q]
    calc Real.log M₁₂ ≤ Real.log (12000 * (2 * Q) ^ 3) := Real.log_le_log (by linarith) hM12_le
      _ = Real.log 12000 + Real.log ((2 * Q) ^ 3) := Real.log_mul (by norm_num) (by positivity)
      _ = Real.log 12000 + 3 * L := by rw [Real.log_pow]; push_cast; rfl
  
  have herr_tot : 3 + 16 * Real.log M₁ + 8 * Real.log M₁₂ < 1 / (2 * δ) := by
    have h500 : 500 * L = 1 / (2 * δ) := by dsimp only [δ]; field_simp [hL_pos.ne']; ring
    have hlog_nn : 0 ≤ Real.log (12000 : ℝ) := Real.log_nonneg (by norm_num)
    have hcomb : 3 + 16 * Real.log M₁ + 8 * Real.log M₁₂ ≤ (59 + 24 * Real.log 12000) * L := by
      nlinarith
    have hlt := mul_lt_mul_of_pos_right numerical_page_closing hL_pos
    linarith
  have hd1 : 1 / (σ - β) ≤ 1 / (σ - β₁) :=
    one_div_le_one_div_of_le (by linarith) (by linarith [min_le_left β₁ β₂])
  have hd2 : 1 / (σ - β) ≤ 1 / (σ - β₂) :=
    one_div_le_one_div_of_le (by linarith) (by linarith [min_le_right β₁ β₂])
  have hineq : 2 / (σ - β) < 3 / (2 * δ) := by
    have h2 : 2 / (σ - β) = 1 / (σ - β) + 1 / (σ - β) := by ring
    have h32 : 1 / δ + 1 / (2 * δ) = 3 / (2 * δ) := by field_simp [hδ0.ne']; ring
    linarith
  have hσβ_pos : 0 < σ - β := by
    have : β < 1 := lt_of_le_of_lt (min_le_left β₁ β₂) hβ1_lt1
    linarith
  have hmul := (div_lt_div_iff₀ hσβ_pos (by positivity : (0 : ℝ) < 2 * δ)).mp hineq
  have hβ_lt : β < 1 - δ / 3 := by dsimp only [σ] at hmul; linarith
  linarith

end RHDirect.Stage7SiegelWalfisz
end

noncomputable section

open Complex DirichletCharacter Finset MeasureTheory Set Filter Topology RHDirect

open RHDirect.Stage3RealAnalyticLandau RHDirect.Stage3ZeroFreeRegion

open RHDirect.Stage5ZetaZeroFree RHDirect.Stage5DirichletLZeroFree

open RHDirect.Stage6EffectivePNT RHDirect.Stage6ClassNumberFormula

open RHDirect.Stage7SiegelWalfisz

open scoped BigOperators

namespace RHDirect.Stage9LandauSiegel

def dirConv (f g : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ n.divisorsAntidiagonal, f p.1 * g p.2

def seqConv (u v : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), u i * v (k - i)

theorem dirConv_zero (f g : ℕ → ℝ) : dirConv f g 0 = 0 := by
  simp [dirConv]

theorem dirConv_one (f g : ℕ → ℝ) : dirConv f g 1 = f 1 * g 1 := by
  simp [dirConv]

theorem dirConv_cast_complex (f g : ℕ → ℝ) (n : ℕ) :
    (dirConv f g n : ℂ) =
      LSeries.convolution (fun m => (f m : ℂ)) (fun m => (g m : ℂ)) n := by
  rw [dirConv, LSeries.convolution_def, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  push_cast; rfl

theorem seqConv_comm (u v : ℕ → ℝ) (k : ℕ) : seqConv u v k = seqConv v u k := by
  unfold seqConv
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have h1 : k + 1 - 1 - i = k - i := by omega
  have h2 : k - (k - i) = i := by omega
  rw [h1, h2, mul_comm]

theorem seqConv_assoc (u v w : ℕ → ℝ) (k : ℕ) :
    seqConv (seqConv u v) w k = seqConv u (seqConv v w) k := by
  unfold seqConv
  have hL :
      ∑ i ∈ Finset.range (k + 1), (∑ j ∈ Finset.range (i + 1), u j * v (i - j)) * w (k - i) =
        ∑ p ∈ (Finset.range (k + 1) ×ˢ Finset.range (k + 1)).filter (fun p => p.1 + p.2 ≤ k),
          u p.1 * v p.2 * w (k - (p.1 + p.2)) := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_sigma']
    refine Finset.sum_nbij'
      (fun x : Σ _ : ℕ, ℕ => (x.2, x.1 - x.2))
      (fun p : ℕ × ℕ => ⟨p.1 + p.2, p.1⟩)
      ?_ ?_ ?_ ?_ ?_
    · intro x hx
      rcases x with ⟨i, j⟩
      simp only [Finset.mem_sigma, Finset.mem_range] at hx
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      omega
    · intro p hp
      rcases p with ⟨a, b⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
      simp only [Finset.mem_sigma, Finset.mem_range]
      omega
    · intro x hx
      rcases x with ⟨i, j⟩
      simp only [Finset.mem_sigma, Finset.mem_range] at hx
      exact Sigma.ext (by dsimp only; omega) (heq_of_eq (by dsimp only))
    · intro p hp
      rcases p with ⟨a, b⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
      exact Prod.ext rfl (by dsimp only; omega)
    · intro x hx
      rcases x with ⟨i, j⟩
      simp only [Finset.mem_sigma, Finset.mem_range] at hx
      have h1 : j + (i - j) = i := by omega
      dsimp only
      rw [h1]
  have hR :
      ∑ j ∈ Finset.range (k + 1), u j * ∑ m ∈ Finset.range (k - j + 1), v m * w (k - j - m) =
        ∑ p ∈ (Finset.range (k + 1) ×ˢ Finset.range (k + 1)).filter (fun p => p.1 + p.2 ≤ k),
          u p.1 * v p.2 * w (k - (p.1 + p.2)) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_sigma']
    refine Finset.sum_nbij'
      (fun x : Σ _ : ℕ, ℕ => (x.1, x.2))
      (fun p : ℕ × ℕ => ⟨p.1, p.2⟩)
      ?_ ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_sigma, Finset.mem_range] at hx
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      omega
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
      simp only [Finset.mem_sigma, Finset.mem_range]
      omega
    · intro _ _; rfl
    · intro _ _; rfl
    · intro x _
      dsimp only
      rw [Nat.sub_sub, mul_assoc]
  rw [hL, hR]

theorem seqConv_zero_pow (u : ℕ → ℝ) (k : ℕ) :
    seqConv u (fun i => (0 : ℝ) ^ i) k = u k := by
  unfold seqConv
  rw [Finset.sum_eq_single k]
  · simp
  · intro i hi hne
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hpos : k - i ≠ 0 := by omega
    dsimp only
    rw [zero_pow hpos, mul_zero]
  · intro hk
    exfalso; exact hk (Finset.mem_range.mpr (Nat.lt_succ_self k))

theorem seqConv_one_neg_one (k : ℕ) :
    seqConv (fun _ => (1 : ℝ)) (fun i => (-1 : ℝ) ^ i) k = if _root_.Even k then 1 else 0 := by
  induction k with
  | zero => simp [seqConv]
  | succ k ih =>
    unfold seqConv at ih ⊢
    rw [Finset.sum_range_succ']
    have hshift :
        ∑ i ∈ Finset.range (k + 1), (1 : ℝ) * (-1 : ℝ) ^ (k + 1 - (i + 1)) =
          ∑ i ∈ Finset.range (k + 1), (1 : ℝ) * (-1 : ℝ) ^ (k - i) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      have : k + 1 - (i + 1) = k - i := by omega
      rw [this]
    rw [hshift, ih, Nat.sub_zero, one_mul]
    by_cases hk : _root_.Even k
    · have hne : ¬ _root_.Even (k + 1) := by
        obtain ⟨m, rfl⟩ := hk; intro ⟨r, hr⟩; omega
      dsimp only
      rw [if_pos hk, if_neg hne, show (-1 : ℝ) ^ (k + 1) = -1 by
        obtain ⟨m, rfl⟩ := hk; rw [pow_succ, ← two_mul, pow_mul]; norm_num]
      ring
    · have hev : _root_.Even (k + 1) := by
        rcases Nat.even_or_odd k with h | ⟨m, rfl⟩
        · exact absurd h hk
        · exact ⟨m + 1, by omega⟩
      dsimp only
      rw [if_neg hk, if_pos hev, show (-1 : ℝ) ^ (k + 1) = 1 by
        obtain ⟨m, hm⟩ := hev; rw [hm, ← two_mul, pow_mul]; norm_num]
      ring

theorem seqConv_nonneg {u v : ℕ → ℝ} (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i) (k : ℕ) :
    0 ≤ seqConv u v k :=
  Finset.sum_nonneg fun i _ => mul_nonneg (hu i) (hv (k - i))

theorem seqConv_ge_term {u v : ℕ → ℝ} (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i) {i k : ℕ}
    (hik : i ≤ k) : u i * v (k - i) ≤ seqConv u v k :=
  Finset.single_le_sum (f := fun j => u j * v (k - j))
    (fun j _ => mul_nonneg (hu j) (hv (k - j))) (Finset.mem_range.mpr (Nat.lt_succ_of_le hik))

theorem dirConv_mul_coprime {f g : ℕ → ℝ}
    (hf : ∀ a b : ℕ, Nat.Coprime a b → f (a * b) = f a * f b)
    (hg : ∀ a b : ℕ, Nat.Coprime a b → g (a * b) = g a * g b)
    {m n : ℕ} (hcop : Nat.Coprime m n) :
    dirConv f g (m * n) = dirConv f g m * dirConv f g n := by
  rcases eq_or_ne m 0 with rfl | hm0
  · simp [dirConv]
  rcases eq_or_ne n 0 with rfl | hn0
  · simp [dirConv]
  unfold dirConv
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  refine Finset.sum_nbij'
    (fun p : ℕ × ℕ => ((Nat.gcd p.1 m, Nat.gcd p.2 m), (Nat.gcd p.1 n, Nat.gcd p.2 n)))
    (fun q : (ℕ × ℕ) × (ℕ × ℕ) => (q.1.1 * q.2.1, q.1.2 * q.2.2))
    ?_ ?_ ?_ ?_ ?_
  · intro p hp
    rcases Nat.mem_divisorsAntidiagonal.mp hp with ⟨hpmul, _⟩
    simp only [Finset.mem_product, Nat.mem_divisorsAntidiagonal]
    have h1 : p.1 ∣ m * n := ⟨p.2, hpmul.symm⟩
    have h2 : p.2 ∣ m * n := ⟨p.1, by linarith⟩
    have hd1 : Nat.gcd p.1 m * Nat.gcd p.1 n = p.1 := by
      rw [← Nat.Coprime.gcd_mul p.1 hcop, Nat.gcd_eq_left h1]
    have hd2 : Nat.gcd p.2 m * Nat.gcd p.2 n = p.2 := by
      rw [← Nat.Coprime.gcd_mul p.2 hcop, Nat.gcd_eq_left h2]
    have hmul_all :
        (Nat.gcd p.1 m * Nat.gcd p.2 m) * (Nat.gcd p.1 n * Nat.gcd p.2 n) = m * n := by
      calc (Nat.gcd p.1 m * Nat.gcd p.2 m) * (Nat.gcd p.1 n * Nat.gcd p.2 n)
          = (Nat.gcd p.1 m * Nat.gcd p.1 n) * (Nat.gcd p.2 m * Nat.gcd p.2 n) := by ring
        _ = p.1 * p.2 := by rw [hd1, hd2]
        _ = m * n := hpmul
    have hm_eq : Nat.gcd p.1 m * Nat.gcd p.2 m = m := by
      have hm_dvd : m ∣ Nat.gcd p.1 m * Nat.gcd p.2 m := by
        have hcop_mn : Nat.Coprime m (Nat.gcd p.1 n * Nat.gcd p.2 n) :=
          (hcop.coprime_dvd_right (Nat.gcd_dvd_right _ _)).mul_right
            (hcop.coprime_dvd_right (Nat.gcd_dvd_right _ _))
        exact hcop_mn.dvd_of_dvd_mul_right (hmul_all ▸ dvd_mul_right m n)
      have hprod_dvd : Nat.gcd p.1 m * Nat.gcd p.2 m ∣ m := by
        have hcop_pn : Nat.Coprime (Nat.gcd p.1 m * Nat.gcd p.2 m) n :=
          (hcop.coprime_dvd_left (Nat.gcd_dvd_right _ _)).mul_left
            (hcop.coprime_dvd_left (Nat.gcd_dvd_right _ _))
        exact hcop_pn.dvd_of_dvd_mul_right (hmul_all.symm ▸ dvd_mul_right _ _)
      exact Nat.dvd_antisymm hprod_dvd hm_dvd
    have hn_eq : Nat.gcd p.1 n * Nat.gcd p.2 n = n := by
      have hmul_m : m * (Nat.gcd p.1 n * Nat.gcd p.2 n) = m * n := by
        calc m * (Nat.gcd p.1 n * Nat.gcd p.2 n)
            = (Nat.gcd p.1 m * Nat.gcd p.2 m) * (Nat.gcd p.1 n * Nat.gcd p.2 n) := by rw [hm_eq]
          _ = m * n := hmul_all
      exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hm0) hmul_m
    exact ⟨⟨hm_eq, hm0⟩, ⟨hn_eq, hn0⟩⟩
  · intro q hq
    simp only [Finset.mem_product, Nat.mem_divisorsAntidiagonal] at hq
    rw [Nat.mem_divisorsAntidiagonal]
    refine ⟨?_, mul_ne_zero hm0 hn0⟩
    calc q.1.1 * q.2.1 * (q.1.2 * q.2.2)
        = (q.1.1 * q.1.2) * (q.2.1 * q.2.2) := by ring
      _ = m * n := by rw [hq.1.1, hq.2.1]
  · intro p hp
    rcases Nat.mem_divisorsAntidiagonal.mp hp with ⟨hpmul, _⟩
    have h1 : p.1 ∣ m * n := ⟨p.2, hpmul.symm⟩
    have h2 : p.2 ∣ m * n := ⟨p.1, by linarith⟩
    ext
    · dsimp only
      rw [← Nat.Coprime.gcd_mul p.1 hcop, Nat.gcd_eq_left h1]
    · dsimp only
      rw [← Nat.Coprime.gcd_mul p.2 hcop, Nat.gcd_eq_left h2]
  · intro q hq
    simp only [Finset.mem_product, Nat.mem_divisorsAntidiagonal] at hq
    have hd11 : q.1.1 ∣ m := ⟨q.1.2, hq.1.1.symm⟩
    have hd12 : q.1.2 ∣ m := ⟨q.1.1, by linarith⟩
    have hd21 : q.2.1 ∣ n := ⟨q.2.2, hq.2.1.symm⟩
    have hd22 : q.2.2 ∣ n := ⟨q.2.1, by linarith⟩
    have hc1 : Nat.Coprime q.2.1 m := hcop.symm.coprime_dvd_left hd21
    have hc2 : Nat.Coprime q.2.2 m := hcop.symm.coprime_dvd_left hd22
    have hc3 : Nat.Coprime q.1.1 n := hcop.coprime_dvd_left hd11
    have hc4 : Nat.Coprime q.1.2 n := hcop.coprime_dvd_left hd12
    ext <;> dsimp only
    · rw [hc1.gcd_mul_right_cancel, Nat.gcd_eq_left hd11]
    · rw [hc2.gcd_mul_right_cancel, Nat.gcd_eq_left hd12]
    · rw [hc3.gcd_mul_left_cancel, Nat.gcd_eq_left hd21]
    · rw [hc4.gcd_mul_left_cancel, Nat.gcd_eq_left hd22]
  · intro p hp
    rcases Nat.mem_divisorsAntidiagonal.mp hp with ⟨hpmul, _⟩
    have h1 : p.1 ∣ m * n := ⟨p.2, hpmul.symm⟩
    have h2 : p.2 ∣ m * n := ⟨p.1, by linarith⟩
    have hd1 : Nat.gcd p.1 m * Nat.gcd p.1 n = p.1 := by
      rw [← Nat.Coprime.gcd_mul p.1 hcop, Nat.gcd_eq_left h1]
    have hd2 : Nat.gcd p.2 m * Nat.gcd p.2 n = p.2 := by
      rw [← Nat.Coprime.gcd_mul p.2 hcop, Nat.gcd_eq_left h2]
    have hc1 : Nat.Coprime (Nat.gcd p.1 m) (Nat.gcd p.1 n) :=
      (hcop.coprime_dvd_left (Nat.gcd_dvd_right _ _)).coprime_dvd_right (Nat.gcd_dvd_right _ _)
    have hc2 : Nat.Coprime (Nat.gcd p.2 m) (Nat.gcd p.2 n) :=
      (hcop.coprime_dvd_left (Nat.gcd_dvd_right _ _)).coprime_dvd_right (Nat.gcd_dvd_right _ _)
    dsimp only
    calc f p.1 * g p.2
        = f (Nat.gcd p.1 m * Nat.gcd p.1 n) * g (Nat.gcd p.2 m * Nat.gcd p.2 n) := by
          rw [hd1, hd2]
      _ = (f (Nat.gcd p.1 m) * f (Nat.gcd p.1 n)) * (g (Nat.gcd p.2 m) * g (Nat.gcd p.2 n)) := by
          rw [hf _ _ hc1, hg _ _ hc2]
      _ = f (Nat.gcd p.1 m) * g (Nat.gcd p.2 m) * (f (Nat.gcd p.1 n) * g (Nat.gcd p.2 n)) := by
          ring

theorem dirConv_prime_pow (f g : ℕ → ℝ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    dirConv f g (p ^ k) = seqConv (fun i => f (p ^ i)) (fun i => g (p ^ i)) k := by
  unfold dirConv seqConv
  refine Finset.sum_nbij'
    (fun q : ℕ × ℕ => q.1.factorization p)
    (fun i : ℕ => (p ^ i, p ^ (k - i)))
    ?_ ?_ ?_ ?_ ?_
  · intro q hq
    rcases Nat.mem_divisorsAntidiagonal.mp hq with ⟨hqmul, hpk0⟩
    have hd : q.1 ∣ p ^ k := ⟨q.2, hqmul.symm⟩
    obtain ⟨i, hik, hi⟩ := (Nat.dvd_prime_pow hp).mp hd
    rw [hi, hp.factorization_pow, Finsupp.single_eq_same]
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hik)
  · intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [Nat.mem_divisorsAntidiagonal]
    refine ⟨?_, pow_ne_zero k hp.ne_zero⟩
    rw [← pow_add, Nat.add_sub_of_le hik]
  · intro q hq
    rcases Nat.mem_divisorsAntidiagonal.mp hq with ⟨hqmul, _⟩
    have hd : q.1 ∣ p ^ k := ⟨q.2, hqmul.symm⟩
    obtain ⟨i, hik, hi⟩ := (Nat.dvd_prime_pow hp).mp hd
    have hfac : q.1.factorization p = i := by
      rw [hi, hp.factorization_pow, Finsupp.single_eq_same]
    rw [hfac]
    ext
    · exact hi.symm
    · dsimp only
      have hmul : p ^ i * q.2 = p ^ i * p ^ (k - i) := by
        calc p ^ i * q.2 = q.1 * q.2 := by rw [hi]
          _ = p ^ k := hqmul
          _ = p ^ (i + (k - i)) := by rw [Nat.add_sub_of_le hik]
          _ = p ^ i * p ^ (k - i) := pow_add p i (k - i)
      exact (Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos i) hmul).symm
  · intro i _
    dsimp only
    rw [hp.factorization_pow, Finsupp.single_eq_same]
  · intro q hq
    rcases Nat.mem_divisorsAntidiagonal.mp hq with ⟨hqmul, _⟩
    have hd : q.1 ∣ p ^ k := ⟨q.2, hqmul.symm⟩
    obtain ⟨i, hik, hi⟩ := (Nat.dvd_prime_pow hp).mp hd
    have hfac : q.1.factorization p = i := by
      rw [hi, hp.factorization_pow, Finsupp.single_eq_same]
    have hq2 : q.2 = p ^ (k - i) := by
      have hmul : p ^ i * q.2 = p ^ i * p ^ (k - i) := by
        calc p ^ i * q.2 = q.1 * q.2 := by rw [hi]
          _ = p ^ k := hqmul
          _ = p ^ (i + (k - i)) := by rw [Nat.add_sub_of_le hik]
          _ = p ^ i * p ^ (k - i) := pow_add p i (k - i)
      exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos i) hmul
    rw [hfac, hi, hq2]

theorem nonneg_of_mul_coprime {f : ℕ → ℝ} (hf0 : f 0 = 0) (hf1 : 0 ≤ f 1)
    (hmul : ∀ a b : ℕ, Nat.Coprime a b → f (a * b) = f a * f b)
    (hpp : ∀ p k : ℕ, p.Prime → 0 ≤ f (p ^ k)) : ∀ n : ℕ, 0 ≤ f n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rcases eq_or_ne n 0 with rfl | hn0
    · linarith
    rcases eq_or_ne n 1 with rfl | hn1
    · exact hf1
    set p : ℕ := n.minFac
    have hp : p.Prime := Nat.minFac_prime hn1
    set k : ℕ := n.factorization p
    have hpk_dvd : p ^ k ∣ n := Nat.ordProj_dvd n p
    have hk_pos : 1 ≤ k := (hp.dvd_iff_one_le_factorization hn0).mp (Nat.minFac_dvd n)
    have hpk_gt1 : 1 < p ^ k := one_lt_pow₀ hp.one_lt (by omega)
    set m : ℕ := n / p ^ k
    have hn_eq : p ^ k * m = n := Nat.mul_div_cancel' hpk_dvd
    have hm_lt : m < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn0) hpk_gt1
    have hcop : Nat.Coprime (p ^ k) m :=
      (Nat.coprime_ordCompl hp hn0).pow_left k
    rw [← hn_eq, hmul (p ^ k) m hcop]
    exact mul_nonneg (hpp p k hp) (ih m hm_lt)

def realCharFn {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) : ℝ :=
  (χ (n : ZMod q)).re

theorem realCharFn_one {q : ℕ} (χ : DirichletCharacter ℂ q) : realCharFn χ 1 = 1 := by
  simp [realCharFn]

theorem realCharFn_mul {q : ℕ} {χ : DirichletCharacter ℂ q} (hreal : IsRealChar χ) (a b : ℕ) :
    realCharFn χ (a * b) = realCharFn χ a * realCharFn χ b := by
  unfold realCharFn
  rw [Nat.cast_mul, map_mul, Complex.mul_re, hreal, hreal, mul_zero, sub_zero]

theorem realCharFn_pow {q : ℕ} {χ : DirichletCharacter ℂ q} (hreal : IsRealChar χ) (p i : ℕ) :
    realCharFn χ (p ^ i) = (realCharFn χ p) ^ i := by
  induction i with
  | zero => simp [realCharFn_one]
  | succ i ih => rw [pow_succ, pow_succ, realCharFn_mul hreal, ih]

theorem realCharFn_trichotomy {q : ℕ} {χ : DirichletCharacter ℂ q} (hreal : IsRealChar χ)
    (n : ℕ) : realCharFn χ n = 0 ∨ realCharFn χ n = 1 ∨ realCharFn χ n = -1 := by
  unfold realCharFn
  rcases real_char_apply_trichotomy hreal (n : ZMod q) with h | h | h <;> simp [h]

theorem realCharFn_cast_complex {q : ℕ} {χ : DirichletCharacter ℂ q} (hreal : IsRealChar χ)
    (n : ℕ) : (realCharFn χ n : ℂ) = χ (n : ZMod q) :=
  Complex.ext (by simp [realCharFn]) (by simp only [Complex.ofReal_im]; exact (hreal _).symm)

def divisorCharSum {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) : ℝ :=
  dirConv (fun _ => 1) (realCharFn χ) n

theorem divisorCharSum_zero {q : ℕ} (χ : DirichletCharacter ℂ q) :
    divisorCharSum χ 0 = 0 := dirConv_zero _ _

theorem divisorCharSum_one {q : ℕ} (χ : DirichletCharacter ℂ q) :
    divisorCharSum χ 1 = 1 := by
  rw [divisorCharSum, dirConv_one, realCharFn_one, one_mul]

theorem divisorCharSum_mul_coprime {q : ℕ} {χ : DirichletCharacter ℂ q} (hreal : IsRealChar χ)
    {m n : ℕ} (hcop : Nat.Coprime m n) :
    divisorCharSum χ (m * n) = divisorCharSum χ m * divisorCharSum χ n :=
  dirConv_mul_coprime (fun _ _ _ => (one_mul 1).symm) (fun a b _ => realCharFn_mul hreal a b) hcop

theorem divisorCharSum_prime_pow_nonneg_and_even {q : ℕ} {χ : DirichletCharacter ℂ q}
    (hreal : IsRealChar χ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    0 ≤ divisorCharSum χ (p ^ k) ∧ (_root_.Even k → 1 ≤ divisorCharSum χ (p ^ k)) := by
  rw [divisorCharSum, dirConv_prime_pow _ _ hp k]
  have hfn : (fun i => realCharFn χ (p ^ i)) = fun i => (realCharFn χ p) ^ i :=
    funext fun i => realCharFn_pow hreal p i
  rw [hfn]
  rcases realCharFn_trichotomy hreal p with h0 | h1 | hm1
  · rw [h0, seqConv_zero_pow]; exact ⟨zero_le_one, fun _ => le_rfl⟩
  · rw [h1]
    have hge : 1 ≤ seqConv (fun _ => (1 : ℝ)) (fun i => (1 : ℝ) ^ i) k := by
      have h0' := seqConv_ge_term (u := fun _ => (1 : ℝ)) (v := fun i => (1 : ℝ) ^ i)
        (fun _ => zero_le_one) (fun _ => by simp) (Nat.zero_le k)
      simpa using h0'
    exact ⟨zero_le_one.trans hge, fun _ => hge⟩
  · rw [hm1, seqConv_one_neg_one]
    by_cases hk : _root_.Even k
    · simp [hk]
    · simp [hk]

theorem divisorCharSum_nonneg {q : ℕ} {χ : DirichletCharacter ℂ q} (hreal : IsRealChar χ)
    (n : ℕ) : 0 ≤ divisorCharSum χ n :=
  nonneg_of_mul_coprime (divisorCharSum_zero χ) (by rw [divisorCharSum_one]; exact zero_le_one)
    (fun _ _ hc => divisorCharSum_mul_coprime hreal hc)
    (fun _ k hp => (divisorCharSum_prime_pow_nonneg_and_even hreal hp k).1) n

theorem LSeries_divisorCharSum_eq {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hreal : IsRealChar χ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (divisorCharSum χ n : ℂ)) s ∧
    dirSeries (divisorCharSum χ) s = riemannZeta s * DirichletCharacter.LFunction χ s := by
  have hsum1 : LSeriesSummable (1 : ℕ → ℂ) s := LSeriesSummable_one_iff.mpr hs
  have hsumχ : LSeriesSummable (fun n : ℕ => χ (n : ZMod q)) s :=
    DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs
  have hconv_eq :
      (fun n : ℕ => (divisorCharSum χ n : ℂ)) =
        LSeries.convolution (1 : ℕ → ℂ) (fun n : ℕ => χ (n : ZMod q)) := by
    funext n
    have h1 : (fun _ : ℕ => ((1 : ℝ) : ℂ)) = (1 : ℕ → ℂ) := by funext _; simp
    have h2 : (fun m : ℕ => (realCharFn χ m : ℂ)) = fun m : ℕ => χ (m : ZMod q) :=
      funext (realCharFn_cast_complex hreal)
    rw [divisorCharSum, dirConv_cast_complex, h1, h2]
  refine ⟨?_, ?_⟩
  · rw [hconv_eq]; exact hsum1.convolution hsumχ
  · rw [dirSeries_eq_LSeries, hconv_eq, LSeries_convolution' hsum1 hsumχ,
      LSeries_one_eq_riemannZeta hs, DirichletCharacter.LFunction_eq_LSeries χ hs]

def fourCharCoeff {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂) (n : ℕ) : ℝ :=
  dirConv (divisorCharSum χ₁) (dirConv (realCharFn χ₂) (realCharFn (prodChar χ₁ χ₂))) n

theorem fourCharCoeff_zero {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂) :
    fourCharCoeff χ₁ χ₂ 0 = 0 := dirConv_zero _ _

theorem fourCharCoeff_one {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂) :
    fourCharCoeff χ₁ χ₂ 1 = 1 := by
  rw [fourCharCoeff, dirConv_one, divisorCharSum_one, dirConv_one, realCharFn_one, realCharFn_one]
  ring

theorem isRealChar_prodChar {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    {χ₁ : DirichletCharacter ℂ q₁} {χ₂ : DirichletCharacter ℂ q₂}
    (h1 : IsRealChar χ₁) (h2 : IsRealChar χ₂) : IsRealChar (prodChar χ₁ χ₂) := by
  intro a
  have ha : ((a.val : ℕ) : ZMod (q₁ * q₂)) = a := ZMod.natCast_zmod_val a
  rw [← ha, prodChar_apply_nat, Complex.mul_im, h1, h2]
  ring

theorem realCharFn_prodChar {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    {χ₁ : DirichletCharacter ℂ q₁} {χ₂ : DirichletCharacter ℂ q₂}
    (h1 : IsRealChar χ₁) (h2 : IsRealChar χ₂) (n : ℕ) :
    realCharFn (prodChar χ₁ χ₂) n = realCharFn χ₁ n * realCharFn χ₂ n := by
  unfold realCharFn
  rw [prodChar_apply_nat, Complex.mul_re, h1, h2]
  ring

theorem fourCharCoeff_mul_coprime {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    {χ₁ : DirichletCharacter ℂ q₁} {χ₂ : DirichletCharacter ℂ q₂}
    (h1 : IsRealChar χ₁) (h2 : IsRealChar χ₂) {m n : ℕ} (hcop : Nat.Coprime m n) :
    fourCharCoeff χ₁ χ₂ (m * n) = fourCharCoeff χ₁ χ₂ m * fourCharCoeff χ₁ χ₂ n := by
  have h12 : IsRealChar (prodChar χ₁ χ₂) := isRealChar_prodChar h1 h2
  exact dirConv_mul_coprime
    (fun _ _ hc => divisorCharSum_mul_coprime h1 hc)
    (fun _ _ hc => dirConv_mul_coprime (fun a b _ => realCharFn_mul h2 a b)
      (fun a b _ => realCharFn_mul h12 a b) hc) hcop

private lemma fourChar_seqConv_nonneg_and_even (α β : ℝ)
    (hα : α = 0 ∨ α = 1 ∨ α = -1) (hβ : β = 0 ∨ β = 1 ∨ β = -1) (k : ℕ) :
    let u := seqConv (seqConv (fun _ => (1 : ℝ)) (fun i => α ^ i))
      (seqConv (fun i => β ^ i) (fun i => (α * β) ^ i))
    0 ≤ u k ∧ (_root_.Even k → 1 ≤ u k) := by
  intro u
  have hpos_ge1 : ∀ (a b : ℕ → ℝ), (∀ i, 0 ≤ a i) → (∀ i, 0 ≤ b i) →
      (∀ j, _root_.Even j → 1 ≤ a j) → (∀ j, _root_.Even j → 1 ≤ b j) →
      0 ≤ seqConv a b k ∧ (_root_.Even k → 1 ≤ seqConv a b k) := by
    intro a b ha hb ha1 hb1
    refine ⟨seqConv_nonneg ha hb k, fun hk => ?_⟩
    have h0 := seqConv_ge_term ha hb (Nat.zero_le k)
    rw [Nat.sub_zero] at h0
    have h1 : 1 ≤ a 0 := ha1 0 ⟨0, rfl⟩
    have h2 : 1 ≤ b k := hb1 k hk
    nlinarith
  have h1_m1 : ∀ i, 0 ≤ seqConv (fun _ => (1 : ℝ)) (fun j => (-1 : ℝ) ^ j) i := fun i => by
    rw [seqConv_one_neg_one]; split_ifs <;> norm_num
  have h1_m1_ev : ∀ j, _root_.Even j → 1 ≤ seqConv (fun _ => (1 : ℝ)) (fun i => (-1 : ℝ) ^ i) j := fun j hj => by
    rw [seqConv_one_neg_one, if_pos hj]
  have h1_1 : ∀ i, 0 ≤ seqConv (fun _ => (1 : ℝ)) (fun j => (1 : ℝ) ^ j) i := fun i =>
    seqConv_nonneg (fun _ => zero_le_one) (fun _ => by simp) i
  have h1_1_ev : ∀ j, _root_.Even j → 1 ≤ seqConv (fun _ => (1 : ℝ)) (fun i => (1 : ℝ) ^ i) j := fun j _ => by
    have h0 := seqConv_ge_term (u := fun _ => (1 : ℝ)) (v := fun i => (1 : ℝ) ^ i)
      (fun _ => zero_le_one) (fun _ => by simp) (Nat.zero_le j)
    simpa using h0
  rcases hα with rfl | rfl | rfl
  · 
    have hu_eq : u k = seqConv (fun _ => (1 : ℝ)) (fun i => β ^ i) k := by
      dsimp only [u]
      have h1 : seqConv (fun _ => (1 : ℝ)) (fun i => (0 : ℝ) ^ i) = fun _ => (1 : ℝ) :=
        funext fun m => seqConv_zero_pow _ m
      have h2 : seqConv (fun i => β ^ i) (fun i => ((0 : ℝ) * β) ^ i) = fun i => β ^ i :=
        funext fun m => by simpa only [zero_mul] using seqConv_zero_pow (fun i => β ^ i) m
      rw [h1, h2]
    rw [hu_eq]
    rcases hβ with rfl | rfl | rfl
    · rw [seqConv_zero_pow]; exact ⟨zero_le_one, fun _ => le_rfl⟩
    · exact ⟨h1_1 k, h1_1_ev k⟩
    · exact ⟨h1_m1 k, h1_m1_ev k⟩
  · 
    rcases hβ with rfl | rfl | rfl
    · have hu_eq : u k = seqConv (fun _ => (1 : ℝ)) (fun i => (1 : ℝ) ^ i) k := by
        dsimp only [u]
        have h2 : seqConv (fun i => (0 : ℝ) ^ i) (fun i => ((1 : ℝ) * 0) ^ i) = fun i => (0 : ℝ) ^ i :=
          funext fun m => by simpa only [mul_zero] using seqConv_zero_pow (fun i => (0 : ℝ) ^ i) m
        rw [h2, seqConv_zero_pow]
      rw [hu_eq]; exact ⟨h1_1 k, h1_1_ev k⟩
    · have hu_eq : u k = seqConv (seqConv (fun _ => (1 : ℝ)) (fun i => (1 : ℝ) ^ i))
          (seqConv (fun _ => (1 : ℝ)) (fun i => (1 : ℝ) ^ i)) k := by
        dsimp only [u]
        have h1 : (fun i => (1 : ℝ) ^ i) = fun _ => (1 : ℝ) := funext fun _ => one_pow _
        simp only [one_mul]; rw [h1]
      rw [hu_eq]
      exact hpos_ge1 _ _ h1_1 h1_1 h1_1_ev h1_1_ev
    · 
      have hu_eq : u k = seqConv (seqConv (fun _ => (1 : ℝ)) (fun i => (-1 : ℝ) ^ i))
          (seqConv (fun _ => (1 : ℝ)) (fun i => (-1 : ℝ) ^ i)) k := by
        dsimp only [u]
        have h1 : (fun i => (1 : ℝ) ^ i) = fun _ => (1 : ℝ) := funext fun _ => one_pow _
        simp only [one_mul]
        rw [h1]
        have hstep :
            seqConv (seqConv (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)))
              (seqConv (fun i => (-1 : ℝ) ^ i) (fun i => (-1 : ℝ) ^ i)) k =
            seqConv (seqConv (fun _ => (1 : ℝ)) (fun i => (-1 : ℝ) ^ i))
              (seqConv (fun _ => (1 : ℝ)) (fun i => (-1 : ℝ) ^ i)) k := by
          rw [seqConv_assoc]
          have hmid :
              seqConv (fun _ => (1 : ℝ)) (seqConv (fun i => (-1 : ℝ) ^ i) (fun i => (-1 : ℝ) ^ i)) =
              seqConv (fun i => (-1 : ℝ) ^ i) (seqConv (fun _ => (1 : ℝ)) (fun i => (-1 : ℝ) ^ i)) := by
            funext m
            rw [← seqConv_assoc]
            exact seqConv_comm (seqConv (fun _ => (1 : ℝ)) (fun i => (-1 : ℝ) ^ i))
              (fun i => (-1 : ℝ) ^ i) m
          rw [hmid, ← seqConv_assoc]
        exact hstep
      rw [hu_eq]
      exact hpos_ge1 _ _ h1_m1 h1_m1 h1_m1_ev h1_m1_ev
  · 
    rcases hβ with rfl | rfl | rfl
    · have hu_eq : u k = seqConv (fun _ => (1 : ℝ)) (fun i => (-1 : ℝ) ^ i) k := by
        dsimp only [u]
        have h2 : seqConv (fun i => (0 : ℝ) ^ i) (fun i => ((-1 : ℝ) * 0) ^ i) = fun i => (0 : ℝ) ^ i :=
          funext fun m => by simpa only [mul_zero] using seqConv_zero_pow (fun i => (0 : ℝ) ^ i) m
        rw [h2, seqConv_zero_pow]
      rw [hu_eq]; exact ⟨h1_m1 k, h1_m1_ev k⟩
    · 
      have hu_eq : u k = seqConv (seqConv (fun _ => (1 : ℝ)) (fun i => (-1 : ℝ) ^ i))
          (seqConv (fun _ => (1 : ℝ)) (fun i => (-1 : ℝ) ^ i)) k := by
        dsimp only [u]
        have h1 : (fun i => (1 : ℝ) ^ i) = fun _ => (1 : ℝ) := funext fun _ => one_pow _
        simp only [mul_one]; rw [h1]
      rw [hu_eq]
      exact hpos_ge1 _ _ h1_m1 h1_m1 h1_m1_ev h1_m1_ev
    · 
      have hu_eq : u k = seqConv (seqConv (fun _ => (1 : ℝ)) (fun i => (-1 : ℝ) ^ i))
          (seqConv (fun _ => (1 : ℝ)) (fun i => (-1 : ℝ) ^ i)) k := by
        dsimp only [u]
        have h1 : (fun i => ((-1 : ℝ) * -1) ^ i) = fun _ => (1 : ℝ) := by
          funext i; norm_num
        rw [h1]
        have hc : seqConv (fun i => (-1 : ℝ) ^ i) (fun _ => (1 : ℝ)) =
            seqConv (fun _ => (1 : ℝ)) (fun i => (-1 : ℝ) ^ i) :=
          funext fun m => seqConv_comm _ _ m
        rw [hc]
      rw [hu_eq]
      exact hpos_ge1 _ _ h1_m1 h1_m1 h1_m1_ev h1_m1_ev

theorem fourCharCoeff_prime_pow_nonneg_and_even {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    {χ₁ : DirichletCharacter ℂ q₁} {χ₂ : DirichletCharacter ℂ q₂}
    (h1 : IsRealChar χ₁) (h2 : IsRealChar χ₂) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    0 ≤ fourCharCoeff χ₁ χ₂ (p ^ k) ∧ (_root_.Even k → 1 ≤ fourCharCoeff χ₁ χ₂ (p ^ k)) := by
  have h12 : IsRealChar (prodChar χ₁ χ₂) := isRealChar_prodChar h1 h2
  rw [fourCharCoeff, dirConv_prime_pow _ _ hp k]
  have hf1 : (fun i => divisorCharSum χ₁ (p ^ i)) =
      seqConv (fun _ => (1 : ℝ)) (fun i => (realCharFn χ₁ p) ^ i) := by
    funext i
    rw [divisorCharSum, dirConv_prime_pow _ _ hp i]
    congr 1; funext j; exact realCharFn_pow h1 p j
  have hf2 : (fun i => dirConv (realCharFn χ₂) (realCharFn (prodChar χ₁ χ₂)) (p ^ i)) =
      seqConv (fun i => (realCharFn χ₂ p) ^ i)
        (fun i => (realCharFn χ₁ p * realCharFn χ₂ p) ^ i) := by
    funext i
    rw [dirConv_prime_pow _ _ hp i]
    congr 1
    · funext j; exact realCharFn_pow h2 p j
    · funext j; rw [realCharFn_pow h12 p j, realCharFn_prodChar h1 h2 p]
  rw [hf1, hf2]
  exact fourChar_seqConv_nonneg_and_even (realCharFn χ₁ p) (realCharFn χ₂ p)
    (realCharFn_trichotomy h1 p) (realCharFn_trichotomy h2 p) k

theorem fourCharCoeff_nonneg {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    {χ₁ : DirichletCharacter ℂ q₁} {χ₂ : DirichletCharacter ℂ q₂}
    (h1 : IsRealChar χ₁) (h2 : IsRealChar χ₂) (n : ℕ) :
    0 ≤ fourCharCoeff χ₁ χ₂ n :=
  nonneg_of_mul_coprime (fourCharCoeff_zero χ₁ χ₂)
    (by rw [fourCharCoeff_one]; exact zero_le_one)
    (fun _ _ hc => fourCharCoeff_mul_coprime h1 h2 hc)
    (fun _ k hp => (fourCharCoeff_prime_pow_nonneg_and_even h1 h2 hp k).1) n

theorem LSeries_fourCharCoeff_eq {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    {χ₁ : DirichletCharacter ℂ q₁} {χ₂ : DirichletCharacter ℂ q₂}
    (h1 : IsRealChar χ₁) (h2 : IsRealChar χ₂) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (fourCharCoeff χ₁ χ₂ n : ℂ)) s ∧
    dirSeries (fourCharCoeff χ₁ χ₂) s =
      riemannZeta s * DirichletCharacter.LFunction χ₁ s *
        DirichletCharacter.LFunction χ₂ s * DirichletCharacter.LFunction (prodChar χ₁ χ₂) s := by
  have h12 : IsRealChar (prodChar χ₁ χ₂) := isRealChar_prodChar h1 h2
  obtain ⟨hsum1, heq1⟩ := LSeries_divisorCharSum_eq h1 hs
  have hsum2 : LSeriesSummable (fun n : ℕ => χ₂ (n : ZMod q₂)) s :=
    DirichletCharacter.LSeriesSummable_of_one_lt_re χ₂ hs
  have hsum12 : LSeriesSummable (fun n : ℕ => prodChar χ₁ χ₂ (n : ZMod (q₁ * q₂))) s :=
    DirichletCharacter.LSeriesSummable_of_one_lt_re (prodChar χ₁ χ₂) hs
  have hconv2_eq :
      (fun n : ℕ => (dirConv (realCharFn χ₂) (realCharFn (prodChar χ₁ χ₂)) n : ℂ)) =
        LSeries.convolution (fun n : ℕ => χ₂ (n : ZMod q₂))
          (fun n : ℕ => prodChar χ₁ χ₂ (n : ZMod (q₁ * q₂))) := by
    funext n
    rw [dirConv_cast_complex]
    congr 1
    · funext m; exact realCharFn_cast_complex h2 m
    · funext m; exact realCharFn_cast_complex h12 m
  have hsum_rhs :
      LSeriesSummable (fun n : ℕ => (dirConv (realCharFn χ₂) (realCharFn (prodChar χ₁ χ₂)) n : ℂ)) s := by
    rw [hconv2_eq]; exact hsum2.convolution hsum12
  have hconv_all :
      (fun n : ℕ => (fourCharCoeff χ₁ χ₂ n : ℂ)) =
        LSeries.convolution (fun n : ℕ => (divisorCharSum χ₁ n : ℂ))
          (fun n : ℕ => (dirConv (realCharFn χ₂) (realCharFn (prodChar χ₁ χ₂)) n : ℂ)) := by
    funext n; exact dirConv_cast_complex _ _ n
  refine ⟨?_, ?_⟩
  · rw [hconv_all]; exact hsum1.convolution hsum_rhs
  · rw [dirSeries_eq_LSeries, hconv_all, LSeries_convolution' hsum1 hsum_rhs,
      ← dirSeries_eq_LSeries, heq1, hconv2_eq, LSeries_convolution' hsum2 hsum12,
      DirichletCharacter.LFunction_eq_LSeries χ₂ hs,
      DirichletCharacter.LFunction_eq_LSeries (prodChar χ₁ χ₂) hs]
    ring

private lemma iteratedDeriv_sub_one_inv (m : ℕ) :
    ∀ s : ℂ, s ≠ 1 →
      iteratedDeriv m (fun z : ℂ => (z - 1)⁻¹) s =
        (-1 : ℂ) ^ m * (m.factorial : ℂ) * ((s - 1)⁻¹) ^ (m + 1) := by
  induction m with
  | zero =>
    intro s _
    simp
  | succ m ih =>
    intro s hs
    rw [iteratedDeriv_succ]
    have hopen : IsOpen ({(1 : ℂ)}ᶜ) := isClosed_singleton.isOpen_compl
    have hev :
        iteratedDeriv m (fun z : ℂ => (z - 1)⁻¹) =ᶠ[𝓝 s]
          fun z : ℂ => (-1 : ℂ) ^ m * (m.factorial : ℂ) * ((z - 1)⁻¹) ^ (m + 1) := by
      filter_upwards [hopen.mem_nhds hs] with z hz
      exact ih z hz
    rw [hev.deriv_eq]
    have hsub_ne : s - 1 ≠ 0 := sub_ne_zero.mpr hs
    have hd1 : HasDerivAt (fun z : ℂ => (z - 1)⁻¹) (-(s - 1)⁻¹ ^ 2) s := by
      have h := ((hasDerivAt_id s).sub_const (1 : ℂ)).inv hsub_ne
      exact h.congr_deriv (by simp only [id]; field_simp [hsub_ne])
    have hd2 : HasDerivAt (fun z : ℂ => ((z - 1)⁻¹) ^ (m + 1))
        (((m + 1 : ℕ) : ℂ) * ((s - 1)⁻¹) ^ m * (-(s - 1)⁻¹ ^ 2)) s :=
      hd1.pow (m + 1)
    have hd3 := hd2.const_mul ((-1 : ℂ) ^ m * (m.factorial : ℂ))
    rw [hd3.deriv, Nat.factorial_succ]
    push_cast
    ring

set_option maxHeartbeats 2000000 in
theorem estermann_positivity_inequality {a : ℕ → ℝ} (ha0 : a 0 = 0) (ha1 : 1 ≤ a 1)
    (ha_nn : ∀ n, 0 ≤ a n)
    (hconv : ∀ x : ℝ, 1 < x → LSeriesSummable (fun n => (a n : ℂ)) (x : ℂ))
    {F G : ℂ → ℂ} {lam M : ℝ} (hM_nn : 0 ≤ M)
    (hG_diff : DifferentiableOn ℂ G {s : ℂ | 0 < s.re})
    (hGF : ∀ s : ℂ, 0 < s.re → s ≠ 1 → G s = F s - (lam : ℂ) / (s - 1))
    (hagree : ∀ s : ℂ, 1 < s.re → F s = dirSeries a s)
    (hM_bd : ∀ s ∈ Metric.sphere (2 : ℂ) (3 / 2), ‖G s‖ ≤ M)
    {β : ℝ} (hβ_lo : 3 / 4 ≤ β) (hβ_hi : β < 1) {K : ℕ} (hK : 1 ≤ K) :
    1 - (lam / (1 - β)) * (2 - β) ^ K - 6 * M * (2 * (2 - β) / 3) ^ K ≤ (F (β : ℂ)).re := by
  set R : NNReal := ⟨3 / 2, by norm_num⟩
  have hR_pos : (0 : NNReal) < R := by change (0 : ℝ) < 3 / 2; norm_num
  have hR_val : (R : ℝ) = 3 / 2 := rfl
  have hsub : Metric.closedBall (2 : ℂ) (R : ℝ) ⊆ {s : ℂ | 0 < s.re} := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm, hR_val] at hz
    have hre := abs_le.mp ((Complex.abs_re_le_norm (z - 2)).trans hz)
    simp only [Complex.sub_re, Complex.re_ofNat] at hre
    show 0 < z.re
    linarith
  have hpow : HasFPowerSeriesOnBall G (cauchyPowerSeries G (2 : ℂ) (R : ℝ)) (2 : ℂ) (R : ENNReal) :=
    (hG_diff.mono hsub).hasFPowerSeriesOnBall hR_pos
  set u : ℝ := 2 - β
  have hu_gt1 : 1 < u := by dsimp only [u]; linarith
  have hu_le : u ≤ 5 / 4 := by dsimp only [u]; linarith
  have hu_pos : 0 < u := by linarith
  have hβ_mem : (β : ℂ) ∈ Metric.eball (2 : ℂ) (R : ENNReal) := by
    rw [Metric.mem_eball, edist_dist]
    have hd : dist (β : ℂ) (2 : ℂ) = u := by
      rw [Complex.dist_eq, show (β : ℂ) - 2 = ((-(u : ℝ) : ℝ) : ℂ) by dsimp only [u]; push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos hu_pos]
    rw [hd, ENNReal.ofReal_lt_coe_iff hu_pos.le]
    change u < 3 / 2
    linarith
  have hhasSum := hpow.hasSum_sub hβ_mem
  
  have hev_G : G =ᶠ[𝓝 (2 : ℂ)] fun s : ℂ => dirSeries a s - (lam : ℂ) * (s - 1)⁻¹ := by
    have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with s hs
    have hs0 : 0 < s.re := zero_lt_one.trans hs
    have hs1 : s ≠ 1 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    rw [hGF s hs0 hs1, hagree s hs, div_eq_mul_inv]
  
  let b : ℕ → ℝ := fun m =>
    (∑' n : ℕ, a n * (Real.log (n : ℝ)) ^ m * (n : ℝ) ^ (-2 : ℝ)) / (m.factorial : ℝ)
  have hb_nn : ∀ m : ℕ, 0 ≤ b m := fun m => by
    refine div_nonneg (tsum_nonneg fun n => ?_) (Nat.cast_nonneg _)
    rcases eq_or_ne n 0 with rfl | hn0
    · simp [ha0]
    · have hn1 : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr (Nat.pos_of_ne_zero hn0)
      exact mul_nonneg (mul_nonneg (ha_nn n) (pow_nonneg (Real.log_nonneg hn1) m))
        (Real.rpow_nonneg (zero_le_one.trans hn1) _)
  have hb0_ge1 : 1 ≤ b 0 := by
    dsimp only [b]
    rw [Nat.factorial_zero, Nat.cast_one, div_one]
    have hsumm : Summable (fun n : ℕ => a n * (Real.log (n : ℝ)) ^ 0 * (n : ℝ) ^ (-2 : ℝ)) :=
      summable_log_pow_mul_rpow ha0 ha_nn hconv (by norm_num : (1 : ℝ) < 2) 0
    have hle := hsumm.le_tsum 1 fun n _ => by
      rcases eq_or_ne n 0 with rfl | hn0
      · simp [ha0]
      · have hn1 : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr (Nat.pos_of_ne_zero hn0)
        exact mul_nonneg (mul_nonneg (ha_nn n) (by simp))
          (Real.rpow_nonneg (zero_le_one.trans hn1) _)
    have h1 : a 1 * (Real.log ((1 : ℕ) : ℝ)) ^ 0 * ((1 : ℕ) : ℝ) ^ (-2 : ℝ) = a 1 := by
      simp
    rw [h1] at hle
    exact ha1.trans hle
  
  have hterm_eq : ∀ m : ℕ,
      cauchyPowerSeries G (2 : ℂ) (R : ℝ) m (fun _ => (β : ℂ) - 2) =
        (((b m - lam) * u ^ m : ℝ) : ℂ) := by
    intro m
    have hdiff : (β : ℂ) - 2 = (-((u : ℝ) : ℂ)) := by dsimp only [u]; push_cast; ring
    have hfac := hpow.factorial_smul ((β : ℂ) - 2) m
    have hmult : (iteratedFDeriv ℂ m G (2 : ℂ)) (fun _ => (β : ℂ) - 2) =
        (-((u : ℝ) : ℂ)) ^ m * iteratedDeriv m G (2 : ℂ) := by
      rw [hdiff]
      have h1 : (fun _ : Fin m => (-((u : ℝ) : ℂ))) = fun _ => (-((u : ℝ) : ℂ)) • (1 : ℂ) := by
        ext; simp
      rw [h1, ContinuousMultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul, ← iteratedDeriv_eq_iteratedFDeriv]
    have hm0 : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
    have hdiv : cauchyPowerSeries G (2 : ℂ) (R : ℝ) m (fun _ => (β : ℂ) - 2) =
        ((-1 : ℂ) ^ m * iteratedDeriv m G (2 : ℂ) / (m.factorial : ℂ)) * (u : ℂ) ^ m := by
      rw [nsmul_eq_mul, hmult] at hfac
      have hdiv' : cauchyPowerSeries G (2 : ℂ) (R : ℝ) m (fun _ => (β : ℂ) - 2) =
          (-((u : ℝ) : ℂ)) ^ m * iteratedDeriv m G (2 : ℂ) / (m.factorial : ℂ) :=
        (eq_div_iff hm0).mpr (by rw [mul_comm, hfac])
      rw [hdiv', show (-((u : ℝ) : ℂ)) ^ m = (-1 : ℂ) ^ m * (u : ℂ) ^ m by rw [← mul_pow]; ring]
      ring
    rw [hdiv, hev_G.iteratedDeriv_eq m]
    
    have hcd1 : ContDiffAt ℂ m (dirSeries a) (2 : ℂ) := by
      have hfun : dirSeries a = LSeries (fun n => (a n : ℂ)) := funext (dirSeries_eq_LSeries a)
      rw [hfun]
      have habs : LSeries.abscissaOfAbsConv (fun n => (a n : ℂ)) ≤ (1 : EReal) :=
        LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable hconv
      have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
      have hdiff : DifferentiableOn ℂ (LSeries (fun n => (a n : ℂ))) {s : ℂ | 1 < s.re} := by
        intro z hz
        have hlt : LSeries.abscissaOfAbsConv (fun n => (a n : ℂ)) < (z.re : EReal) :=
          lt_of_le_of_lt habs (EReal.coe_lt_coe_iff.mpr hz)
        exact (LSeries_hasDerivAt hlt).differentiableAt.differentiableWithinAt
      exact (hdiff.analyticAt (hopen.mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re))).contDiffAt.of_le
        le_top
    have hcd2 : ContDiffAt ℂ m (fun s : ℂ => (lam : ℂ) * (s - 1)⁻¹) (2 : ℂ) := by
      have h21 : (2 : ℂ) - 1 ≠ 0 := by norm_num
      exact contDiffAt_const.mul ((contDiffAt_id.sub contDiffAt_const).inv h21)
    have hsub_deriv :
        iteratedDeriv m (fun s : ℂ => dirSeries a s - (lam : ℂ) * (s - 1)⁻¹) (2 : ℂ) =
          iteratedDeriv m (dirSeries a) (2 : ℂ) -
            (lam : ℂ) * iteratedDeriv m (fun s : ℂ => (s - 1)⁻¹) (2 : ℂ) := by
      rw [iteratedDeriv_fun_sub hcd1 hcd2, iteratedDeriv_const_mul_field]
    rw [hsub_deriv, iteratedDeriv_sub_one_inv m 2 (by norm_num),
      show (2 : ℂ) - 1 = 1 by norm_num, inv_one, one_pow, mul_one]
    have hdir := alternating_iteratedDeriv_dirSeries_real ha0 hconv (by norm_num : (1 : ℝ) < 2) m
    have hdir2 : (-1 : ℂ) ^ m * iteratedDeriv m (dirSeries a) (2 : ℂ) =
        ((b m * (m.factorial : ℝ) : ℝ) : ℂ) := by
      dsimp only [b]
      have hfac_ne : (m.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr m.factorial_ne_zero
      rw [div_mul_cancel₀ _ hfac_ne]
      simpa using hdir
    have hneg_sq : (-1 : ℂ) ^ m * (-1 : ℂ) ^ m = 1 := by
      rw [← mul_pow]; norm_num
    have hcoeff :
        (-1 : ℂ) ^ m * (iteratedDeriv m (dirSeries a) (2 : ℂ) -
            (lam : ℂ) * ((-1 : ℂ) ^ m * (m.factorial : ℂ))) / (m.factorial : ℂ) =
          ((b m - lam : ℝ) : ℂ) := by
      rw [mul_sub, hdir2,
        show (-1 : ℂ) ^ m * ((lam : ℂ) * ((-1 : ℂ) ^ m * (m.factorial : ℂ))) =
          ((-1 : ℂ) ^ m * (-1 : ℂ) ^ m) * ((lam : ℂ) * (m.factorial : ℂ)) by ring,
        hneg_sq, one_mul]
      push_cast
      field_simp [hm0]
    rw [hcoeff]
    push_cast
    rfl
  
  set r : ℝ := 2 * u / 3
  have hr_pos : 0 < r := by positivity
  have hr_le : r ≤ 5 / 6 := by dsimp only [r]; linarith
  have hr_lt1 : r < 1 := by linarith
  have hterm_norm : ∀ m : ℕ,
      ‖cauchyPowerSeries G (2 : ℂ) (R : ℝ) m (fun _ => (β : ℂ) - 2)‖ ≤ M * r ^ m := by
    intro m
    have hint_le :
        (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, ‖G (circleMap (2 : ℂ) (R : ℝ) θ)‖ ≤ M := by
      have hcont : ContinuousOn (fun θ : ℝ => ‖G (circleMap (2 : ℂ) (R : ℝ) θ)‖)
          (Set.uIcc 0 (2 * Real.pi)) := by
        refine ContinuousOn.norm (hG_diff.continuousOn.comp (continuous_circleMap _ _).continuousOn ?_)
        intro θ _
        exact hsub (Metric.sphere_subset_closedBall (circleMap_mem_sphere (2 : ℂ) (by positivity) θ))
      have hmono :
          ∫ θ in (0 : ℝ)..2 * Real.pi, ‖G (circleMap (2 : ℂ) (R : ℝ) θ)‖ ≤
            ∫ _θ in (0 : ℝ)..2 * Real.pi, M := by
        refine intervalIntegral.integral_mono_on (by positivity) hcont.intervalIntegrable
          intervalIntegrable_const fun θ _ => ?_
        exact hM_bd _ (circleMap_mem_sphere (2 : ℂ) (by positivity) θ)
      rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hmono
      have h2pi_pos : 0 < 2 * Real.pi := by positivity
      calc (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, ‖G (circleMap (2 : ℂ) (R : ℝ) θ)‖
          ≤ (2 * Real.pi)⁻¹ * (2 * Real.pi * M) :=
            mul_le_mul_of_nonneg_left hmono (inv_nonneg.mpr h2pi_pos.le)
        _ = M := by field_simp [h2pi_pos.ne']
    have hnorm_v : ‖(β : ℂ) - 2‖ = u := by
      rw [show (β : ℂ) - 2 = ((-(u : ℝ) : ℝ) : ℂ) by dsimp only [u]; push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos hu_pos]
    calc ‖cauchyPowerSeries G (2 : ℂ) (R : ℝ) m (fun _ => (β : ℂ) - 2)‖
        ≤ ‖cauchyPowerSeries G (2 : ℂ) (R : ℝ) m‖ * ∏ _i : Fin m, ‖(β : ℂ) - 2‖ :=
          ContinuousMultilinearMap.le_opNorm _ _
      _ = ‖cauchyPowerSeries G (2 : ℂ) (R : ℝ) m‖ * u ^ m := by
          simp [hnorm_v]
      _ ≤ (((2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, ‖G (circleMap (2 : ℂ) (R : ℝ) θ)‖) *
            |(R : ℝ)|⁻¹ ^ m) * u ^ m := by
          gcongr
          exact norm_cauchyPowerSeries_le _ _ _ _
      _ ≤ (M * (3 / 2 : ℝ)⁻¹ ^ m) * u ^ m := by
          rw [hR_val] at hint_le
          rw [hR_val, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
          gcongr
      _ = M * r ^ m := by
          rw [mul_assoc, ← mul_pow]
          dsimp only [r]
          congr 2; ring
  
  have hsplit :
      (∑ m ∈ Finset.range K, cauchyPowerSeries G (2 : ℂ) (R : ℝ) m (fun _ => (β : ℂ) - 2)) +
        (∑' m : ℕ, cauchyPowerSeries G (2 : ℂ) (R : ℝ) (m + K) (fun _ => (β : ℂ) - 2)) =
      G (β : ℂ) := by
    rw [hhasSum.summable.sum_add_tsum_nat_add K, hhasSum.tsum_eq]
  have hre_split :
      (G (β : ℂ)).re =
        (∑ m ∈ Finset.range K, (b m - lam) * u ^ m) +
          (∑' m : ℕ, cauchyPowerSeries G (2 : ℂ) (R : ℝ) (m + K) (fun _ => (β : ℂ) - 2)).re := by
    have h := congrArg Complex.re hsplit.symm
    rw [Complex.add_re, Complex.re_sum] at h
    rw [h]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hterm_eq m, Complex.ofReal_re]
  
  have hfin_ge : 1 - lam * (u ^ K - 1) / (u - 1) ≤ ∑ m ∈ Finset.range K, (b m - lam) * u ^ m := by
    have hsep :
        ∑ m ∈ Finset.range K, (b m - lam) * u ^ m =
          (∑ m ∈ Finset.range K, b m * u ^ m) - lam * ∑ m ∈ Finset.range K, u ^ m := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun m _ => by ring
    have hb_sum : 1 ≤ ∑ m ∈ Finset.range K, b m * u ^ m := by
      have h0 := Finset.single_le_sum (f := fun m => b m * u ^ m)
        (fun m _ => mul_nonneg (hb_nn m) (pow_nonneg hu_pos.le m))
        (Finset.mem_range.mpr hK)
      simp only [pow_zero, mul_one] at h0
      exact hb0_ge1.trans h0
    have hgeom : ∑ m ∈ Finset.range K, u ^ m = (u ^ K - 1) / (u - 1) :=
      geom_sum_eq hu_gt1.ne' K
    rw [hsep, hgeom, mul_div_assoc]
    linarith
  
  have htail_le :
      ‖∑' m : ℕ, cauchyPowerSeries G (2 : ℂ) (R : ℝ) (m + K) (fun _ => (β : ℂ) - 2)‖ ≤
        6 * M * r ^ K := by
    have hsumm_geom : Summable (fun m : ℕ => M * r ^ (m + K)) := by
      have h1 : Summable (fun m : ℕ => r ^ m) := summable_geometric_of_lt_one hr_pos.le hr_lt1
      simpa only [pow_add, ← mul_assoc] using h1.mul_right (r ^ K) |>.mul_left M
    have hsumm_tail :
        Summable (fun m : ℕ =>
          cauchyPowerSeries G (2 : ℂ) (R : ℝ) (m + K) (fun _ => (β : ℂ) - 2)) :=
      Summable.of_norm_bounded hsumm_geom fun m => hterm_norm (m + K)
    have h1 := norm_tsum_le_tsum_norm hsumm_tail.norm
    have h2 :
        ∑' m : ℕ, ‖cauchyPowerSeries G (2 : ℂ) (R : ℝ) (m + K) (fun _ => (β : ℂ) - 2)‖ ≤
          ∑' m : ℕ, M * r ^ (m + K) :=
      hsumm_tail.norm.tsum_le_tsum (fun m => hterm_norm (m + K)) hsumm_geom
    have h3 : ∑' m : ℕ, M * r ^ (m + K) = M * r ^ K * (1 - r)⁻¹ := by
      have hrew : (fun m : ℕ => M * r ^ (m + K)) = fun m : ℕ => (M * r ^ K) * r ^ m := by
        funext m; rw [pow_add]; ring
      rw [hrew, tsum_mul_left, tsum_geometric_of_lt_one hr_pos.le hr_lt1]
    have hinv_le : (1 - r)⁻¹ ≤ 6 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    calc ‖∑' m : ℕ, cauchyPowerSeries G (2 : ℂ) (R : ℝ) (m + K) (fun _ => (β : ℂ) - 2)‖
        ≤ M * r ^ K * (1 - r)⁻¹ := (h1.trans h2).trans_eq h3
      _ ≤ M * r ^ K * 6 := mul_le_mul_of_nonneg_left hinv_le (by positivity)
      _ = 6 * M * r ^ K := by ring
  have htail_re :
      -(6 * M * r ^ K) ≤
        (∑' m : ℕ, cauchyPowerSeries G (2 : ℂ) (R : ℝ) (m + K) (fun _ => (β : ℂ) - 2)).re := by
    have h := (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans htail_le)
    linarith
  
  have hGF_β := hGF (β : ℂ) (by simp; linarith) (by
    intro h; have := congrArg Complex.re h; simp at this; linarith)
  have hF_re : (F (β : ℂ)).re = (G (β : ℂ)).re - lam / (1 - β) := by
    have h1 : F (β : ℂ) = G (β : ℂ) + (lam : ℂ) / ((β : ℂ) - 1) := by linear_combination -hGF_β
    have h2 : ((lam : ℂ) / ((β : ℂ) - 1)).re = -lam / (1 - β) := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_div, Complex.ofReal_re]
      have hne : 1 - β ≠ 0 := by linarith
      have hne' : β - 1 ≠ 0 := by linarith
      field_simp [hne, hne']; ring
    rw [h1, Complex.add_re, h2]; ring
  have halg :
      1 - lam * (u ^ K - 1) / (u - 1) - lam / (1 - β) = 1 - (lam / (1 - β)) * u ^ K := by
    have hu1 : u - 1 = 1 - β := by dsimp only [u]; ring
    have hne : 1 - β ≠ 0 := by linarith
    rw [hu1]
    field_simp [hne]; ring
  linarith

theorem estermann_residue_lower_bound_of_nonpos {a : ℕ → ℝ} (ha0 : a 0 = 0) (ha1 : 1 ≤ a 1)
    (ha_nn : ∀ n, 0 ≤ a n)
    (hconv : ∀ x : ℝ, 1 < x → LSeriesSummable (fun n => (a n : ℂ)) (x : ℂ))
    {F G : ℂ → ℂ} {lam M : ℝ} (hM1 : 1 ≤ M)
    (hG_diff : DifferentiableOn ℂ G {s : ℂ | 0 < s.re})
    (hGF : ∀ s : ℂ, 0 < s.re → s ≠ 1 → G s = F s - (lam : ℂ) / (s - 1))
    (hagree : ∀ s : ℂ, 1 < s.re → F s = dirSeries a s)
    (hM_bd : ∀ s ∈ Metric.sphere (2 : ℂ) (3 / 2), ‖G s‖ ≤ M)
    {β : ℝ} (hβ_lo : 3 / 4 ≤ β) (hβ_hi : β < 1) (hF_nonpos : (F (β : ℂ)).re ≤ 0) :
    (1 - β) / (4 * (12 * M) ^ (6 * (1 - β))) ≤ lam := by
  set u : ℝ := 2 - β
  have hu_gt1 : 1 < u := by dsimp only [u]; linarith
  have hu_le : u ≤ 5 / 4 := by dsimp only [u]; linarith
  have hu_pos : 0 < u := by linarith
  set r : ℝ := 2 * u / 3
  have hr_pos : 0 < r := by positivity
  have hr_le : r ≤ 5 / 6 := by dsimp only [r]; linarith
  have hrinv_ge : (6 / 5 : ℝ) ≤ r⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hr_pos]; linarith
  have hlog_rinv_ge : (1 / 6 : ℝ) ≤ Real.log r⁻¹ := by
    have h1 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 6 / 5)
    have h2 : Real.log (6 / 5 : ℝ) ≤ Real.log r⁻¹ := Real.log_le_log (by norm_num) hrinv_ge
    norm_num at h1
    linarith
  have hlog_rinv_pos : 0 < Real.log r⁻¹ := by linarith
  have h12M_gt1 : (1 : ℝ) < 12 * M := by linarith
  have h12M_pos : (0 : ℝ) < 12 * M := by linarith
  have hlog12M_pos : 0 < Real.log (12 * M) := Real.log_pos h12M_gt1
  set xK : ℝ := Real.log (12 * M) / Real.log r⁻¹
  have hxK_pos : 0 < xK := div_pos hlog12M_pos hlog_rinv_pos
  set K : ℕ := Nat.ceil xK
  have hK1 : 1 ≤ K := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hxK_pos).ne'
  have hK_ge : xK ≤ (K : ℝ) := Nat.le_ceil xK
  have hK_lt : (K : ℝ) < xK + 1 := Nat.ceil_lt_add_one hxK_pos.le
  
  have htail_half : 6 * M * r ^ K ≤ 1 / 2 := by
    have hlog_le : Real.log (12 * M) ≤ (K : ℝ) * Real.log r⁻¹ := by
      have h := mul_le_mul_of_nonneg_right hK_ge hlog_rinv_pos.le
      rwa [div_mul_cancel₀ _ hlog_rinv_pos.ne'] at h
    have hexp := Real.exp_le_exp.mpr hlog_le
    rw [Real.exp_log h12M_pos, Real.exp_nat_mul, Real.exp_log (inv_pos.mpr hr_pos), inv_pow] at hexp
    have hpow_pos : 0 < r ^ K := pow_pos hr_pos K
    have hmul := mul_le_mul_of_nonneg_right hexp hpow_pos.le
    rw [inv_mul_cancel₀ hpow_pos.ne'] at hmul
    linarith
  
  have huK_le : u ^ K ≤ 2 * (12 * M) ^ (6 * (1 - β)) := by
    have hlog_u_pos : 0 < Real.log u := Real.log_pos hu_gt1
    have hlog_u_le : Real.log u ≤ 1 - β := by
      have h := Real.log_le_sub_one_of_pos hu_pos
      dsimp only [u] at h; linarith
    have hratio : Real.log u / Real.log r⁻¹ ≤ 6 * (1 - β) := by
      rw [div_le_iff₀ hlog_rinv_pos]
      have h1β : 0 ≤ 1 - β := by linarith
      nlinarith
    have hK_log : (K : ℝ) * Real.log u ≤ 6 * (1 - β) * Real.log (12 * M) + Real.log u := by
      have h1 : (K : ℝ) * Real.log u ≤ (xK + 1) * Real.log u :=
        mul_le_mul_of_nonneg_right hK_lt.le hlog_u_pos.le
      have h2 : xK * Real.log u = Real.log (12 * M) * (Real.log u / Real.log r⁻¹) := by
        dsimp only [xK]; ring
      have h3 : Real.log (12 * M) * (Real.log u / Real.log r⁻¹) ≤
          Real.log (12 * M) * (6 * (1 - β)) :=
        mul_le_mul_of_nonneg_left hratio hlog12M_pos.le
      linarith
    have hexp := Real.exp_le_exp.mpr hK_log
    rw [Real.exp_nat_mul, Real.exp_log hu_pos, Real.exp_add, Real.exp_log hu_pos,
      mul_comm (6 * (1 - β)), ← Real.rpow_def_of_pos h12M_pos] at hexp
    have hpow_nn : 0 ≤ (12 * M) ^ (6 * (1 - β)) := Real.rpow_nonneg h12M_pos.le _
    nlinarith
  
  have hest := estermann_positivity_inequality ha0 ha1 ha_nn hconv (by linarith) hG_diff hGF
    hagree hM_bd hβ_lo hβ_hi hK1
  have h1β_pos : 0 < 1 - β := by linarith
  have hprod_ge : 1 / 2 ≤ (lam / (1 - β)) * u ^ K := by
    dsimp only [u, r] at hest htail_half ⊢
    linarith
  have hlam_pos : 0 < lam := by
    by_contra hle; push Not at hle
    have h1 : lam / (1 - β) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hle h1β_pos.le
    have h2 : (lam / (1 - β)) * u ^ K ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h1 (pow_nonneg hu_pos.le K)
    linarith
  have hprod_le : (lam / (1 - β)) * u ^ K ≤ (lam / (1 - β)) * (2 * (12 * M) ^ (6 * (1 - β))) :=
    mul_le_mul_of_nonneg_left huK_le (div_nonneg hlam_pos.le h1β_pos.le)
  have hden_pos : 0 < 4 * (12 * M) ^ (6 * (1 - β)) := by positivity
  rw [div_le_iff₀ hden_pos]
  have h1 : 1 / 2 ≤ (lam / (1 - β)) * (2 * (12 * M) ^ (6 * (1 - β))) := hprod_ge.trans hprod_le
  have h2 := mul_le_mul_of_nonneg_right h1 h1β_pos.le
  have h3 : (lam / (1 - β)) * (2 * (12 * M) ^ (6 * (1 - β))) * (1 - β) =
      lam * (2 * (12 * M) ^ (6 * (1 - β))) := by
    field_simp [h1β_pos.ne']
  rw [h3] at h2
  linarith

theorem riemannZeta_neg_on_Ioo {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    (riemannZeta (σ : ℂ)).re < 0 ∧ (riemannZeta (σ : ℂ)).im = 0 := by
  have hs0 : 0 < (σ : ℂ).re := by simpa using h0
  have hs1 : (σ : ℂ) ≠ 1 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hem := riemannZeta_sub_pole_eq_eulerMaclaurin hs0 hs1
  have hint_real :
      ∫ t in Ioi (1 : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-(σ : ℂ) - 1) =
        ((∫ t in Ioi (1 : ℝ), fractNat t * t ^ (-σ - 1) : ℝ) : ℂ) := by
    have hof :
        ∫ t in Ioi (1 : ℝ), ((fractNat t * t ^ (-σ - 1) : ℝ) : ℂ) =
          ((∫ t in Ioi (1 : ℝ), fractNat t * t ^ (-σ - 1) : ℝ) : ℂ) :=
      integral_ofReal
    rw [← hof]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := zero_lt_one.trans ht
    rw [Complex.ofReal_mul, show -(σ : ℂ) - 1 = ((-σ - 1 : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_cpow ht0.le]
  have hζ_eq :
      riemannZeta (σ : ℂ) =
        (((1 / (σ - 1) + 1 - σ * ∫ t in Ioi (1 : ℝ), fractNat t * t ^ (-σ - 1) : ℝ)) : ℂ) := by
    have h := eq_add_of_sub_eq hem
    rw [h, hint_real]
    push_cast
    ring
  rw [hζ_eq, Complex.ofReal_re, Complex.ofReal_im]
  refine ⟨?_, rfl⟩
  have hint_nn : 0 ≤ ∫ t in Ioi (1 : ℝ), fractNat t * t ^ (-σ - 1) := by
    refine setIntegral_nonneg measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := zero_lt_one.trans ht
    have hfr_nn : 0 ≤ fractNat t := by
      unfold fractNat
      exact sub_nonneg.mpr (Nat.floor_le ht0.le)
    exact mul_nonneg hfr_nn (Real.rpow_nonneg ht0.le _)
  have hfrac_neg : 1 / (σ - 1) + 1 < 0 := by
    have hden : σ - 1 < 0 := by linarith
    have heq : 1 / (σ - 1) + 1 = σ / (σ - 1) := by field_simp [hden.ne]; ring
    rw [heq]
    exact div_neg_of_pos_of_neg h0 hden
  nlinarith

theorem norm_riemannZeta_le_of_mem_sphere {s : ℂ} (hs : s ∈ Metric.sphere (2 : ℂ) (3 / 2)) :
    ‖riemannZeta s‖ ≤ 10 := by
  rw [Metric.mem_sphere, dist_eq_norm] at hs
  have hre_diff := abs_le.mp ((Complex.abs_re_le_norm (s - 2)).trans hs.le)
  simp only [Complex.sub_re, Complex.re_ofNat] at hre_diff
  have hs_re : 1 / 2 ≤ s.re := by linarith
  have hs_pos : 0 < s.re := by linarith
  have hs_norm : ‖s‖ ≤ 7 / 2 := by
    have h := norm_add_le (s - 2) 2
    rw [sub_add_cancel, hs, show ‖(2 : ℂ)‖ = 2 by norm_num] at h
    linarith
  have hs1_ge : (1 / 2 : ℝ) ≤ ‖s - 1‖ := by
    have h := norm_add_le (s - 1) (-1)
    have h1 : (s - 1) + (-1 : ℂ) = s - 2 := by ring
    rw [h1, hs, norm_neg, norm_one] at h
    linarith
  have hs1_ne : s ≠ 1 := fun h => by subst h; norm_num at hs1_ge
  have hem := riemannZeta_sub_pole_eq_eulerMaclaurin hs_pos hs1_ne
  have hζ : riemannZeta s =
      1 / (s - 1) + 1 - s * ∫ t in Ioi (1 : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1) := by
    linear_combination hem
  rw [hζ]
  have hinv : ‖(1 : ℂ) / (s - 1)‖ ≤ 2 := by
    rw [norm_div, norm_one]
    have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hs1_ge
    linarith
  have htail : ‖∫ t in Ioi (1 : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)‖ ≤ 2 := by
    have h := norm_eulerMaclaurin_tail_le (a := 1) le_rfl hs_pos
    rw [Real.one_rpow] at h
    have h2 : 1 / s.re ≤ 2 := by rw [div_le_iff₀ hs_pos]; linarith
    exact h.trans h2
  calc ‖1 / (s - 1) + 1 - s * ∫ t in Ioi (1 : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)‖
      ≤ ‖(1 : ℂ) / (s - 1) + 1‖ +
        ‖s * ∫ t in Ioi (1 : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)‖ := norm_sub_le _ _
    _ ≤ (‖(1 : ℂ) / (s - 1)‖ + ‖(1 : ℂ)‖) +
        ‖s‖ * ‖∫ t in Ioi (1 : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)‖ := by
        rw [norm_mul]; gcongr; exact norm_add_le _ _
    _ ≤ (2 + 1) + (7 / 2) * 2 := by
        rw [norm_one]
        have hmul : ‖s‖ * ‖∫ t in Ioi (1 : ℝ), ((fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)‖ ≤
            (7 / 2) * 2 :=
          mul_le_mul hs_norm htail (norm_nonneg _) (by norm_num)
        linarith
    _ = 10 := by norm_num

theorem norm_LFunction_le_of_mem_sphere {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {s : ℂ} (hs : s ∈ Metric.sphere (2 : ℂ) (3 / 2)) :
    ‖DirichletCharacter.LFunction χ s‖ ≤ 15 * (q : ℝ) := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast NeZero.pos q
  rw [Metric.mem_sphere, dist_eq_norm] at hs
  have hre_diff := abs_le.mp ((Complex.abs_re_le_norm (s - 2)).trans hs.le)
  have him_diff := abs_le.mp ((Complex.abs_im_le_norm (s - 2)).trans hs.le)
  simp only [Complex.sub_re, Complex.re_ofNat, Complex.sub_im, Complex.im_ofNat,
    sub_zero] at hre_diff him_diff
  by_cases hre2 : s.re ≤ 2
  · have hstrip := norm_LFunction_strip_le hχ (by linarith : 1 / 2 ≤ s.re) hre2
    have him : |s.im| ≤ 3 / 2 := abs_le.mpr him_diff
    nlinarith
  · push Not at hre2
    have hgt1 : 1 < s.re := by linarith
    have h1 := (norm_LFunction_and_inv_and_logDeriv_of_one_lt_re χ hgt1 s.im).1
    have hs_eq : (s.re : ℂ) + I * (s.im : ℂ) = s := by
      apply Complex.ext <;> simp
    rw [hs_eq] at h1
    have hdiv : s.re / (s.re - 1) ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    linarith

def regZetaMul (H : ℂ → ℂ) (s : ℂ) : ℂ :=
  dslope zetaReg 1 s * H s + dslope H 1 s

theorem differentiableOn_regZetaMul {H : ℂ → ℂ} (hH : Differentiable ℂ H) :
    DifferentiableOn ℂ (regZetaMul H) {s : ℂ | 0 < s.re} := by
  have hopen : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hmem : {s : ℂ | 0 < s.re} ∈ 𝓝 (1 : ℂ) := hopen.mem_nhds (by norm_num)
  have h1 : DifferentiableOn ℂ (dslope zetaReg 1) {s : ℂ | 0 < s.re} :=
    (Complex.differentiableOn_dslope hmem).mpr differentiableOn_zetaReg
  have h2 : DifferentiableOn ℂ (dslope H 1) {s : ℂ | 0 < s.re} :=
    ((Complex.differentiableOn_dslope univ_mem).mpr hH.differentiableOn).mono (Set.subset_univ _)
  exact (h1.mul hH.differentiableOn).add h2

theorem regZetaMul_eq {H : ℂ → ℂ} {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    regZetaMul H s = riemannZeta s * H s - H 1 / (s - 1) := by
  unfold regZetaMul
  rw [dslope_of_ne _ hs1, dslope_of_ne _ hs1, slope_def_field, slope_def_field,
    zetaReg_one, zetaReg_eq_mul_riemannZeta hs hs1]
  have hne : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  field_simp [hne]
  ring

theorem LFunction_one_lower_bound_of_re_nonneg {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (hreal : IsRealChar χ) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 4)
    (hL_nn : 0 ≤ (DirichletCharacter.LFunction χ ((1 - δ : ℝ) : ℂ)).re) :
    δ / (4 * (2400 * (q : ℝ)) ^ (6 * δ)) ≤ (DirichletCharacter.LFunction χ 1).re := by
  have hq2 : 2 ≤ q := two_le_of_dirichletChar_ne_one hχ
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  set lam : ℝ := (DirichletCharacter.LFunction χ 1).re
  have hlam_eq : (lam : ℂ) = DirichletCharacter.LFunction χ 1 :=
    Complex.ext (by simp [lam]) (by simp [(LFunction_one_pos_of_real χ hχ hreal).2])
  set F : ℂ → ℂ := fun s => riemannZeta s * DirichletCharacter.LFunction χ s
  set G : ℂ → ℂ := regZetaMul (DirichletCharacter.LFunction χ)
  set M : ℝ := 200 * (q : ℝ)
  have hM1 : 1 ≤ M := by dsimp only [M]; linarith
  have hG_diff : DifferentiableOn ℂ G {s : ℂ | 0 < s.re} :=
    differentiableOn_regZetaMul (DirichletCharacter.differentiable_LFunction hχ)
  have hGF : ∀ s : ℂ, 0 < s.re → s ≠ 1 → G s = F s - (lam : ℂ) / (s - 1) := by
    intro s hs hs1
    dsimp only [G, F]
    rw [regZetaMul_eq hs hs1, hlam_eq]
  have hM_bd : ∀ s ∈ Metric.sphere (2 : ℂ) (3 / 2), ‖G s‖ ≤ M := by
    intro s hs
    have hs_re : 0 < s.re := by
      rw [Metric.mem_sphere, dist_eq_norm] at hs
      have hre := abs_le.mp ((Complex.abs_re_le_norm (s - 2)).trans hs.le)
      simp only [Complex.sub_re, Complex.re_ofNat] at hre; linarith
    have hs1_ge : (1 / 2 : ℝ) ≤ ‖s - 1‖ := by
      rw [Metric.mem_sphere, dist_eq_norm] at hs
      have h := norm_add_le (s - 1) (-1)
      have h1 : (s - 1) + (-1 : ℂ) = s - 2 := by ring
      rw [h1, hs, norm_neg, norm_one] at h; linarith
    have hs1_ne : s ≠ 1 := fun h => by subst h; norm_num at hs1_ge
    rw [hGF s hs_re hs1_ne]
    have hζ := norm_riemannZeta_le_of_mem_sphere hs
    have hL := norm_LFunction_le_of_mem_sphere hχ hs
    have hL1 : ‖DirichletCharacter.LFunction χ 1‖ ≤ 6 * (q : ℝ) := by
      have h := norm_LFunction_strip_le hχ (s := 1) (by norm_num) (by norm_num)
      simp only [Complex.one_im, abs_zero, zero_add] at h
      linarith
    have hinv : ‖(lam : ℂ) / (s - 1)‖ ≤ 12 * (q : ℝ) := by
      rw [hlam_eq, norm_div, div_le_iff₀ (by linarith)]
      nlinarith
    calc ‖riemannZeta s * DirichletCharacter.LFunction χ s - (lam : ℂ) / (s - 1)‖
        ≤ ‖riemannZeta s‖ * ‖DirichletCharacter.LFunction χ s‖ + ‖(lam : ℂ) / (s - 1)‖ := by
          rw [← norm_mul]; exact norm_sub_le _ _
      _ ≤ 10 * (15 * (q : ℝ)) + 12 * (q : ℝ) := by
          gcongr
      _ ≤ M := by dsimp only [M]; linarith
  
  set β : ℝ := 1 - δ
  have hβ_lo : 3 / 4 ≤ β := by dsimp only [β]; linarith
  have hβ_hi : β < 1 := by dsimp only [β]; linarith
  have hF_nonpos : (F (β : ℂ)).re ≤ 0 := by
    dsimp only [F]
    have hζ := riemannZeta_neg_on_Ioo (by linarith : 0 < β) hβ_hi
    have hL_im := LFunction_im_eq_zero_of_real hχ hreal (by linarith : 0 < β)
    rw [Complex.mul_re, hζ.2, hL_im, mul_zero, sub_zero]
    exact mul_nonpos_of_nonpos_of_nonneg hζ.1.le hL_nn
  have hest := estermann_residue_lower_bound_of_nonpos
    (divisorCharSum_zero χ) (by rw [divisorCharSum_one]) (divisorCharSum_nonneg hreal)
    (fun x hx => (LSeries_divisorCharSum_eq hreal (by simpa using hx)).1)
    hM1 hG_diff hGF (fun s hs => (LSeries_divisorCharSum_eq hreal hs).2.symm)
    hM_bd hβ_lo hβ_hi hF_nonpos
  have h1β : 1 - β = δ := by dsimp only [β]; ring
  have h12M : 12 * M = 2400 * (q : ℝ) := by dsimp only [M]; ring
  rwa [h1β, h12M] at hest

theorem LFunction_one_lower_bound_of_no_real_zero {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (hreal : IsRealChar χ) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 4)
    (hnozero : ∀ σ : ℝ, 1 - δ ≤ σ → σ < 1 → DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0) :
    δ / (4 * (2400 * (q : ℝ)) ^ (6 * δ)) ≤ (DirichletCharacter.LFunction χ 1).re := by
  apply LFunction_one_lower_bound_of_re_nonneg hχ hreal hδ0 hδ
  by_contra hneg; push Not at hneg
  have hpos1 : 0 < (DirichletCharacter.LFunction χ ((1 : ℝ) : ℂ)).re := by
    simpa using (LFunction_one_pos_of_real χ hχ hreal).1
  have hcont : ContinuousOn (fun σ : ℝ => (DirichletCharacter.LFunction χ (σ : ℂ)).re)
      (Set.Icc (1 - δ) 1) :=
    (Complex.continuous_re.comp
      ((DirichletCharacter.differentiable_LFunction hχ).continuous.comp
        Complex.continuous_ofReal)).continuousOn
  have hmem : (0 : ℝ) ∈ Set.Icc
      (DirichletCharacter.LFunction χ ((1 - δ : ℝ) : ℂ)).re
      (DirichletCharacter.LFunction χ ((1 : ℝ) : ℂ)).re :=
    ⟨hneg.le, hpos1.le⟩
  obtain ⟨β, hβ_mem, hβ_re⟩ := intermediate_value_Icc (by linarith : 1 - δ ≤ 1) hcont hmem
  have hβ_lt1 : β < 1 := lt_of_le_of_ne hβ_mem.2 fun h1 => by rw [h1] at hβ_re; linarith
  have hβ_pos : 0 < β := by linarith [hβ_mem.1]
  have hβ_im := LFunction_im_eq_zero_of_real hχ hreal hβ_pos
  have hzero : DirichletCharacter.LFunction χ (β : ℂ) = 0 :=
    Complex.ext (by simpa using hβ_re) (by simpa using hβ_im)
  exact hnozero β hβ_mem.1 hβ_lt1 hzero

theorem exists_real_zero_of_LFunction_one_lt {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (hreal : IsRealChar χ) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 4)
    (hlt : (DirichletCharacter.LFunction χ 1).re < δ / (4 * (2400 * (q : ℝ)) ^ (6 * δ))) :
    ∃ β : ℝ, 1 - δ ≤ β ∧ β < 1 ∧ DirichletCharacter.LFunction χ (β : ℂ) = 0 := by
  by_contra hno
  push Not at hno
  have hge := LFunction_one_lower_bound_of_no_real_zero hχ hreal hδ0 hδ hno
  linarith

set_option maxHeartbeats 2000000 in
theorem tatuzawa_two_char_effective_L1_lower_bound {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 4)
    {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    {χ₁ : DirichletCharacter ℂ q₁} {χ₂ : DirichletCharacter ℂ q₂}
    (hprim1 : χ₁.IsPrimitive) (hprim2 : χ₂.IsPrimitive)
    (hreal1 : IsRealChar χ₁) (hreal2 : IsRealChar χ₂)
    (h1ne : χ₁ ≠ 1) (h2ne : χ₂ ≠ 1)
    (hne : PChar.of χ₁ ≠ PChar.of χ₂) :
    ¬ ((DirichletCharacter.LFunction χ₁ 1).re < (ε / 100000) / (q₁ : ℝ) ^ ε ∧
       (DirichletCharacter.LFunction χ₂ 1).re < (ε / 100000) / (q₂ : ℝ) ^ ε) := by
  
  suffices hsym : ∀ {r₁ r₂ : ℕ} [NeZero r₁] [NeZero r₂]
      {φ₁ : DirichletCharacter ℂ r₁} {φ₂ : DirichletCharacter ℂ r₂},
      r₁ ≤ r₂ → φ₁.IsPrimitive → φ₂.IsPrimitive →
      IsRealChar φ₁ → IsRealChar φ₂ → φ₁ ≠ 1 → φ₂ ≠ 1 →
      PChar.of φ₁ ≠ PChar.of φ₂ →
      ¬ ((DirichletCharacter.LFunction φ₁ 1).re < (ε / 100000) / (r₁ : ℝ) ^ ε ∧
         (DirichletCharacter.LFunction φ₂ 1).re < (ε / 100000) / (r₂ : ℝ) ^ ε) by
    rcases le_total q₁ q₂ with hle | hle
    · exact hsym hle hprim1 hprim2 hreal1 hreal2 h1ne h2ne hne
    · intro ⟨h1, h2⟩
      exact hsym hle hprim2 hprim1 hreal2 hreal1 h2ne h1ne hne.symm ⟨h2, h1⟩
  intro r₁ r₂ _ _ φ₁ φ₂ hr_le hprim1 hprim2 hreal1 hreal2 h1ne h2ne hne ⟨hlt1, hlt2⟩
  have hr1_ge2 : 2 ≤ r₁ := two_le_of_dirichletChar_ne_one h1ne
  have hr2_ge2 : 2 ≤ r₂ := two_le_of_dirichletChar_ne_one h2ne
  have hr1_R : (2 : ℝ) ≤ (r₁ : ℝ) := by exact_mod_cast hr1_ge2
  have hr2_R : (2 : ℝ) ≤ (r₂ : ℝ) := by exact_mod_cast hr2_ge2
  have hr_leR : (r₁ : ℝ) ≤ (r₂ : ℝ) := by exact_mod_cast hr_le
  
  set η : ℝ := ε / 24
  have hη0 : 0 < η := by positivity
  have hη_le : η ≤ 1 / 4 := by dsimp only [η]; linarith
  have h6η_eq : 6 * η = ε / 4 := by dsimp only [η]; ring
  have hstep1 : ∀ {r : ℕ} [NeZero r], (2 : ℝ) ≤ (r : ℝ) →
      (ε / 100000) / (r : ℝ) ^ ε ≤ η / (4 * (2400 * (r : ℝ)) ^ (6 * η)) := by
    intro r _ hr
    have h2400 : (2400 : ℝ) ^ (6 * η) ≤ 50 := by
      have h1 : (2400 : ℝ) ^ (6 * η) ≤ (2400 : ℝ) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by rw [h6η_eq]; linarith)
      have h2 : (2400 : ℝ) ^ (1 / 2 : ℝ) ≤ 50 := by
        rw [← Real.sqrt_eq_rpow]
        exact Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
      exact h1.trans h2
    have hr_pow : (r : ℝ) ^ (6 * η) ≤ (r : ℝ) ^ ε :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by rw [h6η_eq]; linarith)
    have hprod : 4 * (2400 * (r : ℝ)) ^ (6 * η) ≤ 200 * (r : ℝ) ^ ε := by
      rw [Real.mul_rpow (by norm_num) (by linarith)]
      have h1 : (2400 : ℝ) ^ (6 * η) * (r : ℝ) ^ (6 * η) ≤ 50 * (r : ℝ) ^ ε :=
        mul_le_mul h2400 hr_pow (Real.rpow_nonneg (by linarith) _) (by norm_num)
      linarith
    have hden_pos : 0 < 4 * (2400 * (r : ℝ)) ^ (6 * η) := by positivity
    calc (ε / 100000) / (r : ℝ) ^ ε
        ≤ η / (200 * (r : ℝ) ^ ε) := by
          dsimp only [η]
          rw [show (ε / 24) / (200 * (r : ℝ) ^ ε) = (ε / 4800) / (r : ℝ) ^ ε by ring]
          exact div_le_div_of_nonneg_right (by linarith) (Real.rpow_nonneg (by linarith) _)
      _ ≤ η / (4 * (2400 * (r : ℝ)) ^ (6 * η)) :=
          div_le_div_of_nonneg_left hη0.le hden_pos hprod
  obtain ⟨β₁, hβ₁_lo, hβ₁_lt1, hz1⟩ :=
    exists_real_zero_of_LFunction_one_lt h1ne hreal1 hη0 hη_le (hlt1.trans_le (hstep1 hr1_R))
  obtain ⟨β₂, hβ₂_lo, hβ₂_lt1, hz2⟩ :=
    exists_real_zero_of_LFunction_one_lt h2ne hreal2 hη0 hη_le (hlt2.trans_le (hstep1 hr2_R))
  
  set β : ℝ := min β₁ β₂
  have hβ_lo : 1 - η ≤ β := le_min hβ₁_lo hβ₂_lo
  have hβ_hi : β < 1 := lt_of_le_of_lt (min_le_left β₁ β₂) hβ₁_lt1
  have hβ_ge34 : 3 / 4 ≤ β := by linarith
  have hpage := page_landau_two_distinct_nonprincipal_real_explicit (Q := (r₂ : ℝ)) hr2_R
    hr_leR le_rfl hprim1 hprim2 h1ne h2ne hreal1 hreal2 hne hz1 hz2
  have h1β_ge : 1 / (3000 * Real.log (2 * (r₂ : ℝ))) ≤ 1 - β := by linarith
  have h1β_le : 1 - β ≤ η := by linarith
  
  set ψ₁ : PChar := ⟨r₁, φ₁, hprim1⟩
  set ψ₂ : PChar := ⟨r₂, φ₂, hprim2⟩
  have hψ_ne : ψ₁ ≠ ψ₂ := by
    intro heq; apply hne
    rw [show PChar.of φ₁ = ψ₁ from PChar.of_self ψ₁,
      show PChar.of φ₂ = ψ₂ from PChar.of_self ψ₂, heq]
  have h12_ne : prodChar φ₁ φ₂ ≠ 1 :=
    prodChar_ne_one_of_distinct_primitive_real (ψ₁ := ψ₁) (ψ₂ := ψ₂) hreal1 hψ_ne
  have hreal12 : IsRealChar (prodChar φ₁ φ₂) := isRealChar_prodChar hreal1 hreal2
  set H : ℂ → ℂ := fun s =>
    DirichletCharacter.LFunction φ₁ s * DirichletCharacter.LFunction φ₂ s *
      DirichletCharacter.LFunction (prodChar φ₁ φ₂) s
  have hH_diff : Differentiable ℂ H :=
    ((DirichletCharacter.differentiable_LFunction h1ne).mul
      (DirichletCharacter.differentiable_LFunction h2ne)).mul
      (DirichletCharacter.differentiable_LFunction h12_ne)
  have hL1_pos := LFunction_one_pos_of_real φ₁ h1ne hreal1
  have hL2_pos := LFunction_one_pos_of_real φ₂ h2ne hreal2
  have hL12_pos := LFunction_one_pos_of_real (prodChar φ₁ φ₂) h12_ne hreal12
  set lam : ℝ :=
    (DirichletCharacter.LFunction φ₁ 1).re * (DirichletCharacter.LFunction φ₂ 1).re *
      (DirichletCharacter.LFunction (prodChar φ₁ φ₂) 1).re
  have hH1_eq : (lam : ℂ) = H 1 := by
    dsimp only [lam, H]
    have h1 : ((DirichletCharacter.LFunction φ₁ 1).re : ℂ) = DirichletCharacter.LFunction φ₁ 1 :=
      Complex.ext (by simp) (by simp [hL1_pos.2])
    have h2 : ((DirichletCharacter.LFunction φ₂ 1).re : ℂ) = DirichletCharacter.LFunction φ₂ 1 :=
      Complex.ext (by simp) (by simp [hL2_pos.2])
    have h3 : ((DirichletCharacter.LFunction (prodChar φ₁ φ₂) 1).re : ℂ) =
        DirichletCharacter.LFunction (prodChar φ₁ φ₂) 1 :=
      Complex.ext (by simp) (by simp [hL12_pos.2])
    push_cast; rw [h1, h2, h3]
  set F : ℂ → ℂ := fun s => riemannZeta s * H s
  set G : ℂ → ℂ := regZetaMul H
  set M : ℝ := 40000 * ((r₁ : ℝ) * (r₂ : ℝ)) ^ 2
  have hM1 : 1 ≤ M := by
    have h4 : (4 : ℝ) ≤ (r₁ : ℝ) * (r₂ : ℝ) := by nlinarith
    dsimp only [M]; nlinarith
  have hG_diff : DifferentiableOn ℂ G {s : ℂ | 0 < s.re} := differentiableOn_regZetaMul hH_diff
  have hGF : ∀ s : ℂ, 0 < s.re → s ≠ 1 → G s = F s - (lam : ℂ) / (s - 1) := by
    intro s hs hs1
    dsimp only [G, F]
    rw [regZetaMul_eq hs hs1, hH1_eq]
  have hM_bd : ∀ s ∈ Metric.sphere (2 : ℂ) (3 / 2), ‖G s‖ ≤ M := by
    intro s hs
    have hs_re : 0 < s.re := by
      rw [Metric.mem_sphere, dist_eq_norm] at hs
      have hre := abs_le.mp ((Complex.abs_re_le_norm (s - 2)).trans hs.le)
      simp only [Complex.sub_re, Complex.re_ofNat] at hre; linarith
    have hs1_ge : (1 / 2 : ℝ) ≤ ‖s - 1‖ := by
      rw [Metric.mem_sphere, dist_eq_norm] at hs
      have h := norm_add_le (s - 1) (-1)
      have h1 : (s - 1) + (-1 : ℂ) = s - 2 := by ring
      rw [h1, hs, norm_neg, norm_one] at h; linarith
    have hs1_ne : s ≠ 1 := fun h => by subst h; norm_num at hs1_ge
    rw [hGF s hs_re hs1_ne]
    have hζ := norm_riemannZeta_le_of_mem_sphere hs
    have hL1 := norm_LFunction_le_of_mem_sphere h1ne hs
    have hL2 := norm_LFunction_le_of_mem_sphere h2ne hs
    have hL12 : ‖DirichletCharacter.LFunction (prodChar φ₁ φ₂) s‖ ≤ 15 * ((r₁ : ℝ) * (r₂ : ℝ)) := by
      simpa [Nat.cast_mul] using norm_LFunction_le_of_mem_sphere h12_ne hs
    have hHs : ‖H s‖ ≤ 3375 * ((r₁ : ℝ) * (r₂ : ℝ)) ^ 2 := by
      dsimp only [H]
      rw [norm_mul, norm_mul]
      have h1 : ‖DirichletCharacter.LFunction φ₁ s‖ * ‖DirichletCharacter.LFunction φ₂ s‖ ≤
          (15 * (r₁ : ℝ)) * (15 * (r₂ : ℝ)) :=
        mul_le_mul hL1 hL2 (norm_nonneg _) (by positivity)
      have h2 := mul_le_mul h1 hL12 (norm_nonneg _) (by positivity)
      linarith
    have hH1_norm : ‖H 1‖ ≤ 216 * ((r₁ : ℝ) * (r₂ : ℝ)) ^ 2 := by
      dsimp only [H]
      rw [norm_mul, norm_mul]
      have hb1 : ‖DirichletCharacter.LFunction φ₁ 1‖ ≤ 6 * (r₁ : ℝ) := by
        have h := norm_LFunction_strip_le h1ne (s := 1) (by norm_num) (by norm_num)
        simp only [Complex.one_im, abs_zero, zero_add] at h; linarith
      have hb2 : ‖DirichletCharacter.LFunction φ₂ 1‖ ≤ 6 * (r₂ : ℝ) := by
        have h := norm_LFunction_strip_le h2ne (s := 1) (by norm_num) (by norm_num)
        simp only [Complex.one_im, abs_zero, zero_add] at h; linarith
      have hb12 : ‖DirichletCharacter.LFunction (prodChar φ₁ φ₂) 1‖ ≤ 6 * ((r₁ : ℝ) * (r₂ : ℝ)) := by
        have h := norm_LFunction_strip_le h12_ne (s := 1) (by norm_num) (by norm_num)
        simp only [Complex.one_im, abs_zero, zero_add, Nat.cast_mul] at h; nlinarith
      have h1 := mul_le_mul hb1 hb2 (norm_nonneg _) (by positivity)
      have h2 := mul_le_mul h1 hb12 (norm_nonneg _) (by positivity)
      linarith
    have hinv : ‖(lam : ℂ) / (s - 1)‖ ≤ 432 * ((r₁ : ℝ) * (r₂ : ℝ)) ^ 2 := by
      rw [hH1_eq, norm_div, div_le_iff₀ (by linarith)]
      nlinarith
    calc ‖riemannZeta s * H s - (lam : ℂ) / (s - 1)‖
        ≤ ‖riemannZeta s‖ * ‖H s‖ + ‖(lam : ℂ) / (s - 1)‖ := by
          rw [← norm_mul]; exact norm_sub_le _ _
      _ ≤ 10 * (3375 * ((r₁ : ℝ) * (r₂ : ℝ)) ^ 2) + 432 * ((r₁ : ℝ) * (r₂ : ℝ)) ^ 2 := by
          gcongr
      _ ≤ M := by dsimp only [M]; nlinarith
  have hagree : ∀ s : ℂ, 1 < s.re → F s = dirSeries (fourCharCoeff φ₁ φ₂) s := by
    intro s hs
    have h := (LSeries_fourCharCoeff_eq hreal1 hreal2 hs).2
    dsimp only [F, H]
    rw [h]; ring
  have hF_zero : (F (β : ℂ)).re ≤ 0 := by
    have h0 : F (β : ℂ) = 0 := by
      dsimp only [F, H, β]
      rcases min_choice β₁ β₂ with hβeq | hβeq
      · rw [hβeq, hz1]; ring
      · rw [hβeq, hz2]; ring
    rw [h0, Complex.zero_re]
  have hest := estermann_residue_lower_bound_of_nonpos
    (fourCharCoeff_zero φ₁ φ₂) (by rw [fourCharCoeff_one]) (fourCharCoeff_nonneg hreal1 hreal2)
    (fun x hx => (LSeries_fourCharCoeff_eq hreal1 hreal2 (by simpa using hx)).1)
    hM1 hG_diff hGF hagree hM_bd hβ_ge34 hβ_hi hF_zero
  
  have h6_1β : 6 * (1 - β) ≤ ε / 4 := by linarith
  have h12M_le : (12 * M) ^ (6 * (1 - β)) ≤ 700 * ((r₁ : ℝ) * (r₂ : ℝ)) ^ (ε / 2) := by
    have h12M_eq : 12 * M = 480000 * ((r₁ : ℝ) * (r₂ : ℝ)) ^ 2 := by dsimp only [M]; ring
    rw [h12M_eq, Real.mul_rpow (by norm_num) (by positivity)]
    have h480 : (480000 : ℝ) ^ (6 * (1 - β)) ≤ 700 := by
      have h1 : (480000 : ℝ) ^ (6 * (1 - β)) ≤ (480000 : ℝ) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      have h2 : (480000 : ℝ) ^ (1 / 2 : ℝ) ≤ 700 := by
        rw [← Real.sqrt_eq_rpow]
        exact Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
      exact h1.trans h2
    have hpow2 : (((r₁ : ℝ) * (r₂ : ℝ)) ^ 2) ^ (6 * (1 - β)) ≤ ((r₁ : ℝ) * (r₂ : ℝ)) ^ (ε / 2) := by
      rw [← Real.rpow_natCast ((r₁ : ℝ) * (r₂ : ℝ)) 2, ← Real.rpow_mul (by positivity)]
      exact Real.rpow_le_rpow_of_exponent_le (by nlinarith) (by push_cast; linarith)
    exact mul_le_mul h480 hpow2 (Real.rpow_nonneg (by positivity) _) (by norm_num)
  have hlog2r2_pos : 0 < Real.log (2 * (r₂ : ℝ)) := Real.log_pos (by linarith)
  have hlam_lo :
      1 / (8400000 * Real.log (2 * (r₂ : ℝ)) * ((r₁ : ℝ) * (r₂ : ℝ)) ^ (ε / 2)) ≤ lam := by
    have hden_pos : 0 < 4 * (12 * M) ^ (6 * (1 - β)) := by positivity
    have h1 : (1 / (3000 * Real.log (2 * (r₂ : ℝ)))) / (4 * (700 * ((r₁ : ℝ) * (r₂ : ℝ)) ^ (ε / 2))) ≤
        (1 - β) / (4 * (12 * M) ^ (6 * (1 - β))) := by
      calc (1 / (3000 * Real.log (2 * (r₂ : ℝ)))) / (4 * (700 * ((r₁ : ℝ) * (r₂ : ℝ)) ^ (ε / 2)))
          ≤ (1 - β) / (4 * (700 * ((r₁ : ℝ) * (r₂ : ℝ)) ^ (ε / 2))) :=
            div_le_div_of_nonneg_right h1β_ge (by positivity)
        _ ≤ (1 - β) / (4 * (12 * M) ^ (6 * (1 - β))) :=
            div_le_div_of_nonneg_left (by linarith) hden_pos (by linarith)
    have h2 : (1 / (3000 * Real.log (2 * (r₂ : ℝ)))) /
          (4 * (700 * ((r₁ : ℝ) * (r₂ : ℝ)) ^ (ε / 2))) =
        1 / (8400000 * Real.log (2 * (r₂ : ℝ)) * ((r₁ : ℝ) * (r₂ : ℝ)) ^ (ε / 2)) := by
      field_simp [hlog2r2_pos.ne', (Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < (r₁ : ℝ) * (r₂ : ℝ)) _).ne']
      ring
    rw [← h2]
    exact h1.trans hest
  
  have hL12_up : (DirichletCharacter.LFunction (prodChar φ₁ φ₂) 1).re ≤ 10 * Real.log (2 * (r₂ : ℝ)) := by
    have hup := norm_LFunction_le_log_of_one_le_re h12_ne (s := 1) (by simp) (by simp)
    simp only [Complex.one_im, abs_zero, zero_add, Nat.cast_mul] at hup
    have hre : (DirichletCharacter.LFunction (prodChar φ₁ φ₂) 1).re ≤
        5 * Real.log ((r₁ : ℝ) * (r₂ : ℝ) * 2) :=
      ((le_abs_self _).trans (Complex.abs_re_le_norm _)).trans hup
    have hlog_sq : Real.log ((r₁ : ℝ) * (r₂ : ℝ) * 2) ≤ 2 * Real.log (2 * (r₂ : ℝ)) := by
      have hsq : (r₁ : ℝ) * (r₂ : ℝ) * 2 ≤ (2 * (r₂ : ℝ)) ^ 2 := by nlinarith
      have h1 := Real.log_le_log (by positivity) hsq
      rw [Real.log_pow] at h1; push_cast at h1; exact h1
    linarith
  have hlam_up :
      lam < 10 * (ε / 100000) ^ 2 * Real.log (2 * (r₂ : ℝ)) / ((r₁ : ℝ) * (r₂ : ℝ)) ^ ε := by
    have hmul12 :
        (DirichletCharacter.LFunction φ₁ 1).re * (DirichletCharacter.LFunction φ₂ 1).re <
          ((ε / 100000) / (r₁ : ℝ) ^ ε) * ((ε / 100000) / (r₂ : ℝ) ^ ε) :=
      mul_lt_mul'' hlt1 hlt2 hL1_pos.1.le hL2_pos.1.le
    have hprod_eq :
        ((ε / 100000) / (r₁ : ℝ) ^ ε) * ((ε / 100000) / (r₂ : ℝ) ^ ε) =
          (ε / 100000) ^ 2 / ((r₁ : ℝ) * (r₂ : ℝ)) ^ ε := by
      rw [Real.mul_rpow (by linarith) (by linarith)]
      ring
    rw [hprod_eq] at hmul12
    have h3 :
        (DirichletCharacter.LFunction φ₁ 1).re * (DirichletCharacter.LFunction φ₂ 1).re *
          (DirichletCharacter.LFunction (prodChar φ₁ φ₂) 1).re <
        ((ε / 100000) ^ 2 / ((r₁ : ℝ) * (r₂ : ℝ)) ^ ε) * (10 * Real.log (2 * (r₂ : ℝ))) := by
      calc (DirichletCharacter.LFunction φ₁ 1).re * (DirichletCharacter.LFunction φ₂ 1).re *
              (DirichletCharacter.LFunction (prodChar φ₁ φ₂) 1).re
          ≤ (DirichletCharacter.LFunction φ₁ 1).re * (DirichletCharacter.LFunction φ₂ 1).re *
              (10 * Real.log (2 * (r₂ : ℝ))) :=
            mul_le_mul_of_nonneg_left hL12_up (mul_nonneg hL1_pos.1.le hL2_pos.1.le)
        _ < ((ε / 100000) ^ 2 / ((r₁ : ℝ) * (r₂ : ℝ)) ^ ε) * (10 * Real.log (2 * (r₂ : ℝ))) :=
            mul_lt_mul_of_pos_right hmul12 (by positivity)
    dsimp only [lam]
    linarith [show ((ε / 100000) ^ 2 / ((r₁ : ℝ) * (r₂ : ℝ)) ^ ε) * (10 * Real.log (2 * (r₂ : ℝ))) =
        10 * (ε / 100000) ^ 2 * Real.log (2 * (r₂ : ℝ)) / ((r₁ : ℝ) * (r₂ : ℝ)) ^ ε by ring]
  
  have hlog_sq_bd : (Real.log (2 * (r₂ : ℝ))) ^ 2 ≤ (64 / ε ^ 2) * ((r₁ : ℝ) * (r₂ : ℝ)) ^ (ε / 2) := by
    have hlog1 : Real.log (2 * (r₂ : ℝ)) ≤ (2 * (r₂ : ℝ)) ^ (ε / 8) / (ε / 8) :=
      Real.log_le_rpow_div (by linarith) (by positivity)
    have h2r2_sq : 2 * (r₂ : ℝ) ≤ (r₂ : ℝ) ^ 2 := by nlinarith
    have hpow1 : (2 * (r₂ : ℝ)) ^ (ε / 8) ≤ (r₂ : ℝ) ^ (ε / 4) := by
      have h := Real.rpow_le_rpow (by linarith) h2r2_sq (by positivity : (0 : ℝ) ≤ ε / 8)
      rw [← Real.rpow_natCast (r₂ : ℝ) 2, ← Real.rpow_mul (by linarith)] at h
      have hexp : ((2 : ℕ) : ℝ) * (ε / 8) = ε / 4 := by push_cast; ring
      rwa [hexp] at h
    have hlog2 : Real.log (2 * (r₂ : ℝ)) ≤ (8 / ε) * (r₂ : ℝ) ^ (ε / 4) := by
      have h1 : (2 * (r₂ : ℝ)) ^ (ε / 8) / (ε / 8) = (8 / ε) * (2 * (r₂ : ℝ)) ^ (ε / 8) := by
        field_simp [hε0.ne']
      rw [h1] at hlog1
      exact hlog1.trans (mul_le_mul_of_nonneg_left hpow1 (by positivity))
    have hsq := pow_le_pow_left₀ hlog2r2_pos.le hlog2 2
    rw [mul_pow, ← Real.rpow_natCast ((r₂ : ℝ) ^ (ε / 4)) 2, ← Real.rpow_mul (by linarith)] at hsq
    have hexp2 : ε / 4 * ((2 : ℕ) : ℝ) = ε / 2 := by push_cast; ring
    rw [hexp2] at hsq
    have hr2_le_prod : (r₂ : ℝ) ^ (ε / 2) ≤ ((r₁ : ℝ) * (r₂ : ℝ)) ^ (ε / 2) :=
      Real.rpow_le_rpow (by linarith) (by nlinarith) (by positivity)
    calc (Real.log (2 * (r₂ : ℝ))) ^ 2
        ≤ (8 / ε) ^ 2 * (r₂ : ℝ) ^ (ε / 2) := hsq
      _ ≤ (8 / ε) ^ 2 * ((r₁ : ℝ) * (r₂ : ℝ)) ^ (ε / 2) :=
          mul_le_mul_of_nonneg_left hr2_le_prod (by positivity)
      _ = (64 / ε ^ 2) * ((r₁ : ℝ) * (r₂ : ℝ)) ^ (ε / 2) := by ring
  
  have hcomb := hlam_lo.trans_lt hlam_up
  have hpow_pos : 0 < ((r₁ : ℝ) * (r₂ : ℝ)) ^ (ε / 2) := Real.rpow_pos_of_pos (by positivity) _
  have hpow_sq : ((r₁ : ℝ) * (r₂ : ℝ)) ^ ε = (((r₁ : ℝ) * (r₂ : ℝ)) ^ (ε / 2)) ^ 2 := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity)]
    congr 1; push_cast; ring
  rw [hpow_sq] at hcomb
  have hden1 : 0 < 8400000 * Real.log (2 * (r₂ : ℝ)) * ((r₁ : ℝ) * (r₂ : ℝ)) ^ (ε / 2) := by positivity
  have hden2 : 0 < (((r₁ : ℝ) * (r₂ : ℝ)) ^ (ε / 2)) ^ 2 := sq_pos_of_pos hpow_pos
  have hcross := (div_lt_div_iff₀ hden1 hden2).mp hcomb
  
  have hcancel :
      ((r₁ : ℝ) * (r₂ : ℝ)) ^ (ε / 2) <
        84000000 * (ε / 100000) ^ 2 * (Real.log (2 * (r₂ : ℝ))) ^ 2 := by
    nlinarith
  have hfinal :
      84000000 * (ε / 100000) ^ 2 * (Real.log (2 * (r₂ : ℝ))) ^ 2 ≤
        (5376000000 / 100000 ^ 2 : ℝ) * ((r₁ : ℝ) * (r₂ : ℝ)) ^ (ε / 2) := by
    calc 84000000 * (ε / 100000) ^ 2 * (Real.log (2 * (r₂ : ℝ))) ^ 2
        ≤ 84000000 * (ε / 100000) ^ 2 * ((64 / ε ^ 2) * ((r₁ : ℝ) * (r₂ : ℝ)) ^ (ε / 2)) :=
          mul_le_mul_of_nonneg_left hlog_sq_bd (by positivity)
      _ = (5376000000 / 100000 ^ 2 : ℝ) * ((r₁ : ℝ) * (r₂ : ℝ)) ^ (ε / 2) := by
          field_simp [hε0.ne']; ring
  nlinarith

theorem tatuzawa_effective_L1_lower_bound {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 4) :
    ∃ ψ₁ : PChar,
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        χ.IsPrimitive → IsRealChar χ → χ ≠ 1 →
        PChar.of χ ≠ ψ₁ →
        (ε / 100000) / (q : ℝ) ^ ε ≤ (DirichletCharacter.LFunction χ 1).re := by
  by_cases hex : ∃ (q₀ : ℕ) (_ : NeZero q₀) (χ₀ : DirichletCharacter ℂ q₀),
      χ₀.IsPrimitive ∧ IsRealChar χ₀ ∧ χ₀ ≠ 1 ∧
      (DirichletCharacter.LFunction χ₀ 1).re < (ε / 100000) / (q₀ : ℝ) ^ ε
  · rcases hex with ⟨q₀, _, χ₀, hprim0, hreal0, hχ0ne, hlt0⟩
    refine ⟨PChar.of χ₀, fun q _ χ hprim hreal hχne hne => ?_⟩
    by_contra hlt; push Not at hlt
    exact tatuzawa_two_char_effective_L1_lower_bound hε0 hε hprim0 hprim hreal0 hreal
      hχ0ne hχne hne.symm ⟨hlt0, hlt⟩
  · push Not at hex
    refine ⟨PChar.of (1 : DirichletCharacter ℂ 1), fun q hne χ hprim hreal hχne _ => ?_⟩
    exact hex q hne χ hprim hreal hχne

private lemma LFunction_eq_of_pchar_eq {ψ₁ ψ₂ : PChar} (heq : ψ₁ = ψ₂) :
    ψ₁.N = ψ₂.N ∧ ∀ s : ℂ, DirichletCharacter.LFunction ψ₁.χ s = DirichletCharacter.LFunction ψ₂.χ s := by
  subst heq
  exact ⟨rfl, fun _ => rfl⟩

private lemma LFunction_eq_of_pchar_of_eq {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    {χ₁ : DirichletCharacter ℂ q₁} {χ₂ : DirichletCharacter ℂ q₂}
    (hprim1 : χ₁.IsPrimitive) (hprim2 : χ₂.IsPrimitive)
    (heq : PChar.of χ₁ = PChar.of χ₂) :
    q₁ = q₂ ∧ ∀ s : ℂ, DirichletCharacter.LFunction χ₁ s = DirichletCharacter.LFunction χ₂ s := by
  set ψ₁ : PChar := ⟨q₁, χ₁, hprim1⟩
  set ψ₂ : PChar := ⟨q₂, χ₂, hprim2⟩
  have hψ : ψ₁ = ψ₂ := by
    rw [← PChar.of_self ψ₁, ← PChar.of_self ψ₂]
    exact heq
  exact LFunction_eq_of_pchar_eq hψ

theorem siegel_theorem_L1_lower_bound :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧
        ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
          χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 →
          C / (q : ℝ) ^ ε ≤ (DirichletCharacter.LFunction χ 1).re := by
  intro ε hε0
  set ε' : ℝ := min ε (1 / 8)
  have hε'0 : 0 < ε' := lt_min hε0 (by norm_num)
  have hε'lt : ε' < 1 / 4 := (min_le_right ε (1 / 8)).trans_lt (by norm_num)
  have hε'le : ε' ≤ ε := min_le_left ε (1 / 8)
  obtain ⟨ψ₁, htat⟩ := tatuzawa_effective_L1_lower_bound hε'0 hε'lt
  by_cases hψ : ψ₁.IsReal ∧ ψ₁.χ ≠ 1
  · have hpos1 : 0 < (DirichletCharacter.LFunction ψ₁.χ 1).re :=
      (LFunction_one_pos_of_real ψ₁.χ hψ.2 hψ.1).1
    have hN1_pos : (0 : ℝ) < (ψ₁.N : ℝ) := Nat.cast_pos.mpr (NeZero.pos ψ₁.N)
    set v : ℝ := (DirichletCharacter.LFunction ψ₁.χ 1).re * (ψ₁.N : ℝ) ^ ε'
    have hv_pos : 0 < v := mul_pos hpos1 (Real.rpow_pos_of_pos hN1_pos ε')
    set C : ℝ := min (ε' / 100000) v
    have hC_pos : 0 < C := lt_min (by positivity) hv_pos
    refine ⟨C, hC_pos, fun q _ χ hprim hsq hχne => ?_⟩
    have hreal : IsRealChar χ := isRealChar_of_sq_eq_one hsq
    have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast NeZero.pos q
    have hpow_le : (q : ℝ) ^ ε' ≤ (q : ℝ) ^ ε := Real.rpow_le_rpow_of_exponent_le hq1 hε'le
    by_cases hne : PChar.of χ ≠ ψ₁
    · have h1 := htat q χ hprim hreal hχne hne
      calc C / (q : ℝ) ^ ε
          ≤ (ε' / 100000) / (q : ℝ) ^ ε :=
            div_le_div_of_nonneg_right (min_le_left _ _) (Real.rpow_nonneg (by linarith) _)
        _ ≤ (ε' / 100000) / (q : ℝ) ^ ε' :=
            div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos (by linarith) _) hpow_le
        _ ≤ (DirichletCharacter.LFunction χ 1).re := h1
    · push Not at hne
      have hof : PChar.of χ = PChar.of ψ₁.χ := by rwa [PChar.of_self ψ₁]
      obtain ⟨hqeq, hLeq⟩ := LFunction_eq_of_pchar_of_eq hprim ψ₁.prim hof
      calc C / (q : ℝ) ^ ε
          ≤ v / (q : ℝ) ^ ε :=
            div_le_div_of_nonneg_right (min_le_right _ _) (Real.rpow_nonneg (by linarith) _)
        _ ≤ v / (q : ℝ) ^ ε' :=
            div_le_div_of_nonneg_left hv_pos.le (Real.rpow_pos_of_pos (by linarith) _) hpow_le
        _ = (DirichletCharacter.LFunction ψ₁.χ 1).re := by
            dsimp only [v]
            rw [hqeq, mul_div_cancel_right₀ _ (Real.rpow_pos_of_pos hN1_pos ε').ne']
        _ = (DirichletCharacter.LFunction χ 1).re := by rw [hLeq 1]
  · refine ⟨ε' / 100000, by positivity, fun q _ χ hprim hsq hχne => ?_⟩
    have hreal : IsRealChar χ := isRealChar_of_sq_eq_one hsq
    have hne : PChar.of χ ≠ ψ₁ := by
      intro heq
      have hof : PChar.of χ = PChar.of ψ₁.χ := by rwa [PChar.of_self ψ₁]
      set ψ : PChar := ⟨q, χ, hprim⟩
      have hψeq : ψ = ψ₁ := by rw [← PChar.of_self ψ]; exact heq
      subst hψeq
      exact hψ ⟨hreal, hχne⟩
    have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast NeZero.pos q
    have hpow_le : (q : ℝ) ^ ε' ≤ (q : ℝ) ^ ε := Real.rpow_le_rpow_of_exponent_le hq1 hε'le
    calc (ε' / 100000) / (q : ℝ) ^ ε
        ≤ (ε' / 100000) / (q : ℝ) ^ ε' :=
          div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos (by linarith) _) hpow_le
      _ ≤ (DirichletCharacter.LFunction χ 1).re := htat q χ hprim hreal hχne hne

end RHDirect.Stage9LandauSiegel
end

/-!
The character is the Jacobi symbol on residues. Its conductor is the full squarefree
modulus because at every prime divisor there is a quadratic nonresidue that is
one at all the other primes. The conductor criterion and the nonresidue lemma
are adapted from @nil-commits, Arithmetica4, GaussClassNumberUnconditional.lean,
commit 023f6441c22a9ca0db1670e351e8ac44f00555ea, under Apache-2.0.
-/
noncomputable section
namespace OMA.Jacobi338
open Finset

private theorem jacVal {s : ℕ} [NeZero s] {z : ZMod s} {a : ℤ}
    (h : (a : ZMod s) = z) : jacobiSym (z.val : ℤ) s = jacobiSym a s := by
  apply jacobiSym.mod_left'
  change (z.val : ℤ) ≡ a [ZMOD (s : ℤ)]
  rw [← ZMod.intCast_eq_intCast_iff]
  push_cast
  simpa using h.symm

private def character (s : ℕ) [NeZero s] : DirichletCharacter ℂ s where
  toFun z := (jacobiSym (z.val : ℤ) s : ℂ)
  map_one' := by
    rw [jacVal (a := 1) (by simp), jacobiSym.one_left]
    norm_num
  map_mul' z w := by
    have h : ((((z.val : ℤ) * w.val : ℤ)) : ZMod s) = z*w := by simp
    rw [jacVal h, jacobiSym.mul_left, Int.cast_mul]
  map_nonunit' z hz := by
    have h : ¬Nat.Coprime z.val s := by
      intro hc
      exact hz (by simpa using (ZMod.isUnit_iff_coprime z.val s).mpr hc)
    have hj : jacobiSym (z.val : ℤ) s = 0 := jacobiSym.eq_zero_iff_not_coprime.mpr (by
      rw [Int.gcd_natCast_natCast]; exact h)
    change (jacobiSym (z.val : ℤ) s : ℂ) = 0
    rw [hj]
    norm_num

private theorem character_nat {s : ℕ} [NeZero s] (n : ℕ) :
    character s (n : ZMod s) = (jacobiSym (n : ℤ) s : ℂ) := by
  change (jacobiSym ((n : ZMod s).val : ℤ) s : ℂ) = _
  rw [jacVal (a := (n : ℤ)) (by simp)]

private theorem character_sq {s : ℕ} [NeZero s] : character s ^ 2 = 1 := by
  ext u
  rw [MulChar.pow_apply_coe, MulChar.one_apply u.isUnit]
  have cop : Nat.Coprime (u : ZMod s).val s := (ZMod.isUnit_iff_coprime _ _).mp (by simpa using u.isUnit)
  have hn := jacobiSym.ne_zero (a := ((u : ZMod s).val : ℤ)) (b := s) (by rw [Int.gcd_natCast_natCast]; exact cop.gcd_eq_one)
  change ((jacobiSym ((u : ZMod s).val : ℤ) s : ℂ)) ^ 2 = 1
  rcases jacobiSym.trichotomy ((u : ZMod s).val : ℤ) s with h | h | h
  · contradiction
  · rw [h]; norm_num
  · rw [h]; norm_num

private theorem character_ne {s : ℕ} [NeZero s] (hs : s%4=3) : character s ≠ 1 := by
  intro he
  have h := congrArg (fun χ : DirichletCharacter ℂ s => χ (-1)) he
  rw [MulChar.one_apply isUnit_one.neg] at h
  change (jacobiSym ((-1 : ZMod s).val : ℤ) s : ℂ) = 1 at h
  rw [jacVal (a:=(-1 : ℤ)) (by simp), jacobiSym.at_neg_one (Nat.odd_iff.mpr (by omega)),
    show (s : ZMod 4) = 3 from (ZMod.natCast_eq_natCast_iff s 3 4).mpr hs] at h
  have hc : ZMod.χ₄ (3 : ZMod 4) = -1 := by decide
  rw [hc] at h
  norm_num at h


private lemma exists_nonsquare_ne_zero_zmod' {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    ∃ r : ZMod p, r ≠ 0 ∧ ¬ IsSquare r := by
  have hp : p.Prime := Fact.out
  let sqMap : (ZMod p)ˣ → (ZMod p)ˣ := fun u => u ^ 2
  have hnot_inj : ¬ Function.Injective sqMap := by
    intro hinj
    have h1 : (1 : (ZMod p)ˣ) = -1 := hinj (by simp [sqMap])
    have hv : (1 : ZMod p) = -1 := congrArg Units.val h1
    have h20 : ((2 : ℕ) : ZMod p) = 0 := by push_cast; linear_combination hv
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h20
    exact hp2 (Nat.le_antisymm (Nat.le_of_dvd (by norm_num) hdvd) hp.two_le)
  have hnot_surj : ¬ Function.Surjective sqMap :=
    mt (Finite.injective_iff_surjective (f := sqMap)).mpr hnot_inj
  unfold Function.Surjective at hnot_surj
  push Not at hnot_surj
  obtain ⟨u, hu⟩ := hnot_surj
  refine ⟨(u : ZMod p), u.ne_zero, ?_⟩
  rintro ⟨x, hx⟩
  have hx_ne : x ≠ 0 := fun h0 => u.ne_zero (by rw [hx, h0, mul_zero])
  exact hu (isUnit_iff_ne_zero.mpr hx_ne).unit (Units.ext (by simp [sqMap, sq, hx]))
private theorem isPrimitive_of_forall_prime_witness {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q}
    (hw : ∀ p : ℕ, p.Prime → p ∣ q →
      ∃ u : (ZMod q)ˣ, (ZMod.cast (u : ZMod q) : ZMod (q / p)) = 1 ∧ χ (u : ZMod q) ≠ 1) :
    χ.IsPrimitive := by
  show χ.conductor = q
  apply Nat.dvd_antisymm χ.conductor_dvd_level
  by_contra hnot
  have hk_dvd : χ.conductor ∣ q := χ.conductor_dvd_level
  have hq_pos : 0 < q := NeZero.pos q
  have hk_pos : 0 < χ.conductor := Nat.pos_of_ne_zero χ.conductor_ne_zero
  have hk_lt : χ.conductor < q := lt_of_le_of_ne (Nat.le_of_dvd hq_pos hk_dvd)
    (by rintro h; exact hnot (by rw [h]))
  have hquot_gt1 : 1 < q / χ.conductor := by
    have hmul : χ.conductor * (q / χ.conductor) = q := Nat.mul_div_cancel' hk_dvd
    nlinarith
  set p := (q / χ.conductor).minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hp_dvd_quot : p ∣ q / χ.conductor := Nat.minFac_dvd _
  have hp_dvd_q : p ∣ q := dvd_trans hp_dvd_quot (Nat.div_dvd_of_dvd hk_dvd)
  have hk_dvd_qp : χ.conductor ∣ q / p := by
    obtain ⟨t, ht⟩ := hp_dvd_quot
    refine ⟨t, ?_⟩
    have hmul1 : χ.conductor * (p * t) = q := by rw [← ht, Nat.mul_div_cancel' hk_dvd]
    have hmul2 : p * (q / p) = q := Nat.mul_div_cancel' hp_dvd_q
    have : p * (χ.conductor * t) = p * (q / p) := by linarith
    exact (Nat.eq_of_mul_eq_mul_left hp.pos this).symm
  obtain ⟨u, hu_mod, hu_ne⟩ := hw p hp hp_dvd_q
  obtain ⟨hdvd_c, ψ, hψ⟩ := χ.factorsThrough_conductor
  have hcast_k : ZMod.cast (u : ZMod q) = (1 : ZMod χ.conductor) := by
    have hqp_dvd : q / p ∣ q := Nat.div_dvd_of_dvd hp_dvd_q
    have hcomp : (ZMod.castHom hk_dvd_qp (ZMod χ.conductor)).comp
        (ZMod.castHom hqp_dvd (ZMod (q / p))) = ZMod.castHom hk_dvd (ZMod χ.conductor) :=
      ZMod.castHom_comp hk_dvd_qp hqp_dvd
    have h1 := congrArg (fun f => f (u : ZMod q)) hcomp
    simp only [RingHom.comp_apply, ZMod.castHom_apply] at h1
    rw [← h1, hu_mod]
    change ZMod.castHom hk_dvd_qp (ZMod χ.conductor) 1 = 1
    exact map_one _
  have hval : χ (u : ZMod q) = 1 := by
    rw [hψ, DirichletCharacter.changeLevel_def, MulChar.ofUnitHom_coe]
    change ψ ((ZMod.unitsMap hdvd_c u : (ZMod χ.conductor)ˣ) : ZMod χ.conductor) = 1
    have hv : ((ZMod.unitsMap hdvd_c u : (ZMod χ.conductor)ˣ) : ZMod χ.conductor) = 1 := hcast_k
    rw [hv, map_one]
  exact hu_ne hval

private theorem character_primitive {s : ℕ} [NeZero s] (sqfree : Squarefree s) (odd : Odd s) :
    (character s).IsPrimitive := by
  apply isPrimitive_of_forall_prime_witness
  intro p hp hps
  let M := s / p
  have hprod : p * M = s := Nat.mul_div_cancel' hps
  have cop : Nat.Coprime p M := hp.coprime_iff_not_dvd.mpr fun h =>
    hp.not_isUnit (sqfree p (hprod ▸ Nat.mul_dvd_mul_left p h))
  have : NeZero M := ⟨by intro hm; rw [hm,mul_zero] at hprod; exact NeZero.ne s hprod.symm⟩
  have hodd : p ≠ 2 := by
    rintro rfl
    have h := Nat.odd_iff.mp odd
    omega
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨r, hr, hnonsq⟩ := exists_nonsquare_ne_zero_zmod' hodd
  obtain ⟨n, np, nM⟩ := Nat.chineseRemainder cop r.val 1
  have ep : (n : ZMod p) = r := by
    simpa using (ZMod.natCast_eq_natCast_iff n r.val p).mpr np
  have eM : (n : ZMod M) = 1 := by
    simpa using (ZMod.natCast_eq_natCast_iff n 1 M).mpr nM
  have un : IsUnit (n : ZMod s) := by
    rw [ZMod.isUnit_iff_coprime, ← hprod]
    exact ((ZMod.isUnit_iff_coprime _ _).mp (ep ▸ isUnit_iff_ne_zero.mpr hr)).mul_right
      ((ZMod.isUnit_iff_coprime _ _).mp (eM ▸ isUnit_one))
  refine ⟨un.unit, ?_, ?_⟩
  · rw [IsUnit.unit_spec, ZMod.cast_natCast (Nat.div_dvd_of_dvd hps)]; exact eM
  · rw [IsUnit.unit_spec, character_nat]
    have h1 : jacobiSym (n : ℤ) M = 1 := by
      rw [jacobiSym.mod_left' (show (n:ℤ) ≡ 1 [ZMOD (M : ℤ)] by
        rw [← ZMod.intCast_eq_intCast_iff]; push_cast; exact eM), jacobiSym.one_left]
    have hn : jacobiSym (n : ℤ) p = -1 := by
      rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_neg_one_iff]
      simpa only [Int.cast_natCast, ep] using hnonsq
    rw [← hprod, jacobiSym.mul_right, h1, hn]
    norm_num

end OMA.Jacobi338
end

open Filter Finset Real
open scoped Topology

theorem OMA.solution : OMA.R_Erdos338_erdos_338_variants_triangular_R1_H1_R1_H1_R1_H1_R1_H1_R1.H1 := by
  obtain ⟨C, hC, lower⟩ := RHDirect.Stage9LandauSiegel.siegel_theorem_L1_lower_bound (1/8) (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro s hs sqfree mod8
  letI : NeZero s := ⟨hs.ne'⟩
  let χ := OMA.Jacobi338.character s
  have hn : χ ≠ 1 := OMA.Jacobi338.character_ne (by omega)
  have hp : χ.IsPrimitive := OMA.Jacobi338.character_primitive sqfree (Nat.odd_iff.mpr (by omega))
  have b := lower s χ hp OMA.Jacobi338.character_sq hn
  refine ⟨(DirichletCharacter.LFunction χ 1).re, ?_, ?_⟩
  · have lim := Complex.continuous_re.continuousAt.tendsto.comp
        (RHDirect.Stage6ClassNumberFormula.tendsto_partialSum_LFunction_one hn)
    refine lim.congr fun N => ?_
    simp only [Function.comp_apply, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [show χ (n : ZMod s) = (jacobiSym (n : ℤ) s : ℂ) from OMA.Jacobi338.character_nat n]
    rw [← Complex.ofReal_intCast, ← Complex.ofReal_natCast, ← Complex.ofReal_div, Complex.ofReal_re]
  · simpa only [Real.rpow_neg (Nat.cast_nonneg s), ← div_eq_mul_inv] using b
