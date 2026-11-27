import FormalConjectures.ErdosProblems.«116»
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Data.Nat.Log
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Complex.Liouville
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
A reduction of the lemniscate area lower bound to the logarithmic harmonic sign-area estimate.
-/

noncomputable section

open Set Metric MeasureTheory Polynomial
open scoped BigOperators ENNReal ComplexConjugate

namespace LemniscateLog

def reflected {n : ℕ} (a : Fin n → ℂ) : ℂ[X] := ∏ i, (1 - C (conj (a i)) * X)

def logarithm {n : ℕ} (a : Fin n → ℂ) (w : ℂ) : ℂ :=
  - ∑ i, Complex.log (1 - conj (a i)*w)

def levelPolynomial {n : ℕ} (a : Fin n → ℂ) (r : ℝ) : ℂ[X] :=
  reflected a * (∏ i, (X - C (a i * (r:ℂ)^2))) - X^n

theorem reflected_eval {n : ℕ} (a : Fin n → ℂ) (w : ℂ) :
    (reflected a).eval w = ∏ i, (1 - conj (a i)*w) := by
  rw [reflected, Polynomial.eval_prod]
  simp

theorem reflected_natDegree {n : ℕ} (a : Fin n → ℂ) :
    (reflected a).natDegree ≤ n := by
  unfold reflected
  refine (natDegree_prod_le _ _).trans ?_
  calc
    _ ≤ ∑ i : Fin n, 1 := by
      apply Finset.sum_le_sum
      intro i _
      exact (natDegree_sub_le _ _).trans (by simpa using natDegree_C_mul_X_pow_le (conj (a i)) 1)
    _ = n := by simp

theorem levelPolynomial_natDegree {n : ℕ} (a : Fin n → ℂ) (r : ℝ) :
    (levelPolynomial a r).natDegree ≤ 2*n := by
  have h : (∏ i, (X - C (a i * (r:ℂ)^2))).natDegree ≤ n := by
    refine (natDegree_prod_le _ _).trans ?_
    calc
      _ ≤ ∑ i : Fin n, 1 := by
        exact Finset.sum_le_sum (fun i _ => (natDegree_sub_le _ _).trans (by rw [natDegree_X,natDegree_C]; decide))
      _ = n := by simp
  unfold levelPolynomial
  apply (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · have hp := reflected_natDegree a
    exact (natDegree_mul_le ..).trans (by omega)
  · simpa using (show n ≤ 2*n by omega)

theorem reflected_has_root {n : ℕ} {a : Fin n → ℂ} (h : ∃ i, a i ≠ 0) :
    ∃ z ≠ (0:ℂ), (reflected a).eval z = 0 := by
  obtain ⟨i,hi⟩ := h
  have hc : conj (a i) ≠ 0 := (_root_.map_ne_zero conj).mpr hi
  refine ⟨(conj (a i))⁻¹,inv_ne_zero hc,?_⟩
  rw [reflected_eval]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hc])

theorem levelPolynomial_ne_zero {n : ℕ} {a : Fin n → ℂ} (h : ∃ i, a i ≠ 0) (r : ℝ) :
    levelPolynomial a r ≠ 0 := by
  obtain ⟨z,hz,hpz⟩ := reflected_has_root h
  intro he
  have H := congrArg (eval z) he
  simp [levelPolynomial,hpz,pow_ne_zero _ hz] at H

private theorem mul_conj_eq_of_norm {w : ℂ} {r : ℝ} (h : ‖w‖ = r) :
    w * conj w = (r:ℂ)^2 := by
  rw [Complex.mul_conj, ← Complex.sq_norm, h]
  norm_cast

theorem levelPolynomial_eval {n : ℕ} (a : Fin n → ℂ) {r : ℝ} {w : ℂ}
    (hw : ‖w‖ = r) :
    (levelPolynomial a r).eval w =
      w^n * ((‖(reflected a).eval w‖^2 - 1 : ℝ) : ℂ) := by
  have hfac (i : Fin n) : w - a i * (r:ℂ)^2 = w * conj (1 - conj (a i)*w) := by
    rw [← mul_conj_eq_of_norm hw, map_sub, map_one, map_mul, Complex.conj_conj]
    ring
  have hprod : (∏ i, (w - a i * (r:ℂ)^2)) =
      w^n * conj ((reflected a).eval w) := by
    simp only [hfac, Finset.prod_mul_distrib, ← map_prod, reflected_eval, Finset.prod_const,
      Finset.card_univ,Fintype.card_fin]
  rw [levelPolynomial, eval_sub, eval_mul, eval_prod, eval_pow, eval_X]
  simp only [eval_sub, eval_X,eval_C,hprod]
  rw [← mul_assoc, mul_right_comm ((reflected a).eval w), Complex.mul_conj, ← Complex.sq_norm]
  push_cast
  ring

theorem finite_levelOnCircle {n : ℕ} (a : Fin n → ℂ) (h : ∃ i, a i ≠ 0) (r : ℝ) :
    ({w : ℂ | ‖w‖ = r ∧ ‖(reflected a).eval w‖ = 1}).Finite ∧
    ({w : ℂ | ‖w‖ = r ∧ ‖(reflected a).eval w‖ = 1}).ncard ≤ 2*n := by
  classical
  let P := levelPolynomial a r
  have hp : P ≠ 0 := levelPolynomial_ne_zero h r
  have hsub : {w : ℂ | ‖w‖ = r ∧ ‖(reflected a).eval w‖ = 1} ⊆ (P.roots.toFinset : Set ℂ) := by
    intro w hw
    have hw' : P.eval w = 0 := by
      rw [levelPolynomial_eval a hw.1,hw.2]
      simp
    simpa only [Finset.mem_coe,Multiset.mem_toFinset,mem_roots hp,IsRoot] using hw'
  exact ⟨P.roots.toFinset.finite_toSet.subset hsub,
    (Set.ncard_le_ncard hsub P.roots.toFinset.finite_toSet).trans (by
      rw [Set.ncard_coe_finset]
      exact (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' _).trans (levelPolynomial_natDegree a r)))⟩

private theorem factor_norm_le {w z : ℂ} (hw : ‖w‖ ≤ 1) (hz : ‖z‖ ≤ 1) :
    ‖w-z‖ ≤ ‖1-conj z*w‖ := by
  have he : ‖1-conj z*w‖^2 - ‖w-z‖^2 = (1-‖z‖^2)*(1-‖w‖^2) := by
    simp only [Complex.sq_norm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,
      Complex.conj_re,Complex.conj_im,Complex.sub_re,Complex.sub_im,Complex.one_re,Complex.one_im]
    ring
  have hzn : 0 ≤ 1-‖z‖^2 := by nlinarith [norm_nonneg z]
  have hwn : 0 ≤ 1-‖w‖^2 := by nlinarith [norm_nonneg w]
  have := mul_nonneg hzn hwn
  nlinarith [norm_nonneg (w-z),norm_nonneg (1-conj z*w)]

theorem norm_prod_le_reflected {n : ℕ} {a : Fin n → ℂ} (ha : ∀ i, ‖a i‖ ≤ 1)
    {w : ℂ} (hw : ‖w‖ ≤ 1) : ‖∏ i, (w-a i)‖ ≤ ‖(reflected a).eval w‖ := by
  rw [reflected_eval, norm_prod, norm_prod]
  exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => factor_norm_le hw (ha i))

private theorem factor_mem_slitPlane {w z : ℂ} (hw : ‖w‖ < 1) (hz : ‖z‖ ≤ 1) :
    1-conj z*w ∈ Complex.slitPlane := by
  suffices h : 0 < (1-conj z*w).re by exact Or.inl h
  have hnorm : ‖conj z*w‖ < 1 := by
    rw [norm_mul,Complex.norm_conj]
    exact (mul_le_of_le_one_left (norm_nonneg _) hz).trans_lt hw
  simpa only [Complex.sub_re,Complex.one_re,sub_pos] using
    (Complex.re_le_norm (conj z*w)).trans_lt hnorm

private theorem factor_ne_zero {w z : ℂ} (hw : ‖w‖ < 1) (hz : ‖z‖ ≤ 1) :
    1-conj z*w ≠ 0 := Complex.slitPlane_ne_zero (factor_mem_slitPlane hw hz)

theorem logarithm_analyticOn {n : ℕ} {a : Fin n → ℂ} (ha : ∀ i, ‖a i‖ ≤ 1) :
    AnalyticOnNhd ℂ (logarithm a) (ball 0 1) := by
  intro w hw
  apply AnalyticAt.neg
  apply Finset.analyticAt_fun_sum
  intro i _
  have h : AnalyticAt ℂ (fun w : ℂ => 1-conj (a i)*w) w := by fun_prop
  exact h.clog (factor_mem_slitPlane (by simpa using hw) (ha i))

theorem logarithm_zero {n : ℕ} (a : Fin n → ℂ) : logarithm a 0 = 0 := by
  simp [logarithm]

theorem exp_neg_logarithm {n : ℕ} {a : Fin n → ℂ} (ha : ∀ i, ‖a i‖ ≤ 1)
    {w : ℂ} (hw : ‖w‖ < 1) :
    Complex.exp (-logarithm a w) = (reflected a).eval w := by
  simp only [logarithm,neg_neg,Complex.exp_sum,reflected_eval]
  exact Finset.prod_congr rfl (fun i _ => Complex.exp_log (factor_ne_zero hw (ha i)))

theorem re_pos_iff {n : ℕ} {a : Fin n → ℂ} (ha : ∀ i, ‖a i‖ ≤ 1)
    {w : ℂ} (hw : ‖w‖ < 1) :
    0 < (logarithm a w).re ↔ ‖(reflected a).eval w‖ < 1 := by
  rw [← exp_neg_logarithm ha hw,Complex.norm_exp,Complex.neg_re,Real.exp_lt_one_iff,neg_lt_zero]

theorem re_zero_iff {n : ℕ} {a : Fin n → ℂ} (ha : ∀ i, ‖a i‖ ≤ 1)
    {w : ℂ} (hw : ‖w‖ < 1) :
    (logarithm a w).re = 0 ↔ ‖(reflected a).eval w‖ = 1 := by
  rw [← exp_neg_logarithm ha hw,Complex.norm_exp,Complex.neg_re,Real.exp_eq_one_iff,neg_eq_zero]

end LemniscateLog

/-
Logarithmic derivative factorization on a zero-free-boundary disc.
-/

noncomputable section

open Set Metric Filter Complex Function
open scoped Topology BigOperators

namespace LemniscateNPS

private theorem larger_radius_no_new_zeros {f : ℂ → ℂ} {R S : ℝ} (hRS : R < S)
    (hfin : ({z : ℂ | ‖z‖ < S ∧ f z = 0}).Finite)
    (hR : ∀ z ∈ sphere 0 R, f z ≠ 0) :
    ∃ T, R < T ∧ T < S ∧ ∀ z : ℂ, ‖z‖ < T → f z = 0 → ‖z‖ < R := by
  classical
  let V := insert S (((hfin.image norm).toFinset).filter (fun x => R<x))
  have hV : V.Nonempty := Finset.insert_nonempty _ _
  have hVR (x : ℝ) (hx : x∈V) : R < x := by
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hRS
    · exact (Finset.mem_filter.mp hx).2
  let u := V.min' hV
  have huR := hVR u (Finset.min'_mem V hV)
  have huS : u ≤ S := Finset.min'_le _ _ (Finset.mem_insert_self _ _)
  let T := (R+u)/2
  refine ⟨T,by dsimp [T]; linarith,by dsimp [T]; linarith,fun z hz hf => ?_⟩
  by_contra! H
  have hr : R < ‖z‖ := by
    apply lt_of_le_of_ne H
    intro he
    exact hR z (by simp [he]) hf
  have hmem : ‖z‖∈V := Finset.mem_insert_of_mem (Finset.mem_filter.mpr
    ⟨((hfin.image norm).mem_toFinset).mpr ⟨z,⟨hz.trans (by dsimp [T]; linarith),hf⟩,rfl⟩,hr⟩)
  have hb : u ≤ ‖z‖ := Finset.min'_le _ _ hmem
  dsimp [T] at hz
  linarith

/-- The logarithmic derivative is a holomorphic derivative plus one simple-pole term per zero. -/
theorem exists_logDeriv_factor {f : ℂ → ℂ} {R S : ℝ} (hR : 0 < R) (hRS : R < S)
    (hf : AnalyticOnNhd ℂ f (ball 0 S)) (hf0 : f 0 = 0)
    (hfin : ({z : ℂ | ‖z‖ < S ∧ f z = 0}).Finite)
    (hR0 : ∀ z ∈ sphere 0 R, f z ≠ 0) :
    ∃ (m : ℕ) (ζ : Fin m → ℂ) (g : ℂ → ℂ), (∀ i, ‖ζ i‖ < R) ∧ (∃ i, ζ i = 0) ∧
      AnalyticOnNhd ℂ g (closedBall 0 R) ∧ ∀ z ∈ closedBall 0 R, f z ≠ 0 →
        deriv f z / f z = deriv g z + ∑ i, (z-ζ i)⁻¹ := by
  classical
  obtain ⟨T,hRT,hTS,hTZ⟩ := larger_radius_no_new_zeros hRS hfin hR0
  let U := ball (0:ℂ) T
  let d := MeromorphicOn.divisor f U
  have hT : 0 < T := hR.trans hRT
  have hU : U ⊆ ball 0 S := ball_subset_ball hTS.le
  have hcb : closedBall (0:ℂ) R ⊆ U := closedBall_subset_ball hRT
  have han : AnalyticOnNhd ℂ f U := hf.mono hU
  have hfm := han.meromorphicOn
  let x : ℂ := (R:ℂ)
  have hx : x∈sphere 0 R := by simp [x,abs_of_pos hR]
  have hxU : x∈U := hcb (sphere_subset_closedBall hx)
  have hnx : meromorphicOrderAt f x ≠ ⊤ := by
    intro h
    have hne : f =ᶠ[𝓝[≠] x] (fun _ => (0:ℂ)) := meromorphicOrderAt_eq_top_iff.mp h
    exact hR0 x hx (tendsto_nhds_unique_of_eventuallyEq
      (han x hxU).continuousAt.continuousWithinAt tendsto_const_nhds hne)
  have hnt (z : U) : meromorphicOrderAt f z ≠ ⊤ :=
    hfm.meromorphicOrderAt_ne_top_of_isPreconnected (convex_ball _ _).isPreconnected hxU z.2 hnx
  have hds : d.support ⊆ {z : ℂ | ‖z‖ < S ∧ f z = 0} := by
    intro z hz
    have hzU := d.supportWithinDomain hz
    refine ⟨by simpa using hU hzU,?_⟩
    by_contra hne
    have ha0 : analyticOrderAt f z = 0 := (han z hzU).analyticOrderAt_eq_zero.mpr hne
    have hd0 : d z = 0 := by
      change MeromorphicOn.divisor f U z = 0
      rw [MeromorphicOn.AnalyticOnNhd.divisor_apply han hzU,ha0]
      simp
    exact hz hd0
  have hdf : d.support.Finite := hfin.subset hds
  have hdnn : 0 ≤ d := MeromorphicOn.AnalyticOnNhd.divisor_nonneg han
  have hdn (z : ℂ) : 0 ≤ d z := hdnn z
  have hroot (z : ℂ) (hz : z ∈ d.support) : ‖z‖ < R :=
    hTZ z (by simpa [U] using d.supportWithinDomain hz) (hds hz).2
  obtain ⟨h,hha,hh0,hEq⟩ := hfm.extract_zeros_poles hnt hdf
  let : Fintype d.support := hdf.fintype
  let J := Σ z : d.support, Fin (d z.val).toNat
  let N := Fintype.card J
  let e := Fintype.equivFin J
  let ζ (i : Fin N) : ℂ := (e.symm i).1.val
  let P (z : ℂ) := ∏ i : Fin N, (z-ζ i)
  have hP (z : ℂ) : (∏ᶠ u : ℂ, (z-u)^d u) = P z := by
    have hsub : (fun u : ℂ => (z-u)^d u).mulSupport ⊆ d.support := by
      intro u hu
      by_contra hn
      apply hu
      change (z-u)^d u = 1
      rw [Function.notMem_support.mp hn,zpow_zero]
    rw [finprod_eq_prod_of_mulSupport_subset _ (by simpa only [Set.Finite.coe_toFinset] using hsub :
      (fun u : ℂ => (z-u)^d u).mulSupport ⊆ (hdf.toFinset : Set ℂ))]
    have he : (∏ u ∈ hdf.toFinset, (z-u)^d u) = ∏ u : d.support, (z-u.val)^d u.val := by
      exact Finset.prod_subtype _ (fun u => hdf.mem_toFinset) (fun u => (z-u)^d u)
    rw [he]
    have hp : P z = ∏ j : J, (z-j.1.val) :=
      Fintype.prod_equiv e.symm _ _ (fun _ => rfl)
    rw [hp,Fintype.prod_sigma]
    apply Finset.prod_congr rfl
    intro u _
    change (z-u.val)^d u.val = ∏ _ : Fin (d u.val).toNat, (z-u.val)
    rw [Finset.prod_const,Finset.card_univ,Fintype.card_fin,← zpow_natCast,
      Int.toNat_of_nonneg (hdn _)]
  have hPS : HasFiniteMulSupport (fun u : ℂ => (fun z : ℂ => z-u)^d u) := by
    unfold HasFiniteMulSupport
    rw [Function.FactorizedRational.mulSupport]
    exact hdf
  have hEq' : f =ᶠ[Filter.codiscreteWithin U] (fun z => P z*h z) := by
    filter_upwards [hEq] with z hz
    change f z = (∏ᶠ u : ℂ, (fun z : ℂ => z-u)^d u) z * h z at hz
    rw [finprod_apply hPS] at hz
    change f z = (∏ᶠ u : ℂ, (z-u)^d u) * h z at hz
    rw [hP] at hz
    exact hz
  have hPa : AnalyticOnNhd ℂ P univ := by
    intro z _
    unfold P
    apply Finset.analyticAt_fun_prod
    intro i _
    fun_prop
  have hp : AnalyticOnNhd ℂ (fun z => P z*h z) U :=
    fun z hz => (hPa z trivial).mul (hha z hz)
  have hEqOn : EqOn f (fun z => P z*h z) U := by
    intro z hz
    have hne : {w | f w=P w*h w} ∪ Uᶜ ∈ 𝓝[≠] z :=
      mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp hEq' z hz
    have hu : U ∈ 𝓝[≠] z := mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds hz)
    have hen : f =ᶠ[𝓝[≠] z] (fun w => P w*h w) := by
      filter_upwards [hne,hu] with w hw hwU
      exact hw.elim id (fun h => (h hwU).elim)
    exact tendsto_nhds_unique_of_eventuallyEq (han z hz).continuousAt.continuousWithinAt
      (hp z hz).continuousAt.continuousWithinAt hen
  have hhD : DifferentiableOn ℂ (fun z => deriv h z / h z) U :=
    hha.deriv.differentiableOn.div hha.differentiableOn (fun z hz => hh0 ⟨z,hz⟩)
  obtain ⟨g,hg⟩ := hhD.isExactOn_ball
  have hga : AnalyticOnNhd ℂ g U := (show DifferentiableOn ℂ g U from
    fun z hz => (hg z hz).differentiableAt.differentiableWithinAt).analyticOnNhd isOpen_ball
  have hfzero : ∃ i, ζ i = 0 := by
    have h0U : 0∈U := mem_ball_self hT
    have H := hEqOn h0U
    rw [hf0,zero_eq_mul] at H
    have hP0 : P 0 = 0 := H.resolve_right (hh0 ⟨0,h0U⟩)
    obtain ⟨i,_,hi⟩ := Finset.prod_eq_zero_iff.mp hP0
    exact ⟨i,by simpa using hi⟩
  refine ⟨N,ζ,g,fun i => hroot _ (e.symm i).1.2,hfzero,hga.mono hcb,?_⟩
  intro z hz hzf
  have hzU := hcb hz
  have hh0' := hh0 ⟨z,hzU⟩
  have hP0 : P z ≠ 0 := by
    intro h0
    exact hzf ((hEqOn hzU).trans (by simp [h0]))
  have hz0 (i : Fin N) : z-ζ i ≠ 0 := fun hi => hP0 (Finset.prod_eq_zero (Finset.mem_univ i) hi)
  have hN : f =ᶠ[𝓝 z] (fun x => P x*h x) := by
    filter_upwards [isOpen_ball.mem_nhds hzU] with w hw using hEqOn hw
  change logDeriv f z = _
  have hd' : deriv g z = logDeriv h z := (hg z hzU).deriv
  rw [(logDeriv_congr_nhds hN).eq_of_nhds,logDeriv_mul _ hP0 hh0' (hPa z trivial).differentiableAt (hha z hzU).differentiableAt,
    hd']
  rw [show logDeriv P z = ∑ i, (z-ζ i)⁻¹ from ?_,add_comm]
  unfold P
  rw [logDeriv_prod (fun i _ => hz0 i) (fun i _ => by fun_prop)]
  apply Finset.sum_congr rfl
  intro i _
  simp [logDeriv_apply,one_div]

end LemniscateNPS

/-
Argument increments on circles for the Nazarov–Polterovich–Sodin estimate.
-/

noncomputable section

open Set Metric MeasureTheory Filter Complex
open scoped Real ENNReal Topology ComplexConjugate

namespace LemniscateNPS

def velocity (f : ℂ → ℂ) (r θ : ℝ) : ℂ :=
  deriv f (circleMap 0 r θ) / f (circleMap 0 r θ) * (circleMap 0 r θ * I)

def increment (f : ℂ → ℂ) (r a b : ℝ) : ℝ := (∫ θ in a..b, velocity f r θ).im

def BoundedArgument (f : ℂ → ℂ) (r M : ℝ) : Prop :=
  ∀ a b : ℝ, a ≤ b → b-a ≤ 2*π → increment f r a b < M

theorem norm_circle {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) : ‖circleMap 0 r θ‖ = r := by
  rw [norm_circleMap_zero,abs_of_nonneg hr]

private theorem circle_mem_sphere {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) :
    circleMap 0 r θ ∈ sphere 0 r := by
  rw [mem_sphere,dist_zero_right,norm_circle hr]

theorem continuous_velocity {f : ℂ → ℂ} {S : Set ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hf : AnalyticOnNhd ℂ f S) (hS : sphere 0 r ⊆ S)
    (h0 : ∀ z ∈ sphere 0 r, f z ≠ 0) :
    Continuous (velocity f r) := by
  have ht : MapsTo (circleMap 0 r) univ S := fun t _ => hS (circle_mem_sphere hr t)
  have ha : Continuous (fun t => f (circleMap 0 r t)) :=
    continuousOn_univ.mp (hf.continuousOn.comp (continuous_circleMap 0 r).continuousOn ht)
  have hd : Continuous (fun t => deriv f (circleMap 0 r t)) :=
    continuousOn_univ.mp (hf.deriv.continuousOn.comp (continuous_circleMap 0 r).continuousOn ht)
  exact (hd.div ha (fun t => h0 _ (circle_mem_sphere hr t))).mul
    ((continuous_circleMap 0 r).mul continuous_const)

theorem lift_exists {f : ℂ → ℂ} {S : Set ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hf : AnalyticOnNhd ℂ f S) (hS : sphere 0 r ⊆ S)
    (h0 : ∀ z ∈ sphere 0 r, f z ≠ 0) :
    ∃ L : ℝ → ℂ, (∀ θ, HasDerivAt L (velocity f r θ) θ) ∧
      (∀ θ, exp (L θ) = f (circleMap 0 r θ)) ∧
      ∀ a b, (L b).im - (L a).im = increment f r a b := by
  let L (θ : ℝ) := log (f (circleMap 0 r 0)) + ∫ t in (0:ℝ)..θ, velocity f r t
  have hcv := continuous_velocity hr hf hS h0
  have hL (θ : ℝ) : HasDerivAt L (velocity f r θ) θ := by
    exact (intervalIntegral.integral_hasDerivAt_right (hcv.intervalIntegrable _ _)
      hcv.stronglyMeasurable.aestronglyMeasurable.stronglyMeasurableAtFilter hcv.continuousAt).const_add _
  have he (θ : ℝ) : HasDerivAt (fun t => f (circleMap 0 r t) * exp (-L t)) 0 θ := by
    let z := circleMap 0 r θ
    have hz := h0 z (circle_mem_sphere hr θ)
    have hd := (hf z (hS (circle_mem_sphere hr θ))).differentiableAt.hasDerivAt.scomp θ
      (hasDerivAt_circleMap 0 r θ)
    have h := hd.mul ((hL θ).neg.cexp)
    refine h.congr_deriv ?_
    change (z*I)*deriv f z*exp (-L θ) + f z*(exp (-L θ)* -(deriv f z / f z*(z*I))) = 0
    field_simp
    ring
  have hE (θ : ℝ) : f (circleMap 0 r θ) * exp (-L θ) = 1 := by
    rw [is_const_of_deriv_eq_zero (fun t => (he t).differentiableAt) (fun t => (he t).deriv) θ 0]
    simp only [L,intervalIntegral.integral_same,add_zero,exp_neg,exp_log (h0 _ (circle_mem_sphere hr 0))]
    exact mul_inv_cancel₀ (h0 _ (circle_mem_sphere hr 0))
  refine ⟨L,hL,fun θ => ?_,fun a b => ?_⟩
  · have h := hE θ
    rw [exp_neg,← div_eq_mul_inv,div_eq_iff (exp_ne_zero _),one_mul] at h
    exact h.symm
  · have h : (∫ t in a..b, velocity f r t) = L b - L a :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t _ => hL t) (hcv.intervalIntegrable _ _)
    rw [increment,h,Complex.sub_im]

theorem re_pos_iff_cos_pos {z L : ℂ} (h : exp L = z) : 0 < z.re ↔ 0 < Real.cos L.im := by
  rw [← h,exp_re]
  exact mul_pos_iff_of_pos_left (Real.exp_pos _)

theorem re_zero_iff_cos_zero {z L : ℂ} (h : exp L = z) : z.re = 0 ↔ Real.cos L.im = 0 := by
  rw [← h,exp_re,mul_eq_zero]
  simp [Real.exp_ne_zero]

private theorem marker_cos_zero (k : ℤ) : Real.cos (π/2 + (k:ℝ)*π) = 0 := by
  rw [Real.cos_add,Real.cos_pi_div_two,Real.sin_int_mul_pi]
  ring

theorem increment_le_of_level_card {f : ℂ → ℂ} {S : Set ℂ} {r : ℝ} (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f S) (hS : sphere 0 r ⊆ S) (h0 : ∀ z ∈ sphere 0 r, f z ≠ 0)
    (N : ℕ) (hfin : ({z : ℂ | ‖z‖ = r ∧ (f z).re = 0}).Finite)
    (hcard : ({z : ℂ | ‖z‖ = r ∧ (f z).re = 0}).ncard ≤ N)
    {a b : ℝ} (hab : a ≤ b) (hlen : b-a ≤ 2*π) :
    increment f r a b ≤ (N+1:ℝ)*π := by
  classical
  obtain ⟨L,hL,hExp,hInc⟩ := lift_exists hr.le hf hS h0
  rw [← hInc]
  by_contra! H
  let m : ℤ := ⌊((L a).im-π/2)/π⌋+1
  let v (i : Fin (N+1)) := π/2+((m+(i.val:ℤ):ℤ):ℝ)*π
  have hm1 : (L a).im < π/2+(m:ℝ)*π := by
    have h := (div_lt_iff₀ Real.pi_pos).mp (Int.lt_floor_add_one (((L a).im-π/2)/π))
    push_cast [m]
    linarith
  have hm0 : π/2+(m:ℝ)*π ≤ (L a).im+π := by
    have h := (le_div_iff₀ Real.pi_pos).mp (Int.floor_le (((L a).im-π/2)/π))
    push_cast [m]
    nlinarith
  have Hv (i : Fin (N+1)) : (L a).im < v i ∧ v i < (L b).im := by
    have hi : (i.val:ℝ) ≤ N := by exact_mod_cast (Nat.lt_succ_iff.mp i.isLt)
    have hi0 : 0 ≤ (i.val:ℝ) := by positivity
    dsimp [v]
    push_cast
    constructor <;> nlinarith [mul_nonneg hi0 Real.pi_pos.le,
      mul_nonneg (sub_nonneg.mpr hi) Real.pi_pos.le]
  have hL' : Continuous (fun t => (L t).im) :=
    Complex.continuous_im.comp (continuous_iff_continuousAt.mpr (fun t => (hL t).continuousAt))
  have hpoint (i : Fin (N+1)) : ∃ t ∈ Ioo a b, (L t).im = v i := by
    obtain ⟨t,ht,he⟩ := intermediate_value_Icc hab hL'.continuousOn ⟨(Hv i).1.le,(Hv i).2.le⟩
    refine ⟨t,⟨lt_of_le_of_ne ht.1 ?_,lt_of_le_of_ne ht.2 ?_⟩,he⟩
    · intro h
      exact (ne_of_lt (Hv i).1) (h ▸ he)
    · intro h
      exact (ne_of_lt (Hv i).2) (h ▸ he).symm
  choose t ht htv using hpoint
  let W (i : Fin (N+1)) := circleMap 0 r (t i)
  have hinj : Function.Injective W := by
    intro i j hij
    have he : t i = t j := injOn_circleMap_of_abs_sub_le' hr.ne' hlen
      ⟨(ht i).1.le,(ht i).2⟩ ⟨(ht j).1.le,(ht j).2⟩ hij
    have hval : v i = v j := by rw [← htv i,← htv j,he]
    apply Fin.ext
    dsimp [v] at hval
    push_cast at hval
    exact_mod_cast (show (i.val:ℝ)=(j.val:ℝ) by
      exact mul_right_cancel₀ Real.pi_pos.ne' (by linarith))
  have hW (i) : W i ∈ {z : ℂ | ‖z‖ = r ∧ (f z).re = 0} := by
    refine ⟨norm_circle hr.le _,(re_zero_iff_cos_zero (hExp (t i))).mpr ?_⟩
    rw [htv]
    exact marker_cos_zero _
  have hN : N+1 ≤ ({z : ℂ | ‖z‖ = r ∧ (f z).re = 0}).ncard := by
    calc
      N+1 = (Finset.univ.image W).card := by rw [Finset.card_image_of_injective _ hinj]; simp
      _ = ((Finset.univ.image W : Finset ℂ) : Set ℂ).ncard := (Set.ncard_coe_finset _).symm
      _ ≤ _ := Set.ncard_le_ncard (by
        intro z hz
        obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hz
        exact hW i) hfin
  omega

def cosPart (x : ℝ) : ℝ := max (Real.cos x) 0

private theorem continuous_cosPart : Continuous cosPart := Real.continuous_cos.max continuous_const

private theorem cosPart_nonneg (x : ℝ) : 0 ≤ cosPart x := le_max_right _ _

private theorem periodic_cosPart : Function.Periodic cosPart (2*π) := by
  intro t
  simp only [cosPart,Real.cos_add_two_pi]

def sweep : ℝ := ∫ x in (0:ℝ)..2*π, cosPart x

theorem sweep_pos : 0 < sweep := by
  have hπ := Real.pi_pos
  have hs : ∀ x ∈ Icc (0:ℝ) (π/3), 1/2 ≤ cosPart x := by
    intro x hx
    have hx' : x ∈ Icc (0:ℝ) π := ⟨hx.1, hx.2.trans (by linarith)⟩
    have hπ' : π/3 ∈ Icc (0:ℝ) π := ⟨by linarith, by linarith⟩
    have h := Real.strictAntiOn_cos.antitoneOn hx' hπ' hx.2
    rw [Real.cos_pi_div_three] at h
    exact h.trans (le_max_left _ _)
  calc
    0 < (π/3)*(1/2) := by positivity
    _ = ∫ x in (0:ℝ)..π/3, (1/2:ℝ) := by simp [intervalIntegral.integral_const]
    _ ≤ ∫ x in (0:ℝ)..π/3, cosPart x :=
      intervalIntegral.integral_mono_on (by linarith) (continuous_const.intervalIntegrable _ _)
        (continuous_cosPart.intervalIntegrable _ _) hs
    _ ≤ sweep := intervalIntegral.integral_mono_interval le_rfl (by linarith) (by linarith)
      (.of_forall cosPart_nonneg) (continuous_cosPart.intervalIntegrable _ _)

def angularWeight (f : ℂ → ℂ) (r θ : ℝ) : ℝ :=
  max ((f (circleMap 0 r θ)).re / ‖f (circleMap 0 r θ)‖) 0 * ‖velocity f r θ‖

theorem angularWeight_nonneg (f : ℂ → ℂ) (r θ : ℝ) : 0 ≤ angularWeight f r θ :=
  mul_nonneg (le_max_right _ _) (norm_nonneg _)

theorem periodic_angularWeight (f : ℂ → ℂ) (r : ℝ) :
    Function.Periodic (angularWeight f r) (2*π) := by
  intro t
  rw [angularWeight,angularWeight,velocity,velocity,(periodic_circleMap 0 r) t]

theorem continuous_angularWeight {f : ℂ → ℂ} {S : Set ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hf : AnalyticOnNhd ℂ f S) (hS : sphere 0 r ⊆ S)
    (h0 : ∀ z ∈ sphere 0 r, f z ≠ 0) :
    Continuous (angularWeight f r) := by
  have hfc : Continuous (fun t => f (circleMap 0 r t)) :=
    continuousOn_univ.mp (hf.continuousOn.comp (continuous_circleMap 0 r).continuousOn
      (fun t _ => hS (circle_mem_sphere hr t)))
  have hquot := (continuous_re.comp hfc).div hfc.norm
    (fun t => norm_ne_zero_iff.mpr (h0 _ (circle_mem_sphere hr t)))
  exact (hquot.max continuous_const).mul (continuous_velocity hr hf hS h0).norm

theorem angular_lower {f : ℂ → ℂ} {S : Set ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hf : AnalyticOnNhd ℂ f S) (hS : sphere 0 r ⊆ S)
    (h0 : ∀ z ∈ sphere 0 r, f z ≠ 0)
    {a b : ℝ} (hab : a ≤ b) (hlen : b-a ≤ 2*π) {k : ℕ}
    (hinc : (k:ℝ)*(2*π) ≤ increment f r a b) :
    (k:ℝ)*sweep ≤ ∫ θ in (0:ℝ)..2*π, angularWeight f r θ := by
  obtain ⟨L,hL,hLexp,hInc⟩ := lift_exists hr hf hS h0
  have hLIm (t : ℝ) : HasDerivAt (fun θ => (L θ).im) (velocity f r t).im t :=
    imCLM.hasFDerivAt.comp_hasDerivAt t (hL t)
  have hLm : Continuous (fun t => (L t).im) :=
    continuous_iff_continuousAt.mpr (fun t => (hLIm t).continuousAt)
  let P (t : ℝ) := ∫ θ in (0:ℝ)..t, cosPart θ
  have hP (t : ℝ) : HasDerivAt P (cosPart t) t :=
    intervalIntegral.integral_hasDerivAt_right (continuous_cosPart.intervalIntegrable _ _)
      continuous_cosPart.stronglyMeasurable.aestronglyMeasurable.stronglyMeasurableAtFilter
      continuous_cosPart.continuousAt
  have hDP (t : ℝ) : HasDerivAt (fun θ => P ((L θ).im))
      (cosPart ((L t).im) * (velocity f r t).im) t :=
    (hP _).comp t (hLIm t)
  have hW : Continuous (angularWeight f r) := continuous_angularWeight hr hf hS h0
  have hV : Continuous (fun t => cosPart ((L t).im)*(velocity f r t).im) :=
    (continuous_cosPart.comp hLm).mul (continuous_im.comp (continuous_velocity hr hf hS h0))
  have hK : (∫ θ in (L a).im..((L a).im+(k:ℝ)*(2*π)), cosPart θ) = (k:ℝ)*sweep := by
    have he : ∫ θ in (L a).im..((L a).im+2*π), cosPart θ = sweep := by
      simpa only [zero_add,sweep] using periodic_cosPart.intervalIntegral_add_eq (L a).im 0
    simpa [zsmul_eq_mul,he] using periodic_cosPart.intervalIntegral_add_zsmul_eq (k:ℤ)
      (L a).im (fun x y => continuous_cosPart.intervalIntegrable x y)
  have hEnd : (L a).im+(k:ℝ)*(2*π) ≤ (L b).im := by rw [← hInc] at hinc; linarith
  have hStart : (L a).im ≤ (L a).im+(k:ℝ)*(2*π) := by
    exact le_add_of_nonneg_right (by positivity)
  calc
    (k:ℝ)*sweep = ∫ θ in (L a).im..((L a).im+(k:ℝ)*(2*π)), cosPart θ := hK.symm
    _ ≤ ∫ θ in (L a).im..(L b).im, cosPart θ :=
      intervalIntegral.integral_mono_interval le_rfl hStart hEnd (.of_forall cosPart_nonneg)
        (continuous_cosPart.intervalIntegrable _ _)
    _ = P ((L b).im) - P ((L a).im) := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hP x) (continuous_cosPart.intervalIntegrable _ _)
    _ = ∫ θ in a..b, cosPart ((L θ).im)*(velocity f r θ).im :=
      (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hDP x)
        (hV.intervalIntegrable _ _)).symm
    _ ≤ ∫ θ in a..b, angularWeight f r θ := by
      apply intervalIntegral.integral_mono_on hab (hV.intervalIntegrable _ _) (hW.intervalIntegrable _ _)
      intro t _
      have hl : (f (circleMap 0 r t)).re / ‖f (circleMap 0 r t)‖ = Real.cos (L t).im := by
        rw [← hLexp,Complex.exp_re,Complex.norm_exp,mul_div_cancel_left₀ _ (Real.exp_ne_zero _)]
      rw [angularWeight,hl,← cosPart]
      exact mul_le_mul_of_nonneg_left
        ((le_abs_self _).trans (Complex.abs_im_le_norm _)) (cosPart_nonneg _)
    _ ≤ ∫ θ in a..(a+2*π), angularWeight f r θ :=
      intervalIntegral.integral_mono_interval le_rfl hab (by linarith)
        (.of_forall (angularWeight_nonneg _ _)) (hW.intervalIntegrable _ _)
    _ = ∫ θ in (0:ℝ)..2*π, angularWeight f r θ := by
      simpa only [zero_add] using (periodic_angularWeight f r).intervalIntegral_add_eq a 0

/-- The radii where the argument bound can be divided by two, with zero included. -/
def lowerRadii (good : ℕ → ℝ → Prop) (k : ℕ) (R : ℝ) : Set ℝ :=
  insert 0 {r | 0 < r ∧ r < R ∧ good k r}

theorem lowerRadii_nonempty (good : ℕ → ℝ → Prop) (k : ℕ) (R : ℝ) :
    (lowerRadii good k R).Nonempty := ⟨0,mem_insert _ _⟩

theorem lowerRadii_bounded (good : ℕ → ℝ → Prop) (k : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    BddAbove (lowerRadii good k R) := ⟨R,fun r hr => by
      rcases hr with h | h
      · exact h ▸ hR
      · exact h.2.1.le⟩

private theorem quad_bound (R r k : ℝ) (hk : 0 < k) :
    R^2/(k+1) ≤ r^2/k+(R-r)^2 := by
  have he : (r^2/k+(R-r)^2)-R^2/(k+1) = (((k+1)*r-k*R)^2)/(k*(k+1)) := by
    have hk1 : k+1 ≠ 0 := by linarith
    field_simp
    ring
  apply sub_nonneg.mp
  rw [he]
  positivity

/-- Adding an annulus estimate at the first radius where the argument threshold doubles. -/
theorem multiscale_bound (good : ℕ → ℝ → Prop) (A : ℝ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hA0 : 0 ≤ A 0) (hzero : ∀ R > 0, ¬ good 0 R)
    (hgap : ∀ k R (_hR : 0 < R), good (k+1) R →
      ∀ t ∈ lowerRadii good k R, A t + c*(R-sSup (lowerRadii good k R))^2 ≤ A R) :
    ∀ k, 0 < k → ∀ R > 0, good k R → c*R^2/k ≤ A R := by
  intro k
  induction k with
  | zero => omega
  | succ k ih =>
    intro _ R hR hg
    let S := lowerRadii good k R
    let s := sSup S
    have hS : S.Nonempty := lowerRadii_nonempty good k R
    have hB : BddAbove S := lowerRadii_bounded good k hR.le
    have hclose : s ∈ closure S := csSup_mem_closure hS hB
    have hGap (t : ℝ) (ht : t∈S) : A t + c*(R-s)^2 ≤ A R := hgap k R hR hg t ht
    rcases eq_or_lt_of_le (Nat.zero_le k) with h | hk
    · subst k
      have he : S = {0} := by
        ext t
        simp only [S, lowerRadii, mem_insert_iff, mem_singleton_iff, mem_ofPred_eq]
        exact or_iff_left_of_imp (fun h => False.elim (hzero t h.1 h.2.2))
      have hs : s = 0 := by simp [s,he]
      have h := hGap 0 (mem_insert _ _)
      simp only [hs,sub_zero] at h
      simpa only [Nat.zero_add,Nat.cast_one,div_one] using (le_add_of_nonneg_left hA0).trans h
    · have hkR : (0:ℝ)<k := by exact_mod_cast hk
      let T := {r : ℝ | c*r^2/k ≤ A R - c*(R-s)^2}
      have hT : IsClosed T := isClosed_le (by fun_prop) continuous_const
      have hST : S ⊆ T := by
        intro t ht
        change c*t^2/(k:ℝ) ≤ A R - c*(R-s)^2
        apply le_sub_iff_add_le.mpr
        refine le_trans ?_ (hGap t ht)
        gcongr
        rcases ht with h | h
        · rw [Set.mem_singleton_iff.mp h]
          simp [hA0]
        · exact ih hk t h.1 h.2.2
      have hsT : s ∈ T := closure_minimal hST hT hclose
      have hs' : c*s^2/k ≤ A R - c*(R-s)^2 := hsT
      have hq := mul_le_mul_of_nonneg_left (quad_bound R s k hkR) hc
      push_cast
      calc
        c*R^2/((k:ℝ)+1) = c*(R^2/((k:ℝ)+1)) := by ring
        _ ≤ c*(s^2/k+(R-s)^2) := hq
        _ = c*s^2/k+c*(R-s)^2 := by ring
        _ ≤ A R := le_sub_iff_add_le.mp hs'

def annulus (a b : ℝ) : Set ℂ := {z | ‖z‖ ∈ Ioo a b}

theorem measurableSet_annulus (a b : ℝ) : MeasurableSet (annulus a b) :=
  measurableSet_Ioo.preimage measurable_norm

theorem polar_eq_circleMap (x : ℝ × ℝ) :
    Complex.polarCoord.symm x = circleMap 0 x.1 x.2 := by
  rw [Complex.polarCoord_symm_apply,circleMap,zero_add,Complex.exp_mul_I,← Complex.ofReal_cos,← Complex.ofReal_sin]

private theorem measurable_polarCircle :
    Measurable (fun p : ℝ × ℝ => circleMap 0 p.1 p.2) := by
  unfold circleMap
  fun_prop

theorem lintegral_annulus (W : ℂ → ℝ≥0∞) (hW : Measurable W)
    {a b : ℝ} (ha : 0 ≤ a) :
    (∫⁻ z in annulus a b, W z) =
      ∫⁻ r in Ioo a b, ∫⁻ θ in Ioo (-π) π,
        ENNReal.ofReal r * W (circleMap 0 r θ) := by
  let V (p : ℝ × ℝ) := ENNReal.ofReal p.1 * W (circleMap 0 p.1 p.2)
  let U : Set (ℝ × ℝ) := Ioi (0:ℝ) ×ˢ Ioo (-π) π
  let P : Set (ℝ × ℝ) := Ioo a b ×ˢ univ
  have hP : MeasurableSet P := measurableSet_Ioo.prod MeasurableSet.univ
  have hmeas : Measurable V := (ENNReal.measurable_ofReal.comp measurable_fst).mul
    (hW.comp measurable_polarCircle)
  have he : P ∩ U = Ioo a b ×ˢ Ioo (-π) π := by
    ext p
    simp only [P,U,mem_inter_iff,mem_prod,mem_univ,and_true,mem_Ioi]
    constructor
    · rintro ⟨h,_,h'⟩
      exact ⟨h,h'⟩
    · rintro ⟨h,h'⟩
      exact ⟨h,ha.trans_lt h.1,h'⟩
  calc
    (∫⁻ z in annulus a b, W z) = ∫⁻ z, (annulus a b).indicator W z :=
      (lintegral_indicator (measurableSet_annulus a b) _).symm
    _ = ∫⁻ p in U, ENNReal.ofReal p.1 * (annulus a b).indicator W (Complex.polarCoord.symm p) := by
      exact (Complex.lintegral_comp_polarCoord_symm ((annulus a b).indicator W)).symm
    _ = ∫⁻ p in U, P.indicator V p := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioo : MeasurableSet U)] with p hp
      have hpos : 0 ≤ p.1 := hp.1.le
      have hp' : Complex.polarCoord.symm p ∈ annulus a b ↔ p∈P := by
        change ‖Complex.polarCoord.symm p‖ ∈ Ioo a b ↔ p.1∈Ioo a b ∧ p.2∈univ
        rw [Complex.norm_polarCoord_symm,abs_of_nonneg hpos]
        simp
      by_cases h : p ∈ P
      · rw [Set.indicator_of_mem (hp'.mpr h),Set.indicator_of_mem h,polar_eq_circleMap]
      · rw [Set.indicator_of_notMem (fun H => h (hp'.mp H)),Set.indicator_of_notMem h,mul_zero]
    _ = ∫⁻ p in Ioo a b ×ˢ Ioo (-π) π, V p := by
      rw [lintegral_indicator hP,Measure.restrict_restrict hP,he]
    _ = _ := by
      change (∫⁻ p in Ioo a b ×ˢ Ioo (-π) π, V p ∂(volume.prod volume)) = _
      rw [← Measure.prod_restrict,lintegral_prod _ hmeas.aemeasurable]

def density (f : ℂ → ℂ) (z : ℂ) : ℝ :=
  max ((f z).re / ‖f z‖) 0 * ‖deriv f z / f z‖

theorem density_nonneg (f : ℂ → ℂ) (z : ℂ) : 0 ≤ density f z :=
  mul_nonneg (le_max_right _ _) (norm_nonneg _)

theorem density_zero_of_re_nonpos (f : ℂ → ℂ) {z : ℂ} (hz : (f z).re ≤ 0) :
    density f z = 0 := by rw [density,max_eq_right (div_nonpos_of_nonpos_of_nonneg hz (norm_nonneg _)),zero_mul]

theorem density_le (f : ℂ → ℂ) (z : ℂ) : density f z ≤ ‖deriv f z / f z‖ := by
  refine mul_le_of_le_one_left (norm_nonneg _) (max_le ?_ zero_le_one)
  by_cases hf : f z = 0
  · simp [hf]
  · exact (div_le_one (norm_pos_iff.mpr hf)).mpr (Complex.re_le_norm _)

theorem measurable_density {f : ℂ → ℂ} (hf : Measurable f) : Measurable (density f) :=
  (((Complex.continuous_re.measurable.comp hf).div hf.norm).max measurable_const).mul
    ((measurable_deriv f).div hf).norm

theorem angularWeight_eq_density_mul (f : ℂ → ℂ) {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) :
    angularWeight f r θ = r * density f (circleMap 0 r θ) := by
  rw [angularWeight,density,velocity,norm_mul,norm_mul,norm_circle hr,norm_I,mul_one]
  ring

theorem lintegral_angularWeight {f : ℂ → ℂ} {S : Set ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hf : AnalyticOnNhd ℂ f S) (hS : sphere 0 r ⊆ S) (h0 : ∀ z ∈ sphere 0 r, f z ≠ 0) :
    (∫⁻ θ in Ioo (-π) π, ENNReal.ofReal r * ENNReal.ofReal (density f (circleMap 0 r θ))) =
      ENNReal.ofReal (∫ θ in (0:ℝ)..2*π, angularWeight f r θ) := by
  have hp : ∫ θ in -π..(-π+2*π), angularWeight f r θ =
      ∫ θ in (0:ℝ)..2*π, angularWeight f r θ := by
    simpa only [zero_add] using (periodic_angularWeight f r).intervalIntegral_add_eq (-π) 0
  rw [show -π+2*π = π by ring] at hp
  rw [← hp,intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),← restrict_Ioo_eq_restrict_Ioc]
  have hW := continuous_angularWeight hr hf hS h0
  have hWi : Integrable (angularWeight f r) (volume.restrict (Ioo (-π) π)) :=
    (hW.integrableOn_Icc (a := -π) (b := π)).mono_set Ioo_subset_Icc_self
  rw [ofReal_integral_eq_lintegral_ofReal hWi (.of_forall (angularWeight_nonneg _ _))]
  apply lintegral_congr
  intro θ
  rw [angularWeight_eq_density_mul f hr θ,ENNReal.ofReal_mul hr]

theorem lintegral_lower_shell {f : ℂ → ℂ} {S : Set ℂ} (hfm : Measurable f)
    (hf : AnalyticOnNhd ℂ f S) {a b : ℝ} (ha : 0 ≤ a) (_hab : a ≤ b)
    (hS : ∀ r ∈ Ioo a b, sphere 0 r ⊆ S)
    (h0 : ∀ᵐ r ∂(volume.restrict (Ioo a b)), ∀ z ∈ sphere 0 r, f z ≠ 0)
    (k : ℕ)
    (h : ∀ r ∈ Ioo a b, (∀ z ∈ sphere 0 r, f z ≠ 0) →
      ¬ BoundedArgument f r ((k:ℝ)*(2*π))) :
    ENNReal.ofReal (((k:ℝ)*sweep)*(b-a)) ≤
      ∫⁻ z in (annulus a b ∩ {z | 0 < (f z).re}), ENNReal.ofReal (density f z) := by
  have he : (∫⁻ z in (annulus a b ∩ {z | 0 < (f z).re}), ENNReal.ofReal (density f z)) =
      ∫⁻ z in annulus a b, ENNReal.ofReal (density f z) := by
    have hm : MeasurableSet {z | 0 < (f z).re} :=
      measurableSet_lt measurable_const (Complex.continuous_re.measurable.comp hfm)
    rw [inter_comm,← Measure.restrict_restrict hm,← lintegral_indicator hm]
    apply lintegral_congr
    intro z
    by_cases hz : 0 < (f z).re
    · simp [hz]
    · simp [hz,density_zero_of_re_nonpos f (le_of_not_gt hz)]
  rw [he,lintegral_annulus (fun z => ENNReal.ofReal (density f z))
    (ENNReal.measurable_ofReal.comp (measurable_density hfm)) (b := b) ha]
  have hstep : ∀ᵐ r ∂(volume.restrict (Ioo a b)), ENNReal.ofReal ((k:ℝ)*sweep) ≤
      ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal r * ENNReal.ofReal (density f (circleMap 0 r θ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo,h0] with r hr hz
    rw [lintegral_angularWeight (ha.trans hr.1.le) hf (hS r hr) hz]
    obtain ⟨x,y,hxy,hxy',Hi⟩ : ∃ x y : ℝ, x≤y ∧ y-x≤2*π ∧
        (k:ℝ)*(2*π) ≤ increment f r x y := by
      by_contra H
      apply h r hr hz
      intro x y hxy hy
      exact lt_of_not_ge (fun H' => H ⟨x,y,hxy,hy,H'⟩)
    exact ENNReal.ofReal_le_ofReal (angular_lower (ha.trans hr.1.le) hf (hS r hr) hz hxy hxy' Hi)
  refine le_trans ?_ (lintegral_mono_ae hstep)
  rw [lintegral_const,Measure.restrict_apply MeasurableSet.univ,univ_inter,Real.volume_Ioo,
    ← ENNReal.ofReal_mul (mul_nonneg (Nat.cast_nonneg _) sweep_pos.le)]

private def poleVelocity (ζ : ℂ) (R θ : ℝ) : ℂ :=
  (circleMap 0 R θ - ζ)⁻¹ * (circleMap 0 R θ * I)

private theorem circle_sub_ne_zero {ζ : ℂ} {R : ℝ} (hζ : ‖ζ‖ < R) (θ : ℝ) :
    circleMap 0 R θ - ζ ≠ 0 := by
  intro h
  have hp : 0 ≤ R := (norm_nonneg ζ).trans hζ.le
  have he := congrArg norm (sub_eq_zero.mp h)
  rw [norm_circle hp] at he
  exact (ne_of_gt hζ) he

private theorem continuous_poleVelocity {ζ : ℂ} {R : ℝ} (hζ : ‖ζ‖ < R) :
    Continuous (poleVelocity ζ R) :=
  (((continuous_circleMap 0 R).sub continuous_const).inv₀ (circle_sub_ne_zero hζ)).mul
    ((continuous_circleMap 0 R).mul continuous_const)

private theorem poleVelocity_im_nonneg {ζ : ℂ} {R : ℝ} (hζ : ‖ζ‖ < R) (t : ℝ) :
    0 ≤ (poleVelocity ζ R t).im := by
  let w := circleMap 0 R t
  have hp : 0 ≤ R := (norm_nonneg ζ).trans hζ.le
  have hw : ‖w‖ = R := norm_circle hp t
  have hr : (w*conj ζ).re ≤ R*‖ζ‖ := by
    simpa only [norm_mul,Complex.norm_conj,hw] using Complex.re_le_norm (w*conj ζ)
  have hmul : (w * conj (w-ζ)).re = R^2-(w*conj ζ).re := by
    rw [map_sub, mul_sub, Complex.sub_re,Complex.mul_conj,Complex.ofReal_re,← Complex.sq_norm,hw]
  have h : 0 ≤ (w * conj (w-ζ)).re := by
    rw [hmul]
    nlinarith [mul_nonneg hp (sub_nonneg.mpr hζ.le)]
  change 0 ≤ ((w-ζ)⁻¹*(w*I)).im
  rw [show (w-ζ)⁻¹*(w*I) = (w*conj (w-ζ) * Complex.ofReal (normSq (w-ζ))⁻¹)*I by
    rw [Complex.inv_def]
    ring, Complex.mul_I_im]
  rw [Complex.mul_re]
  simp only [Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  exact mul_nonneg h (inv_nonneg.mpr (normSq_nonneg _))

private theorem poleVelocity_integral {ζ : ℂ} {R : ℝ} (hζ : ‖ζ‖ < R) :
    (∫ t in (0:ℝ)..2*π, poleVelocity ζ R t).im = 2*π := by
  have h : ζ ∈ ball (0:ℂ) R := by simpa using hζ
  have he := circleIntegral.integral_sub_inv_of_mem_ball h
  rw [circleIntegral] at he
  simp only [deriv_circleMap,smul_eq_mul] at he
  have he' : (∫ t in (0:ℝ)..2*π, poleVelocity ζ R t) = 2*(π:ℂ)*I := by
    simpa only [poleVelocity,mul_comm] using he
  rw [he']
  simp [Complex.mul_im]

private theorem increment_split {f g : ℂ → ℂ} {m : ℕ} {ζ : Fin m → ℂ} {R : ℝ}
    (hR : 0 < R) (hg : AnalyticOnNhd ℂ g (closedBall 0 R)) (hζ : ∀ i, ‖ζ i‖ < R)
    (h0 : ∀ z ∈ sphere 0 R, f z ≠ 0)
    (hd : ∀ z ∈ closedBall 0 R, f z ≠ 0 → deriv f z / f z =
      deriv g z + ∑ i, (z-ζ i)⁻¹)
    (a b : ℝ) :
    increment f R a b =
      (g (circleMap 0 R b)).im-(g (circleMap 0 R a)).im +
        ∑ i, (∫ θ in a..b, poleVelocity (ζ i) R θ).im := by
  let V (t : ℝ) := deriv g (circleMap 0 R t) * (circleMap 0 R t * I)
  have hs (t : ℝ) : circleMap 0 R t ∈ closedBall 0 R :=
    sphere_subset_closedBall (circle_mem_sphere hR.le t)
  have hv (t : ℝ) : velocity f R t = V t + ∑ i, poleVelocity (ζ i) R t := by
    rw [velocity,hd _ (hs t) (h0 _ (circle_mem_sphere hR.le t)),add_mul,Finset.sum_mul]
    rfl
  have hVa : Continuous V := by
    have hg' : Continuous (fun t => deriv g (circleMap 0 R t)) :=
      continuousOn_univ.mp (hg.deriv.continuousOn.comp (continuous_circleMap 0 R).continuousOn
        (fun t _ => hs t))
    exact hg'.mul ((continuous_circleMap 0 R).mul continuous_const)
  have hsum : IntervalIntegrable (fun t => ∑ i, poleVelocity (ζ i) R t) volume a b :=
    (continuous_finsetSum (Finset.univ : Finset (Fin m))
      (fun i _ => continuous_poleVelocity (hζ i))).intervalIntegrable a b
  have he : (∫ θ in a..b, V θ) = g (circleMap 0 R b) - g (circleMap 0 R a) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ (hVa.intervalIntegrable _ _)
    intro t _
    refine ((hg _ (hs t)).differentiableAt.hasDerivAt.scomp t
        (hasDerivAt_circleMap 0 R t)).congr_deriv ?_
    simp only [V,smul_eq_mul,mul_comm]
  simp_rw [increment,hv]
  rw [intervalIntegral.integral_add (hVa.intervalIntegrable _ _) hsum,
    intervalIntegral.integral_finsetSum (fun i _ => (continuous_poleVelocity (hζ i)).intervalIntegrable _ _),he]
  simp only [Complex.add_im,Complex.sub_im,Complex.im_sum]

theorem increment_full_turn {f g : ℂ → ℂ} {m : ℕ} {ζ : Fin m → ℂ} {R : ℝ}
    (hR : 0 < R) (hg : AnalyticOnNhd ℂ g (closedBall 0 R)) (hζ : ∀ i, ‖ζ i‖ < R)
    (h0 : ∀ z ∈ sphere 0 R, f z ≠ 0)
    (hd : ∀ z ∈ closedBall 0 R, f z ≠ 0 → deriv f z / f z =
      deriv g z + ∑ i, (z-ζ i)⁻¹) :
    increment f R 0 (2*π) = (m:ℝ)*(2*π) := by
  have hper : circleMap 0 R (2*π) = circleMap 0 R 0 := by simpa only [zero_add] using (periodic_circleMap 0 R) 0
  rw [increment_split hR hg hζ h0 hd,hper,sub_self,zero_add]
  simp only [poleVelocity_integral (hζ _),Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

theorem imag_oscillation {f g : ℂ → ℂ} {m : ℕ} {ζ : Fin m → ℂ} {R M : ℝ}
    (hR : 0 < R) (hg : AnalyticOnNhd ℂ g (closedBall 0 R)) (hζ : ∀ i, ‖ζ i‖ < R)
    (h0 : ∀ z ∈ sphere 0 R, f z ≠ 0)
    (hd : ∀ z ∈ closedBall 0 R, f z ≠ 0 → deriv f z / f z =
      deriv g z + ∑ i, (z-ζ i)⁻¹) (hArg : BoundedArgument f R M)
    {x y : ℂ} (hx : x ∈ sphere 0 R) (hy : y ∈ sphere 0 R) :
    (g y).im-(g x).im ≤ M := by
  obtain ⟨a,ha⟩ : x∈range (circleMap 0 R) := by
    rw [range_circleMap,abs_of_pos hR]
    exact hx
  obtain ⟨b,hb,hby⟩ : y ∈ circleMap 0 R '' Ioc a (a+2*π) := by
    rw [(periodic_circleMap 0 R).image_Ioc Real.two_pi_pos,range_circleMap,abs_of_pos hR]
    exact hy
  have hab : a ≤ b := hb.1.le
  have H := (hArg a b hab (by linarith [hb.2])).le
  rw [increment_split hR hg hζ h0 hd,ha,hby] at H
  have hs : 0 ≤ ∑ i, (∫ θ in a..b, poleVelocity (ζ i) R θ).im := by
    apply Finset.sum_nonneg
    intro i _
    have he : (∫ θ in a..b, (poleVelocity (ζ i) R θ).im) =
        (∫ θ in a..b, poleVelocity (ζ i) R θ).im :=
      Complex.imCLM.intervalIntegral_comp_comm ((continuous_poleVelocity (hζ i)).intervalIntegrable _ _)
    rw [← he]
    exact intervalIntegral.integral_nonneg hab (fun t _ => poleVelocity_im_nonneg (hζ i) t)
  linarith

def gradConstant : ℝ := Real.exp 1 / Real.exp (-1)

theorem gradConstant_pos : 0 < gradConstant := by unfold gradConstant; positivity

theorem norm_deriv_le_of_im_bound {g : ℂ → ℂ} {R M m δ : ℝ} (hR : 0 < R)
    (hM : 0 < M) (hδ : 0 < δ)
    (hg : AnalyticOnNhd ℂ g (closedBall 0 R))
    (him : ∀ w ∈ sphere 0 R, |(g w).im-m| ≤ M)
    {z : ℂ} (hz : ‖z‖+δ ≤ R) :
    ‖deriv g z‖ ≤ gradConstant*M/δ := by
  let H (w : ℂ) := (↑M : ℂ)⁻¹*((g w-(m:ℂ)*I)*I)
  let F (w : ℂ) := exp (H w)
  let G (w : ℂ) := exp (-H w)
  have hH : AnalyticOnNhd ℂ H (closedBall 0 R) := by
    intro w hw
    have := hg w hw
    unfold H
    fun_prop
  have hF : AnalyticOnNhd ℂ F (closedBall 0 R) := by
    intro w hw
    exact (hH w hw).cexp
  have hG : AnalyticOnNhd ℂ G (closedBall 0 R) := by
    intro w hw
    exact (hH w hw).neg.cexp
  have hRe (w : ℂ) : (H w).re = -((g w).im-m)/M := by
    simp [H,Complex.mul_re,Complex.mul_im,← Complex.ofReal_inv,div_eq_mul_inv,mul_comm]
  have hHr (w : ℂ) (hw : w ∈ sphere 0 R) : |(H w).re| ≤ 1 := by
    rw [hRe,abs_div,abs_neg,abs_of_pos hM,div_le_one hM]
    exact him w hw
  have hFB (w : ℂ) (hw : w ∈ closedBall 0 R) : ‖F w‖ ≤ Real.exp 1 := by
    apply Complex.norm_le_of_forall_mem_frontier_norm_le (U := ball (0:ℂ) R) isBounded_ball
      (hF.differentiableOn.diffContOnCl_ball subset_rfl) ?_ (by rwa [closure_ball (0:ℂ) hR.ne'])
    intro v hv
    rw [frontier_ball (0:ℂ) hR.ne'] at hv
    change ‖exp (H v)‖ ≤ _
    rw [Complex.norm_exp,Real.exp_le_exp]
    exact (le_abs_self _).trans (hHr v hv)
  have hGB (w : ℂ) (hw : w ∈ closedBall 0 R) : ‖G w‖ ≤ Real.exp 1 := by
    apply Complex.norm_le_of_forall_mem_frontier_norm_le (U := ball (0:ℂ) R) isBounded_ball
      (hG.differentiableOn.diffContOnCl_ball subset_rfl) ?_ (by rwa [closure_ball (0:ℂ) hR.ne'])
    intro v hv
    rw [frontier_ball (0:ℂ) hR.ne'] at hv
    change ‖exp (-H v)‖ ≤ _
    rw [Complex.norm_exp,Complex.neg_re,Real.exp_le_exp]
    exact (neg_le_abs _).trans (hHr v hv)
  have hsub : closedBall z δ ⊆ closedBall 0 R := by
    intro w hw
    rw [mem_closedBall] at hw ⊢
    exact (dist_triangle w z 0).trans (by rw [dist_zero_right]; linarith)
  have hzR : z∈closedBall 0 R := hsub (mem_closedBall_self hδ.le)
  have hFlo : Real.exp (-1) ≤ ‖F z‖ := by
    have h := hGB z hzR
    change ‖exp (-H z)‖ ≤ _ at h
    rw [Complex.norm_exp,Complex.neg_re,Real.exp_le_exp] at h
    change Real.exp (-1) ≤ ‖exp (H z)‖
    rw [Complex.norm_exp,Real.exp_le_exp]
    linarith
  have hd : ‖deriv F z‖ ≤ Real.exp 1 / δ :=
    Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hδ
      (hF.differentiableOn.diffContOnCl_ball hsub) (fun w hw => hFB w (hsub (sphere_subset_closedBall hw)))
  have he : HasDerivAt F (exp (H z)*((↑M : ℂ)⁻¹*(deriv g z*I))) z :=
    ((((hg z hzR).differentiableAt.hasDerivAt.sub_const ((m:ℂ)*I)).mul_const I).const_mul
      ((↑M:ℂ)⁻¹)).cexp
  rw [he.deriv,norm_mul,norm_mul,norm_mul,norm_I,mul_one,norm_inv,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos hM] at hd
  have hu : Real.exp (-1)*‖deriv g z‖/M ≤ Real.exp 1 / δ := by
    calc
      _ ≤ ‖exp (H z)‖*(M⁻¹*‖deriv g z‖) := by
        rw [div_eq_mul_inv,mul_right_comm (Real.exp (-1)),mul_assoc]
        exact mul_le_mul_of_nonneg_right hFlo (by positivity)
      _ ≤ _ := hd
  have hv := (div_le_div_iff₀ hM hδ).mp hu
  apply (le_div_iff₀ hδ).mpr
  calc
    ‖deriv g z‖*δ ≤ (Real.exp 1*M) / Real.exp (-1) := by
      apply (le_div_iff₀ (Real.exp_pos _)).mpr
      simpa only [mul_left_comm,mul_comm,mul_assoc] using hv
    _ = gradConstant*M := by unfold gradConstant; ring

def pole (ζ z : ℂ) : ℝ≥0∞ := (ENNReal.ofReal ‖z-ζ‖)⁻¹

theorem measurable_pole (ζ : ℂ) : Measurable (pole ζ) := by
  unfold pole
  fun_prop

private theorem pole_ball_origin (ρ : ℝ) :
    (∫⁻ z in ball (0:ℂ) ρ, pole 0 z) = ENNReal.ofReal (2*π*ρ) := by
  have he : ball (0:ℂ) ρ =ᵐ[(volume:Measure ℂ)] annulus 0 ρ := by
    have h0 : ∀ᵐ z ∂(volume:Measure ℂ), z ≠ 0 := by rw [ae_iff]; simp
    filter_upwards [h0] with z hz
    apply propext
    change z∈ball 0 ρ ↔ z∈annulus 0 ρ
    simp [annulus,hz]
  rw [Measure.restrict_congr_set he,lintegral_annulus (pole 0) (measurable_pole 0) le_rfl]
  calc
    _ = ∫⁻ r in Ioo (0:ℝ) ρ, volume (Ioo (-π) π) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      have hs : ∀ θ : ℝ, ENNReal.ofReal r * pole 0 (circleMap 0 r θ) = 1 := by
        intro θ
        rw [pole,sub_zero,norm_circle hr.1.le,ENNReal.mul_inv_cancel (by simpa using hr.1) ENNReal.ofReal_ne_top]
      simp only [hs,lintegral_const,one_mul,Measure.restrict_apply MeasurableSet.univ,univ_inter]
    _ = _ := by
      rw [lintegral_const,Measure.restrict_apply MeasurableSet.univ,univ_inter,
        Real.volume_Ioo,Real.volume_Ioo,sub_zero,← ENNReal.ofReal_mul (by linarith [Real.pi_pos])]
      congr 1
      ring

theorem pole_ball (ρ : ℝ) (ζ : ℂ) :
    (∫⁻ z in ball ζ ρ, pole ζ z) = ENNReal.ofReal (2*π*ρ) := by
  have hm : MeasurePreserving (fun z : ℂ => z-ζ) (volume:Measure ℂ) volume := by
    simpa only [sub_eq_add_neg] using measurePreserving_add_right (volume:Measure ℂ) (-ζ)
  have he : (fun z : ℂ => z-ζ) ⁻¹' ball (0:ℂ) ρ = ball ζ ρ := by
    ext z
    simp [dist_eq_norm]
  have hmr := hm.restrict_preimage (measurableSet_ball : MeasurableSet (ball (0:ℂ) ρ))
  rw [he] at hmr
  simpa only [pole,sub_zero] using (hmr.lintegral_comp (measurable_pole 0)).trans (pole_ball_origin ρ)

theorem pole_integral_le (E : Set ℂ) {ρ : ℝ} (hρ : 0 < ρ) (ζ : ℂ) :
    (∫⁻ z in E, pole ζ z) ≤
      ENNReal.ofReal (2*π*ρ) + ENNReal.ofReal (ρ⁻¹)*volume E := by
  let B := ball ζ ρ
  have hB : MeasurableSet B := measurableSet_ball
  have hp (z : ℂ) : pole ζ z ≤ B.indicator (pole ζ) z + ENNReal.ofReal (ρ⁻¹) := by
    by_cases h : z∈B
    · rw [indicator_of_mem h]
      exact le_add_of_nonneg_right zero_le
    · rw [indicator_of_notMem h,zero_add,pole,ENNReal.ofReal_inv_of_pos hρ]
      apply ENNReal.inv_le_inv.mpr
      apply ENNReal.ofReal_le_ofReal
      exact le_of_not_gt (by simpa [B,dist_eq_norm] using h)
  calc
    _ ≤ ∫⁻ z in E, B.indicator (pole ζ) z + ENNReal.ofReal (ρ⁻¹) := lintegral_mono hp
    _ = (∫⁻ z in E, B.indicator (pole ζ) z) + ENNReal.ofReal (ρ⁻¹)*volume E := by
      rw [lintegral_add_left ((measurable_pole ζ).indicator hB),lintegral_const,
        Measure.restrict_apply MeasurableSet.univ,univ_inter]
    _ ≤ _ := by
      gcongr
      rw [lintegral_indicator hB,Measure.restrict_restrict hB,← pole_ball ρ ζ]
      exact lintegral_mono_set inter_subset_left

theorem lintegral_upper_shell {f : ℂ → ℂ} {E : Set ℂ} {m : ℕ} (ζ : Fin m → ℂ)
    (hE : MeasurableSet E) {ρ D : ℝ} (hρ : 0 < ρ) (hD : 0 ≤ D)
    (hb : ∀ z ∈ E, density f z ≤ D + ∑ i, ‖z-ζ i‖⁻¹) :
    (∫⁻ z in E, ENNReal.ofReal (density f z)) ≤
      ENNReal.ofReal (D+(m:ℝ)/ρ)*volume E + (m:ℝ≥0∞)*ENNReal.ofReal (2*π*ρ) := by
  have H : ∀ z ∈ E, ENNReal.ofReal (density f z) ≤ ENNReal.ofReal D + ∑ i, pole (ζ i) z := by
    intro z hz
    refine (ENNReal.ofReal_le_ofReal (hb z hz)).trans ?_
    rw [ENNReal.ofReal_add hD (Finset.sum_nonneg (fun _ _ => inv_nonneg.mpr (norm_nonneg _))),
      ENNReal.ofReal_sum_of_nonneg (fun _ _ => inv_nonneg.mpr (norm_nonneg _))]
    gcongr
    exact ENNReal.ofReal_inv_le
  calc
    _ ≤ ∫⁻ z in E, ENNReal.ofReal D + ∑ i, pole (ζ i) z := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hE] with z hz using H z hz
    _ = ENNReal.ofReal D * volume E + ∑ i, ∫⁻ z in E, pole (ζ i) z := by
      rw [lintegral_add_left measurable_const,lintegral_const,Measure.restrict_apply MeasurableSet.univ,
        univ_inter,lintegral_finsetSum _ (fun i _ => measurable_pole (ζ i))]
    _ ≤ ENNReal.ofReal D * volume E +
        ∑ _ : Fin m, (ENNReal.ofReal (2*π*ρ) + ENNReal.ofReal (ρ⁻¹)*volume E) := by
      gcongr
      exact pole_integral_le E hρ _
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      rw [ENNReal.ofReal_add hD (by positivity),div_eq_mul_inv,
        ENNReal.ofReal_mul (p := (m:ℝ)) (by positivity),ENNReal.ofReal_natCast]
      ring

def turnThreshold (k : ℕ) : ℝ := (2:ℝ)^k*(2*π)

def lowerConstant : ℝ := sweep/(4*π)

def upperConstant : ℝ := gradConstant + (π*lowerConstant)⁻¹

def shellConstant : ℝ := lowerConstant/(8*upperConstant)

theorem lowerConstant_pos : 0 < lowerConstant := div_pos sweep_pos (by positivity)

theorem upperConstant_pos : 0 < upperConstant :=
  add_pos gradConstant_pos (inv_pos.mpr (mul_pos Real.pi_pos lowerConstant_pos))

theorem shellConstant_pos : 0 < shellConstant :=
  div_pos lowerConstant_pos (mul_pos (by norm_num) upperConstant_pos)

private theorem shell_numeric {δ M A : ℝ} (hδ : 0 < δ) (hM : 0 < M) (hA : 0 ≤ A) (m : ℕ)
    (hm : (m:ℝ)*(2*π) ≤ M)
    (hi : M*lowerConstant*δ ≤
      (gradConstant*M/δ+(m:ℝ)/(lowerConstant*δ/2))*A+(m:ℝ)*(2*π*(lowerConstant*δ/2))) :
    shellConstant * (2*δ)^2 ≤ A := by
  let ρ := lowerConstant*δ/2
  have hl := lowerConstant_pos
  have hu := upperConstant_pos
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hπ := Real.pi_pos
  have hmn : (m:ℝ) ≤ M/(2*π) := (le_div_iff₀ (mul_pos (by norm_num) hπ)).mpr hm
  have hbig : (gradConstant*M/δ+(m:ℝ)/ρ)*A+(m:ℝ)*(2*π*ρ) ≤
      M*(upperConstant/δ*A+lowerConstant*δ/2) := by
    calc
      _ ≤ (gradConstant*M/δ+(M/(2*π))/ρ)*A+(M/(2*π))*(2*π*ρ) := by gcongr
      _ = _ := by
        unfold upperConstant
        dsimp [ρ]
        field_simp
  have haux : lowerConstant*δ ≤ upperConstant/δ*A + lowerConstant*δ/2 := by
    apply (mul_le_mul_iff_right₀ hM).mp
    exact (by simpa only [mul_assoc] using hi.trans hbig)
  have haux' : lowerConstant*δ/2 ≤ (upperConstant*A)/δ := by
    rw [show upperConstant/δ*A=upperConstant*A/δ by ring] at haux
    linarith
  have H := (le_div_iff₀ hδ).mp haux'
  unfold shellConstant
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (mul_pos (by norm_num) hu)).mpr
  nlinarith [show lowerConstant*(2*δ)^2=8*(lowerConstant*δ/2*δ) by ring]

def positivePart (f : ℂ → ℂ) : Set ℂ := {z | 0 < (f z).re}

def positiveDisk (f : ℂ → ℂ) (R : ℝ) : Set ℂ := ball 0 R ∩ positivePart f

def positiveArea (f : ℂ → ℂ) (R : ℝ) : ℝ := (volume (positiveDisk f R)).toReal

private theorem measurable_positivePart {f : ℂ → ℂ} (hfm : Measurable f) :
    MeasurableSet (positivePart f) :=
  measurableSet_lt measurable_const (Complex.continuous_re.measurable.comp hfm)

private theorem positiveDisk_volume_ne_top (f : ℂ → ℂ) (R : ℝ) :
    volume (positiveDisk f R) ≠ ⊤ :=
  ne_of_lt ((measure_mono inter_subset_left).trans_lt (measure_ball_lt_top (μ := (volume:Measure ℂ))))

private theorem positiveArea_mono (f : ℂ → ℂ) : Monotone (positiveArea f) :=
  fun _ _ h => ENNReal.toReal_mono (positiveDisk_volume_ne_top _ _)
    (measure_mono (inter_subset_inter_left _ (ball_subset_ball h)))

private theorem shell_volume_ne_top (f : ℂ → ℂ) (s R : ℝ) :
    volume (annulus s R ∩ positivePart f) ≠ ⊤ := by
  apply ne_of_lt
  refine (measure_mono (show annulus s R ∩ positivePart f ⊆ ball 0 R from ?_)).trans_lt
    (measure_ball_lt_top (μ := (volume:Measure ℂ)))
  intro z hz
  exact mem_ball_zero_iff.mpr hz.1.2

private theorem ae_radial_nonzero {f : ℂ → ℂ} {S a b : ℝ} (hb : b ≤ S)
    (hfin : ({z : ℂ | ‖z‖<S ∧ f z=0}).Finite) :
    ∀ᵐ r ∂(volume.restrict (Ioo a b)), ∀ z ∈ sphere 0 r, f z ≠ 0 := by
  let T := norm '' {z : ℂ | ‖z‖<S ∧ f z=0}
  have hT : T.Finite := hfin.image norm
  have hn : ∀ᵐ r ∂(volume : Measure ℝ), r ∉ T := by
    rw [ae_iff]
    rw [show {a : ℝ | ¬a∉T} = T by ext; simp]
    exact hT.measure_zero _
  filter_upwards [ae_restrict_mem measurableSet_Ioo,ae_restrict_of_ae hn] with r hr ht z hz he
  rw [Metric.mem_sphere,dist_zero_right] at hz
  exact ht ⟨z,⟨hz.trans_lt (hr.2.trans_le hb),he⟩,hz⟩

private theorem shell_area {f : ℂ → ℂ} (hfm : Measurable f) {S R s : ℝ}
    (hf : AnalyticOnNhd ℂ f (ball 0 S)) (hf0 : f 0 = 0)
    (hfin : ({z : ℂ | ‖z‖<S ∧ f z=0}).Finite)
    (hR : 0 < R) (hRS : R < S) (hs : 0 ≤ s) (hsR : s < R)
    (h0 : ∀ z ∈ sphere 0 R, f z ≠ 0) (k : ℕ) (hArg : BoundedArgument f R (turnThreshold (k+1)))
    (hnot : ∀ r ∈ Ioo s ((R+s)/2), (∀ z ∈ sphere 0 r, f z ≠ 0) →
      ¬ BoundedArgument f r (turnThreshold k)) :
    shellConstant*(R-s)^2 ≤ (volume (annulus s ((R+s)/2) ∩ positivePart f)).toReal := by
  obtain ⟨m,ζ,g,hζ,_,hga,hgd⟩ := exists_logDeriv_factor hR hRS hf hf0 hfin h0
  let δ := (R-s)/2
  let E := annulus s ((R+s)/2) ∩ positivePart f
  let M := turnThreshold (k+1)
  let ρ := lowerConstant*δ/2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hM : 0 < M := by dsimp [M,turnThreshold]; positivity
  have hℓ := lowerConstant_pos
  have hgpos := gradConstant_pos
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hE : MeasurableSet E := (measurableSet_annulus s _).inter (measurable_positivePart hfm)
  have hvol : volume E ≠ ⊤ := shell_volume_ne_top f s _
  have hsF (r : ℝ) (hr : r∈Ioo s ((R+s)/2)) : sphere 0 r ⊆ ball (0:ℂ) S := by
    intro z hz
    rw [Metric.mem_sphere,dist_zero_right] at hz
    rw [mem_ball_zero_iff,hz]
    linarith [hr.2]
  have hLower := lintegral_lower_shell hfm hf hs (by linarith) hsF
    (ae_radial_nonzero (by linarith) hfin) (2^k)
    (by simpa only [turnThreshold,Nat.cast_pow,Nat.cast_ofNat] using hnot)
  have hLId : ((↑(2^k:ℕ):ℝ)*sweep)*((R+s)/2-s) = M*lowerConstant*δ := by
    simp only [Nat.cast_pow,Nat.cast_ofNat,M,turnThreshold,pow_succ,lowerConstant,δ]
    field_simp [Real.pi_pos.ne']
    ring
  rw [hLId] at hLower
  have hMbound : (m:ℝ)*(2*π) ≤ M := by
    have HH := hArg 0 (2*π) (by positivity) (by simp)
    rw [increment_full_turn hR hga hζ h0 hgd] at HH
    exact HH.le
  let x : ℂ := (R:ℂ)
  have hx : x∈sphere (0:ℂ) R := by simp [x,abs_of_pos hR]
  have hgim (z : ℂ) (hz : z∈sphere (0:ℂ) R) : |(g z).im-(g x).im| ≤ M := by
    rw [abs_le]
    exact ⟨by have h := imag_oscillation hR hga hζ h0 hgd hArg hz hx; linarith,
      imag_oscillation hR hga hζ h0 hgd hArg hx hz⟩
  have hbd (z : ℂ) (hz : z∈E) : density f z ≤ gradConstant*M/δ + ∑ i, ‖z-ζ i‖⁻¹ := by
    have hzn : ‖z‖+δ ≤ R := by dsimp [δ]; linarith [hz.1.2]
    have hzcl : z∈closedBall (0:ℂ) R := mem_closedBall_zero_iff.mpr (by linarith)
    have hzf : f z ≠ 0 := by intro h; have H := hz.2; change 0 < (f z).re at H; simp [h] at H
    have hh := norm_deriv_le_of_im_bound hR hM hδ hga hgim hzn
    refine (density_le f z).trans ?_
    rw [hgd z hzcl hzf]
    refine (norm_add_le _ _).trans (add_le_add hh ?_)
    exact (norm_sum_le _ _).trans_eq (by simp only [norm_inv])
  have hUpper := lintegral_upper_shell ζ hE hρ
    (by positivity : 0 ≤ gradConstant*M/δ) hbd
  let A := (volume E).toReal
  have hA : 0 ≤ A := ENNReal.toReal_nonneg
  have heA : volume E = ENNReal.ofReal A := (ENNReal.ofReal_toReal hvol).symm
  change ENNReal.ofReal (M*lowerConstant*δ) ≤ _ at hLower
  have hu := hLower.trans hUpper
  rw [heA,← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (by positivity : 0 ≤ (m:ℝ)),
    ← ENNReal.ofReal_add (by positivity) (by positivity)] at hu
  have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hu
  have h := shell_numeric hδ hM hA m hMbound hreal
  simpa only [show R-s = 2*δ by dsimp [δ]; ring] using h

/-- A positive sign has area of order one over the number of doublings of the argument bound. -/
theorem positiveArea_large {f : ℂ → ℂ} {S : ℝ} (hfm : Measurable f)
    (hf : AnalyticOnNhd ℂ f (ball 0 S)) (hf0 : f 0 = 0)
    (hfin : ({z : ℂ | ‖z‖<S ∧ f z=0}).Finite)
    {k : ℕ} (hk : 0 < k) {R : ℝ} (hR : 0 < R) (hRS : R<S)
    (h0 : ∀ z ∈ sphere 0 R, f z ≠ 0) (hArg : BoundedArgument f R (turnThreshold k)) :
    shellConstant*R^2/k ≤ positiveArea f R := by
  let good (j : ℕ) (r : ℝ) := r<S ∧ (∀ z ∈ sphere 0 r, f z ≠ 0) ∧
    BoundedArgument f r (turnThreshold j)
  refine multiscale_bound good (positiveArea f) shellConstant shellConstant_pos.le
    ENNReal.toReal_nonneg ?_ ?_ k hk R hR ⟨hRS,h0,hArg⟩
  · intro r hr h
    obtain ⟨m,ζ,g,hζ,⟨i,_⟩,hga,hgd⟩ := exists_logDeriv_factor hr h.1 hf hf0 hfin h.2.1
    have hF := h.2.2 0 (2*π) (by positivity) (by simp)
    rw [increment_full_turn hr hga hζ h.2.1 hgd,turnThreshold,pow_zero,one_mul] at hF
    have hm : (1:ℝ) ≤ m := by exact_mod_cast Fin.pos i
    nlinarith [Real.pi_pos]
  · intro j r hr hgood t ht
    let U := lowerRadii good j r
    let s := sSup U
    have hU : BddAbove U := lowerRadii_bounded good j hr.le
    have hs0 : 0 ≤ s := le_csSup hU (mem_insert _ _)
    have hsR : s ≤ r := csSup_le (lowerRadii_nonempty good j r) (fun q hq => by
      rcases hq with hq | hq
      · exact hq ▸ hr.le
      · exact hq.2.1.le)
    have htS : t ≤ s := le_csSup hU ht
    change positiveArea f t + shellConstant*(r-s)^2 ≤ positiveArea f r
    rcases hsR.eq_or_lt with h | h
    · rw [h,sub_self,zero_pow (by decide),mul_zero,add_zero]
      exact positiveArea_mono f (htS.trans hsR)
    · let E := annulus s ((r+s)/2) ∩ positivePart f
      have hE : MeasurableSet E := (measurableSet_annulus s _).inter (measurable_positivePart hfm)
      have hsid : shellConstant*(r-s)^2 ≤ (volume E).toReal := by
        apply shell_area hfm hf hf0 hfin hr hgood.1 hs0 h hgood.2.1 j hgood.2.2
        intro p hp hpn hag
        have H : p∈U := mem_insert_of_mem _ ⟨hs0.trans_lt hp.1,by linarith [hp.2],
          (by linarith [hgood.1,hp.2] : p<S),hpn,hag⟩
        exact (not_lt_of_ge (le_csSup hU H)) hp.1
      have hd : Disjoint (positiveDisk f t) E := Set.disjoint_left.mpr (fun z hz hz' =>
        (not_lt_of_ge htS) ((mem_ball_zero_iff.mp hz.1).trans' hz'.1.1))
      have hu : positiveDisk f t ∪ E ⊆ positiveDisk f r := by
        rintro z (hz | hz)
        · exact ⟨ball_subset_ball (htS.trans hsR) hz.1,hz.2⟩
        · exact ⟨mem_ball_zero_iff.mpr (by linarith [hz.1.2]),hz.2⟩
      have hvol : volume (positiveDisk f t) + volume E ≤ volume (positiveDisk f r) := by
        rw [← measure_union hd hE]
        exact measure_mono hu
      have H := ENNReal.toReal_mono (positiveDisk_volume_ne_top f r) hvol
      rw [ENNReal.toReal_add (positiveDisk_volume_ne_top _ _) (shell_volume_ne_top _ _ _)] at H
      exact (add_le_add_right hsid _).trans H

end LemniscateNPS

namespace LemniscateLog

private theorem logarithm_measurable {n : ℕ} (a : Fin n → ℂ) : Measurable (logarithm a) := by
  unfold logarithm
  exact (Finset.measurable_fun_sum _ (fun i _ => Complex.measurable_log.comp (by fun_prop))).neg

private theorem finite_logarithm_zeros {n : ℕ} {a : Fin n → ℂ} (ha : ∀ i, ‖a i‖ ≤ 1)
    (h : ∃ i, a i ≠ 0) : ({z : ℂ | ‖z‖<1 ∧ logarithm a z=0}).Finite := by
  classical
  let Q : ℂ[X] := reflected a - 1
  have hQ : Q ≠ 0 := by
    obtain ⟨x,_,hx⟩ := reflected_has_root h
    intro he
    have H := congrArg (Polynomial.eval x) he
    simp [Q,hx] at H
  refine Q.roots.toFinset.finite_toSet.subset ?_
  intro z hz
  have h := exp_neg_logarithm ha hz.1
  rw [hz.2,neg_zero,Complex.exp_zero] at h
  simpa [Multiset.mem_toFinset,Polynomial.mem_roots hQ,Polynomial.IsRoot,Q,sub_eq_zero] using h.symm

private theorem exists_nonsingular_radius {f : ℂ → ℂ} (hfin : ({z : ℂ | ‖z‖<1 ∧ f z=0}).Finite) :
    ∃ r : ℝ, 1/2<r ∧ r<3/4 ∧ ∀ z ∈ sphere 0 r, f z ≠ 0 := by
  classical
  let T := norm '' {z : ℂ | ‖z‖<1 ∧ f z=0}
  have hT : T.Finite := hfin.image norm
  obtain ⟨r,hr,hout⟩ : ∃ r ∈ Ioo (1/2:ℝ) (3/4), r ∉ T := by
    by_contra! h
    have hv := measure_mono (μ := (volume:Measure ℝ)) (show Ioo (1/2:ℝ) (3/4) ⊆ T from h)
    rw [hT.measure_zero _ ,Real.volume_Ioo] at hv
    norm_num at hv
  refine ⟨r,hr.1,hr.2,fun z hz hf => ?_⟩
  rw [mem_sphere,dist_zero_right] at hz
  exact hout ⟨z,⟨hz.trans_lt (hr.2.trans (by norm_num)),hf⟩,hz⟩

private theorem log_count_bounds {n : ℕ} (hn : 2 ≤ n) :
    (n:ℝ) < (2:ℝ)^(Nat.log 2 n+1) ∧
    ((Nat.log 2 n+1:ℕ):ℝ)*Real.log 2 ≤ 2*Real.log n := by
  constructor
  · exact_mod_cast Nat.lt_pow_succ_log_self (by decide : 1 < 2) n
  · have hn0 : n ≠ 0 := by omega
    have hp : (2:ℝ)^Nat.log 2 n ≤ (n:ℝ) := by exact_mod_cast Nat.pow_log_le_self 2 hn0
    have hlog := Real.log_le_log (by positivity) hp
    rw [Real.log_pow] at hlog
    have hn2 : (2:ℝ) ≤ n := by exact_mod_cast hn
    have hmin := Real.log_le_log (by norm_num : (0:ℝ)<2) hn2
    push_cast
    linarith

end LemniscateLog

open LemniscateNPS LemniscateLog in
open scoped Real in
/-- Erdős 116 via reflection and the sign-area estimate of Nazarov, Polterovich, and Sodin.
See https://arxiv.org/abs/2503.18270 and https://arxiv.org/abs/math/0402412, Section 2. -/
theorem OMA.solution : type_of% @Erdos116.erdos_116.variants.log := by
  let c := min (shellConstant*Real.log 2/8) (π*Real.log 2)
  have hlog2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hc : 0 < c := lt_min (div_pos (mul_pos shellConstant_pos hlog2) (by norm_num))
    (mul_pos Real.pi_pos hlog2)
  refine ⟨c,hc,?_⟩
  intro n hn a ha
  have npos : (1:ℝ) < n := by exact_mod_cast (show 1<n by omega)
  have hlog : 0 < Real.log (n:ℝ) := Real.log_pos npos
  let E : Set ℂ := {w | ‖∏ i, (w-a i)‖ < 1}
  by_cases h : ∃ i, a i ≠ 0
  · let f := logarithm a
    have hfm : Measurable f := LemniscateLog.logarithm_measurable a
    have hf : AnalyticOnNhd ℂ f (ball 0 1) := logarithm_analyticOn ha
    have hfin : ({z : ℂ | ‖z‖<1 ∧ f z=0}).Finite := LemniscateLog.finite_logarithm_zeros ha h
    obtain ⟨R,hRl,hRu,hR0⟩ := LemniscateLog.exists_nonsingular_radius hfin
    have hR : 0 < R := by linarith
    have hR1 : R < 1 := by linarith
    let k := Nat.log 2 n+1
    have hk : 0 < k := Nat.zero_lt_succ _
    have hk' : (0:ℝ) < k := by exact_mod_cast hk
    have hs : sphere (0:ℂ) R ⊆ ball 0 1 := fun z hz =>
      mem_ball.mpr ((mem_sphere.mp hz).trans_lt hR1)
    have hl := finite_levelOnCircle a h R
    have he : {w : ℂ | ‖w‖=R ∧ (f w).re=0} =
        {w : ℂ | ‖w‖=R ∧ ‖(reflected a).eval w‖=1} := by
      ext w
      constructor
      · rintro ⟨hw,hz⟩
        exact ⟨hw,(re_zero_iff ha (hw.trans_lt hR1)).mp hz⟩
      · rintro ⟨hw,hz⟩
        exact ⟨hw,(re_zero_iff ha (hw.trans_lt hR1)).mpr hz⟩
    have hArg : BoundedArgument f R (turnThreshold k) := by
      intro x y hx hy
      refine (increment_le_of_level_card hR hf hs hR0 (2*n)
        (by rw [he]; exact hl.1) (by rw [he]; exact hl.2) hx hy).trans_lt ?_
      have H := (LemniscateLog.log_count_bounds hn).1
      change ((n:ℝ)) < (2:ℝ)^k at H
      push_cast
      unfold turnThreshold
      have H' : (n:ℝ)+1 ≤ (2:ℝ)^k := by
        have HNat : n < (2:ℕ)^k := by exact_mod_cast H
        exact_mod_cast (Nat.succ_le_of_lt HNat)
      calc
        _ < (2*(2:ℝ)^k)*π := mul_lt_mul_of_pos_right (by linarith) Real.pi_pos
        _ = _ := by ring
    have hA := positiveArea_large hfm hf (logarithm_zero a) hfin hk hR hR1 hR0 hArg
    have hE : positiveDisk f R ⊆ E := by
      intro w hw
      have hwD : ‖w‖ < 1 := (mem_ball_zero_iff.mp hw.1).trans hR1
      exact (norm_prod_le_reflected ha hwD.le).trans_lt
        ((re_pos_iff ha hwD).mp hw.2)
    have hscale : c / Real.log (n:ℝ) ≤ shellConstant*R^2/k := by
      apply (div_le_div_iff₀ hlog hk').mpr
      calc
        c*k ≤ (shellConstant*Real.log 2/8)*k :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) hk'.le
        _ ≤ shellConstant*(Real.log n/4) := by
          have H := mul_le_mul_of_nonneg_left (LemniscateLog.log_count_bounds hn).2 shellConstant_pos.le
          nlinarith only [show shellConstant * (k * Real.log 2) ≤ shellConstant*(2*Real.log n) from H]
        _ ≤ shellConstant*R^2*Real.log n := by
          have hsR : (1/4:ℝ) ≤ R^2 := by nlinarith
          calc
            _ = shellConstant*((1/4:ℝ)*Real.log n) := by ring
            _ ≤ shellConstant*(R^2*Real.log n) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsR hlog.le) shellConstant_pos.le
            _ = _ := by ring
    exact (ENNReal.ofReal_le_ofReal (hscale.trans hA)).trans
      (((ENNReal.ofReal_toReal (positiveDisk_volume_ne_top f R)).le).trans (measure_mono hE))
  · push Not at h
    have hsub : ball (0:ℂ) 1 ⊆ E := by
      intro w hw
      have hw' := mem_ball_zero_iff.mp hw
      have hN : n ≠ 0 := by omega
      change ‖∏ i, (w-a i)‖ < 1
      simp only [h,sub_zero,Finset.prod_const,Finset.card_univ,Fintype.card_fin,norm_pow]
      exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) hN).mpr hw'
    have hB : c / Real.log (n:ℝ) ≤ π := by
      apply (div_le_iff₀ hlog).mpr
      exact (min_le_right _ _).trans (mul_le_mul_of_nonneg_left
        (Real.log_le_log (by norm_num) (by exact_mod_cast hn)) Real.pi_pos.le)
    refine (ENNReal.ofReal_le_ofReal hB).trans ?_
    calc
      ENNReal.ofReal π = volume (ball (0:ℂ) 1) := by
        rw [Complex.volume_ball,ENNReal.ofReal_one,one_pow,one_mul]
        change ENNReal.ofReal (NNReal.pi:ℝ) = (NNReal.pi:ℝ≥0∞)
        exact ENNReal.ofReal_coe_nnreal
      _ ≤ volume E := measure_mono hsub