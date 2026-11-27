import FormalConjectures.Wikipedia.Bloch
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Analytic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! The univalent Bloch lower bound via the odd Grunsky compression and a rational disk estimate. The complex-analytic approach is based on Wikström (arXiv:2610.34580). -/

section

/- Nonnegative weighted boundary flux for exterior univalent maps. -/

/- Weighted area comparison for two differentiable parameterizations of the plane. -/

open MeasureTheory Set Complex Module
open scoped Interval ComplexConjugate

namespace GrunskyArea

abbrev Plane := ℝ × ℝ

private theorem det_cols (L : Plane →L[ℝ] Plane) :
    L.toLinearMap.det = (L (1,0)).1 * (L (0,1)).2 - (L (0,1)).1 * (L (1,0)).2 := by
  let B := Basis.finTwoProd ℝ
  rw [← LinearMap.det_toMatrix B]
  have hM : LinearMap.toMatrix B B L.toLinearMap =
      !![(L (1,0)).1, (L (0,1)).1; (L (1,0)).2, (L (0,1)).2] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [LinearMap.toMatrix_apply, B, Basis.finTwoProd_zero, Basis.finTwoProd_one,
        Basis.coe_finTwoProd_repr]
  rw [hM, Matrix.det_fin_two]
  simp

/-- In real coordinates, the determinant of the derivative is the complex flux of its columns. -/
theorem det_eq_flux (L : Plane →L[ℝ] Plane) {u v : ℂ}
    (hu : L (1,0) = (u.re,u.im)) (hv : L (0,1) = (v.re,v.im)) :
    L.toLinearMap.det = (conj u * v).im := by
  rw [det_cols, hu, hv]
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

/-- Area comparison, expressed as iterated integrals on the two parameter rectangles. -/
theorem chart_integral_le (f g : Plane → Plane) (df dg : Plane → Plane →L[ℝ] Plane)
    (w : Plane → ℝ) (a b c d e k l m : ℝ)
    (ha : a ≤ b) (hc : c ≤ d) (he : e ≤ k) (hl : l ≤ m)
    (hfi : InjOn f (uIoc a b ×ˢ uIoc c d)) (hgi : InjOn g (uIoc e k ×ˢ uIoc l m))
    (hf' : ∀ x ∈ uIoc a b ×ˢ uIoc c d, HasFDerivAt f (df x) x)
    (hg' : ∀ x ∈ uIoc e k ×ˢ uIoc l m, HasFDerivAt g (dg x) x)
    (hsub : f '' (uIoc a b ×ˢ uIoc c d) ⊆ g '' (uIoc e k ×ˢ uIoc l m))
    (hg : ContinuousOn g (uIcc e k ×ˢ uIcc l m)) (hw : Continuous w)
    (hw0 : ∀ x, 0 ≤ w x) :
    (∫ t in a..b, ∫ θ in c..d, |(df (t,θ)).toLinearMap.det| * w (f (t,θ))) ≤
      (∫ t in e..k, ∫ θ in l..m, |(dg (t,θ)).toLinearMap.det| * w (g (t,θ))) := by
  let S := uIoc a b ×ˢ uIoc c d
  let T := uIoc e k ×ˢ uIoc l m
  have hST : (g '' T) ⊆ g '' (uIcc e k ×ˢ uIcc l m) :=
    Set.image_mono (Set.prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)
  have hK : IsCompact (g '' (uIcc e k ×ˢ uIcc l m)) :=
    (isCompact_uIcc.prod isCompact_uIcc).image_of_continuousOn hg
  have hgInt : IntegrableOn w (g '' T) volume :=
    (hw.continuousOn.integrableOn_compact hK).mono_set hST
  have hfInt : IntegrableOn w (f '' S) volume := hgInt.mono_set hsub
  have hcomp : (∫ z in f '' S, w z) ≤ (∫ z in g '' T, w z) :=
    setIntegral_mono_set hgInt (Filter.Eventually.of_forall hw0)
      (Filter.Eventually.of_forall hsub)
  have hS : MeasurableSet S := measurableSet_uIoc.prod measurableSet_uIoc
  have hT : MeasurableSet T := measurableSet_uIoc.prod measurableSet_uIoc
  have hfW : ∀ x ∈ S, HasFDerivWithinAt f (df x) S x :=
    fun x hx => (hf' x hx).hasFDerivWithinAt
  have hgW : ∀ x ∈ T, HasFDerivWithinAt g (dg x) T x :=
    fun x hx => (hg' x hx).hasFDerivWithinAt
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hS hfW hfi,
    integral_image_eq_integral_abs_det_fderiv_smul volume hT hgW hgi] at hcomp
  have hfD := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hS hfW hfi w).1 hfInt
  have hgD := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hT hgW hgi w).1 hgInt
  simp only [S,T, Measure.volume_eq_prod] at hcomp hfD hgD
  rw [setIntegral_prod _ hfD, setIntegral_prod _ hgD,
    uIoc_of_le ha,uIoc_of_le hc,uIoc_of_le he,uIoc_of_le hl] at hcomp
  simpa only [intervalIntegral.integral_of_le ha, intervalIntegral.integral_of_le hc,
    intervalIntegral.integral_of_le he, intervalIntegral.integral_of_le hl, smul_eq_mul] using hcomp

/-- The determinant of a complex-valued chart in Cartesian coordinates is determined by
its radial and angular derivatives. -/
theorem derivative_in_coordinates (F : Plane → ℂ) (p : Plane) {u v : ℂ}
    (hF : DifferentiableAt ℝ F p)
    (hu : HasDerivAt (fun t => F (t,p.2)) u p.1)
    (hv : HasDerivAt (fun θ => F (p.1,θ)) v p.2) :
    ∃ D : Plane →L[ℝ] Plane,
      HasFDerivAt (fun x => Complex.equivRealProdCLM (F x)) D p ∧
      D.toLinearMap.det = (conj u * v).im := by
  let L := fderiv ℝ F p
  have hL : HasFDerivAt F L p := hF.hasFDerivAt
  have hr : HasDerivAt (fun t : ℝ => (t,p.2)) (1,0) p.1 :=
    (hasDerivAt_id _).prodMk (hasDerivAt_const _ _)
  have ha : HasDerivAt (fun θ : ℝ => (p.1,θ)) (0,1) p.2 :=
    (hasDerivAt_const _ _).prodMk (hasDerivAt_id _)
  have hu' : L (1,0) = u := by
    have ht : HasDerivAt (fun t : ℝ => F (t,p.2)) (L (1,0)) p.1 :=
      hL.comp_hasDerivAt p.1 hr
    exact ht.deriv.symm.trans hu.deriv
  have hv' : L (0,1) = v := by
    have ht : HasDerivAt (fun θ : ℝ => F (p.1,θ)) (L (0,1)) p.2 :=
      hL.comp_hasDerivAt p.2 ha
    exact ht.deriv.symm.trans hv.deriv
  let D := Complex.equivRealProdCLM.toContinuousLinearMap.comp L
  have hD : HasFDerivAt (fun x => Complex.equivRealProdCLM (F x)) D p :=
    Complex.equivRealProdCLM.toContinuousLinearMap.hasFDerivAt.comp p hL
  refine ⟨D,hD,?_⟩
  apply det_eq_flux D
  · change Complex.equivRealProdCLM (L (1,0)) = (u.re,u.im)
    rw [hu']
    rfl
  · change Complex.equivRealProdCLM (L (0,1)) = (v.re,v.im)
    rw [hv']
    rfl

end GrunskyArea

/- Radial charts whose angular lift traverses one full turn. -/

open Set Complex Metric

namespace GrunskyStar

noncomputable section

def direction (z : ℂ) : ℂ := z / (‖z‖ : ℂ)

def radial (γ : ℝ → ℂ) (p : ℝ × ℝ) : ℂ := (p.1 : ℂ) * γ p.2

theorem norm_direction {z : ℂ} (hz : z ≠ 0) : ‖direction z‖ = 1 := by
  rw [direction, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z)]
  exact div_self (ne_of_gt (norm_pos_iff.mpr hz))

theorem direction_mul_pos (z : ℂ) {s : ℝ} (hs : 0 < s) :
    direction ((s : ℂ) * z) = direction z := by
  by_cases hz : z = 0
  · simp [hz, direction]
  simp only [direction, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs,
    Complex.ofReal_mul]
  exact mul_div_mul_left _ _ (Complex.ofReal_ne_zero.mpr hs.ne')

theorem norm_circle_factor {z : ℂ} {ρ : ℝ} {t : ℝ}
    (hz : z = (ρ : ℂ) * circleMap 0 1 t) (hρ : 0 < ρ) :
    ‖z‖ = ρ := by
  rw [hz, norm_mul, norm_circleMap_zero, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hρ, abs_one, mul_one]

theorem direction_circle_factor {z : ℂ} {ρ t : ℝ}
    (hz : z = (ρ : ℂ) * circleMap 0 1 t) (hρ : 0 < ρ) :
    direction z = circleMap 0 1 t := by
  rw [direction, norm_circle_factor hz hρ, hz]
  exact mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr hρ.ne')

theorem direction_inj (γ : ℝ → ℂ) (ρ φ : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hρ : ∀ t ∈ Ioc a b, 0 < ρ t)
    (hγ : ∀ t ∈ Ioc a b, γ t = (ρ t : ℂ) * circleMap 0 1 (φ t))
    (hmono : StrictMonoOn φ (Icc a b)) (hend : φ b = φ a + 2*Real.pi) :
    InjOn (direction ∘ γ) (Ioc a b) := by
  intro x hx y hy hxy
  have hx' : φ x ∈ uIoc (φ a) (φ b) := by
    rw [uIoc_of_le (hmono.monotoneOn (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hab)]
    exact hmono.mapsTo_Ioc hx
  have hy' : φ y ∈ uIoc (φ a) (φ b) := by
    rw [uIoc_of_le (hmono.monotoneOn (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hab)]
    exact hmono.mapsTo_Ioc hy
  have hd : |φ a - φ b| ≤ 2*Real.pi := by
    rw [hend, show φ a - (φ a + 2 * Real.pi) = -(2*Real.pi) by ring,
      abs_neg, abs_of_nonneg (by positivity)]
  apply hmono.injOn (Ioc_subset_Icc_self hx) (Ioc_subset_Icc_self hy)
  apply injOn_circleMap_of_abs_sub_le (by norm_num : (1:ℝ) ≠ 0) hd hx' hy'
  simpa only [Function.comp_apply, direction_circle_factor (hγ x hx) (hρ x hx),
    direction_circle_factor (hγ y hy) (hρ y hy)] using hxy

/-- A full-turn lift gives an injective radial chart off the origin. -/
theorem radial_inj (γ : ℝ → ℂ) {a b : ℝ}
    (hnz : ∀ t ∈ Ioc a b, γ t ≠ 0) (hdir : InjOn (direction ∘ γ) (Ioc a b)) :
    InjOn (radial γ) (Ioc 0 1 ×ˢ Ioc a b) := by
  intro x hx y hy heq
  have hangle : x.2 = y.2 := by
    apply hdir hx.2 hy.2
    have he := congrArg direction heq
    simpa only [radial, Function.comp_apply, direction_mul_pos _ hx.1.1,
      direction_mul_pos _ hy.1.1] using he
  refine Prod.ext ?_ hangle
  apply Complex.ofReal_injective
  rw [radial, radial, hangle] at heq
  exact mul_right_cancel₀ (hnz y.2 hy.2) heq

private theorem circleMap_angle_mod (s θ : ℝ) :
    circleMap 0 1 (toIocMod Real.two_pi_pos s θ) = circleMap 0 1 θ := by
  rw [circleMap_eq_circleMap_iff 0 (by norm_num : (1:ℝ) ≠ 0)]
  refine ⟨-toIocDiv Real.two_pi_pos s θ, ?_⟩
  simp only [toIocMod, zsmul_eq_mul, Complex.ofReal_sub, Complex.ofReal_mul,
    Complex.ofReal_intCast, Complex.ofReal_ofNat, Int.cast_neg]
  ring

/-- Every nonzero point lies on a ray of the chart, with the radius fixed by its norm. -/
theorem exists_radial (γ : ℝ → ℂ) (ρ φ : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hρ : ∀ t ∈ Ioc a b, 0 < ρ t)
    (hγ : ∀ t ∈ Ioc a b, γ t = (ρ t : ℂ) * circleMap 0 1 (φ t))
    (hc : ContinuousOn φ (Icc a b)) (hend : φ b = φ a + 2*Real.pi)
    {z : ℂ} (_hz : z ≠ 0) :
    ∃ t ∈ Ioc a b, z = ((‖z‖ / ‖γ t‖ : ℝ) : ℂ) * γ t := by
  let α := toIocMod Real.two_pi_pos (φ a) z.arg
  have hα : α ∈ Ioc (φ a) (φ b) := by
    rw [hend]
    exact toIocMod_mem_Ioc Real.two_pi_pos _ _
  obtain ⟨t, ht, htα⟩ := intermediate_value_Icc hab hc (Ioc_subset_Icc_self hα)
  have ht' : t ∈ Ioc a b := ⟨by
    refine lt_of_le_of_ne ht.1 ?_
    intro he
    exact (ne_of_lt hα.1) (he ▸ htα), ht.2⟩
  have hθ : circleMap 0 1 (φ t) = circleMap 0 1 z.arg := by
    rw [htα]
    exact circleMap_angle_mod _ _
  refine ⟨t, ht', ?_⟩
  rw [norm_circle_factor (hγ t ht') (hρ t ht'), hγ t ht', ← mul_assoc,
    ← Complex.ofReal_mul, div_mul_cancel₀ _ (hρ t ht').ne', hθ, circleMap_zero]
  simpa only [Complex.ofReal_one, one_mul] using (Complex.norm_mul_exp_arg_mul_I z).symm

private theorem angle_to_Ioc {γ : ℝ → ℂ} {a b t : ℝ} (hab : a < b)
    (hends : γ a = γ b) (ht : t ∈ Icc a b) : ∃ u ∈ Ioc a b, γ u = γ t := by
  by_cases h : t = a
  · subst t
    exact ⟨b, ⟨hab,le_rfl⟩,hends.symm⟩
  · exact ⟨t, ⟨lt_of_le_of_ne ht.1 (Ne.symm h),ht.2⟩,rfl⟩

/-- A bounded connected set off the radial boundary stays inside if it contains a point
closer to the origin than every point of that boundary. -/
theorem subset_radial_of_preconnected (γ : ℝ → ℂ) {a b m B : ℝ} (hab : a < b)
    (hcont : Continuous γ) (hends : γ a = γ b)
    (hm : 0 < m) (hlower : ∀ t ∈ Ioc a b, m ≤ ‖γ t‖)
    (hdir : InjOn (direction ∘ γ) (Ioc a b))
    (hrays : ∀ z : ℂ, z ≠ 0 → ∃ t ∈ Ioc a b, z = ((‖z‖ / ‖γ t‖ : ℝ) : ℂ) * γ t)
    (S : Set ℂ) (hconn : IsPreconnected S) (h0 : 0 ∉ S) (hB : ∀ z ∈ S, ‖z‖ ≤ B)
    (hboundary : Disjoint S (γ '' Icc a b))
    (hinside : ∃ z ∈ S, ‖z‖ < m) :
    S ⊆ radial γ '' (Ioc 0 1 ×ˢ Ioc a b) := by
  let M := max 1 (B/m)
  let Inner := radial γ '' (Icc 0 1 ×ˢ Icc a b)
  let Outer := radial γ '' (Icc 1 M ×ˢ Icc a b)
  have hRadCont : Continuous (radial γ) := by
    unfold radial
    fun_prop
  have hI : IsClosed Inner := (isCompact_Icc.prod isCompact_Icc).image hRadCont |>.isClosed
  have hO : IsClosed Outer := (isCompact_Icc.prod isCompact_Icc).image hRadCont |>.isClosed
  have hcover : S ⊆ Inner ∪ Outer := by
    intro z hz
    have hz0 : z ≠ 0 := fun h => h0 (h ▸ hz)
    obtain ⟨t,ht,hzrep⟩ := hrays z hz0
    have hn : 0 < ‖γ t‖ := hm.trans_le (hlower t ht)
    let q := ‖z‖ / ‖γ t‖
    have hq : 0 < q := div_pos (norm_pos_iff.mpr hz0) hn
    rcases le_or_gt q 1 with h | h
    · exact Or.inl ⟨(q,t),⟨⟨hq.le,h⟩,Ioc_subset_Icc_self ht⟩,hzrep.symm⟩
    · have hqB : q ≤ M :=
        (div_le_div_of_nonneg_left (norm_nonneg _) hm (hlower t ht)).trans
          ((div_le_div_of_nonneg_right (hB z hz) hm.le).trans (le_max_right _ _))
      exact Or.inr ⟨(q,t),⟨⟨h.le,hqB⟩,Ioc_subset_Icc_self ht⟩,hzrep.symm⟩
  have huniq {s t x y : ℝ} (hs : 0 < s) (ht : 0 < t) (hx : x ∈ Ioc a b) (hy : y ∈ Ioc a b)
      (h : (s:ℂ) * γ x = (t:ℂ) * γ y) : s = t ∧ x = y := by
    have hxy : x = y := by
      apply hdir hx hy
      simpa only [Function.comp_apply, direction_mul_pos _ hs, direction_mul_pos _ ht]
        using congrArg direction h
    subst y
    have hnz : γ x ≠ 0 := norm_pos_iff.mp (hm.trans_le (hlower x hx))
    exact ⟨Complex.ofReal_injective (mul_right_cancel₀ hnz h), rfl⟩
  have hcross : S ∩ (Inner ∩ Outer) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro z ⟨hz, ⟨⟨s,x⟩,⟨hs,hx⟩,he⟩, ⟨t,y⟩,⟨ht,hy⟩,hf⟩
    obtain ⟨x',hx',hxEq⟩ := angle_to_Ioc hab hends hx
    obtain ⟨y',hy',hyEq⟩ := angle_to_Ioc hab hends hy
    change (s:ℂ)*γ x = z at he
    change (t:ℂ)*γ y = z at hf
    rw [← hxEq] at he
    rw [← hyEq] at hf
    have hspos : 0 < s := by
      refine lt_of_le_of_ne hs.1 ?_
      intro hzero
      have hzEq : (0:ℂ) = z := by simpa [← hzero] using he
      exact h0 (hzEq ▸ hz)
    have heq := (huniq hspos (zero_lt_one.trans_le ht.1) hx' hy' (he.trans hf.symm)).1
    have hs1 : s = 1 := le_antisymm hs.2 (heq ▸ ht.1)
    have hγz : γ x' = z := by simpa [hs1] using he
    exact Set.disjoint_left.mp hboundary hz ⟨x',Ioc_subset_Icc_self hx',hγz⟩
  have hInner : S ⊆ Inner := by
    rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hconn) Inner Outer hI hO hcover hcross with h | h
    · exact h
    · obtain ⟨z,hz,hsmall⟩ := hinside
      obtain ⟨⟨t,u⟩,⟨ht,hu⟩,he⟩ := h hz
      obtain ⟨u',hu',huEq⟩ := angle_to_Ioc hab hends hu
      change (t:ℂ)*γ u = z at he
      rw [← huEq] at he
      have hnorm : ‖z‖ = t * ‖γ u'‖ := by
        rw [← he,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (zero_le_one.trans ht.1)]
      have hle : ‖γ u'‖ ≤ t * ‖γ u'‖ := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right ht.1 (norm_nonneg _)
      exact False.elim ((not_lt_of_ge ((hlower u' hu').trans (hle.trans_eq hnorm.symm))) hsmall)
  intro z hz
  obtain ⟨⟨t,u⟩,⟨ht,hu⟩,he⟩ := hInner hz
  obtain ⟨u',hu',huEq⟩ := angle_to_Ioc hab hends hu
  change (t:ℂ)*γ u = z at he
  rw [← huEq] at he
  have htpos : 0 < t := by
    refine lt_of_le_of_ne ht.1 ?_
    intro hzero
    have hze : (0:ℂ) = z := by simpa [← hzero] using he
    exact h0 (hze ▸ hz)
  exact ⟨(t,u'),⟨⟨htpos,ht.2⟩,hu'⟩,he⟩


/-- The ordinary polar chart is injective on a positive radial interval and a single turn. -/
theorem circular_inj (r R a : ℝ) (hr : 0 ≤ r) :
    InjOn (fun p : ℝ × ℝ => circleMap 0 p.1 p.2)
      (Ioc r R ×ˢ Ioc a (a+2*Real.pi)) := by
  intro x hx y hy he
  have hx0 : 0 < x.1 := hr.trans_lt hx.1.1
  have hy0 : 0 < y.1 := hr.trans_lt hy.1.1
  have hrads : x.1 = y.1 := by
    simpa only [norm_circleMap_zero, abs_of_pos hx0, abs_of_pos hy0] using
      congrArg (fun z : ℂ => ‖z‖) he
  refine Prod.ext hrads ?_
  have hd : |a-(a+2*Real.pi)| ≤ 2*Real.pi := by
    rw [show a-(a+2*Real.pi) = -(2*Real.pi) by ring, abs_neg, abs_of_nonneg (by positivity)]
  change circleMap 0 x.1 x.2 = circleMap 0 y.1 y.2 at he
  rw [hrads] at he
  have ha : a ≤ a+2*Real.pi := by linarith [Real.pi_pos]
  exact injOn_circleMap_of_abs_sub_le hy0.ne' hd (by simpa only [uIoc_of_le ha] using hx.2)
    (by simpa only [uIoc_of_le ha] using hy.2) he

/-- The image of an injective annulus chart fits inside the radial chart of its outer curve. -/
theorem annulus_to_radial (h : ℂ → ℂ) (r R a m B : ℝ) (hr : 0 < r) (hrR : r < R)
    (hcont : ContinuousOn h {z : ℂ | r ≤ ‖z‖ ∧ ‖z‖ ≤ R})
    (hinj : InjOn h {z : ℂ | r ≤ ‖z‖ ∧ ‖z‖ ≤ R})
    (hnz : ∀ z : ℂ, r ≤ ‖z‖ → ‖z‖ ≤ R → h z ≠ 0)
    (hB : ∀ z : ℂ, r ≤ ‖z‖ → ‖z‖ ≤ R → ‖h z‖ ≤ B)
    (hm : 0 < m) (hw : ‖h (circleMap 0 r a)‖ < m)
    (hlo : ∀ t ∈ Ioc a (a+2*Real.pi), m ≤ ‖h (circleMap 0 R t)‖)
    (hdir : InjOn (fun t => direction (h (circleMap 0 R t))) (Ioc a (a+2*Real.pi)))
    (hrays : ∀ z : ℂ, z ≠ 0 → ∃ t ∈ Ioc a (a+2*Real.pi),
      z = ((‖z‖ / ‖h (circleMap 0 R t)‖ : ℝ) : ℂ) * h (circleMap 0 R t)) :
    (fun p : ℝ × ℝ => h (circleMap 0 p.1 p.2)) '' (Ioc r R ×ˢ Ioc a (a+2*Real.pi)) ⊆
      radial (fun t => h (circleMap 0 R t)) '' (Ioc 0 1 ×ˢ Ioc a (a+2*Real.pi)) := by
  let b := a+2*Real.pi
  have hab : a < b := by dsimp [b]; linarith [Real.pi_pos]
  let γ := fun t => h (circleMap 0 R t)
  let H := fun p : ℝ × ℝ => h (circleMap 0 p.1 p.2)
  let D := Ico r R ×ˢ Icc a b
  let S := H '' D
  have hR0 : 0 < R := hr.trans hrR
  have hcoord (s t : ℝ) (hs : r ≤ s) (hR : s ≤ R) :
      circleMap 0 s t ∈ {z : ℂ | r ≤ ‖z‖ ∧ ‖z‖ ≤ R} := by
    simpa only [mem_ofPred_eq, norm_circleMap_zero, abs_of_nonneg (hr.le.trans hs)] using
      And.intro hs hR
  have hC : Continuous γ := by
    apply hcont.comp_continuous
    · unfold circleMap
      fun_prop
    · exact fun t => hcoord R t hrR.le le_rfl
  have hP : γ a = γ b := congrArg h ((periodic_circleMap 0 R a).symm)
  have hDH : ContinuousOn H D := by
    change ContinuousOn (h ∘ fun p : ℝ × ℝ => circleMap 0 p.1 p.2) D
    apply hcont.comp
    · apply Continuous.continuousOn
      unfold circleMap
      fun_prop
    · intro p hp
      exact hcoord p.1 p.2 hp.1.1 hp.1.2.le
  have hS : IsPreconnected S := (isPreconnected_Ico.prod isPreconnected_Icc).image _ hDH
  have hS0 : 0 ∉ S := by
    rintro ⟨p,hp,he⟩
    have hc := hcoord p.1 p.2 hp.1.1 hp.1.2.le
    exact hnz _ hc.1 hc.2 he
  have hSB : ∀ z ∈ S, ‖z‖ ≤ B := by
    rintro z ⟨p,hp,rfl⟩
    have hc := hcoord p.1 p.2 hp.1.1 hp.1.2.le
    exact hB _ hc.1 hc.2
  have hdisj : Disjoint S (γ '' Icc a b) := by
    apply disjoint_left.mpr
    rintro z ⟨p,hp,rfl⟩ ⟨t,_,ht⟩
    have he := hinj (hcoord R t hrR.le le_rfl) (hcoord p.1 p.2 hp.1.1 hp.1.2.le) ht
    have hrads : R = p.1 := by
      simpa only [norm_circleMap_zero, abs_of_pos hR0, abs_of_nonneg (hr.le.trans hp.1.1)]
        using congrArg (fun w : ℂ => ‖w‖) he
    exact (ne_of_lt hp.1.2) hrads.symm
  have hsmall : ∃ z ∈ S, ‖z‖ < m :=
    ⟨H (r,a),⟨(r,a),⟨⟨le_rfl,hrR⟩,⟨le_rfl,hab.le⟩⟩,rfl⟩,hw⟩
  have hsub := subset_radial_of_preconnected γ hab hC hP hm hlo hdir hrays S hS hS0 hSB hdisj hsmall
  rintro z ⟨p,hp,rfl⟩
  by_cases hpR : p.1 = R
  · refine ⟨(1,p.2),⟨⟨zero_lt_one,le_rfl⟩,hp.2⟩,?_⟩
    simp [radial,hpR]
  · exact hsub ⟨p,⟨⟨hp.1.1.le,lt_of_le_of_ne hp.1.2 hpR⟩,Ioc_subset_Icc_self hp.2⟩,rfl⟩

end

end GrunskyStar

/- The angular lift of a holomorphic map normalized at infinity. -/

open Set Filter Complex Metric
open scoped Topology ComplexConjugate

namespace GrunskyOuter

noncomputable section

def probe (R θ : ℝ) : ℂ := circleMap 0 R⁻¹ (-θ)

def outer (u : ℂ → ℂ) (R θ : ℝ) : ℂ := circleMap 0 R θ * u (probe R θ)

def angle (u : ℂ → ℂ) (R θ : ℝ) : ℝ := θ + (Complex.log (u (probe R θ))).im

theorem probe_eq_inv (R θ : ℝ) : probe R θ = (circleMap 0 R θ)⁻¹ :=
  (circleMap_zero_inv R θ).symm

theorem probe_periodic (R : ℝ) : Function.Periodic (probe R) (2*Real.pi) := by
  intro θ
  unfold probe
  rw [neg_add, ← sub_eq_add_neg]
  exact (periodic_circleMap 0 R⁻¹).sub_eq _

theorem angle_period (u : ℂ → ℂ) (R θ : ℝ) :
    angle u R (θ+2*Real.pi) = angle u R θ + 2*Real.pi := by
  unfold angle
  rw [probe_periodic R θ]
  ring

private theorem probe_deriv (R θ : ℝ) :
    HasDerivAt (probe R) (-(probe R θ * I)) θ := by
  unfold probe
  simpa only [Function.comp_def, neg_one_smul]
    using (hasDerivAt_circleMap 0 R⁻¹ (-θ)).scomp θ (hasDerivAt_id θ).neg

private theorem local_data (u : ℂ → ℂ) (hu : AnalyticAt ℂ u 0) (h1 : u 0 = 1) :
    ∃ ε K : ℝ, 0 < ε ∧ 0 < K ∧ ∀ z ∈ ball (0 : ℂ) ε,
      AnalyticAt ℂ u z ∧ ‖u z-1‖ < 1/2 ∧ ‖deriv u z‖ < K := by
  let K := ‖deriv u 0‖+1
  have hK : 0 < K := by positivity
  have hu₁ : ∀ᶠ z in 𝓝 (0 : ℂ), ‖u z-1‖ < 1/2 := by
    have hc : ContinuousAt (fun z => ‖u z-1‖) (0:ℂ) :=
      (hu.continuousAt.sub continuousAt_const).norm
    have ht : ‖u (0:ℂ)-1‖ < (1:ℝ)/2 := by simp [h1]
    exact hc.eventually (gt_mem_nhds ht)
  have hd₁ : ∀ᶠ z in 𝓝 (0 : ℂ), ‖deriv u z‖ < K :=
    hu.deriv.continuousAt.norm.eventually (gt_mem_nhds (by dsimp [K]; linarith))
  obtain ⟨ε,hε,h⟩ := Metric.eventually_nhds_iff_ball.mp
    (hu.eventually_analyticAt.and (hu₁.and hd₁))
  exact ⟨ε,K,hε,hK,h⟩

/-- For all sufficiently large radii, the outer curve has radius greater than R/2
and a strictly positively oriented angular lift making one full turn. -/
theorem large_radius_angle (u : ℂ → ℂ) (hu : AnalyticAt ℂ u 0) (h1 : u 0 = 1) :
    ∀ᶠ R : ℝ in atTop, 0 < R ∧ Differentiable ℝ (angle u R) ∧
      (∀ θ : ℝ, 0 < deriv (angle u R) θ) ∧
      (∀ θ : ℝ, R/2 < ‖outer u R θ‖ ∧
        outer u R θ = (‖outer u R θ‖ : ℂ) * circleMap 0 1 (angle u R θ)) := by
  obtain ⟨ε,K,hε,hK,hlocal⟩ := local_data u hu h1
  filter_upwards [eventually_gt_atTop ε⁻¹,eventually_gt_atTop (2*K)] with R hRε hRK
  have hR : 0 < R := lt_trans (by positivity) hRK
  have hprobe (θ : ℝ) : ‖probe R θ‖ = R⁻¹ := by
    simp only [probe, norm_circleMap_zero, abs_of_pos (inv_pos.mpr hR)]
  have hsmall (θ : ℝ) : probe R θ ∈ ball (0 : ℂ) ε := by
    rw [mem_ball, dist_zero_right,hprobe]
    exact (inv_lt_comm₀ hR hε).mpr hRε
  have hnorm (θ : ℝ) : 1/2 < ‖u (probe R θ)‖ := by
    have hn := norm_sub_norm_le (1:ℂ) (u (probe R θ))
    rw [norm_one,norm_sub_rev] at hn
    linarith [(hlocal _ (hsmall θ)).2.1]
  have hslit (θ : ℝ) : u (probe R θ) ∈ slitPlane := by
    have hn : ‖u (probe R θ)-1‖ < 1 := (hlocal _ (hsmall θ)).2.1.trans (by norm_num)
    simpa only [add_sub_cancel] using
      (show 1 + (u (probe R θ)-1) ∈ slitPlane from mem_slitPlane_of_norm_lt_one hn)
  have hderiv (θ : ℝ) : HasDerivAt (angle u R)
      (1 + ((-(probe R θ*I)) * deriv u (probe R θ) / u (probe R θ)).im) θ := by
    have hU := (hlocal _ (hsmall θ)).1.differentiableAt.hasDerivAt
    have hcomp : HasDerivAt (fun t => u (probe R t))
        ((-(probe R θ*I)) * deriv u (probe R θ)) θ := by
      simpa [Function.comp_def] using
        ((hU.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt θ (probe_deriv R θ))
    exact (hasDerivAt_id θ).add
      (imCLM.hasFDerivAt.comp_hasDerivAt θ (hcomp.clog_real (hslit θ)))
  refine ⟨hR, fun θ => (hderiv θ).differentiableAt, ?_, ?_⟩
  · intro θ
    rw [(hderiv θ).deriv]
    have hn :
        ‖(-(probe R θ*I)) * deriv u (probe R θ) / u (probe R θ)‖ < 1 := by
      rw [norm_div,norm_mul,norm_neg,norm_mul,norm_I,mul_one,hprobe,div_lt_one (by linarith [hnorm θ])]
      have hd := (hlocal _ (hsmall θ)).2.2
      have h₁ : R⁻¹ * ‖deriv u (probe R θ)‖ < R⁻¹ * K :=
        mul_lt_mul_of_pos_left hd (inv_pos.mpr hR)
      have h₂ : R⁻¹ * K < 1/2 := by
        rw [inv_mul_eq_div, div_lt_iff₀ hR]
        linarith
      exact (h₁.trans h₂).trans (hnorm θ)
    have him := Complex.abs_im_le_norm
      ((-(probe R θ*I)) * deriv u (probe R θ) / u (probe R θ))
    have hopen := neg_lt_of_abs_lt (him.trans_lt hn)
    linarith
  · intro θ
    have hN : ‖outer u R θ‖ = R*‖u (probe R θ)‖ := by
      rw [outer,norm_mul,norm_circleMap_zero, abs_of_pos hR]
    refine ⟨by rw [hN]; nlinarith only [mul_pos hR (sub_pos.mpr (hnorm θ))], ?_⟩
    rw [hN,Complex.ofReal_mul,angle,Complex.log_im]
    calc
      outer u R θ = circleMap 0 R θ *
          ((‖u (probe R θ)‖ : ℂ) * exp ((u (probe R θ)).arg * I)) :=
        congrArg (fun z : ℂ => circleMap 0 R θ * z)
          (norm_mul_exp_arg_mul_I (u (probe R θ))).symm
      _ = _ := by
        simp only [circleMap_zero, Complex.ofReal_one, one_mul, Complex.ofReal_add, add_mul, Complex.exp_add]
        ring

private theorem phase_identity (u : ℂ) (r s d : ℝ) (hu : ‖u‖ = 1) :
    (conj ((r:ℂ)*u) * ((s:ℂ)*u + (r:ℂ)*(u*I*(d:ℂ)))).im = r^2*d := by
  have h : conj ((r:ℂ)*u) * ((s:ℂ)*u + (r:ℂ)*(u*I*(d:ℂ))) =
      (conj u*u) * ((r:ℂ)*(s:ℂ) + (r:ℂ)^2*(d:ℂ)*I) := by
    rw [map_mul,Complex.conj_ofReal]
    ring
  rw [h, ← normSq_eq_conj_mul_self, normSq_eq_norm_sq, hu, one_pow, Complex.ofReal_one, one_mul]
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.mul_re, zero_mul, mul_zero, zero_add, add_zero,
    sub_zero, mul_one, ← Complex.ofReal_pow]

/-- The star chart is positively oriented when its angular lift increases. -/
theorem phase_flux (γ : ℝ → ℂ) (φ : ℝ → ℝ) (θ : ℝ)
    (hγ : DifferentiableAt ℝ γ θ) (hφ : DifferentiableAt ℝ φ θ) (hn : γ θ ≠ 0)
    (hshape : ∀ t, γ t = (‖γ t‖ : ℂ) * circleMap 0 1 (φ t)) :
    (conj (γ θ) * deriv γ θ).im = ‖γ θ‖^2 * deriv φ θ := by
  have hr := (hγ.norm ℂ hn).hasDerivAt
  have hrC : HasDerivAt (fun t => (‖γ t‖ : ℂ)) ((deriv (fun t => ‖γ t‖) θ : ℝ) : ℂ) θ := by
    simpa [Function.comp_def] using ofRealCLM.hasFDerivAt.comp_hasDerivAt θ hr
  have hCircle : HasDerivAt (fun t => circleMap 0 1 (φ t))
      (circleMap 0 1 (φ θ) * I * ((deriv φ θ : ℝ) : ℂ)) θ := by
    simpa [Function.comp_def, Complex.real_smul, mul_comm] using
      (hasDerivAt_circleMap 0 1 (φ θ)).scomp θ hφ.hasDerivAt
  have hProd := hrC.mul hCircle
  have hEq : (fun t => (‖γ t‖ : ℂ)*circleMap 0 1 (φ t)) = γ :=
    funext fun t => (hshape t).symm
  change HasDerivAt (fun t => (‖γ t‖ : ℂ)*circleMap 0 1 (φ t)) _ θ at hProd
  rw [hEq] at hProd
  rw [hProd.deriv]
  conv_lhs => arg 1; arg 1; rw [hshape θ]
  apply phase_identity
  simp [norm_circleMap_zero]

end

end GrunskyOuter

/- The boundary integral for an analytic map on a radial family. -/

open Filter
open scoped Topology

open Complex
open scoped ComplexConjugate

namespace GrunskyJacobian

/-- The oriented determinant of two vectors in the complex plane. -/
theorem flux_eq_det (u v : ℂ) :
    (conj u * v).im = Matrix.det !![u.re, v.re; u.im, v.im] := by
  simp [Matrix.det_fin_two, Complex.mul_im, sub_eq_add_neg, mul_comm, add_comm]

/-- The Jacobian scales by the squared modulus of the holomorphic derivative. -/
theorem weighted_flux (g u v : ℂ) (r : ℝ) :
    (conj (g*u) * (g * ((r : ℂ) * v))).im = r * ‖g‖^2 * (conj u * v).im := by
  have h : conj (g*u) * (g * ((r : ℂ) * v)) =
      ((Complex.normSq g * r : ℝ) : ℂ) * (conj u * v) := by
    calc
      _ = (conj g * g) * ((r : ℂ) * (conj u * v)) := by rw [map_mul]; ring
      _ = _ := by rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_mul, mul_assoc]
  rw [h, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
    Complex.normSq_eq_norm_sq, mul_comm (‖g‖^2) r]

end GrunskyJacobian

open Complex MeasureTheory intervalIntegral Set
open scoped Interval ComplexConjugate

namespace GrunskyFlux

def flux (z w : ℂ) : ℝ := (conj z * w).im

theorem flux_deriv {f g : ℝ → ℂ} {f' g' : ℂ} {x : ℝ}
    (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) :
    HasDerivAt (fun t => flux (f t) (g t))
      ((conj f' * g x + conj (f x) * g').im) x := by
  have hconj : HasDerivAt (fun t => conj (f t)) (conj f') x :=
    conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt x hf
  exact imCLM.hasFDerivAt.comp_hasDerivAt x (hconj.mul hg)

private theorem flux_difference (z u v w : ℂ) :
    (conj u * v + conj z * w).im = 2 * flux u v + (conj v * u + conj z * w).im := by
  simp only [flux, add_im, mul_im, conj_im, conj_re]
  ring

/-- The integrated radial boundary flux equals twice the area integrand when the angular
ends agree. The proof is the fundamental theorem of calculus and Fubini on a rectangle. -/
theorem boundary_flux (F U V W : ℝ → ℝ → ℂ) {r R a b : ℝ}
    (hF : Continuous F.uncurry) (hU : Continuous U.uncurry)
    (hV : Continuous V.uncurry) (hW : Continuous W.uncurry)
    (hrF : ∀ t ∈ uIcc r R, ∀ θ ∈ uIcc a b,
      HasDerivAt (fun x => F x θ) (U t θ) t)
    (hrV : ∀ t ∈ uIcc r R, ∀ θ ∈ uIcc a b,
      HasDerivAt (fun x => V x θ) (W t θ) t)
    (haF : ∀ t ∈ uIcc r R, ∀ θ ∈ uIcc a b,
      HasDerivAt (F t) (V t θ) θ)
    (haU : ∀ t ∈ uIcc r R, ∀ θ ∈ uIcc a b,
      HasDerivAt (U t) (W t θ) θ)
    (hper : ∀ t ∈ uIcc r R, flux (F t a) (U t a) = flux (F t b) (U t b)) :
    (∫ θ in a..b, flux (F R θ) (V R θ) - flux (F r θ) (V r θ)) =
      (∫ θ in a..b, ∫ t in r..R, 2 * flux (U t θ) (V t θ)) := by
  let rad (θ t : ℝ) := (conj (U t θ) * V t θ + conj (F t θ) * W t θ).im
  let ang (θ t : ℝ) := (conj (V t θ) * U t θ + conj (F t θ) * W t θ).im
  let jac (θ t : ℝ) := 2 * flux (U t θ) (V t θ)
  have hFc : Continuous fun p : ℝ × ℝ => F p.2 p.1 :=
    hF.comp (continuous_snd.prodMk continuous_fst)
  have hUc : Continuous fun p : ℝ × ℝ => U p.2 p.1 :=
    hU.comp (continuous_snd.prodMk continuous_fst)
  have hVc : Continuous fun p : ℝ × ℝ => V p.2 p.1 :=
    hV.comp (continuous_snd.prodMk continuous_fst)
  have hWc : Continuous fun p : ℝ × ℝ => W p.2 p.1 :=
    hW.comp (continuous_snd.prodMk continuous_fst)
  have hr : Continuous rad.uncurry := by
    dsimp [Function.uncurry, rad]
    fun_prop
  have ha : Continuous ang.uncurry := by
    dsimp [Function.uncurry, ang]
    fun_prop
  have hj : Continuous jac.uncurry := by
    dsimp [Function.uncurry, jac, flux]
    fun_prop
  have hr' (θ : ℝ) : Continuous (rad θ) :=
    hr.comp (continuous_const.prodMk continuous_id)
  have ha' (θ : ℝ) : Continuous (ang θ) :=
    ha.comp (continuous_const.prodMk continuous_id)
  have hj' (θ : ℝ) : Continuous (jac θ) :=
    hj.comp (continuous_const.prodMk continuous_id)
  have ha'' (t : ℝ) : Continuous (fun θ => ang θ t) :=
    ha.comp (continuous_id.prodMk continuous_const)
  have hRad (θ : ℝ) (hθ : θ ∈ uIcc a b) :
      (∫ t in r..R, rad θ t) =
        flux (F R θ) (V R θ) - flux (F r θ) (V r θ) :=
    integral_eq_sub_of_hasDerivAt
      (fun t ht => flux_deriv (hrF t ht θ hθ) (hrV t ht θ hθ))
      ((hr' θ).intervalIntegrable _ _)
  have hAng (t : ℝ) (ht : t ∈ uIcc r R) : (∫ θ in a..b, ang θ t) = 0 := by
    rw [integral_eq_sub_of_hasDerivAt
      (fun θ hθ => flux_deriv (haF t ht θ hθ) (haU t ht θ hθ))
      ((ha'' t).intervalIntegrable _ _)]
    rw [hper t ht, sub_self]
  have hAZ : (∫ θ in a..b, ∫ t in r..R, ang θ t) = 0 := by
    have hK := (isCompact_uIcc (a := a) (b := b)).prod (isCompact_uIcc (a := r) (b := R))
    have hbox := ha.continuousOn.integrableOn_compact (μ := volume) hK
    rw [MeasureTheory.intervalIntegral_intervalIntegral_swap
      (hbox.mono_set (Set.prod_mono uIoc_subset_uIcc uIoc_subset_uIcc))]
    calc
      (∫ t in r..R, ∫ θ in a..b, ang θ t) = ∫ t in r..R, (0:ℝ) :=
        intervalIntegral.integral_congr hAng
      _ = 0 := by simp
  have hcombine (θ : ℝ) : (∫ t in r..R, rad θ t) =
      (∫ t in r..R, jac θ t) + (∫ t in r..R, ang θ t) := by
    rw [← intervalIntegral.integral_add ((hj' θ).intervalIntegrable _ _)
      ((ha' θ).intervalIntegrable _ _)]
    exact intervalIntegral.integral_congr (fun t _ => flux_difference (F t θ) _ _ _)
  calc
    _ = (∫ θ in a..b, ∫ t in r..R, rad θ t) :=
      intervalIntegral.integral_congr (fun θ hθ => (hRad θ hθ).symm)
    _ = (∫ θ in a..b, ((∫ t in r..R, jac θ t) + ∫ t in r..R, ang θ t)) :=
      intervalIntegral.integral_congr (fun θ _ => hcombine θ)
    _ = (∫ θ in a..b, ∫ t in r..R, jac θ t) := by
      rw [intervalIntegral.integral_add
        ((continuous_parametric_intervalIntegral_of_continuous' hj r R).intervalIntegrable _ _)
        ((continuous_parametric_intervalIntegral_of_continuous' ha r R).intervalIntegrable _ _),
        hAZ, add_zero]
    _ = _ := rfl

private theorem deriv_comp_real {K : ℂ → ℂ} {k : ℂ} {q : ℝ → ℂ} {v : ℂ} {t : ℝ}
    (hK : HasDerivAt K k (q t)) (hq : HasDerivAt q v t) :
    HasDerivAt (fun s => K (q s)) (v*k) t := by
  simpa [Function.comp_def] using (hK.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t hq

set_option maxHeartbeats 1200000 in
/-- Flux for an analytic function evaluated on a radial family. Clamping below the
initial radius lets the continuity assumptions live on the exterior of a disk. -/
theorem analytic_radial_flux (K : ℂ → ℂ) (γ : ℝ → ℂ) {r R c a b : ℝ}
    (hr : r ≤ R) (hc : c < r) (hγ : Differentiable ℝ γ)
    (hdγ : Continuous (deriv γ)) (hends : γ a = γ b)
    (hK : ∀ t : ℝ, c ≤ t → ∀ θ : ℝ, AnalyticAt ℂ K ((t:ℂ)*γ θ)) :
    (∫ θ in a..b,
      flux (K ((R:ℂ)*γ θ)) (deriv K ((R:ℂ)*γ θ) * ((R:ℂ)*deriv γ θ)) -
      flux (K ((r:ℂ)*γ θ)) (deriv K ((r:ℂ)*γ θ) * ((r:ℂ)*deriv γ θ))) =
    (∫ θ in a..b, ∫ t in r..R, 2*t*‖deriv K ((t:ℂ)*γ θ)‖^2 * flux (γ θ) (deriv γ θ)) := by
  let x (t θ : ℝ) : ℂ := ((max c t : ℝ) : ℂ)*γ θ
  let F (t θ : ℝ) := K (x t θ)
  let U (t θ : ℝ) := deriv K (x t θ) * γ θ
  let V (t θ : ℝ) := deriv K (x t θ) * (((max c t : ℝ) : ℂ) * deriv γ θ)
  let W (t θ : ℝ) := deriv (deriv K) (x t θ) * (((max c t : ℝ) : ℂ) * γ θ * deriv γ θ) +
    deriv K (x t θ) * deriv γ θ
  have hγC : Continuous γ := hγ.continuous
  have hα (t θ : ℝ) : AnalyticAt ℂ K (x t θ) := hK (max c t) (le_max_left _ _) θ
  have hx : Continuous x.uncurry := by
    unfold Function.uncurry x
    fun_prop
  have hFC : Continuous F.uncurry :=
    continuous_iff_continuousAt.mpr fun p =>
      (hα p.1 p.2).continuousAt.comp (f := x.uncurry) (x := p) hx.continuousAt
  have hDC : Continuous (fun p : ℝ×ℝ => deriv K (x p.1 p.2)) :=
    continuous_iff_continuousAt.mpr fun p =>
      (hα p.1 p.2).deriv.continuousAt.comp (f := x.uncurry) (x := p) hx.continuousAt
  have hDDC : Continuous (fun p : ℝ×ℝ => deriv (deriv K) (x p.1 p.2)) :=
    continuous_iff_continuousAt.mpr fun p =>
      (hα p.1 p.2).deriv.deriv.continuousAt.comp (f := x.uncurry) (x := p) hx.continuousAt
  have hUC : Continuous U.uncurry := by unfold Function.uncurry U; fun_prop
  have hVC : Continuous V.uncurry := by unfold Function.uncurry V; fun_prop
  have hWC : Continuous W.uncurry := by unfold Function.uncurry W; fun_prop
  have hcoef (t : ℝ) (ht : c < t) :
      HasDerivAt (fun s : ℝ => ((max c s : ℝ) : ℂ)) 1 t := by
    have he : max c =ᶠ[𝓝 t] (fun s : ℝ => s) :=
      (lt_mem_nhds ht).mono fun s hs => max_eq_right hs.le
    have h1 := he.hasDerivAt_iff.mpr (hasDerivAt_id t)
    simpa [Function.comp_def] using ofRealCLM.hasFDerivAt.comp_hasDerivAt t h1
  have hxr (t θ : ℝ) (ht : c < t) : HasDerivAt (fun s => x s θ) (γ θ) t := by
    simpa only [x,one_mul] using (hcoef t ht).mul_const (γ θ)
  have hxθ (t θ : ℝ) :
      HasDerivAt (x t) (((max c t : ℝ) : ℂ)*deriv γ θ) θ :=
    (hγ θ).hasDerivAt.const_mul ((max c t : ℝ) : ℂ)
  have htpos (t : ℝ) (ht : t ∈ uIcc r R) : c < t := by
    rw [uIcc_of_le hr] at ht
    exact hc.trans_le ht.1
  have hrF (t : ℝ) (ht : t ∈ uIcc r R) (θ : ℝ) (_ : θ ∈ uIcc a b) :
      HasDerivAt (fun s => F s θ) (U t θ) t := by
    simpa only [F, U, mul_comm] using
      deriv_comp_real (q := fun s => x s θ) (t := t) (hα t θ).differentiableAt.hasDerivAt (hxr t θ (htpos t ht))
  have hrV (t : ℝ) (ht : t ∈ uIcc r R) (θ : ℝ) (_ : θ ∈ uIcc a b) :
      HasDerivAt (fun s => V s θ) (W t θ) t := by
    have hd := deriv_comp_real (q := fun s => x s θ) (t := t) (hα t θ).deriv.differentiableAt.hasDerivAt (hxr t θ (htpos t ht))
    have hv := (hcoef t (htpos t ht)).mul_const (deriv γ θ)
    have heq : γ θ * deriv (deriv K) (x t θ) * (((max c t : ℝ) : ℂ) * deriv γ θ) +
        deriv K (x t θ) * (1 * deriv γ θ) = W t θ := by
      simp only [W, one_mul]
      ring
    rw [← heq]
    exact hd.mul hv
  have haF (t : ℝ) (_ : t ∈ uIcc r R) (θ : ℝ) (_ : θ ∈ uIcc a b) :
      HasDerivAt (F t) (V t θ) θ := by
    simpa only [F,V,mul_comm] using
      deriv_comp_real (hα t θ).differentiableAt.hasDerivAt (hxθ t θ)
  have haU (t : ℝ) (_ : t ∈ uIcc r R) (θ : ℝ) (_ : θ ∈ uIcc a b) :
      HasDerivAt (U t) (W t θ) θ := by
    have hd := deriv_comp_real (hα t θ).deriv.differentiableAt.hasDerivAt (hxθ t θ)
    have heq : (((max c t : ℝ) : ℂ) * deriv γ θ) * deriv (deriv K) (x t θ) * γ θ +
        deriv K (x t θ) * deriv γ θ = W t θ := by
      unfold W
      ring
    rw [← heq]
    exact hd.mul ((hγ θ).hasDerivAt)
  have hper (t : ℝ) (_ : t ∈ uIcc r R) : flux (F t a) (U t a) = flux (F t b) (U t b) := by
    simp [F,U,x,hends]
  have hflux := boundary_flux F U V W hFC hUC hVC hWC hrF hrV haF haU hper
  have hxR : max c R = R := max_eq_right (hc.le.trans hr)
  have hxr' : max c r = r := max_eq_right hc.le
  rw [show (∫ θ in a..b, flux (K ((↑R)*γ θ))
    (deriv K ((↑R)*γ θ) * ((↑R) * deriv γ θ)) -
    flux (K ((↑r)*γ θ)) (deriv K ((↑r)*γ θ) * ((↑r) * deriv γ θ))) =
      (∫ θ in a..b, flux (F R θ) (V R θ) - flux (F r θ) (V r θ)) from by
        simp only [F,V,x,hxR,hxr'], hflux]
  apply intervalIntegral.integral_congr
  intro θ _
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : max c t = t := max_eq_right (htpos t ht).le
  simp only [U,V,x,ht',flux]
  rw [GrunskyJacobian.weighted_flux]
  ring

end GrunskyFlux

open Complex Filter MeasureTheory Set Metric
open scoped Interval ComplexConjugate Topology

namespace GrunskyPositive

open GrunskyArea GrunskyStar

noncomputable section

private def ray (γ : ℝ → ℂ) (p : Plane) : ℂ := (p.1 : ℂ) * γ p.2

private theorem radial_line (γ : ℝ → ℂ) (p : Plane) :
    HasDerivAt (fun t : ℝ => ray γ (t,p.2)) (γ p.2) p.1 := by
  simpa only [ray, one_mul] using
    (show HasDerivAt (fun t : ℝ => (t:ℂ)) 1 p.1 from ofRealCLM.hasDerivAt).mul_const (γ p.2)

private theorem angular_line (γ : ℝ → ℂ) (p : Plane) (hγ : DifferentiableAt ℝ γ p.2) :
    HasDerivAt (fun θ : ℝ => ray γ (p.1,θ)) ((p.1:ℂ)*deriv γ p.2) p.2 :=
  hγ.hasDerivAt.const_mul (p.1:ℂ)

private theorem deriv_comp_real {K : ℂ → ℂ} {k : ℂ} {q : ℝ → ℂ} {v : ℂ} {t : ℝ}
    (hk : HasDerivAt K k (q t)) (hq : HasDerivAt q v t) :
    HasDerivAt (fun s => K (q s)) (k*v) t := by
  simpa [Function.comp_def, mul_comm] using (hk.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t hq

/-- Jacobian of an analytic map written on a radial parameter chart. -/
theorem mapped_radial_deriv (K : ℂ → ℂ) (γ : ℝ → ℂ) (p : Plane)
    (hγ : DifferentiableAt ℝ γ p.2) (hK : DifferentiableAt ℂ K (ray γ p)) :
    ∃ D : Plane →L[ℝ] Plane,
      HasFDerivAt (fun x => Complex.equivRealProdCLM (K (ray γ x))) D p ∧
      D.toLinearMap.det =
        p.1 * ‖deriv K (ray γ p)‖^2 * (conj (γ p.2) * deriv γ p.2).im := by
  have hR : DifferentiableAt ℝ (ray γ) p := by
    unfold ray
    apply DifferentiableAt.mul
    · exact ofRealCLM.differentiableAt.comp p differentiableAt_fst
    · exact hγ.comp p differentiableAt_snd
  have hmap : DifferentiableAt ℝ (fun x => K (ray γ x)) p :=
    hK.real_of_complex.comp p hR
  have h₁ : HasDerivAt (fun t => K (ray γ (t,p.2))) (deriv K (ray γ p) * γ p.2) p.1 :=
    deriv_comp_real (q := fun t => ray γ (t,p.2)) (t := p.1) hK.hasDerivAt (radial_line γ p)
  have h₂ : HasDerivAt (fun θ => K (ray γ (p.1,θ))) (deriv K (ray γ p) *
      ((p.1:ℂ)*deriv γ p.2)) p.2 :=
    deriv_comp_real (q := fun θ => ray γ (p.1,θ)) (t := p.2) hK.hasDerivAt (angular_line γ p hγ)
  obtain ⟨D,hD,hdet⟩ := derivative_in_coordinates _ p hmap h₁ h₂
  exact ⟨D,hD,hdet.trans (GrunskyJacobian.weighted_flux _ _ _ _)⟩

open GrunskyOuter

private def E : ℝ → ℂ := circleMap 0 1

private theorem ray_E (p : Plane) : ray E p = circleMap 0 p.1 p.2 := by
  simp [ray,E,circleMap_zero]

private theorem E_differentiable : Differentiable ℝ E :=
  fun θ => (hasDerivAt_circleMap 0 1 θ).differentiableAt

private theorem E_deriv (θ : ℝ) : deriv E θ = E θ * I :=
  (hasDerivAt_circleMap 0 1 θ).deriv

private theorem E_flux (θ : ℝ) : (conj (E θ) * deriv E θ).im = 1 := by
  rw [E_deriv, ← mul_assoc, ← normSq_eq_conj_mul_self, normSq_eq_norm_sq]
  have hn : ‖E θ‖ = 1 := by simp [E,norm_circleMap_zero]
  simp [hn]

private theorem analytic_ext {h : ℂ → ℂ}
    (hh : DifferentiableOn ℂ h {z : ℂ | 1 < ‖z‖}) {z : ℂ} (hz : 1 < ‖z‖) :
    AnalyticAt ℂ h z :=
  hh.analyticOnNhd (isOpen_lt continuous_const continuous_norm) z hz

private theorem circle_analytic {h : ℂ → ℂ}
    (hh : DifferentiableOn ℂ h {z : ℂ | 1 < ‖z‖}) {R : ℝ} (hR : 1 < R) (θ : ℝ) :
    AnalyticAt ℂ h (circleMap 0 R θ) :=
  analytic_ext hh (by simpa only [norm_circleMap_zero, abs_of_pos (zero_lt_one.trans hR)] using hR)

set_option maxHeartbeats 1600000 in
private theorem weighted_area_le (h P : ℂ → ℂ) (r R : ℝ)
    (hr : 1 < r) (hrR : r < R)
    (hh : DifferentiableOn ℂ h {z : ℂ | 1 < ‖z‖})
    (hP : Differentiable ℂ P) (γ : ℝ → ℂ)
    (hγ : Differentiable ℝ γ) (hflux : ∀ θ, 0 ≤ (conj (γ θ) * deriv γ θ).im)
    (hfi : InjOn (fun p : Plane => h (ray E p)) (Ioc r R ×ˢ Ioc 0 (2*Real.pi)))
    (hgi : InjOn (ray γ) (Ioc 0 1 ×ˢ Ioc 0 (2*Real.pi)))
    (hsub : (fun p : Plane => h (ray E p)) '' (Ioc r R ×ˢ Ioc 0 (2*Real.pi)) ⊆
      ray γ '' (Ioc 0 1 ×ˢ Ioc 0 (2*Real.pi))) :
    (∫ t in r..R, ∫ θ in 0..2*Real.pi, t * ‖deriv (P ∘ h) (ray E (t,θ))‖^2) ≤
      (∫ s in 0..1, ∫ θ in 0..2*Real.pi,
        s * ‖deriv P (ray γ (s,θ))‖^2 * (conj (γ θ) * deriv γ θ).im) := by
  classical
  let e := Complex.equivRealProdCLM
  let f (p : Plane) : Plane := e (h (ray E p))
  let g (p : Plane) : Plane := e (ray γ p)
  let w (p : Plane) : ℝ := ‖deriv P (e.symm p)‖^2
  let b := 2*Real.pi
  have h0b : 0 ≤ b := by dsimp [b]; positivity
  rw [← uIoc_of_le hrR.le, ← uIoc_of_le h0b] at hfi hsub
  rw [← uIoc_of_le zero_le_one, ← uIoc_of_le h0b] at hgi
  rw [← uIoc_of_le zero_le_one] at hsub
  let S := uIoc r R ×ˢ uIoc 0 b
  let T : Set Plane := uIoc 0 1 ×ˢ uIoc 0 b
  have ha (p : Plane) (hp : r ≤ p.1) : AnalyticAt ℂ h (ray E p) := by
    rw [ray_E]
    exact circle_analytic hh (hr.trans_le hp) p.2
  have hf' (p : Plane) (hp : r ≤ p.1) : ∃ D : Plane →L[ℝ] Plane,
      HasFDerivAt f D p ∧ D.toLinearMap.det = p.1 * ‖deriv h (ray E p)‖^2 := by
    obtain ⟨D,hD,hd⟩ := mapped_radial_deriv h E p (E_differentiable _)
      (ha p hp).differentiableAt
    exact ⟨D,hD,by simpa only [E_flux,mul_one] using hd⟩
  have hg' (p : Plane) : ∃ D : Plane →L[ℝ] Plane,
      HasFDerivAt g D p ∧ D.toLinearMap.det = p.1 * (conj (γ p.2) * deriv γ p.2).im := by
    obtain ⟨D,hD,hd⟩ := mapped_radial_deriv id γ p (hγ _) differentiableAt_id
    exact ⟨D,hD,by simpa [deriv_id] using hd⟩
  let df (p : Plane) := if hp : r ≤ p.1 then Classical.choose (hf' p hp) else 0
  let dg (p : Plane) := Classical.choose (hg' p)
  have hdf (p : Plane) (hp : r ≤ p.1) : HasFDerivAt f (df p) p ∧
      (df p).toLinearMap.det = p.1 * ‖deriv h (ray E p)‖^2 := by
    simpa only [df, dif_pos hp] using Classical.choose_spec (hf' p hp)
  have hdg (p : Plane) : HasFDerivAt g (dg p) p ∧
      (dg p).toLinearMap.det = p.1 * (conj (γ p.2) * deriv γ p.2).im :=
    Classical.choose_spec (hg' p)
  have hfI : InjOn f S := fun _ hx _ hy he => hfi hx hy (e.injective he)
  have hgI : InjOn g T := fun _ hx _ hy he => hgi hx hy (e.injective he)
  have hfg : f '' S ⊆ g '' T := by
    rintro z ⟨p,hp,rfl⟩
    obtain ⟨q,hq,he⟩ := hsub (show h (ray E p) ∈ _ from ⟨p,hp,rfl⟩)
    exact ⟨q,hq,congrArg e he⟩
  have hγC := hγ.continuous
  have hgC : Continuous g := by
    unfold g ray e
    fun_prop
  have hPC : Continuous (deriv P) := continuousOn_univ.mp (Complex.analyticOnNhd_univ_iff_differentiable.mpr hP).deriv.continuousOn
  have hw : Continuous w := by
    unfold w
    fun_prop
  have harea := chart_integral_le f g df dg w r R 0 b 0 1 0 b hrR.le h0b zero_le_one h0b
    hfI hgI (fun p hp => (hdf p (((uIoc_of_le hrR.le) ▸ hp.1).1.le)).1) (fun p _ => (hdg p).1) hfg hgC.continuousOn hw
    (fun p => sq_nonneg _)
  have hfEq : (∫ t in r..R, ∫ θ in 0..b, |(df (t,θ)).toLinearMap.det| * w (f (t,θ))) =
      (∫ t in r..R, ∫ θ in 0..b, t * ‖deriv (P ∘ h) (ray E (t,θ))‖^2) := by
    apply intervalIntegral.integral_congr
    intro t ht
    apply intervalIntegral.integral_congr
    intro θ _
    have hrt : r ≤ t := ((uIcc_of_le hrR.le) ▸ ht).1
    have ht0 : 0 ≤ t := (zero_lt_one.trans hr).le.trans hrt
    dsimp only
    rw [(hdf (t,θ) hrt).2, abs_of_nonneg (mul_nonneg ht0 (sq_nonneg _))]
    rw [deriv_comp _ (hP _) (ha (t,θ) hrt).differentiableAt, norm_mul, mul_pow]
    simp only [w,f,e,ContinuousLinearEquiv.symm_apply_apply]
    ring
  have hgEq : (∫ s in 0..1, ∫ θ in 0..b, |(dg (s,θ)).toLinearMap.det| * w (g (s,θ))) =
      (∫ s in 0..1, ∫ θ in 0..b, s * ‖deriv P (ray γ (s,θ))‖^2 *
        (conj (γ θ) * deriv γ θ).im) := by
    apply intervalIntegral.integral_congr
    intro s hs
    apply intervalIntegral.integral_congr
    intro θ _
    have hs0 : 0 ≤ s := ((uIcc_of_le (show (0:ℝ) ≤ 1 from zero_le_one)) ▸ hs).1
    dsimp only
    rw [(hdg (s,θ)).2, abs_of_nonneg (mul_nonneg hs0 (hflux θ))]
    simp only [w,g,e,ContinuousLinearEquiv.symm_apply_apply]
    ring
  rw [hfEq,hgEq] at harea
  exact harea


private theorem swap_integrals {f : ℝ → ℝ → ℝ} {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d)
    (hf : ContinuousOn f.uncurry (Icc a b ×ˢ Icc c d)) :
    (∫ x in a..b, ∫ y in c..d, f x y) = (∫ y in c..d, ∫ x in a..b, f x y) := by
  have h : IntegrableOn f.uncurry (Ioc a b ×ˢ Ioc c d) ((volume : Measure ℝ).prod volume) := by
    apply IntegrableOn.mono_set ?_ (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
    exact hf.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  simp_rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd]
  apply integral_integral_swap
  rw [Measure.prod_restrict]
  exact h

private def boundary (K : ℂ → ℂ) (γ : ℝ → ℂ) (r θ : ℝ) :=
  (conj (K (ray γ (r,θ))) * deriv (fun t => K (ray γ (r,t))) θ).im

private theorem boundary_eq (K : ℂ → ℂ) (γ : ℝ → ℂ) (r θ : ℝ)
    (hγ : DifferentiableAt ℝ γ θ) (hK : DifferentiableAt ℂ K (ray γ (r,θ))) :
    boundary K γ r θ = GrunskyFlux.flux (K ((r:ℂ)*γ θ))
      (deriv K ((r:ℂ)*γ θ) * ((r:ℂ)*deriv γ θ)) := by
  have hd := deriv_comp_real (q := fun t => ray γ (r,t)) (t := θ)
    hK.hasDerivAt (angular_line γ (r,θ) hγ)
  unfold boundary GrunskyFlux.flux
  rw [hd.deriv]
  rfl

set_option maxHeartbeats 2000000 in
/-- The weighted boundary flux of a normalized injective exterior map is nonnegative. -/
theorem exterior_positive (h b P : ℂ → ℂ)
    (hh : DifferentiableOn ℂ h {z : ℂ | 1 < ‖z‖})
    (hi : InjOn h {z : ℂ | 1 < ‖z‖})
    (hn : ∀ w : ℂ, 1 < ‖w‖ → h w ≠ 0)
    (hb : AnalyticAt ℂ b 0) (hb0 : b 0 = 1)
    (he : ∀ w : ℂ, 1 < ‖w‖ → h w = w*b w⁻¹)
    (hP : Differentiable ℂ P) (r : ℝ) (hr : 1 < r) :
    0 ≤ ∫ θ in 0..2*Real.pi,
      (conj (P (h (circleMap 0 r θ))) * deriv (fun t => P (h (circleMap 0 r t))) θ).im := by
  let L := 2*Real.pi
  have hL : 0 ≤ L := by dsimp [L]; positivity
  let K := P ∘ h
  have hPE : ∀ z : ℂ, AnalyticAt ℂ P z := fun z => (Complex.analyticOnNhd_univ_iff_differentiable.mpr hP) z (mem_univ _)
  have hE (t θ : ℝ) (ht : 1 < t) : 1 < ‖circleMap 0 t θ‖ := by
    rwa [norm_circleMap_zero,abs_of_pos (zero_lt_one.trans ht)]
  have hbig : ∀ᶠ R : ℝ in atTop, r < R ∧ 2*‖h (circleMap 0 r 0)‖ < R :=
    (eventually_gt_atTop r).and (eventually_gt_atTop _)
  obtain ⟨R,⟨hrR,hsmall⟩,hR0,hφ,hφpos,hshape⟩ :=
    (hbig.and (large_radius_angle b hb hb0)).exists
  have hR : 1 < R := hr.trans hrR
  let γ := fun t => h (circleMap 0 R t)
  let φ := angle b R
  have hγeq (θ : ℝ) : γ θ = outer b R θ := by
    unfold γ outer
    rw [he _ (hE R θ hR),probe_eq_inv]
  have hγlo (θ : ℝ) : R/2 < ‖γ θ‖ := by rw [hγeq]; exact (hshape θ).1
  have hγnz (θ : ℝ) : γ θ ≠ 0 := hn _ (hE R θ hR)
  have hγshape (θ : ℝ) : γ θ = (‖γ θ‖:ℂ)*circleMap 0 1 (φ θ) := by
    rw [hγeq]
    exact (hshape θ).2
  have hφends : φ L = φ 0 + 2*Real.pi := by
    simpa only [L,zero_add] using angle_period b R 0
  have hγd (θ : ℝ) : HasDerivAt γ
      (deriv h (circleMap 0 R θ) * (circleMap 0 R θ * I)) θ :=
    deriv_comp_real (q := circleMap 0 R) (t := θ)
      (circle_analytic hh hR θ).differentiableAt.hasDerivAt (hasDerivAt_circleMap 0 R θ)
  have hγD : Differentiable ℝ γ := fun θ => (hγd θ).differentiableAt
  have hγflux (θ : ℝ) : 0 ≤ (conj (γ θ) * deriv γ θ).im := by
    rw [phase_flux γ φ θ (hγD θ) (hφ θ) (hγnz θ) hγshape]
    exact mul_nonneg (sq_nonneg _) (hφpos θ).le
  have hγdc : Continuous (deriv γ) := by
    rw [show deriv γ = _ from funext fun θ => (hγd θ).deriv]
    apply Continuous.mul
    · apply continuous_iff_continuousAt.mpr
      intro θ
      exact (circle_analytic hh hR θ).deriv.continuousAt.comp
        (f := circleMap 0 R) (x := θ) (hasDerivAt_circleMap 0 R θ).continuousAt
    · exact ((differentiable_circleMap 0 R).continuous).mul continuous_const
  have hdir : InjOn (direction ∘ γ) (Ioc 0 L) :=
    direction_inj γ (fun θ => ‖γ θ‖) φ hL
      (fun θ _ => norm_pos_iff.mpr (hγnz θ)) (fun θ _ => hγshape θ)
      ((strictMono_of_deriv_pos hφpos).strictMonoOn _) hφends
  have hrays (z : ℂ) (hz : z ≠ 0) : ∃ θ ∈ Ioc 0 L,
      z = ((‖z‖ / ‖γ θ‖ : ℝ) : ℂ) * γ θ :=
    exists_radial γ (fun θ => ‖γ θ‖) φ hL
      (fun θ _ => norm_pos_iff.mpr (hγnz θ)) (fun θ _ => hγshape θ)
      hφ.continuous.continuousOn hφends hz
  let A := {z : ℂ | r ≤ ‖z‖ ∧ ‖z‖ ≤ R}
  have hA : A ⊆ {z : ℂ | 1 < ‖z‖} := fun z hz => hr.trans_le hz.1
  have hAh := hh.continuousOn.mono hA
  have hAc : IsCompact A := by
    have heq : A = closedBall (0:ℂ) R \ ball 0 r := by
      ext z
      simp [A,Metric.mem_ball,Metric.mem_closedBall,dist_zero_right,not_lt,and_comm]
    rw [heq]
    exact (isCompact_closedBall _ _).diff isOpen_ball
  have hAr : circleMap 0 r 0 ∈ A := by
    simp [A,norm_circleMap_zero,abs_of_pos (zero_lt_one.trans hr),hrR.le]
  obtain ⟨z,hz,hmax⟩ := hAc.exists_isMaxOn ⟨_,hAr⟩ hAh.norm
  have hsub := annulus_to_radial h r R 0 (R/2) ‖h z‖ (zero_lt_one.trans hr) hrR hAh
    (hi.mono hA) (fun w hw _ => hn w (hr.trans_le hw))
    (fun w hw hw' => (isMaxOn_iff.mp hmax) w (show w ∈ A from ⟨hw,hw'⟩)) (by positivity)
    (by linarith) (fun θ _ => (hγlo θ).le)
    (by
      rw [zero_add]
      change InjOn (direction ∘ γ) (Ioc 0 L)
      exact hdir)
    (by simpa only [L,zero_add] using hrays)
  have hsub' : (fun p : Plane => h (ray E p)) '' (Ioc r R ×ˢ Ioc 0 L) ⊆
      ray γ '' (Ioc 0 1 ×ˢ Ioc 0 L) := by
    simp only [ray_E]
    rw [zero_add] at hsub
    exact hsub
  have hfi : InjOn (fun p : Plane => h (ray E p)) (Ioc r R ×ˢ Ioc 0 L) := by
    simp only [ray_E]
    have hm : MapsTo (fun p : Plane => circleMap 0 p.1 p.2) (Ioc r R ×ˢ Ioc 0 L)
        {z : ℂ | 1 < ‖z‖} :=
      fun p hp => hE p.1 p.2 (hr.trans hp.1.1)
    exact hi.comp (by simpa only [L,zero_add] using circular_inj r R 0 (zero_lt_one.trans hr).le) hm
  have hgi : InjOn (ray γ) (Ioc 0 1 ×ˢ Ioc 0 L) :=
    radial_inj γ (fun θ _ => hγnz θ) hdir
  have harea := weighted_area_le h P r R hr hrR hh hP γ hγD hγflux hfi hgi hsub'
  have hθE : E 0 = E L := by
    simpa only [E,L,zero_add] using (periodic_circleMap 0 1 0).symm
  have hθγ : γ 0 = γ L := by
    simpa only [γ,L,zero_add] using congrArg h (periodic_circleMap 0 R 0).symm
  let c := (1+r)/2
  have hc1 : 1 < c := by dsimp [c]; linarith
  have hcr : c < r := by dsimp [c]; linarith
  have hKan (t : ℝ) (ht : c ≤ t) (θ : ℝ) : AnalyticAt ℂ K (ray E (t,θ)) := by
    rw [ray_E]
    exact (hPE _).comp (circle_analytic hh (hc1.trans_le ht) θ)
  have hdEc : Continuous (deriv E) := by
    rw [show deriv E = _ from funext E_deriv]
    exact E_differentiable.continuous.mul continuous_const
  have hfluxA := GrunskyFlux.analytic_radial_flux K E (r := r) (R := R) (c := c)
    (a := 0) (b := L) hrR.le hcr E_differentiable hdEc hθE hKan
  have hfluxB := GrunskyFlux.analytic_radial_flux P γ (r := 0) (R := 1) (c := -1)
    (a := 0) (b := L) zero_le_one (by norm_num) hγD hγdc hθγ (fun _ _ _ => hPE _)
  have hEqA (t : ℝ) (ht : c ≤ t) (θ : ℝ) := boundary_eq K E t θ (E_differentiable θ) (hKan t ht θ).differentiableAt
  have hEqB (t θ : ℝ) := boundary_eq P γ t θ (hγD θ) (hP _)
  simp_rw [← hEqA R (hcr.le.trans hrR.le), ← hEqA r hcr.le,
    GrunskyFlux.flux, E_flux, mul_one] at hfluxA
  simp_rw [← hEqB 1, ← hEqB 0, GrunskyFlux.flux] at hfluxB
  have hzero (θ : ℝ) : boundary P γ 0 θ = 0 := by
    simp [hEqB,GrunskyFlux.flux]
  have houter (θ : ℝ) : boundary P γ 1 θ = boundary K E R θ := by
    rw [boundary,boundary]
    have hfun : (fun t => P (ray γ (1,t))) = fun t => K (ray E (R,t)) := by
      funext t
      rw [ray_E]
      simp [ray,γ,K]
    rw [hfun]
    exact congrArg (fun z => (conj z * deriv (fun t => K (ray E (R,t))) θ).im) (congrFun hfun θ)
  simp_rw [hzero,sub_zero,houter] at hfluxB
  have C1 : ContinuousOn (fun p : Plane => p.1 * ‖deriv K (ray E p)‖^2)
      (Icc r R ×ˢ Icc 0 L) := by
    have hRay : Continuous (ray E) := by
      unfold ray
      have := E_differentiable.continuous
      fun_prop
    have hD : ContinuousOn (fun p : Plane => deriv K (ray E p)) (Icc r R ×ˢ Icc 0 L) :=
      fun p hp => ((hKan p.1 (hcr.le.trans hp.1.1) p.2).deriv.continuousAt.comp
        (f := ray E) (x := p) hRay.continuousAt).continuousWithinAt
    exact continuous_fst.continuousOn.mul (hD.norm.pow 2)
  have C2 : ContinuousOn
      (fun p : Plane => p.1 * ‖deriv P (ray γ p)‖^2 * (conj (γ p.2) * deriv γ p.2).im)
      (Icc 0 1 ×ˢ Icc 0 L) := by
    apply Continuous.continuousOn
    unfold ray
    have hγC := hγD.continuous
    have hPC : Continuous (deriv P) := continuousOn_univ.mp (Complex.analyticOnNhd_univ_iff_differentiable.mpr hP).deriv.continuousOn
    fun_prop
  have hswapA := swap_integrals (f := fun t θ => t*‖deriv K (ray E (t,θ))‖^2) hrR.le hL C1
  have hswapB := swap_integrals (f := fun s θ => s*‖deriv P (ray γ (s,θ))‖^2 *
    (conj (γ θ) * deriv γ θ).im) zero_le_one hL C2
  have hBdiff (t : ℝ) (ht : c ≤ t) :
      Continuous fun θ => boundary K E t θ := by
    simp_rw [hEqA t ht,GrunskyFlux.flux]
    have hC : Continuous fun θ => (t:ℂ)*E θ :=
      continuous_const.mul E_differentiable.continuous
    have hKC : Continuous fun θ => K ((t:ℂ)*E θ) :=
      continuous_iff_continuousAt.mpr fun θ =>
        (hKan t ht θ).continuousAt.comp
          (f := fun a => (t:ℂ)*E a) (x := θ) hC.continuousAt
    have hKDC : Continuous fun θ => deriv K ((t:ℂ)*E θ) :=
      continuous_iff_continuousAt.mpr fun θ =>
        (hKan t ht θ).deriv.continuousAt.comp
          (f := fun a => (t:ℂ)*E a) (x := θ) hC.continuousAt
    exact Complex.continuous_im.comp ((Complex.continuous_conj.comp hKC).mul
      (hKDC.mul (continuous_const.mul hdEc)))
  rw [intervalIntegral.integral_sub
    ((hBdiff R (hcr.le.trans hrR.le)).intervalIntegrable _ _)
    ((hBdiff r hcr.le).intervalIntegrable _ _)] at hfluxA
  change _ ≤ _ at harea
  rw [hswapA,hswapB] at harea
  have h2A : (∫ θ in 0..L, ∫ t in r..R, 2*t*‖deriv K ((t:ℂ)*E θ)‖^2) =
      2 * (∫ θ in 0..L, ∫ t in r..R, t*‖deriv K (ray E (t,θ))‖^2) := by
    simp_rw [ray,mul_assoc,intervalIntegral.integral_const_mul]
  have h2B : (∫ θ in 0..L, ∫ t in 0..1, 2*t*‖deriv P ((t:ℂ)*γ θ)‖^2 *
      (conj (γ θ) * deriv γ θ).im) =
      2 * (∫ θ in 0..L, ∫ t in 0..1, t*‖deriv P (ray γ (t,θ))‖^2 *
        (conj (γ θ) * deriv γ θ).im) := by
    simp_rw [ray,mul_assoc,intervalIntegral.integral_const_mul]
  rw [h2A] at hfluxA
  rw [h2B] at hfluxB
  have hresult : 0 ≤ ∫ θ in 0..L, boundary K E r θ := by linarith
  simpa only [boundary,ray_E,K,L,Function.comp_apply] using hresult

end

end GrunskyPositive

end

section

/- Analytic and finite-mode steps of the univalent Bloch lower bound. Based on Wikström, arXiv:2610.34580, §§2–4. -/

/- Compression of the boundary inequality to the first two odd Laurent modes. -/

/- The holomorphic odd square root of a normalized univalent map. -/

open Metric Set Filter FormalMultilinearSeries
open scoped Topology NNReal ENNReal

namespace UnivalentBlochOddRoot

private theorem full_series {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball 0 1)) :
    HasFPowerSeriesOnBall f (cauchyPowerSeries f 0 (1/2)) 0 1 := by
  let r₀ : ℝ≥0 := 1/2
  let p := cauchyPowerSeries f 0 r₀
  have h (r : ℝ≥0) (hr₀ : 0 < r) (hr₁ : (r : ℝ) < 1) :
      HasFPowerSeriesOnBall f (cauchyPowerSeries f 0 r) 0 r :=
    (hf.mono (closedBall_subset_ball hr₁)).hasFPowerSeriesOnBall hr₀
  have h₀ := h r₀ (by norm_num [r₀]) (by norm_num [r₀])
  have haux (r : ℝ≥0) (hr₀ : 0 < r) (hr₁ : r < 1) : HasFPowerSeriesOnBall f p 0 r :=
    h₀.exchange_radius (h r hr₀ (by exact_mod_cast hr₁))
  change HasFPowerSeriesOnBall f p 0 1
  refine ⟨ENNReal.le_of_forall_pos_nnreal_lt (fun r hr₀ hr₁ =>
    (haux r hr₀ (by exact_mod_cast hr₁)).r_le),zero_lt_one,?_⟩
  intro z hz
  have hz' : ‖z‖₊ < 1 := by
    rw [mem_eball_zero_iff, enorm_eq_nnnorm, ← ENNReal.coe_one, ENNReal.coe_lt_coe] at hz
    exact hz
  obtain ⟨r,hrz,hr₁⟩ := exists_between hz'
  have hr₀ : 0 < r := zero_le.trans_lt hrz
  exact (haux r hr₀ hr₁).hasSum (mem_eball_zero_iff.mpr (by exact_mod_cast hrz))

private theorem norm_coeff (p : FormalMultilinearSeries ℂ ℂ ℂ) (k : ℕ) :
    ‖p.coeff k‖ = ‖p k‖ := by
  rw [← ContinuousMultilinearMap.mkPiRing_apply_one_eq_self (p k),
    ContinuousMultilinearMap.norm_mkPiRing]
  rfl

/-- A holomorphic map on the unit disk has a primitive vanishing at zero. -/
theorem exists_primitive {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball 0 1)) :
    ∃ G : ℂ → ℂ, G 0 = 0 ∧ ∀ z ∈ ball (0 : ℂ) 1, HasDerivAt G (f z) z := by
  let p := cauchyPowerSeries f 0 (1/2)
  have hp : HasFPowerSeriesOnBall f p 0 1 := full_series hf
  let d : ℕ → ℂ := fun
    | 0 => 0
    | n+1 => p.coeff n / (n+1 : ℕ)
  let q := FormalMultilinearSeries.ofScalars ℂ d
  have hqRad : 1 ≤ q.radius := by
    apply ENNReal.le_of_forall_pos_nnreal_lt
    intro r hr0 hr1
    have hs := p.summable_norm_mul_pow (hr1.trans_le hp.r_le)
    apply q.le_radius_of_summable
    apply (summable_nat_add_iff 1).mp
    have hs' := hs.mul_left (r : ℝ)
    apply Summable.of_nonneg_of_le (fun _ => by positivity) ?_ hs'
    intro n
    rw [show ‖q (n+1)‖ = ‖p.coeff n / (n+1 : ℕ)‖ by
      rw [FormalMultilinearSeries.ofScalars_norm],
      norm_div, Complex.norm_natCast, norm_coeff, pow_succ]
    have h1 : (1 : ℝ) ≤ (↑(n+1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
    exact (mul_le_mul_of_nonneg_right (div_le_self (norm_nonneg _) h1) (by positivity)).trans_eq
      (by ring)
  have hq : HasFPowerSeriesOnBall q.sum q 0 q.radius :=
    q.hasFPowerSeriesOnBall (zero_lt_one.trans_le hqRad)
  have hq0 : q.sum 0 = 0 := by
    change FormalMultilinearSeries.ofScalarsSum d (0 : ℂ) = 0
    rw [FormalMultilinearSeries.ofScalarsSum_zero]
    simp [d]
  refine ⟨q.sum, hq0, ?_⟩
  intro z hz
  have hzz : z ∈ eball (0 : ℂ) 1 := by
    rw [mem_eball_zero_iff, enorm_eq_nnnorm, ← ENNReal.coe_one, ENNReal.coe_lt_coe]
    exact NNReal.coe_lt_coe.mp (by simpa only [coe_nnnorm, NNReal.coe_one] using mem_ball_zero_iff.mp hz)
  have hzq : z ∈ eball (0 : ℂ) q.radius := eball_subset_eball hqRad hzz
  have hd := (hq.fderiv.hasSum hzq)
  rw [zero_add] at hd
  let E : (ℂ →L[ℂ] ℂ) →L[ℂ] ℂ := ContinuousLinearMap.apply ℂ ℂ 1
  let P := E.compFormalMultilinearSeries q.derivSeries
  have hEq (k : ℕ) : P.coeff k = p.coeff k := by
    change E (q.derivSeries.coeff k) = p.coeff k
    change q.derivSeries.coeff k 1 = _
    rw [FormalMultilinearSeries.derivSeries_coeff_one, FormalMultilinearSeries.coeff_ofScalars]
    have H : ((k+1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
    change (k+1 : ℕ) • (p.coeff k / (k+1 : ℕ)) = p.coeff k
    rw [nsmul_eq_mul, mul_div_cancel₀ _ H]
  have hEq' : P = p := by
    ext k
    exact hEq k
  have hd' := E.hasSum hd
  change HasSum (fun k => P k (fun _ => z)) (deriv q.sum z) at hd'
  rw [hEq'] at hd'
  have hder : deriv q.sum z = f z := hd'.unique (by simpa only [zero_add] using hp.hasSum hzz)
  have haz : AnalyticAt ℂ q.sum z := hq.analyticAt_of_mem (by simpa only [zero_add] using hzq)
  rw [← hder]
  exact haz.differentiableAt.hasDerivAt

private theorem normalized_sqrt {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball 0 1))
    (h0 : f 0 = 1) (hne : ∀ z ∈ ball (0 : ℂ) 1, f z ≠ 0) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball 0 1) ∧ g 0 = 1 ∧
      ∀ z ∈ ball (0 : ℂ) 1, (g z)^2 = f z := by
  let d := fun z => deriv f z / f z
  have hd : DifferentiableOn ℂ d (ball 0 1) := (hf.deriv isOpen_ball).div hf hne
  obtain ⟨G, hG0, hG⟩ := exists_primitive hd
  let q := fun z => f z * Complex.exp (-G z)
  have hq (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) : HasDerivAt q 0 z := by
    have hF := (hf.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
    have hG' := (Complex.hasDerivAt_exp (-G z)).comp z (hG z hz).neg
    have he : deriv f z * Complex.exp (-G z) +
        f z * (Complex.exp (-G z) * -(deriv f z / f z)) = 0 := by
      field_simp [hne z hz]
      ring
    have hm := hF.mul hG'
    change HasDerivAt q (deriv f z * Complex.exp (-G z) +
        f z * (Complex.exp (-G z) * -(deriv f z / f z))) z at hm
    exact he ▸ hm
  have hqeq (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) : q z = 1 := by
    have h := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun w hw => (hq w hw).differentiableAt) (C := 0)
      (fun w hw => by rw [(hq w hw).deriv, norm_zero]) (convex_ball (0 : ℂ) 1)
      (mem_ball_self zero_lt_one) hz
    have he : q z = q 0 := norm_sub_eq_zero_iff.mp (le_antisymm (by simpa using h) (norm_nonneg _))
    simpa [q, hG0, h0] using he
  let g := fun z => Complex.exp (G z / 2)
  have hgD : DifferentiableOn ℂ g (ball 0 1) := by
    intro z hz
    have hzG := (hG z hz).div_const 2
    exact ((Complex.hasDerivAt_exp (G z / 2)).comp z hzG).differentiableAt.differentiableWithinAt
  refine ⟨g, hgD, by simp [g, hG0],?_⟩
  intro z hz
  have he := congrArg (fun w => w*Complex.exp (G z)) (hqeq z hz)
  dsimp only [q] at he
  rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one, one_mul] at he
  dsimp [g]
  rw [pow_two, ← Complex.exp_add, show G z / 2 + G z / 2 = G z by ring, ← he]

theorem exists_odd_sqrt {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball 0 1))
    (hI : InjOn f (ball 0 1)) (h0 : f 0 = 0) (h1 : deriv f 0 = 1) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball 0 1) ∧ InjOn g (ball 0 1) ∧
      g 0 = 0 ∧ deriv g 0 = 1 ∧ (∀ z, g (-z) = -g z) ∧
      ∀ z ∈ ball (0 : ℂ) 1, (g z)^2 = f (z^2) := by
  let D := dslope f 0
  have hmem : (0 : ℂ) ∈ ball 0 1 := mem_ball_self zero_lt_one
  have hd : DifferentiableOn ℂ D (ball 0 1) :=
    (Complex.differentiableOn_dslope (ball_mem_nhds 0 zero_lt_one)).mpr hf
  have hd0 : D 0 = 1 := by simpa [D] using h1
  have hd_eq (z : ℂ) (hz : z ≠ 0) : D z = f z / z := by
    simp [D, dslope_of_ne f hz, slope_def_field, h0]
  have hD_ne (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) : D z ≠ 0 := by
    rcases eq_or_ne z 0 with rfl | hn
    · rw [hd0]
      norm_num
    · have hFz : f z ≠ 0 := fun he => hn (hI hz hmem (he.trans h0.symm))
      rw [hd_eq z hn]
      exact div_ne_zero hFz hn
  obtain ⟨s, hs, hs0, hs_sq⟩ := normalized_sqrt hd hd0 hD_ne
  let g := fun z : ℂ => z*s (z^2)
  have hsqmem (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) : z^2 ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_pow]
    have h := mem_ball_zero_iff.mp hz
    nlinarith [norm_nonneg z, mul_pos (sub_pos.mpr h) (show 0 < 1 + ‖z‖ by positivity)]
  have hG (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) : DifferentiableAt ℂ g z := by
    have hS := hs.differentiableAt (isOpen_ball.mem_nhds (hsqmem z hz))
    exact (differentiableAt_id.mul (hS.comp z (differentiableAt_id.pow 2)))
  have hG0 : g 0 = 0 := by simp [g]
  have hG1 : deriv g 0 = 1 := by
    have hS := (hs.differentiableAt (ball_mem_nhds 0 zero_lt_one)).hasDerivAt
    have hsq : HasDerivAt (fun z : ℂ => z^2) 0 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).fun_pow 2
    have hS' : HasDerivAt s (deriv s 0) ((0 : ℂ)^2) := by simpa using hS
    have hP := (hasDerivAt_id (0 : ℂ)).mul (hS'.comp 0 hsq)
    change HasDerivAt g (1 * s ((0 : ℂ)^2) + 0 * (deriv s 0 * 0)) 0 at hP
    simpa [hs0] using hP.deriv
  have hOdd (z : ℂ) : g (-z) = -g z := by simp [g]
  have hSq (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) : (g z)^2 = f (z^2) := by
    rcases eq_or_ne z 0 with rfl | hn
    · simp [hG0, h0]
    dsimp only [g]
    rw [mul_pow, hs_sq (z^2) (hsqmem z hz), hd_eq _ (pow_ne_zero _ hn), mul_div_cancel₀ _ (pow_ne_zero _ hn)]
  refine ⟨g, fun z hz => (hG z hz).differentiableWithinAt,?_,hG0,hG1,hOdd,hSq⟩
  intro x hx y hy he
  have hxy : x^2 = y^2 := hI (hsqmem x hx) (hsqmem y hy)
    (by rw [← hSq x hx, ← hSq y hy, he])
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hxy with hn | hn
  · exact hn
  · have hneg : -g y = g y := by simpa only [hn, hOdd] using he
    have hyz : g y = 0 := by linear_combination -(1/2 : ℂ)*hneg
    have hxg : g x = 0 := he.trans hyz
    have hyF : f (x^2) = 0 := by rw [← hSq x hx, hxg, zero_pow (by decide)]
    have hx0 : x^2 = 0 := hI (hsqmem x hx) hmem (hyF.trans h0.symm)
    have hxzero : x=0 := sq_eq_zero_iff.mp hx0
    rw [hxzero] at hn ⊢
    exact neg_eq_zero.mp hn.symm |>.symm

end UnivalentBlochOddRoot

/- Taylor coefficient rules for the rational transform at the origin. -/

open Metric Set Filter FormalMultilinearSeries
open scoped Topology NNReal

namespace UnivalentBlochTaylor

noncomputable def c (f : ℂ → ℂ) (n : ℕ) : ℂ := iteratedDeriv n f 0 / (n.factorial : ℂ)

theorem cauchy_eq {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball 0 1)) (n : ℕ) :
    (cauchyPowerSeries f 0 (19/20)).coeff n = c f n := by
  let R : ℝ≥0 := 19/20
  have hR : 0 < R := by norm_num [R]
  have hr : closedBall (0 : ℂ) R ⊆ ball 0 1 := closedBall_subset_ball (by norm_num [R])
  have hs := ((hf.mono hr).hasFPowerSeriesOnBall (c := 0) hR).factorial_smul (1 : ℂ) n
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, Finset.prod_const_one, one_smul] at hs
  have h : (n.factorial : ℂ) * (cauchyPowerSeries f 0 R).coeff n = iteratedDeriv n f 0 := by
    simpa only [FormalMultilinearSeries.coeff, nsmul_eq_mul, Pi.one_def] using hs
  have hn : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  unfold c
  exact (eq_div_iff hn).mpr ((mul_comm _ _).trans h)

@[simp] theorem c_zero (f : ℂ → ℂ) : c f 0 = f 0 := by simp [c]

@[simp] theorem c_one (f : ℂ → ℂ) : c f 1 = deriv f 0 := by simp [c, iteratedDeriv_one]

private theorem c_mul {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (n : ℕ) (hn : n ≤ 4) :
    c (fun z => f z*g z) n = ∑ i ∈ Finset.range (n+1), c f i * c g (n-i) := by
  have hp := iteratedDeriv_fun_mul (n := n) hf.contDiffAt hg.contDiffAt
  unfold c
  rw [hp]
  interval_cases n <;> norm_num [Finset.sum_range_succ, show Nat.choose 4 2 = 6 by decide] <;> ring

theorem scaled_coeff {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball 0 1)) {α : ℂ}
    (hα : α ≠ 0) (ha : ‖α‖ ≤ 1) (n : ℕ) (hn : 1 ≤ n) :
    c (fun z => f (α*z)/α) n = α^(n-1)*c f n := by
  have hz : (0 : ℂ) ∈ ball 0 1 := mem_ball_self zero_lt_one
  have hm : MapsTo (fun z : ℂ => α*z) (ball 0 1) (ball 0 1) := by
    intro z hz
    rw [mem_ball_zero_iff, norm_mul]
    exact (mul_le_mul_of_nonneg_right ha (norm_nonneg z)).trans_lt (by
      simpa using mem_ball_zero_iff.mp hz)
  have hAs := hf.analyticOnNhd isOpen_ball
  have hf0 := hAs 0 hz
  have hD : ContDiffOn ℂ n f (ball 0 1) := hAs.contDiffOn isOpen_ball.uniqueDiffOn
  have hg : AnalyticAt ℂ (fun z : ℂ => f (α*z)) 0 := by
    have hL : AnalyticAt ℂ (fun z : ℂ => α*z) 0 := by fun_prop
    have hAt : AnalyticAt ℂ f (α*0) := by simpa using hf0
    exact hAt.comp hL
  have h := iteratedDerivWithin_comp_const_smul
    hz isOpen_ball.uniqueDiffOn hD α hm
  rw [iteratedDerivWithin_eq_iteratedDeriv isOpen_ball.uniqueDiffOn hg.contDiffAt hz,
    mul_zero, iteratedDerivWithin_eq_iteratedDeriv isOpen_ball.uniqueDiffOn hf0.contDiffAt hz,
    smul_eq_mul] at h
  rw [c, c, iteratedDeriv_div_const, h]
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hn)
  rw [Nat.succ_sub_one, pow_succ]
  field_simp [hα]

/-- The low-order coefficients obtained by multiplying out the rational transform. -/
theorem rational_coeff {f F : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hF : AnalyticAt ℂ F 0)
    (hf0 : f 0 = 0) (hf1 : deriv f 0 = 1) (hc2 : c f 2 = 0)
    (hF0 : F 0 = 0) (hF1 : deriv F 0 = 1)
    {A q : ℂ} (hE : (fun z => F z*(1-A*f z+q*(f z)^2)) =ᶠ[𝓝 0] f) :
    c F 2 = A ∧ (c F 2)^2 - c F 3 = q - c f 3 ∧
      -(c F 2)^3 + 2*(c F 2)*(c F 3) - c F 4 = -c f 4 := by
  let D := fun z => 1 - A*f z + q*(f z)^2
  have hD : AnalyticAt ℂ D 0 := by unfold D; fun_prop
  have hD0 : c D 0 = 1 := by simp [D, hf0]
  have hDform (n : ℕ) (hn : 0 < n) :
      c D n = -A*c f n + q*c (fun z => f z*f z) n := by
    have hC : ContDiffAt ℂ n f 0 := hf.contDiffAt
    have hCA : ContDiffAt ℂ n (fun z : ℂ => 1-A*f z) 0 := by fun_prop
    have hCB : ContDiffAt ℂ n (fun z : ℂ => q*(f z*f z)) 0 := by fun_prop
    simp only [c, D, pow_two]
    rw [iteratedDeriv_fun_add hCA hCB, iteratedDeriv_const_sub hn, iteratedDeriv_neg,
      iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field]
    ring
  have hD1 : c D 1 = -A := by
    rw [hDform 1 (by decide), c_mul hf hf 1 (by decide)]
    norm_num [Finset.sum_range_succ, hf0, hf1]
  have hD2 : c D 2 = q := by
    rw [hDform 2 (by decide), c_mul hf hf 2 (by decide), hc2]
    norm_num [Finset.sum_range_succ, hf0, hf1]
  have hD3 : c D 3 = -A*c f 3 := by
    rw [hDform 3 (by decide), c_mul hf hf 3 (by decide)]
    norm_num [Finset.sum_range_succ, hf0, hf1, hc2]
  have he (n : ℕ) (hn : n ≤ 4) :
      (∑ i ∈ Finset.range (n+1), c F i * c D (n-i)) = c f n := by
    rw [← c_mul hF hD n hn]
    unfold c
    rw [hE.iteratedDeriv_eq _]
  have he2 := he 2 (by decide)
  have he3 := he 3 (by decide)
  have he4 := he 4 (by decide)
  norm_num [Finset.sum_range_succ, hF0, hF1, hD0, hD1, hD2, hD3, hc2] at he2 he3 he4
  have hF2 : c F 2 = A := by linear_combination he2
  rw [hF2] at he3 he4 ⊢
  refine ⟨rfl, ?_, ?_⟩
  · linear_combination -he3
  · linear_combination -he4 + A*he3

end UnivalentBlochTaylor

/- The exterior function and the finite Laurent coefficients used by the Grunsky bound. -/

namespace UnivalentBlochExterior

open Metric Set Filter UnivalentBlochTaylor
open scoped Topology

noncomputable def ext (u : ℂ → ℂ) (w : ℂ) : ℂ := w*u ((w⁻¹)^2)

theorem inverse_square_mem {w : ℂ} (hw : 1 < ‖w‖) : (w⁻¹)^2 ∈ ball (0 : ℂ) 1 := by
  have hp := zero_lt_one.trans hw
  rw [mem_ball_zero_iff, norm_pow, norm_inv]
  exact pow_lt_one₀ (inv_nonneg.mpr hp.le) (inv_lt_one_of_one_lt₀ hw) (by decide)

theorem exists_exterior {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball 0 1))
    (hI : InjOn f (ball 0 1)) (h0 : f 0 = 0) (h1 : deriv f 0 = 1) :
    ∃ u : ℂ → ℂ, DifferentiableOn ℂ u (ball 0 1) ∧ u 0 = 1 ∧
      (∀ z ∈ ball (0 : ℂ) 1, (u z)^2 * dslope f 0 z = 1) ∧
      DifferentiableOn ℂ (ext u) {w | 1 < ‖w‖} ∧ InjOn (ext u) {w | 1 < ‖w‖} := by
  let D := dslope f 0
  have hm : (0 : ℂ) ∈ ball 0 1 := mem_ball_self zero_lt_one
  have hDD : DifferentiableOn ℂ D (ball 0 1) :=
    (Complex.differentiableOn_dslope (ball_mem_nhds 0 zero_lt_one)).mpr hf
  have hD (z : ℂ) (hz : z ≠ 0) : D z = f z / z := by
    simp [D, dslope_of_ne f hz, slope_def_field, h0]
  have hFn (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) (hn : z ≠ 0) : f z ≠ 0 :=
    fun he => hn (hI hz hm (he.trans h0.symm))
  have hD_ne (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) : D z ≠ 0 := by
    rcases eq_or_ne z 0 with rfl | hn
    · simp [D, h1]
    rw [hD z hn]
    exact div_ne_zero (hFn z hz hn) hn
  obtain ⟨u, hu, hu0, hU⟩ := UnivalentBlochOddRoot.normalized_sqrt
    (hDD.inv hD_ne) (by simp [D, h1]) (fun z hz => inv_ne_zero (hD_ne z hz))
  have huEq (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) : (u z)^2 * D z=1 := by
    rw [hU z hz]
    exact inv_mul_cancel₀ (hD_ne z hz)
  refine ⟨u,hu,hu0,huEq,?_,?_⟩
  · intro w hw
    have hw' : 1 < ‖w‖ := hw
    have hn : w ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans hw')
    have hA := hu.differentiableAt (isOpen_ball.mem_nhds (inverse_square_mem hw'))
    unfold ext
    have hB : DifferentiableAt ℂ (fun w : ℂ => (w⁻¹)^2) w :=
      (differentiableAt_id.inv hn).pow 2
    exact (differentiableAt_id.mul (hA.comp w hB)).differentiableWithinAt
  have he (w : ℂ) (hw : w ∈ {w : ℂ | 1 < ‖w‖}) : (ext u w)^2 = (f ((w⁻¹)^2))⁻¹ := by
    have hn : w ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans (show 1 < ‖w‖ from hw))
    have hh : (w⁻¹)^2 ≠ 0 := pow_ne_zero _ (inv_ne_zero hn)
    have hz := inverse_square_mem hw
    rw [ext, mul_pow, hU _ hz]
    change w^2*(D ((w⁻¹)^2))⁻¹ = _
    rw [hD _ hh, inv_div, ← mul_div_assoc, ← mul_pow, mul_inv_cancel₀ hn, one_pow, one_div]
  intro x hx y hy hxy
  have hy0 : y ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans (show 1 < ‖y‖ from hy))
  have hFe : f ((x⁻¹)^2) = f ((y⁻¹)^2) := by
    apply inv_injective
    rw [← he x hx, ← he y hy, hxy]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hI (inverse_square_mem hx) (inverse_square_mem hy) hFe)
    with heq | hneg
  · exact inv_injective heq
  · have hxy' : x=-y := inv_injective (hneg.trans (inv_neg (a := y)).symm)
    have hodd : ext u (-y)= -ext u y := by simp [ext]
    rw [hxy', hodd] at hxy
    have hL : ext u y=0 := by linear_combination -(1/2 : ℂ)*hxy
    have hFne := inv_ne_zero (hFn ((y⁻¹)^2) (inverse_square_mem hy)
      (pow_ne_zero _ (inv_ne_zero hy0)))
    exfalso
    apply hFne
    rw [← he y hy, hL]
    norm_num

private theorem dslope_coeff {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball 0 1))
    (h0 : f 0 = 0) (n : ℕ) (hn : n ≤ 3) :
    c (dslope f 0) n = c f (n+1) := by
  let D := dslope f 0
  have hDD : DifferentiableOn ℂ D (ball 0 1) :=
    (Complex.differentiableOn_dslope (ball_mem_nhds 0 zero_lt_one)).mpr hf
  have hE : (fun z : ℂ => z*D z) = f := by
    funext z
    rcases eq_or_ne z 0 with rfl | hn
    · simp [h0]
    simp [D, dslope_of_ne f hn, slope_def_field, h0, mul_div_cancel₀ _ hn]
  have hsum := UnivalentBlochTaylor.c_mul (show AnalyticAt ℂ (fun z : ℂ => z) 0 by fun_prop)
    (hDD.analyticOnNhd isOpen_ball 0 (mem_ball_self zero_lt_one)) (n+1) (by omega)
  change c (fun z : ℂ => z*D z) (n+1) = _ at hsum
  rw [hE] at hsum
  have hid (i : ℕ) : c (fun z : ℂ => z) i = (if i = 1 then 1 else 0) := by
    by_cases hi : i=1
    · simp [hi]
    · simp [c, iteratedDeriv_fun_id_zero, hi]
  simp_rw [hid] at hsum
  rw [Finset.sum_eq_single 1] at hsum
  · simpa using hsum.symm
  · intro b _ hb
    simp [hb]
  · intro hh
    have he : 1 ∈ Finset.range (n+1+1) := Finset.mem_range.mpr (by omega)
    contradiction

theorem reciprocal_sqrt_coefficients {f u : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 1)) (h0 : f 0=0) (h1 : deriv f 0=1)
    (hu : DifferentiableOn ℂ u (ball 0 1)) (hu0 : u 0=1)
    (he : ∀ z ∈ ball (0 : ℂ) 1, (u z)^2*dslope f 0 z=1) :
    c u 1 = -c f 2/2 ∧ c u 2 = 3*(c f 2)^2/8-c f 3/2 ∧
      c u 3 = -5*(c f 2)^3/16+3*c f 2*c f 3/4-c f 4/2 := by
  let D := dslope f 0
  let U := fun z => u z*u z
  have hball : (ball (0 : ℂ) 1) ∈ 𝓝 (0 : ℂ) := ball_mem_nhds 0 zero_lt_one
  have hDD : DifferentiableOn ℂ D (ball 0 1) :=
    (Complex.differentiableOn_dslope hball).mpr hf
  have hA := hu.analyticOnNhd isOpen_ball 0 (mem_ball_self zero_lt_one)
  have hAD := hDD.analyticOnNhd isOpen_ball 0 (mem_ball_self zero_lt_one)
  have hAU : AnalyticAt ℂ U 0 := hA.mul hA
  have hcD0 : c D 0=1 := by simp [D,h1]
  have hcD1 : c D 1=c f 2 := dslope_coeff hf h0 1 (by decide)
  have hcD2 : c D 2=c f 3 := dslope_coeff hf h0 2 (by decide)
  have hcD3 : c D 3=c f 4 := dslope_coeff hf h0 3 (by decide)
  have hE : (fun z => U z * D z) =ᶠ[𝓝 0] fun _ => 1 := by
    filter_upwards [hball] with z hz
    simpa [U, D, pow_two] using he z hz
  have heq (n : ℕ) (hn : 0 < n) (hn4 : n ≤ 4) :
      (∑ i ∈ Finset.range (n+1), c U i*c D (n-i))=0 := by
    rw [← UnivalentBlochTaylor.c_mul hAU hAD n hn4]
    simp [c, hE.iteratedDeriv_eq n, iteratedDeriv_const, hn.ne']
  have hU0 : c U 0=1 := by simp [U,hu0]
  have hU1 : c U 1=2*c u 1 := by
    unfold U
    rw [UnivalentBlochTaylor.c_mul hA hA 1 (by decide)]
    norm_num [Finset.sum_range_succ,hu0]
    ring
  have hU2 : c U 2=(c u 1)^2+2*c u 2 := by
    unfold U
    rw [UnivalentBlochTaylor.c_mul hA hA 2 (by decide)]
    norm_num [Finset.sum_range_succ,hu0]
    ring
  have hU3 : c U 3=2*c u 1*c u 2+2*c u 3 := by
    unfold U
    rw [UnivalentBlochTaylor.c_mul hA hA 3 (by decide)]
    norm_num [Finset.sum_range_succ,hu0]
    ring
  have hE1 := heq 1 (by decide) (by decide)
  have hE2 := heq 2 (by decide) (by decide)
  have hE3 := heq 3 (by decide) (by decide)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd, Nat.reduceSub,
    hU0, hU1, hU2, hU3, hcD0, hcD1, hcD2, hcD3] at hE1 hE2 hE3
  have hc1 : c u 1=-c f 2/2 := by
    linear_combination (1/2 : ℂ)*hE1
  have hc2 : c u 2=3*(c f 2)^2/8-c f 3/2 := by
    rw [hc1] at hE2
    linear_combination (1/2 : ℂ)*hE2
  have hc3 : c u 3=-5*(c f 2)^3/16+3*c f 2*c f 3/4-c f 4/2 := by
    have hc1' := hc1
    rw [c_one] at hc1'
    rw [hc1,hc2] at hE3
    linear_combination (1/2 : ℂ)*hE3
  exact ⟨hc1,hc2,hc3⟩

noncomputable def weighted (u : ℂ → ℂ) (α β : ℂ) (z : ℂ) : ℂ :=
  β*(u z)^3+(α-3*β*c u 1)*z*u z

theorem weighted_differentiableOn {u : ℂ → ℂ}
    (hu : DifferentiableOn ℂ u (ball 0 1)) (α β : ℂ) :
    DifferentiableOn ℂ (weighted u α β) (ball 0 1) := by
  unfold weighted
  fun_prop

theorem weighted_eq {u : ℂ → ℂ} (α β : ℂ) {w : ℂ} (hw : w ≠ 0) :
    w^3 * weighted u α β ((w⁻¹)^2) =
      α * ext u w + β*((ext u w)^3 - 3*c u 1*ext u w) := by
  simp only [weighted, ext]
  field_simp [hw]
  ring

theorem weighted_coefficients {u : ℂ → ℂ} (hu : AnalyticAt ℂ u 0) (hu0 : u 0=1)
    (α β : ℂ) :
    c (weighted u α β) 0 = β ∧
      c (weighted u α β) 1 = α ∧
      c (weighted u α β) 2 = α*c u 1 + 3*β*c u 2 ∧
      c (weighted u α β) 3 = α*c u 2 + 3*β*(c u 3+c u 1*c u 2+(c u 1)^3/3) := by
  let U := fun z => u z*u z
  let C := fun z => U z*u z
  let L := fun z : ℂ => z*u z
  let d := α-3*β*c u 1
  have hU : AnalyticAt ℂ U 0 := hu.mul hu
  have hC : AnalyticAt ℂ C 0 := hU.mul hu
  have hID : AnalyticAt ℂ (fun z : ℂ => z) 0 := by fun_prop
  have hL : AnalyticAt ℂ L 0 := hID.mul hu
  have hcId (n : ℕ) : c (fun z : ℂ => z) n = if n=1 then 1 else 0 := by
    by_cases hn : n=1 <;> simp [c, hn, iteratedDeriv_fun_id_zero]
  have hCU (n : ℕ) (hn : n ≤ 3) :
      c U n = ∑ i ∈ Finset.range (n+1), c u i*c u (n-i) :=
    UnivalentBlochTaylor.c_mul hu hu n (by omega)
  have hCC (n : ℕ) (hn : n ≤ 3) :
      c C n = ∑ i ∈ Finset.range (n+1), c U i*c u (n-i) :=
    UnivalentBlochTaylor.c_mul hU hu n (by omega)
  have hCL (n : ℕ) (hn : n ≤ 3) :
      c L n = ∑ i ∈ Finset.range (n+1), (if i=1 then 1 else 0)*c u (n-i) := by
    simpa only [hcId] using (UnivalentBlochTaylor.c_mul hID hu n (by omega))
  have hV : weighted u α β = fun z => β*C z+d*L z := by
    funext z
    simp only [weighted, C, U, d, L]
    ring
  have hcv (n : ℕ) : c (weighted u α β) n = β*c C n+d*c L n := by
    have hCD : ContDiffAt ℂ n C 0 := hC.contDiffAt
    have hLD : ContDiffAt ℂ n L 0 := hL.contDiffAt
    have hf : ContDiffAt ℂ n (fun z => β*C z) 0 := by fun_prop
    have hg : ContDiffAt ℂ n (fun z => d*L z) 0 := by fun_prop
    simp only [hV, c, iteratedDeriv_fun_add hf hg, iteratedDeriv_const_mul_field]
    ring
  refine ⟨?_,?_,?_,?_⟩
  · simp [weighted, hu0]
  all_goals
    rw [hcv, hCC _ (by decide), hCL _ (by decide)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd, Nat.reduceSub,
      Nat.reduceEqDiff, ↓reduceIte]
    rw [hCU 0 (by decide), hCU 1 (by decide)]
    try rw [hCU 2 (by decide)]
    try rw [hCU 3 (by decide)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd, Nat.reduceSub,
      c_zero, hu0]
    dsimp only [d]
    ring

end UnivalentBlochExterior

/- Uniform Laurent expansion and derivative expansion for the weighted boundary. -/

open Filter Metric Set FormalMultilinearSeries
open scoped Topology NNReal ENNReal

namespace UnivalentBlochLaurent

open UnivalentBlochTaylor

def order (n : ℕ) : ℤ := 3-2*n

noncomputable def phase (j : ℤ) (θ : ℝ) : ℂ := Complex.exp (((j : ℂ)*Complex.I)*θ)

noncomputable def angular (v : ℂ → ℂ) (R θ : ℝ) : ℂ :=
  (circleMap 0 R θ)^3 * v (((circleMap 0 R θ)⁻¹)^2)

noncomputable def weight (v : ℂ → ℂ) (R : ℝ) (n : ℕ) : ℂ :=
  c v n * (R : ℂ)^(order n)

private theorem scalar_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (p : FormalMultilinearSeries ℂ ℂ E) (n : ℕ) (z : ℂ) :
    p n (fun _ => z) = z^n • p.coeff n := by
  simp only [FormalMultilinearSeries.apply_eq_prod_smul_coeff, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

private theorem taylor_sums {v : ℂ → ℂ} (hv : DifferentiableOn ℂ v (ball 0 1))
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    HasSum (fun n => c v n * z^n) (v z) ∧
      HasSum (fun n : ℕ => ((n : ℂ)*c v n)*z^n) (z*deriv v z) := by
  let p := cauchyPowerSeries v 0 (1/2)
  have hp : HasFPowerSeriesOnBall v p 0 1 := UnivalentBlochOddRoot.full_series hv
  have hc (n : ℕ) : p.coeff n = c v n := by
    unfold c
    have he := hp.factorial_smul (1 : ℂ) n
    rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, Finset.prod_const_one, one_smul] at he
    have h : (n.factorial : ℂ)*p.coeff n = iteratedDeriv n v 0 := by
      simpa only [FormalMultilinearSeries.coeff, nsmul_eq_mul, Pi.one_def] using he
    exact (eq_div_iff (Nat.cast_ne_zero.mpr n.factorial_ne_zero)).mpr ((mul_comm _ _).trans h)
  have hzz : z ∈ eball (0 : ℂ) 1 := by
    rw [mem_eball_zero_iff, enorm_eq_nnnorm, ← ENNReal.coe_one, ENNReal.coe_lt_coe]
    exact NNReal.coe_lt_coe.mp (by simpa only [coe_nnnorm, NNReal.coe_one] using mem_ball_zero_iff.mp hz)
  have hs : HasSum (fun n => p n (fun _ => z)) (v z) := by
    simpa only [zero_add] using hp.hasSum hzz
  constructor
  · simpa only [scalar_apply, hc, smul_eq_mul, mul_comm] using hs
  have hD : HasSum (fun n => p.derivSeries n (fun _ => z)) (fderiv ℂ v z) := by
    simpa only [zero_add] using hp.fderiv.hasSum hzz
  let E : (ℂ →L[ℂ] ℂ) →L[ℂ] ℂ := ContinuousLinearMap.apply ℂ ℂ 1
  have hd := E.hasSum hD
  have hEq (n : ℕ) : E (p.derivSeries n (fun _ => z)) =
      ((n+1 : ℕ):ℂ)*c v (n+1)*z^n := by
    change p.derivSeries n (fun _ => z) 1 = _
    rw [scalar_apply, _root_.smul_apply, p.derivSeries_coeff_one,
      nsmul_eq_mul, hc, smul_eq_mul]
    ring
  change HasSum (fun n => E (p.derivSeries n (fun _ => z))) (deriv v z) at hd
  simp_rw [hEq] at hd
  apply (hasSum_nat_add_iff' 1).mp
  simp only [Finset.sum_range_one, Nat.cast_zero, zero_mul, sub_zero]
  have he : (fun n : ℕ => ((n+1 : ℕ):ℂ)*c v (n+1)*z^(n+1)) =
      (fun n : ℕ => z*(((n+1 : ℕ):ℂ)*c v (n+1)*z^n)) := by
    funext n
    rw [pow_succ]
    ring
  rw [he]
  exact hd.mul_left z

private theorem taylor_norm_summable {v : ℂ → ℂ} (hv : DifferentiableOn ℂ v (ball 0 1))
    {r : ℝ≥0} (hr : r < 1) :
    Summable (fun n => ‖c v n‖*(r : ℝ)^n) ∧
      Summable (fun n : ℕ => ‖(n : ℂ)*c v n‖*(r : ℝ)^n) := by
  let p := cauchyPowerSeries v 0 (1/2)
  have hp : HasFPowerSeriesOnBall v p 0 1 := UnivalentBlochOddRoot.full_series hv
  have hc (n : ℕ) : p.coeff n = c v n := by
    unfold c
    have he := hp.factorial_smul (1 : ℂ) n
    rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, Finset.prod_const_one, one_smul] at he
    have h : (n.factorial : ℂ)*p.coeff n = iteratedDeriv n v 0 := by
      simpa only [FormalMultilinearSeries.coeff, nsmul_eq_mul, Pi.one_def] using he
    exact (eq_div_iff (Nat.cast_ne_zero.mpr n.factorial_ne_zero)).mpr ((mul_comm _ _).trans h)
  have hre : (r : ℝ≥0∞) < 1 := by exact_mod_cast hr
  constructor
  · simpa only [← hc, UnivalentBlochOddRoot.norm_coeff] using
      p.summable_norm_mul_pow (hre.trans_le hp.r_le)
  have hds := p.derivSeries.summable_norm_mul_pow (hre.trans_le hp.fderiv.r_le)
  apply (summable_nat_add_iff 1).mp
  apply Summable.of_nonneg_of_le (fun _ => by positivity) ?_ (hds.mul_left (r : ℝ))
  intro n
  have hb₁ : ‖(p.derivSeries n (fun _ => 1)) 1‖ ≤ ‖p.derivSeries n (fun _ => 1)‖ := by
    simpa using (p.derivSeries n (fun _ => 1)).le_opNorm (1 : ℂ)
  have hb₂ : ‖p.derivSeries n (fun _ => 1)‖ ≤ ‖p.derivSeries n‖ := by
    exact ((p.derivSeries n).le_opNorm (fun _ => (1 : ℂ))).trans (by simp)
  have h : ‖((n+1 : ℕ):ℂ)*c v (n+1)‖ ≤ ‖p.derivSeries n‖ := by
    have hh := hb₁.trans hb₂
    change ‖p.derivSeries.coeff n 1‖ ≤ _ at hh
    rwa [p.derivSeries_coeff_one, nsmul_eq_mul, hc] at hh
  rw [pow_succ]
  exact (mul_le_mul_of_nonneg_right h (by positivity)).trans_eq (by ring)

theorem angular_derivative {v : ℂ → ℂ} (hv : DifferentiableOn ℂ v (ball 0 1))
    {R : ℝ} (hR : 1 < R) (θ : ℝ) :
    HasDerivAt (angular v R)
      (((circleMap 0 R θ)^3 * (3*v (((circleMap 0 R θ)⁻¹)^2) -
        2*((circleMap 0 R θ)⁻¹)^2*deriv v (((circleMap 0 R θ)⁻¹)^2)))*Complex.I) θ := by
  let w := circleMap 0 R θ
  have hwr : ‖w‖=R := by rw [norm_circleMap_zero, abs_of_pos (zero_lt_one.trans hR)]
  have hw0 : w ≠ 0 := norm_pos_iff.mp (hwr ▸ zero_lt_one.trans hR)
  let z := (w⁻¹)^2
  have hz : z ∈ ball (0 : ℂ) 1 :=
    UnivalentBlochExterior.inverse_square_mem (hwr ▸ hR)
  have hd : HasDerivAt v (deriv v z) z :=
    (hv.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
  have hi : HasDerivAt (fun w : ℂ => w⁻¹) (-(w^2)⁻¹) w := hasDerivAt_inv hw0
  have hi' := hi.fun_pow 2
  have hh := ((hasDerivAt_id w).fun_pow 3).mul (hd.comp w hi')
  have hExpect : HasDerivAt (fun w : ℂ => w^3*v ((w⁻¹)^2))
      (w^2*(3*v z-2*z*deriv v z)) w := by
    convert hh using 1
    all_goals first
      | rfl
      | (simp only [Function.comp_apply, id_eq, Nat.reduceSub, pow_one, Nat.cast_ofNat, z];
         field_simp [hw0]; ring)
  have hhc := hExpect.scomp θ (hasDerivAt_circleMap 0 R θ)
  change HasDerivAt (angular v R) ((w*Complex.I)*(w^2*(3*v z-2*z*deriv v z))) θ at hhc
  convert hhc using 1
  change w^3*(3*v z-2*z*deriv v z)*Complex.I = _
  ring

private theorem mode_term (v : ℂ → ℂ) {R : ℝ} (hR : 1 < R) (n : ℕ) (θ : ℝ) :
    weight v R n * phase (order n) θ =
      (circleMap 0 R θ)^3 * (c v n * ((((circleMap 0 R θ)⁻¹)^2)^n)) := by
  have hw : circleMap 0 R θ ≠ 0 := by
    apply norm_pos_iff.mp
    rw [norm_circleMap_zero, abs_of_pos (zero_lt_one.trans hR)]
    exact zero_lt_one.trans hR
  have he : (circleMap 0 R θ)^(order n) = (R : ℂ)^(order n)*phase (order n) θ := by
    rw [circleMap_zero_zpow, circleMap_zero, Complex.ofReal_zpow, Complex.ofReal_mul,
      Complex.ofReal_intCast]
    unfold phase
    congr 2
    ring
  rw [weight, mul_assoc, ← he, order, zpow_sub₀ hw]
  rw [show (2*(n:ℤ))=((2*n:ℕ):ℤ) by push_cast; rfl, zpow_natCast]
  simp only [zpow_ofNat, div_eq_mul_inv]
  generalize circleMap 0 R θ = w
  rw [← inv_pow, pow_mul]
  ring

set_option maxHeartbeats 700000 in
theorem uniform (v : ℂ → ℂ) (hv : DifferentiableOn ℂ v (ball 0 1)) {R : ℝ} (hR : 1 < R) :
    TendstoUniformly
      (fun N θ => ∑ n ∈ Finset.range N, weight v R n * phase (order n) θ)
      (angular v R) atTop ∧
    TendstoUniformly
      (fun N θ => ∑ n ∈ Finset.range N,
        ((order n : ℂ)*Complex.I)*weight v R n * phase (order n) θ)
      (deriv (angular v R)) atTop := by
  have hRpos := zero_lt_one.trans hR
  let r : ℝ≥0 := ⟨(R⁻¹)^2, sq_nonneg _⟩
  have hr : r < 1 := NNReal.coe_lt_coe.mp (by
    simp only [r, NNReal.coe_one]
    exact pow_lt_one₀ (inv_nonneg.mpr hRpos.le) (inv_lt_one_of_one_lt₀ hR) (by decide))
  obtain ⟨hSum,hSumD⟩ := taylor_norm_summable hv hr
  have hθ (θ : ℝ) : ‖circleMap 0 R θ‖=R := by
    rw [norm_circleMap_zero, abs_of_pos hRpos]
  have hz (θ : ℝ) : ‖((circleMap 0 R θ)⁻¹)^2‖=(r : ℝ) := by
    rw [norm_pow, norm_inv, hθ]
    rfl
  have hnorm (n : ℕ) (θ : ℝ) :
      ‖weight v R n * phase (order n) θ‖ = R^3*(‖c v n‖*(r : ℝ)^n) := by
    rw [mode_term v hR, norm_mul, norm_pow, hθ, norm_mul, norm_pow, hz]
  have hs (θ : ℝ) :
      ((circleMap 0 R θ)⁻¹)^2 ∈ ball (0 : ℂ) 1 :=
    UnivalentBlochExterior.inverse_square_mem (by rwa [hθ])
  constructor
  · have h := tendstoUniformly_tsum_nat (hSum.mul_left (R^3)) (fun n θ => (hnorm n θ).le)
    convert h using 1
    funext θ
    have hh := ((taylor_sums hv (hs θ)).1.mul_left ((circleMap 0 R θ)^3))
    simpa only [angular, ← mode_term v hR] using hh.tsum_eq.symm
  let W : ℕ → ℝ := fun n =>
    R^3*(3*(‖c v n‖*(r : ℝ)^n)+2*(‖(n : ℂ)*c v n‖*(r : ℝ)^n))
  have hW : Summable W := ((hSum.mul_left 3).add (hSumD.mul_left 2)).mul_left _
  have hn (n : ℕ) (θ : ℝ) :
      ‖((order n : ℂ)*Complex.I)*weight v R n * phase (order n) θ‖ ≤ W n := by
    rw [mul_assoc, mode_term v hR]
    let w := circleMap 0 R θ
    let z := (w⁻¹)^2
    have hEq : ((order n : ℂ)*Complex.I)*(w^3*(c v n*z^n)) =
        ((Complex.I*w^3)*z^n)*(3*c v n-2*((n : ℂ)*c v n)) := by
      simp [order]
      ring
    rw [hEq, norm_mul, norm_mul, norm_mul, Complex.norm_I, one_mul, norm_pow, norm_pow,
      hθ, hz]
    have hh := norm_sub_le (3*c v n) (2*((n : ℂ)*c v n))
    rw [norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_ofNat] at hh
    exact (mul_le_mul_of_nonneg_left hh (by positivity)).trans_eq (by unfold W; ring)
  have h := tendstoUniformly_tsum_nat hW hn
  convert h using 1
  funext θ
  let w := circleMap 0 R θ
  let z := (w⁻¹)^2
  obtain ⟨he,hDe⟩ := taylor_sums hv (hs θ)
  have hss := (((he.mul_left 3).sub (hDe.mul_left 2)).mul_left (w^3)).mul_right Complex.I
  rw [(angular_derivative hv hR θ).deriv]
  have heq : (fun n : ℕ => ((order n : ℂ)*Complex.I)*weight v R n*phase (order n) θ) =
      (fun n : ℕ => w^3*(3*(c v n*z^n)-2*(((n : ℂ)*c v n)*z^n))*Complex.I) := by
    funext n
    rw [mul_assoc, mode_term v hR]
    change ((order n : ℂ)*Complex.I)*(w^3*(c v n*z^n)) =
      w^3*(3*(c v n*z^n)-2*(((n : ℂ)*c v n)*z^n))*Complex.I
    simp [order]
    ring
  rw [heq]
  change w^3*(3*v z - 2*z*deriv v z)*Complex.I = _
  rw [mul_assoc (2 : ℂ) z (deriv v z)]
  exact hss.tsum_eq.symm

end UnivalentBlochLaurent

/- Orthogonality of Laurent modes in the boundary area integral. -/

open MeasureTheory intervalIntegral Complex Filter
open scoped BigOperators ComplexConjugate

namespace GrunskyBoundary

noncomputable section

private def mode (j : ℤ) (θ : ℝ) : ℂ := exp (((j : ℂ) * I) * θ)

private theorem continuous_mode (j : ℤ) : Continuous (mode j) := by
  unfold mode
  fun_prop

private theorem conj_mode_mul_mode (j k : ℤ) (θ : ℝ) :
    conj (mode k θ) * mode j θ = mode (j-k) θ := by
  unfold mode
  rw [← exp_conj, ← exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, map_intCast, Complex.conj_I, Int.cast_sub]
  ring

private theorem integral_mode (j : ℤ) :
    (∫ θ in 0..2*Real.pi, mode j θ) = if j = 0 then ((2*Real.pi : ℝ) : ℂ) else 0 := by
  by_cases hj : j = 0
  · subst j
    simp [mode, intervalIntegral.integral_const, Complex.real_smul]
  · have hne : ((j : ℂ) * I) ≠ 0 :=
      mul_ne_zero (Int.cast_ne_zero.mpr hj) I_ne_zero
    unfold mode
    rw [integral_exp_mul_complex hne]
    have h : exp ((j : ℂ)*I*((2*Real.pi : ℝ) : ℂ)) = 1 := by
      convert Complex.exp_int_mul_two_pi_mul_I j using 2
      push_cast
      ring
    rw [h, if_neg hj]
    simp

theorem integral_laurent_pair (s : Finset ℤ) (a b : ℤ → ℂ) :
    (∫ θ in 0..2*Real.pi,
      conj (∑ j ∈ s, a j * mode j θ) * (∑ j ∈ s, b j * mode j θ)) =
    ∑ j ∈ s, ((2*Real.pi : ℝ) : ℂ) * (conj (a j) * b j) := by
  have hterm (j k : ℤ) (θ : ℝ) :
      (conj (a k) * conj (mode k θ)) * (b j * mode j θ) =
        (conj (a k) * b j) * mode (j-k) θ := by
    rw [← conj_mode_mul_mode]
    ring
  have hc (k j : ℤ) : Continuous (fun θ => (conj (a k)*b j)*mode (j-k) θ) :=
    continuous_const.mul (continuous_mode (j-k))
  simp_rw [map_sum, Finset.sum_mul, Finset.mul_sum, map_mul, hterm]
  rw [intervalIntegral.integral_finsetSum (fun k _ =>
    Continuous.intervalIntegrable
      (show Continuous (fun θ => ∑ j ∈ s, (conj (a k) * b j) * mode (j-k) θ) from
        continuous_finsetSum s (fun j _ => hc k j)) _ _)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [intervalIntegral.integral_finsetSum (fun j _ =>
    Continuous.intervalIntegrable (hc k j) _ _)]
  simp_rw [intervalIntegral.integral_const_mul, integral_mode, sub_eq_zero]
  simp [hk, mul_comm]

/-- Uniform convergence on a compact interval lets the boundary pairing pass to the limit. -/
theorem integral_tendsto_of_uniform {ι : Type*} {l : Filter ι} {a b : ℝ}
    {F : ι → ℝ → ℂ} {f : ℝ → ℂ} (hab : a < b)
    (h : TendstoUniformlyOn F f l (Set.Icc a b))
    (hF : ∀ i, IntervalIntegrable (F i) volume a b) (hf : IntervalIntegrable f volume a b) :
    Filter.Tendsto (fun i => ∫ t in a..b, F i t) l (nhds (∫ t in a..b, f t)) := by
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  let δ := ε / (2 * (b-a))
  have hpos : 0 < b-a := sub_pos.mpr hab
  have hδ : 0 < δ := div_pos hε (by positivity)
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp h δ hδ] with i hi
  rw [dist_eq_norm, ← intervalIntegral.integral_sub (hF i) hf]
  have hnorm : ‖∫ t in a..b, F i t - f t‖ ≤ δ * |b-a| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    rw [Set.uIoc_of_le hab.le] at ht
    have hd := hi t ⟨ht.1.le,ht.2⟩
    rw [dist_comm, dist_eq_norm] at hd
    exact hd.le
  apply hnorm.trans_lt
  rw [abs_of_pos hpos]
  have heq : δ * (b-a) = ε/2 := by
    dsimp [δ]
    field_simp
  rw [heq]
  linarith

end

end GrunskyBoundary

/- Consequences of the first two odd Grunsky coefficients. -/

open Metric Set FormalMultilinearSeries

namespace UnivalentBlochCompression

def Bound (A Q J : ℂ) : Prop :=
  ∀ x y : ℂ, ‖(-A/2)*x+(Q/2-A^2/8)*y‖^2 +
    3*‖(Q/2-A^2/8)*x+(J/2-A^3/24)*y‖^2 ≤ ‖x‖^2+‖y‖^2/3

noncomputable def a (f : ℂ → ℂ) (n : ℕ) : ℂ :=
  (cauchyPowerSeries f 0 (19/20)).coeff n

def ForNormalized : Prop :=
  ∀ f : ℂ → ℂ, DifferentiableOn ℂ f (ball 0 1) → InjOn f (ball 0 1) →
    f 0 = 0 → deriv f 0 = 1 →
    Bound (a f 2) ((a f 2)^2 - a f 3)
      (-(a f 2)^3 + 2*(a f 2)*(a f 3) - a f 4)

theorem first_row {A : ℝ} {Q J : ℂ} (h : Bound A Q J) :
    A^2/4 + 3*‖Q/2 - ((A^2/8 : ℝ) : ℂ)‖^2 ≤ 1 := by
  have hb := h 1 0
  norm_num at hb
  have he : (|A|/2)^2 = A^2/4 := by
    rw [div_pow, sq_abs]
    norm_num
  rw [he] at hb
  push_cast
  exact hb

theorem fourth {Q J : ℂ} (h : Bound 0 Q J) : ‖J‖ ≤ 2/3 := by
  have hb := h 0 1
  norm_num [norm_div, Complex.norm_ofNat] at hb
  have hj := norm_nonneg J
  by_contra! he
  have ht := mul_pos (sub_pos.mpr he) (show 0 < ‖J‖+2/3 by positivity)
  nlinarith [sq_nonneg ‖Q/2‖]

theorem support {A : ℝ} {Q J : ℂ} (h : Bound A Q J) :
    A^3/12+5*A^2/4+25*A/4-25/2-2/3 ≤ J.re + 5*Q.re := by
  let U := (-(A : ℂ)/2)*(5/2)+(Q/2-(A : ℂ)^2/8)
  let V := (Q/2-(A : ℂ)^2/8)*(5/2)+(J/2-(A : ℂ)^3/24)
  have hUV : ‖U‖^2+3*‖V‖^2 ≤ 25/4+1/3 := by
    have hb := h (5/2) 1
    norm_num [U, V, norm_div, Complex.norm_ofNat] at hb ⊢
    exact hb
  have hnormU : ‖U‖^2 = U.re^2+U.im^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hnormV : ‖V‖^2 = V.re^2+V.im^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hReU : U.re = -A*(5/4)+Q.re/2-A^2/8 := by
    norm_num [U, Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.div_re,
      Complex.normSq_apply, ← Complex.ofReal_pow]
    ring
  have hReV : V.re = (Q.re/2-A^2/8)*(5/2)+J.re/2-A^3/24 := by
    norm_num [V, Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.div_re,
      Complex.normSq_apply, ← Complex.ofReal_pow]
    ring
  rw [hnormU, hnormV] at hUV
  nlinarith [sq_nonneg (U.re+5/2), sq_nonneg (V.re+1/3), sq_nonneg U.im, sq_nonneg V.im,
    hReU, hReV]

end UnivalentBlochCompression

open Metric Set Filter MeasureTheory intervalIntegral
open scoped Topology ComplexConjugate

namespace UnivalentBlochFlux

open UnivalentBlochTaylor UnivalentBlochLaurent

private theorem uniform_pair {F G : ℕ → ℝ → ℂ} {f g : ℝ → ℂ} {s : Set ℝ}
    (hs : IsCompact s) (hf : ContinuousOn f s) (hg : ContinuousOn g s)
    (hF : TendstoUniformlyOn F f atTop s) (hG : TendstoUniformlyOn G g atTop s) :
    TendstoUniformlyOn (fun N θ => conj (F N θ)*G N θ) (fun θ => conj (f θ)*g θ)
      atTop s := by
  obtain ⟨a,ha⟩ := hs.exists_bound_of_continuousOn hf
  obtain ⟨b,hb⟩ := hs.exists_bound_of_continuousOn hg
  let C := max 1 (max a b)
  have hC : 1 ≤ C := le_max_left _ _
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  let δ := min 1 (ε/(3*C))
  have hδ : 0 < δ := lt_min zero_lt_one (div_pos hε (by positivity))
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hF δ hδ,
    Metric.tendstoUniformlyOn_iff.mp hG δ hδ] with N hNF hNG θ hθ
  rw [dist_comm,dist_eq_norm]
  have hfδ := hNF θ hθ
  have hgδ := hNG θ hθ
  rw [dist_comm,dist_eq_norm] at hfδ hgδ
  have hfC : ‖f θ‖ ≤ C := (ha θ hθ).trans ((le_max_left _ _).trans (le_max_right _ _))
  have hgC : ‖g θ‖ ≤ C := (hb θ hθ).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hGN : ‖G N θ‖ ≤ 2*C := by
    calc
      ‖G N θ‖ = ‖(G N θ-g θ)+g θ‖ := by rw [sub_add_cancel]
      _ ≤ ‖G N θ-g θ‖+‖g θ‖ := norm_add_le _ _
      _ ≤ 2*C := by linarith [min_le_left (1 : ℝ) (ε/(3*C))]
  have hEq : conj (F N θ)*G N θ - conj (f θ)*g θ =
      conj (F N θ-f θ)*G N θ+conj (f θ)*(G N θ-g θ) := by
    rw [map_sub]
    ring
  rw [hEq]
  refine (norm_add_le _ _).trans_lt ?_
  rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj]
  have h₁ : ‖F N θ-f θ‖*‖G N θ‖ < δ*(2*C) :=
    (mul_le_mul_of_nonneg_left hGN (norm_nonneg _)).trans_lt
      (mul_lt_mul_of_pos_right hfδ (by positivity))
  have h₂ : ‖f θ‖*‖G N θ-g θ‖ ≤ C*δ :=
    mul_le_mul hfC hgδ.le (norm_nonneg _) hC0.le
  have hδC : δ*(3*C) ≤ ε := (le_div_iff₀ (by positivity : 0 < 3*C)).mp (min_le_right _ _)
  linarith

private theorem continuous_phase (j : ℤ) : Continuous (phase j) := by
  unfold phase
  fun_prop

private theorem sum_bound {v : ℂ → ℂ} (hv : DifferentiableOn ℂ v (ball 0 1))
    {R : ℝ} (hR : 1 < R)
    (hPos : 0 ≤ ∫ θ in 0..2*Real.pi, (conj (angular v R θ)*deriv (angular v R) θ).im) :
    0 ≤ ∑ n ∈ Finset.range 4, (UnivalentBlochLaurent.order n : ℝ)*‖weight v R n‖^2 := by
  obtain ⟨hU,hUD⟩ := uniform v hv hR
  let F : ℕ → ℝ → ℂ := fun N θ => ∑ n ∈ Finset.range N, weight v R n*phase (UnivalentBlochLaurent.order n) θ
  let D : ℕ → ℝ → ℂ := fun N θ => ∑ n ∈ Finset.range N,
    ((UnivalentBlochLaurent.order n : ℂ)*Complex.I)*weight v R n*phase (UnivalentBlochLaurent.order n) θ
  have hFc (N : ℕ) : Continuous (F N) := by
    dsimp [F]
    exact continuous_finsetSum _ fun n _ => continuous_const.mul (continuous_phase _)
  have hDc (N : ℕ) : Continuous (D N) := by
    dsimp [D]
    exact continuous_finsetSum _ fun n _ => continuous_const.mul (continuous_phase _)
  have hC : Continuous (angular v R) := hU.continuous (Frequently.of_forall hFc)
  have hCD : Continuous (deriv (angular v R)) := hUD.continuous (Frequently.of_forall hDc)
  have hcont (N : ℕ) : Continuous (fun θ => conj (F N θ)*D N θ) :=
    (Complex.continuous_conj.comp (hFc N)).mul (hDc N)
  have hcontL : Continuous (fun θ => conj (angular v R θ)*deriv (angular v R) θ) :=
    (Complex.continuous_conj.comp hC).mul hCD
  have hInt := hcontL.intervalIntegrable (μ := volume) 0 (2*Real.pi)
  have hLim := GrunskyBoundary.integral_tendsto_of_uniform
    (by positivity : 0<2*Real.pi)
    (uniform_pair isCompact_Icc hC.continuousOn hCD.continuousOn
      hU.tendstoUniformlyOn hUD.tendstoUniformlyOn)
    (fun N => (hcont N).intervalIntegrable (μ := volume) 0 (2*Real.pi)) hInt
  let e : ℕ ↪ ℤ := ⟨UnivalentBlochLaurent.order, fun a b hab => by unfold UnivalentBlochLaurent.order at hab; omega⟩
  let a : ℤ → ℂ := fun j => weight v R (Function.invFun UnivalentBlochLaurent.order j)
  let b : ℤ → ℂ := fun j => ((j : ℂ)*Complex.I)*a j
  have ha (n : ℕ) : a (e n) = weight v R n := by
    change weight v R (Function.invFun UnivalentBlochLaurent.order (UnivalentBlochLaurent.order n)) = _
    rw [Function.leftInverse_invFun (show Function.Injective UnivalentBlochLaurent.order from e.inj') n]
  have hb (n : ℕ) : b (e n)=((UnivalentBlochLaurent.order n : ℂ)*Complex.I)*weight v R n := by
    change ((UnivalentBlochLaurent.order n : ℂ)*Complex.I)*a (e n) = _
    rw [ha]
  have hMode (n : ℕ) : GrunskyBoundary.mode (e n) = phase (UnivalentBlochLaurent.order n) := rfl
  have hFin (N : ℕ) : (∫ θ in 0..2*Real.pi, conj (F N θ)*D N θ) =
      ∑ n ∈ Finset.range N, ((2*Real.pi : ℝ):ℂ) *
        (conj (weight v R n)*(((UnivalentBlochLaurent.order n : ℂ)*Complex.I)*weight v R n)) := by
    have he := GrunskyBoundary.integral_laurent_pair ((Finset.range N).map e) a b
    simpa only [Finset.sum_map, Function.Embedding.coeFn_mk, ha, hb, hMode, F, D] using he
  change Tendsto (fun N => ∫ θ in 0..2*Real.pi, conj (F N θ)*D N θ) atTop
    (𝓝 (∫ θ in 0..2*Real.pi, conj (angular v R θ)*deriv (angular v R) θ)) at hLim
  simp_rw [hFin] at hLim
  have hImag := (Complex.continuous_im.continuousAt).tendsto.comp hLim
  have hterm (n : ℕ) : (((2*Real.pi : ℝ):ℂ) *
      (conj (weight v R n)*(((UnivalentBlochLaurent.order n : ℂ)*Complex.I)*weight v R n))).im =
      (2*Real.pi)*((UnivalentBlochLaurent.order n : ℝ)*‖weight v R n‖^2) := by
    rw [show conj (weight v R n)*(((UnivalentBlochLaurent.order n : ℂ)*Complex.I)*weight v R n) =
      ((UnivalentBlochLaurent.order n : ℂ)*Complex.I)*(weight v R n*conj (weight v R n)) by ring,
      Complex.mul_conj, ← Complex.sq_norm]
    simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.intCast_re, Complex.intCast_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      add_zero, zero_add, mul_one, sub_zero]
  have hsumIm (N : ℕ) :
      (∑ n ∈ Finset.range N, ((2*Real.pi : ℝ):ℂ) *
        (conj (weight v R n)*(((UnivalentBlochLaurent.order n : ℂ)*Complex.I)*weight v R n))).im =
        (2*Real.pi)*∑ n ∈ Finset.range N, (UnivalentBlochLaurent.order n : ℝ)*‖weight v R n‖^2 := by
    rw [Finset.mul_sum]
    change Complex.imAddGroupHom (∑ n ∈ Finset.range N, _) = _
    rw [map_sum]
    exact Finset.sum_congr rfl (fun n _ => hterm n)
  have hIm : 0 ≤ (∫ θ in 0..2*Real.pi, conj (angular v R θ)*deriv (angular v R) θ).im := by
    have h : (∫ θ in 0..2*Real.pi, (conj (angular v R θ)*deriv (angular v R) θ).im) =
        (∫ θ in 0..2*Real.pi, conj (angular v R θ)*deriv (angular v R) θ).im :=
      Complex.imCLM.intervalIntegral_comp_comm hInt
    rwa [← h]
  have hImLim : Tendsto
      (fun N => (2*Real.pi)*∑ n ∈ Finset.range N, (UnivalentBlochLaurent.order n : ℝ)*‖weight v R n‖^2)
      atTop (𝓝 (∫ θ in 0..2*Real.pi, conj (angular v R θ)*deriv (angular v R) θ).im) := by
    simpa only [Function.comp_def, hsumIm] using hImag
  have hLE := le_of_tendsto hImLim (b := (2*Real.pi)*∑ n ∈ Finset.range 4,
      (UnivalentBlochLaurent.order n : ℝ)*‖weight v R n‖^2) <| eventually_atTop.mpr ⟨4, fun N hN => by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [← Finset.sum_sdiff (Finset.range_mono hN)]
    apply add_le_of_nonpos_left
    apply Finset.sum_nonpos
    intro n hn
    have hn4 : 4 ≤ n := Nat.le_of_not_lt fun h => (Finset.mem_sdiff.mp hn).2 (Finset.mem_range.mpr h)
    have hord : UnivalentBlochLaurent.order n ≤ 0 := by unfold UnivalentBlochLaurent.order; omega
    exact mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hord) (sq_nonneg _)⟩
  exact nonneg_of_mul_nonneg_right (hIm.trans hLE) (by positivity : 0 < 2*Real.pi)

private theorem unit_sum_bound {v : ℂ → ℂ} (hv : DifferentiableOn ℂ v (ball 0 1))
    (hPos : ∀ R>1, 0 ≤ ∫ θ in 0..2*Real.pi, (conj (angular v R θ)*deriv (angular v R) θ).im) :
    0 ≤ ∑ n ∈ Finset.range 4, (UnivalentBlochLaurent.order n : ℝ)*‖c v n‖^2 := by
  let S : ℝ → ℝ := fun R => ∑ n ∈ Finset.range 4, (UnivalentBlochLaurent.order n : ℝ)*‖weight v R n‖^2
  have hC (n : ℕ) : ContinuousAt (fun R : ℝ => (UnivalentBlochLaurent.order n : ℝ)*‖weight v R n‖^2) 1 := by
    apply continuousAt_const.mul
    apply ContinuousAt.pow
    apply ContinuousAt.norm
    unfold weight
    have h₁ : ContinuousAt (fun R : ℝ => (R : ℂ)) 1 := Complex.continuous_ofReal.continuousAt
    exact continuousAt_const.mul (h₁.zpow₀ _ (Or.inl (by norm_num)))
  have hCS : ContinuousAt S 1 := by
    have H0 := hC 0
    have H1 := hC 1
    have H2 := hC 2
    have H3 := hC 3
    simp only [S, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    fun_prop
  have hlim : Tendsto S (𝓝[>] (1:ℝ)) (𝓝 (S 1)) :=
    hCS.continuousWithinAt
  have hpos : 0 ≤ S 1 := ge_of_tendsto hlim <| by
    filter_upwards [self_mem_nhdsWithin] with R hR
    exact sum_bound hv hR (hPos R hR)
  simpa only [S, weight, Complex.ofReal_one, one_zpow, mul_one] using hpos

/-- Boundary positivity for the exterior maps suffices for the two-mode compression. -/
def Positive : Prop :=
  ∀ (u : ℂ → ℂ), DifferentiableOn ℂ u (ball 0 1) → u 0=1 →
    InjOn (UnivalentBlochExterior.ext u) {w | 1 < ‖w‖} →
    ∀ (α β : ℂ) (R : ℝ), 1<R →
      let v := UnivalentBlochExterior.weighted u α β
      0 ≤ ∫ θ in 0..2*Real.pi, (conj (angular v R θ)*deriv (angular v R) θ).im

theorem compression_of_positive (hPositive : Positive) : UnivalentBlochCompression.ForNormalized := by
  intro f hf hI hf0 hf1
  obtain ⟨u,hu,hu0,he,_,hU⟩ := UnivalentBlochExterior.exists_exterior hf hI hf0 hf1
  obtain ⟨h1,h2,h3⟩ := UnivalentBlochExterior.reciprocal_sqrt_coefficients hf hf0 hf1 hu hu0 he
  unfold UnivalentBlochCompression.Bound UnivalentBlochCompression.a
  simp only [cauchy_eq hf]
  intro x y
  let v := UnivalentBlochExterior.weighted u x (y/3)
  have hpos := unit_sum_bound (UnivalentBlochExterior.weighted_differentiableOn hu x (y/3))
    (hPositive u hu hu0 hU x (y/3))
  obtain ⟨hc0,hc1,hc2,hc3⟩ := UnivalentBlochExterior.weighted_coefficients
    (hu.analyticOnNhd isOpen_ball 0 (mem_ball_self zero_lt_one)) hu0 x (y/3)
  have hc2' : c v 2 = -c f 2/2*x+((c f 2^2-c f 3)/2-(c f 2)^2/8)*y := by
    change c (UnivalentBlochExterior.weighted u x (y/3)) 2 = _
    rw [hc2,h1,h2]
    ring
  have hc3' : c v 3 = ((c f 2^2-c f 3)/2-(c f 2)^2/8)*x+
      ((-(c f 2)^3+2*(c f 2)*(c f 3)-c f 4)/2-(c f 2)^3/24)*y := by
    change c (UnivalentBlochExterior.weighted u x (y/3)) 3 = _
    rw [hc3,h1,h2,h3]
    ring
  change 0 ≤ ∑ n ∈ Finset.range 4, (UnivalentBlochLaurent.order n : ℝ)*‖c v n‖^2 at hpos
  have hc0' : c v 0=y/3 := hc0
  have hc1' : c v 1=x := hc1
  norm_num [Finset.sum_range_succ, UnivalentBlochLaurent.order, hc0', hc1', hc2', hc3', norm_div,
    Complex.norm_ofNat] at hpos
  linarith

end UnivalentBlochFlux

namespace UnivalentBlochFlux

open UnivalentBlochTaylor UnivalentBlochLaurent UnivalentBlochExterior

/-- Adapt the exterior-map area comparison to the weighted map used in the
compression. -/
theorem positive_of_exterior
    (H : ∀ (h b P : ℂ → ℂ), DifferentiableOn ℂ h {w | 1 < ‖w‖} →
      InjOn h {w | 1 < ‖w‖} → (∀ w, 1 < ‖w‖ → h w ≠ 0) →
      AnalyticAt ℂ b 0 → b 0 = 1 → (∀ w, 1 < ‖w‖ → h w = w*b w⁻¹) →
      Differentiable ℂ P → ∀ R>1,
      0 ≤ ∫ θ in 0..2*Real.pi,
        (conj (P (h (circleMap 0 R θ))) *
          deriv (fun t => P (h (circleMap 0 R t))) θ).im) : Positive := by
  intro u hu hu0 hInj α β R hR
  let h := UnivalentBlochExterior.ext u
  let b := fun w : ℂ => u (w^2)
  let P := fun w : ℂ => α*w+β*(w^3-3*c u 1*w)
  have hD : DifferentiableOn ℂ h {w | 1 < ‖w‖} := by
    intro w hw
    have hw' : 1<‖w‖ := hw
    have hn : w ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans hw')
    have hA := hu.differentiableAt (isOpen_ball.mem_nhds (inverse_square_mem hw'))
    have hB : DifferentiableAt ℂ (fun w : ℂ => (w⁻¹)^2) w :=
      (differentiableAt_id.inv hn).pow 2
    exact (differentiableAt_id.mul (hA.comp w hB)).differentiableWithinAt
  have hNe (w : ℂ) (hw : 1<‖w‖) : h w ≠ 0 := by
    intro h0
    have hneg : h (-w) = -h w := by simp [h, UnivalentBlochExterior.ext]
    have hI' : InjOn h {w | 1 < ‖w‖} := hInj
    have hww : -w=w := hI' (by simpa using hw) hw (by rw [hneg,h0,neg_zero])
    have hzero : w=0 := by linear_combination -(1/2 : ℂ)*hww
    norm_num [hzero] at hw
  have hb : AnalyticAt ℂ b 0 := by
    have h := hu.analyticOnNhd isOpen_ball 0 (mem_ball_self zero_lt_one)
    have hp : AnalyticAt ℂ (fun w : ℂ => w^2) 0 := by fun_prop
    have h' : AnalyticAt ℂ u ((0 : ℂ)^2) := by simpa using h
    exact h'.comp (f := fun z : ℂ => z^2) (x := (0 : ℂ)) hp
  have hb0 : b 0 = 1 := by simp [b, hu0]
  have hP : Differentiable ℂ P := by unfold P; fun_prop
  have he : angular (weighted u α β) R = fun θ => P (h (circleMap 0 R θ)) := by
    funext θ
    have hn : circleMap 0 R θ ≠ 0 := by
      apply norm_pos_iff.mp
      rw [norm_circleMap_zero, abs_of_pos (zero_lt_one.trans hR)]
      exact zero_lt_one.trans hR
    exact weighted_eq α β hn
  change 0 ≤ ∫ θ in 0..2*Real.pi,
    (conj (angular (weighted u α β) R θ) * deriv (angular (weighted u α β) R) θ).im
  rw [he]
  exact H h b P hD hInj hNe hb hb0 (fun _ _ => rfl) hP R hR

end UnivalentBlochFlux

/- Landau normalization for univalent maps and transfer of disks in their images. -/

open Metric Set
open scoped ComplexConjugate

namespace UnivalentBlochNormalization

def Covers (f : ℂ → ℂ) (B : ℝ) : Prop :=
  ∃ S, IsOpen S ∧ S ⊆ ball 0 1 ∧ ∃ x, f '' S = ball x B ∧ InjOn f S

noncomputable def mobius (a z : ℂ) : ℂ := (z + a) / (1 + conj a * z)

private theorem denom_ne {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    1 + conj a * z ≠ 0 := by
  intro h
  have he : conj a * z = -1 := eq_neg_of_add_eq_zero_right h
  have hn : ‖a‖ * ‖z‖ = 1 := by
    simpa [norm_mul] using congrArg norm he
  nlinarith [norm_nonneg a, norm_nonneg z, mul_pos (sub_pos.mpr ha) (sub_pos.mpr hz)]

theorem norm_identity (a z : ℂ) :
    ‖1 + conj a * z‖ ^ 2 - ‖z + a‖ ^ 2 = (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.one_re, Complex.one_im, Complex.mul_re, Complex.mul_im, Complex.conj_re,
    Complex.conj_im]
  ring

theorem maps_mobius {a : ℂ} (ha : ‖a‖ < 1) :
    MapsTo (mobius a) (ball 0 1) (ball 0 1) := by
  intro z hz
  rw [mem_ball_zero_iff] at hz ⊢
  rw [mobius, norm_div, div_lt_one (norm_pos_iff.mpr (denom_ne ha hz))]
  have hap : 0 < 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
  have hzp : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  nlinarith [norm_identity a z, mul_pos hap hzp, norm_nonneg (z+a),
    norm_nonneg (1+conj a*z)]

theorem mobius_zero {a : ℂ} : mobius a 0 = a := by simp [mobius]

theorem mobius_inverse {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    mobius (-a) (mobius a z) = z := by
  have hd := denom_ne ha hz
  have hza : ‖mobius a z‖ < 1 := mem_ball_zero_iff.mp
    (maps_mobius ha (mem_ball_zero_iff.mpr hz))
  have hdi := denom_ne (a := -a) (by simpa using ha) hza
  unfold mobius at *
  simp only [map_neg] at hdi ⊢
  apply (div_eq_iff hdi).mpr
  have hnum : z + a - a * (1 + conj a * z) =
      z * ((1 + conj a * z) - conj a * (z + a)) := by ring
  have hleft : (z + a) / (1 + conj a * z) + -a =
      (z + a - a * (1 + conj a * z)) / (1 + conj a * z) := by
    apply (eq_div_iff hd).mpr
    rw [add_mul, div_mul_cancel₀ _ hd]
    ring
  have hright : 1 + -conj a * ((z + a) / (1 + conj a * z)) =
      ((1 + conj a * z) - conj a * (z + a)) / (1 + conj a * z) := by
    apply (eq_div_iff hd).mpr
    rw [add_mul, mul_assoc, div_mul_cancel₀ _ hd]
    ring
  rw [hleft, hright, hnum, mul_div_assoc]

theorem hasDerivAt_mobius {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    HasDerivAt (mobius a)
      ((1 - (‖a‖ ^ 2 : ℝ) : ℂ) / (1 + conj a * z)^2) z := by
  have hd := denom_ne ha hz
  have h := ((hasDerivAt_id z).add_const a).div
    (((hasDerivAt_id z).const_mul (conj a)).const_add 1) hd
  have he : conj a * a = (‖a‖ ^ 2 : ℝ) := by
    rw [mul_comm, Complex.mul_conj, Complex.sq_norm]
  have hv : 1 * (1 + conj a * id z) - (id z + a) * (conj a * 1) =
      1 - ((‖a‖ ^ 2 : ℝ) : ℂ) := by
    rw [← he]
    simp only [id_eq]
    ring
  rw [hv] at h
  exact h

theorem mobius_weight {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    (1 - ‖z‖ ^ 2) * ‖deriv (mobius a) z‖ = 1 - ‖mobius a z‖ ^ 2 := by
  have hn := norm_pos_iff.mpr (denom_ne ha hz)
  have hap : 0 ≤ 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
  have he : ‖(1 - ((‖a‖ ^ 2 : ℝ) : ℂ))‖ = 1 - ‖a‖ ^ 2 := by
    rw [show (1 : ℂ) - ↑(‖a‖ ^ 2) = ↑(1 - ‖a‖ ^ 2 : ℝ) by push_cast; rfl,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hap]
  rw [(hasDerivAt_mobius ha hz).deriv, mobius, norm_div, norm_pow, norm_div, div_pow, he]
  field_simp
  nlinarith [norm_identity a z]

theorem normalized_reduction {B R : ℝ} (hB : 0 < B) (hBR : B < R)
    (hNorm : ∀ g : ℂ → ℂ, InjOn g (ball 0 1) → DifferentiableOn ℂ g (ball 0 1) → g 0 = 0 →
      deriv g 0 = 1 → (∀ z ∈ ball (0 : ℂ) 1, (1 - ‖z‖ ^ 2) * ‖deriv g z‖ ≤ 1) →
      Covers g R) : B ≤ Bloch.univalentBlochConstant := by
  unfold Bloch.univalentBlochConstant
  apply le_csSup
  · refine ⟨1, ?_⟩
    intro b hb
    have hc : ∃ S, IsOpen S ∧ S ⊆ ball (0 : ℂ) 1 ∧
        ∃ x, id '' S = ball x b ∧ InjOn id S :=
      hb id (injOn_id _) differentiableOn_id (by simp)
    rcases hc with ⟨S, -, hS, x, hball, -⟩
    rw [image_id] at hball
    by_cases hp : 0 < b
    · exact Bloch.radius_le_of_ball_subset_ball (𝕜 := ℂ) hp (hball ▸ hS)
    · linarith
  intro F hFinj hF hF0
  have hR : 0 < R := hB.trans hBR
  obtain ⟨s, hsB, hs1⟩ := exists_between ((div_lt_one hR).mpr hBR)
  have hs0 : 0 < s := (div_pos hB hR).trans hsB
  have hsB' : B < s * R := (div_lt_iff₀ hR).mp hsB
  let f : ℂ → ℂ := fun z => F ((s : ℂ) * z)
  have hsf : 1 < 1 / s := (lt_div_iff₀ hs0).mpr (by simpa using hs1)
  have hf : DifferentiableOn ℂ f (ball 0 (1 / s)) := by
    have hlin : Differentiable ℂ (fun z : ℂ => (s : ℂ) * z) := by fun_prop
    apply hF.comp hlin.differentiableOn
    intro z hz
    simp only [mem_ball_zero_iff] at hz ⊢
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0]
    nlinarith [(lt_div_iff₀ hs0).mp hz]
  have h0mem : (0 : ℂ) ∈ ball 0 1 := mem_ball_self zero_lt_one
  have hf0 : deriv f 0 = (s : ℂ) := by
    have hF' := (hF.differentiableAt (isOpen_ball.mem_nhds h0mem)).hasDerivAt
    have hh : HasDerivAt (fun z : ℂ => (s : ℂ) * z) (s : ℂ) 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_mul (s : ℂ)
    have hF'' : HasDerivAt F 1 ((s : ℂ) * 0) := by simpa [hF0] using hF'
    simpa [f, Function.comp_def] using (hF''.comp 0 hh).deriv
  let W : ℂ → ℝ := fun z => (1 - ‖z‖ ^ 2) * ‖deriv f z‖
  have hW : ContinuousOn W (closedBall 0 1) := by
    have hc : ContinuousOn (deriv f) (closedBall 0 1) :=
      ((hf.deriv isOpen_ball).continuousOn).mono (closedBall_subset_ball hsf)
    exact ((continuous_const.sub (continuous_norm.pow 2)).continuousOn).mul hc.norm
  obtain ⟨a, ha, hmax⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_isMaxOn
    ⟨0, mem_closedBall_self zero_le_one⟩ hW
  have hwa : s ≤ W a := by
    have hm := hmax (mem_closedBall_self (x := (0 : ℂ)) zero_le_one)
    simpa [W, hf0, abs_of_pos hs0] using hm
  have ha' : ‖a‖ < 1 := by
    have ham : ‖a‖ ≤ 1 := mem_closedBall_zero_iff.mp ha
    apply lt_of_le_of_ne ham
    intro he
    simp [W, he, hs0.not_ge] at hwa
  let d : ℂ := deriv f a * (1 - (‖a‖ ^ 2 : ℝ))
  have hdn : ‖d‖ = W a := by
    have hap : 0 ≤ 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
    dsimp [d, W]
    rw [show (1 : ℂ) - ↑(‖a‖ ^ 2) = ↑(1 - ‖a‖ ^ 2 : ℝ) by push_cast; rfl,
      norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hap, mul_comm]
  have hd0 : d ≠ 0 := norm_pos_iff.mp (by rw [hdn]; exact hs0.trans_le hwa)
  let g : ℂ → ℂ := fun z => (f (mobius a z) - f a) / d
  have hgd (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) :
      HasDerivAt g ((deriv f (mobius a z) * deriv (mobius a) z) / d) z := by
    have hp := hasDerivAt_mobius ha' (mem_ball_zero_iff.mp hz)
    have hza := maps_mobius ha' hz
    have hfd := hf.differentiableAt
      (isOpen_ball.mem_nhds (ball_subset_ball hsf.le hza))
    exact (((hfd.hasDerivAt.comp z (hp.deriv ▸ hp)).sub_const (f a)).div_const d)
  have hgD : DifferentiableOn ℂ g (ball 0 1) :=
    fun z hz => (hgd z hz).differentiableAt.differentiableWithinAt
  have hg0 : g 0 = 0 := by simp [g, mobius_zero]
  have hgD0 : deriv g 0 = 1 := by
    rw [(hgd 0 h0mem).deriv, mobius_zero,
      (hasDerivAt_mobius ha' (by simp : ‖(0 : ℂ)‖ < 1)).deriv]
    simpa [d] using div_self hd0
  have hgW (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) :
      (1 - ‖z‖ ^ 2) * ‖deriv g z‖ ≤ 1 := by
    have hz' := maps_mobius ha' hz
    rw [(hgd z hz).deriv, norm_div, norm_mul, mul_comm ‖deriv f (mobius a z)‖,
      ← mul_div_assoc, ← mul_assoc, mobius_weight ha' (mem_ball_zero_iff.mp hz),
      div_le_one (norm_pos_iff.mpr hd0), hdn]
    exact hmax (ball_subset_closedBall hz')
  let t : ℂ → ℂ := fun z => (s : ℂ) * mobius a z
  let u : ℂ → ℂ := fun z => mobius (-a) (z / (s : ℂ))
  have hsC : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs0.ne'
  have ht (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) : t z ∈ ball 0 s := by
    have hm := mem_ball_zero_iff.mp (maps_mobius ha' hz)
    rw [mem_ball_zero_iff]
    dsimp [t]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0]
    nlinarith
  have huz (z : ℂ) (hz : z ∈ ball (0 : ℂ) s) : ‖z / (s : ℂ)‖ < 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0, div_lt_one hs0]
    exact mem_ball_zero_iff.mp hz
  have htu (z : ℂ) (hz : z ∈ ball (0 : ℂ) s) : t (u z) = z := by
    have hp := mobius_inverse (a := -a) (by simpa using ha') (huz z hz)
    simp only [neg_neg] at hp
    dsimp [t, u]
    rw [hp]
    field_simp
  have hut (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) : u (t z) = z := by
    have he : (s : ℂ) * mobius a z / (s : ℂ) = mobius a z := by
      field_simp
    exact (congrArg (mobius (-a)) he).trans (mobius_inverse ha' (mem_ball_zero_iff.mp hz))
  have hu : ContinuousOn u (ball 0 s) := by
    apply ContinuousOn.div (f := fun z : ℂ => z / (s : ℂ) + -a)
      (g := fun z : ℂ => 1 + conj (-a) * (z / (s : ℂ))) (by fun_prop) (by fun_prop)
    intro z hz
    exact denom_ne (a := -a) (by simpa using ha') (huz z hz)
  have hFt (z : ℂ) : F (t z) = d * g z + f a := by
    change f (mobius a z) = d * ((f (mobius a z) - f a) / d) + f a
    field_simp
    ring
  have hgInj : InjOn g (ball 0 1) := by
    intro x hx y hy he
    have hEq : F (t x) = F (t y) := by rw [hFt, hFt, he]
    have htx : t x ∈ ball (0 : ℂ) 1 := ball_subset_ball hs1.le (ht x hx)
    have hty : t y ∈ ball (0 : ℂ) 1 := ball_subset_ball hs1.le (ht y hy)
    rw [← hut x hx, ← hut y hy, hFinj htx hty hEq]
  obtain ⟨S, hS, hSsub, c, hSc, hSinj⟩ := hNorm g hgInj hgD hg0 hgD0 hgW
  let V := ball (0 : ℂ) s ∩ u ⁻¹' S
  have hV : IsOpen V := hu.isOpen_inter_preimage isOpen_ball hS
  have hVsub : V ⊆ ball (0 : ℂ) 1 := fun _ hz => ball_subset_ball hs1.le hz.1
  let c' := d * c + f a
  have himage : ball c' B ⊆ F '' V := by
    intro w hw
    have hw' : (w - f a) / d ∈ ball c R := by
      rw [mem_ball_iff_norm] at hw ⊢
      have he : (w - f a) / d - c = (w - c') / d := by
        dsimp [c']
        field_simp
        ring
      rw [he, norm_div, div_lt_iff₀ (norm_pos_iff.mpr hd0), hdn]
      exact hw.trans (hsB'.trans_le (by nlinarith))
    rw [← hSc] at hw'
    obtain ⟨z, hz, he⟩ := hw'
    refine ⟨t z, ⟨ht z (hSsub hz), ?_⟩, ?_⟩
    · simpa only [mem_preimage, hut z (hSsub hz)] using hz
    · rw [hFt, he]
      field_simp
      ring
  let U := V ∩ F ⁻¹' ball c' B
  have hU : IsOpen U := ((hF.continuousOn.mono hVsub)).isOpen_inter_preimage hV isOpen_ball
  refine ⟨U, hU, fun _ hz => hVsub hz.1, c', ?_, ?_⟩
  · apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      exact hz.2
    · intro w hw
      obtain ⟨z, hz, he⟩ := himage hw
      exact ⟨z, ⟨hz, by change F z ∈ ball c' B; rwa [he]⟩, he⟩
  · intro x hx y hy he
    have hx' : x ∈ V := hx.1
    have hy' : y ∈ V := hy.1
    have he' : g (u x) = g (u y) := by
      have hxF := hFt (u x)
      have hyF := hFt (u y)
      rw [htu y hy'.1] at hyF
      rw [htu x hx'.1, he, hyF] at hxF
      exact mul_left_cancel₀ hd0 (add_right_cancel hxF.symm)
    have heU := hSinj hx'.2 hy'.2 he'
    rw [← htu x hx'.1, ← htu y hy'.1, heU]

end UnivalentBlochNormalization

namespace UnivalentBlochNormalization

open MeasureTheory

/-- A disk already contained in the image of a univalent function is realized as the exact
image of an open subset of the domain. -/
theorem covers_of_ball_subset {f : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hf : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (hd : ball c r ⊆ f '' (ball 0 1)) : Covers f r := by
  let S := ball (0 : ℂ) 1 ∩ f ⁻¹' ball c r
  have hS : IsOpen S := hf.continuousOn.isOpen_inter_preimage isOpen_ball isOpen_ball
  refine ⟨S,hS,inter_subset_left,c,Subset.antisymm ?_ ?_,hi.mono inter_subset_left⟩
  · rintro _ ⟨z,hz,rfl⟩
    exact hz.2
  · intro w hw
    obtain ⟨z,hz,he⟩ := hd hw
    exact ⟨z,⟨hz,by change f z ∈ ball c r; rwa [he]⟩,he⟩

end UnivalentBlochNormalization

/- Low coefficients of a Landau-normalized holomorphic map. -/

open Metric Set Filter
open scoped NNReal ENNReal Topology ComplexConjugate

namespace BlochDistortion

private theorem deriv_zero_of_weight {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 1)) (hf0 : f 0 = 1)
    (hW : ∀ z ∈ ball (0 : ℂ) 1, (1 - ‖z‖ ^ 2) * ‖f z‖ ≤ 1) : deriv f 0 = 0 := by
  let a := deriv f 0
  let g : ℂ → ℂ := fun z => ((1 : ℂ) - z ^ 2 * (↑‖a‖ : ℂ)^2) * f (conj a * z)
  have hfd : HasDerivAt f a (conj a * 0) := by
    simpa [a] using (hf.differentiableAt (ball_mem_nhds (0 : ℂ) zero_lt_one)).hasDerivAt
  have hgd : HasDerivAt g (a * conj a) 0 := by
    have hh := (hfd.comp 0 ((hasDerivAt_id (0 : ℂ)).const_mul (conj a)))
    have hp : HasDerivAt (fun z : ℂ => (1 : ℂ) - z ^ 2 * (↑‖a‖ : ℂ)^2) 0 0 := by
      simpa using (((hasDerivAt_id (0 : ℂ)).fun_pow 2).mul_const ((↑‖a‖ : ℂ)^2)).const_sub 1
    simpa [g, Function.comp_def] using! hp.mul hh
  have hr := hgd.real_of_complex (z := (0 : ℝ))
  have hloc : IsLocalMax (fun t : ℝ => (g t).re) 0 := by
    change ∀ᶠ t : ℝ in 𝓝 0, (g t).re ≤ (g 0).re
    have hc : Continuous (fun t : ℝ => conj a * (t : ℂ)) := by fun_prop
    have hh : ∀ᶠ t : ℝ in 𝓝 0, conj a * (t : ℂ) ∈ ball (0 : ℂ) 1 := by
      have he : Tendsto (fun t : ℝ => conj a * (t : ℂ)) (𝓝 0) (𝓝 (0 : ℂ)) := by
        simpa using hc.tendsto (0 : ℝ)
      exact he.eventually (ball_mem_nhds (0 : ℂ) zero_lt_one)
    filter_upwards [hh] with t ht
    have hn : ‖conj a * (t : ℂ)‖ ^ 2 = t ^ 2 * ‖a‖ ^ 2 := by
      rw [norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
      ring
    have hp : 0 ≤ 1 - t ^ 2 * ‖a‖ ^ 2 := by
      have hh' := mem_ball_zero_iff.mp ht
      nlinarith [norm_nonneg (conj a * (t : ℂ))]
    have hwt := hW _ ht
    rw [hn] at hwt
    have hle := mul_le_mul_of_nonneg_left (Complex.re_le_norm (f (conj a * (t : ℂ)))) hp
    simpa [g, hf0, ← Complex.ofReal_sub, ← Complex.ofReal_mul, ← Complex.ofReal_pow] using hle.trans hwt
  have hzero := hloc.hasDerivAt_eq_zero hr
  have hh : ‖a‖ ^ 2 = 0 := by
    simpa [Complex.mul_conj, Complex.sq_norm] using hzero
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hh)

end BlochDistortion

namespace BlochCoefficients

private theorem cauchy_bound {f : ℂ → ℂ} {R M : ℝ}
    (hR : 0 < R) (hc : ContinuousOn f (sphere 0 R))
    (hM : ∀ z ∈ sphere (0 : ℂ) R, ‖f z‖ ≤ M) (k : ℕ) :
    ‖(cauchyPowerSeries f 0 R).coeff k‖ ≤ M * R⁻¹ ^ k := by
  have hi : IntervalIntegrable (fun θ : ℝ => ‖f (circleMap 0 R θ)‖)
      MeasureTheory.volume 0 (2 * Real.pi) := by
    have hmaps : MapsTo (circleMap 0 R) (uIcc 0 (2 * Real.pi)) (sphere 0 R) := by
      intro θ _
      exact circleMap_mem_sphere 0 hR.le θ
    exact (hc.comp (continuous_circleMap 0 R).continuousOn hmaps).norm.intervalIntegrable
  have hI : (∫ θ in (0 : ℝ)..2 * Real.pi, ‖f (circleMap 0 R θ)‖) ≤ (2 * Real.pi) * M := by
    calc
      _ ≤ ∫ _θ in (0 : ℝ)..2 * Real.pi, M :=
        intervalIntegral.integral_mono_on Real.two_pi_pos.le hi (intervalIntegrable_const)
          (fun θ _ => hM _ (circleMap_mem_sphere 0 hR.le θ))
      _ = _ := by simp
  have hn : ‖(cauchyPowerSeries f 0 R).coeff k‖ = ‖cauchyPowerSeries f 0 R k‖ := by
    rw [← ContinuousMultilinearMap.mkPiRing_apply_one_eq_self (cauchyPowerSeries f 0 R k),
      ContinuousMultilinearMap.norm_mkPiRing]
    rfl
  calc
    _ = _ := hn
    _ ≤ _ := norm_cauchyPowerSeries_le f 0 R k
    _ ≤ ((2 * Real.pi)⁻¹ * ((2 * Real.pi) * M)) * R⁻¹ ^ k := by
      rw [abs_of_pos hR]
      gcongr
    _ = _ := by rw [inv_mul_cancel_left₀ Real.two_pi_pos.ne']

theorem hasSum_coeff (f : ℂ → ℂ) {R : ℝ≥0} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (closedBall 0 R)) {z : ℂ} (hz : ‖z‖ < R) :
    HasSum (fun k => (cauchyPowerSeries f 0 R).coeff k * z ^ k) (f z) := by
  have hs := hf.hasFPowerSeriesOnBall (c := 0) hR
  have he : ∀ k, ((cauchyPowerSeries f 0 R).coeff k) * z ^ k =
      cauchyPowerSeries f 0 R k (fun _ => z) := by
    intro k
    rw [FormalMultilinearSeries.apply_eq_prod_smul_coeff]
    simp [smul_eq_mul, mul_comm]
  simp only [he]
  simpa only [zero_add] using hs.hasSum (y := z) (by
    rw [mem_eball_zero_iff]
    exact_mod_cast hz)

theorem radius95_coeff_bound {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball 0 1))
    (hW : ∀ z ∈ ball (0 : ℂ) 1, (1 - ‖z‖ ^ 2) * ‖f z‖ ≤ 1) (k : ℕ) :
    ‖(cauchyPowerSeries f 0 (19 / 20)).coeff k‖ ≤ (400 / 39) * (20 / 19 : ℝ) ^ k := by
  have hsub : sphere (0 : ℂ) (19 / 20) ⊆ ball 0 1 :=
    sphere_subset_closedBall.trans (closedBall_subset_ball (by norm_num))
  have h := cauchy_bound (f := f) (R := 19 / 20) (M := 400 / 39) (by norm_num)
    (hf.continuousOn.mono hsub) ?_ k
  · convert h using 3
    norm_num
  · intro z hz
    have hl := hW z (hsub hz)
    rw [mem_sphere_zero_iff_norm.mp hz] at hl
    norm_num at hl
    linarith

end BlochCoefficients

namespace BlochTails

theorem truncation {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {u : ℕ → E} {S : E} (hs : HasSum u S)
    {C q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hu : ∀ n, ‖u n‖ ≤ C * q ^ n) (N : ℕ) :
    ‖S - ∑ n ∈ Finset.range N, u n‖ ≤ C * q ^ N / (1 - q) := by
  have hsC : 0 ≤ C := by simpa using (norm_nonneg (u 0)).trans (hu 0)
  have hm (k : ℕ) : ‖u (k+N)‖ ≤ (C*q^N)*q^k := by
    have h := hu (k+N)
    rw [pow_add] at h
    convert h using 1
    ring
  have hg := (summable_geometric_of_lt_one hq0 hq1).mul_left (C*q^N)
  have hh := Summable.of_nonneg_of_le (fun k => norm_nonneg (u (k+N))) hm hg
  have htail : (∑ n ∈ Finset.range N, u n) + ∑' n, u (n + N) = S := by
    simpa only [hs.tsum_eq] using hs.summable.sum_add_tsum_nat_add N
  rw [← htail, add_sub_cancel_left]
  calc
    _ ≤ ∑' n, ‖u (n+N)‖ := norm_tsum_le_tsum_norm hh
    _ ≤ ∑' n, (C*q^N)*q^n := hh.tsum_le_tsum hm hg
    _ = _ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1, div_eq_mul_inv]

end BlochTails

namespace BlochLowCoefficients

private theorem coeff_eq_iteratedDeriv {f : ℂ → ℂ} {R : ℝ≥0} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (closedBall 0 R)) (n : ℕ) :
    (n.factorial : ℂ) * (cauchyPowerSeries f 0 R).coeff n = iteratedDeriv n f 0 := by
  have hs := (hf.hasFPowerSeriesOnBall (c := 0) hR).factorial_smul (1 : ℂ) n
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, Finset.prod_const_one, one_smul] at hs
  simpa only [FormalMultilinearSeries.coeff, nsmul_eq_mul, Pi.one_def] using hs

private theorem coef_const {f : ℂ → ℂ} {R : ℝ≥0} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (closedBall 0 R)) :
    (cauchyPowerSeries f 0 R).coeff 0 = f 0 := by
  simpa using coeff_eq_iteratedDeriv hR hf 0

private theorem coef_first {f : ℂ → ℂ} {R : ℝ≥0} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (closedBall 0 R)) :
    (cauchyPowerSeries f 0 R).coeff 1 = deriv f 0 := by
  simpa using coeff_eq_iteratedDeriv hR hf 1

private theorem phase_square (a : ℂ) (ha : a ≠ 0) :
    ∃ ξ : ℂ, ‖ξ‖ = 1 ∧ a*ξ^2 = (‖a‖ : ℂ) := by
  obtain ⟨ξ, hξ⟩ := IsAlgClosed.exists_pow_nat_eq ((‖a‖ : ℂ) / a) zero_lt_two
  refine ⟨ξ, ?_, ?_⟩
  · have h := congrArg norm hξ
    rw [norm_pow, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg a),
      div_self (norm_ne_zero_iff.mpr ha)] at h
    nlinarith [norm_nonneg ξ]
  · rw [hξ, mul_div_cancel₀ _ ha]

theorem second {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball 0 1)) (hf0 : f 0 = 1)
    (hW : ∀ z ∈ ball (0 : ℂ) 1, (1 - ‖z‖ ^ 2) * ‖f z‖ ≤ 1) :
    ‖(cauchyPowerSeries f 0 (19 / 20)).coeff 2‖ ≤ 1 := by
  let R : ℝ≥0 := 19/20
  let a := fun k => (cauchyPowerSeries f 0 R).coeff k
  change ‖a 2‖ ≤ 1
  rcases eq_or_ne (a 2) 0 with h | h
  · simp [h]
  obtain ⟨ξ, hξ, hξa⟩ := phase_square _ h
  have hfR : DifferentiableOn ℂ f (closedBall 0 R) := hf.mono
    (closedBall_subset_ball (by norm_num [R]))
  have hR : 0 < R := by norm_num [R]
  have ha0 : a 0 = 1 := (coef_const hR hfR).trans hf0
  have ha1 : a 1 = 0 := (coef_first hR hfR).trans (BlochDistortion.deriv_zero_of_weight hf hf0 hW)
  let C : ℝ := 400/39
  let κ : ℝ := 20/19
  have hlim : Tendsto (fun t : ℝ => 1/(1-t^2) + C*κ^3*t/(1-κ*t)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hc : ContinuousAt (fun t : ℝ => 1/(1-t^2) + C*κ^3*t/(1-κ*t)) 0 := by
      fun_prop (disch := norm_num)
    simpa using hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  apply ge_of_tendsto hlim
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1/2 by norm_num)] with t ⟨ht0, ht1⟩
  let z := ξ * (t : ℂ)
  have hz : ‖z‖ = t := by simp [z, hξ, abs_of_pos ht0]
  have hzr : ‖z‖ < R := by rw [hz]; exact ht1.trans (by norm_num [R])
  have hs := BlochCoefficients.hasSum_coeff f hR hfR hzr
  have hB (k : ℕ) : ‖a k * z^k‖ ≤ C * (κ*t)^k := by
    rw [norm_mul, norm_pow, hz, mul_pow, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (BlochCoefficients.radius95_coeff_bound hf hW k) (pow_nonneg ht0.le k)
  have hp : 0 < 1-κ*t := by norm_num [κ]; linarith
  have ht := BlochTails.truncation hs (by positivity : 0 ≤ κ*t) (sub_pos.mp hp) hB 3
  have he : (∑ k ∈ Finset.range 3, a k * z^k) = 1 + (‖a 2‖ : ℂ)*(t : ℂ)^2 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, ha0, ha1, zero_mul,
      add_zero, pow_zero, mul_one, z, mul_pow, ← mul_assoc, hξa]
  rw [he] at ht
  have htRe := (Complex.abs_re_le_norm _).trans ht
  have hRe : (1 : ℝ) + ‖a 2‖*t^2 ≤ (f z).re + C*(κ*t)^3/(1-κ*t) := by
    have heq : (f z - (1 + (‖a 2‖ : ℂ)*(t : ℂ)^2)).re = (f z).re - (1 + ‖a 2‖*t^2) := by
      rw [Complex.sub_re, Complex.add_re, Complex.one_re, ← Complex.ofReal_pow,
        ← Complex.ofReal_mul, Complex.ofReal_re]
    rw [heq, abs_sub_comm] at htRe
    linarith [ (le_abs_self (1 + ‖a 2‖*t^2 - (f z).re)).trans htRe ]
  have hF := (hW z (mem_ball_zero_iff.mpr (by rw [hz]; linarith)))
  rw [hz] at hF
  have hq : 0 < 1 - t^2 := by nlinarith [mul_pos ht0 (sub_pos.mpr ht1)]
  have hfRe := (Complex.re_le_norm (f z)).trans ((le_div_iff₀ hq).mpr (by simpa [mul_comm] using hF))
  have hh : ‖a 2‖ * t^2 ≤ 1/(1-t^2) + C*(κ*t)^3/(1-κ*t) - 1 := by linarith
  have hid : 1/(1-t^2) + C*(κ*t)^3/(1-κ*t) - 1 =
      (1/(1-t^2) + C*κ^3*t/(1-κ*t))*t^2 := by
    field_simp [hp.ne', hq.ne']
    ring
  rw [hid] at hh
  exact le_of_mul_le_mul_right hh (sq_pos_of_pos ht0)

private theorem coeff_succ {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball 0 1)) (n : ℕ) :
    (cauchyPowerSeries f 0 (19/20)).coeff (n+1) =
      (cauchyPowerSeries (deriv f) 0 (19/20)).coeff n / (n+1 : ℕ) := by
  let R : ℝ≥0 := 19/20
  have hR : 0 < R := by norm_num [R]
  have hr : closedBall (0 : ℂ) R ⊆ ball 0 1 := closedBall_subset_ball (by norm_num [R])
  have h₁ := coeff_eq_iteratedDeriv hR (hf.mono hr) (n+1)
  have h₂ := coeff_eq_iteratedDeriv hR ((hf.deriv isOpen_ball).mono hr) n
  rw [iteratedDeriv_succ', ← h₂, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ] at h₁
  have hn : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hnn : ((n+1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
  change (cauchyPowerSeries f 0 (R : ℝ)).coeff (n+1) =
    (cauchyPowerSeries (deriv f) 0 (R : ℝ)).coeff n / (n+1 : ℕ)
  apply (eq_div_iff hnn).mpr
  apply mul_left_cancel₀ hn
  calc
    _ = ((n : ℂ)+1) * (n.factorial : ℂ) * (cauchyPowerSeries f 0 R).coeff (n+1) := by
      push_cast
      ring
    _ = _ := h₁

end BlochLowCoefficients

namespace UnivalentBlochCoefficients

/-- Second and third coefficients forced by normalization at a maximum of the
weighted derivative. -/
theorem normalized_coefficients {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball 0 1))
    (h₁ : deriv f 0 = 1)
    (hW : ∀ z ∈ ball (0 : ℂ) 1, (1-‖z‖^2)*‖deriv f z‖ ≤ 1) :
    (cauchyPowerSeries f 0 (19/20)).coeff 2 = 0 ∧
      ‖(cauchyPowerSeries f 0 (19/20)).coeff 3‖ ≤ 1/3 := by
  have hf' := hf.deriv isOpen_ball
  have hd := BlochDistortion.deriv_zero_of_weight hf' h₁ hW
  have h₂ := BlochLowCoefficients.second hf' h₁ hW
  constructor
  · rw [BlochLowCoefficients.coeff_succ hf 1]
    have hc : (cauchyPowerSeries (deriv f) 0 (19/20)).coeff 1 = deriv (deriv f) 0 :=
      BlochLowCoefficients.coef_first (R := (19/20 : ℝ≥0)) (by norm_num)
        (hf'.mono (closedBall_subset_ball (by norm_num)))
    rw [hc, hd, zero_div]
  · rw [BlochLowCoefficients.coeff_succ hf 2, norm_div]
    norm_num
    linarith

end UnivalentBlochCoefficients

/- The growth bound from Landau normalization, at the rational radius used for
the bounded-image transform. -/

open Metric Set
open scoped ComplexConjugate

namespace UnivalentBlochGrowth

noncomputable def profile (x : ℝ) : ℝ := (Real.log (1+x)-Real.log (1-x))/2

theorem profile_deriv {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    HasDerivAt profile ((1-x^2)⁻¹) x := by
  have h0 : 1+x ≠ 0 := by positivity
  have h1 : 1-x ≠ 0 := (sub_pos.mpr hx1).ne'
  have hp : 1-x^2 ≠ 0 := (show 0<1-x^2 by nlinarith).ne'
  have hd1 := (Real.hasDerivAt_log h0).comp x ((hasDerivAt_id x).const_add 1)
  have hd2 := (Real.hasDerivAt_log h1).comp x ((hasDerivAt_id x).const_sub 1)
  have hd := (hd1.sub hd2).div_const 2
  have he : (((1+x)⁻¹*1)-((1-x)⁻¹ * (-1)))/2 = (1-x^2)⁻¹ := by
    field_simp [h0, h1, hp]
    ring
  unfold profile
  convert hd using 1 <;> first | rfl | exact he.symm

theorem profile_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) : 0 ≤ profile x := by
  have h := Real.log_le_log (sub_pos.mpr hx1) (show 1-x≤1+x by linarith)
  exact div_nonneg (sub_nonneg.mpr h) zero_le_two

theorem normalized_growth {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball 0 1))
    (hf0 : f 0 = 0) (hW : ∀ z ∈ ball (0 : ℂ) 1, (1-‖z‖^2)*‖deriv f z‖ ≤ 1)
    {z : ℂ} (hz : ‖z‖ < 1) : ‖f z‖ ≤ profile ‖z‖ := by
  by_cases he : f z = 0
  · simpa [he] using profile_nonneg (norm_nonneg z) hz
  have hz0 : z ≠ 0 := fun h => he (h.symm ▸ hf0)
  let r := ‖z‖
  let u := z/(r : ℂ)
  let v := f z/(‖f z‖ : ℂ)
  have rpos : 0 < r := norm_pos_iff.mpr hz0
  have hvpos : 0 < ‖f z‖ := norm_pos_iff.mpr he
  have hu : ‖u‖=1 := by
    dsimp [u]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos rpos, div_self rpos.ne']
  have hv : ‖v‖=1 := by
    dsimp [v]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hvpos, div_self hvpos.ne']
  have huz : (r : ℂ)*u=z := by
    dsimp [u]
    rw [mul_comm, div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr rpos.ne')]
  let l : ℂ → ℂ := fun w => f (w*u)*conj v
  let b : ℝ → ℝ := fun w => profile w - (l w).re
  have hnorm (w : ℝ) (hw : w ∈ Icc 0 r) : ‖(w : ℂ)*u‖ = w := by
    rw [norm_mul, hu, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw.1]
  have hb (w : ℝ) (hw : w ∈ Icc 0 r) : HasDerivAt b
      ((1-w^2)⁻¹-((deriv f ((w : ℂ)*u)*u)*conj v).re) w := by
    have hw1 : w < 1 := hw.2.trans_lt hz
    have hlin : HasDerivAt (fun c : ℂ => c*u) u (w : ℂ) := by
      simpa using (hasDerivAt_id (w : ℂ)).mul_const u
    have hmem : (w : ℂ)*u ∈ ball (0 : ℂ) 1 :=
      mem_ball_zero_iff.mpr (by rwa [hnorm w hw])
    have ha := (hf.differentiableAt (isOpen_ball.mem_nhds hmem)).hasDerivAt
    have hl : HasDerivAt l ((deriv f ((w : ℂ)*u)*u)*conj v) (w : ℂ) := by
      exact (ha.comp (w : ℂ) hlin).mul_const (conj v)
    exact (profile_deriv hw.1 hw1).sub hl.real_of_complex
  have hnonneg (w : ℝ) (hw : w ∈ Icc 0 r) :
      0 ≤ (1-w^2)⁻¹-((deriv f ((w : ℂ)*u)*u)*conj v).re := by
    have hw1 : w < 1 := hw.2.trans_lt hz
    have hmem : (w : ℂ)*u ∈ ball (0 : ℂ) 1 :=
      mem_ball_zero_iff.mpr (by rwa [hnorm w hw])
    have hn := hW _ hmem
    rw [hnorm w hw] at hn
    have hp : 0 < 1-w^2 := by
      nlinarith [mul_pos (sub_pos.mpr hw1) (show 0<1+w by linarith [hw.1])]
    have hbnd : ‖deriv f ((w : ℂ)*u)‖ ≤ (1-w^2)⁻¹ := by
      rw [← one_div, le_div_iff₀ hp, mul_comm]
      exact hn
    have hr := Complex.re_le_norm ((deriv f ((w : ℂ)*u)*u)*conj v)
    rw [norm_mul, norm_mul, hu, Complex.norm_conj, hv, mul_one,mul_one] at hr
    exact sub_nonneg.mpr (hr.trans hbnd)
  have hmono : MonotoneOn b (Icc 0 r) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact fun w hw => (hb w hw).continuousAt.continuousWithinAt
    · exact fun w hw => (hb w (interior_subset hw)).differentiableAt.differentiableWithinAt
    · intro w hw
      rw [(hb w (interior_subset hw)).deriv]
      exact hnonneg w (interior_subset hw)
  have hm := hmono (left_mem_Icc.mpr rpos.le) (right_mem_Icc.mpr rpos.le) rpos.le
  have hconj : v*conj v = 1 := by rw [Complex.mul_conj, ← Complex.sq_norm, hv]; norm_num
  have hvf : f z = (‖f z‖ : ℂ)*v := by
    dsimp [v]
    rw [mul_comm, div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr hvpos.ne')]
  have hrimag : (l (r : ℂ)).re = ‖f z‖ := by
    dsimp [l]
    rw [huz]
    nth_rw 1 [hvf]
    rw [mul_assoc, hconj, mul_one, Complex.ofReal_re]
  have hb0 : b 0 = 0 := by simp [b, l, profile, hf0]
  rw [hb0] at hm
  exact sub_nonneg.mp (by simpa only [b, hrimag] using hm)

theorem fixed_radius_bound {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball 0 1))
    (hf0 : f 0 = 0) (hW : ∀ z ∈ ball (0 : ℂ) 1, (1-‖z‖^2)*‖deriv f z‖ ≤ 1)
    {z : ℂ} (hz : ‖z‖ < 997/1000) : ‖f z‖ < (997/1000)*(10/3) := by
  have ht : (997/1000 : ℝ) < 1 := by norm_num
  have hb := normalized_growth hf hf0 hW (hz.trans ht)
  have hlog₁ : Real.log (1+‖z‖) ≤ Real.log (1+(997/1000 : ℝ)) :=
    Real.log_le_log (by positivity) (by linarith)
  have hlog₂ : Real.log (1-(997/1000 : ℝ)) ≤ Real.log (1-‖z‖) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hpro : profile ‖z‖ ≤ profile (997/1000) := by unfold profile; linarith
  have hN : ((1+(997/1000 : ℝ))/(1-(997/1000 : ℝ))) <
      Real.exp (2*((997/1000)*(10/3))) := by
    refine (show ((1+(997/1000 : ℝ))/(1-(997/1000 : ℝ))) <
      ∑ k ∈ Finset.range 11, (2*((997/1000)*(10/3)))^k/(k.factorial : ℝ) from ?_).trans_le
      (Real.sum_le_exp_of_nonneg (by norm_num) 11)
    norm_num [Finset.sum_range_succ, Nat.factorial_succ]
  have h := Real.log_lt_log (by norm_num : (0 : ℝ) < (1+997/1000)/(1-997/1000)) hN
  rw [Real.log_exp, Real.log_div (by norm_num) (by norm_num)] at h
  apply (hb.trans hpro).trans_lt
  unfold profile
  linarith

end UnivalentBlochGrowth

/-
A scalar reduction for the univalent Bloch bound, using the bounded-image transform
and the translated-disk argument of Wikström (arXiv:2610.34580). The smaller target
radius allows one fixed real supporting parameter. The first Grunsky row is
sufficient for the small cubic case.
-/

open Metric Set
open scoped ComplexConjugate

namespace UnivalentBlochScalar

noncomputable section

def t : ℝ := 997/1000
def q : ℝ := 9/100
def R : ℝ := 571/1000

noncomputable def A (ρ : ℝ) : ℝ := t/ρ + q*ρ/t

def P (x : ℝ) : ℝ := x^3/12 + 5*x^2/4 + 25*x/4 - 25/2 - 2/3

def H : ℝ := (A R + 5)^2/4 * (t/R^2-q/t)

noncomputable def center (a : ℂ) : ℂ :=
  (t^3/H) • (⟨a.re,-3*a.im⟩ : ℂ)

private theorem re_pow_two {ξ : ℂ} (hξ : ‖ξ‖ = 1) :
    (ξ^2).re = 1 - 2*ξ.im^2 := by
  have h : ξ.re^2 + ξ.im^2 = 1 := by
    have hs := Complex.sq_norm ξ
    rw [hξ, Complex.normSq_apply] at hs
    nlinarith
  rw [pow_two, Complex.mul_re]
  nlinarith

private theorem re_cubic_error {ξ a : ℂ} (hξ : ‖ξ‖ = 1) :
    (a*ξ^3).re =
      a.re*ξ.re - 3*a.im*ξ.im - 4*(a*ξ).re*ξ.im^2 := by
  have hs := Complex.sq_norm ξ
  rw [hξ, Complex.normSq_apply] at hs
  simp only [pow_succ, pow_zero, one_mul, Complex.mul_re, Complex.mul_im]
  nlinarith [congrArg (fun x => a.re*ξ.re*x) hs, congrArg (fun x => a.im*ξ.im*x) hs]

private theorem A_tangent {ρ : ℝ} (hρ : 0 < ρ) :
    A R + (R-ρ)*(t/R^2-q/t) ≤ A ρ := by
  have he : A ρ - (A R + (R-ρ)*(t/R^2-q/t)) = t*(R-ρ)^2/(ρ*R^2) := by
    have hR : R ≠ 0 := by norm_num [R]
    have ht : t ≠ 0 := by norm_num [t]
    unfold A
    field_simp [hR, ht, hρ.ne']
    ring
  have hp : 0 ≤ t*(R-ρ)^2/(ρ*R^2) := by unfold t R; positivity
  linarith

private theorem P_tangent {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    P x + (x+5)^2/4*(y-x) ≤ P y := by
  have he : P y - (P x + (x+5)^2/4*(y-x)) = (y-x)^2*(y+2*x+15)/12 := by
    unfold P
    ring
  have hp : (0 : ℝ) ≤ (y-x)^2*(y+2*x+15)/12 := by positivity
  linarith

private theorem P_A_tangent {ρ : ℝ} (hρ : 0 < ρ) :
    P (A R) + (R-ρ)*H ≤ P (A ρ) := by
  have hA : 0 ≤ A ρ := by unfold A t q; positivity
  have hr : 0 ≤ A R := by norm_num [A, R, t, q]
  have hp := P_tangent hr hA
  have ht := A_tangent hρ
  have hh := mul_le_mul_of_nonneg_left ht (show 0 ≤ (A R+5)^2/4 by positivity)
  unfold H
  linarith [hp, hh]

private theorem small_cubic_impossible {s ρ : ℝ} {ξ : ℂ} (hs : 0 ≤ s) (hs' : s ≤ 21/100)
    (hξ : ‖ξ‖=1) (hρ : 0 < ρ) (hρ' : ρ < R)
    (hrow : A ρ^2/4 + 3*‖(((q : ℂ) + ((t^2*s : ℝ) : ℂ)*ξ^2)/2 - ((A ρ^2/8 : ℝ) : ℂ))‖^2
      ≤ 1) : False := by
  have ht := A_tangent hρ
  have hk : 0 < t/R^2-q/t := by norm_num [t, q, R]
  have ha : A R ≤ A ρ := by linarith [mul_pos (sub_pos.mpr hρ') hk]
  have har : 0 ≤ A R := by norm_num [A, R, t, q]
  have hsq : A R^2 ≤ A ρ^2 := pow_le_pow_left₀ har ha _
  let e : ℝ := A R^2/8 - (q+t^2*(21/100))/2
  have he : 0 ≤ e := by norm_num [e, A, R, t, q]
  have hX : (ξ^2).re ≤ 1 := by rw [re_pow_two hξ]; nlinarith [sq_nonneg ξ.im]
  have hMax : t^2*s*(ξ^2).re ≤ t^2*(21/100) := by
    exact (mul_le_of_le_one_right (by positivity) hX).trans
      (mul_le_mul_of_nonneg_left hs' (sq_nonneg t))
  let Q : ℂ := ((q : ℂ) + ((t^2*s : ℝ) : ℂ)*ξ^2)/2 - ((A ρ^2/8 : ℝ) : ℂ)
  have hQ : Q.re = (q + t^2*s*(ξ^2).re)/2 - A ρ^2/8 := by
    have h₂ : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
    dsimp [Q]
    rw [h₂, div_eq_mul_inv, ← Complex.ofReal_inv]
    simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero]
    ring
  have hN : e ≤ ‖Q‖ := by
    have hc := Complex.abs_re_le_norm Q
    have hn := (neg_le_abs Q.re).trans hc
    rw [hQ] at hn
    dsimp only [e]
    linarith
  have hle : 1 < A R^2/4+3*e^2 := by norm_num [e, A, R, t, q]
  have hn₂ := pow_le_pow_left₀ he hN 2
  change A ρ^2/4+3*‖Q‖^2 ≤ 1 at hrow
  linarith

/-- The precise coefficient inequalities needed for the numerical radius. For an
omitted point of direction `ξ` and modulus `ρ`, the first row and the real support
inequality are applied to the bounded-image transform. -/
theorem exists_disjoint_ball (S : Set ℂ) (s : ℝ) (a : ℂ)
    (h0 : 0 ∉ S) (hs : 0 ≤ s) (hs' : s ≤ 1/3) (ha : ‖a‖ ≤ 2/3)
    (hrow : ∀ (ρ : ℝ) (ξ : ℂ), 0 < ρ → ρ < 1 → ‖ξ‖ = 1 → (ρ : ℂ)*ξ ∈ S →
      A ρ^2/4 + 3*‖(((q : ℂ) + ((t^2*s : ℝ) : ℂ)*ξ^2)/2 - ((A ρ^2/8 : ℝ) : ℂ))‖^2 ≤ 1)
    (hsupp : ∀ (ρ : ℝ) (ξ : ℂ), 0 < ρ → ρ < 1 → ‖ξ‖ = 1 → (ρ : ℂ)*ξ ∈ S →
      P (A ρ) ≤ 5*(q+t^2*s*(ξ^2).re)-t^3*(a*ξ^3).re) :
    ∃ c, Disjoint (ball c R) S := by
  have hpolar (w : ℂ) (hw : w ≠ 0) :
      ∃ ξ : ℂ, ‖ξ‖=1 ∧ (‖w‖ : ℂ)*ξ = w := by
    have hp : 0 < ‖w‖ := norm_pos_iff.mpr hw
    refine ⟨w/(‖w‖ : ℂ), ?_, ?_⟩
    · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp, div_self hp.ne']
    · rw [mul_comm, div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr hp.ne')]
  by_cases hsmall : s ≤ 21/100
  · refine ⟨0, Set.disjoint_left.mpr ?_⟩
    intro w hw hS
    have hn : w ≠ 0 := fun he => h0 (he ▸ hS)
    obtain ⟨ξ, hξ, hξe⟩ := hpolar w hn
    have h1 : ‖w‖ < R := mem_ball_zero_iff.mp hw
    have h2 : ‖w‖ < 1 := h1.trans (by norm_num [R])
    exact small_cubic_impossible hs hsmall hξ (norm_pos_iff.mpr hn) h1
      (hrow _ _ (norm_pos_iff.mpr hn) h2 hξ (hξe.symm ▸ hS))
  let c := center a
  have HH : 0 < H := by norm_num [H, A, R, t, q]
  have hN : ‖(⟨a.re,-3*a.im⟩ : ℂ)‖ ≤ 3*‖a‖ := by
    have he : ‖(⟨a.re,-3*a.im⟩ : ℂ)‖^2 = a.re^2+9*a.im^2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      change a.re*a.re+(-3*a.im)*(-3*a.im) = _
      ring
    have ha' := Complex.sq_norm a
    rw [Complex.normSq_apply] at ha'
    nlinarith [norm_nonneg (⟨a.re,-3*a.im⟩ : ℂ), norm_nonneg a, sq_nonneg a.re]
  have hcn : ‖c‖ < 1/10 := by
    have ht : 0 ≤ t^3/H := by unfold t; positivity
    change ‖(t^3/H) • (⟨a.re,-3*a.im⟩ : ℂ)‖ < _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
    have hbound : ‖(⟨a.re,-3*a.im⟩ : ℂ)‖ ≤ 2 := hN.trans (by linarith)
    refine (mul_le_mul_of_nonneg_left hbound ht).trans_lt ?_
    norm_num [H, A, R, t, q]
  refine ⟨c, Set.disjoint_left.mpr ?_⟩
  intro w hw hS
  have hn : w ≠ 0 := fun he => h0 (he ▸ hS)
  obtain ⟨ξ, hξ, hξe⟩ := hpolar w hn
  let ρ := ‖w‖
  have hρ : 0 < ρ := norm_pos_iff.mpr hn
  have hnW : ‖w-c‖ < R := mem_ball_iff_norm.mp hw
  have hρ1 : ρ < 1 := by
    have h := norm_add_le (w-c) c
    rw [sub_add_cancel] at h
    dsimp only [ρ]
    have hr : R+1/10<1 := by norm_num [R]
    linarith
  have hξc : ξ*conj ξ = 1 := by rw [Complex.mul_conj, ← Complex.sq_norm, hξ]; norm_num
  have hrw : (w*conj ξ).re = ρ := by
    rw [← hξe, mul_assoc, hξc, mul_one, Complex.ofReal_re]
  have hcp := Complex.re_le_norm ((w-c)*conj ξ)
  rw [norm_mul, Complex.norm_conj, hξ, mul_one, sub_mul, Complex.sub_re, hrw] at hcp
  have hρlt : ρ < R+(c*conj ξ).re := by linarith
  have sh : H*(c*conj ξ).re = t^3*(a.re*ξ.re-3*a.im*ξ.im) := by
    change H*(((t^3/H) • (⟨a.re,-3*a.im⟩ : ℂ))*conj ξ).re = _
    rw [Complex.real_smul, mul_assoc, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    change H*(t^3/H*(a.re*ξ.re-(-3*a.im)*(-ξ.im))) = _
    field_simp [HH.ne']
  have hta := P_A_tangent hρ
  have hp := mul_lt_mul_of_pos_left hρlt HH
  rw [mul_add, sh] at hp
  have hu := hsupp ρ ξ hρ hρ1 hξ (hξe.symm ▸ hS)
  rw [re_pow_two hξ, re_cubic_error hξ] at hu
  let y := ξ.im^2
  have hy0 : 0 ≤ y := sq_nonneg _
  have hy1 : y ≤ 1 := by
    have hh := Complex.sq_norm_sub_sq_im ξ
    rw [hξ] at hh
    nlinarith [sq_nonneg ξ.re]
  have hC : (a*ξ).re ≤ 2/3 := by
    have hh := Complex.re_le_norm (a*ξ)
    rw [norm_mul, hξ, mul_one] at hh
    exact hh.trans ha
  have hf : P (A R) <
      (1-y)*(5*(q+t^2*s)) + y*(5*(q-t^2*s)+4*t^3*(a*ξ).re) := by
    dsimp only [y]
    linarith [hta, hu, hp]
  have hi0 : 5*(q+t^2*s) ≤ 5*(q+t^2/3) := by nlinarith
  have hi1 : 5*(q-t^2*s)+4*t^3*(a*ξ).re ≤ 5*(q-t^2*(21/100))+4*t^3*(2/3) := by
    have hq := mul_le_mul_of_nonneg_left (le_of_not_ge hsmall) (sq_nonneg t)
    have ht : 0 ≤ t^3 := by norm_num [t]
    have hv := mul_le_mul_of_nonneg_left hC ht
    linarith
  have hd0 : 5*(q+t^2/3) ≤ P (A R) := by norm_num [P, A, R, t, q]
  have hd1 : 5*(q-t^2*(21/100))+4*t^3*(2/3) ≤ P (A R) := by norm_num [P, A, R, t, q]
  have hpos := mul_le_mul_of_nonneg_left (hi0.trans hd0) (sub_nonneg.mpr hy1)
  have hneg := mul_le_mul_of_nonneg_left (hi1.trans hd1) hy0
  linarith


end

end UnivalentBlochScalar

/- Rational operations on the normalized univalent map at an omitted value. -/

open Metric Set Filter FormalMultilinearSeries
open scoped Topology ComplexConjugate

namespace UnivalentBlochTransform

noncomputable def t : ℝ := 997/1000
noncomputable def q : ℝ := 9/100
noncomputable def A (ρ : ℝ) : ℝ := t/ρ + q*ρ/t

noncomputable def scaled (f : ℂ → ℂ) (ξ z : ℂ) : ℂ := f ((t : ℂ)*ξ*z)/((t : ℂ)*ξ)
noncomputable def denom (ρ : ℝ) (g : ℂ) : ℂ := 1 - (A ρ : ℂ)*g + (q : ℂ)*g^2
noncomputable def auxiliary (f : ℂ → ℂ) (ρ : ℝ) (ξ z : ℂ) : ℂ :=
  scaled f ξ z / denom ρ (scaled f ξ z)

private theorem scale_norm {ξ : ℂ} (hξ : ‖ξ‖ = 1) : ‖(t : ℂ)*ξ‖ = t := by
  rw [norm_mul, hξ, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  norm_num [t]

theorem auxiliary_properties {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball 0 1))
    (hI : InjOn f (ball 0 1)) (h0 : f 0 = 0) (h1 : deriv f 0 = 1)
    (hGrowth : ∀ z, ‖z‖ < t → ‖f z‖ < t*(10/3))
    {ρ : ℝ} {ξ : ℂ} (hρ : 0 < ρ) (hρ1 : ρ < 1) (hξ : ‖ξ‖ = 1)
    (hO : (ρ : ℂ)*ξ ∉ f '' ball 0 1) :
    let F := auxiliary f ρ ξ
    DifferentiableOn ℂ F (ball 0 1) ∧ InjOn F (ball 0 1) ∧ F 0 = 0 ∧ deriv F 0 = 1 ∧
      ∀ z ∈ ball (0 : ℂ) 1, (F z)*(denom ρ (scaled f ξ z)) = scaled f ξ z := by
  let α := (t : ℂ)*ξ
  let g := scaled f ξ
  let D := fun z => denom ρ (g z)
  let F := auxiliary f ρ ξ
  have hα : ‖α‖ = t := scale_norm hξ
  have ht : 0 < t := by norm_num [t]
  have ht1 : t < 1 := by norm_num [t]
  have hα0 : α ≠ 0 := norm_pos_iff.mp (hα ▸ ht)
  have hscaled (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) : ‖α*z‖ < t := by
    rw [norm_mul, hα]
    exact mul_lt_of_lt_one_right ht (mem_ball_zero_iff.mp hz)
  have hmaps (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) : α*z ∈ ball (0 : ℂ) 1 :=
    mem_ball_zero_iff.mpr ((hscaled z hz).trans ht1)
  have hg (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) : ‖g z‖ < 10/3 := by
    change ‖f (α*z)/α‖ < _
    rw [norm_div, hα, div_lt_iff₀ ht, mul_comm (10/3 : ℝ) t]
    exact hGrowth _ (hscaled z hz)
  have hD_ne (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) : D z ≠ 0 := by
    have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
    have hqc : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by norm_num [q])
    have hρc : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hρ.ne'
    have hfactors : D z =
        (q : ℂ) * (g z - (ρ : ℂ)/(t : ℂ))*(g z - (t : ℂ)/((q : ℂ)*(ρ : ℂ))) := by
      unfold D denom A
      push_cast
      field_simp [hρc, htc, hqc]
      ring
    intro he
    rw [hfactors, mul_eq_zero, mul_eq_zero, sub_eq_zero, sub_eq_zero] at he
    rcases he with (hqz | hzer) | hbig
    · exact hqc hqz
    · apply hO
      refine ⟨α*z, hmaps z hz, ?_⟩
      have hg_def : g z = f (α*z)/α := rfl
      rw [hg_def, div_eq_iff hα0] at hzer
      calc
        f (α*z) = ((ρ : ℂ)/(t : ℂ))*α := hzer
        _ = (ρ : ℂ)*ξ := by
          dsimp [α]
          field_simp [htc]
    · have hqρ : 0 < q*ρ := mul_pos (by norm_num [q]) hρ
      have hpos : 0 < t/(q*ρ) := div_pos ht hqρ
      have hge : (10/3 : ℝ) ≤ t/(q*ρ) := by
        rw [le_div_iff₀ hqρ]
        unfold q t
        linarith
      have hnorm : ‖g z‖ = t/(q*ρ) := by
        rw [hbig, ← Complex.ofReal_mul, ← Complex.ofReal_div, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hpos]
      linarith [hg z hz]
  have hgI : InjOn g (ball 0 1) := by
    intro x hx y hy he
    change f (α*x)/α = f (α*y)/α at he
    have hk : f (α*x) = f (α*y) := (div_left_inj' hα0).mp he
    exact mul_left_cancel₀ hα0 (hI (hmaps x hx) (hmaps y hy) hk)
  have hFI : InjOn F (ball 0 1) := by
    intro x hx y hy he
    change g x / D x = g y / D y at he
    rw [div_eq_div_iff (hD_ne x hx) (hD_ne y hy)] at he
    have hE : (g x-g y)*(1-(q : ℂ)*g x*g y) = 0 := by
      dsimp [D, denom] at he
      linear_combination he
    have hB : ‖(q : ℂ)*g x*g y‖ < 1 := by
      have hh : ‖g x‖*‖g y‖ < (10/3 : ℝ)*(10/3) :=
        (mul_le_mul_of_nonneg_right (hg x hx).le (norm_nonneg (g y))).trans_lt
          (mul_lt_mul_of_pos_left (hg y hy) (by norm_num))
      have hq : ‖(q : ℂ)‖ = q := by norm_num [q, Complex.norm_real, Real.norm_eq_abs]
      rw [norm_mul, norm_mul, hq, mul_assoc]
      have hp := mul_lt_mul_of_pos_left hh (show 0 < q by norm_num [q])
      exact hp.trans_le (by norm_num [q])
    rcases mul_eq_zero.mp hE with heq | hn
    · exact hgI hx hy (sub_eq_zero.mp heq)
    · have hh : ‖(q : ℂ)*g x*g y‖ = 1 := by rw [← sub_eq_zero.mp hn, norm_one]
      exact False.elim (hB.ne hh)
  have hgD : DifferentiableOn ℂ g (ball 0 1) := by
    have hαD : DifferentiableOn ℂ (fun z : ℂ => α*z) (ball 0 1) :=
      (differentiable_id.const_mul α).differentiableOn
    exact (hf.comp hαD hmaps).div_const α
  have hDD : DifferentiableOn ℂ D (ball 0 1) := by
    unfold D denom
    fun_prop
  have hFD : DifferentiableOn ℂ F (ball 0 1) := hgD.div hDD hD_ne
  have hg0 : g 0 = 0 := by simp [g, scaled, h0]
  have hden0 : D 0 = 1 := by simp [D, denom, hg0]
  have hm : (0 : ℂ) ∈ ball 0 1 := mem_ball_self zero_lt_one
  have hg1 : HasDerivAt g 1 0 := by
    have hl : HasDerivAt (fun z : ℂ => α*z) α 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_mul α
    have hd : HasDerivAt f 1 (α*0) := by
      simpa [h1] using (hf.differentiableAt (isOpen_ball.mem_nhds hm)).hasDerivAt
    have h := (hd.comp (0 : ℂ) hl).div_const α
    change HasDerivAt g (1*α/α) 0 at h
    rwa [one_mul, div_self hα0] at h
  have hF1 : deriv F 0 = 1 := by
    have hd := (hDD.differentiableAt (isOpen_ball.mem_nhds hm)).hasDerivAt
    have h := hg1.div hd (hD_ne 0 hm)
    change HasDerivAt F ((1*D 0 - g 0*deriv D 0)/(D 0)^2) 0 at h
    rw [hden0, hg0] at h
    simpa using h.deriv
  refine ⟨hFD,hFI,?_,hF1,?_⟩
  · change g 0/D 0=0
    simp [hg0]
  · intro z hz
    change g z/D z * D z = g z
    exact div_mul_cancel₀ _ (hD_ne z hz)

end UnivalentBlochTransform

namespace UnivalentBlochReduction

open Metric Set Filter UnivalentBlochTaylor
open scoped Topology

private theorem coefficient_bound (H : UnivalentBlochCompression.ForNormalized) :
    ∀ f : ℂ → ℂ, DifferentiableOn ℂ f (ball 0 1) → InjOn f (ball 0 1) →
      f 0 = 0 → deriv f 0 = 1 →
      UnivalentBlochCompression.Bound (c f 2) ((c f 2)^2 - c f 3)
        (-(c f 2)^3+2*(c f 2)*(c f 3)-c f 4) := by
  intro f hf hi h0 h1
  simpa only [UnivalentBlochCompression.a, cauchy_eq hf] using H f hf hi h0 h1

private theorem omitted_bound (H : UnivalentBlochCompression.ForNormalized)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball 0 1)) (hI : InjOn f (ball 0 1))
    (hf0 : f 0=0) (hf1 : deriv f 0=1)
    (hW : ∀ z ∈ ball (0 : ℂ) 1, (1-‖z‖^2)*‖deriv f z‖≤1)
    {s : ℝ} (hc2 : c f 2=0) (hc3 : c f 3=-(s : ℂ))
    (ρ : ℝ) (ξ : ℂ) (hρ : 0<ρ) (hρ1 : ρ<1) (hξ : ‖ξ‖=1)
    (ho : (ρ : ℂ)*ξ ∉ f '' ball 0 1) :
    let t := UnivalentBlochScalar.t
    let q := UnivalentBlochScalar.q
    let A := UnivalentBlochScalar.A
    (A ρ^2/4 + 3*‖(((q : ℂ) + ((t^2*s : ℝ) : ℂ)*ξ^2)/2 - ((A ρ^2/8 : ℝ) : ℂ))‖^2 ≤ 1) ∧
    UnivalentBlochScalar.P (A ρ) ≤ 5*(q+t^2*s*(ξ^2).re)-t^3*(c f 4*ξ^3).re := by
  let t := UnivalentBlochScalar.t
  let q := UnivalentBlochScalar.q
  let A := UnivalentBlochScalar.A ρ
  let α := (t : ℂ)*ξ
  let F := UnivalentBlochTransform.auxiliary f ρ ξ
  let g := UnivalentBlochTransform.scaled f ξ
  have hB (z : ℂ) (hz : ‖z‖<t) : ‖f z‖<t*(10/3) :=
    UnivalentBlochGrowth.fixed_radius_bound hf hf0 hW hz
  obtain ⟨hFD,hFI,hF0,hF1,hFid⟩ := UnivalentBlochTransform.auxiliary_properties
    hf hI hf0 hf1 hB hρ hρ1 hξ ho
  have hα : ‖α‖=t := by
    rw [show α=(t : ℂ)*ξ by rfl, norm_mul, hξ, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by norm_num [t, UnivalentBlochScalar.t])]
  have hα0 : α ≠ 0 := norm_pos_iff.mp (hα ▸ (show 0<t by norm_num [t, UnivalentBlochScalar.t]))
  have hα1 : ‖α‖ ≤ 1 := by rw [hα]; norm_num [t, UnivalentBlochScalar.t]
  have hG (n : ℕ) (hn : 1≤n) : c g n=α^(n-1)*c f n :=
    scaled_coeff hf hα0 hα1 n hn
  have hg0 : g 0=0 := by simp [g, UnivalentBlochTransform.scaled,hf0]
  have hg1 : deriv g 0=1 := by simpa [hf1] using hG 1 (by decide)
  have hg2 : c g 2=0 := by rw [hG 2 (by decide),hc2,mul_zero]
  have hg3 : q - c g 3 = (q : ℂ) + ((t^2*s : ℝ) : ℂ)*ξ^2 := by
    rw [hG 3 (by decide),hc3]
    simp only [Nat.reduceSub,α]
    push_cast
    ring
  have hg4 : -c g 4 = -((t^3 : ℝ):ℂ)*(c f 4*ξ^3) := by
    rw [hG 4 (by decide)]
    simp only [Nat.reduceSub,α]
    push_cast
    ring
  have hFa : AnalyticAt ℂ F 0 := hFD.analyticOnNhd isOpen_ball 0 (mem_ball_self zero_lt_one)
  have hFne : (fun z => F z*(1-(A : ℂ)*g z+(q : ℂ)*(g z)^2)) =ᶠ[𝓝 0] g := by
    filter_upwards [ball_mem_nhds (0 : ℂ) zero_lt_one] with z hz
    exact hFid z hz
  have hgA : AnalyticAt ℂ g 0 := by
    have hFa0 := hf.analyticOnNhd isOpen_ball 0 (mem_ball_self zero_lt_one)
    have hL : AnalyticAt ℂ (fun z : ℂ => α*z) 0 := by fun_prop
    have hAt : AnalyticAt ℂ f (α*0) := by simpa using hFa0
    exact (hAt.comp hL).div analyticAt_const (show α ≠ 0 from hα0)
  obtain ⟨ha,hQ,hJ⟩ := rational_coeff hgA hFa hg0 hg1 hg2 hF0 hF1 hFne
  have hD := coefficient_bound H F hFD hFI hF0 hF1
  rw [hJ, hQ, ha, hg3, hg4] at hD
  have h1 := UnivalentBlochCompression.first_row hD
  have h2 := UnivalentBlochCompression.support hD
  have hQre : ((q : ℂ)+((t^2*s : ℝ) : ℂ)*ξ^2).re=q+t^2*s*(ξ^2).re := by
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hJre : (-((t^3 : ℝ):ℂ)*(c f 4*ξ^3)).re=-t^3*(c f 4*ξ^3).re := by
    rw [← Complex.ofReal_neg, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
  rw [hQre,hJre] at h2
  refine ⟨h1,?_⟩
  change UnivalentBlochScalar.P A ≤ 5*(q+t^2*s*(ξ^2).re)-t^3*(c f 4*ξ^3).re
  unfold UnivalentBlochScalar.P
  linarith

private theorem normalized_disk (H : UnivalentBlochCompression.ForNormalized)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball 0 1)) (hI : InjOn f (ball 0 1))
    (hf0 : f 0=0) (hf1 : deriv f 0=1)
    (hW : ∀ z ∈ ball (0 : ℂ) 1, (1-‖z‖^2)*‖deriv f z‖≤1) :
    ∃ x, ball x UnivalentBlochScalar.R ⊆ f '' (ball 0 1) := by
  obtain ⟨hf2,hf3⟩ := UnivalentBlochCoefficients.normalized_coefficients hf hf1 hW
  rw [cauchy_eq hf] at hf2 hf3
  let s := ‖c f 3‖
  obtain ⟨η,hη,hηa⟩ : ∃ η : ℂ, ‖η‖=1 ∧ η^2*c f 3=-(s : ℂ) := by
    by_cases h : c f 3=0
    · use 1
      simp [s,h]
    have hs : 0<s := norm_pos_iff.mpr h
    obtain ⟨η,he⟩ := IsAlgClosed.exists_pow_nat_eq (-(s : ℂ)/(c f 3)) zero_lt_two
    have hη := congrArg norm he
    rw [norm_pow,norm_div,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hs] at hη
    change ‖η‖^2=s/s at hη
    rw [div_self hs.ne'] at hη
    have hη' : ‖η‖=1 := by
      have hp := sq_eq_sq_iff_eq_or_eq_neg.mp (show ‖η‖^2=(1 : ℝ)^2 by simpa using hη)
      rcases hp with hp | hp
      · exact hp
      · linarith [norm_nonneg η]
    exact ⟨η,hη',(eq_div_iff h).mp he⟩
  have hηn : η ≠ 0 := by
    intro he
    rw [he,norm_zero] at hη
    norm_num at hη
  let g := fun z : ℂ => f (η*z)/η
  have hM : MapsTo (fun z : ℂ => η*z) (ball 0 1) (ball 0 1) := by
    intro z hz
    simpa [mem_ball_zero_iff, norm_mul, hη] using hz
  have hgD : DifferentiableOn ℂ g (ball 0 1) :=
    (hf.comp ((differentiable_id.const_mul η).differentiableOn) hM).div_const η
  have hgI : InjOn g (ball 0 1) := by
    intro z hz w hw he
    change f (η*z)/η = f (η*w)/η at he
    exact mul_left_cancel₀ hηn (hI (hM hz) (hM hw) ((div_left_inj' hηn).mp he))
  have hg0 : g 0=0 := by simp [g,hf0]
  have hgDer (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) : deriv g z=deriv f (η*z) := by
    have hL : HasDerivAt (fun z : ℂ => η*z) η z := by
      simpa using (hasDerivAt_id z).const_mul η
    have hD := (hf.differentiableAt (isOpen_ball.mem_nhds (hM hz))).hasDerivAt
    have he := ((hD.comp z hL).div_const η).deriv
    change deriv g z = (deriv f (η*z)*η)/η at he
    simpa [mul_div_cancel_right₀ _ hηn] using he
  have hg1 : deriv g 0=1 := by rw [hgDer 0 (mem_ball_self zero_lt_one),mul_zero,hf1]
  have hgW (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) : (1-‖z‖^2)*‖deriv g z‖≤1 := by
    rw [hgDer z hz]
    simpa only [norm_mul,hη,one_mul] using hW (η*z) (hM hz)
  have hg2 : c g 2 = 0 := by
    rw [show c g 2 = η^(2-1:ℕ)*c f 2 from scaled_coeff hf hηn hη.le 2 (by decide),hf2,mul_zero]
  have hg3 : c g 3 = -(s : ℂ) := by
    rw [show c g 3=η^2*c f 3 from scaled_coeff hf hηn hη.le 3 (by decide),hηa]
  have hb := coefficient_bound H g hgD hgI hg0 hg1
  have hba : UnivalentBlochCompression.Bound 0 (-c g 3) (-c g 4) := by
    simpa [hg2] using hb
  have ha := UnivalentBlochCompression.fourth hba
  rw [norm_neg] at ha
  let S : Set ℂ := (g '' (ball 0 1))ᶜ
  have hS0 : (0 : ℂ) ∉ S := by
    change ¬ (0 : ℂ) ∉ g '' ball 0 1
    exact not_not_intro ⟨0,mem_ball_self zero_lt_one,hg0⟩
  have hO (ρ : ℝ) (ξ : ℂ) (hρ : 0<ρ) (hρ1 : ρ<1) (hξ : ‖ξ‖=1) (ho : (ρ : ℂ)*ξ ∈ S) :=
    omitted_bound H hgD hgI hg0 hg1 hgW hg2 hg3 ρ ξ hρ hρ1 hξ ho
  obtain ⟨x,hx⟩ := UnivalentBlochScalar.exists_disjoint_ball S s (c g 4)
    hS0 (norm_nonneg _) hf3 ha (fun ρ ξ hρ hρ1 hξ hS => (hO ρ ξ hρ hρ1 hξ hS).1)
    (fun ρ ξ hρ hρ1 hξ hS => (hO ρ ξ hρ hρ1 hξ hS).2)
  have hsub : ball x UnivalentBlochScalar.R ⊆ g '' ball 0 1 := by
    intro y hy
    by_contra ho
    exact Set.disjoint_left.mp hx hy ho
  refine ⟨η*x, ?_⟩
  intro w hw
  have hdiv : w/η-x=(w-η*x)/η := by field_simp [hηn]
  have hw' : w/η ∈ ball x UnivalentBlochScalar.R := by
    rw [mem_ball_iff_norm, hdiv,norm_div,hη,div_one]
    exact mem_ball_iff_norm.mp hw
  obtain ⟨z,hz,he⟩ := hsub hw'
  exact ⟨η*z, hM hz, (div_left_inj' hηn).mp he⟩

/-- The target lower bound follows from the two odd Grunsky modes. -/
theorem of_compression (H : UnivalentBlochCompression.ForNormalized) :
    0.5708858 ≤ Bloch.univalentBlochConstant := by
  apply UnivalentBlochNormalization.normalized_reduction (R := UnivalentBlochScalar.R)
    (by norm_num) (by norm_num [UnivalentBlochScalar.R])
  intro f hi hf h0 h1 hW
  obtain ⟨x,hx⟩ := normalized_disk H hf hi h0 h1 hW
  exact UnivalentBlochNormalization.covers_of_ball_subset hf hi hx

end UnivalentBlochReduction

/-- The lower bound follows from the geometric weighted boundary positivity. -/
theorem UnivalentBlochReduction.of_positive (H : UnivalentBlochFlux.Positive) :
    0.5708858 ≤ Bloch.univalentBlochConstant :=
  UnivalentBlochReduction.of_compression (UnivalentBlochFlux.compression_of_positive H)

end

theorem OMA.solution : type_of% @Bloch.univalentBlochConstant_lower_bound :=
  UnivalentBlochReduction.of_positive
    (UnivalentBlochFlux.positive_of_exterior GrunskyPositive.exterior_positive)