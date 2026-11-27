import FormalConjectures.ErdosProblems.«980»
import Mathlib

section kitPNT
/-!
# Prime Number Theorem kit (namespace `OMAPNT`), self-contained, pinned Mathlib

Route: Newman's analytic theorem (Zagier's version) in Mellin form, with the contour replaced by
rectangles, so only Mathlib's Cauchy-Goursat for rectangles is needed.

* `RI_pole`: rectangle Cauchy formula `∮ H(z)/z dz = 2πi H(0)` for `[-a,c]×[-b,b]`, `0<a≤c`.
* `newman` / `newman_real`: if `a` is bounded measurable on `[1,∞)` and `∫_1^∞ a(x)x^{-z-1}dx`
  extends holomorphically to an open set containing `Re z ≥ 0`, then `∫_1^X a(x)/x dx` converges.
* `taub`: monotone `S` with convergent `∫_1^X (S(x)/x - c)/x dx` has `S(x)/x → c`.
* `tendsto_psiAP`: PNT in arithmetic progressions, `ψ(x;q,b)/x → 1/φ(q)` for `b` a unit
  (input: Mathlib's `LFunctionResidueClassAux` and non-vanishing of Dirichlet L-functions).
* `tendsto_psi_div`, `tendsto_theta_div`, `tendsto_primeCounting_div`,
  `primeCounting_isEquivalent`, `tendsto_primeCounting_nat`: the PNT.
-/

open Complex MeasureTheory Filter Topology Set Asymptotics
open scoped Interval

namespace OMAPNT

/-! ## Rectangle integrals -/

/-- Boundary integral of `f` over the rectangle `[x0,x1] × [y0,y1]` (counterclockwise). -/
noncomputable def RI (f : ℂ → ℂ) (x0 x1 y0 y1 : ℝ) : ℂ :=
  (∫ x : ℝ in x0..x1, f (x + y0 * I)) - (∫ x : ℝ in x0..x1, f (x + y1 * I)) +
    I * (∫ y : ℝ in y0..y1, f (x1 + y * I)) - I * (∫ y : ℝ in y0..y1, f (x0 + y * I))

theorem RI_eq_zero {f : ℂ → ℂ} {x0 x1 y0 y1 : ℝ}
    (H : DifferentiableOn ℂ f ([[x0, x1]] ×ℂ [[y0, y1]])) : RI f x0 x1 y0 y1 = 0 := by
  have := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f (x0 + y0 * I)
    (x1 + y1 * I) (by simpa using H)
  simpa [RI, smul_eq_mul] using this

theorem integral_b_div_sq_add_sq {a b : ℝ} (hb : 0 < b) :
    ∫ x : ℝ in (-a)..a, b / (x ^ 2 + b ^ 2) = 2 * Real.arctan (a / b) := by
  have hd : ∀ x ∈ [[-a, a]], HasDerivAt (fun x => Real.arctan (x / b)) (b / (x ^ 2 + b ^ 2)) x := by
    intro x _
    have h1 := (Real.hasDerivAt_arctan (x / b)).comp x ((hasDerivAt_id x).div_const b)
    have hb' : b ≠ 0 := hb.ne'
    have h2 : (1 / (1 + (x / b) ^ 2) * (1 / b)) = b / (x ^ 2 + b ^ 2) := by
      field_simp; ring
    rw [h2] at h1; exact h1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd]
  · simp [neg_div, Real.arctan_neg]; ring
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro x _; positivity

theorem inv_sub_inv_horiz (x b : ℝ) (hb : 0 < b) :
    ((x : ℂ) + (-b : ℝ) * I)⁻¹ - ((x : ℂ) + b * I)⁻¹ = 2 * I * ((b / (x ^ 2 + b ^ 2) : ℝ) : ℂ) := by
  have h1 : ((x : ℂ) + (-b : ℝ) * I) ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; linarith
  have h2 : ((x : ℂ) + b * I) ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; linarith
  have h3 : ((x : ℂ) ^ 2 + (b : ℂ) ^ 2) ≠ 0 := by
    have : (0 : ℝ) < x ^ 2 + b ^ 2 := by positivity
    exact_mod_cast this.ne'
  have hp : ((x : ℂ) + (-b : ℝ) * I) * ((x : ℂ) + b * I) = (x : ℂ) ^ 2 + (b : ℂ) ^ 2 := by
    push_cast; ring_nf; rw [I_sq]; ring
  rw [inv_sub_inv h1 h2, hp, div_eq_iff h3]
  push_cast
  field_simp
  ring

theorem inv_sub_inv_vert (y a : ℝ) (ha : 0 < a) :
    I * ((a : ℂ) + y * I)⁻¹ - I * (((-a : ℝ) : ℂ) + y * I)⁻¹ =
      2 * I * ((a / (y ^ 2 + a ^ 2) : ℝ) : ℂ) := by
  have h1 : ((a : ℂ) + y * I) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have h2 : (((-a : ℝ) : ℂ) + y * I) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have h3 : ((y : ℂ) ^ 2 + (a : ℂ) ^ 2) ≠ 0 := by
    have : (0 : ℝ) < y ^ 2 + a ^ 2 := by positivity
    exact_mod_cast this.ne'
  have hp : ((a : ℂ) + y * I) * (((-a : ℝ) : ℂ) + y * I) = -((y : ℂ) ^ 2 + (a : ℂ) ^ 2) := by
    push_cast; ring_nf; rw [I_sq]; ring
  rw [← mul_sub, inv_sub_inv h1 h2, hp]
  push_cast
  field_simp
  ring

theorem ii_inv_horiz {c : ℝ} (hc : c ≠ 0) (x0 x1 : ℝ) :
    IntervalIntegrable (fun x : ℝ => ((x : ℂ) + c * I)⁻¹) volume x0 x1 := by
  apply Continuous.intervalIntegrable
  exact Continuous.inv₀ (by fun_prop) (fun x h => by
    have := congrArg Complex.im h; simp at this; exact hc this)

theorem ii_inv_vert {c : ℝ} (hc : c ≠ 0) (y0 y1 : ℝ) :
    IntervalIntegrable (fun y : ℝ => ((c : ℂ) + y * I)⁻¹) volume y0 y1 := by
  apply Continuous.intervalIntegrable
  exact Continuous.inv₀ (by fun_prop) (fun x h => by
    have := congrArg Complex.re h; simp at this; exact hc this)

theorem RI_inv_sym {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    RI (fun z => z⁻¹) (-a) a (-b) b = 2 * Real.pi * I := by
  unfold RI
  have e1 : (∫ x : ℝ in (-a)..a, ((x : ℂ) + ((-b : ℝ) : ℂ) * I)⁻¹) -
      (∫ x : ℝ in (-a)..a, ((x : ℂ) + (b : ℂ) * I)⁻¹)
      = 2 * I * (((2 * Real.arctan (a / b)) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_sub (ii_inv_horiz (by linarith) _ _)
      (ii_inv_horiz hb.ne' _ _)]
    simp_rw [inv_sub_inv_horiz _ _ hb]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
      integral_b_div_sq_add_sq hb]
  have e2 : I * (∫ y : ℝ in (-b)..b, ((a : ℂ) + y * I)⁻¹) -
      I * (∫ y : ℝ in (-b)..b, (((-a : ℝ) : ℂ) + y * I)⁻¹)
      = 2 * I * (((2 * Real.arctan (b / a)) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub ((ii_inv_vert ha.ne' _ _).const_mul _)
        ((ii_inv_vert (by linarith) _ _).const_mul _)]
    simp_rw [inv_sub_inv_vert _ _ ha]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
      integral_b_div_sq_add_sq ha]
  have hsplit : ∀ p q r t : ℂ, p - q + r - t = (p - q) + (r - t) := fun _ _ _ _ => by ring
  rw [hsplit, e1, e2]
  have hab : b / a = (a / b)⁻¹ := by rw [inv_div]
  rw [hab, Real.arctan_inv_of_pos (div_pos ha hb)]
  push_cast
  ring

/-- Integrability of `f` on the four sides of a rectangle. -/
def RIable (f : ℂ → ℂ) (x0 x1 y0 y1 : ℝ) : Prop :=
  IntervalIntegrable (fun x : ℝ => f (x + y0 * I)) volume x0 x1 ∧
  IntervalIntegrable (fun x : ℝ => f (x + y1 * I)) volume x0 x1 ∧
  IntervalIntegrable (fun y : ℝ => f (x1 + y * I)) volume y0 y1 ∧
  IntervalIntegrable (fun y : ℝ => f (x0 + y * I)) volume y0 y1

theorem RIable_of_contOn {f : ℂ → ℂ} {x0 x1 y0 y1 : ℝ}
    (hf : ContinuousOn f ([[x0, x1]] ×ℂ [[y0, y1]] \ {0}))
    (hx0 : x0 ≠ 0) (hx1 : x1 ≠ 0) (hy0 : y0 ≠ 0) (hy1 : y1 ≠ 0) : RIable f x0 x1 y0 y1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply ContinuousOn.intervalIntegrable <;>
    refine hf.comp (Continuous.continuousOn (by fun_prop)) ?_ <;> intro t ht <;>
    simp only [Set.mem_sdiff, mem_reProdIm, mem_singleton_iff] <;>
    refine ⟨⟨by simp [ht], by simp [ht]⟩, fun h => ?_⟩ <;>
    first
    | (have := congrArg Complex.im h; simp at this; tauto)
    | (have := congrArg Complex.re h; simp at this; tauto)

theorem RI_add {f g : ℂ → ℂ} {x0 x1 y0 y1 : ℝ} (hf : RIable f x0 x1 y0 y1)
    (hg : RIable g x0 x1 y0 y1) :
    RI (fun z => f z + g z) x0 x1 y0 y1 = RI f x0 x1 y0 y1 + RI g x0 x1 y0 y1 := by
  unfold RI
  rw [intervalIntegral.integral_add hf.1 hg.1, intervalIntegral.integral_add hf.2.1 hg.2.1,
    intervalIntegral.integral_add hf.2.2.1 hg.2.2.1, intervalIntegral.integral_add hf.2.2.2 hg.2.2.2]
  ring

theorem RI_sub {f g : ℂ → ℂ} {x0 x1 y0 y1 : ℝ} (hf : RIable f x0 x1 y0 y1)
    (hg : RIable g x0 x1 y0 y1) :
    RI (fun z => f z - g z) x0 x1 y0 y1 = RI f x0 x1 y0 y1 - RI g x0 x1 y0 y1 := by
  unfold RI
  rw [intervalIntegral.integral_sub hf.1 hg.1, intervalIntegral.integral_sub hf.2.1 hg.2.1,
    intervalIntegral.integral_sub hf.2.2.1 hg.2.2.1, intervalIntegral.integral_sub hf.2.2.2 hg.2.2.2]
  ring

theorem RI_const_mul (k : ℂ) (f : ℂ → ℂ) (x0 x1 y0 y1 : ℝ) :
    RI (fun z => k * f z) x0 x1 y0 y1 = k * RI f x0 x1 y0 y1 := by
  unfold RI
  simp only [intervalIntegral.integral_const_mul]
  ring

theorem RI_congr {f g : ℂ → ℂ} {x0 x1 y0 y1 : ℝ} (h : ∀ z, z ≠ 0 → f z = g z)
    (hx0 : x0 ≠ 0) (hx1 : x1 ≠ 0) (hy0 : y0 ≠ 0) (hy1 : y1 ≠ 0) :
    RI f x0 x1 y0 y1 = RI g x0 x1 y0 y1 := by
  unfold RI
  have e1 : ∀ c : ℝ, c ≠ 0 → ∀ x : ℝ, f (x + c * I) = g (x + c * I) := fun c hc x =>
    h _ (fun h' => by have := congrArg Complex.im h'; simp at this; exact hc this)
  have e2 : ∀ c : ℝ, c ≠ 0 → ∀ y : ℝ, f (c + y * I) = g (c + y * I) := fun c hc y =>
    h _ (fun h' => by have := congrArg Complex.re h'; simp at this; exact hc this)
  simp only [e1 _ hy0, e1 _ hy1, e2 _ hx0, e2 _ hx1]

theorem RI_split {f : ℂ → ℂ} {x0 m x1 y0 y1 : ℝ}
    (h1 : IntervalIntegrable (fun x : ℝ => f (x + y0 * I)) volume x0 m)
    (h2 : IntervalIntegrable (fun x : ℝ => f (x + y0 * I)) volume m x1)
    (h3 : IntervalIntegrable (fun x : ℝ => f (x + y1 * I)) volume x0 m)
    (h4 : IntervalIntegrable (fun x : ℝ => f (x + y1 * I)) volume m x1) :
    RI f x0 x1 y0 y1 = RI f x0 m y0 y1 + RI f m x1 y0 y1 := by
  unfold RI
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2,
    ← intervalIntegral.integral_add_adjacent_intervals h3 h4]
  ring

theorem RI_inv {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hac : a ≤ c) :
    RI (fun z => z⁻¹) (-a) c (-b) b = 2 * Real.pi * I := by
  rw [RI_split (m := a) (ii_inv_horiz (by simp; linarith) _ _) (ii_inv_horiz (by simp; linarith) _ _)
    (ii_inv_horiz hb.ne' _ _) (ii_inv_horiz hb.ne' _ _), RI_inv_sym ha hb, RI_eq_zero, add_zero]
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  apply differentiableAt_inv
  intro h
  rw [mem_reProdIm, h] at hz
  simp [uIcc_of_le hac] at hz
  linarith [hz.1]

theorem RI_pole {H : ℂ → ℂ} {V : Set ℂ} {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hac : a ≤ c)
    (hV : IsOpen V) (hR : [[-a, c]] ×ℂ [[-b, b]] ⊆ V) (hH : DifferentiableOn ℂ H V) :
    RI (fun z => H z / z) (-a) c (-b) b = 2 * Real.pi * I * H 0 := by
  have h0 : (0 : ℂ) ∈ V := hR (by
    simp only [mem_reProdIm, zero_re, zero_im]
    exact ⟨mem_uIcc.mpr (Or.inl ⟨by linarith, by linarith⟩),
      mem_uIcc.mpr (Or.inl ⟨by linarith, by linarith⟩)⟩)
  have hg : DifferentiableOn ℂ (dslope H 0) V :=
    (differentiableOn_dslope (hV.mem_nhds h0)).mpr hH
  have hx0 : (-a) ≠ 0 := by linarith
  have hx1 : c ≠ 0 := by linarith
  have hy0 : (-b) ≠ 0 := by linarith
  have hy1 : b ≠ 0 := by linarith
  have hcongr : RI (fun z => H z / z) (-a) c (-b) b =
      RI (fun z => dslope H 0 z + H 0 * z⁻¹) (-a) c (-b) b := by
    apply RI_congr _ hx0 hx1 hy0 hy1
    intro z hz
    rw [dslope_of_ne _ hz, slope_def_field]
    field_simp
    ring
  have hgc : ContinuousOn (dslope H 0) ([[-a, c]] ×ℂ [[-b, b]] \ {0}) :=
    hg.continuousOn.mono (sdiff_subset.trans hR)
  have hic : ContinuousOn (fun z : ℂ => H 0 * z⁻¹) ([[-a, c]] ×ℂ [[-b, b]] \ {0}) := by
    apply ContinuousOn.mul continuousOn_const
    exact continuousOn_inv₀.mono (fun z hz => hz.2)
  rw [hcongr, RI_add (RIable_of_contOn hgc hx0 hx1 hy0 hy1) (RIable_of_contOn hic hx0 hx1 hy0 hy1),
    RI_const_mul, RI_inv ha hb hac, RI_eq_zero (hg.mono hR)]
  ring

/-! ## Newman's analytic theorem, Mellin form -/

/-- Truncated Mellin transform `∫_1^X a(x) x^{-z-1} dx`. -/
noncomputable def GX (a : ℝ → ℝ) (X : ℝ) (z : ℂ) : ℂ :=
  ∫ x in (1 : ℝ)..X, (a x : ℂ) * (x : ℂ) ^ (-z - 1)

/-- Mellin transform `∫_1^∞ a(x) x^{-z-1} dx`. -/
noncomputable def Gint (a : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ x in Ioi (1 : ℝ), (a x : ℂ) * (x : ℂ) ^ (-z - 1)

section analytic

variable {a : ℝ → ℝ} {B : ℝ}

theorem norm_integrand_le (hbd : ∀ x, 1 ≤ x → |a x| ≤ B) (z : ℂ) {x : ℝ} (hx : 1 ≤ x) :
    ‖(a x : ℂ) * (x : ℂ) ^ (-z - 1)‖ ≤ B * x ^ (-z.re - 1) := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_cpow_eq_rpow_re_of_pos (by linarith)]
  simp only [sub_re, neg_re, one_re]
  exact mul_le_mul_of_nonneg_right (hbd x hx) (Real.rpow_nonneg (by linarith) _)

theorem aesm_integrand (hmeas : Measurable a) (z : ℂ) (μ : Measure ℝ) :
    AEStronglyMeasurable (fun x : ℝ => (a x : ℂ) * (x : ℂ) ^ (-z - 1)) μ := by
  apply Measurable.aestronglyMeasurable
  exact (Complex.measurable_ofReal.comp hmeas).mul (Complex.measurable_ofReal.pow_const _)

theorem integrableOn_integrand (hmeas : Measurable a) (hbd : ∀ x, 1 ≤ x → |a x| ≤ B)
    {z : ℂ} (hz : 0 < z.re) {c : ℝ} (hc : 1 ≤ c) :
    IntegrableOn (fun x : ℝ => (a x : ℂ) * (x : ℂ) ^ (-z - 1)) (Ioi c) := by
  refine Integrable.mono'
    ((integrableOn_Ioi_rpow_of_lt (by linarith : -z.re - 1 < -1) (by linarith)).const_mul B)
    (aesm_integrand hmeas z _) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_)
  exact norm_integrand_le hbd z (le_trans hc (le_of_lt hx))

theorem tail_eq (hmeas : Measurable a) (hbd : ∀ x, 1 ≤ x → |a x| ≤ B)
    {z : ℂ} (hz : 0 < z.re) {X : ℝ} (hX : 1 ≤ X) :
    Gint a z - GX a X z = ∫ x in Ioi X, (a x : ℂ) * (x : ℂ) ^ (-z - 1) := by
  unfold Gint GX
  rw [intervalIntegral.integral_of_le hX, ← Ioc_union_Ioi_eq_Ioi hX,
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      ((integrableOn_integrand hmeas hbd hz le_rfl).mono_set Ioc_subset_Ioi_self)
      (integrableOn_integrand hmeas hbd hz hX)]
  ring

theorem tail_bound (hmeas : Measurable a) (hbd : ∀ x, 1 ≤ x → |a x| ≤ B)
    {z : ℂ} (hz : 0 < z.re) {X : ℝ} (hX : 1 ≤ X) :
    ‖Gint a z - GX a X z‖ ≤ B * (X ^ (-z.re) / z.re) := by
  rw [tail_eq hmeas hbd hz hX]
  have hint := (integrableOn_Ioi_rpow_of_lt (by linarith : -z.re - 1 < -1)
    (by linarith : (0 : ℝ) < X)).const_mul B
  calc _ ≤ ∫ x in Ioi X, B * x ^ (-z.re - 1) := by
        refine norm_integral_le_of_norm_le hint ?_
        refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_)
        exact norm_integrand_le hbd z (le_trans hX (le_of_lt hx))
    _ = B * (X ^ (-z.re) / z.re) := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) (by linarith)]
        congr 1
        rw [show -z.re - 1 + 1 = -z.re by ring, neg_div, div_neg, neg_neg]

theorem head_bound (hbd : ∀ x, 1 ≤ x → |a x| ≤ B)
    {z : ℂ} (hz : z.re < 0) {X : ℝ} (hX : 1 ≤ X) :
    ‖GX a X z‖ ≤ B * (X ^ (-z.re) / (-z.re)) := by
  have hB : 0 ≤ B := le_trans (abs_nonneg _) (hbd 1 le_rfl)
  have h0 : (0 : ℝ) ∉ [[1, X]] := by
    rw [uIcc_of_le hX]; intro h; linarith [h.1]
  unfold GX
  calc _ ≤ ∫ x in (1 : ℝ)..X, B * x ^ (-z.re - 1) := by
        refine intervalIntegral.norm_integral_le_of_norm_le hX
          (Eventually.of_forall fun x hx => norm_integrand_le hbd z (le_of_lt hx.1)) ?_
        exact (intervalIntegral.intervalIntegrable_rpow (Or.inr h0)).const_mul B
    _ = B * ((X ^ (-z.re) - 1) / (-z.re)) := by
        rw [intervalIntegral.integral_const_mul,
          integral_rpow (Or.inr ⟨by intro h; linarith, h0⟩)]
        congr 1
        rw [show -z.re - 1 + 1 = -z.re by ring, Real.one_rpow]
    _ ≤ B * (X ^ (-z.re) / (-z.re)) := by
        apply mul_le_mul_of_nonneg_left _ hB
        apply div_le_div_of_nonneg_right _ (by linarith)
        linarith

theorem rpow_neg_mul_exp {X σ : ℝ} (hX : 0 < X) :
    X ^ (-σ) * Real.exp (σ * Real.log X) = 1 := by
  rw [Real.rpow_def_of_pos hX, ← Real.exp_add]
  simp only [mul_neg, Real.exp_eq_one_iff]
  ring

theorem tail_bound_exp (hmeas : Measurable a) (hbd : ∀ x, 1 ≤ x → |a x| ≤ B)
    {z : ℂ} (hz : 0 < z.re) {X : ℝ} (hX : 1 ≤ X) :
    ‖Gint a z - GX a X z‖ * Real.exp (z.re * Real.log X) ≤ B / z.re := by
  have h := mul_le_mul_of_nonneg_right (tail_bound hmeas hbd hz hX)
    (Real.exp_pos (z.re * Real.log X)).le
  calc _ ≤ _ := h
    _ = B / z.re * (X ^ (-z.re) * Real.exp (z.re * Real.log X)) := by ring
    _ = B / z.re := by rw [rpow_neg_mul_exp (by linarith), mul_one]

theorem head_bound_exp (hbd : ∀ x, 1 ≤ x → |a x| ≤ B)
    {z : ℂ} (hz : z.re < 0) {X : ℝ} (hX : 1 ≤ X) :
    ‖GX a X z‖ * Real.exp (z.re * Real.log X) ≤ B / (-z.re) := by
  have h := mul_le_mul_of_nonneg_right (head_bound hbd hz hX)
    (Real.exp_pos (z.re * Real.log X)).le
  calc _ ≤ _ := h
    _ = B / (-z.re) * (X ^ (-z.re) * Real.exp (z.re * Real.log X)) := by ring
    _ = B / (-z.re) := by rw [rpow_neg_mul_exp (by linarith), mul_one]

theorem GX_differentiable (hmeas : Measurable a) (hbd : ∀ x, 1 ≤ x → |a x| ≤ B)
    {X : ℝ} (hX : 1 ≤ X) : Differentiable ℂ (GX a X) := by
  set f : ℝ → ℂ := (Ioc 1 X).indicator (fun t => (a t : ℂ)) with hf
  have hfe : ∀ z, GX a X z = mellin f (-z) := by
    intro z
    unfold GX mellin
    rw [intervalIntegral.integral_of_le hX]
    have : ∀ t : ℝ, (t : ℂ) ^ (-z - 1) • f t =
        (Ioc 1 X).indicator (fun t => (a t : ℂ) * (t : ℂ) ^ (-z - 1)) t := by
      intro t; by_cases ht : t ∈ Ioc 1 X <;> simp [f, ht, mul_comm]
    simp_rw [this]
    rw [setIntegral_indicator measurableSet_Ioc]
    have hsub : Ioi (0 : ℝ) ∩ Ioc 1 X = Ioc 1 X := inter_eq_right.mpr
      (fun t (ht : t ∈ Ioc 1 X) => show t ∈ Ioi (0 : ℝ) from by simp only [mem_Ioi]; linarith [ht.1])
    rw [hsub]
  have hfeq : GX a X = fun z => mellin f (-z) := funext hfe
  rw [hfeq]
  intro z
  have hm : DifferentiableAt ℂ (mellin f) (-z) := by
    refine mellin_differentiableAt_of_isBigO_rpow (a := -z.re + 1) (b := -z.re - 1) ?_ ?_ ?_ ?_ ?_
    · refine LocallyIntegrable.locallyIntegrableOn (Integrable.locallyIntegrable ?_) _
      rw [hf, integrable_indicator_iff measurableSet_Ioc]
      refine Measure.integrableOn_of_bounded (M := B) (by simp [Real.volume_Ioc])
        (Complex.measurable_ofReal.comp hmeas).aestronglyMeasurable ?_
      refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun x hx => ?_)
      simpa using hbd x (le_of_lt hx.1)
    · refine (isBigO_zero _ _).congr' ?_ EventuallyEq.rfl
      filter_upwards [eventually_gt_atTop X] with t ht
      simp [f, ht.not_ge]
    · simp
    · refine (isBigO_zero _ _).congr' ?_ EventuallyEq.rfl
      filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
      have : t ∉ Ioc 1 X := fun h => by linarith [h.1, ht.2]
      simp [f, this]
    · simp

  exact hm.comp z differentiableAt_id.neg

end analytic

/-! ## Kernel estimates -/

/-- Newman's kernel numerator `X^z (1 + z^2/R^2)` with `L = log X`. -/
noncomputable def KN (L R : ℝ) (z : ℂ) : ℂ := Complex.exp (z * L) * (1 + z ^ 2 / (R : ℂ) ^ 2)

theorem KN_zero (L R : ℝ) : KN L R 0 = 1 := by simp [KN]

theorem KN_differentiable (L R : ℝ) : Differentiable ℂ (KN L R) := by
  unfold KN; fun_prop

theorem norm_PK (P z : ℂ) (L R : ℝ) :
    ‖P * KN L R z / z‖ = ‖P‖ * Real.exp (z.re * L) * ‖1 + z ^ 2 / (R : ℂ) ^ 2‖ / ‖z‖ := by
  unfold KN
  rw [norm_div, norm_mul, norm_mul, Complex.norm_exp]
  simp only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
  ring

theorem pt_gen {P z : ℂ} {L R c d e : ℝ} (hP : ‖P‖ * Real.exp (z.re * L) ≤ c)
    (hq : ‖1 + z ^ 2 / (R : ℂ) ^ 2‖ ≤ d) (hz : e ≤ ‖z‖) (he : 0 < e) (hd : 0 ≤ d) :
    ‖P * KN L R z / z‖ ≤ c * d / e := by
  rw [norm_PK]
  have h1 : 0 ≤ ‖P‖ * Real.exp (z.re * L) := by positivity
  have hc : 0 ≤ c := le_trans h1 hP
  apply div_le_div₀ (mul_nonneg hc hd) (mul_le_mul hP hq (norm_nonneg _) hc) he hz

theorem q_top {z : ℂ} {R : ℝ} (hR : 0 < R) (hy : |z.im| = R) (hx : |z.re| ≤ R) :
    ‖1 + z ^ 2 / (R : ℂ) ^ 2‖ ≤ 3 * |z.re| / R := by
  set x := z.re
  set y := z.im
  have hz : z = x + y * I := (re_add_im z).symm
  have hy2 : (y : ℂ) ^ 2 = (R : ℂ) ^ 2 := by
    have : y ^ 2 = R ^ 2 := by rw [← sq_abs y, hy]
    exact_mod_cast this
  have hR2 : (R : ℂ) ^ 2 ≠ 0 := by exact_mod_cast (pow_pos hR 2).ne'
  have e : 1 + z ^ 2 / (R : ℂ) ^ 2 = ((x : ℂ) ^ 2 + 2 * x * y * I) / (R : ℂ) ^ 2 := by
    rw [eq_div_iff hR2, add_mul, div_mul_cancel₀ _ hR2, hz]
    linear_combination (-1 : ℂ) * hy2 + (y : ℂ) ^ 2 * I_sq
  rw [e, norm_div]
  have hn : ‖(x : ℂ) ^ 2 + 2 * x * y * I‖ ≤ |x| ^ 2 + 2 * |x| * |y| := by
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    simp [Complex.norm_real]
  rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR,
    div_le_div_iff₀ (by positivity) hR]
  have hx0 := abs_nonneg x
  rw [hy] at hn
  nlinarith [mul_le_mul_of_nonneg_left hx hx0]

theorem q_box {z : ℂ} {R : ℝ} (hR : 0 < R) (hx : |z.re| ≤ R) (hy : |z.im| ≤ R) :
    ‖1 + z ^ 2 / (R : ℂ) ^ 2‖ ≤ 5 := by
  have hzn : ‖z‖ ≤ 2 * R := by
    calc ‖z‖ = ‖(z.re : ℂ) + z.im * I‖ := by rw [re_add_im]
      _ ≤ ‖(z.re : ℂ)‖ + ‖(z.im : ℂ) * I‖ := norm_add_le _ _
      _ = |z.re| + |z.im| := by simp [Complex.norm_real]
      _ ≤ 2 * R := by linarith
  calc ‖1 + z ^ 2 / (R : ℂ) ^ 2‖ ≤ ‖(1 : ℂ)‖ + ‖z ^ 2 / (R : ℂ) ^ 2‖ := norm_add_le _ _
    _ = 1 + ‖z‖ ^ 2 / R ^ 2 := by
        rw [norm_div, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR,
          norm_one]
    _ ≤ 1 + (2 * R) ^ 2 / R ^ 2 := by
        gcongr
    _ = 5 := by field_simp; ring

theorem abs_mul_exp_le {x L : ℝ} (hx : x ≤ 0) (hL : 0 < L) :
    |x| * Real.exp (x * L) ≤ 1 / L := by
  rw [abs_of_nonpos hx, le_div_iff₀ hL]
  have h1 := Real.add_one_le_exp (-(x * L))
  have h2 : Real.exp (-(x * L)) * Real.exp (x * L) = 1 := by
    rw [← Real.exp_add]; simp
  have h3 := Real.exp_pos (x * L)
  nlinarith

/-! ## Newman's contour estimate -/

theorem ii_h {F : ℂ → ℂ} {S : Set ℂ} (hF : ContinuousOn F S) {c p q : ℝ}
    (h : ∀ x ∈ [[p, q]], (x : ℂ) + c * I ∈ S) :
    IntervalIntegrable (fun x : ℝ => F (x + c * I)) volume p q :=
  (hF.comp (Continuous.continuousOn (by fun_prop)) h).intervalIntegrable

theorem ii_v {F : ℂ → ℂ} {S : Set ℂ} (hF : ContinuousOn F S) {c p q : ℝ}
    (h : ∀ y ∈ [[p, q]], (c : ℂ) + y * I ∈ S) :
    IntervalIntegrable (fun y : ℝ => F (c + y * I)) volume p q :=
  (hF.comp (Continuous.continuousOn (by fun_prop)) h).intervalIntegrable

theorem memh {x c x0 x1 y0 y1 : ℝ} (hx : x ∈ [[x0, x1]]) (hc : c ∈ [[y0, y1]]) (hc0 : c ≠ 0) :
    (x : ℂ) + c * I ∈ [[x0, x1]] ×ℂ [[y0, y1]] \ {0} := by
  refine ⟨by simp [mem_reProdIm, hx, hc], fun h => ?_⟩
  have := congrArg Complex.im (mem_singleton_iff.mp h); simp at this; exact hc0 this

theorem memv {c y x0 x1 y0 y1 : ℝ} (hc : c ∈ [[x0, x1]]) (hy : y ∈ [[y0, y1]]) (hc0 : c ≠ 0) :
    (c : ℂ) + y * I ∈ [[x0, x1]] ×ℂ [[y0, y1]] \ {0} := by
  refine ⟨by simp [mem_reProdIm, hy, hc], fun h => ?_⟩
  have := congrArg Complex.re (mem_singleton_iff.mp h); simp at this; exact hc0 this

theorem uIcc_sub {x a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (hca : c ≤ a) (hbd : b ≤ d)
    (hx : x ∈ [[a, b]]) : x ∈ [[c, d]] := by
  rw [uIcc_of_le hab] at hx; rw [uIcc_of_le hcd]; exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

theorem nb {F : ℝ → ℂ} {C a b : ℝ} (hab : a ≤ b) (h : ∀ x ∈ Ioc a b, ‖F x‖ ≤ C) :
    ‖∫ x in a..b, F x‖ ≤ C * (b - a) := by
  have := intervalIntegral.norm_integral_le_of_norm_le_const (f := F) (C := C)
    (fun x hx => h x (by rwa [uIoc_of_le hab] at hx))
  rwa [abs_of_nonneg (by linarith)] at this

theorem norm9 (a1 a2 a3 f1 f2 f3 h1 h2 h3 : ℂ) :
    ‖(a1 - a2 + I * a3) + (f1 - f2 - I * f3) - (h1 - h2 - I * h3)‖ ≤
      ‖a1‖ + ‖a2‖ + ‖a3‖ + ‖f1‖ + ‖f2‖ + ‖f3‖ + ‖h1‖ + ‖h2‖ + ‖h3‖ := by
  have hI : ∀ w : ℂ, ‖I * w‖ = ‖w‖ := fun w => by rw [norm_mul, Complex.norm_I, one_mul]
  have e1 := norm_sub_le ((a1 - a2 + I * a3) + (f1 - f2 - I * f3)) (h1 - h2 - I * h3)
  have e2 := norm_add_le (a1 - a2 + I * a3) (f1 - f2 - I * f3)
  have e3 := norm_add_le (a1 - a2) (I * a3)
  have e4 := norm_sub_le a1 a2
  have e5 := norm_sub_le (f1 - f2) (I * f3)
  have e6 := norm_sub_le f1 f2
  have e7 := norm_sub_le (h1 - h2) (I * h3)
  have e8 := norm_sub_le h1 h2
  rw [hI] at e3 e5 e7
  linarith

section core

variable {a : ℝ → ℝ} {B : ℝ}

theorem newman_core (hmeas : Measurable a) (hbd : ∀ x, 1 ≤ x → |a x| ≤ B)
    {G : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hHP : ∀ z : ℂ, 0 ≤ z.re → z ∈ U)
    (hG : DifferentiableOn ℂ G U) (hGeq : ∀ z : ℂ, 0 < z.re → G z = Gint a z)
    {R : ℝ} (hR : 0 < R) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ X : ℝ, 1 < X →
      2 * Real.pi * ‖G 0 - GX a X 0‖ ≤
        32 * B / R + C / Real.log X + C * Real.exp (-(δ * Real.log X)) := by
  have hB : 0 ≤ B := le_trans (abs_nonneg _) (hbd 1 le_rfl)
  have hK0 : IsCompact ([[0, R]] ×ℂ [[-R, R]]) := isCompact_uIcc.reProdIm isCompact_uIcc
  have hK0U : [[0, R]] ×ℂ [[-R, R]] ⊆ U := fun z hz => hHP z (by
    rw [mem_reProdIm, uIcc_of_le hR.le] at hz; exact hz.1.1)
  obtain ⟨δ0, hδ0, hthick⟩ := hK0.exists_cthickening_subset_open hU hK0U
  set δ := min δ0 R with hδdef
  have hδ : 0 < δ := lt_min hδ0 hR
  have hδR : δ ≤ R := min_le_right _ _
  have hδδ0 : δ ≤ δ0 := min_le_left _ _
  have hDU : [[-δ, R]] ×ℂ [[-R, R]] ⊆ U := by
    intro z hz
    rw [mem_reProdIm, uIcc_of_le (by linarith), uIcc_of_le (by linarith)] at hz
    by_cases h0 : 0 ≤ z.re
    · exact hK0U (by
        rw [mem_reProdIm, uIcc_of_le hR.le, uIcc_of_le (by linarith)]
        exact ⟨⟨h0, hz.1.2⟩, hz.2⟩)
    · apply hthick
      refine Metric.mem_cthickening_of_dist_le z ((z.im : ℂ) * I) δ0 _ ?_ ?_
      · rw [mem_reProdIm, uIcc_of_le hR.le, uIcc_of_le (by linarith)]
        simp only [mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
          mul_im, add_zero]
        exact ⟨⟨le_rfl, hR.le⟩, hz.2⟩
      · rw [Complex.dist_eq]
        have : z - (z.im : ℂ) * I = (z.re : ℂ) := by
          apply Complex.ext <;> simp
        rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
        linarith [hz.1.1]
  have hDc : IsCompact ([[-δ, R]] ×ℂ [[-R, R]]) := isCompact_uIcc.reProdIm isCompact_uIcc
  obtain ⟨M0, hM0⟩ := hDc.exists_bound_of_continuousOn (hG.continuousOn.mono hDU)
  set M := max M0 0
  have hM : 0 ≤ M := le_max_right _ _
  have hGM : ∀ z ∈ [[-δ, R]] ×ℂ [[-R, R]], ‖G z‖ ≤ M :=
    fun z hz => (hM0 z hz).trans (le_max_left _ _)
  refine ⟨6 * M * δ / R ^ 2 + 10 * M * R / δ, δ, hδ, fun X hX => ?_⟩
  set L := Real.log X with hLdef
  have hL : 0 < L := Real.log_pos hX
  have hX1 : 1 ≤ X := hX.le
  set f : ℂ → ℂ := fun z => G z * KN L R z / z with hfdef
  set g : ℂ → ℂ := fun z => GX a X z * KN L R z / z with hgdef
  have hP1 : RI f (-δ) R (-R) R = 2 * Real.pi * I * G 0 := by
    have := RI_pole (H := fun z => G z * KN L R z) hδ hR hδR hU hDU
      (hG.mul (KN_differentiable L R).differentiableOn)
    rw [KN_zero, mul_one] at this
    exact this
  have hP2 : RI g (-R) R (-R) R = 2 * Real.pi * I * GX a X 0 := by
    have := RI_pole (H := fun z => GX a X z * KN L R z) hR hR le_rfl isOpen_univ (subset_univ _)
      ((GX_differentiable hmeas hbd hX1).mul (KN_differentiable L R)).differentiableOn
    rw [KN_zero, mul_one] at this
    exact this
  have hfc : ContinuousOn f ([[-δ, R]] ×ℂ [[-R, R]] \ {0}) := by
    apply ContinuousOn.div ((hG.continuousOn.mono (sdiff_subset.trans hDU)).mul
      (KN_differentiable L R).continuous.continuousOn) continuousOn_id
    intro z hz; exact hz.2
  have hgc : ContinuousOn g ([[-R, R]] ×ℂ [[-R, R]] \ {0}) := by
    apply ContinuousOn.div ((GX_differentiable hmeas hbd hX1).continuous.continuousOn.mul
      (KN_differentiable L R).continuous.continuousOn) continuousOn_id
    intro z hz; exact hz.2
  have hR0 : R ≠ 0 := hR.ne'
  have hmR0 : (-R) ≠ 0 := by linarith
  have hmRm : (-R) ∈ [[-R, R]] := left_mem_uIcc
  have hRm : R ∈ [[-R, R]] := right_mem_uIcc
  have hRmD : R ∈ [[-δ, R]] := right_mem_uIcc
  have hRδ : -R ≤ -δ := by linarith
  -- integrability
  have fb1 : IntervalIntegrable (fun x : ℝ => f (x + ((-R : ℝ) : ℂ) * I)) volume (-δ) 0 :=
    ii_h hfc (fun x hx => memh (uIcc_sub (by linarith) (by linarith) le_rfl hR.le hx) hmRm hmR0)
  have fb2 : IntervalIntegrable (fun x : ℝ => f (x + ((-R : ℝ) : ℂ) * I)) volume 0 R :=
    ii_h hfc (fun x hx => memh (uIcc_sub hR.le (by linarith) (by linarith) le_rfl hx) hmRm hmR0)
  have ft1 : IntervalIntegrable (fun x : ℝ => f (x + (R : ℂ) * I)) volume (-δ) 0 :=
    ii_h hfc (fun x hx => memh (uIcc_sub (by linarith) (by linarith) le_rfl hR.le hx) hRm hR0)
  have ft2 : IntervalIntegrable (fun x : ℝ => f (x + (R : ℂ) * I)) volume 0 R :=
    ii_h hfc (fun x hx => memh (uIcc_sub hR.le (by linarith) (by linarith) le_rfl hx) hRm hR0)
  have gb1 : IntervalIntegrable (fun x : ℝ => g (x + ((-R : ℝ) : ℂ) * I)) volume (-R) 0 :=
    ii_h hgc (fun x hx => memh (uIcc_sub (by linarith) (by linarith) le_rfl hR.le hx) hmRm hmR0)
  have gb2 : IntervalIntegrable (fun x : ℝ => g (x + ((-R : ℝ) : ℂ) * I)) volume 0 R :=
    ii_h hgc (fun x hx => memh (uIcc_sub hR.le (by linarith) (by linarith) le_rfl hx) hmRm hmR0)
  have gt1 : IntervalIntegrable (fun x : ℝ => g (x + (R : ℂ) * I)) volume (-R) 0 :=
    ii_h hgc (fun x hx => memh (uIcc_sub (by linarith) (by linarith) le_rfl hR.le hx) hRm hR0)
  have gt2 : IntervalIntegrable (fun x : ℝ => g (x + (R : ℂ) * I)) volume 0 R :=
    ii_h hgc (fun x hx => memh (uIcc_sub hR.le (by linarith) (by linarith) le_rfl hx) hRm hR0)
  have fr : IntervalIntegrable (fun y : ℝ => f ((R : ℂ) + y * I)) volume (-R) R :=
    ii_v hfc (fun y hy => memv hRmD hy hR0)
  have gr : IntervalIntegrable (fun y : ℝ => g ((R : ℂ) + y * I)) volume (-R) R :=
    ii_v hgc (fun y hy => memv hRm hy hR0)
  -- decomposition
  unfold RI at hP1 hP2
  rw [← intervalIntegral.integral_add_adjacent_intervals fb1 fb2,
    ← intervalIntegral.integral_add_adjacent_intervals ft1 ft2] at hP1
  rw [← intervalIntegral.integral_add_adjacent_intervals gb1 gb2,
    ← intervalIntegral.integral_add_adjacent_intervals gt1 gt2] at hP2
  have hA1 := intervalIntegral.integral_sub fb2 gb2
  have hA2 := intervalIntegral.integral_sub ft2 gt2
  have hA3 := intervalIntegral.integral_sub fr gr
  have key : 2 * Real.pi * I * (G 0 - GX a X 0) =
      ((∫ x in (0 : ℝ)..R, (f (x + ((-R : ℝ) : ℂ) * I) - g (x + ((-R : ℝ) : ℂ) * I))) -
        (∫ x in (0 : ℝ)..R, (f (x + (R : ℂ) * I) - g (x + (R : ℂ) * I))) +
        I * (∫ y in (-R)..R, (f ((R : ℂ) + y * I) - g ((R : ℂ) + y * I)))) +
      ((∫ x in (-δ)..0, f (x + ((-R : ℝ) : ℂ) * I)) - (∫ x in (-δ)..0, f (x + (R : ℂ) * I)) -
        I * (∫ y in (-R)..R, f (((-δ : ℝ) : ℂ) + y * I))) -
      ((∫ x in (-R)..0, g (x + ((-R : ℝ) : ℂ) * I)) - (∫ x in (-R)..0, g (x + (R : ℂ) * I)) -
        I * (∫ y in (-R)..R, g (((-R : ℝ) : ℂ) + y * I))) := by
    rw [mul_sub, ← hP1, ← hP2, hA1, hA2, hA3]
    ring
  -- pointwise bounds
  have hRpos2 : 0 < R ^ 2 := by positivity
  have pA : ∀ z : ℂ, 0 < z.re → z.re ≤ R → |z.im| = R → ‖f z - g z‖ ≤ 3 * B / R ^ 2 := by
    intro z h1 h2 h3
    have e : f z - g z = (Gint a z - GX a X z) * KN L R z / z := by
      simp only [hfdef, hgdef, hGeq z h1]; ring
    rw [e]
    have := pt_gen (L := L) (R := R) (P := Gint a z - GX a X z) (z := z)
      (tail_bound_exp hmeas hbd h1 hX1) (q_top hR h3 (by rw [abs_of_pos h1]; exact h2))
      (by rw [← h3]; exact abs_im_le_norm z) hR (by positivity)
    calc _ ≤ _ := this
      _ = 3 * B / R ^ 2 := by rw [abs_of_pos h1]; have := h1.ne'; field_simp
  have pAv : ∀ z : ℂ, z.re = R → |z.im| ≤ R → ‖f z - g z‖ ≤ 5 * B / R ^ 2 := by
    intro z h1 h3
    have h1' : 0 < z.re := h1 ▸ hR
    have e : f z - g z = (Gint a z - GX a X z) * KN L R z / z := by
      simp only [hfdef, hgdef, hGeq z h1']; ring
    rw [e]
    have := pt_gen (L := L) (R := R) (P := Gint a z - GX a X z) (z := z)
      (tail_bound_exp hmeas hbd h1' hX1) (q_box hR (by rw [h1, abs_of_pos hR]) h3)
      (by have := abs_re_le_norm z; rw [h1, abs_of_pos hR] at this; exact this) hR (by norm_num)
    calc _ ≤ _ := this
      _ = 5 * B / R ^ 2 := by rw [h1]; field_simp
  have pH : ∀ z : ℂ, -R ≤ z.re → z.re ≤ 0 → |z.im| = R → ‖g z‖ ≤ 3 * B / R ^ 2 := by
    intro z h1 h2 h3
    have hzR : |z.re| ≤ R := abs_le.mpr ⟨h1, by linarith⟩
    have hzn : R ≤ ‖z‖ := by rw [← h3]; exact abs_im_le_norm z
    rcases lt_or_eq_of_le h2 with h2 | h2
    · have := pt_gen (L := L) (R := R) (P := GX a X z) (z := z)
        (head_bound_exp hbd h2 hX1) (q_top hR h3 hzR) hzn hR (by positivity)
      calc _ ≤ _ := this
        _ = 3 * B / R ^ 2 := by
          rw [abs_of_neg h2]; have : z.re ≠ 0 := by linarith
          field_simp
    · have := pt_gen (L := L) (R := R) (P := GX a X z) (z := z) le_rfl (q_top hR h3 hzR) hzn hR
        (by positivity)
      rw [h2] at this
      simp only [abs_zero, mul_zero, zero_div] at this
      exact this.trans (by positivity)
  have pHv : ∀ z : ℂ, z.re = -R → |z.im| ≤ R → ‖g z‖ ≤ 5 * B / R ^ 2 := by
    intro z h1 h3
    have h1' : z.re < 0 := by linarith
    have := pt_gen (L := L) (R := R) (P := GX a X z) (z := z)
      (head_bound_exp hbd h1' hX1) (q_box hR (by rw [h1, abs_neg, abs_of_pos hR]) h3)
      (by have := abs_re_le_norm z; rw [h1, abs_neg, abs_of_pos hR] at this; exact this) hR
      (by norm_num)
    calc _ ≤ _ := this
      _ = 5 * B / R ^ 2 := by rw [h1, neg_neg]; field_simp
  have pF : ∀ z : ℂ, -δ ≤ z.re → z.re ≤ 0 → |z.im| = R → ‖f z‖ ≤ 3 * M / (R ^ 2 * L) := by
    intro z h1 h2 h3
    have hzR : |z.re| ≤ R := abs_le.mpr ⟨by linarith, by linarith⟩
    have hzD : z ∈ [[-δ, R]] ×ℂ [[-R, R]] := by
      rw [mem_reProdIm, uIcc_of_le (by linarith), uIcc_of_le (by linarith)]
      exact ⟨⟨h1, by linarith⟩, abs_le.mp h3.le⟩
    have hP : ‖G z‖ * Real.exp (z.re * L) ≤ M * Real.exp (z.re * L) :=
      mul_le_mul_of_nonneg_right (hGM z hzD) (Real.exp_pos _).le
    have := pt_gen (L := L) (R := R) (P := G z) (z := z) hP (q_top hR h3 hzR)
      (by rw [← h3]; exact abs_im_le_norm z) hR (by positivity)
    have hk := abs_mul_exp_le h2 hL
    calc ‖f z‖ = ‖G z * KN L R z / z‖ := rfl
      _ ≤ _ := this
      _ = 3 * M / R ^ 2 * (|z.re| * Real.exp (z.re * L)) := by field_simp
      _ ≤ 3 * M / R ^ 2 * (1 / L) := mul_le_mul_of_nonneg_left hk (by positivity)
      _ = 3 * M / (R ^ 2 * L) := by field_simp
  have pFv : ∀ z : ℂ, z.re = -δ → |z.im| ≤ R → ‖f z‖ ≤ 5 * M * Real.exp (-(δ * L)) / δ := by
    intro z h1 h3
    have hzD : z ∈ [[-δ, R]] ×ℂ [[-R, R]] := by
      rw [mem_reProdIm, uIcc_of_le (by linarith), uIcc_of_le (by linarith)]
      exact ⟨⟨by linarith, by linarith⟩, abs_le.mp h3⟩
    have hP : ‖G z‖ * Real.exp (z.re * L) ≤ M * Real.exp (-(δ * L)) := by
      rw [h1, neg_mul]
      exact mul_le_mul_of_nonneg_right (hGM z hzD) (Real.exp_pos _).le
    have := pt_gen (L := L) (R := R) (P := G z) (z := z) hP
      (q_box hR (by rw [h1, abs_neg, abs_of_pos hδ]; exact hδR) h3)
      (by have := abs_re_le_norm z; rw [h1, abs_neg, abs_of_pos hδ] at this; exact this) hδ
      (by norm_num)
    calc ‖f z‖ = ‖G z * KN L R z / z‖ := rfl
      _ ≤ _ := this
      _ = 5 * M * Real.exp (-(δ * L)) / δ := by ring
  -- integral bounds
  have habsR : |(-R)| = R := by rw [abs_neg, abs_of_pos hR]
  have n1 : ‖∫ x in (0 : ℝ)..R, (f (x + ((-R : ℝ) : ℂ) * I) - g (x + ((-R : ℝ) : ℂ) * I))‖ ≤
      3 * B / R ^ 2 * (R - 0) :=
    nb hR.le (fun x hx => pA _ (by simpa using hx.1) (by simpa using hx.2) (by simpa using habsR))
  have n2 : ‖∫ x in (0 : ℝ)..R, (f (x + (R : ℂ) * I) - g (x + (R : ℂ) * I))‖ ≤
      3 * B / R ^ 2 * (R - 0) :=
    nb hR.le (fun x hx => pA _ (by simpa using hx.1) (by simpa using hx.2)
      (by simp [abs_of_pos hR]))
  have n3 : ‖∫ y in (-R)..R, (f ((R : ℂ) + y * I) - g ((R : ℂ) + y * I))‖ ≤
      5 * B / R ^ 2 * (R - -R) :=
    nb (by linarith) (fun y hy => pAv _ (by simp) (by simpa using abs_le.mpr ⟨hy.1.le, hy.2⟩))
  have n4 : ‖∫ x in (-δ)..0, f (x + ((-R : ℝ) : ℂ) * I)‖ ≤ 3 * M / (R ^ 2 * L) * (0 - -δ) :=
    nb (by linarith) (fun x hx => pF _ (by simpa using hx.1.le) (by simpa using hx.2)
      (by simpa using habsR))
  have n5 : ‖∫ x in (-δ)..0, f (x + (R : ℂ) * I)‖ ≤ 3 * M / (R ^ 2 * L) * (0 - -δ) :=
    nb (by linarith) (fun x hx => pF _ (by simpa using hx.1.le) (by simpa using hx.2)
      (by simp [abs_of_pos hR]))
  have n6 : ‖∫ y in (-R)..R, f (((-δ : ℝ) : ℂ) + y * I)‖ ≤
      5 * M * Real.exp (-(δ * L)) / δ * (R - -R) :=
    nb (by linarith) (fun y hy => pFv _ (by simp) (by simpa using abs_le.mpr ⟨hy.1.le, hy.2⟩))
  have n7 : ‖∫ x in (-R)..0, g (x + ((-R : ℝ) : ℂ) * I)‖ ≤ 3 * B / R ^ 2 * (0 - -R) :=
    nb (by linarith) (fun x hx => pH _ (by simpa using hx.1.le) (by simpa using hx.2)
      (by simpa using habsR))
  have n8 : ‖∫ x in (-R)..0, g (x + (R : ℂ) * I)‖ ≤ 3 * B / R ^ 2 * (0 - -R) :=
    nb (by linarith) (fun x hx => pH _ (by simpa using hx.1.le) (by simpa using hx.2)
      (by simp [abs_of_pos hR]))
  have n9 : ‖∫ y in (-R)..R, g (((-R : ℝ) : ℂ) + y * I)‖ ≤ 5 * B / R ^ 2 * (R - -R) :=
    nb (by linarith) (fun y hy => pHv _ (by simp) (by simpa using abs_le.mpr ⟨hy.1.le, hy.2⟩))
  have hnorm : ‖2 * Real.pi * I * (G 0 - GX a X 0)‖ = 2 * Real.pi * ‖G 0 - GX a X 0‖ := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    simp
  rw [← hnorm, key]
  refine (norm9 _ _ _ _ _ _ _ _ _).trans ?_
  set e := Real.exp (-(δ * L)) with hedef
  have he : 0 ≤ e := (Real.exp_pos _).le
  have c1 : 3 * B / R ^ 2 * (R - 0) = 3 * B / R := by field_simp; ring
  have c3 : 5 * B / R ^ 2 * (R - -R) = 10 * B / R := by field_simp; ring
  have c7 : 3 * B / R ^ 2 * (0 - -R) = 3 * B / R := by field_simp; ring
  have c4 : 3 * M / (R ^ 2 * L) * (0 - -δ) = 3 * M * δ / R ^ 2 / L := by field_simp; ring
  have c6 : 5 * M * e / δ * (R - -R) = 10 * M * R / δ * e := by field_simp; ring
  have hCL : (6 * M * δ / R ^ 2 + 10 * M * R / δ) / L =
      6 * M * δ / R ^ 2 / L + 10 * M * R / δ / L := add_div _ _ _
  have hCe : (6 * M * δ / R ^ 2 + 10 * M * R / δ) * e =
      6 * M * δ / R ^ 2 * e + 10 * M * R / δ * e := add_mul _ _ _
  have p1 : 0 ≤ 10 * M * R / δ / L := by positivity
  have p2 : 0 ≤ 6 * M * δ / R ^ 2 * e := by positivity
  have c32 : 32 * B / R = 3 * B / R + 3 * B / R + 10 * B / R + 3 * B / R + 3 * B / R +
      10 * B / R := by ring
  have c44 : 6 * M * δ / R ^ 2 / L = 3 * M * δ / R ^ 2 / L + 3 * M * δ / R ^ 2 / L := by ring
  linarith

end core

section newmanthm

variable {a : ℝ → ℝ} {B : ℝ}

/-- **Newman's analytic theorem** (Mellin form): if `a` is bounded and measurable on `[1,∞)` and
its Mellin transform `∫_1^∞ a(x) x^{-z-1} dx` extends holomorphically to an open set containing
`Re z ≥ 0`, then `∫_1^X a(x)/x dx` converges to the value at `0`. -/
theorem newman (hmeas : Measurable a) (hbd : ∀ x, 1 ≤ x → |a x| ≤ B)
    {G : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hHP : ∀ z : ℂ, 0 ≤ z.re → z ∈ U)
    (hG : DifferentiableOn ℂ G U) (hGeq : ∀ z : ℂ, 0 < z.re → G z = Gint a z) :
    Tendsto (fun X => GX a X 0) atTop (𝓝 (G 0)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hB : 0 ≤ B := le_trans (abs_nonneg _) (hbd 1 le_rfl)
  have hpe : 0 < Real.pi * ε := mul_pos Real.pi_pos hε
  set R := 32 * (B + 1) / (Real.pi * ε) with hRdef
  have hR : 0 < R := by positivity
  obtain ⟨C, δ, hδ, hb⟩ := newman_core hmeas hbd hU hHP hG hGeq hR
  have hT : Tendsto (fun X => C / Real.log X + C * Real.exp (-(δ * Real.log X))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun X => C / Real.log X) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
    have h2 : Tendsto (fun X => Real.exp (-(δ * Real.log X))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (Real.tendsto_log_atTop.const_mul_atTop hδ)
    simpa using h1.add (h2.const_mul C)
  have hev := (hT.eventually (gt_mem_nhds hpe)).and (eventually_gt_atTop (1 : ℝ))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨N, fun X hX => ?_⟩
  obtain ⟨hE, hX1⟩ := hN X hX
  have h32 : 32 * B / R < Real.pi * ε := by
    rw [hRdef, div_div_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  have := hb X hX1
  rw [dist_eq_norm, norm_sub_rev]
  nlinarith [Real.pi_pos]

/-- Real form of Newman's theorem. -/
theorem newman_real (hmeas : Measurable a) (hbd : ∀ x, 1 ≤ x → |a x| ≤ B)
    {G : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hHP : ∀ z : ℂ, 0 ≤ z.re → z ∈ U)
    (hG : DifferentiableOn ℂ G U) (hGeq : ∀ z : ℂ, 0 < z.re → G z = Gint a z) :
    Tendsto (fun X => ∫ x in (1 : ℝ)..X, a x / x) atTop (𝓝 (G 0).re) := by
  have h := (Complex.continuous_re.tendsto _).comp (newman hmeas hbd hU hHP hG hGeq)
  refine h.congr (fun X => ?_)
  simp only [Function.comp, GX]
  have : ∀ x : ℝ, (a x : ℂ) * (x : ℂ) ^ (-(0 : ℂ) - 1) = ((a x / x : ℝ) : ℂ) := by
    intro x
    rw [neg_zero, zero_sub, cpow_neg_one]
    push_cast
    ring
  simp_rw [this, intervalIntegral.integral_ofReal, ofReal_re]

end newmanthm

/-! ## Tauberian step: convergence of `∫ (S(x)/x - c)/x` forces `S(x)/x → c` -/

section tauberian

theorem taub {S : ℝ → ℝ} {c l : ℝ} (hc : 0 < c) (hmono : Monotone S)
    (hI : Tendsto (fun X => ∫ x in (1 : ℝ)..X, (S x / x - c) / x) atTop (𝓝 l)) :
    Tendsto (fun x => S x / x) atTop (𝓝 c) := by
  set F : ℝ → ℝ := fun x => (S x / x - c) / x with hF
  set I : ℝ → ℝ := fun X => ∫ x in (1 : ℝ)..X, F x with hIdef
  have hii : ∀ p q : ℝ, 0 < p → 0 < q → IntervalIntegrable F volume p q := by
    intro p q hp hq
    have h0 : ∀ x ∈ [[p, q]], x ≠ 0 := by
      intro x hx
      rcases le_total p q with h | h
      · rw [uIcc_of_le h] at hx; linarith [hx.1]
      · rw [uIcc_of_ge h] at hx; linarith [hx.1]
    have h1 : IntervalIntegrable (fun x => S x * (x⁻¹ * x⁻¹)) volume p q :=
      (hmono.intervalIntegrable).mul_continuousOn
        ((continuousOn_inv₀.mono (fun x hx => h0 x hx)).mul
          (continuousOn_inv₀.mono (fun x hx => h0 x hx)))
    have h2 : IntervalIntegrable (fun x : ℝ => c * x⁻¹) volume p q :=
      (ContinuousOn.intervalIntegrable
        (continuousOn_const.mul (continuousOn_inv₀.mono (fun x hx => h0 x hx))))
    refine (h1.sub h2).congr ?_
    intro x _
    simp only [hF]
    ring
  have hdiff : ∀ p q : ℝ, 1 ≤ p → 1 ≤ q → I q - I p = ∫ x in p..q, F x := by
    intro p q hp hq
    exact intervalIntegral.integral_interval_sub_left (hii 1 q one_pos (by linarith))
      (hii 1 p one_pos (by linarith))
  have hC : ∀ μ : ℝ, 0 < μ → Tendsto (fun x => I (μ * x) - I x) atTop (𝓝 0) := by
    intro μ hμ
    have := (hI.comp (tendsto_id.const_mul_atTop hμ)).sub hI
    simpa using this
  -- upper bound
  have up : ∀ ε > 0, ∀ᶠ x in atTop, S x / x ≤ c + ε := by
    intro ε hε
    by_contra h
    rw [not_eventually] at h
    set μ := 1 + ε / (2 * c) with hμ
    have hμ1 : 1 < μ := by have : 0 < ε / (2 * c) := by positivity
                           linarith
    have hμ0 : 0 < μ := by linarith
    set d := (c + ε) / μ - c with hd
    have hdpos : 0 < d := by
      rw [hd, sub_pos, lt_div_iff₀ hμ0, hμ]
      field_simp
      nlinarith
    set κ := d * (μ - 1) / μ with hκ
    have hκpos : 0 < κ := by positivity
    obtain ⟨x, hxS, hxC, hx1⟩ :=
      (h.and_eventually (((hC μ hμ0).eventually (eventually_lt_nhds hκpos)).and
        (eventually_ge_atTop 1))).exists
    have hx0 : 0 < x := by linarith
    have hxS' : (c + ε) * x < S x := by
      rw [not_le, lt_div_iff₀ hx0] at hxS; exact hxS
    have hxle : x ≤ μ * x := by nlinarith
    have hge : κ ≤ ∫ t in x..μ * x, F t := by
      have hm := intervalIntegral.integral_mono_on hxle
        (intervalIntegrable_const (c := d / (μ * x))) (hii x (μ * x) hx0 (by positivity)) ?_
      · rw [intervalIntegral.integral_const, smul_eq_mul] at hm
        refine le_trans (le_of_eq ?_) hm
        rw [hκ]; field_simp
      · intro t ht
        have ht0 : 0 < t := by linarith [ht.1]
        have hSt : (c + ε) * x < S t := lt_of_lt_of_le hxS' (hmono ht.1)
        have h2 : d ≤ S t / t - c := by
          rw [hd, sub_le_sub_iff_right, div_le_div_iff₀ hμ0 ht0]
          have : (c + ε) * t ≤ (c + ε) * (μ * x) := by
            apply mul_le_mul_of_nonneg_left ht.2; linarith
          nlinarith
        have h3 : d / (μ * x) ≤ d / t := div_le_div_of_nonneg_left hdpos.le ht0 ht.2
        have h4 : d / t ≤ (S t / t - c) / t := div_le_div_of_nonneg_right h2 ht0.le
        simp only [hF]
        linarith
    have := hdiff x (μ * x) hx1 (by nlinarith)
    simp only [hIdef] at hxC this
    linarith
  -- lower bound
  have lo : ∀ ε > 0, ε < c → ∀ᶠ x in atTop, c - ε ≤ S x / x := by
    intro ε hε hεc
    by_contra h
    rw [not_eventually] at h
    set μ := 1 + ε / (2 * c) with hμ
    have hμ1 : 1 < μ := by have : 0 < ε / (2 * c) := by positivity
                           linarith
    have hμ0 : 0 < μ := by linarith
    set d := c - (c - ε) * μ with hd
    have hdpos : 0 < d := by
      rw [hd, hμ]
      have : (c - ε) * (1 + ε / (2 * c)) = c - ε / 2 - ε ^ 2 / (2 * c) := by field_simp; ring
      rw [this]
      have : 0 < ε ^ 2 / (2 * c) := by positivity
      linarith
    set κ := d * (1 - μ⁻¹) with hκ
    have hκpos : 0 < κ := by
      have : μ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hμ1
      have : 0 < 1 - μ⁻¹ := by linarith
      positivity
    have hC' : Tendsto (fun y => I (μ⁻¹ * y) - I y) atTop (𝓝 0) := hC μ⁻¹ (inv_pos.mpr hμ0)
    obtain ⟨y, hyS, hyC, hy1⟩ :=
      (h.and_eventually ((hC'.eventually (eventually_lt_nhds hκpos)).and
        (eventually_ge_atTop μ))).exists
    have hy0 : 0 < y := by linarith
    set x := μ⁻¹ * y with hxdef
    have hx0 : 0 < x := by positivity
    have hx1 : 1 ≤ x := by
      rw [hxdef, ← div_eq_inv_mul, le_div_iff₀ hμ0]; linarith
    have hyx : y = μ * x := by rw [hxdef]; field_simp
    have hyS' : S y < (c - ε) * y := by
      rw [not_le, div_lt_iff₀ hy0] at hyS; exact hyS
    have hxle : x ≤ y := by rw [hyx]; nlinarith
    have hle : ∫ t in x..y, F t ≤ -κ := by
      have hm := intervalIntegral.integral_mono_on hxle (hii x y hx0 hy0)
        (intervalIntegrable_const (c := -d / y)) ?_
      · rw [intervalIntegral.integral_const, smul_eq_mul] at hm
        refine le_trans hm (le_of_eq ?_)
        rw [hκ, hyx]; field_simp
      · intro t ht
        have ht0 : 0 < t := by linarith [ht.1]
        have hSt : S t < (c - ε) * y := lt_of_le_of_lt (hmono ht.2) hyS'
        have hyt : y ≤ μ * t := by rw [hyx]; nlinarith [ht.1]
        have h2 : S t / t - c ≤ -d := by
          rw [hd, div_sub' ht0.ne', div_le_iff₀ ht0]
          have : (c - ε) * y ≤ (c - ε) * (μ * t) :=
            mul_le_mul_of_nonneg_left hyt (by linarith)
          nlinarith
        have h3 : (S t / t - c) / t ≤ -d / t := div_le_div_of_nonneg_right h2 ht0.le
        have h4 : -d / t ≤ -d / y := by
          rw [neg_div, neg_div, neg_le_neg_iff]
          exact div_le_div_of_nonneg_left hdpos.le ht0 ht.2
        simp only [hF]
        linarith
    have := hdiff x y hx1 (by linarith)
    simp only [hIdef] at hyC this
    linarith
  rw [tendsto_order]
  constructor
  · intro a' ha'
    set ε := min ((c - a') / 2) (c / 2) with hε
    have hε0 : 0 < ε := lt_min (by linarith) (by linarith)
    have hεc : ε < c := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have hεa : ε < c - a' := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    filter_upwards [lo ε hε0 hεc] with x hx
    linarith
  · intro a' ha'
    filter_upwards [up ((a' - c) / 2) (by linarith)] with x hx
    linarith

end tauberian

/-! ## Primes in arithmetic progressions and the Prime Number Theorem -/

section application

open ArithmeticFunction ArithmeticFunction.vonMangoldt DirichletCharacter

variable {q : ℕ}

/-- Chebyshev's `ψ` restricted to the residue class `b` mod `q`. -/
noncomputable def psiAP (b : ZMod q) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, residueClass b k

theorem psiAP_nonneg (b : ZMod q) (x : ℝ) : 0 ≤ psiAP b x :=
  Finset.sum_nonneg fun k _ => residueClass_nonneg b k

theorem psiAP_mono (b : ZMod q) : Monotone (psiAP b) := by
  intro x y hxy
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Icc_subset_Icc le_rfl (Nat.floor_le_floor hxy))
  intro k _ _; exact residueClass_nonneg b k

theorem Icc_one_eq_Ioc_zero (n : ℕ) : Finset.Icc 1 n = Finset.Ioc 0 n := by
  ext k; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega

theorem psiAP_le (b : ZMod q) {x : ℝ} (hx : 0 ≤ x) : psiAP b x ≤ (Real.log 4 + 4) * x := by
  refine le_trans ?_ (Chebyshev.psi_le_const_mul_self hx)
  rw [Chebyshev.psi, psiAP, Icc_one_eq_Ioc_zero]
  exact Finset.sum_le_sum fun k _ => residueClass_le b k

theorem psiAP_measurable (b : ZMod q) : Measurable (psiAP b) :=
  (measurable_from_nat (f := fun n => ∑ k ∈ Finset.Icc 1 n, residueClass b k)).comp
    Nat.measurable_floor

theorem psiAP_div_bound (b : ZMod q) {x : ℝ} (hx : 1 ≤ x) :
    |psiAP b x / x| ≤ Real.log 4 + 4 := by
  have hx0 : 0 < x := by linarith
  rw [abs_of_nonneg (div_nonneg (psiAP_nonneg b x) hx0.le), div_le_iff₀ hx0]
  exact psiAP_le b hx0.le

theorem A_bound (b : ZMod q) {x : ℝ} (hx : 1 ≤ x) :
    |psiAP b x / x - (q.totient : ℝ)⁻¹| ≤ Real.log 4 + 4 + (q.totient : ℝ)⁻¹ := by
  have h1 := psiAP_div_bound b hx
  have h2 : 0 ≤ (q.totient : ℝ)⁻¹ := by positivity
  calc _ ≤ |psiAP b x / x| + |(q.totient : ℝ)⁻¹| := abs_sub _ _
    _ ≤ _ := by rw [abs_of_nonneg h2]; linarith

theorem A_measurable (b : ZMod q) :
    Measurable (fun x => psiAP b x / x - (q.totient : ℝ)⁻¹) :=
  ((psiAP_measurable b).div measurable_id).sub measurable_const

variable [NeZero q]

/-- The open set on which the auxiliary function is holomorphic (shifted by one). -/
def Uq (q : ℕ) [NeZero q] : Set ℂ :=
  {z | z + 1 ≠ 0} ∩ {z | LFunctionTrivChar₁ q (z + 1) ≠ 0} ∩
    ⋂ χ ∈ {χ : DirichletCharacter ℂ q | χ ≠ 1}, {z | LFunction χ (z + 1) ≠ 0}

theorem Uq_open : IsOpen (Uq q) := by
  refine ((isOpen_ne_fun (by fun_prop) continuous_const).inter
    (isOpen_ne_fun ((differentiable_LFunctionTrivChar₁ q).continuous.comp (by fun_prop))
      continuous_const)).inter ?_
  refine Set.Finite.isOpen_biInter (Set.toFinite _) fun χ hχ => ?_
  exact isOpen_ne_fun ((differentiable_LFunction hχ).continuous.comp (by fun_prop))
    continuous_const

theorem LFunctionTrivChar₁_ne_zero {s : ℂ} (hs : 1 ≤ s.re) : LFunctionTrivChar₁ q s ≠ 0 := by
  rcases eq_or_ne s 1 with rfl | h1
  · exact LFunctionTrivChar₁_apply_one_ne_zero q
  · simp only [LFunctionTrivChar₁, Function.update_of_ne h1]
    exact mul_ne_zero (sub_ne_zero.mpr h1) (LFunction_ne_zero_of_one_le_re 1 (.inr h1) hs)

theorem mem_Uq {z : ℂ} (hz : 0 ≤ z.re) : z ∈ Uq q := by
  have hs : 1 ≤ (z + 1).re := by simp; linarith
  refine ⟨⟨?_, LFunctionTrivChar₁_ne_zero hs⟩, ?_⟩
  · intro h; have := congrArg Complex.re h; simp at this; linarith
  · simp only [mem_iInter₂, mem_ofPred_eq]
    intro χ hχ
    exact LFunction_ne_zero_of_one_le_re χ (.inl hχ) hs

/-- The shifted auxiliary function `(Aux(z+1) - 1/φ(q)) / (z+1)`. -/
noncomputable def Gq (b : ZMod q) (z : ℂ) : ℂ :=
  (LFunctionResidueClassAux b (z + 1) - (q.totient : ℂ)⁻¹) / (z + 1)

theorem aux_differentiableAt (b : ZMod q) {s : ℂ} (h1 : LFunctionTrivChar₁ q s ≠ 0)
    (h2 : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → LFunction χ s ≠ 0) :
    DifferentiableAt ℂ (LFunctionResidueClassAux b) s := by
  unfold LFunctionResidueClassAux
  apply DifferentiableAt.const_mul
  apply DifferentiableAt.sub
  · apply DifferentiableAt.div _ (differentiable_LFunctionTrivChar₁ q s) h1
    exact (((differentiable_LFunctionTrivChar₁ q).analyticAt s).deriv.differentiableAt).neg
  · apply DifferentiableAt.fun_sum
    intro χ hχ
    have hχ1 : χ ≠ 1 := by simpa using hχ
    apply DifferentiableAt.div _ (differentiable_LFunction hχ1 s) (h2 χ hχ1)
    exact (((differentiable_LFunction hχ1).analyticAt s).deriv.differentiableAt).const_mul _

theorem Gq_differentiableOn (b : ZMod q) : DifferentiableOn ℂ (Gq b) (Uq q) := by
  intro z hz
  obtain ⟨⟨hz1, hz2⟩, hz3⟩ := hz
  simp only [mem_iInter₂, mem_ofPred_eq] at hz1 hz2 hz3
  apply DifferentiableAt.differentiableWithinAt
  unfold Gq
  have hD : DifferentiableAt ℂ
      (fun w => LFunctionResidueClassAux b (w + 1) - (q.totient : ℂ)⁻¹) z :=
    ((aux_differentiableAt b hz2 hz3).comp z (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => w + 1) z)).sub_const _
  exact hD.div (by fun_prop) hz1

theorem Gq_eq (b : ZMod q) (hb : IsUnit b) {z : ℂ} (hz : 0 < z.re) :
    Gq b z = Gint (fun x => psiAP b x / x - (q.totient : ℝ)⁻¹) z := by
  set s := z + 1 with hsdef
  have hs : 1 < s.re := by simp [hsdef]; linarith
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have hs0 : s ≠ 0 := fun h => by simp [h] at hs; linarith
  have hre : (-z - 1).re < -1 := by simp; linarith
  have I1 : IntegrableOn (fun t : ℝ => ((psiAP b t / t : ℝ) : ℂ) * (t : ℂ) ^ (-z - 1)) (Ioi 1) :=
    integrableOn_integrand ((psiAP_measurable b).div measurable_id)
      (fun x hx => psiAP_div_bound b hx) hz le_rfl
  have I2 : IntegrableOn (fun t : ℝ => ((q.totient : ℝ)⁻¹ : ℂ) * (t : ℂ) ^ (-z - 1)) (Ioi 1) :=
    (integrableOn_Ioi_cpow_of_lt hre one_pos).const_mul _
  have h1 : Gint (fun x => psiAP b x / x - (q.totient : ℝ)⁻¹) z =
      (∫ t in Ioi (1 : ℝ), ((psiAP b t / t : ℝ) : ℂ) * (t : ℂ) ^ (-z - 1)) -
        ∫ t in Ioi (1 : ℝ), ((q.totient : ℝ)⁻¹ : ℂ) * (t : ℂ) ^ (-z - 1) := by
    unfold Gint
    rw [← integral_sub I1 I2]
    congr 1; ext t; push_cast; ring
  have h2 : ∫ t in Ioi (1 : ℝ), ((q.totient : ℝ)⁻¹ : ℂ) * (t : ℂ) ^ (-z - 1) =
      ((q.totient : ℝ)⁻¹ : ℂ) / z := by
    rw [integral_const_mul, integral_Ioi_cpow_of_lt hre one_pos]
    simp only [ofReal_one, one_cpow, sub_add_cancel]
    field_simp
  have h3 : ∫ t in Ioi (1 : ℝ), ((psiAP b t / t : ℝ) : ℂ) * (t : ℂ) ^ (-z - 1) =
      ∫ t in Ioi (1 : ℝ), (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ((residueClass b k : ℝ) : ℂ)) *
        (t : ℂ) ^ (-(s + 1)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by simp at ht; linarith)
    have e : -(s + 1) = (-z - 1) - 1 := by rw [hsdef]; ring
    simp only [e, cpow_sub _ _ ht0, cpow_one, psiAP]
    push_cast
    field_simp
  have hS : LSeriesSummable (fun n : ℕ => ((residueClass b n : ℝ) : ℂ)) s :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re
      ((abscissaOfAbsConv_residueClass_le_one b).trans_lt (by exact_mod_cast hs))
  have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, (fun n : ℕ => ((residueClass b n : ℝ) : ℂ)) k) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ (1 : ℝ) := by
    refine Asymptotics.IsBigO.of_bound (Real.log 4 + 4) (Eventually.of_forall fun n => ?_)
    have e : (∑ k ∈ Finset.Icc 1 n, (fun n : ℕ => ((residueClass b n : ℝ) : ℂ)) k) = ((psiAP b n : ℝ) : ℂ) := by
      simp [psiAP, Nat.floor_natCast]
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (psiAP_nonneg b _),
      Real.rpow_one, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    exact psiAP_le b (Nat.cast_nonneg _)
  have h4 := LSeries_eq_mul_integral (fun n : ℕ => ((residueClass b n : ℝ) : ℂ)) zero_le_one hs hS hO
  have h5 := eqOn_LFunctionResidueClassAux hb (show s ∈ {s : ℂ | 1 < s.re} from hs)
  simp only at h5
  have hsz : s - 1 = z := by rw [hsdef]; ring
  rw [hsz] at h5
  rw [h1, h2, h3]
  unfold Gq
  rw [← hsdef, h5, h4]
  push_cast
  field_simp
  ring

/-- **Prime number theorem in arithmetic progressions**: `ψ(x; q, b) / x → 1/φ(q)`. -/
theorem tendsto_psiAP (b : ZMod q) (hb : IsUnit b) :
    Tendsto (fun x => psiAP b x / x) atTop (𝓝 (q.totient : ℝ)⁻¹) := by
  have hc : 0 < (q.totient : ℝ)⁻¹ := by
    have : 0 < q.totient := Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
    positivity
  exact taub hc (psiAP_mono b)
    (newman_real (A_measurable b) (fun x hx => A_bound b hx) Uq_open (fun z hz => mem_Uq hz)
      (Gq_differentiableOn b) (fun z hz => Gq_eq b hb hz))

end application

/-! ## The Prime Number Theorem -/

section pnt

theorem psiAP_one (x : ℝ) : psiAP (1 : ZMod 1) x = Chebyshev.psi x := by
  rw [psiAP, Chebyshev.psi, Icc_one_eq_Ioc_zero]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact Set.indicator_of_mem (s := {n : ℕ | (n : ZMod 1) = 1}) (Subsingleton.elim _ _) _

/-- `ψ(x) / x → 1`. -/
theorem tendsto_psi_div : Tendsto (fun x => Chebyshev.psi x / x) atTop (𝓝 1) := by
  have := tendsto_psiAP (q := 1) (1 : ZMod 1) isUnit_one
  simpa [psiAP_one] using this

/-- `θ(x) / x → 1`. -/
theorem tendsto_theta_div : Tendsto (fun x => Chebyshev.theta x / x) atTop (𝓝 1) := by
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  have h0 : Tendsto (fun x => (Chebyshev.psi x - Chebyshev.theta x) / x) atTop (𝓝 0) := by
    have hlim : Tendsto (fun x : ℝ => C / Real.sqrt x) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
    refine squeeze_zero' ?_ ?_ hlim
    · filter_upwards [eventually_gt_atTop 0] with x hx
      exact div_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi x)) hx.le
    · filter_upwards [eventually_gt_atTop 0] with x hx
      have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
      have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx.le
      calc (Chebyshev.psi x - Chebyshev.theta x) / x ≤ C * Real.sqrt x / x :=
            div_le_div_of_nonneg_right (hC x) hx.le
        _ = C / Real.sqrt x := by
            rw [div_eq_div_iff hx.ne' hs.ne', mul_assoc, hsq]
  have := tendsto_psi_div.sub h0
  simp only [sub_zero] at this
  refine this.congr fun x => ?_
  ring

/-- **Prime Number Theorem**: `π(x) / (x / log x) → 1`. -/
theorem tendsto_primeCounting_div : Tendsto
    (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ) / (x / Real.log x)) atTop (𝓝 1) := by
  obtain ⟨C, hC⟩ := Chebyshev.primeCounting_sub_theta_div_log_isBigO.bound
  have hE : Tendsto (fun x => ((Nat.primeCounting ⌊x⌋₊ : ℝ) - Chebyshev.theta x / Real.log x) *
      (Real.log x / x)) atTop (𝓝 0) := by
    have hlim : Tendsto (fun x : ℝ => |C| / Real.log x) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [hC, eventually_gt_atTop 1] with x hx hx1
    have hl : 0 < Real.log x := Real.log_pos hx1
    have hx0 : 0 < x := by linarith
    rw [norm_mul, Real.norm_eq_abs (Real.log x / x), abs_of_pos (by positivity)]
    rw [Real.norm_eq_abs (x / Real.log x ^ 2), abs_of_pos (by positivity)] at hx
    calc _ ≤ C * (x / Real.log x ^ 2) * (Real.log x / x) :=
          mul_le_mul_of_nonneg_right hx (by positivity)
      _ = C / Real.log x := by field_simp
      _ ≤ |C| / Real.log x := div_le_div_of_nonneg_right (le_abs_self C) hl.le
  have := tendsto_theta_div.add hE
  simp only [add_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with x hx
  have hl : 0 < Real.log x := Real.log_pos hx
  have hx0 : 0 < x := by linarith
  field_simp
  ring

/-- **Prime Number Theorem**, asymptotic-equivalence form: `π(x) ~ x / log x`. -/
theorem primeCounting_isEquivalent : (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ)) ~[atTop]
    (fun x : ℝ => x / Real.log x) :=
  isEquivalent_of_tendsto_one tendsto_primeCounting_div

/-- **Prime Number Theorem** for natural numbers: `π(n) / (n / log n) → 1`. -/
theorem tendsto_primeCounting_nat : Tendsto
    (fun n : ℕ => (Nat.primeCounting n : ℝ) / ((n : ℝ) / Real.log n)) atTop (𝓝 1) := by
  have := tendsto_primeCounting_div.comp tendsto_natCast_atTop_atTop
  refine this.congr fun n => ?_
  simp [Function.comp, Nat.floor_natCast]

end pnt

end OMAPNT

end kitPNT

section kitLS
/-!
# The arithmetic large sieve (OMA kit)

* `OMALargeSieve.large_sieve_points` : analytic large sieve for `δ`-separated points,
  `∑_r |∑_{n ∈ F} c_n e(n x_r)|² ≤ (N + 2/δ) ∑ |c_n|²` for `F` inside `N` consecutive integers.
* `OMALargeSieve.large_sieve_farey` : the Farey version
  `∑_{q ≤ Q} ∑_{(a,q)=1} |S(a/q)|² ≤ (N + 2Q²) ∑ |c_n|²`.

Proof: duality + a trapezoid (box * box) majorant of the interval, whose kernel decays like
`1/‖θ‖²`; the separated points then contribute `∑ 1/(kδ)² ≤ 2/δ²` on each side.
-/

namespace OMALargeSieve

open Finset Complex

/-- `e(x) = exp(2πix)`. -/
noncomputable def e (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x)

/-- Distance to the nearest integer. -/
noncomputable def dist1 (x : ℝ) : ℝ := |x - round x|

lemma e_add (x y : ℝ) : e (x + y) = e x * e y := by
  unfold e; rw [← Complex.exp_add]; congr 1; push_cast; ring

lemma e_zero : e 0 = 1 := by simp [e]

lemma e_int (k : ℤ) : e k = 1 := by
  unfold e
  rw [show (2 * Real.pi * Complex.I * ((k : ℝ) : ℂ)) = (k : ℂ) * (2 * Real.pi * Complex.I) by
    push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I k

lemma e_add_int (x : ℝ) (k : ℤ) : e (x + k) = e x := by
  rw [e_add, e_int, mul_one]

lemma norm_e (x : ℝ) : ‖e x‖ = 1 := by
  unfold e
  rw [show (2 * Real.pi * Complex.I * (x : ℂ)) = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

lemma conj_e (x : ℝ) : (starRingEnd ℂ) (e x) = e (-x) := by
  unfold e
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
  push_cast; ring

lemma e_nat_mul (n : ℕ) (x : ℝ) : e (n * x) = e x ^ n := by
  unfold e
  rw [← Complex.exp_nat_mul]
  congr 1; push_cast; ring

lemma dist1_nonneg (x : ℝ) : 0 ≤ dist1 x := abs_nonneg _

lemma dist1_le (x : ℝ) (k : ℤ) : dist1 x ≤ |x - k| := round_le x k

lemma dist1_le_half (x : ℝ) : dist1 x ≤ 1 / 2 := abs_sub_round x

lemma dist1_neg (x : ℝ) : dist1 (-x) = dist1 x := by
  apply le_antisymm
  · have := dist1_le (-x) (-round x)
    rw [show -x - ((-round x : ℤ) : ℝ) = -(x - round x) by push_cast; ring, abs_neg] at this
    exact this
  · have := dist1_le x (-round (-x))
    rw [show x - ((-round (-x) : ℤ) : ℝ) = -(-x - round (-x)) by push_cast; ring, abs_neg] at this
    exact this

lemma dist1_sub_comm (x y : ℝ) : dist1 (x - y) = dist1 (y - x) := by
  rw [← dist1_neg, neg_sub]

/-- `|e(x) - 1| ≥ 4 ‖x‖`. -/
lemma four_dist1_le_norm_e_sub_one (x : ℝ) : 4 * dist1 x ≤ ‖e x - 1‖ := by
  set t := x - round x with ht
  have hx : e x = e t := by
    rw [ht, show x - (round x : ℝ) = x + ((-round x : ℤ) : ℝ) by push_cast; ring, e_add_int]
  have ht2 : |t| ≤ 1 / 2 := abs_sub_round x
  have hnorm : ‖e t - 1‖ = ‖2 * Real.sin (Real.pi * t)‖ := by
    unfold e
    rw [show (2 * Real.pi * Complex.I * (t : ℂ)) = Complex.I * ((2 * Real.pi * t : ℝ) : ℂ) by
      push_cast; ring, Complex.norm_exp_I_mul_ofReal_sub_one]
    congr 2; ring_nf
  rw [hx, hnorm, Real.norm_eq_abs, abs_mul, abs_two]
  unfold dist1
  rw [← ht]
  have hpi := Real.pi_pos
  rcases le_total 0 t with h0 | h0
  · have h1 : 0 ≤ Real.pi * t := by positivity
    have h2 : Real.pi * t ≤ Real.pi / 2 := by
      rw [abs_of_nonneg h0] at ht2; nlinarith
    have := Real.mul_le_sin h1 h2
    rw [abs_of_nonneg h0, abs_of_nonneg (le_trans (mul_nonneg (by positivity) h1) this)]
    have : 2 / Real.pi * (Real.pi * t) = 2 * t := by field_simp
    linarith
  · have h1 : 0 ≤ Real.pi * (-t) := by nlinarith
    have h2 : Real.pi * (-t) ≤ Real.pi / 2 := by
      rw [abs_of_nonpos h0] at ht2; nlinarith
    have := Real.mul_le_sin h1 h2
    rw [show Real.pi * (-t) = -(Real.pi * t) by ring, Real.sin_neg] at this
    have hs : 0 ≤ -Real.sin (Real.pi * t) :=
      le_trans (mul_nonneg (by positivity) (by linarith : 0 ≤ -(Real.pi * t))) this
    rw [abs_of_nonpos h0, abs_of_nonpos (by linarith)]
    have : 2 / Real.pi * -(Real.pi * t) = 2 * (-t) := by field_simp
    linarith

/-- Geometric sum bound `|∑_{m<A} e(mx)| ≤ 1/(2‖x‖)`. -/
lemma norm_sum_e_le (A : ℕ) (x : ℝ) (hx : 0 < dist1 x) :
    ‖∑ m ∈ range A, e (m * x)‖ ≤ 1 / (2 * dist1 x) := by
  have h4 := four_dist1_le_norm_e_sub_one x
  have hne : e x - 1 ≠ 0 := by
    intro h; rw [h, norm_zero] at h4; linarith
  have hne' : e x ≠ 1 := sub_ne_zero.mp hne
  simp_rw [e_nat_mul]
  rw [geom_sum_eq hne', norm_div]
  have hnum : ‖e x ^ A - 1‖ ≤ 2 := by
    calc ‖e x ^ A - 1‖ ≤ ‖e x ^ A‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, norm_e, one_pow, norm_one]; norm_num
  have hpos : 0 < ‖e x - 1‖ := by linarith
  rw [div_le_div_iff₀ hpos (by positivity)]
  nlinarith

/-! ### Counting separated points -/

lemma sum_inv_sq_nat_le (s : Finset ℕ) (hs : ∀ i ∈ s, 0 < i) :
    ∑ i ∈ s, ((i : ℝ) ^ 2)⁻¹ ≤ 2 := by
  set K := s.sup id
  have hsub : s ⊆ Ioo 0 (K + 1) := by
    intro i hi
    rw [mem_Ioo]
    exact ⟨hs i hi, Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)⟩
  calc ∑ i ∈ s, ((i : ℝ) ^ 2)⁻¹ ≤ ∑ i ∈ Ioo 0 (K + 1), ((i : ℝ) ^ 2)⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ 2 / ((0 : ℕ) + 1 : ℝ) := sum_Ioo_inv_sq_le 0 (K + 1)
    _ = 2 := by norm_num

/-- Points `t_s ≥ δ`, pairwise `δ`-separated: `∑ 1/t_s² ≤ 2/δ²`. -/
lemma sum_inv_sq_sep {ι : Type*} (S : Finset ι) (t : ι → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hpos : ∀ s ∈ S, δ ≤ t s)
    (hsep : ∀ s ∈ S, ∀ s' ∈ S, s ≠ s' → δ ≤ |t s - t s'|) :
    ∑ s ∈ S, 1 / t s ^ 2 ≤ 2 / δ ^ 2 := by
  set k : ι → ℕ := fun s => ⌊t s / δ⌋₊ with hk
  have hk1 : ∀ s ∈ S, 1 ≤ k s := by
    intro s hs
    have : (1 : ℝ) ≤ t s / δ := by rw [le_div_iff₀ hδ]; linarith [hpos s hs]
    exact Nat.le_floor (by exact_mod_cast this)
  have hkle : ∀ s ∈ S, (k s : ℝ) * δ ≤ t s := by
    intro s hs
    have h0 : 0 ≤ t s / δ := div_nonneg (by linarith [hpos s hs]) hδ.le
    have := Nat.floor_le h0
    rw [le_div_iff₀ hδ] at this
    exact this
  have hinj : Set.InjOn k S := by
    intro s hs s' hs' hss
    by_contra hne
    have h1 := Nat.floor_le (div_nonneg (by linarith [hpos s hs]) hδ.le : 0 ≤ t s / δ)
    have h2 := Nat.lt_floor_add_one (t s / δ)
    have h3 := Nat.floor_le (div_nonneg (by linarith [hpos s' hs']) hδ.le : 0 ≤ t s' / δ)
    have h4 := Nat.lt_floor_add_one (t s' / δ)
    have hkk : (⌊t s / δ⌋₊ : ℝ) = ⌊t s' / δ⌋₊ := by exact_mod_cast hss
    have hlt : |t s / δ - t s' / δ| < 1 := by
      rw [abs_lt]; constructor <;> linarith
    have := hsep s hs s' hs' hne
    rw [← sub_div, abs_div, abs_of_pos hδ, div_lt_one hδ] at hlt
    linarith
  have hterm : ∀ s ∈ S, 1 / t s ^ 2 ≤ (1 / δ ^ 2) * ((k s : ℝ) ^ 2)⁻¹ := by
    intro s hs
    have hk0 : (0 : ℝ) < k s := by exact_mod_cast hk1 s hs
    have hkd := hkle s hs
    have hpos' : 0 < (k s : ℝ) * δ := by positivity
    have : ((k s : ℝ) * δ) ^ 2 ≤ t s ^ 2 := pow_le_pow_left₀ hpos'.le hkd 2
    calc 1 / t s ^ 2 ≤ 1 / ((k s : ℝ) * δ) ^ 2 := one_div_le_one_div_of_le (by positivity) this
      _ = (1 / δ ^ 2) * ((k s : ℝ) ^ 2)⁻¹ := by rw [mul_pow]; field_simp
  calc ∑ s ∈ S, 1 / t s ^ 2 ≤ ∑ s ∈ S, (1 / δ ^ 2) * ((k s : ℝ) ^ 2)⁻¹ :=
        Finset.sum_le_sum hterm
    _ = (1 / δ ^ 2) * ∑ i ∈ S.image k, ((i : ℝ) ^ 2)⁻¹ := by
        rw [← Finset.mul_sum, Finset.sum_image (fun a ha b hb h => hinj ha hb h)]
    _ ≤ (1 / δ ^ 2) * 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply sum_inv_sq_nat_le
        intro i hi
        obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hi
        exact hk1 s hs
    _ = 2 / δ ^ 2 := by ring

/-- Separated points on the circle: `∑_{s ≠ r} 1/‖x_r - x_s‖² ≤ 4/δ²`. -/
lemma sum_inv_sq_dist1_le {ι : Type*} [DecidableEq ι] (R : Finset ι) (x : ι → ℝ) (δ : ℝ)
    (hδ : 0 < δ) (hsep : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → δ ≤ dist1 (x r - x s)) (r : ι)
    (hr : r ∈ R) :
    ∑ s ∈ R.erase r, 1 / dist1 (x r - x s) ^ 2 ≤ 4 / δ ^ 2 := by
  set t : ι → ℝ := fun s => (x s - x r) - round (x s - x r) with ht
  have habs : ∀ s, dist1 (x r - x s) = |t s| := by
    intro s; rw [dist1_sub_comm]; rfl
  have hge : ∀ s ∈ R.erase r, δ ≤ |t s| := by
    intro s hs
    rw [← habs]
    obtain ⟨hne, hs'⟩ := Finset.mem_erase.mp hs
    exact hsep r hr s hs' (Ne.symm hne)
  have hsep' : ∀ s ∈ R.erase r, ∀ s' ∈ R.erase r, s ≠ s' → δ ≤ |t s - t s'| := by
    intro s hs s' hs' hne
    have h1 := hsep s (Finset.mem_of_mem_erase hs) s' (Finset.mem_of_mem_erase hs') hne
    have h2 := dist1_le (x s - x s') (round (x s - x r) - round (x s' - x r))
    have : t s - t s' = (x s - x s') - (((round (x s - x r) - round (x s' - x r) : ℤ)) : ℝ) := by
      simp only [ht]; push_cast; ring
    rw [this]; linarith
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun s => 0 < t s)]
  have hP : ∑ s ∈ (R.erase r).filter (fun s => 0 < t s), 1 / dist1 (x r - x s) ^ 2
      ≤ 2 / δ ^ 2 := by
    have := sum_inv_sq_sep ((R.erase r).filter (fun s => 0 < t s)) t δ hδ
      (by
        intro s hs
        obtain ⟨hs1, hs2⟩ := Finset.mem_filter.mp hs
        have := hge s hs1; rwa [abs_of_pos hs2] at this)
      (by
        intro s hs s' hs' hne
        exact hsep' s (Finset.mem_filter.mp hs).1 s' (Finset.mem_filter.mp hs').1 hne)
    refine le_trans (le_of_eq ?_) this
    apply Finset.sum_congr rfl
    intro s hs
    rw [habs, abs_of_pos (Finset.mem_filter.mp hs).2]
  have hN : ∑ s ∈ (R.erase r).filter (fun s => ¬ 0 < t s), 1 / dist1 (x r - x s) ^ 2
      ≤ 2 / δ ^ 2 := by
    have := sum_inv_sq_sep ((R.erase r).filter (fun s => ¬ 0 < t s)) (fun s => - t s) δ hδ
      (by
        intro s hs
        obtain ⟨hs1, hs2⟩ := Finset.mem_filter.mp hs
        have := hge s hs1; rwa [abs_of_nonpos (not_lt.mp hs2)] at this)
      (by
        intro s hs s' hs' hne
        have := hsep' s (Finset.mem_filter.mp hs).1 s' (Finset.mem_filter.mp hs').1 hne
        rwa [show -t s - -t s' = -(t s - t s') by ring, abs_neg])
    refine le_trans (le_of_eq ?_) this
    apply Finset.sum_congr rfl
    intro s hs
    rw [habs, abs_of_nonpos (not_lt.mp (Finset.mem_filter.mp hs).2)]
  have h4 : 4 / δ ^ 2 = 2 / δ ^ 2 + 2 / δ ^ 2 := by ring
  linarith

/-! ### The dual inequality -/

/-- The trapezoid kernel `K(θ) = ∑_{j<H} ∑_{m<A} e((M+m-j)θ)`. -/
noncomputable def kernel (M : ℤ) (A H : ℕ) (θ : ℝ) : ℂ :=
  ∑ j ∈ range H, ∑ m ∈ range A, e (((M + m - j : ℤ) : ℝ) * θ)

lemma norm_kernel_le_triv (M : ℤ) (A H : ℕ) (θ : ℝ) : ‖kernel M A H θ‖ ≤ H * A := by
  unfold kernel
  calc ‖∑ j ∈ range H, ∑ m ∈ range A, e (((M + m - j : ℤ) : ℝ) * θ)‖
      ≤ ∑ j ∈ range H, ‖∑ m ∈ range A, e (((M + m - j : ℤ) : ℝ) * θ)‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ range H, ∑ m ∈ range A, ‖e (((M + m - j : ℤ) : ℝ) * θ)‖ :=
        Finset.sum_le_sum (fun _ _ => norm_sum_le _ _)
    _ = H * A := by simp [norm_e]

lemma norm_kernel_le (M : ℤ) (A H : ℕ) (θ : ℝ) (hθ : 0 < dist1 θ) :
    ‖kernel M A H θ‖ ≤ 1 / (4 * dist1 θ ^ 2) := by
  unfold kernel
  have hrw : ∀ j m : ℕ, e (((M + m - j : ℤ) : ℝ) * θ) =
      e (M * θ) * (e (m * θ) * e (j * (-θ))) := by
    intro j m; rw [← e_add, ← e_add]; congr 1; push_cast; ring
  simp_rw [hrw]
  have hfac : (∑ j ∈ range H, ∑ m ∈ range A, e (M * θ) * (e (m * θ) * e (j * (-θ)))) =
      e (M * θ) * ((∑ m ∈ range A, e (m * θ)) * ∑ j ∈ range H, e (j * (-θ))) := by
    rw [Finset.sum_mul_sum, Finset.mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.mul_sum]
  rw [hfac, norm_mul, norm_mul, norm_e, one_mul]
  have h1 := norm_sum_e_le A θ hθ
  have h2 := norm_sum_e_le H (-θ) (by rwa [dist1_neg])
  rw [dist1_neg] at h2
  calc ‖∑ m ∈ range A, e (m * θ)‖ * ‖∑ j ∈ range H, e (j * (-θ))‖
      ≤ (1 / (2 * dist1 θ)) * (1 / (2 * dist1 θ)) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = 1 / (4 * dist1 θ ^ 2) := by field_simp; ring

lemma sum_sym_le {ι : Type*} (R : Finset ι) (u : ι → ℝ) (κ : ι → ι → ℝ)
    (hκ : ∀ r s, κ r s = κ s r) (hκ0 : ∀ r s, 0 ≤ κ r s) :
    ∑ r ∈ R, ∑ s ∈ R, u r * u s * κ r s ≤ ∑ r ∈ R, ∑ s ∈ R, u r ^ 2 * κ r s := by
  have h2 : ∑ r ∈ R, ∑ s ∈ R, u s ^ 2 * κ r s = ∑ r ∈ R, ∑ s ∈ R, u r ^ 2 * κ r s := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun s _ => by rw [hκ]))
  calc ∑ r ∈ R, ∑ s ∈ R, u r * u s * κ r s
      ≤ ∑ r ∈ R, ∑ s ∈ R, (u r ^ 2 * κ r s / 2 + u s ^ 2 * κ r s / 2) := by
        apply Finset.sum_le_sum; intro r _; apply Finset.sum_le_sum; intro s _
        have := hκ0 r s
        nlinarith [sq_nonneg (u r - u s), mul_nonneg this (sq_nonneg (u r - u s))]
    _ = (∑ r ∈ R, ∑ s ∈ R, u r ^ 2 * κ r s) / 2 + (∑ r ∈ R, ∑ s ∈ R, u s ^ 2 * κ r s) / 2 := by
        simp only [Finset.sum_add_distrib, Finset.sum_div]
    _ = ∑ r ∈ R, ∑ s ∈ R, u r ^ 2 * κ r s := by rw [h2]; ring

/-- **Dual large sieve** for `δ`-separated points. -/
theorem dual_large_sieve {ι : Type*} [DecidableEq ι] (R : Finset ι) (x : ι → ℝ) (δ : ℝ)
    (hδ : 0 < δ) (hsep : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → δ ≤ dist1 (x r - x s)) (M : ℤ) (N : ℕ)
    (b : ι → ℂ) :
    ∑ n ∈ range N, ‖∑ r ∈ R, b r * e (((M + n : ℤ) : ℝ) * x r)‖ ^ 2
      ≤ (N + 2 / δ) * ∑ r ∈ R, ‖b r‖ ^ 2 := by
  set T : ℤ → ℂ := fun t => ∑ r ∈ R, b r * e ((t : ℝ) * x r) with hT
  show ∑ n ∈ range N, ‖T (M + n)‖ ^ 2 ≤ (N + 2 / δ) * ∑ r ∈ R, ‖b r‖ ^ 2
  set H := ⌈1 / δ⌉₊ with hHdef
  have hH1 : 1 ≤ H := Nat.ceil_pos.mpr (by positivity)
  have hHge : 1 / δ ≤ H := Nat.le_ceil _
  have hHlt : (H : ℝ) < 1 / δ + 1 := Nat.ceil_lt_add_one (by positivity)
  set A := N + H - 1 with hAdef
  have hAcast : (A : ℝ) = N + H - 1 := by
    rw [hAdef, Nat.cast_sub (by omega)]; push_cast; ring
  set X := ∑ n ∈ range N, ‖T (M + n)‖ ^ 2 with hX
  set B := ∑ r ∈ R, ‖b r‖ ^ 2 with hB
  have hB0 : 0 ≤ B := by positivity
  -- step 1: averaging over shifts
  have step1 : (H : ℝ) * X ≤ ∑ j ∈ range H, ∑ m ∈ range A, ‖T (M + m - j)‖ ^ 2 := by
    have : (H : ℝ) * X = ∑ j ∈ range H, X := by simp
    rw [this]
    apply Finset.sum_le_sum
    intro j hj
    have hjH := Finset.mem_range.mp hj
    calc X = ∑ m ∈ Ico j (j + N), ‖T (M + m - j)‖ ^ 2 := by
          rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left, hX]
          refine Finset.sum_congr rfl (fun n _ => ?_)
          congr 3; push_cast; ring
      _ ≤ ∑ m ∈ range A, ‖T (M + m - j)‖ ^ 2 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro m hm; rw [Finset.mem_Ico] at hm; rw [Finset.mem_range]; omega
          · intros; positivity
  -- step 2: expansion
  have hexp : ∀ t : ℤ, ((‖T t‖ ^ 2 : ℝ) : ℂ) = ∑ p ∈ R ×ˢ R,
      b p.1 * (starRingEnd ℂ) (b p.2) * e ((t : ℝ) * (x p.1 - x p.2)) := by
    intro t
    rw [Complex.ofReal_pow, ← Complex.mul_conj', Finset.sum_product]
    simp only [hT, map_sum, map_mul, conj_e, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun s _ => ?_))
    rw [show (t : ℝ) * (x r - x s) = t * x r + -(t * x s) by ring, e_add]; ring
  have step2 : ((∑ j ∈ range H, ∑ m ∈ range A, ‖T (M + m - j)‖ ^ 2 : ℝ) : ℂ) =
      ∑ p ∈ R ×ˢ R, b p.1 * (starRingEnd ℂ) (b p.2) * kernel M A H (x p.1 - x p.2) := by
    simp_rw [Complex.ofReal_sum, hexp, kernel, Finset.mul_sum]
    conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
  -- step 3: bound the kernel
  set κ : ι → ι → ℝ := fun r s => if r = s then (H : ℝ) * A else 1 / (4 * dist1 (x r - x s) ^ 2)
    with hκ
  have hκsym : ∀ r s, κ r s = κ s r := by
    intro r s
    simp only [hκ]
    by_cases h : r = s
    · subst h; rfl
    · rw [if_neg h, if_neg (Ne.symm h), dist1_sub_comm]
  have hκ0 : ∀ r s, 0 ≤ κ r s := by
    intro r s; simp only [hκ]; split_ifs <;> positivity
  have hK : ∀ r ∈ R, ∀ s ∈ R, ‖kernel M A H (x r - x s)‖ ≤ κ r s := by
    intro r hr s hs
    simp only [hκ]
    split_ifs with h
    · exact norm_kernel_le_triv M A H _
    · exact norm_kernel_le M A H _ (lt_of_lt_of_le hδ (hsep r hr s hs h))
  have step3 : ∑ j ∈ range H, ∑ m ∈ range A, ‖T (M + m - j)‖ ^ 2 ≤
      ∑ r ∈ R, ∑ s ∈ R, ‖b r‖ * ‖b s‖ * κ r s := by
    set Y := ∑ j ∈ range H, ∑ m ∈ range A, ‖T (M + m - j)‖ ^ 2
    calc Y ≤ ‖(Y : ℂ)‖ := by rw [Complex.norm_real]; exact le_abs_self _
      _ = ‖∑ p ∈ R ×ˢ R, b p.1 * (starRingEnd ℂ) (b p.2) * kernel M A H (x p.1 - x p.2)‖ := by
          rw [step2]
      _ ≤ ∑ p ∈ R ×ˢ R, ‖b p.1 * (starRingEnd ℂ) (b p.2) * kernel M A H (x p.1 - x p.2)‖ :=
          norm_sum_le _ _
      _ = ∑ r ∈ R, ∑ s ∈ R, ‖b r‖ * ‖b s‖ * ‖kernel M A H (x r - x s)‖ := by
          rw [Finset.sum_product]; simp
      _ ≤ ∑ r ∈ R, ∑ s ∈ R, ‖b r‖ * ‖b s‖ * κ r s := by
          apply Finset.sum_le_sum; intro r hr; apply Finset.sum_le_sum; intro s hs
          exact mul_le_mul_of_nonneg_left (hK r hr s hs) (by positivity)
  have step4 : ∑ r ∈ R, ∑ s ∈ R, ‖b r‖ * ‖b s‖ * κ r s ≤ (H * A + 1 / δ ^ 2) * B := by
    refine (sum_sym_le R (fun r => ‖b r‖) κ hκsym hκ0).trans ?_
    rw [hB, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro r hr
    rw [← Finset.mul_sum, mul_comm]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    rw [← Finset.add_sum_erase _ _ hr]
    have hrr : κ r r = H * A := by simp [hκ]
    have herase : ∑ s ∈ R.erase r, κ r s = (1 / 4) * ∑ s ∈ R.erase r, 1 / dist1 (x r - x s) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun s hs => ?_)
      have hne : r ≠ s := Ne.symm (Finset.ne_of_mem_erase hs)
      simp only [hκ, if_neg hne]
      field_simp
    rw [hrr, herase]
    have := sum_inv_sq_dist1_le R x δ hδ hsep r hr
    have h4 : (1 / 4 : ℝ) * (4 / δ ^ 2) = 1 / δ ^ 2 := by field_simp
    nlinarith
  -- step 5: conclude
  have hHpos : (0 : ℝ) < H := by exact_mod_cast hH1
  have hfin : (H : ℝ) * A + 1 / δ ^ 2 ≤ H * (N + 2 / δ) := by
    rw [hAcast]
    set d := 1 / δ with hd
    have hd2 : 1 / δ ^ 2 = d ^ 2 := by rw [hd]; field_simp
    have h2d : 2 / δ = 2 * d := by rw [hd]; ring
    rw [hd2, h2d]
    have hdpos : 0 < d := by rw [hd]; positivity
    nlinarith [mul_nonneg (sub_nonneg.mpr hHge) (by linarith : (0:ℝ) ≤ d + 1 - H)]
  have : (H : ℝ) * X ≤ H * ((N + 2 / δ) * B) := by
    calc (H : ℝ) * X ≤ (H * A + 1 / δ ^ 2) * B := step1.trans (step3.trans step4)
      _ ≤ (H * (N + 2 / δ)) * B := mul_le_mul_of_nonneg_right hfin hB0
      _ = H * ((N + 2 / δ) * B) := by ring
  exact le_of_mul_le_mul_left this hHpos

/-- **Analytic large sieve** for `δ`-separated points: for `F` inside an interval of `N`
consecutive integers, `∑_r |∑_{n∈F} c_n e(n x_r)|² ≤ (N + 2/δ) ∑_{n∈F} |c_n|²`. -/
theorem large_sieve_points {ι : Type*} [DecidableEq ι] (R : Finset ι) (x : ι → ℝ) (δ : ℝ)
    (hδ : 0 < δ) (hsep : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → δ ≤ dist1 (x r - x s)) (M N : ℕ)
    (F : Finset ℕ) (hF : F ⊆ Ico M (M + N)) (c : ℕ → ℂ) :
    ∑ r ∈ R, ‖∑ n ∈ F, c n * e (n * x r)‖ ^ 2 ≤ (N + 2 / δ) * ∑ n ∈ F, ‖c n‖ ^ 2 := by
  set S : ι → ℂ := fun r => ∑ n ∈ F, c n * e (n * x r) with hS
  show ∑ r ∈ R, ‖S r‖ ^ 2 ≤ (N + 2 / δ) * ∑ n ∈ F, ‖c n‖ ^ 2
  set B := ∑ r ∈ R, ‖S r‖ ^ 2 with hB
  set C := ∑ n ∈ F, ‖c n‖ ^ 2 with hC
  set T : ℕ → ℂ := fun n => ∑ r ∈ R, (starRingEnd ℂ) (S r) * e (n * x r) with hT
  have hBC : (B : ℂ) = ∑ n ∈ F, c n * T n := by
    rw [hB, Complex.ofReal_sum]
    simp_rw [Complex.ofReal_pow, ← Complex.mul_conj']
    simp only [hT, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [hS, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun n _ => by ring)
  have hB0 : 0 ≤ B := by positivity
  have h1 : B ≤ ∑ n ∈ F, ‖c n‖ * ‖T n‖ := by
    calc B = ‖(B : ℂ)‖ := by rw [Complex.norm_real, Real.norm_of_nonneg hB0]
      _ = ‖∑ n ∈ F, c n * T n‖ := by rw [hBC]
      _ ≤ ∑ n ∈ F, ‖c n * T n‖ := norm_sum_le _ _
      _ = ∑ n ∈ F, ‖c n‖ * ‖T n‖ := by simp
  have h2 : B ^ 2 ≤ C * ∑ n ∈ F, ‖T n‖ ^ 2 :=
    (pow_le_pow_left₀ hB0 h1 2).trans (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)
  have h3 : ∑ n ∈ F, ‖T n‖ ^ 2 ≤ (N + 2 / δ) * B := by
    calc ∑ n ∈ F, ‖T n‖ ^ 2 ≤ ∑ n ∈ Ico M (M + N), ‖T n‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hF (by intros; positivity)
      _ = ∑ i ∈ range N, ‖∑ r ∈ R, (starRingEnd ℂ) (S r) * e ((((M : ℤ) + i : ℤ) : ℝ) * x r)‖ ^ 2 := by
          rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          simp only [hT]; push_cast; rfl
      _ ≤ (N + 2 / δ) * ∑ r ∈ R, ‖(starRingEnd ℂ) (S r)‖ ^ 2 :=
          dual_large_sieve R x δ hδ hsep M N _
      _ = (N + 2 / δ) * B := by simp [hB]
  have hK : 0 ≤ (N : ℝ) + 2 / δ := by positivity
  rcases hB0.lt_or_eq with hBpos | hBz
  · have : B * B ≤ (C * (N + 2 / δ)) * B := by
      calc B * B = B ^ 2 := by ring
        _ ≤ C * ((N + 2 / δ) * B) := h2.trans (mul_le_mul_of_nonneg_left h3 (by positivity))
        _ = (C * (N + 2 / δ)) * B := by ring
    have := le_of_mul_le_mul_right this hBpos
    linarith
  · rw [← hBz]; positivity

/-- Farey fractions `a/q`, `q ≤ Q`, `(a,q) = 1`, are `1/Q²`-separated. -/
lemma farey_sep (Q : ℕ) (q a q' a' : ℕ) (hq : 1 ≤ q) (hqQ : q ≤ Q) (ha : a < q)
    (hc : a.Coprime q) (hq' : 1 ≤ q') (hqQ' : q' ≤ Q) (ha' : a' < q') (hc' : a'.Coprime q')
    (hne : ¬ (q = q' ∧ a = a')) :
    1 / (Q : ℝ) ^ 2 ≤ dist1 ((a : ℝ) / q - (a' : ℝ) / q') := by
  set k := round ((a : ℝ) / q - (a' : ℝ) / q')
  set z : ℤ := a * q' - a' * q - k * q * q' with hz
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hqR' : (0 : ℝ) < q' := by exact_mod_cast hq'
  have hval : (a : ℝ) / q - (a' : ℝ) / q' - k = (z : ℝ) / (q * q') := by
    rw [hz]; push_cast; field_simp
  have hz0 : z ≠ 0 := by
    intro h0
    have hqdvd : (q : ℤ) ∣ (a : ℤ) * q' := ⟨a' + k * q', by rw [hz] at h0; linarith⟩
    have hqdvd' : (q' : ℤ) ∣ (a' : ℤ) * q := ⟨a - k * q, by rw [hz] at h0; linarith⟩
    have c1 : IsCoprime (q : ℤ) (a : ℤ) := (Nat.isCoprime_iff_coprime.mpr hc.symm)
    have c2 : IsCoprime (q' : ℤ) (a' : ℤ) := (Nat.isCoprime_iff_coprime.mpr hc'.symm)
    have d1 : (q : ℤ) ∣ q' := c1.dvd_of_dvd_mul_left hqdvd
    have d2 : (q' : ℤ) ∣ q := c2.dvd_of_dvd_mul_left hqdvd'
    have hqq : q = q' := Nat.dvd_antisymm (Int.natCast_dvd_natCast.mp d1)
      (Int.natCast_dvd_natCast.mp d2)
    subst hqq
    have h2 : ((a : ℤ) - a' - k * q) * q = 0 := by rw [hz] at h0; linarith
    have h3 : (a : ℤ) - a' = k * q := by
      have := (mul_eq_zero.mp h2).resolve_right (by exact_mod_cast (by omega : q ≠ 0))
      linarith
    have hk : k = 0 := by
      have hlt1 : (a : ℤ) - a' < q := by omega
      have hlt2 : -(q : ℤ) < (a : ℤ) - a' := by omega
      rw [h3] at hlt1 hlt2
      have hqz : (0 : ℤ) < q := by exact_mod_cast hq
      by_contra hk0
      rcases lt_or_gt_of_ne hk0 with hkn | hkp
      · nlinarith
      · nlinarith
    rw [hk, zero_mul] at h3
    exact hne ⟨rfl, by omega⟩
  have hz1 : (1 : ℝ) ≤ |(z : ℝ)| := by
    have := Int.one_le_abs hz0
    exact_mod_cast this
  unfold dist1
  rw [hval, abs_div, abs_of_pos (by positivity : (0 : ℝ) < q * q')]
  have hQ : (q : ℝ) * q' ≤ (Q : ℝ) ^ 2 := by
    have : (q : ℝ) ≤ Q := by exact_mod_cast hqQ
    have : (q' : ℝ) ≤ Q := by exact_mod_cast hqQ'
    nlinarith
  rw [div_le_div_iff₀ (by nlinarith) (by positivity)]
  nlinarith

/-- **Analytic large sieve, Farey form**:
`∑_{q ≤ Q} ∑_{a mod q, (a,q)=1} |∑_{n∈F} c_n e(an/q)|² ≤ (N + 2Q²) ∑ |c_n|²`
for `F` contained in `N` consecutive integers. -/
theorem large_sieve_farey (Q M N : ℕ) (F : Finset ℕ) (hF : F ⊆ Ico M (M + N)) (c : ℕ → ℂ) :
    ∑ q ∈ Icc 1 Q, ∑ a ∈ (range q).filter (fun a => a.Coprime q),
      ‖∑ n ∈ F, c n * e (n * ((a : ℝ) / q))‖ ^ 2 ≤ (N + 2 * (Q : ℝ) ^ 2) * ∑ n ∈ F, ‖c n‖ ^ 2 := by
  rcases Nat.eq_zero_or_pos Q with hQ | hQ
  · subst hQ; simp only [Finset.Icc_eq_empty_of_lt (by norm_num : 0 < 1), Finset.sum_empty]
    positivity
  set R := (Icc 1 Q).sigma (fun q => (range q).filter (fun a => a.Coprime q))
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have := large_sieve_points R (fun p => (p.2 : ℝ) / p.1) (1 / (Q : ℝ) ^ 2) (by positivity)
    (by
      rintro ⟨q, a⟩ hr ⟨q', a'⟩ hs hne
      simp only [R, Finset.mem_sigma, Finset.mem_Icc, Finset.mem_filter, Finset.mem_range] at hr hs
      apply farey_sep Q q a q' a' hr.1.1 hr.1.2 hr.2.1 hr.2.2 hs.1.1 hs.1.2 hs.2.1 hs.2.2
      rintro ⟨rfl, rfl⟩; exact hne rfl) M N F hF c
  rw [Finset.sum_sigma] at this
  have h2 : 2 / (1 / (Q : ℝ) ^ 2) = 2 * (Q : ℝ) ^ 2 := by field_simp
  rw [h2] at this
  exact this

/-! ### Montgomery's lemma and the arithmetic large sieve -/

/-- Reduced residues `0 ≤ a < q`, `(a,q) = 1`. -/
def U (q : ℕ) : Finset ℕ := (range q).filter (fun a => a.Coprime q)

lemma card_U (q : ℕ) : (U q).card = Nat.totient q := by
  rw [Nat.totient_eq_card_coprime, U]
  congr 1
  apply Finset.filter_congr
  intro a _
  exact Nat.coprime_comm

/-- Orthogonality: `∑_{a<p} e(a(b-b')/p) = p·[b = b']` for `b, b' < p`. -/
lemma sum_e_orth (p b b' : ℕ) (hb : b < p) (hb' : b' < p) :
    ∑ a ∈ range p, e (a * (((b : ℝ) - b') / p)) = if b = b' then (p : ℂ) else 0 := by
  have hp : 0 < p := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  split_ifs with h
  · subst h; simp [e_zero]
  · set θ : ℝ := ((b : ℝ) - b') / p
    have hpow : e θ ^ p = 1 := by
      rw [← e_nat_mul]
      have : (p : ℝ) * θ = (((b : ℤ) - b' : ℤ) : ℝ) := by
        simp only [θ]; push_cast; field_simp
      rw [this, e_int]
    have hd : 0 < dist1 θ := by
      unfold dist1
      apply abs_pos.mpr
      intro h0
      have : ((b : ℤ) - b' - round θ * p : ℤ) = 0 := by
        have h1 : θ * p = (round θ : ℝ) * p := congrArg (· * (p : ℝ)) (sub_eq_zero.mp h0)
        simp only [θ] at h1
        field_simp at h1
        exact_mod_cast (by linarith : ((b : ℝ) - b' - (round θ : ℝ) * p) = 0)
      have hk : round θ = 0 := by
        by_contra hk0
        rcases lt_or_gt_of_ne hk0 with hkn | hkp
        · have : (round θ) * (p : ℤ) ≤ -p := by nlinarith
          omega
        · have : (p : ℤ) ≤ (round θ) * (p : ℤ) := by nlinarith
          omega
      rw [hk] at this
      omega
    have h4 := four_dist1_le_norm_e_sub_one θ
    have hne : e θ ≠ 1 := by
      intro h1; rw [h1, sub_self, norm_zero] at h4; linarith
    simp_rw [e_nat_mul]
    rw [geom_sum_eq hne, hpow, sub_self, zero_div]

lemma e_mod (n p a : ℕ) (hp : 0 < p) :
    e (n * ((a : ℝ) / p)) = e ((n % p : ℕ) * ((a : ℝ) / p)) := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have : (n : ℝ) * ((a : ℝ) / p) = (n % p : ℕ) * ((a : ℝ) / p) + (((n / p * a : ℕ) : ℤ) : ℝ) := by
    have h := Nat.mod_add_div n p
    have h' : (n : ℝ) = (n % p : ℕ) + p * (n / p : ℕ) := by exact_mod_cast h.symm
    have h2 : ((((n / p * a : ℕ) : ℤ) : ℝ)) = ((n / p : ℕ) : ℝ) * a := by
      rw [Int.cast_natCast, Nat.cast_mul]
    rw [h2, h']; field_simp
  rw [this, e_add_int]

/-- Discrete Parseval for `ℤ/p`. -/
lemma parseval_mod (p : ℕ) (Z : ℕ → ℂ) :
    ∑ a ∈ range p, ‖∑ b ∈ range p, Z b * e (b * ((a : ℝ) / p))‖ ^ 2
      = p * ∑ b ∈ range p, ‖Z b‖ ^ 2 := by
  apply Complex.ofReal_injective
  push_cast
  simp_rw [← Complex.mul_conj', map_sum, map_mul, conj_e, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  have : ∀ b ∈ range p, ∀ b' ∈ range p, ∑ a ∈ range p, Z b * e (b * ((a : ℝ) / p)) *
      ((starRingEnd ℂ) (Z b') * e (-(b' * ((a : ℝ) / p))))
      = Z b * (starRingEnd ℂ) (Z b') * (if b = b' then (p : ℂ) else 0) := by
    intro b hb b' hb'
    rw [← sum_e_orth p b b' (Finset.mem_range.mp hb) (Finset.mem_range.mp hb'), Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [show (a : ℝ) * (((b : ℝ) - b') / p) = b * ((a : ℝ) / p) + -(b' * ((a : ℝ) / p)) by ring,
      e_add]
    ring
  refine Finset.sum_congr rfl (fun b hb => ?_)
  rw [Finset.sum_comm, Finset.sum_congr rfl (this b hb)]
  simp [hb]
  ring

/-- **Montgomery's lemma, prime modulus**: if the support of `c` avoids the classes `Ω` mod `p`,
then `ω/(p-ω) |∑ c_n e(nβ)|² ≤ ∑_{(a,p)=1} |∑ c_n e(n(β + a/p))|²`. -/
lemma montgomery_prime (p : ℕ) (hp : p.Prime) (Ω : Finset ℕ) (hΩ : Ω ⊆ range p)
    (F : Finset ℕ) (c : ℕ → ℂ) (hF : ∀ n ∈ F, n % p ∉ Ω) (β : ℝ) :
    (Ω.card : ℝ) / (p - Ω.card) * ‖∑ n ∈ F, c n * e (n * β)‖ ^ 2 ≤
      ∑ a ∈ U p, ‖∑ n ∈ F, c n * e (n * (β + (a : ℝ) / p))‖ ^ 2 := by
  have hp0 : 0 < p := hp.pos
  set d : ℕ → ℂ := fun n => c n * e (n * β) with hd
  set Z : ℕ → ℂ := fun b => ∑ n ∈ F.filter (fun n => n % p = b), d n with hZ
  have hS : ∀ a : ℕ, ∑ n ∈ F, c n * e (n * (β + (a : ℝ) / p)) =
      ∑ b ∈ range p, Z b * e (b * ((a : ℝ) / p)) := by
    intro a
    have : ∀ n : ℕ, c n * e (n * (β + (a : ℝ) / p)) = d n * e ((n % p : ℕ) * ((a : ℝ) / p)) := by
      intro n; rw [hd, ← e_mod n p a hp0, mul_add, e_add]; ring
    simp_rw [this]
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun n => n % p) (t := range p)
      (fun n _ => Finset.mem_range.mpr (Nat.mod_lt n hp0))]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [hZ, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    rw [(Finset.mem_filter.mp hn).2]
  have hS0 : ∑ n ∈ F, c n * e (n * β) = ∑ b ∈ range p, Z b := by
    have := hS 0
    simp only [Nat.cast_zero, zero_div, add_zero, mul_zero, e_zero, mul_one] at this
    exact this
  have hZΩ : ∀ b ∈ Ω, Z b = 0 := by
    intro b hb
    rw [hZ]; apply Finset.sum_eq_zero
    intro n hn
    obtain ⟨hnF, hnb⟩ := Finset.mem_filter.mp hn
    exact absurd (hnb ▸ hb) (hF n hnF)
  set W := ∑ b ∈ range p, ‖Z b‖ ^ 2 with hW
  set s0 := ‖∑ n ∈ F, c n * e (n * β)‖ ^ 2 with hs0
  have hωp : Ω.card ≤ p := by simpa using Finset.card_le_card hΩ
  have hcs : s0 ≤ (p - Ω.card) * W := by
    have hsplit : ∑ b ∈ range p, Z b = ∑ b ∈ range p \ Ω, Z b := by
      rw [← Finset.sum_sdiff hΩ, Finset.sum_eq_zero hZΩ, add_zero]
    have hcard : ((range p \ Ω).card : ℝ) = p - Ω.card := by
      rw [Finset.card_sdiff_of_subset hΩ, Finset.card_range, Nat.cast_sub hωp]
    calc s0 = ‖∑ b ∈ range p \ Ω, Z b‖ ^ 2 := by rw [hs0, hS0, hsplit]
      _ ≤ (∑ b ∈ range p \ Ω, ‖Z b‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ (range p \ Ω).card * ∑ b ∈ range p \ Ω, ‖Z b‖ ^ 2 := sq_sum_le_card_mul_sum_sq
      _ ≤ (p - Ω.card) * W := by
          rw [hcard]; apply mul_le_mul_of_nonneg_left
          · exact Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
              (fun _ _ _ => by positivity)
          · rw [← hcard]; positivity
  have hpars : ∑ a ∈ range p, ‖∑ n ∈ F, c n * e (n * (β + (a : ℝ) / p))‖ ^ 2 = p * W := by
    simp_rw [hS]; exact parseval_mod p Z
  have hsplit : ∑ a ∈ range p, ‖∑ n ∈ F, c n * e (n * (β + (a : ℝ) / p))‖ ^ 2 =
      s0 + ∑ a ∈ U p, ‖∑ n ∈ F, c n * e (n * (β + (a : ℝ) / p))‖ ^ 2 := by
    rw [U, ← Finset.sum_filter_add_sum_filter_not (range p) (fun a => a.Coprime p), add_comm]
    congr 1
    have : (range p).filter (fun a => ¬ a.Coprime p) = {0} := by
      ext a; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      constructor
      · rintro ⟨ha, hc⟩
        rw [Nat.coprime_comm, hp.coprime_iff_not_dvd, not_not] at hc
        exact Nat.eq_zero_of_dvd_of_lt hc ha
      · rintro rfl; exact ⟨hp0, by rw [Nat.coprime_zero_left]; exact hp.one_lt.ne'⟩
    rw [this, Finset.sum_singleton]; simp [hs0]
  have hω : (Ω.card : ℝ) ≤ p := by exact_mod_cast hωp
  have hW0 : 0 ≤ W := by positivity
  set T := ∑ a ∈ U p, ‖∑ n ∈ F, c n * e (n * (β + (a : ℝ) / p))‖ ^ 2
  have hT : T = p * W - s0 := by linarith
  rcases (sub_nonneg.mpr hω).lt_or_eq with hpos | hzero
  · rw [div_mul_eq_mul_div, div_le_iff₀ hpos, hT]
    have hp0' : (0 : ℝ) ≤ p := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hcs hp0']
  · rw [← hzero, div_zero, zero_mul, hT]
    rw [← hzero, zero_mul] at hcs
    nlinarith

/-- Chinese remainder theorem for reduced fractions mod 1. -/
lemma sum_U_mul (q1 q2 : ℕ) (h1 : 0 < q1) (h2 : 0 < q2) (hc : q1.Coprime q2) (f : ℝ → ℝ)
    (hf : ∀ x (k : ℕ), f (x + k) = f x) :
    ∑ c ∈ U (q1 * q2), f ((c : ℝ) / ((q1 * q2 : ℕ) : ℝ)) =
      ∑ a1 ∈ U q1, ∑ a2 ∈ U q2, f ((a1 : ℝ) / q1 + (a2 : ℝ) / q2) := by
  have hm0 : 0 < q1 * q2 := Nat.mul_pos h1 h2
  set g : ℕ × ℕ → ℕ := fun p => (p.1 * q2 + p.2 * q1) % (q1 * q2) with hg
  have hq1 : (q1 : ℝ) ≠ 0 := by exact_mod_cast h1.ne'
  have hq2 : (q2 : ℝ) ≠ 0 := by exact_mod_cast h2.ne'
  have hval : ∀ a1 a2 : ℕ, f ((a1 : ℝ) / q1 + (a2 : ℝ) / q2) =
      f ((g (a1, a2) : ℝ) / ((q1 * q2 : ℕ) : ℝ)) := by
    intro a1 a2
    have hmod := Nat.mod_add_div (a1 * q2 + a2 * q1) (q1 * q2)
    have hcast : ((a1 * q2 + a2 * q1 : ℕ) : ℝ) = (g (a1, a2) : ℝ) +
        ((q1 * q2 : ℕ) : ℝ) * (((a1 * q2 + a2 * q1) / (q1 * q2) : ℕ) : ℝ) := by
      rw [hg]; exact_mod_cast hmod.symm
    have h3 : (a1 : ℝ) / q1 + (a2 : ℝ) / q2 =
        ((a1 * q2 + a2 * q1 : ℕ) : ℝ) / ((q1 * q2 : ℕ) : ℝ) := by
      push_cast; field_simp
    have h4 : (a1 : ℝ) / q1 + (a2 : ℝ) / q2 = (g (a1, a2) : ℝ) / ((q1 * q2 : ℕ) : ℝ) +
        (((a1 * q2 + a2 * q1) / (q1 * q2) : ℕ) : ℝ) := by
      rw [h3, hcast, add_div, mul_div_cancel_left₀]
      exact_mod_cast hm0.ne'
    rw [h4, hf]
  have hinj : Set.InjOn g ↑(U q1 ×ˢ U q2) := by
    rintro ⟨a1, a2⟩ hp ⟨b1, b2⟩ hq heq
    simp only [Finset.mem_coe, Finset.mem_product, U, Finset.mem_filter,
      Finset.mem_range] at hp hq
    have hmod : (a1 * q2 + a2 * q1) ≡ (b1 * q2 + b2 * q1) [MOD q1 * q2] := heq
    have e1 : a1 * q2 ≡ b1 * q2 [MOD q1] := by
      have := hmod.of_mul_right q2
      unfold Nat.ModEq at this ⊢
      rwa [Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right] at this
    have e2 : a2 * q1 ≡ b2 * q1 [MOD q2] := by
      have := hmod.of_mul_left q1
      unfold Nat.ModEq at this ⊢
      rwa [add_comm (a1 * q2), add_comm (b1 * q2), Nat.add_mul_mod_self_right,
        Nat.add_mul_mod_self_right] at this
    have f1 := Nat.ModEq.cancel_right_of_coprime (by exact hc) e1
    have f2 := Nat.ModEq.cancel_right_of_coprime (by exact hc.symm) e2
    unfold Nat.ModEq at f1 f2
    rw [Nat.mod_eq_of_lt hp.1.1, Nat.mod_eq_of_lt hq.1.1] at f1
    rw [Nat.mod_eq_of_lt hp.2.1, Nat.mod_eq_of_lt hq.2.1] at f2
    rw [f1, f2]
  have hmaps : ∀ p ∈ U q1 ×ˢ U q2, g p ∈ U (q1 * q2) := by
    rintro ⟨a1, a2⟩ hp
    simp only [Finset.mem_product, U, Finset.mem_filter, Finset.mem_range] at hp
    simp only [U, Finset.mem_filter, Finset.mem_range, hg]
    refine ⟨Nat.mod_lt _ hm0, ?_⟩
    have hA : Nat.Coprime (a1 * q2 + a2 * q1) q1 :=
      (Nat.coprime_add_mul_right_left (a1 * q2) q1 a2).mpr (Nat.Coprime.mul_left hp.1.2 hc.symm)
    have hB : Nat.Coprime (a1 * q2 + a2 * q1) q2 := by
      rw [add_comm]
      exact (Nat.coprime_add_mul_right_left (a2 * q1) q2 a1).mpr (Nat.Coprime.mul_left hp.2.2 hc)
    have hcop := Nat.Coprime.mul_right hA hB
    unfold Nat.Coprime at hcop ⊢
    rw [← Nat.gcd_rec, Nat.gcd_comm]; exact hcop
  have himage : (U q1 ×ˢ U q2).image g = U (q1 * q2) := by
    apply Finset.eq_of_subset_of_card_le
    · intro c hc; obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hc; exact hmaps p hp
    · rw [Finset.card_image_of_injOn hinj, Finset.card_product, card_U, card_U, card_U,
        Nat.totient_mul hc]
  rw [← himage, Finset.sum_image hinj, Finset.sum_product]
  exact Finset.sum_congr rfl (fun a1 _ => Finset.sum_congr rfl (fun a2 _ => (hval a1 a2).symm))

/-- The local sieve factor `h(p) = ω(p)/(p - ω(p))`. -/
noncomputable def hfac (Ω : ℕ → Finset ℕ) (p : ℕ) : ℝ := ((Ω p).card : ℝ) / (p - (Ω p).card)

lemma hfac_nonneg (Ω : ℕ → Finset ℕ) (p : ℕ) (h : Ω p ⊆ range p) : 0 ≤ hfac Ω p := by
  unfold hfac
  have : (Ω p).card ≤ p := by simpa using Finset.card_le_card h
  have : ((Ω p).card : ℝ) ≤ p := by exact_mod_cast this
  apply div_nonneg (by positivity); linarith

/-- **Montgomery's lemma** for squarefree moduli:
`∏_{p | q} h(p) · |∑ c_n e(nβ)|² ≤ ∑_{(a,q)=1} |∑ c_n e(n(β + a/q))|²`. -/
theorem montgomery (Ω : ℕ → Finset ℕ) (F : Finset ℕ) (c : ℕ → ℂ) :
    ∀ q : ℕ, 0 < q → Squarefree q → (∀ p ∈ q.primeFactors, Ω p ⊆ range p) →
    (∀ n ∈ F, ∀ p ∈ q.primeFactors, n % p ∉ Ω p) → ∀ β : ℝ,
    (∏ p ∈ q.primeFactors, hfac Ω p) * ‖∑ n ∈ F, c n * e (n * β)‖ ^ 2 ≤
      ∑ a ∈ U q, ‖∑ n ∈ F, c n * e (n * (β + (a : ℝ) / q))‖ ^ 2 := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
  intro hq0 hsq hΩ hF β
  rcases Nat.lt_or_ge q 2 with hq1 | hq2
  · have : q = 1 := by omega
    subst this
    have hU : U 1 = {0} := by decide
    simp [hU]
  · set p := q.minFac with hpdef
    have hp : p.Prime := Nat.minFac_prime (by omega)
    set q' := q / p with hq'def
    have hpq : p * q' = q := Nat.mul_div_cancel' (Nat.minFac_dvd q)
    have hq'0 : 0 < q' := by
      rcases Nat.eq_zero_or_pos q' with h | h
      · rw [h, mul_zero] at hpq; omega
      · exact h
    have hcop : p.Coprime q' := by
      rw [hp.coprime_iff_not_dvd]
      rintro ⟨t, ht⟩
      have : p * p ∣ q := ⟨t, by rw [← hpq, ht]; ring⟩
      exact hp.one_lt.ne' (Nat.isUnit_iff.mp (hsq p this))
    have hq'lt : q' < q := Nat.div_lt_self hq0 hp.one_lt
    have hsq' : Squarefree q' := hsq.squarefree_of_dvd ⟨p, by rw [← hpq]; ring⟩
    have hpf : q.primeFactors = {p} ∪ q'.primeFactors := by
      rw [← hpq, Nat.Coprime.primeFactors_mul hcop, hp.primeFactors]
    have hdisj : Disjoint {p} q'.primeFactors := by
      rw [← hp.primeFactors]; exact hcop.disjoint_primeFactors
    have hsub : q'.primeFactors ⊆ q.primeFactors := by rw [hpf]; exact Finset.subset_union_right
    have hpmem : p ∈ q.primeFactors := by rw [hpf]; simp
    rw [hpf, Finset.prod_union hdisj, Finset.prod_singleton]
    set f : ℝ → ℝ := fun x => ‖∑ n ∈ F, c n * e (n * (β + x))‖ ^ 2 with hfdef
    have hfper : ∀ x (k : ℕ), f (x + k) = f x := by
      intro x k; simp only [hfdef]; congr 2; refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [show (n : ℝ) * (β + (x + k)) = n * (β + x) + ((n * k : ℕ) : ℤ) by push_cast; ring,
        e_add_int]
    have hcrt := sum_U_mul p q' hp.pos hq'0 hcop f hfper
    rw [hpq] at hcrt
    show _ ≤ ∑ a ∈ U q, f ((a : ℝ) / q)
    rw [hcrt, Finset.sum_comm]
    have hih := ih q' hq'lt hq'0 hsq' (fun p hp => hΩ p (hsub hp))
      (fun n hn p hp => hF n hn p (hsub hp)) β
    have hh0 := hfac_nonneg Ω p (hΩ p hpmem)
    calc hfac Ω p * (∏ x ∈ q'.primeFactors, hfac Ω x) * ‖∑ n ∈ F, c n * e (n * β)‖ ^ 2
        ≤ hfac Ω p * ∑ a ∈ U q', ‖∑ n ∈ F, c n * e (n * (β + (a : ℝ) / q'))‖ ^ 2 := by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hih hh0
      _ = ∑ a2 ∈ U q', hfac Ω p * ‖∑ n ∈ F, c n * e (n * (β + (a2 : ℝ) / q'))‖ ^ 2 :=
          Finset.mul_sum _ _ _
      _ ≤ ∑ a2 ∈ U q', ∑ a1 ∈ U p, f ((a1 : ℝ) / p + (a2 : ℝ) / q') := by
          apply Finset.sum_le_sum
          intro a2 _
          have := montgomery_prime p hp (Ω p) (hΩ p hpmem) F c (fun n hn => hF n hn p hpmem)
            (β + (a2 : ℝ) / q')
          refine this.trans (le_of_eq (Finset.sum_congr rfl (fun a1 _ => ?_)))
          simp only [hfdef]
          rw [show β + (a2 : ℝ) / q' + (a1 : ℝ) / p = β + ((a1 : ℝ) / p + (a2 : ℝ) / q') by ring]

/-- **Arithmetic large sieve (Montgomery)**: if `A ⊆ [M, M+N)` avoids the residue classes
`Ω p` mod every prime `p ≤ Q`, then `|A| · L ≤ N + 2Q²` with
`L = ∑_{q ≤ Q squarefree} ∏_{p | q} ω(p)/(p - ω(p))`. -/
theorem arith_large_sieve (Q M N : ℕ) (A : Finset ℕ) (hA : A ⊆ Ico M (M + N))
    (Ω : ℕ → Finset ℕ) (hΩ : ∀ p, p.Prime → p ≤ Q → Ω p ⊆ range p)
    (hAΩ : ∀ n ∈ A, ∀ p, p.Prime → p ≤ Q → n % p ∉ Ω p) :
    (A.card : ℝ) * ∑ q ∈ (Icc 1 Q).filter Squarefree, ∏ p ∈ q.primeFactors, hfac Ω p
      ≤ N + 2 * (Q : ℝ) ^ 2 := by
  have hfarey := large_sieve_farey Q M N A hA (fun _ => 1)
  simp only [one_mul, norm_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hfarey
  have hmont : ∀ q ∈ (Icc 1 Q).filter Squarefree, (∏ p ∈ q.primeFactors, hfac Ω p) *
      (A.card : ℝ) ^ 2 ≤ ∑ a ∈ U q, ‖∑ n ∈ A, e (n * ((a : ℝ) / q))‖ ^ 2 := by
    intro q hq
    obtain ⟨hq1, hsq⟩ := Finset.mem_filter.mp hq
    have hqQ := Finset.mem_Icc.mp hq1
    have hpf : ∀ p ∈ q.primeFactors, p.Prime ∧ p ≤ Q := fun p hp =>
      ⟨Nat.prime_of_mem_primeFactors hp, (Nat.le_of_mem_primeFactors hp).trans hqQ.2⟩
    have := montgomery Ω A (fun _ => 1) q hqQ.1 hsq
      (fun p hp => hΩ p (hpf p hp).1 (hpf p hp).2)
      (fun n hn p hp => hAΩ n hn p (hpf p hp).1 (hpf p hp).2) 0
    simp only [one_mul, mul_zero, e_zero, zero_add, Finset.sum_const, nsmul_eq_mul, mul_one,
      Complex.norm_natCast] at this
    exact this
  set L := ∑ q ∈ (Icc 1 Q).filter Squarefree, ∏ p ∈ q.primeFactors, hfac Ω p
  have hL : L * (A.card : ℝ) ^ 2 ≤ (N + 2 * (Q : ℝ) ^ 2) * A.card := by
    calc L * (A.card : ℝ) ^ 2 = ∑ q ∈ (Icc 1 Q).filter Squarefree,
          (∏ p ∈ q.primeFactors, hfac Ω p) * (A.card : ℝ) ^ 2 := Finset.sum_mul _ _ _
      _ ≤ ∑ q ∈ (Icc 1 Q).filter Squarefree, ∑ a ∈ U q, ‖∑ n ∈ A, e (n * ((a : ℝ) / q))‖ ^ 2 :=
          Finset.sum_le_sum hmont
      _ ≤ ∑ q ∈ Icc 1 Q, ∑ a ∈ U q, ‖∑ n ∈ A, e (n * ((a : ℝ) / q))‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => by positivity)
      _ ≤ (N + 2 * (Q : ℝ) ^ 2) * A.card := hfarey
  rcases Nat.eq_zero_or_pos A.card with h0 | hpos
  · rw [h0]; simp; positivity
  · have hApos : (0 : ℝ) < A.card := by exact_mod_cast hpos
    have : (A.card * L) * A.card ≤ (N + 2 * (Q : ℝ) ^ 2) * A.card := by nlinarith
    exact le_of_mul_le_mul_right this hApos

/-! ### Linnik's application: primes with many small quadratic residues -/

open Classical in
/-- At most `p/2` of the nonzero residues `b < p` are squares mod `p`. -/
lemma card_nonzero_sq_le (p : ℕ) (hp : p.Prime) :
    ((range p).filter (fun b : ℕ => b ≠ 0 ∧ IsSquare (b : ZMod p))).card ≤ p / 2 := by
  have := Fact.mk hp
  have hp2 : 0 < p / 2 ∨ p / 2 = 0 := by omega
  calc _
      ≤ (Polynomial.nthRootsFinset (p / 2) (1 : ZMod p)).card := by
        apply Finset.card_le_card_of_injOn (fun b : ℕ => (b : ZMod p))
        · intro b hb
          obtain ⟨hbp, hb0, hbs⟩ := by simpa using hb
          have hne : (b : ZMod p) ≠ 0 := by
            rw [Ne, ZMod.natCast_eq_zero_iff]
            intro hd; exact hb0 (Nat.eq_zero_of_dvd_of_lt hd hbp)
          have h1 := (ZMod.euler_criterion p hne).mp hbs
          rcases hp2 with hpos | hz
          · simp only [Finset.mem_coe]
            exact (Polynomial.mem_nthRootsFinset hpos _).mpr h1
          · exfalso; have := hp.two_le; omega
        · intro b hb b' hb' h
          simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hb hb'
          have := (ZMod.natCast_eq_natCast_iff' b b' p).mp h
          rwa [Nat.mod_eq_of_lt hb.1, Nat.mod_eq_of_lt hb'.1] at this
    _ ≤ p / 2 := by
        classical
        rw [Polynomial.nthRootsFinset_def]
        exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots _ _)

open Classical in
/-- The nonresidue classes mod `p`. -/
noncomputable def nonres (p : ℕ) : Finset ℕ :=
  (range p).filter (fun b : ℕ => ¬ IsSquare (b : ZMod p))

open Classical in
lemma nonres_subset (p : ℕ) : nonres p ⊆ range p := by
  unfold nonres; intro x hx; exact (Finset.mem_filter.mp hx).1

open Classical in
lemma three_mul_card_nonres (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) :
    p ≤ 3 * (nonres p).card ∧ (nonres p).card < p := by
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := range p) (fun b : ℕ => ¬ IsSquare (b : ZMod p))
  rw [Finset.card_range] at hsplit
  have hnr : (nonres p).card = ((range p).filter (fun b : ℕ => ¬ IsSquare (b : ZMod p))).card := by
    unfold nonres; congr 1
  have hsq : ((range p).filter (fun b : ℕ => ¬ ¬ IsSquare (b : ZMod p))).card ≤ 1 + p / 2 := by
    have hsub : (range p).filter (fun b : ℕ => ¬ ¬ IsSquare (b : ZMod p)) ⊆
        {0} ∪ (range p).filter (fun b : ℕ => b ≠ 0 ∧ IsSquare (b : ZMod p)) := by
      intro b hb
      simp only [Finset.mem_filter, Finset.mem_range, not_not] at hb
      by_cases h0 : b = 0
      · simp [h0]
      · simp [hb.1, hb.2, h0]
    calc _ ≤ ({0} ∪ (range p).filter (fun b : ℕ => b ≠ 0 ∧ IsSquare (b : ZMod p))).card :=
          Finset.card_le_card hsub
      _ ≤ ({0} : Finset ℕ).card + ((range p).filter
            (fun b : ℕ => b ≠ 0 ∧ IsSquare (b : ZMod p))).card := Finset.card_union_le _ _
      _ ≤ 1 + p / 2 := by rw [Finset.card_singleton]; have := card_nonzero_sq_le p hp; omega
  have hzero : ((range p).filter (fun b : ℕ => ¬ ¬ IsSquare (b : ZMod p))).card ≥ 1 := by
    apply Finset.card_pos.mpr
    refine ⟨0, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_range, not_not, Nat.cast_zero]
    exact ⟨by omega, ⟨0, by simp⟩⟩
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two (by omega))
  rw [hnr]
  constructor <;> omega

lemma hfac_nonres_ge (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) :
    (1 / 2 : ℝ) ≤ hfac (fun _ => nonres p) p := by
  obtain ⟨h1, h2⟩ := three_mul_card_nonres p hp hp3
  unfold hfac
  have h1' : (p : ℝ) ≤ 3 * (nonres p).card := by exact_mod_cast h1
  have h2' : ((nonres p).card : ℝ) < p := by exact_mod_cast h2
  rw [le_div_iff₀ (by linarith)]
  linarith

/-- If every prime `ℓ ≤ y` is a square mod `p`, so is every `y`-smooth `n`. -/
lemma smooth_isSquare (p y : ℕ) (hsq : ∀ ℓ, ℓ.Prime → ℓ ≤ y → IsSquare (ℓ : ZMod p)) :
    ∀ n : ℕ, (∀ ℓ, ℓ.Prime → ℓ ∣ n → ℓ ≤ y) → IsSquare (n : ZMod p) := by
  intro n
  induction n using Nat.recOnMul with
  | zero => intro _; exact ⟨0, by simp⟩
  | one => intro _; exact ⟨1, by simp⟩
  | prime ℓ hℓ => intro h; exact hsq ℓ hℓ (h ℓ hℓ dvd_rfl)
  | mul a b iha ihb =>
    intro h
    rw [Nat.cast_mul]
    exact (iha (fun ℓ hℓ hd => h ℓ hℓ (dvd_mul_of_dvd_left hd b))).mul
      (ihb (fun ℓ hℓ hd => h ℓ hℓ (dvd_mul_of_dvd_right hd a)))

open Classical in
/-- **Linnik-type bound from the large sieve.** Let `E` be the set of primes `3 ≤ p ≤ Q` modulo
which every prime `ℓ ≤ y` is a quadratic residue, and `Ψ(N,y)` the number of `y`-smooth
`n ∈ [1,N]`. Then `|E| · Ψ(N,y) ≤ 2(N + 2Q²)`. -/
theorem linnik_large_sieve (N Q y : ℕ) :
    (((Icc 1 Q).filter (fun p => p.Prime ∧ 3 ≤ p ∧
        ∀ ℓ, ℓ.Prime → ℓ ≤ y → IsSquare (ℓ : ZMod p))).card : ℝ) *
      ((Icc 1 N).filter (fun n => ∀ ℓ, ℓ.Prime → ℓ ∣ n → ℓ ≤ y)).card
      ≤ 2 * (N + 2 * (Q : ℝ) ^ 2) := by
  set E := (Icc 1 Q).filter (fun p => p.Prime ∧ 3 ≤ p ∧
        ∀ ℓ, ℓ.Prime → ℓ ≤ y → IsSquare (ℓ : ZMod p)) with hE
  set A := (Icc 1 N).filter (fun n => ∀ ℓ, ℓ.Prime → ℓ ∣ n → ℓ ≤ y) with hAdef
  set Ω : ℕ → Finset ℕ := fun p => if p ∈ E then nonres p else ∅ with hΩ
  have hΩsub : ∀ p, Ω p ⊆ range p := by
    intro p; simp only [hΩ]; split_ifs
    · exact nonres_subset p
    · exact Finset.empty_subset _
  have hA : A ⊆ Ico 1 (1 + N) := by
    intro n hn
    have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1)
    rw [Finset.mem_Ico]; omega
  have hAΩ : ∀ n ∈ A, ∀ p, p.Prime → p ≤ Q → n % p ∉ Ω p := by
    intro n hn p hp _
    simp only [hΩ]
    split_ifs with hpE
    · have hpE' := (Finset.mem_filter.mp hpE).2
      have hsq := smooth_isSquare p y hpE'.2.2 n (Finset.mem_filter.mp hn).2
      unfold nonres
      simp only [Finset.mem_filter, Finset.mem_range, not_and, not_not]
      intro _
      rw [ZMod.natCast_mod]; exact hsq
    · exact Finset.notMem_empty _
  have hsieve := arith_large_sieve Q 1 N A hA Ω (fun p _ _ => hΩsub p) hAΩ
  set L := ∑ q ∈ (Icc 1 Q).filter Squarefree, ∏ p ∈ q.primeFactors, hfac Ω p
  have hEL : (E.card : ℝ) / 2 ≤ L := by
    have hsubE : E ⊆ (Icc 1 Q).filter Squarefree := by
      intro p hp
      obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨h1, h2.1.squarefree⟩
    calc (E.card : ℝ) / 2 = ∑ p ∈ E, (1 / 2 : ℝ) := by simp; ring
      _ ≤ ∑ p ∈ E, ∏ r ∈ p.primeFactors, hfac Ω r := by
          apply Finset.sum_le_sum
          intro p hp
          obtain ⟨_, h2⟩ := Finset.mem_filter.mp hp
          rw [h2.1.primeFactors, Finset.prod_singleton]
          have : hfac Ω p = hfac (fun _ => nonres p) p := by
            simp only [hfac, hΩ, if_pos hp]
          rw [this]
          exact hfac_nonres_ge p h2.1 h2.2.1
      _ ≤ L := Finset.sum_le_sum_of_subset_of_nonneg hsubE (fun q _ _ =>
          Finset.prod_nonneg (fun r _ => hfac_nonneg Ω r (hΩsub r)))
  have hA0 : (0 : ℝ) ≤ A.card := by positivity
  calc (E.card : ℝ) * A.card = 2 * (A.card * (E.card / 2)) := by ring
    _ ≤ 2 * (A.card * L) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact mul_le_mul_of_nonneg_left hEL hA0
    _ ≤ 2 * (N + 2 * (Q : ℝ) ^ 2) := by linarith

open Classical in
/-- The same bound phrased with (every `1 ≤ m ≤ y` is a square mod `p`)
(i.e. the least quadratic nonresidue exceeds `y`), as in `Erdos980.leastNonresidue`. -/
theorem linnik_nonresidue (N Q y : ℕ) :
    (((Icc 1 Q).filter (fun p => p.Prime ∧ 3 ≤ p ∧
        ∀ m : ℕ, 0 < m → m ≤ y → ∃ x : ZMod p, x ^ 2 = (m : ZMod p))).card : ℝ) *
      ((Icc 1 N).filter (fun n => ∀ ℓ, ℓ.Prime → ℓ ∣ n → ℓ ≤ y)).card
      ≤ 2 * (N + 2 * (Q : ℝ) ^ 2) := by
  refine le_trans ?_ (linnik_large_sieve N Q y)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro p hp
  simp only [Finset.mem_filter] at hp ⊢
  refine ⟨hp.1, hp.2.1, hp.2.2.1, fun ℓ hℓ hℓy => ?_⟩
  obtain ⟨x, hx⟩ := hp.2.2.2 ℓ hℓ.pos hℓy
  exact ⟨x, by rw [← hx, sq]⟩

open Classical in
/-- Smooth numbers, crude lower bound: products of `k` distinct primes `≤ y`.
`Ψ(N, y) ≥ (π(y) + 1 - k)^k / k!` whenever `y^k ≤ N`. -/
theorem smooth_count_ge (N y k : ℕ) (hk : y ^ k ≤ N) :
    ((((Nat.primesBelow (y + 1)).card + 1 - k : ℕ) : ℝ) ^ k / (k.factorial : ℝ))
      ≤ ((Icc 1 N).filter (fun n => ∀ ℓ, ℓ.Prime → ℓ ∣ n → ℓ ≤ y)).card := by
  set P := Nat.primesBelow (y + 1) with hP
  have hPp : ∀ p ∈ P, p.Prime ∧ p ≤ y := by
    intro p hp
    obtain ⟨h1, h2⟩ := Nat.mem_primesBelow.mp hp
    exact ⟨h2, by omega⟩
  refine le_trans (Nat.pow_le_choose k P.card) ?_
  rw [← Finset.card_powersetCard]
  apply Nat.cast_le.mpr
  apply Finset.card_le_card_of_injOn (fun s => ∏ p ∈ s, p)
  · intro s hs
    simp only [Finset.mem_coe, Finset.mem_powersetCard] at hs
    obtain ⟨hsP, hcard⟩ := hs
    have hprime : ∀ p ∈ s, p.Prime := fun p hp => (hPp p (hsP hp)).1
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨Finset.prod_pos (fun p hp => (hprime p hp).pos), ?_⟩, ?_⟩
    · calc ∏ p ∈ s, p ≤ y ^ s.card :=
            Finset.prod_le_pow_card s id y (fun p hp => (hPp p (hsP hp)).2)
        _ = y ^ k := by rw [hcard]
        _ ≤ N := hk
    · intro ℓ hℓ hdvd
      have hne : ∏ p ∈ s, p ≠ 0 := (Finset.prod_pos (fun p hp => (hprime p hp).pos)).ne'
      have hmem : ℓ ∈ (∏ p ∈ s, p).primeFactors := Nat.mem_primeFactors.mpr ⟨hℓ, hdvd, hne⟩
      rw [Nat.primeFactors_prod hprime] at hmem
      exact (hPp ℓ (hsP hmem)).2
  · intro s hs t ht hst
    simp only [Finset.mem_coe, Finset.mem_powersetCard] at hs ht
    have h1 := Nat.primeFactors_prod (fun p hp => (hPp p (hs.1 hp)).1)
    have h2 := Nat.primeFactors_prod (fun p hp => (hPp p (ht.1 hp)).1)
    simp only at hst
    rw [← h1, ← h2, hst]

open Classical in
/-- **Linnik tail, explicit.** The number `E` of primes `3 ≤ p ≤ Q` whose least quadratic
nonresidue exceeds `y` satisfies `E · (π(y) + 1 - k)^k / k! ≤ 2(y^k + 2Q²)` for every `k`. -/
theorem linnik_explicit (Q y k : ℕ) :
    (((Icc 1 Q).filter (fun p => p.Prime ∧ 3 ≤ p ∧
        ∀ m : ℕ, 0 < m → m ≤ y → ∃ x : ZMod p, x ^ 2 = (m : ZMod p))).card : ℝ) *
      ((((Nat.primesBelow (y + 1)).card + 1 - k : ℕ) : ℝ) ^ k / (k.factorial : ℝ))
      ≤ 2 * ((y ^ k : ℕ) + 2 * (Q : ℝ) ^ 2) := by
  refine le_trans (mul_le_mul_of_nonneg_left (smooth_count_ge (y ^ k) y k le_rfl)
    (by positivity)) ?_
  exact linnik_nonresidue (y ^ k) Q y

/-! ### The least quadratic nonresidue (same definition as `Erdos980.leastNonresidue 2`) -/

/-- Least quadratic nonresidue; definitionally `Erdos980.leastNonresidue 2 p`. -/
noncomputable def lnr (p : ℕ) : ℕ :=
  sInf {n : ℕ | 0 < n ∧ ¬ ∃ x : ZMod p, x ^ 2 = (n : ZMod p)}

lemma exists_nonres (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) :
    ∃ n : ℕ, 0 < n ∧ ¬ ∃ x : ZMod p, x ^ 2 = (n : ZMod p) := by
  classical
  obtain ⟨h1, h2⟩ := three_mul_card_nonres p hp hp3
  have hpos : 0 < (nonres p).card := by omega
  obtain ⟨b, hb⟩ := Finset.card_pos.mp hpos
  unfold nonres at hb
  obtain ⟨hbp, hbs⟩ := Finset.mem_filter.mp hb
  refine ⟨b, ?_, fun ⟨x, hx⟩ => hbs ⟨x, by rw [← hx, sq]⟩⟩
  rcases Nat.eq_zero_or_pos b with h | h
  · exact absurd ⟨0, by simp [h]⟩ hbs
  · exact h

lemma lnr_spec (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) :
    0 < lnr p ∧ (¬ ∃ x : ZMod p, x ^ 2 = (lnr p : ZMod p)) ∧
      ∀ m : ℕ, 0 < m → m < lnr p → ∃ x : ZMod p, x ^ 2 = (m : ZMod p) := by
  have hne := exists_nonres p hp hp3
  have hmem := Nat.sInf_mem hne
  refine ⟨hmem.1, hmem.2, fun m hm hlt => ?_⟩
  by_contra hns
  exact absurd (Nat.sInf_le (⟨hm, hns⟩ : m ∈ {n : ℕ | 0 < n ∧ ¬ ∃ x : ZMod p, x ^ 2 = (n : ZMod p)}))
    (not_le.mpr hlt)

lemma sq_mul_sq {p : ℕ} {a b : ZMod p} (ha : ∃ x : ZMod p, x ^ 2 = a)
    (hb : ∃ x : ZMod p, x ^ 2 = b) : ∃ x : ZMod p, x ^ 2 = a * b := by
  obtain ⟨x, rfl⟩ := ha; obtain ⟨y, rfl⟩ := hb; exact ⟨x * y, by ring⟩

/-- The least nonresidue `n` of an odd prime satisfies `2 ≤ n`, `n` prime, `n(n-1) < p`. -/
theorem lnr_bounds (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) :
    2 ≤ lnr p ∧ (lnr p).Prime ∧ lnr p * (lnr p - 1) < p := by
  have := Fact.mk hp
  obtain ⟨hpos, hns, hmin⟩ := lnr_spec p hp hp3
  set n := lnr p with hn
  have h2 : 2 ≤ n := by
    by_contra h
    have : n = 1 := by omega
    exact hns ⟨1, by rw [this]; simp⟩
  -- `n < p`
  have hnp : n < p := by
    by_contra h
    have hm := hmin (p - 1) (by omega) (by omega)
    have hm2 := hmin 1 (by omega) (by omega)
    -- every nonzero residue is a square, contradiction with `exists_nonres` being below `p`
    obtain ⟨b, hb0, hbs⟩ := exists_nonres p hp hp3
    apply hbs
    have hbmod : ((b % p : ℕ) : ZMod p) = (b : ZMod p) := ZMod.natCast_mod b p
    rcases Nat.eq_zero_or_pos (b % p) with hz | hz
    · exact ⟨0, by rw [← hbmod, hz]; simp⟩
    · rw [← hbmod]; exact hmin _ hz (by have := Nat.mod_lt b hp.pos; omega)
  have hprime : n.Prime := by
    by_contra hnp'
    have hmf := Nat.minFac_dvd n
    have hmfp : (Nat.minFac n).Prime := Nat.minFac_prime (by omega)
    have hlt1 : Nat.minFac n < n := by
      rcases (Nat.minFac_le (by omega : 0 < n)).lt_or_eq with h | h
      · exact h
      · exact absurd (h ▸ hmfp) hnp'
    obtain ⟨t, ht⟩ := hmf
    have ht1 : 1 < t := by
      by_contra h
      have : t ≤ 1 := by omega
      interval_cases t
      · omega
      · omega
    have htn : t < n := by
      have := hmfp.two_le
      nlinarith
    apply hns
    rw [ht, Nat.cast_mul]
    exact sq_mul_sq (hmin _ hmfp.pos hlt1) (hmin _ (by omega) htn)
  refine ⟨h2, hprime, ?_⟩
  -- `m = p / n + 1`, `r = m n - p ∈ (0, n)`
  set m := p / n + 1 with hm
  have hndvd : ¬ n ∣ p := by
    intro hd
    rcases (Nat.prime_dvd_prime_iff_eq hprime hp).mp hd with h
    omega
  have hdiv := Nat.div_add_mod p n
  have hmod_pos : 0 < p % n := by
    rcases Nat.eq_zero_or_pos (p % n) with h | h
    · exact absurd (Nat.dvd_of_mod_eq_zero h) hndvd
    · exact h
  have hmodlt := Nat.mod_lt p (by omega : n > 0)
  set t := p / n with ht
  have hm1 : 0 < m := by rw [hm]; exact Nat.succ_pos _
  have hmn_eq : m * n = n * t + n := by rw [hm]; ring
  have hgt : p < m * n := by omega
  set r := m * n - p with hr
  have hr_eq : r + p = m * n := Nat.sub_add_cancel hgt.le
  have hr0 : 0 < r := by omega
  have hrn : r < n := by omega
  have hrsq := hmin r hr0 hrn
  -- if `m < n` then `m` is a square, hence so is `n`
  have hmn : n ≤ m := by
    by_contra hlt
    push Not at hlt
    have hmsq := hmin m hm1 hlt
    have hm0 : (m : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hd
      have := Nat.le_of_dvd (by omega) hd
      omega
    apply hns
    obtain ⟨a, ha⟩ := hmsq
    obtain ⟨b, hb⟩ := hrsq
    have hrel : (m : ZMod p) * n = r := by
      have : ((r + p : ℕ) : ZMod p) = ((m * n : ℕ) : ZMod p) := by rw [hr_eq]
      push_cast at this
      rw [ZMod.natCast_self, add_zero] at this
      exact this.symm
    have ha0 : a ≠ 0 := by rintro rfl; rw [← ha] at hm0; simp at hm0
    refine ⟨b / a, ?_⟩
    rw [div_pow, ha, hb, ← hrel]
    field_simp
  have h1 : n * (n - 1) ≤ n * t := Nat.mul_le_mul_left n (by omega)
  omega

end OMALargeSieve

end kitLS

namespace OMA980

open Finset

theorem crt_sum (M l : ℕ) (h : M.Coprime l) (hM : 0 < M) (hl : 0 < l) (f : ℕ → ℕ → ℕ) :
    ∑ r ∈ range (M * l), f (r % M) (r % l) = ∑ a ∈ range M, ∑ c ∈ range l, f a c := by
  rw [← Finset.sum_product']
  apply Finset.sum_nbij' (fun r => (r % M, r % l))
    (fun ac => (Nat.chineseRemainder h ac.1 ac.2 : ℕ))
  · intro r _
    simp only [Finset.mem_product, Finset.mem_range]
    exact ⟨Nat.mod_lt _ hM, Nat.mod_lt _ hl⟩
  · intro ac _
    simp only [Finset.mem_range]
    exact Nat.chineseRemainder_lt_mul h _ _ hM.ne' hl.ne'
  · intro r hr
    simp only [Finset.mem_range] at hr
    have h1 := Nat.chineseRemainder_modEq_unique h (Nat.mod_modEq r M).symm (Nat.mod_modEq r l).symm
    have hlt := Nat.chineseRemainder_lt_mul h (r % M) (r % l) hM.ne' hl.ne'
    simp only
    unfold Nat.ModEq at h1
    rw [Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hlt] at h1
    exact h1.symm
  · intro ac hac
    simp only [Finset.mem_product, Finset.mem_range] at hac
    have h1 := (Nat.chineseRemainder h ac.1 ac.2).prop.1
    have h2 := (Nat.chineseRemainder h ac.1 ac.2).prop.2
    unfold Nat.ModEq at h1 h2
    rw [h1, h2, Nat.mod_eq_of_lt hac.1, Nat.mod_eq_of_lt hac.2]
  · intro r _; rfl

theorem card_jacobi (l : ℕ) (hl : l.Prime) (hl2 : l ≠ 2) (s : ℤ) (hs : s = 1 ∨ s = -1) :
    2 * ((range l).filter (fun c : ℕ => jacobiSym (c : ℤ) l = s)).card = l - 1 := by
  have := Fact.mk hl
  set χ := quadraticChar (ZMod l) with hχ
  have hJ : ∀ c : ℕ, jacobiSym c l = χ (c : ZMod l) := by
    intro c
    rw [← jacobiSym.legendreSym.to_jacobiSym]
    simp [legendreSym, hχ]
  have hcard : ∀ t : ℤ, ((range l).filter (fun c : ℕ => jacobiSym (c : ℤ) l = t)).card =
      (Finset.univ.filter (fun a : ZMod l => χ a = t)).card := by
    intro t
    apply Finset.card_nbij' (fun c : ℕ => (c : ZMod l)) (fun a : ZMod l => a.val)
    · intro c hc
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hc
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
      rw [← hJ]; exact hc.2
    · intro a ha
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ha
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq]
      refine ⟨ZMod.val_lt a, ?_⟩
      rw [hJ, ZMod.natCast_zmod_val]; exact ha
    · intro c hc
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hc
      simp only
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt hc.1]
    · intro a _
      simp only [ZMod.natCast_zmod_val]
  have hchar : ringChar (ZMod l) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hl2
  have hsum := quadraticChar_sum_zero hchar
  have hpt : ∀ a : ZMod l, χ a = (if χ a = 1 then (1 : ℤ) else 0) - (if χ a = -1 then 1 else 0) := by
    intro a
    by_cases ha : a = 0
    · simp [hχ, ha]
    · rcases quadraticChar_dichotomy ha with h | h <;> simp [hχ, h]
  have hpt2 : ∀ a : ZMod l, (if χ a = 1 then (1 : ℤ) else 0) + (if χ a = -1 then 1 else 0) =
      if a ≠ 0 then 1 else 0 := by
    intro a
    by_cases ha : a = 0
    · simp [hχ, ha]
    · rcases quadraticChar_dichotomy ha with h | h <;> simp [hχ, h, ha]
  have e1 : ∑ a : ZMod l, χ a = ((Finset.univ.filter (fun a : ZMod l => χ a = 1)).card : ℤ) -
      (Finset.univ.filter (fun a : ZMod l => χ a = -1)).card := by
    rw [Finset.sum_congr rfl (fun a _ => hpt a), Finset.sum_sub_distrib, Finset.sum_boole,
      Finset.sum_boole]
  have e2 : ((Finset.univ.filter (fun a : ZMod l => χ a = 1)).card : ℤ) +
      (Finset.univ.filter (fun a : ZMod l => χ a = -1)).card = l - 1 := by
    rw [← Finset.sum_boole, ← Finset.sum_boole, ← Finset.sum_add_distrib,
      Finset.sum_congr rfl (fun a _ => hpt2 a), Finset.sum_boole]
    have : (Finset.univ.filter (fun a : ZMod l => a ≠ 0)) = Finset.univ.erase 0 := by
      ext a; simp
    rw [this, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]
    have := hl.one_lt
    push_cast [Nat.cast_sub this.le]
    ring
  have hl1 : 1 ≤ l := hl.one_lt.le
  rw [hcard s]
  zify [hl1]
  rw [← e2]
  rcases hs with rfl | rfl <;> linarith [e1, hsum]

theorem coprime_mod_iff (r M : ℕ) : (r % M).Coprime M ↔ r.Coprime M := by
  unfold Nat.Coprime
  rw [← Nat.gcd_rec M r, Nat.gcd_comm]

theorem step_count (M l : ℕ) (hM4 : 4 ∣ M) (hMl : M.Coprime l) (hl : l.Prime) (hl2 : l ≠ 2)
    (P : ℕ → Prop) [DecidablePred P] :
    2 * ((range (M * l)).filter (fun r => r.Coprime (M * l) ∧ P (r % M) ∧
        jacobiSym l r = 1)).card
      = ((range M).filter (fun a => a.Coprime M ∧ P a)).card * (l - 1) := by
  have := Fact.mk hl
  have hM : 0 < M := Nat.pos_of_ne_zero (by rintro rfl; simp at hMl; exact hl.one_lt.ne' hMl)
  have hlpos := hl.pos
  have hlodd : Odd l := hl.odd_of_ne_two hl2
  set F : ℕ → ℕ → ℕ := fun (a c : ℕ) => if (a.Coprime M ∧ P a) ∧ jacobiSym c l = qrSign a l then 1 else 0
    with hF
  have hodd : ∀ a : ℕ, a.Coprime M → Odd a := by
    intro a ha
    rw [Nat.odd_iff]
    by_contra h
    have h2 : 2 ∣ a := by omega
    have : 2 ∣ Nat.gcd a M := Nat.dvd_gcd h2 ((by norm_num : (2:ℕ) ∣ 4).trans hM4)
    rw [ha] at this; omega
  have hcond : ∀ r : ℕ, (r.Coprime (M * l) ∧ P (r % M) ∧ jacobiSym l r = 1) ↔
      ((r % M).Coprime M ∧ P (r % M)) ∧ jacobiSym ((r % l : ℕ) : ℤ) l = qrSign (r % M) l := by
    intro r
    have hJl : jacobiSym ((r % l : ℕ) : ℤ) l = jacobiSym r l := by
      rw [jacobiSym.mod_left (r : ℤ) l]; push_cast; rfl
    have hq : qrSign (r % M) l = qrSign r l := by
      unfold qrSign
      congr 1
      rw [ZMod.χ₄_nat_mod_four r, ZMod.χ₄_nat_mod_four (r % M), Nat.mod_mod_of_dvd r hM4]
    rw [hJl, hq, coprime_mod_iff, Nat.coprime_mul_iff_right]
    constructor
    · rintro ⟨⟨h1, h2⟩, hP, hJ⟩
      refine ⟨⟨h1, hP⟩, ?_⟩
      have hro := hodd r h1
      rw [jacobiSym.quadratic_reciprocity' hlodd hro] at hJ
      have hsq := qrSign.sq_eq_one hro hlodd
      calc jacobiSym r l = qrSign r l * (qrSign r l * jacobiSym r l) := by
            rw [← mul_assoc, ← sq, hsq, one_mul]
        _ = qrSign r l := by rw [hJ, mul_one]
    · rintro ⟨⟨h1, hP⟩, hJ⟩
      have hro := hodd r h1
      have hsq := qrSign.sq_eq_one hro hlodd
      have hne : jacobiSym r l ≠ 0 := by
        rw [hJ]; intro h0; rw [h0] at hsq; norm_num at hsq
      refine ⟨⟨h1, ?_⟩, hP, ?_⟩
      · have := (jacobiSym.eq_zero_iff_not_coprime (a := (r : ℤ)) (b := l)).not.mp hne
        push Not at this
        rw [Int.gcd_natCast_natCast] at this
        exact this
      · rw [jacobiSym.quadratic_reciprocity' hlodd hro, hJ, ← sq, hsq]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_congr rfl (fun r _ => (if_congr (hcond r) rfl rfl :
    (if (r.Coprime (M * l) ∧ P (r % M) ∧ jacobiSym l r = 1) then 1 else 0) = F (r % M) (r % l)))]
  rw [crt_sum M l hMl hM hlpos F, Finset.mul_sum, Finset.card_eq_sum_ones, Finset.sum_filter,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  simp only [hF]
  by_cases ha : a.Coprime M ∧ P a
  · have h1 := ha.1
    have h2 := ha.2
    rw [if_pos ha, one_mul]
    simp only [and_iff_right ha]
    rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones]
    have hao := hodd a ha.1
    have hs : qrSign a l = 1 ∨ qrSign a l = -1 := by
      have := qrSign.sq_eq_one hao hlodd
      rw [sq] at this
      exact mul_self_eq_one_iff.mp this
    exact card_jacobi l hl hl2 _ hs
  · simp [ha]

/-- The modulus `4 ∏_{j<i} p_j`. -/
noncomputable def Mi (i : ℕ) : ℕ := 4 * ∏ j ∈ range i, Nat.nth Nat.Prime j

/-- Residues mod `Mi i` for which `p_0, …, p_{i-1}` are all residues (in Jacobi form). -/
noncomputable def Ai (i : ℕ) : Finset ℕ :=
  (range (Mi i)).filter (fun r => r.Coprime (Mi i) ∧ ∀ j < i, jacobiSym (Nat.nth Nat.Prime j) r = 1)

theorem Mi_pos (i : ℕ) : 0 < Mi i := by
  unfold Mi
  have := Finset.prod_pos (s := range i) (f := fun j => Nat.nth Nat.Prime j)
    (fun j _ => (Nat.prime_nth_prime j).pos)
  omega

theorem dvd_Mi {i j : ℕ} (h : j < i) : 4 * Nat.nth Nat.Prime j ∣ Mi i :=
  mul_dvd_mul_left 4 (Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr h))

theorem Mi_succ (i : ℕ) : Mi (i + 1) = Mi i * Nat.nth Nat.Prime i := by
  unfold Mi; rw [Finset.prod_range_succ]; ring

theorem odd_of_coprime_Mi {i r : ℕ} (h : r.Coprime (Mi i)) : Odd r := by
  rw [Nat.odd_iff]
  by_contra h'
  have h2 : 2 ∣ r := by omega
  have : 2 ∣ Nat.gcd r (Mi i) := Nat.dvd_gcd h2 (Dvd.dvd.mul_right (by norm_num) _)
  rw [h] at this; omega

/-- `J(p_j | r)` only depends on `r mod Mi i` for `j < i` and odd `r`. -/
theorem jac_mod {i j r : ℕ} (hj : j < i) (hr : Odd r) :
    jacobiSym (Nat.nth Nat.Prime j) (r % Mi i) = jacobiSym (Nat.nth Nat.Prime j) r := by
  have hd := dvd_Mi hj
  have hro : Odd (r % Mi i) := by
    rw [Nat.odd_iff] at hr ⊢
    rw [Nat.mod_mod_of_dvd r ((by norm_num : (2:ℕ) ∣ 4).trans ((dvd_mul_right 4 _).trans hd))]
    exact hr
  rw [jacobiSym.mod_right _ hr, jacobiSym.mod_right _ hro]
  simp only [Int.natAbs_natCast]
  rw [Nat.mod_mod_of_dvd r hd]

theorem class_count (i : ℕ) : 2 ^ i * (Ai i).card = (Mi i).totient := by
  induction i with
  | zero =>
    simp only [Ai, Mi, Finset.range_zero, Finset.prod_empty, mul_one, pow_zero, one_mul]
    simp only [Nat.not_lt_zero, false_imp_iff, imp_true_iff, and_true, IsEmpty.forall_iff]
    rw [Nat.totient]
    congr 1
    try (ext r; simp [Nat.coprime_comm])
  | succ i ih =>
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · -- modulus 8
      have hM : Mi 1 = 8 := by simp [Mi, Nat.nth_prime_zero_eq_two]
      have hA : Ai 1 = (range 8).filter (fun r => r % 8 = 1 ∨ r % 8 = 7) := by
        unfold Ai
        rw [hM]
        apply Finset.filter_congr
        intro r hr
        rw [Finset.mem_range] at hr
        simp only [Nat.lt_one_iff, forall_eq, Nat.nth_prime_zero_eq_two]
        constructor
        · rintro ⟨hc, hj⟩
          have hro : Odd r := by
            rw [Nat.odd_iff]; by_contra h'
            have : 2 ∣ Nat.gcd r 8 := Nat.dvd_gcd (by omega) (by norm_num)
            rw [hc] at this; omega
          have := jacobiSym.at_two hro
          push_cast at hj
          rw [hj, ZMod.χ₈_nat_eq_if_mod_eight] at this
          split_ifs at this with h1 h2 <;> first | omega | (norm_num at this)
        · intro h
          have hro : Odd r := by rw [Nat.odd_iff]; omega
          refine ⟨?_, ?_⟩
          · interval_cases r <;> simp_all <;> decide
          · push_cast
            rw [jacobiSym.at_two hro, ZMod.χ₈_nat_eq_if_mod_eight]
            split_ifs with h1 h2 <;> first | rfl | omega
      rw [hA, hM]
      decide
    · set l := Nat.nth Nat.Prime i with hl
      have hlp : l.Prime := Nat.prime_nth_prime i
      have hmono := Nat.nth_strictMono Nat.infinite_setOfPred_prime
      have hl2 : l ≠ 2 := by
        intro h
        have : Nat.nth Nat.Prime 0 < l := hmono hi
        rw [Nat.nth_prime_zero_eq_two, h] at this; omega
      have hcop : (Mi i).Coprime l := by
        unfold Mi
        apply Nat.Coprime.mul_left
        · rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hlp]
          intro h
          have : l ∣ 2 ^ 2 := by norm_num; exact h
          have := hlp.dvd_of_dvd_pow this
          exact hl2 ((Nat.prime_dvd_prime_iff_eq hlp Nat.prime_two).mp this)
        · apply Nat.Coprime.prod_left
          intro j hj
          rw [Finset.mem_range] at hj
          rw [Nat.coprime_primes (Nat.prime_nth_prime j) hlp]
          exact (hmono hj).ne
      have hstep := step_count (Mi i) l (dvd_mul_right 4 _) hcop hlp hl2
        (fun a => ∀ j < i, jacobiSym (Nat.nth Nat.Prime j) a = 1)
      have hA : Ai (i + 1) = (range (Mi i * l)).filter (fun r => r.Coprime (Mi i * l) ∧
          (∀ j < i, jacobiSym (Nat.nth Nat.Prime j) (r % Mi i) = 1) ∧ jacobiSym l r = 1) := by
        unfold Ai
        rw [Mi_succ]
        apply Finset.filter_congr
        intro r _
        constructor
        · rintro ⟨hc, hj⟩
          have hro := odd_of_coprime_Mi (i := i) (Nat.Coprime.coprime_mul_right_right hc)
          refine ⟨hc, fun j hji => ?_, hj i (Nat.lt_succ_self i)⟩
          rw [jac_mod hji hro]; exact hj j (by omega)
        · rintro ⟨hc, hj, hl1⟩
          have hro := odd_of_coprime_Mi (i := i) (Nat.Coprime.coprime_mul_right_right hc)
          refine ⟨hc, fun j hji => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hji with h | h
          · rw [← jac_mod h hro]; exact hj j h
          · rw [h]; exact hl1
      have hA' : Ai i = (range (Mi i)).filter (fun a => a.Coprime (Mi i) ∧
          ∀ j < i, jacobiSym (Nat.nth Nat.Prime j) a = 1) := rfl
      rw [Mi_succ, Nat.totient_mul hcop, Nat.totient_prime hlp, ← ih, hA, pow_succ]
      rw [hA', mul_assoc, hstep, mul_assoc]

end OMA980

namespace OMA980

open Filter Topology Finset

/-- `π(x; q, r)`: primes `p < x` with `p % q = r`. -/
noncomputable def piAP (q r : ℕ) (x : ℝ) : ℕ :=
  ((Nat.primesBelow ⌈x⌉₊).filter (fun p => p % q = r)).card

/-- `θ(x; q, r)`. -/
noncomputable def thAP (q r : ℕ) (x : ℝ) : ℝ :=
  ∑ p ∈ (Ioc 0 ⌊x⌋₊).filter (fun p => p.Prime ∧ p % q = r), Real.log p

/-- primes `p ≤ x` with `p % q = r`. -/
noncomputable def cLE (q r : ℕ) (x : ℝ) : ℕ :=
  ((Ioc 0 ⌊x⌋₊).filter (fun p => p.Prime ∧ p % q = r)).card

theorem psiAP_eq (q r : ℕ) (x : ℝ) : OMAPNT.psiAP (r : ZMod q) x =
    ∑ k ∈ Ioc 0 ⌊x⌋₊, (if k % q = r % q then ArithmeticFunction.vonMangoldt k else 0) := by
  rw [OMAPNT.psiAP, OMAPNT.Icc_one_eq_Ioc_zero]
  apply Finset.sum_congr rfl
  intro k _
  simp only [ArithmeticFunction.vonMangoldt.residueClass, Set.indicator_apply, Set.mem_ofPred_eq,
    ZMod.natCast_eq_natCast_iff']

theorem thAP_le_psiAP (q r : ℕ) (hr : r < q) (x : ℝ) : thAP q r x ≤ OMAPNT.psiAP (r : ZMod q) x := by
  rw [psiAP_eq, thAP, Finset.sum_filter]
  apply Finset.sum_le_sum
  intro k _
  by_cases h : k.Prime ∧ k % q = r
  · rw [if_pos h, if_pos (by rw [h.2, Nat.mod_eq_of_lt hr]),
      ArithmeticFunction.vonMangoldt_apply_prime h.1]
  · rw [if_neg h]
    split_ifs
    · exact ArithmeticFunction.vonMangoldt_nonneg
    · exact le_rfl

theorem psiAP_sub_thAP (q r : ℕ) (hr : r < q) (x : ℝ) :
    OMAPNT.psiAP (r : ZMod q) x - thAP q r x ≤ Chebyshev.psi x - Chebyshev.theta x := by
  rw [psiAP_eq, thAP, Finset.sum_filter, Chebyshev.psi, Chebyshev.theta, Finset.sum_filter,
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro k _
  rw [Nat.mod_eq_of_lt hr]
  by_cases hc : k % q = r
  · by_cases hp : k.Prime
    · simp [hc, hp]
    · simp [hc, hp]
  · by_cases hp : k.Prime
    · simp [hc, hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
    · simp [hc, hp, ArithmeticFunction.vonMangoldt_nonneg]

theorem card_primes_Ioc (n : ℕ) : ((Ioc 0 n).filter Nat.Prime).card = Nat.primeCounting n := by
  rw [← Nat.primesLE_card_eq_primeCounting, Nat.primesLE_eq_filter_range]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range]
  constructor
  · rintro ⟨⟨_, h⟩, hp⟩; exact ⟨by omega, hp⟩
  · rintro ⟨h, hp⟩; exact ⟨⟨hp.pos, by omega⟩, hp⟩

theorem cLE_upper (q r : ℕ) {x : ℝ} (hx : 1 < x) :
    (cLE q r x : ℝ) ≤ thAP q r x / Real.log x +
      ((Nat.primeCounting ⌊x⌋₊ : ℝ) - Chebyshev.theta x / Real.log x) := by
  have hl : 0 < Real.log x := Real.log_pos hx
  have hx0 : 0 < x := by linarith
  have hle : ∀ p ∈ Ioc 0 ⌊x⌋₊, Real.log p ≤ Real.log x := by
    intro p hp
    rw [Finset.mem_Ioc] at hp
    apply Real.log_le_log (by exact_mod_cast hp.1)
    exact (Nat.le_floor_iff hx0.le).mp hp.2
  set S := (Ioc 0 ⌊x⌋₊).filter (fun p => p.Prime ∧ p % q = r)
  set T := (Ioc 0 ⌊x⌋₊).filter Nat.Prime
  have hST : S ⊆ T := by
    intro p hp; simp only [S, T, Finset.mem_filter] at hp ⊢; exact ⟨hp.1, hp.2.1⟩
  have h1 : (cLE q r x : ℝ) = thAP q r x / Real.log x + ∑ p ∈ S, (1 - Real.log p / Real.log x) := by
    rw [Finset.sum_sub_distrib, thAP, Finset.sum_div, cLE]
    simp only [S, Finset.sum_const, nsmul_eq_mul, mul_one]
    ring
  have h2 : ∑ p ∈ S, (1 - Real.log p / Real.log x) ≤ ∑ p ∈ T, (1 - Real.log p / Real.log x) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hST
    intro p hp _
    simp only [T, Finset.mem_filter] at hp
    have := hle p hp.1
    rw [sub_nonneg, div_le_one hl]; exact this
  have h3 : ∑ p ∈ T, (1 - Real.log p / Real.log x) =
      (Nat.primeCounting ⌊x⌋₊ : ℝ) - Chebyshev.theta x / Real.log x := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, Chebyshev.theta, ← card_primes_Ioc]
    simp [T]
  linarith

theorem cLE_lower (q r : ℕ) {x : ℝ} (hx : 1 < x) :
    thAP q r x / Real.log x ≤ cLE q r x := by
  have hl : 0 < Real.log x := Real.log_pos hx
  have hx0 : 0 < x := by linarith
  rw [div_le_iff₀ hl, thAP, cLE, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_Ioc] at hp
  simp only [Nat.cast_one, one_mul]
  apply Real.log_le_log (by exact_mod_cast hp.1.1)
  exact (Nat.le_floor_iff hx0.le).mp hp.1.2

theorem piAP_le_cLE (q r : ℕ) {x : ℝ} (hx : 0 < x) : piAP q r x ≤ cLE q r x := by
  apply Finset.card_le_card
  intro p hp
  simp only [Finset.mem_filter, Nat.mem_primesBelow, Finset.mem_Ioc] at hp ⊢
  refine ⟨⟨hp.1.2.pos, ?_⟩, hp.1.2, hp.2⟩
  have := (Nat.lt_ceil).mp hp.1.1
  exact Nat.le_floor this.le

theorem cLE_le_piAP (q r : ℕ) {x : ℝ} (hx : 0 < x) : cLE q r x ≤ piAP q r x + 1 := by
  unfold cLE piAP
  refine le_trans (Finset.card_le_card (t := insert ⌊x⌋₊
    ((Nat.primesBelow ⌈x⌉₊).filter (fun p => p % q = r))) ?_) (Finset.card_insert_le _ _)
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_Ioc] at hp
  rw [Finset.mem_insert]
  rcases eq_or_lt_of_le hp.1.2 with h | h
  · exact Or.inl h
  · right
    simp only [Finset.mem_filter, Nat.mem_primesBelow]
    refine ⟨⟨?_, hp.2.1⟩, hp.2.2⟩
    apply Nat.lt_ceil.mpr
    have : (p : ℝ) < ⌊x⌋₊ := by exact_mod_cast h
    exact lt_of_lt_of_le this (Nat.floor_le hx.le)

theorem tendsto_log_div_self : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) :=
  Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero

theorem tendsto_E_div : Tendsto (fun x : ℝ => ((Nat.primeCounting ⌊x⌋₊ : ℝ) -
    Chebyshev.theta x / Real.log x) / (x / Real.log x)) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := Chebyshev.primeCounting_sub_theta_div_log_isBigO.bound
  have hlim : Tendsto (fun x : ℝ => |C| / Real.log x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [hC, eventually_gt_atTop 1] with x hx hx1
  have hl : 0 < Real.log x := Real.log_pos hx1
  have hx0 : 0 < x := by linarith
  rw [norm_div, Real.norm_eq_abs (x / Real.log x), abs_of_pos (by positivity)]
  rw [Real.norm_eq_abs (x / Real.log x ^ 2), abs_of_pos (by positivity)] at hx
  rw [div_le_iff₀ (by positivity)]
  calc _ ≤ C * (x / Real.log x ^ 2) := hx
    _ ≤ |C| * (x / Real.log x ^ 2) := mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    _ = |C| / Real.log x * (x / Real.log x) := by field_simp

theorem tendsto_thAP {q r : ℕ} (hq : 0 < q) (hr : r < q) (hcop : r.Coprime q) :
    Tendsto (fun x => thAP q r x / x) atTop (𝓝 ((q.totient : ℝ)⁻¹)) := by
  have : NeZero q := ⟨hq.ne'⟩
  have hu : IsUnit (r : ZMod q) := (ZMod.isUnit_iff_coprime r q).mpr hcop
  have hpsi := OMAPNT.tendsto_psiAP (r : ZMod q) hu
  have hd : Tendsto (fun x => (Chebyshev.psi x - Chebyshev.theta x) / x) atTop (𝓝 0) := by
    have := OMAPNT.tendsto_psi_div.sub OMAPNT.tendsto_theta_div
    simp only [sub_self] at this
    refine this.congr' ?_
    filter_upwards with x
    ring
  have hd2 : Tendsto (fun x => (OMAPNT.psiAP (r : ZMod q) x - thAP q r x) / x) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ hd
    · filter_upwards [eventually_gt_atTop 0] with x hx
      exact div_nonneg (sub_nonneg.mpr (thAP_le_psiAP q r hr x)) hx.le
    · filter_upwards [eventually_gt_atTop 0] with x hx
      exact div_le_div_of_nonneg_right (psiAP_sub_thAP q r hr x) hx.le
  have := hpsi.sub hd2
  simp only [sub_zero] at this
  refine this.congr' ?_
  filter_upwards with x
  ring

theorem tendsto_piAP {q r : ℕ} (hq : 0 < q) (hr : r < q) (hcop : r.Coprime q) :
    Tendsto (fun x => (piAP q r x : ℝ) / (x / Real.log x)) atTop (𝓝 ((q.totient : ℝ)⁻¹)) := by
  have hth := tendsto_thAP hq hr hcop
  have hlow : Tendsto (fun x => thAP q r x / x - Real.log x / x) atTop
      (𝓝 ((q.totient : ℝ)⁻¹)) := by
    simpa using hth.sub tendsto_log_div_self
  have hup : Tendsto (fun x => thAP q r x / x + ((Nat.primeCounting ⌊x⌋₊ : ℝ) -
      Chebyshev.theta x / Real.log x) / (x / Real.log x)) atTop (𝓝 ((q.totient : ℝ)⁻¹)) := by
    simpa using hth.add tendsto_E_div
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
  · filter_upwards [eventually_gt_atTop 1] with x hx
    have hl : 0 < Real.log x := Real.log_pos hx
    have hx0 : 0 < x := by linarith
    have h1 := cLE_lower q r hx
    have h2 := cLE_le_piAP q r hx0
    have h2' : (cLE q r x : ℝ) ≤ piAP q r x + 1 := by exact_mod_cast h2
    rw [le_div_iff₀ (by positivity)]
    have : (thAP q r x / x - Real.log x / x) * (x / Real.log x) = thAP q r x / Real.log x - 1 := by
      field_simp
    rw [this]; linarith
  · filter_upwards [eventually_gt_atTop 1] with x hx
    have hl : 0 < Real.log x := Real.log_pos hx
    have hx0 : 0 < x := by linarith
    have h1 := cLE_upper q r hx
    have h2 := piAP_le_cLE q r hx0
    have h2' : (piAP q r x : ℝ) ≤ cLE q r x := by exact_mod_cast h2
    rw [div_le_iff₀ (by positivity)]
    have : (thAP q r x / x + ((Nat.primeCounting ⌊x⌋₊ : ℝ) - Chebyshev.theta x / Real.log x) /
        (x / Real.log x)) * (x / Real.log x) = thAP q r x / Real.log x +
        ((Nat.primeCounting ⌊x⌋₊ : ℝ) - Chebyshev.theta x / Real.log x) := by
      field_simp
    rw [this]; linarith

end OMA980

namespace OMA980

open Filter Topology Finset

noncomputable abbrev nr (p : ℕ) : ℕ := Erdos980.leastNonresidue 2 p

theorem nr_prime {p : ℕ} (hp : p.Prime) (h : p % 2 = 1) : (nr p).Prime := by
  have h3 : 3 ≤ p := by have := hp.two_le; omega
  exact (OMALargeSieve.lnr_bounds p hp h3).2.1

/-- number of odd primes `p < x` with `n(p) = p_i`. -/
noncomputable def cnt (i : ℕ) (x : ℝ) : ℕ :=
  ((Nat.primesBelow ⌈x⌉₊).filter (fun p => p % 2 = 1 ∧ nr p = Nat.nth Nat.Prime i)).card

/-- `ℓ` is a quadratic residue mod `p`. -/
def QR (l p : ℕ) : Prop := ∃ y : ZMod p, y ^ 2 = (l : ZMod p)

theorem nr_eq_iff {p : ℕ} (hp : p.Prime) (h2 : p % 2 = 1) (i : ℕ) :
    nr p = Nat.nth Nat.Prime i ↔ (∀ j < i, QR (Nat.nth Nat.Prime j) p) ∧
      ¬ QR (Nat.nth Nat.Prime i) p := by
  have h3 : 3 ≤ p := by have := hp.two_le; omega
  have hmono := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  obtain ⟨hpos, hns, hmin⟩ := OMALargeSieve.lnr_spec p hp h3
  have hnr : nr p = OMALargeSieve.lnr p := rfl
  constructor
  · intro h
    rw [hnr] at h
    refine ⟨fun j hj => ?_, by rw [← h]; exact hns⟩
    exact hmin _ (Nat.prime_nth_prime j).pos (by rw [h]; exact hmono hj)
  · rintro ⟨hj, hi⟩
    have hle : nr p ≤ Nat.nth Nat.Prime i :=
      Nat.sInf_le ⟨(Nat.prime_nth_prime i).pos, hi⟩
    have hpr := nr_prime hp h2
    set c := Nat.count Nat.Prime (nr p) with hc
    have hnc : Nat.nth Nat.Prime c = nr p := Nat.nth_count hpr
    have hci : c ≤ i := by rw [← hmono.le_iff_le, hnc]; exact hle
    rcases eq_or_lt_of_le hci with h | h
    · rw [← hnc, h]
    · exfalso
      apply hns
      have := hj c h
      rw [hnc] at this
      exact this

theorem qr_iff_jacobi {p l : ℕ} (hp : p.Prime) (hl : l.Prime) (hne : l ≠ p) :
    QR l p ↔ jacobiSym l p = 1 := by
  have := Fact.mk hp
  have h0 : ((l : ℤ) : ZMod p) ≠ 0 := by
    rw [Int.cast_natCast, Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    exact hne ((Nat.prime_dvd_prime_iff_eq hp hl).mp hd).symm
  rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_one_iff p h0, Int.cast_natCast, QR]
  constructor
  · rintro ⟨y, hy⟩; exact ⟨y, by rw [← hy, sq]⟩
  · rintro ⟨y, hy⟩; exact ⟨y, by rw [hy, sq]⟩

open Classical in
/-- Odd primes `p < x` for which `p_0, …, p_{i-1}` are residues. -/
noncomputable def Dset (i : ℕ) (x : ℝ) : Finset ℕ :=
  (Nat.primesBelow ⌈x⌉₊).filter (fun p => p % 2 = 1 ∧ ∀ j < i, QR (Nat.nth Nat.Prime j) p)

theorem Dset_iff {i p : ℕ} (hp : p.Prime) (hpM : Mi i < p) :
    (p % 2 = 1 ∧ ∀ j < i, QR (Nat.nth Nat.Prime j) p) ↔ p % Mi i ∈ Ai i := by
  have hM4 : 4 ≤ Mi i := by
    unfold Mi
    have := Finset.prod_pos (s := range i) (f := fun j => Nat.nth Nat.Prime j)
      (fun j _ => (Nat.prime_nth_prime j).pos)
    omega
  have hp2 : p % 2 = 1 := by
    rcases Nat.even_or_odd p with he | ho
    · exfalso; have := (Nat.Prime.even_iff hp).mp he; omega
    · exact Nat.odd_iff.mp ho
  have hpo : Odd p := Nat.odd_iff.mpr hp2
  have hcop : p.Coprime (Mi i) := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hd
    have := Nat.le_of_dvd (Mi_pos i) hd
    omega
  unfold Ai
  rw [Finset.mem_filter, Finset.mem_range, coprime_mod_iff]
  constructor
  · rintro ⟨_, hj⟩
    refine ⟨Nat.mod_lt _ (Mi_pos i), hcop, fun j hji => ?_⟩
    rw [jac_mod hji hpo]
    have hlt : Nat.nth Nat.Prime j < p := by
      have := dvd_Mi hji
      have := Nat.le_of_dvd (Mi_pos i) this
      omega
    exact (qr_iff_jacobi hp (Nat.prime_nth_prime j) hlt.ne).mp (hj j hji)
  · rintro ⟨_, _, hj⟩
    refine ⟨hp2, fun j hji => ?_⟩
    have hlt : Nat.nth Nat.Prime j < p := by
      have := dvd_Mi hji
      have := Nat.le_of_dvd (Mi_pos i) this
      omega
    rw [qr_iff_jacobi hp (Nat.prime_nth_prime j) hlt.ne, ← jac_mod hji hpo]
    exact hj j hji

theorem sum_piAP_eq (i : ℕ) (x : ℝ) : ∑ r ∈ Ai i, (piAP (Mi i) r x : ℝ) =
    ((Nat.primesBelow ⌈x⌉₊).filter (fun p => p % Mi i ∈ Ai i)).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun p => p % Mi i) (t := Ai i)]
  · push_cast
    apply Finset.sum_congr rfl
    intro r hr
    unfold piAP
    congr 2
    ext p
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, by rw [h2]; exact hr⟩, h2⟩
    · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
  · intro p hp
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hp
    exact hp.2

open Classical in
theorem tendsto_D (i : ℕ) : Tendsto (fun x : ℝ => ((Dset i x).card : ℝ) / (x / Real.log x)) atTop
    (𝓝 (1 / 2 ^ i)) := by
  set M := Mi i
  have hMpos := Mi_pos i
  -- the class sum
  have hsum : Tendsto (fun x : ℝ => ∑ r ∈ Ai i, (piAP M r x : ℝ) / (x / Real.log x)) atTop
      (𝓝 (∑ r ∈ Ai i, ((M.totient : ℝ)⁻¹))) := by
    apply tendsto_finsetSum
    intro r hr
    unfold Ai at hr
    rw [Finset.mem_filter, Finset.mem_range] at hr
    exact tendsto_piAP hMpos hr.1 hr.2.1
  have hval : ∑ r ∈ Ai i, ((M.totient : ℝ)⁻¹) = 1 / 2 ^ i := by
    rw [Finset.sum_const, nsmul_eq_mul]
    have hc := class_count i
    have htot : (0 : ℝ) < M.totient := by exact_mod_cast Nat.totient_pos.mpr hMpos
    have hA0 : ((Ai i).card : ℝ) ≠ 0 := by
      intro h0; rw [← hc] at htot; push_cast at htot; rw [h0] at htot; simp at htot
    rw [← hc]
    push_cast
    field_simp
  rw [hval] at hsum
  have herr : Tendsto (fun x : ℝ => ((M : ℝ) + 1) / (x / Real.log x)) atTop (𝓝 0) := by
    have := (tendsto_log_div_self).const_mul ((M : ℝ) + 1)
    simp only [mul_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 1] with x hx
    have : 0 < Real.log x := Real.log_pos hx
    field_simp
  have hlow := hsum.sub herr
  have hup := hsum.add herr
  simp only [sub_zero, add_zero] at hlow hup
  -- comparison of the two sets
  have hsub1 : ∀ x : ℝ, Dset i x ⊆ (Nat.primesBelow ⌈x⌉₊).filter (fun p => p % M ∈ Ai i) ∪
      range (M + 1) := by
    intro x p hp
    rw [Finset.mem_union, Finset.mem_range]
    by_cases hpM : p < M + 1
    · exact Or.inr hpM
    · left
      unfold Dset at hp
      rw [Finset.mem_filter] at hp ⊢
      exact ⟨hp.1, (Dset_iff (Nat.prime_of_mem_primesBelow hp.1) (by omega)).mp hp.2⟩
  have hsub2 : ∀ x : ℝ, (Nat.primesBelow ⌈x⌉₊).filter (fun p => p % M ∈ Ai i) ⊆ Dset i x ∪
      range (M + 1) := by
    intro x p hp
    rw [Finset.mem_union, Finset.mem_range]
    by_cases hpM : p < M + 1
    · exact Or.inr hpM
    · left
      unfold Dset
      rw [Finset.mem_filter] at hp ⊢
      exact ⟨hp.1, (Dset_iff (Nat.prime_of_mem_primesBelow hp.1) (by omega)).mpr hp.2⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
  · filter_upwards [eventually_gt_atTop 1] with x hx
    have hw : 0 < x / Real.log x := div_pos (by linarith) (Real.log_pos hx)
    have h := (Finset.card_le_card (hsub2 x)).trans (Finset.card_union_le _ _)
    rw [Finset.card_range] at h
    have h' : (((Nat.primesBelow ⌈x⌉₊).filter (fun p => p % M ∈ Ai i)).card : ℝ) ≤
        (Dset i x).card + (M + 1) := by exact_mod_cast h
    rw [← Finset.sum_div, div_sub_div_same, sum_piAP_eq]
    exact div_le_div_of_nonneg_right (by linarith) hw.le
  · filter_upwards [eventually_gt_atTop 1] with x hx
    have hw : 0 < x / Real.log x := div_pos (by linarith) (Real.log_pos hx)
    have h := (Finset.card_le_card (hsub1 x)).trans (Finset.card_union_le _ _)
    rw [Finset.card_range] at h
    have h' : ((Dset i x).card : ℝ) ≤
        (((Nat.primesBelow ⌈x⌉₊).filter (fun p => p % M ∈ Ai i)).card : ℝ) + (M + 1) := by
      exact_mod_cast h
    rw [← Finset.sum_div, ← add_div, sum_piAP_eq]
    exact div_le_div_of_nonneg_right h' hw.le

open Classical in
theorem cnt_add (i : ℕ) (x : ℝ) : (cnt i x : ℝ) + (Dset (i + 1) x).card = (Dset i x).card := by
  have hsub : Dset (i + 1) x ⊆ Dset i x := by
    intro p hp
    unfold Dset at hp ⊢
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, hp.2.1, fun j hj => hp.2.2 j (by omega)⟩
  have heq : (Nat.primesBelow ⌈x⌉₊).filter (fun p => p % 2 = 1 ∧ nr p = Nat.nth Nat.Prime i) =
      Dset i x \ Dset (i + 1) x := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_sdiff, Dset]
    constructor
    · rintro ⟨hpb, hp2, hpi⟩
      have hp := Nat.prime_of_mem_primesBelow hpb
      rw [nr_eq_iff hp hp2] at hpi
      refine ⟨⟨hpb, hp2, hpi.1⟩, ?_⟩
      rintro ⟨_, _, hall⟩
      exact hpi.2 (hall i (Nat.lt_succ_self i))
    · rintro ⟨⟨hpb, hp2, hj⟩, hn⟩
      have hp := Nat.prime_of_mem_primesBelow hpb
      refine ⟨hpb, hp2, (nr_eq_iff hp hp2 i).mpr ⟨hj, ?_⟩⟩
      intro hq
      apply hn
      refine ⟨hpb, hp2, fun j hji => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hji with h | h
      · exact hj j h
      · rw [h]; exact hq
  unfold cnt
  rw [heq, Finset.card_sdiff_of_subset hsub]
  have := Finset.card_le_card hsub
  push_cast [this]
  ring

theorem main_term (i : ℕ) : Tendsto (fun x : ℝ => (cnt i x : ℝ) / (x / Real.log x)) atTop
    (𝓝 (1 / 2 ^ (i + 1))) := by
  have := (tendsto_D i).sub (tendsto_D (i + 1))
  have hv : (1 : ℝ) / 2 ^ i - 1 / 2 ^ (i + 1) = 1 / 2 ^ (i + 1) := by
    rw [pow_succ]; field_simp; ring
  rw [hv] at this
  refine this.congr' ?_
  filter_upwards with x
  rw [← sub_div, ← cnt_add i x]
  ring

end OMA980

namespace OMA980

open Finset

/-- `∑_{q ≤ z squarefree} ∏_{p | q} g(p)`. -/
noncomputable def Fsum (g : ℕ → ℝ) (z : ℕ) : ℝ :=
  ∑ q ∈ (Icc 1 z).filter Squarefree, ∏ p ∈ q.primeFactors, g p

/-- the same sum restricted to `r ∤ q`. -/
noncomputable def Bsum (g : ℕ → ℝ) (r z : ℕ) : ℝ :=
  ∑ q ∈ (Icc 1 z).filter (fun q => Squarefree q ∧ ¬ r ∣ q), ∏ p ∈ q.primeFactors, g p

theorem Fsum_split (g : ℕ → ℝ) {r : ℕ} (hr : r.Prime) (z : ℕ) :
    Fsum g z = Bsum g r z + g r * Bsum g r (z / r) := by
  unfold Fsum Bsum
  rw [← Finset.sum_filter_add_sum_filter_not ((Icc 1 z).filter Squarefree) (fun q => ¬ r ∣ q),
    Finset.filter_filter]
  congr 1
  rw [Finset.filter_filter, Finset.mul_sum]
  symm
  apply Finset.sum_nbij' (fun q => r * q) (fun q => q / r)
  · intro q hq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hq ⊢
    obtain ⟨⟨h1, h2⟩, hsq, hnd⟩ := hq
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · have := hr.one_lt; nlinarith
    · calc r * q ≤ r * (z / r) := Nat.mul_le_mul_left r h2
        _ ≤ z := Nat.mul_div_le z r
    · rw [Nat.squarefree_mul_iff]
      exact ⟨(Nat.Prime.coprime_iff_not_dvd hr).mpr hnd, hr.squarefree, hsq⟩
    · simp
  · intro q hq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc, not_not] at hq ⊢
    obtain ⟨⟨h1, h2⟩, hsq, hd⟩ := hq
    obtain ⟨t, rfl⟩ := hd
    have hr0 := hr.pos
    rw [Nat.mul_div_cancel_left t hr0]
    rw [Nat.squarefree_mul_iff] at hsq
    refine ⟨⟨?_, ?_⟩, hsq.2.2, ?_⟩
    · rcases Nat.eq_zero_or_pos t with h | h
      · subst h; simp at h1
      · exact h
    · exact (Nat.le_div_iff_mul_le hr0).mpr (by linarith)
    · exact (Nat.Prime.coprime_iff_not_dvd hr).mp hsq.1
  · intro q _
    exact Nat.mul_div_cancel_left q hr.pos
  · intro q hq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc, not_not] at hq
    exact Nat.mul_div_cancel' hq.2.2
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_Icc] at hq
    obtain ⟨⟨h1, h2⟩, hsq, hnd⟩ := hq
    have hq0 : q ≠ 0 := by omega
    rw [Nat.primeFactors_mul hr.ne_zero hq0, hr.primeFactors]
    rw [Finset.prod_union]
    · rw [Finset.prod_singleton]
    · rw [Finset.disjoint_singleton_left]
      intro hm
      exact hnd (Nat.dvd_of_mem_primeFactors hm)

theorem Bsum_mono (g : ℕ → ℝ) (hg : ∀ p, 0 ≤ g p) (r : ℕ) {z z' : ℕ} (h : z ≤ z') :
    Bsum g r z ≤ Bsum g r z' := by
  unfold Bsum
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_Icc] at hq ⊢
    exact ⟨⟨hq.1.1, hq.1.2.trans h⟩, hq.2⟩
  · intro q _ _
    exact Finset.prod_nonneg (fun p _ => hg p)

theorem Bsum_nonneg (g : ℕ → ℝ) (hg : ∀ p, 0 ≤ g p) (r z : ℕ) : 0 ≤ Bsum g r z :=
  Finset.sum_nonneg (fun _ _ => Finset.prod_nonneg (fun p _ => hg p))

theorem Bsum_congr (g g' : ℕ → ℝ) (r z : ℕ) (h : ∀ p, p ≠ r → g p = g' p) :
    Bsum g r z = Bsum g' r z := by
  unfold Bsum
  apply Finset.sum_congr rfl
  intro q hq
  simp only [Finset.mem_filter] at hq
  apply Finset.prod_congr rfl
  intro p hp
  apply h
  rintro rfl
  exact hq.2.2 (Nat.dvd_of_mem_primeFactors hp)

open Classical in
/-- weights: `1 + 2/ℓ` on `S`, `1/ℓ` elsewhere. -/
noncomputable def gS (S : Finset ℕ) (l : ℕ) : ℝ := if l ∈ S then 1 + 2 / l else 1 / l

theorem gS_nonneg (S : Finset ℕ) (l : ℕ) : 0 ≤ gS S l := by
  unfold gS; split_ifs <;> positivity

theorem peel (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (z : ℕ) :
    2 ^ S.card * Fsum (gS ∅) (z / ∏ p ∈ S, p) ≤ Fsum (gS S) z := by
  induction S using Finset.induction_on generalizing z with
  | empty => simp
  | insert r S hrS ih =>
    have hr : r.Prime := hS r (Finset.mem_insert_self r S)
    have hS' : ∀ p ∈ S, p.Prime := fun p hp => hS p (Finset.mem_insert_of_mem hp)
    have ih' := ih hS' (z / r)
    rw [Nat.div_div_eq_div_mul] at ih'
    rw [Finset.prod_insert hrS]
    rw [Finset.card_insert_of_notMem hrS, pow_succ]
    have hB : ∀ w, Bsum (gS (insert r S)) r w = Bsum (gS S) r w := by
      intro w
      apply Bsum_congr
      intro p hp
      unfold gS
      simp [Finset.mem_insert, hp]
    have hg1 : gS (insert r S) r = 1 + 2 / r := by unfold gS; simp
    have hg2 : gS S r = 1 / r := by unfold gS; simp [hrS]
    have h1 := Fsum_split (gS (insert r S)) hr z
    have h2 := Fsum_split (gS S) hr (z / r)
    rw [hB, hB, hg1] at h1
    rw [hg2] at h2
    have hm1 : Bsum (gS S) r (z / r) ≤ Bsum (gS S) r z :=
      Bsum_mono _ (gS_nonneg S) r (Nat.div_le_self z r)
    have hm2 : Bsum (gS S) r (z / r / r) ≤ Bsum (gS S) r (z / r) :=
      Bsum_mono _ (gS_nonneg S) r (Nat.div_le_self _ r)
    have hb0 := Bsum_nonneg _ (gS_nonneg S) r (z / r / r)
    have hrpos : (0 : ℝ) < r := by exact_mod_cast hr.pos
    have hkey : 2 * Fsum (gS S) (z / r) ≤ Fsum (gS (insert r S)) z := by
      rw [h1, h2]
      have : 2 / (r : ℝ) * Bsum (gS S) r (z / r / r) ≤ 2 / (r : ℝ) * Bsum (gS S) r (z / r) :=
        mul_le_mul_of_nonneg_left hm2 (by positivity)
      have e1 : 2 * (Bsum (gS S) r (z / r) + 1 / (r : ℝ) * Bsum (gS S) r (z / r / r)) =
          2 * Bsum (gS S) r (z / r) + 2 / (r : ℝ) * Bsum (gS S) r (z / r / r) := by ring
      have e2 : (1 + 2 / (r : ℝ)) * Bsum (gS S) r (z / r) =
          Bsum (gS S) r (z / r) + 2 / (r : ℝ) * Bsum (gS S) r (z / r) := by ring
      rw [e1, e2]
      linarith
    calc 2 ^ S.card * 2 * Fsum (gS ∅) (z / (r * ∏ p ∈ S, p))
        = 2 * (2 ^ S.card * Fsum (gS ∅) (z / (r * ∏ p ∈ S, p))) := by ring
      _ ≤ 2 * Fsum (gS S) (z / r) := by linarith
      _ ≤ _ := hkey

theorem Fsum_empty (z : ℕ) : Fsum (gS ∅) z = ∑ q ∈ (Icc 1 z).filter Squarefree, (1 / (q : ℝ)) := by
  unfold Fsum
  apply Finset.sum_congr rfl
  intro q hq
  simp only [Finset.mem_filter] at hq
  have : ∏ p ∈ q.primeFactors, gS ∅ p = ∏ p ∈ q.primeFactors, (1 / (p : ℝ)) := by
    apply Finset.prod_congr rfl; intro p _; unfold gS; simp
  rw [this, Finset.prod_div_distrib, Finset.prod_const_one]
  congr 1
  rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hq.2]

theorem harmonic_le_Fsum (z : ℕ) :
    ∑ n ∈ Icc 1 z, (1 / (n : ℝ)) ≤ 2 * Fsum (gS ∅) z := by
  rw [Fsum_empty]
  set T := ((Icc 1 z).filter Squarefree) ×ˢ (Icc 1 z) with hT
  set μ : ℕ × ℕ → ℕ := fun t => t.2 ^ 2 * t.1 with hμ
  have hsurj : ∀ n ∈ Icc 1 z, ∃ t ∈ T, μ t = n := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    obtain ⟨a, b, hab, hsq⟩ := Nat.sq_mul_squarefree n
    have ha : 1 ≤ a := by
      rcases Nat.eq_zero_or_pos a with h | h
      · subst h; simp at hab; omega
      · exact h
    have hb : 1 ≤ b := by
      rcases Nat.eq_zero_or_pos b with h | h
      · subst h; simp at hab; omega
      · exact h
    have hb2 : 1 ≤ b ^ 2 := Nat.one_le_pow _ _ hb
    refine ⟨(a, b), ?_, hab⟩
    simp only [hT, Finset.mem_product, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨⟨ha, ?_⟩, hsq⟩, hb, ?_⟩
    · calc a = 1 * a := (one_mul a).symm
        _ ≤ b ^ 2 * a := Nat.mul_le_mul_right a hb2
        _ = n := hab
        _ ≤ z := hn.2
    · calc b ≤ b ^ 2 := by nlinarith
        _ = b ^ 2 * 1 := (mul_one _).symm
        _ ≤ b ^ 2 * a := Nat.mul_le_mul_left _ ha
        _ = n := hab
        _ ≤ z := hn.2
  have step1 : ∑ n ∈ Icc 1 z, (1 / (n : ℝ)) ≤
      ∑ n ∈ Icc 1 z, ∑ t ∈ T.filter (fun t => μ t = n), (1 / (μ t : ℝ)) := by
    apply Finset.sum_le_sum
    intro n hn
    obtain ⟨t, ht, hμt⟩ := hsurj n hn
    have hmem : t ∈ T.filter (fun t => μ t = n) := Finset.mem_filter.mpr ⟨ht, hμt⟩
    calc (1 / (n : ℝ)) = 1 / (μ t : ℝ) := by rw [hμt]
      _ ≤ _ := Finset.single_le_sum (f := fun t => (1 / (μ t : ℝ))) (fun _ _ => by positivity) hmem
  have step2 : ∑ n ∈ Icc 1 z, ∑ t ∈ T.filter (fun t => μ t = n), (1 / (μ t : ℝ)) ≤
      ∑ t ∈ T, (1 / (μ t : ℝ)) := by
    have hf := Finset.sum_fiberwise_of_maps_to (s := T.filter (fun t => μ t ∈ Icc 1 z))
      (t := Icc 1 z) (g := μ) (fun t ht => (Finset.mem_filter.mp ht).2) (fun t => (1 / (μ t : ℝ)))
    calc _ = ∑ n ∈ Icc 1 z, ∑ t ∈ (T.filter (fun t => μ t ∈ Icc 1 z)).filter (fun t => μ t = n),
          (1 / (μ t : ℝ)) := by
          apply Finset.sum_congr rfl
          intro n hn
          apply Finset.sum_congr
          · ext t; simp only [Finset.mem_filter]
            constructor
            · rintro ⟨h1, h2⟩; exact ⟨⟨h1, by rw [h2]; exact hn⟩, h2⟩
            · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
          · intro _ _; rfl
      _ = _ := hf
      _ ≤ _ := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro _ _ _; positivity
  have step3 : ∑ t ∈ T, (1 / (μ t : ℝ)) =
      (∑ a ∈ (Icc 1 z).filter Squarefree, (1 / (a : ℝ))) * ∑ b ∈ Icc 1 z, (1 / ((b : ℝ) ^ 2)) := by
    rw [hT, Finset.sum_product, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    simp only [hμ]; push_cast
    rw [one_div_mul_one_div, mul_comm]
  have step4 : ∑ b ∈ Icc 1 z, (1 / ((b : ℝ) ^ 2)) ≤ 2 := by
    have := sum_Ioo_inv_sq_le (α := ℝ) 0 (z + 1)
    have hsub : Icc 1 z = Ioo 0 (z + 1) := by ext b; simp; omega
    rw [hsub]
    simp only [one_div]
    simpa using this
  have hpos : 0 ≤ ∑ a ∈ (Icc 1 z).filter Squarefree, (1 / (a : ℝ)) :=
    Finset.sum_nonneg (fun _ _ => by positivity)
  calc _ ≤ _ := step1
    _ ≤ _ := step2
    _ = _ := step3
    _ ≤ (∑ a ∈ (Icc 1 z).filter Squarefree, (1 / (a : ℝ))) * 2 :=
        mul_le_mul_of_nonneg_left step4 hpos
    _ = _ := by ring

theorem log_le_Fsum (z : ℕ) : Real.log (z + 1) ≤ 2 * Fsum (gS ∅) z := by
  refine le_trans ?_ (harmonic_le_Fsum z)
  have := log_add_one_le_harmonic z
  rw [harmonic_eq_sum_Icc] at this
  push_cast at this
  simpa [one_div] using this

end OMA980

namespace OMA980

open Filter Topology Finset

/-- number of odd primes `p < x` with `n(p) > m`. -/
noncomputable def E (x : ℝ) (m : ℕ) : ℕ :=
  ((Nat.primesBelow ⌈x⌉₊).filter (fun p => p % 2 = 1 ∧ m < nr p)).card

/-- primes `ℓ ≤ m`, `ℓ ≡ 1 mod 4`. -/
def Rset (m : ℕ) : Finset ℕ := (Nat.primesBelow (m + 1)).filter (fun p => p % 4 = 1)

/-- `π(m; 4, 1)`. -/
def R (m : ℕ) : ℕ := (Rset m).card

open Classical in
theorem nonres_card (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) :
    p - 1 ≤ 2 * (OMALargeSieve.nonres p).card ∧ (OMALargeSieve.nonres p).card + 2 ≤ p ∧
      0 ∉ OMALargeSieve.nonres p := by
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two (by omega))
  have h0 : 0 ∉ OMALargeSieve.nonres p := by
    unfold OMALargeSieve.nonres
    simp only [Finset.mem_filter, not_and, not_not]
    intro _; exact ⟨0, by simp⟩
  have h1 : 1 ∉ OMALargeSieve.nonres p := by
    unfold OMALargeSieve.nonres
    simp only [Finset.mem_filter, not_and, not_not]
    intro _; exact ⟨1, by simp⟩
  refine ⟨?_, ?_, h0⟩
  · have hsplit := Finset.card_filter_add_card_filter_not
      (s := range p) (fun b : ℕ => ¬ IsSquare (b : ZMod p))
    rw [Finset.card_range] at hsplit
    have hnr : (OMALargeSieve.nonres p).card =
        ((range p).filter (fun b : ℕ => ¬ IsSquare (b : ZMod p))).card := by
      unfold OMALargeSieve.nonres; congr 1
    have hsub : (range p).filter (fun b : ℕ => ¬ ¬ IsSquare (b : ZMod p)) ⊆
        insert 0 ((range p).filter (fun b : ℕ => b ≠ 0 ∧ IsSquare (b : ZMod p))) := by
      intro b hb
      simp only [Finset.mem_filter, Finset.mem_range, not_not] at hb
      rw [Finset.mem_insert, Finset.mem_filter, Finset.mem_range]
      by_cases hb0 : b = 0
      · exact Or.inl hb0
      · exact Or.inr ⟨hb.1, hb0, hb.2⟩
    have hc := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
    have := OMALargeSieve.card_nonzero_sq_le p hp
    omega
  · have hsub : OMALargeSieve.nonres p ⊆ ((range p).erase 0).erase 1 := by
      intro b hb
      have hb' := OMALargeSieve.nonres_subset p hb
      rw [Finset.mem_erase, Finset.mem_erase]
      refine ⟨?_, ?_, hb'⟩
      · rintro rfl; exact h1 hb
      · rintro rfl; exact h0 hb
    have := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem, Finset.card_erase_of_mem, Finset.card_range] at this
    · omega
    · simp; omega
    · simp; omega

open Classical in
/-- sieving classes: `{0} ∪ nonresidues` at `ℓ ∈ Rset m`, `{0}` elsewhere. -/
noncomputable def Om (m : ℕ) (l : ℕ) : Finset ℕ :=
  if l ∈ Rset m then insert 0 (OMALargeSieve.nonres l) else {0}

theorem Om_sub (m l : ℕ) (hl : l.Prime) : Om m l ⊆ range l := by
  unfold Om
  split_ifs
  · intro b hb
    rw [Finset.mem_insert] at hb
    rcases hb with rfl | hb
    · simp [hl.pos]
    · exact OMALargeSieve.nonres_subset l hb
  · intro b hb; rw [Finset.mem_singleton] at hb; subst hb; simp [hl.pos]

theorem gS_le_hfac (m l : ℕ) (hl : l.Prime) : gS (Rset m) l ≤ OMALargeSieve.hfac (Om m) l := by
  unfold gS OMALargeSieve.hfac Om
  have hl2 := hl.two_le
  have hlpos : (0 : ℝ) < l := by exact_mod_cast hl.pos
  split_ifs with h
  · have h4 : l % 4 = 1 := (Finset.mem_filter.mp h).2
    have hl3 : 3 ≤ l := by omega
    obtain ⟨c1, c2, c0⟩ := nonres_card l hl hl3
    rw [Finset.card_insert_of_notMem c0]
    set w := (OMALargeSieve.nonres l).card
    have hw1 : (l : ℝ) - 1 ≤ 2 * w := by
      have : l - 1 ≤ 2 * w := c1
      have h' : ((l - 1 : ℕ) : ℝ) ≤ 2 * w := by exact_mod_cast this
      rw [Nat.cast_sub (by omega)] at h'; simpa using h'
    have hw2 : (w : ℝ) + 2 ≤ l := by exact_mod_cast c2
    push_cast
    have hden : 0 < (l : ℝ) - (w + 1) := by linarith
    rw [le_div_iff₀ hden]
    have hq : 1 ≤ 2 * ((w : ℝ) + 1) / l := by
      rw [le_div_iff₀ hlpos]; linarith
    have e : (1 + 2 / (l : ℝ)) * ((l : ℝ) - (w + 1)) = (l : ℝ) - (w + 1) + 2 - 2 * (w + 1) / l := by
      field_simp
      ring
    rw [e]
    linarith
  · rw [Finset.card_singleton]
    push_cast
    have hden : 0 < (l : ℝ) - 1 := by
      have : (2 : ℝ) ≤ l := by exact_mod_cast hl2
      linarith
    exact one_div_le_one_div_of_le hden (by linarith)

theorem sq_of_lt_nr {n l : ℕ} (hn : n.Prime) (hn3 : 3 ≤ n) (hl : l.Prime) (hl4 : l % 4 = 1)
    (hln : l < n) (hlnr : l < nr n) : IsSquare (n : ZMod l) := by
  have := Fact.mk hn
  have := Fact.mk hl
  obtain ⟨_, _, hmin⟩ := OMALargeSieve.lnr_spec n hn hn3
  have hq := hmin l hl.pos hlnr
  have hl0 : ((l : ℤ) : ZMod n) ≠ 0 := by
    rw [Int.cast_natCast, Ne, ZMod.natCast_eq_zero_iff]
    intro hd; have := Nat.le_of_dvd hl.pos hd; omega
  have hn0 : ((n : ℤ) : ZMod l) ≠ 0 := by
    rw [Int.cast_natCast, Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    have := (Nat.prime_dvd_prime_iff_eq hl hn).mp hd
    omega
  have h1 : legendreSym n l = 1 := by
    rw [legendreSym.eq_one_iff n hl0, Int.cast_natCast]
    obtain ⟨y, hy⟩ := hq
    exact ⟨y, by rw [← hy, sq]⟩
  rw [legendreSym.quadratic_reciprocity_one_mod_four hl4 (by omega)] at h1
  have := (legendreSym.eq_one_iff l hn0).mp h1
  rwa [Int.cast_natCast] at this

open Classical in
theorem sieve_core (N Q m : ℕ) (hQ : 2 ≤ Q) :
    (((Nat.primesBelow N).filter (fun p => Q < p ∧ m < nr p)).card : ℝ) *
      (2 ^ R m * Fsum (gS ∅) (Q / ∏ p ∈ Rset m, p)) ≤ N + 2 * (Q : ℝ) ^ 2 := by
  set A := (Nat.primesBelow N).filter (fun p => Q < p ∧ m < nr p) with hAdef
  have hA : A ⊆ Ico 0 (0 + N) := by
    intro p hp
    rw [hAdef, Finset.mem_filter, Nat.mem_primesBelow] at hp
    rw [Finset.mem_Ico]; omega
  have hAΩ : ∀ n ∈ A, ∀ p, p.Prime → p ≤ Q → n % p ∉ Om m p := by
    intro n hn l hl hlQ
    rw [hAdef, Finset.mem_filter, Nat.mem_primesBelow] at hn
    obtain ⟨⟨_, hnp⟩, hQn, hmn⟩ := hn
    have hnd : n % l ≠ 0 := by
      intro h
      have := (Nat.prime_dvd_prime_iff_eq hl hnp).mp (Nat.dvd_of_mod_eq_zero h)
      omega
    unfold Om
    split_ifs with hR
    · rw [Finset.mem_insert, not_or]
      refine ⟨hnd, ?_⟩
      unfold OMALargeSieve.nonres
      rw [Finset.mem_filter, not_and, not_not]
      intro _
      rw [ZMod.natCast_mod]
      have hR' := Finset.mem_filter.mp hR
      have hlm : l < m + 1 := (Nat.mem_primesBelow.mp hR'.1).1
      exact sq_of_lt_nr hnp (by omega) hl hR'.2 (by omega) (by omega)
    · rw [Finset.mem_singleton]; exact hnd
  have hsieve := OMALargeSieve.arith_large_sieve Q 0 N A hA (Om m)
    (fun p hp _ => Om_sub m p hp) hAΩ
  have hRp : ∀ p ∈ Rset m, p.Prime := fun p hp =>
    Nat.prime_of_mem_primesBelow (Finset.mem_filter.mp hp).1
  have hpeel := peel (Rset m) hRp Q
  have hL : Fsum (gS (Rset m)) Q ≤
      ∑ q ∈ (Icc 1 Q).filter Squarefree, ∏ p ∈ q.primeFactors, OMALargeSieve.hfac (Om m) p := by
    unfold Fsum
    apply Finset.sum_le_sum
    intro q _
    apply Finset.prod_le_prod
    · intro p _; exact gS_nonneg _ _
    · intro p hp; exact gS_le_hfac m p (Nat.prime_of_mem_primeFactors hp)
  have hA0 : (0 : ℝ) ≤ A.card := by positivity
  unfold R
  calc (A.card : ℝ) * (2 ^ (Rset m).card * Fsum (gS ∅) (Q / ∏ p ∈ Rset m, p))
      ≤ A.card * ∑ q ∈ (Icc 1 Q).filter Squarefree, ∏ p ∈ q.primeFactors,
          OMALargeSieve.hfac (Om m) p := mul_le_mul_of_nonneg_left (hpeel.trans hL) hA0
    _ ≤ _ := hsieve

theorem prod_Rset_le (m : ℕ) : ∏ p ∈ Rset m, p ≤ 4 ^ m := by
  refine le_trans ?_ (primorial_le_four_pow m)
  unfold primorial Rset
  apply Finset.prod_le_prod_of_subset_of_one_le'
  · intro p hp
    rw [Finset.mem_filter, Nat.mem_primesBelow] at hp
    rw [Finset.mem_filter, Finset.mem_range]
    exact hp.1
  · intro p hp _
    exact (Finset.mem_filter.mp hp).2.one_lt.le

theorem E_le {x : ℝ} (hx : 256 ≤ x) (m : ℕ) (hm : (4 : ℝ) ^ m ≤ x ^ ((8 : ℝ)⁻¹)) :
    (E x m : ℝ) ≤ 32 * x / (2 ^ R m * Real.log x) + Real.sqrt x + 1 := by
  have hx0 : 0 < x := by linarith
  set t := x ^ ((8 : ℝ)⁻¹) with ht
  have ht8 : t ^ 8 = x := by
    rw [ht, show (8 : ℝ)⁻¹ = ((8 : ℕ) : ℝ)⁻¹ by norm_num]
    exact Real.rpow_inv_natCast_pow hx0.le (by norm_num)
  have ht0 : 0 ≤ t := Real.rpow_nonneg hx0.le _
  have ht2 : 2 ≤ t := by
    by_contra h
    push Not at h
    have : t ^ 8 < 2 ^ 8 := pow_lt_pow_left₀ h ht0 (by norm_num)
    rw [ht8] at this; norm_num at this; linarith
  have hsq : Real.sqrt x = t ^ 4 := by
    rw [← ht8, show t ^ 8 = (t ^ 4) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hlogx : Real.log x = 8 * Real.log t := by
    rw [← ht8, Real.log_pow]; norm_num
  set N := ⌈x⌉₊ with hN
  set Q := ⌊Real.sqrt x⌋₊ with hQ
  set P := ∏ p ∈ Rset m, p with hP
  set z := Q / P with hz
  have hQle : (Q : ℝ) ≤ t ^ 4 := by rw [← hsq]; exact Nat.floor_le (Real.sqrt_nonneg x)
  have hQgt : t ^ 4 - 1 < (Q : ℝ) := by
    rw [← hsq]; have := Nat.lt_floor_add_one (Real.sqrt x); linarith
  have hQ2 : 2 ≤ Q := by
    have : (16 : ℝ) ≤ t ^ 4 := by nlinarith [pow_le_pow_left₀ (by norm_num) ht2 4]
    have : (2 : ℝ) < Q + 1 := by linarith
    have : (1 : ℝ) < Q := by linarith
    have : 1 < Q := by exact_mod_cast this
    omega
  have hPpos : 0 < P := Finset.prod_pos (fun p hp =>
    (Nat.prime_of_mem_primesBelow (Finset.mem_filter.mp hp).1).pos)
  have hPt : (P : ℝ) ≤ t := by
    have := prod_Rset_le m
    have h' : (P : ℝ) ≤ (4 : ℝ) ^ m := by exact_mod_cast this
    linarith
  have hzP : Q < (z + 1) * P := by
    have := Nat.lt_div_mul_add (a := Q) hPpos
    rw [hz]; nlinarith
  have hzP' : (Q : ℝ) < ((z : ℝ) + 1) * P := by exact_mod_cast hzP
  have hz1 : t ^ 2 ≤ (z : ℝ) + 1 := by
    by_contra h
    push Not at h
    have hz0 : (0 : ℝ) ≤ z := by positivity
    have h1 : ((z : ℝ) + 1) * P ≤ ((z : ℝ) + 1) * t := mul_le_mul_of_nonneg_left hPt (by positivity)
    have h2 : ((z : ℝ) + 1) * t ≤ t ^ 2 * t := mul_le_mul_of_nonneg_right h.le ht0
    have h3 : t ^ 4 - 1 < t ^ 3 := by nlinarith
    nlinarith [pow_le_pow_left₀ (by norm_num) ht2 3]
  have hlogz : Real.log x / 4 ≤ Real.log ((z : ℝ) + 1) := by
    have := Real.log_le_log (by positivity) hz1
    rw [Real.log_pow] at this
    rw [hlogx]; push_cast at this; linarith
  have hF : Real.log x / 8 ≤ Fsum (gS ∅) z := by
    have := log_le_Fsum z
    push_cast at this
    linarith
  have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hcore := sieve_core N Q m hQ2
  rw [← hP, ← hz] at hcore
  set A := (Nat.primesBelow N).filter (fun p => Q < p ∧ m < nr p) with hA
  have hNx : (N : ℝ) ≤ x + 1 := (Nat.ceil_lt_add_one hx0.le).le
  have hQ2x : 2 * (Q : ℝ) ^ 2 ≤ 2 * x := by
    have : (Q : ℝ) ^ 2 ≤ (t ^ 4) ^ 2 := pow_le_pow_left₀ (by positivity) hQle 2
    rw [← hsq, Real.sq_sqrt hx0.le] at this; linarith
  have h2R : (0 : ℝ) < 2 ^ R m := by positivity
  have hAle : (A.card : ℝ) ≤ 32 * x / (2 ^ R m * Real.log x) := by
    rw [le_div_iff₀ (by positivity)]
    have hA0 : (0 : ℝ) ≤ A.card := by positivity
    have : (A.card : ℝ) * (2 ^ R m * (Real.log x / 8)) ≤ 4 * x := by
      calc (A.card : ℝ) * (2 ^ R m * (Real.log x / 8)) ≤ A.card * (2 ^ R m * Fsum (gS ∅) z) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hF h2R.le) hA0
        _ ≤ N + 2 * (Q : ℝ) ^ 2 := hcore
        _ ≤ 4 * x := by linarith
    nlinarith
  have hsub : (Nat.primesBelow N).filter (fun p => p % 2 = 1 ∧ m < nr p) ⊆ A ∪ range (Q + 1) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    rw [Finset.mem_union, Finset.mem_range, hA, Finset.mem_filter]
    by_cases hpQ : p < Q + 1
    · exact Or.inr hpQ
    · exact Or.inl ⟨hp.1, by omega, hp.2.2⟩
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  rw [Finset.card_range] at hc
  have hc' : (E x m : ℝ) ≤ A.card + (Q + 1) := by
    unfold E; rw [← hN]; exact_mod_cast hc
  rw [hsq]
  linarith

end OMA980

namespace OMA980

open Filter Topology Finset

theorem pi_lower : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ ((31 : ℝ) / 32) ≤ (Nat.primesBelow (n + 1)).card := by
  have h1 := OMAPNT.tendsto_primeCounting_nat
  have h2 : ∀ᶠ n : ℕ in atTop, (1 / 2 : ℝ) ≤ (Nat.primeCounting n : ℝ) / ((n : ℝ) / Real.log n) :=
    h1.eventually (eventually_ge_nhds (by norm_num))
  have h3 := (isLittleO_log_rpow_atTop (r := (1 : ℝ) / 32) (by norm_num)).bound
    (c := 1 / 2) (by norm_num)
  have h3' : ∀ᶠ n : ℕ in atTop, ‖Real.log n‖ ≤ 1 / 2 * ‖(n : ℝ) ^ ((1 : ℝ) / 32)‖ :=
    tendsto_natCast_atTop_atTop.eventually h3
  filter_upwards [h2, h3', eventually_ge_atTop 3] with n hn hl hn3
  have hnr : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  have hlog : 0 < Real.log n := Real.log_pos (by linarith)
  have hcard : (Nat.primesBelow (n + 1)).card = Nat.primeCounting n := by
    rw [Nat.primesBelow_card_eq_primeCounting']; rfl
  rw [hcard]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hlog,
    abs_of_nonneg (Real.rpow_nonneg (by linarith) _)] at hl
  rw [le_div_iff₀ (by positivity)] at hn
  have hsplit : (n : ℝ) = (n : ℝ) ^ ((31 : ℝ) / 32) * (n : ℝ) ^ ((1 : ℝ) / 32) := by
    rw [← Real.rpow_add (by linarith)]; norm_num
  have hp : 0 ≤ (n : ℝ) ^ ((31 : ℝ) / 32) := Real.rpow_nonneg (by linarith) _
  have : (n : ℝ) ^ ((31 : ℝ) / 32) * Real.log n ≤ (n : ℝ) / 2 := by
    calc (n : ℝ) ^ ((31 : ℝ) / 32) * Real.log n
        ≤ (n : ℝ) ^ ((31 : ℝ) / 32) * (1 / 2 * (n : ℝ) ^ ((1 : ℝ) / 32)) :=
          mul_le_mul_of_nonneg_left hl hp
      _ = ((n : ℝ) ^ ((31 : ℝ) / 32) * (n : ℝ) ^ ((1 : ℝ) / 32)) / 2 := by ring
      _ = (n : ℝ) / 2 := by rw [← hsplit]
  have h4 : (n : ℝ) / 2 = 1 / 2 * ((n : ℝ) / Real.log n) * Real.log n := by field_simp
  rw [h4] at this
  have := le_of_mul_le_mul_right this hlog
  linarith

open Classical in
theorem linnik_step (N t : ℕ) (ht : 3 ≤ t) (hN : 1 ≤ N)
    (hpi : (t : ℝ) ^ 31 ≤ (Nat.primesBelow (t ^ 32 + 1)).card)
    (hk : 2 * Nat.log (t ^ 32) (N ^ 2) ≤ t ^ 3) :
    ((((Icc 1 N).filter (fun p => p.Prime ∧ 3 ≤ p ∧
        ∀ m : ℕ, 0 < m → m ≤ t ^ 32 → ∃ x : ZMod p, x ^ 2 = (m : ZMod p))).card : ℝ)) ^ 8 ≤
      6 ^ 8 * (N : ℝ) ^ 2 * (t : ℝ) ^ 224 := by
  set y := t ^ 32 with hy
  set k := Nat.log y (N ^ 2) with hkdef
  set Ep := (Icc 1 N).filter (fun p => p.Prime ∧ 3 ≤ p ∧
        ∀ m : ℕ, 0 < m → m ≤ y → ∃ x : ZMod p, x ^ 2 = (m : ZMod p)) with hEp
  set π0 := (Nat.primesBelow (y + 1)).card with hπ
  have h1 := OMALargeSieve.linnik_explicit N y k
  have hy1 : 1 < y := by
    rw [hy]; calc 1 < 3 ^ 32 := by norm_num
      _ ≤ t ^ 32 := Nat.pow_le_pow_left ht 32
  have hyk : y ^ k ≤ N ^ 2 := Nat.pow_log_le_self y (by positivity)
  have hyk1 : N ^ 2 < y ^ (k + 1) := Nat.lt_pow_succ_log_self hy1 _
  have hπn : t ^ 31 ≤ π0 := by exact_mod_cast hpi
  have hkt : k * t ^ 28 + k ≤ π0 := by
    have : 2 * k * t ^ 28 ≤ t ^ 3 * t ^ 28 := Nat.mul_le_mul_right _ hk
    have h28 : 1 ≤ t ^ 28 := Nat.one_le_pow _ _ (by omega)
    have : t ^ 3 * t ^ 28 = t ^ 31 := by ring
    nlinarith
  have hbase : k * t ^ 28 ≤ π0 + 1 - k := by omega
  have hnat : t ^ (28 * k) * k.factorial ≤ (π0 + 1 - k) ^ k := by
    calc t ^ (28 * k) * k.factorial ≤ t ^ (28 * k) * k ^ k :=
          Nat.mul_le_mul_left _ (Nat.factorial_le_pow k)
      _ = (k * t ^ 28) ^ k := by rw [mul_pow, ← pow_mul]; ring
      _ ≤ (π0 + 1 - k) ^ k := Nat.pow_le_pow_left hbase k
  have hratio : (t : ℝ) ^ (28 * k) ≤ (((π0 + 1 - k : ℕ) : ℝ) ^ k / (k.factorial : ℝ)) := by
    rw [le_div_iff₀ (by exact_mod_cast Nat.factorial_pos k)]
    exact_mod_cast hnat
  have hE0 : (0 : ℝ) ≤ Ep.card := by positivity
  have h2 : (Ep.card : ℝ) * (t : ℝ) ^ (28 * k) ≤ 6 * (N : ℝ) ^ 2 := by
    calc (Ep.card : ℝ) * (t : ℝ) ^ (28 * k)
        ≤ Ep.card * (((π0 + 1 - k : ℕ) : ℝ) ^ k / (k.factorial : ℝ)) :=
          mul_le_mul_of_nonneg_left hratio hE0
      _ ≤ 2 * ((y ^ k : ℕ) + 2 * (N : ℝ) ^ 2) := h1
      _ ≤ 6 * (N : ℝ) ^ 2 := by
          have : ((y ^ k : ℕ) : ℝ) ≤ (N : ℝ) ^ 2 := by exact_mod_cast hyk
          linarith
  have h3 : ((N : ℝ) ^ 2) ^ 7 < (t : ℝ) ^ (224 * k) * (t : ℝ) ^ 224 := by
    have : ((N ^ 2 : ℕ) : ℝ) < ((y ^ (k + 1) : ℕ) : ℝ) := by exact_mod_cast hyk1
    push_cast at this
    rw [hy] at this
    push_cast at this
    have h7 := pow_lt_pow_left₀ this (by positivity) (by norm_num : (7 : ℕ) ≠ 0)
    calc ((N : ℝ) ^ 2) ^ 7 < (((t : ℝ) ^ 32) ^ (k + 1)) ^ 7 := h7
      _ = (t : ℝ) ^ (224 * k) * (t : ℝ) ^ 224 := by rw [← pow_mul, ← pow_mul, ← pow_add]; ring_nf
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have h4 : ((Ep.card : ℝ) * (t : ℝ) ^ (28 * k)) ^ 8 ≤ (6 * (N : ℝ) ^ 2) ^ 8 :=
    pow_le_pow_left₀ (by positivity) h2 8
  have h5 : (Ep.card : ℝ) ^ 8 * ((N : ℝ) ^ 2) ^ 7 ≤ (6 ^ 8 * (N : ℝ) ^ 2 * (t : ℝ) ^ 224) *
      ((N : ℝ) ^ 2) ^ 7 := by
    have e1 : ((Ep.card : ℝ) * (t : ℝ) ^ (28 * k)) ^ 8 = (Ep.card : ℝ) ^ 8 * (t : ℝ) ^ (224 * k) := by
      rw [mul_pow, ← pow_mul]; ring_nf
    rw [e1] at h4
    have hE8 : (0 : ℝ) ≤ (Ep.card : ℝ) ^ 8 := by positivity
    calc (Ep.card : ℝ) ^ 8 * ((N : ℝ) ^ 2) ^ 7
        ≤ (Ep.card : ℝ) ^ 8 * ((t : ℝ) ^ (224 * k) * (t : ℝ) ^ 224) :=
          mul_le_mul_of_nonneg_left h3.le hE8
      _ = ((Ep.card : ℝ) ^ 8 * (t : ℝ) ^ (224 * k)) * (t : ℝ) ^ 224 := by ring
      _ ≤ (6 * (N : ℝ) ^ 2) ^ 8 * (t : ℝ) ^ 224 :=
          mul_le_mul_of_nonneg_right h4 (by positivity)
      _ = _ := by ring
  exact le_of_mul_le_mul_right h5 (by positivity)

theorem nr_le_sqrt {p : ℕ} (hp : p.Prime) (h2 : p % 2 = 1) : (nr p : ℝ) ≤ Real.sqrt p + 1 := by
  have h3 : 3 ≤ p := by have := hp.two_le; omega
  obtain ⟨hn2, _, hlt⟩ := OMALargeSieve.lnr_bounds p hp h3
  have hnr : nr p = OMALargeSieve.lnr p := rfl
  rw [hnr]
  set n := OMALargeSieve.lnr p
  have h1 : (n - 1) * (n - 1) < p := lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.sub_le n 1)) hlt
  have h1' : ((n - 1 : ℕ) : ℝ) ^ 2 < p := by rw [sq]; exact_mod_cast h1
  have h2' : ((n - 1 : ℕ) : ℝ) < Real.sqrt p := Real.lt_sqrt_of_sq_lt h1'
  rw [Nat.cast_sub (by omega)] at h2'
  push_cast at h2'
  linarith

end OMA980

namespace OMA980

open Filter Topology Finset

theorem R_eq (m : ℕ) : (R m : ℝ) = piAP 4 1 ((m : ℝ) + 1) := by
  unfold R Rset piAP
  have : ⌈((m : ℝ) + 1)⌉₊ = m + 1 := by exact_mod_cast Nat.ceil_natCast (m + 1)
  rw [this]

theorem R_growth : ∃ m0 : ℕ, ∀ m ≥ m0, ((m : ℝ) + 1) ^ 34 ≤ 2 ^ R m := by
  have h1 := tendsto_piAP (q := 4) (r := 1) (by norm_num) (by norm_num) (by norm_num)
  have ht : ((Nat.totient 4 : ℕ) : ℝ)⁻¹ = 1 / 2 := by
    rw [show Nat.totient 4 = 2 by decide]; norm_num
  rw [ht] at h1
  have h2 : ∀ᶠ x : ℝ in atTop, (1 / 3 : ℝ) ≤ (piAP 4 1 x : ℝ) / (x / Real.log x) :=
    h1.eventually (eventually_ge_nhds (by norm_num))
  have h3 := (isLittleO_log_rpow_rpow_atTop 2 (by norm_num : (0 : ℝ) < 1)).bound
    (c := Real.log 2 / 102) (by positivity)
  obtain ⟨X, hX⟩ := eventually_atTop.mp (h2.and (h3.and (eventually_gt_atTop 1)))
  refine ⟨⌈X⌉₊, fun m hm => ?_⟩
  have hmX : X ≤ (m : ℝ) + 1 := by
    have := (Nat.ceil_le).mp hm; linarith
  obtain ⟨hA, hB, hC⟩ := hX _ hmX
  set u : ℝ := (m : ℝ) + 1 with hu
  have hlog : 0 < Real.log u := Real.log_pos hC
  have hu0 : 0 < u := by linarith
  rw [le_div_iff₀ (by positivity), ← R_eq] at hA
  rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.rpow_one, abs_of_pos hu0,
    abs_of_nonneg (Real.rpow_nonneg hlog.le _)] at hB
  rw [show (Real.log u) ^ (2 : ℝ) = Real.log u ^ (2 : ℕ) by norm_cast] at hB
  -- 34 log u ≤ R log 2
  have hkey : 34 * Real.log u ≤ (R m : ℝ) * Real.log 2 := by
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have e1 : 1 / 3 * (u / Real.log u) * Real.log 2 ≤ (R m : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_right hA hl2.le
    have e2 : 34 * Real.log u ≤ 1 / 3 * (u / Real.log u) * Real.log 2 := by
      rw [show 1 / 3 * (u / Real.log u) * Real.log 2 = u * Real.log 2 / (3 * Real.log u) by
        field_simp]
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    linarith
  have hlhs : Real.log (u ^ 34) = 34 * Real.log u := by rw [Real.log_pow]; norm_num
  have hrhs : Real.log ((2 : ℝ) ^ R m) = (R m : ℝ) * Real.log 2 := by rw [Real.log_pow]
  rw [← Real.log_le_log_iff (by positivity) (by positivity), hlhs, hrhs]
  exact hkey

theorem nth_prime_le_sq : ∀ᶠ i : ℕ in atTop, (Nat.nth Nat.Prime i : ℝ) ≤ ((i : ℝ) + 1) ^ 2 := by
  have hmono := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  have h := hmono.tendsto_atTop.eventually (pi_lower.and (eventually_ge_atTop 1))
  filter_upwards [h] with i ⟨hi, hi1⟩
  set p := Nat.nth Nat.Prime i
  have hcount : (Nat.primesBelow (p + 1)).card = i + 1 := by
    rw [Nat.primesBelow_succ, if_pos (Nat.prime_nth_prime i),
      Finset.card_insert_of_notMem (Nat.notMem_primesBelow _),
      Nat.primesBelow_card_eq_primeCounting', Nat.primeCounting'_nth_eq]
  rw [hcount] at hi
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hi1
  have hsq : Real.sqrt p ≤ (p : ℝ) ^ ((31 : ℝ) / 32) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hp1 (by norm_num)
  have : Real.sqrt p ≤ (i : ℝ) + 1 := by push_cast at hi; linarith
  rw [Real.sqrt_le_left (by positivity)] at this
  exact this

theorem summable_c : Summable (fun i : ℕ => (Nat.nth Nat.Prime i : ℝ) / 2 ^ (i + 1)) := by
  have hg : Summable (fun i : ℕ => 4 * ((i : ℝ) ^ 2 * (1 / 2 : ℝ) ^ i)) :=
    (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2 (r := 1 / 2)
      (by rw [Real.norm_eq_abs, abs_of_pos (by norm_num)]; norm_num)).mul_left 4
  refine Summable.of_norm_bounded_eventually hg ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [nth_prime_le_sq, eventually_ge_atTop 1] with i hi hi1
  have hi1' : (1 : ℝ) ≤ i := by exact_mod_cast hi1
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
  have e : 4 * ((i : ℝ) ^ 2 * (1 / 2 : ℝ) ^ i) * 2 ^ (i + 1) = 8 * (i : ℝ) ^ 2 := by
    rw [pow_succ, one_div, inv_pow]
    field_simp
    ring
  rw [e]
  nlinarith

/-- `∑ n(p)` over odd primes `p < x` with `n(p) > Y`. -/
noncomputable def tailSum (Y : ℕ) (x : ℝ) : ℝ :=
  ∑ p ∈ (Nat.primesBelow ⌈x⌉₊).filter (fun p => p % 2 = 1 ∧ Y < nr p), (nr p : ℝ)

theorem E_anti (x : ℝ) {m m' : ℕ} (h : m ≤ m') : E x m' ≤ E x m := by
  unfold E
  apply Finset.card_le_card
  intro p hp
  simp only [Finset.mem_filter] at hp ⊢
  exact ⟨hp.1, hp.2.1, by omega⟩

theorem layer (Y y2 : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    tailSum Y x ≤ Y * E x Y + ∑ m ∈ Ico Y y2, (E x m : ℝ) + (Real.sqrt x + 1) * E x y2 := by
  set T := (Nat.primesBelow ⌈x⌉₊).filter (fun p => p % 2 = 1 ∧ Y < nr p) with hT
  have hpt : ∀ p ∈ T, (nr p : ℝ) ≤ Y + ∑ m ∈ Ico Y y2, (if m < nr p then (1 : ℝ) else 0) +
      (Real.sqrt x + 1) * (if y2 < nr p then (1 : ℝ) else 0) := by
    intro p hp
    rw [hT, Finset.mem_filter, Nat.mem_primesBelow] at hp
    obtain ⟨⟨hpx, hpp⟩, hp2, hY⟩ := hp
    have hs0 : 0 ≤ ∑ m ∈ Ico Y y2, (if m < nr p then (1 : ℝ) else 0) :=
      Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)
    by_cases h : y2 < nr p
    · rw [if_pos h, mul_one]
      have h1 := nr_le_sqrt hpp hp2
      have h2 : Real.sqrt p ≤ Real.sqrt x :=
        Real.sqrt_le_sqrt ((Nat.lt_ceil.mp hpx).le)
      have : (0 : ℝ) ≤ Y := by positivity
      linarith
    · rw [if_neg h, mul_zero, add_zero]
      rw [Finset.sum_boole]
      have hset : (Ico Y y2).filter (fun m => m < nr p) = Ico Y (nr p) := by
        ext m; simp only [Finset.mem_filter, Finset.mem_Ico]; omega
      rw [hset, Nat.card_Ico]
      rw [Nat.cast_sub hY.le]
      linarith
  unfold tailSum
  rw [← hT]
  calc ∑ p ∈ T, (nr p : ℝ)
      ≤ ∑ p ∈ T, ((Y : ℝ) + ∑ m ∈ Ico Y y2, (if m < nr p then (1 : ℝ) else 0) +
          (Real.sqrt x + 1) * (if y2 < nr p then (1 : ℝ) else 0)) := Finset.sum_le_sum hpt
    _ = Y * T.card + ∑ m ∈ Ico Y y2, ((T.filter (fun p => m < nr p)).card : ℝ) +
          (Real.sqrt x + 1) * (T.filter (fun p => y2 < nr p)).card := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_comm, ← Finset.mul_sum]
        simp only [Finset.sum_const, nsmul_eq_mul, Finset.sum_boole]
        ring
    _ ≤ Y * E x Y + ∑ m ∈ Ico Y y2, (E x m : ℝ) + (Real.sqrt x + 1) * E x y2 := by
        have h1 : (T.card : ℝ) = E x Y := rfl
        have h2 : ∀ m, ((T.filter (fun p => m < nr p)).card : ℝ) ≤ E x m := by
          intro m
          have : (T.filter (fun p => m < nr p)).card ≤ E x m := by
            unfold E
            apply Finset.card_le_card
            intro p hp
            simp only [hT, Finset.mem_filter] at hp ⊢
            exact ⟨hp.1.1, hp.1.2.1, hp.2⟩
          exact_mod_cast this
        rw [h1]
        have h3 := Finset.sum_le_sum (fun m (_ : m ∈ Ico Y y2) => h2 m)
        have h4 : (Real.sqrt x + 1) * ((T.filter (fun p => y2 < nr p)).card : ℝ) ≤
            (Real.sqrt x + 1) * E x y2 :=
          mul_le_mul_of_nonneg_left (h2 y2) (by positivity)
        linarith

end OMA980

namespace OMA980

open Filter Topology Finset

theorem four_pow_le {x : ℝ} (hx : 1 ≤ x) : (4 : ℝ) ^ ⌊Real.log x / 12⌋₊ ≤ x ^ ((8 : ℝ)⁻¹) := by
  set M := ⌊Real.log x / 12⌋₊
  have hL : 0 ≤ Real.log x := Real.log_nonneg hx
  have hM : (M : ℝ) ≤ Real.log x / 12 := Nat.floor_le (by positivity)
  have hl4 : Real.log 4 ≤ 3 / 2 := by
    have := Real.log_two_lt_d9
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; linarith
  have hl40 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  rw [Real.rpow_def_of_pos (by linarith), ← Real.exp_log (by positivity : (0 : ℝ) < 4 ^ M),
    Real.log_pow]
  apply Real.exp_le_exp.mpr
  have hM0 : (0 : ℝ) ≤ M := by positivity
  nlinarith

theorem sum_inv_sq_Ico (Y y2 : ℕ) :
    ∑ m ∈ Ico Y y2, (1 / ((m : ℝ) + 1) ^ 2) ≤ 2 / ((Y : ℝ) + 1) := by
  have h := sum_Ioo_inv_sq_le (α := ℝ) Y (y2 + 1)
  have e : ∑ m ∈ Ico Y y2, (1 / ((m : ℝ) + 1) ^ 2) = ∑ i ∈ Ico (Y + 1) (y2 + 1), ((i : ℝ) ^ 2)⁻¹ := by
    rw [← Finset.sum_Ico_add' (fun i : ℕ => ((i : ℝ) ^ 2)⁻¹) Y y2 1]
    apply Finset.sum_congr rfl; intro m _; push_cast; rw [one_div]
  rw [e]
  refine le_trans ?_ h
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi; rw [Finset.mem_Ico] at hi; rw [Finset.mem_Ioo]; omega
  · intro _ _ _; positivity

theorem tendsto_log_pow_div (k : ℕ) :
    Tendsto (fun x : ℝ => Real.log x ^ k / x ^ ((4 : ℝ)⁻¹)) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop (k : ℝ) (by norm_num : (0 : ℝ) < (4 : ℝ)⁻¹)).tendsto_div_nhds_zero
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with x hx
  rw [Real.rpow_natCast]

theorem hk_bound (t N : ℕ) (x : ℝ) (ht3 : 3 ≤ t) (hx0 : 0 < x) (hN1 : 1 ≤ N)
    (hNx : (N : ℝ) ≤ 2 * x) (htL : Real.log x ≤ t) : 2 * Nat.log (t ^ 32) (N ^ 2) ≤ t ^ 3 := by
  set k := Nat.log (t ^ 32) (N ^ 2)
  have hpow : (t ^ 32) ^ k ≤ N ^ 2 := Nat.pow_log_le_self _ (by positivity)
  have h2t : 2 ≤ t ^ 32 := le_trans (by norm_num) (Nat.pow_le_pow_left ht3 32)
  have h2k : 2 ^ k ≤ N ^ 2 := le_trans (Nat.pow_le_pow_left h2t k) hpow
  have h2k' : (2 : ℝ) ^ k ≤ (N : ℝ) ^ 2 := by exact_mod_cast h2k
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hlg := Real.log_le_log (by positivity) h2k'
  rw [Real.log_pow, Real.log_pow] at hlg
  have hlN : Real.log N ≤ Real.log (2 * x) := Real.log_le_log hNpos hNx
  rw [Real.log_mul (by norm_num) hx0.ne'] at hlN
  have hl2 : (0.69 : ℝ) ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hl2' : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hkL : (k : ℝ) * 0.69 ≤ 2 * (1 + t) := by
    have : (k : ℝ) * 0.69 ≤ k * Real.log 2 := mul_le_mul_of_nonneg_left hl2 hk0
    push_cast at hlg
    linarith
  have ht3' : (3 : ℝ) ≤ t := by exact_mod_cast ht3
  have hk' : (2 * k : ℝ) ≤ (t : ℝ) ^ 3 := by
    have h9 : (9 : ℝ) * t ≤ (t : ℝ) ^ 3 := by
      have : (9 : ℝ) ≤ (t : ℝ) ^ 2 := by nlinarith
      nlinarith
    nlinarith
  exact_mod_cast hk'

open Classical in
theorem Ey2_bound (x : ℝ) (hx : 256 ≤ x) (t : ℕ) (ht3 : 3 ≤ t) (htL : Real.log x ≤ t)
    (hpi : (t : ℝ) ^ 31 ≤ (Nat.primesBelow (t ^ 32 + 1)).card) (s : ℝ) (hs8 : s ^ 8 = x)
    (hs0 : 0 ≤ s) : (E x (t ^ 32) : ℝ) ≤ 12 * s ^ 2 * (t : ℝ) ^ 28 := by
  have hx0 : 0 < x := by linarith
  set N := ⌈x⌉₊ with hN
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hNx : (N : ℝ) ≤ 2 * x := by have := Nat.ceil_lt_add_one hx0.le; linarith
  have hk := hk_bound t N x ht3 hx0 hN1 hNx htL
  have hls := linnik_step N t ht3 hN1 hpi hk
  have hsub : E x (t ^ 32) ≤ ((Icc 1 N).filter (fun p => p.Prime ∧ 3 ≤ p ∧
      ∀ m : ℕ, 0 < m → m ≤ t ^ 32 → ∃ x : ZMod p, x ^ 2 = (m : ZMod p))).card := by
    unfold E
    apply Finset.card_le_card
    intro p hp
    simp only [Finset.mem_filter, Nat.mem_primesBelow, Finset.mem_Icc] at hp ⊢
    obtain ⟨⟨hpN, hpp⟩, hp2, hy⟩ := hp
    have hp3 : 3 ≤ p := by have := hpp.two_le; omega
    obtain ⟨_, _, hmin⟩ := OMALargeSieve.lnr_spec p hpp hp3
    have hnr : nr p = OMALargeSieve.lnr p := rfl
    exact ⟨⟨hpp.pos, by omega⟩, hpp, hp3, fun m hm hmy => hmin m hm (by omega)⟩
  have hsub' : (E x (t ^ 32) : ℝ) ≤ (((Icc 1 N).filter (fun p => p.Prime ∧ 3 ≤ p ∧
      ∀ m : ℕ, 0 < m → m ≤ t ^ 32 → ∃ x : ZMod p, x ^ 2 = (m : ZMod p))).card : ℝ) := by
    exact_mod_cast hsub
  have hE0 : (0 : ℝ) ≤ E x (t ^ 32) := by positivity
  have hN2 : (N : ℝ) ^ 2 ≤ 4 * s ^ 16 := by
    have : (N : ℝ) ^ 2 ≤ (2 * x) ^ 2 := pow_le_pow_left₀ (by positivity) hNx 2
    rw [← hs8] at this; nlinarith
  have hT : (0 : ℝ) ≤ (t : ℝ) ^ 224 := by positivity
  have h8 : (E x (t ^ 32) : ℝ) ^ 8 ≤ (12 * s ^ 2 * (t : ℝ) ^ 28) ^ 8 := by
    have e : (12 * s ^ 2 * (t : ℝ) ^ 28) ^ 8 = 12 ^ 8 * s ^ 16 * (t : ℝ) ^ 224 := by ring
    rw [e]
    calc (E x (t ^ 32) : ℝ) ^ 8 ≤ _ := pow_le_pow_left₀ hE0 hsub' 8
      _ ≤ 6 ^ 8 * (N : ℝ) ^ 2 * (t : ℝ) ^ 224 := hls
      _ ≤ 6 ^ 8 * (4 * s ^ 16) * (t : ℝ) ^ 224 := by
          apply mul_le_mul_of_nonneg_right _ hT
          exact mul_le_mul_of_nonneg_left hN2 (by norm_num)
      _ ≤ 12 ^ 8 * s ^ 16 * (t : ℝ) ^ 224 := by
          apply mul_le_mul_of_nonneg_right _ hT
          have : (0 : ℝ) ≤ s ^ 16 := by positivity
          nlinarith
  exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) h8

theorem rem1 (L t M : ℝ) (hL1 : 1 ≤ L) (ht : 0 ≤ t) (ht2L : t ≤ 2 * L) (hM1 : L / 12 ≤ M + 1) :
    32 * (t ^ 32 / (M + 1) ^ 34) ≤ 32 * 2 ^ 32 * 12 ^ 34 / L ^ 2 := by
  have hLpos : 0 < L := by linarith
  have hden : (L / 12) ^ 34 ≤ (M + 1) ^ 34 := pow_le_pow_left₀ (by positivity) hM1 34
  have hnum : t ^ 32 ≤ (2 * L) ^ 32 := pow_le_pow_left₀ ht ht2L 32
  calc 32 * (t ^ 32 / (M + 1) ^ 34) ≤ 32 * ((2 * L) ^ 32 / (L / 12) ^ 34) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact div_le_div₀ (by positivity) hnum (by positivity) hden
    _ = 32 * 2 ^ 32 * 12 ^ 34 / L ^ 2 := by field_simp

theorem rem2 (Y L s t : ℝ) (hY : 0 ≤ Y) (hL1 : 1 ≤ L) (hs1 : 1 ≤ s) (ht : 0 ≤ t)
    (ht2L : t ≤ 2 * L) :
    (Y + t ^ 32) * (s ^ 4 + 1) + (s ^ 4 + 1) * (12 * s ^ 2 * t ^ 28) ≤
      (2 * (Y + 1) * 2 ^ 32 + 24 * 2 ^ 28) * (L ^ 32 * s ^ 6) := by
  have hL32 : (1 : ℝ) ≤ L ^ 32 := one_le_pow₀ hL1
  have hs2 : (1 : ℝ) ≤ s ^ 2 := one_le_pow₀ hs1
  have hs4' : (1 : ℝ) ≤ s ^ 4 := one_le_pow₀ hs1
  have hs6 : s ^ 4 + 1 ≤ 2 * s ^ 6 := by
    have : s ^ 6 = s ^ 4 * s ^ 2 := by ring
    nlinarith
  have hs4 : s ^ 4 + 1 ≤ 2 * s ^ 4 := by linarith
  have ht32 : t ^ 32 ≤ 2 ^ 32 * L ^ 32 := by
    calc t ^ 32 ≤ (2 * L) ^ 32 := pow_le_pow_left₀ ht ht2L 32
      _ = 2 ^ 32 * L ^ 32 := by ring
  have ht28 : t ^ 28 ≤ 2 ^ 28 * L ^ 32 := by
    calc t ^ 28 ≤ (2 * L) ^ 28 := pow_le_pow_left₀ ht ht2L 28
      _ = 2 ^ 28 * L ^ 28 := by ring
      _ ≤ 2 ^ 28 * L ^ 32 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL1 (by norm_num)) (by norm_num)
  have hYy : Y + t ^ 32 ≤ (Y + 1) * (2 ^ 32 * L ^ 32) := by nlinarith
  have hA : (Y + t ^ 32) * (s ^ 4 + 1) ≤ ((Y + 1) * (2 ^ 32 * L ^ 32)) * (2 * s ^ 6) :=
    mul_le_mul hYy hs6 (by positivity) (by positivity)
  have hB : (s ^ 4 + 1) * (12 * s ^ 2 * t ^ 28) ≤ (2 * s ^ 4) * (12 * s ^ 2 * (2 ^ 28 * L ^ 32)) :=
    mul_le_mul hs4 (mul_le_mul_of_nonneg_left ht28 (by positivity)) (by positivity) (by positivity)
  have e1 : ((Y + 1) * (2 ^ 32 * L ^ 32)) * (2 * s ^ 6) = 2 * (Y + 1) * 2 ^ 32 * (L ^ 32 * s ^ 6) := by
    ring
  have e2 : (2 * s ^ 4) * (12 * s ^ 2 * (2 ^ 28 * L ^ 32)) = 24 * 2 ^ 28 * (L ^ 32 * s ^ 6) := by
    ring
  rw [e1] at hA; rw [e2] at hB
  linarith

end OMA980

namespace OMA980

open Filter Topology Finset

theorem Yterm (Y W A s4 : ℝ) (hY0 : 0 ≤ Y) (hW : 0 ≤ W)
    (hA : A ≤ 32 * W / (Y + 1) ^ 34 + s4) : Y * A ≤ 32 * W / (Y + 1) + Y * s4 := by
  have hp : (Y + 1) ^ 2 ≤ (Y + 1) ^ 34 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hYY : Y * (Y + 1) ≤ (Y + 1) ^ 34 := by nlinarith
  have hq : Y / (Y + 1) ^ 34 ≤ 1 / (Y + 1) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
  have h1 : Y * (32 * W / (Y + 1) ^ 34) = 32 * W * (Y / (Y + 1) ^ 34) := by ring
  have h2 : 32 * W * (Y / (Y + 1) ^ 34) ≤ 32 * W * (1 / (Y + 1)) :=
    mul_le_mul_of_nonneg_left hq (by positivity)
  have h3 := mul_le_mul_of_nonneg_left hA hY0
  have h4 : 32 * W * (1 / (Y + 1)) = 32 * W / (Y + 1) := by ring
  nlinarith

set_option maxHeartbeats 1000000 in
theorem tail_at (Y m0 : ℕ) (hm0 : ∀ m ≥ m0, ((m : ℝ) + 1) ^ 34 ≤ 2 ^ R m) (hYm0 : m0 ≤ Y)
    (ε : ℝ) (hε : 0 < ε) (hYε : 96 / ((Y : ℝ) + 1) ≤ ε / 2) (x : ℝ) (hx : 256 ≤ x)
    (h1 : 32 * 2 ^ 32 * 12 ^ 34 / Real.log x ^ 2 ≤ ε / 4)
    (h2 : (2 * ((Y : ℝ) + 1) * 2 ^ 32 + 24 * 2 ^ 28) * (Real.log x ^ 33 / x ^ ((4 : ℝ)⁻¹)) ≤ ε / 4)
    (h3 : ((⌈Real.log x⌉₊ ^ 32 : ℕ) : ℝ) ^ ((31 : ℝ) / 32) ≤
      (Nat.primesBelow (⌈Real.log x⌉₊ ^ 32 + 1)).card)
    (h4 : Y ≤ ⌊Real.log x / 12⌋₊) (h5 : 2 ^ 8 ≤ Real.log x) :
    tailSum Y x ≤ ε * (x / Real.log x) := by
  have hx0 : 0 < x := by linarith
  set L := Real.log x with hLdef
  have hL1 : 1 ≤ L := by linarith
  have hLpos : 0 < L := by linarith
  set s := x ^ ((8 : ℝ)⁻¹) with hs
  have hs8 : s ^ 8 = x := by
    rw [hs, show (8 : ℝ)⁻¹ = ((8 : ℕ) : ℝ)⁻¹ by norm_num]
    exact Real.rpow_inv_natCast_pow hx0.le (by norm_num)
  have hs0 : 0 ≤ s := Real.rpow_nonneg hx0.le _
  have hs1 : 1 ≤ s := by
    by_contra h; push Not at h
    have : s ^ 8 < 1 := pow_lt_one₀ hs0 h (by norm_num)
    linarith
  have hsq : Real.sqrt x = s ^ 4 := by
    rw [← hs8, show s ^ 8 = (s ^ 4) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hs2 : s ^ 2 = x ^ ((4 : ℝ)⁻¹) := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
  set t := ⌈L⌉₊ with ht
  have htL : L ≤ t := Nat.le_ceil L
  have ht2L : (t : ℝ) ≤ 2 * L := by have := Nat.ceil_lt_add_one hLpos.le; linarith
  have ht3 : 3 ≤ t := by
    have : (3 : ℝ) < t := by linarith
    exact_mod_cast this.le
  set M := ⌊L / 12⌋₊ with hM
  have hM1 : L / 12 ≤ (M : ℝ) + 1 := (Nat.lt_floor_add_one (L / 12)).le
  set W := x / L with hW
  have hWpos : 0 < W := by positivity
  have hW0 : 0 ≤ 32 * W := by positivity
  have hsieve : ∀ m, m0 ≤ m → m ≤ M → (E x m : ℝ) ≤ 32 * W / ((m : ℝ) + 1) ^ 34 + (s ^ 4 + 1) := by
    intro m hm hmM
    have h4m : (4 : ℝ) ^ m ≤ x ^ ((8 : ℝ)⁻¹) :=
      (pow_le_pow_right₀ (by norm_num) hmM).trans (four_pow_le (by linarith))
    have hE := E_le hx m h4m
    have hg := hm0 m hm
    rw [hsq] at hE
    have : 32 * x / (2 ^ R m * Real.log x) ≤ 32 * W / ((m : ℝ) + 1) ^ 34 := by
      rw [hW]
      calc 32 * x / (2 ^ R m * L) ≤ 32 * x / (((m : ℝ) + 1) ^ 34 * L) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity)
              (mul_le_mul_of_nonneg_right hg hLpos.le)
        _ = 32 * (x / L) / ((m : ℝ) + 1) ^ 34 := by field_simp
    linarith
  have hEY : (E x Y : ℝ) ≤ 32 * W / ((Y : ℝ) + 1) ^ 34 + (s ^ 4 + 1) := hsieve Y hYm0 h4
  have hEm : ∀ m ∈ Ico Y (t ^ 32), (E x m : ℝ) ≤
      32 * W * (1 / ((m : ℝ) + 1) ^ 2 + 1 / ((M : ℝ) + 1) ^ 34) + (s ^ 4 + 1) := by
    intro m hm
    rw [Finset.mem_Ico] at hm
    by_cases hmM : m ≤ M
    · have h6 := hsieve m (by omega) hmM
      have hm1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by linarith [show (0 : ℝ) ≤ m from Nat.cast_nonneg m]
      have hp : 1 / ((m : ℝ) + 1) ^ 34 ≤ 1 / ((m : ℝ) + 1) ^ 2 :=
        one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ hm1 (by norm_num))
      have h7 : 32 * W / ((m : ℝ) + 1) ^ 34 ≤
          32 * W * (1 / ((m : ℝ) + 1) ^ 2 + 1 / ((M : ℝ) + 1) ^ 34) := by
        rw [div_eq_mul_one_div]
        apply mul_le_mul_of_nonneg_left _ hW0
        have : 0 ≤ 1 / ((M : ℝ) + 1) ^ 34 := by positivity
        linarith
      linarith
    · have hanti : (E x m : ℝ) ≤ E x M := by exact_mod_cast E_anti x (show M ≤ m by omega)
      have h6 := hsieve M (by omega) le_rfl
      have h7 : 32 * W / ((M : ℝ) + 1) ^ 34 ≤
          32 * W * (1 / ((m : ℝ) + 1) ^ 2 + 1 / ((M : ℝ) + 1) ^ 34) := by
        rw [div_eq_mul_one_div]
        apply mul_le_mul_of_nonneg_left _ hW0
        have : 0 ≤ 1 / ((m : ℝ) + 1) ^ 2 := by positivity
        linarith
      linarith
  have hpi : (t : ℝ) ^ 31 ≤ (Nat.primesBelow (t ^ 32 + 1)).card := by
    refine le_trans (le_of_eq ?_) h3
    rw [Nat.cast_pow, ← Real.rpow_natCast (t : ℝ) 32, ← Real.rpow_mul (by positivity),
      ← Real.rpow_natCast]
    norm_num
  have hEy2 := Ey2_bound x hx t ht3 htL hpi s hs8 hs0
  have hlay := layer Y (t ^ 32) x hx0.le
  rw [hsq] at hlay
  have hsum : ∑ m ∈ Ico Y (t ^ 32), (E x m : ℝ) ≤
      32 * W * (2 / ((Y : ℝ) + 1)) +
        ((t ^ 32 : ℕ) : ℝ) * (32 * W / ((M : ℝ) + 1) ^ 34 + (s ^ 4 + 1)) := by
    have hc : ((Ico Y (t ^ 32)).card : ℝ) ≤ ((t ^ 32 : ℕ) : ℝ) := by
      rw [Nat.card_Ico]; exact_mod_cast Nat.sub_le _ _
    have h8 := sum_inv_sq_Ico Y (t ^ 32)
    have h9 : (0 : ℝ) ≤ 32 * W / ((M : ℝ) + 1) ^ 34 + (s ^ 4 + 1) := by positivity
    have h10 := mul_le_mul_of_nonneg_left h8 hW0
    have h11 := mul_le_mul_of_nonneg_right hc h9
    have e : ∑ m ∈ Ico Y (t ^ 32),
          (32 * W * (1 / ((m : ℝ) + 1) ^ 2 + 1 / ((M : ℝ) + 1) ^ 34) + (s ^ 4 + 1)) =
        32 * W * (∑ m ∈ Ico Y (t ^ 32), (1 / ((m : ℝ) + 1) ^ 2)) +
          ((Ico Y (t ^ 32)).card : ℝ) * (32 * W / ((M : ℝ) + 1) ^ 34 + (s ^ 4 + 1)) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
        Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
      ring
    have := Finset.sum_le_sum hEm
    linarith
  have hYterm : (Y : ℝ) * E x Y ≤ 32 * W / ((Y : ℝ) + 1) + Y * (s ^ 4 + 1) :=
    Yterm Y W (E x Y) (s ^ 4 + 1) (by positivity) hWpos.le hEY
  have hthird : (s ^ 4 + 1) * (E x (t ^ 32) : ℝ) ≤ (s ^ 4 + 1) * (12 * s ^ 2 * (t : ℝ) ^ 28) :=
    mul_le_mul_of_nonneg_left hEy2 (by positivity)
  have hr1 : 32 * W * (((t ^ 32 : ℕ) : ℝ) / ((M : ℝ) + 1) ^ 34) ≤ W * (ε / 4) := by
    have h6 := rem1 L t M hL1 (by positivity) ht2L hM1
    have h7 := mul_le_mul_of_nonneg_left (h6.trans h1) hWpos.le
    push_cast
    linarith
  have hr2 : ((Y : ℝ) + ((t ^ 32 : ℕ) : ℝ)) * (s ^ 4 + 1) +
      (s ^ 4 + 1) * (12 * s ^ 2 * (t : ℝ) ^ 28) ≤ W * (ε / 4) := by
    have h6 := rem2 Y L s t (by positivity) hL1 hs1 (by positivity) ht2L
    have hfin : (2 * ((Y : ℝ) + 1) * 2 ^ 32 + 24 * 2 ^ 28) * (L ^ 32 * s ^ 6) =
        W * ((2 * ((Y : ℝ) + 1) * 2 ^ 32 + 24 * 2 ^ 28) * (L ^ 33 / x ^ ((4 : ℝ)⁻¹))) := by
      rw [hW, ← hs2, ← hs8]; field_simp
    have h7 := mul_le_mul_of_nonneg_left h2 hWpos.le
    push_cast
    linarith
  calc tailSum Y x ≤ Y * E x Y + ∑ m ∈ Ico Y (t ^ 32), (E x m : ℝ) + (s ^ 4 + 1) * E x (t ^ 32) :=
        hlay
    _ ≤ (32 * W / ((Y : ℝ) + 1) + Y * (s ^ 4 + 1)) +
        (32 * W * (2 / ((Y : ℝ) + 1)) +
          ((t ^ 32 : ℕ) : ℝ) * (32 * W / ((M : ℝ) + 1) ^ 34 + (s ^ 4 + 1))) +
        (s ^ 4 + 1) * (12 * s ^ 2 * (t : ℝ) ^ 28) := by linarith
    _ = W * (96 / ((Y : ℝ) + 1)) + 32 * W * (((t ^ 32 : ℕ) : ℝ) / ((M : ℝ) + 1) ^ 34) +
        (((Y : ℝ) + ((t ^ 32 : ℕ) : ℝ)) * (s ^ 4 + 1) +
          (s ^ 4 + 1) * (12 * s ^ 2 * (t : ℝ) ^ 28)) := by ring
    _ ≤ W * (ε / 2) + W * (ε / 4) + W * (ε / 4) := by
        have := mul_le_mul_of_nonneg_left hYε hWpos.le
        linarith
    _ = ε * (x / Real.log x) := by rw [hW]; ring

theorem tail (ε : ℝ) (hε : 0 < ε) :
    ∃ Y : ℕ, ∀ᶠ x : ℝ in atTop, tailSum Y x ≤ ε * (x / Real.log x) := by
  obtain ⟨m0, hm0⟩ := R_growth
  set Y := max m0 ⌈192 / ε⌉₊ + 1 with hYdef
  refine ⟨Y, ?_⟩
  have hYm0 : m0 ≤ Y := by omega
  have hYε : 96 / ((Y : ℝ) + 1) ≤ ε / 2 := by
    have : 192 / ε ≤ (Y : ℝ) := by
      have h1 := Nat.le_ceil (192 / ε)
      have h2 : (⌈192 / ε⌉₊ : ℝ) ≤ Y := by exact_mod_cast (show ⌈192 / ε⌉₊ ≤ Y by omega)
      linarith
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ hε] at this
    nlinarith
  have ev1 : ∀ᶠ x : ℝ in atTop, 32 * 2 ^ 32 * 12 ^ 34 / Real.log x ^ 2 ≤ ε / 4 := by
    have : Tendsto (fun x : ℝ => (32 * 2 ^ 32 * 12 ^ 34 : ℝ) / Real.log x ^ 2) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by norm_num)).comp Real.tendsto_log_atTop)
    exact this.eventually (eventually_le_nhds (by positivity))
  have ev2 : ∀ᶠ x : ℝ in atTop, (2 * ((Y : ℝ) + 1) * 2 ^ 32 + 24 * 2 ^ 28) *
      (Real.log x ^ 33 / x ^ ((4 : ℝ)⁻¹)) ≤ ε / 4 := by
    have : Tendsto (fun x : ℝ => (2 * ((Y : ℝ) + 1) * 2 ^ 32 + 24 * 2 ^ 28) *
        (Real.log x ^ 33 / x ^ ((4 : ℝ)⁻¹))) atTop (𝓝 0) := by
      simpa using (tendsto_log_pow_div 33).const_mul (2 * ((Y : ℝ) + 1) * 2 ^ 32 + 24 * 2 ^ 28)
    exact this.eventually (eventually_le_nhds (by positivity))
  have hceil : Tendsto (fun x : ℝ => ⌈Real.log x⌉₊) atTop atTop :=
    tendsto_nat_ceil_atTop.comp Real.tendsto_log_atTop
  have ev3 : ∀ᶠ x : ℝ in atTop, ((⌈Real.log x⌉₊ ^ 32 : ℕ) : ℝ) ^ ((31 : ℝ) / 32) ≤
      (Nat.primesBelow (⌈Real.log x⌉₊ ^ 32 + 1)).card :=
    ((tendsto_pow_atTop (by norm_num : (32 : ℕ) ≠ 0)).comp hceil).eventually pi_lower
  have hfloor : Tendsto (fun x : ℝ => ⌊Real.log x / 12⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (Real.tendsto_log_atTop.atTop_div_const (by norm_num))
  have ev4 : ∀ᶠ x : ℝ in atTop, Y ≤ ⌊Real.log x / 12⌋₊ := hfloor.eventually (eventually_ge_atTop Y)
  have ev5 : ∀ᶠ x : ℝ in atTop, 2 ^ 8 ≤ Real.log x := Real.tendsto_log_atTop.eventually
    (eventually_ge_atTop _)
  filter_upwards [ev1, ev2, ev3, ev4, ev5, eventually_ge_atTop (256 : ℝ)] with x h1 h2 h3 h4 h5 hx
  exact tail_at Y m0 hm0 hYm0 ε hε hYε x hx h1 h2 h3 h4 h5

end OMA980

namespace OMA980

open Filter Topology Asymptotics Finset

theorem tailSum_anti {Y Y' : ℕ} (h : Y ≤ Y') (x : ℝ) : tailSum Y' x ≤ tailSum Y x := by
  unfold tailSum
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    simp only [Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, hp.2.1, by omega⟩
  · intro _ _ _; positivity

theorem decomp (K : ℕ) (x : ℝ) : Erdos980.residueSum 2 x =
    ∑ i ∈ range (K + 1), (Nat.nth Nat.Prime i : ℝ) * cnt i x + tailSum (Nat.nth Nat.Prime K) x := by
  have hinf := Nat.infinite_setOfPred_prime
  have hmono := Nat.nth_strictMono hinf
  unfold Erdos980.residueSum
  set s := (Nat.primesBelow ⌈x⌉₊).filter (fun p ↦ p % 2 = 1) with hs
  rw [← Finset.sum_filter_add_sum_filter_not s (fun p => nr p ≤ Nat.nth Nat.Prime K)]
  congr 1
  · symm
    rw [← Finset.sum_fiberwise_of_maps_to (s := s.filter (fun p => nr p ≤ Nat.nth Nat.Prime K))
      (t := range (K + 1)) (g := fun p => Nat.count Nat.Prime (nr p))]
    · apply Finset.sum_congr rfl
      intro i hi
      have hiK : i ≤ K := by simpa [Nat.lt_succ_iff] using hi
      have hset : (s.filter (fun p => nr p ≤ Nat.nth Nat.Prime K)).filter
          (fun p => Nat.count Nat.Prime (nr p) = i) =
          (Nat.primesBelow ⌈x⌉₊).filter (fun p => p % 2 = 1 ∧ nr p = Nat.nth Nat.Prime i) := by
        ext p
        simp only [hs, Finset.mem_filter]
        constructor
        · rintro ⟨⟨⟨hpb, hp2⟩, hle⟩, hc⟩
          refine ⟨hpb, hp2, ?_⟩
          have hpr := nr_prime (Nat.mem_primesBelow.mp hpb).2 hp2
          rw [← hc, Nat.nth_count hpr]
        · rintro ⟨hpb, hp2, hpi⟩
          refine ⟨⟨⟨hpb, hp2⟩, ?_⟩, ?_⟩
          · rw [hpi]; exact hmono.monotone hiK
          · rw [hpi]; exact Nat.count_nth_of_infinite hinf i
      rw [hset, cnt, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      simp only [Finset.mem_filter] at hp
      show _ = (nr p : ℝ)
      rw [hp.2.2]; simp
    · intro p hp
      simp only [hs, Finset.mem_filter, Nat.mem_primesBelow] at hp
      have hpr := nr_prime hp.1.1.2 hp.1.2
      simp only [Finset.mem_range, Nat.lt_succ_iff]
      rw [← hmono.le_iff_le, Nat.nth_count hpr]
      exact hp.2
  · unfold tailSum
    rw [hs, Finset.filter_filter]
    apply Finset.sum_congr
    · ext p; simp only [Finset.mem_filter, not_le]
    · intro _ _; rfl

theorem key : Tendsto (fun x => Erdos980.residueSum 2 x / (x / Real.log x)) atTop
    (𝓝 (∑' i : ℕ, (Nat.nth Nat.Prime i : ℝ) / 2 ^ (i + 1))) := by
  set C := ∑' i : ℕ, (Nat.nth Nat.Prime i : ℝ) / 2 ^ (i + 1) with hCdef
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨Y, hY⟩ := tail (ε / 4) (by linarith)
  have hps := summable_c.hasSum.tendsto_sum_nat
  rw [Metric.tendsto_nhds] at hps
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp (hps (ε / 4) (by linarith))
  set K := max N0 Y with hK
  have hKN : N0 ≤ K + 1 := by omega
  have hKY : Y ≤ Nat.nth Nat.Prime K := by
    have := Nat.add_two_le_nth_prime K; omega
  have hmain : Tendsto (fun x : ℝ => ∑ i ∈ range (K + 1),
      (Nat.nth Nat.Prime i : ℝ) * ((cnt i x : ℝ) / (x / Real.log x))) atTop
      (𝓝 (∑ i ∈ range (K + 1), (Nat.nth Nat.Prime i : ℝ) * (1 / 2 ^ (i + 1)))) :=
    tendsto_finsetSum _ (fun i _ => (main_term i).const_mul _)
  rw [Metric.tendsto_nhds] at hmain
  filter_upwards [hmain (ε / 4) (by linarith), hY, eventually_gt_atTop 1] with x hx1 hx2 hx3
  have hw : 0 < x / Real.log x := div_pos (by linarith) (Real.log_pos hx3)
  have hCK := hN0 (K + 1) hKN
  rw [decomp K x, add_div, Finset.sum_div]
  have e1 : ∑ i ∈ range (K + 1), (Nat.nth Nat.Prime i : ℝ) * (cnt i x : ℝ) / (x / Real.log x) =
      ∑ i ∈ range (K + 1), (Nat.nth Nat.Prime i : ℝ) * ((cnt i x : ℝ) / (x / Real.log x)) := by
    apply Finset.sum_congr rfl; intro i _; ring
  have e2 : ∑ i ∈ range (K + 1), (Nat.nth Nat.Prime i : ℝ) * (1 / 2 ^ (i + 1)) =
      ∑ i ∈ range (K + 1), (Nat.nth Nat.Prime i : ℝ) / 2 ^ (i + 1) := by
    apply Finset.sum_congr rfl; intro i _; ring
  rw [e1]
  rw [e2] at hx1
  have ht0 : 0 ≤ tailSum (Nat.nth Nat.Prime K) x := by
    unfold tailSum; apply Finset.sum_nonneg; intro _ _; positivity
  have ht1 : tailSum (Nat.nth Nat.Prime K) x / (x / Real.log x) ≤ ε / 4 := by
    rw [div_le_iff₀ hw]; exact (tailSum_anti hKY x).trans hx2
  have ht2 : 0 ≤ tailSum (Nat.nth Nat.Prime K) x / (x / Real.log x) := div_nonneg ht0 hw.le
  rw [Real.dist_eq] at hx1 hCK ⊢
  rw [abs_lt] at hx1 hCK ⊢
  constructor <;> linarith [hx1.1, hx1.2, hCK.1, hCK.2]

theorem solution : Erdos980.residueSum 2 ~[atTop]
    fun x ↦ (∑' i : ℕ, (Nat.nth Nat.Prime i : ℝ) / 2 ^ (i + 1)) * x / Real.log x := by
  set C := ∑' i : ℕ, (Nat.nth Nat.Prime i : ℝ) / 2 ^ (i + 1) with hCdef
  have hC : 0 < C := by
    have h0 : (Nat.nth Nat.Prime 0 : ℝ) / 2 ^ (0 + 1) ≤ C :=
      summable_c.le_tsum 0 (fun j _ => by positivity)
    have : (Nat.nth Nat.Prime 0 : ℝ) / 2 ^ (0 + 1) = 1 := by
      rw [Nat.nth_prime_zero_eq_two]; norm_num
    linarith
  apply isEquivalent_of_tendsto_one
  have := key.div_const C
  rw [div_self hC.ne'] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with x hx
  have hl : 0 < Real.log x := Real.log_pos hx
  simp only [Pi.div_apply]
  field_simp

end OMA980

theorem OMA.solution : type_of% @Erdos980.erdos_980.variants.erdos_two :=
  OMA980.solution

