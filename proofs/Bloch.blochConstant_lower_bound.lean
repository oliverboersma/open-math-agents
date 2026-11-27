import FormalConjectures.Wikipedia.Bloch
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Analytic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic

/-!
The improved lower bound for the Bloch constant follows from disk automorphism normalization,
the distortion argument of Bonk, Minda, and Yanagihara (Pacific J. Math. 179, 1997), and a
rational dual certificate built using Wikström's method (arXiv:2608.17660).
-/

open Metric Set
open scoped ComplexConjugate

namespace BlochNormalization

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
    (hNorm : ∀ g : ℂ → ℂ, DifferentiableOn ℂ g (ball 0 1) → g 0 = 0 →
      deriv g 0 = 1 → (∀ z ∈ ball (0 : ℂ) 1, (1 - ‖z‖ ^ 2) * ‖deriv g z‖ ≤ 1) →
      Covers g R) : B ≤ Bloch.blochConstant := by
  unfold Bloch.blochConstant
  apply le_csSup
  · refine ⟨1, ?_⟩
    intro b hb
    have hc : ∃ S, IsOpen S ∧ S ⊆ ball (0 : ℂ) 1 ∧
        ∃ x, id '' S = ball x b ∧ InjOn id S :=
      hb id differentiableOn_id (by simp)
    rcases hc with ⟨S, -, hS, x, hball, -⟩
    rw [image_id] at hball
    by_cases hp : 0 < b
    · exact Bloch.radius_le_of_ball_subset_ball (𝕜 := ℂ) hp (hball ▸ hS)
    · linarith
  intro F hF hF0
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
  obtain ⟨S, hS, hSsub, c, hSc, hSinj⟩ := hNorm g hgD hg0 hgD0 hgW
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
  let V := ball (0 : ℂ) s ∩ u ⁻¹' S
  have hV : IsOpen V := hu.isOpen_inter_preimage isOpen_ball hS
  have hVsub : V ⊆ ball (0 : ℂ) 1 := fun _ hz => ball_subset_ball hs1.le hz.1
  have hFt (z : ℂ) : F (t z) = d * g z + f a := by
    change f (mobius a z) = d * ((f (mobius a z) - f a) / d) + f a
    field_simp
    ring
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

end BlochNormalization

namespace BlochDistortion

open Filter
open scoped Topology

private theorem norm_mobius_sq {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    1 - ‖BlochNormalization.mobius a z‖ ^ 2 =
      (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) / ‖1 + conj a * z‖ ^ 2 := by
  have hd : 1 + conj a * z ≠ 0 := BlochNormalization.denom_ne ha hz
  rw [BlochNormalization.mobius, norm_div, div_pow]
  apply (eq_div_iff (pow_ne_zero _ (norm_ne_zero_iff.mpr hd))).mpr
  rw [sub_mul, one_mul, div_mul_cancel₀ _ (pow_ne_zero _ (norm_ne_zero_iff.mpr hd))]
  exact BlochNormalization.norm_identity a z

private theorem schwarzPick_cross {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (ball 0 1))
    (hgmap : MapsTo g (ball 0 1) (ball 0 1))
    {x y : ℂ} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    (1 - ‖g x‖ ^ 2) * (1 - ‖g y‖ ^ 2) * ‖1 - conj x * y‖ ^ 2 ≥
      (1 - ‖x‖ ^ 2) * (1 - ‖y‖ ^ 2) * ‖1 - conj (g x) * g y‖ ^ 2 := by
  have hx' : ‖g x‖ < 1 := mem_ball_zero_iff.mp (hgmap (mem_ball_zero_iff.mpr hx))
  have hy' : ‖g y‖ < 1 := mem_ball_zero_iff.mp (hgmap (mem_ball_zero_iff.mpr hy))
  let G : ℂ → ℂ := fun z => BlochNormalization.mobius (-(g x)) (g (BlochNormalization.mobius x z))
  have hd : DifferentiableOn ℂ G (ball 0 1) := by
    intro z hz
    have ht := BlochNormalization.hasDerivAt_mobius hx (mem_ball_zero_iff.mp hz)
    have htm := BlochNormalization.maps_mobius hx hz
    have hgt := hg.differentiableAt (isOpen_ball.mem_nhds htm)
    have hM := BlochNormalization.hasDerivAt_mobius (a := -(g x)) (by simpa using hx')
      (mem_ball_zero_iff.mp (hgmap htm))
    exact (hM.differentiableAt.comp z (hgt.comp z ht.differentiableAt)).differentiableWithinAt
  have hmap : MapsTo G (ball 0 1) (closedBall 0 1) :=
    fun z hz => ball_subset_closedBall
      (BlochNormalization.maps_mobius (a := -(g x)) (by simpa using hx')
        (hgmap (BlochNormalization.maps_mobius hx hz)))
  have h0 : G 0 = 0 := by simp [G, BlochNormalization.mobius]
  let u := BlochNormalization.mobius (-x) y
  have hu : u ∈ ball 0 1 := BlochNormalization.maps_mobius (a := -x) (by simpa using hx)
    (mem_ball_zero_iff.mpr hy)
  have hcomp : BlochNormalization.mobius x u = y := by
    simpa only [u, neg_neg] using
      BlochNormalization.mobius_inverse (a := -x) (by simpa using hx) hy
  have hn := Complex.norm_le_norm_of_mapsTo_ball hd hmap h0 (mem_ball_zero_iff.mp hu)
  have hs : 1 - ‖u‖ ^ 2 ≤ 1 - ‖BlochNormalization.mobius (-(g x)) (g y)‖ ^ 2 := by
    change ‖BlochNormalization.mobius (-(g x)) (g (BlochNormalization.mobius x u))‖ ≤ ‖u‖ at hn
    rw [hcomp] at hn
    nlinarith [norm_nonneg u, norm_nonneg (BlochNormalization.mobius (-(g x)) (g y))]
  dsimp [u] at hs
  rw [norm_mobius_sq (by simpa using hx) hy, norm_mobius_sq (by simpa using hx') hy'] at hs
  simp only [norm_neg, map_neg, neg_mul, ← sub_eq_add_neg] at hs
  have hp₁ : 0 < ‖1 - conj x * y‖ := norm_pos_iff.mpr <| by
    simpa [sub_eq_add_neg] using BlochNormalization.denom_ne (a := -x) (by simpa using hx) hy
  have hp₂ : 0 < ‖1 - conj (g x) * g y‖ := norm_pos_iff.mpr <| by
    simpa [sub_eq_add_neg] using BlochNormalization.denom_ne (a := -(g x)) (by simpa using hx') hy'
  exact (div_le_div_iff₀ (sq_pos_of_pos hp₁) (sq_pos_of_pos hp₂)).mp hs

private theorem julia_cross {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (ball 0 1))
    (hgmap : MapsTo g (ball 0 1) (ball 0 1)) (hg1 : g 1 = 1)
    (hgd : HasDerivAt g 1 1) {w : ℂ} (hw : ‖w‖ < 1) :
    (1 - ‖g w‖ ^ 2) * ‖1-w‖ ^ 2 ≥ (1 - ‖w‖ ^ 2) * ‖1-g w‖ ^ 2 := by
  have hre : HasDerivAt (fun t : ℝ => (g (t : ℂ)).re) 1 1 := by
    simpa using hgd.real_of_complex (z := (1 : ℝ))
  have him : HasDerivAt (fun t : ℝ => (g (t : ℂ)).im) 0 1 := by
    simpa [Complex.mul_re] using (hgd.const_mul (-Complex.I)).real_of_complex (z := (1 : ℝ))
  have hn : HasDerivAt (fun t : ℝ => ‖g (t : ℂ)‖ ^ 2) 2 1 := by
    have he : (fun t : ℝ => ‖g (t : ℂ)‖ ^ 2) =
        (fun t : ℝ => (g (t : ℂ)).re) ^ 2 + (fun t : ℝ => (g (t : ℂ)).im) ^ 2 := by
      funext t
      change ‖g (t : ℂ)‖ ^ 2 = (g t).re ^ 2 + (g t).im ^ 2
      rw [Complex.sq_norm]
      simp [Complex.normSq_apply, pow_two]
    rw [he]
    simpa [hg1] using (hre.pow 2).add (him.pow 2)
  have hlim : Tendsto (fun t : ℝ => (1 - ‖g (t : ℂ)‖ ^ 2) / (1 - t ^ 2))
      (𝓝[<] (1 : ℝ)) (𝓝 1) := by
    have h₂ : HasDerivAt (fun t : ℝ => t ^ 2) 2 1 := by
      simpa using! (hasDerivAt_id (1 : ℝ)).pow 2
    have h : Tendsto (fun t : ℝ => slope (fun t : ℝ => ‖g (t : ℂ)‖ ^ 2) 1 t /
        slope (fun t : ℝ => t ^ 2) 1 t) (𝓝[<] (1 : ℝ)) (𝓝 (2 / 2)) :=
      (hn.tendsto_slope.mono_left (nhdsLT_le_nhdsNE (1 : ℝ))).div
        (h₂.tendsto_slope.mono_left (nhdsLT_le_nhdsNE (1 : ℝ))) (by norm_num)
    rw [div_self (by norm_num : (2 : ℝ) ≠ 0)] at h
    refine h.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with t ⟨ht0, ht1⟩
    have htne : t - 1 ≠ 0 := sub_ne_zero.mpr ht1.ne
    have htt : t ^ 2 < 1 := by nlinarith [mul_pos ht0 (sub_pos.mpr ht1)]
    have htpos : 1 - t ^ 2 ≠ 0 := (sub_pos.mpr htt).ne'
    have hn' : t ^ 2 - 1 ≠ 0 := sub_ne_zero.mpr htt.ne
    simp only [slope_def_field, Complex.ofReal_one, hg1, norm_one, one_pow]
    field_simp [htne, htpos, hn']
    ring
  have hcont : Tendsto (fun t : ℝ => g (t : ℂ)) (𝓝[<] (1 : ℝ)) (𝓝 1) := by
    have hhh := hgd.continuousAt.tendsto.comp (Complex.continuous_ofReal.tendsto (1 : ℝ))
    simpa [hg1, Function.comp_def] using hhh.mono_left nhdsWithin_le_nhds
  have hinj1 : Tendsto (fun t : ℝ => ‖1 - conj (t : ℂ) * w‖ ^ 2)
      (𝓝[<] (1 : ℝ)) (𝓝 (‖1 - w‖ ^ 2)) := by
    have h : Continuous (fun t : ℝ => ‖1 - conj (t : ℂ) * w‖ ^ 2) := by fun_prop
    simpa using (h.tendsto 1).mono_left nhdsWithin_le_nhds
  have hinj2 : Tendsto (fun t : ℝ => ‖1 - conj (g (t : ℂ)) * g w‖ ^ 2)
      (𝓝[<] (1 : ℝ)) (𝓝 (‖1 - g w‖ ^ 2)) := by
    have h : Continuous (fun z : ℂ => ‖1 - conj z * g w‖ ^ 2) := by fun_prop
    simpa [Function.comp_def] using (h.tendsto (1 : ℂ)).comp hcont
  have hL : Tendsto (fun t : ℝ => (1 - ‖g (t : ℂ)‖ ^ 2) / (1 - t ^ 2) *
      (1 - ‖g w‖ ^ 2) * ‖1 - conj (t : ℂ) * w‖ ^ 2) (𝓝[<] (1 : ℝ))
      (𝓝 (1 * (1 - ‖g w‖ ^ 2) * ‖1 - w‖ ^ 2)) := (hlim.mul tendsto_const_nhds).mul hinj1
  have hR : Tendsto (fun t : ℝ => (1 - ‖w‖ ^ 2) * ‖1 - conj (g (t : ℂ)) * g w‖ ^ 2)
      (𝓝[<] (1 : ℝ)) (𝓝 ((1 - ‖w‖ ^ 2) * ‖1 - g w‖ ^ 2)) := tendsto_const_nhds.mul hinj2
  have he : ∀ᶠ t in 𝓝[<] (1 : ℝ), t ∈ Ioo 0 1 := Ioo_mem_nhdsLT zero_lt_one
  have h := le_of_tendsto_of_tendsto hR hL ?_
  · simpa using h
  filter_upwards [he] with t ⟨ht0, ht1⟩
  have ht : ‖(t : ℂ)‖ < 1 := by simpa [abs_of_pos ht0] using ht1
  have hs := schwarzPick_cross hg hgmap ht hw
  have htp : 0 < 1 - t ^ 2 := by nlinarith
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0] at hs
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
  exact (le_div_iff₀ htp).mpr (by simpa only [mul_assoc, mul_left_comm, mul_comm] using hs)

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

/-- The Bonk–Minda–Yanagihara distortion argument at normalization one. It uses the
Schwarz–Pick boundary inequality on the disk obtained by moving the hyperbolic center
to the positive real point of modulus one over square root three. -/
private theorem positive_on_real_radius {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 1)) (hf0 : f 0 = 1)
    (hW : ∀ z ∈ ball (0 : ℂ) 1, (1 - ‖z‖ ^ 2) * ‖f z‖ ≤ 1)
    {m t : ℝ} (hm : 0 < m) (hm2 : m ^ 2 = 1 / 3) (ht0 : 0 ≤ t) (htm : t < m) :
    0 < (f (t : ℂ)).re := by
  rcases ht0.eq_or_lt with rfl | ht0
  · simp [hf0]
  have hm1 : m < 1 := by nlinarith
  have hmC : ‖(m : ℂ)‖ = m := by simp [abs_of_pos hm]
  have hmC1 : ‖(m : ℂ)‖ < 1 := hmC.symm ▸ hm1
  have hmCN : ‖-(m : ℂ)‖ < 1 := by rwa [norm_neg]
  have hmt : 0 < 1 - m*t := by nlinarith [mul_pos (sub_pos.mpr hm1) ht0]
  have hmq : 0 < 1 - m^2 := by rw [hm2]; norm_num
  let Z : ℂ → ℂ := fun w => BlochNormalization.mobius (m : ℂ) (-(m : ℂ)*w)
  let g : ℂ → ℂ := fun w => (1 - (m : ℂ) * Z w)^2 * f (Z w)
  have hin (w : ℂ) (hw : ‖w‖ < 1) : ‖-(m : ℂ) * w‖ < 1 := by
    rw [norm_mul, norm_neg, hmC]
    exact (mul_lt_mul_of_pos_left hw hm).trans (by simpa using hm1)
  have hZ (w : ℂ) (hw : ‖w‖ < 1) : ‖Z w‖ < 1 :=
    mem_ball_zero_iff.mp (BlochNormalization.maps_mobius hmC1
      (mem_ball_zero_iff.mpr (hin w hw)))
  have hZdiff (w : ℂ) (hw : ‖-(m : ℂ) * w‖ < 1) : DifferentiableAt ℂ Z w := by
    have h := BlochNormalization.hasDerivAt_mobius hmC1 hw
    exact h.differentiableAt.comp w (by fun_prop)
  have hgd : DifferentiableOn ℂ g (ball 0 1) := by
    intro w hw
    have hw' := mem_ball_zero_iff.mp hw
    have hZ' := hZdiff w (hin w hw')
    have hh : DifferentiableAt ℂ (fun w => f (Z w)) w :=
      (hf.differentiableAt (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr (hZ w hw')))).comp w hZ'
    have hp : DifferentiableAt ℂ (fun w => (1 - (m : ℂ) * Z w)^2) w := by fun_prop
    exact (hp.mul hh).differentiableWithinAt
  have hgmap : MapsTo g (ball 0 1) (ball 0 1) := by
    intro w hw
    have hw' := mem_ball_zero_iff.mp hw
    have hz := hZ w hw'
    have hzmem : Z w ∈ ball 0 1 := mem_ball_zero_iff.mpr hz
    have hinv : BlochNormalization.mobius (-(m : ℂ)) (Z w) = -(m : ℂ) * w :=
      BlochNormalization.mobius_inverse hmC1 (hin w hw')
    have hd : 1 - (m : ℂ) * Z w ≠ 0 := by
      simpa [sub_eq_add_neg] using BlochNormalization.denom_ne (a := -(m : ℂ))
        hmCN hz
    have hfwt := hW _ hzmem
    have hN := norm_mobius_sq (a := -(m : ℂ)) (z := Z w)
      hmCN hz
    rw [hinv, norm_mul, norm_neg, hmC] at hN
    simp only [map_neg, Complex.conj_ofReal, neg_mul, ← sub_eq_add_neg] at hN
    have hN' := (eq_div_iff (pow_ne_zero 2 (norm_ne_zero_iff.mpr hd))).mp hN
    have hZp : 0 < 1 - ‖Z w‖ ^ 2 := by nlinarith [norm_nonneg (Z w)]
    have hwp : 0 < 1 - (m * ‖w‖)^2 := by
      have hn := hin w hw'
      rw [norm_mul, norm_neg, hmC] at hn
      nlinarith [show 0 ≤ m * ‖w‖ by positivity]
    have hwt : 1 - m^2 < 1 - (m * ‖w‖)^2 := by
      have hn := mul_lt_mul_of_pos_left hw' hm
      nlinarith [show 0 ≤ m * ‖w‖ by positivity]
    have hle : ‖1 - (m : ℂ) * Z w‖^2 * ‖f (Z w)‖ ≤ (1 - m^2)/(1 - (m*‖w‖)^2) := by
      apply (le_div_iff₀ hwp).mpr
      calc
        _ = ((1 - (m*‖w‖)^2) * ‖1 - (m : ℂ)* Z w‖^2) * ‖f (Z w)‖ := by ring
        _ = (1 - m^2) * ((1 - ‖Z w‖^2) * ‖f (Z w)‖) := by rw [hN']; ring
        _ ≤ 1 - m^2 := by simpa using mul_le_mul_of_nonneg_left hfwt hmq.le
    rw [mem_ball_zero_iff]
    simpa only [g, norm_mul, norm_pow] using hle.trans_lt ((div_lt_one hwp).mpr hwt)
  have hZ1 : Z 1 = 0 := by simp [Z, BlochNormalization.mobius]
  have hg1 : g 1 = 1 := by simp [g, hZ1, hf0]
  have hder : HasDerivAt g 1 1 := by
    have hmul : HasDerivAt (fun w : ℂ => -(m : ℂ)*w) (-(m : ℂ)) 1 := by
      simpa using (hasDerivAt_id (1 : ℂ)).const_mul (-(m : ℂ))
    have hM := BlochNormalization.hasDerivAt_mobius (z := -(m : ℂ)*1)
      hmC1 (by simpa only [mul_one] using hmCN)
    have hC : (m : ℂ)^2 = (1/3 : ℂ) := by
      simpa only [Complex.ofReal_pow, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
        using congrArg Complex.ofReal hm2
    have hZ' : HasDerivAt Z (-(3/2 : ℂ) * m) 1 := by
      have h := hM.comp 1 hmul
      have he : (1 - ((m^2 : ℝ) : ℂ)) / (1 + conj (m : ℂ)*(-(m : ℂ)*1))^2 *
          (-(m : ℂ)) = -(3/2 : ℂ)* m := by
        rw [hm2]
        simp only [Complex.conj_ofReal, mul_one, mul_neg, ← pow_two, hC]
        norm_num
      simpa only [Z, Function.comp_def, hmC, he] using h
    have hq : HasDerivAt (fun w => 1 - (m : ℂ) * Z w) ((3/2 : ℂ)*m^2) 1 := by
      have h := (hZ'.const_mul (m : ℂ)).const_sub 1
      have he : -((m : ℂ) * (-(3/2 : ℂ)*m)) = (3/2 : ℂ)*m^2 := by ring
      simpa only [he] using h
    have hq' : HasDerivAt (fun w => (1 - (m : ℂ) * Z w)^2) 1 1 := by
      norm_num [hZ1, hC] at hq ⊢
      simpa [hZ1] using hq.fun_pow 2
    have hfa := (hf.differentiableAt (ball_mem_nhds 0 zero_lt_one)).hasDerivAt
    have hfa' : HasDerivAt f 0 (Z 1) := by
      simpa only [hZ1, deriv_zero_of_weight hf hf0 hW] using hfa
    have hcomp : HasDerivAt (fun w => f (Z w)) 0 1 := by
      simpa only [zero_mul, Function.comp_def] using hfa'.comp 1 hZ'
    simpa [g, hZ1, hf0] using! hq'.mul hcomp
  let v : ℝ := (m-t)/(m*(1-m*t))
  have hv0 : 0 < v := div_pos (sub_pos.mpr htm) (mul_pos hm hmt)
  have hv1 : v < 1 := by
    apply (div_lt_one (mul_pos hm hmt)).mpr
    nlinarith [mul_pos ht0 hmq]
  have hvC : ‖(v : ℂ)‖ < 1 := by simpa [abs_of_pos hv0] using hv1
  have hzt : Z (v : ℂ) = t := by
    have hpre : -(m : ℂ) * (v : ℂ) = BlochNormalization.mobius (-(m : ℂ)) (t : ℂ) := by
      have hmN : (m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hm.ne'
      have hdN : 1 - (m : ℂ)*(t : ℂ) ≠ 0 := by exact_mod_cast hmt.ne'
      unfold v BlochNormalization.mobius
      push_cast
      simp only [map_neg, Complex.conj_ofReal, neg_mul, ← sub_eq_add_neg]
      field_simp [hmN, hdN]
      ring
    have htC : ‖(t : ℂ)‖ < 1 := by simpa [abs_of_pos ht0] using htm.trans hm1
    simpa only [Z, hpre, neg_neg] using
      BlochNormalization.mobius_inverse (a := -(m : ℂ)) hmCN htC
  have hJ := julia_cross hgd hgmap hg1 hder hvC
  have hh : 0 < (g (v : ℂ)).re := by
    by_contra! hneg
    have hN : 1 ≤ ‖1 - g (v : ℂ)‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
        Complex.one_re, Complex.one_im]
      nlinarith [sq_nonneg ((g (v : ℂ)).re), sq_nonneg ((g (v : ℂ)).im)]
    have hK : ‖1 - (v : ℂ)‖ ^ 2 = (1-v)^2 := by
      rw [show (1 : ℂ) - (v : ℂ) = ((1-v : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have hv' : ‖(v : ℂ)‖ = v := by simp [abs_of_pos hv0]
    rw [hK, hv'] at hJ
    have hA := mul_le_mul_of_nonneg_left hN (show 0 ≤ 1-v^2 by nlinarith)
    have hB := mul_le_mul_of_nonneg_right
      (sub_le_self 1 (sq_nonneg ‖g (v : ℂ)‖)) (sq_nonneg (1-v))
    have hcontra := hA.trans (hJ.trans hB)
    nlinarith [mul_pos hv0 (sub_pos.mpr hv1)]
  have hh' : (g (v : ℂ)).re = (1-m*t)^2 * (f (t : ℂ)).re := by
    dsimp only [g]
    rw [hzt]
    rw [show (1 : ℂ) - (m : ℂ)*(t : ℂ) = ((1-m*t : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
  rw [hh'] at hh
  exact pos_of_mul_pos_right hh (sq_nonneg _)

theorem positive_re_of_weight {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 1)) (hf0 : f 0 = 1)
    (hW : ∀ z ∈ ball (0 : ℂ) 1, (1 - ‖z‖ ^ 2) * ‖f z‖ ≤ 1)
    {z : ℂ} (hz : ‖z‖ < Real.sqrt (1/3)) : 0 < (f z).re := by
  rcases eq_or_ne z 0 with rfl | hn
  · simp [hf0]
  let d := z / (‖z‖ : ℂ)
  have hp : 0 < ‖z‖ := norm_pos_iff.mpr hn
  have hd : ‖d‖ = 1 := by
    dsimp [d]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp, div_self hp.ne']
  have hD (w : ℂ) : ‖d*w‖ = ‖w‖ := by rw [norm_mul, hd, one_mul]
  have he : d * (‖z‖ : ℂ) = z := by
    exact div_mul_cancel₀ z (by exact_mod_cast hp.ne')
  have hdiff : DifferentiableOn ℂ (fun w => f (d*w)) (ball 0 1) := by
    have hlin : Differentiable ℂ (fun w => d*w) := by fun_prop
    exact hf.comp hlin.differentiableOn (by intro w hw; simpa only [mem_ball_zero_iff, hD] using hw)
  have hB (w : ℂ) (hw : w ∈ ball (0 : ℂ) 1) :
      (1 - ‖w‖^2) * ‖f (d*w)‖ ≤ 1 := by
    have hw' : d*w ∈ ball (0 : ℂ) 1 := by simpa only [mem_ball_zero_iff, hD] using hw
    simpa only [hD] using hW _ hw'
  have h := positive_on_real_radius hdiff (by simpa using hf0) hB
    (Real.sqrt_pos.mpr (by norm_num)) (Real.sq_sqrt (by norm_num)) (norm_nonneg z) hz
  simpa [he] using h

end BlochDistortion

/- Cauchy estimates for the coefficients used in the Bloch bound. -/

open Metric Set Filter
open scoped NNReal ENNReal Topology ComplexConjugate

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

/- Uniform geometric control of truncated holomorphic series. -/

open Metric Set Filter
open scoped BigOperators

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

theorem split33 {R : Type*} [AddCommMonoid R] (a : ℕ → R) :
    (∑ k ∈ Finset.range 33, a k) = a 0 + a 1 + ∑ k : Fin 31, a (k.val + 2) := by
  rw [← Fin.sum_univ_eq_sum_range, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp [Fin.val_succ, add_assoc]

end BlochTails

namespace BlochLowCoefficients

open Filter
open scoped NNReal ENNReal Topology

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

private theorem small_coeff (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (ball 0 1))
    (hf0 : f 0 = 0) (hf1 : deriv f 0 = 0)
    (hmap : MapsTo f (ball 0 1) (ball 0 1)) :
    ‖iteratedDeriv 3 f 0‖ ≤ 6 := by
  have ha := (hf.differentiableAt (ball_mem_nhds 0 zero_lt_one)).hasDerivAt
  rw [hf1] at ha
  have hsmall : (fun w => f w - f 0) =o[𝓝 0] (fun w => ‖w - 0‖ ^ (1 : ℕ)) := by
    simpa using (ha.isLittleO).norm_right
  have hsq (z : ℂ) (hz : ‖z‖ < 1) : ‖f z‖ ≤ ‖z‖ ^ 2 := by
    have h := Complex.dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO
      (c := (0 : ℂ)) (n := 1) (R₂ := 1) hf (by rw [hf0]; exact hmap.mono_right ball_subset_closedBall)
      hsmall (mem_ball_zero_iff.mpr hz)
    simpa [hf0, dist_zero_right] using h
  have hR (R : ℝ) (h0 : 0 < R) (h1 : R < 1) :
      ‖iteratedDeriv 3 f 0‖ ≤ 6 / R := by
    let Q : ℝ≥0 := ⟨R, h0.le⟩
    have hfR : DifferentiableOn ℂ f (closedBall 0 Q) :=
      hf.mono (closedBall_subset_ball h1)
    have hC := BlochCoefficients.cauchy_bound (f := f) (R := R) (M := R^2) h0
      (hfR.continuousOn.mono sphere_subset_closedBall) (fun z hz => by
        have hzn := mem_sphere_zero_iff_norm.mp hz
        rw [← hzn]
        exact hsq z (hzn.symm ▸ h1)) 3
    have he := congrArg norm (coeff_eq_iteratedDeriv (R := Q) h0 hfR 3)
    norm_num [norm_mul] at he
    rw [← he]
    refine (mul_le_mul_of_nonneg_left hC (by norm_num)).trans_eq ?_
    field_simp [h0.ne']
  have hlim : Tendsto (fun R : ℝ => 6 / R) (𝓝[<] (1 : ℝ)) (𝓝 6) := by
    have hc : ContinuousAt (fun R : ℝ => 6 / R) 1 := by fun_prop (disch := norm_num)
    simpa using hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio (1 : ℝ)))
  refine ge_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with R hR'
  exact hR R hR'.1 hR'.2

theorem third {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball 0 1)) (hf0 : f 0 = 1)
    (hW : ∀ z ∈ ball (0 : ℂ) 1, (1 - ‖z‖ ^ 2) * ‖f z‖ ≤ 1) :
    ‖(cauchyPowerSeries f 0 (19/20)).coeff 3‖ ≤ 21/5 := by
  have hf1 := BlochDistortion.deriv_zero_of_weight hf hf0 hW
  let c : ℂ := 5 / 9
  let s : ℂ := 2 / 3
  let L : ℂ → ℂ := fun z => c * f (s*z)
  let H : ℂ → ℂ := fun z => BlochNormalization.mobius (-c) (L z)
  let D : ℂ → ℂ := fun z => 1 - c * L z
  have hc : ‖c‖ = 5/9 := by
    rw [show c = ((5/9 : ℝ) : ℂ) by norm_num [c], Complex.norm_real]
    norm_num
  have hs : ‖s‖ = 2/3 := by
    rw [show s = ((2/3 : ℝ) : ℂ) by norm_num [s], Complex.norm_real]
    norm_num
  have hcc : conj c = c := by
    rw [show c = ((5/9 : ℝ) : ℂ) by norm_num [c], Complex.conj_ofReal]
  have hcn : ‖-c‖ < 1 := by rw [norm_neg, hc]; norm_num
  have hscale : MapsTo (fun z => s*z) (ball 0 1) (ball 0 1) := by
    intro z hz
    rw [mem_ball_zero_iff, norm_mul, hs]
    have h := mem_ball_zero_iff.mp hz
    linarith
  have hld (z : ℂ) : HasDerivAt (fun w => s*w) s z := by
    simpa using (hasDerivAt_id z).const_mul s
  have hL : DifferentiableOn ℂ L (ball 0 1) :=
    (hf.comp (fun z _ => (hld z).differentiableAt.differentiableWithinAt) hscale).const_mul c
  have hL0 : L 0 = c := by simp [L, hf0]
  have hL1 : HasDerivAt L 0 0 := by
    have hf' : HasDerivAt f 0 (s * 0) := by
      simpa [hf1] using (hf.differentiableAt (ball_mem_nhds 0 zero_lt_one)).hasDerivAt
    simpa [L, Function.comp_def] using (hf'.comp 0 (hld 0)).const_mul c
  have hLmap : MapsTo L (ball 0 1) (ball 0 1) := by
    intro z hz
    have hW' := hW _ (hscale hz)
    have hz' := mem_ball_zero_iff.mp hz
    have hfact : 5/9 < 1 - ‖s*z‖^2 := by
      rw [norm_mul, hs]
      nlinarith [norm_nonneg z, mul_pos (sub_pos.mpr hz') (show 0 < 1 + ‖z‖ by positivity)]
    rw [mem_ball_zero_iff]
    dsimp [L]
    rw [norm_mul, hc]
    by_contra! he
    have hp : 0 < ‖f (s*z)‖ := by linarith
    linarith [mul_lt_mul_of_pos_right hfact hp]
  have hH : DifferentiableOn ℂ H (ball 0 1) := by
    intro z hz
    exact ((BlochNormalization.hasDerivAt_mobius hcn
      (mem_ball_zero_iff.mp (hLmap hz))).differentiableAt.comp z
      (hL.differentiableAt (isOpen_ball.mem_nhds hz))).differentiableWithinAt
  have hHmap : MapsTo H (ball 0 1) (ball 0 1) :=
    (BlochNormalization.maps_mobius hcn).comp hLmap
  have hH0 : H 0 = 0 := by simp [H, hL0, BlochNormalization.mobius]
  have hH1 : deriv H 0 = 0 := by
    have hm := BlochNormalization.hasDerivAt_mobius hcn
      (mem_ball_zero_iff.mp (hLmap (mem_ball_self zero_lt_one)))
    simpa only [mul_zero, H, Function.comp_def] using (hm.comp 0 hL1).deriv
  have hD0 : D 0 = 1 - c^2 := by simp [D, hL0, pow_two]
  have hD1 : deriv D 0 = 0 := by simpa [D] using (hL1.const_mul c |>.const_sub 1).deriv
  have hD : DifferentiableOn ℂ D (ball 0 1) :=
    (hL.const_mul c).const_sub 1
  have hEq : (fun w => H w * D w) =ᶠ[𝓝 0] (fun w => L w - c) := by
    filter_upwards [ball_mem_nhds (0 : ℂ) zero_lt_one] with z hz
    have hd : D z ≠ 0 := by
      simpa [D, hcc, sub_eq_add_neg] using BlochNormalization.denom_ne hcn
        (mem_ball_zero_iff.mp (hLmap hz))
    have he : H z = (L z - c) / D z := by
      simp [H, D, BlochNormalization.mobius, hcc, sub_eq_add_neg]
    rw [he, div_mul_cancel₀ _ hd]
  have hder := hEq.iteratedDeriv_eq 3
  have ho : (0 : ℂ) ∈ ball 0 1 := mem_ball_self zero_lt_one
  have hHd : ContDiffAt ℂ 3 H 0 := (hH.analyticOnNhd isOpen_ball 0 ho).contDiffAt
  have hDd : ContDiffAt ℂ 3 D 0 := (hD.analyticOnNhd isOpen_ball 0 ho).contDiffAt
  have hLd : ContDiffAt ℂ 3 L 0 := (hL.analyticOnNhd isOpen_ball 0 ho).contDiffAt
  rw [iteratedDeriv_fun_mul hHd hDd] at hder
  have hright : iteratedDeriv 3 (fun w => L w - c) 0 = iteratedDeriv 3 L 0 := by
    rw [show (fun w => L w - c) = L - fun _ => c by rfl]
    rw [iteratedDeriv_sub hLd contDiffAt_const]
    simp [iteratedDeriv_succ']
  rw [hright] at hder
  have hL3 : iteratedDeriv 3 L 0 = c * s^3 * iteratedDeriv 3 f 0 := by
    have hd : DifferentiableOn ℂ (fun z => f (s*z)) (ball 0 1) :=
      hf.comp (fun z _ => (hld z).differentiableAt.differentiableWithinAt) hscale
    have hcd : ContDiffAt ℂ 3 (fun z => f (s*z)) 0 :=
      (hd.analyticOnNhd isOpen_ball 0 ho).contDiffAt
    have hfcd : ContDiffOn ℂ 3 f (ball 0 1) :=
      fun z hz => (hf.analyticOnNhd isOpen_ball z hz).contDiffAt.contDiffWithinAt
    have hfc : ContDiffAt ℂ 3 f 0 := (hf.analyticOnNhd isOpen_ball 0 ho).contDiffAt
    have huniq : UniqueDiffOn ℂ (ball (0 : ℂ) 1) := isOpen_ball.uniqueDiffOn
    have he := iteratedDerivWithin_comp_const_smul (x := (0 : ℂ)) ho huniq hfcd s hscale
    rw [mul_zero, iteratedDerivWithin_eq_iteratedDeriv huniq hcd ho,
      iteratedDerivWithin_eq_iteratedDeriv huniq hfc ho, smul_eq_mul] at he
    change iteratedDeriv 3 (fun z => c * f (s*z)) 0 = _
    rw [iteratedDeriv_const_mul_field, he]
    ring
  have hId : iteratedDeriv 3 H 0 * (1-c^2) = c*s^3*iteratedDeriv 3 f 0 := by
    rw [hL3] at hder
    norm_num [Finset.sum_range_succ, hH0, hH1, hD0, hD1] at hder
    norm_num [c, s]
    exact hder
  have hh := small_coeff H hH hH0 hH1 hHmap
  have hnn := congrArg norm hId
  have hnC : ‖1 - c^2‖ = 56/81 := by
    rw [show 1 - c^2 = ((56/81 : ℝ) : ℂ) by norm_num [c], Complex.norm_real]
    norm_num
  rw [norm_mul, hnC, norm_mul, norm_mul, norm_pow, hs, hc] at hnn
  let R : ℝ≥0 := 19/20
  have hF_R : DifferentiableOn ℂ f (closedBall 0 R) := hf.mono
    (closedBall_subset_ball (by norm_num [R]))
  have hw := congrArg norm (coeff_eq_iteratedDeriv (R := R) (by norm_num [R]) hF_R 3)
  norm_num [norm_mul, R] at hw
  rw [← hw] at hnn
  nlinarith

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

theorem primitive_series {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F (ball 0 1))
    (hF0 : F 0 = 0) {z : ℂ} (hz : ‖z‖ < 19 / 20) :
    HasSum (fun k => (cauchyPowerSeries (deriv F) 0 (19/20)).coeff k * z^(k+1) /
      (k + 1 : ℕ)) (F z) := by
  let R : ℝ≥0 := 19/20
  have hR : 0 < R := by norm_num [R]
  have hr : closedBall (0 : ℂ) R ⊆ ball 0 1 := closedBall_subset_ball (by norm_num [R])
  have hFR := hF.mono hr
  have hDR := (hF.deriv isOpen_ball).mono hr
  let a := fun n => (cauchyPowerSeries F 0 R).coeff n
  let b := fun n => (cauchyPowerSeries (deriv F) 0 R).coeff n
  have ha0 : a 0 = 0 := (coef_const hR hFR).trans hF0
  have he (n : ℕ) : a (n+1) = b n / (n+1 : ℕ) := by
    have h₁ := coeff_eq_iteratedDeriv hR hFR (n+1)
    have h₂ := coeff_eq_iteratedDeriv hR hDR n
    rw [iteratedDeriv_succ', ← h₂, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ] at h₁
    have hn : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    have hnn : ((n+1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
    apply (eq_div_iff hnn).mpr
    apply mul_left_cancel₀ hn
    rw [← h₁]
    push_cast
    ring
  have hs : HasSum (fun k => a k*z^k) (F z) :=
    BlochCoefficients.hasSum_coeff F hR hFR (show ‖z‖ < R from hz)
  have htail := (hasSum_nat_add_iff' 1).mpr hs
  change HasSum (fun k => b k*z^(k+1)/(k+1 : ℕ)) (F z)
  simpa only [Finset.sum_range_one, ha0, zero_mul, sub_zero, he, div_mul_eq_mul_div] using htail

end BlochLowCoefficients

/-
A rational dual certificate for a radial lower bound. The test constraints and radial objective
are obtained by the linear-programming method of Wikström (arXiv:2608.17660, Theorem 3.2).
The test points and multipliers below come from a separate numerical search.
-/

open scoped BigOperators

namespace BlochCertificate

structure Test where
  x : ℤ
  y : ℤ
  u : ℕ
  turn : ℕ
  q : ℕ
  weight : ℕ

def tests : List Test := [
  ⟨12, 8, 5, 3, 722, 19172655⟩,
  ⟨(-15), 4, 8, 0, 777, 59611⟩,
  ⟨9, 9, 8, 3, 637, 125172814⟩,
  ⟨(-9), 13, 4, 3, 791, 334957⟩,
  ⟨8, 9, 8, 3, 603, 172579750⟩,
  ⟨(-3), 16, 9, 0, 814, 193233⟩,
  ⟨13, 7, 4, 3, 739, 95243006⟩,
  ⟨(-13), 7, 3, 0, 739, 270795⟩,
  ⟨(-14), 6, 4, 0, 762, 1223326⟩,
  ⟨(-10), 12, 6, 3, 782, 603332⟩,
  ⟨16, 2, 4, 2, 807, 43239787⟩,
  ⟨(-2), 16, 6, 0, 807, 362302⟩,
  ⟨1, 15, 2, 0, 752, 1758728⟩,
  ⟨0, 15, 3, 0, 750, 139650⟩,
  ⟨5, 8, 9, 3, 472, 658683181⟩,
  ⟨16, 1, 2, 2, 802, 68022339⟩,
  ⟨(-11), 9, 0, 0, 711, 2861662⟩,
  ⟨15, 4, 0, 3, 777, 137316309⟩,
  ⟨11, 8, 6, 3, 681, 215759624⟩,
  ⟨(-16), 0, 0, 2, 800, 186405⟩,
  ⟨4, 7, 9, 3, 404, 587082651⟩,
  ⟨14, 6, 3, 3, 762, 96785916⟩,
  ⟨(-16), 3, 1, 1, 814, 420800⟩,
  ⟨(-7), 15, 6, 2, 828, 276610⟩,
  ⟨(-12), 8, 1, 0, 722, 540103⟩,
  ⟨15, 5, 1, 3, 791, 2459604⟩,
  ⟨4, 16, 6, 3, 825, 208748⟩]

def Test.zre (t : Test) : ℚ := t.x / 20

def Test.zim (t : Test) : ℚ := t.y / 20

def Test.phase (t : Test) : ℚ × ℚ :=
  let x := (100 - (t.u : ℚ)^2) / (100 + (t.u : ℚ)^2)
  let y := 20 * (t.u : ℚ) / (100 + (t.u : ℚ)^2)
  match t.turn with
  | 0 => (x, y)
  | 1 => (-y, x)
  | 2 => (-x, -y)
  | _ => (y, -x)

def Test.weightRat (t : Test) : ℚ := t.weight / 10000000000

def Test.rho (t : Test) : ℚ := t.q / 1000

def Test.discWeight (t : Test) : ℚ := 1 - t.zre^2 - t.zim^2

def gaussianPowers (x y : ℚ) : ℕ → ℚ × ℚ
  | 0 => (1, 0)
  | n + 1 =>
    let p := gaussianPowers x y n
    (x * p.1 - y * p.2, x * p.2 + y * p.1)

def Test.feature (t : Test) (k : ℕ) : ℚ :=
  let p := gaussianPowers t.zre t.zim k
  t.discWeight * (p.1 * t.phase.1 + p.2 * t.phase.2)

def tail (q : ℚ) : ℚ := (400 / 39) * ((20 / 19) * q)^33 / (1 - (20 / 19) * q)

def Test.rhs (t : Test) : ℚ := 1 - t.discWeight * t.phase.1 + t.discWeight * tail t.rho

def radius : ℚ := 57735 / 100000

def coeffBound (k : ℕ) : ℚ :=
  if k = 2 then 1 else if k = 3 then 21 / 5 else (400 / 39) * (20 / 19)^k

def target (k : ℕ) : ℚ :=
  -(radius^(k+1) / (k+1)) + (if k = 2 then 9 / 200 else if k = 3 then 13 / 2000 else 0)

def residual (k : ℕ) : ℚ :=
  target k - (∑ i : Fin tests.length, (tests.get i).weightRat * (tests.get i).feature k)

def totalError : ℚ :=
  (∑ i : Fin tests.length, (tests.get i).weightRat * (tests.get i).rhs) +
    (∑ k : Fin 31, coeffBound (k.val + 2) * |residual (k.val + 2)|) + radius * tail radius

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem numeric : (4833 : ℚ) / 10000 ≤ radius - totalError := by
  decide +kernel

set_option maxRecDepth 30000 in
theorem row_valid (i : Fin tests.length) :
    let t := tests.get i
    0 ≤ t.rho ∧ t.rho < 19/20 ∧ t.zre^2 + t.zim^2 ≤ t.rho^2 ∧
      t.phase.1^2 + t.phase.2^2 = 1 := by
  revert i
  decide +kernel

theorem Test.weight_nonneg (t : Test) : 0 ≤ t.weightRat := by
  unfold weightRat
  positivity

theorem radial_lower_of_tests (b : ℕ → ℝ) (L : ℝ)
    (hb : ∀ k : Fin 31, |b (k.val + 2)| ≤ (coeffBound (k.val + 2) : ℝ))
    (ht : ∀ i : Fin tests.length,
      (∑ k : Fin 31, ((tests.get i).feature (k.val + 2) : ℝ) * b (k.val + 2)) ≤
        ((tests.get i).rhs : ℝ))
    (hL : (radius : ℝ) + (∑ k : Fin 31, ((radius ^ (k.val + 3)) / (k.val + 3) : ℚ) *
        b (k.val + 2)) - ((radius * tail radius : ℚ) : ℝ) ≤ L) :
    (4833 : ℝ) / 10000 + (9 / 200) * b 2 + (13 / 2000) * b 3 ≤ L := by
  have hnum : (4833 : ℝ) / 10000 ≤ (radius : ℝ) - (totalError : ℝ) := by
    have h : (((4833 : ℚ) / 10000 : ℚ) : ℝ) ≤ ((radius - totalError : ℚ) : ℝ) :=
      Rat.cast_le.mpr numeric
    push_cast at h
    exact h
  have hres : (∑ k : Fin 31, (residual (k.val + 2) : ℝ) * b (k.val + 2)) ≤
      (∑ k : Fin 31, (coeffBound (k.val + 2) * |residual (k.val + 2)| : ℚ) : ℝ) := by
    push_cast
    exact Finset.sum_le_sum fun k _ => calc
      _ ≤ |(residual (k.val + 2) : ℝ) * b (k.val + 2)| := le_abs_self _
      _ = |(residual (k.val + 2) : ℝ)| * |b (k.val + 2)| := abs_mul _ _
      _ ≤ _ := by rw [mul_comm]; exact mul_le_mul_of_nonneg_right (hb k) (abs_nonneg _)
  have htests := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin tests.length)))
    (fun i _ => mul_le_mul_of_nonneg_left (ht i)
      (show 0 ≤ ((tests.get i).weightRat : ℝ) from Rat.cast_nonneg.mpr (tests.get i).weight_nonneg))
  have heq :
      (∑ k : Fin 31, (target (k.val + 2) : ℝ) * b (k.val + 2)) =
      (∑ k : Fin 31, (residual (k.val + 2) : ℝ) * b (k.val + 2)) +
      (∑ i : Fin tests.length, ((tests.get i).weightRat : ℝ) *
        ∑ k : Fin 31, ((tests.get i).feature (k.val + 2) : ℝ) * b (k.val + 2)) := by
    conv_rhs =>
      arg 2
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [residual]
    push_cast
    simp only [sub_mul, Finset.sum_mul, mul_assoc, sub_add_cancel]
  have hlin₁ :
      (∑ k : Fin 31, (if k.val + 2 = 2 then (9 / 200 : ℝ) * b (k.val + 2) else 0)) =
        (9 / 200 : ℝ) * b 2 := by
    rw [Finset.sum_eq_single (0 : Fin 31)]
    · rfl
    · intro k _ hk
      have hv : k.val ≠ 0 := fun h => hk (Fin.ext h)
      simp [hv]
    · simp
  have hlin₂ :
      (∑ k : Fin 31, (if k.val + 2 = 3 then (13 / 2000 : ℝ) * b (k.val + 2) else 0)) =
        (13 / 2000 : ℝ) * b 3 := by
    rw [Finset.sum_eq_single (1 : Fin 31)]
    · rfl
    · intro k _ hk
      have hv : k.val + 2 ≠ 3 := fun h => hk (Fin.ext (by omega))
      simp only [hv, if_false]
    · simp
  have htar :
      (∑ k : Fin 31, (target (k.val + 2) : ℝ) * b (k.val + 2)) =
        -(∑ k : Fin 31, ((radius ^ (k.val + 3)) / (k.val + 3) : ℚ) * b (k.val + 2)) +
          (9 / 200 : ℝ) * b 2 + (13 / 2000 : ℝ) * b 3 := by
    rw [← hlin₁, ← hlin₂, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    unfold target
    push_cast
    split_ifs <;> first | omega | ring
  unfold totalError at hnum
  rw [htar] at heq
  push_cast at hnum hL hres heq htests
  linarith

end BlochCertificate

namespace BlochAnalyticCertificate

open BlochCertificate
open scoped BigOperators NNReal ENNReal

private theorem projection_error {x y u : ℂ} (hu : ‖u‖ = 1) :
    |(x * conj u).re - (y * conj u).re| ≤ ‖x-y‖ := by
  have h := Complex.abs_re_le_norm ((x-y)*conj u)
  rw [norm_mul, Complex.norm_conj, hu, mul_one, sub_mul, Complex.sub_re] at h
  exact h

private theorem gauss_coordinates (x y : ℚ) (n : ℕ) :
    ((⟨↑x, ↑y⟩ : ℂ)^n).re = ((gaussianPowers x y n).1 : ℝ) ∧
      ((⟨↑x, ↑y⟩ : ℂ)^n).im = ((gaussianPowers x y n).2 : ℝ) := by
  induction n with
  | zero => norm_num [gaussianPowers]
  | succ n ih =>
    rw [pow_succ']
    rcases ih with ⟨hr, hi⟩
    simp only [Complex.mul_re, Complex.mul_im, hr, hi, gaussianPowers, Rat.cast_sub,
      Rat.cast_add, Rat.cast_mul]
    trivial

private theorem rotated_symm_sum (A : ℕ → ℂ) (f : ℂ → ℂ)
    (hs : ∀ z, ‖z‖ < 19/20 → HasSum (fun k => A k*z^k) (f z))
    (ξ z : ℂ) (hξ : ‖ξ‖ = 1) (hz : ‖z‖ < 19/20) :
    HasSum (fun k => (↑(A k*ξ^k).re : ℂ)*z^k)
      ((f (ξ*z) + conj (f (ξ*conj z)))/2) := by
  have h₁ := hs (ξ*z) (by simpa [norm_mul, hξ] using hz)
  have h₂ := Complex.hasSum_conj'.2 (hs (ξ*conj z) (by simpa [norm_mul, hξ] using hz))
  have h₃ := (h₁.add h₂).mul_left (1/2 : ℂ)
  have he (k : ℕ) : (1/2 : ℂ) * (A k * (ξ*z)^k + conj (A k * (ξ*conj z)^k)) =
      ((A k*ξ^k).re : ℂ)*z^k := by
    have hd (a : ℂ) : a + conj a = 2 * (a.re : ℂ) := by
      apply Complex.ext
      · simp only [Complex.add_re, Complex.conj_re, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, mul_zero, sub_zero, Complex.re_ofNat]
        ring
      · simp [Complex.add_im, Complex.conj_im, Complex.mul_im]
    have hf₁ : A k*(ξ*z)^k = (A k*ξ^k)*z^k := by rw [mul_pow, mul_assoc]
    have hf₂ : conj (A k*(ξ*conj z)^k) = (conj (A k*ξ^k))*z^k := by
      simp only [mul_pow, map_mul, map_pow, starRingEnd_self_apply, mul_assoc]
    rw [hf₁, hf₂, ← add_mul, hd (A k*ξ^k)]
    ring
  have heq : (fun i => (1 / 2 : ℂ) * (A i * (ξ*z)^i + conj (A i * (ξ*conj z)^i))) =
      (fun k => ((A k*ξ^k).re : ℂ)*z^k) := funext he
  rw [heq] at h₃
  have hval : (1/2 : ℂ) * (f (ξ*z) + conj (f (ξ*conj z))) =
      (f (ξ*z) + conj (f (ξ*conj z)))/2 := by ring
  rw [hval] at h₃
  exact h₃

private theorem row_inequality {f : ℂ → ℂ} {A : ℕ → ℂ}
    (hs : ∀ z, ‖z‖ < 19/20 → HasSum (fun k => A k * z^k) (f z))
    (hA : ∀ k, ‖A k‖ ≤ (400/39) * (20/19 : ℝ)^k)
    (ha0 : A 0 = 1) (ha1 : A 1 = 0)
    (hf : ∀ z ∈ ball (0 : ℂ) 1, (1-‖z‖^2)*‖f z‖ ≤ 1)
    {ξ : ℂ} (hξ : ‖ξ‖=1) (i : Fin tests.length) :
    (∑ k : Fin 31, ((tests.get i).feature (k.val + 2) : ℝ) * (A (k.val+2)*ξ^(k.val+2)).re)
      ≤ ((tests.get i).rhs : ℝ) := by
  let t := tests.get i
  let q : ℝ := t.rho
  let z : ℂ := ⟨(t.zre : ℝ), (t.zim : ℝ)⟩
  let v : ℂ := ⟨(t.phase.1 : ℝ), (t.phase.2 : ℝ)⟩
  let b : ℕ → ℝ := fun k => (A k*ξ^k).re
  have hval := row_valid i
  have hq0 : 0 ≤ q := Rat.cast_nonneg.mpr hval.1
  have hq1' : t.rho < (19 / 20 : ℚ) := hval.2.1
  have hq1 : q < 19/20 := by
    have h : (t.rho : ℝ) < ((19/20 : ℚ) : ℝ) := Rat.cast_lt.mpr hq1'
    norm_num at h
    exact h
  have hzq : ‖z‖ ≤ q := by
    have hq : ((t.zre^2 + t.zim^2 : ℚ) : ℝ) ≤ ((t.rho^2 : ℚ) : ℝ) :=
      Rat.cast_le.mpr hval.2.2.1
    push_cast at hq
    have hz : ‖z‖^2 = (t.zre : ℝ)^2 + (t.zim : ℝ)^2 := by
      rw [Complex.sq_norm]
      simp [z, Complex.normSq_apply, pow_two]
    nlinarith [norm_nonneg z]
  have hv : ‖v‖ = 1 := by
    have h := congrArg (fun a : ℚ => (a : ℝ)) hval.2.2.2
    push_cast at h
    have hv : ‖v‖^2 = (t.phase.1 : ℝ)^2 + (t.phase.2 : ℝ)^2 := by
      rw [Complex.sq_norm]
      simp [v, Complex.normSq_apply, pow_two]
    nlinarith [norm_nonneg v]
  have hz1 : ‖z‖ < 1 := hzq.trans_lt (hq1.trans (by norm_num))
  have hw : (t.discWeight : ℝ) = 1 - ‖z‖^2 := by
    rw [Complex.sq_norm]
    simp [Test.discWeight, z, Complex.normSq_apply, pow_two]
    ring
  have hw0 : 0 ≤ (t.discWeight : ℝ) := by rw [hw]; nlinarith [norm_nonneg z]
  let Fz := (f (ξ*z) + conj (f (ξ*conj z)))/2
  have hseries : HasSum (fun k => (b k : ℂ)*z^k) Fz :=
    rotated_symm_sum A f hs ξ z hξ (hzq.trans_lt hq1)
  have hQ : (20/19 : ℝ)*q < 1 := by linarith
  have hNorm (k : ℕ) : ‖(b k : ℂ)*z^k‖ ≤ (400/39)*((20/19)*q)^k := by
    have hh := Complex.abs_re_le_norm (A k*ξ^k)
    rw [norm_mul, norm_pow, hξ, one_pow, mul_one] at hh
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, mul_pow, ← mul_assoc]
    exact mul_le_mul (hh.trans (hA k)) (pow_le_pow_left₀ (norm_nonneg z) hzq k)
      (pow_nonneg (norm_nonneg z) k) (by positivity)
  have herr := BlochTails.truncation hseries (by positivity : 0 ≤ (20/19 : ℝ)*q) hQ hNorm 33
  rw [BlochTails.split33] at herr
  have hconst : b 0 = 1 := by simp [b, ha0]
  have hlin : b 1 = 0 := by simp [b, ha1]
  simp only [hconst, hlin, Complex.ofReal_one, Complex.ofReal_zero, pow_zero, mul_one, zero_mul,
    add_zero] at herr
  let P : ℂ := 1 + ∑ k : Fin 31, (b (k.val+2) : ℂ)*z^(k.val+2)
  have hcast : (tail t.rho : ℝ) = (400/39)*((20/19)*q)^33/(1-(20/19)*q) := by
    unfold tail
    push_cast
    rfl
  have he : ‖Fz-P‖ ≤ (tail t.rho : ℝ) := hcast.symm ▸ herr
  have hFz : (t.discWeight : ℝ)*‖Fz‖ ≤ 1 := by
    have hξz : ‖ξ*z‖ = ‖z‖ := by rw [norm_mul, hξ, one_mul]
    have hξz' : ‖ξ*conj z‖ = ‖z‖ := by rw [norm_mul, Complex.norm_conj, hξ, one_mul]
    have h₁ := hf (ξ*z) (mem_ball_zero_iff.mpr (hξz.symm ▸ hz1))
    have h₂ := hf (ξ*conj z) (mem_ball_zero_iff.mpr (hξz'.symm ▸ hz1))
    rw [hξz, ← hw] at h₁
    rw [hξz', ← hw] at h₂
    have hN : ‖Fz‖ ≤ (‖f (ξ*z)‖ + ‖f (ξ*conj z)‖)/2 := by
      rw [show Fz = (f (ξ*z) + conj (f (ξ*conj z)))/2 by rfl, norm_div]
      norm_num
      simpa only [Complex.norm_conj] using
        div_le_div_of_nonneg_right (norm_add_le (f (ξ*z)) (conj (f (ξ*conj z)))) (by norm_num : 0 ≤ (2 : ℝ))
    have hN' := mul_le_mul_of_nonneg_left hN hw0
    rw [← mul_div_assoc, mul_add] at hN'
    linarith
  have hproj := (projection_error (x := Fz) (y := P) hv).trans he
  have hP : (P * conj v).re ≤ ‖Fz‖ + (tail t.rho : ℝ) := by
    have hR : (Fz * conj v).re ≤ ‖Fz‖ := by
      simpa only [norm_mul, Complex.norm_conj, hv, mul_one] using (Complex.re_le_norm (Fz*conj v))
    linarith [(neg_le_abs ((Fz*conj v).re - (P*conj v).re)).trans hproj]
  have hform : (t.discWeight : ℝ)*(P*conj v).re =
      (t.discWeight : ℝ)*(t.phase.1 : ℝ) +
      ∑ k : Fin 31, (t.feature (k.val+2) : ℝ)*b (k.val+2) := by
    simp only [P, add_mul, one_mul, Finset.sum_mul, Complex.add_re, Complex.conj_re,
      Complex.re_sum, v, mul_add, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    have hc := gauss_coordinates t.zre t.zim (k.val+2)
    change (z^(k.val+2)).re = _ ∧ (z^(k.val+2)).im = _ at hc
    simp only [Test.feature, Rat.cast_mul, Rat.cast_add, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.conj_re,
      Complex.conj_im, hc.1, hc.2]
    ring
  have hh := mul_le_mul_of_nonneg_left hP hw0
  rw [hform, mul_add] at hh
  change ∑ k : Fin 31, (t.feature (k.val+2) : ℝ)*b (k.val+2) ≤ (t.rhs : ℝ)
  unfold Test.rhs
  push_cast
  linarith

set_option maxHeartbeats 1500000 in
theorem radial {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F (ball 0 1))
    (hF0 : F 0 = 0) (hF1 : deriv F 0 = 1)
    (hW : ∀ z ∈ ball (0 : ℂ) 1, (1-‖z‖^2)*‖deriv F z‖ ≤ 1)
    {ξ : ℂ} (hξ : ‖ξ‖=1) :
    let a := fun k => (cauchyPowerSeries (deriv F) 0 (19/20)).coeff k
    (4833 : ℝ)/10000 + 9/200*(a 2*ξ^2).re + 13/2000*(a 3*ξ^3).re ≤
      (F ((radius : ℝ)*ξ)*conj ξ).re := by
  let a := fun k => (cauchyPowerSeries (deriv F) 0 (19/20)).coeff k
  let b : ℕ → ℝ := fun k => (a k*ξ^k).re
  let r : ℝ := radius
  let z : ℂ := (r : ℂ)*ξ
  change (4833 : ℝ)/10000 + 9/200*b 2 + 13/2000*b 3 ≤ (F z*conj ξ).re
  have hr0 : 0 < r := by norm_num [r, radius]
  have hr1 : r < 19/20 := by norm_num [r, radius]
  have hz : ‖z‖ = r := by simp [z, hξ, abs_of_pos hr0]
  have hf := hF.deriv isOpen_ball
  let R : ℝ≥0 := 19/20
  have hR : 0 < R := by norm_num [R]
  have hfR := hf.mono (closedBall_subset_ball (show (R : ℝ) < 1 by norm_num [R]))
  have ha0 : a 0 = 1 := (BlochLowCoefficients.coef_const hR hfR).trans hF1
  have ha1 : a 1 = 0 := (BlochLowCoefficients.coef_first hR hfR).trans
    (BlochDistortion.deriv_zero_of_weight hf hF1 hW)
  have hA (k : ℕ) : ‖a k‖ ≤ (400/39)*(20/19 : ℝ)^k :=
    BlochCoefficients.radius95_coeff_bound hf hW k
  have h2 : ‖a 2‖ ≤ 1 := BlochLowCoefficients.second hf hF1 hW
  have h3 : ‖a 3‖ ≤ 21/5 := BlochLowCoefficients.third hf hF1 hW
  have hb (k : Fin 31) : |b (k.val+2)| ≤ (coeffBound (k.val+2) : ℝ) := by
    have hh : |b (k.val+2)| ≤ ‖a (k.val+2)‖ := by
      have h := Complex.abs_re_le_norm (a (k.val+2)*ξ^(k.val+2))
      rw [norm_mul, norm_pow, hξ, one_pow, mul_one] at h
      exact h
    unfold coeffBound
    split_ifs with hk hk'
    · rw [hk] at hh ⊢
      norm_num
      exact hh.trans h2
    · rw [hk'] at hh ⊢
      push_cast
      exact hh.trans h3
    · push_cast
      exact hh.trans (hA _)
  have ht := row_inequality (f := deriv F) (A := a)
    (fun w hw => BlochCoefficients.hasSum_coeff (deriv F) hR hfR hw) hA ha0 ha1 hW hξ
  apply radial_lower_of_tests b ((F z*conj ξ).re) hb ht
  have hs : HasSum (fun k => a k*z^(k+1)/(k+1 : ℕ)) (F z) :=
    BlochLowCoefficients.primitive_series hF hF0 (z := z) (hz.symm ▸ hr1)
  have hN (k : ℕ) : ‖a k * z^(k+1) / (k+1 : ℕ)‖ ≤
      ((400/39)*r)*((20/19)*r)^k := by
    have hk : (1 : ℝ) ≤ ((k+1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
    rw [norm_div, norm_mul, norm_pow, hz, Complex.norm_natCast]
    have hh : ‖a k‖*r^(k+1) ≤ ((400/39)*r)*((20/19)*r)^k := by
      rw [pow_succ, mul_pow]
      have he := mul_le_mul_of_nonneg_right (hA k) (show 0 ≤ r^k*r by positivity)
      simpa only [mul_assoc, mul_left_comm, mul_comm] using he
    exact ((div_le_iff₀ (zero_lt_one.trans_le hk)).mpr
      (le_mul_of_one_le_right (by positivity) hk)).trans hh
  have hq : (20 / 19 : ℝ)*r < 1 := by linarith
  have he := BlochTails.truncation hs (by positivity : 0 ≤ (20/19 : ℝ)*r) hq hN 33
  rw [BlochTails.split33] at he
  have hproj := (projection_error (x := F z) hξ).trans he
  have hconj : ξ * conj ξ = 1 := by rw [Complex.mul_conj, ← Complex.sq_norm, hξ]; norm_num
  have hterm (k : ℕ) : ((a k*z^(k+1)/(k+1 : ℕ))*conj ξ).re =
      r^(k+1)/((k+1 : ℕ) : ℝ)*b k := by
    have hv : (a k*z^(k+1)/(k+1 : ℕ))*conj ξ =
        (↑(r^(k+1)/((k+1 : ℕ) : ℝ)) : ℂ)*(a k*ξ^k) := by
      have hm : ξ^ (k+1)*conj ξ = ξ^k := by rw [pow_succ, mul_assoc, hconj, mul_one]
      push_cast
      simp only [z, mul_pow, div_mul_eq_mul_div]
      rw [mul_assoc (a k) _ _, mul_assoc ((r : ℂ)^(k+1)) _ _, hm]
      ring
    rw [hv]
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  simp only [add_mul, Finset.sum_mul, Complex.add_re, Complex.re_sum, hterm] at hproj
  have hb0 : b 0 = 1 := by simp [b, ha0]
  have hb1 : b 1 = 0 := by simp [b, ha1]
  simp only [hb0, hb1, Nat.reduceAdd, Nat.cast_one, pow_one, div_one, mul_one,
    mul_zero, add_zero] at hproj
  have hS : (∑ k : Fin 31, ((radius^(k.val+3) / (k.val+3) : ℚ) : ℝ) * b (k.val+2)) =
      (∑ k : Fin 31, r^((k.val+2)+1)/((k.val+2+1 : ℕ) : ℝ)*b (k.val+2)) := by
    apply Finset.sum_congr rfl
    intro k _
    push_cast
    rw [show (k.val : ℝ) + 2 + 1 = (k.val : ℝ) + 3 by ring]
  have hE : ((radius * tail radius : ℚ) : ℝ) = (400/39)*r*((20/19)*r)^33/(1-(20/19)*r) := by
    unfold tail
    push_cast
    change r * ((400 / 39) * ((20 / 19) * r) ^ 33 / (1 - (20 / 19) * r)) = _
    ring
  change r + (∑ k : Fin 31, ((radius^(k.val+3) / (k.val+3) : ℚ) : ℝ) * b (k.val+2)) -
    ((radius * tail radius : ℚ) : ℝ) ≤ (F z*conj ξ).re
  rw [hS, hE]
  linarith only [(neg_le_abs _).trans hproj]

end BlochAnalyticCertificate

namespace BlochGeometry

private theorem injOn_of_positive_deriv {F : ℂ → ℂ} {r : ℝ}
    (hF : DifferentiableOn ℂ F (ball 0 r))
    (hpos : ∀ z ∈ ball (0 : ℂ) r, 0 < (deriv F z).re) : InjOn F (ball 0 r) := by
  intro x hx y hy he
  by_contra hxy
  have hne : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
  let l : ℂ → ℂ := fun z => x + (y - x) * z
  let q : ℂ → ℂ := fun z => F (l z) / (y - x)
  have hs (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : l t ∈ ball 0 r := by
    have hm := convex_ball (0 : ℂ) r hx hy
      (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel (1 : ℝ) t)
    convert hm using 1
    simp only [l, Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_one]
    ring
  have hq (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun s : ℝ => (q s).re) (deriv F (l t)).re t := by
    have hld : HasDerivAt l (y - x) (t : ℂ) := by
      simpa [l] using ((hasDerivAt_id (t : ℂ)).const_mul (y - x)).const_add x
    have hFd := (hF.differentiableAt (isOpen_ball.mem_nhds (hs t ht))).hasDerivAt
    have hqd : HasDerivAt q (deriv F (l t)) (t : ℂ) := by
      have h := (hFd.comp (t : ℂ) hld).div_const (y - x)
      simpa [q, Function.comp_def, hne] using h
    exact hqd.real_of_complex
  have hmono : StrictMonoOn (fun t : ℝ => (q t).re) (Icc 0 1) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc _ _) (fun t ht => (hq t ht).continuousAt.continuousWithinAt) ?_
    intro t ht
    exact (hq t (interior_subset ht)).deriv ▸ hpos (l t) (hs t (interior_subset ht))
  have hlt := hmono (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one) zero_lt_one
  simp [q, l, he] at hlt

/-- A positive real part of the derivative and a separating boundary projection give a
schlicht disk. This is the geometric implication in Wikström, Lemma 2.3
(arXiv:2608.17660). -/
theorem covers_of_boundary_projection {F : ℂ → ℂ} {r B : ℝ} {c : ℂ}
    (hr : 0 < r) (hr1 : r < 1)
    (hF : DifferentiableOn ℂ F (ball 0 1)) (hF0 : F 0 = 0)
    (hpos : ∀ z ∈ ball (0 : ℂ) r, 0 < (deriv F z).re)
    (hc : ‖c‖ < B)
    (hbd : ∀ z ∈ sphere (0 : ℂ) r, B ≤ ((F z - c) * conj (z / (r : ℂ))).re) :
    BlochNormalization.Covers F B := by
  have hinj := injOn_of_positive_deriv (hF.mono (ball_subset_ball hr1.le)) hpos
  let U := F '' ball (0 : ℂ) r
  have hU : IsOpen U := by
    have hF' := hF.analyticOnNhd isOpen_ball
    rcases (hF'.mono (ball_subset_ball hr1.le)).is_constant_or_isOpen
      (convex_ball (0 : ℂ) r).isPreconnected with ⟨v, hv⟩ | hopen
    · exfalso
      have hzero : (0 : ℂ) ∈ ball 0 r := mem_ball_self hr
      have hn : ∃ x ∈ ball (0 : ℂ) r, x ≠ 0 := by
        refine ⟨(r / 2 : ℝ), ?_, by exact_mod_cast (half_pos hr).ne'⟩
        simpa [abs_of_pos hr] using half_lt_self hr
      obtain ⟨x, hx, hxne⟩ := hn
      exact hxne (hinj hx hzero ((hv x hx).trans (hv 0 hzero).symm))
    · exact hopen _ Subset.rfl isOpen_ball
  have hfront : frontier U ⊆ F '' sphere 0 r := by
    intro w hw
    have hclosed : IsClosed (F '' closedBall 0 r) :=
      ((isCompact_closedBall (0 : ℂ) r).image_of_continuousOn
        (hF.continuousOn.mono (closedBall_subset_ball hr1))).isClosed
    have ho : closure U ⊆ F '' closedBall 0 r :=
      closure_minimal (image_mono ball_subset_closedBall) hclosed
    obtain ⟨z, hz, he⟩ := ho (frontier_subset_closure hw)
    refine ⟨z, ?_, he⟩
    rw [frontier, hU.interior_eq] at hw
    have hn : z ∉ ball (0 : ℂ) r := fun h => hw.2 ⟨z, h, he⟩
    exact mem_sphere.mpr (le_antisymm (mem_closedBall.mp hz) (le_of_not_gt fun h => hn (mem_ball.mpr h)))
  have hsep : Disjoint (frontier U) (ball c B) := by
    refine Set.disjoint_left.mpr ?_
    intro w hw hwb
    obtain ⟨z, hz, rfl⟩ := hfront hw
    have hzn : ‖z / (r : ℂ)‖ = 1 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
        mem_sphere_zero_iff_norm.mp hz, div_self hr.ne']
    have hbound := (hbd z hz).trans (Complex.re_le_norm _)
    simp only [norm_mul, Complex.norm_conj, hzn, mul_one] at hbound
    exact (not_lt_of_ge hbound) (mem_ball_iff_norm.mp hwb)
  have h0U : 0 ∈ U := ⟨0, mem_ball_self hr, hF0⟩
  have h0cb : (0 : ℂ) ∈ ball c B := by simpa [mem_ball_iff_norm] using hc
  have hball : ball c B ⊆ U := by
    let V := ball c B
    let : PreconnectedSpace V := Subtype.preconnectedSpace (convex_ball c B).isPreconnected
    have hm : ({x : V | x.val ∈ U} : Set V) = univ := by
      apply IsClopen.eq_univ
      · exact isClopen_preimage_val hU hsep
      · exact ⟨⟨0, h0cb⟩, h0U⟩
    intro x hx
    have hxm : (⟨x, hx⟩ : V) ∈ ({y : V | y.val ∈ U} : Set V) := by rw [hm]; exact mem_univ _
    exact hxm
  refine ⟨ball 0 r ∩ F ⁻¹' ball c B,
    (hF.continuousOn.mono (ball_subset_ball hr1.le)).isOpen_inter_preimage isOpen_ball isOpen_ball,
    fun _ hz => ball_subset_ball hr1.le hz.1, c, ?_, hinj.mono inter_subset_left⟩
  apply Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact hz.2
  · intro w hw
    obtain ⟨z, hz, he⟩ := hball hw
    exact ⟨z, ⟨hz, by change F z ∈ ball c B; rwa [he]⟩, he⟩

end BlochGeometry

open Complex
open scoped ComplexConjugate

namespace BlochRecentering

private def gap (b t : ℝ) : ℝ :=
  0.05005 - 0.045 * b + 0.09 * b * t

private def residualSq (A t : ℝ) : ℝ :=
  A ^ 2 * t + (16 - 8 * A) * t ^ 2

private theorem gap_pos {b t : ℝ} (hb : 0 ≤ b) (hb1 : b ≤ 1) (ht : 0 ≤ t) :
    0 < gap b t := by
  unfold gap
  nlinarith only [hb1, mul_nonneg hb ht]

private theorem interpolateInterval {lo hi A b : ℝ} (hlo : 0 ≤ lo) (hhi : hi ≤ 1)
    (hlb : lo ≤ b) (hbh : b ≤ hi)
    (hLeft : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → (0.0273 : ℝ)^2 * residualSq A t ≤ (gap lo t)^2)
    (hRight : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → (0.0273 : ℝ)^2 * residualSq A t ≤ (gap hi t)^2) :
    ∀ t : ℝ, 0 ≤ t → t ≤ 1 → (0.0273 : ℝ)^2 * residualSq A t ≤ (gap b t)^2 := by
  intro t ht0 ht1
  have hb0 := hlo.trans hlb
  have hb1 := hbh.trans hhi
  by_cases ht : (1 / 2 : ℝ) ≤ t
  · have hmono : gap lo t ≤ gap b t := by
      dsimp only [gap]
      nlinarith only [mul_nonneg (sub_nonneg.mpr hlb) (sub_nonneg.mpr ht)]
    exact (hLeft t ht0 ht1).trans ((sq_le_sq₀ (gap_pos hlo (hlb.trans hb1) ht0).le
      (gap_pos hb0 hb1 ht0).le).mpr hmono)
  · have hmono : gap hi t ≤ gap b t := by
      dsimp only [gap]
      nlinarith only [mul_nonneg (sub_nonneg.mpr hbh) (sub_nonneg.mpr (le_of_not_ge ht))]
    exact (hRight t ht0 ht1).trans ((sq_le_sq₀ (gap_pos (hb0.trans hbh) hhi ht0).le
      (gap_pos hb0 hb1 ht0).le).mpr hmono)

private theorem recenteringParameter {b : ℝ} (hb0 : 1 / 2 ≤ b) (hb1 : b ≤ 1) :
    ∃ A : ℝ, 0 ≤ A ∧ A ≤ 3 ∧
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 → (0.0273 : ℝ)^2 * residualSq A t ≤ (gap b t)^2 := by
  by_cases h1 : b ≤ 5 / 8
  · refine ⟨1.47, by norm_num, by norm_num, interpolateInterval (by norm_num) (by norm_num) hb0 h1 ?_ ?_⟩
    all_goals
      intro t ht0 ht1
      dsimp only [residualSq, gap]
      nlinarith only [ht0, sq_nonneg t, mul_nonneg ht0 (sub_nonneg.mpr ht1)]
  by_cases h2 : b ≤ 3 / 4
  · refine ⟨1.2, by norm_num, by norm_num,
      interpolateInterval (by norm_num) (by norm_num) (le_of_not_ge h1) h2 ?_ ?_⟩
    all_goals
      intro t ht0 ht1
      dsimp only [residualSq, gap]
      nlinarith only [ht0, sq_nonneg t, mul_nonneg ht0 (sub_nonneg.mpr ht1)]
  by_cases h3 : b ≤ 7 / 8
  · refine ⟨0.96, by norm_num, by norm_num,
      interpolateInterval (by norm_num) (by norm_num) (le_of_not_ge h2) h3 ?_ ?_⟩
    all_goals
      intro t ht0 ht1
      dsimp only [residualSq, gap]
      nlinarith only [ht0, sq_nonneg t, mul_nonneg ht0 (sub_nonneg.mpr ht1)]
  refine ⟨0.73, by norm_num, by norm_num,
    interpolateInterval (by norm_num) (by norm_num) (le_of_not_ge h3) hb1 ?_ ?_⟩
  all_goals
    intro t ht0 ht1
    dsimp only [residualSq, gap]
    nlinarith only [ht0, sq_nonneg t, mul_nonneg ht0 (sub_nonneg.mpr ht1)]

private theorem residual_norm_sq (v : ℂ) (hv : ‖v‖ = 1) (A : ℝ) :
    ‖v ^ 3 - (⟨v.re, (3 - A) * v.im⟩ : ℂ)‖ ^ 2 = residualSq A (v.im ^ 2) := by
  have hs : v.re*v.re + v.im*v.im = 1 := by
    rw [← Complex.normSq_apply, ← Complex.sq_norm, hv, one_pow]
  have hre : (v ^ 3 - (⟨v.re, (3 - A) * v.im⟩ : ℂ)).re = -4 * v.re * v.im ^ 2 := by
    simp only [pow_succ, pow_zero, one_mul, Complex.sub_re, Complex.mul_re, Complex.mul_im]
    linear_combination v.re * hs
  have him : (v ^ 3 - (⟨v.re, (3 - A) * v.im⟩ : ℂ)).im = v.im * (A - 4 * v.im^2) := by
    simp only [pow_succ, pow_zero, one_mul, Complex.sub_im, Complex.mul_re, Complex.mul_im]
    linear_combination (3 * v.im) * hs
  rw [Complex.sq_norm, Complex.normSq_apply, hre, him, residualSq]
  linear_combination (16 * v.im^4) * hs

private theorem normalized_phase (a : ℂ) : ∃ u : ℂ, ‖u‖ = 1 ∧ a * u ^ 2 = -((‖a‖ : ℝ) : ℂ) := by
  by_cases haz : a = 0
  · subst a
    exact ⟨1, by simp, by simp⟩
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (-((‖a‖ : ℝ) : ℂ) / a) (show 0 < 2 by decide)
  have ht : ‖-((‖a‖ : ℝ) : ℂ) / a‖ = 1 := by
    rw [norm_div, norm_neg, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg a),
      div_self (norm_ne_zero_iff.mpr haz)]
  have hnu : ‖u‖ ^ 2 = (1 : ℝ) ^ 2 := by rw [← norm_pow, hu, ht, one_pow]
  refine ⟨u, (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp hnu, ?_⟩
  rw [hu, mul_div_left_comm, div_self haz, mul_one]

private theorem unit_mul_conj {u : ℂ} (hu : ‖u‖ = 1) : u * conj u = 1 := by
  rw [Complex.mul_conj, ← Complex.sq_norm, hu, one_pow, Complex.ofReal_one]

private theorem re_ge_neg_norm (z : ℂ) : -‖z‖ ≤ z.re := by
  have h := Complex.abs_re_le_norm z
  linarith [neg_abs_le z.re]

/-- The second and third boundary harmonics admit a translation preserving the
specified lower radial projection under the stated coefficient bounds. -/
theorem exists_center (a₂ a₃ : ℂ) (ha₂ : ‖a₂‖ ≤ 1) (ha₃ : ‖a₃‖ ≤ 4.2) :
    ∃ c : ℂ, ‖c‖ < 0.43325 ∧ ∀ ξ : ℂ, ‖ξ‖ = 1 →
      0.43325 + (c * conj ξ).re ≤
        0.4833 + 0.045 * (a₂ * ξ ^ 2).re + 0.0065 * (a₃ * ξ ^ 3).re := by
  by_cases hsmall : ‖a₂‖ ≤ 1 / 2
  · refine ⟨0, by norm_num, ?_⟩
    intro ξ hξ
    have h₂ := re_ge_neg_norm (a₂ * ξ ^ 2)
    have h₃ := re_ge_neg_norm (a₃ * ξ ^ 3)
    simp only [norm_mul, norm_pow, hξ, one_pow, mul_one] at h₂ h₃
    simp only [zero_mul, Complex.zero_re, add_zero]
    linarith only [hsmall, ha₃, h₂, h₃]
  obtain ⟨u, hu, halign⟩ := normalized_phase a₂
  obtain ⟨A, hA0, hA3, hgap⟩ := recenteringParameter (le_of_not_ge hsmall) ha₂
  let B : ℂ := ((0.0065 : ℝ) : ℂ) * a₃ * u ^ 3
  let c' : ℂ := ⟨B.re, -((3 - A) * B.im)⟩
  have hB : ‖B‖ ≤ 0.0273 := by
    dsimp only [B]
    rw [norm_mul, norm_mul, norm_pow, hu, one_pow, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (by norm_num : 0 ≤ (0.0065 : ℝ))]
    linarith only [ha₃]
  have hc' : ‖c'‖ ≤ (1 + (3 - A)) * ‖B‖ := by
    calc
      _ ≤ |c'.re| + |c'.im| := Complex.norm_le_abs_re_add_abs_im _
      _ = |B.re| + (3 - A) * |B.im| := by
        change |B.re| + |-((3 - A) * B.im)| = _
        rw [abs_neg, abs_mul, abs_of_nonneg (sub_nonneg.mpr hA3)]
      _ ≤ ‖B‖ + (3 - A) * ‖B‖ := add_le_add (Complex.abs_re_le_norm B)
        (mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm B) (sub_nonneg.mpr hA3))
      _ = _ := by ring
  refine ⟨u * c', ?_, ?_⟩
  · rw [norm_mul, hu, one_mul]
    apply hc'.trans_lt
    have hcb : (1 + (3 - A)) * ‖B‖ ≤ 4 * (0.0273 : ℝ) :=
      mul_le_mul (by linarith only [hA0]) hB (norm_nonneg _) (by norm_num)
    exact hcb.trans_lt (by norm_num)
  intro ξ hξ
  let v := conj u * ξ
  have hv : ‖v‖ = 1 := by
    rw [show ‖v‖ = ‖conj u * ξ‖ from rfl, norm_mul, Complex.norm_conj, hu, hξ, one_mul]
  have huv : u * v = ξ := by
    dsimp only [v]
    rw [← mul_assoc, unit_mul_conj hu, one_mul]
  let L : ℂ := ⟨v.re, (3 - A) * v.im⟩
  let W : ℂ := v ^ 3 - L
  have ht0 : 0 ≤ v.im ^ 2 := sq_nonneg _
  have ht1 : v.im ^ 2 ≤ 1 := by
    have hh := Complex.abs_im_le_norm v
    rw [hv] at hh
    have hv' := (sq_le_sq₀ (abs_nonneg v.im) zero_le_one).mpr hh
    simpa only [sq_abs, one_pow] using hv'
  have hW : (0.0273 : ℝ) * ‖W‖ ≤ gap ‖a₂‖ (v.im ^ 2) := by
    apply (sq_le_sq₀ (mul_nonneg (by norm_num) (norm_nonneg _))
      (gap_pos (norm_nonneg a₂) ha₂ ht0).le).mp
    rw [mul_pow, show ‖W‖ ^ 2 = residualSq A (v.im ^ 2) from residual_norm_sq v hv A]
    exact hgap _ ht0 ht1
  have hBW : -gap ‖a₂‖ (v.im ^ 2) ≤ (B * W).re := by
    calc
      _ ≤ -((0.0273 : ℝ) * ‖W‖) := neg_le_neg hW
      _ ≤ -‖B * W‖ := by
        rw [norm_mul]
        exact neg_le_neg (mul_le_mul_of_nonneg_right hB (norm_nonneg _))
      _ ≤ _ := re_ge_neg_norm _
  have hquad : (a₂ * ξ ^ 2).re = -‖a₂‖ + 2 * ‖a₂‖ * v.im ^ 2 := by
    rw [← huv, mul_pow, ← mul_assoc, halign]
    simp only [pow_two, Complex.mul_re, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, neg_zero, zero_mul, sub_zero]
    have hn : v.re * v.re + v.im * v.im = 1 := by
      rw [← Complex.normSq_apply, ← Complex.sq_norm, hv, one_pow]
    linear_combination (-‖a₂‖) * hn
  have hcubic : (B * v ^ 3).re = 0.0065 * (a₃ * ξ ^ 3).re := by
    have hξpow : ξ ^ 3 = u ^ 3 * v ^ 3 := by
      calc
        _ = (u * v) ^ 3 := congrArg (· ^ 3) huv.symm
        _ = _ := mul_pow _ _ _
    have heq : B * v ^ 3 = ((0.0065 : ℝ) : ℂ) * (a₃ * (u ^ 3 * v ^ 3)) := by
      dsimp only [B]
      ring
    rw [hξpow, heq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hshift : ((u * c') * conj ξ).re = (B * L).re := by
    rw [← huv, map_mul]
    have heq : (u * c') * (conj u * conj v) = c' * conj v := by
      calc
        _ = (u * conj u) * (c' * conj v) := by ring
        _ = _ := by rw [unit_mul_conj hu, one_mul]
    rw [heq]
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    change B.re * v.re - (-((3 - A) * B.im)) * -v.im =
      B.re * v.re - B.im * ((3 - A) * v.im)
    ring
  have hres : (B * W).re = (B * v ^ 3).re - (B * L).re := by
    dsimp only [W]
    rw [mul_sub, Complex.sub_re]
  rw [hshift, hquad, ← hcubic]
  rw [hres] at hBW
  dsimp only [gap] at hBW
  linarith only [hBW]

end BlochRecentering

/-- The improved lower bound follows from the normalized Schwarz–Pick distortion argument
and an independent exact rational certificate in the form of Wikström's radial estimates. -/
theorem OMA.solution : type_of% @Bloch.blochConstant_lower_bound := by
  apply BlochNormalization.normalized_reduction (R := 0.43325)
  · norm_num
    positivity
  · have h := Real.sq_sqrt (by norm_num : 0 ≤ (3 : ℝ))
    have hs : Real.sqrt 3 < (8661 : ℝ)/5000 := by
      by_contra! hn
      nlinarith [sq_nonneg (Real.sqrt 3 - (8661 : ℝ)/5000)]
    norm_num
    linarith
  intro F hF hF0 hF1 hW
  let a := fun k => (cauchyPowerSeries (deriv F) 0 (19/20)).coeff k
  let r : ℝ := BlochCertificate.radius
  have hf := hF.deriv isOpen_ball
  have h₂ : ‖a 2‖ ≤ 1 := BlochLowCoefficients.second hf hF1 hW
  have h₃ : ‖a 3‖ ≤ 4.2 := by
    norm_num
    exact BlochLowCoefficients.third hf hF1 hW
  obtain ⟨c, hc, hproj⟩ := BlochRecentering.exists_center (a 2) (a 3) h₂ h₃
  have hr : 0 < r := by norm_num [r, BlochCertificate.radius]
  have hr1 : r < 1 := by norm_num [r, BlochCertificate.radius]
  have hr0 : r < Real.sqrt (1/3) := by
    have hm := Real.sq_sqrt (by norm_num : 0 ≤ (1 / 3 : ℝ))
    by_contra! h
    have hm' : Real.sqrt (1/3) ≤ r := h
    have hh := mul_le_mul hm' hm' (Real.sqrt_nonneg _) hr.le
    have hv : r^2 < 1/3 := by norm_num [r, BlochCertificate.radius]
    nlinarith
  have hP (z : ℂ) (hz : z ∈ ball 0 r) : 0 < (deriv F z).re :=
    BlochDistortion.positive_re_of_weight hf hF1 hW ((mem_ball_zero_iff.mp hz).trans hr0)
  refine BlochGeometry.covers_of_boundary_projection hr hr1 hF hF0 hP hc ?_
  intro z hz
  let ξ := z / (r : ℂ)
  have hξ : ‖ξ‖=1 := by
    dsimp [ξ]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
      mem_sphere_zero_iff_norm.mp hz, div_self hr.ne']
  have hzξ : (r : ℂ)*ξ = z := by
    dsimp [ξ]
    rw [mul_comm, div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr hr.ne')]
  have hh := BlochAnalyticCertificate.radial hF hF0 hF1 hW hξ
  change (4833 : ℝ)/10000 + 9/200*(a 2*ξ^2).re + 13/2000*(a 3*ξ^3).re ≤
    (F ((r : ℂ)*ξ)*conj ξ).re at hh
  rw [hzξ] at hh
  have hL := hproj ξ hξ
  rw [sub_mul, Complex.sub_re]
  linarith only [hh, hL]