import FormalConjectures.OptimizationConstants.«6a»
import Mathlib

/-!
# Proof of `Constant6a.c6a_lower_bound_improved` (`0.38272 < C6a`)

Self-contained elementary Lean 4 proof of `0.38272 < C6a` (proving `38273 / 100000 ≤ C6a`)
via a finite `2^n`-coin conditionally i.i.d. entropy coupling (Liu's Example 5 with smooth
quadratic perturbation `f(s) = (7/10) * s * (1 - s)` mixed with the independent coupling at
weight `θ = 4/25`), proved via:
1. Exact global log-submodularity `∂²/(∂s ∂t) log h((1-s)(1-t)(1 + (49/100) s t)) ≤ 0` on `(0, 1)^2`,
   established purely algebraically via a 9-term positive Bernstein identity and a 3-square SOS.
2. Three analytical boundary lemmas (corner `u, v ≤ 1/200`, strip `v ≤ 1/10000 ∧ u ≥ 1/200`,
   tail `u + v ≥ 27`) plus a compact 202-leaf exact-integer linear+bilinear certificate verified
   by kernel `rfl` (zero `native_decide`, zero `MeasureTheory`).
-/

namespace C6aProof

open Finset

-- ============================================================================
-- SECTION 1: Binary entropy `h`, transformed entropy `F`, and elementary bounds
-- ============================================================================

noncomputable def h (x : ℝ) : ℝ :=
  -x * Real.log x - (1 - x) * Real.log (1 - x)

lemma h_zero : h 0 = 0 := by simp [h]

lemma h_one : h 1 = 0 := by simp [h]

lemma h_symm (x : ℝ) : h (1 - x) = h x := by
  unfold h
  have : 1 - (1 - x) = x := by ring
  rw [this]; ring

lemma h_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : 0 ≤ h x := by
  unfold h
  have h1 : 0 ≤ -x * Real.log x := by
    rcases hx0.eq_or_lt with rfl | hpos
    · simp
    · have hlog : Real.log x ≤ 0 := Real.log_nonpos hx0 hx1
      nlinarith
  have h2 : 0 ≤ -(1 - x) * Real.log (1 - x) := by
    rcases hx1.eq_or_lt with rfl | hlt
    · simp
    · have hpos : 0 < 1 - x := by linarith
      have hlog : Real.log (1 - x) ≤ 0 := Real.log_nonpos hpos.le (by linarith)
      nlinarith
  linarith

lemma h_pos {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) : 0 < h x := by
  unfold h
  have h1 : Real.log x < 0 := Real.log_neg hx0 hx1
  have h2 : Real.log (1 - x) < 0 := Real.log_neg (by linarith) (by linarith)
  nlinarith

lemma h_le_tangent {p m : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hm0 : 0 < m) (hm1 : m < 1) :
    h p ≤ h m + Real.log ((1 - m) / m) * (p - m) := by
  have hm1_pos : 0 < 1 - m := by linarith
  have hterm1 : p * Real.log m ≤ p * Real.log p + (m - p) := by
    rcases hp0.eq_or_lt with rfl | hpp
    · simp; linarith
    · have hle : Real.log (m / p) ≤ m / p - 1 := Real.log_le_sub_one_of_pos (div_pos hm0 hpp)
      rw [Real.log_div hm0.ne' hpp.ne'] at hle
      have hmul := mul_le_mul_of_nonneg_left hle hpp.le
      have : p * (m / p - 1) = m - p := by field_simp
      linarith
  have hterm2 : (1 - p) * Real.log (1 - m) ≤ (1 - p) * Real.log (1 - p) + (p - m) := by
    rcases hp1.eq_or_lt with rfl | hplt
    · simp; linarith
    · have hp1p : 0 < 1 - p := by linarith
      have hle : Real.log ((1 - m) / (1 - p)) ≤ (1 - m) / (1 - p) - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hm1_pos hp1p)
      rw [Real.log_div hm1_pos.ne' hp1p.ne'] at hle
      have hmul := mul_le_mul_of_nonneg_left hle hp1p.le
      have : (1 - p) * ((1 - m) / (1 - p) - 1) = p - m := by field_simp; ring
      linarith
  have hdiv : Real.log ((1 - m) / m) = Real.log (1 - m) - Real.log m :=
    Real.log_div hm1_pos.ne' hm0.ne'
  unfold h
  rw [hdiv]
  linarith

lemma sum_mul_h_le {ι : Type*} (s : Finset ι) (w p : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hsum : ∑ i ∈ s, w i = 1)
    (hp0 : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∀ i ∈ s, p i ≤ 1) :
    ∑ i ∈ s, w i * h (p i) ≤ h (∑ i ∈ s, w i * p i) := by
  set m := ∑ i ∈ s, w i * p i
  have hm0 : 0 ≤ m := Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi) (hp0 i hi)
  have hm1 : m ≤ 1 := by
    calc m = ∑ i ∈ s, w i * p i := rfl
      _ ≤ ∑ i ∈ s, w i * 1 := Finset.sum_le_sum fun i hi =>
          mul_le_mul_of_nonneg_left (hp1 i hi) (hw i hi)
      _ = 1 := by simp [hsum]
  rcases hm0.eq_or_lt with hm_zero | hm_pos
  · have hzero : ∀ i ∈ s, w i * h (p i) = 0 := by
      intro i hi
      have hwp : w i * p i = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun j hj => mul_nonneg (hw j hj) (hp0 j hj))).mp
          hm_zero.symm i hi
      rcases mul_eq_zero.mp hwp with hwi | hpi
      · simp [hwi]
      · simp [hpi, h_zero]
    rw [Finset.sum_eq_zero hzero, ← hm_zero, h_zero]
  · rcases hm1.eq_or_lt with hm_one | hm_lt
    · have hone : ∀ i ∈ s, w i * h (p i) = 0 := by
        intro i hi
        have hsum0 : ∑ j ∈ s, w j * (1 - p j) = 0 := by
          have : ∑ j ∈ s, w j * (1 - p j) = (∑ j ∈ s, w j) - ∑ j ∈ s, w j * p j := by
            simp [mul_sub, Finset.sum_sub_distrib]
          linarith [this, hsum, hm_one]
        have hwp : w i * (1 - p i) = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg
            (fun j hj => mul_nonneg (hw j hj) (sub_nonneg.mpr (hp1 j hj)))).mp hsum0 i hi
        rcases mul_eq_zero.mp hwp with hwi | hpi
        · simp [hwi]
        · have : p i = 1 := by linarith
          simp [this, h_one]
      rw [Finset.sum_eq_zero hone, hm_one, h_one]
    · set c := Real.log ((1 - m) / m)
      calc ∑ i ∈ s, w i * h (p i)
          ≤ ∑ i ∈ s, w i * (h m + c * (p i - m)) :=
            Finset.sum_le_sum fun i hi =>
              mul_le_mul_of_nonneg_left (h_le_tangent (hp0 i hi) (hp1 i hi) hm_pos hm_lt) (hw i hi)
        _ = ∑ i ∈ s, (w i * h m + c * (w i * p i) - w i * (c * m)) := by
            refine Finset.sum_congr rfl fun i _ => ?_; ring
        _ = (∑ i ∈ s, w i) * h m + c * (∑ i ∈ s, w i * p i) - (∑ i ∈ s, w i) * (c * m) := by
            rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul,
                ← Finset.mul_sum, ← Finset.sum_mul]
        _ = h m := by rw [hsum]; simp only [m]; ring

-- Weighted version for non-normalized positive sum W = ∑ w i > 0:
lemma sum_mul_h_le_weighted {ι : Type*} (s : Finset ι) (w p : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hp0 : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∀ i ∈ s, p i ≤ 1) :
    ∑ i ∈ s, w i * h (p i) ≤ (∑ i ∈ s, w i) * h ((∑ i ∈ s, w i * p i) / (∑ i ∈ s, w i)) := by
  set W := ∑ i ∈ s, w i
  have hW0 : 0 ≤ W := Finset.sum_nonneg hw
  rcases hW0.eq_or_lt with hWz | hWp
  · have hzero : ∀ i ∈ s, w i * h (p i) = 0 := by
      intro i hi
      have := (Finset.sum_eq_zero_iff_of_nonneg hw).mp hWz.symm i hi
      simp [this]
    rw [Finset.sum_eq_zero hzero, ← hWz, zero_mul]
  · have hnorm : ∑ i ∈ s, (w i / W) = 1 := by
      rw [← Finset.sum_div, div_self hWp.ne']
    have hjen := sum_mul_h_le s (fun i => w i / W) p
      (fun i hi => div_nonneg (hw i hi) hWp.le) hnorm hp0 hp1
    have harg : ∑ i ∈ s, (w i / W) * p i = (∑ i ∈ s, w i * p i) / W := by
      simp_rw [div_mul_eq_mul_div, ← Finset.sum_div]
    rw [harg] at hjen
    have hmul := mul_le_mul_of_nonneg_left hjen hWp.le
    have hlhs : W * ∑ i ∈ s, (w i / W) * h (p i) = ∑ i ∈ s, w i * h (p i) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      field_simp [hWp.ne']
    linarith

noncomputable def F (u : ℝ) : ℝ :=
  u - (Real.exp u - 1) * Real.log (1 - Real.exp (-u))

noncomputable def Fp (u : ℝ) : ℝ :=
  -Real.exp u * Real.log (1 - Real.exp (-u))

lemma F_eq_h_div {u : ℝ} : F u = h (Real.exp (-u)) / Real.exp (-u) := by
  unfold F h
  have hexp_pos : 0 < Real.exp (-u) := Real.exp_pos (-u)
  have hexp_mul : Real.exp u * Real.exp (-u) = 1 := by rw [← Real.exp_add]; simp
  have hdiff : Real.exp (-u) * (Real.exp u - 1) = 1 - Real.exp (-u) := by linarith
  rw [Real.log_exp]
  field_simp [hexp_pos.ne']
  have : Real.exp (-u) * (u - (Real.exp u - 1) * Real.log (1 - Real.exp (-u))) =
      u * Real.exp (-u) - Real.exp (-u) * (Real.exp u - 1) * Real.log (1 - Real.exp (-u)) := by ring
  rw [this, hdiff]

lemma neg_log_one_sub_ge {z : ℝ} (hz1 : z < 1) : z ≤ -Real.log (1 - z) := by
  have h1 : Real.log (1 - z) ≤ (1 - z) - 1 := Real.log_le_sub_one_of_pos (by linarith)
  linarith

lemma neg_log_one_sub_le {z : ℝ} (hz1 : z < 1) :
    -Real.log (1 - z) ≤ z / (1 - z) := by
  have hpos : 0 < 1 - z := by linarith
  have h1 : Real.log (1 / (1 - z)) ≤ 1 / (1 - z) - 1 :=
    Real.log_le_sub_one_of_pos (div_pos one_pos hpos)
  rw [Real.log_div one_ne_zero hpos.ne', Real.log_one, zero_sub] at h1
  have h2 : 1 / (1 - z) - 1 = z / (1 - z) := by field_simp [hpos.ne']; ring
  linarith

lemma neg_log_one_sub_le_quad {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    -Real.log (1 - z) ≤ z + z ^ 2 / (2 * (1 - z)) := by
  let g : ℝ → ℝ := fun t => t + t ^ 2 / (2 * (1 - t)) + Real.log (1 - t)
  have hg_deriv : ∀ t ∈ Set.Icc 0 z,
      HasDerivAt g (t ^ 2 / (2 * (1 - t) ^ 2)) t := by
    intro t ht
    have h1t : 0 < 1 - t := by linarith [ht.2]
    have hd1 : HasDerivAt (fun x : ℝ => x) 1 t := hasDerivAt_id t
    have hd_num : HasDerivAt (fun x : ℝ => x ^ 2) (2 * t) t := by
      simpa using (hasDerivAt_pow 2 t)
    have hd_1m : HasDerivAt (fun x : ℝ => 1 - x) (-1) t := (hasDerivAt_id t).const_sub 1
    have hd_den : HasDerivAt (fun x : ℝ => 2 * (1 - x)) (-2) t := by
      simpa using hd_1m.const_mul 2
    have hd_q : HasDerivAt (fun x : ℝ => x ^ 2 / (2 * (1 - x)))
        ((2 * t * (2 * (1 - t)) - t ^ 2 * (-2)) / (2 * (1 - t)) ^ 2) t :=
      hd_num.div hd_den (by linarith)
    have hd_log : HasDerivAt (fun x : ℝ => Real.log (1 - x)) (-1 / (1 - t)) t :=
      hd_1m.log h1t.ne'
    have hsum := (hd1.add hd_q).add hd_log
    have hval : 1 + (2 * t * (2 * (1 - t)) - t ^ 2 * -2) / (2 * (1 - t)) ^ 2 + -1 / (1 - t) =
        t ^ 2 / (2 * (1 - t) ^ 2) := by
      field_simp [h1t.ne']; ring
    rw [hval] at hsum
    exact hsum
  have hg_mono : MonotoneOn g (Set.Icc 0 z) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 z)
    · exact fun t ht => (hg_deriv t ht).continuousAt.continuousWithinAt
    · exact fun t ht => (hg_deriv t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hg_deriv t (interior_subset ht)).deriv]
      positivity
  have h0 : g 0 ≤ g z := hg_mono ⟨le_rfl, hz0.le⟩ ⟨hz0.le, le_rfl⟩ hz0.le
  simp only [g, zero_pow two_ne_zero, zero_div, add_zero, sub_zero, Real.log_one] at h0
  linarith

lemma hasDerivAt_F {u : ℝ} (hu : 0 < u) : HasDerivAt F (Fp u) u := by
  have hexp_lt : Real.exp (-u) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have h1m : 0 < 1 - Real.exp (-u) := by linarith
  have hprod : Real.exp u * Real.exp (-u) = 1 := by rw [← Real.exp_add]; simp
  have hd_u : HasDerivAt (fun x : ℝ => x) 1 u := hasDerivAt_id u
  have hd_eu : HasDerivAt (fun x : ℝ => Real.exp x - 1) (Real.exp u) u :=
    (Real.hasDerivAt_exp u).sub_const 1
  have hd_emu : HasDerivAt (fun x : ℝ => 1 - Real.exp (-x)) (Real.exp (-u)) u := by
    have he : HasDerivAt (fun x : ℝ => Real.exp (-x)) (Real.exp (-u) * -1) u :=
      (hasDerivAt_id u).neg.exp
    simpa using he.const_sub 1
  have hd_log : HasDerivAt (fun x : ℝ => Real.log (1 - Real.exp (-x)))
      (Real.exp (-u) / (1 - Real.exp (-u))) u := hd_emu.log h1m.ne'
  have hd := hd_u.sub (hd_eu.mul hd_log)
  have hval : 1 - (Real.exp u * Real.log (1 - Real.exp (-u)) +
      (Real.exp u - 1) * (Real.exp (-u) / (1 - Real.exp (-u)))) = Fp u := by
    unfold Fp
    have hdiff : (Real.exp u - 1) * Real.exp (-u) = 1 - Real.exp (-u) := by linarith
    field_simp [h1m.ne']
    nlinarith [hprod]
  rw [hval] at hd
  exact hd

lemma hasDerivAt_Fp {u : ℝ} (hu : 0 < u) :
    HasDerivAt Fp (Real.exp u * (-Real.log (1 - Real.exp (-u)) -
      Real.exp (-u) / (1 - Real.exp (-u)))) u := by
  have hexp_lt : Real.exp (-u) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have h1m : 0 < 1 - Real.exp (-u) := by linarith
  have hprod : Real.exp u * Real.exp (-u) = 1 := by rw [← Real.exp_add]; simp
  have hd_eu : HasDerivAt (fun x : ℝ => -Real.exp x) (-Real.exp u) u := (Real.hasDerivAt_exp u).neg
  have hd_emu : HasDerivAt (fun x : ℝ => 1 - Real.exp (-x)) (Real.exp (-u)) u := by
    have he : HasDerivAt (fun x : ℝ => Real.exp (-x)) (Real.exp (-u) * -1) u :=
      (hasDerivAt_id u).neg.exp
    simpa using he.const_sub 1
  have hd_log : HasDerivAt (fun x : ℝ => Real.log (1 - Real.exp (-x)))
      (Real.exp (-u) / (1 - Real.exp (-u))) u := hd_emu.log h1m.ne'
  have hd := hd_eu.mul hd_log
  have hval : -Real.exp u * Real.log (1 - Real.exp (-u)) +
      -Real.exp u * (Real.exp (-u) / (1 - Real.exp (-u))) =
      Real.exp u * (-Real.log (1 - Real.exp (-u)) - Real.exp (-u) / (1 - Real.exp (-u))) := by ring
  rw [hval] at hd
  exact hd

lemma Fp_pos {u : ℝ} (hu : 0 < u) : 0 < Fp u := by
  unfold Fp
  have hexp_lt : Real.exp (-u) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hlog : Real.log (1 - Real.exp (-u)) < 0 :=
    Real.log_neg (by linarith) (by linarith [Real.exp_pos (-u)])
  have he : 0 < Real.exp u := Real.exp_pos u
  nlinarith

lemma F_strictMono : StrictMonoOn F (Set.Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · exact fun u hu => (hasDerivAt_F hu).continuousAt.continuousWithinAt
  · intro u hu
    have hu' : 0 < u := by simpa [interior_Ioi] using hu
    rw [(hasDerivAt_F hu').deriv]
    exact Fp_pos hu'

lemma Fp_antitone : AntitoneOn Fp (Set.Ioi 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
  · exact fun u hu => (hasDerivAt_Fp hu).continuousAt.continuousWithinAt
  · intro u hu
    have hu' : 0 < u := by simpa [interior_Ioi] using hu
    exact (hasDerivAt_Fp hu').differentiableAt.differentiableWithinAt
  · intro u hu
    have hu' : 0 < u := by simpa [interior_Ioi] using hu
    rw [(hasDerivAt_Fp hu').deriv]
    have hz1 : Real.exp (-u) < 1 := by rw [Real.exp_lt_one_iff]; linarith
    have hle := neg_log_one_sub_le hz1
    have he : 0 < Real.exp u := Real.exp_pos u
    nlinarith

lemma F_le_tangent {u m : ℝ} (hu : 0 < u) (hm : 0 < m) :
    F u ≤ F m + Fp m * (u - m) := by
  rcases lt_trichotomy u m with hlt | rfl | hgt
  · obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope F Fp hlt
      (fun x hx => (hasDerivAt_F (lt_of_lt_of_le hu hx.1)).continuousAt.continuousWithinAt)
      (fun x hx => hasDerivAt_F (lt_trans hu hx.1))
    have hanti : Fp m ≤ Fp c := Fp_antitone (lt_trans hu hc.1) hm hc.2.le
    have hdiff : F m - F u = Fp c * (m - u) := by
      have hne : m - u ≠ 0 := by linarith
      field_simp [hne] at hslope; linarith
    nlinarith
  · simp
  · obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope F Fp hgt
      (fun x hx => (hasDerivAt_F (lt_of_lt_of_le hm hx.1)).continuousAt.continuousWithinAt)
      (fun x hx => hasDerivAt_F (lt_trans hm hx.1))
    have hanti : Fp c ≤ Fp m := Fp_antitone hm (lt_trans hm hc.1) hc.1.le
    have hdiff : F u - F m = Fp c * (u - m) := by
      have hne : u - m ≠ 0 := by linarith
      field_simp [hne] at hslope; linarith
    nlinarith

lemma F_secant_le {a b t : ℝ} (ha : 0 < a) (hab : a < b) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) * F a + t * F b ≤ F ((1 - t) * a + t * b) := by
  set x := (1 - t) * a + t * b
  rcases ht0.eq_or_lt with rfl | ht0'
  · simp [x]
  rcases ht1.eq_or_lt with rfl | ht1'
  · simp [x]
  have hax : a < x := by nlinarith
  have hxb : x < b := by nlinarith
  obtain ⟨c1, hc1, hs1⟩ := exists_hasDerivAt_eq_slope F Fp hax
    (fun z hz => (hasDerivAt_F (lt_of_lt_of_le ha hz.1)).continuousAt.continuousWithinAt)
    (fun z hz => hasDerivAt_F (lt_trans ha hz.1))
  obtain ⟨c2, hc2, hs2⟩ := exists_hasDerivAt_eq_slope F Fp hxb
    (fun z hz => (hasDerivAt_F (lt_trans ha (lt_of_lt_of_le hax hz.1))).continuousAt.continuousWithinAt)
    (fun z hz => hasDerivAt_F (lt_trans ha (lt_trans hax hz.1)))
  have hanti : Fp c2 ≤ Fp c1 :=
    Fp_antitone (lt_trans ha hc1.1) (lt_trans ha (lt_trans hax hc2.1)) (le_of_lt (lt_trans hc1.2 hc2.1))
  have h1 : F x - F a = Fp c1 * (t * (b - a)) := by
    have hxa : x - a = t * (b - a) := by ring
    have hne : x - a ≠ 0 := by linarith
    field_simp [hne] at hs1; rw [hxa] at hs1; linarith
  have h2 : F b - F x = Fp c2 * ((1 - t) * (b - a)) := by
    have hbx : b - x = (1 - t) * (b - a) := by ring
    have hne : b - x ≠ 0 := by linarith
    field_simp [hne] at hs2; rw [hbx] at hs2; linarith
  have hw : 0 ≤ t * (1 - t) * (b - a) := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hanti hw
  nlinarith

lemma F_pos {u : ℝ} (hu : 0 < u) : 0 < F u := by
  rw [F_eq_h_div]
  have hz0 : 0 < Real.exp (-u) := Real.exp_pos (-u)
  have hz1 : Real.exp (-u) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  exact div_pos (h_pos hz0 hz1) hz0

lemma F_ge_add_one_sub_exp {u : ℝ} (hu : 0 < u) : u + 1 - Real.exp (-u) ≤ F u := by
  unfold F
  have hz1 : Real.exp (-u) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hlog := neg_log_one_sub_ge hz1
  have hprod : Real.exp u * Real.exp (-u) = 1 := by rw [← Real.exp_add]; simp
  have he : 1 < Real.exp u := by rw [Real.one_lt_exp_iff]; exact hu
  have h1 : (Real.exp u - 1) * Real.exp (-u) = 1 - Real.exp (-u) := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hlog (show 0 ≤ Real.exp u - 1 by linarith)]

lemma F_le_add_one {u : ℝ} (hu : 0 < u) : F u ≤ u + 1 := by
  unfold F
  have hz1 : Real.exp (-u) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hlog := neg_log_one_sub_le hz1
  have hprod : Real.exp u * Real.exp (-u) = 1 := by rw [← Real.exp_add]; simp
  have he : 1 < Real.exp u := by rw [Real.one_lt_exp_iff]; exact hu
  have h1 : (Real.exp u - 1) * (Real.exp (-u) / (1 - Real.exp (-u))) = 1 := by
    have hne : 1 - Real.exp (-u) ≠ 0 := by linarith
    field_simp [hne]; linarith
  nlinarith [mul_le_mul_of_nonneg_left hlog (show 0 ≤ Real.exp u - 1 by linarith)]

-- ============================================================================
-- SECTION 2: Inequality I (Exact global log-submodularity, ZERO grids!)
-- ============================================================================

noncomputable def f (s : ℝ) : ℝ := (7 / 10 : ℝ) * s * (1 - s)

noncomputable def pfn (s t : ℝ) : ℝ := (1 - s) * (1 - t) + f s * f t

noncomputable def gfn (s : ℝ) : ℝ := Real.sqrt (h (pfn s s))

lemma pfn_eq (s t : ℝ) : pfn s t = (1 - s) * (1 - t) * (1 + (49 / 100 : ℝ) * s * t) := by
  unfold pfn f; ring

lemma f_bounds {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ f s ∧ f s ≤ s ∧ f s ≤ 1 - s := by
  unfold f
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

lemma pfn_pos_lt_one {s t : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ht0 : 0 < t) (ht1 : t < 1) :
    0 < pfn s t ∧ pfn s t < 1 := by
  have h1 : 0 < pfn s t := by rw [pfn_eq]; positivity
  have h2 : pfn s t < 1 := by
    have hfs := f_bounds hs0.le hs1.le
    have hft := f_bounds ht0.le ht1.le
    unfold pfn
    nlinarith
  exact ⟨h1, h2⟩

lemma poly_bridge_ineq1 {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 + (49 / 100 : ℝ) * s * t) * (1 + (49 / 100 : ℝ) * (1 - 2 * s) * (1 - 2 * t)) ≤
    (1 + (1 - s) * (1 - t)) * (1 + (49 / 100 : ℝ) * t * (2 * s - 1)) *
      (1 + (49 / 100 : ℝ) * s * (2 * t - 1)) := by
  set u := 1 - s
  set v := 1 - t
  have hu : 0 ≤ u := by linarith
  have hv : 0 ≤ v := by linarith
  have hid :
      (1 + u * v) * (1 + (49 / 100 : ℝ) * t * (2 * s - 1)) *
        (1 + (49 / 100 : ℝ) * s * (2 * t - 1)) -
      (1 + (49 / 100 : ℝ) * s * t) * (1 + (49 / 100 : ℝ) * (1 - 2 * s) * (1 - 2 * t)) =
      u * v * (
        (51 / 100 : ℝ) * u ^ 2 * v ^ 2 +
        (53 / 100 : ℝ) * u ^ 2 * v * t +
        (1 / 50 : ℝ) * u ^ 2 * t ^ 2 +
        (53 / 100 : ℝ) * u * s * v ^ 2 +
        (22801 / 10000 : ℝ) * u * s * v * t +
        (12699 / 10000 : ℝ) * u * s * t ^ 2 +
        (1 / 50 : ℝ) * s ^ 2 * v ^ 2 +
        (12699 / 10000 : ℝ) * s ^ 2 * v * t +
        (17301 / 10000 : ℝ) * s ^ 2 * t ^ 2) := by
    simp only [u, v]; ring
  have hpos : 0 ≤ u * v * (
        (51 / 100 : ℝ) * u ^ 2 * v ^ 2 +
        (53 / 100 : ℝ) * u ^ 2 * v * t +
        (1 / 50 : ℝ) * u ^ 2 * t ^ 2 +
        (53 / 100 : ℝ) * u * s * v ^ 2 +
        (22801 / 10000 : ℝ) * u * s * v * t +
        (12699 / 10000 : ℝ) * u * s * t ^ 2 +
        (1 / 50 : ℝ) * s ^ 2 * v ^ 2 +
        (12699 / 10000 : ℝ) * s ^ 2 * v * t +
        (17301 / 10000 : ℝ) * s ^ 2 * t ^ 2) := by positivity
  linarith

lemma entropy_bridge_ineq1 {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1 / 2) :
    1 + z ≤ z * Real.log ((1 - z) / z) / h z + 1 / ((1 - z) * Real.log ((1 - z) / z)) := by
  have h1z : 0 < 1 - z := by linarith
  have hratio : 1 < (1 - z) / z := by rw [one_lt_div hz0]; linarith
  set A := Real.log ((1 - z) / z)
  have hA : 0 < A := Real.log_pos hratio
  set L := -Real.log (1 - z)
  have hL_ge : z ≤ L := neg_log_one_sub_ge (by linarith)
  have hL_le : L ≤ z + z ^ 2 / (2 * (1 - z)) := neg_log_one_sub_le_quad hz0 (by linarith)
  have hh_eq : h z = z * A + L := by
    unfold h; simp only [A, L]; rw [Real.log_div h1z.ne' hz0.ne']; ring
  have hh_pos : 0 < h z := h_pos hz0 (by linarith)
  have hden_pos : 0 < h z * ((1 - z) * A) := mul_pos hh_pos (mul_pos h1z hA)
  suffices hmain : 0 ≤ L * (1 - (1 - z ^ 2) * A) + z * A * (1 - z * (1 - z) * A) by
    have hrew :
        (z * A / h z + 1 / ((1 - z) * A) - (1 + z)) * (h z * ((1 - z) * A)) =
        L * (1 - (1 - z ^ 2) * A) + z * A * (1 - z * (1 - z) * A) := by
      have h1 : h z ≠ 0 := hh_pos.ne'
      have h2 : (1 - z) * A ≠ 0 := (mul_pos h1z hA).ne'
      field_simp [h1, h2]
      rw [hh_eq]; ring
    have hprod : 0 ≤ (z * A / h z + 1 / ((1 - z) * A) - (1 + z)) * (h z * ((1 - z) * A)) := by
      linarith [hrew, hmain]
    have hnonneg : 0 ≤ z * A / h z + 1 / ((1 - z) * A) - (1 + z) :=
      nonneg_of_mul_nonneg_left hprod hden_pos
    linarith
  by_cases hcoeff : 0 ≤ 1 - (1 - z ^ 2) * A
  · have hstep : z * (1 - (1 - z ^ 2) * A) ≤ L * (1 - (1 - z ^ 2) * A) :=
      mul_le_mul_of_nonneg_right hL_ge hcoeff
    have h1z2 : 0 < 1 - z ^ 2 := by nlinarith
    have hA_le : A ≤ 1 / (1 - z ^ 2) := by rw [le_div_iff₀ h1z2]; linarith
    have hmul : z * (1 - z) * A ≤ z * (1 - z) / (1 - z ^ 2) := by
      have := mul_le_mul_of_nonneg_left hA_le (show 0 ≤ z * (1 - z) by nlinarith)
      rwa [mul_one_div] at this
    have hfrac : z * (1 - z) / (1 - z ^ 2) ≤ 1 := by
      rw [div_le_one h1z2]; nlinarith
    have hquad : 0 ≤ 1 - z * (1 - z) * A := by linarith
    have h1 : 0 ≤ z * (1 - (1 - z ^ 2) * A) := mul_nonneg hz0.le hcoeff
    have h2 : 0 ≤ z * A * (1 - z * (1 - z) * A) := mul_nonneg (mul_nonneg hz0.le hA.le) hquad
    linarith
  · have hcoeff_lt : 1 - (1 - z ^ 2) * A < 0 := not_le.mp hcoeff
    have hstep : (z + z ^ 2 / (2 * (1 - z))) * (1 - (1 - z ^ 2) * A) ≤
        L * (1 - (1 - z ^ 2) * A) :=
      mul_le_mul_of_nonpos_right hL_le hcoeff_lt.le
    set r := Real.sqrt (Real.sqrt ((1 - z) / z))
    have hr_pos : 0 < r := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (div_pos h1z hz0))
    have hr4 : r ^ 4 = (1 - z) / z := by
      have hsq1 : r ^ 2 = Real.sqrt ((1 - z) / z) := Real.sq_sqrt (Real.sqrt_nonneg _)
      have hsq2 : (Real.sqrt ((1 - z) / z)) ^ 2 = (1 - z) / z :=
        Real.sq_sqrt (div_nonneg h1z.le hz0.le)
      calc r ^ 4 = (r ^ 2) ^ 2 := by ring
        _ = (Real.sqrt ((1 - z) / z)) ^ 2 := by rw [hsq1]
        _ = (1 - z) / z := hsq2
    have hr_ge1 : 1 ≤ r := by
      by_contra hlt
      have hlt' : r < 1 := not_le.mp hlt
      have : r ^ 4 < 1 := by
        have h1 : r ^ 2 < 1 := by nlinarith
        nlinarith
      linarith [hr4, hratio]
    set w := r - 1
    have hw : 0 ≤ w := by linarith
    have hA_le4w : A ≤ 4 * w := by
      have hlogr : Real.log r ≤ r - 1 := Real.log_le_sub_one_of_pos hr_pos
      have hA4 : A = 4 * Real.log r := by
        simp only [A, ← hr4, Real.log_pow]; ring
      linarith
    have hrew_q : (z + z ^ 2 / (2 * (1 - z))) * (1 - (1 - z ^ 2) * A) +
        z * A * (1 - z * (1 - z) * A) =
        z * ((1 + z / (2 * (1 - z))) - (z * (1 - z) / 2) * A - z * (1 - z) * A ^ 2) := by
      field_simp [h1z.ne']; ring
    have hmono_A :
        (1 + z / (2 * (1 - z))) - (z * (1 - z) / 2) * (4 * w) - z * (1 - z) * (4 * w) ^ 2 ≤
        (1 + z / (2 * (1 - z))) - (z * (1 - z) / 2) * A - z * (1 - z) * A ^ 2 := by
      have hA2 : A ^ 2 ≤ (4 * w) ^ 2 := by nlinarith
      have hzz : 0 ≤ z * (1 - z) := by nlinarith
      nlinarith
    have hz_eq : z = 1 / (1 + r ^ 4) := by
      have h1r : 1 + r ^ 4 ≠ 0 := by positivity
      have : z * (1 + r ^ 4) = 1 := by rw [hr4]; field_simp [hz0.ne']; ring
      field_simp [h1r]; linarith
    have h1z_eq : 1 - z = r ^ 4 / (1 + r ^ 4) := by
      have h1r : 1 + r ^ 4 ≠ 0 := by positivity
      rw [hz_eq]; field_simp [h1r]; ring
    have hpoly_nonneg : 0 ≤ (2 * r ^ 4 + 1) * (1 + r ^ 4) ^ 2 -
        2 * r ^ 8 * (2 * w + 16 * w ^ 2) := by
      have hrw : r = 1 + w := by ring
      rw [hrw]
      have hid : (2 * (1 + w) ^ 4 + 1) * (1 + (1 + w) ^ 4) ^ 2 -
          2 * (1 + w) ^ 8 * (2 * w + 16 * w ^ 2) =
          208 * w ^ 2 * (1 - w ^ 3 / 2) ^ 2 +
          340 * w ^ 3 * (1 - 7 * w ^ 3 / 10) ^ 2 +
          210 * w ^ 4 * (1 - 2 * w ^ 3 / 3) ^ 2 +
          12 + 76 * w + 24 * w ^ 2 + 28 * w ^ 3 + 14 * w ^ 4 +
          15 * w ^ 8 + (67 / 5 : ℝ) * w ^ 9 + (20 / 3 : ℝ) * w ^ 10 +
          24 * w ^ 11 + 2 * w ^ 12 := by ring
      rw [hid]; positivity
    have hval_pos : 0 ≤ (1 + z / (2 * (1 - z))) - (z * (1 - z) / 2) * (4 * w) -
        z * (1 - z) * (4 * w) ^ 2 := by
      rw [h1z_eq, hz_eq]
      have hden : 0 < 2 * r ^ 4 * (1 + r ^ 4) ^ 2 := by positivity
      have hrew2 :
          (1 + (1 / (1 + r ^ 4)) / (2 * (r ^ 4 / (1 + r ^ 4)))) -
            ((1 / (1 + r ^ 4)) * (r ^ 4 / (1 + r ^ 4)) / 2) * (4 * w) -
            (1 / (1 + r ^ 4)) * (r ^ 4 / (1 + r ^ 4)) * (4 * w) ^ 2 =
          ((2 * r ^ 4 + 1) * (1 + r ^ 4) ^ 2 - 2 * r ^ 8 * (2 * w + 16 * w ^ 2)) /
            (2 * r ^ 4 * (1 + r ^ 4) ^ 2) := by
        have h1 : r ^ 4 ≠ 0 := by positivity
        have h2 : 1 + r ^ 4 ≠ 0 := by positivity
        field_simp [h1, h2]; ring
      rw [hrew2]
      exact div_nonneg hpoly_nonneg hden.le
    nlinarith

noncomputable def pxFn (x y : ℝ) : ℝ := -(1 - y) * (1 + (49 / 100 : ℝ) * y * (2 * x - 1))
noncomputable def pyFn (x y : ℝ) : ℝ := -(1 - x) * (1 + (49 / 100 : ℝ) * x * (2 * y - 1))
noncomputable def pxyFn (x y : ℝ) : ℝ := 1 + (49 / 100 : ℝ) * (1 - 2 * x) * (1 - 2 * y)
noncomputable def hpFn (z : ℝ) : ℝ := Real.log ((1 - z) / z)
noncomputable def dLxFn (x y : ℝ) : ℝ := (hpFn (pfn x y) / h (pfn x y)) * pxFn x y

lemma hd_hFn {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) : HasDerivAt h (hpFn z) z := by
  have h1z : 0 < 1 - z := by linarith
  have hd1 : HasDerivAt (fun r : ℝ => -r * Real.log r) (-Real.log z - 1) z := by
    have hraw : HasDerivAt (fun r : ℝ => -r * Real.log r) (-1 * Real.log z + -z * z⁻¹) z :=
      (hasDerivAt_id z).neg.mul (Real.hasDerivAt_log hz0.ne')
    have hv : -1 * Real.log z + -z * z⁻¹ = -Real.log z - 1 := by
      field_simp [hz0.ne']; ring
    rw [hv] at hraw; exact hraw
  have hd2 : HasDerivAt (fun r : ℝ => (1 - r) * Real.log (1 - r)) (-Real.log (1 - z) - 1) z := by
    have h1 : HasDerivAt (fun r : ℝ => 1 - r) (-1) z := (hasDerivAt_id z).const_sub 1
    have hraw : HasDerivAt (fun r : ℝ => (1 - r) * Real.log (1 - r))
        (-1 * Real.log (1 - z) + (1 - z) * (-1 / (1 - z))) z := h1.mul (h1.log h1z.ne')
    have hv : -1 * Real.log (1 - z) + (1 - z) * (-1 / (1 - z)) = -Real.log (1 - z) - 1 := by
      field_simp [h1z.ne']; ring
    rw [hv] at hraw; exact hraw
  have hsub := hd1.sub hd2
  have hv : (-Real.log z - 1) - (-Real.log (1 - z) - 1) = hpFn z := by
    simp only [hpFn]; rw [Real.log_div h1z.ne' hz0.ne']; ring
  rw [hv] at hsub
  exact hsub

lemma hd_hpFn {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    HasDerivAt hpFn (-1 / (z * (1 - z))) z := by
  have h1z : 0 < 1 - z := by linarith
  have h1 : HasDerivAt (fun r : ℝ => Real.log (1 - r)) (-1 / (1 - z)) z :=
    ((hasDerivAt_id z).const_sub 1).log h1z.ne'
  have h2 : HasDerivAt (fun r : ℝ => Real.log r) (1 / z) z := by
    simpa [one_div] using Real.hasDerivAt_log hz0.ne'
  have hsub := h1.sub h2
  have hv : -1 / (1 - z) - 1 / z = -1 / (z * (1 - z)) := by
    field_simp [hz0.ne', h1z.ne']; ring
  rw [hv] at hsub
  have heq : ∀ᶠ r in nhds z, hpFn r = Real.log (1 - r) - Real.log r := by
    filter_upwards [Ioo_mem_nhds hz0 hz1] with r hr
    simp only [hpFn]; exact Real.log_div (by linarith [hr.2]) hr.1.ne'
  exact hsub.congr_of_eventuallyEq heq

lemma hd_pxFn (x y : ℝ) : HasDerivAt (fun r => pfn r y) (pxFn x y) x := by
  have hfun : (fun r => pfn r y) =
      (fun r => (1 - r) * (1 - y) + (49 / 100 : ℝ) * y * (1 - y) * (r - r ^ 2)) := by
    funext r; unfold pfn f; ring
  rw [hfun]
  have h1 : HasDerivAt (fun r : ℝ => (1 - r) * (1 - y)) (-(1 - y)) x := by
    simpa using ((hasDerivAt_id x).const_sub 1).mul_const (1 - y)
  have h2 : HasDerivAt (fun r : ℝ => r - r ^ 2) (1 - 2 * x) x := by
    have hp2 : HasDerivAt (fun r : ℝ => r ^ 2) (2 * x) x := by simpa using hasDerivAt_pow 2 x
    exact (hasDerivAt_id x).sub hp2
  have h3 := h1.add (h2.const_mul ((49 / 100 : ℝ) * y * (1 - y)))
  have hv : -(1 - y) + (49 / 100 : ℝ) * y * (1 - y) * (1 - 2 * x) = pxFn x y := by
    simp only [pxFn]; ring
  rw [hv] at h3; exact h3

lemma hd_pyFn (x y : ℝ) : HasDerivAt (fun r => pfn x r) (pyFn x y) y := by
  have hsw : (fun r => pfn x r) = (fun r => pfn r x) := funext fun r => by unfold pfn f; ring
  rw [hsw]; exact hd_pxFn y x

lemma hd_px_yFn (x y : ℝ) : HasDerivAt (fun r => pxFn x r) (pxyFn x y) y := by
  have hfun : (fun r => pxFn x r) =
      (fun r => -(1 - r) - (49 / 100 : ℝ) * (2 * x - 1) * (r - r ^ 2)) := by
    funext r; simp only [pxFn]; ring
  rw [hfun]
  have h1 : HasDerivAt (fun r : ℝ => -(1 - r)) 1 y := by
    have hraw : HasDerivAt (fun r : ℝ => -(1 - r)) (-(-1)) y := ((hasDerivAt_id y).const_sub 1).neg
    rw [neg_neg] at hraw; exact hraw
  have h2 : HasDerivAt (fun r : ℝ => r - r ^ 2) (1 - 2 * y) y := by
    have hp2 : HasDerivAt (fun r : ℝ => r ^ 2) (2 * y) y := by simpa using hasDerivAt_pow 2 y
    exact (hasDerivAt_id y).sub hp2
  have h3 := h1.sub (h2.const_mul ((49 / 100 : ℝ) * (2 * x - 1)))
  have hv : 1 - (49 / 100 : ℝ) * (2 * x - 1) * (1 - 2 * y) = pxyFn x y := by
    simp only [pxyFn]; ring
  rw [hv] at h3; exact h3

lemma dLxFn_antitone {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    AntitoneOn (fun y => dLxFn x y) (Set.Ioo 0 1) := by
  have hd_dLx : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt (fun r => dLxFn x r)
        ((hpFn (pfn x y) / h (pfn x y)) * pxyFn x y +
         (((-1 / (pfn x y * (1 - pfn x y))) * h (pfn x y) - hpFn (pfn x y) ^ 2) /
           h (pfn x y) ^ 2) * (pxFn x y * pyFn x y)) y := by
    intro y hy
    have hp_b := pfn_pos_lt_one hx0 hx1 hy.1 hy.2
    have hh_pos : 0 < h (pfn x y) := h_pos hp_b.1 hp_b.2
    have h_num : HasDerivAt (fun r => hpFn (pfn x r))
        ((-1 / (pfn x y * (1 - pfn x y))) * pyFn x y) y :=
      (hd_hpFn hp_b.1 hp_b.2).comp y (hd_pyFn x y)
    have h_den : HasDerivAt (fun r => h (pfn x r)) (hpFn (pfn x y) * pyFn x y) y :=
      (hd_hFn hp_b.1 hp_b.2).comp y (hd_pyFn x y)
    have h_q : HasDerivAt (fun r => hpFn (pfn x r) / h (pfn x r))
        ((-1 / (pfn x y * (1 - pfn x y)) * pyFn x y * h (pfn x y) -
          hpFn (pfn x y) * (hpFn (pfn x y) * pyFn x y)) / h (pfn x y) ^ 2) y :=
      h_num.div h_den hh_pos.ne'
    have h_tot : HasDerivAt (fun r => dLxFn x r)
        ((-1 / (pfn x y * (1 - pfn x y)) * pyFn x y * h (pfn x y) -
            hpFn (pfn x y) * (hpFn (pfn x y) * pyFn x y)) / h (pfn x y) ^ 2 * pxFn x y +
          hpFn (pfn x y) / h (pfn x y) * pxyFn x y) y :=
      h_q.mul (hd_px_yFn x y)
    have hv :
        ((-1 / (pfn x y * (1 - pfn x y)) * pyFn x y * h (pfn x y) -
            hpFn (pfn x y) * (hpFn (pfn x y) * pyFn x y)) / h (pfn x y) ^ 2) * pxFn x y +
          hpFn (pfn x y) / h (pfn x y) * pxyFn x y =
        hpFn (pfn x y) / h (pfn x y) * pxyFn x y +
          ((-1 / (pfn x y * (1 - pfn x y)) * h (pfn x y) - hpFn (pfn x y) ^ 2) /
            h (pfn x y) ^ 2) * (pxFn x y * pyFn x y) := by ring
    rw [hv] at h_tot
    exact h_tot
  apply antitoneOn_of_deriv_nonpos (convex_Ioo 0 1)
  · exact fun y hy => (hd_dLx y hy).continuousAt.continuousWithinAt
  · intro y hy
    have hy' : y ∈ Set.Ioo (0 : ℝ) 1 := interior_subset hy
    exact (hd_dLx y hy').differentiableAt.differentiableWithinAt
  · intro y hy
    have hy' : y ∈ Set.Ioo (0 : ℝ) 1 := interior_subset hy
    rw [(hd_dLx y hy').deriv]
    set z := pfn x y
    have hz := pfn_pos_lt_one hx0 hx1 hy'.1 hy'.2
    have hhz : 0 < h z := h_pos hz.1 hz.2
    have h1z : 0 < 1 - z := by linarith [hz.2]
    have hpx_neg : pxFn x y < 0 := by
      simp only [pxFn]
      have h1 : 0 < 1 - y := by linarith [hy'.2]
      have h2 : 0 < 1 + (49 / 100 : ℝ) * y * (2 * x - 1) := by nlinarith [hy'.1, hy'.2, hx0, hx1]
      nlinarith
    have hpy_neg : pyFn x y < 0 := by
      simp only [pyFn]
      have h1 : 0 < 1 - x := by linarith [hx1]
      have h2 : 0 < 1 + (49 / 100 : ℝ) * x * (2 * y - 1) := by nlinarith [hy'.1, hy'.2, hx0, hx1]
      nlinarith
    have hpxpy : 0 < pxFn x y * pyFn x y := mul_pos_of_neg_of_neg hpx_neg hpy_neg
    have hpxy_pos : 0 < pxyFn x y := by
      simp only [pxyFn]; nlinarith [hx0, hx1, hy'.1, hy'.2]
    by_cases hzhalf : 1 / 2 ≤ z
    · have hhp_le : hpFn z ≤ 0 := by
        simp only [hpFn]; apply Real.log_nonpos (div_nonneg h1z.le hz.1.le)
        rw [div_le_one hz.1]; linarith
      have ht1 : (hpFn z / h z) * pxyFn x y ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg hhp_le hhz.le) hpxy_pos.le
      have ht2 : ((-1 / (z * (1 - z))) * h z - hpFn z ^ 2) / h z ^ 2 * (pxFn x y * pyFn x y) ≤ 0 := by
        have hnum : (-1 / (z * (1 - z))) * h z - hpFn z ^ 2 ≤ 0 := by
          have : 0 < h z / (z * (1 - z)) := div_pos hhz (mul_pos hz.1 h1z)
          have hsq : 0 ≤ hpFn z ^ 2 := sq_nonneg _
          have : (-1 / (z * (1 - z))) * h z = -(h z / (z * (1 - z))) := by ring
          linarith
        exact mul_nonpos_of_nonpos_of_nonneg
          (div_nonpos_of_nonpos_of_nonneg hnum (sq_nonneg _)) hpxpy.le
      linarith
    · have hzhalf' : z < 1 / 2 := not_le.mp hzhalf
      have hhp_pos : 0 < hpFn z := by
        simp only [hpFn]; apply Real.log_pos; rw [one_lt_div hz.1]; linarith
      have hbr1 : z * pxyFn x y ≤ (1 + z) * (pxFn x y * pyFn x y) := by
        have hp_poly := poly_bridge_ineq1 hx0.le hx1.le hy'.1.le hy'.2.le
        have h1x : 0 < 1 - x := by linarith [hx1]
        have h1y : 0 < 1 - y := by linarith [hy'.2]
        have hz_ge : (1 - x) * (1 - y) ≤ z := by
          simp only [z, pfn_eq]
          have h0 : 0 ≤ (49 / 100 : ℝ) * x * y := by nlinarith [hx0, hy'.1]
          nlinarith [mul_pos h1x h1y]
        have hden_pos : 0 < (1 + (49 / 100 : ℝ) * y * (2 * x - 1)) *
            (1 + (49 / 100 : ℝ) * x * (2 * y - 1)) := by
          have ha1 : 0 < 1 + (49 / 100 : ℝ) * y * (2 * x - 1) := by nlinarith [hy'.1, hy'.2, hx0, hx1]
          have ha2 : 0 < 1 + (49 / 100 : ℝ) * x * (2 * y - 1) := by nlinarith [hy'.1, hy'.2, hx0, hx1]
          exact mul_pos ha1 ha2
        have hstep : (1 + (49 / 100 : ℝ) * x * y) * pxyFn x y ≤
            (1 + z) * ((1 + (49 / 100 : ℝ) * y * (2 * x - 1)) *
              (1 + (49 / 100 : ℝ) * x * (2 * y - 1))) := by
          simp only [pxyFn]; nlinarith
        have hmul := mul_le_mul_of_nonneg_left hstep (mul_pos h1x h1y).le
        have hl : (1 - x) * (1 - y) * ((1 + (49 / 100 : ℝ) * x * y) * pxyFn x y) = z * pxyFn x y := by
          simp only [z, pfn_eq]; ring
        have hr : (1 - x) * (1 - y) * ((1 + z) * ((1 + (49 / 100 : ℝ) * y * (2 * x - 1)) *
            (1 + (49 / 100 : ℝ) * x * (2 * y - 1)))) = (1 + z) * (pxFn x y * pyFn x y) := by
          simp only [pxFn, pyFn]; ring
        linarith
      have hbr2 : 1 + z ≤ z * hpFn z / h z + 1 / ((1 - z) * hpFn z) :=
        entropy_bridge_ineq1 hz.1 hzhalf'
      have hcomb : z * pxyFn x y ≤ (z * hpFn z / h z + 1 / ((1 - z) * hpFn z)) * (pxFn x y * pyFn x y) := by
        have := mul_le_mul_of_nonneg_right hbr2 hpxpy.le
        linarith
      have hfac : 0 < hpFn z / (z * h z) := div_pos hhp_pos (mul_pos hz.1 hhz)
      have hfin := mul_le_mul_of_nonneg_left hcomb hfac.le
      have hzne : z ≠ 0 := hz.1.ne'; have h1zne : 1 - z ≠ 0 := h1z.ne'
      have hhzne : h z ≠ 0 := hhz.ne'; have hhpne : hpFn z ≠ 0 := hhp_pos.ne'
      have hl : hpFn z / (z * h z) * (z * pxyFn x y) = hpFn z / h z * pxyFn x y := by
        field_simp
      have hr_c : hpFn z / (z * h z) * (z * hpFn z / h z + 1 / ((1 - z) * hpFn z)) =
          -((-1 / (z * (1 - z))) * h z - hpFn z ^ 2) / h z ^ 2 := by
        field_simp; ring
      have hr : hpFn z / (z * h z) * ((z * hpFn z / h z + 1 / ((1 - z) * hpFn z)) * (pxFn x y * pyFn x y)) =
          -(((-1 / (z * (1 - z))) * h z - hpFn z ^ 2) / h z ^ 2 * (pxFn x y * pyFn x y)) := by
        rw [← mul_assoc, hr_c]; ring
      linarith

lemma ineq1_log_submod {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    gfn s * gfn t ≤ h (pfn s t) := by
  rcases hs0.eq_or_lt with rfl | hs0'
  · simp [gfn, pfn, f, h_one]; exact h_nonneg (by linarith) (by linarith)
  rcases hs1.eq_or_lt with rfl | hs1'
  · simp [gfn, pfn, f, h_zero]
  rcases ht0.eq_or_lt with rfl | ht0'
  · simp [gfn, pfn, f, h_one]; exact h_nonneg (by linarith) (by linarith)
  rcases ht1.eq_or_lt with rfl | ht1'
  · simp [gfn, pfn, f, h_zero]
  have hsym : ∀ a b : ℝ, pfn a b = pfn b a := fun a b => by unfold pfn f; ring
  suffices hmain : ∀ a b : ℝ, 0 < a → a ≤ b → b < 1 →
      Real.log (h (pfn a a)) + Real.log (h (pfn b b)) ≤ 2 * Real.log (h (pfn a b)) by
    have hlog : Real.log (h (pfn s s)) + Real.log (h (pfn t t)) ≤ 2 * Real.log (h (pfn s t)) := by
      rcases le_total s t with hst | hts
      · exact hmain s t hs0' hst ht1'
      · rw [add_comm, hsym s t]; exact hmain t s ht0' hts hs1'
    have hps := pfn_pos_lt_one hs0' hs1' hs0' hs1'
    have hpt := pfn_pos_lt_one ht0' ht1' ht0' ht1'
    have hpst := pfn_pos_lt_one hs0' hs1' ht0' ht1'
    have hhs : 0 < h (pfn s s) := h_pos hps.1 hps.2
    have hht : 0 < h (pfn t t) := h_pos hpt.1 hpt.2
    have hhst : 0 < h (pfn s t) := h_pos hpst.1 hpst.2
    have hexp : h (pfn s s) * h (pfn t t) ≤ h (pfn s t) ^ 2 := by
      have := Real.exp_le_exp.mpr hlog
      rw [Real.exp_add, Real.exp_log hhs, Real.exp_log hht] at this
      have h2 : Real.exp (2 * Real.log (h (pfn s t))) = h (pfn s t) ^ 2 := by
        rw [show 2 * Real.log (h (pfn s t)) = Real.log (h (pfn s t)) + Real.log (h (pfn s t)) by ring,
            Real.exp_add, Real.exp_log hhst]; ring
      linarith
    unfold gfn
    rw [← Real.sqrt_mul hhs.le]
    exact (Real.sqrt_le_iff).mpr ⟨hhst.le, hexp⟩
  intro a b ha hab hb
  let L : ℝ → ℝ → ℝ := fun x y => Real.log (h (pfn x y))
  have hd_L_diff : ∀ x ∈ Set.Icc a b,
      HasDerivAt (fun r => L r b - L r a) (dLxFn x b - dLxFn x a) x := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
    have hx1 : x < 1 := lt_of_le_of_lt hx.2 hb
    have hpb := pfn_pos_lt_one hx0 hx1 (lt_of_lt_of_le ha hab) hb
    have hpa := pfn_pos_lt_one hx0 hx1 ha (lt_of_le_of_lt hab hb)
    have h1 : HasDerivAt (fun r => L r b) (dLxFn x b) x := by
      have hh : HasDerivAt (fun r => h (pfn r b)) (hpFn (pfn x b) * pxFn x b) x := by
        simpa [Function.comp_def] using (hd_hFn hpb.1 hpb.2).comp x (hd_pxFn x b)
      have hlog : HasDerivAt (fun r => L r b) (hpFn (pfn x b) * pxFn x b / h (pfn x b)) x :=
        hh.log (h_pos hpb.1 hpb.2).ne'
      have hv : hpFn (pfn x b) * pxFn x b / h (pfn x b) = dLxFn x b := by simp only [dLxFn]; ring
      rw [hv] at hlog; exact hlog
    have h2 : HasDerivAt (fun r => L r a) (dLxFn x a) x := by
      have hh : HasDerivAt (fun r => h (pfn r a)) (hpFn (pfn x a) * pxFn x a) x := by
        simpa [Function.comp_def] using (hd_hFn hpa.1 hpa.2).comp x (hd_pxFn x a)
      have hlog : HasDerivAt (fun r => L r a) (hpFn (pfn x a) * pxFn x a / h (pfn x a)) x :=
        hh.log (h_pos hpa.1 hpa.2).ne'
      have hv : hpFn (pfn x a) * pxFn x a / h (pfn x a) = dLxFn x a := by simp only [dLxFn]; ring
      rw [hv] at hlog; exact hlog
    exact h1.sub h2
  have hanti_L : AntitoneOn (fun r => L r b - L r a) (Set.Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a b)
    · exact fun x hx => (hd_L_diff x hx).continuousAt.continuousWithinAt
    · exact fun x hx => (hd_L_diff x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' : x ∈ Set.Icc a b := interior_subset hx
      rw [(hd_L_diff x hx').deriv]
      have hx0 : 0 < x := lt_of_lt_of_le ha hx'.1
      have hx1 : x < 1 := lt_of_le_of_lt hx'.2 hb
      have hle := dLxFn_antitone hx0 hx1 ⟨ha, lt_of_le_of_lt hab hb⟩ ⟨lt_of_lt_of_le ha hab, hb⟩ hab
      linarith
  have hba := hanti_L ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  have hLsym : L b a = L a b := by simp only [L, hsym b a]
  linarith

-- ============================================================================
-- SECTION 3: Transformed G(u), Taylor bounds, & analytical boundary lemmas
-- ============================================================================

noncomputable def Afn (u : ℝ) : ℝ := 1 + (49 / 100 : ℝ) * (1 - Real.exp (-u)) ^ 2
noncomputable def wfn (u : ℝ) : ℝ := 2 * u - Real.log (Afn u)
noncomputable def Gfn (u : ℝ) : ℝ := Real.sqrt (Afn u * F (wfn u))

lemma Afn_ge_one (u : ℝ) : 1 ≤ Afn u := by
  unfold Afn
  have : 0 ≤ (49 / 100 : ℝ) * (1 - Real.exp (-u)) ^ 2 := by positivity
  linarith

lemma Afn_le (u : ℝ) (hu : 0 < u) : Afn u ≤ 149 / 100 := by
  unfold Afn
  have h1 : 0 < Real.exp (-u) := Real.exp_pos (-u)
  have h2 : Real.exp (-u) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  nlinarith

lemma wfn_pos {u : ℝ} (hu : 0 < u) : 0 < wfn u := by
  unfold wfn
  have h1 : 0 < Real.exp (-u) := Real.exp_pos (-u)
  have h2 : Real.exp (-u) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hs : 1 - Real.exp (-u) ≤ u := by linarith [Real.add_one_le_exp (-u)]
  have hA : Afn u ≤ 1 + u ^ 2 := by unfold Afn; nlinarith
  have hlog : Real.log (Afn u) ≤ Afn u - 1 := Real.log_le_sub_one_of_pos (by linarith [Afn_ge_one u])
  have hA2 : Afn u ≤ 149 / 100 := Afn_le u hu
  by_cases hu1 : u ≤ 1
  · nlinarith
  · linarith

lemma Gfn_eq_g_div {u : ℝ} (hu : 0 < u) :
    Gfn u = gfn (1 - Real.exp (-u)) / Real.exp (-u) := by
  have hx : 0 < Real.exp (-u) := Real.exp_pos (-u)
  have hw : 0 < wfn u := wfn_pos hu
  have hA : 0 < Afn u := by linarith [Afn_ge_one u]
  have hp_eq : pfn (1 - Real.exp (-u)) (1 - Real.exp (-u)) = Real.exp (-wfn u) := by
    rw [pfn_eq]
    simp only [sub_sub_cancel, wfn, neg_sub, Real.exp_sub, Real.exp_log hA]
    have h2 : Real.exp (2 * u) = (Real.exp (-u))⁻¹ ^ 2 := by
      rw [Real.exp_neg, inv_inv, ← Real.exp_nat_mul]; norm_num
    rw [h2]; unfold Afn; field_simp [hx.ne']
  have hAF : Afn u * F (wfn u) = h (pfn (1 - Real.exp (-u)) (1 - Real.exp (-u))) / Real.exp (-u) ^ 2 := by
    rw [F_eq_h_div, ← hp_eq]
    rw [hp_eq]
    simp only [wfn, neg_sub, Real.exp_sub, Real.exp_log hA]
    have h2 : Real.exp (2 * u) = (Real.exp (-u))⁻¹ ^ 2 := by
      rw [Real.exp_neg, inv_inv, ← Real.exp_nat_mul]; norm_num
    rw [h2]; field_simp [hx.ne', hA.ne']
  unfold Gfn gfn
  rw [hAF, Real.sqrt_div (h_nonneg (by rw [hp_eq]; positivity)
      (by rw [hp_eq, Real.exp_le_one_iff]; linarith)), Real.sqrt_sq hx.le]

def Ineq2UV (u v : ℝ) : Prop :=
  (2000 / 2469 : ℝ) * (F u + F v) ≤ (21 / 25 : ℝ) * F (u + v) + (4 / 25 : ℝ) * Gfn u * Gfn v

noncomputable def expNegPoly : ℕ → ℝ → ℝ
  | 0, _ => 1
  | n + 1, u => expNegPoly n u + (-u) ^ (n + 1) / (Nat.factorial (n + 1) : ℝ)

lemma expNegPoly_zero (n : ℕ) : expNegPoly n 0 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [expNegPoly, ih]

lemma hasDerivAt_expNegPoly (n : ℕ) (u : ℝ) :
    HasDerivAt (expNegPoly (n + 1)) (-expNegPoly n u) u := by
  induction n with
  | zero =>
    have hfun : expNegPoly 1 = fun x => 1 - x := by funext x; simp [expNegPoly]; ring
    rw [hfun]; simpa [expNegPoly] using (hasDerivAt_id u).const_sub 1
  | succ n ih =>
    have hd_term : HasDerivAt (fun x : ℝ => (-x) ^ (n + 2) / (Nat.factorial (n + 2) : ℝ))
        (-((-u) ^ (n + 1) / (Nat.factorial (n + 1) : ℝ))) u := by
      have h1 : HasDerivAt (fun x : ℝ => (-x) ^ (n + 2))
          (-((n + 2 : ℝ) * (-u) ^ (n + 1))) u := by
        have hraw : HasDerivAt (fun x : ℝ => (-x) ^ (n + 2))
            (((n + 2 : ℕ) : ℝ) * (-u) ^ (n + 2 - 1) * -1) u :=
          (hasDerivAt_id u).neg.pow (n + 2)
        have hv : ((n + 2 : ℕ) : ℝ) * (-u) ^ (n + 2 - 1) * -1 = -((n + 2 : ℝ) * (-u) ^ (n + 1)) := by
          push_cast; ring
        rw [hv] at hraw; exact hraw
      have h2 := h1.div_const (Nat.factorial (n + 2) : ℝ)
      have hv : -((n + 2 : ℝ) * (-u) ^ (n + 1)) / (Nat.factorial (n + 2) : ℝ) =
          -((-u) ^ (n + 1) / (Nat.factorial (n + 1) : ℝ)) := by
        have hfac : (Nat.factorial (n + 2) : ℝ) = (n + 2 : ℝ) * (Nat.factorial (n + 1) : ℝ) := by
          rw [Nat.factorial_succ]; push_cast; ring
        have hpos1 : (Nat.factorial (n + 1) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
        have hpos2 : (n + 2 : ℝ) ≠ 0 := by positivity
        rw [hfac]; field_simp [hpos1, hpos2]
      rw [hv] at h2; exact h2
    have hsum := ih.add hd_term
    have hv : -expNegPoly n u + -((-u) ^ (n + 1) / (Nat.factorial (n + 1) : ℝ)) =
        -expNegPoly (n + 1) u := by simp only [expNegPoly]; ring
    rw [hv] at hsum; exact hsum

lemma expNeg_taylor_even_odd :
    ∀ k : ℕ, (∀ u : ℝ, 0 ≤ u → Real.exp (-u) ≤ expNegPoly (2 * k) u) ∧
             (∀ u : ℝ, 0 ≤ u → expNegPoly (2 * k + 1) u ≤ Real.exp (-u)) := by
  intro k
  induction k with
  | zero =>
    constructor
    · intro u hu; simp [expNegPoly, Real.exp_le_one_iff]; linarith
    · intro u hu
      have : expNegPoly 1 u = 1 - u := by simp [expNegPoly]; ring
      rw [this]; linarith [Real.add_one_le_exp (-u)]
  | succ k ih =>
    have h_even : ∀ u : ℝ, 0 ≤ u → Real.exp (-u) ≤ expNegPoly (2 * (k + 1)) u := by
      intro u hu
      let d : ℝ → ℝ := fun x => expNegPoly (2 * k + 2) x - Real.exp (-x)
      have hd : ∀ x : ℝ, HasDerivAt d (Real.exp (-x) - expNegPoly (2 * k + 1) x) x := by
        intro x
        have h1 := hasDerivAt_expNegPoly (2 * k + 1) x
        have h2 : HasDerivAt (fun r => Real.exp (-r)) (-Real.exp (-x)) x := by
          simpa using (hasDerivAt_id x).neg.exp
        have hsub := h1.sub h2
        have hv : -expNegPoly (2 * k + 1) x - -Real.exp (-x) =
            Real.exp (-x) - expNegPoly (2 * k + 1) x := by ring
        rw [hv] at hsub; exact hsub
      have hmono : MonotoneOn d (Set.Ici 0) := by
        apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
        · exact fun x _ => (hd x).continuousAt.continuousWithinAt
        · exact fun x _ => (hd x).differentiableAt.differentiableWithinAt
        · intro x hx
          rw [(hd x).deriv]
          have hx' : 0 ≤ x := interior_subset hx
          linarith [ih.2 x hx']
      have h0 := hmono (Set.mem_Ici.mpr le_rfl) hu hu
      simp only [d, expNegPoly_zero, neg_zero, Real.exp_zero, sub_self] at h0
      have h2k : 2 * (k + 1) = 2 * k + 2 := by ring
      rw [h2k]; linarith
    have h_odd : ∀ u : ℝ, 0 ≤ u → expNegPoly (2 * (k + 1) + 1) u ≤ Real.exp (-u) := by
      intro u hu
      let d : ℝ → ℝ := fun x => Real.exp (-x) - expNegPoly (2 * (k + 1) + 1) x
      have hd : ∀ x : ℝ, HasDerivAt d (expNegPoly (2 * (k + 1)) x - Real.exp (-x)) x := by
        intro x
        have h1 : HasDerivAt (fun r => Real.exp (-r)) (-Real.exp (-x)) x := by
          simpa using (hasDerivAt_id x).neg.exp
        have h2 := hasDerivAt_expNegPoly (2 * (k + 1)) x
        have hsub := h1.sub h2
        have hv : -Real.exp (-x) - -expNegPoly (2 * (k + 1)) x =
            expNegPoly (2 * (k + 1)) x - Real.exp (-x) := by ring
        rw [hv] at hsub; exact hsub
      have hmono : MonotoneOn d (Set.Ici 0) := by
        apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
        · exact fun x _ => (hd x).continuousAt.continuousWithinAt
        · exact fun x _ => (hd x).differentiableAt.differentiableWithinAt
        · intro x hx
          rw [(hd x).deriv]
          have hx' : 0 ≤ x := interior_subset hx
          linarith [h_even x hx']
      have h0 := hmono (Set.mem_Ici.mpr le_rfl) hu hu
      simp only [d, expNegPoly_zero, neg_zero, Real.exp_zero, sub_self] at h0
      linarith
    exact ⟨h_even, h_odd⟩

lemma expNeg_ge_poly7 {u : ℝ} (hu : 0 ≤ u) :
    1 - u + u ^ 2 / 2 - u ^ 3 / 6 + u ^ 4 / 24 - u ^ 5 / 120 + u ^ 6 / 720 - u ^ 7 / 5040 ≤
      Real.exp (-u) := by
  have h := (expNeg_taylor_even_odd 3).2 u hu
  convert h using 1
  simp only [expNegPoly, Nat.factorial]; norm_num; ring

lemma expNeg_le_poly8 {u : ℝ} (hu : 0 ≤ u) :
    Real.exp (-u) ≤
      1 - u + u ^ 2 / 2 - u ^ 3 / 6 + u ^ 4 / 24 - u ^ 5 / 120 + u ^ 6 / 720 -
        u ^ 7 / 5040 + u ^ 8 / 40320 := by
  have h := (expNeg_taylor_even_odd 4).1 u hu
  convert h using 1
  simp only [expNegPoly, Nat.factorial]; norm_num; ring

lemma exp_neg_eight_le : Real.exp (-8 : ℝ) ≤ 1 / 2000 := by
  have h1 : (7 : ℝ) ≤ Real.exp 2 := by
    have h := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num) 5
    simp [Finset.sum_range_succ, Nat.factorial] at h
    norm_num at h; linarith
  have h2 : (2000 : ℝ) ≤ Real.exp 8 := by
    have he8 : Real.exp (8 : ℝ) = (Real.exp 2) ^ 4 := by
      rw [← Real.exp_nat_mul]; norm_num
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7) h1 4
    rw [he8]; norm_num at hp; linarith
  rw [Real.exp_neg, one_div]
  exact inv_anti₀ (by norm_num) h2

lemma log_two_le : Real.log 2 ≤ 694 / 1000 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 694 / 1000 by norm_num) 6
  simp [Finset.sum_range_succ, Nat.factorial] at h
  norm_num at h; linarith

lemma log_200_ge : (529 / 100 : ℝ) ≤ Real.log 200 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h1 := expNeg_ge_poly7 (show (0 : ℝ) ≤ 529 / 800 by norm_num)
  have h2 : (516 / 1000 : ℝ) ≤ Real.exp (-(529 / 800 : ℝ)) := by norm_num at h1; linarith
  have h3 : Real.exp (529 / 800 : ℝ) ≤ 1000 / 516 := by
    rw [Real.exp_neg] at h2
    have := inv_anti₀ (by norm_num : (0 : ℝ) < 516 / 1000) h2
    rw [inv_inv] at this; norm_num at this; linarith
  have h4 : Real.exp (529 / 100 : ℝ) = (Real.exp (529 / 800 : ℝ)) ^ 8 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h4]
  have hpow : (Real.exp (529 / 800 : ℝ)) ^ 8 ≤ (1000 / 516 : ℝ) ^ 8 :=
    pow_le_pow_left₀ (Real.exp_pos _).le h3 8
  norm_num at hpow; linarith

lemma ineq2_tail {u v : ℝ} (hu : 0 < u) (hv : 0 < v) (hsum : 27 ≤ u + v) :
    Ineq2UV u v := by
  unfold Ineq2UV
  have hFuv : u + v + 1 - 1 / 2000 ≤ F (u + v) := by
    have h1 := F_ge_add_one_sub_exp (add_pos hu hv)
    have h2 : Real.exp (-(u + v)) ≤ Real.exp (-8) := Real.exp_le_exp.mpr (by linarith)
    linarith [h1, h2, exp_neg_eight_le]
  have hFu := F_le_add_one hu
  have hFv := F_le_add_one hv
  have hG : 0 ≤ Gfn u * Gfn v := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  nlinarith

lemma F_double_ge_corner {w : ℝ} (hw0 : 0 < w) (hw1 : w ≤ 1 / 200) :
    (173 / 100 : ℝ) * F w ≤ F (2 * w) := by
  have he2w : 2 * w ≤ Real.exp (2 * w) - 1 := by linarith [Real.add_one_le_exp (2 * w)]
  have h1me2w : 1 - Real.exp (-(2 * w)) ≤ 2 * w := by linarith [Real.add_one_le_exp (-(2 * w))]
  have h1me2w_pos : 0 < 1 - Real.exp (-(2 * w)) := by
    have : Real.exp (-(2 * w)) < 1 := by rw [Real.exp_lt_one_iff]; linarith
    linarith
  have hlog2w : Real.log (1 / w) - Real.log 2 ≤ -Real.log (1 - Real.exp (-(2 * w))) := by
    have h1 : Real.log (1 - Real.exp (-(2 * w))) ≤ Real.log (2 * w) :=
      Real.log_le_log h1me2w_pos h1me2w
    have h2 : Real.log (2 * w) = Real.log 2 - Real.log (1 / w) := by
      rw [Real.log_mul (by norm_num) hw0.ne', one_div, Real.log_inv]; ring
    linarith
  have hL_ge : (529 / 100 : ℝ) ≤ Real.log (1 / w) := by
    have : (200 : ℝ) ≤ 1 / w := by rw [le_div_iff₀ hw0]; linarith
    exact le_trans log_200_ge (Real.log_le_log (by norm_num) this)
  have hF2w_lo : 2 * w * (Real.log (1 / w) + 1 - 694 / 1000) ≤ F (2 * w) := by
    unfold F
    have hpos : 0 ≤ Real.log (1 / w) - Real.log 2 := by linarith [hL_ge, log_two_le]
    nlinarith [mul_le_mul he2w hlog2w hpos (by linarith : 0 ≤ Real.exp (2 * w) - 1), log_two_le]
  have hew_hi : Real.exp w - 1 ≤ (1006 / 1000 : ℝ) * w := by
    have h1 : 1 - w ≤ Real.exp (-w) := by linarith [Real.add_one_le_exp (-w)]
    have h2 : Real.exp w ≤ 1 / (1 - w) := by
      rw [Real.exp_neg] at h1
      have := inv_anti₀ (by linarith : 0 < 1 - w) h1
      rw [inv_inv] at this; rw [one_div]; exact this
    have h3 : 1 / (1 - w) - 1 ≤ (1006 / 1000 : ℝ) * w := by
      have h1w : 0 < 1 - w := by linarith
      rw [div_sub_one h1w.ne', div_le_iff₀ h1w]; nlinarith
    linarith
  have h1mew_lo : w * Real.exp (-w) ≤ 1 - Real.exp (-w) := by
    have h1 : w ≤ Real.exp w - 1 := by linarith [Real.add_one_le_exp w]
    have hprod : Real.exp w * Real.exp (-w) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [mul_le_mul_of_nonneg_right h1 (Real.exp_pos (-w)).le]
  have hlogw_hi : -Real.log (1 - Real.exp (-w)) ≤ Real.log (1 / w) + w := by
    have h1 : Real.log (w * Real.exp (-w)) ≤ Real.log (1 - Real.exp (-w)) :=
      Real.log_le_log (mul_pos hw0 (Real.exp_pos (-w))) h1mew_lo
    rw [Real.log_mul hw0.ne' (Real.exp_pos (-w)).ne', Real.log_exp] at h1
    rw [one_div, Real.log_inv]; linarith
  have hFw_hi : F w ≤ w * ((1006 / 1000 : ℝ) * Real.log (1 / w) + 1006 / 1000) := by
    unfold F
    have hew0 : 0 ≤ Real.exp w - 1 := by linarith [Real.add_one_le_exp w]
    have hlog0 : 0 ≤ -Real.log (1 - Real.exp (-w)) := by
      have : Real.exp (-w) < 1 := by rw [Real.exp_lt_one_iff]; linarith
      have : Real.log (1 - Real.exp (-w)) ≤ 0 :=
        Real.log_nonpos (by linarith) (by linarith [Real.exp_pos (-w)])
      linarith
    have hmul := mul_le_mul hew_hi hlogw_hi hlog0 (by positivity)
    nlinarith
  nlinarith

lemma G_sq_ge_corner {w : ℝ} (hw0 : 0 < w) (hw1 : w ≤ 1 / 200) :
    (172 / 100 : ℝ) * F w ≤ Gfn w ^ 2 := by
  have hA1 : 1 ≤ Afn w := Afn_ge_one w
  have hw_pos : 0 < wfn w := wfn_pos hw0
  have hGsq : Gfn w ^ 2 = Afn w * F (wfn w) :=
    Real.sq_sqrt (mul_nonneg (by linarith) (F_pos hw_pos).le)
  rw [hGsq]
  have hs : 1 - Real.exp (-w) ≤ w := by linarith [Real.add_one_le_exp (-w)]
  have hs0 : 0 ≤ 1 - Real.exp (-w) := by
    have : Real.exp (-w) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
    linarith
  have hlogA : Real.log (Afn w) ≤ (3 / 1000 : ℝ) * w := by
    have h1 : Real.log (Afn w) ≤ Afn w - 1 := Real.log_le_sub_one_of_pos (by linarith)
    unfold Afn at h1 ⊢; nlinarith
  have hw_lo : (1997 / 1000 : ℝ) * w ≤ wfn w := by unfold wfn; linarith
  have hsec : (1996 / 1999 : ℝ) * F (2 * w) ≤ F ((1997 / 1000 : ℝ) * w) := by
    have h1 := F_secant_le (show 0 < w / 1000 by linarith) (show w / 1000 < 2 * w by linarith)
      (show (0 : ℝ) ≤ 1996 / 1999 by norm_num) (show (1996 / 1999 : ℝ) ≤ 1 by norm_num)
    have harg : (1 - (1996 / 1999 : ℝ)) * (w / 1000) + (1996 / 1999 : ℝ) * (2 * w) =
        (1997 / 1000 : ℝ) * w := by ring
    rw [harg] at h1
    have hpos : 0 ≤ (1 - (1996 / 1999 : ℝ)) * F (w / 1000) :=
      mul_nonneg (by norm_num) (F_pos (by linarith)).le
    linarith
  have hF_mono : F ((1997 / 1000 : ℝ) * w) ≤ F (wfn w) :=
    F_strictMono.monotoneOn (show 0 < (1997 / 1000 : ℝ) * w by linarith) hw_pos hw_lo
  have hF2 := F_double_ge_corner hw0 hw1
  have hFw_pos : 0 < F w := F_pos hw0
  have hF_ge : (172 / 100 : ℝ) * F w ≤ F (wfn w) := by linarith
  nlinarith

lemma ineq2_corner {u v : ℝ} (hv0 : 0 < v) (hvu : v ≤ u) (hu1 : u ≤ 1 / 200) :
    Ineq2UV u v := by
  unfold Ineq2UV
  have hu0 : 0 < u := lt_of_lt_of_le hv0 hvu
  set a := Real.sqrt (F v)
  set b := Real.sqrt (F u)
  have ha0 : 0 < a := Real.sqrt_pos.mpr (F_pos hv0)
  have hb0 : 0 < b := Real.sqrt_pos.mpr (F_pos hu0)
  have ha2 : a ^ 2 = F v := Real.sq_sqrt (F_pos hv0).le
  have hb2 : b ^ 2 = F u := Real.sq_sqrt (F_pos hu0).le
  have hab : a ≤ b := Real.sqrt_le_sqrt (F_strictMono.monotoneOn hv0 hu0 hvu)
  have hF1 : b ^ 2 ≤ F (u + v) := by
    rw [hb2]; exact F_strictMono.monotoneOn hu0 (add_pos hu0 hv0) (by linarith)
  have hF2 : (173 / 200 : ℝ) * (a ^ 2 + b ^ 2) ≤ F (u + v) := by
    set m := (u + v) / 2
    have hm0 : 0 < m := by simp only [m]; linarith
    have hm1 : m ≤ 1 / 200 := by simp only [m]; linarith
    have hd : (173 / 100 : ℝ) * F m ≤ F (2 * m) := F_double_ge_corner hm0 hm1
    have h2m : 2 * m = u + v := by simp only [m]; ring
    rw [h2m] at hd
    have hconc : (1 / 2 : ℝ) * F v + (1 / 2 : ℝ) * F u ≤ F m := by
      rcases hvu.eq_or_lt with rfl | hlt
      · have hm_eq : m = v := by simp only [m]; ring
        rw [hm_eq]; linarith
      · have := F_secant_le hv0 hlt (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (1 / 2 : ℝ) ≤ 1 by norm_num)
        have harg : (1 - (1 / 2 : ℝ)) * v + (1 / 2 : ℝ) * u = m := by simp only [m]; ring
        rw [harg] at this; linarith
    rw [ha2, hb2]; linarith
  have hG : (172 / 100 : ℝ) * (a * b) ≤ Gfn u * Gfn v := by
    have hGu : Real.sqrt (172 / 100 : ℝ) * b ≤ Gfn u := by
      have h1 := G_sq_ge_corner hu0 hu1
      have hsq : (Real.sqrt (172 / 100 : ℝ) * b) ^ 2 ≤ Gfn u ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by norm_num), hb2]; exact h1
      have hnn1 : 0 ≤ Real.sqrt (172 / 100 : ℝ) * b := by positivity
      have hnn2 : 0 ≤ Gfn u := Real.sqrt_nonneg _
      nlinarith
    have hGv : Real.sqrt (172 / 100 : ℝ) * a ≤ Gfn v := by
      have h1 := G_sq_ge_corner hv0 (le_trans hvu hu1)
      have hsq : (Real.sqrt (172 / 100 : ℝ) * a) ^ 2 ≤ Gfn v ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by norm_num), ha2]; exact h1
      have hnn1 : 0 ≤ Real.sqrt (172 / 100 : ℝ) * a := by positivity
      have hnn2 : 0 ≤ Gfn v := Real.sqrt_nonneg _
      nlinarith
    have hmul := mul_le_mul hGu hGv (by positivity) (Real.sqrt_nonneg _)
    have hrew : Real.sqrt (172 / 100 : ℝ) * b * (Real.sqrt (172 / 100 : ℝ) * a) =
        (172 / 100 : ℝ) * (a * b) := by
      have hsq : Real.sqrt (172 / 100 : ℝ) * Real.sqrt (172 / 100 : ℝ) = 172 / 100 :=
        Real.mul_self_sqrt (by norm_num)
      calc Real.sqrt (172 / 100 : ℝ) * b * (Real.sqrt (172 / 100 : ℝ) * a)
          = (Real.sqrt (172 / 100 : ℝ) * Real.sqrt (172 / 100 : ℝ)) * (a * b) := by ring
        _ = (172 / 100 : ℝ) * (a * b) := by rw [hsq]
    linarith
  rw [← ha2, ← hb2]
  by_cases hcase : a ≤ (39 / 100 : ℝ) * b
  · have h1 : a * a ≤ (39 / 100 : ℝ) * b * a := mul_le_mul_of_nonneg_right hcase ha0.le
    have h2 : a * b ≤ (39 / 100 : ℝ) * b * b := mul_le_mul_of_nonneg_right hcase hb0.le
    nlinarith
  · have hgt : (39 / 100 : ℝ) * b < a := not_le.mp hcase
    have hprod : 0 ≤ (a - (39 / 100 : ℝ) * b) * (b - a) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith

lemma ineq2_strip {u v : ℝ} (hv0 : 0 < v) (hv1 : v ≤ 1 / 10000) (hu1 : 1 / 200 ≤ u) :
    Ineq2UV u v := by
  unfold Ineq2UV
  have hu0 : 0 < u := by linarith
  have hFuv : F u ≤ F (u + v) := F_strictMono.monotoneOn hu0 (add_pos hu0 hv0) (by linarith)
  have hG : 0 ≤ Gfn u * Gfn v := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hFv_hi : F v ≤ 11 / 10000 := by
    have hm : F v ≤ F (1 / 10000) := F_strictMono.monotoneOn hv0 (by norm_num) hv1
    have hlog10000 : Real.log (10000 : ℝ) ≤ 922 / 100 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have h1 : (100 : ℝ) ≤ Real.exp (461 / 100 : ℝ) := by
        have hs := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 461 / 800 by norm_num) 6
        simp [Finset.sum_range_succ, Nat.factorial] at hs
        have hstep : (1779 / 1000 : ℝ) ≤ Real.exp (461 / 800 : ℝ) := by norm_num at hs; linarith
        have he : Real.exp (461 / 100 : ℝ) = (Real.exp (461 / 800 : ℝ)) ^ 8 := by
          rw [← Real.exp_nat_mul]; norm_num
        rw [he]
        have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1779 / 1000) hstep 8
        norm_num at hp; linarith
      have he2 : Real.exp (922 / 100 : ℝ) = (Real.exp (461 / 100 : ℝ)) ^ 2 := by
        rw [← Real.exp_nat_mul]; norm_num
      rw [he2]; nlinarith
    have hF10 : F (1 / 10000 : ℝ) ≤ 11 / 10000 := by
      unfold F
      set w : ℝ := 1 / 10000
      have hew : Real.exp w - 1 ≤ (1001 / 1000 : ℝ) * w := by
        have h1 : 1 - w ≤ Real.exp (-w) := by linarith [Real.add_one_le_exp (-w)]
        rw [Real.exp_neg] at h1
        have h2 := inv_anti₀ (by norm_num : 0 < 1 - w) h1
        rw [inv_inv] at h2; norm_num [w] at h2 ⊢; linarith
      have h1mew : w * Real.exp (-w) ≤ 1 - Real.exp (-w) := by
        have h1 : w ≤ Real.exp w - 1 := by linarith [Real.add_one_le_exp w]
        have hprod : Real.exp w * Real.exp (-w) = 1 := by rw [← Real.exp_add]; simp
        nlinarith [mul_le_mul_of_nonneg_right h1 (Real.exp_pos (-w)).le]
      have hlog : -Real.log (1 - Real.exp (-w)) ≤ 922 / 100 + w := by
        have h1 := Real.log_le_log (mul_pos (by norm_num : 0 < w) (Real.exp_pos (-w))) h1mew
        rw [Real.log_mul (by norm_num) (Real.exp_pos (-w)).ne', Real.log_exp] at h1
        have hlw : Real.log w = -Real.log (10000 : ℝ) := by simp [w]
        rw [hlw] at h1
        have h2 : -Real.log (1 - Real.exp (-w)) ≤ Real.log (10000 : ℝ) + w := by linarith
        exact le_trans h2 (add_le_add hlog10000 le_rfl)
      have he0 : 0 ≤ Real.exp w - 1 := by linarith [Real.add_one_le_exp w]
      have hl0 : 0 ≤ -Real.log (1 - Real.exp (-w)) := by
        have hlt : Real.exp (-w) < 1 := by rw [Real.exp_lt_one_iff]; norm_num [w]
        have := Real.log_nonpos (x := 1 - Real.exp (-w)) (by linarith) (by linarith [Real.exp_pos (-w)])
        linarith
      have := mul_le_mul hew hlog hl0 (by positivity)
      norm_num [w] at this ⊢; linarith
    linarith
  have hFu_lo : (31 / 1000 : ℝ) ≤ F u := by
    have hm : F (1 / 200) ≤ F u := F_strictMono.monotoneOn (by norm_num) hu0 hu1
    have hF200 : (31 / 1000 : ℝ) ≤ F (1 / 200 : ℝ) := by
      unfold F
      set w : ℝ := 1 / 200
      have hew : w ≤ Real.exp w - 1 := by linarith [Real.add_one_le_exp w]
      have h1mew : 1 - Real.exp (-w) ≤ w := by linarith [Real.add_one_le_exp (-w)]
      have hpos : 0 < 1 - Real.exp (-w) := by
        have : Real.exp (-w) < 1 := by rw [Real.exp_lt_one_iff]; norm_num [w]
        linarith
      have hlog : (529 / 100 : ℝ) ≤ -Real.log (1 - Real.exp (-w)) := by
        have h1 := Real.log_le_log hpos h1mew
        have hlw : Real.log w = -Real.log 200 := by simp [w]
        linarith [log_200_ge]
      have hmul := mul_le_mul hew hlog (by norm_num) (by linarith)
      norm_num [w] at hmul ⊢; linarith
    linarith
  nlinarith

-- ============================================================================
-- SECTION 4: Exact Fixed-Point Int Certificate & Soundness (ZERO native_decide!)
-- ============================================================================

def SC : Int := 1000000000000
def fdiv (a b : Int) : Int := Int.ediv a b
def cdiv (a b : Int) : Int := -Int.ediv (-a) b

lemma SC_pos : (0 : ℝ) < (SC : ℝ) := by norm_num [SC]
lemma SC_pos_int : (0 : Int) < SC := by decide

lemma fdiv_le_div {a b : Int} (hb : 0 < b) : ((fdiv a b : Int) : ℝ) ≤ (a : ℝ) / (b : ℝ) := by
  have hbR : (0 : ℝ) < (b : ℝ) := Int.cast_pos.mpr hb
  rw [le_div_iff₀ hbR]
  have h1 : Int.ediv a b * b ≤ a := Int.ediv_mul_le a (Int.ne_of_gt hb)
  exact_mod_cast h1

lemma div_le_cdiv {a b : Int} (hb : 0 < b) : (a : ℝ) / (b : ℝ) ≤ ((cdiv a b : Int) : ℝ) := by
  have hbR : (0 : ℝ) < (b : ℝ) := Int.cast_pos.mpr hb
  rw [div_le_iff₀ hbR]
  have h1 : Int.ediv (-a) b * b ≤ -a := Int.ediv_mul_le (-a) (Int.ne_of_gt hb)
  have h2 : a ≤ (-Int.ediv (-a) b) * b := by linarith
  exact_mod_cast h2

def expNegLoSmall (t : Int) : Int :=
  let p1 := t
  let p2Lo := fdiv (p1 * t) SC; let p2Hi := cdiv (p1 * t) SC
  let p3Lo := fdiv (p2Lo * t) SC; let p3Hi := cdiv (p2Hi * t) SC
  let p4Lo := fdiv (p3Lo * t) SC; let p4Hi := cdiv (p3Hi * t) SC
  let p5Lo := fdiv (p4Lo * t) SC; let p5Hi := cdiv (p4Hi * t) SC
  let p6Lo := fdiv (p5Lo * t) SC; let p6Hi := cdiv (p5Hi * t) SC
  let p7Hi := cdiv (p6Hi * t) SC
  let res := SC - p1 + fdiv p2Lo 2 - cdiv p3Hi 6 + fdiv p4Lo 24 - cdiv p5Hi 120 + fdiv p6Lo 720 - cdiv p7Hi 5040
  if res < 0 then 0 else res

def expNegHiSmall (t : Int) : Int :=
  let p1 := t
  let p2Lo := fdiv (p1 * t) SC; let p2Hi := cdiv (p1 * t) SC
  let p3Lo := fdiv (p2Lo * t) SC; let p3Hi := cdiv (p2Hi * t) SC
  let p4Lo := fdiv (p3Lo * t) SC; let p4Hi := cdiv (p3Hi * t) SC
  let p5Lo := fdiv (p4Lo * t) SC; let p5Hi := cdiv (p4Hi * t) SC
  let p6Lo := fdiv (p5Lo * t) SC; let p6Hi := cdiv (p5Hi * t) SC
  let p7Lo := fdiv (p6Lo * t) SC; let p7Hi := cdiv (p6Hi * t) SC
  let p8Hi := cdiv (p7Hi * t) SC
  let res := SC - p1 + cdiv p2Hi 2 - fdiv p3Lo 6 + cdiv p4Hi 24 - fdiv p5Lo 120 + cdiv p6Hi 720 - fdiv p7Lo 5040 + cdiv p8Hi 40320
  if res > SC then SC else res

def sqLo10 (x : Int) : Int :=
  let x := fdiv (x * x) SC; let x := fdiv (x * x) SC
  let x := fdiv (x * x) SC; let x := fdiv (x * x) SC
  let x := fdiv (x * x) SC; let x := fdiv (x * x) SC
  let x := fdiv (x * x) SC; let x := fdiv (x * x) SC
  let x := fdiv (x * x) SC; fdiv (x * x) SC

def sqHi10 (x : Int) : Int :=
  let x := cdiv (x * x) SC; let x := cdiv (x * x) SC
  let x := cdiv (x * x) SC; let x := cdiv (x * x) SC
  let x := cdiv (x * x) SC; let x := cdiv (x * x) SC
  let x := cdiv (x * x) SC; let x := cdiv (x * x) SC
  let x := cdiv (x * x) SC; cdiv (x * x) SC

def expNegLo (x : Int) : Int := sqLo10 (expNegLoSmall (cdiv x 1024))
def expNegHi (x : Int) : Int := sqHi10 (expNegHiSmall (fdiv x 1024))

lemma fdiv_mul_nonneg {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ fdiv (a * b) SC :=
  Int.ediv_nonneg (mul_nonneg ha hb) SC_pos_int.le

lemma expNegLoSmall_nonneg (t : Int) : 0 ≤ expNegLoSmall t := by
  unfold expNegLoSmall; dsimp only; split_ifs with h <;> omega

lemma expNegHiSmall_le_SC (t : Int) : expNegHiSmall t ≤ SC := by
  unfold expNegHiSmall; dsimp only; split_ifs with h <;> omega

lemma cdiv_sq_le_SC {x : Int} (hx0 : 0 ≤ x) (hx1 : x ≤ SC) :
    0 ≤ cdiv (x * x) SC ∧ cdiv (x * x) SC ≤ SC := by
  have hsq0 : 0 ≤ x * x := mul_nonneg hx0 hx0
  have hsq1 : x * x ≤ SC * SC := mul_le_mul hx1 hx1 hx0 SC_pos_int.le
  constructor
  · have h1 : (0 : ℝ) ≤ (x * x : ℝ) / SC := by
      exact_mod_cast div_nonneg (show (0 : ℝ) ≤ (x * x : ℝ) by exact_mod_cast hsq0) SC_pos.le
    have h2 := div_le_cdiv (a := x * x) SC_pos_int
    have h3 : (0 : ℝ) ≤ (cdiv (x * x) SC : ℝ) := le_trans (by exact_mod_cast h1) h2
    exact_mod_cast h3
  · unfold cdiv
    have hneg : -(SC * SC) ≤ -(x * x) := by linarith
    have hdiv : Int.ediv (-(SC * SC)) SC ≤ Int.ediv (-(x * x)) SC :=
      Int.ediv_le_ediv SC_pos_int hneg
    have heq : Int.ediv (-(SC * SC)) SC = -SC := by decide
    omega

lemma expNegLoSmall_sound {t : Int} (ht : 0 ≤ t) :
    ((expNegLoSmall t : Int) : ℝ) / (SC : ℝ) ≤ Real.exp (-((t : ℝ) / (SC : ℝ))) := by
  set u : ℝ := (t : ℝ) / (SC : ℝ)
  have hu : 0 ≤ u := div_nonneg (by exact_mod_cast ht) SC_pos.le
  unfold expNegLoSmall; dsimp only
  split_ifs with hneg
  · simp; exact (Real.exp_pos _).le
  · have hSC : (0 : ℝ) < (SC : ℝ) := SC_pos
    have stepLo : ∀ a : Int, ∀ x : ℝ, ((a : ℝ) / SC) ≤ x →
        ((fdiv (a * t) SC : Int) : ℝ) / SC ≤ x * u := by
      intro a x hax
      have h1 := fdiv_le_div (a := a * t) SC_pos_int
      have h2 : ((fdiv (a * t) SC : Int) : ℝ) / SC ≤ ((a : ℝ) / SC) * u := by
        simp only [u]; push_cast at h1; rw [div_le_iff₀ hSC]
        have : ((a : ℝ) / SC) * ((t : ℝ) / SC) * SC = (a : ℝ) * (t : ℝ) / SC := by field_simp [hSC.ne']
        linarith
      exact le_trans h2 (mul_le_mul_of_nonneg_right hax hu)
    have stepHi : ∀ a : Int, ∀ x : ℝ, x ≤ ((a : ℝ) / SC) →
        x * u ≤ ((cdiv (a * t) SC : Int) : ℝ) / SC := by
      intro a x hxa
      have h1 := div_le_cdiv (a := a * t) SC_pos_int
      have h2 : ((a : ℝ) / SC) * u ≤ ((cdiv (a * t) SC : Int) : ℝ) / SC := by
        simp only [u]; push_cast at h1; rw [le_div_iff₀ hSC]
        have : ((a : ℝ) / SC) * ((t : ℝ) / SC) * SC = (a : ℝ) * (t : ℝ) / SC := by field_simp [hSC.ne']
        linarith
      exact le_trans (mul_le_mul_of_nonneg_right hxa hu) h2
    set p2Lo := fdiv (t * t) SC; set p2Hi := cdiv (t * t) SC
    set p3Lo := fdiv (p2Lo * t) SC; set p3Hi := cdiv (p2Hi * t) SC
    set p4Lo := fdiv (p3Lo * t) SC; set p4Hi := cdiv (p3Hi * t) SC
    set p5Lo := fdiv (p4Lo * t) SC; set p5Hi := cdiv (p4Hi * t) SC
    set p6Lo := fdiv (p5Lo * t) SC; set p6Hi := cdiv (p5Hi * t) SC
    set p7Hi := cdiv (p6Hi * t) SC
    have h2l : (p2Lo : ℝ) / SC ≤ u ^ 2 := by simpa [sq] using stepLo t u le_rfl
    have h2h : u ^ 2 ≤ (p2Hi : ℝ) / SC := by simpa [sq] using stepHi t u le_rfl
    have h3l : (p3Lo : ℝ) / SC ≤ u ^ 3 := by simpa [pow_succ] using stepLo p2Lo (u ^ 2) h2l
    have h3h : u ^ 3 ≤ (p3Hi : ℝ) / SC := by simpa [pow_succ] using stepHi p2Hi (u ^ 2) h2h
    have h4l : (p4Lo : ℝ) / SC ≤ u ^ 4 := by simpa [pow_succ] using stepLo p3Lo (u ^ 3) h3l
    have h4h : u ^ 4 ≤ (p4Hi : ℝ) / SC := by simpa [pow_succ] using stepHi p3Hi (u ^ 3) h3h
    have h5l : (p5Lo : ℝ) / SC ≤ u ^ 5 := by simpa [pow_succ] using stepLo p4Lo (u ^ 4) h4l
    have h5h : u ^ 5 ≤ (p5Hi : ℝ) / SC := by simpa [pow_succ] using stepHi p4Hi (u ^ 4) h4h
    have h6l : (p6Lo : ℝ) / SC ≤ u ^ 6 := by simpa [pow_succ] using stepLo p5Lo (u ^ 5) h5l
    have h6h : u ^ 6 ≤ (p6Hi : ℝ) / SC := by simpa [pow_succ] using stepHi p5Hi (u ^ 5) h5h
    have h7h : u ^ 7 ≤ (p7Hi : ℝ) / SC := by simpa [pow_succ] using stepHi p6Hi (u ^ 6) h6h
    have d2 := fdiv_le_div (a := p2Lo) (b := 2) (by decide)
    have d3 := div_le_cdiv (a := p3Hi) (b := 6) (by decide)
    have d4 := fdiv_le_div (a := p4Lo) (b := 24) (by decide)
    have d5 := div_le_cdiv (a := p5Hi) (b := 120) (by decide)
    have d6 := fdiv_le_div (a := p6Lo) (b := 720) (by decide)
    have d7 := div_le_cdiv (a := p7Hi) (b := 5040) (by decide)
    have htay := expNeg_ge_poly7 hu
    have hdiv_all :
        ((SC - t + fdiv p2Lo 2 - cdiv p3Hi 6 + fdiv p4Lo 24 - cdiv p5Hi 120 +
            fdiv p6Lo 720 - cdiv p7Hi 5040 : Int) : ℝ) / SC ≤
        1 - u + u ^ 2 / 2 - u ^ 3 / 6 + u ^ 4 / 24 - u ^ 5 / 120 + u ^ 6 / 720 - u ^ 7 / 5040 := by
      push_cast at d2 d3 d4 d5 d6 d7 ⊢
      rw [div_le_iff₀ hSC]
      have hmul2 : (fdiv p2Lo 2 : ℝ) ≤ u ^ 2 / 2 * SC := by
        have : (p2Lo : ℝ) ≤ u ^ 2 * SC := by rwa [div_le_iff₀ hSC] at h2l
        linarith
      have hmul3 : u ^ 3 / 6 * SC ≤ (cdiv p3Hi 6 : ℝ) := by
        have : u ^ 3 * SC ≤ (p3Hi : ℝ) := by rwa [le_div_iff₀ hSC] at h3h
        linarith
      have hmul4 : (fdiv p4Lo 24 : ℝ) ≤ u ^ 4 / 24 * SC := by
        have : (p4Lo : ℝ) ≤ u ^ 4 * SC := by rwa [div_le_iff₀ hSC] at h4l
        linarith
      have hmul5 : u ^ 5 / 120 * SC ≤ (cdiv p5Hi 120 : ℝ) := by
        have : u ^ 5 * SC ≤ (p5Hi : ℝ) := by rwa [le_div_iff₀ hSC] at h5h
        linarith
      have hmul6 : (fdiv p6Lo 720 : ℝ) ≤ u ^ 6 / 720 * SC := by
        have : (p6Lo : ℝ) ≤ u ^ 6 * SC := by rwa [div_le_iff₀ hSC] at h6l
        linarith
      have hmul7 : u ^ 7 / 5040 * SC ≤ (cdiv p7Hi 5040 : ℝ) := by
        have : u ^ 7 * SC ≤ (p7Hi : ℝ) := by rwa [le_div_iff₀ hSC] at h7h
        linarith
      have htu : (t : ℝ) = u * SC := by simp only [u]; field_simp [hSC.ne']
      linarith
    exact le_trans hdiv_all htay

lemma expNegHiSmall_sound {t : Int} (ht : 0 ≤ t) :
    Real.exp (-((t : ℝ) / (SC : ℝ))) ≤ ((expNegHiSmall t : Int) : ℝ) / (SC : ℝ) := by
  set u : ℝ := (t : ℝ) / (SC : ℝ)
  have hu : 0 ≤ u := div_nonneg (by exact_mod_cast ht) SC_pos.le
  unfold expNegHiSmall; dsimp only
  split_ifs with hgt
  · rw [div_self SC_pos.ne', Real.exp_le_one_iff]; linarith
  · have hSC : (0 : ℝ) < (SC : ℝ) := SC_pos
    have stepLo : ∀ a : Int, ∀ x : ℝ, ((a : ℝ) / SC) ≤ x →
        ((fdiv (a * t) SC : Int) : ℝ) / SC ≤ x * u := by
      intro a x hax
      have h1 := fdiv_le_div (a := a * t) SC_pos_int
      have h2 : ((fdiv (a * t) SC : Int) : ℝ) / SC ≤ ((a : ℝ) / SC) * u := by
        simp only [u]; push_cast at h1; rw [div_le_iff₀ hSC]
        have : ((a : ℝ) / SC) * ((t : ℝ) / SC) * SC = (a : ℝ) * (t : ℝ) / SC := by field_simp [hSC.ne']
        linarith
      exact le_trans h2 (mul_le_mul_of_nonneg_right hax hu)
    have stepHi : ∀ a : Int, ∀ x : ℝ, x ≤ ((a : ℝ) / SC) →
        x * u ≤ ((cdiv (a * t) SC : Int) : ℝ) / SC := by
      intro a x hxa
      have h1 := div_le_cdiv (a := a * t) SC_pos_int
      have h2 : ((a : ℝ) / SC) * u ≤ ((cdiv (a * t) SC : Int) : ℝ) / SC := by
        simp only [u]; push_cast at h1; rw [le_div_iff₀ hSC]
        have : ((a : ℝ) / SC) * ((t : ℝ) / SC) * SC = (a : ℝ) * (t : ℝ) / SC := by field_simp [hSC.ne']
        linarith
      exact le_trans (mul_le_mul_of_nonneg_right hxa hu) h2
    set p2Lo := fdiv (t * t) SC; set p2Hi := cdiv (t * t) SC
    set p3Lo := fdiv (p2Lo * t) SC; set p3Hi := cdiv (p2Hi * t) SC
    set p4Lo := fdiv (p3Lo * t) SC; set p4Hi := cdiv (p3Hi * t) SC
    set p5Lo := fdiv (p4Lo * t) SC; set p5Hi := cdiv (p4Hi * t) SC
    set p6Lo := fdiv (p5Lo * t) SC; set p6Hi := cdiv (p5Hi * t) SC
    set p7Lo := fdiv (p6Lo * t) SC; set p7Hi := cdiv (p6Hi * t) SC
    set p8Hi := cdiv (p7Hi * t) SC
    have h2l : (p2Lo : ℝ) / SC ≤ u ^ 2 := by simpa [sq] using stepLo t u le_rfl
    have h2h : u ^ 2 ≤ (p2Hi : ℝ) / SC := by simpa [sq] using stepHi t u le_rfl
    have h3l : (p3Lo : ℝ) / SC ≤ u ^ 3 := by simpa [pow_succ] using stepLo p2Lo (u ^ 2) h2l
    have h3h : u ^ 3 ≤ (p3Hi : ℝ) / SC := by simpa [pow_succ] using stepHi p2Hi (u ^ 2) h2h
    have h4l : (p4Lo : ℝ) / SC ≤ u ^ 4 := by simpa [pow_succ] using stepLo p3Lo (u ^ 3) h3l
    have h4h : u ^ 4 ≤ (p4Hi : ℝ) / SC := by simpa [pow_succ] using stepHi p3Hi (u ^ 3) h3h
    have h5l : (p5Lo : ℝ) / SC ≤ u ^ 5 := by simpa [pow_succ] using stepLo p4Lo (u ^ 4) h4l
    have h5h : u ^ 5 ≤ (p5Hi : ℝ) / SC := by simpa [pow_succ] using stepHi p4Hi (u ^ 4) h4h
    have h6l : (p6Lo : ℝ) / SC ≤ u ^ 6 := by simpa [pow_succ] using stepLo p5Lo (u ^ 5) h5l
    have h6h : u ^ 6 ≤ (p6Hi : ℝ) / SC := by simpa [pow_succ] using stepHi p5Hi (u ^ 5) h5h
    have h7l : (p7Lo : ℝ) / SC ≤ u ^ 7 := by simpa [pow_succ] using stepLo p6Lo (u ^ 6) h6l
    have h7h : u ^ 7 ≤ (p7Hi : ℝ) / SC := by simpa [pow_succ] using stepHi p6Hi (u ^ 6) h6h
    have h8h : u ^ 8 ≤ (p8Hi : ℝ) / SC := by simpa [pow_succ] using stepHi p7Hi (u ^ 7) h7h
    have d2 := div_le_cdiv (a := p2Hi) (b := 2) (by decide)
    have d3 := fdiv_le_div (a := p3Lo) (b := 6) (by decide)
    have d4 := div_le_cdiv (a := p4Hi) (b := 24) (by decide)
    have d5 := fdiv_le_div (a := p5Lo) (b := 120) (by decide)
    have d6 := div_le_cdiv (a := p6Hi) (b := 720) (by decide)
    have d7 := fdiv_le_div (a := p7Lo) (b := 5040) (by decide)
    have d8 := div_le_cdiv (a := p8Hi) (b := 40320) (by decide)
    have htay := expNeg_le_poly8 hu
    have hdiv_all :
        1 - u + u ^ 2 / 2 - u ^ 3 / 6 + u ^ 4 / 24 - u ^ 5 / 120 + u ^ 6 / 720 -
          u ^ 7 / 5040 + u ^ 8 / 40320 ≤
        ((SC - t + cdiv p2Hi 2 - fdiv p3Lo 6 + cdiv p4Hi 24 - fdiv p5Lo 120 +
            cdiv p6Hi 720 - fdiv p7Lo 5040 + cdiv p8Hi 40320 : Int) : ℝ) / SC := by
      push_cast at d2 d3 d4 d5 d6 d7 d8 ⊢
      rw [le_div_iff₀ hSC]
      have hmul2 : u ^ 2 / 2 * SC ≤ (cdiv p2Hi 2 : ℝ) := by
        have : u ^ 2 * SC ≤ (p2Hi : ℝ) := by rwa [le_div_iff₀ hSC] at h2h
        linarith
      have hmul3 : (fdiv p3Lo 6 : ℝ) ≤ u ^ 3 / 6 * SC := by
        have : (p3Lo : ℝ) ≤ u ^ 3 * SC := by rwa [div_le_iff₀ hSC] at h3l
        linarith
      have hmul4 : u ^ 4 / 24 * SC ≤ (cdiv p4Hi 24 : ℝ) := by
        have : u ^ 4 * SC ≤ (p4Hi : ℝ) := by rwa [le_div_iff₀ hSC] at h4h
        linarith
      have hmul5 : (fdiv p5Lo 120 : ℝ) ≤ u ^ 5 / 120 * SC := by
        have : (p5Lo : ℝ) ≤ u ^ 5 * SC := by rwa [div_le_iff₀ hSC] at h5l
        linarith
      have hmul6 : u ^ 6 / 720 * SC ≤ (cdiv p6Hi 720 : ℝ) := by
        have : u ^ 6 * SC ≤ (p6Hi : ℝ) := by rwa [le_div_iff₀ hSC] at h6h
        linarith
      have hmul7 : (fdiv p7Lo 5040 : ℝ) ≤ u ^ 7 / 5040 * SC := by
        have : (p7Lo : ℝ) ≤ u ^ 7 * SC := by rwa [div_le_iff₀ hSC] at h7l
        linarith
      have hmul8 : u ^ 8 / 40320 * SC ≤ (cdiv p8Hi 40320 : ℝ) := by
        have : u ^ 8 * SC ≤ (p8Hi : ℝ) := by rwa [le_div_iff₀ hSC] at h8h
        linarith
      have htu : (t : ℝ) = u * SC := by simp only [u]; field_simp [hSC.ne']
      linarith
    exact le_trans htay hdiv_all

lemma expNegHi_le_SC' {x : Int} (hx : 0 ≤ x) : expNegHi x ≤ SC := by
  unfold expNegHi sqHi10; dsimp only
  have ht0 : 0 ≤ fdiv x 1024 := Int.ediv_nonneg hx (by decide)
  have hbase_le : expNegHiSmall (fdiv x 1024) ≤ SC := expNegHiSmall_le_SC _
  have hbase_nn : 0 ≤ expNegHiSmall (fdiv x 1024) := by
    have hs := expNegHiSmall_sound ht0
    have hpos : (0 : ℝ) ≤ (expNegHiSmall (fdiv x 1024) : ℝ) / SC := le_trans (Real.exp_pos _).le hs
    have hpos2 : (0 : ℝ) ≤ (expNegHiSmall (fdiv x 1024) : ℝ) := by
      nlinarith [SC_pos, div_mul_cancel₀ (expNegHiSmall (fdiv x 1024) : ℝ) SC_pos.ne']
    exact_mod_cast hpos2
  have h0 := cdiv_sq_le_SC hbase_nn hbase_le
  have h1 := cdiv_sq_le_SC h0.1 h0.2
  have h2 := cdiv_sq_le_SC h1.1 h1.2
  have h3 := cdiv_sq_le_SC h2.1 h2.2
  have h4 := cdiv_sq_le_SC h3.1 h3.2
  have h5 := cdiv_sq_le_SC h4.1 h4.2
  have h6 := cdiv_sq_le_SC h5.1 h5.2
  have h7 := cdiv_sq_le_SC h6.1 h6.2
  have h8 := cdiv_sq_le_SC h7.1 h7.2
  exact (cdiv_sq_le_SC h8.1 h8.2).2

lemma sqLo_step {a : Int} {y : ℝ} (ha : 0 ≤ a) (hle : (a : ℝ) / SC ≤ y) :
    0 ≤ fdiv (a * a) SC ∧ ((fdiv (a * a) SC : Int) : ℝ) / SC ≤ y ^ 2 := by
  refine ⟨fdiv_mul_nonneg ha ha, ?_⟩
  have h1 := fdiv_le_div (a := a * a) SC_pos_int
  have haR : 0 ≤ (a : ℝ) / SC := div_nonneg (by exact_mod_cast ha) SC_pos.le
  have h2 : ((fdiv (a * a) SC : Int) : ℝ) / SC ≤ ((a : ℝ) / SC) ^ 2 := by
    push_cast at h1; rw [div_le_iff₀ SC_pos]
    have : ((a : ℝ) / SC) ^ 2 * SC = (a : ℝ) * (a : ℝ) / SC := by field_simp [SC_pos.ne']
    linarith
  exact le_trans h2 (pow_le_pow_left₀ haR hle 2)

lemma sqHi_step {a : Int} {y : ℝ} (hy : 0 ≤ y) (hle : y ≤ (a : ℝ) / SC) :
    y ^ 2 ≤ ((cdiv (a * a) SC : Int) : ℝ) / SC := by
  have h1 := div_le_cdiv (a := a * a) SC_pos_int
  have h2 : ((a : ℝ) / SC) ^ 2 ≤ ((cdiv (a * a) SC : Int) : ℝ) / SC := by
    push_cast at h1; rw [le_div_iff₀ SC_pos]
    have : ((a : ℝ) / SC) ^ 2 * SC = (a : ℝ) * (a : ℝ) / SC := by field_simp [SC_pos.ne']
    linarith
  exact le_trans (pow_le_pow_left₀ hy hle 2) h2

lemma expNegLo_sound {x : Int} (hx : 0 ≤ x) :
    ((expNegLo x : Int) : ℝ) / (SC : ℝ) ≤ Real.exp (-((x : ℝ) / (SC : ℝ))) := by
  unfold expNegLo sqLo10; dsimp only
  set t := cdiv x 1024
  have ht0 : 0 ≤ t := by
    have h1 : (0 : ℝ) ≤ (x : ℝ) / (1024 : ℝ) := div_nonneg (by exact_mod_cast hx) (by norm_num)
    have h2 := div_le_cdiv (a := x) (b := 1024) (by decide)
    have h3 : (0 : ℝ) ≤ (t : ℝ) := le_trans h1 (by exact_mod_cast h2)
    exact_mod_cast h3
  have ht_ge : (x : ℝ) / (1024 * SC) ≤ (t : ℝ) / SC := by
    have h1 := div_le_cdiv (a := x) (b := 1024) (by decide)
    push_cast at h1
    have hpos : (0 : ℝ) < 1024 * (SC : ℝ) := mul_pos (by norm_num) SC_pos
    rw [div_le_div_iff₀ hpos SC_pos]
    have h2 : (x : ℝ) ≤ (t : ℝ) * 1024 := by linarith [(div_le_iff₀ (by norm_num : (0 : ℝ) < 1024)).mp h1]
    nlinarith [SC_pos]
  have hbase : (expNegLoSmall t : ℝ) / SC ≤ Real.exp (-((x : ℝ) / (1024 * SC))) :=
    le_trans (expNegLoSmall_sound ht0) (Real.exp_le_exp.mpr (by linarith))
  set y : ℝ := Real.exp (-((x : ℝ) / (1024 * SC)))
  have h0 := sqLo_step (expNegLoSmall_nonneg t) hbase
  have h1 := sqLo_step h0.1 h0.2
  have h2 := sqLo_step h1.1 h1.2
  have h3 := sqLo_step h2.1 h2.2
  have h4 := sqLo_step h3.1 h3.2
  have h5 := sqLo_step h4.1 h4.2
  have h6 := sqLo_step h5.1 h5.2
  have h7 := sqLo_step h6.1 h6.2
  have h8 := sqLo_step h7.1 h7.2
  have h9 := sqLo_step h8.1 h8.2
  have hpow : ((((((((((y ^ 2) ^ 2) ^ 2) ^ 2) ^ 2) ^ 2) ^ 2) ^ 2) ^ 2) ^ 2) =
      Real.exp (-((x : ℝ) / (SC : ℝ))) := by
    have : ((((((((((y ^ 2) ^ 2) ^ 2) ^ 2) ^ 2) ^ 2) ^ 2) ^ 2) ^ 2) ^ 2) = y ^ (1024 : ℕ) := by ring
    rw [this]; simp only [y, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [← hpow]; exact h9.2

lemma expNegHi_sound {x : Int} (hx : 0 ≤ x) :
    Real.exp (-((x : ℝ) / (SC : ℝ))) ≤ ((expNegHi x : Int) : ℝ) / (SC : ℝ) := by
  unfold expNegHi sqHi10; dsimp only
  set t := fdiv x 1024
  have ht0 : 0 ≤ t := Int.ediv_nonneg hx (by decide)
  have ht_le : (t : ℝ) / SC ≤ (x : ℝ) / (1024 * SC) := by
    have h1 := fdiv_le_div (a := x) (b := 1024) (by decide)
    push_cast at h1
    have hpos : (0 : ℝ) < 1024 * (SC : ℝ) := mul_pos (by norm_num) SC_pos
    rw [div_le_div_iff₀ SC_pos hpos]
    have h2 : (t : ℝ) * 1024 ≤ (x : ℝ) := (le_div_iff₀ (by norm_num : (0 : ℝ) < 1024)).mp h1
    nlinarith [SC_pos]
  have hbase : Real.exp (-((x : ℝ) / (1024 * SC))) ≤ (expNegHiSmall t : ℝ) / SC :=
    le_trans (Real.exp_le_exp.mpr (by linarith)) (expNegHiSmall_sound ht0)
  set y : ℝ := Real.exp (-((x : ℝ) / (1024 * SC)))
  have hy : 0 ≤ y := (Real.exp_pos _).le
  have h0 := sqHi_step hy hbase
  have h1 := sqHi_step (by positivity) h0
  have h2 := sqHi_step (by positivity) h1
  have h3 := sqHi_step (by positivity) h2
  have h4 := sqHi_step (by positivity) h3
  have h5 := sqHi_step (by positivity) h4
  have h6 := sqHi_step (by positivity) h5
  have h7 := sqHi_step (by positivity) h6
  have h8 := sqHi_step (by positivity) h7
  have h9 := sqHi_step (by positivity) h8
  have hpow : ((((((((((y ^ 2) ^ 2) ^ 2) ^ 2) ^ 2) ^ 2) ^ 2) ^ 2) ^ 2) ^ 2) =
      Real.exp (-((x : ℝ) / (SC : ℝ))) := by
    have : ((((((((((y ^ 2) ^ 2) ^ 2) ^ 2) ^ 2) ^ 2) ^ 2) ^ 2) ^ 2) ^ 2) = y ^ (1024 : ℕ) := by ring
    rw [this]; simp only [y, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [← hpow]; exact h9

def checkNegLog (zLo zHi lLo lHi : Int) : Bool :=
  decide (0 ≤ lLo) && decide (lLo ≤ lHi) && decide (0 < zLo) && decide (zHi ≤ SC) &&
  decide (zHi ≤ expNegLo lLo) && decide (expNegHi lHi ≤ zLo)

lemma checkNegLog_sound {zLo zHi lLo lHi : Int} {z : ℝ}
    (hc : checkNegLog zLo zHi lLo lHi = true)
    (hzLo : (zLo : ℝ) / SC ≤ z) (hzHi : z ≤ (zHi : ℝ) / SC) :
    (lLo : ℝ) / SC ≤ -Real.log z ∧ -Real.log z ≤ (lHi : ℝ) / SC := by
  simp only [checkNegLog, Bool.and_eq_true, decide_eq_true_eq] at hc
  rcases hc with ⟨⟨⟨⟨⟨hl0, hll⟩, hz0⟩, _⟩, h1⟩, h2⟩
  have hzpos : 0 < z := lt_of_lt_of_le (div_pos (Int.cast_pos.mpr hz0) SC_pos) hzLo
  have hlHi0 : 0 ≤ lHi := le_trans hl0 hll
  constructor
  · have hstep : z ≤ Real.exp (-((lLo : ℝ) / SC)) :=
      le_trans hzHi (le_trans (div_le_div_of_nonneg_right (Int.cast_le.mpr h1) SC_pos.le)
        (expNegLo_sound hl0))
    have hlog := Real.log_le_log hzpos hstep
    rw [Real.log_exp] at hlog; linarith
  · have hstep : Real.exp (-((lHi : ℝ) / SC)) ≤ z :=
      le_trans (expNegHi_sound hlHi0)
        (le_trans (div_le_div_of_nonneg_right (Int.cast_le.mpr h2) SC_pos.le) hzLo)
    have hlog := Real.log_le_log (Real.exp_pos _) hstep
    rw [Real.log_exp] at hlog; linarith

def evalF (u lLo lHi : Int) : Option (Int × Int × Int × Int) :=
  if u ≥ 8 * SC then
    some (u + SC - 500000000, u + SC, SC, SC + 1000000000)
  else
    let xLo := expNegLo u
    let xHi := expNegHi u
    if decide (0 < xLo) && decide (xHi < SC) && checkNegLog (SC - xHi) (SC - xLo) lLo lHi then
      some (u + fdiv ((SC - xHi) * lLo) xHi, u + cdiv ((SC - xLo) * lHi) xLo,
            fdiv (lLo * SC) xHi, cdiv (lHi * SC) xLo)
    else none

lemma evalF_sound {u lLo lHi fLo fHi fpLo fpHi : Int} (hu : 0 < u)
    (he : evalF u lLo lHi = some (fLo, fHi, fpLo, fpHi)) :
    (fLo : ℝ) / SC ≤ F ((u : ℝ) / SC) ∧ F ((u : ℝ) / SC) ≤ (fHi : ℝ) / SC ∧
    (fpLo : ℝ) / SC ≤ Fp ((u : ℝ) / SC) ∧ Fp ((u : ℝ) / SC) ≤ (fpHi : ℝ) / SC := by
  set r : ℝ := (u : ℝ) / SC
  have hr : 0 < r := div_pos (Int.cast_pos.mpr hu) SC_pos
  unfold evalF at he
  split_ifs at he with h8
  · simp only [Option.some.injEq, Prod.mk.injEq] at he
    rcases he with ⟨rfl, rfl, rfl, rfl⟩
    have hr8 : (8 : ℝ) ≤ r := by
      have hR : (8 : ℝ) * SC ≤ (u : ℝ) := by exact_mod_cast h8
      rw [le_div_iff₀ SC_pos]; linarith
    have hexp : Real.exp (-r) ≤ 1 / 2000 :=
      le_trans (Real.exp_le_exp.mpr (by linarith)) exp_neg_eight_le
    have hz1 : Real.exp (-r) < 1 := by linarith
    have hprod : Real.exp r * Real.exp (-r) = 1 := by rw [← Real.exp_add]; simp
    refine ⟨?_, ?_, ?_, ?_⟩
    · have h1 := F_ge_add_one_sub_exp hr
      have hcast : ((u + SC - 500000000 : Int) : ℝ) / SC = r + 1 - 1 / 2000 := by
        simp only [r, SC]; push_cast; ring
      rw [hcast]; linarith
    · have hcast : ((u + SC : Int) : ℝ) / SC = r + 1 := by
        simp only [r, SC]; push_cast; ring
      rw [hcast]; exact F_le_add_one hr
    · have hlog := neg_log_one_sub_ge hz1
      have hcast : (SC : ℝ) / SC = 1 := div_self SC_pos.ne'
      rw [hcast]; unfold Fp
      have : -Real.exp r * Real.log (1 - Real.exp (-r)) = Real.exp r * (-Real.log (1 - Real.exp (-r))) := by ring
      rw [this]; nlinarith [mul_le_mul_of_nonneg_left hlog (Real.exp_pos r).le, hprod]
    · have hlog := neg_log_one_sub_le hz1
      have hcast : ((SC + 1000000000 : Int) : ℝ) / SC = 1 + 1 / 1000 := by
        simp only [SC]; push_cast; ring
      rw [hcast]; unfold Fp
      have h1 : -Real.exp r * Real.log (1 - Real.exp (-r)) = Real.exp r * (-Real.log (1 - Real.exp (-r))) := by ring
      rw [h1]
      have h2 : Real.exp r * (Real.exp (-r) / (1 - Real.exp (-r))) = 1 / (1 - Real.exp (-r)) := by
        field_simp [(show 1 - Real.exp (-r) ≠ 0 by linarith)]; linarith
      have h3 : 1 / (1 - Real.exp (-r)) ≤ 1 + 1 / 1000 := by
        rw [div_le_iff₀ (by linarith)]; linarith
      nlinarith [mul_le_mul_of_nonneg_left hlog (Real.exp_pos r).le]
  · dsimp only at he
    split_ifs at he with hc
    · simp only [Option.some.injEq, Prod.mk.injEq] at he
      rcases he with ⟨rfl, rfl, rfl, rfl⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      rcases hc with ⟨⟨hxLo0, hxHi1⟩, hnl⟩
      have hxLo_le : (expNegLo u : ℝ) / SC ≤ Real.exp (-r) := expNegLo_sound hu.le
      have hxHi_ge : Real.exp (-r) ≤ (expNegHi u : ℝ) / SC := expNegHi_sound hu.le
      have hxLo_pos : (0 : ℝ) < (expNegLo u : ℝ) / SC := div_pos (Int.cast_pos.mpr hxLo0) SC_pos
      have hxHi_pos_int : (0 : Int) < expNegHi u := by
        have : (expNegLo u : ℝ) ≤ (expNegHi u : ℝ) := by
          have := le_trans hxLo_le hxHi_ge
          rwa [div_le_div_iff_of_pos_right SC_pos] at this
        have : expNegLo u ≤ expNegHi u := Int.cast_le.mp this
        omega
      have hxHi_pos : (0 : ℝ) < (expNegHi u : ℝ) / SC := div_pos (Int.cast_pos.mpr hxHi_pos_int) SC_pos
      have hzLo : ((SC - expNegHi u : Int) : ℝ) / SC ≤ 1 - Real.exp (-r) := by
        push_cast; rw [sub_div, div_self SC_pos.ne']; linarith
      have hzHi : 1 - Real.exp (-r) ≤ ((SC - expNegLo u : Int) : ℝ) / SC := by
        push_cast; rw [sub_div, div_self SC_pos.ne']; linarith
      have hL := checkNegLog_sound hnl hzLo hzHi
      have hlLo0 : 0 ≤ lLo := by
        simp only [checkNegLog, Bool.and_eq_true, decide_eq_true_eq] at hnl; exact hnl.1.1.1.1.1
      have hlHi0 : 0 ≤ lHi := by
        simp only [checkNegLog, Bool.and_eq_true, decide_eq_true_eq] at hnl; linarith [hnl.1.1.1.1.1, hnl.1.1.1.1.2]
      have hprod : Real.exp r * Real.exp (-r) = 1 := by rw [← Real.exp_add]; simp
      have hFeq : F r = r + (1 - Real.exp (-r)) / Real.exp (-r) * (-Real.log (1 - Real.exp (-r))) := by
        unfold F; field_simp [(Real.exp_pos (-r)).ne']
        have hdiff : Real.exp (-r) * (Real.exp r - 1) = 1 - Real.exp (-r) := by linarith
        have : Real.exp (-r) * (r - (Real.exp r - 1) * Real.log (1 - Real.exp (-r))) =
            r * Real.exp (-r) - Real.exp (-r) * (Real.exp r - 1) * Real.log (1 - Real.exp (-r)) := by ring
        rw [this, hdiff]; ring
      have hFpeq : Fp r = (-Real.log (1 - Real.exp (-r))) / Real.exp (-r) := by
        unfold Fp; field_simp [(Real.exp_pos (-r)).ne']
        rw [hprod]; ring
      have hSC : (0 : ℝ) < (SC : ℝ) := SC_pos
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hFeq]; push_cast; rw [add_div]
        have hd := fdiv_le_div (a := (SC - expNegHi u) * lLo) hxHi_pos_int
        push_cast at hd
        have h1 : ((fdiv ((SC - expNegHi u) * lLo) (expNegHi u) : Int) : ℝ) / SC ≤
            (((SC : ℝ) - expNegHi u) / expNegHi u) * ((lLo : ℝ) / SC) := by
          rw [div_le_iff₀ hSC]
          have : ((SC : ℝ) - expNegHi u) / expNegHi u * ((lLo : ℝ) / SC) * SC =
              ((SC : ℝ) - expNegHi u) * lLo / expNegHi u := by field_simp [hSC.ne']
          linarith
        have h2 : ((SC : ℝ) - expNegHi u) / expNegHi u ≤ (1 - Real.exp (-r)) / Real.exp (-r) := by
          have : ((SC : ℝ) - expNegHi u) / expNegHi u = (1 - (expNegHi u : ℝ) / SC) / ((expNegHi u : ℝ) / SC) := by
            field_simp [hSC.ne']
          rw [this, div_le_div_iff₀ hxHi_pos (Real.exp_pos (-r))]; nlinarith
        have hlLoR : (0 : ℝ) ≤ (lLo : ℝ) / SC := div_nonneg (by exact_mod_cast hlLo0) hSC.le
        have h1me_nn : 0 ≤ 1 - Real.exp (-r) := by
          have : (expNegHi u : ℝ) / SC < 1 := by rw [div_lt_one hSC]; exact_mod_cast hxHi1
          linarith
        have h4 := mul_le_mul h2 hL.1 hlLoR (div_nonneg h1me_nn (Real.exp_pos (-r)).le)
        linarith
      · rw [hFeq]; push_cast; rw [add_div]
        have hd := div_le_cdiv (a := (SC - expNegLo u) * lHi) hxLo0
        push_cast at hd
        have h1 : (((SC : ℝ) - expNegLo u) / expNegLo u) * ((lHi : ℝ) / SC) ≤
            ((cdiv ((SC - expNegLo u) * lHi) (expNegLo u) : Int) : ℝ) / SC := by
          rw [le_div_iff₀ hSC]
          have : ((SC : ℝ) - expNegLo u) / expNegLo u * ((lHi : ℝ) / SC) * SC =
              ((SC : ℝ) - expNegLo u) * lHi / expNegLo u := by field_simp [hSC.ne']
          linarith
        have h2 : (1 - Real.exp (-r)) / Real.exp (-r) ≤ ((SC : ℝ) - expNegLo u) / expNegLo u := by
          have : ((SC : ℝ) - expNegLo u) / expNegLo u = (1 - (expNegLo u : ℝ) / SC) / ((expNegLo u : ℝ) / SC) := by
            field_simp [hSC.ne']
          rw [this, div_le_div_iff₀ (Real.exp_pos (-r)) hxLo_pos]; nlinarith
        have h3 : 0 ≤ -Real.log (1 - Real.exp (-r)) :=
          le_trans (div_nonneg (by exact_mod_cast hlLo0) hSC.le) hL.1
        have hxLo_le_SC : (expNegLo u : ℝ) ≤ SC := by
          have : (expNegLo u : ℝ) / SC ≤ 1 := le_trans hxLo_le (by rw [Real.exp_le_one_iff]; linarith)
          rwa [div_le_one hSC] at this
        have h4 := mul_le_mul h2 hL.2 h3 (div_nonneg (by linarith) (Int.cast_pos.mpr hxLo0).le)
        linarith
      · rw [hFpeq]
        have hd := fdiv_le_div (a := lLo * SC) hxHi_pos_int
        push_cast at hd
        have h1 : ((fdiv (lLo * SC) (expNegHi u) : Int) : ℝ) / SC ≤ ((lLo : ℝ) / SC) / ((expNegHi u : ℝ) / SC) := by
          have : ((lLo : ℝ) / SC) / ((expNegHi u : ℝ) / SC) = (lLo : ℝ) / expNegHi u := by field_simp [hSC.ne']
          rw [this, div_le_iff₀ hSC]
          have : (lLo : ℝ) / expNegHi u * SC = (lLo : ℝ) * SC / expNegHi u := by ring
          linarith
        have h2 : ((lLo : ℝ) / SC) / ((expNegHi u : ℝ) / SC) ≤ (-Real.log (1 - Real.exp (-r))) / Real.exp (-r) := by
          rw [div_le_div_iff₀ hxHi_pos (Real.exp_pos (-r))]
          exact mul_le_mul hL.1 hxHi_ge (Real.exp_pos (-r)).le
            (le_trans (div_nonneg (by exact_mod_cast hlLo0) hSC.le) hL.1)
        exact le_trans h1 h2
      · rw [hFpeq]
        have hd := div_le_cdiv (a := lHi * SC) hxLo0
        push_cast at hd
        have h1 : ((lHi : ℝ) / SC) / ((expNegLo u : ℝ) / SC) ≤ ((cdiv (lHi * SC) (expNegLo u) : Int) : ℝ) / SC := by
          have : ((lHi : ℝ) / SC) / ((expNegLo u : ℝ) / SC) = (lHi : ℝ) / expNegLo u := by field_simp [hSC.ne']
          rw [this, le_div_iff₀ hSC]
          have : (lHi : ℝ) / expNegLo u * SC = (lHi : ℝ) * SC / expNegLo u := by ring
          linarith
        have h2 : (-Real.log (1 - Real.exp (-r))) / Real.exp (-r) ≤ ((lHi : ℝ) / SC) / ((expNegLo u : ℝ) / SC) := by
          rw [div_le_div_iff₀ (Real.exp_pos (-r)) hxLo_pos]
          exact mul_le_mul hL.2 hxLo_le hxLo_pos.le (div_nonneg (by exact_mod_cast hlHi0) hSC.le)
        exact le_trans h2 h1

lemma sqrt_mul_linear_ge {a1 a2 f1 f2 t : ℝ}
    (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2) (hf1 : 0 ≤ f1) (hf2 : 0 ≤ f2)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) * Real.sqrt (a1 * f1) + t * Real.sqrt (a2 * f2) ≤
      Real.sqrt (((1 - t) * a1 + t * a2) * ((1 - t) * f1 + t * f2)) := by
  have h1mt : 0 ≤ 1 - t := by linarith
  have hprod_nn : 0 ≤ ((1 - t) * a1 + t * a2) * ((1 - t) * f1 + t * f2) :=
    mul_nonneg (by nlinarith) (by nlinarith)
  rw [Real.le_sqrt (by positivity) hprod_nn]
  have hsq1 : Real.sqrt (a1 * f1) ^ 2 = a1 * f1 := Real.sq_sqrt (mul_nonneg ha1 hf1)
  have hsq2 : Real.sqrt (a2 * f2) ^ 2 = a2 * f2 := Real.sq_sqrt (mul_nonneg ha2 hf2)
  have hcs : 2 * (Real.sqrt (a1 * f1) * Real.sqrt (a2 * f2)) ≤ a1 * f2 + a2 * f1 := by
    have h1 : 0 ≤ (Real.sqrt (a1 * f2) - Real.sqrt (a2 * f1)) ^ 2 := sq_nonneg _
    have h2 : Real.sqrt (a1 * f1) * Real.sqrt (a2 * f2) = Real.sqrt (a1 * f2) * Real.sqrt (a2 * f1) := by
      rw [← Real.sqrt_mul (mul_nonneg ha1 hf1), ← Real.sqrt_mul (mul_nonneg ha1 hf2)]
      congr 1; ring
    have h3 : Real.sqrt (a1 * f2) ^ 2 = a1 * f2 := Real.sq_sqrt (mul_nonneg ha1 hf2)
    have h4 : Real.sqrt (a2 * f1) ^ 2 = a2 * f1 := Real.sq_sqrt (mul_nonneg ha2 hf1)
    nlinarith
  have hmul : 2 * ((1 - t) * t) * (Real.sqrt (a1 * f1) * Real.sqrt (a2 * f2)) ≤
      ((1 - t) * t) * (a1 * f2 + a2 * f1) := by
    have := mul_le_mul_of_nonneg_left hcs (mul_nonneg h1mt ht0)
    linarith
  have hexp1 : ((1 - t) * Real.sqrt (a1 * f1) + t * Real.sqrt (a2 * f2)) ^ 2 =
      (1 - t) ^ 2 * Real.sqrt (a1 * f1) ^ 2 + t ^ 2 * Real.sqrt (a2 * f2) ^ 2 +
      2 * ((1 - t) * t) * (Real.sqrt (a1 * f1) * Real.sqrt (a2 * f2)) := by ring
  have hexp2 : ((1 - t) * a1 + t * a2) * ((1 - t) * f1 + t * f2) =
      (1 - t) ^ 2 * (a1 * f1) + t ^ 2 * (a2 * f2) + ((1 - t) * t) * (a1 * f2 + a2 * f1) := by ring
  rw [hexp1, hsq1, hsq2, hexp2]; linarith

-- Clean split helpers for checkLinG!
def getAHiPair (u2 um x2Lo xmLo : Int) : Int × Int :=
  let halfW := u2 - um
  if halfW < SC then
    let sh1 := SC - fdiv (xmLo * (SC + halfW)) SC
    let sh2 := SC - fdiv (xmLo * (SC - halfW)) SC
    if decide (0 ≤ sh1) && decide (sh2 ≤ SC) then
      (SC + cdiv (49 * sh1 * sh1) (100 * SC), SC + cdiv (49 * sh2 * sh2) (100 * SC))
    else
      let st := SC - x2Lo; let v := SC + cdiv (49 * st * st) (100 * SC); (v, v)
  else
    let st := SC - x2Lo; let v := SC + cdiv (49 * st * st) (100 * SC); (v, v)

lemma getAHiPair_sound {u1 u2 : Int} (hu1 : 0 < u1) (h12 : u1 < u2) (heven : (u1 + u2) % 2 = 0)
    (_hx20 : 0 < expNegLo u2) (hxm0 : 0 < expNegLo (fdiv (u1 + u2) 2)) :
    let um := fdiv (u1 + u2) 2
    let p := getAHiPair u2 um (expNegLo u2) (expNegLo um)
    SC ≤ p.1 ∧ SC ≤ p.2 ∧
    ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      Afn ((1 - t) * ((u1 : ℝ) / SC) + t * ((u2 : ℝ) / SC)) ≤
        (1 - t) * ((p.1 : ℝ) / SC) + t * ((p.2 : ℝ) / SC) := by
  have hSC : (0 : ℝ) < (SC : ℝ) := SC_pos
  have hu2 : 0 < u2 := lt_trans hu1 h12
  set um := fdiv (u1 + u2) 2
  have hum_eq : 2 * um = u1 + u2 := by
    change 2 * ((u1 + u2) / 2) = u1 + u2; omega
  have hum_pos : 0 < um := by omega
  have hconst_ok : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      Afn ((1 - t) * ((u1 : ℝ) / SC) + t * ((u2 : ℝ) / SC)) ≤
        ((SC + cdiv (49 * (SC - expNegLo u2) * (SC - expNegLo u2)) (100 * SC) : Int) : ℝ) / SC := by
    intro t ht0 ht1
    set u : ℝ := (1 - t) * ((u1 : ℝ) / SC) + t * ((u2 : ℝ) / SC)
    have hu_le : u ≤ (u2 : ℝ) / SC := by
      have : (u1 : ℝ) / SC < (u2 : ℝ) / SC := div_lt_div_of_pos_right (Int.cast_lt.mpr h12) hSC
      nlinarith
    have hx2_le : (expNegLo u2 : ℝ) / SC ≤ Real.exp (-u) :=
      le_trans (expNegLo_sound hu2.le) (Real.exp_le_exp.mpr (by linarith))
    have hs_le : 1 - Real.exp (-u) ≤ ((SC - expNegLo u2 : Int) : ℝ) / SC := by
      push_cast; rw [sub_div, div_self hSC.ne']; linarith
    have hs_nn : 0 ≤ 1 - Real.exp (-u) := by
      have hu_pos : 0 < u := by
        have h1 : (0 : ℝ) < (u1 : ℝ) / SC := div_pos (Int.cast_pos.mpr hu1) hSC
        have hlt : (u1 : ℝ) / SC < (u2 : ℝ) / SC := div_lt_div_of_pos_right (Int.cast_lt.mpr h12) hSC
        have hge : (u1 : ℝ) / SC ≤ u := by simp only [u]; nlinarith
        linarith
      have : Real.exp (-u) < 1 := by rw [Real.exp_lt_one_iff]; linarith
      linarith
    have hsq : (1 - Real.exp (-u)) ^ 2 ≤ (((SC - expNegLo u2 : Int) : ℝ) / SC) ^ 2 :=
      pow_le_pow_left₀ hs_nn hs_le 2
    push_cast at hsq
    have hd := div_le_cdiv (a := 49 * (SC - expNegLo u2) * (SC - expNegLo u2)) (b := 100 * SC) (by decide)
    push_cast at hd ⊢
    unfold Afn
    rw [add_div, div_self hSC.ne']
    have h2 : (49 / 100 : ℝ) * (((SC : ℝ) - expNegLo u2) / SC) ^ 2 ≤
        (cdiv (49 * (SC - expNegLo u2) * (SC - expNegLo u2)) (100 * SC) : ℝ) / SC := by
      rw [le_div_iff₀ hSC]
      have : (49 / 100 : ℝ) * (((SC : ℝ) - expNegLo u2) / SC) ^ 2 * SC =
          49 * ((SC : ℝ) - expNegLo u2) * ((SC : ℝ) - expNegLo u2) / (100 * SC) := by field_simp [hSC.ne']
      linarith
    nlinarith
  have hcdiv_nn : ∀ a : Int, 0 ≤ cdiv (49 * a * a) (100 * SC) := by
    intro a
    have h1 : (0 : ℝ) ≤ (49 * a * a : ℝ) / (100 * SC : ℝ) := by
      have : (0 : ℝ) ≤ (49 * a * a : ℝ) := by
        have : (49 * a * a : ℝ) = 49 * (a : ℝ) ^ 2 := by ring
        rw [this]; positivity
      exact div_nonneg this (by positivity)
    have h2 := div_le_cdiv (a := 49 * a * a) (b := 100 * SC) (by decide)
    have h3 : (0 : ℝ) ≤ (cdiv (49 * a * a) (100 * SC) : ℝ) := le_trans (by exact_mod_cast h1) h2
    exact_mod_cast h3
  dsimp only
  unfold getAHiPair; dsimp only
  split_ifs with hhw hsh
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hsh
    set halfW := u2 - um
    set xmLo := expNegLo um
    set sh1 := SC - fdiv (xmLo * (SC + halfW)) SC
    set sh2 := SC - fdiv (xmLo * (SC - halfW)) SC
    refine ⟨by linarith [hcdiv_nn sh1], by linarith [hcdiv_nn sh2], fun t ht0 ht1 => ?_⟩
    set r1 : ℝ := (u1 : ℝ) / SC; set r2 : ℝ := (u2 : ℝ) / SC
    set rm : ℝ := (um : ℝ) / SC; set u : ℝ := (1 - t) * r1 + t * r2
    have hrm_eq : rm = (r1 + r2) / 2 := by
      have : (2 : ℝ) * um = (u1 : ℝ) + u2 := by exact_mod_cast hum_eq
      simp only [r1, r2, rm]; field_simp [hSC.ne']; linarith
    have hhw_eq : (halfW : ℝ) / SC = (r2 - r1) / 2 := by
      have : (2 : ℝ) * halfW = (u2 : ℝ) - u1 := by
        have : 2 * halfW = u2 - u1 := by omega
        exact_mod_cast this
      simp only [r1, r2]; field_simp [hSC.ne']; linarith
    have hexp_tan : Real.exp (-rm) * (1 - (u - rm)) ≤ Real.exp (-u) := by
      have h1 : 1 - (u - rm) ≤ Real.exp (-(u - rm)) := by linarith [Real.add_one_le_exp (-(u - rm))]
      have h2 := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (-rm)).le
      rw [← Real.exp_add] at h2
      have : -rm + -(u - rm) = -u := by ring
      rw [this] at h2; exact h2
    have h1mu_pos : 0 ≤ 1 - (u - rm) := by
      have hhw_lt : (halfW : ℝ) / SC < 1 := by rw [div_lt_one hSC]; exact_mod_cast hhw
      have hhw0 : (0 : ℝ) ≤ (halfW : ℝ) / SC :=
        div_nonneg (by exact_mod_cast (show 0 ≤ halfW by omega)) hSC.le
      have : u - rm = (2 * t - 1) * ((halfW : ℝ) / SC) := by rw [hrm_eq, hhw_eq]; simp only [u]; ring
      nlinarith
    have hxm_le : (xmLo : ℝ) / SC ≤ Real.exp (-rm) := expNegLo_sound hum_pos.le
    have hexp_lin : ((xmLo : ℝ) / SC) * (1 - (u - rm)) ≤ Real.exp (-u) :=
      le_trans (mul_le_mul_of_nonneg_right hxm_le h1mu_pos) hexp_tan
    have hsh1_ge : 1 - ((xmLo : ℝ) / SC) * (1 + (halfW : ℝ) / SC) ≤ (sh1 : ℝ) / SC := by
      have hd := fdiv_le_div (a := xmLo * (SC + halfW)) SC_pos_int
      push_cast at hd
      simp only [sh1]; push_cast; rw [sub_div, div_self hSC.ne']
      have hrew : ((xmLo : ℝ) / SC) * (1 + (halfW : ℝ) / SC) =
          ((xmLo : ℝ) * ((SC : ℝ) + halfW) / SC) / SC := by field_simp [hSC.ne']
      rw [hrew]
      have := div_le_div_of_nonneg_right hd hSC.le
      linarith
    have hsh2_ge : 1 - ((xmLo : ℝ) / SC) * (1 - (halfW : ℝ) / SC) ≤ (sh2 : ℝ) / SC := by
      have hd := fdiv_le_div (a := xmLo * (SC - halfW)) SC_pos_int
      push_cast at hd
      simp only [sh2]; push_cast; rw [sub_div, div_self hSC.ne']
      have hrew : ((xmLo : ℝ) / SC) * (1 - (halfW : ℝ) / SC) =
          ((xmLo : ℝ) * ((SC : ℝ) - halfW) / SC) / SC := by field_simp [hSC.ne']
      rw [hrew]
      have := div_le_div_of_nonneg_right hd hSC.le
      linarith
    have hs_lin : 1 - Real.exp (-u) ≤ (1 - t) * ((sh1 : ℝ) / SC) + t * ((sh2 : ℝ) / SC) := by
      have hlin_eq : 1 - ((xmLo : ℝ) / SC) * (1 - (u - rm)) =
          (1 - t) * (1 - ((xmLo : ℝ) / SC) * (1 + (halfW : ℝ) / SC)) +
          t * (1 - ((xmLo : ℝ) / SC) * (1 - (halfW : ℝ) / SC)) := by
        rw [hrm_eq, hhw_eq]; simp only [u]; ring
      nlinarith
    have hs_nn : 0 ≤ 1 - Real.exp (-u) := by
      have hu_pos : 0 < u := by
        have h1 : (0 : ℝ) < r1 := div_pos (Int.cast_pos.mpr hu1) hSC
        have hlt : r1 < r2 := div_lt_div_of_pos_right (Int.cast_lt.mpr h12) hSC
        have hge : r1 ≤ u := by simp only [u]; nlinarith
        linarith
      have : Real.exp (-u) < 1 := by rw [Real.exp_lt_one_iff]; linarith
      linarith
    have hsq_conv : ((1 - t) * ((sh1 : ℝ) / SC) + t * ((sh2 : ℝ) / SC)) ^ 2 ≤
        (1 - t) * ((sh1 : ℝ) / SC) ^ 2 + t * ((sh2 : ℝ) / SC) ^ 2 := by
      have hdiff : (1 - t) * ((sh1 : ℝ) / SC) ^ 2 + t * ((sh2 : ℝ) / SC) ^ 2 -
          ((1 - t) * ((sh1 : ℝ) / SC) + t * ((sh2 : ℝ) / SC)) ^ 2 =
          (1 - t) * t * (((sh1 : ℝ) / SC) - ((sh2 : ℝ) / SC)) ^ 2 := by ring
      have hnn : 0 ≤ (1 - t) * t * (((sh1 : ℝ) / SC) - ((sh2 : ℝ) / SC)) ^ 2 :=
        mul_nonneg (mul_nonneg (by linarith) ht0) (sq_nonneg _)
      linarith
    have hsq : (1 - Real.exp (-u)) ^ 2 ≤
        (1 - t) * ((sh1 : ℝ) / SC) ^ 2 + t * ((sh2 : ℝ) / SC) ^ 2 :=
      le_trans (pow_le_pow_left₀ hs_nn hs_lin 2) hsq_conv
    have hA1 : 1 + (49 / 100 : ℝ) * ((sh1 : ℝ) / SC) ^ 2 ≤
        ((SC + cdiv (49 * sh1 * sh1) (100 * SC) : Int) : ℝ) / SC := by
      have hd := div_le_cdiv (a := 49 * sh1 * sh1) (b := 100 * SC) (by decide)
      push_cast at hd ⊢; rw [add_div, div_self hSC.ne']
      have : (49 / 100 : ℝ) * ((sh1 : ℝ) / SC) ^ 2 * SC = 49 * (sh1 : ℝ) * sh1 / (100 * SC) := by
        field_simp [hSC.ne']
      have : (49 / 100 : ℝ) * ((sh1 : ℝ) / SC) ^ 2 ≤ (cdiv (49 * sh1 * sh1) (100 * SC) : ℝ) / SC := by
        rw [le_div_iff₀ hSC]; linarith
      linarith
    have hA2 : 1 + (49 / 100 : ℝ) * ((sh2 : ℝ) / SC) ^ 2 ≤
        ((SC + cdiv (49 * sh2 * sh2) (100 * SC) : Int) : ℝ) / SC := by
      have hd := div_le_cdiv (a := 49 * sh2 * sh2) (b := 100 * SC) (by decide)
      push_cast at hd ⊢; rw [add_div, div_self hSC.ne']
      have : (49 / 100 : ℝ) * ((sh2 : ℝ) / SC) ^ 2 * SC = 49 * (sh2 : ℝ) * sh2 / (100 * SC) := by
        field_simp [hSC.ne']
      have : (49 / 100 : ℝ) * ((sh2 : ℝ) / SC) ^ 2 ≤ (cdiv (49 * sh2 * sh2) (100 * SC) : ℝ) / SC := by
        rw [le_div_iff₀ hSC]; linarith
      linarith
    unfold Afn
    nlinarith
  · refine ⟨by linarith [hcdiv_nn (SC - expNegLo u2)],
            by linarith [hcdiv_nn (SC - expNegLo u2)], fun t ht0 ht1 => ?_⟩
    have := hconst_ok t ht0 ht1; linarith
  · refine ⟨by linarith [hcdiv_nn (SC - expNegLo u2)],
            by linarith [hcdiv_nn (SC - expNegLo u2)], fun t ht0 ht1 => ?_⟩
    have := hconst_ok t ht0 ht1; linarith

def checkLinG (u1 u2 lamHi w1Lo w1Hi w2Lo w2Hi g1 g2 : Int) : Bool :=
  if decide (u1 ≥ u2) || decide ((u1 + u2) % 2 ≠ 0) then false
  else if u1 ≥ 8 * SC then
    let aLo : Int := 1480000000000
    decide (0 ≤ g1) && decide (0 ≤ g2) && decide (g1 * g1 ≤ aLo * (2 * u1)) && decide (g2 * g2 ≤ aLo * (2 * u2))
  else
    let um := fdiv (u1 + u2) 2
    let x1Lo := expNegLo u1; let x1Hi := expNegHi u1
    let x2Lo := expNegLo u2; let x2Hi := expNegHi u2
    let xmLo := expNegLo um
    if decide (x1Lo ≤ 0) || decide (x2Lo ≤ 0) || decide (xmLo ≤ 0) then false
    else
      let sl1 := SC - x1Hi; let sl2 := SC - x2Hi; let slm := fdiv (sl1 + sl2) 2
      let aLo1 := SC + fdiv (49 * slm * (2 * sl1 - slm)) (100 * SC)
      let aLo2 := SC + fdiv (49 * slm * (2 * sl2 - slm)) (100 * SC)
      let p := getAHiPair u2 um x2Lo xmLo
      let aHi1 := p.1; let aHi2 := p.2
      let aM := fdiv (aHi1 + aHi2) 2
      if decide (aLo1 < 0) || decide (aLo2 < 0) || decide (aM < SC) || decide (lamHi < 0) then false
      else if decide (expNegHi lamHi * aM > SC * SC) then false
      else
        let lA1 := lamHi + cdiv ((aHi1 - aM) * SC) aM
        let lA2 := lamHi + cdiv ((aHi2 - aM) * SC) aM
        let w1 := 2 * u1 - lA1; let w2 := 2 * u2 - lA2
        if decide (w1 ≤ 0) || decide (w2 ≤ 0) then false
        else match evalF w1 w1Lo w1Hi, evalF w2 w2Lo w2Hi with
          | some (f1Lo, _, _, _), some (f2Lo, _, _, _) =>
            decide (0 ≤ g1) && decide (0 ≤ g2) && decide (g1 * g1 ≤ aLo1 * f1Lo) && decide (g2 * g2 ≤ aLo2 * f2Lo)
          | _, _ => false

lemma checkLinG_sound {u1 u2 lamHi w1Lo w1Hi w2Lo w2Hi g1 g2 : Int}
    (hu1 : 0 < u1) (hc : checkLinG u1 u2 lamHi w1Lo w1Hi w2Lo w2Hi g1 g2 = true) :
    0 ≤ g1 ∧ 0 ≤ g2 ∧
    ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      (1 - t) * ((g1 : ℝ) / SC) + t * ((g2 : ℝ) / SC) ≤
        Gfn ((1 - t) * ((u1 : ℝ) / SC) + t * ((u2 : ℝ) / SC)) := by
  have hSC : (0 : ℝ) < (SC : ℝ) := SC_pos
  unfold checkLinG at hc
  split at hc
  · cases hc
  · rename_i hbad
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_le, not_ne_iff] at hbad
    split at hc
    · rename_i h8
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      rcases hc with ⟨⟨⟨hg1, hg2⟩, hsq1⟩, hsq2⟩
      refine ⟨hg1, hg2, fun t ht0 ht1 => ?_⟩
      set r1 : ℝ := (u1 : ℝ) / SC; set r2 : ℝ := (u2 : ℝ) / SC
      set u : ℝ := (1 - t) * r1 + t * r2
      have hr1 : (8 : ℝ) ≤ r1 := by
        have : (8 : ℝ) * SC ≤ (u1 : ℝ) := by exact_mod_cast h8
        rw [le_div_iff₀ hSC]; linarith
      have hr2 : (8 : ℝ) ≤ r2 := by
        have : r1 < r2 := div_lt_div_of_pos_right (Int.cast_lt.mpr hbad.1) hSC
        linarith
      have hu8 : (8 : ℝ) ≤ u := by
        simp only [u]; nlinarith
      have hA_lo : (148 / 100 : ℝ) ≤ Afn u := by
        unfold Afn
        have hexp : Real.exp (-u) ≤ 1 / 2000 :=
          le_trans (Real.exp_le_exp.mpr (by linarith)) exp_neg_eight_le
        nlinarith
      have hF_lo : 2 * u ≤ F (wfn u) := by
        have hA_hi : Afn u ≤ 149 / 100 := Afn_le u (by linarith)
        have hlog : Real.log (Afn u) ≤ 49 / 100 := by
          have := Real.log_le_sub_one_of_pos (show 0 < Afn u by linarith [Afn_ge_one u])
          linarith
        have hw8 : (8 : ℝ) ≤ wfn u := by unfold wfn; linarith
        have hexp : Real.exp (-wfn u) ≤ 1 / 2000 :=
          le_trans (Real.exp_le_exp.mpr (by linarith)) exp_neg_eight_le
        have h1 := F_ge_add_one_sub_exp (show 0 < wfn u by linarith)
        unfold wfn at h1 hexp ⊢; linarith
      have hG_ge : Real.sqrt (((1 - t) * (148 / 100 : ℝ) + t * (148 / 100 : ℝ)) *
          ((1 - t) * (2 * r1) + t * (2 * r2))) ≤ Gfn u := by
        unfold Gfn; apply Real.sqrt_le_sqrt
        have heq1 : (1 - t) * (148 / 100 : ℝ) + t * (148 / 100 : ℝ) = 148 / 100 := by ring
        have heq2 : (1 - t) * (2 * r1) + t * (2 * r2) = 2 * u := by simp only [u]; ring
        rw [heq1, heq2]; exact mul_le_mul hA_lo hF_lo (by linarith) (by linarith)
      have hcs := sqrt_mul_linear_ge (a1 := 148 / 100) (a2 := 148 / 100)
        (f1 := 2 * r1) (f2 := 2 * r2) (by norm_num) (by norm_num) (by linarith) (by linarith) ht0 ht1
      have hg1_le : (g1 : ℝ) / SC ≤ Real.sqrt ((148 / 100 : ℝ) * (2 * r1)) := by
        rw [Real.le_sqrt (div_nonneg (by exact_mod_cast hg1) hSC.le) (by linarith)]
        have hR : (g1 : ℝ) * (g1 : ℝ) ≤ (1480000000000 : ℝ) * (2 * (u1 : ℝ)) := by exact_mod_cast hsq1
        rw [div_pow, div_le_iff₀ (sq_pos_of_pos hSC)]
        simp only [r1, SC] at hR ⊢; push_cast; field_simp; nlinarith
      have hg2_le : (g2 : ℝ) / SC ≤ Real.sqrt ((148 / 100 : ℝ) * (2 * r2)) := by
        rw [Real.le_sqrt (div_nonneg (by exact_mod_cast hg2) hSC.le) (by linarith)]
        have hR : (g2 : ℝ) * (g2 : ℝ) ≤ (1480000000000 : ℝ) * (2 * (u2 : ℝ)) := by exact_mod_cast hsq2
        rw [div_pow, div_le_iff₀ (sq_pos_of_pos hSC)]
        simp only [r2, SC] at hR ⊢; push_cast; field_simp; nlinarith
      have hlin : (1 - t) * ((g1 : ℝ) / SC) + t * ((g2 : ℝ) / SC) ≤
          (1 - t) * Real.sqrt ((148 / 100 : ℝ) * (2 * r1)) +
          t * Real.sqrt ((148 / 100 : ℝ) * (2 * r2)) := by nlinarith
      exact le_trans hlin (le_trans hcs hG_ge)
    · set um := fdiv (u1 + u2) 2
      set x1Lo := expNegLo u1; set x1Hi := expNegHi u1
      set x2Lo := expNegLo u2; set x2Hi := expNegHi u2
      set xmLo := expNegLo um
      dsimp only at hc
      split at hc
      · cases hc
      · rename_i hxbad
        simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_le] at hxbad
        set sl1 := SC - x1Hi; set sl2 := SC - x2Hi; set slm := fdiv (sl1 + sl2) 2
        set aLo1 := SC + fdiv (49 * slm * (2 * sl1 - slm)) (100 * SC)
        set aLo2 := SC + fdiv (49 * slm * (2 * sl2 - slm)) (100 * SC)
        set p := getAHiPair u2 um x2Lo xmLo
        set aHi1 := p.1; set aHi2 := p.2
        set aM := fdiv (aHi1 + aHi2) 2
        split at hc
        · cases hc
        · rename_i hmbad
          simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_lt] at hmbad
          split at hc
          · cases hc
          rename_i hlam_bad
          simp only [decide_eq_true_eq, not_lt] at hlam_bad
          set lA1 := lamHi + cdiv ((aHi1 - aM) * SC) aM
          set lA2 := lamHi + cdiv ((aHi2 - aM) * SC) aM
          set w1 := 2 * u1 - lA1; set w2 := 2 * u2 - lA2
          split at hc
          · cases hc
          rename_i hwbad
          simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_le] at hwbad
          cases hF1 : evalF w1 w1Lo w1Hi with
          | none => simp [hF1] at hc
          | some b1 =>
            rcases b1 with ⟨f1Lo, f1Hi, f1pLo, f1pHi⟩
            cases hF2 : evalF w2 w2Lo w2Hi with
            | none => simp [hF1, hF2] at hc
            | some b2 =>
              rcases b2 with ⟨f2Lo, f2Hi, f2pLo, f2pHi⟩
              simp only [hF1, hF2, Bool.and_eq_true, decide_eq_true_eq] at hc
              rcases hc with ⟨⟨⟨hg1, hg2⟩, hsq1⟩, hsq2⟩
              refine ⟨hg1, hg2, fun t ht0 ht1 => ?_⟩
              set r1 : ℝ := (u1 : ℝ) / SC; set r2 : ℝ := (u2 : ℝ) / SC
              set u : ℝ := (1 - t) * r1 + t * r2
              have hu2_pos : 0 < u2 := lt_trans hu1 hbad.1
              -- Step 1: Afn u ≥ (1-t)*(aLo1/SC) + t*(aLo2/SC)
              have hexp_conv : Real.exp (-u) ≤ (1 - t) * Real.exp (-r1) + t * Real.exp (-r2) := by
                have harg : -u = (1 - t) * (-r1) + t * (-r2) := by simp only [u]; ring
                rw [harg]
                have := convexOn_exp.2 (Set.mem_univ (-r1)) (Set.mem_univ (-r2)) (show 0 ≤ 1 - t by linarith) ht0 (by ring)
                simpa [smul_eq_mul] using this
              have hx1_hi : Real.exp (-r1) ≤ (x1Hi : ℝ) / SC := expNegHi_sound hu1.le
              have hx2_hi : Real.exp (-r2) ≤ (x2Hi : ℝ) / SC := expNegHi_sound hu2_pos.le
              have hs_lo : (1 - t) * ((sl1 : ℝ) / SC) + t * ((sl2 : ℝ) / SC) ≤ 1 - Real.exp (-u) := by
                have h1 : (sl1 : ℝ) / SC = 1 - (x1Hi : ℝ) / SC := by
                  simp only [sl1]; push_cast; rw [sub_div, div_self hSC.ne']
                have h2 : (sl2 : ℝ) / SC = 1 - (x2Hi : ℝ) / SC := by
                  simp only [sl2]; push_cast; rw [sub_div, div_self hSC.ne']
                have h3 : (1 - t) * (1 - (x1Hi : ℝ) / SC) + t * (1 - (x2Hi : ℝ) / SC) ≤
                    (1 - t) * (1 - Real.exp (-r1)) + t * (1 - Real.exp (-r2)) :=
                  add_le_add (mul_le_mul_of_nonneg_left (by linarith) (by linarith))
                    (mul_le_mul_of_nonneg_left (by linarith) ht0)
                rw [h1, h2]; linarith
              have hslm_nn : (0 : ℝ) ≤ (slm : ℝ) / SC := by
                have h1 : x1Hi ≤ SC := expNegHi_le_SC' hu1.le
                have h2 : x2Hi ≤ SC := expNegHi_le_SC' hu2_pos.le
                have h3 : 0 ≤ slm := Int.ediv_nonneg (by simp only [sl1, sl2]; omega) (by decide)
                exact div_nonneg (by exact_mod_cast h3) hSC.le
              have hA_lo : (1 - t) * ((aLo1 : ℝ) / SC) + t * ((aLo2 : ℝ) / SC) ≤ Afn u := by
                have htan : 1 + (49 / 100 : ℝ) * ((slm : ℝ) / SC) * (2 * (1 - Real.exp (-u)) - (slm : ℝ) / SC) ≤ Afn u := by
                  unfold Afn
                  have hsq := sq_nonneg ((1 - Real.exp (-u)) - (slm : ℝ) / SC)
                  have : (1 - Real.exp (-u)) ^ 2 - ((slm : ℝ) / SC) * (2 * (1 - Real.exp (-u)) - (slm : ℝ) / SC) =
                      ((1 - Real.exp (-u)) - (slm : ℝ) / SC) ^ 2 := by ring
                  linarith
                have hlin1 : (aLo1 : ℝ) / SC ≤ 1 + (49 / 100 : ℝ) * ((slm : ℝ) / SC) * (2 * ((sl1 : ℝ) / SC) - (slm : ℝ) / SC) := by
                  have hd := fdiv_le_div (a := 49 * slm * (2 * sl1 - slm)) (b := 100 * SC) (by decide)
                  push_cast at hd
                  simp only [aLo1]; push_cast; rw [add_div, div_self hSC.ne']
                  have hrew : (49 / 100 : ℝ) * ((slm : ℝ) / SC) * (2 * ((sl1 : ℝ) / SC) - (slm : ℝ) / SC) =
                      (49 * (slm : ℝ) * (2 * (sl1 : ℝ) - slm) / (100 * SC)) / SC := by field_simp [hSC.ne']
                  rw [hrew]
                  have := div_le_div_of_nonneg_right hd hSC.le
                  linarith
                have hlin2 : (aLo2 : ℝ) / SC ≤ 1 + (49 / 100 : ℝ) * ((slm : ℝ) / SC) * (2 * ((sl2 : ℝ) / SC) - (slm : ℝ) / SC) := by
                  have hd := fdiv_le_div (a := 49 * slm * (2 * sl2 - slm)) (b := 100 * SC) (by decide)
                  push_cast at hd
                  simp only [aLo2]; push_cast; rw [add_div, div_self hSC.ne']
                  have hrew : (49 / 100 : ℝ) * ((slm : ℝ) / SC) * (2 * ((sl2 : ℝ) / SC) - (slm : ℝ) / SC) =
                      (49 * (slm : ℝ) * (2 * (sl2 : ℝ) - slm) / (100 * SC)) / SC := by field_simp [hSC.ne']
                  rw [hrew]
                  have := div_le_div_of_nonneg_right hd hSC.le
                  linarith
                have hcomb : (1 - t) * ((aLo1 : ℝ) / SC) + t * ((aLo2 : ℝ) / SC) ≤
                    1 + (49 / 100 : ℝ) * ((slm : ℝ) / SC) * (2 * ((1 - t) * ((sl1 : ℝ) / SC) + t * ((sl2 : ℝ) / SC)) - (slm : ℝ) / SC) := by
                  have hadd := add_le_add (mul_le_mul_of_nonneg_left hlin1 (show 0 ≤ 1 - t by linarith))
                    (mul_le_mul_of_nonneg_left hlin2 ht0)
                  have hid : (1 - t) * (1 + (49 / 100 : ℝ) * ((slm : ℝ) / SC) * (2 * ((sl1 : ℝ) / SC) - (slm : ℝ) / SC)) +
                      t * (1 + (49 / 100 : ℝ) * ((slm : ℝ) / SC) * (2 * ((sl2 : ℝ) / SC) - (slm : ℝ) / SC)) =
                      1 + (49 / 100 : ℝ) * ((slm : ℝ) / SC) * (2 * ((1 - t) * ((sl1 : ℝ) / SC) + t * ((sl2 : ℝ) / SC)) - (slm : ℝ) / SC) := by ring
                  linarith
                have hstep := mul_le_mul_of_nonneg_left (show 2 * ((1 - t) * ((sl1 : ℝ) / SC) + t * ((sl2 : ℝ) / SC)) - (slm : ℝ) / SC ≤
                    2 * (1 - Real.exp (-u)) - (slm : ℝ) / SC by linarith) (mul_nonneg (show (0 : ℝ) ≤ 49 / 100 by norm_num) hslm_nn)
                linarith
              -- Step 2: F(wfn u) ≥ (1-t)*ff1 + t*ff2
              have hA_hi_all := getAHiPair_sound hu1 hbad.1 hbad.2 hxbad.1.2 hxbad.2
              have hA_hi : Afn u ≤ (1 - t) * ((aHi1 : ℝ) / SC) + t * ((aHi2 : ℝ) / SC) :=
                hA_hi_all.2.2 t ht0 ht1
              have haM_pos : (0 : ℝ) < (aM : ℝ) / SC :=
                div_pos (Int.cast_pos.mpr (lt_of_lt_of_le SC_pos_int hmbad.1.2)) hSC
              have haM_pos_int : (0 : Int) < aM := lt_of_lt_of_le SC_pos_int hmbad.1.2
              have hlog_aM : Real.log ((aM : ℝ) / SC) ≤ (lamHi : ℝ) / SC := by
                have h1 : Real.exp (-((lamHi : ℝ) / SC)) ≤ (expNegHi lamHi : ℝ) / SC :=
                  expNegHi_sound hmbad.2
                have h2 : (expNegHi lamHi : ℝ) / SC ≤ 1 / ((aM : ℝ) / SC) := by
                  have hR : (expNegHi lamHi : ℝ) * (aM : ℝ) ≤ (SC : ℝ) * SC := by exact_mod_cast hlam_bad
                  rw [div_le_div_iff₀ hSC haM_pos]
                  have : (expNegHi lamHi : ℝ) * ((aM : ℝ) / SC) ≤ 1 * SC := by
                    rw [mul_div_assoc', div_le_iff₀ hSC]; linarith
                  linarith
                have h3 : Real.exp (-((lamHi : ℝ) / SC)) ≤ ((aM : ℝ) / SC)⁻¹ := by
                  simpa [one_div] using le_trans h1 h2
                have h4 := Real.log_le_log (Real.exp_pos _) h3
                rw [Real.log_exp, Real.log_inv] at h4; linarith
              have hlog_A : Real.log (Afn u) ≤ (1 - t) * ((lA1 : ℝ) / SC) + t * ((lA2 : ℝ) / SC) := by
                have h1 : Real.log (Afn u / ((aM : ℝ) / SC)) ≤ Afn u / ((aM : ℝ) / SC) - 1 :=
                  Real.log_le_sub_one_of_pos (div_pos (by linarith [Afn_ge_one u]) haM_pos)
                rw [Real.log_div (by linarith [Afn_ge_one u]) haM_pos.ne'] at h1
                have h2 : Real.log (Afn u) ≤ (lamHi : ℝ) / SC + (Afn u - (aM : ℝ) / SC) / ((aM : ℝ) / SC) := by
                  have : Afn u / ((aM : ℝ) / SC) - 1 = (Afn u - (aM : ℝ) / SC) / ((aM : ℝ) / SC) := by
                    field_simp [haM_pos.ne']
                  linarith
                have h3 : (Afn u - (aM : ℝ) / SC) / ((aM : ℝ) / SC) ≤
                    (1 - t) * (((aHi1 : ℝ) - aM) / aM) + t * (((aHi2 : ℝ) - aM) / aM) := by
                  have hrew : (1 - t) * (((aHi1 : ℝ) - aM) / aM) + t * (((aHi2 : ℝ) - aM) / aM) =
                      ((1 - t) * ((aHi1 : ℝ) / SC) + t * ((aHi2 : ℝ) / SC) - (aM : ℝ) / SC) / ((aM : ℝ) / SC) := by
                    field_simp [hSC.ne', (Int.cast_pos.mpr haM_pos_int).ne']; ring
                  rw [hrew]; exact div_le_div_of_nonneg_right (by linarith) haM_pos.le
                have hlA1 : (lamHi : ℝ) / SC + ((aHi1 : ℝ) - aM) / aM ≤ (lA1 : ℝ) / SC := by
                  have hd := div_le_cdiv (a := (aHi1 - aM) * SC) haM_pos_int
                  push_cast at hd
                  simp only [lA1]; push_cast; rw [add_div]
                  have : ((aHi1 : ℝ) - aM) / aM = ((aHi1 : ℝ) - aM) * SC / aM / SC := by field_simp [hSC.ne']
                  rw [this]; linarith [div_le_div_of_nonneg_right hd hSC.le]
                have hlA2 : (lamHi : ℝ) / SC + ((aHi2 : ℝ) - aM) / aM ≤ (lA2 : ℝ) / SC := by
                  have hd := div_le_cdiv (a := (aHi2 - aM) * SC) haM_pos_int
                  push_cast at hd
                  simp only [lA2]; push_cast; rw [add_div]
                  have : ((aHi2 : ℝ) - aM) / aM = ((aHi2 : ℝ) - aM) * SC / aM / SC := by field_simp [hSC.ne']
                  rw [this]; linarith [div_le_div_of_nonneg_right hd hSC.le]
                have hcomb := add_le_add (mul_le_mul_of_nonneg_left hlA1 (show 0 ≤ 1 - t by linarith))
                  (mul_le_mul_of_nonneg_left hlA2 ht0)
                have hid : (1 - t) * ((lamHi : ℝ) / SC + ((aHi1 : ℝ) - aM) / aM) +
                    t * ((lamHi : ℝ) / SC + ((aHi2 : ℝ) - aM) / aM) =
                    (lamHi : ℝ) / SC + ((1 - t) * (((aHi1 : ℝ) - aM) / aM) + t * (((aHi2 : ℝ) - aM) / aM)) := by ring
                linarith
              have hw_ge : (1 - t) * ((w1 : ℝ) / SC) + t * ((w2 : ℝ) / SC) ≤ wfn u := by
                have hw1_eq : (w1 : ℝ) / SC = 2 * r1 - (lA1 : ℝ) / SC := by
                  simp only [w1, r1]; push_cast; ring
                have hw2_eq : (w2 : ℝ) / SC = 2 * r2 - (lA2 : ℝ) / SC := by
                  simp only [w2, r2]; push_cast; ring
                rw [hw1_eq, hw2_eq]; unfold wfn; simp only [u]; linarith
              have hw1R : (0 : ℝ) < (w1 : ℝ) / SC := div_pos (Int.cast_pos.mpr hwbad.1) hSC
              have hw2R : (0 : ℝ) < (w2 : ℝ) / SC := div_pos (Int.cast_pos.mpr hwbad.2) hSC
              have hF1_s := evalF_sound hwbad.1 hF1
              have hF2_s := evalF_sound hwbad.2 hF2
              -- Step 3: Combine A_lo and F_lin via sqrt_mul_linear_ge!
              have ha1_nn : (0 : ℝ) ≤ (aLo1 : ℝ) / SC := div_nonneg (by exact_mod_cast hmbad.1.1.1) hSC.le
              have ha2_nn : (0 : ℝ) ≤ (aLo2 : ℝ) / SC := div_nonneg (by exact_mod_cast hmbad.1.1.2) hSC.le
              set ff1 := max 0 ((f1Lo : ℝ) / SC)
              set ff2 := max 0 ((f2Lo : ℝ) / SC)
              have hff1_le : ff1 ≤ F ((w1 : ℝ) / SC) := max_le (F_pos hw1R).le hF1_s.1
              have hff2_le : ff2 ≤ F ((w2 : ℝ) / SC) := max_le (F_pos hw2R).le hF2_s.1
              have hF_lin2 : (1 - t) * ff1 + t * ff2 ≤ F (wfn u) := by
                have hsec : (1 - t) * F ((w1 : ℝ) / SC) + t * F ((w2 : ℝ) / SC) ≤
                    F ((1 - t) * ((w1 : ℝ) / SC) + t * ((w2 : ℝ) / SC)) := by
                  rcases lt_trichotomy ((w1 : ℝ) / SC) ((w2 : ℝ) / SC) with hlt | heq | hgt
                  · exact F_secant_le hw1R hlt ht0 ht1
                  · rw [heq]; ring_nf; exact le_rfl
                  · have h1 := F_secant_le hw2R hgt (show 0 ≤ 1 - t by linarith) (show 1 - t ≤ 1 by linarith)
                    have harg : (1 - (1 - t)) * ((w2 : ℝ) / SC) + (1 - t) * ((w1 : ℝ) / SC) =
                        (1 - t) * ((w1 : ℝ) / SC) + t * ((w2 : ℝ) / SC) := by ring
                    rw [harg] at h1; linarith
                have hw_mid_pos : 0 < (1 - t) * ((w1 : ℝ) / SC) + t * ((w2 : ℝ) / SC) := by
                  rcases le_total ((w1 : ℝ) / SC) ((w2 : ℝ) / SC) with hle | hle
                  · have : (w1 : ℝ) / SC ≤ (1 - t) * ((w1 : ℝ) / SC) + t * ((w2 : ℝ) / SC) := by nlinarith only [hle, ht0, ht1]
                    linarith
                  · have : (w2 : ℝ) / SC ≤ (1 - t) * ((w1 : ℝ) / SC) + t * ((w2 : ℝ) / SC) := by nlinarith only [hle, ht0, ht1]
                    linarith
                have hu_pos : 0 < u := by
                  have h1 : 0 < r1 := div_pos (Int.cast_pos.mpr hu1) hSC
                  have hlt : r1 < r2 := div_lt_div_of_pos_right (Int.cast_lt.mpr hbad.1) hSC
                  have hge : r1 ≤ u := by simp only [u]; nlinarith only [hlt, ht0, ht1]
                  linarith
                have hmono : F ((1 - t) * ((w1 : ℝ) / SC) + t * ((w2 : ℝ) / SC)) ≤ F (wfn u) :=
                  F_strictMono.monotoneOn hw_mid_pos (wfn_pos hu_pos) hw_ge
                have hcomb := add_le_add (mul_le_mul_of_nonneg_left hff1_le (show 0 ≤ 1 - t by linarith))
                  (mul_le_mul_of_nonneg_left hff2_le ht0)
                linarith
              have hff1_nn : 0 ≤ ff1 := le_max_left 0 ((f1Lo : ℝ) / SC)
              have hff2_nn : 0 ≤ ff2 := le_max_left 0 ((f2Lo : ℝ) / SC)
              have hcs := sqrt_mul_linear_ge ha1_nn ha2_nn hff1_nn hff2_nn ht0 ht1
              have hg1_le : (g1 : ℝ) / SC ≤ Real.sqrt (((aLo1 : ℝ) / SC) * ff1) := by
                rw [Real.le_sqrt (div_nonneg (by exact_mod_cast hg1) hSC.le) (mul_nonneg ha1_nn (le_max_left 0 _))]
                have hR : (g1 : ℝ) * g1 ≤ (aLo1 : ℝ) * f1Lo := by exact_mod_cast hsq1
                have h1 : ((g1 : ℝ) / SC) ^ 2 ≤ ((aLo1 : ℝ) / SC) * ((f1Lo : ℝ) / SC) := by
                  rw [div_pow, div_mul_div_comm, ← sq, div_le_div_iff_of_pos_right (sq_pos_of_pos hSC), sq]
                  exact hR
                exact le_trans h1 (mul_le_mul_of_nonneg_left (le_max_right 0 _) ha1_nn)
              have hg2_le : (g2 : ℝ) / SC ≤ Real.sqrt (((aLo2 : ℝ) / SC) * ff2) := by
                rw [Real.le_sqrt (div_nonneg (by exact_mod_cast hg2) hSC.le) (mul_nonneg ha2_nn (le_max_left 0 _))]
                have hR : (g2 : ℝ) * g2 ≤ (aLo2 : ℝ) * f2Lo := by exact_mod_cast hsq2
                have h1 : ((g2 : ℝ) / SC) ^ 2 ≤ ((aLo2 : ℝ) / SC) * ((f2Lo : ℝ) / SC) := by
                  rw [div_pow, div_mul_div_comm, ← sq, div_le_div_iff_of_pos_right (sq_pos_of_pos hSC), sq]
                  exact hR
                exact le_trans h1 (mul_le_mul_of_nonneg_left (le_max_right 0 _) ha2_nn)
              have hG_ge : Real.sqrt (((1 - t) * ((aLo1 : ℝ) / SC) + t * ((aLo2 : ℝ) / SC)) *
                  ((1 - t) * ff1 + t * ff2)) ≤ Gfn u := by
                unfold Gfn; apply Real.sqrt_le_sqrt
                have hff_nn : 0 ≤ (1 - t) * ff1 + t * ff2 :=
                  add_nonneg (mul_nonneg (show 0 ≤ 1 - t by linarith) (le_max_left 0 _)) (mul_nonneg ht0 (le_max_left 0 _))
                exact mul_le_mul hA_lo hF_lin2 hff_nn (by linarith [Afn_ge_one u])
              have hlin := add_le_add (mul_le_mul_of_nonneg_left hg1_le (show 0 ≤ 1 - t by linarith))
                (mul_le_mul_of_nonneg_left hg2_le ht0)
              linarith

def checkCorner (fw1Lo fw2Lo w1 w2 fU fV gu gv u v : Int) : Bool :=
  let fuv := fw1Lo + fdiv ((fw2Lo - fw1Lo) * (u + v - w1)) (w2 - w1)
  let gp := fdiv (gu * gv) SC
  decide (51849 * fuv + 9876 * gp ≥ 50000 * (fU + fV))

inductive BoxTree
  | skipDiag
  | skipCorner
  | skipTail
  | leaf (w1Lo w1Hi w2Lo w2Hi umLo umHi vmLo vmHi
          uLam uW1Lo uW1Hi uW2Lo uW2Hi uG1 uG2
          vLam vW1Lo vW1Hi vW2Lo vW2Hi vG1 vG2 : Int)
  | splitU (m : Int) (l r : BoxTree)
  | splitV (m : Int) (l r : BoxTree)

def checkTree (u1 u2 v1 v2 : Int) : BoxTree → Bool
  | .skipDiag => decide (u2 ≤ v1)
  | .skipCorner => decide (u2 ≤ 5000000000) && decide (v2 ≤ 5000000000)
  | .skipTail => decide (u1 + v1 ≥ 27 * SC)
  | .splitU m l r => decide (u1 < m) && decide (m < u2) && checkTree u1 m v1 v2 l && checkTree m u2 v1 v2 r
  | .splitV m l r => decide (v1 < m) && decide (m < v2) && checkTree u1 u2 v1 m l && checkTree u1 u2 m v2 r
  | .leaf w1Lo w1Hi w2Lo w2Hi umLo umHi vmLo vmHi
          uLam uW1Lo uW1Hi uW2Lo uW2Hi uG1 uG2
          vLam vW1Lo vW1Hi vW2Lo vW2Hi vG1 vG2 =>
    if decide (u1 ≤ 0) || decide (v1 ≤ 0) || decide (u1 ≥ u2) || decide (v1 ≥ v2) ||
       decide ((u1 + u2) % 2 ≠ 0) || decide ((v1 + v2) % 2 ≠ 0) then false
    else
      let um := fdiv (u1 + u2) 2; let vm := fdiv (v1 + v2) 2
      let w1 := u1 + v1; let w2 := u2 + v2
      match evalF w1 w1Lo w1Hi, evalF w2 w2Lo w2Hi, evalF um umLo umHi, evalF vm vmLo vmHi with
      | some (fw1Lo, _, _, _), some (fw2Lo, _, _, _),
        some (_, fumHi, fumpLo, fumpHi), some (_, fvmHi, fvmpLo, fvmpHi) =>
        if checkLinG u1 u2 uLam uW1Lo uW1Hi uW2Lo uW2Hi uG1 uG2 &&
           checkLinG v1 v2 vLam vW1Lo vW1Hi vW2Lo vW2Hi vG1 vG2 then
          let du := u2 - um; let dv := v2 - vm
          let fu0 := fumHi - fdiv (fumpLo * du) SC
          let fu1 := fumHi + cdiv (fumpHi * du) SC
          let fv0 := fvmHi - fdiv (fvmpLo * dv) SC
          let fv1 := fvmHi + cdiv (fvmpHi * dv) SC
          checkCorner fw1Lo fw2Lo w1 w2 fu0 fv0 uG1 vG1 u1 v1 &&
          checkCorner fw1Lo fw2Lo w1 w2 fu0 fv1 uG1 vG2 u1 v2 &&
          checkCorner fw1Lo fw2Lo w1 w2 fu1 fv0 uG2 vG1 u2 v1 &&
          checkCorner fw1Lo fw2Lo w1 w2 fu1 fv1 uG2 vG2 u2 v2
        else false
      | _, _, _, _ => false

lemma checkCorner_ineq {fw1Lo fw2Lo w1 w2 fU fV gu gv u v : Int}
    (hw : w1 < w2) (hc : checkCorner fw1Lo fw2Lo w1 w2 fU fV gu gv u v = true) :
    (2000 / 2469 : ℝ) * ((fU : ℝ) / SC + (fV : ℝ) / SC) ≤
      (21 / 25 : ℝ) * ((fw1Lo : ℝ) / SC + (((fw2Lo : ℝ) / SC - (fw1Lo : ℝ) / SC) *
        (((u : ℝ) / SC + (v : ℝ) / SC - (w1 : ℝ) / SC) / ((w2 : ℝ) / SC - (w1 : ℝ) / SC)))) +
      (4 / 25 : ℝ) * (((gu : ℝ) / SC) * ((gv : ℝ) / SC)) := by
  have hSC : (0 : ℝ) < (SC : ℝ) := SC_pos
  simp only [checkCorner, decide_eq_true_eq] at hc
  have hR : (50000 : ℝ) * ((fU : ℝ) + fV) ≤
      51849 * (fw1Lo + fdiv ((fw2Lo - fw1Lo) * (u + v - w1)) (w2 - w1) : Int) +
      9876 * (fdiv (gu * gv) SC : Int) := by exact_mod_cast hc
  have hd1 := fdiv_le_div (a := (fw2Lo - fw1Lo) * (u + v - w1)) (b := w2 - w1) (by omega)
  have hd2 := fdiv_le_div (a := gu * gv) SC_pos_int
  push_cast at hR hd1 hd2
  have hrew1 : ((fw1Lo : ℝ) + ((fw2Lo : ℝ) - fw1Lo) * ((u : ℝ) + v - w1) / ((w2 : ℝ) - w1)) / SC =
      (fw1Lo : ℝ) / SC + (((fw2Lo : ℝ) / SC - (fw1Lo : ℝ) / SC) *
        (((u : ℝ) / SC + (v : ℝ) / SC - (w1 : ℝ) / SC) / ((w2 : ℝ) / SC - (w1 : ℝ) / SC))) := by
    have hne : (w2 : ℝ) - w1 ≠ 0 := by
      have : (w1 : ℝ) < w2 := Int.cast_lt.mpr hw
      linarith
    field_simp [hSC.ne', hne]
  have hrew2 : ((gu : ℝ) * gv / SC) / SC = ((gu : ℝ) / SC) * ((gv : ℝ) / SC) := by
    field_simp [hSC.ne']
  have hdiv : (50000 : ℝ) * ((fU : ℝ) / SC + (fV : ℝ) / SC) ≤
      51849 * (((fw1Lo : ℝ) + ((fw2Lo : ℝ) - fw1Lo) * ((u : ℝ) + v - w1) / ((w2 : ℝ) - w1)) / SC) +
      9876 * (((gu : ℝ) * gv / SC) / SC) := by
    have h1 : (50000 : ℝ) * ((fU : ℝ) + fV) ≤
        51849 * ((fw1Lo : ℝ) + ((fw2Lo : ℝ) - fw1Lo) * ((u : ℝ) + v - w1) / ((w2 : ℝ) - w1)) +
        9876 * ((gu : ℝ) * gv / SC) := by linarith
    have h2 := div_le_div_of_nonneg_right h1 hSC.le
    ring_nf at h2 ⊢; linarith
  rw [hrew1, hrew2] at hdiv
  linarith

lemma F_lin_upper {u1 u2 um fmHi fmpLo fmpHi : Int} {u lam : ℝ}
    (hu0 : 0 < u) (hum_pos : 0 < um) (hu12 : u1 < u2) (hum_eq : 2 * um = u1 + u2)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hu_eq : u = (1 - lam) * ((u1 : ℝ) / SC) + lam * ((u2 : ℝ) / SC))
    (hFm : F ((um : ℝ) / SC) ≤ (fmHi : ℝ) / SC)
    (hFmpLo : (fmpLo : ℝ) / SC ≤ Fp ((um : ℝ) / SC))
    (hFmpHi : Fp ((um : ℝ) / SC) ≤ (fmpHi : ℝ) / SC) :
    F u ≤ (1 - lam) * (((fmHi - fdiv (fmpLo * (u2 - um)) SC : Int) : ℝ) / SC) +
      lam * (((fmHi + cdiv (fmpHi * (u2 - um)) SC : Int) : ℝ) / SC) := by
  have hSC : (0 : ℝ) < (SC : ℝ) := SC_pos
  set r1 : ℝ := (u1 : ℝ) / SC; set r2 : ℝ := (u2 : ℝ) / SC
  set du : Int := u2 - um
  have hr12 : r1 < r2 := div_lt_div_of_pos_right (Int.cast_lt.mpr hu12) hSC
  have hrm : (um : ℝ) / SC = (r1 + r2) / 2 := by
    have : (2 : ℝ) * um = (u1 : ℝ) + u2 := by exact_mod_cast hum_eq
    simp only [r1, r2]; field_simp [hSC.ne']; linarith
  have hdu : (du : ℝ) / SC = (r2 - r1) / 2 := by
    have : (2 : ℝ) * du = (u2 : ℝ) - u1 := by
      have : 2 * du = u2 - u1 := by omega
      exact_mod_cast this
    simp only [r1, r2]; field_simp [hSC.ne']; linarith
  have htan := F_le_tangent hu0 (div_pos (Int.cast_pos.mpr hum_pos) hSC)
  have hlin : F ((um : ℝ) / SC) + Fp ((um : ℝ) / SC) * (u - (um : ℝ) / SC) =
      (1 - lam) * (F ((um : ℝ) / SC) - Fp ((um : ℝ) / SC) * ((du : ℝ) / SC)) +
      lam * (F ((um : ℝ) / SC) + Fp ((um : ℝ) / SC) * ((du : ℝ) / SC)) := by
    rw [hu_eq, hrm, hdu]; ring
  have hdu0 : (0 : ℝ) ≤ (du : ℝ) / SC := by linarith [hdu, hr12]
  have hf0_ge : F ((um : ℝ) / SC) - Fp ((um : ℝ) / SC) * ((du : ℝ) / SC) ≤
      ((fmHi - fdiv (fmpLo * du) SC : Int) : ℝ) / SC := by
    have hd := fdiv_le_div (a := fmpLo * du) SC_pos_int
    push_cast at hd ⊢; rw [sub_div]
    have h1 : (fdiv (fmpLo * du) SC : ℝ) / SC ≤ ((fmpLo : ℝ) / SC) * ((du : ℝ) / SC) := by
      have : ((fmpLo : ℝ) / SC) * ((du : ℝ) / SC) = ((fmpLo : ℝ) * du / SC) / SC := by field_simp [hSC.ne']
      rw [this]; exact div_le_div_of_nonneg_right hd hSC.le
    have h2 := mul_le_mul_of_nonneg_right hFmpLo hdu0
    linarith
  have hf1_ge : F ((um : ℝ) / SC) + Fp ((um : ℝ) / SC) * ((du : ℝ) / SC) ≤
      ((fmHi + cdiv (fmpHi * du) SC : Int) : ℝ) / SC := by
    have hd := div_le_cdiv (a := fmpHi * du) SC_pos_int
    push_cast at hd ⊢; rw [add_div]
    have h1 : ((fmpHi : ℝ) / SC) * ((du : ℝ) / SC) ≤ (cdiv (fmpHi * du) SC : ℝ) / SC := by
      have : ((fmpHi : ℝ) / SC) * ((du : ℝ) / SC) = ((fmpHi : ℝ) * du / SC) / SC := by field_simp [hSC.ne']
      rw [this]; exact div_le_div_of_nonneg_right hd hSC.le
    have h2 := mul_le_mul_of_nonneg_right hFmpHi hdu0
    linarith
  have hadd := add_le_add (mul_le_mul_of_nonneg_left hf0_ge (show 0 ≤ 1 - lam by linarith))
    (mul_le_mul_of_nonneg_left hf1_ge hlam0)
  linarith

lemma checkTree_sound : ∀ (T : BoxTree) (u1 u2 v1 v2 : Int),
    checkTree u1 u2 v1 v2 T = true →
    ∀ u v : ℝ, 0 < v → v < u →
      (u1 : ℝ) / SC ≤ u → u ≤ (u2 : ℝ) / SC →
      (v1 : ℝ) / SC ≤ v → v ≤ (v2 : ℝ) / SC →
      Ineq2UV u v := by
  intro T
  induction T with
  | skipDiag =>
    intro u1 u2 v1 v2 hc u v _ hvu _ hu2 hv1 _
    simp only [checkTree, decide_eq_true_eq] at hc
    have h1 : (u2 : ℝ) / SC ≤ (v1 : ℝ) / SC := div_le_div_of_nonneg_right (Int.cast_le.mpr hc) SC_pos.le
    linarith
  | skipCorner =>
    intro u1 u2 v1 v2 hc u v hv0 hvu _ hu2 _ _
    simp only [checkTree, Bool.and_eq_true, decide_eq_true_eq] at hc
    have hu_le : u ≤ 1 / 200 := by
      have : (u2 : ℝ) / SC ≤ 1 / 200 := by
        have h1 : (u2 : ℝ) ≤ 5000000000 := Int.cast_le.mpr hc.1
        rw [div_le_iff₀ SC_pos]; simp only [SC]; linarith
      linarith
    exact ineq2_corner hv0 hvu.le hu_le
  | skipTail =>
    intro u1 u2 v1 v2 hc u v hv0 hvu hu1 _ hv1 _
    simp only [checkTree, decide_eq_true_eq] at hc
    have hsum : 27 ≤ u + v := by
      have h1 : (27 : ℝ) * SC ≤ (u1 : ℝ) + v1 := by exact_mod_cast hc
      have h2 : (27 : ℝ) ≤ (u1 : ℝ) / SC + (v1 : ℝ) / SC := by
        rw [← add_div, le_div_iff₀ SC_pos]; linarith
      linarith
    exact ineq2_tail (lt_trans hv0 hvu) hv0 hsum
  | splitU m l r ihl ihr =>
    intro u1 u2 v1 v2 hc u v hv0 hvu hu1 hu2 hv1 hv2
    simp only [checkTree, Bool.and_eq_true, decide_eq_true_eq] at hc
    rcases hc with ⟨⟨⟨_, _⟩, hl⟩, hr⟩
    by_cases hum : u ≤ (m : ℝ) / SC
    · exact ihl u1 m v1 v2 hl u v hv0 hvu hu1 hum hv1 hv2
    · exact ihr m u2 v1 v2 hr u v hv0 hvu (le_of_not_ge hum) hu2 hv1 hv2
  | splitV m l r ihl ihr =>
    intro u1 u2 v1 v2 hc u v hv0 hvu hu1 hu2 hv1 hv2
    simp only [checkTree, Bool.and_eq_true, decide_eq_true_eq] at hc
    rcases hc with ⟨⟨⟨_, _⟩, hl⟩, hr⟩
    by_cases hvm : v ≤ (m : ℝ) / SC
    · exact ihl u1 u2 v1 m hl u v hv0 hvu hu1 hu2 hv1 hvm
    · exact ihr u1 u2 m v2 hr u v hv0 hvu hu1 hu2 (le_of_not_ge hvm) hv2
  | leaf w1Lo w1Hi w2Lo w2Hi umLo umHi vmLo vmHi
         uLam uW1Lo uW1Hi uW2Lo uW2Hi uG1 uG2
         vLam vW1Lo vW1Hi vW2Lo vW2Hi vG1 vG2 =>
    intro u1 u2 v1 v2 hc u v hv0 hvu hu1 hu2 hv1 hv2
    have hSC : (0 : ℝ) < (SC : ℝ) := SC_pos
    simp only [checkTree] at hc
    split at hc
    · cases hc
    · rename_i hbad
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_le, not_ne_iff] at hbad
      rcases hbad with ⟨⟨⟨⟨⟨hu1_pos, hv1_pos⟩, hu12⟩, hv12⟩, hueven⟩, hveven⟩
      set um := fdiv (u1 + u2) 2; set vm := fdiv (v1 + v2) 2
      set w1 := u1 + v1; set w2 := u2 + v2
      cases hFw1 : evalF w1 w1Lo w1Hi with
      | none => simp [hFw1] at hc
      | some b1 =>
        rcases b1 with ⟨fw1Lo, fw1Hi, fw1pLo, fw1pHi⟩
        cases hFw2 : evalF w2 w2Lo w2Hi with
        | none => simp [hFw1, hFw2] at hc
        | some b2 =>
          rcases b2 with ⟨fw2Lo, fw2Hi, fw2pLo, fw2pHi⟩
          cases hFum : evalF um umLo umHi with
          | none => simp [hFw1, hFw2, hFum] at hc
          | some b3 =>
            rcases b3 with ⟨fumLo, fumHi, fumpLo, fumpHi⟩
            cases hFvm : evalF vm vmLo vmHi with
            | none => simp [hFw1, hFw2, hFum, hFvm] at hc
            | some b4 =>
              rcases b4 with ⟨fvmLo, fvmHi, fvmpLo, fvmpHi⟩
              simp only [hFw1, hFw2, hFum, hFvm] at hc
              split at hc
              · rename_i hGok
                simp only [Bool.and_eq_true] at hGok hc
                rcases hGok with ⟨hGu_ok, hGv_ok⟩
                rcases hc with ⟨⟨⟨hc00, hc01⟩, hc10⟩, hc11⟩
                have hum_eq : 2 * um = u1 + u2 := by change 2 * ((u1 + u2) / 2) = u1 + u2; omega
                have hvm_eq : 2 * vm = v1 + v2 := by change 2 * ((v1 + v2) / 2) = v1 + v2; omega
                have hum_pos : 0 < um := by omega
                have hvm_pos : 0 < vm := by omega
                have hw1_pos : 0 < w1 := by omega
                have hw2_pos : 0 < w2 := by omega
                have hw12 : w1 < w2 := by omega
                have sFw1 := evalF_sound hw1_pos hFw1
                have sFw2 := evalF_sound hw2_pos hFw2
                have sFum := evalF_sound hum_pos hFum
                have sFvm := evalF_sound hvm_pos hFvm
                have sGu := checkLinG_sound hu1_pos hGu_ok
                have sGv := checkLinG_sound hv1_pos hGv_ok
                set r1 : ℝ := (u1 : ℝ) / SC; set r2 : ℝ := (u2 : ℝ) / SC
                set q1 : ℝ := (v1 : ℝ) / SC; set q2 : ℝ := (v2 : ℝ) / SC
                have hr12 : r1 < r2 := div_lt_div_of_pos_right (Int.cast_lt.mpr hu12) hSC
                have hq12 : q1 < q2 := div_lt_div_of_pos_right (Int.cast_lt.mpr hv12) hSC
                set lam : ℝ := (u - r1) / (r2 - r1)
                set mu : ℝ := (v - q1) / (q2 - q1)
                have hlam0 : 0 ≤ lam := div_nonneg (by linarith) (by linarith)
                have hlam1 : lam ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
                have hmu0 : 0 ≤ mu := div_nonneg (by linarith) (by linarith)
                have hmu1 : mu ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
                have hu_eq : u = (1 - lam) * r1 + lam * r2 := by
                  simp only [lam]; field_simp [(show r2 - r1 ≠ 0 by linarith)]; ring
                have hv_eq : v = (1 - mu) * q1 + mu * q2 := by
                  simp only [mu]; field_simp [(show q2 - q1 ≠ 0 by linarith)]; ring
                -- Evaluate upper bounds on F u, F v and lower bounds on F(u+v), Gfn u * Gfn v!
                set du := u2 - um; set dv := v2 - vm
                set fu0 := fumHi - fdiv (fumpLo * du) SC
                set fu1 := fumHi + cdiv (fumpHi * du) SC
                set fv0 := fvmHi - fdiv (fvmpLo * dv) SC
                set fv1 := fvmHi + cdiv (fvmpHi * dv) SC
                -- 1. F u ≤ (1-lam)*(fu0/SC) + lam*(fu1/SC)
                have hFu_ub : F u ≤ (1 - lam) * ((fu0 : ℝ) / SC) + lam * ((fu1 : ℝ) / SC) :=
                  F_lin_upper (lt_trans hv0 hvu) hum_pos hu12 hum_eq hlam0 hlam1 hu_eq
                    sFum.2.1 sFum.2.2.1 sFum.2.2.2
                -- 2. F v ≤ (1-mu)*(fv0/SC) + mu*(fv1/SC)
                have hFv_ub : F v ≤ (1 - mu) * ((fv0 : ℝ) / SC) + mu * ((fv1 : ℝ) / SC) :=
                  F_lin_upper hv0 hvm_pos hv12 hvm_eq hmu0 hmu1 hv_eq
                    sFvm.2.1 sFvm.2.2.1 sFvm.2.2.2
                -- 3. F(u + v) ≥ linear secant on [w1/SC, w2/SC]
                set tau : ℝ := (u + v - (w1 : ℝ) / SC) / ((w2 : ℝ) / SC - (w1 : ℝ) / SC)
                have hw1_eq : (w1 : ℝ) / SC = r1 + q1 := by simp only [w1, r1, q1]; push_cast; ring
                have hw2_eq : (w2 : ℝ) / SC = r2 + q2 := by simp only [w2, r2, q2]; push_cast; ring
                have htau0 : 0 ≤ tau := div_nonneg (by linarith [hw1_eq]) (by linarith [hw1_eq, hw2_eq])
                have htau1 : tau ≤ 1 := (div_le_one (by linarith [hw1_eq, hw2_eq])).mpr (by linarith [hw2_eq])
                have hFuv_lb : (fw1Lo : ℝ) / SC + ((fw2Lo : ℝ) / SC - (fw1Lo : ℝ) / SC) * tau ≤ F (u + v) := by
                  have hsec := F_secant_le (div_pos (Int.cast_pos.mpr hw1_pos) hSC)
                    (div_lt_div_of_pos_right (Int.cast_lt.mpr hw12) hSC) htau0 htau1
                  have harg : (1 - tau) * ((w1 : ℝ) / SC) + tau * ((w2 : ℝ) / SC) = u + v := by
                    have hne : (w2 : ℝ) / SC - (w1 : ℝ) / SC ≠ 0 := by linarith [hw1_eq, hw2_eq]
                    have h1 : (1 - tau) * ((w1 : ℝ) / SC) + tau * ((w2 : ℝ) / SC) =
                        (w1 : ℝ) / SC + tau * ((w2 : ℝ) / SC - (w1 : ℝ) / SC) := by ring
                    rw [h1]; simp only [tau]; rw [div_mul_cancel₀ _ hne]; ring
                  rw [harg] at hsec
                  have hlin : (1 - tau) * ((fw1Lo : ℝ) / SC) + tau * ((fw2Lo : ℝ) / SC) =
                      (fw1Lo : ℝ) / SC + ((fw2Lo : ℝ) / SC - (fw1Lo : ℝ) / SC) * tau := by ring
                  have hadd := add_le_add (mul_le_mul_of_nonneg_left sFw1.1 (show 0 ≤ 1 - tau by linarith))
                    (mul_le_mul_of_nonneg_left sFw2.1 htau0)
                  linarith
                -- 4. Gfn u * Gfn v ≥ linear_u * linear_v
                have hGu_lb : (1 - lam) * ((uG1 : ℝ) / SC) + lam * ((uG2 : ℝ) / SC) ≤ Gfn u := by
                  rw [hu_eq]; exact sGu.2.2 lam hlam0 hlam1
                have hGv_lb : (1 - mu) * ((vG1 : ℝ) / SC) + mu * ((vG2 : ℝ) / SC) ≤ Gfn v := by
                  rw [hv_eq]; exact sGv.2.2 mu hmu0 hmu1
                have hGuv_lb : ((1 - lam) * ((uG1 : ℝ) / SC) + lam * ((uG2 : ℝ) / SC)) *
                    ((1 - mu) * ((vG1 : ℝ) / SC) + mu * ((vG2 : ℝ) / SC)) ≤ Gfn u * Gfn v :=
                  mul_le_mul hGu_lb hGv_lb
                    (add_nonneg (mul_nonneg (show 0 ≤ 1 - mu by linarith) (div_nonneg (by exact_mod_cast sGv.1) hSC.le))
                      (mul_nonneg hmu0 (div_nonneg (by exact_mod_cast sGv.2.1) hSC.le)))
                    (Real.sqrt_nonneg _)
                -- 5. Combine the 4 corner bounds and match the bilinear identities!
                have h00 := checkCorner_ineq hw12 hc00
                have h01 := checkCorner_ineq hw12 hc01
                have h10 := checkCorner_ineq hw12 hc10
                have h11 := checkCorner_ineq hw12 hc11
                set w00 := (1 - lam) * (1 - mu); set w01 := (1 - lam) * mu
                set w10 := lam * (1 - mu); set w11 := lam * mu
                have hw00 : 0 ≤ w00 := mul_nonneg (by linarith) (by linarith)
                have hw01 : 0 ≤ w01 := mul_nonneg (by linarith) hmu0
                have hw10 : 0 ≤ w10 := mul_nonneg hlam0 (by linarith)
                have hw11 : 0 ≤ w11 := mul_nonneg hlam0 hmu0
                have hcomb := add_le_add
                  (add_le_add (mul_le_mul_of_nonneg_left h00 hw00) (mul_le_mul_of_nonneg_left h01 hw01))
                  (add_le_add (mul_le_mul_of_nonneg_left h10 hw10) (mul_le_mul_of_nonneg_left h11 hw11))
                -- 5. Algebraic identity: convex combination of the 4 corners equals our bilinear expression!
                have hlhs_id :
                    w00 * ((2000 / 2469 : ℝ) * ((fu0 : ℝ) / SC + (fv0 : ℝ) / SC)) +
                    w01 * ((2000 / 2469 : ℝ) * ((fu0 : ℝ) / SC + (fv1 : ℝ) / SC)) +
                    (w10 * ((2000 / 2469 : ℝ) * ((fu1 : ℝ) / SC + (fv0 : ℝ) / SC)) +
                     w11 * ((2000 / 2469 : ℝ) * ((fu1 : ℝ) / SC + (fv1 : ℝ) / SC))) =
                    (2000 / 2469 : ℝ) * (((1 - lam) * ((fu0 : ℝ) / SC) + lam * ((fu1 : ℝ) / SC)) +
                      ((1 - mu) * ((fv0 : ℝ) / SC) + mu * ((fv1 : ℝ) / SC))) := by
                  simp only [w00, w01, w10, w11]; ring
                have hrhs_id :
                    w00 * ((21 / 25 : ℝ) * ((fw1Lo : ℝ) / SC + ((fw2Lo : ℝ) / SC - (fw1Lo : ℝ) / SC) *
                      ((r1 + q1 - (w1 : ℝ) / SC) / ((w2 : ℝ) / SC - (w1 : ℝ) / SC))) +
                      (4 / 25 : ℝ) * (((uG1 : ℝ) / SC) * ((vG1 : ℝ) / SC))) +
                    w01 * ((21 / 25 : ℝ) * ((fw1Lo : ℝ) / SC + ((fw2Lo : ℝ) / SC - (fw1Lo : ℝ) / SC) *
                      ((r1 + q2 - (w1 : ℝ) / SC) / ((w2 : ℝ) / SC - (w1 : ℝ) / SC))) +
                      (4 / 25 : ℝ) * (((uG1 : ℝ) / SC) * ((vG2 : ℝ) / SC))) +
                    (w10 * ((21 / 25 : ℝ) * ((fw1Lo : ℝ) / SC + ((fw2Lo : ℝ) / SC - (fw1Lo : ℝ) / SC) *
                      ((r2 + q1 - (w1 : ℝ) / SC) / ((w2 : ℝ) / SC - (w1 : ℝ) / SC))) +
                      (4 / 25 : ℝ) * (((uG2 : ℝ) / SC) * ((vG1 : ℝ) / SC))) +
                     w11 * ((21 / 25 : ℝ) * ((fw1Lo : ℝ) / SC + ((fw2Lo : ℝ) / SC - (fw1Lo : ℝ) / SC) *
                      ((r2 + q2 - (w1 : ℝ) / SC) / ((w2 : ℝ) / SC - (w1 : ℝ) / SC))) +
                      (4 / 25 : ℝ) * (((uG2 : ℝ) / SC) * ((vG2 : ℝ) / SC)))) =
                    (21 / 25 : ℝ) * ((fw1Lo : ℝ) / SC + ((fw2Lo : ℝ) / SC - (fw1Lo : ℝ) / SC) * tau) +
                    (4 / 25 : ℝ) * (((1 - lam) * ((uG1 : ℝ) / SC) + lam * ((uG2 : ℝ) / SC)) *
                      ((1 - mu) * ((vG1 : ℝ) / SC) + mu * ((vG2 : ℝ) / SC))) := by
                  simp only [w00, w01, w10, w11, tau]
                  have hne : (w2 : ℝ) / SC - (w1 : ℝ) / SC ≠ 0 := by linarith [hw1_eq, hw2_eq]
                  rw [hu_eq, hv_eq]
                  field_simp [hne]; ring
                unfold Ineq2UV
                rw [hlhs_id, hrhs_id] at hcomb
                linarith
              · cases hc

-- ============================================================================
-- SECTION 5: Finite Shannon Entropy, Liu-Ex5 Coupling, & Main Theorem
-- ============================================================================

noncomputable def H {α : Type*} [Fintype α] (P : α → ℝ) : ℝ :=
  ∑ x : α, -P x * Real.log (P x)

-- Gibbs / Max-Entropy Lemma: if P is a PMF supported on B : Finset α, then H P ≤ Real.log #B.
lemma H_le_log_card {α : Type*} [Fintype α] [DecidableEq α] (B : Finset α) (P : α → ℝ)
    (hP0 : ∀ x, 0 ≤ P x) (hP1 : ∑ x, P x = 1) (hsupp : ∀ x, x ∉ B → P x = 0)
    (hB : B.Nonempty) :
    H P ≤ Real.log (#B : ℝ) := by
  have hBpos : (0 : ℝ) < (#B : ℝ) := Nat.cast_pos.mpr hB.card_pos
  have hstep : ∀ x ∈ B, -P x * Real.log (P x) - P x * Real.log (#B : ℝ) ≤ 1 / (#B : ℝ) - P x := by
    intro x _
    rcases (hP0 x).eq_or_lt with hxz | hxp
    · rw [← hxz]; simp
    · have hle : Real.log (1 / ((#B : ℝ) * P x)) ≤ 1 / ((#B : ℝ) * P x) - 1 :=
        Real.log_le_sub_one_of_pos (div_pos one_pos (mul_pos hBpos hxp))
      rw [Real.log_div one_ne_zero (mul_pos hBpos hxp).ne', Real.log_one, zero_sub,
          Real.log_mul hBpos.ne' hxp.ne'] at hle
      have hmul := mul_le_mul_of_nonneg_left hle hxp.le
      have h1 : P x * (1 / ((#B : ℝ) * P x) - 1) = 1 / (#B : ℝ) - P x := by
        field_simp [hBpos.ne', hxp.ne']
      linarith
  have hsumB : ∑ x ∈ B, P x = 1 := by
    rw [← hP1]
    exact Finset.sum_subset (Finset.subset_univ B) fun x _ hx => hsupp x hx
  have hHB : H P = ∑ x ∈ B, -P x * Real.log (P x) := by
    unfold H
    symm
    exact Finset.sum_subset (Finset.subset_univ B) fun x _ hx => by simp [hsupp x hx]
  have htot := Finset.sum_le_sum hstep
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, Finset.sum_sub_distrib,
      Finset.sum_const, nsmul_eq_mul, hsumB] at htot
  have hcard : (#B : ℝ) * (1 / (#B : ℝ)) = 1 := by field_simp [hBpos.ne']
  rw [← hHB, one_mul, hcard] at htot
  linarith

-- Uniform distribution entropy: H (Unif B) = Real.log #B.
lemma H_unif {α : Type*} [Fintype α] [DecidableEq α] (B : Finset α) (hB : B.Nonempty) :
    H (fun x => if x ∈ B then (1 : ℝ) / (#B : ℝ) else 0) = Real.log (#B : ℝ) := by
  have hBpos : (0 : ℝ) < (#B : ℝ) := Nat.cast_pos.mpr hB.card_pos
  unfold H
  have hcongr : ∑ x ∈ B, -(if x ∈ B then (1 : ℝ) / (#B : ℝ) else 0) *
        Real.log (if x ∈ B then (1 : ℝ) / (#B : ℝ) else 0) =
      ∑ x ∈ B, -((1 : ℝ) / (#B : ℝ)) * Real.log ((1 : ℝ) / (#B : ℝ)) :=
    Finset.sum_congr rfl fun x hx => by simp [hx]
  have hsplit : ∑ x : α, -(if x ∈ B then (1 : ℝ) / (#B : ℝ) else 0) *
        Real.log (if x ∈ B then (1 : ℝ) / (#B : ℝ) else 0) =
      ∑ x ∈ B, -(if x ∈ B then (1 : ℝ) / (#B : ℝ) else 0) *
        Real.log (if x ∈ B then (1 : ℝ) / (#B : ℝ) else 0) := by
    symm; exact Finset.sum_subset (Finset.subset_univ B) fun x _ hx => by simp [hx]
  rw [hsplit, hcongr, Finset.sum_const, nsmul_eq_mul, one_div, Real.log_inv]
  field_simp [hBpos.ne']

-- Pair decomposition identity: -a log a - b log b = -(a+b) log(a+b) + (a+b) * h(a / (a+b))
lemma pair_entropy_eq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    -a * Real.log a - b * Real.log b =
      -(a + b) * Real.log (a + b) + (a + b) * h (a / (a + b)) := by
  rcases (add_nonneg ha hb).eq_or_lt with habz | habp
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    simp [ha0, hb0, h_zero]
  · unfold h
    have h1 : 1 - a / (a + b) = b / (a + b) := by field_simp [habp.ne']; ring
    rw [h1]
    have hta : a * Real.log (a / (a + b)) = a * Real.log a - a * Real.log (a + b) := by
      rcases ha.eq_or_lt with rfl | hap
      · simp
      · rw [Real.log_div hap.ne' habp.ne']; ring
    have htb : b * Real.log (b / (a + b)) = b * Real.log b - b * Real.log (a + b) := by
      rcases hb.eq_or_lt with rfl | hbp
      · simp
      · rw [Real.log_div hbp.ne' habp.ne']; ring
    have hmul : (a + b) * (-(a / (a + b)) * Real.log (a / (a + b)) -
        b / (a + b) * Real.log (b / (a + b))) =
        -a * Real.log (a / (a + b)) - b * Real.log (b / (a + b)) := by
      field_simp [habp.ne']
    rw [hmul]; linarith

-- Equivalence between (Fin (n + 1) → Bool) and Bool × (Fin n → Bool) via Fin.cons / (x 0, Fin.tail x)
def consEquiv (n : ℕ) : (Bool × (Fin n → Bool)) ≃ (Fin (n + 1) → Bool) where
  toFun p := Fin.cons p.1 p.2
  invFun x := (x 0, Fin.tail x)
  left_inv p := by ext <;> simp
  right_inv x := by funext i; refine Fin.cases ?_ ?_ i <;> simp [Fin.tail]

lemma cons_inj {n : ℕ} {a b : Bool} {u v : Fin n → Bool}
    (h : (Fin.cons a u : Fin (n + 1) → Bool) = Fin.cons b v) : a = b ∧ u = v :=
  ⟨by simpa using congrArg (fun f => f 0) h, by simpa using congrArg Fin.tail h⟩

-- 1-step chain rule for finite Shannon entropy on Fin (n + 1) → Bool!
lemma H_succ_eq {n : ℕ} (W : (Fin (n + 1) → Bool) → ℝ) (hW0 : ∀ x, 0 ≤ W x) :
    H W = H (fun x' => W (Fin.cons false x') + W (Fin.cons true x')) +
      ∑ x' : Fin n → Bool, (W (Fin.cons false x') + W (Fin.cons true x')) *
        h (W (Fin.cons true x') / (W (Fin.cons false x') + W (Fin.cons true x'))) := by
  unfold H
  rw [← Equiv.sum_comp (consEquiv n)]
  simp only [consEquiv, Equiv.coe_fn_mk, Fintype.sum_prod_type_right, Fintype.sum_bool]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x' _ => ?_
  have h1 := pair_entropy_eq (hW0 (Fin.cons true x')) (hW0 (Fin.cons false x'))
  have hadd : W (Fin.cons true x') + W (Fin.cons false x') =
      W (Fin.cons false x') + W (Fin.cons true x') := by ring
  rw [hadd] at h1
  linarith

def orVec {n : ℕ} (a b : Fin n → Bool) : Fin n → Bool := fun k => a k || b k

lemma orVec_cons {n : ℕ} (ba bb : Bool) (a b : Fin n → Bool) :
    orVec (Fin.cons ba a) (Fin.cons bb b) = Fin.cons (ba || bb) (orVec a b) := by
  funext i; refine Fin.cases ?_ ?_ i <;> simp [orVec]

-- Finite Cauchy-Schwarz: (∑ u, a u)^2 ≤ |ι| * ∑ u, (a u)^2
lemma sq_sum_le_card_mul_sum_sq {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    (∑ u : ι, a u) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ u : ι, a u ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι) (fun _ => (1 : ℝ)) a
  simpa using h

-- Helper: prove Ineq2UV for ALL 0 < v ≤ u (using checkTree_sound on v < u + continuity at u = v!)
lemma Ineq2UV_of_tree {T : BoxTree}
    (hcert : checkTree 100000000 27000000000000 100000000 27000000000000 T = true)
    (hskip : ∀ T' u1 u2 v1 v2, checkTree u1 u2 v1 v2 T' = true →
      ∀ u v : ℝ, 0 < v → v < u →
        (u1 : ℝ) / SC ≤ u → u ≤ (u2 : ℝ) / SC →
        (v1 : ℝ) / SC ≤ v → v ≤ (v2 : ℝ) / SC → Ineq2UV u v) :
    ∀ s t : ℝ, 0 ≤ s → s ≤ 1 → 0 ≤ t → t ≤ 1 →
      ((1 - t) * h s + (1 - s) * h t) / (2 * (1 - 1531 / 4000 : ℝ)) ≤
        (21 / 25 : ℝ) * h ((1 - s) * (1 - t)) + (4 / 25 : ℝ) * gfn s * gfn t := by
  -- First prove Ineq2UV u v for all 0 < v < u, then extend to v = u by continuity!
  have hstrict : ∀ u v : ℝ, 0 < v → v < u → Ineq2UV u v := by
    intro u v hv0 hvu
    by_cases htail : 27 ≤ u + v
    · exact ineq2_tail (lt_trans hv0 hvu) hv0 htail
    · by_cases hcorn : u ≤ 1 / 200
      · exact ineq2_corner hv0 hvu.le hcorn
      · by_cases hstrip : v ≤ 1 / 10000
        · exact ineq2_strip hv0 hstrip (le_of_not_ge hcorn)
        · have hu1 : (100000000 : ℝ) / SC ≤ u := by
            have : (1 / 10000 : ℝ) < v := not_le.mp hstrip
            simp only [SC]; norm_num at *; linarith
          have hu2 : u ≤ (27000000000000 : ℝ) / SC := by
            simp only [SC]; norm_num; linarith
          have hv1 : (100000000 : ℝ) / SC ≤ v := by
            have : (1 / 10000 : ℝ) < v := not_le.mp hstrip
            simp only [SC]; norm_num at *; linarith
          have hv2 : v ≤ (27000000000000 : ℝ) / SC := by
            simp only [SC]; norm_num; linarith
          exact hskip T 100000000 27000000000000 100000000 27000000000000 hcert u v hv0 hvu hu1 hu2 hv1 hv2
  -- Extend to all 0 < v ≤ u by continuity of F and Gfn!
  have hall_uv : ∀ u v : ℝ, 0 < v → v ≤ u → Ineq2UV u v := by
    intro u v hv0 hvu
    rcases hvu.eq_or_lt with rfl | hlt
    · -- Continuity as x → v⁺ of Ineq2UV x v:
      have hcont_F : ContinuousAt F v := (hasDerivAt_F hv0).continuousAt
      have hcont_F2 : ContinuousAt (fun x => F (x + v)) v :=
        ContinuousAt.comp (g := F) (f := fun x => x + v)
          (hasDerivAt_F (add_pos hv0 hv0)).continuousAt (by fun_prop)
      have hcont_G : ContinuousAt Gfn v := by
        unfold Gfn
        have hA_cont : ContinuousAt Afn v := by
          unfold Afn; fun_prop
        have hA_pos : 0 < Afn v := by linarith [Afn_ge_one v]
        have hw_cont : ContinuousAt wfn v := by
          unfold wfn
          exact (continuousAt_const.mul continuousAt_id).sub (Real.continuousAt_log hA_pos.ne' |>.comp hA_cont)
        have hFw_cont : ContinuousAt (fun x => F (wfn x)) v :=
          (hasDerivAt_F (wfn_pos hv0)).continuousAt.comp hw_cont
        exact Real.continuous_sqrt.continuousAt.comp (hA_cont.mul hFw_cont)
      have hdiff_cont : ContinuousAt (fun x =>
          ((21 / 25 : ℝ) * F (x + v) + (4 / 25 : ℝ) * Gfn x * Gfn v) -
          (2000 / 2469 : ℝ) * (F x + F v)) v :=
        ((continuousAt_const.mul hcont_F2).add ((continuousAt_const.mul hcont_G).mul continuousAt_const)).sub
          (continuousAt_const.mul (hcont_F.add continuousAt_const))
      have hev : ∀ᶠ x in nhdsWithin v (Set.Ioi v),
          0 ≤ ((21 / 25 : ℝ) * F (x + v) + (4 / 25 : ℝ) * Gfn x * Gfn v) -
            (2000 / 2469 : ℝ) * (F x + F v) := by
        filter_upwards [self_mem_nhdsWithin] with x hx
        have := hstrict x v hv0 hx
        unfold Ineq2UV at this; linarith
      have hlim : Filter.Tendsto (fun x =>
          ((21 / 25 : ℝ) * F (x + v) + (4 / 25 : ℝ) * Gfn x * Gfn v) -
          (2000 / 2469 : ℝ) * (F x + F v)) (nhdsWithin v (Set.Ioi v))
          (nhds (((21 / 25 : ℝ) * F (v + v) + (4 / 25 : ℝ) * Gfn v * Gfn v) -
            (2000 / 2469 : ℝ) * (F v + F v))) :=
        hdiff_cont.continuousWithinAt
      have hnonneg := ge_of_tendsto hlim hev
      unfold Ineq2UV; linarith
    · exact hstrict u v hv0 hlt
  -- Now transfer from (u, v) to (s, t) ∈ [0, 1]^2!
  intro s t hs0 hs1 ht0 ht1
  rcases hs1.eq_or_lt with rfl | hs1'
  · simp [h_one, gfn, pfn, f, h_zero]
  rcases ht1.eq_or_lt with rfl | ht1'
  · simp [h_one, gfn, pfn, f, h_zero]
  rcases hs0.eq_or_lt with rfl | hs0'
  · simp only [sub_zero, one_mul, h_zero, mul_zero, zero_add, h_symm]
    have hh : 0 ≤ h t := h_nonneg ht0 ht1
    have hg : 0 ≤ (4 / 25 : ℝ) * gfn 0 * gfn t :=
      mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
    have hcoef : h t / (2 * (1 - 1531 / 4000 : ℝ)) = (2000 / 2469 : ℝ) * h t := by ring
    linarith
  rcases ht0.eq_or_lt with rfl | ht0'
  · simp only [sub_zero, one_mul, mul_one, h_zero, mul_zero, add_zero, h_symm]
    have hh : 0 ≤ h s := h_nonneg hs0 hs1
    have hg : 0 ≤ (4 / 25 : ℝ) * gfn s * gfn 0 :=
      mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
    have hcoef : h s / (2 * (1 - 1531 / 4000 : ℝ)) = (2000 / 2469 : ℝ) * h s := by ring
    linarith
  -- Interior s, t ∈ (0, 1): set u = -log(1-s), v = -log(1-t) > 0!
  set u := -Real.log (1 - s)
  set v := -Real.log (1 - t)
  have h1s : 0 < 1 - s := by linarith
  have h1t : 0 < 1 - t := by linarith
  have hu0 : 0 < u := by
    have : Real.log (1 - s) < 0 := Real.log_neg h1s (by linarith)
    linarith
  have hv0 : 0 < v := by
    have : Real.log (1 - t) < 0 := Real.log_neg h1t (by linarith)
    linarith
  have hexpu : Real.exp (-u) = 1 - s := by simp [u, Real.exp_log h1s]
  have hexpv : Real.exp (-v) = 1 - t := by simp [v, Real.exp_log h1t]
  have huv_ineq : Ineq2UV u v := by
    rcases le_total v u with hvu | huv
    · exact hall_uv u v hv0 hvu
    · have := hall_uv v u hu0 huv
      unfold Ineq2UV at this ⊢
      have hcomm : (4 / 25 : ℝ) * Gfn v * Gfn u = (4 / 25 : ℝ) * Gfn u * Gfn v := by ring
      rw [add_comm v u, hcomm] at this; linarith
  unfold Ineq2UV at huv_ineq
  have hFu : F u = h s / (1 - s) := by rw [F_eq_h_div, hexpu, h_symm]
  have hFv : F v = h t / (1 - t) := by rw [F_eq_h_div, hexpv, h_symm]
  have hFuv : F (u + v) = h ((1 - s) * (1 - t)) / ((1 - s) * (1 - t)) := by
    rw [F_eq_h_div, neg_add, Real.exp_add, hexpu, hexpv]
  have hGu : Gfn u = gfn s / (1 - s) := by
    rw [Gfn_eq_g_div hu0, hexpu, sub_sub_cancel]
  have hGv : Gfn v = gfn t / (1 - t) := by
    rw [Gfn_eq_g_div hv0, hexpv, sub_sub_cancel]
  rw [hFu, hFv, hFuv, hGu, hGv] at huv_ineq
  have hmul := mul_le_mul_of_nonneg_left huv_ineq (mul_pos h1s h1t).le
  have hl : (1 - s) * (1 - t) * ((2000 / 2469 : ℝ) * (h s / (1 - s) + h t / (1 - t))) =
      ((1 - t) * h s + (1 - s) * h t) / (2 * (1 - 1531 / 4000 : ℝ)) := by
    field_simp [h1s.ne', h1t.ne']; ring
  have hr : (1 - s) * (1 - t) * ((21 / 25 : ℝ) * (h ((1 - s) * (1 - t)) / ((1 - s) * (1 - t))) +
      (4 / 25 : ℝ) * (gfn s / (1 - s)) * (gfn t / (1 - t))) =
      (21 / 25 : ℝ) * h ((1 - s) * (1 - t)) + (4 / 25 : ℝ) * gfn s * gfn t := by
    field_simp [h1s.ne', h1t.ne']
  linarith

-- Master Inductive Entropy-Coupling Theorem on Fin n → Bool!
lemma master_coupling_induction
    (hineq2 : ∀ s t : ℝ, 0 ≤ s → s ≤ 1 → 0 ≤ t → t ≤ 1 →
      ((1 - t) * h s + (1 - s) * h t) / (2 * (1 - 1531 / 4000 : ℝ)) ≤
        (21 / 25 : ℝ) * h ((1 - s) * (1 - t)) + (4 / 25 : ℝ) * gfn s * gfn t) :
    ∀ (n : ℕ) (P : (Fin n → Bool) → ℝ),
      (∀ x, 0 ≤ P x) → (∑ x, P x = 1) →
      (∀ k : Fin n, ∑ x, (if x k = true then P x else 0) ≤ 38273 / 100000) →
      ∃ Q : (Fin n → Bool) → (Fin n → Bool) → ℝ,
        (∀ u x, 0 ≤ Q u x) ∧
        (∀ u, ∑ x, Q u x = 1) ∧
        (∀ u x, P x = 0 → Q u x = 0) ∧
        (∀ x, (∑ u, Q u x) / ((2 ^ n : ℕ) : ℝ) = P x) ∧
        let P_ind : (Fin n → Bool) → ℝ := fun z => ∑ a, ∑ b, if orVec a b = z then P a * P b else 0
        let R_ex5 : (Fin n → Bool) → ℝ :=
          fun z => (∑ u, ∑ a, ∑ b, if orVec a b = z then Q u a * Q u b else 0) / ((2 ^ n : ℕ) : ℝ)
        ((1 - 38273 / 100000 : ℝ) / (1 - 1531 / 4000 : ℝ)) * H P ≤
          (21 / 25 : ℝ) * H P_ind + (4 / 25 : ℝ) * H R_ex5 := by
  intro n
  induction n with
  | zero =>
    intro P hP0 hP1 _
    refine ⟨fun _ x => P x, fun _ x => hP0 x, fun _ => hP1, fun _ _ hx => hx, fun x => ?_, ?_⟩
    · simp
    · dsimp only
      have huniq : ∀ x : Fin 0 → Bool, x = Fin.elim0 := fun x => funext fun i => Fin.elim0 i
      have hP_one : P Fin.elim0 = 1 := by
        rw [← hP1, Fintype.sum_unique]; rfl
      have hHP : H P = 0 := by
        unfold H; rw [Fintype.sum_unique]; change -P Fin.elim0 * Real.log (P Fin.elim0) = 0
        simp [hP_one]
      have hPind_one : (∑ a : Fin 0 → Bool, ∑ b : Fin 0 → Bool,
          if orVec a b = Fin.elim0 then P a * P b else 0) = 1 := by
        simp [huniq, hP_one]
      have hHind : H (fun z : Fin 0 → Bool => ∑ a, ∑ b, if orVec a b = z then P a * P b else 0) = 0 := by
        unfold H; rw [Fintype.sum_unique]
        change -(∑ a : Fin 0 → Bool, ∑ b : Fin 0 → Bool, if orVec a b = Fin.elim0 then P a * P b else 0) *
          Real.log (∑ a : Fin 0 → Bool, ∑ b : Fin 0 → Bool, if orVec a b = Fin.elim0 then P a * P b else 0) = 0
        rw [hPind_one]; simp
      have hHex5 : H (fun z : Fin 0 → Bool =>
          (∑ u : Fin 0 → Bool, ∑ a, ∑ b, if orVec a b = z then P a * P b else 0) / ((2 ^ 0 : ℕ) : ℝ)) = 0 := by
        unfold H; rw [Fintype.sum_unique]
        have h1 : (∑ u : Fin 0 → Bool, ∑ a : Fin 0 → Bool, ∑ b : Fin 0 → Bool,
            if orVec a b = Fin.elim0 then P a * P b else 0) = 1 := by
          rw [Fintype.sum_unique]; exact hPind_one
        change -((∑ u : Fin 0 → Bool, ∑ a : Fin 0 → Bool, ∑ b : Fin 0 → Bool,
            if orVec a b = Fin.elim0 then P a * P b else 0) / ((2 ^ 0 : ℕ) : ℝ)) *
          Real.log ((∑ u : Fin 0 → Bool, ∑ a : Fin 0 → Bool, ∑ b : Fin 0 → Bool,
            if orVec a b = Fin.elim0 then P a * P b else 0) / ((2 ^ 0 : ℕ) : ℝ)) = 0
        rw [h1]; simp
      rw [hHP, hHind, hHex5]; norm_num
  | succ n ih =>
    intro P hP0 hP1 hmarg
    -- Define marginal P₀ on Fin n → Bool
    let P₀ : (Fin n → Bool) → ℝ := fun x' => P (Fin.cons false x') + P (Fin.cons true x')
    have hP₀0 : ∀ x', 0 ≤ P₀ x' := fun x' => add_nonneg (hP0 _) (hP0 _)
    have hP₀1 : ∑ x', P₀ x' = 1 := by
      rw [← hP1, ← Equiv.sum_comp (consEquiv n)]
      simp [consEquiv, Fintype.sum_prod_type_right, P₀, add_comm]
    have hmarg₀ : ∀ k : Fin n, ∑ x', (if x' k = true then P₀ x' else 0) ≤ 38273 / 100000 := by
      intro k
      have hk := hmarg k.succ
      have heq : ∑ x : Fin (n + 1) → Bool, (if x k.succ = true then P x else 0) =
          ∑ x' : Fin n → Bool, (if x' k = true then P₀ x' else 0) := by
        rw [← Equiv.sum_comp (consEquiv n)]
        simp only [consEquiv, Equiv.coe_fn_mk, Fintype.sum_prod_type_right, Fintype.sum_bool,
                   Fin.cons_succ, P₀]
        refine Finset.sum_congr rfl fun x' _ => ?_
        split_ifs <;> ring
      linarith
    obtain ⟨Q₀, hQ₀0, hQ₀1, hQ₀supp, hQ₀avg, hIH⟩ := ih P₀ hP₀0 hP₀1 hmarg₀
    -- Conditional probability s(x') = P(cons true x') / P₀(x') ∈ [0, 1]
    let s : (Fin n → Bool) → ℝ := fun x' => if P₀ x' = 0 then 0 else P (Fin.cons true x') / P₀ x'
    have hs0 : ∀ x', 0 ≤ s x' := fun x' => by
      simp only [s]; split_ifs with h
      · exact le_rfl
      · exact div_nonneg (hP0 _) (hP₀0 x')
    have hs1 : ∀ x', s x' ≤ 1 := fun x' => by
      simp only [s]; split_ifs with h
      · norm_num
      · have hpos : 0 < P₀ x' := lt_of_le_of_ne (hP₀0 x') (Ne.symm h)
        rw [div_le_one hpos]; simp only [P₀]; linarith [hP0 (Fin.cons false x')]
    have hP_true : ∀ x', P (Fin.cons true x') = P₀ x' * s x' := fun x' => by
      simp only [s]; split_ifs with h
      · have : P (Fin.cons true x') = 0 := by
          have := hP0 (Fin.cons false x'); have := hP0 (Fin.cons true x'); simp only [P₀] at h; linarith
        simp [h, this]
      · field_simp [h]
    have hP_false : ∀ x', P (Fin.cons false x') = P₀ x' * (1 - s x') := fun x' => by
      have := hP_true x'; simp only [P₀] at this ⊢; linarith
    -- Lift Q₀ to Q on Fin (n + 1) → Bool using the head coin σ = u 0!
    let kStep (σ b : Bool) (r : ℝ) : ℝ :=
      match σ, b with
      | true, false  => (1 - r) + f r
      | true, true   => r - f r
      | false, false => (1 - r) - f r
      | false, true  => r + f r
    let Q : (Fin (n + 1) → Bool) → (Fin (n + 1) → Bool) → ℝ :=
      fun u x => Q₀ (Fin.tail u) (Fin.tail x) * kStep (u 0) (x 0) (s (Fin.tail x))
    have hkStep_nn : ∀ σ b r, 0 ≤ r → r ≤ 1 → 0 ≤ kStep σ b r := by
      intro σ b r hr0 hr1
      have hf := f_bounds hr0 hr1
      cases σ <;> cases b <;> simp only [kStep] <;> linarith
    have hkStep_sum : ∀ σ r, kStep σ false r + kStep σ true r = 1 := by
      intro σ r; cases σ <;> simp only [kStep] <;> ring
    have hkStep_avg_false : ∀ r, (kStep false false r + kStep true false r) / 2 = 1 - r := by
      intro r; simp only [kStep]; ring
    have hkStep_avg_true : ∀ r, (kStep false true r + kStep true true r) / 2 = r := by
      intro r; simp only [kStep]; ring
    have hkStep_or_false : ∀ r1 r2,
        (kStep false false r1 * kStep false false r2 + kStep true false r1 * kStep true false r2) / 2 =
          pfn r1 r2 := by
      intro r1 r2; simp only [kStep, pfn]; ring
    have hQ0 : ∀ u x, 0 ≤ Q u x := fun u x =>
      mul_nonneg (hQ₀0 _ _) (hkStep_nn _ _ _ (hs0 _) (hs1 _))
    have hQ1 : ∀ u, ∑ x, Q u x = 1 := by
      intro u
      rw [← Equiv.sum_comp (consEquiv n)]
      simp only [consEquiv, Equiv.coe_fn_mk, Fintype.sum_prod_type_right, Fintype.sum_bool,
                 Q, Fin.cons_zero, Fin.tail_cons]
      have : ∑ x' : Fin n → Bool,
          (Q₀ (Fin.tail u) x' * kStep (u 0) true (s x') + Q₀ (Fin.tail u) x' * kStep (u 0) false (s x')) =
          ∑ x' : Fin n → Bool, Q₀ (Fin.tail u) x' := by
        refine Finset.sum_congr rfl fun x' _ => ?_
        rw [← mul_add, add_comm (kStep (u 0) true (s x')), hkStep_sum, mul_one]
      rw [this, hQ₀1]
    have hQsupp : ∀ u x, P x = 0 → Q u x = 0 := by
      intro u x hx
      have hx_cons : x = Fin.cons (x 0) (Fin.tail x) := (consEquiv n).right_inv x |>.symm
      rw [hx_cons] at hx
      simp only [Q]
      by_cases hP0z : P₀ (Fin.tail x) = 0
      · rw [hQ₀supp _ _ hP0z, zero_mul]
      · cases hb : x 0
        · rw [hb] at hx
          have hs_one : s (Fin.tail x) = 1 := by
            have := hP_false (Fin.tail x); rw [hx] at this
            rcases mul_eq_zero.mp this.symm with h1 | h2
            · exact absurd h1 hP0z
            · linarith
          rw [hs_one]; cases u 0 <;> simp [kStep, f]
        · rw [hb] at hx
          have hs_zero : s (Fin.tail x) = 0 := by
            have := hP_true (Fin.tail x); rw [hx] at this
            rcases mul_eq_zero.mp this.symm with h1 | h2
            · exact absurd h1 hP0z
            · exact h2
          rw [hs_zero]; cases u 0 <;> simp [kStep, f]
    have hQavg : ∀ x, (∑ u, Q u x) / ((2 ^ (n + 1) : ℕ) : ℝ) = P x := by
      intro x
      have hx_cons : x = Fin.cons (x 0) (Fin.tail x) := (consEquiv n).right_inv x |>.symm
      rw [← Equiv.sum_comp (consEquiv n)]
      simp only [consEquiv, Equiv.coe_fn_mk, Fintype.sum_prod_type_right, Fintype.sum_bool,
                 Q, Fin.cons_zero, Fin.tail_cons]
      have hfac : ∑ u' : Fin n → Bool,
          (Q₀ u' (Fin.tail x) * kStep true (x 0) (s (Fin.tail x)) +
           Q₀ u' (Fin.tail x) * kStep false (x 0) (s (Fin.tail x))) =
          (∑ u' : Fin n → Bool, Q₀ u' (Fin.tail x)) *
            (kStep false (x 0) (s (Fin.tail x)) + kStep true (x 0) (s (Fin.tail x))) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun u' _ => by ring
      rw [hfac, pow_succ, Nat.cast_mul, Nat.cast_ofNat]
      have hdiv : ((∑ u', Q₀ u' (Fin.tail x)) * (kStep false (x 0) (s (Fin.tail x)) +
            kStep true (x 0) (s (Fin.tail x)))) / (((2 ^ n : ℕ) : ℝ) * 2) =
          ((∑ u', Q₀ u' (Fin.tail x)) / ((2 ^ n : ℕ) : ℝ)) *
            ((kStep false (x 0) (s (Fin.tail x)) + kStep true (x 0) (s (Fin.tail x))) / 2) := by
        ring
      rw [hdiv, hQ₀avg]
      conv_rhs => rw [hx_cons]
      cases x 0
      · rw [hkStep_avg_false, hP_false]
      · rw [hkStep_avg_true, hP_true]
    refine ⟨Q, hQ0, hQ1, hQsupp, hQavg, ?_⟩
    -- Now prove the 1-step entropy inequality!
    dsimp only
    set P_ind : (Fin (n + 1) → Bool) → ℝ := fun z => ∑ a, ∑ b, if orVec a b = z then P a * P b else 0
    set R_ex5 : (Fin (n + 1) → Bool) → ℝ :=
      fun z => (∑ u, ∑ a, ∑ b, if orVec a b = z then Q u a * Q u b else 0) / ((2 ^ (n + 1) : ℕ) : ℝ)
    set P_ind₀ : (Fin n → Bool) → ℝ := fun z' => ∑ a', ∑ b', if orVec a' b' = z' then P₀ a' * P₀ b' else 0
    set R_ex5₀ : (Fin n → Bool) → ℝ :=
      fun z' => (∑ u', ∑ a', ∑ b', if orVec a' b' = z' then Q₀ u' a' * Q₀ u' b' else 0) / ((2 ^ n : ℕ) : ℝ)
    have hP_ind0 : ∀ z, 0 ≤ P_ind z := fun z =>
      Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ =>
        by split_ifs <;> [exact mul_nonneg (hP0 a) (hP0 b); exact le_rfl]
    have hR_ex50 : ∀ z, 0 ≤ R_ex5 z := fun z =>
      div_nonneg (Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun a _ =>
        Finset.sum_nonneg fun b _ => by split_ifs <;> [exact mul_nonneg (hQ0 u a) (hQ0 u b); exact le_rfl])
        (by positivity)
    -- Step A: Chain rule on P, P_ind, R_ex5
    have hHP := H_succ_eq P hP0
    have hHPind := H_succ_eq P_ind hP_ind0
    have hHRex5 := H_succ_eq R_ex5 hR_ex50
    -- Identify the tail marginals of P_ind and R_ex5 with P_ind₀ and R_ex5₀!
    have hPind_marg : ∀ z', P_ind (Fin.cons false z') + P_ind (Fin.cons true z') = P_ind₀ z' := by
      intro z'
      simp only [P_ind, P_ind₀]
      rw [← Finset.sum_add_distrib]
      have hinner : ∀ a : Fin (n + 1) → Bool,
          (∑ b, if orVec a b = Fin.cons false z' then P a * P b else 0) +
          (∑ b, if orVec a b = Fin.cons true z' then P a * P b else 0) =
          ∑ b, if orVec (Fin.tail a) (Fin.tail b) = z' then P a * P b else 0 := by
        intro a; rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun b _ => ?_
        have hcons : orVec a b = Fin.cons (a 0 || b 0) (orVec (Fin.tail a) (Fin.tail b)) := by
          have ha := ((consEquiv n).right_inv a).symm
          have hb := ((consEquiv n).right_inv b).symm
          conv_lhs => rw [ha, hb]
          exact orVec_cons (a 0) (b 0) (Fin.tail a) (Fin.tail b)
        rw [hcons]
        by_cases ht : orVec (Fin.tail a) (Fin.tail b) = z'
        · rw [ht]; cases a 0 || b 0 <;> simp
        · have hne1 : (Fin.cons (a 0 || b 0) (orVec (Fin.tail a) (Fin.tail b)) : Fin (n + 1) → Bool) ≠ Fin.cons false z' :=
            fun h => ht (cons_inj h).2
          have hne2 : (Fin.cons (a 0 || b 0) (orVec (Fin.tail a) (Fin.tail b)) : Fin (n + 1) → Bool) ≠ Fin.cons true z' :=
            fun h => ht (cons_inj h).2
          simp [ht, hne1, hne2]
      simp_rw [hinner]
      rw [← Equiv.sum_comp (consEquiv n)]
      simp only [consEquiv, Equiv.coe_fn_mk, Fintype.sum_prod_type_right, Fintype.sum_bool, Fin.tail_cons]
      refine Finset.sum_congr rfl fun a' _ => ?_
      rw [← Equiv.sum_comp (consEquiv n), ← Equiv.sum_comp (consEquiv n)]
      simp only [consEquiv, Equiv.coe_fn_mk, Fintype.sum_prod_type_right, Fintype.sum_bool, Fin.tail_cons]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b' _ => ?_
      split_ifs
      · simp only [P₀]; ring
      · ring
    have hPind_false : ∀ z', P_ind (Fin.cons false z') =
        ∑ a', ∑ b', if orVec a' b' = z' then P₀ a' * P₀ b' * ((1 - s a') * (1 - s b')) else 0 := by
      intro z'
      simp only [P_ind]
      rw [← Equiv.sum_comp (consEquiv n)]
      simp only [consEquiv, Equiv.coe_fn_mk, Fintype.sum_prod_type_right, Fintype.sum_bool]
      refine Finset.sum_congr rfl fun a' _ => ?_
      rw [← Equiv.sum_comp (consEquiv n), ← Equiv.sum_comp (consEquiv n)]
      simp only [consEquiv, Equiv.coe_fn_mk, Fintype.sum_prod_type_right, Fintype.sum_bool, orVec_cons]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b' _ => ?_
      have hne_tf : (Fin.cons true (orVec a' b') : Fin (n + 1) → Bool) ≠ Fin.cons false z' :=
        fun h => Bool.noConfusion (cons_inj h).1
      simp only [Bool.true_or, Bool.false_or, hne_tf, ↓reduceIte, zero_add]
      have hiff : ((Fin.cons false (orVec a' b') : Fin (n + 1) → Bool) = Fin.cons false z') ↔ orVec a' b' = z' :=
        ⟨fun h => (cons_inj h).2, fun h => by rw [h]⟩
      simp only [hiff, hP_false]
      split_ifs <;> ring
    have hRex5_marg : ∀ z', R_ex5 (Fin.cons false z') + R_ex5 (Fin.cons true z') = R_ex5₀ z' := by
      intro z'
      simp only [R_ex5, R_ex5₀]
      rw [← add_div, ← Finset.sum_add_distrib]
      have hinner : ∀ u : Fin (n + 1) → Bool,
          (∑ a, ∑ b, if orVec a b = Fin.cons false z' then Q u a * Q u b else 0) +
          (∑ a, ∑ b, if orVec a b = Fin.cons true z' then Q u a * Q u b else 0) =
          ∑ a', ∑ b', if orVec a' b' = z' then Q₀ (Fin.tail u) a' * Q₀ (Fin.tail u) b' else 0 := by
        intro u
        rw [← Finset.sum_add_distrib]
        have hstep : ∀ a : Fin (n + 1) → Bool,
            (∑ b, if orVec a b = Fin.cons false z' then Q u a * Q u b else 0) +
            (∑ b, if orVec a b = Fin.cons true z' then Q u a * Q u b else 0) =
            ∑ b, if orVec (Fin.tail a) (Fin.tail b) = z' then Q u a * Q u b else 0 := by
          intro a; rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun b _ => ?_
          have hcons : orVec a b = Fin.cons (a 0 || b 0) (orVec (Fin.tail a) (Fin.tail b)) := by
            have ha := ((consEquiv n).right_inv a).symm
            have hb := ((consEquiv n).right_inv b).symm
            conv_lhs => rw [ha, hb]
            exact orVec_cons (a 0) (b 0) (Fin.tail a) (Fin.tail b)
          rw [hcons]
          by_cases ht : orVec (Fin.tail a) (Fin.tail b) = z'
          · rw [ht]; cases a 0 || b 0 <;> simp
          · have hne1 : (Fin.cons (a 0 || b 0) (orVec (Fin.tail a) (Fin.tail b)) : Fin (n + 1) → Bool) ≠ Fin.cons false z' :=
              fun h => ht (cons_inj h).2
            have hne2 : (Fin.cons (a 0 || b 0) (orVec (Fin.tail a) (Fin.tail b)) : Fin (n + 1) → Bool) ≠ Fin.cons true z' :=
              fun h => ht (cons_inj h).2
            simp [ht, hne1, hne2]
        simp_rw [hstep]
        rw [← Equiv.sum_comp (consEquiv n)]
        simp only [consEquiv, Equiv.coe_fn_mk, Fintype.sum_prod_type_right, Fintype.sum_bool, Fin.tail_cons]
        refine Finset.sum_congr rfl fun a' _ => ?_
        rw [← Equiv.sum_comp (consEquiv n), ← Equiv.sum_comp (consEquiv n)]
        simp only [consEquiv, Equiv.coe_fn_mk, Fintype.sum_prod_type_right, Fintype.sum_bool,
                   Fin.tail_cons, Q, Fin.cons_zero]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun b' _ => ?_
        split_ifs
        · calc Q₀ (Fin.tail u) a' * kStep (u 0) true (s a') * (Q₀ (Fin.tail u) b' * kStep (u 0) true (s b')) +
                Q₀ (Fin.tail u) a' * kStep (u 0) true (s a') * (Q₀ (Fin.tail u) b' * kStep (u 0) false (s b')) +
                (Q₀ (Fin.tail u) a' * kStep (u 0) false (s a') * (Q₀ (Fin.tail u) b' * kStep (u 0) true (s b')) +
                 Q₀ (Fin.tail u) a' * kStep (u 0) false (s a') * (Q₀ (Fin.tail u) b' * kStep (u 0) false (s b')))
              = Q₀ (Fin.tail u) a' * Q₀ (Fin.tail u) b' *
                  ((kStep (u 0) false (s a') + kStep (u 0) true (s a')) *
                   (kStep (u 0) false (s b') + kStep (u 0) true (s b'))) := by ring
            _ = Q₀ (Fin.tail u) a' * Q₀ (Fin.tail u) b' := by rw [hkStep_sum, hkStep_sum]; ring
        · ring
      simp_rw [hinner]
      rw [← Equiv.sum_comp (consEquiv n)]
      simp only [consEquiv, Equiv.coe_fn_mk, Fintype.sum_prod_type_right, Fintype.sum_bool,
                 Fin.tail_cons, pow_succ, Nat.cast_mul, Nat.cast_ofNat]
      have : ∀ x : ℝ, (x + x) = 2 * x := fun x => by ring
      simp_rw [this, ← Finset.mul_sum]
      field_simp
    have hRex5_false : ∀ z', R_ex5 (Fin.cons false z') =
        (∑ u', ∑ a', ∑ b', if orVec a' b' = z' then Q₀ u' a' * Q₀ u' b' * pfn (s a') (s b') else 0) /
          ((2 ^ n : ℕ) : ℝ) := by
      intro z'
      simp only [R_ex5]
      rw [← Equiv.sum_comp (consEquiv n)]
      simp only [consEquiv, Equiv.coe_fn_mk, Fintype.sum_prod_type_right, Fintype.sum_bool]
      have hinner : ∀ u : Fin (n + 1) → Bool,
          (∑ a, ∑ b, if orVec a b = Fin.cons false z' then Q u a * Q u b else 0) =
          ∑ a', ∑ b', if orVec a' b' = z' then
            Q₀ (Fin.tail u) a' * Q₀ (Fin.tail u) b' *
              (kStep (u 0) false (s a') * kStep (u 0) false (s b')) else 0 := by
        intro u
        rw [← Equiv.sum_comp (consEquiv n)]
        simp only [consEquiv, Equiv.coe_fn_mk, Fintype.sum_prod_type_right, Fintype.sum_bool]
        refine Finset.sum_congr rfl fun a' _ => ?_
        rw [← Equiv.sum_comp (consEquiv n), ← Equiv.sum_comp (consEquiv n)]
        simp only [consEquiv, Equiv.coe_fn_mk, Fintype.sum_prod_type_right, Fintype.sum_bool,
                   orVec_cons, Q, Fin.cons_zero, Fin.tail_cons]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun b' _ => ?_
        have hne : (Fin.cons true (orVec a' b') : Fin (n + 1) → Bool) ≠ Fin.cons false z' :=
          fun h => Bool.noConfusion (cons_inj h).1
        have hiff : ((Fin.cons false (orVec a' b') : Fin (n + 1) → Bool) = Fin.cons false z') ↔ orVec a' b' = z' :=
          ⟨fun h => (cons_inj h).2, fun h => by rw [h]⟩
        simp only [Bool.true_or, Bool.false_or, hne, ↓reduceIte, zero_add, hiff]
        split_ifs <;> ring
      simp_rw [hinner, Fin.cons_zero, Fin.tail_cons]
      have hcombine : ∀ u' : Fin n → Bool,
          (∑ a', ∑ b', if orVec a' b' = z' then
              Q₀ u' a' * Q₀ u' b' * (kStep true false (s a') * kStep true false (s b')) else 0) +
          (∑ a', ∑ b', if orVec a' b' = z' then
              Q₀ u' a' * Q₀ u' b' * (kStep false false (s a') * kStep false false (s b')) else 0) =
          2 * ∑ a', ∑ b', if orVec a' b' = z' then
              Q₀ u' a' * Q₀ u' b' * pfn (s a') (s b') else 0 := by
        intro u'
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a' _ => ?_
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
        refine Finset.sum_congr rfl fun b' _ => ?_
        split_ifs
        · rw [← hkStep_or_false (s a') (s b')]; ring
        · ring
      simp_rw [hcombine, ← Finset.mul_sum, pow_succ, Nat.cast_mul, Nat.cast_ofNat]
      field_simp
    -- Step B: Conditioning reduces entropy for P_ind (via sum_mul_h_le_weighted)
    have hHind_step : ∑ a', ∑ b', P₀ a' * P₀ b' * h ((1 - s a') * (1 - s b')) ≤ H P_ind - H P_ind₀ := by
      have hrew : H P_ind - H P_ind₀ =
          ∑ z' : Fin n → Bool, P_ind₀ z' * h (P_ind (Fin.cons false z') / P_ind₀ z') := by
        have h1 : (fun z' => P_ind (Fin.cons false z') + P_ind (Fin.cons true z')) = P_ind₀ :=
          funext hPind_marg
        rw [h1] at hHPind
        simp_rw [hPind_marg] at hHPind
        have hsym_each : ∀ z', P_ind₀ z' * h (P_ind (Fin.cons true z') / P_ind₀ z') =
            P_ind₀ z' * h (P_ind (Fin.cons false z') / P_ind₀ z') := by
          intro z'
          by_cases hz : P_ind₀ z' = 0
          · simp [hz]
          · have : P_ind (Fin.cons true z') / P_ind₀ z' = 1 - P_ind (Fin.cons false z') / P_ind₀ z' := by
              have := hPind_marg z'; field_simp [hz]; linarith
            rw [this, h_symm]
        simp_rw [hsym_each] at hHPind
        linarith
      rw [hrew]
      -- Partition (a', b') by z' = orVec a' b'
      have hpart : ∑ a', ∑ b', P₀ a' * P₀ b' * h ((1 - s a') * (1 - s b')) =
          ∑ z' : Fin n → Bool, ∑ p : (Fin n → Bool) × (Fin n → Bool),
            (if orVec p.1 p.2 = z' then P₀ p.1 * P₀ p.2 else 0) * h ((1 - s p.1) * (1 - s p.2)) := by
        symm
        simp only [Fintype.sum_prod_type]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a' _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b' _ => ?_
        simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
      rw [hpart]
      refine Finset.sum_le_sum fun z' _ => ?_
      have hj := sum_mul_h_le_weighted Finset.univ
        (fun p : (Fin n → Bool) × (Fin n → Bool) => if orVec p.1 p.2 = z' then P₀ p.1 * P₀ p.2 else 0)
        (fun p => (1 - s p.1) * (1 - s p.2))
        (fun p _ => by split_ifs <;> [exact mul_nonneg (hP₀0 _) (hP₀0 _); exact le_rfl])
        (fun p _ => mul_nonneg (by linarith [hs1 p.1]) (by linarith [hs1 p.2]))
        (fun p _ => by nlinarith [hs0 p.1, hs1 p.1, hs0 p.2, hs1 p.2])
      have hW : (∑ p : (Fin n → Bool) × (Fin n → Bool),
          if orVec p.1 p.2 = z' then P₀ p.1 * P₀ p.2 else 0) = P_ind₀ z' := by
        simp [Fintype.sum_prod_type, P_ind₀]
      have hN : (∑ p : (Fin n → Bool) × (Fin n → Bool),
          (if orVec p.1 p.2 = z' then P₀ p.1 * P₀ p.2 else 0) * ((1 - s p.1) * (1 - s p.2))) =
          P_ind (Fin.cons false z') := by
        rw [hPind_false]; simp only [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun b' _ => ?_
        split_ifs <;> ring
      rw [hW, hN] at hj; exact hj
    -- Step C: Conditioning reduces entropy + Inequality I + Cauchy-Schwarz for R_ex5!
    have hHex5_step : ∑ a', ∑ b', P₀ a' * P₀ b' * (gfn (s a') * gfn (s b')) ≤ H R_ex5 - H R_ex5₀ := by
      have hrew : H R_ex5 - H R_ex5₀ =
          ∑ z' : Fin n → Bool, R_ex5₀ z' * h (R_ex5 (Fin.cons false z') / R_ex5₀ z') := by
        have h1 : (fun z' => R_ex5 (Fin.cons false z') + R_ex5 (Fin.cons true z')) = R_ex5₀ :=
          funext hRex5_marg
        rw [h1] at hHRex5
        simp_rw [hRex5_marg] at hHRex5
        have hsym_each : ∀ z', R_ex5₀ z' * h (R_ex5 (Fin.cons true z') / R_ex5₀ z') =
            R_ex5₀ z' * h (R_ex5 (Fin.cons false z') / R_ex5₀ z') := by
          intro z'
          by_cases hz : R_ex5₀ z' = 0
          · simp [hz]
          · have : R_ex5 (Fin.cons true z') / R_ex5₀ z' = 1 - R_ex5 (Fin.cons false z') / R_ex5₀ z' := by
              have := hRex5_marg z'; field_simp [hz]; linarith
            rw [this, h_symm]
        simp_rw [hsym_each] at hHRex5
        linarith
      rw [hrew]
      -- First lower-bound by fiber Jensen:
      have hstep1 : (∑ u', ∑ a', ∑ b', Q₀ u' a' * Q₀ u' b' * h (pfn (s a') (s b'))) / ((2 ^ n : ℕ) : ℝ) ≤
          ∑ z', R_ex5₀ z' * h (R_ex5 (Fin.cons false z') / R_ex5₀ z') := by
        have hpart : (∑ u', ∑ a', ∑ b', Q₀ u' a' * Q₀ u' b' * h (pfn (s a') (s b'))) / ((2 ^ n : ℕ) : ℝ) =
            ∑ z' : Fin n → Bool, ∑ t : (Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool),
              (if orVec t.2.1 t.2.2 = z' then Q₀ t.1 t.2.1 * Q₀ t.1 t.2.2 / ((2 ^ n : ℕ) : ℝ) else 0) *
                h (pfn (s t.2.1) (s t.2.2)) := by
          symm
          simp only [Fintype.sum_prod_type]
          rw [Finset.sum_div, Finset.sum_comm]
          refine Finset.sum_congr rfl fun u' _ => ?_
          rw [Finset.sum_div, Finset.sum_comm]
          refine Finset.sum_congr rfl fun a' _ => ?_
          rw [Finset.sum_div, Finset.sum_comm]
          refine Finset.sum_congr rfl fun b' _ => ?_
          simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, div_mul_eq_mul_div]
        rw [hpart]
        refine Finset.sum_le_sum fun z' _ => ?_
        have hj := sum_mul_h_le_weighted Finset.univ
          (fun t : (Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool) =>
            if orVec t.2.1 t.2.2 = z' then Q₀ t.1 t.2.1 * Q₀ t.1 t.2.2 / ((2 ^ n : ℕ) : ℝ) else 0)
          (fun t => pfn (s t.2.1) (s t.2.2))
          (fun t _ => by split_ifs <;> [exact div_nonneg (mul_nonneg (hQ₀0 _ _) (hQ₀0 _ _)) (by positivity); exact le_rfl])
          (fun t _ => by rw [pfn_eq]; have := hs0 t.2.1; have := hs1 t.2.1; have := hs0 t.2.2; have := hs1 t.2.2; positivity)
          (fun t _ => by
            have hfa := f_bounds (hs0 t.2.1) (hs1 t.2.1)
            have hfb := f_bounds (hs0 t.2.2) (hs1 t.2.2)
            unfold pfn; nlinarith [hs0 t.2.1, hs1 t.2.1, hs0 t.2.2, hs1 t.2.2])
        have hW : (∑ t : (Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool),
            if orVec t.2.1 t.2.2 = z' then Q₀ t.1 t.2.1 * Q₀ t.1 t.2.2 / ((2 ^ n : ℕ) : ℝ) else 0) = R_ex5₀ z' := by
          simp only [Fintype.sum_prod_type, R_ex5₀, Finset.sum_div]
          refine Finset.sum_congr rfl fun u' _ => Finset.sum_congr rfl fun a' _ =>
            Finset.sum_congr rfl fun b' _ => by split_ifs <;> simp
        have hN : (∑ t : (Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool),
            (if orVec t.2.1 t.2.2 = z' then Q₀ t.1 t.2.1 * Q₀ t.1 t.2.2 / ((2 ^ n : ℕ) : ℝ) else 0) *
              pfn (s t.2.1) (s t.2.2)) = R_ex5 (Fin.cons false z') := by
          rw [hRex5_false]; simp only [Fintype.sum_prod_type, Finset.sum_div]
          refine Finset.sum_congr rfl fun u' _ => Finset.sum_congr rfl fun a' _ =>
            Finset.sum_congr rfl fun b' _ => by split_ifs <;> [ring; simp]
        rw [hW, hN] at hj; exact hj
      -- Next apply Inequality I (h (pfn (s a') (s b')) ≥ gfn (s a') * gfn (s b'))!
      have hstep2 : (∑ u', (∑ a', Q₀ u' a' * gfn (s a')) ^ 2) / ((2 ^ n : ℕ) : ℝ) ≤
          (∑ u', ∑ a', ∑ b', Q₀ u' a' * Q₀ u' b' * h (pfn (s a') (s b'))) / ((2 ^ n : ℕ) : ℝ) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        refine Finset.sum_le_sum fun u' _ => ?_
        have hsq_eq : (∑ a', Q₀ u' a' * gfn (s a')) ^ 2 =
            ∑ a', ∑ b', Q₀ u' a' * Q₀ u' b' * (gfn (s a') * gfn (s b')) := by
          rw [sq, Finset.sum_mul_sum]
          refine Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun b' _ => by ring
        rw [hsq_eq]
        refine Finset.sum_le_sum fun a' _ => Finset.sum_le_sum fun b' _ => ?_
        exact mul_le_mul_of_nonneg_left (ineq1_log_submod (hs0 a') (hs1 a') (hs0 b') (hs1 b'))
          (mul_nonneg (hQ₀0 _ _) (hQ₀0 _ _))
      -- Next apply Cauchy-Schwarz over u' : Fin n → Bool!
      have hstep3 : ∑ a', ∑ b', P₀ a' * P₀ b' * (gfn (s a') * gfn (s b')) ≤
          (∑ u', (∑ a', Q₀ u' a' * gfn (s a')) ^ 2) / ((2 ^ n : ℕ) : ℝ) := by
        have hcs := sq_sum_le_card_mul_sum_sq (fun u' : Fin n → Bool => ∑ a', Q₀ u' a' * gfn (s a'))
        have hcard : (Fintype.card (Fin n → Bool) : ℝ) = ((2 ^ n : ℕ) : ℝ) := by simp
        rw [hcard] at hcs
        have hsum_eq : ∑ u', ∑ a', Q₀ u' a' * gfn (s a') =
            ((2 ^ n : ℕ) : ℝ) * ∑ a', P₀ a' * gfn (s a') := by
          rw [Finset.sum_comm, Finset.mul_sum]
          refine Finset.sum_congr rfl fun a' _ => ?_
          rw [← Finset.sum_mul, ← hQ₀avg a']
          field_simp
        rw [hsum_eq] at hcs
        have h2pos : (0 : ℝ) < ((2 ^ n : ℕ) : ℝ) := by positivity
        have hdiv : (∑ a', P₀ a' * gfn (s a')) ^ 2 ≤
            (∑ u', (∑ a', Q₀ u' a' * gfn (s a')) ^ 2) / ((2 ^ n : ℕ) : ℝ) := by
          rw [le_div_iff₀ h2pos]; nlinarith
        have hsq_eq : (∑ a', P₀ a' * gfn (s a')) ^ 2 =
            ∑ a', ∑ b', P₀ a' * P₀ b' * (gfn (s a') * gfn (s b')) := by
          rw [sq, Finset.sum_mul_sum]
          refine Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun b' _ => by ring
        linarith
      linarith
    -- Step D: Combine via Inequality II and marginal bound on coordinate 0!
    have hcomb_step : ((1 - 38273 / 100000 : ℝ) / (1 - 1531 / 4000 : ℝ)) * (H P - H P₀) ≤
        (21 / 25 : ℝ) * (H P_ind - H P_ind₀) + (4 / 25 : ℝ) * (H R_ex5 - H R_ex5₀) := by
      have h1 : ∑ a', ∑ b', P₀ a' * P₀ b' *
          (((1 - s b') * h (s a') + (1 - s a') * h (s b')) / (2 * (1 - 1531 / 4000 : ℝ))) ≤
          (21 / 25 : ℝ) * (H P_ind - H P_ind₀) + (4 / 25 : ℝ) * (H R_ex5 - H R_ex5₀) := by
        have hpt : ∑ a', ∑ b', P₀ a' * P₀ b' *
            (((1 - s b') * h (s a') + (1 - s a') * h (s b')) / (2 * (1 - 1531 / 4000 : ℝ))) ≤
            ∑ a', ∑ b', P₀ a' * P₀ b' *
              ((21 / 25 : ℝ) * h ((1 - s a') * (1 - s b')) + (4 / 25 : ℝ) * gfn (s a') * gfn (s b')) :=
          Finset.sum_le_sum fun a' _ => Finset.sum_le_sum fun b' _ =>
            mul_le_mul_of_nonneg_left (hineq2 (s a') (s b') (hs0 a') (hs1 a') (hs0 b') (hs1 b'))
              (mul_nonneg (hP₀0 a') (hP₀0 b'))
        have hsplit : ∑ a', ∑ b', P₀ a' * P₀ b' *
            ((21 / 25 : ℝ) * h ((1 - s a') * (1 - s b')) + (4 / 25 : ℝ) * gfn (s a') * gfn (s b')) =
            (21 / 25 : ℝ) * (∑ a', ∑ b', P₀ a' * P₀ b' * h ((1 - s a') * (1 - s b'))) +
            (4 / 25 : ℝ) * (∑ a', ∑ b', P₀ a' * P₀ b' * (gfn (s a') * gfn (s b'))) := by
          simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun b' _ => by ring
        linarith
      -- Simplify the LHS double sum:
      have hlhs_eval : ∑ a', ∑ b', P₀ a' * P₀ b' *
          (((1 - s b') * h (s a') + (1 - s a') * h (s b')) / (2 * (1 - 1531 / 4000 : ℝ))) =
          ((1 - ∑ b', P₀ b' * s b') / (1 - 1531 / 4000 : ℝ)) * (∑ a', P₀ a' * h (s a')) := by
        have hsym_sum : ∑ a', ∑ b', P₀ a' * P₀ b' * ((1 - s b') * h (s a')) =
            (∑ b', P₀ b' * (1 - s b')) * (∑ a', P₀ a' * h (s a')) := by
          rw [Finset.sum_comm, Finset.sum_mul_sum]
          refine Finset.sum_congr rfl fun b' _ => Finset.sum_congr rfl fun a' _ => by ring
        have hsym_sum2 : ∑ a', ∑ b', P₀ a' * P₀ b' * ((1 - s a') * h (s b')) =
            (∑ a', P₀ a' * (1 - s a')) * (∑ b', P₀ b' * h (s b')) := by
          rw [Finset.sum_mul_sum]
          refine Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun b' _ => by ring
        have h1ms : ∑ b', P₀ b' * (1 - s b') = 1 - ∑ b', P₀ b' * s b' := by
          simp_rw [mul_sub, mul_one, Finset.sum_sub_distrib, hP₀1]
        have hdiv : ∑ a', ∑ b', P₀ a' * P₀ b' *
            (((1 - s b') * h (s a') + (1 - s a') * h (s b')) / (2 * (1 - 1531 / 4000 : ℝ))) =
            ((∑ a', ∑ b', P₀ a' * P₀ b' * ((1 - s b') * h (s a'))) +
             (∑ a', ∑ b', P₀ a' * P₀ b' * ((1 - s a') * h (s b')))) / (2 * (1 - 1531 / 4000 : ℝ)) := by
          simp only [← Finset.sum_add_distrib]
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl fun a' _ => ?_
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl fun b' _ => by ring
        rw [hdiv, hsym_sum, hsym_sum2, h1ms]; ring
      have hmarg0 : ∑ b', P₀ b' * s b' ≤ 38273 / 100000 := by
        have hm0 := hmarg 0
        have heq : ∑ x : Fin (n + 1) → Bool, (if x 0 = true then P x else 0) = ∑ b', P₀ b' * s b' := by
          rw [← Equiv.sum_comp (consEquiv n)]
          simp only [consEquiv, Equiv.coe_fn_mk, Fintype.sum_prod_type_right, Fintype.sum_bool,
                     Fin.cons_zero, ↓reduceIte, Bool.false_eq_true, add_zero, hP_true]
        linarith
      have hHP_diff : H P - H P₀ = ∑ a', P₀ a' * h (s a') := by
        have heq : ∑ a', P₀ a' * h (P (Fin.cons true a') / P₀ a') = ∑ a', P₀ a' * h (s a') := by
          refine Finset.sum_congr rfl fun a' _ => ?_
          by_cases h0 : P₀ a' = 0
          · simp [h0]
          · simp [s, h0]
        linarith
      have hH_nn : 0 ≤ ∑ a', P₀ a' * h (s a') :=
        Finset.sum_nonneg fun a' _ => mul_nonneg (hP₀0 a') (h_nonneg (hs0 a') (hs1 a'))
      have hrat : (1 - 38273 / 100000 : ℝ) / (1 - 1531 / 4000 : ℝ) ≤
          (1 - ∑ b', P₀ b' * s b') / (1 - 1531 / 4000 : ℝ) :=
        div_le_div_of_nonneg_right (by linarith) (by norm_num)
      rw [hlhs_eval] at h1
      rw [hHP_diff]
      exact le_trans (mul_le_mul_of_nonneg_right hrat hH_nn) h1
    -- Combine IH with hcomb_step!
    linarith

-- Final theorem (taking the rfl cert check as parameter here for fast logic test):
theorem main_from_cert {T : BoxTree}
    (hcert : checkTree 100000000 27000000000000 100000000 27000000000000 T = true)
    (hskip : ∀ T' u1 u2 v1 v2, checkTree u1 u2 v1 v2 T' = true →
      ∀ u v : ℝ, 0 < v → v < u →
        (u1 : ℝ) / SC ≤ u → u ≤ (u2 : ℝ) / SC →
        (v1 : ℝ) / SC ≤ v → v ≤ (v2 : ℝ) / SC → Ineq2UV u v) :
    (0.38272 : ℝ) < Constant6a.C6a := by
  -- 1. Show BddAbove of the defining set of C6a (upper bound 1/2 via A₀ = {∅, {0}})
  let S : Set ℝ := {c : ℝ | ∀ (A : Finset (Finset ℕ)), A ≠ {∅} →
    (∀ᵉ (X ∈ A) (Y ∈ A), X ∪ Y ∈ A) → ∃ i, c * #A ≤ #{x ∈ A | i ∈ x}}
  have hBdd : BddAbove S := by
    refine ⟨1 / 2, fun c hc => ?_⟩
    let A₀ : Finset (Finset ℕ) := {∅, {0}}
    have hne : A₀ ≠ {∅} := by
      intro heq
      have hmem : ({0} : Finset ℕ) ∈ ({∅} : Finset (Finset ℕ)) := by
        rw [← heq]; simp [A₀]
      simp at hmem
    have huc : ∀ X ∈ A₀, ∀ Y ∈ A₀, X ∪ Y ∈ A₀ := by
      intro X hX Y hY
      simp only [A₀, Finset.mem_insert, Finset.mem_singleton] at hX hY ⊢
      rcases hX with rfl | rfl <;> rcases hY with rfl | rfl <;> simp
    obtain ⟨i, hi⟩ := hc A₀ hne huc
    have hcardA : #A₀ = 2 := by
      have : (∅ : Finset ℕ) ≠ {0} := by simp
      simp [A₀, this]
    have hsub : #{x ∈ A₀ | i ∈ x} ≤ 1 := by
      have hle : {x ∈ A₀ | i ∈ x} ⊆ {{0}} := by
        intro x hx
        simp only [A₀, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
        rcases hx.1 with rfl | rfl
        · simp at hx
        · rfl
      exact le_trans (Finset.card_le_card hle) (by simp)
    rw [hcardA] at hi
    have hsubR : (#{x ∈ A₀ | i ∈ x} : ℝ) ≤ 1 := by exact_mod_cast hsub
    norm_num at hi; linarith
  -- 2. Show 38273 / 100000 ∈ S
  have hmem : (38273 / 100000 : ℝ) ∈ S := by
    intro A hne huc
    by_cases hA0 : A = ∅
    · subst hA0; exact ⟨0, by simp⟩
    have hAne : A.Nonempty := Finset.nonempty_iff_ne_empty.mpr hA0
    by_cases hA1 : #A = 1
    · obtain ⟨X, rfl⟩ := Finset.card_eq_one.mp hA1
      have hXne : X ≠ ∅ := fun h => hne (by rw [h])
      obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hXne
      refine ⟨i, ?_⟩
      have hf : {x ∈ ({X} : Finset (Finset ℕ)) | i ∈ x} = {X} := by
        ext x; simp only [Finset.mem_filter, Finset.mem_singleton, and_iff_left_iff_imp]
        rintro rfl; exact hi
      rw [hf]; norm_num
    have hA2 : 2 ≤ #A := by have := hAne.card_pos; omega
    by_contra hcon
    push Not at hcon
    -- Embed A into (Fin n → Bool) via U = A.biUnion id
    let U : Finset ℕ := A.biUnion id
    let n : ℕ := #U
    let e : Fin n ≃ U := (Finset.equivFin U).symm
    let enc : Finset ℕ → (Fin n → Bool) := fun X k => decide ((e k).1 ∈ X)
    have henc_inj : Set.InjOn enc A := by
      intro X hX Y hY heq
      ext m
      by_cases hmU : m ∈ U
      · let k := e.symm ⟨m, hmU⟩
        have hkm : (e k).1 = m := by simp [k]
        have h1 := congrFun heq k
        simp only [enc, hkm, decide_eq_decide] at h1
        exact h1
      · have hnotX : m ∉ X := fun hm => hmU (Finset.mem_biUnion.mpr ⟨X, hX, hm⟩)
        have hnotY : m ∉ Y := fun hm => hmU (Finset.mem_biUnion.mpr ⟨Y, hY, hm⟩)
        simp [hnotX, hnotY]
    let B : Finset (Fin n → Bool) := A.image enc
    have hcardB : #B = #A := Finset.card_image_of_injOn henc_inj
    have hBne : B.Nonempty := by rw [Finset.image_nonempty]; exact hAne
    have hB_or : ∀ a ∈ B, ∀ b ∈ B, orVec a b ∈ B := by
      intro a ha b hb
      obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp hb
      refine Finset.mem_image.mpr ⟨X ∪ Y, huc X hX Y hY, ?_⟩
      funext k; simp [enc, orVec, Finset.mem_union]
    let P : (Fin n → Bool) → ℝ := fun x => if x ∈ B then (1 : ℝ) / (#B : ℝ) else 0
    have hBpos : (0 : ℝ) < (#B : ℝ) := Nat.cast_pos.mpr hBne.card_pos
    have hP0 : ∀ x, 0 ≤ P x := fun x => by simp only [P]; split_ifs <;> positivity
    have hP1 : ∑ x, P x = 1 := by
      simp only [P]
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
          Finset.sum_const, nsmul_eq_mul]
      field_simp [hBpos.ne']
    have hmarg : ∀ k : Fin n, ∑ x, (if x k = true then P x else 0) ≤ 38273 / 100000 := by
      intro k
      have hk := (hcon (e k).1).le
      have hcnt : #{x ∈ B | x k = true} = #{X ∈ A | (e k).1 ∈ X} := by
        have himg : {x ∈ B | x k = true} = ({X ∈ A | (e k).1 ∈ X}).image enc := by
          ext x; simp only [B, Finset.mem_filter, Finset.mem_image]
          constructor
          · rintro ⟨⟨X, hX, rfl⟩, hxk⟩
            exact ⟨X, ⟨hX, by simpa [enc] using hxk⟩, rfl⟩
          · rintro ⟨X, ⟨hX, hXk⟩, rfl⟩
            exact ⟨⟨X, hX, rfl⟩, by simpa [enc] using hXk⟩
        rw [himg]
        exact Finset.card_image_of_injOn (henc_inj.mono (Finset.filter_subset _ _))
      have hsum_k : ∑ x : Fin n → Bool, (if x k = true then P x else 0) =
          (#{x ∈ B | x k = true} : ℝ) / (#B : ℝ) := by
        have : ∀ x : Fin n → Bool, (if x k = true then P x else 0) =
            if x ∈ {y ∈ B | y k = true} then (1 : ℝ) / (#B : ℝ) else 0 := by
          intro x; simp only [P, Finset.mem_filter]; split_ifs <;> simp_all
        simp_rw [this, ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
                 Finset.sum_const, nsmul_eq_mul, mul_one_div]
      rw [hsum_k, hcnt, hcardB, div_le_iff₀ (by rw [← hcardB]; exact hBpos)]
      linarith
    have hineq2 := Ineq2UV_of_tree hcert hskip
    obtain ⟨Q, hQ0, hQ1, hQsupp, hQavg, hmain⟩ := master_coupling_induction hineq2 n P hP0 hP1 hmarg
    dsimp only at hmain
    set P_ind : (Fin n → Bool) → ℝ := fun z => ∑ a, ∑ b, if orVec a b = z then P a * P b else 0
    set R_ex5 : (Fin n → Bool) → ℝ :=
      fun z => (∑ u, ∑ a, ∑ b, if orVec a b = z then Q u a * Q u b else 0) / ((2 ^ n : ℕ) : ℝ)
    -- Show P_ind and R_ex5 are PMFs supported on B!
    have hPind0 : ∀ z, 0 ≤ P_ind z := fun z =>
      Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => by split_ifs <;> positivity
    have hPind1 : ∑ z, P_ind z = 1 := by
      simp only [P_ind]
      rw [Finset.sum_comm]
      have : ∀ a, ∑ z, ∑ b, (if orVec a b = z then P a * P b else 0) = ∑ b, P a * P b := by
        intro a; rw [Finset.sum_comm]; simp
      simp_rw [this, ← Finset.mul_sum, hP1, mul_one, hP1]
    have hPind_supp : ∀ z, z ∉ B → P_ind z = 0 := by
      intro z hz
      apply Finset.sum_eq_zero; intro a _
      apply Finset.sum_eq_zero; intro b _
      split_ifs with hor
      · by_cases ha : a ∈ B
        · by_cases hb : b ∈ B
          · exact absurd (hor ▸ hB_or a ha b hb) hz
          · simp [P, hb]
        · simp [P, ha]
      · rfl
    have hRex50 : ∀ z, 0 ≤ R_ex5 z := fun z =>
      div_nonneg (Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun a _ =>
        Finset.sum_nonneg fun b _ => by split_ifs <;> [exact mul_nonneg (hQ0 u a) (hQ0 u b); exact le_rfl])
        (by positivity)
    have hRex51 : ∑ z, R_ex5 z = 1 := by
      simp only [R_ex5, ← Finset.sum_div]
      rw [Finset.sum_comm]
      have : ∀ u, ∑ z, ∑ a, ∑ b, (if orVec a b = z then Q u a * Q u b else 0) = 1 := by
        intro u
        rw [Finset.sum_comm]
        have h1 : ∀ a, ∑ z, ∑ b, (if orVec a b = z then Q u a * Q u b else 0) = ∑ b, Q u a * Q u b := by
          intro a; rw [Finset.sum_comm]; simp
        simp_rw [h1, ← Finset.mul_sum, hQ1 u, mul_one, hQ1 u]
      simp_rw [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      have hcard : (Fintype.card (Fin n → Bool) : ℝ) = ((2 ^ n : ℕ) : ℝ) := by simp
      rw [hcard, div_self (by positivity)]
    have hRex5_supp : ∀ z, z ∉ B → R_ex5 z = 0 := by
      intro z hz
      simp only [R_ex5]
      have hnum : ∑ u, ∑ a, ∑ b, (if orVec a b = z then Q u a * Q u b else 0) = 0 := by
        apply Finset.sum_eq_zero; intro u _
        apply Finset.sum_eq_zero; intro a _
        apply Finset.sum_eq_zero; intro b _
        split_ifs with hor
        · by_cases ha : a ∈ B
          · by_cases hb : b ∈ B
            · exact absurd (hor ▸ hB_or a ha b hb) hz
            · have : Q u b = 0 := hQsupp u b (by simp [P, hb])
              simp [this]
          · have : Q u a = 0 := hQsupp u a (by simp [P, ha])
            simp [this]
        · rfl
      rw [hnum, zero_div]
    have hHP_eq : H P = Real.log (#B : ℝ) := H_unif B hBne
    have hHP_pos : 0 < H P := by
      rw [hHP_eq]
      apply Real.log_pos
      have : (2 : ℝ) ≤ (#B : ℝ) := by rw [hcardB]; exact_mod_cast hA2
      linarith
    have h1 := H_le_log_card B P_ind hPind0 hPind1 hPind_supp hBne
    have h2 := H_le_log_card B R_ex5 hRex50 hRex51 hRex5_supp hBne
    rw [← hHP_eq] at h1 h2
    have hratio : (1 : ℝ) < (1 - 38273 / 100000 : ℝ) / (1 - 1531 / 4000 : ℝ) := by norm_num
    nlinarith
  -- 3. Conclude 0.38272 < C6a via le_csSup!
  have hle : (38273 / 100000 : ℝ) ≤ Constant6a.C6a := le_csSup hBdd hmem
  have hlt : (0.38272 : ℝ) < 38273 / 100000 := by norm_num
  exact lt_of_lt_of_le hlt hle


def certTree : BoxTree :=
(.splitU 374999999488
  (.splitV 374999999488
  (.splitU 20000000000
  (.splitV 20000000000
  (.splitU 2000000000
  (.splitV 2000000000
  .skipCorner
  .skipDiag)
  (.splitV 2000000000
  (.splitU 5000000000
  .skipCorner
  (.splitV 499999744
  (.splitU 12500000000
  (.leaf 5281062791092 5281064607131 4349298521258 4349299238967 4743072944154 4743074006729 8111865955813 8111896684520 43966187 4611383230481 4611384162670 3704348226598 3704348606252 237226178214 344123433010 70676 8517335614558 8517381706183 6908380411341 6908389627134 43628829207 88942548336)
  (.leaf 4380351465062 4380352204966 3897562689958 3897563100237 4127776060435 4127776635648 8111865955813 8111896684520 133976202 3704348226598 3704348606252 3243531375368 3243531616475 344123449213 414199975163 70676 8517335614558 8517381706183 6908380411341 6908389627134 43628829207 88942548336))
  (.leaf 5205755116228 5205756802091 3827692454186 3827692836665 4388269762265 4388270509631 6685233164123 6685239729416 102496191 4611393836428 4611394768123 3243541385504 3243541626921 237222748846 414194133684 1046611 6908380411341 6908389627134 5523949072771 5523951386740 88942536255 161639143326)))
  (.splitU 5000000000
  (.splitV 5000000000
  .skipCorner
  .skipDiag)
  (.splitV 5000000000
  (.leaf 4965342409596 4965343736610 3701353255347 3701353633299 4388269762265 4388270509631 5656740390500 5656743031665 102496191 4611393836428 4611394768123 3243541385504 3243541626921 237222748846 414194133684 7083335 5523949584543 5523951898513 4611380371980 4611381304468 161639043100 237227134093)
  (.leaf 4610165593119 4610166422483 3238809040556 3238809254911 4388269762265 4388270509631 4388269762265 4388270509631 102496191 4611393836428 4611394768123 3243541385504 3243541626921 237222748846 414194133684 102496191 4611393836428 4611394768123 3243541385504 3243541626921 237222748846 414194133684)))))
  .skipDiag)
  (.splitV 20000000000
  (.splitU 124999999488
  (.splitV 2000000000
  (.splitU 62499999744
  (.splitV 499999744
  (.leaf 3917068386972 3917068855761 2795955116997 2795955257209 3208658168614 3208658377191 8111865955813 8111896684520 1003433409 3243640887999 3243641129002 2154991417551 2154991502127 414141039421 637459294830 70676 8517335614558 8517381706183 6908380411341 6908389627134 43628829207 88942548336)
  (.leaf 3897562689958 3897563100237 2773166653045 2773166789709 3208658168614 3208658377191 6685233164123 6685239729416 1003433409 3243640887999 3243641129002 2154991417551 2154991502127 414141039421 637459294830 1046611 6908380411341 6908389627134 5523949072771 5523951386740 88942536255 161639143326))
  (.splitV 499999744
  (.leaf 2802126642293 2802126799304 2137543316469 2137543391236 2413632384124 2413632481778 8111865955813 8111896684520 4311516513 2155118960717 2155119045087 1532993893698 1532993940285 637365842036 818240658176 70676 8517335614558 8517381706183 6908380411341 6908389627134 43628829207 88942548336)
  (.leaf 2795955116997 2795955257209 2126396203933 2126396278421 2413632384124 2413632481778 6685233164123 6685239729416 4311516513 2155118960717 2155119045087 1532993893698 1532993940285 637365842036 818240658176 1046611 6908380411341 6908389627134 5523949072771 5523951386740 88942536255 161639143326)))
  (.splitU 62499999744
  (.splitV 5000000000
  (.leaf 3827692454186 3827692836665 2729187771682 2729187917914 3208658168614 3208658377191 5656740390500 5656743031665 1003433409 3243640887999 3243641129002 2154991417551 2154991502127 414141039421 637459294830 7083335 5523949584543 5523951898513 4611380371980 4611381304468 161639043100 237227134093)
  (.splitU 41249999872
  (.leaf 3701353255347 3701353633299 2823260043391 2823260187315 3501211889050 3501212199429 4388269762265 4388270509631 497653575 3243555459985 3243555697920 2545297536659 2545297659214 414186597344 546440425082 102496191 4611393836428 4611394768123 3243541385504 3243541626921 237222748846 414194133684)
  (.leaf 3096729574218 3096729782923 2535923357069 2535923466589 2984743598622 2984743784069 4388269762265 4388270509631 1301245287 2545298100511 2545298223015 2154916619218 2154916703522 546440894909 637527050189 102496191 4611393836428 4611394768123 3243541385504 3243541626921 237222748846 414194133684)))
  (.splitV 5000000000
  (.leaf 2773166653045 2773166789709 2104516729102 2104516809803 2413632384124 2413632481778 5656740390500 5656743031665 4311516513 2155118960717 2155119045087 1532993893698 1532993940285 637365842036 818240658176 7083335 5523949584543 5523951898513 4611380371980 4611381304468 161639043100 237227134093)
  (.leaf 2729187771682 2729187917914 2002645622969 2002645689645 2413632384124 2413632481778 4388269762265 4388270509631 4311516513 2155118960717 2155119045087 1532993893698 1532993940285 637365842036 818240658176 102496191 4611393836428 4611394768123 3243541385504 3243541626921 237222748846 414194133684))))
  (.splitV 2000000000
  (.splitU 250000000000
  (.splitV 499999744
  (.leaf 2140539826495 2140539909574 1506933111166 1506933154081 1766261989630 1766262048381 8111865955813 8111896684520 15517708333 1533624943060 1533624990428 971022116468 971022145619 817657637400 1044980049426 70676 8517335614558 8517381706183 6908380411341 6908389627134 43628829207 88942548336)
  (.leaf 2137543316469 2137543391236 1501681572689 1501681615403 1766261989630 1766262048381 6685233164123 6685239729416 15517708333 1533624943060 1533624990428 971022116468 971022145619 817657637400 1044980049426 1046611 6908380411341 6908389627134 5523949072771 5523951386740 88942536255 161639143326))
  (.splitV 499999744
  (.leaf 1508339525563 1508339572148 1161378672197 1161378704214 1315335090632 1315335127078 8111865955813 8111896684520 35675315692 971029529193 971029558325 683665630453 683665653522 1045125447956 1210438382949 70676 8517335614558 8517381706183 6908380411341 6908389627134 43628829207 88942548336)
  (.leaf 1506933111166 1506933154081 1158095034177 1158095066195 1315335090632 1315335127078 6685233164123 6685239729416 35675315692 971029529193 971029558325 683665630453 683665653522 1045125447956 1210438382949 1046611 6908380411341 6908389627134 5523949072771 5523951386740 88942536255 161639143326)))
  (.splitU 250000000000
  (.splitV 5000000000
  (.leaf 2126396203933 2126396278421 1491283806105 1491283851530 1766261989630 1766262048381 5656740390500 5656743031665 15517708333 1533624943060 1533624990428 971022116468 971022145619 817657637400 1044980049426 7083335 5523949584543 5523951898513 4611380371980 4611381304468 161639043100 237227134093)
  (.leaf 2104516729102 2104516809803 1441297642939 1441297683501 1766261989630 1766262048381 4388269762265 4388270509631 15517708333 1533624943060 1533624990428 971022116468 971022145619 817657637400 1044980049426 102496191 4611393836428 4611394768123 3243541385504 3243541626921 237222748846 414194133684))
  (.splitV 5000000000
  (.leaf 1501681572689 1501681615403 1151574568710 1151574602857 1315335090632 1315335127078 5656740390500 5656743031665 35675315692 971029529193 971029558325 683665630453 683665653522 1045125447956 1210438382949 7083335 5523949584543 5523951898513 4611380371980 4611381304468 161639043100 237227134093)
  (.leaf 1491283806105 1491283851530 1119876890995 1119876921952 1315335090632 1315335127078 4388269762265 4388270509631 35675315692 971029529193 971029558325 683665630453 683665653522 1045125447956 1210438382949 102496191 4611393836428 4611394768123 3243541385504 3243541626921 237222748846 414194133684)))))
  (.splitU 124999999488
  (.splitV 124999999488
  (.splitU 62499999744
  (.splitV 62499999744
  (.leaf 3238809040556 3238809254911 2141290554150 2141290629732 3208658168614 3208658377191 3208658168614 3208658377191 1003433409 3243640887999 3243641129002 2154991417551 2154991502127 414141039421 637459294830 1003433409 3243640887999 3243641129002 2154991417551 2154991502127 414141039421 637459294830)
  .skipDiag)
  (.splitV 62499999744
  (.leaf 2535923357069 2535923466589 1766261994607 1766262048381 2413632384124 2413632481778 3208658168614 3208658377191 4311516513 2155118960717 2155119045087 1532993893698 1532993940285 637365842036 818240658176 1003433409 3243640887999 3243641129002 2154991417551 2154991502127 414141039421 637459294830)
  (.leaf 2141290554150 2141290629732 1508691534835 1508691577629 2413632384124 2413632481778 2413632384124 2413632481778 4311516513 2155118960717 2155119045087 1532993893698 1532993940285 637365842036 818240658176 4311516513 2155118960717 2155119045087 1532993893698 1532993940285 637365842036 818240658176)))
  .skipDiag)
  (.splitV 124999999488
  (.splitU 250000000000
  (.splitV 62499999744
  (.leaf 2002645622969 2002645689645 1315335090632 1315335127078 1766261989630 1766262048381 3208658168614 3208658377191 15517708333 1533624943060 1533624990428 971022116468 971022145619 817657637400 1044980049426 1003433409 3243640887999 3243641129002 2154991417551 2154991502127 414141039421 637459294830)
  (.splitU 187499999744
  (.leaf 1766261994607 1766262048381 1315335090632 1315335129903 1933405913761 1933405982306 2413632384124 2413632481778 10547513393 1533000805100 1533000852679 1194636564266 1194636599590 818257325190 944388024619 4311516513 2155118960717 2155119045087 1532993893698 1532993940285 637365842036 818240658176)
  (.leaf 1508691531237 1508691577629 1162476715755 1162476747687 1627207713127 1627207764965 2413632384124 2413632481778 19042158084 1194639976498 1194640011522 970563332315 970563361533 944405824055 1045709006179 4311516513 2155118960717 2155119045087 1532993893698 1532993940285 637365842036 818240658176)))
  (.splitV 62499999744
  (.leaf 1441297642939 1441297683501 1037465984183 1037466013200 1315335090632 1315335127078 3208658168614 3208658377191 35675315692 971029529193 971029558325 683665630453 683665653522 1045125447956 1210438382949 1003433409 3243640887999 3243641129002 2154991417551 2154991502127 414141039421 637459294830)
  (.leaf 1315335090632 1315335127078 932752119116 932752145736 1315335090632 1315335127078 2413632384124 2413632481778 35675315692 971029529193 971029558325 683665630453 683665653522 1045125447956 1210438382949 4311516513 2155118960717 2155119045087 1532993893698 1532993940285 637365842036 818240658176)))
  (.splitU 250000000000
  (.splitV 250000000000
  (.splitU 187499999744
  (.splitV 187499999744
  (.leaf 1508691534835 1508691577629 1162476715755 1162476747687 1933405913761 1933405982306 1933405913761 1933405982306 10547513393 1533000805100 1533000852679 1194636564266 1194636599590 818257325190 944388024619 10547513393 1533000805100 1533000852679 1194636564266 1194636599590 818257325190 944388024619)
  .skipDiag)
  (.splitV 187499999744
  (.leaf 1315335090632 1315335129903 1037465982255 1037466013200 1627207713127 1627207764965 1933405913761 1933405982306 19042158084 1194639976498 1194640011522 970563332315 970563361533 944405824055 1045709006179 10547513393 1533000805100 1533000852679 1194636564266 1194636599590 818257325190 944388024619)
  (.leaf 1162476715755 1162476747687 932752117500 932752144130 1627207713127 1627207764965 1627207713127 1627207764965 19042158084 1194639976498 1194640011522 970563332315 970563361533 944405824055 1045709006179 19042158084 1194639976498 1194640011522 970563332315 970563361533 944405824055 1045709006179)))
  .skipDiag)
  (.splitV 250000000000
  (.splitU 312499999744
  (.splitV 187499999744
  (.leaf 1162476715755 1162476747687 932752117500 932752145736 1405842578580 1405842617907 1933405913761 1933405982306 29290253588 970564357442 970564386678 807914276557 807914302066 1045727075961 1132911888605 10547513393 1533000805100 1533000852679 1194636564266 1194636599590 818257325190 944388024619)
  (.leaf 1037465982255 1037466013200 843465127788 843465152614 1405842578580 1405842617907 1627207713127 1627207764965 29290253588 970564357442 970564386678 807914276557 807914302066 1045727075961 1132911888605 19042158084 1194639976498 1194640011522 970563332315 970563361533 944405824055 1045709006179))
  (.splitV 187499999744
  (.leaf 1037465984183 1037466013200 843465127788 843465153986 1234796952715 1234796986768 1933405913761 1933405982306 40857867512 807913761836 807913787295 683314125316 683314148407 1132929703866 1211106210695 10547513393 1533000805100 1533000852679 1194636564266 1194636599590 818257325190 944388024619)
  (.leaf 932752117500 932752145736 766280233170 766280256673 1234796952715 1234796986768 1627207713127 1627207764965 40857867512 807913761836 807913787295 683314125316 683314148407 1132929703866 1211106210695 19042158084 1194639976498 1194640011522 970563332315 970563361533 944405824055 1045709006179)))
  (.splitU 312499999744
  (.splitV 312499999744
  (.splitU 281249999872
  (.splitV 281249999872
  (.leaf 932752117500 932752144130 843465127788 843465152614 1455544089863 1455544130940 1455544089863 1455544130940 26383289474 970448580834 970448610071 883286901097 883286928233 1045884471295 1090850885597 26383289474 970448580834 970448610071 883286901097 883286928233 1045884471295 1090850885597)
  .skipDiag)
  (.splitV 281249999872
  (.leaf 886415640412 886415666208 803525698915 803525723141 1359211996210 1359212034060 1455544089863 1455544130940 31881939795 883286924478 883286951582 807813726045 807813751503 1090853131843 1133078855808 26383289474 970448580834 970448610071 883286901097 883286928233 1045884471295 1090850885597)
  (.leaf 843465127788 843465152614 766280233170 766280256673 1359211996210 1359212034060 1359211996210 1359212034060 31881939795 883286924478 883286951582 807813726045 807813751503 1090853131843 1133078855808 31881939795 883286924478 883286951582 807813726045 807813751503 1090853131843 1133078855808)))
  .skipDiag)
  (.splitV 312499999744
  (.splitU 343749999616
  (.splitV 281249999872
  (.leaf 843465127788 843465152614 766280233170 766280256673 1273941065386 1273941100643 1455544089863 1455544130940 37684149887 807813662220 807813687786 741698001813 741698026034 1133081080484 1173086782699 26383289474 970448580834 970448610071 883286901097 883286928233 1045884471295 1090850885597)
  (.leaf 803525698915 803525723141 731458082421 731458105270 1273941065386 1273941100643 1359211996210 1359212034060 37684149887 807813662220 807813687786 741698001813 741698026034 1133081080484 1173086782699 31881939795 883286924478 883286951582 807813726045 807813751503 1090853131843 1133078855808))
  (.splitV 281249999872
  (.leaf 803525698915 803525723141 731458082421 731458105270 1197700865531 1197700898529 1455544089863 1455544130940 43744100135 741697872276 741697896484 683226857757 683226880843 1173088974700 1211264769367 26383289474 970448580834 970448610071 883286901097 883286928233 1045884471295 1090850885597)
  (.leaf 766280233170 766280256673 698826423419 698826445811 1197700865531 1197700898529 1359211996210 1359212034060 43744100135 741697872276 741697896484 683226857757 683226880843 1173088974700 1211264769367 31881939795 883286924478 883286951582 807813726045 807813751503 1090853131843 1133078855808)))
  (.splitU 343749999616
  (.splitV 343749999616
  (.leaf 766280233170 766280256673 698826423419 698826445811 1273941065386 1273941100643 1273941065386 1273941100643 37684149887 807813662220 807813687786 741698001813 741698026034 1133081080484 1173086782699 37684149887 807813662220 807813687786 741698001813 741698026034 1133081080484 1173086782699)
  .skipDiag)
  (.splitV 343749999616
  (.splitU 359374999552
  (.splitV 328124999680
  (.leaf 731458082421 731458105270 698826423419 698826445811 1216004462639 1216004498626 1294343074013 1294343112321 42164726914 741674600479 741674624723 711573265010 711573288672 1173126782225 1192423247523 36162112600 807788608360 807788633829 773680686178 773680711000 1133119844817 1153373660955)
  (.leaf 714881708996 714881731678 683267926565 683267948616 1216004462639 1216004498626 1254101045534 1254101082715 42164726914 741674600479 741674624723 711573265010 711573288672 1173126782225 1192423247523 39132611948 773680674177 773680699000 741674616340 741674640584 1153373937042 1173126508254))
  (.splitV 328124999680
  (.leaf 714881708996 714881731678 683267926565 683267948616 1179864918859 1179864953574 1294343074013 1294343112321 45253218143 711573245826 711573269414 683205116610 683205139696 1192423518993 1211303416291 36162112600 807788608360 807788633829 773680686178 773680711000 1133119844817 1153373660955)
  (.leaf 698826423419 698826445811 668183524844 668183546743 1179864918859 1179864953574 1254101045534 1254101082715 45253218143 711573245826 711573269414 683205116610 683205139696 1192423518993 1211303416291 39132611948 773680674177 773680699000 741674616340 741674640584 1153373937042 1173126508254)))
  (.splitU 359374999552
  (.splitV 359374999552
  (.leaf 698826423419 698826445811 668183524844 668183546743 1216004462639 1216004498626 1216004462639 1216004498626 42164726914 741674600479 741674624723 711573265010 711573288672 1173126782225 1192423247523 42164726914 741674600479 741674624723 711573265010 711573288672 1173126782225 1192423247523)
  .skipDiag)
  (.splitV 359374999552
  (.leaf 683267926565 683267948616 653551996726 653552018250 1179864918859 1179864953574 1216004462639 1216004498626 45253218143 711573245826 711573269414 683205116610 683205139696 1192423518993 1211303416291 42164726914 741674600479 741674624723 711573265010 711573288672 1173126782225 1192423247523)
  (.leaf 668183524844 668183546743 639353455536 639353476836 1179864918859 1179864953574 1179864918859 1179864953574 45253218143 711573245826 711573269414 683205116610 683205139696 1192423518993 1211303416291 45253218143 711573245826 711573269414 683205116610 683205139696 1192423518993 1211303416291)))))))))))))
  .skipDiag)
  (.splitV 374999999488
  (.splitU 2000000000000
  (.splitV 20000000000
  (.splitU 750000000000
  (.splitV 2000000000
  (.splitU 500000000000
  (.splitV 499999744
  (.leaf 1162256962013 1162256996376 931981859093 931981885601 1037465982255 1037466013200 8111865955813 8111896684520 60459659386 683653952159 683653975223 504175676806 504175696822 1210576667141 1350041340786 70676 8517335614558 8517381706183 6908380411341 6908389627134 43628829207 88942548336)
  (.leaf 1161378672197 1161378704214 929676942138 929676968813 1037465982255 1037466013200 6685233164123 6685239729416 60459659386 683653952159 683653975223 504175676806 504175696822 1210576667141 1350041340786 1046611 6908380411341 6908389627134 5523949072771 5523951386740 88942536255 161639143326))
  (.splitV 499999744
  (.leaf 932597985067 932598013329 638906039282 638906060711 766280231952 766280256673 8111865955813 8111896684520 102578890908 505111942226 505111962339 293200552885 293200569942 1348435254541 1590541845134 70676 8517335614558 8517381706183 6908380411341 6908389627134 43628829207 88942548336)
  (.leaf 931981859093 931981885601 637566331280 637566352614 766280231952 766280256673 6685233164123 6685239729416 102578890908 505111942226 505111962339 293200552885 293200569942 1348435254541 1590541845134 1046611 6908380411341 6908389627134 5523949072771 5523951386740 88942536255 161639143326)))
  (.splitU 500000000000
  (.splitV 5000000000
  (.leaf 1158095034177 1158095066195 925093287180 925093315231 1037465982255 1037466013200 5656740390500 5656743031665 60459659386 683653952159 683653975223 504175676806 504175696822 1210576667141 1350041340786 7083335 5523949584543 5523951898513 4611380371980 4611381304468 161639043100 237227134093)
  (.leaf 1151574568710 1151574602857 902685067678 902685093793 1037465982255 1037466013200 4388269762265 4388270509631 60459659386 683653952159 683653975223 504175676806 504175696822 1210576667141 1350041340786 102496191 4611393836428 4611394768123 3243541385504 3243541626921 237222748846 414194133684))
  (.splitV 5000000000
  (.leaf 929676942138 929676968813 634898290468 634898312696 766280231952 766280256673 5656740390500 5656743031665 102578890908 505111942226 505111962339 293200552885 293200569942 1348435254541 1590541845134 7083335 5523949584543 5523951898513 4611380371980 4611381304468 161639043100 237227134093)
  (.leaf 925093287180 925093315231 621781510534 621781531638 766280231952 766280256673 4388269762265 4388270509631 102578890908 505111942226 505111962339 293200552885 293200569942 1348435254541 1590541845134 102496191 4611393836428 4611394768123 3243541385504 3243541626921 237222748846 414194133684))))
  (.splitV 2000000000
  (.splitU 1000000000000
  (.splitV 499999744
  (.leaf 639263936932 639263959114 458384263423 458384282235 539331438262 539331458893 8111865955813 8111896684520 155254286692 293090693463 293090710654 176913054527 176913070288 1591282774688 1806909857753 70676 8517335614558 8517381706183 6908380411341 6908389627134 43628829207 88942548336)
  (.leaf 638906039282 638906060711 457513021451 457513040172 539331438262 539331458893 6685233164123 6685239729416 155254286692 293090693463 293090710654 176913054527 176913070288 1591282774688 1806909857753 1046611 6908380411341 6908389627134 5523949072771 5523951386740 88942536255 161639143326))
  (.splitV 499999744
  (.leaf 458616942388 458616961733 145335214089 145335229396 252482450896 252482467287 8111865955813 8111896684520 263768687118 180389396859 180389412682 25780844024 25780858270 1796494543218 2516701902163 70676 8517335614558 8517381706183 6908380411341 6908389627134 43628829207 88942548336)
  (.leaf 458384263423 458384282235 145100776725 145100792005 252482450896 252482467287 6685233164123 6685239729416 263768687118 180389396859 180389412682 25780844024 25780858270 1796494543218 2516701902163 1046611 6908380411341 6908389627134 5523949072771 5523951386740 88942536255 161639143326)))
  (.splitU 1000000000000
  (.splitV 5000000000
  (.leaf 637566331280 637566352614 455776719728 455776739071 539331438262 539331458893 5656740390500 5656743031665 155254286692 293090693463 293090710654 176913054527 176913070288 1591282774688 1806909857753 7083335 5523949584543 5523951898513 4611380371980 4611381304468 161639043100 237227134093)
  (.leaf 634898290468 634898312696 447217120284 447217138576 539331438262 539331458893 4388269762265 4388270509631 155254286692 293090693463 293090710654 176913054527 176913070288 1591282774688 1806909857753 102496191 4611393836428 4611394768123 3243541385504 3243541626921 237222748846 414194133684))
  (.splitV 5000000000
  (.leaf 457513021451 457513040172 144633119621 144633135072 252482450896 252482467287 5656740390500 5656743031665 263768687118 180389396859 180389412682 25780844024 25780858270 1796494543218 2516701902163 7083335 5523949584543 5523951898513 4611380371980 4611381304468 161639043100 237227134093)
  (.leaf 455776719728 455776739071 142318986089 142319001350 252482450896 252482467287 4388269762265 4388270509631 263768687118 180389396859 180389412682 25780844024 25780858270 1796494543218 2516701902163 102496191 4611393836428 4611394768123 3243541385504 3243541626921 237222748846 414194133684)))))
  (.splitU 750000000000
  (.splitV 124999999488
  (.splitU 500000000000
  (.splitV 62499999744
  (.leaf 1119876890995 1119876921952 843465127788 843465152614 1037465982255 1037466013200 3208658168614 3208658377191 60459659386 683653952159 683653975223 504175676806 504175696822 1210576667141 1350041340786 1003433409 3243640887999 3243641129002 2154991417551 2154991502127 414141039421 637459294830)
  (.leaf 1037465984183 1037466013200 766280233170 766280256673 1037465982255 1037466013200 2413632384124 2413632481778 60459659386 683653952159 683653975223 504175676806 504175696822 1210576667141 1350041340786 4311516513 2155118960717 2155119045087 1532993893698 1532993940285 637365842036 818240658176))
  (.splitV 62499999744
  (.leaf 902685067678 902685093793 586532600084 586532620659 766280231952 766280256673 3208658168614 3208658377191 102578890908 505111942226 505111962339 293200552885 293200569942 1348435254541 1590541845134 1003433409 3243640887999 3243641129002 2154991417551 2154991502127 414141039421 637459294830)
  (.leaf 843465127788 843465152614 539331439010 539331458893 766280231952 766280256673 2413632384124 2413632481778 102578890908 505111942226 505111962339 293200552885 293200569942 1348435254541 1590541845134 4311516513 2155118960717 2155119045087 1532993893698 1532993940285 637365842036 818240658176)))
  (.splitU 500000000000
  (.splitV 250000000000
  (.splitU 437499999744
  (.splitV 187499999744
  (.leaf 932752119116 932752145736 766280233170 766280256673 1097044335184 1097044367693 1933405913761 1933405982306 53377523064 683312682550 683312705505 584411211242 584411232619 1211123435915 1283111568058 10547513393 1533000805100 1533000852679 1194636564266 1194636599590 818257325190 944388024619)
  (.leaf 843465127788 843465153986 698826422387 698826445811 1097044335184 1097044367693 1627207713127 1627207764965 53377523064 683312682550 683312705505 584411211242 584411232619 1211123435915 1283111568058 19042158084 1194639976498 1194640011522 970563332315 970563361533 944405824055 1045709006179))
  (.splitV 187499999744
  (.leaf 843465127788 843465153986 698826422387 698826445811 982922120811 982922150241 1933405913761 1933405982306 66541974179 584409270745 584409292101 503914363419 503914383506 1283127990100 1350627379719 10547513393 1533000805100 1533000852679 1194636564266 1194636599590 818257325190 944388024619)
  (.leaf 766280233170 766280256673 639353454590 639353475890 982922120811 982922150241 1627207713127 1627207764965 66541974179 584409270745 584409292101 503914363419 503914383506 1283127990100 1350627379719 19042158084 1194639976498 1194640011522 970563332315 970563361533 944405824055 1045709006179)))
  (.splitU 437499999744
  (.splitV 312499999744
  (.splitU 406249999616
  (.splitV 281249999872
  (.leaf 766280233170 766280256673 698826422387 698826445811 1128969978008 1128970011402 1455544089863 1455544130940 50019842544 683226677870 683226700959 631106277552 631106299568 1211266920577 1247911665624 26383289474 970448580834 970448610071 883286901097 883286928233 1045884471295 1090850885597)
  (.leaf 731458082421 731458105270 668183523875 668183546743 1128969978008 1128970011402 1359211996210 1359212034060 50019842544 683226677870 683226700959 631106277552 631106299568 1211266920577 1247911665624 31881939795 883286924478 883286951582 807813726045 807813751503 1090853131843 1133078855808))
  (.splitV 281249999872
  (.leaf 731458081290 731458105270 668183523875 668183546743 1066578899071 1066578930138 1455544089863 1455544130940 56473091803 631106061267 631106083430 584336011371 584336032717 1247913769391 1283260593118 26383289474 970448580834 970448610071 883286901097 883286928233 1045884471295 1090850885597)
  (.leaf 698826422387 698826445811 639353454590 639353476836 1066578899071 1066578930138 1359211996210 1359212034060 56473091803 631106061267 631106083430 584336011371 584336032717 1247913769391 1283260593118 31881939795 883286924478 883286951582 807813726045 807813751503 1090853131843 1133078855808)))
  (.splitU 406249999616
  (.splitV 343749999616
  (.splitU 390624999552
  (.splitV 328124999680
  (.leaf 698826423419 698826445811 668183523875 668183546743 1145517582932 1145517616784 1294343074013 1294343112321 48393077888 683205095590 683205118617 656420079846 656420102307 1211303684948 1229801807562 36162112600 807788608360 807788633829 773680686178 773680711000 1133119844817 1153373660955)
  (.leaf 683267926565 683267948616 653551995786 653552018250 1145517582932 1145517616784 1254101045534 1254101082715 48393077888 683205095590 683205118617 656420079846 656420102307 1211303684948 1229801807562 39132611948 773680674177 773680699000 741674616340 741674640584 1153373937042 1173126508254))
  (.splitV 328124999680
  (.leaf 683267925536 683267948616 653551995786 653552018250 1112817412732 1112817445724 1294343074013 1294343112321 51579524321 656420055218 656420077622 631086100139 631086122303 1229802073578 1247949167354 36162112600 807788608360 807788633829 773680686178 773680711000 1133119844817 1153373660955)
  (.leaf 668183523875 668183546743 639353454590 639353476836 1112817412732 1112817445724 1254101045534 1254101082715 51579524321 656420055218 656420077622 631086100139 631086122303 1229802073578 1247949167354 39132611948 773680674177 773680699000 741674616340 741674640584 1153373937042 1173126508254)))
  (.splitU 390624999552
  (.splitV 359374999552
  (.leaf 668183524844 668183546743 639353454590 639353476836 1145517582932 1145517616784 1216004462639 1216004498626 48393077888 683205095590 683205118617 656420079846 656420102307 1211303684948 1229801807562 42164726914 741674600479 741674624723 711573265010 711573288672 1173126782225 1192423247523)
  (.leaf 653551996726 653552018250 625569251107 625569273146 1145517582932 1145517616784 1179864918859 1179864953574 48393077888 683205095590 683205118617 656420079846 656420102307 1211303684948 1229801807562 45253218143 711573245826 711573269414 683205116610 683205139696 1192423518993 1211303416291))
  (.splitV 359374999552
  (.leaf 653551995786 653552018250 625569251107 625569273146 1112817412732 1112817445724 1216004462639 1216004498626 51579524321 656420055218 656420077622 631086100139 631086122303 1229802073578 1247949167354 42164726914 741674600479 741674624723 711573265010 711573288672 1173126782225 1192423247523)
  (.leaf 639353454590 639353476836 612181863829 612181885653 1112817412732 1112817445724 1179864918859 1179864953574 51579524321 656420055218 656420077622 631086100139 631086122303 1229802073578 1247949167354 45253218143 711573245826 711573269414 683205116610 683205139696 1192423518993 1211303416291))))
  (.splitV 343749999616
  (.leaf 668183523875 668183546743 612181863829 612181885653 1066578899071 1066578930138 1273941065386 1273941100643 56473091803 631106061267 631106083430 584336011371 584336032717 1247913769391 1283260593118 37684149887 807813662220 807813687786 741698001813 741698026034 1133081080484 1173086782699)
  (.splitU 421874999680
  (.splitV 359374999552
  (.leaf 639353454590 639353476836 612181863829 612181885653 1081636107783 1081636139888 1216004462639 1216004498626 54807994914 631086073192 631086095355 607086416910 607086438666 1247949430142 1265772771916 42164726914 741674600479 741674624723 711573265010 711573288672 1173126782225 1192423247523)
  (.leaf 625569251107 625569273146 599174819208 599174840827 1081636107783 1081636139888 1179864918859 1179864953574 54807994914 631086073192 631086095355 607086416910 607086438666 1247949430142 1265772771916 45253218143 711573245826 711573269414 683205116610 683205139696 1192423518993 1211303416291))
  (.splitV 359374999552
  (.leaf 625569251107 625569273146 599174819208 599174840827 1051859644682 1051859675947 1216004462639 1216004498626 58074137753 607086387958 607086409611 584317315408 584317336623 1265773031795 1283296904879 42164726914 741674600479 741674624723 711573265010 711573288672 1173126782225 1192423247523)
  (.leaf 612181863829 612181885653 586532600084 586532621499 1051859644682 1051859675947 1179864918859 1179864953574 58074137753 607086387958 607086409611 584317315408 584317336623 1265773031795 1283296904879 45253218143 711573245826 711573269414 683205116610 683205139696 1192423518993 1211303416291))))))
  (.splitV 312499999744
  (.leaf 698826422387 698826445811 586532600084 586532620659 982922120811 982922150241 1405842578580 1405842617907 66541974179 584409270745 584409292101 503914363419 503914383506 1283127990100 1350627379719 29290253588 970564357442 970564386678 807914276557 807914302066 1045727075961 1132911888605)
  (.splitU 468749999872
  (.splitV 343749999616
  (.leaf 639353454590 639353476836 586532600084 586532621499 1009609235594 1009609265794 1273941065386 1273941100643 63069009777 584335769227 584335790468 542127777728 542127798312 1283262644384 1317496154971 37684149887 807813662220 807813687786 741698001813 741698026034 1133081080484 1173086782699)
  (.leaf 612181863829 612181885653 562284959073 562284979574 1009609235594 1009609265794 1197700865531 1197700898529 63069009777 584335769227 584335790468 542127777728 542127798312 1283262644384 1317496154971 43744100135 741697872276 741697896484 683226857757 683226880843 1173088974700 1211264769367))
  (.splitV 343749999616
  (.leaf 612181863829 612181885653 562284959073 562284978809 957326611614 957326640430 1273941065386 1273941100643 69775985922 542127518141 542127538806 503849949343 503849969435 1317498149647 1350766395741 37684149887 807813662220 807813687786 741698001813 741698026034 1133081080484 1173086782699)
  (.leaf 586532600084 586532621499 539331439010 539331458893 957326611614 957326640430 1197700865531 1197700898529 69775985922 542127518141 542127538806 503849949343 503849969435 1317498149647 1350766395741 43744100135 741697872276 741697896484 683226857757 683226880843 1173088974700 1211264769367))))))
  (.splitV 250000000000
  (.splitU 625000000000
  (.splitV 187499999744
  (.leaf 766280233170 766280256673 586532600084 586532620659 843465126398 843465152614 1933405913761 1933405982306 87382433134 504158491206 504158511210 381257570110 381257588378 1350165589445 1475672519567 10547513393 1533000805100 1533000852679 1194636564266 1194636599590 818257325190 944388024619)
  (.leaf 698826422387 698826445811 539331438262 539331458893 843465126398 843465152614 1627207713127 1627207764965 87382433134 504158491206 504158511210 381257570110 381257588378 1350165589445 1475672519567 19042158084 1194639976498 1194640011522 970563332315 970563361533 944405824055 1045709006179))
  (.splitV 187499999744
  (.leaf 639353454590 639353476836 496931957994 496931977894 698826422387 698826445811 1933405913761 1933405982306 114756607340 381241002812 381241021137 292631464609 292631481794 1475780478851 1592435847195 10547513393 1533000805100 1533000852679 1194636564266 1194636599590 818257325190 944388024619)
  (.leaf 586532600084 586532620659 458675136391 458675155125 698826422387 698826445811 1627207713127 1627207764965 114756607340 381241002812 381241021137 292631464609 292631481794 1475780478851 1592435847195 19042158084 1194639976498 1194640011522 970563332315 970563361533 944405824055 1045709006179)))
  (.splitU 625000000000
  (.splitU 562500000000
  (.splitV 312499999744
  (.leaf 639353454590 639353475890 539331438262 539331458893 886415638929 886415666208 1405842578580 1405842617907 80097384626 503912216204 503912236200 437177449532 437177468648 1350642869508 1414740221722 29290253588 970564357442 970564386678 807914276557 807914302066 1045727075961 1132911888605)
  (.leaf 586532600084 586532620659 496931957994 496931977894 886415638929 886415666208 1234796952715 1234796986768 80097384626 503912216204 503912236200 437177449532 437177468648 1350642869508 1414740221722 40857867512 807913761836 807913787295 683314125316 683314148407 1132929703866 1211106210695))
  (.splitV 312499999744
  (.leaf 586532599266 586532620659 496931957994 496931977894 803525697707 803525723141 1405842578580 1405842617907 93836461052 437175281889 437175300988 381067545176 381067563374 1414754711061 1476174890436 29290253588 970564357442 970564386678 807914276557 807914302066 1045727075961 1132911888605)
  (.leaf 539331438262 539331458893 458675136391 458675155719 803525697707 803525723141 1234796952715 1234796986768 93836461052 437175281889 437175300988 381067545176 381067563374 1414754711061 1476174890436 40857867512 807913761836 807913787295 683314125316 683314148407 1132929703866 1211106210695)))
  (.leaf 539331438262 539331458893 392527848815 392527866802 698826422387 698826445811 1315335090632 1315335127078 114756607340 381241002812 381241021137 292631464609 292631481794 1475780478851 1592435847195 35675315692 971029529193 971029558325 683665630453 683665653522 1045125447956 1210438382949)))))
  (.splitV 124999999488
  (.splitU 1000000000000
  (.splitV 62499999744
  (.leaf 621781510534 621781531638 424022353666 424022372029 539331438262 539331458893 3208658168614 3208658377191 155254286692 293090693463 293090710654 176913054527 176913070288 1591282774688 1806909857753 1003433409 3243640887999 3243641129002 2154991417551 2154991502127 414141039421 637459294830)
  (.leaf 586532600084 586532620659 392527848815 392527866802 539331438262 539331458893 2413632384124 2413632481778 155254286692 293090693463 293090710654 176913054527 176913070288 1591282774688 1806909857753 4311516513 2155118960717 2155119045087 1532993893698 1532993940285 637365842036 818240658176))
  (.splitV 62499999744
  (.leaf 447217120284 447217138576 135975206390 135975221586 252482450896 252482467287 3208658168614 3208658377191 263768687118 180389396859 180389412682 25780844024 25780858270 1796494543218 2516701902163 1003433409 3243640887999 3243641129002 2154991417551 2154991502127 414141039421 637459294830)
  (.leaf 424022353666 424022372029 127189217173 127189232309 252482450896 252482467287 2413632384124 2413632481778 263768687118 180389396859 180389412682 25780844024 25780858270 1796494543218 2516701902163 4311516513 2155118960717 2155119045087 1532993893698 1532993940285 637365842036 818240658176)))
  (.splitU 1000000000000
  (.splitV 250000000000
  (.leaf 539331439010 539331458893 337579556670 337579574001 539331438262 539331458893 1766261989630 1766262048381 155254286692 293090693463 293090710654 176913054527 176913070288 1591282774688 1806909857753 15517708333 1533624943060 1533624990428 971022116468 971022145619 817657637400 1044980049426)
  (.leaf 458675136391 458675155125 291475377714 291475394526 539331438262 539331458893 1315335090632 1315335127078 155254286692 293090693463 293090710654 176913054527 176913070288 1591282774688 1806909857753 35675315692 971029529193 971029558325 683665630453 683665653522 1045125447956 1210438382949))
  (.splitV 250000000000
  (.leaf 392527848815 392527866802 111377713640 111377728629 252482450896 252482467287 1766261989630 1766262048381 263768687118 180389396859 180389412682 25780844024 25780858270 1796494543218 2516701902163 15517708333 1533624943060 1533624990428 971022116468 971022145619 817657637400 1044980049426)
  (.leaf 337579556670 337579574001 97628796492 97628811352 252482450896 252482467287 1315335090632 1315335127078 263768687118 180389396859 180389412682 25780844024 25780858270 1796494543218 2516701902163 35675315692 971029529193 971029558325 683665630453 683665653522 1045125447956 1210438382949))))))
  (.splitV 20000000000
  (.splitU 8000000000000
  (.splitV 2000000000
  (.splitU 4000000000000
  (.splitV 499999744
  (.leaf 145397799328 145397814753 18476113442 18476127593 51069173788 51069188223 8111865955813 8111896684520 386768110831 27334766310 27334780572 493988126 494002132 2505387385733 3558889880531 70676 8517335614558 8517381706183 6908380411341 6908389627134 43628829207 88942548336)
  (.leaf 145335214089 145335229396 18448162993 18448177144 51069173788 51069188223 6685233164123 6685239729416 386768110831 27334766310 27334780572 493988126 494002132 2505387385733 3558889880531 1046611 6908380411341 6908389627134 5523949072771 5523951386740 88942536255 161639143326))
  (.splitV 499999744
  (.leaf 18483574107 18483588283 0 0 2481822359 2481836382 8111865955813 8111896684520 398555499782 499846956 499860963 0 0 3558433204993 4972855634660 70676 8517335614558 8517381706183 6908380411341 6908389627134 43628829207 88942548336)
  (.leaf 18476113442 18476127593 0 0 2481822359 2481836382 6685233164123 6685239729416 398555499782 499846956 499860963 0 0 3558433204993 4972855634660 1046611 6908380411341 6908389627134 5523949072771 5523951386740 88942536255 161639143326)))
  (.splitU 4000000000000
  (.splitV 5000000000
  (.leaf 145100776725 145100792005 18392390076 18392404251 51069173788 51069188223 5656740390500 5656743031665 386768110831 27334766310 27334780572 493988126 494002132 2505387385733 3558889880531 7083335 5523949584543 5523951898513 4611380371980 4611381304468 161639043100 237227134093)
  (.leaf 144633119621 144633135072 18116067491 18116081646 51069173788 51069188223 4388269762265 4388270509631 386768110831 27334766310 27334780572 493988126 494002132 2505387385733 3558889880531 102496191 4611393836428 4611394768123 3243541385504 3243541626921 237222748846 414194133684))
  (.splitV 5000000000
  (.leaf 18448162993 18448177144 0 0 2481822359 2481836382 5656740390500 5656743031665 398555499782 499846956 499860963 0 0 3558433204993 4972855634660 7083335 5523949584543 5523951898513 4611380371980 4611381304468 161639043100 237227134093)
  (.leaf 18392390076 18392404251 0 0 2481822359 2481836382 4388269762265 4388270509631 398555499782 499846956 499860963 0 0 3558433204993 4972855634660 102496191 4611393836428 4611394768123 3243541385504 3243541626921 237222748846 414194133684))))
  (.splitV 2000000000
  (.splitU 16000000000000
  (.splitV 499999744
  (.leaf 0 0 0 0 0 0 8111865955813 8111896684520 0 0 0 0 0 4866210024238 6881860213634 70676 8517335614558 8517381706183 6908380411341 6908389627134 43628829207 88942548336)
  (.leaf 0 0 0 0 0 0 6685233164123 6685239729416 0 0 0 0 0 4866210024238 6881860213634 1046611 6908380411341 6908389627134 5523949072771 5523951386740 88942536255 161639143326))
  (.splitV 499999744
  (.leaf 0 0 0 0 0 0 8111865955813 8111896684520 0 0 0 0 0 6881860213634 8939798655450 70676 8517335614558 8517381706183 6908380411341 6908389627134 43628829207 88942548336)
  (.leaf 0 0 0 0 0 0 6685233164123 6685239729416 0 0 0 0 0 6881860213634 8939798655450 1046611 6908380411341 6908389627134 5523949072771 5523951386740 88942536255 161639143326)))
  (.splitU 16000000000000
  (.splitV 5000000000
  (.leaf 0 0 0 0 0 0 5656740390500 5656743031665 0 0 0 0 0 4866210024238 6881860213634 7083335 5523949584543 5523951898513 4611380371980 4611381304468 161639043100 237227134093)
  (.leaf 0 0 0 0 0 0 4388269762265 4388270509631 0 0 0 0 0 4866210024238 6881860213634 102496191 4611393836428 4611394768123 3243541385504 3243541626921 237222748846 414194133684))
  (.splitV 5000000000
  (.leaf 0 0 0 0 0 0 5656740390500 5656743031665 0 0 0 0 0 6881860213634 8939798655450 7083335 5523949584543 5523951898513 4611380371980 4611381304468 161639043100 237227134093)
  (.leaf 0 0 0 0 0 0 4388269762265 4388270509631 0 0 0 0 0 6881860213634 8939798655450 102496191 4611393836428 4611394768123 3243541385504 3243541626921 237222748846 414194133684)))))
  (.splitU 8000000000000
  (.splitV 124999999488
  (.splitU 4000000000000
  (.splitV 62499999744
  (.leaf 142318986089 142319001350 17355685841 17355699990 51069173788 51069188223 3208658168614 3208658377191 386768110831 27334766310 27334780572 493988126 494002132 2505387385733 3558889880531 1003433409 3243640887999 3243641129002 2154991417551 2154991502127 414141039421 637459294830)
  (.leaf 135975206390 135975221586 16295541711 16295555850 51069173788 51069188223 2413632384124 2413632481778 386768110831 27334766310 27334780572 493988126 494002132 2505387385733 3558889880531 4311516513 2155118960717 2155119045087 1532993893698 1532993940285 637365842036 818240658176))
  (.splitV 62499999744
  (.leaf 18116067491 18116081646 0 0 2481822359 2481836382 3208658168614 3208658377191 398555499782 499846956 499860963 0 0 3558433204993 4972855634660 1003433409 3243640887999 3243641129002 2154991417551 2154991502127 414141039421 637459294830)
  (.leaf 17355685841 17355699990 0 0 2481822359 2481836382 2413632384124 2413632481778 398555499782 499846956 499860963 0 0 3558433204993 4972855634660 4311516513 2155118960717 2155119045087 1532993893698 1532993940285 637365842036 818240658176)))
  (.splitU 4000000000000
  (.splitV 250000000000
  (.leaf 127189217173 127189232309 14366938950 14366953072 51069173788 51069188223 1766261989630 1766262048381 386768110831 27334766310 27334780572 493988126 494002132 2505387385733 3558889880531 15517708333 1533624943060 1533624990428 971022116468 971022145619 817657637400 1044980049426)
  (.leaf 111377713640 111377728629 12668037108 12668051213 51069173788 51069188223 1315335090632 1315335127078 386768110831 27334766310 27334780572 493988126 494002132 2505387385733 3558889880531 35675315692 971029529193 971029558325 683665630453 683665653522 1045125447956 1210438382949))
  (.splitV 250000000000
  (.leaf 16295541711 16295555850 0 0 2481822359 2481836382 1766261989630 1766262048381 398555499782 499846956 499860963 0 0 3558433204993 4972855634660 15517708333 1533624943060 1533624990428 971022116468 971022145619 817657637400 1044980049426)
  (.leaf 14366938950 14366953072 0 0 2481822359 2481836382 1315335090632 1315335127078 398555499782 499846956 499860963 0 0 3558433204993 4972855634660 35675315692 971029529193 971029558325 683665630453 683665653522 1045125447956 1210438382949))))
  (.splitV 124999999488
  (.splitU 16000000000000
  (.splitV 62499999744
  (.leaf 0 0 0 0 0 0 3208658168614 3208658377191 0 0 0 0 0 4866210024238 6881860213634 1003433409 3243640887999 3243641129002 2154991417551 2154991502127 414141039421 637459294830)
  (.leaf 0 0 0 0 0 0 2413632384124 2413632481778 0 0 0 0 0 4866210024238 6881860213634 4311516513 2155118960717 2155119045087 1532993893698 1532993940285 637365842036 818240658176))
  (.splitV 62499999744
  (.leaf 0 0 0 0 0 0 3208658168614 3208658377191 0 0 0 0 0 6881860213634 8939798655450 1003433409 3243640887999 3243641129002 2154991417551 2154991502127 414141039421 637459294830)
  (.leaf 0 0 0 0 0 0 2413632384124 2413632481778 0 0 0 0 0 6881860213634 8939798655450 4311516513 2155118960717 2155119045087 1532993893698 1532993940285 637365842036 818240658176)))
  (.splitU 16000000000000
  (.splitV 250000000000
  (.leaf 0 0 0 0 0 0 1766261989630 1766262048381 0 0 0 0 0 4866210024238 6881860213634 15517708333 1533624943060 1533624990428 971022116468 971022145619 817657637400 1044980049426)
  (.leaf 0 0 0 0 0 0 1315335090632 1315335127078 0 0 0 0 0 4866210024238 6881860213634 35675315692 971029529193 971029558325 683665630453 683665653522 1045125447956 1210438382949))
  (.splitV 250000000000
  (.leaf 0 0 0 0 0 0 1766261989630 1766262048381 0 0 0 0 0 6881860213634 8939798655450 15517708333 1533624943060 1533624990428 971022116468 971022145619 817657637400 1044980049426)
  (.leaf 0 0 0 0 0 0 1315335090632 1315335127078 0 0 0 0 0 6881860213634 8939798655450 35675315692 971029529193 971029558325 683665630453 683665653522 1045125447956 1210438382949)))))))
  (.splitU 2000000000000
  (.splitV 2000000000000
  (.splitU 750000000000
  (.splitV 750000000000
  (.splitU 500000000000
  (.splitV 500000000000
  (.splitU 437499999744
  (.splitV 437499999744
  (.splitU 406249999616
  (.splitV 406249999616
  (.splitU 390624999552
  (.splitV 390624999552
  (.leaf 639353455536 639353476836 612181863829 612181885653 1145517582932 1145517616784 1145517582932 1145517616784 48393077888 683205095590 683205118617 656420079846 656420102307 1211303684948 1229801807562 48393077888 683205095590 683205118617 656420079846 656420102307 1211303684948 1229801807562)
  .skipDiag)
  (.splitV 390624999552
  (.leaf 625569251107 625569273146 599174819208 599174840827 1112817412732 1112817445724 1145517582932 1145517616784 51579524321 656420055218 656420077622 631086100139 631086122303 1229802073578 1247949167354 48393077888 683205095590 683205118617 656420079846 656420102307 1211303684948 1229801807562)
  (.leaf 612181863829 612181885653 586532600084 586532621499 1112817412732 1112817445724 1112817412732 1112817445724 51579524321 656420055218 656420077622 631086100139 631086122303 1229802073578 1247949167354 51579524321 656420055218 656420077622 631086100139 631086122303 1229802073578 1247949167354)))
  .skipDiag)
  (.splitV 406249999616
  (.splitU 421874999680
  (.splitV 390624999552
  (.leaf 612181863829 612181885653 586532600084 586532621499 1081636107783 1081636139888 1145517582932 1145517616784 54807994914 631086073192 631086095355 607086416910 607086438666 1247949430142 1265772771916 48393077888 683205095590 683205118617 656420079846 656420102307 1211303684948 1229801807562)
  (.leaf 599174819208 599174840827 574240580853 574240602048 1081636107783 1081636139888 1112817412732 1112817445724 54807994914 631086073192 631086095355 607086416910 607086438666 1247949430142 1265772771916 51579524321 656420055218 656420077622 631086100139 631086122303 1229802073578 1247949167354))
  (.splitV 390624999552
  (.leaf 599174819208 599174840827 574240580853 574240602048 1051859644682 1051859675947 1145517582932 1145517616784 58074137753 607086387958 607086409611 584317315408 584317336623 1265773031795 1283296904879 48393077888 683205095590 683205118617 656420079846 656420102307 1211303684948 1229801807562)
  (.leaf 586532600084 586532621499 562284959073 562284979574 1051859644682 1051859675947 1112817412732 1112817445724 58074137753 607086387958 607086409611 584317315408 584317336623 1265773031795 1283296904879 51579524321 656420055218 656420077622 631086100139 631086122303 1229802073578 1247949167354)))
  (.leaf 586532600084 586532621499 539331439010 539331458893 1066578899071 1066578930138 1066578899071 1066578930138 56473091803 631106061267 631106083430 584336011371 584336032717 1247913769391 1283260593118 56473091803 631106061267 631106083430 584336011371 584336032717 1247913769391 1283260593118)))
  .skipDiag)
  (.splitV 437499999744
  (.splitU 468749999872
  (.splitV 406249999616
  (.leaf 586532600084 586532621499 539331439010 539331458893 1009609235594 1009609265794 1128969978008 1128970011402 63069009777 584335769227 584335790468 542127777728 542127798312 1283262644384 1317496154971 50019842544 683226677870 683226700959 631106277552 631106299568 1211266920577 1247911665624)
  (.leaf 562284959073 562284979574 517575885666 517575905960 1009609235594 1009609265794 1066578899071 1066578930138 63069009777 584335769227 584335790468 542127777728 542127798312 1283262644384 1317496154971 56473091803 631106061267 631106083430 584336011371 584336032717 1247913769391 1283260593118))
  (.splitV 406249999616
  (.leaf 562284959073 562284979574 517575885666 517575905960 957326611614 957326640430 1128969978008 1128970011402 69775985922 542127518141 542127538806 503849949343 503849969435 1317498149647 1350766395741 50019842544 683226677870 683226700959 631106277552 631106299568 1211266920577 1247911665624)
  (.leaf 539331439010 539331458893 496931957994 496931977894 957326611614 957326640430 1066578899071 1066578930138 69775985922 542127518141 542127538806 503849949343 503849969435 1317498149647 1350766395741 56473091803 631106061267 631106083430 584336011371 584336032717 1247913769391 1283260593118)))
  (.leaf 539331439010 539331458893 458675136391 458675155125 982922120811 982922150241 982922120811 982922150241 66541974179 584409270745 584409292101 503914363419 503914383506 1283127990100 1350627379719 66541974179 584409270745 584409292101 503914363419 503914383506 1283127990100 1350627379719)))
  .skipDiag)
  (.splitV 500000000000
  (.splitU 625000000000
  (.splitV 437499999744
  (.splitU 562500000000
  (.splitV 406249999616
  (.leaf 539331439010 539331458893 477321833554 477321853242 886415638929 886415666208 1128969978008 1128970011402 80097384626 503912216204 503912236200 437177449532 437177468648 1350642869508 1414740221722 50019842544 683226677870 683226700959 631106277552 631106299568 1211266920577 1247911665624)
  (.leaf 517575885666 517575905960 458675136391 458675155719 886415638929 886415666208 1066578899071 1066578930138 80097384626 503912216204 503912236200 437177449532 437177468648 1350642869508 1414740221722 56473091803 631106061267 631106083430 584336011371 584336032717 1247913769391 1283260593118))
  (.splitV 406249999616
  (.leaf 496931957994 496931977894 440928011534 440928030680 803525697707 803525723141 1128969978008 1128970011402 93836461052 437175281889 437175300988 381067545176 381067563374 1414754711061 1476174890436 50019842544 683226677870 683226700959 631106277552 631106299568 1211266920577 1247911665624)
  (.leaf 477321833554 477321853242 424022353666 424022372029 803525697707 803525723141 1066578899071 1066578930138 93836461052 437175281889 437175300988 381067545176 381067563374 1414754711061 1476174890436 56473091803 631106061267 631106083430 584336011371 584336032717 1247913769391 1283260593118)))
  (.leaf 496931957994 496931977894 392527848319 392527866802 843465126398 843465152614 982922120811 982922150241 87382433134 504158491206 504158511210 381257570110 381257588378 1350165589445 1475672519567 66541974179 584409270745 584409292101 503914363419 503914383506 1283127990100 1350627379719))
  (.splitV 437499999744
  (.leaf 458675136391 458675155719 363818631803 363818649878 698826422387 698826445811 1097044335184 1097044367693 114756607340 381241002812 381241021137 292631464609 292631481794 1475780478851 1592435847195 53377523064 683312682550 683312705505 584411211242 584411232619 1211123435915 1283111568058)
  (.leaf 424022353666 424022372029 337579556670 337579574001 698826422387 698826445811 982922120811 982922150241 114756607340 381241002812 381241021137 292631464609 292631481794 1475780478851 1592435847195 66541974179 584409270745 584409292101 503914363419 503914383506 1283127990100 1350627379719)))
  (.splitU 625000000000
  (.splitV 625000000000
  (.leaf 458675136391 458675155125 337579556670 337579574001 843465126398 843465152614 843465126398 843465152614 87382433134 504158491206 504158511210 381257570110 381257588378 1350165589445 1475672519567 87382433134 504158491206 504158511210 381257570110 381257588378 1350165589445 1475672519567)
  .skipDiag)
  (.splitV 625000000000
  (.leaf 392527848319 392527866802 291475377357 291475394526 698826422387 698826445811 843465126398 843465152614 114756607340 381241002812 381241021137 292631464609 292631481794 1475780478851 1592435847195 87382433134 504158491206 504158511210 381257570110 381257588378 1350165589445 1475672519567)
  (.leaf 337579556670 337579574001 252482450896 252482467287 698826422387 698826445811 698826422387 698826445811 114756607340 381241002812 381241021137 292631464609 292631481794 1475780478851 1592435847195 114756607340 381241002812 381241021137 292631464609 292631481794 1475780478851 1592435847195)))))
  .skipDiag)
  (.splitV 750000000000
  (.splitU 1000000000000
  (.splitV 500000000000
  (.leaf 392527848815 392527866802 252482450896 252482467287 539331438262 539331458893 1037465982255 1037466013200 155254286692 293090693463 293090710654 176913054527 176913070288 1591282774688 1806909857753 60459659386 683653952159 683653975223 504175676806 504175696822 1210576667141 1350041340786)
  (.leaf 337579556670 337579574001 190886858906 190886874642 539331438262 539331458893 766280231952 766280256673 155254286692 293090693463 293090710654 176913054527 176913070288 1591282774688 1806909857753 102578890908 505111942226 505111962339 293200552885 293200569942 1348435254541 1590541845134))
  (.splitV 500000000000
  (.leaf 291475377714 291475394526 85650476390 85650491144 252482450896 252482467287 1037465982255 1037466013200 263768687118 180389396859 180389412682 25780844024 25780858270 1796494543218 2516701902163 60459659386 683653952159 683653975223 504175676806 504175696822 1210576667141 1350041340786)
  (.leaf 252482450896 252482467287 66062726852 66062741415 252482450896 252482467287 766280231952 766280256673 263768687118 180389396859 180389412682 25780844024 25780858270 1796494543218 2516701902163 102578890908 505111942226 505111962339 293200552885 293200569942 1348435254541 1590541845134)))
  (.splitU 1000000000000
  (.splitV 1000000000000
  (.leaf 252482450896 252482467287 145413450279 145413465520 539331438262 539331458893 539331438262 539331458893 155254286692 293090693463 293090710654 176913054527 176913070288 1591282774688 1806909857753 155254286692 293090693463 293090710654 176913054527 176913070288 1591282774688 1806909857753)
  .skipDiag)
  (.splitV 1000000000000
  (.leaf 190886858906 190886874642 51069173788 51069188223 252482450896 252482467287 539331438262 539331458893 263768687118 180389396859 180389412682 25780844024 25780858270 1796494543218 2516701902163 155254286692 293090693463 293090710654 176913054527 176913070288 1591282774688 1806909857753)
  (.leaf 145413450279 145413465520 18485439743 18485453887 252482450896 252482467287 252482450896 252482467287 263768687118 180389396859 180389412682 25780844024 25780858270 1796494543218 2516701902163 263768687118 180389396859 180389412682 25780844024 25780858270 1796494543218 2516701902163)))))
  .skipDiag)
  (.splitV 2000000000000
  (.splitU 8000000000000
  (.splitV 750000000000
  (.splitU 4000000000000
  (.splitV 500000000000
  (.leaf 97628796492 97628811352 11171155222 11171169318 51069173788 51069188223 1037465982255 1037466013200 386768110831 27334766310 27334780572 493988126 494002132 2505387385733 3558889880531 60459659386 683653952159 683653975223 504175676806 504175696822 1210576667141 1350041340786)
  (.leaf 85650476390 85650491144 8689331357 8689345432 51069173788 51069188223 766280231952 766280256673 386768110831 27334766310 27334780572 493988126 494002132 2505387385733 3558889880531 102578890908 505111942226 505111962339 293200552885 293200569942 1348435254541 1590541845134))
  (.splitV 500000000000
  (.leaf 12668037108 12668051213 0 0 2481822359 2481836382 1037465982255 1037466013200 398555499782 499846956 499860963 0 0 3558433204993 4972855634660 60459659386 683653952159 683653975223 504175676806 504175696822 1210576667141 1350041340786)
  (.leaf 11171155222 11171169318 0 0 2481822359 2481836382 766280231952 766280256673 398555499782 499846956 499860963 0 0 3558433204993 4972855634660 102578890908 505111942226 505111962339 293200552885 293200569942 1348435254541 1590541845134)))
  (.splitU 4000000000000
  (.splitV 1000000000000
  (.leaf 66062726852 66062741415 6760742417 6760756475 51069173788 51069188223 539331438262 539331458893 386768110831 27334766310 27334780572 493988126 494002132 2505387385733 3558889880531 155254286692 293090693463 293090710654 176913054527 176913070288 1591282774688 1806909857753)
  (.leaf 51069173788 51069188223 2481822359 2481836382 51069173788 51069188223 252482450896 252482467287 386768110831 27334766310 27334780572 493988126 494002132 2505387385733 3558889880531 263768687118 180389396859 180389412682 25780844024 25780858270 1796494543218 2516701902163))
  (.splitV 1000000000000
  (.leaf 8689331357 8689345432 0 0 2481822359 2481836382 539331438262 539331458893 398555499782 499846956 499860963 0 0 3558433204993 4972855634660 155254286692 293090693463 293090710654 176913054527 176913070288 1591282774688 1806909857753)
  (.leaf 6760742417 6760756475 0 0 2481822359 2481836382 252482450896 252482467287 398555499782 499846956 499860963 0 0 3558433204993 4972855634660 263768687118 180389396859 180389412682 25780844024 25780858270 1796494543218 2516701902163))))
  (.splitV 750000000000
  (.splitU 16000000000000
  (.splitV 500000000000
  (.leaf 0 0 0 0 0 0 1037465982255 1037466013200 0 0 0 0 0 4866210024238 6881860213634 60459659386 683653952159 683653975223 504175676806 504175696822 1210576667141 1350041340786)
  (.leaf 0 0 0 0 0 0 766280231952 766280256673 0 0 0 0 0 4866210024238 6881860213634 102578890908 505111942226 505111962339 293200552885 293200569942 1348435254541 1590541845134))
  (.splitV 500000000000
  (.leaf 0 0 0 0 0 0 1037465982255 1037466013200 0 0 0 0 0 6881860213634 8939798655450 60459659386 683653952159 683653975223 504175676806 504175696822 1210576667141 1350041340786)
  (.leaf 0 0 0 0 0 0 766280231952 766280256673 0 0 0 0 0 6881860213634 8939798655450 102578890908 505111942226 505111962339 293200552885 293200569942 1348435254541 1590541845134)))
  (.splitU 16000000000000
  (.splitV 1000000000000
  (.leaf 0 0 0 0 0 0 539331438262 539331458893 0 0 0 0 0 4866210024238 6881860213634 155254286692 293090693463 293090710654 176913054527 176913070288 1591282774688 1806909857753)
  (.leaf 0 0 0 0 0 0 252482450896 252482467287 0 0 0 0 0 4866210024238 6881860213634 263768687118 180389396859 180389412682 25780844024 25780858270 1796494543218 2516701902163))
  (.splitV 1000000000000
  (.leaf 0 0 0 0 0 0 539331438262 539331458893 0 0 0 0 0 6881860213634 8939798655450 155254286692 293090693463 293090710654 176913054527 176913070288 1591282774688 1806909857753)
  (.leaf 0 0 0 0 0 0 252482450896 252482467287 0 0 0 0 0 6881860213634 8939798655450 263768687118 180389396859 180389412682 25780844024 25780858270 1796494543218 2516701902163)))))
  (.splitU 8000000000000
  (.splitV 8000000000000
  (.splitU 4000000000000
  (.splitV 4000000000000
  (.leaf 18485439743 18485453887 0 0 51069173788 51069188223 51069173788 51069188223 386768110831 27334766310 27334780572 493988126 494002132 2505387385733 3558889880531 386768110831 27334766310 27334780572 493988126 494002132 2505387385733 3558889880531)
  .skipDiag)
  (.splitV 4000000000000
  (.leaf 2481822359 2481836382 0 0 2481822359 2481836382 51069173788 51069188223 398555499782 499846956 499860963 0 0 3558433204993 4972855634660 386768110831 27334766310 27334780572 493988126 494002132 2505387385733 3558889880531)
  (.leaf 0 0 0 0 2481822359 2481836382 2481822359 2481836382 398555499782 499846956 499860963 0 0 3558433204993 4972855634660 398555499782 499846956 499860963 0 0 3558433204993 4972855634660)))
  .skipDiag)
  (.splitV 8000000000000
  (.splitU 16000000000000
  (.splitV 4000000000000
  (.leaf 0 0 0 0 0 0 51069173788 51069188223 0 0 0 0 0 4866210024238 6881860213634 386768110831 27334766310 27334780572 493988126 494002132 2505387385733 3558889880531)
  (.leaf 0 0 0 0 0 0 2481822359 2481836382 0 0 0 0 0 4866210024238 6881860213634 398555499782 499846956 499860963 0 0 3558433204993 4972855634660))
  (.splitV 4000000000000
  (.leaf 0 0 0 0 0 0 51069173788 51069188223 0 0 0 0 0 6881860213634 8939798655450 386768110831 27334766310 27334780572 493988126 494002132 2505387385733 3558889880531)
  (.leaf 0 0 0 0 0 0 2481822359 2481836382 0 0 0 0 0 6881860213634 8939798655450 398555499782 499846956 499860963 0 0 3558433204993 4972855634660)))
  (.splitU 16000000000000
  (.splitV 16000000000000
  (.leaf 0 0 0 0 0 0 0 0 0 0 0 0 0 4866210024238 6881860213634 0 0 0 0 0 4866210024238 6881860213634)
  .skipDiag)
  (.splitV 16000000000000
  (.leaf 0 0 0 0 0 0 0 0 0 0 0 0 0 6881860213634 8939798655450 0 0 0 0 0 4866210024238 6881860213634)
  .skipTail))))))))

theorem cert_ok : checkTree 100000000 27000000000000 100000000 27000000000000 certTree = true := rfl

end C6aProof

theorem OMA.solution : type_of% @Constant6a.c6a_lower_bound_improved :=
  C6aProof.main_from_cert C6aProof.cert_ok C6aProof.checkTree_sound
