import OMAStatements.S_mo_184507
import Mathlib

/-!
# A continuously differentiable graph whose slice length is not differentiable

Place a sine wave in each of a sequence of disjoint horizontal bands accumulating
at the middle slice. The two partial derivatives have summable uniform bounds.
At distance 16⁻ⁿ from the middle the horizontal slope has amplitude 2⁻ⁿ, so
the length exceeds the middle length by at least 4⁻ⁿ / 6.
-/

namespace MO184507Cutoff

open scoped ContDiff

private noncomputable def bump : ContDiffBump (1 : ℝ) :=
  ⟨1/8, 1/4, by norm_num, by norm_num⟩

noncomputable def h : ℝ → ℝ := bump

theorem smooth : ContDiff ℝ ∞ h := bump.contDiff

theorem diff : Differentiable ℝ h := smooth.differentiable (by simp)

theorem bound (x : ℝ) : |h x| ≤ 1 := by
  change |bump x| ≤ 1
  rw [abs_of_nonneg bump.nonneg]
  exact bump.le_one

theorem deriv_bound : ∃ D : ℝ, 0 ≤ D ∧ ∀ x, |deriv h x| ≤ D := by
  have hc : HasCompactSupport h := bump.hasCompactSupport
  obtain ⟨C,hC⟩ := hc.deriv.exists_bound_of_continuous (smooth.continuous_deriv (by simp))
  exact ⟨max C 0, le_max_right _ _, fun x => (hC x).trans (le_max_left _ _)⟩

theorem one : h 1 = 1 := bump.one_of_mem_closedBall (by simp [bump])

theorem supported : tsupport h ⊆ Set.Ioo (1/2:ℝ) (3/2) := by
  change tsupport (bump : ℝ → ℝ) ⊆ _
  rw [bump.tsupport_eq]
  intro x hx
  change dist x 1 ≤ 1/4 at hx
  rw [Real.dist_eq,abs_le] at hx
  constructor <;> linarith

theorem outside {x : ℝ} (hx : x ∉ Set.Ioo (1/2:ℝ) (3/2)) : h x = 0 := by
  by_contra hn
  exact hx (supported (subset_closure (show x ∈ Function.support h from hn)))

theorem zero : h 0 = 0 := outside (by norm_num)

theorem scaled (m n : ℕ) : h ((16:ℝ)^m * (1/16:ℝ)^n) = if m=n then 1 else 0 := by
  rw [one_div, inv_pow, ← div_eq_mul_inv]
  rcases lt_trichotomy m n with hmn | rfl | hnm
  · rw [if_neg hmn.ne]
    apply outside
    have hpow : (16:ℝ)^(m+1) ≤ 16^n := pow_right_mono₀ (by norm_num) hmn
    rw [pow_succ] at hpow
    have hle : (16:ℝ)^m / 16^n ≤ 1/2 := by
      apply (div_le_iff₀ (by positivity)).mpr
      linarith [show 0 ≤ (16:ℝ)^m by positivity]
    exact fun hx => (not_lt_of_ge hle) hx.1
  · simp [one]
  · rw [if_neg hnm.ne']
    apply outside
    have hpow : (16:ℝ)^(n+1) ≤ 16^m := pow_right_mono₀ (by norm_num) hnm
    rw [pow_succ] at hpow
    have hle : 3/2 ≤ (16:ℝ)^m / 16^n := by
      apply (le_div_iff₀ (by positivity)).mpr
      linarith [show 0 ≤ (16:ℝ)^n by positivity]
    exact fun hx => (not_lt_of_ge hle) hx.2

theorem ratio (n m : ℕ) : h ((1/16:ℝ)^n / (1/16:ℝ)^m) = if n=m then 1 else 0 := by
  simpa [div_eq_mul_inv, one_div, mul_comm, eq_comm] using scaled m n

end MO184507Cutoff

namespace MO184507Series
noncomputable section
open Real ContinuousLinearMap
abbrev Plane := ℝ × ℝ

def term (g : ℝ → ℝ) (a k w : ℝ) (z : Plane) :=
  a * g (w*z.2) * sin (k*z.1)
def F (g : ℝ → ℝ) (a k w : ℕ → ℝ) (z : Plane) := ∑' n, term g (a n) (k n) (w n) z

private def X (g : ℝ → ℝ) (a k w : ℝ) (z : Plane) :=
  a * g (w*z.2) * k * cos (k*z.1)
private def Y (g : ℝ → ℝ) (a k w : ℝ) (z : Plane) :=
  a * deriv g (w*z.2) * w * sin (k*z.1)
private def D (g : ℝ → ℝ) (a k w : ℝ) (z : Plane) : Plane →L[ℝ] ℝ :=
  X g a k w z • fst ℝ ℝ ℝ + Y g a k w z • snd ℝ ℝ ℝ

private theorem derivative {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) (a k w : ℝ) (z : Plane) :
    HasFDerivAt (term g a k w) (D g a k w z) z := by
  have hy : HasFDerivAt (fun v : Plane => w*v.2) (w • snd ℝ ℝ ℝ) z :=
    hasFDerivAt_snd.const_mul w
  have hx : HasFDerivAt (fun v : Plane => k*v.1) (k • fst ℝ ℝ ℝ) z :=
    hasFDerivAt_fst.const_mul k
  have h1 := ((hg.differentiable_one _).hasDerivAt.comp_hasFDerivAt z hy).const_mul a
  have h2 := (hasDerivAt_sin (k*z.1)).comp_hasFDerivAt z hx
  have hform : D g a k w z = (a*g (w*z.2)) • cos (k*z.1) • k • fst ℝ ℝ ℝ + sin (k*z.1) • a • deriv g (w*z.2) • w • snd ℝ ℝ ℝ := by
    apply ContinuousLinearMap.ext
    intro v
    change (a * g (w*z.2) * k * cos (k*z.1))*v.1 + (a*deriv g (w*z.2)*w*sin (k*z.1))*v.2 =
      (a*g (w*z.2)) * (cos (k*z.1) * (k*v.1)) + sin (k*z.1) * (a*(deriv g (w*z.2)*(w*v.2)))
    ring
  rw [hform]
  exact h1.mul h2

private theorem bound {g : ℝ → ℝ} {B M : ℝ} (hb : ∀ y, |g y| ≤ B)
    (hm : ∀ y, |deriv g y| ≤ M) (a k w : ℝ) (z : Plane) :
    ‖D g a k w z‖ ≤ |a| * B * |k| + |a| * M * |w| := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (hb 0)
  have hM : 0 ≤ M := (abs_nonneg _).trans (hm 0)
  have hx : |X g a k w z| ≤ |a| * B * |k| := by
    unfold X
    simp only [abs_mul]
    calc
      _ ≤ |a| * B * |k| * 1 := by gcongr <;> first | positivity | exact hb _ | exact abs_cos_le_one _
      _ = _ := mul_one _
  have hy : |Y g a k w z| ≤ |a| * M * |w| := by
    unfold Y
    simp only [abs_mul]
    calc
      _ ≤ |a| * M * |w| * 1 := by gcongr <;> first | positivity | exact hm _ | exact abs_sin_le_one _
      _ = _ := mul_one _
  apply (norm_add_le _ _).trans
  simp only [norm_smul, Real.norm_eq_abs]
  exact add_le_add ((mul_le_mul_of_nonneg_left (norm_fst_le ℝ ℝ ℝ) (abs_nonneg _)).trans
    (by simpa using hx)) ((mul_le_mul_of_nonneg_left (norm_snd_le ℝ ℝ ℝ) (abs_nonneg _)).trans
    (by simpa using hy))

theorem regular {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) (a k w : ℕ → ℝ) {B M : ℝ}
    (hb : ∀ y, |g y| ≤ B) (hm : ∀ y, |deriv g y| ≤ M)
    (hx : Summable (fun n => |a n| * B * |k n|)) (hy : Summable (fun n => |a n| * M * |w n|)) :
    ContDiff ℝ 1 (F g a k w) ∧
    ∀ z, fderiv ℝ (F g a k w) z (1,0) =
      ∑' n, a n * g (w n*z.2) * k n * cos (k n*z.1) := by
  have h0 : Summable (fun n => term g (a n) (k n) (w n) (0,0)) := by simp [term]
  have hbound := fun n z => bound hb hm (a n) (k n) (w n) z
  have hder := fun z => hasFDerivAt_tsum (hx.add hy) (fun n => derivative hg (a n) (k n) (w n)) hbound h0 z
  have hgc := hg.continuous
  have hgd := (contDiff_one_iff_deriv.mp hg).2
  refine ⟨contDiff_one_iff_hasFDerivAt.mpr ⟨_, ?_, hder⟩, ?_⟩
  · have hct (n : ℕ) : Continuous (D g (a n) (k n) (w n)) := by
      unfold D X Y
      fun_prop
    exact continuous_tsum hct (hx.add hy) hbound
  · intro z
    unfold F
    rw [(hder z).fderiv]
    let e := ContinuousLinearMap.apply ℝ ℝ ((1,0) : Plane)
    have hs : Summable (fun n => D g (a n) (k n) (w n) z) := (hx.add hy).of_norm_bounded (hbound · z)
    change e (∑' n, D g (a n) (k n) (w n) z) = _
    rw [e.map_tsum hs]
    apply tsum_congr
    intro n
    simp [e,D,X, smul_eq_mul]
end
end MO184507Series

namespace MO184507
open Real MeasureTheory

theorem cosine_square_integral {N : ℕ} (hN : 0 < N) :
    (∫ x in (0:ℝ)..1, Real.cos (2 * Real.pi * N * x)^2) = 1/2 := by
  let c : ℝ := 2 * Real.pi * N
  have hc : 0 < c := by dsimp [c]; positivity
  have hs : Real.sin c = 0 := by
    convert Real.sin_nat_mul_pi (2*N) using 2
    dsimp [c]
    push_cast
    ring
  change (∫ x in (0:ℝ)..1, (fun y => Real.cos y ^ 2) (c*x)) = _
  rw [intervalIntegral.integral_comp_mul_left (fun y => Real.cos y ^ 2) hc.ne']
  simp [integral_cos_sq,hs,smul_eq_mul,hc.ne']
  field_simp

theorem cosine_slice_length {a : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 1) {N : ℕ} (hN : 0 < N) :
    1 + a^2/6 ≤ ∫ x in (0:ℝ)..1, Real.sqrt (1+(a*Real.cos (2*Real.pi*N*x))^2) := by
  let w := fun x : ℝ => Real.cos (2*Real.pi*N*x)
  have hw : Continuous w := by dsimp [w]; fun_prop
  have hpoint (x : ℝ) : 1 + (a^2/3)*w x ^ 2 ≤ Real.sqrt (1+(a*w x)^2) := by
    have hab : |a*w x| ≤ 1 := by
      rw [abs_mul,abs_of_nonneg ha]
      exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) ha).trans (by simpa)
    have hb := sq_le_sq₀ (abs_nonneg (a*w x)) (by norm_num : (0:ℝ) ≤ 1)
    have hy : (a*w x)^2 ≤ 1 := by simpa using hb.mpr hab
    have hs := Real.sq_sqrt (by positivity : 0 ≤ 1+(a*w x)^2)
    nlinarith [sq_nonneg (a*w x),Real.sqrt_nonneg (1+(a*w x)^2),
      mul_nonneg (sq_nonneg (a*w x)) (sub_nonneg.mpr hy)]
  have hR : Continuous (fun x => Real.sqrt (1+(a*w x)^2)) := by fun_prop
  have hT : Continuous (fun x => (a^2/3)*w x^2) := by fun_prop
  have hh := intervalIntegral.integral_mono_on (μ := volume) zero_le_one
    ((continuous_const.add hT).intervalIntegrable 0 1) (hR.intervalIntegrable 0 1)
    (fun x _ => hpoint x)
  simp only [Pi.add_apply] at hh
  rw [intervalIntegral.integral_add (continuous_const.intervalIntegrable ..) (hT.intervalIntegrable ..),
    intervalIntegral.integral_const_mul] at hh
  have hcos : (∫ x in (0:ℝ)..1, w x^2) = 1/2 := cosine_square_integral hN
  rw [hcos] at hh
  simpa only [intervalIntegral.integral_const,sub_zero,one_smul] using (show
    1 + a^2/6 ≤ ∫ x in (0:ℝ)..1, Real.sqrt (1+(a*w x)^2) by
      simp at hh
      linarith)
end MO184507

namespace SliceCounterexample
open Filter Set OMA.S_mo_184507
open scoped Topology

noncomputable def height (n : ℕ) : ℝ := 1/2+(1/16:ℝ)^n
noncomputable def freq (n : ℕ) : ℝ := 2 * Real.pi * (64:ℝ)^n
noncomputable def scale (n : ℕ) : ℝ := (16:ℝ)^n
noncomputable def amp (n : ℕ) : ℝ := (1/2:ℝ)^n / freq n

theorem freq_pos (n : ℕ) : 0 < freq n := by unfold freq; positivity

theorem height_mem {n : ℕ} (hn : 1 ≤ n) : height n ∈ interval := by
  have h := pow_le_pow_of_le_one (by norm_num : 0 ≤ (1/16:ℝ)) (by norm_num : (1/16:ℝ) ≤ 1) hn
  change 0 ≤ 1/2+(1/16:ℝ)^n ∧ 1/2+(1/16:ℝ)^n ≤ 1
  constructor
  · positivity
  · norm_num at h; linarith

theorem summable_x (B : ℝ) : Summable (fun n => |amp n| * B * |freq n|) := by
  apply ((summable_geometric_of_abs_lt_one (by norm_num : |(1/2:ℝ)| < 1)).mul_right B).congr
  intro n
  symm
  have hk := freq_pos n
  rw [abs_of_pos hk, abs_of_pos (show 0 < amp n by unfold amp; positivity)]
  unfold amp
  field_simp

theorem summable_y (D : ℝ) : Summable (fun n => |amp n| * D * |scale n|) := by
  apply ((summable_geometric_of_abs_lt_one (by norm_num : |(1/8:ℝ)| < 1)).mul_right (D/(2*Real.pi))).congr
  intro n
  symm
  have hk := freq_pos n
  rw [abs_of_pos (show 0 < amp n by unfold amp; positivity), abs_of_pos (show 0 < scale n by unfold scale; positivity)]
  unfold amp scale freq
  have he : (1/2:ℝ)^n * 16^n = (1/8:ℝ)^n * 64^n := by
    rw [← mul_pow, ← mul_pow]; norm_num
  field_simp [Real.pi_ne_zero]
  linear_combination D * he

theorem not_differentiable {L : ℝ → ℝ} (h0 : L (1/2) = 1)
    (hb : ∀ n : ℕ, 1 ≤ n → 1 + ((1/2:ℝ)^n)^2 / 6 ≤ L (height n)) :
    ¬ DifferentiableAt ℝ L (1/2) := by
  intro hd
  have ht : Tendsto height atTop (𝓝 (1/2:ℝ)) := by
    change Tendsto (fun n : ℕ => (1/2:ℝ)+(1/16:ℝ)^n) atTop _
    simpa only [add_zero] using (tendsto_const_nhds (x := (1/2:ℝ))).add
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/16) (by norm_num))
  obtain ⟨C,hC⟩ := (hd.hasDerivAt.isBigO_sub.comp_tendsto ht).bound
  have hlarge := (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<4)).eventually_gt_atTop (6*C)
  obtain ⟨n,hn,hle,hbig⟩ := (eventually_ge_atTop 1 |>.and (hC.and hlarge)).exists
  have hpos : 0 < (1/16:ℝ)^n := by positivity
  change ‖L (height n) - L (1/2)‖ ≤ C * ‖height n - 1/2‖ at hle
  rw [h0, Real.norm_eq_abs, Real.norm_eq_abs, height, add_sub_cancel_left, abs_of_pos hpos] at hle
  have hu := (le_abs_self _).trans hle
  have he : ((1/2:ℝ)^n)^2 = (4:ℝ)^n*(1/16:ℝ)^n := by
    rw [← mul_pow, ← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  have hlo := hb n hn
  rw [he] at hlo
  change 1 + _ ≤ L (1/2 + (1/16:ℝ)^n) at hlo
  nlinarith [mul_lt_mul_of_pos_right hbig hpos]

end SliceCounterexample

namespace SliceCounterexample
open Set OMA.S_mo_184507
open scoped Topology

theorem disproof_of_derivatives (G : ℝ × ℝ → ℝ) (hG : ContDiff ℝ 1 G)
    (h0 : ∀ x : ℝ, fderiv ℝ G (x,0) (1,0) = 0)
    (hseq : ∀ (n : ℕ) (x : ℝ), fderiv ℝ G (x,(1/16:ℝ)^n) (1,0) =
      (1/2:ℝ)^n * Real.cos (2*Real.pi*((64^n:ℕ):ℝ)*x)) :
    ¬ (type_of% @OMA.S_mo_184507.main) := by
  let t : ℝ × ℝ := (0,1/2)
  let f := fun z : ℝ × ℝ => G (z-t)
  have hf : ContDiff ℝ 1 f := hG.comp (contDiff_id.sub contDiff_const)
  have hUD : UniqueDiffOn ℝ square := uniqueDiffOn_Icc_zero_one.prod uniqueDiffOn_Icc_zero_one
  have hshift {x y : ℝ} (hx : x ∈ interval) (hy : y ∈ interval) :
      fderivWithin ℝ f square (x,y) (1,0) = fderiv ℝ G (x,y-1/2) (1,0) := by
    have hd := ((hG.differentiable (by norm_num)).differentiableAt
      (x := (x,y)-t)).hasFDerivAt.comp (x,y) (hasFDerivAt_sub_const t)
    have he := hd.hasFDerivWithinAt.fderivWithin (hUD (x,y) ⟨hx,hy⟩)
    change fderivWithin ℝ f square (x,y) (1,0) = _
    rw [show fderivWithin ℝ f square (x,y) = _ from he]
    simp [t,Prod.sub_def]
  have hmid : (1/2:ℝ) ∈ interval := by constructor <;> norm_num
  have hz : sliceLength f (1/2) = 1 := by
    unfold sliceLength
    calc
      _ = ∫ _x in (0:ℝ)..1, (1:ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le zero_le_one] at hx
        dsimp only
        rw [hshift hx hmid,sub_self,h0]
        norm_num
      _ = _ := by simp
  have hb (n : ℕ) (hn : 1 ≤ n) : 1 + ((1/2:ℝ)^n)^2/6 ≤ sliceLength f (height n) := by
    refine (MO184507.cosine_slice_length (a := (1/2:ℝ)^n) (by positivity)
      (pow_le_one₀ (by norm_num) (by norm_num)) (N := 64^n) (by positivity)).trans_eq ?_
    unfold sliceLength
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le zero_le_one] at hx
    dsimp only
    rw [hshift hx (height_mem hn),show height n - 1/2 = (1/16:ℝ)^n by unfold height; ring,hseq]
  intro hmain
  have hcd := hmain f hf.contDiffOn
  exact not_differentiable hz hb ((hcd.differentiableOn (by norm_num) _ hmid).differentiableAt
    (Icc_mem_nhds (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1)))
end SliceCounterexample

namespace SliceCounterexample

theorem construction : ∃ G : ℝ × ℝ → ℝ, ContDiff ℝ 1 G ∧
    (∀ x : ℝ, fderiv ℝ G (x,0) (1,0) = 0) ∧
    (∀ (n : ℕ) (x : ℝ), fderiv ℝ G (x,(1/16:ℝ)^n) (1,0) =
      (1/2:ℝ)^n * Real.cos (2*Real.pi*((64^n:ℕ):ℝ)*x)) := by
  obtain ⟨D, _, hd⟩ := MO184507Cutoff.deriv_bound
  have hh : ContDiff ℝ 1 MO184507Cutoff.h := MO184507Cutoff.smooth.of_le (by simp)
  obtain ⟨hG,hder⟩ := MO184507Series.regular hh amp freq scale
    MO184507Cutoff.bound hd (summable_x 1) (summable_y D)
  refine ⟨_,hG,?_,?_⟩
  · intro x
    rw [hder]
    simp [MO184507Cutoff.zero]
  · intro n x
    rw [hder, tsum_eq_single n]
    · simp only [scale,MO184507Cutoff.scaled,↓reduceIte,mul_one,amp]
      rw [div_mul_cancel₀ _ (freq_pos n).ne']
      simp [freq]
    · intro m hmn
      simp only [scale, MO184507Cutoff.scaled, if_neg hmn, mul_zero, zero_mul]

end SliceCounterexample

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_184507.main) := by
  obtain ⟨G, hG, h0, hs⟩ := SliceCounterexample.construction
  exact SliceCounterexample.disproof_of_derivatives G hG h0 hs
