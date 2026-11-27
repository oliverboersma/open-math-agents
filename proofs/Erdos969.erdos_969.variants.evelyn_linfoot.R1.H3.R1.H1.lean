import OMAReductions.R_Erdos969_erdos_969_variants_evelyn_linfoot_R1_H3_R1
import Mathlib

/-!
Analytic continuation of a discrete Abel transform.

New proof: Hanan Beer (@hananzlt).
Reduction and target formulation: Erik Byrwa (@ebyrwa), open-math-agents PR 2735.
The power-difference estimate is reused from Hanan Beer's proof of the sibling step
Erdos969.erdos_969.variants.evelyn_linfoot.R1.H3.R1.H2.

The identity-theorem setup in `continuation_on` and the upper/lower half-plane
argument in `continuation` adapt the corresponding argument by Sky (@ChironTheCentaur),
HardyOmegaFC/Continuation.lean, commit 80d65168002a5c5903c5808f619f23f21a21f632:
https://github.com/ChironTheCentaur/rh-lab-divisor-problem/blob/80d65168002a5c5903c5808f619f23f21a21f632/HardyOmegaFC/Continuation.lean
The source was consulted through its preserved port in
open-math-agents/proofs/DirichletDivisorProblem.divisor_error_hardy.lean.

NOTICE: HardyDivisorOmega (standalone package), Copyright 2026 Sky
(GitHub: ChironTheCentaur). The original work in HardyOmegaFC/ is licensed under
the Apache License, Version 2.0 (http://www.apache.org/licenses/LICENSE-2.0),
distributed on an AS IS basis, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND.
The adapted argument in this file is a modified version.

The coefficient bound gives a locally summable majorant on Re(s) > 1/4.
Absolute convergence identifies the Abel transform with the given L-series on
Re(s) > 2. The identity theorem extends that equality to each nonreal half-plane.
-/

open Filter Topology Asymptotics

namespace AbelianContinuation

lemma power_difference_bound (s : ℂ) (hs : 0 < s.re) (x : ℝ) (hx : 0 < x) :
    ‖(x : ℂ) ^ (-s) - ((x + 1 : ℝ) : ℂ) ^ (-s)‖ ≤
      ‖s‖ * x ^ (-s.re - 1) := by
  have hs0 : -s ≠ 0 := neg_ne_zero.mpr (fun h => by simp [h] at hs)
  have hd (y : ℝ) (hy : y ∈ Set.Icc x (x + 1)) :
      HasDerivWithinAt (fun v : ℝ => (v : ℂ) ^ (-s))
        ((-s) * (y : ℂ) ^ (-s - 1)) (Set.Icc x (x + 1)) y :=
    (hasDerivAt_ofReal_cpow_const (by linarith [hy.1]) hs0).hasDerivWithinAt
  have hb (y : ℝ) (hy : y ∈ Set.Ico x (x + 1)) :
      ‖(-s) * (y : ℂ) ^ (-s - 1)‖ ≤ ‖s‖ * x ^ (-s.re - 1) := by
    rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith [hy.1])]
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hx hy.1 (by linarith)) (norm_nonneg s)
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hd hb (x + 1)
    (show x + 1 ∈ Set.Icc x (x + 1) by constructor <;> linarith)
  simpa only [norm_sub_rev, add_sub_cancel_left, mul_one] using h

lemma global_bound (u : ℕ → ℂ)
    (hu : u =O[atTop] (fun n : ℕ => (n : ℝ) ^ (1 / 4 : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n → ‖u n‖ ≤ C * (n : ℝ) ^ (1 / 4 : ℝ) := by
  obtain ⟨C, hC⟩ := hu.bound
  obtain ⟨N, hN⟩ := eventually_atTop.mp hC
  let D := ∑ n ∈ Finset.range N, ‖u n‖
  have hD : 0 ≤ D := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  refine ⟨max C 0 + D, by positivity, fun n hn => ?_⟩
  have hp : 0 ≤ (n : ℝ) ^ (1 / 4 : ℝ) := by positivity
  by_cases h : N ≤ n
  · have hb := hN n h
    rw [Real.norm_of_nonneg hp] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right (by linarith [le_max_left C 0]) hp)
  · have hb : ‖u n‖ ≤ D := Finset.single_le_sum (fun _ _ => norm_nonneg _)
      (Finset.mem_range.mpr (by omega))
    have hp1 : 1 ≤ (n : ℝ) ^ (1 / 4 : ℝ) :=
      Real.one_le_rpow (by exact_mod_cast hn) (by norm_num)
    calc ‖u n‖ ≤ D := hb
      _ ≤ D * (n : ℝ) ^ (1 / 4 : ℝ) := by nlinarith
      _ ≤ (max C 0 + D) * (n : ℝ) ^ (1 / 4 : ℝ) := by
        gcongr
        exact le_add_of_nonneg_left (le_max_right C 0)

noncomputable def transform (u : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∑' n : ℕ, u (n + 1) *
    (((n + 1 : ℕ) : ℂ) ^ (-s) - ((n + 2 : ℕ) : ℂ) ^ (-s))

lemma majorant (u : ℕ → ℂ) (C a R : ℝ)
    (hC : 0 ≤ C) (ha : 1 / 4 < a)
    (hu : ∀ n : ℕ, 1 ≤ n → ‖u n‖ ≤ C * (n : ℝ) ^ (1 / 4 : ℝ))
    (n : ℕ) (s : ℂ) (hs : a < s.re) (hR : ‖s‖ < R) :
    ‖u (n + 1) * (((n + 1 : ℕ) : ℂ) ^ (-s) - ((n + 2 : ℕ) : ℂ) ^ (-s))‖ ≤
      C * R * ((n + 1 : ℕ) : ℝ) ^ (1 / 4 - a - 1) := by
  have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hpow := power_difference_bound s (by linarith) ((n + 1 : ℕ) : ℝ) (by positivity)
  norm_cast at hpow
  rw [norm_mul]
  calc ‖u (n + 1)‖ * ‖((n + 1 : ℕ) : ℂ) ^ (-s) - ((n + 2 : ℕ) : ℂ) ^ (-s)‖
      ≤ (C * ((n + 1 : ℕ) : ℝ) ^ (1 / 4 : ℝ)) *
          (‖s‖ * ((n + 1 : ℕ) : ℝ) ^ (-s.re - 1)) := by gcongr; exact hu _ (by omega)
    _ ≤ (C * ((n + 1 : ℕ) : ℝ) ^ (1 / 4 : ℝ)) *
          (R * ((n + 1 : ℕ) : ℝ) ^ (-a - 1)) := by
      gcongr
      linarith [norm_nonneg s]
    _ = _ := by
      rw [show C * ((n + 1 : ℕ) : ℝ) ^ (1 / 4 : ℝ) *
          (R * ((n + 1 : ℕ) : ℝ) ^ (-a - 1)) =
        C * R * (((n + 1 : ℕ) : ℝ) ^ (1 / 4 : ℝ) *
          ((n + 1 : ℕ) : ℝ) ^ (-a - 1)) by ring]
      rw [← Real.rpow_add (by positivity)]
      congr 2
      ring

lemma differentiableAt_transform (u : ℕ → ℂ)
    (hu : u =O[atTop] (fun n : ℕ => (n : ℝ) ^ (1 / 4 : ℝ)))
    (s : ℂ) (hs : 1 / 4 < s.re) : DifferentiableAt ℂ (transform u) s := by
  obtain ⟨C, hC, hbound⟩ := global_bound u hu
  obtain ⟨a, ha, has⟩ := exists_between hs
  let R := ‖s‖ + 1
  let U : Set ℂ := {z | a < z.re ∧ ‖z‖ < R}
  have hU : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt continuous_norm continuous_const)
  have hsU : s ∈ U := ⟨has, by dsimp [R]; linarith⟩
  have hsum : Summable (fun n : ℕ => C * R * ((n + 1 : ℕ) : ℝ) ^ (1 / 4 - a - 1)) :=
    ((Real.summable_nat_rpow.mpr (by linarith : 1 / 4 - a - 1 < -1)).comp_injective
      (fun _ _ h => Nat.add_right_cancel h)).mul_left (C * R)
  have hd (n : ℕ) : DifferentiableOn ℂ
      (fun z => u (n + 1) * (((n + 1 : ℕ) : ℂ) ^ (-z) - ((n + 2 : ℕ) : ℂ) ^ (-z))) U := by
    apply Differentiable.differentiableOn
    fun_prop
  exact (Complex.differentiableOn_tsum_of_summable_norm hsum hd hU
    (fun n z hz => majorant u C a R hC ha hbound n z hz.1 hz.2)).differentiableAt
      (hU.mem_nhds hsU)

lemma summable_weight (u : ℕ → ℂ)
    (hu : u =O[atTop] (fun n : ℕ => (n : ℝ) ^ (1 / 4 : ℝ)))
    (s : ℂ) (hs : 2 < s.re) :
    Summable (fun n : ℕ => u (n + 1) * ((n + 1 : ℕ) : ℂ) ^ (-s)) := by
  have ht : LSeriesSummable u s := LSeriesSummable_of_isBigO_rpow
    (x := 5 / 4) (by linarith) (by convert hu using 1; norm_num)
  have h := ht.comp_injective (i := fun n : ℕ => n + 1) (fun _ _ h => Nat.add_right_cancel h)
  simpa only [Function.comp_def, LSeries.term_of_ne_zero (Nat.succ_ne_zero _), Complex.cpow_neg,
    div_eq_mul_inv] using h

lemma summable_weight_shift (u : ℕ → ℂ)
    (hu : u =O[atTop] (fun n : ℕ => (n : ℝ) ^ (1 / 4 : ℝ)))
    (s : ℂ) (hs : 2 < s.re) :
    Summable (fun n : ℕ => u n * ((n + 1 : ℕ) : ℂ) ^ (-s)) := by
  have ht : LSeriesSummable u s := LSeriesSummable_of_isBigO_rpow
    (x := 5 / 4) (by linarith) (by convert hu using 1; norm_num)
  apply Summable.of_norm_bounded_eventually_nat ht.norm
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega : 0 < n + 1), Complex.neg_re,
    LSeries.norm_term_eq, if_neg (by omega : n ≠ 0),
    div_eq_mul_inv, ← Real.rpow_neg (Nat.cast_nonneg n)]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos hn0 (by norm_num) (by linarith)) (norm_nonneg _)

lemma transform_eq (u : ℕ → ℂ)
    (hu : u =O[atTop] (fun n : ℕ => (n : ℝ) ^ (1 / 4 : ℝ)))
    (s : ℂ) (hs : 2 < s.re) :
    transform u s = u 0 + ∑' n : ℕ, (u (n + 1) - u n) * ((n + 1 : ℕ) : ℂ) ^ (-s) := by
  have h₁ := summable_weight u hu s hs
  have h₂ := summable_weight_shift u hu s hs
  have h₃ := h₂.comp_injective (i := fun n : ℕ => n + 1) (fun _ _ h => Nat.add_right_cancel h)
  simp only [Function.comp_def, Nat.add_assoc] at h₃
  unfold transform
  simp_rw [mul_sub, sub_mul]
  rw [h₁.tsum_sub h₃, h₁.tsum_sub h₂]
  have heq := h₂.tsum_eq_zero_add
  simp only [Nat.zero_add, Nat.cast_one, Complex.one_cpow, mul_one] at heq
  linear_combination heq

lemma summable_powers (s : ℂ) (hs : 1 < s.re) :
    Summable (fun n : ℕ => ((n + 1 : ℕ) : ℂ) ^ (-s)) := by
  have h : LSeriesSummable (fun _ : ℕ => (1 : ℂ)) s :=
    LSeriesSummable_of_bounded_of_one_lt_re (fun _ _ => le_rfl) hs
  have h' := h.comp_injective (i := fun n : ℕ => n + 1) (fun _ _ h => Nat.add_right_cancel h)
  simpa [Function.comp_def, LSeries.term, Complex.cpow_neg, one_div] using h'

lemma identity_right (A : ℕ → ℕ) (c : ℝ)
    (hu : (fun n : ℕ => ((A n : ℂ) - (c : ℂ) * n)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (1 / 4 : ℝ)))
    (s : ℂ) (hs : 2 < s.re) :
    (c : ℂ) * riemannZeta s - (A 0 : ℂ) +
      transform (fun n : ℕ => (A n : ℂ) - (c : ℂ) * n) s =
        LSeries (fun n : ℕ => (A n : ℂ) - (A (n - 1) : ℂ)) s := by
  let u (n : ℕ) : ℂ := (A n : ℂ) - (c : ℂ) * n
  have h₁ := summable_weight u hu s hs
  have h₂ := summable_weight_shift u hu s hs
  have hd : Summable (fun n : ℕ => (u (n + 1) - u n) * ((n + 1 : ℕ) : ℂ) ^ (-s)) := by
    simpa only [sub_mul] using h₁.sub h₂
  have hp := (summable_powers s (by linarith)).mul_left (c : ℂ)
  have heq : (fun n : ℕ => ((A (n + 1) : ℂ) - (A n : ℂ)) * ((n + 1 : ℕ) : ℂ) ^ (-s)) =
      fun n : ℕ => (c : ℂ) * ((n + 1 : ℕ) : ℂ) ^ (-s) +
        (u (n + 1) - u n) * ((n + 1 : ℕ) : ℂ) ^ (-s) := by
    funext n
    dsimp [u]
    push_cast
    ring
  have hsum : Summable (fun n : ℕ => ((A (n + 1) : ℂ) - (A n : ℂ)) * ((n + 1 : ℕ) : ℂ) ^ (-s)) := by
    rw [heq]
    exact hp.add hd
  have ht : LSeriesSummable (fun n : ℕ => (A n : ℂ) - (A (n - 1) : ℂ)) s := by
    apply (summable_nat_add_iff 1).mp
    simpa [LSeries.term, Complex.cpow_neg, div_eq_mul_inv] using hsum
  have hz : riemannZeta s = ∑' n : ℕ, ((n + 1 : ℕ) : ℂ) ^ (-s) := by
    simpa only [Complex.cpow_neg, one_div, Nat.cast_add, Nat.cast_one] using
      zeta_eq_tsum_one_div_nat_add_one_cpow (by linarith : 1 < s.re)
  rw [transform_eq _ hu s hs]
  change (c : ℂ) * riemannZeta s - (A 0 : ℂ) + (u 0 + _) = _
  rw [show u 0 = (A 0 : ℂ) by simp [u]]
  rw [LSeries, ht.tsum_eq_zero_add]
  simp only [LSeries.term_zero, zero_add, LSeries.term_of_ne_zero (Nat.succ_ne_zero _),
    Nat.succ_eq_add_one, Nat.add_sub_cancel, div_eq_mul_inv, ← Complex.cpow_neg]
  rw [heq, hp.tsum_add hd, tsum_mul_left, ← hz]
  ring

lemma continuation_on (A : ℕ → ℕ) (c : ℝ)
    (hu : (fun n : ℕ => (A n : ℂ) - (c : ℂ) * n) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (1 / 4 : ℝ)))
    (hseries : ∀ s : ℂ, 1 < s.re →
      LSeries (fun n : ℕ => (A n : ℂ) - (A (n - 1) : ℂ)) s *
        riemannZeta (2 * s) = riemannZeta s)
    {U : Set ℂ} (hUo : IsOpen U) (hUc : Convex ℝ U)
    (hU : ∀ z ∈ U, 1 / 4 < z.re ∧ z.im ≠ 0)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) (hz₀re : 2 < z₀.re) :
    Set.EqOn (fun s : ℂ => ((c : ℂ) * riemannZeta s - (A 0 : ℂ) +
      transform (fun n : ℕ => (A n : ℂ) - (c : ℂ) * n) s) *
        riemannZeta (2 * s)) riemannZeta U := by
  have hz (z : ℂ) (hz : z ∈ U) : z ≠ 1 := by
    intro heq
    exact (hU z hz).2 (by simp [heq])
  have h2z (z : ℂ) (hz : z ∈ U) : 2 * z ≠ 1 := by
    intro heq
    have hi := congrArg Complex.im heq
    norm_num [Complex.mul_im] at hi
    exact (hU z hz).2 (by linarith)
  have hF : DifferentiableOn ℂ (fun s : ℂ =>
      ((c : ℂ) * riemannZeta s - (A 0 : ℂ) +
        transform (fun n : ℕ => (A n : ℂ) - (c : ℂ) * n) s) *
          riemannZeta (2 * s)) U := by
    intro z hmem
    have hζ := differentiableAt_riemannZeta (hz z hmem)
    have hζ2 : DifferentiableAt ℂ (fun s : ℂ => riemannZeta (2 * s)) z :=
      (differentiableAt_riemannZeta (h2z z hmem)).comp z
        (differentiableAt_id.const_mul 2)
    exact ((((hζ.const_mul (c : ℂ)).sub_const (A 0 : ℂ)).add
      (differentiableAt_transform _ hu z (hU z hmem).1)).mul hζ2).differentiableWithinAt
  have hG : DifferentiableOn ℂ riemannZeta U := fun z hmem =>
    (differentiableAt_riemannZeta (hz z hmem)).differentiableWithinAt
  refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    (hF.analyticOnNhd hUo) (hG.analyticOnNhd hUo) hUc.isPreconnected hz₀ ?_
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz₀re] with z hzr
  rw [identity_right A c hu z hzr]
  exact hseries z (by linarith)

lemma continuation (A : ℕ → ℕ) (c : ℝ)
    (hu : (fun n : ℕ => (A n : ℂ) - (c : ℂ) * n) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (1 / 4 : ℝ)))
    (hseries : ∀ s : ℂ, 1 < s.re →
      LSeries (fun n : ℕ => (A n : ℂ) - (A (n - 1) : ℂ)) s *
        riemannZeta (2 * s) = riemannZeta s)
    (s : ℂ) (hs : 1 / 4 < s.re) (him : s.im ≠ 0) :
    ((c : ℂ) * riemannZeta s - (A 0 : ℂ) +
      transform (fun n : ℕ => (A n : ℂ) - (c : ℂ) * n) s) *
        riemannZeta (2 * s) = riemannZeta s := by
  rcases lt_or_gt_of_ne him with hneg | hpos
  · let U : Set ℂ := {z | 1 / 4 < z.re} ∩ {z | z.im < 0}
    have hUo : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_im continuous_const)
    have hUc : Convex ℝ U := (convex_halfSpace_re_gt _).inter
      (convex_halfSpace_im_lt _)
    exact continuation_on A c hu hseries hUo hUc
      (fun _ hz => ⟨hz.1, ne_of_lt hz.2⟩)
      (z₀ := 3 - Complex.I) ⟨by norm_num, by norm_num⟩ (by norm_num) ⟨hs, hneg⟩
  · let U : Set ℂ := {z | 1 / 4 < z.re} ∩ {z | 0 < z.im}
    have hUo : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
    have hUc : Convex ℝ U := (convex_halfSpace_re_gt _).inter
      (convex_halfSpace_im_gt _)
    exact continuation_on A c hu hseries hUo hUc
      (fun _ hz => ⟨hz.1, ne_of_gt hz.2⟩)
      (z₀ := 3 + Complex.I) ⟨by norm_num, by norm_num⟩ (by norm_num) ⟨hs, hpos⟩

end AbelianContinuation

theorem OMA.solution : OMA.R_Erdos969_erdos_969_variants_evelyn_linfoot_R1_H3_R1.H1 := by
  intro A c hbound hseries s hs him
  have hu : (fun n : ℕ => (A n : ℂ) - (c : ℂ) * n) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (1 / 4 : ℝ)) := by
    apply IsBigO.of_norm_left
    simpa only [← Complex.ofReal_natCast, ← Complex.ofReal_mul, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs] using hbound
  simpa only [AbelianContinuation.transform, Complex.ofReal_sub, Complex.ofReal_mul,
    Complex.ofReal_natCast] using AbelianContinuation.continuation A c hu hseries s hs him
