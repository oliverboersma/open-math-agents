import FormalConjectures.ErdosProblems.«509»

/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 The LeanProofs contributors. All rights reserved.
Released under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).

Christian Pommerenke proved the enclosure theorem. The weighted Jensen estimate and parts of
its projection argument follow the LeanProofs formalization of Erdős 1046 by Codex and GPT-5.6 Sol.
Source files at revision 8822f7ddef30fadbd92e1c6ab4ed897af356af5e:
https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1046/Erdos1046Jensen.lean
https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1046.lean

Modified for the connected closed sublevel set in Erdős 509. The finite extrema of the
projected roots and the selected point belong to the projected set, including its boundary.
The single closed disk centered at the root centroid gives the required indexed cover.
See also Pommerenke, On metric properties of complex polynomials, Theorem 10 (1961),
https://doi.org/10.1307/mmj/1028998561.
-/

namespace PommerenkeRootEnclosure

noncomputable section

open Complex Filter Metric Real Set Topology
open scoped ComplexConjugate Topology

namespace JensenWeight

noncomputable def unitLift (t : ℝ) : ℂ := t + I * Real.sqrt (1 - t ^ 2)

@[simp] lemma unitLift_re (t : ℝ) : (unitLift t).re = t := by
  simp [unitLift]

lemma norm_unitLift {t : ℝ} (ht : |t| ≤ 1) : ‖unitLift t‖ = 1 := by
  have hs := Complex.normSq_ofReal_add_I_mul_sqrt_one_sub ht
  rw [Complex.normSq_eq_norm_sq] at hs
  change ‖unitLift t‖ ^ 2 = 1 at hs
  nlinarith [norm_nonneg (unitLift t)]

lemma conj_mem_unitSphere {z : ℂ} (hz : z ∈ sphere 0 1) : conj z ∈ sphere 0 1 := by
  simpa [mem_sphere_iff_norm] using hz

lemma re_sq_add_im_sq_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) :
    z.re ^ 2 + z.im ^ 2 = 1 := by
  have h := Complex.sq_norm z
  rw [hz, Complex.normSq_apply] at h
  norm_num at h
  nlinarith

lemma mul_sub_conj_eq_two_mul_re_sub {z ρ : ℂ} (hz : ‖z‖ = 1) (hρ : ‖ρ‖ = 1) :
    (z - ρ) * (z - conj ρ) = 2 * z * (z.re - ρ.re) := by
  have hz' := re_sq_add_im_sq_of_norm_eq_one hz
  have hρ' := re_sq_add_im_sq_of_norm_eq_one hρ
  apply Complex.ext <;> simp [mul_re, mul_im] <;> nlinarith

lemma norm_mul_sub_conj {z ρ : ℂ} (hz : ‖z‖ = 1) (hρ : ‖ρ‖ = 1) :
    ‖z - ρ‖ * ‖z - conj ρ‖ = 2 * |z.re - ρ.re| := by
  rw [← Complex.norm_mul, mul_sub_conj_eq_two_mul_re_sub hz hρ, norm_mul, norm_mul]
  have hc : ((z.re : ℂ) - ρ.re) = ((z.re - ρ.re : ℝ) : ℂ) := by norm_num
  rw [hc, Complex.norm_real, Real.norm_eq_abs]
  norm_num [hz]

lemma eq_or_eq_conj_of_re_eq_of_norm_eq_one {z ρ : ℂ} (hz : ‖z‖ = 1) (hρ : ‖ρ‖ = 1)
    (hre : z.re = ρ.re) : z = ρ ∨ z = conj ρ := by
  have hz' := re_sq_add_im_sq_of_norm_eq_one hz
  have hρ' := re_sq_add_im_sq_of_norm_eq_one hρ
  have hs : z.im ^ 2 = ρ.im ^ 2 := by
    rw [hre] at hz'
    nlinarith [hz', hρ']
  have him : z.im = ρ.im ∨ z.im = -ρ.im := sq_eq_sq_iff_eq_or_eq_neg.mp hs
  rcases him with him | him
  · left
    apply Complex.ext <;> simp_all
  · right
    apply Complex.ext <;> simp_all

def exceptional {n : ℕ} (ρ : Fin n → ℂ) : Set ℂ :=
  Set.range ρ ∪ Set.range (fun i ↦ conj (ρ i))

lemma exceptional_finite {n : ℕ} (ρ : Fin n → ℂ) : (exceptional ρ).Finite := by
  exact (Set.finite_range ρ).union (Set.finite_range fun i ↦ conj (ρ i))

lemma re_ne_of_notMem_exceptional {n : ℕ} {ρ : Fin n → ℂ} {z : ℂ}
    (hz : ‖z‖ = 1) (hρ : ∀ i, ‖ρ i‖ = 1) (hex : z ∉ exceptional ρ) (i : Fin n) :
    z.re ≠ (ρ i).re := by
  intro hre
  rcases eq_or_eq_conj_of_re_eq_of_norm_eq_one hz (hρ i) hre with h | h
  · exact hex (Or.inl ⟨i, h.symm⟩)
  · exact hex (Or.inr ⟨i, h.symm⟩)

noncomputable def logBoundary {n : ℕ} (h : ℝ) (ρ : Fin n → ℂ) (z : ℂ) : ℝ :=
  n * Real.log (h / 2) +
    ∑ i, (Real.log ‖z - ρ i‖ + Real.log ‖z - conj (ρ i)‖)

noncomputable def kernel (r : ℝ) (z : ℂ) : ℝ :=
  (herglotzRieszKernel 0 (r : ℂ) z).re

def kernelLower (r : ℝ) : ℝ := (1 - r) / (1 + r)

noncomputable def weight (r : ℝ) (z : ℂ) : ℝ := kernel r z - kernelLower r

lemma circleIntegrable_logBoundary {n : ℕ} (h : ℝ) (ρ : Fin n → ℂ) :
    CircleIntegrable (logBoundary h ρ) 0 1 := by
  let F : ℂ → ℝ := (fun _ ↦ n * Real.log (h / 2)) +
    ∑ i, (fun z ↦ Real.log ‖z - ρ i‖ + Real.log ‖z - conj (ρ i)‖)
  have hs : CircleIntegrable
      (∑ i, (fun z ↦ Real.log ‖z - ρ i‖ + Real.log ‖z - conj (ρ i)‖)) 0 1 := by
    apply CircleIntegrable.sum Finset.univ
    intro i hi
    exact (circleIntegrable_log_norm_sub_const 1).add
      (circleIntegrable_log_norm_sub_const 1)
  have hF : CircleIntegrable F 0 1 :=
    (circleIntegrable_const (n * Real.log (h / 2)) 0 1).add hs
  exact (circleIntegrable_congr (c := 0) (R := 1) (f₁ := logBoundary h ρ) (f₂ := F)
    (by intro z hz; simp [F, logBoundary])).2 hF

lemma circleAverage_logBoundary {n : ℕ} (h : ℝ) (ρ : Fin n → ℂ)
    (hρ : ∀ i, ‖ρ i‖ = 1) :
    circleAverage (logBoundary h ρ) 0 1 = n * Real.log (h / 2) := by
  let B : Fin n → ℂ → ℝ := fun i z ↦
    Real.log ‖z - ρ i‖ + Real.log ‖z - conj (ρ i)‖
  have hB (i : Fin n) : CircleIntegrable (B i) 0 1 :=
    (circleIntegrable_log_norm_sub_const 1).add
      (circleIntegrable_log_norm_sub_const 1)
  have hsum : CircleIntegrable (fun z ↦ ∑ i, B i z) 0 1 := by
    have hs : CircleIntegrable (∑ i, B i) 0 1 :=
      CircleIntegrable.sum Finset.univ (fun i _ ↦ hB i)
    exact (circleIntegrable_congr (c := 0) (R := 1)
      (f₁ := fun z ↦ ∑ i, B i z) (f₂ := ∑ i, B i)
      (by intro z hz; simp)).2 hs
  rw [show logBoundary h ρ = fun z ↦ n * Real.log (h / 2) + ∑ i, B i z by
    funext z; simp [logBoundary, B]]
  rw [circleAverage_fun_add (circleIntegrable_const _ _ _) hsum,
    circleAverage_const, circleAverage_fun_sum (fun i _ ↦ hB i)]
  have hzero (i : Fin n) : circleAverage (B i) 0 1 = 0 := by
    rw [show B i = fun z ↦ Real.log ‖z - ρ i‖ + Real.log ‖z - conj (ρ i)‖ by
      rfl]
    rw [circleAverage_fun_add (circleIntegrable_log_norm_sub_const 1)
      (circleIntegrable_log_norm_sub_const 1)]
    rw [circleAverage_log_norm_sub_const₁ (hρ i),
      circleAverage_log_norm_sub_const₁ (by simpa using hρ i)]
    simp
  simp_rw [hzero]
  simp

def quadratic (r t : ℝ) : ℝ := 1 - 2 * t * r + r ^ 2

lemma sub_mul_sub_conj_of_norm_eq_one {r : ℝ} {z : ℂ} (hz : ‖z‖ = 1) :
    ((r : ℂ) - z) * ((r : ℂ) - conj z) = (quadratic r z.re : ℝ) := by
  apply Complex.ext
  · simp only [mul_re, sub_re, ofReal_re, conj_re, sub_im, ofReal_im, conj_im,
      zero_sub, neg_mul, mul_neg, quadratic]
    have hz' := re_sq_add_im_sq_of_norm_eq_one hz
    ring_nf
    nlinarith
  · simp [mul_im]
    ring

lemma quadratic_pos {r t : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (ht : |t| ≤ 1) :
    0 < quadratic r t := by
  rw [abs_le] at ht
  dsimp [quadratic]
  nlinarith [sq_nonneg (1 - r), mul_nonneg hr0 (sub_nonneg.mpr ht.2)]

lemma log_norm_sub_add_log_norm_sub_conj {r : ℝ} {z : ℂ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hz : ‖z‖ = 1) :
    Real.log ‖(r : ℂ) - z‖ + Real.log ‖(r : ℂ) - conj z‖ =
      Real.log (quadratic r z.re) := by
  have hzr : (r : ℂ) ≠ z := by
    intro heq
    have := congrArg norm heq
    simp [hz, abs_of_nonneg hr0] at this
    linarith
  have hzcr : (r : ℂ) ≠ conj z := by
    intro heq
    have := congrArg norm heq
    simp [hz, abs_of_nonneg hr0] at this
    linarith
  rw [← Real.log_mul (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hzr))
      (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hzcr)),
    ← Complex.norm_mul, sub_mul_sub_conj_of_norm_eq_one hz, Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_pos (quadratic_pos hr0 hr1 (by simpa [hz] using Complex.abs_re_le_norm z))]

lemma circleAverage_kernel_mul_log {r : ℝ} {z : ℂ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hz : ‖z‖ = 1) :
    circleAverage (fun w ↦ kernel r w * Real.log ‖w - z‖) 0 1 =
      Real.log ‖(r : ℂ) - z‖ := by
  apply circleAverage_re_herglotzRieszKernel_mul_log
  · simpa [mem_sphere_iff_norm] using hz
  · simp [abs_of_nonneg hr0, hr1]

lemma circleAverage_kernel {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    circleAverage (kernel r) 0 1 = 1 := by
  have hw : (r : ℂ) ∈ ball 0 1 := by
    simp [abs_of_nonneg hr0, hr1]
  have hf : InnerProductSpace.HarmonicContOnCl (fun _ : ℂ ↦ (1 : ℝ)) (ball 0 1) :=
    InnerProductSpace.harmonicContOnCl_const
  change circleAverage (fun z ↦ kernel r z) 0 1 = 1
  have heq : (fun z ↦ kernel r z) =
      ((Complex.re ∘ herglotzRieszKernel 0 (r : ℂ)) • (fun _ : ℂ ↦ (1 : ℝ))) := by
    funext z
    simp [kernel]
  rw [heq]
  exact hf.circleAverage_re_herglotzRieszKernel_smul hw

lemma continuousOn_kernel {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ContinuousOn (kernel r) (sphere 0 |(1 : ℝ)|) := by
  have hw : (r : ℂ) ∈ ball 0 1 := by
    simp [abs_of_nonneg hr0, hr1]
  exact Complex.continuous_re.comp_continuousOn
    (continuousOn_herglotzRieszKernel_sphere hw)

lemma circleAverage_kernel_mul_logBoundary {n : ℕ} {r h : ℝ} (ρ : Fin n → ℂ)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hρ : ∀ i, ‖ρ i‖ = 1) :
    circleAverage (fun z ↦ kernel r z * logBoundary h ρ z) 0 1 =
      n * Real.log (h / 2) + ∑ i, Real.log (quadratic r (ρ i).re) := by
  let A : ℝ := n * Real.log (h / 2)
  let B : Fin n → ℂ → ℝ := fun i z ↦
    Real.log ‖z - ρ i‖ + Real.log ‖z - conj (ρ i)‖
  have hB (i : Fin n) : CircleIntegrable (B i) 0 1 :=
    (circleIntegrable_log_norm_sub_const 1).add
      (circleIntegrable_log_norm_sub_const 1)
  have hk := continuousOn_kernel hr0 hr1
  have hkB (i : Fin n) : CircleIntegrable (fun z ↦ kernel r z * B i z) 0 1 :=
    (hB i).continuousOn_mul hk
  rw [show (fun z ↦ kernel r z * logBoundary h ρ z) =
      (fun z ↦ kernel r z * A) + ∑ i, (fun z ↦ kernel r z * B i z) by
    ext z
    simp [A, B, logBoundary, mul_add, Finset.mul_sum]]
  have hKA : CircleIntegrable (fun z ↦ kernel r z * A) 0 1 :=
    (hk.circleIntegrable').mul_continuousOn continuousOn_const
  have hKS : CircleIntegrable (∑ i, (fun z ↦ kernel r z * B i z)) 0 1 :=
    CircleIntegrable.sum Finset.univ (fun i _ ↦ hkB i)
  rw [circleAverage_add (f₁ := fun z ↦ kernel r z * A)
      (f₂ := ∑ i, (fun z ↦ kernel r z * B i z)) hKA hKS,
    circleAverage_sum (fun i _ ↦ hkB i)]
  have hconst : circleAverage (fun z ↦ kernel r z * A) 0 1 = A := by
    rw [circleAverage_congr_sphere (f₂ := fun z ↦ A • kernel r z) (by intro z hz; simp [mul_comm]),
      circleAverage_fun_smul, circleAverage_kernel hr0 hr1, smul_eq_mul, mul_one]
  rw [hconst]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [show (fun z ↦ kernel r z * B i z) =
      (fun z ↦ kernel r z * Real.log ‖z - ρ i‖) +
        (fun z ↦ kernel r z * Real.log ‖z - conj (ρ i)‖) by
    ext z; simp [B, mul_add]]
  rw [circleAverage_add
      (f₁ := fun z ↦ kernel r z * Real.log ‖z - ρ i‖)
      (f₂ := fun z ↦ kernel r z * Real.log ‖z - conj (ρ i)‖)
      ((circleIntegrable_log_norm_sub_const 1).continuousOn_mul hk)
      ((circleIntegrable_log_norm_sub_const 1).continuousOn_mul hk),
    circleAverage_kernel_mul_log hr0 hr1 (hρ i),
    circleAverage_kernel_mul_log hr0 hr1 (by simpa using hρ i),
    log_norm_sub_add_log_norm_sub_conj hr0 hr1 (hρ i)]

lemma continuousOn_weight {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ContinuousOn (weight r) (sphere 0 |(1 : ℝ)|) := by
  exact (continuousOn_kernel hr0 hr1).sub continuousOn_const

lemma circleAverage_weight_mul_logBoundary {n : ℕ} {r h : ℝ} (ρ : Fin n → ℂ)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hρ : ∀ i, ‖ρ i‖ = 1) :
    circleAverage (fun z ↦ weight r z * logBoundary h ρ z) 0 1 =
      (1 - kernelLower r) * (n * Real.log (h / 2)) +
        ∑ i, Real.log (quadratic r (ρ i).re) := by
  have hL := circleIntegrable_logBoundary h ρ
  have hk := continuousOn_kernel hr0 hr1
  rw [show (fun z ↦ weight r z * logBoundary h ρ z) =
      (fun z ↦ kernel r z * logBoundary h ρ z) -
        (fun z ↦ kernelLower r * logBoundary h ρ z) by
    ext z; simp [weight]; ring]
  have hkL : CircleIntegrable (fun z ↦ kernel r z * logBoundary h ρ z) 0 1 :=
    hL.continuousOn_mul hk
  have hcL : CircleIntegrable (fun z ↦ kernelLower r * logBoundary h ρ z) 0 1 :=
    hL.const_smul
  have hcavg : circleAverage (fun z ↦ kernelLower r * logBoundary h ρ z) 0 1 =
      kernelLower r * circleAverage (logBoundary h ρ) 0 1 := by
    change circleAverage (fun z ↦ kernelLower r • logBoundary h ρ z) 0 1 = _
    rw [circleAverage_fun_smul]
    rfl
  rw [circleAverage_sub (f₁ := fun z ↦ kernel r z * logBoundary h ρ z)
      (f₂ := fun z ↦ kernelLower r * logBoundary h ρ z) hkL hcL,
    circleAverage_kernel_mul_logBoundary ρ hr0 hr1 hρ,
    hcavg, circleAverage_logBoundary h ρ hρ]
  ring

lemma weight_nonneg_on_unitSphere {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {z : ℂ} (hz : z ∈ sphere 0 1) : 0 ≤ weight r z := by
  have hw : (r : ℂ) ∈ ball 0 1 := by
    simp [abs_of_nonneg hr0, hr1]
  have := le_re_herglotzRieszKernel (w := (r : ℂ)) hz hw
  simpa [weight, kernel, kernelLower, herglotzRieszKernel_def, abs_of_nonneg hr0] using this

noncomputable def modifiedLogBoundary {n : ℕ} (h : ℝ) (ρ : Fin n → ℂ) (z : ℂ) : ℝ :=
  by
    classical
    exact if z ∈ exceptional ρ then 0 else logBoundary h ρ z

lemma modifiedLogBoundary_eventuallyEq {n : ℕ} (h : ℝ) (ρ : Fin n → ℂ) :
    modifiedLogBoundary h ρ =ᶠ[codiscreteWithin (sphere 0 |(1 : ℝ)|)] logBoundary h ρ := by
  classical
  filter_upwards [compl_finite_mem_codiscreteWithin (exceptional_finite ρ)] with z hz
  have hzn : z ∉ exceptional ρ := by simpa using hz
  simp [modifiedLogBoundary, hzn]

lemma circleIntegrable_modifiedLogBoundary {n : ℕ} (h : ℝ) (ρ : Fin n → ℂ) :
    CircleIntegrable (modifiedLogBoundary h ρ) 0 1 :=
  (circleIntegrable_logBoundary h ρ).congr_codiscreteWithin
    (modifiedLogBoundary_eventuallyEq h ρ).symm

lemma weighted_boundary_inequality {n : ℕ} {r h : ℝ} (ρ : Fin n → ℂ)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hρ : ∀ i, ‖ρ i‖ = 1)
    (hlog : ∀ z ∈ sphere (0 : ℂ) 1, z ∉ exceptional ρ → logBoundary h ρ z ≤ 0) :
    (1 - kernelLower r) * (n * Real.log (h / 2)) +
        ∑ i, Real.log (quadratic r (ρ i).re) ≤ 0 := by
  have hmod := circleIntegrable_modifiedLogBoundary h ρ
  have hwcont := continuousOn_weight hr0 hr1
  have havg : circleAverage (fun z ↦ weight r z * modifiedLogBoundary h ρ z) 0 1 ≤ 0 := by
    apply circleAverage_mono_on_of_le_circle (hmod.continuousOn_mul hwcont)
    intro z hz
    by_cases he : z ∈ exceptional ρ
    · simp [modifiedLogBoundary, he]
    · exact mul_nonpos_of_nonneg_of_nonpos
        (weight_nonneg_on_unitSphere (r := r) hr0 hr1 (by simpa using hz))
        (by simpa [modifiedLogBoundary, he] using hlog z (by simpa using hz) he)
  rw [circleAverage_congr_codiscreteWithin (hR := one_ne_zero)
      (f₂ := fun z ↦ weight r z * logBoundary h ρ z) (by
        filter_upwards [modifiedLogBoundary_eventuallyEq h ρ] with z hz
        simp [hz]),
    circleAverage_weight_mul_logBoundary ρ hr0 hr1 hρ] at havg
  exact havg

lemma log_abs_re_sub_eq {z ρ : ℂ} (hz : ‖z‖ = 1) (hρ : ‖ρ‖ = 1)
    (hne : z.re ≠ ρ.re) :
    Real.log |z.re - ρ.re| =
      Real.log ‖z - ρ‖ + Real.log ‖z - conj ρ‖ - Real.log 2 := by
  have ha : 0 < |z.re - ρ.re| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have h₁ : z - ρ ≠ 0 := by
    intro he
    apply hne
    simpa using congrArg Complex.re (sub_eq_zero.mp he)
  have h₂ : z - conj ρ ≠ 0 := by
    intro he
    apply hne
    have := congrArg Complex.re (sub_eq_zero.mp he)
    simpa using this
  have heq : |z.re - ρ.re| = (‖z - ρ‖ * ‖z - conj ρ‖) / 2 := by
    rw [norm_mul_sub_conj hz hρ]
    ring
  rw [heq, Real.log_div (mul_ne_zero (norm_ne_zero_iff.mpr h₁)
      (norm_ne_zero_iff.mpr h₂)) two_ne_zero,
    Real.log_mul (norm_ne_zero_iff.mpr h₁) (norm_ne_zero_iff.mpr h₂)]

lemma logBoundary_nonpos_of_prod_le {n : ℕ} {h : ℝ} (ρ : Fin n → ℂ)
    (hh : 0 < h) (hρ : ∀ i, ‖ρ i‖ = 1)
    (hbound : ∀ z ∈ sphere (0 : ℂ) 1,
      h ^ n * ∏ i, |z.re - (ρ i).re| ≤ 1) :
    ∀ z ∈ sphere (0 : ℂ) 1, z ∉ exceptional ρ → logBoundary h ρ z ≤ 0 := by
  intro z hz hex
  have hzn : ‖z‖ = 1 := by simpa [mem_sphere_iff_norm] using hz
  have hne (i : Fin n) : z.re ≠ (ρ i).re :=
    re_ne_of_notMem_exceptional hzn hρ hex i
  have hprodpos : 0 < ∏ i, |z.re - (ρ i).re| := by
    apply Finset.prod_pos
    intro i hi
    exact abs_pos.mpr (sub_ne_zero.mpr (hne i))
  have hlogprod : Real.log (h ^ n * ∏ i, |z.re - (ρ i).re|) ≤ 0 := by
    simpa using Real.log_le_log (mul_pos (pow_pos hh n) hprodpos) (hbound z hz)
  rw [Real.log_mul (pow_ne_zero n hh.ne') (ne_of_gt hprodpos), Real.log_pow,
    Real.log_prod (fun i _ ↦ (abs_ne_zero.mpr (sub_ne_zero.mpr (hne i))))] at hlogprod
  calc
    logBoundary h ρ z = n * Real.log h + ∑ i, Real.log |z.re - (ρ i).re| := by
      simp only [logBoundary]
      rw [Real.log_div hh.ne' two_ne_zero]
      simp_rw [log_abs_re_sub_eq hzn (hρ _) (hne _)]
      simp [Finset.sum_sub_distrib]
      ring
    _ ≤ 0 := hlogprod

lemma tendsto_weighted_log_quadratic (t : ℝ) :
    Tendsto (fun r : ℝ ↦ -(1 + r) / (2 * r) * Real.log (quadratic r t))
      (nhdsWithin 0 (Ioi 0)) (nhds t) := by
  have hq : HasDerivAt (fun r : ℝ ↦ 1 - 2 * r * t + r ^ 2) (-2 * t) 0 := by
    have hone : HasDerivAt (fun _ : ℝ ↦ (1 : ℝ)) 0 0 := hasDerivAt_const 0 1
    have hid : HasDerivAt (fun r : ℝ ↦ r) 1 0 := hasDerivAt_id' 0
    convert! (hone.sub ((hid.const_mul 2).mul_const t)).add (hid.pow 2) using 1
    all_goals ring
  have hlog : HasDerivAt
      (fun r : ℝ ↦ Real.log (1 - 2 * r * t + r ^ 2)) (-2 * t) 0 := by
    have hne : (1 - 2 * (0 : ℝ) * t + 0 ^ 2) ≠ 0 := by norm_num
    convert! (Real.hasDerivAt_log hne).comp 0 hq using 1
    all_goals norm_num
  have hslope : Tendsto
      (fun r : ℝ ↦ r⁻¹ * Real.log (1 - 2 * r * t + r ^ 2))
      (nhdsWithin 0 ({0}ᶜ : Set ℝ)) (nhds (-2 * t)) := by
    simpa [smul_eq_mul] using hlog.tendsto_slope_zero
  have hhalf := hslope.const_mul (1 / 2 : ℝ)
  have heq :
      (fun r : ℝ ↦ (1 / 2 : ℝ) * (r⁻¹ * Real.log (1 - 2 * r * t + r ^ 2)))
        =ᶠ[nhdsWithin 0 ({0}ᶜ : Set ℝ)]
      (fun r : ℝ ↦ Real.log (1 - 2 * r * t + r ^ 2) / (2 * r)) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hr
    field_simp
  have hbase : Tendsto
      (fun r : ℝ ↦ Real.log (1 - 2 * r * t + r ^ 2) / (2 * r))
      (nhdsWithin 0 ({0}ᶜ : Set ℝ)) (nhds (-t)) := by
    convert hhalf.congr' heq using 1
    all_goals ring_nf
  have hbaseR := hbase.mono_left (nhdsGT_le_nhdsNE (0 : ℝ))
  have hfac0 : Tendsto (fun r : ℝ ↦ -(1 + r)) (nhds 0) (nhds (-1)) := by
    have hc : ContinuousAt (fun r : ℝ ↦ -(1 + r)) 0 := by fun_prop
    have ht : Tendsto (fun r : ℝ ↦ -(1 + r)) (nhds 0)
        (nhds (-(1 + (0 : ℝ)))) := hc
    simpa using ht
  have hfac : Tendsto (fun r : ℝ ↦ -(1 + r)) (nhdsWithin 0 (Ioi 0)) (nhds (-1)) :=
    hfac0.mono_left
      (show nhdsWithin (0 : ℝ) (Ioi 0) ≤ nhds 0 from nhdsWithin_le_nhds)
  have hout := hfac.mul hbaseR
  have hevent :
      (fun r : ℝ ↦ -(1 + r) *
          (Real.log (1 - 2 * r * t + r ^ 2) / (2 * r))) =ᶠ[nhdsWithin 0 (Ioi 0)]
        (fun r : ℝ ↦ -(1 + r) / (2 * r) * Real.log (quadratic r t)) := by
    filter_upwards with r
    rw [quadratic]
    ring_nf
  have htarget := hout.congr' hevent
  convert htarget using 1
  all_goals ring_nf

theorem weighted_jensen {n : ℕ} (hn : 0 < n) {h : ℝ} (hh : 0 < h) (ρ : Fin n → ℂ)
    (hρ : ∀ i, ‖ρ i‖ = 1)
    (hbound : ∀ z ∈ sphere (0 : ℂ) 1,
      h ^ n * ∏ i, |z.re - (ρ i).re| ≤ 1) :
    Real.log (h / 2) ≤ (∑ i, (ρ i).re) / n := by
  let G : ℝ → ℝ := fun r ↦
    (∑ i, (-(1 + r) / (2 * r) * Real.log (quadratic r (ρ i).re))) / n
  have hG : Tendsto G (nhdsWithin 0 (Ioi 0)) (nhds ((∑ i, (ρ i).re) / n)) := by
    apply Tendsto.div_const
    exact tendsto_finsetSum Finset.univ (fun i _ ↦ tendsto_weighted_log_quadratic (ρ i).re)
  apply ge_of_tendsto hG
  have hIio : Iio (1 : ℝ) ∈ nhdsWithin 0 (Ioi 0) :=
    mem_of_superset (inter_mem_nhdsWithin _ (Iio_mem_nhds zero_lt_one)) inter_subset_right
  filter_upwards [self_mem_nhdsWithin, hIio] with r hr0 hr1
  have hr0' : 0 < r := hr0
  have hineq := weighted_boundary_inequality ρ hr0'.le hr1 hρ
    (logBoundary_nonpos_of_prod_le ρ hh hρ hbound)
  have hk : 1 - kernelLower r = 2 * r / (1 + r) := by
    dsimp [kernelLower]
    field_simp
    ring
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hden : 0 < (1 - kernelLower r) * (n : ℝ) := by
    rw [hk]
    positivity
  have hfirst : Real.log (h / 2) ≤
      -(∑ i, Real.log (quadratic r (ρ i).re)) /
        ((1 - kernelLower r) * (n : ℝ)) := by
    rw [le_div_iff₀ hden]
    nlinarith
  calc
    Real.log (h / 2) ≤
        -(∑ i, Real.log (quadratic r (ρ i).re)) /
          ((1 - kernelLower r) * (n : ℝ)) := hfirst
    _ = G r := by
      dsimp [G]
      rw [hk]
      field_simp
      calc
        -((∑ i, Real.log (quadratic r (ρ i).re)) * (1 + r)) =
            ∑ i, -(Real.log (quadratic r (ρ i).re) * (1 + r)) := by
          rw [Finset.sum_mul, Finset.sum_neg_distrib]
        _ = 2 * r * ∑ i, -((1 + r) * Real.log (quadratic r (ρ i).re) / (2 * r)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          field_simp

/--
Weighted Jensen estimate used in Pommerenke's radius-two argument.  The family `t` is a finite
multiset represented by `Fin n → ℝ`.
-/
theorem weighted_jensen_real {n : ℕ} (hn : 0 < n) {h : ℝ} (hh : 0 < h)
    (t : Fin n → ℝ) (ht : ∀ i, |t i| ≤ 1)
    (hbound : ∀ z ∈ sphere (0 : ℂ) 1,
      h ^ n * ∏ i, |z.re - t i| ≤ 1) :
    Real.log (h / 2) ≤ (∑ i, t i) / n := by
  let ρ : Fin n → ℂ := fun i ↦ unitLift (t i)
  have hρ : ∀ i, ‖ρ i‖ = 1 := fun i ↦ norm_unitLift (ht i)
  simpa [ρ] using weighted_jensen hn hh ρ hρ (by simpa [ρ] using hbound)

/-- A monic product with real roots in an interval and bounded by one has its right endpoint
at distance at most two from the average of its roots. -/
theorem right_endpoint_sub_average_le_two {n : ℕ} (hn : 0 < n) {A B : ℝ} (hAB : A < B)
    (x : Fin n → ℝ) (hx : ∀ i, x i ∈ Icc A B)
    (hbound : ∀ y ∈ Icc A B, ∏ i, |y - x i| ≤ 1) :
    B - (∑ i, x i) / n ≤ 2 := by
  let h : ℝ := (B - A) / 2
  let m : ℝ := (A + B) / 2
  let t : Fin n → ℝ := fun i ↦ (x i - m) / h
  have hh : 0 < h := by dsimp [h]; linarith
  have ht : ∀ i, |t i| ≤ 1 := by
    intro i
    rw [abs_le]
    have hi := hx i
    dsimp [t, m, h]
    constructor
    · rw [le_div_iff₀ (by linarith)]
      linarith [hi.1, hi.2]
    · rw [div_le_iff₀ (by linarith)]
      linarith [hi.1, hi.2]
  have hfac (z : ℂ) (i : Fin n) :
      h * |z.re - t i| = |m + h * z.re - x i| := by
    calc
      h * |z.re - t i| = |h| * |z.re - t i| := by rw [abs_of_pos hh]
      _ = |h * (z.re - t i)| := (abs_mul _ _).symm
      _ = |m + h * z.re - x i| := by
        congr 1
        dsimp [t]
        field_simp [hh.ne']
        ring
  have hcircle : ∀ z ∈ sphere (0 : ℂ) 1,
      h ^ n * ∏ i, |z.re - t i| ≤ 1 := by
    intro z hz
    have hz_norm : ‖z‖ = 1 := by simpa [mem_sphere_iff_norm] using hz
    have hz_re : |z.re| ≤ 1 := by simpa [hz_norm] using Complex.abs_re_le_norm z
    have hy : m + h * z.re ∈ Icc A B := by
      rw [abs_le] at hz_re
      dsimp [m, h]
      constructor <;> nlinarith
    calc
      h ^ n * ∏ i, |z.re - t i| = ∏ i, (h * |z.re - t i|) := by
        rw [Finset.prod_mul_distrib]
        simp
      _ = ∏ i, |m + h * z.re - x i| := by
        apply Finset.prod_congr rfl
        intro i hi
        exact hfac z i
      _ ≤ 1 := hbound _ hy
  have hJ := weighted_jensen_real hn hh t ht hcircle
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have havg : (∑ i, t i) / (n : ℝ) = ((∑ i, x i) / (n : ℝ) - m) / h := by
    dsimp [t]
    rw [← Finset.sum_div]
    field_simp
    simp [Finset.sum_sub_distrib]
    ring
  rw [havg] at hJ
  have hdist : B - (∑ i, x i) / (n : ℝ) ≤ h * (1 - Real.log (h / 2)) := by
    have hBm : B = m + h := by dsimp [m, h]; ring
    rw [hBm]
    rw [le_div_iff₀ hh] at hJ
    nlinarith
  have hs : 0 < h / 2 := by positivity
  have hlog := Real.one_sub_inv_le_log_of_pos hs
  calc
    B - (∑ i, x i) / (n : ℝ) ≤ h * (1 - Real.log (h / 2)) := hdist
    _ ≤ h * (1 - (1 - (h / 2)⁻¹)) := by gcongr
    _ = 2 := by field_simp; ring

end JensenWeight

end

open Metric Polynomial Set
open scoped BigOperators ComplexConjugate

/-- The mean of the complex roots, with multiplicity. -/
noncomputable def rootCentroid (f : ℂ[X]) : ℂ := f.roots.sum / (f.natDegree : ℂ)

/-- The real coordinate in direction `u`; the estimates use a unit vector. -/
def projection (u z : ℂ) : ℝ := (conj u * z).re

lemma continuous_projection (u : ℂ) : Continuous (projection u) :=
  Complex.continuous_re.comp (continuous_const.mul continuous_id)

lemma projection_sub_le_norm (u w r : ℂ) (hu : ‖u‖ = 1) :
    |projection u w - projection u r| ≤ ‖w - r‖ := by
  calc
    |projection u w - projection u r| = |(conj u * (w - r)).re| := by
      simp only [projection, mul_sub, Complex.sub_re]
    _ ≤ ‖conj u * (w - r)‖ := Complex.abs_re_le_norm _
    _ = ‖w - r‖ := by simp [hu]

lemma projection_rootCentroid (f : ℂ[X]) (u : ℂ) :
    (f.roots.map (projection u)).sum / (f.roots.card : ℝ) = projection u (rootCentroid f) := by
  let p : ℂ →+ ℝ :=
    { toFun := projection u
      map_zero' := by simp [projection]
      map_add' := by intro a b; simp [projection, mul_add] }
  have hs : (f.roots.map (projection u)).sum = projection u f.roots.sum :=
    (map_multiset_sum p f.roots).symm
  rw [hs, ← (IsAlgClosed.splits f).natDegree_eq_card_roots]
  simp only [projection, rootCentroid, mul_div_assoc']
  rw [show (f.natDegree : ℂ) = ((f.natDegree : ℝ) : ℂ) by norm_cast]
  rw [Complex.div_ofReal_re]

lemma fin_prod_multiset_occurrences {α β : Type*} [DecidableEq α] [CommMonoid β]
    (m : Multiset α) (g : α → β) :
    (∏ i : Fin (Fintype.card m), g (((Fintype.equivFin m).symm i : m) : α)) =
      (m.map g).prod := by
  calc
    _ = ∏ j : m, g (j : α) :=
      Fintype.prod_equiv (Fintype.equivFin m).symm _ _ (fun _ => rfl)
    _ = _ := by
      change ((Finset.univ : Finset m).val.map (fun j : m => g (j : α))).prod = _
      exact congrArg Multiset.prod (Multiset.map_univ m g)

lemma fin_sum_multiset_occurrences {α β : Type*} [DecidableEq α] [AddCommMonoid β]
    (m : Multiset α) (g : α → β) :
    (∑ i : Fin (Fintype.card m), g (((Fintype.equivFin m).symm i : m) : α)) =
      (m.map g).sum := by
  calc
    _ = ∑ j : m, g (j : α) :=
      Fintype.sum_equiv (Fintype.equivFin m).symm _ _ (fun _ => rfl)
    _ = _ := by
      change ((Finset.univ : Finset m).val.map (fun j : m => g (j : α))).sum = _
      exact congrArg Multiset.sum (Multiset.map_univ m g)

/-- The same interval estimate covers a singleton interval, in which every root equals `B`. -/
lemma endpoint_bound {n : ℕ} (hn : 0 < n) {A B : ℝ} (x : Fin n → ℝ)
    (hx : ∀ i, x i ∈ Icc A B) (hp : ∀ y ∈ Icc A B, ∏ i, |y - x i| ≤ 1) :
    B - (∑ i, x i) / (n : ℝ) ≤ 2 := by
  by_cases hAB : A < B
  · exact JensenWeight.right_endpoint_sub_average_le_two hn hAB x hx hp
  · have heq (i) : x i = B := le_antisymm (hx i).2 ((le_of_not_gt hAB).trans (hx i).1)
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    simp [heq, nsmul_eq_mul, hn']

/-- Projecting a connected closed sublevel set fills the interval between its sampled extrema. -/
lemma projection_sub_centroid_le_two (f : ℂ[X]) (hf : f.Monic) (hdeg : f.natDegree ≠ 0)
    (hE : IsConnected {w : ℂ | ‖f.eval w‖ ≤ 1}) {z : ℂ} (hz : ‖f.eval z‖ ≤ 1)
    (u : ℂ) (hu : ‖u‖ = 1) : projection u z - projection u (rootCentroid f) ≤ 2 := by
  classical
  let e : Fin (Fintype.card f.roots) ≃ f.roots := (Fintype.equivFin f.roots).symm
  let x : Fin (Fintype.card f.roots) → ℝ := fun i ↦ projection u (e i : ℂ)
  let T := insert (projection u z) (Finset.univ.image x)
  have hzT : projection u z ∈ T := Finset.mem_insert_self _ _
  have hT : T.Nonempty := ⟨_, hzT⟩
  have hxT (i) : x i ∈ T := Finset.mem_insert_of_mem (Finset.mem_image_of_mem x (Finset.mem_univ i))
  have hT_image (t) (ht : t ∈ T) : t ∈ projection u '' {w : ℂ | ‖f.eval w‖ ≤ 1} := by
    rcases Finset.mem_insert.mp ht with h | h
    · exact ⟨z, hz, h.symm⟩
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h
      have hr : f.eval (e i : ℂ) = 0 :=
        (Polynomial.mem_roots hf.ne_zero).mp (Multiset.coe_mem (x := e i))
      exact ⟨(e i : ℂ), by simp [hr], rfl⟩
  let A := T.min' hT
  let B := T.max' hT
  have hIcc := (hE.image _ (continuous_projection u).continuousOn).Icc_subset
    (hT_image A (Finset.min'_mem T hT)) (hT_image B (Finset.max'_mem T hT))
  have hx (i) : x i ∈ Icc A B := ⟨T.min'_le _ (hxT i), T.le_max' _ (hxT i)⟩
  have hp (y) (hy : y ∈ Icc A B) : ∏ i, |y - x i| ≤ 1 := by
    obtain ⟨w, hw, rfl⟩ := hIcc hy
    calc
      ∏ i, |projection u w - x i| ≤ ∏ i, ‖w - (e i : ℂ)‖ :=
        Finset.prod_le_prod (fun _ _ ↦ abs_nonneg _) (fun i _ ↦ projection_sub_le_norm _ _ _ hu)
      _ = ‖∏ i, (w - (e i : ℂ))‖ := (norm_prod _ _).symm
      _ = ‖f.eval w‖ := by
        rw [(IsAlgClosed.splits f).eval_eq_prod_roots_of_monic hf w]
        exact congrArg norm (fin_prod_multiset_occurrences f.roots (fun r ↦ w - r))
      _ ≤ 1 := hw
  have hn : 0 < Fintype.card f.roots := by
    simpa using (show 0 < f.roots.card by
      rw [← (IsAlgClosed.splits f).natDegree_eq_card_roots]
      exact Nat.pos_of_ne_zero hdeg)
  have hmean : (∑ i, x i) / (Fintype.card f.roots : ℝ) = projection u (rootCentroid f) := by
    have hs : (∑ i, x i) = (f.roots.map (projection u)).sum :=
      fin_sum_multiset_occurrences f.roots (projection u)
    rw [hs]
    simpa using projection_rootCentroid f u
  have hend := endpoint_bound hn x hx hp
  rw [hmean] at hend
  exact (sub_le_sub_right (T.le_max' _ hzT) _).trans hend

/-- The entire closed sublevel set lies in the closed disk about the root centroid. -/
theorem centroid_enclosure (f : ℂ[X]) (hf : f.Monic) (hdeg : f.natDegree ≠ 0)
    (hE : IsConnected {w : ℂ | ‖f.eval w‖ ≤ 1}) :
    {w : ℂ | ‖f.eval w‖ ≤ 1} ⊆ Metric.closedBall (rootCentroid f) 2 := by
  intro z hz
  by_cases hzc : z = rootCentroid f
  · simp [hzc]
  · let d : ℂ := z - rootCentroid f
    have hd : d ≠ 0 := by simpa [d, sub_ne_zero] using hzc
    have hdnorm : 0 < ‖d‖ := norm_pos_iff.mpr hd
    let u : ℂ := d / (‖d‖ : ℂ)
    have hu : ‖u‖ = 1 := by
      simp [u, hdnorm.ne']
    have hproj : projection u z - projection u (rootCentroid f) = ‖d‖ := by
      rw [show projection u z - projection u (rootCentroid f) =
          (conj u * d).re by simp [projection, d, mul_sub]]
      dsimp [u]
      simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, neg_mul,
        sub_neg_eq_add]
      have hre : (d / (‖d‖ : ℂ)).re = d.re / ‖d‖ := by
        exact Complex.div_ofReal_re d ‖d‖
      have him : (d / (‖d‖ : ℂ)).im = d.im / ‖d‖ := by
        exact Complex.div_ofReal_im d ‖d‖
      rw [hre, him]
      have hs : d.re * d.re + d.im * d.im = ‖d‖ ^ 2 := by
        rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq]
      field_simp [hdnorm.ne']
      nlinarith
    have hle := projection_sub_centroid_le_two f hf hdeg hE hz u hu
    rw [hproj] at hle
    simpa [mem_closedBall, dist_eq_norm, d] using hle

end PommerenkeRootEnclosure

theorem OMA.solution : type_of% @Erdos509.erdos_509.variants.Pommerenke_connected := by
  intro f hf hdeg hE
  refine ⟨Unit, ⟨{
    C := fun _ ↦ PommerenkeRootEnclosure.rootCentroid f
    R := fun _ ↦ 2
    h_cover := ?_
    h_summable := (hasSum_fintype _).summable
    h_bdd := ?_
    h_pos := fun _ ↦ by norm_num }⟩⟩
  · intro z hz
    exact Set.mem_iUnion.mpr ⟨(), PommerenkeRootEnclosure.centroid_enclosure f hf hdeg hE hz⟩
  · simp

/-

                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
-/
