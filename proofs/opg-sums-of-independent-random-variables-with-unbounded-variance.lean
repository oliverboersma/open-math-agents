import OMAStatements.S_opg_sums_of_independent_random_variables_with_unbounded_variance
import Mathlib

/-
Feige's inequality for every δ > 0 (Open Problem Garden: sums of independent random variables
with unbounded variance), following Z. Ling, On Samuels' Conjecture, arXiv:2608.18392v2.

Generated from the Lake project feige-lean by scripts/make_submission.py.
The parts in namespace `Feige` are vendored from LeanPool/lean-pool
(https://github.com/LeanPool/lean-pool, LeanPool/Feige/, commit 9decab6, Apache-2.0,
author Zhengqing Zhou); see the per-part headers below. Everything else is in namespace `Samuels`.
-/

/- ===== Vendor/LeanPool/TwoPointMixture.lean ===== -/
section

/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
-- Vendored from LeanPool/lean-pool (https://github.com/LeanPool/lean-pool),
-- file LeanPool/Feige/TwoPointMixture.lean at commit 9decab6341e6b0fd82bd7f9763a5dd7a9ce8778d, Apache-2.0 (see LICENSE in this folder).
-- Changes: import paths renamed from `LeanPool.Feige.*` to `Feige.Vendor.LeanPool.*`.
-- Portability (Left to Solve CI, Lean v4.33.1): `add_apply`/`smul_apply` qualified as `Measure.*`,
-- `ite_eq_left/right` replaced by `if_pos/if_neg`, and small elaboration fixes where needed.



/-!
# Algebraic core of the two-point mixture lemma

This file develops the two-point mixture decomposition used in the proof of
Theorem 2.1.  It isolates the equality of the lower and upper first moments
and constructs the mean-one two-point law `Q_{x,y}`.
-/


open MeasureTheory Set

namespace Feige

noncomputable section

/-- The lower absolute first moment around one. -/
def belowMoment (μ : Measure ℝ) : ℝ :=
  ∫ x, (|x - 1| - (x - 1)) / 2 ∂μ

/-- The upper absolute first moment around one. -/
def aboveMoment (μ : Measure ℝ) : ℝ :=
  ∫ x, (|x - 1| + (x - 1)) / 2 ∂μ

theorem integrable_sub_one {μ : Measure ℝ}
    [IsFiniteMeasure μ]
    (hμ : Integrable (fun x : ℝ ↦ x) μ) :
    Integrable (fun x : ℝ ↦ x - 1) μ :=
  hμ.sub (integrable_const 1)

theorem integrable_abs_sub_one {μ : Measure ℝ}
    [IsFiniteMeasure μ]
    (hμ : Integrable (fun x : ℝ ↦ x) μ) :
    Integrable (fun x : ℝ ↦ |x - 1|) μ :=
  (integrable_sub_one hμ).abs

/-- The two expressions for `M` agree whenever the law has mean one.  No
support assumption is needed for this algebraic identity. -/
theorem belowMoment_eq_aboveMoment {μ : Measure ℝ}
    [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ ↦ x) μ)
    (hmean : (∫ x : ℝ, x ∂μ) = 1) :
    belowMoment μ = aboveMoment μ := by
  have hsub : (∫ x : ℝ, x - 1 ∂μ) = 0 := by
    rw [integral_sub hμ (integrable_const 1), hmean]
    simp
  unfold belowMoment aboveMoment
  rw [integral_div, integral_div, integral_sub (integrable_abs_sub_one hμ)
    (integrable_sub_one hμ), integral_add (integrable_abs_sub_one hμ)
    (integrable_sub_one hμ), hsub]
  ring

/-- Lower weight in the mean-one law supported on `x < 1 < y`. -/
def twoPointLowerWeight (x y : ℝ) : ℝ :=
  (y - 1) / (y - x)

/-- Upper weight in the mean-one law supported on `x < 1 < y`. -/
def twoPointUpperWeight (x y : ℝ) : ℝ :=
  (1 - x) / (y - x)

theorem twoPointWeights_nonneg {x y : ℝ} (hxy : x < y)
    (hx : x ≤ 1) (hy : 1 ≤ y) :
    0 ≤ twoPointLowerWeight x y ∧ 0 ≤ twoPointUpperWeight x y := by
  constructor
  · unfold twoPointLowerWeight
    exact div_nonneg (sub_nonneg.2 hy) (sub_nonneg.2 hxy.le)
  · unfold twoPointUpperWeight
    exact div_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 hxy.le)

theorem twoPointWeights_add {x y : ℝ} (hxy : x ≠ y) :
    twoPointLowerWeight x y + twoPointUpperWeight x y = 1 := by
  unfold twoPointLowerWeight twoPointUpperWeight
  field_simp
  ring

/-- The mean-one two-point law, expressed as a genuine nonnegative measure. -/
def twoPointMeasure (x y : ℝ) : Measure ℝ :=
  ENNReal.ofReal (twoPointLowerWeight x y) • Measure.dirac x +
    ENNReal.ofReal (twoPointUpperWeight x y) • Measure.dirac y

theorem twoPointMeasure_isProbability {x y : ℝ}
    (hx : x ≤ 1) (hy : 1 ≤ y) (hxy : x < y) :
    IsProbabilityMeasure (twoPointMeasure x y) := by
  constructor
  simp only [twoPointMeasure, Measure.add_apply, Measure.smul_apply]
  simp only [measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (twoPointWeights_nonneg hxy hx hy).1
      (twoPointWeights_nonneg hxy hx hy).2,
    twoPointWeights_add hxy.ne]
  norm_num

theorem twoPointMeasure_mean {x y : ℝ}
    (hx : x ≤ 1) (hy : 1 ≤ y) (hxy : x < y) :
    (∫ z : ℝ, z ∂(twoPointMeasure x y)) = 1 := by
  have hw := twoPointWeights_nonneg hxy hx hy
  have hIx : Integrable (fun z : ℝ ↦ z)
      (ENNReal.ofReal (twoPointLowerWeight x y) • Measure.dirac x) :=
    (integrable_dirac' stronglyMeasurable_id (by simp)).smul_measure (by simp)
  have hIy : Integrable (fun z : ℝ ↦ z)
      (ENNReal.ofReal (twoPointUpperWeight x y) • Measure.dirac y) :=
    (integrable_dirac' stronglyMeasurable_id (by simp)).smul_measure (by simp)
  rw [twoPointMeasure, integral_add_measure hIx hIy,
    integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac,
    ENNReal.toReal_ofReal hw.1, ENNReal.toReal_ofReal hw.2]
  simp only [smul_eq_mul]
  unfold twoPointLowerWeight twoPointUpperWeight
  calc
    ((y - 1) / (y - x)) * x + ((1 - x) / (y - x)) * y =
        (y - x) * (y - x)⁻¹ := by field_simp [sub_ne_zero.mpr hxy.ne']; ring
    _ = 1 := mul_inv_cancel₀ (sub_ne_zero.mpr hxy.ne')

/-- Pointwise algebra behind the two-point mixture formula. -/
theorem twoPointMeasure_scaled_apply {x y : ℝ}
    (hx : x ≤ 1) (hy : 1 ≤ y) (hxy : x < y)
    (B : Set ℝ) :
    ENNReal.ofReal (y - x) * twoPointMeasure x y B =
      ENNReal.ofReal (y - 1) * Measure.dirac x B +
        ENNReal.ofReal (1 - x) * Measure.dirac y B := by
  rw [twoPointMeasure, Measure.add_apply, Measure.smul_apply,
    Measure.smul_apply, mul_add]
  have hw := twoPointWeights_nonneg hxy hx hy
  change
    ENNReal.ofReal (y - x) *
          (ENNReal.ofReal (twoPointLowerWeight x y) * Measure.dirac x B) +
        ENNReal.ofReal (y - x) *
          (ENNReal.ofReal (twoPointUpperWeight x y) * Measure.dirac y B) =
      ENNReal.ofReal (y - 1) * Measure.dirac x B +
        ENNReal.ofReal (1 - x) * Measure.dirac y B
  rw [← mul_assoc, ← ENNReal.ofReal_mul (sub_nonneg.2 hxy.le),
    ← mul_assoc, ← ENNReal.ofReal_mul (sub_nonneg.2 hxy.le)]
  congr 1
  · apply congrArg₂ (· * ·) _ rfl
    apply congrArg ENNReal.ofReal
    unfold twoPointLowerWeight
    field_simp [sub_ne_zero.mpr hxy.ne']
  · apply congrArg₂ (· * ·) _ rfl
    apply congrArg ENNReal.ofReal
    unfold twoPointUpperWeight
    field_simp [sub_ne_zero.mpr hxy.ne']

/-- The measure obtained after expanding the double integral in the
two-point mixture formula.

The first restricted measure is multiplied by the upper moment (integration
in `y`), and the second by the lower moment (integration in `x`). -/
def expandedTwoPointMixture (μ : Measure ℝ) (M : ℝ) : Measure ℝ :=
  μ {1} • Measure.dirac 1 +
    (ENNReal.ofReal M)⁻¹ •
      (ENNReal.ofReal (aboveMoment μ) • μ.restrict (Iio 1) +
        ENNReal.ofReal (belowMoment μ) • μ.restrict (Ioi 1))

/-- Splitting a measure at one into its below, atom, and above pieces. -/
theorem restrict_below_add_atom_add_above (μ : Measure ℝ) :
    μ.restrict (Iio 1) + μ {1} • Measure.dirac 1 + μ.restrict (Ioi 1) = μ := by
  rw [← Measure.restrict_singleton]
  have h₁ := Measure.restrict_add_restrict_compl
    (μ := μ) (s := Iio (1 : ℝ)) measurableSet_Iio
  have h₂ := Measure.restrict_add_restrict_compl
    (μ := μ.restrict (Iio (1 : ℝ))ᶜ) (s := {1}) (measurableSet_singleton 1)
  rw [MeasureTheory.Measure.restrict_restrict (measurableSet_singleton 1),
    MeasureTheory.Measure.restrict_restrict (measurableSet_singleton 1).compl] at h₂
  have hc : {1} ∩ (Iio (1 : ℝ))ᶜ = {1} := by ext x; simp
  have ha : {1}ᶜ ∩ (Iio (1 : ℝ))ᶜ = Ioi 1 := by
    ext x
    simp only [mem_inter_iff, mem_compl_iff, mem_singleton_iff, mem_Iio, mem_Ioi]
    constructor <;> intro h
    · rcases h with ⟨hne, hle⟩
      exact lt_of_le_of_ne (le_of_not_gt hle) (Ne.symm hne)
    · exact ⟨ne_of_gt h, not_lt_of_ge h.le⟩
  rw [hc, ha] at h₂
  calc
    μ.restrict (Iio 1) + μ.restrict {1} + μ.restrict (Ioi 1) =
        μ.restrict (Iio 1) + (μ.restrict {1} + μ.restrict (Ioi 1)) := add_assoc ..
    _ = μ.restrict (Iio 1) + μ.restrict (Iio 1)ᶜ := by rw [h₂]
    _ = μ := h₁

/-- The two-point mixture formula after evaluating its two product integrals.
The support assumption is not needed for this final algebraic identity; it
is needed only to ensure that the sampled lower point is nonnegative. -/
theorem expandedTwoPointMixture_eq
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ ↦ x) μ)
    (hmean : (∫ x : ℝ, x ∂μ) = 1)
    (hM : 0 < belowMoment μ) :
    expandedTwoPointMixture μ (belowMoment μ) = μ := by
  have heq := belowMoment_eq_aboveMoment hμ hmean
  have hne : ENNReal.ofReal (belowMoment μ) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr hM)
  rw [expandedTwoPointMixture, ← heq]
  rw [smul_add]
  rw [← mul_smul, ← mul_smul, ENNReal.inv_mul_cancel hne (by simp), one_smul]
  rw [one_smul ENNReal]
  calc
    μ {1} • Measure.dirac 1 + (μ.restrict (Iio 1) + μ.restrict (Ioi 1)) =
        μ.restrict (Iio 1) + μ {1} • Measure.dirac 1 + μ.restrict (Ioi 1) := by abel
    _ = μ := restrict_below_add_atom_add_above μ

/-- The two-point mixture formula at the canonical lower moment. -/
theorem twoPointMixture_formula42
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ ↦ x) μ)
    (hmean : (∫ x : ℝ, x ∂μ) = 1)
    (hM : 0 < belowMoment μ) :
    expandedTwoPointMixture μ (belowMoment μ) = μ :=
  expandedTwoPointMixture_eq hμ hmean hM

/-- The lower moment is nonnegative. -/
theorem belowMoment_nonneg {μ : Measure ℝ} :
    0 ≤ belowMoment μ := by
  unfold belowMoment
  apply integral_nonneg
  intro x
  exact div_nonneg (sub_nonneg.mpr (le_abs_self (x - 1))) (by norm_num)

/-- The degenerate branch of the mixture decomposition: if `M = 0`, a
mean-one probability law is concentrated at one. -/
theorem eq_dirac_one_of_belowMoment_eq_zero
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ ↦ x) μ)
    (hmean : (∫ x : ℝ, x ∂μ) = 1)
    (hM : belowMoment μ = 0) :
    μ = Measure.dirac 1 := by
  have hsub := integrable_sub_one hμ
  have habs := integrable_abs_sub_one hμ
  have hdefInt :
      Integrable (fun x : ℝ ↦ (|x - 1| - (x - 1)) / 2) μ :=
    (habs.sub hsub).div_const 2
  have hdefNonneg :
      ∀ x : ℝ, 0 ≤ (|x - 1| - (x - 1)) / 2 := by
    intro x
    have := le_abs_self (x - 1)
    linarith
  have hzero :
      (fun x : ℝ ↦ (|x - 1| - (x - 1)) / 2) =ᵐ[μ] 0 := by
    apply (integral_eq_zero_iff_of_nonneg hdefNonneg hdefInt).1
    simpa [belowMoment] using hM
  have hone_le : (fun _ : ℝ ↦ (1 : ℝ)) ≤ᵐ[μ] fun x ↦ x := by
    filter_upwards [hzero] with x hx
    change (|x - 1| - (x - 1)) / 2 = 0 at hx
    have habseq : |x - 1| = x - 1 := by linarith
    have : 0 ≤ x - 1 := habseq ▸ abs_nonneg (x - 1)
    linarith
  have hone_ae : (fun _ : ℝ ↦ (1 : ℝ)) =ᵐ[μ] fun x ↦ x := by
    apply (integral_eq_iff_of_ae_le (integrable_const 1) hμ hone_le).1
    simp [hmean]
  apply Measure.ext
  intro B hB
  by_cases h1 : (1 : ℝ) ∈ B
  · have hBae : (B : Set ℝ) =ᵐ[μ] Set.univ := by
      filter_upwards [hone_ae] with x hx
      try rw [eq_iff_iff]
      constructor
      · intro
        exact Set.mem_univ x
      · intro
        rwa [← hx]
    rw [measure_congr hBae, measure_univ]
    simp [Measure.dirac_apply' _ hB, Set.indicator_of_mem h1]
  · have hBae : (B : Set ℝ) =ᵐ[μ] (∅ : Set ℝ) := by
      filter_upwards [hone_ae] with x hx
      try rw [eq_iff_iff]
      constructor
      · intro hxB
        exfalso
        apply h1
        rwa [← hx] at hxB
      · intro hxE
        exact False.elim hxE
    rw [measure_congr hBae, measure_empty]
    simp [Measure.dirac_apply' _ hB, Set.indicator_of_notMem h1]

/-- Full mixture dichotomy: either the law is the degenerate law at one, or
its positive lower moment gives the two-point mixture formula. -/
theorem twoPointMixture_dichotomy
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ ↦ x) μ)
    (hmean : (∫ x : ℝ, x ∂μ) = 1) :
    μ = Measure.dirac 1 ∨
      (0 < belowMoment μ ∧
        expandedTwoPointMixture μ (belowMoment μ) = μ) := by
  rcases (belowMoment_nonneg (μ := μ)).eq_or_lt with hzero | hpos
  · exact Or.inl (eq_dirac_one_of_belowMoment_eq_zero hμ hmean hzero.symm)
  · exact Or.inr ⟨hpos, twoPointMixture_formula42 hμ hmean hpos⟩

end

end Feige

end

/- ===== Vendor/LeanPool/MeasurableTwoPointKernel.lean ===== -/
section

/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
-- Vendored from LeanPool/lean-pool (https://github.com/LeanPool/lean-pool),
-- file LeanPool/Feige/MeasurableTwoPointKernel.lean at commit 9decab6341e6b0fd82bd7f9763a5dd7a9ce8778d, Apache-2.0 (see LICENSE in this folder).
-- Changes: import paths renamed from `LeanPool.Feige.*` to `Feige.Vendor.LeanPool.*`;
-- two proofs given explicit type annotations and `measurable_twoPointParams_val` added, so that they also elaborate in a non-module file.
-- Portability (Left to Solve CI, Lean v4.33.1): `add_apply`/`smul_apply` qualified as `Measure.*`,
-- `ite_eq_left/right` replaced by `if_pos/if_neg`, and small elaboration fixes where needed.



/-!
# A measurable kernel of mean-one two-point laws

This file supplies the measurable-kernel interface needed to condition on
the latent two-point parameters in the proof of Theorem 2.1.
-/


open MeasureTheory ProbabilityTheory Set

namespace Feige

noncomputable section

/-- Evaluation of the two-point law on a Borel set is measurable in both
support points. -/
theorem measurable_twoPointMeasure_apply {B : Set ℝ} (hB : MeasurableSet B) :
    Measurable (fun p : ℝ × ℝ ↦ twoPointMeasure p.1 p.2 B) := by
  simp only [twoPointMeasure, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply' _ hB]
  unfold twoPointLowerWeight twoPointUpperWeight
  fun_prop

/-- Admissible parameters `x ≤ 1 ≤ y`, with distinct support points. -/
def TwoPointParams :=
  {p : ℝ × ℝ // p.1 ≤ 1 ∧ 1 ≤ p.2 ∧ p.1 < p.2}

instance : MeasurableSpace TwoPointParams :=
  MeasurableSpace.comap Subtype.val inferInstance

/-- The coordinate projection on admissible parameters is measurable (added for the vendored copy). -/
theorem measurable_twoPointParams_val : Measurable (fun q : TwoPointParams ↦ q.1) :=
  fun s hs ↦ ⟨s, hs, rfl⟩

/-- The Markov kernel sending `(x,y)` to the mean-one two-point law
`Q_{x,y}`. -/
noncomputable def twoPointKernel : Kernel TwoPointParams ℝ where
  toFun p := twoPointMeasure p.1.1 p.1.2
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro B hB
    exact (measurable_twoPointMeasure_apply hB).comp measurable_subtype_coe

@[simp] theorem twoPointKernel_apply (p : TwoPointParams) :
    twoPointKernel p = twoPointMeasure p.1.1 p.1.2 :=
  rfl

instance : IsMarkovKernel twoPointKernel where
  isProbabilityMeasure p :=
    twoPointMeasure_isProbability p.2.1 p.2.2.1 p.2.2.2

theorem twoPointKernel_mean (p : TwoPointParams) :
    (∫ z : ℝ, z ∂(twoPointKernel p)) = 1 := by
  rw [twoPointKernel_apply]
  exact twoPointMeasure_mean p.2.1 p.2.2.1 p.2.2.2

theorem twoPointKernel_nonnegative_support (p : TwoPointParams)
    (hx : 0 ≤ p.1.1) :
    twoPointKernel p (Iio 0) = 0 := by
  rw [twoPointKernel_apply, twoPointMeasure]
  simp only [Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply' _ measurableSet_Iio]
  have hy : 0 ≤ p.1.2 := le_trans (by norm_num) p.2.2.1
  simp [not_lt_of_ge hx, not_lt_of_ge hy]

/-- The genuine measure obtained by sampling latent two-point parameters and
then sampling from their two-point law. -/
noncomputable def kernelTwoPointMixture (ν : Measure TwoPointParams) : Measure ℝ :=
  twoPointKernel ∘ₘ ν

instance (ν : Measure TwoPointParams) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (kernelTwoPointMixture ν) := by
  unfold kernelTwoPointMixture
  infer_instance

/-- The `Measure.bind` formula for the two-point mixture. -/
theorem kernelTwoPointMixture_apply (ν : Measure TwoPointParams)
    {B : Set ℝ} (hB : MeasurableSet B) :
    kernelTwoPointMixture ν B =
      ∫⁻ p, twoPointMeasure p.1.1 p.1.2 B ∂ν := by
  rw [kernelTwoPointMixture, Measure.bind_apply hB twoPointKernel.aemeasurable]
  rfl

/-- Averaging a pointwise probability bound over latent parameters. -/
theorem kernelTwoPointMixture_apply_le
    (ν : Measure TwoPointParams) [IsProbabilityMeasure ν]
    {B : Set ℝ} (hB : MeasurableSet B) {c : ENNReal}
    (hc : ∀ p : TwoPointParams, twoPointMeasure p.1.1 p.1.2 B ≤ c) :
    kernelTwoPointMixture ν B ≤ c := by
  rw [kernelTwoPointMixture_apply ν hB]
  calc
    (∫⁻ p, twoPointMeasure p.1.1 p.1.2 B ∂ν) ≤ ∫⁻ _p, c ∂ν :=
      lintegral_mono fun p ↦ hc p
    _ = c := by simp

/-- The strict below-above region used for the nondegenerate latent pair. -/
def strictPairSet : Set (ℝ × ℝ) :=
  {p | p.1 < 1 ∧ 1 < p.2}

theorem measurableSet_strictPairSet : MeasurableSet strictPairSet := by
  have h1 : MeasurableSet {p : ℝ × ℝ | p.1 < 1} :=
    measurableSet_lt measurable_fst measurable_const
  have h2 : MeasurableSet {p : ℝ × ℝ | 1 < p.2} :=
    measurableSet_lt measurable_const measurable_snd
  exact h1.inter h2

/-- Every strict below-above pair is an admissible two-point parameter. -/
theorem strictPairSet_admissible {p : ℝ × ℝ} (hp : p ∈ strictPairSet) :
    p.1 ≤ 1 ∧ 1 ≤ p.2 ∧ p.1 < p.2 :=
  ⟨hp.1.le, hp.2.le, hp.1.trans hp.2⟩

/-- Classical decidability for membership in the strict parameter region. -/
local instance : DecidablePred (· ∈ strictPairSet) :=
  Classical.decPred _

/-- A total measurable map into `TwoPointParams`; outside the strict region
we use the harmless default pair `(0,2)`.  The weighted latent measure below
is supported on the strict region. -/
noncomputable def pairToParams (p : ℝ × ℝ) : TwoPointParams :=
  if hp : p ∈ strictPairSet then ⟨p, strictPairSet_admissible hp⟩
  else ⟨(0, 2), by norm_num⟩

theorem measurable_pairToParams : Measurable pairToParams := by
  let f : ℝ × ℝ → ℝ × ℝ :=
    fun p ↦ if p ∈ strictPairSet then p else (0, 2)
  have hf : Measurable f :=
    Measurable.ite measurableSet_strictPairSet measurable_id measurable_const
  rw [measurable_iff_comap_le]
  change MeasurableSpace.comap pairToParams
      (MeasurableSpace.comap (fun p : TwoPointParams ↦ p.val)
        (inferInstance : MeasurableSpace (ℝ × ℝ))) ≤
    (inferInstance : MeasurableSpace (ℝ × ℝ))
  rw [MeasurableSpace.comap_comp]
  change MeasurableSpace.comap (fun p ↦ (pairToParams p).val)
      (inferInstance : MeasurableSpace (ℝ × ℝ)) ≤
    (inferInstance : MeasurableSpace (ℝ × ℝ))
  rw [show (fun p ↦ (pairToParams p).val) = f by
    funext p
    by_cases hp : p ∈ strictPairSet <;> simp [pairToParams, f, hp]]
  exact hf.comap_le

/-- The unnormalized product law on a strict below point and a strict above
point. -/
noncomputable def belowAboveProduct (μ : Measure ℝ) : Measure (ℝ × ℝ) :=
  (μ.restrict (Iio 1)).prod (μ.restrict (Ioi 1))

/-- The density `(y-x)/M` of the latent below/above pair, written in
`ℝ≥0∞`. -/
noncomputable def latentPairDensity (M : ℝ) (p : ℝ × ℝ) : ENNReal :=
  (ENNReal.ofReal M)⁻¹ * ENNReal.ofReal (p.2 - p.1)

theorem measurable_latentPairDensity (M : ℝ) :
    Measurable (latentPairDensity M) := by
  unfold latentPairDensity
  fun_prop

/-- The concrete weighted below×above latent measure. -/
noncomputable def latentPairMeasure (μ : Measure ℝ) (M : ℝ) :
    Measure (ℝ × ℝ) :=
  (belowAboveProduct μ).withDensity (latentPairDensity M)

theorem strictPairSet_eq_prod :
    strictPairSet = Iio (1 : ℝ) ×ˢ Ioi (1 : ℝ) := by
  ext p
  rfl

theorem belowAboveProduct_compl_strictPairSet (μ : Measure ℝ) [SFinite μ] :
    belowAboveProduct μ strictPairSetᶜ = 0 := by
  rw [belowAboveProduct, Measure.prod_restrict,
    strictPairSet_eq_prod,
    Measure.restrict_apply (measurableSet_Iio.prod measurableSet_Ioi).compl]
  simp

/-- The weighted latent pair measure has no mass outside the strict
below×above parameter region. -/
theorem latentPairMeasure_compl_strictPairSet (μ : Measure ℝ) [SFinite μ] (M : ℝ) :
    latentPairMeasure μ M strictPairSetᶜ = 0 := by
  rw [latentPairMeasure, withDensity_apply _ measurableSet_strictPairSet.compl]
  exact setLIntegral_measure_zero strictPairSetᶜ (latentPairDensity M)
    (belowAboveProduct_compl_strictPairSet μ)

instance (μ : Measure ℝ) [SFinite μ] (M : ℝ) :
    SFinite (latentPairMeasure μ M) := by
  unfold latentPairMeasure belowAboveProduct
  infer_instance

/-- The weighted pair measure, transported to the admissible parameter
subtype on which `twoPointKernel` is Markov. -/
noncomputable def latentParamsMeasure (μ : Measure ℝ) (M : ℝ) :
    Measure TwoPointParams :=
  (latentPairMeasure μ M).map pairToParams

theorem latentParamsMeasure_apply (μ : Measure ℝ) (M : ℝ)
    {A : Set TwoPointParams} (hA : MeasurableSet A) :
    latentParamsMeasure μ M A =
      latentPairMeasure μ M (pairToParams ⁻¹' A) := by
  rw [latentParamsMeasure, Measure.map_apply measurable_pairToParams hA]

/-- The resulting genuine kernel mixture of the nondegenerate latent
component. -/
noncomputable def nondegenerateKernelMixture (μ : Measure ℝ) (M : ℝ) :
    Measure ℝ :=
  kernelTwoPointMixture (latentParamsMeasure μ M)

/-- The absolute-value definition of the lower moment is the usual
restricted first moment below one. -/
theorem belowMoment_eq_integral_Iio (μ : Measure ℝ) :
    belowMoment μ = ∫ x in Iio (1 : ℝ), 1 - x ∂μ := by
  rw [← integral_indicator measurableSet_Iio]
  unfold belowMoment
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x < 1
  · have hxmem : x ∈ Iio (1 : ℝ) := hx
    rw [Set.indicator_of_mem hxmem]
    rw [abs_of_neg (sub_neg.mpr hx)]
    ring
  · have hxmem : x ∉ Iio (1 : ℝ) := hx
    rw [Set.indicator_of_notMem hxmem]
    rw [abs_of_nonneg (sub_nonneg.mpr (le_of_not_gt hx))]
    ring

/-- The absolute-value definition of the upper moment is the usual
restricted first moment above one. -/
theorem aboveMoment_eq_integral_Ioi (μ : Measure ℝ) :
    aboveMoment μ = ∫ y in Ioi (1 : ℝ), y - 1 ∂μ := by
  rw [← integral_indicator measurableSet_Ioi]
  unfold aboveMoment
  apply integral_congr_ae
  filter_upwards [] with y
  by_cases hy : 1 < y
  · have hymem : y ∈ Ioi (1 : ℝ) := hy
    rw [Set.indicator_of_mem hymem]
    rw [abs_of_pos (sub_pos.mpr hy)]
    ring
  · have hymem : y ∉ Ioi (1 : ℝ) := hy
    rw [Set.indicator_of_notMem hymem]
    rw [abs_of_nonpos (sub_nonpos.mpr (le_of_not_gt hy))]
    ring

theorem ofReal_belowMoment_eq_lintegral_Iio
    {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hμ : Integrable (fun x : ℝ ↦ x) μ) :
    ENNReal.ofReal (belowMoment μ) =
      ∫⁻ x in Iio (1 : ℝ), ENNReal.ofReal (1 - x) ∂μ := by
  rw [belowMoment_eq_integral_Iio]
  apply ofReal_integral_eq_lintegral_ofReal
  · exact ((integrable_const 1).sub hμ).integrableOn
  · filter_upwards [ae_restrict_mem measurableSet_Iio] with x hx
    exact sub_nonneg.mpr hx.le

theorem ofReal_aboveMoment_eq_lintegral_Ioi
    {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hμ : Integrable (fun x : ℝ ↦ x) μ) :
    ENNReal.ofReal (aboveMoment μ) =
      ∫⁻ y in Ioi (1 : ℝ), ENNReal.ofReal (y - 1) ∂μ := by
  rw [aboveMoment_eq_integral_Ioi]
  apply ofReal_integral_eq_lintegral_ofReal
  · exact (hμ.sub (integrable_const 1)).integrableOn
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact sub_nonneg.mpr hy.le

/-- Tonelli expansion of the total mass of the nondegenerate latent pair
measure. -/
theorem latentPairMeasure_univ
    {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hμ : Integrable (fun x : ℝ ↦ x) μ) (M : ℝ) :
    latentPairMeasure μ M Set.univ =
      (ENNReal.ofReal M)⁻¹ *
        (μ (Iio 1) * ENNReal.ofReal (aboveMoment μ) +
          ENNReal.ofReal (belowMoment μ) * μ (Ioi 1)) := by
  rw [latentPairMeasure, withDensity_apply _ MeasurableSet.univ,
    setLIntegral_univ]
  unfold latentPairDensity belowAboveProduct
  rw [lintegral_const_mul]
  · have hae :
        (fun p : ℝ × ℝ ↦ ENNReal.ofReal (p.2 - p.1)) =ᵐ[
          (μ.restrict (Iio 1)).prod (μ.restrict (Ioi 1))]
        (fun p ↦ ENNReal.ofReal (p.2 - 1) + ENNReal.ofReal (1 - p.1)) := by
      have hf : Measurable (fun p : ℝ × ℝ ↦ ENNReal.ofReal (p.2 - p.1)) := by
        fun_prop
      have hg : Measurable (fun p : ℝ × ℝ ↦
          ENNReal.ofReal (p.2 - 1) + ENNReal.ofReal (1 - p.1)) := by
        fun_prop
      have heqmeas : MeasurableSet {p : ℝ × ℝ |
          ENNReal.ofReal (p.2 - p.1) =
            ENNReal.ofReal (p.2 - 1) + ENNReal.ofReal (1 - p.1)} := by
        rw [show {p : ℝ × ℝ |
            ENNReal.ofReal (p.2 - p.1) =
              ENNReal.ofReal (p.2 - 1) + ENNReal.ofReal (1 - p.1)} =
            {p | ENNReal.ofReal (p.2 - p.1) ≤
              ENNReal.ofReal (p.2 - 1) + ENNReal.ofReal (1 - p.1)} ∩
            {p | ENNReal.ofReal (p.2 - 1) + ENNReal.ofReal (1 - p.1) ≤
              ENNReal.ofReal (p.2 - p.1)} by
                ext p
                simp only [mem_ofPred_eq, mem_inter_iff]
                constructor
                · intro h
                  exact ⟨h.le, h.ge⟩
                · rintro ⟨h₁, h₂⟩
                  exact le_antisymm h₁ h₂]
        exact (measurableSet_le hf hg).inter (measurableSet_le hg hf)
      apply (Measure.ae_prod_iff_ae_ae heqmeas).2
      filter_upwards [ae_restrict_mem measurableSet_Iio] with x hx
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      rw [← ENNReal.ofReal_add (sub_nonneg.mpr (le_of_lt (show (1 : ℝ) < y from hy)))
        (sub_nonneg.mpr (le_of_lt (show x < (1 : ℝ) from hx)))]
      congr 1
      ring
    rw [lintegral_congr_ae hae]
    rw [lintegral_add_left (by fun_prop)]
    have hfirst :
        (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (p.2 - 1)
          ∂(μ.restrict (Iio 1)).prod (μ.restrict (Ioi 1))) =
        (∫⁻ _x : ℝ, (1 : ENNReal) ∂μ.restrict (Iio 1)) *
          ∫⁻ y : ℝ, ENNReal.ofReal (y - 1) ∂μ.restrict (Ioi 1) := by
      simpa using
        (lintegral_prod_mul (μ := μ.restrict (Iio 1))
          (ν := μ.restrict (Ioi 1))
          (f := fun _x : ℝ ↦ (1 : ENNReal))
          (g := fun y : ℝ ↦ ENNReal.ofReal (y - 1))
          (by fun_prop) (by fun_prop))
    have hsecond :
        (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (1 - p.1)
          ∂(μ.restrict (Iio 1)).prod (μ.restrict (Ioi 1))) =
        (∫⁻ x : ℝ, ENNReal.ofReal (1 - x) ∂μ.restrict (Iio 1)) *
          ∫⁻ _y : ℝ, (1 : ENNReal) ∂μ.restrict (Ioi 1) := by
      simpa using
        (lintegral_prod_mul (μ := μ.restrict (Iio 1))
          (ν := μ.restrict (Ioi 1))
          (f := fun x : ℝ ↦ ENNReal.ofReal (1 - x))
          (g := fun _y : ℝ ↦ (1 : ENNReal))
          (by fun_prop) (by fun_prop))
    rw [hfirst, hsecond]
    simp only [lintegral_one, Measure.restrict_apply MeasurableSet.univ,
      Set.univ_inter]
    rw [← ofReal_aboveMoment_eq_lintegral_Ioi hμ,
      ← ofReal_belowMoment_eq_lintegral_Iio hμ]
  · fun_prop

theorem mass_below_add_above
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    μ (Iio 1) + μ (Ioi 1) = 1 - μ {1} := by
  have hparts := congrArg (fun ν : Measure ℝ ↦ ν Set.univ)
    (restrict_below_add_atom_add_above μ)
  simp only [Measure.add_apply, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, Measure.smul_apply, measure_univ,
    Measure.dirac_apply' _ MeasurableSet.univ, Set.indicator_of_mem
      (Set.mem_univ (1 : ℝ)), Pi.one_apply, smul_eq_mul, mul_one] at hparts
  apply ENNReal.eq_sub_of_add_eq' (by simp)
  calc
    μ (Iio 1) + μ (Ioi 1) + μ {1} =
        μ (Iio 1) + μ {1} + μ (Ioi 1) := by ac_rfl
    _ = 1 := hparts

/-- In the mean-one positive-moment branch, the nondegenerate latent
component has precisely the mass outside the atom at one. -/
theorem latentPairMeasure_univ_meanOne
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ ↦ x) μ)
    (hmean : (∫ x : ℝ, x ∂μ) = 1)
    (hM : 0 < belowMoment μ) :
    latentPairMeasure μ (belowMoment μ) Set.univ = 1 - μ {1} := by
  rw [latentPairMeasure_univ hμ]
  rw [← belowMoment_eq_aboveMoment hμ hmean]
  let a : ENNReal := ENNReal.ofReal (belowMoment μ)
  have ha0 : a ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hM)
  have hatop : a ≠ ⊤ := by simp [a]
  change a⁻¹ * (μ (Iio 1) * a + a * μ (Ioi 1)) = 1 - μ {1}
  calc
    a⁻¹ * (μ (Iio 1) * a + a * μ (Ioi 1)) =
        a⁻¹ * (a * (μ (Iio 1) + μ (Ioi 1))) := by
          congr 1
          rw [mul_comm (μ (Iio 1)) a, mul_add]
    _ = μ (Iio 1) + μ (Ioi 1) :=
      ENNReal.inv_mul_cancel_left ha0 hatop
    _ = 1 - μ {1} := mass_below_add_above μ

/-- The full kernel mixture: the atom at one plus the nondegenerate latent
two-point component. -/
noncomputable def fullKernelMixture (μ : Measure ℝ) (M : ℝ) : Measure ℝ :=
  μ {1} • Measure.dirac 1 + nondegenerateKernelMixture μ M

theorem nondegenerateKernelMixture_univ
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ ↦ x) μ)
    (hmean : (∫ x : ℝ, x ∂μ) = 1)
    (hM : 0 < belowMoment μ) :
    nondegenerateKernelMixture μ (belowMoment μ) Set.univ =
      1 - μ {1} := by
  rw [nondegenerateKernelMixture, kernelTwoPointMixture_apply _
    MeasurableSet.univ]
  have hmap :
      latentParamsMeasure μ (belowMoment μ) Set.univ =
        latentPairMeasure μ (belowMoment μ) Set.univ := by
    rw [latentParamsMeasure, Measure.map_apply measurable_pairToParams
      MeasurableSet.univ]
    simp
  rw [show (∫⁻ p : TwoPointParams,
      twoPointMeasure p.1.1 p.1.2 Set.univ
        ∂latentParamsMeasure μ (belowMoment μ)) =
      latentParamsMeasure μ (belowMoment μ) Set.univ by
        rw [← lintegral_one]
        apply lintegral_congr
        intro p
        let := twoPointMeasure_isProbability p.2.1 p.2.2.1 p.2.2.2
        exact measure_univ]
  rw [hmap, latentPairMeasure_univ_meanOne hμ hmean hM]

theorem fullKernelMixture_isProbability
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ ↦ x) μ)
    (hmean : (∫ x : ℝ, x ∂μ) = 1)
    (hM : 0 < belowMoment μ) :
    IsProbabilityMeasure (fullKernelMixture μ (belowMoment μ)) := by
  constructor
  rw [fullKernelMixture, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply' _ MeasurableSet.univ,
    Set.indicator_of_mem (Set.mem_univ (1 : ℝ)), Pi.one_apply,
    smul_eq_mul, mul_one,
    nondegenerateKernelMixture_univ hμ hmean hM]
  apply add_tsub_cancel_of_le
  calc
    μ ({1} : Set ℝ) ≤ μ Set.univ := measure_mono (subset_univ _)
    _ = 1 := measure_univ

/-- Pull the nondegenerate kernel mixture back from the parameter subtype to
the original weighted pair measure.  This is the change-of-variables layer
in the Borel-set verification of the two-point mixture formula. -/
theorem nondegenerateKernelMixture_apply_pair
    (μ : Measure ℝ) (M : ℝ) {B : Set ℝ} (hB : MeasurableSet B) :
    nondegenerateKernelMixture μ M B =
      ∫⁻ p : ℝ × ℝ,
        twoPointMeasure (pairToParams p).1.1 (pairToParams p).1.2 B
          ∂latentPairMeasure μ M := by
  rw [nondegenerateKernelMixture, kernelTwoPointMixture_apply _ hB]
  rw [latentParamsMeasure]
  have hf : Measurable (fun q : TwoPointParams ↦
      twoPointMeasure q.1.1 q.1.2 B) := by
    exact (measurable_twoPointMeasure_apply hB).comp measurable_subtype_coe
  rw [lintegral_map hf measurable_pairToParams]

theorem nondegenerateKernelMixture_apply_strict
    (μ : Measure ℝ) [SFinite μ] (M : ℝ)
    {B : Set ℝ} (hB : MeasurableSet B) :
    nondegenerateKernelMixture μ M B =
      ∫⁻ p : ℝ × ℝ, twoPointMeasure p.1 p.2 B
        ∂latentPairMeasure μ M := by
  rw [nondegenerateKernelMixture_apply_pair μ M hB]
  apply lintegral_congr_ae
  filter_upwards [compl_mem_ae_iff.2
    (latentPairMeasure_compl_strictPairSet μ M)] with p hp
  have hps : p ∈ strictPairSet := by simpa only [compl_compl] using hp
  simp [pairToParams, hps]

theorem nondegenerateKernelMixture_apply_expanded
    {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hμ : Integrable (fun x : ℝ ↦ x) μ) (M : ℝ)
    {B : Set ℝ} (hB : MeasurableSet B) :
    nondegenerateKernelMixture μ M B =
      (ENNReal.ofReal M)⁻¹ *
        (ENNReal.ofReal (aboveMoment μ) * μ.restrict (Iio 1) B +
          ENNReal.ofReal (belowMoment μ) * μ.restrict (Ioi 1) B) := by
  have hdirac : Measurable (fun x : ℝ ↦ Measure.dirac x B) := by
    simp only [Measure.dirac_apply' _ hB]
    exact measurable_const.indicator hB
  rw [nondegenerateKernelMixture_apply_strict μ M hB]
  rw [latentPairMeasure, lintegral_withDensity_eq_lintegral_mul _
    (measurable_latentPairDensity M)
    (measurable_twoPointMeasure_apply hB)]
  unfold latentPairDensity belowAboveProduct
  have hae :
      (fun p : ℝ × ℝ ↦
        ((ENNReal.ofReal M)⁻¹ * ENNReal.ofReal (p.2 - p.1)) *
          twoPointMeasure p.1 p.2 B) =ᵐ[
        (μ.restrict (Iio 1)).prod (μ.restrict (Ioi 1))]
      (fun p ↦ (ENNReal.ofReal M)⁻¹ *
        (ENNReal.ofReal (p.2 - 1) * Measure.dirac p.1 B +
          ENNReal.ofReal (1 - p.1) * Measure.dirac p.2 B)) := by
    apply (Measure.ae_prod_iff_ae_ae (by
      have hf : Measurable (fun p : ℝ × ℝ ↦
          ((ENNReal.ofReal M)⁻¹ * ENNReal.ofReal (p.2 - p.1)) *
            twoPointMeasure p.1 p.2 B) := by
        exact (measurable_const.mul
          ((measurable_snd.sub measurable_fst).ennreal_ofReal)).mul
            (measurable_twoPointMeasure_apply hB)
      have hg : Measurable (fun p : ℝ × ℝ ↦ (ENNReal.ofReal M)⁻¹ *
          (ENNReal.ofReal (p.2 - 1) * Measure.dirac p.1 B +
            ENNReal.ofReal (1 - p.1) * Measure.dirac p.2 B)) := by
        exact measurable_const.mul
          (((measurable_snd.sub measurable_const).ennreal_ofReal.mul
              (hdirac.comp measurable_fst)).add
            ((measurable_const.sub measurable_fst).ennreal_ofReal.mul
              (hdirac.comp measurable_snd)))
      rw [show {p | (fun p : ℝ × ℝ ↦
          ((ENNReal.ofReal M)⁻¹ * ENNReal.ofReal (p.2 - p.1)) *
            twoPointMeasure p.1 p.2 B) p =
          (fun p ↦ (ENNReal.ofReal M)⁻¹ *
            (ENNReal.ofReal (p.2 - 1) * Measure.dirac p.1 B +
              ENNReal.ofReal (1 - p.1) * Measure.dirac p.2 B)) p} =
          {p | (fun p : ℝ × ℝ ↦
            ((ENNReal.ofReal M)⁻¹ * ENNReal.ofReal (p.2 - p.1)) *
              twoPointMeasure p.1 p.2 B) p ≤
            (fun p ↦ (ENNReal.ofReal M)⁻¹ *
              (ENNReal.ofReal (p.2 - 1) * Measure.dirac p.1 B +
                ENNReal.ofReal (1 - p.1) * Measure.dirac p.2 B)) p} ∩
          {p | (fun p : ℝ × ℝ ↦ (ENNReal.ofReal M)⁻¹ *
              (ENNReal.ofReal (p.2 - 1) * Measure.dirac p.1 B +
                ENNReal.ofReal (1 - p.1) * Measure.dirac p.2 B)) p ≤
            (fun p ↦
              ((ENNReal.ofReal M)⁻¹ * ENNReal.ofReal (p.2 - p.1)) *
                twoPointMeasure p.1 p.2 B) p} by
            ext p
            simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, le_antisymm_iff]]
      exact (measurableSet_le hf hg).inter (measurableSet_le hg hf))).2
    filter_upwards [ae_restrict_mem measurableSet_Iio] with x hx
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hs := twoPointMeasure_scaled_apply hx.le hy.le (hx.trans hy) B
    calc
      ((ENNReal.ofReal M)⁻¹ * ENNReal.ofReal (y - x)) *
          twoPointMeasure x y B =
        (ENNReal.ofReal M)⁻¹ *
          (ENNReal.ofReal (y - x) * twoPointMeasure x y B) := by ac_rfl
      _ = _ := by rw [hs]
  change (∫⁻ p : ℝ × ℝ,
      ((ENNReal.ofReal M)⁻¹ * ENNReal.ofReal (p.2 - p.1)) *
        twoPointMeasure p.1 p.2 B
      ∂(μ.restrict (Iio 1)).prod (μ.restrict (Ioi 1))) = _
  rw [lintegral_congr_ae hae]
  have hterm1 : Measurable (fun p : ℝ × ℝ ↦
      ENNReal.ofReal (p.2 - 1) * Measure.dirac p.1 B) :=
    (measurable_snd.sub measurable_const).ennreal_ofReal.mul
      (hdirac.comp measurable_fst)
  have hterm2 : Measurable (fun p : ℝ × ℝ ↦
      ENNReal.ofReal (1 - p.1) * Measure.dirac p.2 B) :=
    (measurable_const.sub measurable_fst).ennreal_ofReal.mul
      (hdirac.comp measurable_snd)
  rw [lintegral_const_mul]
  case hf => exact hterm1.add hterm2
  rw [lintegral_add_left hterm1]
  have hfirst :
      (∫⁻ p : ℝ × ℝ,
          ENNReal.ofReal (p.2 - 1) * Measure.dirac p.1 B
          ∂(μ.restrict (Iio 1)).prod (μ.restrict (Ioi 1))) =
        μ.restrict (Iio 1) B * ENNReal.ofReal (aboveMoment μ) := by
    rw [show (fun p : ℝ × ℝ ↦
        ENNReal.ofReal (p.2 - 1) * Measure.dirac p.1 B) =
      fun p ↦ Measure.dirac p.1 B * ENNReal.ofReal (p.2 - 1) by
        funext p; ac_rfl]
    rw [lintegral_prod_mul
      (μ := μ.restrict (Iio 1)) (ν := μ.restrict (Ioi 1))
      (f := fun x ↦ Measure.dirac x B)
      (g := fun y ↦ ENNReal.ofReal (y - 1))
      hdirac.aemeasurable (by fun_prop)]
    rw [show (∫⁻ x, Measure.dirac x B ∂μ.restrict (Iio 1)) =
        μ.restrict (Iio 1) B by
          simp only [Measure.dirac_apply' _ hB]
          rw [← lintegral_indicator_one hB]]
    rw [← ofReal_aboveMoment_eq_lintegral_Ioi hμ]
  have hsecond :
      (∫⁻ p : ℝ × ℝ,
          ENNReal.ofReal (1 - p.1) * Measure.dirac p.2 B
          ∂(μ.restrict (Iio 1)).prod (μ.restrict (Ioi 1))) =
        ENNReal.ofReal (belowMoment μ) * μ.restrict (Ioi 1) B := by
    rw [lintegral_prod_mul
      (μ := μ.restrict (Iio 1)) (ν := μ.restrict (Ioi 1))
      (f := fun x ↦ ENNReal.ofReal (1 - x))
      (g := fun y ↦ Measure.dirac y B)
      (by fun_prop) hdirac.aemeasurable]
    rw [show (∫⁻ y, Measure.dirac y B ∂μ.restrict (Ioi 1)) =
        μ.restrict (Ioi 1) B by
          simp only [Measure.dirac_apply' _ hB]
          rw [← lintegral_indicator_one hB]]
    rw [← ofReal_belowMoment_eq_lintegral_Iio hμ]
  rw [hfirst, hsecond, mul_comm (μ.restrict (Iio 1) B)]

/-- The measurable-kernel construction agrees with the direct expansion of
the two-point mixture formula. -/
theorem fullKernelMixture_eq_expanded
    {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hμ : Integrable (fun x : ℝ ↦ x) μ) (M : ℝ) :
    fullKernelMixture μ M = expandedTwoPointMixture μ M := by
  ext B hB
  rw [fullKernelMixture, expandedTwoPointMixture, Measure.add_apply,
    Measure.add_apply, nondegenerateKernelMixture_apply_expanded hμ M hB]
  simp only [Measure.smul_apply, Measure.add_apply, smul_eq_mul]

/-- For a mean-one probability law with a nonzero lower moment, sampling the
latent pair and then the corresponding two-point law reconstructs the
original law. -/
theorem fullKernelMixture_eq
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ ↦ x) μ)
    (hmean : (∫ x : ℝ, x ∂μ) = 1)
    (hM : 0 < belowMoment μ) :
    fullKernelMixture μ (belowMoment μ) = μ := by
  rw [fullKernelMixture_eq_expanded hμ,
    expandedTwoPointMixture_eq hμ hmean hM]

end

end Feige

end

/- ===== Vendor/LeanPool/AugmentedTwoPointKernel.lean ===== -/
section

/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
-- Vendored from LeanPool/lean-pool (https://github.com/LeanPool/lean-pool),
-- file LeanPool/Feige/AugmentedTwoPointKernel.lean at commit 9decab6341e6b0fd82bd7f9763a5dd7a9ce8778d, Apache-2.0 (see LICENSE in this folder).
-- Changes: import paths renamed from `LeanPool.Feige.*` to `Feige.Vendor.LeanPool.*`.
-- Portability (Left to Solve CI, Lean v4.33.1): `add_apply`/`smul_apply` qualified as `Measure.*`,
-- `ite_eq_left/right` replaced by `if_pos/if_neg`, and small elaboration fixes where needed.



/-!
# An augmented latent kernel

The extra `Unit` branch records the atom at one.  The other branch records a
strict below/above pair.  Thus a single latent parameter always determines a
mean-one law supported on at most two points.
-/


open MeasureTheory ProbabilityTheory Set

namespace Feige

noncomputable section

/-- A latent coordinate is either the distinguished atom at one or a genuine
strict two-point parameter. -/
abbrev AugmentedTwoPointParams := Unit ⊕ TwoPointParams

/-- The conditional coordinate kernel attached to an augmented parameter. -/
noncomputable def augmentedTwoPointKernel : Kernel AugmentedTwoPointParams ℝ where
  toFun := Sum.elim (fun _ ↦ Measure.dirac 1) twoPointKernel
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun B hB ↦ ?_
    exact measurable_const.sumElim (twoPointKernel.measurable_coe hB)

@[simp]
theorem augmentedTwoPointKernel_atom :
    augmentedTwoPointKernel (Sum.inl ()) = Measure.dirac 1 :=
  by simp [augmentedTwoPointKernel]

@[simp]
theorem augmentedTwoPointKernel_pair (p : TwoPointParams) :
    augmentedTwoPointKernel (Sum.inr p) = twoPointMeasure p.1.1 p.1.2 :=
  by simp [augmentedTwoPointKernel]

instance : IsMarkovKernel augmentedTwoPointKernel where
  isProbabilityMeasure p := by
    cases p with
    | inl u =>
        cases u
        rw [augmentedTwoPointKernel_atom]
        infer_instance
    | inr p =>
        rw [augmentedTwoPointKernel_pair]
        exact twoPointMeasure_isProbability p.2.1 p.2.2.1 p.2.2.2

/-- Every conditional law selected by an augmented parameter has mean one. -/
theorem augmentedTwoPointKernel_mean (p : AugmentedTwoPointParams) :
    (∫ x : ℝ, x ∂(augmentedTwoPointKernel p)) = 1 := by
  cases p with
  | inl u =>
      cases u
      simp
  | inr p =>
      rw [augmentedTwoPointKernel_pair]
      exact twoPointMeasure_mean p.2.1 p.2.2.1 p.2.2.2

/-- Every conditional law is concentrated on either one point or the two
points encoded by its latent parameter. -/
theorem augmentedTwoPointKernel_support
    (p : AugmentedTwoPointParams) :
    augmentedTwoPointKernel p
        (match p with
          | Sum.inl _ => ({1} : Set ℝ)ᶜ
          | Sum.inr q => ({q.1.1, q.1.2} : Set ℝ)ᶜ) = 0 := by
  cases p with
  | inl u =>
      cases u
      simp
  | inr p =>
      rw [augmentedTwoPointKernel_pair, twoPointMeasure]
      simp only [Measure.add_apply, Measure.smul_apply,
        Measure.dirac_apply' _
          (measurableSet_insert.mpr (measurableSet_singleton _)).compl]
      simp

/-- The complete latent law: its left branch carries the atom at one, and its
right branch carries the nondegenerate parameter measure. -/
noncomputable def augmentedLatentMeasure (μ : Measure ℝ) (M : ℝ) :
    Measure AugmentedTwoPointParams :=
  μ {1} • Measure.dirac (Sum.inl ()) +
    (latentParamsMeasure μ M).map Sum.inr

theorem augmentedLatentMeasure_apply_atom
    (μ : Measure ℝ) (M : ℝ) :
    augmentedLatentMeasure μ M (Set.range Sum.inl) = μ {1} := by
  rw [augmentedLatentMeasure, Measure.add_apply,
    Measure.smul_apply, Measure.map_apply measurable_inr measurableSet_range_inl]
  simp

/-- Binding the augmented latent law against its conditional kernel gives
exactly the full one-coordinate mixture. -/
theorem augmentedTwoPointKernel_comp_latent
    (μ : Measure ℝ) (M : ℝ) :
    augmentedTwoPointKernel ∘ₘ augmentedLatentMeasure μ M =
      fullKernelMixture μ M := by
  ext B hB
  rw [Measure.bind_apply hB augmentedTwoPointKernel.aemeasurable]
  rw [augmentedLatentMeasure, lintegral_add_measure]
  · rw [lintegral_smul_measure]
    rw [lintegral_dirac' _ (augmentedTwoPointKernel.measurable_coe hB)]
    rw [lintegral_map' (by
      exact (augmentedTwoPointKernel.measurable_coe hB).aemeasurable)
      measurable_inr.aemeasurable]
    simp only [augmentedTwoPointKernel_atom, augmentedTwoPointKernel_pair]
    change μ {1} * Measure.dirac 1 B +
        ∫⁻ p, twoPointMeasure p.1.1 p.1.2 B ∂latentParamsMeasure μ M =
      fullKernelMixture μ M B
    rw [← kernelTwoPointMixture_apply (latentParamsMeasure μ M) hB]
    rfl

/-- Under the hypotheses of the decomposition, the complete latent law is
itself a probability measure. -/
theorem augmentedLatentMeasure_isProbability
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ ↦ x) μ)
    (hmean : (∫ x : ℝ, x ∂μ) = 1)
    (hM : 0 < belowMoment μ) :
    IsProbabilityMeasure
      (augmentedLatentMeasure μ (belowMoment μ)) := by
  constructor
  have hfull :
      fullKernelMixture μ (belowMoment μ) Set.univ = 1 :=
    (fullKernelMixture_isProbability hμ hmean hM).measure_univ
  rw [← augmentedTwoPointKernel_comp_latent μ (belowMoment μ),
    Measure.bind_apply MeasurableSet.univ
      augmentedTwoPointKernel.aemeasurable] at hfull
  have hpoint :
      (fun p : AugmentedTwoPointParams ↦
        augmentedTwoPointKernel p Set.univ) = fun _ ↦ (1 : ENNReal) := by
    funext p
    let : IsProbabilityMeasure (augmentedTwoPointKernel p) :=
      inferInstance
    exact measure_univ
  rw [hpoint, lintegral_one] at hfull
  exact hfull

/-- The bind/Tonelli identity for the complete one-coordinate latent
decomposition. -/
theorem lintegral_augmentedTwoPointKernel_comp
    (μ : Measure ℝ) (M : ℝ) (f : ℝ → ENNReal)
    (hf : Measurable f) :
    (∫⁻ x, f x ∂fullKernelMixture μ M) =
      ∫⁻ p, ∫⁻ x, f x ∂augmentedTwoPointKernel p
        ∂augmentedLatentMeasure μ M := by
  rw [← augmentedTwoPointKernel_comp_latent μ M]
  exact Measure.lintegral_bind
    augmentedTwoPointKernel.aemeasurable hf.aemeasurable

end

end Feige

end

/- ===== Vendor/LeanPool/ProductTwoPointKernel.lean ===== -/
section

/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
-- Vendored from LeanPool/lean-pool (https://github.com/LeanPool/lean-pool),
-- file LeanPool/Feige/ProductTwoPointKernel.lean at commit 9decab6341e6b0fd82bd7f9763a5dd7a9ce8778d, Apache-2.0 (see LICENSE in this folder).
-- Changes: import paths renamed from `LeanPool.Feige.*` to `Feige.Vendor.LeanPool.*`.
-- Portability (Left to Solve CI, Lean v4.33.1): `add_apply`/`smul_apply` qualified as `Measure.*`,
-- `ite_eq_left/right` replaced by `if_pos/if_neg`, and small elaboration fixes where needed.



/-!
# Coordinatewise two-point mixtures

This file lifts the one-dimensional measurable two-point decomposition to a
finite independent product.  It is the product-measure interface used in the
proof of Theorem 2.1 before conditioning on all latent pairs.
-/


open MeasureTheory ProbabilityTheory Set

namespace Feige

noncomputable section

/-- Given all latent coordinates, the observations are conditionally
independent with the augmented two-point conditional marginals. -/
noncomputable def augmentedConditionalProduct {n : ℕ}
    (p : Fin n → AugmentedTwoPointParams) : Measure (Fin n → ℝ) :=
  Measure.pi (fun i ↦ augmentedTwoPointKernel (p i))

instance {n : ℕ} (p : Fin n → AugmentedTwoPointParams) :
    IsProbabilityMeasure (augmentedConditionalProduct p) := by
  unfold augmentedConditionalProduct
  infer_instance

/-- Each coordinate of every conditional product is a mean-one law. -/
theorem augmentedConditionalProduct_coordinate_mean {n : ℕ}
    (p : Fin n → AugmentedTwoPointParams) (i : Fin n) :
    (∫ x : ℝ, x ∂augmentedTwoPointKernel (p i)) = 1 :=
  augmentedTwoPointKernel_mean (p i)

/-- Each coordinate of every conditional product is supported on at most two
points (one point on the atom branch). -/
theorem augmentedConditionalProduct_coordinate_support {n : ℕ}
    (p : Fin n → AugmentedTwoPointParams) (i : Fin n) :
    augmentedTwoPointKernel (p i)
        (match p i with
          | Sum.inl _ => ({1} : Set ℝ)ᶜ
          | Sum.inr q => ({q.1.1, q.1.2} : Set ℝ)ᶜ) = 0 :=
  augmentedTwoPointKernel_support (p i)

/-- Binary Fubini exchange: independently binding two latent laws against
their coordinate kernels is the same as binding their product against the
parallel product kernel.  This is the recursion step needed for a finite
product. -/
theorem parallelComp_comp_prod_measure
    {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace δ]
    (κ : Kernel α β) [IsSFiniteKernel κ]
    (η : Kernel γ δ) [IsSFiniteKernel η]
    (μ : Measure α) (ν : Measure γ) [SFinite μ] [SFinite ν] :
    (κ ∥ₖ η) ∘ₘ (μ.prod ν) = (κ ∘ₘ μ).prod (η ∘ₘ ν) := by
  symm
  calc
    (κ ∘ₘ μ).prod (η ∘ₘ ν) =
      (κ ∥ₖ Kernel.id) ∘ₘ (μ.prod (η ∘ₘ ν)) := by
        rw [← Measure.prod_comp_left]
    _ = (κ ∥ₖ Kernel.id) ∘ₘ
        ((Kernel.id ∥ₖ η) ∘ₘ (μ.prod ν)) := by
          rw [← Measure.prod_comp_right]
    _ = ((κ ∥ₖ Kernel.id) ∘ₖ (Kernel.id ∥ₖ η)) ∘ₘ
        (μ.prod ν) := by rw [Measure.comp_assoc]
    _ = (κ ∥ₖ η) ∘ₘ (μ.prod ν) := by
      rw [Kernel.parallelComp_id_right_comp_parallelComp, Kernel.comp_id]

section RecursiveFiniteKernel

/-- Measurable head/tail splitting of a homogeneous `Fin (n+1)` vector. -/
noncomputable def finHeadTailEquiv (α : Type*) [MeasurableSpace α] (n : ℕ) :
    (Fin (n + 1) → α) ≃ᵐ α × (Fin n → α) :=
  MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) 0

/-- A genuinely measurable finite parallel product of the augmented
coordinate kernels.  This avoids the unavailable `Kernel.pi`: the successor
case splits head and tail, uses `parallelComp`, and maps the output pair back
to a `Fin (n+1)` vector. -/
noncomputable def recursiveAugmentedKernel :
    (n : ℕ) → Kernel (Fin n → AugmentedTwoPointParams) (Fin n → ℝ)
  | 0 => Kernel.const _ (Measure.dirac (fun i => Fin.elim0 i))
  | n + 1 =>
      (((augmentedTwoPointKernel ∥ₖ recursiveAugmentedKernel n).comap
          (finHeadTailEquiv AugmentedTwoPointParams n)
          (finHeadTailEquiv AugmentedTwoPointParams n).measurable).map
        (finHeadTailEquiv ℝ n).symm)

instance recursiveAugmentedKernel_markov (n : ℕ) :
    IsMarkovKernel (recursiveAugmentedKernel n) := by
  induction n with
  | zero =>
      unfold recursiveAugmentedKernel
      infer_instance
  | succ n ih =>
      let : IsMarkovKernel (recursiveAugmentedKernel n) := ih
      unfold recursiveAugmentedKernel
      exact Kernel.IsMarkovKernel.map _
        (finHeadTailEquiv ℝ n).symm.measurable

/-- Binding is invariant under simultaneous measurable-equivalence changes
of latent and observation coordinates. -/
theorem bind_congr_measurableEquiv
    {α α' β β' : Type*} [MeasurableSpace α] [MeasurableSpace α']
    [MeasurableSpace β] [MeasurableSpace β']
    (κ : Kernel α β) (μ : Measure α)
    (eα : α' ≃ᵐ α) (eβ : β' ≃ᵐ β) :
    ((κ.comap eα eα.measurable).map eβ.symm) ∘ₘ
        (μ.map eα.symm) =
      (κ ∘ₘ μ).map eβ.symm := by
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _),
    Measure.map_apply eβ.symm.measurable hs,
    Measure.bind_apply (hs.preimage eβ.symm.measurable) κ.aemeasurable]
  rw [lintegral_map' (by
      exact (Kernel.measurable_coe _ hs).aemeasurable)
    eα.symm.measurable.aemeasurable]
  apply lintegral_congr
  intro a
  rw [Kernel.map_apply' _ eβ.symm.measurable _ hs,
    Kernel.comap_apply]
  simp

/-- Recursive latent product aligned definitionally with
`recursiveAugmentedKernel`. -/
noncomputable def recursiveAugmentedLatent :
    (n : ℕ) → (Fin n → Measure AugmentedTwoPointParams) →
      Measure (Fin n → AugmentedTwoPointParams)
  | 0 => fun _ => Measure.dirac (fun i => Fin.elim0 i)
  | Nat.succ n => fun latent =>
      ((latent 0).prod
        (recursiveAugmentedLatent n (fun i => latent (Fin.succ i)))).map
          (finHeadTailEquiv AugmentedTwoPointParams n).symm

/-- The analogous head/tail recursive product of observation marginals. -/
noncomputable def recursiveRealProduct :
    (n : ℕ) → (Fin n → Measure ℝ) → Measure (Fin n → ℝ)
  | 0 => fun _ => Measure.dirac (fun i => Fin.elim0 i)
  | Nat.succ n => fun μ =>
      ((μ 0).prod (recursiveRealProduct n (fun i => μ (Fin.succ i)))).map
        (finHeadTailEquiv ℝ n).symm

instance recursiveAugmentedLatent_sfinite
    (n : ℕ) (latent : Fin n → Measure AugmentedTwoPointParams)
    [∀ i, SFinite (latent i)] :
    SFinite (recursiveAugmentedLatent n latent) := by
  induction n with
  | zero =>
      unfold recursiveAugmentedLatent
      infer_instance
  | succ n ih =>
      let : ∀ i : Fin n, SFinite (latent (Fin.succ i)) :=
        fun i => inferInstance
      have htail : SFinite
          (recursiveAugmentedLatent n (fun i => latent (Fin.succ i))) :=
        ih (fun i => latent (Fin.succ i))
      let := htail
      unfold recursiveAugmentedLatent
      infer_instance

/-- Finite recursive product-of-binds theorem.  This is the full induction:
the binary Fubini step handles head/tail and the measurable-equivalence
conjugation returns to `Fin (n+1)` coordinates. -/
theorem recursiveAugmentedKernel_comp_latent
    (n : ℕ) (latent : Fin n → Measure AugmentedTwoPointParams)
    [∀ i, SFinite (latent i)] :
    recursiveAugmentedKernel n ∘ₘ
        recursiveAugmentedLatent n latent =
      recursiveRealProduct n
        (fun i => augmentedTwoPointKernel ∘ₘ latent i) := by
  induction n with
  | zero =>
      unfold recursiveAugmentedKernel recursiveAugmentedLatent
        recursiveRealProduct
      simp
  | succ n ih =>
      let : ∀ i : Fin n, SFinite (latent (Fin.succ i)) :=
        fun i => inferInstance
      let : IsMarkovKernel (recursiveAugmentedKernel n) :=
        recursiveAugmentedKernel_markov n
      unfold recursiveAugmentedKernel recursiveAugmentedLatent
        recursiveRealProduct
      rw [bind_congr_measurableEquiv]
      rw [parallelComp_comp_prod_measure]
      rw [ih (fun i => latent (Fin.succ i))]

/-- Zero-dimensional recursive product. -/
theorem recursiveRealProduct_zero (μ : Fin 0 → Measure ℝ) :
    recursiveRealProduct 0 μ =
      Measure.dirac (fun i : Fin 0 => Fin.elim0 i) := rfl

/-- The head/tail recursive product is the standard finite `Measure.pi`. -/
theorem recursiveRealProduct_eq_pi
    (n : ℕ) (μ : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] :
    recursiveRealProduct n μ = Measure.pi μ := by
  induction n with
  | zero =>
      rw [recursiveRealProduct_zero, Measure.pi_of_empty]
      exact congrArg Measure.dirac (Subsingleton.elim _ _)
  | succ n ih =>
      let : ∀ i : Fin n, IsProbabilityMeasure (μ (Fin.succ i)) :=
        fun i => inferInstance
      change
        ((μ 0).prod
          (recursiveRealProduct n (fun i => μ (Fin.succ i)))).map
            (finHeadTailEquiv ℝ n).symm = Measure.pi μ
      rw [ih (fun i => μ (Fin.succ i))]
      have hmp := MeasureTheory.measurePreserving_piFinSuccAbove
        (fun i : Fin (n + 1) => μ i) 0
      exact hmp.symm.map_eq

end RecursiveFiniteKernel

end

end Feige

end

/- ===== Vendor/LeanPool/RecursiveLatentProbability.lean ===== -/
section

/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
-- Vendored from LeanPool/lean-pool (https://github.com/LeanPool/lean-pool),
-- file LeanPool/Feige/RecursiveLatentProbability.lean at commit 9decab6341e6b0fd82bd7f9763a5dd7a9ce8778d, Apache-2.0 (see LICENSE in this folder).
-- Changes: import paths renamed from `LeanPool.Feige.*` to `Feige.Vendor.LeanPool.*`.
-- Portability (Left to Solve CI, Lean v4.33.1): `add_apply`/`smul_apply` qualified as `Measure.*`,
-- `ite_eq_left/right` replaced by `if_pos/if_neg`, and small elaboration fixes where needed.



/-!
# Probability instance for the recursive latent product
-/


open MeasureTheory

namespace Feige

noncomputable section

instance recursiveAugmentedLatent_isProbability
    (n : ℕ)
    (latent : Fin n → Measure AugmentedTwoPointParams)
    [∀ i, IsProbabilityMeasure (latent i)] :
    IsProbabilityMeasure (recursiveAugmentedLatent n latent) := by
  induction n with
  | zero =>
      unfold recursiveAugmentedLatent
      infer_instance
  | succ n ih =>
      let : ∀ i : Fin n,
          IsProbabilityMeasure (latent (Fin.succ i)) :=
        fun i ↦ inferInstance
      let : IsProbabilityMeasure
          (recursiveAugmentedLatent n
            (fun i ↦ latent (Fin.succ i))) :=
        ih (fun i ↦ latent (Fin.succ i))
      unfold recursiveAugmentedLatent
      exact (Measure.isProbabilityMeasure_map_iff
        (finHeadTailEquiv AugmentedTwoPointParams n).symm.measurable.aemeasurable).mpr
          inferInstance

end

end Feige

end

/- ===== Vendor/LeanPool/MeanOneAugmentedMixture.lean ===== -/
section

/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
-- Vendored from LeanPool/lean-pool (https://github.com/LeanPool/lean-pool),
-- file LeanPool/Feige/MeanOneAugmentedMixture.lean at commit 9decab6341e6b0fd82bd7f9763a5dd7a9ce8778d, Apache-2.0 (see LICENSE in this folder).
-- Changes: import paths renamed from `LeanPool.Feige.*` to `Feige.Vendor.LeanPool.*`.
-- Portability (Left to Solve CI, Lean v4.33.1): `add_apply`/`smul_apply` qualified as `Measure.*`,
-- `ite_eq_left/right` replaced by `if_pos/if_neg`, and small elaboration fixes where needed.



/-!
# A total augmented mixture for mean-one laws

The positive-moment branch uses the latent two-point measure from Lemma
4.6.  When the lower moment vanishes, the original law is `δ₁`, so the
latent law is simply the atom branch.  This removes the artificial
coordinatewise strict-moment assumption from the finite product mixture.
-/


open MeasureTheory ProbabilityTheory

namespace Feige

noncomputable section

/-- The augmented latent law, including the degenerate zero-below-moment case. -/
def meanOneAugmentedLatent (μ : Measure ℝ) :
    Measure AugmentedTwoPointParams :=
  if belowMoment μ = 0 then
    Measure.dirac (Sum.inl ())
  else
    augmentedLatentMeasure μ (belowMoment μ)

theorem meanOneAugmentedLatent_isProbability
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ ↦ x) μ)
    (hmean : (∫ x : ℝ, x ∂μ) = 1) :
    IsProbabilityMeasure (meanOneAugmentedLatent μ) := by
  by_cases hM : belowMoment μ = 0
  · rw [meanOneAugmentedLatent, if_pos hM]
    infer_instance
  · rw [meanOneAugmentedLatent, if_neg hM]
    exact augmentedLatentMeasure_isProbability hμ hmean
      (lt_of_le_of_ne belowMoment_nonneg (Ne.symm hM))

theorem augmentedTwoPointKernel_comp_meanOneLatent
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ ↦ x) μ)
    (hmean : (∫ x : ℝ, x ∂μ) = 1) :
    augmentedTwoPointKernel ∘ₘ meanOneAugmentedLatent μ = μ := by
  by_cases hM : belowMoment μ = 0
  · rw [meanOneAugmentedLatent, if_pos hM]
    rw [Measure.dirac_bind augmentedTwoPointKernel.measurable]
    rw [augmentedTwoPointKernel_atom]
    exact (eq_dirac_one_of_belowMoment_eq_zero
      hμ hmean hM).symm
  · rw [meanOneAugmentedLatent, if_neg hM,
      augmentedTwoPointKernel_comp_latent,
      fullKernelMixture_eq hμ hmean
        (lt_of_le_of_ne belowMoment_nonneg (Ne.symm hM))]

/-- Every finite product of mean-one laws is a mixture of the conditionally
independent augmented two-point systems, including all degenerate `δ₁`
coordinates. -/
theorem pi_eq_recursiveMeanOneAugmented_mixture
    (n : ℕ) (μ : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)]
    (hμ : ∀ i, Integrable (fun x : ℝ ↦ x) (μ i))
    (hmean : ∀ i, (∫ x : ℝ, x ∂μ i) = 1) :
    recursiveAugmentedKernel n ∘ₘ
        recursiveAugmentedLatent n
          (fun i ↦ meanOneAugmentedLatent (μ i)) =
      Measure.pi μ := by
  let hlatent : ∀ i, IsProbabilityMeasure
      (meanOneAugmentedLatent (μ i)) :=
    fun i ↦ meanOneAugmentedLatent_isProbability
      (hμ i) (hmean i)
  rw [recursiveAugmentedKernel_comp_latent]
  have hcoord :
      (fun i => augmentedTwoPointKernel ∘ₘ
          meanOneAugmentedLatent (μ i)) = μ := by
    funext i
    exact augmentedTwoPointKernel_comp_meanOneLatent
      (hμ i) (hmean i)
  rw [hcoord, recursiveRealProduct_eq_pi]

end

end Feige

end

/- ===== Vendor/LeanPool/ConditionalProductKernel.lean ===== -/
section

/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
-- Vendored from LeanPool/lean-pool (https://github.com/LeanPool/lean-pool),
-- file LeanPool/Feige/ConditionalProductKernel.lean at commit 9decab6341e6b0fd82bd7f9763a5dd7a9ce8778d, Apache-2.0 (see LICENSE in this folder).
-- Changes: import paths renamed from `LeanPool.Feige.*` to `Feige.Vendor.LeanPool.*`.
-- Portability (Left to Solve CI, Lean v4.33.1): `add_apply`/`smul_apply` qualified as `Measure.*`,
-- `ite_eq_left/right` replaced by `if_pos/if_neg`, and small elaboration fixes where needed.



/-!
# Conditional product law of the recursive augmented kernel

The recursively measurable kernel used for the finite mixture construction
has, at every fixed latent parameter vector, exactly the ordinary finite
product of the selected one-coordinate laws.
-/


open MeasureTheory ProbabilityTheory

namespace Feige

noncomputable section

theorem recursiveAugmentedKernel_apply_eq_conditionalProduct
    (n : ℕ) (p : Fin n → AugmentedTwoPointParams) :
    recursiveAugmentedKernel n p = augmentedConditionalProduct p := by
  induction n with
  | zero =>
      unfold recursiveAugmentedKernel augmentedConditionalProduct
      rw [Measure.pi_of_empty]
      congr
  | succ n ih =>
      unfold recursiveAugmentedKernel augmentedConditionalProduct
      rw [Kernel.map_apply _ (finHeadTailEquiv ℝ n).symm.measurable]
      rw [Kernel.comap_apply]
      rw [Kernel.parallelComp_apply]
      change
        Measure.map (finHeadTailEquiv ℝ n).symm
          ((augmentedTwoPointKernel (p 0)).prod
            (recursiveAugmentedKernel n
              (fun i : Fin n ↦ p (Fin.succ i)))) =
          Measure.pi (fun i : Fin (n + 1) ↦ augmentedTwoPointKernel (p i))
      rw [ih (fun i : Fin n ↦ p (Fin.succ i))]
      unfold augmentedConditionalProduct
      exact
        (measurePreserving_piFinSuccAbove
          (fun i : Fin (n + 1) ↦ augmentedTwoPointKernel (p i)) 0).symm.map_eq

end

end Feige

end

/- ===== Vendor/LeanPool/TwoPointParameters.lean ===== -/
section

/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
-- Vendored from LeanPool/lean-pool (https://github.com/LeanPool/lean-pool),
-- file LeanPool/Feige/TwoPoint.lean at commit 9decab6341e6b0fd82bd7f9763a5dd7a9ce8778d, Apache-2.0 (see LICENSE in this folder).
-- Changes: only the `Parameters` section is kept (the Boolean-lattice / Dirichlet-statistic part
-- is not needed here), so the import of `LeanPool.Feige.KStatistic` is replaced by Mathlib.
-- Portability (Left to Solve CI, Lean v4.33.1): `add_apply`/`smul_apply` qualified as `Measure.*`,
-- `ite_eq_left/right` replaced by `if_pos/if_neg`, and small elaboration fixes where needed.


/-!
# Mean-one two-point parameters (excerpt of LeanPool's `TwoPoint.lean`)
-/


namespace Feige

section Parameters

/-- Probability of the high value in a mean-one two-point law. -/
noncomputable def highProbability (γ β : ℝ) : ℝ :=
  γ / (γ + β)

/-- The low value in the mean-one two-point parametrization. -/
def lowValue (γ : ℝ) : ℝ := 1 - γ

/-- The high value in the mean-one two-point parametrization. -/
def highValue (β : ℝ) : ℝ := 1 + β

theorem highProbability_nonneg {γ β : ℝ} (hγ : 0 ≤ γ) (hβ : 0 < β) :
    0 ≤ highProbability γ β := by
  exact div_nonneg hγ (add_pos_of_nonneg_of_pos hγ hβ).le

theorem highProbability_le_one {γ β : ℝ} (hγ : 0 ≤ γ) (hβ : 0 < β) :
    highProbability γ β ≤ 1 := by
  rw [highProbability, div_le_one (add_pos_of_nonneg_of_pos hγ hβ)]
  linarith

/-- The complementary probability in symmetric form. -/
theorem one_sub_highProbability {γ β : ℝ} (h : γ + β ≠ 0) :
    1 - highProbability γ β = β / (γ + β) := by
  rw [highProbability]
  field_simp
  ring

/-- The parametrized two-point law has mean exactly one. -/
theorem twoPoint_mean_one {γ β : ℝ} (h : γ + β ≠ 0) :
    highProbability γ β * highValue β +
        (1 - highProbability γ β) * lowValue γ = 1 := by
  rw [one_sub_highProbability h]
  simp only [highProbability, highValue, lowValue]
  field_simp
  ring

end Parameters

end Feige

end

/- ===== Vendor/LeanPool/AugmentedParameterization.lean ===== -/
section

/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
-- Vendored from LeanPool/lean-pool (https://github.com/LeanPool/lean-pool),
-- file LeanPool/Feige/AugmentedParameterization.lean at commit 9decab6341e6b0fd82bd7f9763a5dd7a9ce8778d, Apache-2.0 (see LICENSE in this folder).
-- Changes: import paths renamed from `LeanPool.Feige.*` to `Feige.Vendor.LeanPool.*`.
-- Portability (Left to Solve CI, Lean v4.33.1): `add_apply`/`smul_apply` qualified as `Measure.*`,
-- `ite_eq_left/right` replaced by `if_pos/if_neg`, and small elaboration fixes where needed.



/-!
# Two-point parameters for augmented latent coordinates

The atom-at-one branch is represented by the harmless degenerate
parametrization `γ = 0`, `β = 1`.  A genuine support pair `(x,y)` is
represented by `γ = 1-x`, `β = y-1`.
-/


open MeasureTheory

namespace Feige

noncomputable section

/-- The lower displacement encoded by an augmented parameter. -/
def augmentedGamma (p : AugmentedTwoPointParams) : ℝ :=
  match p with
  | Sum.inl _ => 0
  | Sum.inr q => 1 - q.1.1

/-- The upper displacement encoded by an augmented parameter. -/
def augmentedBeta (p : AugmentedTwoPointParams) : ℝ :=
  match p with
  | Sum.inl _ => 1
  | Sum.inr q => q.1.2 - 1

/-- The nonnegativity condition on an augmented two-point parameter. -/
def AugmentedParamNonnegative (p : AugmentedTwoPointParams) : Prop :=
  match p with
  | Sum.inl _ => True
  | Sum.inr q => 0 ≤ q.1.1 ∧ 1 < q.1.2

/-- The condition enjoyed by latent parameters sampled from a
nonnegative mean-one law: genuine lower support points are nonnegative and
genuine upper support points are strictly above one. -/
def AugmentedParamsNonnegative {n : ℕ}
    (p : Fin n → AugmentedTwoPointParams) : Prop :=
  ∀ i, AugmentedParamNonnegative (p i)

theorem augmentedGamma_nonneg {n : ℕ}
    {p : Fin n → AugmentedTwoPointParams} :
    ∀ i, 0 ≤ augmentedGamma (p i) := by
  intro i
  cases hpi : p i with
  | inl u => simp [augmentedGamma]
  | inr q =>
      change 0 ≤ 1 - q.1.1
      exact sub_nonneg.mpr q.2.1

theorem augmentedGamma_le_one {n : ℕ}
    {p : Fin n → AugmentedTwoPointParams}
    (hp : AugmentedParamsNonnegative p) :
    ∀ i, augmentedGamma (p i) ≤ 1 := by
  intro i
  specialize hp i
  cases hpi : p i with
  | inl u => simp [augmentedGamma]
  | inr q =>
      simp only [hpi] at hp
      change 1 - q.1.1 ≤ 1
      linarith [hp.1]

theorem augmentedBeta_pos {n : ℕ}
    {p : Fin n → AugmentedTwoPointParams}
    (hp : AugmentedParamsNonnegative p) :
    ∀ i, 0 < augmentedBeta (p i) := by
  intro i
  specialize hp i
  cases hpi : p i with
  | inl u => simp [augmentedBeta]
  | inr q =>
      simp only [hpi] at hp
      change 0 < q.1.2 - 1
      linarith [hp.2]

/-- Both branches of the augmented kernel are exactly the canonical
mean-one two-point measure for their `γ,β` parameters. -/
theorem augmentedTwoPointKernel_eq_twoPointMeasure
    (p : AugmentedTwoPointParams) :
    augmentedTwoPointKernel p =
      twoPointMeasure (lowValue (augmentedGamma p))
        (highValue (augmentedBeta p)) := by
  cases p with
  | inl u =>
      cases u
      rw [augmentedTwoPointKernel_atom]
      simp [augmentedGamma, augmentedBeta, lowValue, highValue,
        twoPointMeasure, twoPointLowerWeight, twoPointUpperWeight]
  | inr q =>
      rw [augmentedTwoPointKernel_pair]
      congr 1
      · simp [augmentedGamma, lowValue]
      · simp [augmentedBeta, highValue]

theorem augmentedConditionalProduct_eq_twoPointProduct {n : ℕ}
    (p : Fin n → AugmentedTwoPointParams) :
    augmentedConditionalProduct p =
      Measure.pi (fun i ↦
        twoPointMeasure (lowValue (augmentedGamma (p i)))
          (highValue (augmentedBeta (p i)))) := by
  unfold augmentedConditionalProduct
  congr 1
  funext i
  exact augmentedTwoPointKernel_eq_twoPointMeasure (p i)

end

end Feige

end

/- ===== Vendor/LeanPool/AugmentedLatentSupport.lean ===== -/
section

/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
-- Vendored from LeanPool/lean-pool (https://github.com/LeanPool/lean-pool),
-- file LeanPool/Feige/AugmentedLatentSupport.lean at commit 9decab6341e6b0fd82bd7f9763a5dd7a9ce8778d, Apache-2.0 (see LICENSE in this folder).
-- Changes: import paths renamed from `LeanPool.Feige.*` to `Feige.Vendor.LeanPool.*`;
-- `measurable_subtype_coe` replaced by `measurable_twoPointParams_val` (elaborates in non-module files).
-- Portability (Left to Solve CI, Lean v4.33.1): `add_apply`/`smul_apply` qualified as `Measure.*`,
-- `ite_eq_left/right` replaced by `if_pos/if_neg`, and small elaboration fixes where needed.



/-!
# Support of the augmented latent parameterization
-/


open Set MeasureTheory ProbabilityTheory

namespace Feige

noncomputable section

theorem measurableSet_augmentedParamNonnegative :
    MeasurableSet {p : AugmentedTwoPointParams |
      AugmentedParamNonnegative p} := by
  rw [measurableSet_sum_iff]
  constructor
  · simp
  · change MeasurableSet {q : TwoPointParams |
      0 ≤ q.1.1 ∧ 1 < q.1.2}
    rw [Set.setOf_and]
    exact (measurableSet_le measurable_const
      (measurable_fst.comp measurable_twoPointParams_val)).inter
      (measurableSet_lt measurable_const
        (measurable_snd.comp measurable_twoPointParams_val))

theorem measurableSet_augmentedParamsNonnegative (n : ℕ) :
    MeasurableSet {p : Fin n → AugmentedTwoPointParams |
      AugmentedParamsNonnegative p} := by
  rw [show {p : Fin n → AugmentedTwoPointParams |
      AugmentedParamsNonnegative p} =
      ⋂ i, (fun p : Fin n → AugmentedTwoPointParams => p i) ⁻¹'
        {q | AugmentedParamNonnegative q} by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iInter,
      Set.mem_preimage]
    rfl]
  exact MeasurableSet.iInter fun i =>
    measurableSet_augmentedParamNonnegative.preimage
      (measurable_pi_apply i)

theorem ae_latentPair_first_nonnegative
    {μ : Measure ℝ} [SFinite μ] (hsupport : μ (Iio 0) = 0)
    (M : ℝ) :
    ∀ᵐ p ∂latentPairMeasure μ M, 0 ≤ p.1 := by
  have hx : ∀ᵐ x ∂μ.restrict (Iio 1), 0 ≤ x := by
    rw [ae_iff]
    rw [show {a : ℝ | ¬0 ≤ a} = Iio 0 by ext; simp]
    rw [Measure.restrict_apply measurableSet_Iio]
    simpa [inter_eq_left.2 (Iio_subset_Iio (by norm_num : (0 : ℝ) ≤ 1))]
      using hsupport
  have hprod :
      ∀ᵐ p ∂belowAboveProduct μ, 0 ≤ p.1 := by
    unfold belowAboveProduct
    rw [Measure.ae_prod_iff_ae_ae
      (measurableSet_le measurable_const measurable_fst)]
    filter_upwards [hx] with x hx
    exact Filter.Eventually.of_forall fun _ => hx
  exact hprod.filter_mono
    (withDensity_absolutelyContinuous
      (belowAboveProduct μ) (latentPairDensity M)).ae_le

theorem ae_latentParams_nonnegative
    {μ : Measure ℝ} [SFinite μ] (hsupport : μ (Iio 0) = 0)
    (M : ℝ) :
    ∀ᵐ q ∂latentParamsMeasure μ M,
      0 ≤ q.1.1 ∧ 1 < q.1.2 := by
  unfold latentParamsMeasure
  rw [ae_map_iff measurable_pairToParams.aemeasurable
    (by
      rw [Set.setOf_and]
      exact (measurableSet_le measurable_const
        (measurable_fst.comp measurable_twoPointParams_val)).inter
        (measurableSet_lt measurable_const
          (measurable_snd.comp measurable_twoPointParams_val)))]
  filter_upwards
    [ae_latentPair_first_nonnegative hsupport M,
      (show ∀ᵐ p ∂latentPairMeasure μ M,
          p ∈ strictPairSet by
        rw [ae_iff]
        change latentPairMeasure μ M strictPairSetᶜ = 0
        exact latentPairMeasure_compl_strictPairSet μ M)]
    with p hp0 hpstrict
  simp [pairToParams, hpstrict, hp0, hpstrict.2]

theorem ae_augmentedLatent_nonnegative
    {μ : Measure ℝ} [SFinite μ]
    (hsupport : μ (Iio 0) = 0) :
    ∀ᵐ p ∂meanOneAugmentedLatent μ,
      AugmentedParamNonnegative p := by
  by_cases hM : belowMoment μ = 0
  · rw [meanOneAugmentedLatent, if_pos hM]
    rw [ae_dirac_iff measurableSet_augmentedParamNonnegative]
    simp [AugmentedParamNonnegative]
  · rw [meanOneAugmentedLatent, if_neg hM,
      augmentedLatentMeasure, ae_add_measure_iff]
    constructor
    · exact Measure.ae_smul_measure
        (by
          rw [ae_dirac_iff measurableSet_augmentedParamNonnegative]
          simp [AugmentedParamNonnegative]) _
    · rw [ae_map_iff measurable_inr.aemeasurable
        measurableSet_augmentedParamNonnegative]
      exact ae_latentParams_nonnegative hsupport (belowMoment μ)

theorem ae_recursiveAugmentedLatent_nonnegative
    (n : ℕ) (μ : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)]
    (hμ : ∀ i, Integrable (fun x : ℝ ↦ x) (μ i))
    (hmean : ∀ i, (∫ x : ℝ, x ∂μ i) = 1)
    (hsupport : ∀ i, μ i (Iio 0) = 0) :
    ∀ᵐ p ∂recursiveAugmentedLatent n
        (fun i ↦ meanOneAugmentedLatent (μ i)),
      AugmentedParamsNonnegative p := by
  induction n with
  | zero =>
      unfold recursiveAugmentedLatent
      simp [AugmentedParamsNonnegative]
  | succ n ih =>
      let latent := fun i : Fin (n + 1) =>
        meanOneAugmentedLatent (μ i)
      let tail := recursiveAugmentedLatent n
        (fun i => meanOneAugmentedLatent (μ (Fin.succ i)))
      let : ∀ i, IsProbabilityMeasure (latent i) :=
        fun i => meanOneAugmentedLatent_isProbability
          (hμ i) (hmean i)
      have hhead :
          ∀ᵐ p ∂latent 0, AugmentedParamNonnegative p :=
        ae_augmentedLatent_nonnegative
          (hsupport 0)
      have htail :
          ∀ᵐ p ∂tail, AugmentedParamsNonnegative p :=
        ih (fun i => μ (Fin.succ i))
          (fun i => hμ (Fin.succ i))
          (fun i => hmean (Fin.succ i))
          (fun i => hsupport (Fin.succ i))
      unfold recursiveAugmentedLatent
      rw [ae_map_iff
        (finHeadTailEquiv AugmentedTwoPointParams n).symm.measurable.aemeasurable
          (measurableSet_augmentedParamsNonnegative (n + 1))]
      rw [Measure.ae_prod_iff_ae_ae
        (by
          exact (measurableSet_augmentedParamsNonnegative (n + 1)).preimage
            (finHeadTailEquiv AugmentedTwoPointParams n).symm.measurable)]
      filter_upwards [hhead] with head hhead
      filter_upwards [htail] with tail htail
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · change AugmentedParamNonnegative head
        exact hhead
      · change AugmentedParamNonnegative (tail j)
        exact htail j

end

end Feige

end

/- ===== Calculus/NoInteriorMin.lean ===== -/
section

/-!
# One-variable calculus helpers

* `le_of_hasDerivAt_nonneg`, `lt_of_hasDerivAt_neg`: monotonicity from the sign of the
  derivative (mean value theorem).
* `min_endpoints_le_of_stationary`: if at every interior stationary point of `g` on `[a, b]`
  the second derivative is negative, then `g` has no interior minimum, so
  `min (g a) (g b) ≤ g x` for all `x ∈ [a, b]`.  This is the argument used for Ling's
  Claim 3.4 and for the minimization over `m` in Ling's Corollary 1.3.
-/

open Set Filter Topology

namespace Samuels

lemma le_of_hasDerivAt_nonneg {f f' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn f (Icc a b)) (hd : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hpos : ∀ x ∈ Ioo a b, 0 ≤ f' x) : f a ≤ f b := by
  rcases hab.eq_or_lt with rfl | hlt
  · exact le_rfl
  obtain ⟨c, hc', hceq⟩ := exists_hasDerivAt_eq_slope f f' hlt hc hd
  have h0 := hpos c hc'
  rw [hceq, le_div_iff₀ (sub_pos.mpr hlt), zero_mul] at h0
  linarith

lemma lt_of_hasDerivAt_neg {f f' : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hc : ContinuousOn f (Icc a b)) (hd : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hneg : ∀ x ∈ Ioo a b, f' x < 0) : f b < f a := by
  obtain ⟨c, hc', hceq⟩ := exists_hasDerivAt_eq_slope f f' hab hc hd
  have h0 := hneg c hc'
  rw [hceq, div_lt_iff₀ (sub_pos.mpr hab), zero_mul] at h0
  linarith

/-- No interior minimum: if at every interior stationary point the second derivative is
negative, the minimum of `g` over `[a, b]` is attained at an endpoint. -/
theorem min_endpoints_le_of_stationary {g g' g'' : ℝ → ℝ} {a b : ℝ}
    (hcont : ContinuousOn g (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x)
    (hd2 : ∀ x ∈ Ioo a b, HasDerivAt g' (g'' x) x)
    (hstat : ∀ x ∈ Ioo a b, g' x = 0 → g'' x < 0) :
    ∀ x ∈ Icc a b, min (g a) (g b) ≤ g x := by
  intro x hx
  by_contra hlt
  push Not at hlt
  obtain ⟨c, hcI, hcmin⟩ := isCompact_Icc.exists_isMinOn ⟨x, hx⟩ hcont
  have hcx : g c ≤ g x := hcmin hx
  have hca : c ≠ a := by
    rintro rfl
    have := min_le_left (g c) (g b)
    linarith
  have hcb : c ≠ b := by
    rintro rfl
    have := min_le_right (g a) (g c)
    linarith
  have hcIoo : c ∈ Ioo a b :=
    ⟨lt_of_le_of_ne hcI.1 (Ne.symm hca), lt_of_le_of_ne hcI.2 hcb⟩
  have hloc : IsLocalMin g c := hcmin.isLocalMin (Icc_mem_nhds hcIoo.1 hcIoo.2)
  have hg'c : g' c = 0 := hloc.hasDerivAt_eq_zero (hd c hcIoo)
  have hg''c : g'' c < 0 := hstat c hcIoo hg'c
  have hslope := hasDerivAt_iff_tendsto_slope.mp (hd2 c hcIoo)
  have hev : ∀ᶠ y in 𝓝[≠] c, slope g' c y < 0 :=
    hslope.eventually (gt_mem_nhds hg''c)
  have hev' : ∀ᶠ y in 𝓝[>] c, g' y < 0 := by
    filter_upwards [nhdsGT_le_nhdsNE c hev, self_mem_nhdsWithin] with y hy hyc
    rw [slope_def_field, hg'c, sub_zero] at hy
    have hpos : 0 < y - c := sub_pos.mpr hyc
    by_contra hge
    push Not at hge
    have := div_nonneg hge hpos.le
    linarith
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev'
  have hu' : c < u := hu
  set y := (c + min u b) / 2 with hy
  have hcm : c < min u b := lt_min hu' hcIoo.2
  have hcy : c < y := by rw [hy]; linarith
  have hyb : y < min u b := by rw [hy]; linarith
  have hyu : y < u := lt_of_lt_of_le hyb (min_le_left _ _)
  have hyb' : y < b := lt_of_lt_of_le hyb (min_le_right _ _)
  have hlt' : g y < g c := by
    apply lt_of_hasDerivAt_neg hcy
    · exact hcont.mono (Icc_subset_Icc hcI.1 hyb'.le)
    · intro z hz
      exact hd z ⟨lt_of_le_of_lt hcI.1 hz.1, lt_trans hz.2 hyb'⟩
    · intro z hz
      exact hsub ⟨hz.1, lt_trans hz.2 hyu⟩
  have := hcmin (show y ∈ Icc a b from ⟨(lt_of_le_of_lt hcI.1 hcy).le, hyb'.le⟩)
  exact absurd this (not_le.mpr hlt')

end Samuels

end

/- ===== Calculus/HDelta.lean ===== -/
section

/-!
# M-Calc-A: the minimization over `m` (manuscript Prop. 5.2, Ling Cor. 1.3)

For `D > 0` and real `x ≥ 1`,
`(1 - 1/(x + D))^x ≥ min (D/(1+D)) (exp (-1))`.

We work with `f(x) = x * (log (x + D - 1) - log (x + D)) = x * log (1 - 1/(x+D))` and show
`f x ≥ min (f 1) (-1)`.

* If `D ≤ 1/2`, then `f' ≥ 0` on `[1, ∞)` (using `log y ≤ (y - 1/y)/2` for `y ≥ 1`), so
  `f x ≥ f 1`.
* If `D > 1/2`, then at every point with `f'' ≥ 0` we have `f' < 0` (using the four-term
  Taylor upper bound for `log (1 - t)`), so every stationary point is a strict local maximum.
  Moreover `f N ≥ -1` for `N` large (explicitly `N (2D - 1) ≥ 2D(1-D)`), so on `[1, N]` the
  minimum is at an endpoint and `f x ≥ min (f 1) (f N) ≥ min (f 1) (-1)`.

This route avoids limits entirely.
-/

open Set Filter Topology Real

namespace Samuels

/-! ### Two elementary logarithm inequalities -/

/-- `log y ≤ (y - y⁻¹)/2` for `y ≥ 1`. -/
lemma log_le_half_sub_inv {y : ℝ} (hy : 1 ≤ y) : log y ≤ (y - y⁻¹) / 2 := by
  let φ : ℝ → ℝ := fun z => (z - z⁻¹) / 2 - log z
  have hφ : ∀ z, 0 < z → HasDerivAt φ ((1 + (z ^ 2)⁻¹) / 2 - z⁻¹) z := by
    intro z hz
    have h1 : HasDerivAt (fun z : ℝ => z⁻¹) (-(z ^ 2)⁻¹) z := hasDerivAt_inv hz.ne'
    have h3 := (((hasDerivAt_id' z).sub h1).div_const 2).sub (hasDerivAt_log hz.ne')
    exact h3.congr_deriv (by ring)
  have key : φ 1 ≤ φ y := by
    apply le_of_hasDerivAt_nonneg hy
    · intro z hz
      exact (hφ z (by linarith [hz.1])).continuousAt.continuousWithinAt
    · intro z hz
      exact hφ z (by linarith [hz.1])
    · intro z hz
      have hz0 : 0 < z := by linarith [hz.1]
      have : (1 + (z ^ 2)⁻¹) / 2 - z⁻¹ = (z - 1) ^ 2 / (2 * z ^ 2) := by
        field_simp
        ring
      rw [this]
      positivity
  have h1 : φ 1 = 0 := by simp [φ]
  simp only [φ, h1] at key
  linarith

/-- Lower bound: for `u > 1`, `log (u-1) - log u ≥ -(2u-1)/(2u(u-1))`. -/
lemma log_sub_log_ge {u : ℝ} (hu : 1 < u) :
    -(2 * u - 1) / (2 * u * (u - 1)) ≤ log (u - 1) - log u := by
  have hu0 : 0 < u := by linarith
  have hu1 : 0 < u - 1 := by linarith
  have hy : 1 ≤ u / (u - 1) := by
    rw [le_div_iff₀ hu1]; linarith
  have h := log_le_half_sub_inv hy
  rw [log_div hu0.ne' hu1.ne'] at h
  have : (u / (u - 1) - (u / (u - 1))⁻¹) / 2 = (2 * u - 1) / (2 * u * (u - 1)) := by
    field_simp
    ring
  rw [this] at h
  rw [neg_div]
  linarith

/-- Upper bound: for `u > 1`,
`log (u-1) - log u ≤ -(1/u + 1/(2u²) + 1/(3u³) + 1/(4u⁴))`. -/
lemma log_sub_log_le {u : ℝ} (hu : 1 < u) :
    log (u - 1) - log u ≤ -(1 / u + 1 / (2 * u ^ 2) + 1 / (3 * u ^ 3) + 1 / (4 * u ^ 4)) := by
  have hu0 : 0 < u := by linarith
  have hu1 : 0 < u - 1 := by linarith
  set t := 1 / u with ht
  have ht0 : 0 < t := by positivity
  have ht1 : t < 1 := by rw [ht, div_lt_one hu0]; exact hu
  have habs : |t| < 1 := by rw [abs_of_pos ht0]; exact ht1
  have hs := hasSum_pow_div_log_of_abs_lt_one habs
  have hle := sum_le_hasSum (Finset.range 4) (fun i _ => by positivity) hs
  have hlog : log (1 - t) = log (u - 1) - log u := by
    rw [← log_div hu1.ne' hu0.ne']
    congr 1
    rw [ht]
    field_simp
  rw [← hlog]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hle
  have : 1 / u + 1 / (2 * u ^ 2) + 1 / (3 * u ^ 3) + 1 / (4 * u ^ 4) =
      0 + t ^ (0 + 1) / ((0 : ℕ) + 1 : ℝ) + t ^ (1 + 1) / ((1 : ℕ) + 1 : ℝ) +
        t ^ (2 + 1) / ((2 : ℕ) + 1 : ℝ) + t ^ (3 + 1) / ((3 : ℕ) + 1 : ℝ) := by
    rw [ht]
    push_cast
    field_simp
    ring
  rw [this]
  linarith

/-! ### The function `f_D` and its derivatives -/

/-- `f_D(x) = x * log (1 - 1/(x + D))`, written as `x * (log (x+D-1) - log (x+D))`. -/
noncomputable def fD (D x : ℝ) : ℝ := x * (log (x + D - 1) - log (x + D))

/-- The first derivative of `fD`. -/
noncomputable def fD' (D x : ℝ) : ℝ :=
  (log (x + D - 1) - log (x + D)) + x / ((x + D - 1) * (x + D))

/-- The second derivative of `fD`. -/
noncomputable def fD'' (D x : ℝ) : ℝ :=
  ((2 * D - 1) * (x + D) - D) / ((x + D - 1) ^ 2 * (x + D) ^ 2)

lemma hasDerivAt_fD {D x : ℝ} (hx : 1 < x + D) : HasDerivAt (fD D) (fD' D x) x := by
  have h1 : x + D - 1 ≠ 0 := by linarith
  have h2 : x + D ≠ 0 := by linarith
  have hA : HasDerivAt (fun y => log (y + D - 1)) (1 / (x + D - 1)) x := by
    have := (((hasDerivAt_id x).add_const D).sub_const 1).log (by simpa using h1)
    simpa using this
  have hB : HasDerivAt (fun y => log (y + D)) (1 / (x + D)) x := by
    have := ((hasDerivAt_id x).add_const D).log (by simpa using h2)
    simpa using this
  have := (hasDerivAt_id' x).mul (hA.sub hB)
  show HasDerivAt (fun y => y * (log (y + D - 1) - log (y + D))) _ x
  refine this.congr_deriv ?_
  simp only [Pi.sub_apply]
  unfold fD'
  field_simp
  ring

lemma hasDerivAt_fD' {D x : ℝ} (hx : 1 < x + D) : HasDerivAt (fD' D) (fD'' D x) x := by
  have h1 : x + D - 1 ≠ 0 := by linarith
  have h2 : x + D ≠ 0 := by linarith
  have hA : HasDerivAt (fun y => log (y + D - 1)) (1 / (x + D - 1)) x := by
    have := (((hasDerivAt_id x).add_const D).sub_const 1).log (by simpa using h1)
    simpa using this
  have hB : HasDerivAt (fun y => log (y + D)) (1 / (x + D)) x := by
    have := ((hasDerivAt_id x).add_const D).log (by simpa using h2)
    simpa using this
  have hP : HasDerivAt (fun y => (y + D - 1) * (y + D)) ((x + D - 1) + (x + D)) x := by
    have := (((hasDerivAt_id' x).add_const D).sub_const 1).mul ((hasDerivAt_id' x).add_const D)
    exact this.congr_deriv (by ring)
  have hQ := (hasDerivAt_id' x).div hP (mul_ne_zero h1 h2)
  have := (hA.sub hB).add hQ
  show HasDerivAt (fun y => (log (y + D - 1) - log (y + D)) + y / ((y + D - 1) * (y + D))) _ x
  refine this.congr_deriv ?_
  unfold fD''
  field_simp
  ring

lemma continuousOn_fD {D a b : ℝ} (ha : 1 < a + D) : ContinuousOn (fD D) (Icc a b) := by
  intro x hx
  exact (hasDerivAt_fD (by linarith [hx.1])).continuousAt.continuousWithinAt

/-! ### Sign facts -/

/-- For `D ≤ 1/2`, `f_D' ≥ 0` wherever `x + D > 1` and `x ≥ 0`. -/
lemma fD'_nonneg {D x : ℝ} (hD : D ≤ 1 / 2) (_hx0 : 0 ≤ x) (hx : 1 < x + D) :
    0 ≤ fD' D x := by
  unfold fD'
  set u := x + D with hu
  have hu1 : 0 < u - 1 := by linarith
  have hu0 : 0 < u := by linarith
  have hlb := log_sub_log_ge hx
  have hxu : x = u - D := by rw [hu]; ring
  have : -(2 * u - 1) / (2 * u * (u - 1)) + x / ((u - 1) * u) =
      (1 - 2 * D) / (2 * u * (u - 1)) := by
    rw [hxu]
    field_simp
    ring
  have hpos : 0 ≤ (1 - 2 * D) / (2 * u * (u - 1)) := by
    apply div_nonneg (by linarith); positivity
  linarith

/-- For `D > 1/2`, wherever `f_D'' ≥ 0` (i.e. `(2D-1)(x+D) ≥ D`) and `x ≥ 1`, we have
`f_D' < 0`. -/
lemma fD'_neg {D x : ℝ} (hD : 1 / 2 < D) (hx : 1 ≤ x) (hsec : D ≤ (2 * D - 1) * (x + D)) :
    fD' D x < 0 := by
  unfold fD'
  set u := x + D with hu
  have hu1' : 1 < u := by linarith
  have hu1 : 0 < u - 1 := by linarith
  have hu0 : 0 < u := by linarith
  have hub := log_sub_log_le hu1'
  have hxu : x = u - D := by rw [hu]; ring
  have heq : -(1 / u + 1 / (2 * u ^ 2) + 1 / (3 * u ^ 3) + 1 / (4 * u ^ 4)) +
      x / ((u - 1) * u) =
      ((6 - 12 * D) * u ^ 3 + 2 * u ^ 2 + u + 3) / (12 * u ^ 4 * (u - 1)) := by
    rw [hxu]
    field_simp
    ring
  -- the polynomial is negative
  have hpoly : (6 - 12 * D) * u ^ 3 + 2 * u ^ 2 + u + 3 < 0 := by
    have hu_ge : 1 + D ≤ u := by linarith
    have h1 : 6 * D * u ^ 2 ≤ (12 * D - 6) * u ^ 3 := by
      have : (12 * D - 6) * u ^ 3 = 6 * ((2 * D - 1) * u) * u ^ 2 := by ring
      rw [this]
      have hu2 : 0 ≤ u ^ 2 := by positivity
      nlinarith
    have h2 : 3 * D * u ≤ 3 * (2 * D - 1) * u ^ 2 := by
      have : 3 * (2 * D - 1) * u ^ 2 = 3 * ((2 * D - 1) * u) * u := by ring
      rw [this]
      nlinarith
    have h3 : (1 + D) ^ 2 + (3 * D - 1) * (1 + D) ≤ u ^ 2 + (3 * D - 1) * u := by
      have h3a : (1 + D) ^ 2 ≤ u ^ 2 := by nlinarith
      have h3b : (3 * D - 1) * (1 + D) ≤ (3 * D - 1) * u :=
        mul_le_mul_of_nonneg_left hu_ge (by linarith)
      linarith
    have h4 : 0 < (2 * D - 1) * (2 * D + 3) := by
      apply mul_pos <;> linarith
    nlinarith
  have hden : 0 < 12 * u ^ 4 * (u - 1) := by positivity
  have := div_neg_of_neg_of_pos hpoly hden
  linarith

/-- For `D > 1/2`, every stationary point of `f_D` in `x ≥ 1` has negative second derivative. -/
lemma fD''_neg_of_stationary {D x : ℝ} (hD : 1 / 2 < D) (hx : 1 ≤ x) (hst : fD' D x = 0) :
    fD'' D x < 0 := by
  by_contra h
  push Not at h
  have hu1 : 0 < x + D - 1 := by linarith
  have hu0 : 0 < x + D := by linarith
  have hden : 0 < (x + D - 1) ^ 2 * (x + D) ^ 2 := by positivity
  unfold fD'' at h
  have hnum : 0 ≤ (2 * D - 1) * (x + D) - D := by
    by_contra hn
    push Not at hn
    have := div_neg_of_neg_of_pos hn hden
    linarith
  have := fD'_neg hD hx (by linarith)
  linarith

/-- For `D > 1/2` and `N ≥ 1` with `N (2D-1) ≥ 2D(1-D)`, we have `f_D N ≥ -1`. -/
lemma fD_ge_neg_one {D N : ℝ} (hD : 1 / 2 < D) (hN : 1 ≤ N)
    (hbig : 2 * D * (1 - D) ≤ N * (2 * D - 1)) : -1 ≤ fD D N := by
  unfold fD
  set u := N + D with hu
  have hu1' : 1 < u := by linarith
  have hu1 : 0 < u - 1 := by linarith
  have hu0 : 0 < u := by linarith
  have hlb := log_sub_log_ge hu1'
  have hN0 : 0 ≤ N := by linarith
  have h1 : N * (-(2 * u - 1) / (2 * u * (u - 1))) ≤ N * (log (u - 1) - log u) :=
    mul_le_mul_of_nonneg_left hlb hN0
  have h2 : -1 ≤ N * (-(2 * u - 1) / (2 * u * (u - 1))) := by
    have hden : 0 < 2 * u * (u - 1) := by positivity
    rw [mul_div_assoc', le_div_iff₀ hden]
    have hNu : N = u - D := by rw [hu]; ring
    rw [hNu] at hbig ⊢
    nlinarith
  linarith

/-! ### The main real inequality -/

/-- `f_D x ≥ min (f_D 1) (-1)` for all `x ≥ 1`. -/
theorem fD_ge_min {D x : ℝ} (hD : 0 < D) (hx : 1 ≤ x) : min (fD D 1) (-1) ≤ fD D x := by
  rcases le_or_gt D (1 / 2) with hD2 | hD2
  · -- monotone case
    have : fD D 1 ≤ fD D x := by
      apply le_of_hasDerivAt_nonneg hx (continuousOn_fD (by linarith))
      · intro z hz; exact hasDerivAt_fD (by linarith [hz.1])
      · intro z hz; exact fD'_nonneg hD2 (by linarith [hz.1]) (by linarith [hz.1])
    exact (min_le_left _ _).trans this
  · -- no interior minimum on `[1, N]`
    set N := max x (2 * D * (1 - D) / (2 * D - 1)) with hNdef
    have hxN : x ≤ N := le_max_left _ _
    have hN1 : 1 ≤ N := hx.trans hxN
    have hbig : 2 * D * (1 - D) ≤ N * (2 * D - 1) := by
      have h2 : 0 < 2 * D - 1 := by linarith
      have : 2 * D * (1 - D) / (2 * D - 1) ≤ N := le_max_right _ _
      rwa [div_le_iff₀ h2] at this
    have hNf := fD_ge_neg_one hD2 hN1 hbig
    have hmin := min_endpoints_le_of_stationary (g := fD D) (g' := fD' D) (g'' := fD'' D)
      (a := 1) (b := N) (continuousOn_fD (by linarith))
      (fun z hz => hasDerivAt_fD (by linarith [hz.1]))
      (fun z hz => hasDerivAt_fD' (by linarith [hz.1]))
      (fun z hz hst => fD''_neg_of_stationary hD2 hz.1.le hst) x ⟨hx, hxN⟩
    calc min (fD D 1) (-1) ≤ min (fD D 1) (fD D N) := min_le_min le_rfl hNf
      _ ≤ fD D x := hmin

/-- `(1 - 1/(x+D))^x = exp (f_D x)` for `x + D > 1`. -/
lemma rpow_eq_exp_fD {D x : ℝ} (hx : 1 < x + D) :
    (1 - 1 / (x + D)) ^ x = exp (fD D x) := by
  have h0 : 0 < x + D := by linarith
  have h1 : 0 < x + D - 1 := by linarith
  have hpos : 0 < 1 - 1 / (x + D) := by
    rw [sub_pos, div_lt_one h0]; exact hx
  rw [rpow_def_of_pos hpos, fD]
  congr 1
  have : 1 - 1 / (x + D) = (x + D - 1) / (x + D) := by field_simp
  rw [this, log_div h1.ne' h0.ne']
  ring

/-- **Prop. 5.2 (real form).** For `D > 0` and real `x ≥ 1`,
`min (D/(1+D)) (exp (-1)) ≤ (1 - 1/(x + D))^x`. -/
theorem min_le_rpow {D x : ℝ} (hD : 0 < D) (hx : 1 ≤ x) :
    min (D / (1 + D)) (exp (-1)) ≤ (1 - 1 / (x + D)) ^ x := by
  rw [rpow_eq_exp_fD (by linarith)]
  have h1 : exp (fD D 1) = D / (1 + D) := by
    have := rpow_eq_exp_fD (D := D) (x := 1) (by linarith)
    rw [← this, rpow_one]
    field_simp
    ring
  have hmono : exp (min (fD D 1) (-1)) ≤ exp (fD D x) := exp_le_exp.mpr (fD_ge_min hD hx)
  have hexpmin : exp (min (fD D 1) (-1)) = min (exp (fD D 1)) (exp (-1)) :=
    Monotone.map_min exp_monotone
  rw [hexpmin, h1] at hmono
  exact hmono

/-- **Prop. 5.2 (integer form, M-Calc-A).** For `δ > 0` and integers `m ≥ 1`,
`min (δ/(1+δ)) (exp (-1)) ≤ (1 - 1/(m + δ))^m`. -/
theorem min_le_pow {δ : ℝ} (hδ : 0 < δ) {m : ℕ} (hm : 1 ≤ m) :
    min (δ / (1 + δ)) (exp (-1)) ≤ (1 - 1 / (m + δ)) ^ m := by
  have := min_le_rpow (x := (m : ℝ)) hδ (by exact_mod_cast hm)
  rwa [rpow_natCast] at this

end Samuels

end

/- ===== Bernoulli/Ex.lean ===== -/
section

/-!
# Finite Bernoulli product expectations

For a finite index set `s` and success probabilities `p`, a subset `S ⊆ s` (the set of
coordinates with `Bᵢ = 1`) has product weight `wt p s S`, and `Ex p s F` is the expectation of
`F : Finset ι → ℝ`.  Everything in Ling's §3 is a finite sum of this form, so no measure
theory is needed for Theorem 2.1.
-/

open Finset

namespace Samuels

variable {ι : Type*} [DecidableEq ι]

/-- Product weight of the high set `S ⊆ s`. -/
noncomputable def wt (p : ι → ℝ) (s S : Finset ι) : ℝ :=
  (∏ i ∈ S, p i) * ∏ i ∈ s \ S, (1 - p i)

/-- Expectation of `F` under independent `Bernoulli (p i)`, `i ∈ s`. -/
noncomputable def Ex (p : ι → ℝ) (s : Finset ι) (F : Finset ι → ℝ) : ℝ :=
  ∑ S ∈ s.powerset, wt p s S * F S

variable {p : ι → ℝ}

@[simp] lemma Ex_empty (F : Finset ι → ℝ) : Ex p ∅ F = F ∅ := by
  simp [Ex, wt]

lemma wt_insert_of_subset {i : ι} {s S : Finset ι} (hi : i ∉ s) (hS : S ⊆ s) :
    wt p (insert i s) S = (1 - p i) * wt p s S := by
  unfold wt
  have hiS : i ∉ S := fun h => hi (hS h)
  rw [Finset.insert_sdiff_of_notMem _ hiS, Finset.prod_insert (by simp [hi])]
  ring

lemma wt_insert_insert {i : ι} {s S : Finset ι} (hi : i ∉ s) (hS : S ⊆ s) :
    wt p (insert i s) (insert i S) = p i * wt p s S := by
  unfold wt
  have hiS : i ∉ S := fun h => hi (hS h)
  have hsd : insert i s \ insert i S = s \ S := by
    ext j
    simp only [mem_sdiff, mem_insert]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact absurd (Or.inl h1) h2
      · exact ⟨h1, fun h => h2 (Or.inr h)⟩
    · rintro ⟨h1, h2⟩
      refine ⟨Or.inr h1, ?_⟩
      rintro (h | h)
      · exact hi (h ▸ h1)
      · exact h2 h
  rw [hsd, Finset.prod_insert hiS]
  ring

/-- Conditioning on the coordinate `i`. -/
lemma Ex_insert {i : ι} {s : Finset ι} (hi : i ∉ s) (F : Finset ι → ℝ) :
    Ex p (insert i s) F = (1 - p i) * Ex p s F + p i * Ex p s (fun S => F (insert i S)) := by
  unfold Ex
  rw [Finset.sum_powerset_insert hi, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro S hS
    rw [wt_insert_of_subset hi (mem_powerset.mp hS)]
    ring
  · apply Finset.sum_congr rfl
    intro S hS
    rw [wt_insert_insert hi (mem_powerset.mp hS)]
    ring

lemma Ex_congr {s : Finset ι} {F G : Finset ι → ℝ} (h : ∀ S ⊆ s, F S = G S) :
    Ex p s F = Ex p s G := by
  unfold Ex
  apply Finset.sum_congr rfl
  intro S hS
  rw [h S (mem_powerset.mp hS)]

lemma Ex_add (s : Finset ι) (F G : Finset ι → ℝ) :
    Ex p s (fun S => F S + G S) = Ex p s F + Ex p s G := by
  simp [Ex, mul_add, Finset.sum_add_distrib]

lemma Ex_sub (s : Finset ι) (F G : Finset ι → ℝ) :
    Ex p s (fun S => F S - G S) = Ex p s F - Ex p s G := by
  simp [Ex, mul_sub, Finset.sum_sub_distrib]

lemma Ex_mul_left (s : Finset ι) (c : ℝ) (F : Finset ι → ℝ) :
    Ex p s (fun S => c * F S) = c * Ex p s F := by
  simp only [Ex, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  ring

lemma Ex_zero (s : Finset ι) : Ex p s (fun _ => 0) = 0 := by
  simp [Ex]

lemma Ex_finsum {κ : Type*} (s : Finset ι) (t : Finset κ) (F : κ → Finset ι → ℝ) :
    Ex p s (fun S => ∑ j ∈ t, F j S) = ∑ j ∈ t, Ex p s (F j) := by
  simp only [Ex, Finset.mul_sum]
  rw [Finset.sum_comm]

lemma wt_nonneg {s S : Finset ι} (hp0 : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∀ i ∈ s, p i ≤ 1)
    (hS : S ⊆ s) : 0 ≤ wt p s S := by
  unfold wt
  apply mul_nonneg
  · exact Finset.prod_nonneg fun i hi => hp0 i (hS hi)
  · exact Finset.prod_nonneg fun i hi => sub_nonneg.mpr (hp1 i (mem_sdiff.mp hi).1)

lemma Ex_mono {s : Finset ι} (hp0 : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∀ i ∈ s, p i ≤ 1)
    {F G : Finset ι → ℝ} (h : ∀ S ⊆ s, F S ≤ G S) : Ex p s F ≤ Ex p s G := by
  unfold Ex
  apply Finset.sum_le_sum
  intro S hS
  exact mul_le_mul_of_nonneg_left (h S (mem_powerset.mp hS))
    (wt_nonneg hp0 hp1 (mem_powerset.mp hS))

lemma Ex_nonneg {s : Finset ι} (hp0 : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∀ i ∈ s, p i ≤ 1)
    {F : Finset ι → ℝ} (h : ∀ S ⊆ s, 0 ≤ F S) : 0 ≤ Ex p s F := by
  have := Ex_mono hp0 hp1 (F := fun _ => 0) h
  rwa [Ex_zero] at this

lemma Ex_const (s : Finset ι) (c : ℝ) : Ex p s (fun _ => c) = c := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Ex_insert hi]
    simp only [ih]
    ring

/-- The mean of `T = ∑_{i ∈ S} wᵢ`. -/
lemma Ex_sum_mem (s : Finset ι) (w : ι → ℝ) :
    Ex p s (fun S => ∑ i ∈ S, w i) = ∑ i ∈ s, w i * p i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Ex_insert hi, Finset.sum_insert hi, ih]
    have : Ex p s (fun S => ∑ j ∈ insert i S, w j) = Ex p s (fun S => w i + ∑ j ∈ S, w j) := by
      apply Ex_congr
      intro S hS
      rw [Finset.sum_insert (fun h => hi (hS h))]
    rw [this, Ex_add, Ex_const, ih]
    ring

end Samuels

end

/- ===== Bernoulli/ZM.lean ===== -/
section

/-!
# Truncated moments of a weighted Bernoulli sum

`T S = ∑_{i ∈ S} wᵢ`. For a threshold `c`,
* `Z s c = P(T < c)`,
* `M s c = E[T · 1{T < c}]`,
* `Q s c = E[T² · 1{T < c}]`,
and their recursions when one coordinate is added.
-/

open Finset

namespace Samuels

variable {ι : Type*} [DecidableEq ι] (p w : ι → ℝ)

/-- The weighted sum `T(S) = ∑_{i ∈ S} wᵢ`. -/
def T (S : Finset ι) : ℝ := ∑ i ∈ S, w i

/-- `P(T < c)`. -/
noncomputable def Z (s : Finset ι) (c : ℝ) : ℝ :=
  Ex p s (fun S => if T w S < c then 1 else 0)

/-- `E[T 1{T < c}]`. -/
noncomputable def M (s : Finset ι) (c : ℝ) : ℝ :=
  Ex p s (fun S => if T w S < c then T w S else 0)

/-- `E[T² 1{T < c}]`. -/
noncomputable def Q (s : Finset ι) (c : ℝ) : ℝ :=
  Ex p s (fun S => if T w S < c then T w S ^ 2 else 0)

/-- `E[T] = ∑ wᵢ pᵢ`. -/
def E (s : Finset ι) : ℝ := ∑ i ∈ s, w i * p i

variable {p w}

lemma T_insert {i : ι} {S : Finset ι} (hi : i ∉ S) : T w (insert i S) = w i + T w S := by
  simp [T, Finset.sum_insert hi]

lemma Z_insert {i : ι} {s : Finset ι} (hi : i ∉ s) (c : ℝ) :
    Z p w (insert i s) c = (1 - p i) * Z p w s c + p i * Z p w s (c - w i) := by
  unfold Z
  rw [Ex_insert hi]
  congr 2
  apply Ex_congr
  intro S hS
  rw [T_insert (fun h => hi (hS h))]
  by_cases h : T w S < c - w i
  · rw [if_pos (by linarith), if_pos h]
  · rw [if_neg (by linarith), if_neg h]

lemma M_insert {i : ι} {s : Finset ι} (hi : i ∉ s) (c : ℝ) :
    M p w (insert i s) c =
      (1 - p i) * M p w s c + p i * (M p w s (c - w i) + w i * Z p w s (c - w i)) := by
  unfold M Z
  rw [Ex_insert hi]
  congr 2
  rw [← Ex_mul_left, ← Ex_add]
  apply Ex_congr
  intro S hS
  rw [T_insert (fun h => hi (hS h))]
  by_cases h : T w S < c - w i
  · rw [if_pos (by linarith), if_pos h, if_pos h]; ring
  · rw [if_neg (by linarith), if_neg h, if_neg h]; ring

lemma Z_nonneg {s : Finset ι} (hp0 : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∀ i ∈ s, p i ≤ 1) (c : ℝ) :
    0 ≤ Z p w s c := by
  apply Ex_nonneg hp0 hp1
  intro S _
  split_ifs <;> norm_num

lemma Z_pos {s : Finset ι} (hp0 : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∀ i ∈ s, p i < 1)
    (hw : ∀ i ∈ s, 0 ≤ w i) {c : ℝ} (hc : 0 < c) : 0 < Z p w s c := by
  induction s using Finset.induction_on with
  | empty => simp [Z, T, hc]
  | insert i s hi ih =>
    rw [Z_insert hi]
    have h1 := ih (fun j hj => hp0 j (mem_insert_of_mem hj)) (fun j hj => hp1 j (mem_insert_of_mem hj))
      (fun j hj => hw j (mem_insert_of_mem hj))
    have h2 := Z_nonneg (w := w) (fun j hj => hp0 j (mem_insert_of_mem hj))
      (fun j hj => (hp1 j (mem_insert_of_mem hj)).le) (c - w i)
    have h3 : 0 < 1 - p i := sub_pos.mpr (hp1 i (mem_insert_self i s))
    have h4 := hp0 i (mem_insert_self i s)
    nlinarith

lemma Z_le_one {s : Finset ι} (hp0 : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∀ i ∈ s, p i ≤ 1) (c : ℝ) :
    Z p w s c ≤ 1 := by
  have := Ex_mono (F := fun S => if T w S < c then (1 : ℝ) else 0) (G := fun _ => 1) hp0 hp1
    (fun S _ => by split_ifs <;> norm_num)
  rwa [Ex_const] at this

lemma Z_mono {s : Finset ι} (hp0 : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∀ i ∈ s, p i ≤ 1) {c' c : ℝ}
    (hc : c' ≤ c) : Z p w s c' ≤ Z p w s c := by
  apply Ex_mono hp0 hp1
  intro S _
  by_cases h : T w S < c'
  · rw [if_pos h, if_pos (lt_of_lt_of_le h hc)]
  · rw [if_neg h]; split_ifs <;> norm_num

/-- On `{c' ≤ T < c}` we have `T ≥ c'`, so `E[T 1{c' ≤ T < c}] ≥ c' P(c' ≤ T < c)`. -/
lemma M_sub_ge {s : Finset ι} (hp0 : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∀ i ∈ s, p i ≤ 1) {c' c : ℝ}
    (hc : c' ≤ c) : c' * (Z p w s c - Z p w s c') ≤ M p w s c - M p w s c' := by
  unfold M Z
  rw [← Ex_sub, ← Ex_sub, ← Ex_mul_left]
  apply Ex_mono hp0 hp1
  intro S _
  rcases lt_or_ge (T w S) c' with h | h
  · have h' : T w S < c := lt_of_lt_of_le h hc
    simp [h, h']
  · rcases lt_or_ge (T w S) c with h' | h'
    · simp [h', not_lt.mpr h]; nlinarith
    · simp [not_lt.mpr h, not_lt.mpr h']

/-- Claim 3.1, last part: `E[T] ≥ M + (1 - Z)`, i.e. `Z - M ≥ 1 - E[T]`. -/
lemma one_sub_E_le {s : Finset ι} (hp0 : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∀ i ∈ s, p i ≤ 1) :
    1 - E p w s ≤ Z p w s 1 - M p w s 1 := by
  have hE : E p w s = Ex p s (fun S => T w S) := by
    rw [E]; exact (Ex_sum_mem s w).symm
  have : Ex p s (fun S => (if T w S < 1 then T w S else 0) + (1 - (if T w S < 1 then 1 else 0)))
      ≤ Ex p s (fun S => T w S) := by
    apply Ex_mono hp0 hp1
    intro S _
    split_ifs with h
    · simp
    · push Not at h; linarith
  rw [Ex_add, Ex_sub, Ex_const] at this
  unfold M Z
  rw [hE]
  linarith

/-- Cauchy–Schwarz: `M² ≤ Z Q`. -/
lemma M_sq_le {s : Finset ι} (hp0 : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∀ i ∈ s, p i ≤ 1) (c : ℝ)
    (hZ : 0 < Z p w s c) : M p w s c ^ 2 / Z p w s c ≤ Q p w s c := by
  set m := M p w s c / Z p w s c
  have h0 : 0 ≤ Ex p s (fun S => if T w S < c then (T w S - m) ^ 2 else 0) := by
    apply Ex_nonneg hp0 hp1
    intro S _
    split_ifs <;> positivity
  have hexp : Ex p s (fun S => if T w S < c then (T w S - m) ^ 2 else 0) =
      Q p w s c - 2 * m * M p w s c + m ^ 2 * Z p w s c := by
    unfold Q M Z
    rw [← Ex_mul_left, ← Ex_mul_left, ← Ex_sub, ← Ex_add]
    apply Ex_congr
    intro S _
    split_ifs <;> ring
  rw [hexp] at h0
  have : m * Z p w s c = M p w s c := by
    simp only [m]; field_simp
  rw [div_le_iff₀ hZ]
  have : M p w s c ^ 2 = m ^ 2 * Z p w s c ^ 2 := by
    rw [← this]; ring
  nlinarith

end Samuels

end

/- ===== Bernoulli/Moments.lean ===== -/
section

/-!
# Moments restricted to `Bᵢ = 1`

`E[Bᵢ 1{T<c}] = pᵢ P(T₋ᵢ < c - wᵢ)` and `E[Bᵢ T 1{T<c}] = pᵢ (E[T₋ᵢ 1{T₋ᵢ<c-wᵢ}] + wᵢ P(T₋ᵢ<c-wᵢ))`,
and the decompositions `T 1{T<c} = ∑ᵢ wᵢ Bᵢ 1{T<c}`, `T² 1{T<c} = ∑ᵢ wᵢ Bᵢ T 1{T<c}`.
-/

open Finset

namespace Samuels

variable {ι : Type*} [DecidableEq ι] {p w : ι → ℝ}

/-- `E[Bᵢ 1{T<c}]` on `insert i s`. -/
lemma Ex_mem_ind {i : ι} {s : Finset ι} (hi : i ∉ s) (c : ℝ) :
    Ex p (insert i s) (fun S => if i ∈ S then (if T w S < c then 1 else 0) else 0) =
      p i * Z p w s (c - w i) := by
  rw [Ex_insert hi]
  have h1 : Ex p s (fun S => if i ∈ S then (if T w S < c then (1 : ℝ) else 0) else 0) = 0 := by
    refine (Ex_congr (G := fun _ => 0) fun S hS => ?_).trans (Ex_zero s)
    rw [if_neg (fun h => hi (hS h))]
  rw [h1, mul_zero, zero_add]
  congr 1
  unfold Z
  apply Ex_congr
  intro S hS
  rw [if_pos (mem_insert_self i S), T_insert (fun h => hi (hS h))]
  by_cases h : T w S < c - w i
  · rw [if_pos (by linarith), if_pos h]
  · rw [if_neg (by linarith), if_neg h]

/-- `E[Bᵢ T 1{T<c}]` on `insert i s`. -/
lemma Ex_mem_T {i : ι} {s : Finset ι} (hi : i ∉ s) (c : ℝ) :
    Ex p (insert i s) (fun S => if i ∈ S then (if T w S < c then T w S else 0) else 0) =
      p i * (M p w s (c - w i) + w i * Z p w s (c - w i)) := by
  rw [Ex_insert hi]
  have h1 : Ex p s (fun S => if i ∈ S then (if T w S < c then T w S else 0) else 0) = 0 := by
    refine (Ex_congr (G := fun _ => 0) fun S hS => ?_).trans (Ex_zero s)
    rw [if_neg (fun h => hi (hS h))]
  rw [h1, mul_zero, zero_add]
  congr 1
  unfold M Z
  rw [← Ex_mul_left, ← Ex_add]
  apply Ex_congr
  intro S hS
  rw [if_pos (mem_insert_self i S), T_insert (fun h => hi (hS h))]
  by_cases h : T w S < c - w i
  · rw [if_pos (by linarith), if_pos h, if_pos h]; ring
  · rw [if_neg (by linarith), if_neg h, if_neg h]; ring

lemma sum_mem_ite {s S : Finset ι} (hS : S ⊆ s) (f : ι → ℝ) :
    ∑ i ∈ s, (if i ∈ S then f i else 0) = ∑ i ∈ S, f i := by
  rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hS]

/-- `M = ∑ᵢ wᵢ E[Bᵢ 1{T<c}]`. -/
lemma M_eq_sum (s : Finset ι) (c : ℝ) :
    M p w s c = ∑ i ∈ s, w i *
      Ex p s (fun S => if i ∈ S then (if T w S < c then 1 else 0) else 0) := by
  simp_rw [← Ex_mul_left]
  rw [← Ex_finsum]
  unfold M
  apply Ex_congr
  intro S hS
  have : ∑ i ∈ s, w i * (if i ∈ S then (if T w S < c then (1 : ℝ) else 0) else 0) =
      ∑ i ∈ s, (if i ∈ S then w i * (if T w S < c then 1 else 0) else 0) := by
    apply Finset.sum_congr rfl; intro i _; split_ifs <;> simp
  rw [this, sum_mem_ite hS, ← Finset.sum_mul]
  unfold T
  split_ifs <;> simp

/-- `Q = ∑ᵢ wᵢ E[Bᵢ T 1{T<c}]`. -/
lemma Q_eq_sum (s : Finset ι) (c : ℝ) :
    Q p w s c = ∑ i ∈ s, w i *
      Ex p s (fun S => if i ∈ S then (if T w S < c then T w S else 0) else 0) := by
  simp_rw [← Ex_mul_left]
  rw [← Ex_finsum]
  unfold Q
  apply Ex_congr
  intro S hS
  have : ∑ i ∈ s, w i * (if i ∈ S then (if T w S < c then T w S else 0) else 0) =
      ∑ i ∈ s, (if i ∈ S then w i * (if T w S < c then T w S else 0) else 0) := by
    apply Finset.sum_congr rfl; intro i _; split_ifs <;> simp
  rw [this, sum_mem_ite hS, ← Finset.sum_mul]
  change _ = T w S * _
  split_ifs <;> ring

end Samuels

end

/- ===== Bernoulli/Step.lean ===== -/
section

/-!
# The real-number core of one step of Ling's Claim 3.2

With `Z₀ = P(T₋ᵢ < 1)`, `Z₁ = P(T₋ᵢ < 1 - wᵢ)`, `M₀, M₁` the corresponding truncated first
moments, and `m = E[T | T < 1]`, the facts supplied by the finite-sum layer are
* `Z = (1-p) Z₀ + p Z₁`, `m Z = (1-p) M₀ + p (M₁ + w Z₁)`,
* `(1 - w)(Z₀ - Z₁) ≤ M₀ - M₁` (on `{1-w ≤ T₋ᵢ < 1}` we have `T₋ᵢ ≥ 1 - w`),
* `M₀ ≤ m Z₀` (the choice of `i`, i.e. `R₋ᵢ ≥ R`).
From these: `Δ = w p - (m - M₀/Z₀) ∈ [0, a]` and
`-log Z ≤ -log Z₀ + (Δ / a) log (R / (R - a))` with `R = 1 - m`.
-/

open Real

namespace Samuels

/-- Chord bound for the convex function `-log (1 - x)` vanishing at `0`. -/
lemma neg_log_one_sub_le {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy1 : y < 1) (hy0 : 0 < y) :
    -log (1 - x) ≤ x / y * (-log (1 - y)) := by
  have hc := strictConcaveOn_log_Ioi.concaveOn
  have h1 : (1 : ℝ) ∈ Set.Ioi 0 := by norm_num
  have h2 : 1 - y ∈ Set.Ioi (0 : ℝ) := by simp; linarith
  have ht0 : 0 ≤ x / y := div_nonneg hx hy0.le
  have ht1 : x / y ≤ 1 := (div_le_one hy0).mpr hxy
  have := hc.2 h1 h2 (sub_nonneg.mpr ht1) ht0 (by ring)
  simp only [smul_eq_mul, log_one, mul_zero, zero_add] at this
  have harg : (1 - x / y) * 1 + x / y * (1 - y) = 1 - x := by
    field_simp; ring
  rw [harg] at this
  linarith

/-- One step of Claim 3.2, in pure real arithmetic. -/
theorem claim32_step {p w a Z0 Z1 M0 M1 m : ℝ}
    (hZ0 : 0 < Z0) (hZ1 : 0 ≤ Z1) (hZ10 : Z1 ≤ Z0) (hp0 : 0 ≤ p) (hp1 : p < 1)
    (hM : (1 - w) * (Z0 - Z1) ≤ M0 - M1)
    (hmZ : m * ((1 - p) * Z0 + p * Z1) = (1 - p) * M0 + p * (M1 + w * Z1))
    (hm0 : M0 ≤ m * Z0) (hwa : w * p ≤ a) (ha : 0 < a) (haR : a < 1 - m) :
    0 ≤ w * p - (m - M0 / Z0) ∧ w * p - (m - M0 / Z0) ≤ a ∧
      -log ((1 - p) * Z0 + p * Z1) ≤
        -log Z0 + (w * p - (m - M0 / Z0)) / a * log ((1 - m) / ((1 - m) - a)) := by
  set Δ := w * p - (m - M0 / Z0) with hΔ
  set R := 1 - m with hR
  have hRpos : 0 < R := by linarith
  set ρ := p * (Z0 - Z1) / Z0 with hρ
  have hρ0 : 0 ≤ ρ := div_nonneg (mul_nonneg hp0 (sub_nonneg.mpr hZ10)) hZ0.le
  have hZρ : (1 - p) * Z0 + p * Z1 = Z0 * (1 - ρ) := by
    rw [hρ]; field_simp; ring
  have hm0' : M0 / Z0 ≤ m := (div_le_iff₀ hZ0).mpr hm0
  -- `Z₀ Δ = p ((M₀ - M₁) + (w - m)(Z₀ - Z₁))`
  have hkey : Z0 * Δ = p * ((M0 - M1) + (w - m) * (Z0 - Z1)) := by
    rw [hΔ, mul_sub, mul_sub, mul_div_cancel₀ _ hZ0.ne']
    linear_combination -hmZ
  have hρR : ρ * R ≤ Δ := by
    have h1 : p * ((1 - w) * (Z0 - Z1) + (w - m) * (Z0 - Z1)) ≤
        p * ((M0 - M1) + (w - m) * (Z0 - Z1)) :=
      mul_le_mul_of_nonneg_left (by linarith) hp0
    rw [← hkey] at h1
    have h2 : ρ * R * Z0 = p * ((1 - w) * (Z0 - Z1) + (w - m) * (Z0 - Z1)) := by
      rw [hρ, hR]; field_simp; ring
    have h3 : ρ * R * Z0 ≤ Δ * Z0 := by rw [h2]; linarith
    exact le_of_mul_le_mul_right h3 hZ0
  have hΔ0 : 0 ≤ Δ := le_trans (mul_nonneg hρ0 hRpos.le) hρR
  have hΔa : Δ ≤ a := by rw [hΔ]; linarith
  refine ⟨hΔ0, hΔa, ?_⟩
  -- the logarithmic estimate
  have hy0 : 0 < a / R := div_pos ha hRpos
  have hy1 : a / R < 1 := (div_lt_one hRpos).mpr haR
  have hρy : ρ ≤ a / R := by
    rw [le_div_iff₀ hRpos]; linarith
  have hρ1 : ρ < 1 := lt_of_le_of_lt hρy hy1
  have hchord := neg_log_one_sub_le hρ0 hρy hy1 hy0
  have hlogR : -log (1 - a / R) = log (R / (R - a)) := by
    have : 1 - a / R = (R - a) / R := by field_simp
    rw [this, ← log_inv, inv_div]
  rw [hlogR] at hchord
  have hlogpos : 0 ≤ log (R / (R - a)) := by
    apply log_nonneg
    rw [le_div_iff₀ (by linarith)]; linarith
  have hcoef : ρ / (a / R) ≤ Δ / a := by
    rw [div_div_eq_mul_div, div_le_div_iff_of_pos_right ha]; linarith
  have hb : ρ / (a / R) * log (R / (R - a)) ≤ Δ / a * log (R / (R - a)) :=
    mul_le_mul_of_nonneg_right hcoef hlogpos
  rw [hZρ, log_mul hZ0.ne' (by linarith)]
  linarith

end Samuels

end

/- ===== Bernoulli/Claim32.lean ===== -/
section

/-!
# Ling's Claims 3.1 and 3.2 (interior case, `0 ≤ pᵢ < 1`)

`R s = 1 - E[T | T < 1]` and `L s = E[T] - E[T | T < 1]`.

* `exists_index`: some coordinate `i` has `E[T₋ᵢ | T₋ᵢ < 1] ≤ E[T | T < 1]` (this is
  `Cov(T, Bᵢ | T < 1) ≥ 0` in Ling's proof).  Following a suggestion of Fable, we take `i` with
  `wᵢ Dᵢ ≥ 0` where `∑ wᵢ Dᵢ = Var(T | T<1) · P(T<1) ≥ 0`, and treat `wᵢ = 0` directly.
* `claim32`: the Bellman induction.
-/

open Finset Real

namespace Samuels

variable {ι : Type*} [DecidableEq ι] {p w : ι → ℝ}

/-- `R = 1 - E[T | T < 1]`. -/
noncomputable def Rv (p w : ι → ℝ) (s : Finset ι) : ℝ := 1 - M p w s 1 / Z p w s 1

/-- `L = E[T] - E[T | T < 1]`. -/
noncomputable def Lv (p w : ι → ℝ) (s : Finset ι) : ℝ := E p w s - M p w s 1 / Z p w s 1

lemma exists_index {s : Finset ι} (hs : s.Nonempty) (hp0 : ∀ i ∈ s, 0 ≤ p i)
    (hp1 : ∀ i ∈ s, p i < 1) (hw : ∀ i ∈ s, 0 ≤ w i) :
    ∃ i ∈ s, M p w (s.erase i) 1 ≤ M p w s 1 / Z p w s 1 * Z p w (s.erase i) 1 := by
  have hp1' : ∀ i ∈ s, p i ≤ 1 := fun i hi => (hp1 i hi).le
  have hZ : 0 < Z p w s 1 := Z_pos hp0 hp1 hw one_pos
  set m := M p w s 1 / Z p w s 1 with hm
  have hmZ : m * Z p w s 1 = M p w s 1 := by rw [hm]; field_simp
  -- `Dᵢ = E[Bᵢ T 1{T<1}] - m E[Bᵢ 1{T<1}]`
  let D : ι → ℝ := fun i =>
    p i * (M p w (s.erase i) (1 - w i) + w i * Z p w (s.erase i) (1 - w i)) -
      m * (p i * Z p w (s.erase i) (1 - w i))
  have hsum : 0 ≤ ∑ i ∈ s, w i * D i := by
    have hQ := Q_eq_sum (p := p) (w := w) s 1
    have hMs := M_eq_sum (p := p) (w := w) s 1
    have hB : ∀ i ∈ s, Ex p s (fun S => if i ∈ S then (if T w S < 1 then T w S else 0) else 0) =
        p i * (M p w (s.erase i) (1 - w i) + w i * Z p w (s.erase i) (1 - w i)) := by
      intro i hi
      conv_lhs => rw [← insert_erase hi]
      exact Ex_mem_T (notMem_erase i s) 1
    have hA : ∀ i ∈ s, Ex p s (fun S => if i ∈ S then (if T w S < 1 then 1 else 0) else 0) =
        p i * Z p w (s.erase i) (1 - w i) := by
      intro i hi
      conv_lhs => rw [← insert_erase hi]
      exact Ex_mem_ind (notMem_erase i s) 1
    rw [Finset.sum_congr rfl (fun i hi => by rw [hB i hi])] at hQ
    rw [Finset.sum_congr rfl (fun i hi => by rw [hA i hi])] at hMs
    have hcs := M_sq_le hp0 hp1' 1 hZ (w := w)
    have : ∑ i ∈ s, w i * D i = Q p w s 1 - m * M p w s 1 := by
      simp only [D, mul_sub, Finset.sum_sub_distrib]
      rw [hQ, hMs, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl; intro i _; ring
    rw [this]
    have : m * M p w s 1 = M p w s 1 ^ 2 / Z p w s 1 := by rw [hm]; ring
    linarith
  obtain ⟨i, hi, hDi⟩ : ∃ i ∈ s, 0 ≤ w i * D i := by
    by_contra h
    push Not at h
    have := Finset.sum_lt_sum_of_nonempty hs h
    simp at this
    linarith
  refine ⟨i, hi, ?_⟩
  have his : i ∉ (s.erase i) := notMem_erase i s
  have hss : insert i (s.erase i) = s := insert_erase hi
  have hZr := Z_insert (p := p) (w := w) his 1
  have hMr := M_insert (p := p) (w := w) his 1
  rw [hss] at hZr hMr
  have hpi1 : 0 < 1 - p i := sub_pos.mpr (hp1 i hi)
  -- `Dᵢ = (1 - pᵢ)(m Z₀ - M₀)`
  have hDform : D i = (1 - p i) * (m * Z p w (s.erase i) 1 - M p w (s.erase i) 1) := by
    simp only [D]
    linear_combination -hMr + m * hZr - hmZ
  rcases (hw i hi).lt_or_eq with hwpos | hwzero
  · have : 0 ≤ D i := by
      by_contra h; push Not at h; nlinarith
    rw [hDform] at this
    nlinarith
  · -- `wᵢ = 0`: then `Z₁ = Z₀` and `M₁ = M₀`
    have hD2 : D i = p i * (M p w (s.erase i) 1 - m * Z p w (s.erase i) 1) := by
      simp only [D, ← hwzero, sub_zero]; ring
    have : (m * Z p w (s.erase i) 1 - M p w (s.erase i) 1) = 0 := by
      have h := hDform.symm.trans hD2
      linear_combination h
    linarith

/-- **Claim 3.2** (Bellman induction). -/
theorem claim32 (p w a : ι → ℝ) (s : Finset ι) (hp0 : ∀ i ∈ s, 0 ≤ p i)
    (hp1 : ∀ i ∈ s, p i < 1) (hw : ∀ i ∈ s, 0 ≤ w i) (hwa : ∀ i ∈ s, w i * p i ≤ a i)
    (ha : ∀ i ∈ s, 0 < a i) (hR : ∀ i ∈ s, a i < Rv p w s) :
    ∃ ℓ : ι → ℝ, (∀ i ∈ s, 0 ≤ ℓ i ∧ ℓ i ≤ a i) ∧ ∑ i ∈ s, ℓ i = Lv p w s ∧
      -log (Z p w s 1) ≤ ∑ i ∈ s, ℓ i / a i * log (Rv p w s / (Rv p w s - a i)) := by
  induction s using Finset.strongInduction with
  | H s ih =>
  rcases s.eq_empty_or_nonempty with rfl | hs
  · refine ⟨fun _ => 0, by simp, ?_, ?_⟩
    · simp [Lv, E, M, Z, T]
    · simp [Z, T]
  have hp1' : ∀ i ∈ s, p i ≤ 1 := fun i hi => (hp1 i hi).le
  obtain ⟨i, hi, hchoice⟩ := exists_index hs hp0 hp1 hw
  set s' := s.erase i with hs'
  have his : i ∉ s' := notMem_erase i s
  have hss : insert i s' = s := insert_erase hi
  have hsub : s' ⊆ s := erase_subset i s
  have hp0' : ∀ j ∈ s', 0 ≤ p j := fun j hj => hp0 j (hsub hj)
  have hp1'' : ∀ j ∈ s', p j < 1 := fun j hj => hp1 j (hsub hj)
  have hw' : ∀ j ∈ s', 0 ≤ w j := fun j hj => hw j (hsub hj)
  have hZ : 0 < Z p w s 1 := Z_pos hp0 hp1 hw one_pos
  have hZ0 : 0 < Z p w s' 1 := Z_pos hp0' hp1'' hw' one_pos
  set m := M p w s 1 / Z p w s 1 with hm
  set m0 := M p w s' 1 / Z p w s' 1 with hm0
  have hmm0 : m0 ≤ m := by rw [hm0, div_le_iff₀ hZ0]; exact hchoice
  have hRR : Rv p w s ≤ Rv p w s' := by simp only [Rv]; linarith
  -- induction hypothesis on `s'`
  obtain ⟨ℓ', hℓ'b, hℓ'sum, hℓ'log⟩ := ih s' (erase_ssubset hi) hp0' hp1'' hw'
    (fun j hj => hwa j (hsub hj)) (fun j hj => ha j (hsub hj))
    (fun j hj => lt_of_lt_of_le (hR j (hsub hj)) hRR)
  -- the real step
  have hZr := Z_insert (p := p) (w := w) his 1
  have hMr := M_insert (p := p) (w := w) his 1
  rw [hss] at hZr hMr
  have hZ1 := Z_nonneg (w := w) hp0' (fun j hj => (hp1'' j hj).le) (1 - w i)
  have hZ1le := Z_mono (w := w) hp0' (fun j hj => (hp1'' j hj).le)
    (show 1 - w i ≤ 1 by linarith [hw i hi])
  have hMsub := M_sub_ge (w := w) hp0' (fun j hj => (hp1'' j hj).le)
    (show 1 - w i ≤ 1 by linarith [hw i hi])
  have hmZ : m * ((1 - p i) * Z p w s' 1 + p i * Z p w s' (1 - w i)) =
      (1 - p i) * M p w s' 1 + p i * (M p w s' (1 - w i) + w i * Z p w s' (1 - w i)) := by
    rw [← hZr, ← hMr, hm]; field_simp
  obtain ⟨hΔ0, hΔa, hlog⟩ := claim32_step hZ0 hZ1 hZ1le (hp0 i hi) (hp1 i hi) hMsub hmZ
    hchoice (hwa i hi) (ha i hi) (hR i hi)
  set Δ := w i * p i - (m - m0) with hΔ
  have hRdef : Rv p w s = 1 - m := rfl
  rw [← hZr, ← hRdef] at hlog
  -- assemble
  refine ⟨Function.update ℓ' i Δ, ?_, ?_, ?_⟩
  · intro j hj
    by_cases hji : j = i
    · subst hji; simp [hΔ0, hΔa]
    · rw [Function.update_of_ne hji]
      exact hℓ'b j (mem_erase.mpr ⟨hji, hj⟩)
  · have hE : E p w s = E p w s' + w i * p i := by
      rw [← hss, E, E, Finset.sum_insert his]; ring
    rw [← hss, Finset.sum_insert his, Function.update_self,
      Finset.sum_congr rfl (fun j hj => Function.update_of_ne (ne_of_mem_erase hj) Δ ℓ'),
      hℓ'sum, hss]
    simp only [Lv]
    rw [hE, hΔ, hm, hm0]
    ring
  · rw [← hss, Finset.sum_insert his, Function.update_self,
      Finset.sum_congr rfl (fun j hj => by rw [Function.update_of_ne (ne_of_mem_erase hj) Δ ℓ'])]
    rw [hss]
    have hmono : ∑ j ∈ s', ℓ' j / a j * log (Rv p w s' / (Rv p w s' - a j)) ≤
        ∑ j ∈ s', ℓ' j / a j * log (Rv p w s / (Rv p w s - a j)) := by
      apply Finset.sum_le_sum
      intro j hj
      have haj := ha j (hsub hj)
      have hRj := hR j (hsub hj)
      apply mul_le_mul_of_nonneg_left _ (div_nonneg (hℓ'b j hj).1 haj.le)
      apply log_le_log
      · apply div_pos <;> linarith
      · rw [div_le_div_iff₀ (by linarith) (by linarith)]
        nlinarith
    linarith

end Samuels

end

/- ===== Bernoulli/Thm21.lean ===== -/
section

/-!
# Theorem 2.1 of Ling, equal-bound case

If `0 ≤ pᵢ < 1`, `wᵢ ≥ 0` and `wᵢ pᵢ ≤ a` for one common `a > 0`, and `d = 1 - E[T] > 0`, then
`P(T < 1) ≥ min (d/(d+a)) e⁻¹`.

This is the specialization of Ling's Theorem 2.1 to `a₁ = ⋯ = aₙ = a`, combined with the real
form of Prop. 5.2: when `L ≤ a`, Claim 3.1 gives `P(T<1) ≥ d/(d+L) ≥ d/(d+a)`; when `L > a`,
Claim 3.2 gives `P(T<1) ≥ (1 - a/R)^{L/a} = (1 - 1/(x + D))^x` with `x = L/a ≥ 1`, `D = d/a`,
which is `≥ min (D/(1+D)) e⁻¹` by `min_le_rpow`.  Claims 3.3–3.4 are not needed here.
-/

open Finset Real

namespace Samuels

variable {ι : Type*} [DecidableEq ι]

theorem bernoulli_equal_bound (p w : ι → ℝ) (s : Finset ι) (hp0 : ∀ i ∈ s, 0 ≤ p i)
    (hp1 : ∀ i ∈ s, p i < 1) (hw : ∀ i ∈ s, 0 ≤ w i) {a : ℝ} (ha : 0 < a)
    (hwa : ∀ i ∈ s, w i * p i ≤ a) (hd : 0 < 1 - E p w s) :
    min ((1 - E p w s) / ((1 - E p w s) + a)) (exp (-1)) ≤ Z p w s 1 := by
  have hp1' : ∀ i ∈ s, p i ≤ 1 := fun i hi => (hp1 i hi).le
  set d := 1 - E p w s with hddef
  have hZ : 0 < Z p w s 1 := Z_pos hp0 hp1 hw one_pos
  have hZM : d ≤ Z p w s 1 - M p w s 1 := one_sub_E_le hp0 hp1'
  set R := Rv p w s with hRdef
  set L := Lv p w s with hLdef
  have hRL : R = d + L := by simp only [hRdef, hLdef, Rv, Lv, hddef]; ring
  have hZR : Z p w s 1 * R = Z p w s 1 - M p w s 1 := by
    simp only [hRdef, Rv]; field_simp
  have hRpos : 0 < R := by
    by_contra h; push Not at h
    have : Z p w s 1 * R ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hZ.le h
    linarith
  rcases le_or_gt L a with hLa | hLa
  · -- Claim 3.1: `P(T<1) ≥ d/R ≥ d/(d+a)`
    apply (min_le_left _ _).trans
    rw [div_le_iff₀ (by linarith)]
    have h1 : d ≤ Z p w s 1 * R := by linarith
    have h2 : Z p w s 1 * R ≤ Z p w s 1 * (d + a) :=
      mul_le_mul_of_nonneg_left (by linarith) hZ.le
    linarith
  · -- Claim 3.2
    have haR : a < R := by linarith
    obtain ⟨ℓ, -, hℓsum, hℓlog⟩ :=
      claim32 p w (fun _ => a) s hp0 hp1 hw hwa (fun _ _ => ha) (fun _ _ => haR)
    rw [← Finset.sum_mul, ← Finset.sum_div, hℓsum] at hℓlog
    -- `Z ≥ (1 - a/R)^(L/a)`
    have hbase : 0 < 1 - a / R := by rw [sub_pos, div_lt_one hRpos]; exact haR
    have hlog1 : log (R / (R - a)) = -log (1 - a / R) := by
      have : 1 - a / R = (R - a) / R := by field_simp
      rw [this, ← log_inv, inv_div]
    have hZge : (1 - a / R) ^ (L / a) ≤ Z p w s 1 := by
      rw [rpow_def_of_pos hbase, ← exp_log hZ]
      apply exp_le_exp.mpr
      rw [hlog1] at hℓlog
      linarith
    have hD : 0 < d / a := div_pos hd ha
    have hx : 1 ≤ L / a := by rw [le_div_iff₀ ha]; linarith
    have hmain := min_le_rpow hD hx
    have he1 : 1 - 1 / (L / a + d / a) = 1 - a / R := by
      rw [hRL]; field_simp; ring
    have he2 : d / a / (1 + d / a) = d / (d + a) := by field_simp; ring
    rw [he1, he2] at hmain
    exact hmain.trans hZge

end Samuels

end

/- ===== Bernoulli/TwoPointBound.lean ===== -/
section

/-!
# Bernoullification for mean-one two-point laws (Ling §2.2, equal means)

Coordinate `i` takes value `xᵢ` with probability `1 - pᵢ` and `yᵢ` with probability `pᵢ`, where
`0 ≤ xᵢ ≤ yᵢ`, `pᵢ (yᵢ - xᵢ) = 1 - xᵢ` (mean one) and `0 ≤ pᵢ < 1`.  Atoms at one are
`x = y = 1`, `p = 0`.  With `Λ = δ + ∑ (1 - xᵢ)`, `wᵢ = (yᵢ - xᵢ)/Λ`, `a = 1/Λ`,
the event `∑ Yᵢ < n + δ` is `T < 1`, `wᵢ pᵢ = (1-xᵢ)/Λ ≤ a`, and `d = 1 - E[T] = δ/Λ`,
so `d/(d+a) = δ/(1+δ)`.
-/

open Finset Real

namespace Samuels

theorem twoPoint_bound {n : ℕ} (x y p : Fin n → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hx0 : ∀ i, 0 ≤ x i) (hxy : ∀ i, x i ≤ y i) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i < 1)
    (hpxy : ∀ i, p i * (y i - x i) = 1 - x i) :
    min (δ / (1 + δ)) (exp (-1)) ≤
      Ex p univ (fun S => if ∑ i, x i + ∑ i ∈ S, (y i - x i) < n + δ then 1 else 0) := by
  have hx1 : ∀ i, 0 ≤ 1 - x i := fun i => by
    rw [← hpxy i]; exact mul_nonneg (hp0 i) (sub_nonneg.mpr (hxy i))
  set Λ := δ + ∑ i, (1 - x i) with hΛ
  have hΛpos : 0 < Λ := by
    have : 0 ≤ ∑ i, (1 - x i) := Finset.sum_nonneg fun i _ => hx1 i
    linarith
  set w : Fin n → ℝ := fun i => (y i - x i) / Λ with hw
  have hw0 : ∀ i ∈ (univ : Finset (Fin n)), 0 ≤ w i :=
    fun i _ => div_nonneg (sub_nonneg.mpr (hxy i)) hΛpos.le
  have hwp : ∀ i, w i * p i = (1 - x i) / Λ := fun i => by
    simp only [hw]; rw [← hpxy i]; ring
  have hwa : ∀ i ∈ (univ : Finset (Fin n)), w i * p i ≤ 1 / Λ := fun i _ => by
    rw [hwp i]
    exact div_le_div_of_nonneg_right (by linarith [hx0 i]) hΛpos.le
  have hE : E p w univ = (∑ i, (1 - x i)) / Λ := by
    simp only [E, hwp, Finset.sum_div]
  have hd : 1 - E p w univ = δ / Λ := by
    rw [hE]; field_simp; rw [hΛ]; ring
  have hmain := bernoulli_equal_bound p w univ (fun i _ => hp0 i) (fun i _ => hp1 i) hw0
    (one_div_pos.mpr hΛpos) hwa (by rw [hd]; exact div_pos hδ hΛpos)
  have hratio : (1 - E p w univ) / ((1 - E p w univ) + 1 / Λ) = δ / (1 + δ) := by
    rw [hd]; field_simp; ring
  rw [hratio] at hmain
  refine hmain.trans (le_of_eq ?_)
  unfold Z
  apply Ex_congr
  intro S _
  have hsumx : ∑ i, x i = n - ∑ i, (1 - x i) := by
    simp [Finset.sum_sub_distrib]
  have hiff : T w S < 1 ↔ ∑ i, x i + ∑ i ∈ S, (y i - x i) < n + δ := by
    simp only [T, hw, ← Finset.sum_div]
    rw [div_lt_one hΛpos, hsumx, hΛ]
    constructor <;> intro h <;> linarith
  by_cases h : T w S < 1
  · rw [if_pos h, if_pos (hiff.mp h)]
  · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]

end Samuels

end

/- ===== Bridge/PiDirac.lean ===== -/
section

/-!
# Finite products of two-point laws

`twoPt p x y = (1-p) δₓ + p δ_y`.  A finite product of such laws is the finite sum of Dirac
masses at the vectors `v_S = (if i ∈ S then yᵢ else xᵢ)` with weights `wt p univ S`
(the strategy `Measure.pi_eq` + `Finset.prod_add` was suggested by Gemini 4 Neon).
Consequently the product measure of any measurable set `A` is the finite Bernoulli
expectation `Ex p univ (1{v_S ∈ A})`.
-/

open MeasureTheory Finset ENNReal

namespace Samuels

noncomputable section

open scoped Classical

/-- The two-point law `(1-p) δₓ + p δ_y`. -/
def twoPt (p x y : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 - p) • Measure.dirac x + ENNReal.ofReal p • Measure.dirac y

lemma twoPt_isProbability {p x y : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (twoPt p x y) := by
  constructor
  simp [twoPt, ← ENNReal.ofReal_add (sub_nonneg.mpr hp1) hp0]

lemma twoPt_apply (p x y : ℝ) {B : Set ℝ} (hB : MeasurableSet B) :
    twoPt p x y B = (if y ∈ B then ENNReal.ofReal p else 0) +
      (if x ∈ B then ENNReal.ofReal (1 - p) else 0) := by
  simp only [twoPt, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply' _ hB,
    smul_eq_mul]
  simp only [Set.indicator_apply]
  split_ifs <;> simp [add_comm]

variable {n : ℕ}

/-- The vector encoded by a high set. -/
def vecOf (x y : Fin n → ℝ) (S : Finset (Fin n)) : Fin n → ℝ :=
  fun i => if i ∈ S then y i else x i

theorem pi_twoPt_eq (p x y : Fin n → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) :
    haveI := fun i => twoPt_isProbability (x := x i) (y := y i) (hp0 i) (hp1 i)
    Measure.pi (fun i => twoPt (p i) (x i) (y i)) =
      ∑ S ∈ (univ : Finset (Fin n)).powerset,
        ENNReal.ofReal (wt p univ S) • Measure.dirac (vecOf x y S) := by
  haveI := fun i => twoPt_isProbability (x := x i) (y := y i) (hp0 i) (hp1 i)
  apply Measure.pi_eq
  intro s hs
  have hbox : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
  simp only [Measure.finsetSum_apply, Measure.smul_apply, Measure.dirac_apply' _ hbox,
    smul_eq_mul]
  simp_rw [twoPt_apply _ _ _ (hs _)]
  rw [Finset.prod_add (fun i => if y i ∈ s i then ENNReal.ofReal (p i) else 0)
    (fun i => if x i ∈ s i then ENNReal.ofReal (1 - p i) else 0)]
  apply Finset.sum_congr rfl
  intro S _
  have hwt : ENNReal.ofReal (wt p univ S) =
      (∏ i ∈ S, ENNReal.ofReal (p i)) * ∏ i ∈ univ \ S, ENNReal.ofReal (1 - p i) := by
    unfold wt
    rw [ENNReal.ofReal_mul (Finset.prod_nonneg fun i _ => hp0 i),
      ENNReal.ofReal_prod_of_nonneg (fun i _ => hp0 i),
      ENNReal.ofReal_prod_of_nonneg (fun i _ => sub_nonneg.mpr (hp1 i))]
  rw [hwt, Set.indicator_apply]
  by_cases hmem : vecOf x y S ∈ Set.univ.pi s
  · rw [if_pos hmem, Pi.one_apply, mul_one]
    have hm : ∀ i, vecOf x y S i ∈ s i := fun i => hmem i (Set.mem_univ i)
    congr 1
    · apply Finset.prod_congr rfl
      intro i hi
      have := hm i
      simp only [vecOf, if_pos hi] at this
      rw [if_pos this]
    · apply Finset.prod_congr rfl
      intro i hi
      have := hm i
      have hiS : i ∉ S := (mem_sdiff.mp hi).2
      simp only [vecOf, if_neg hiS] at this
      rw [if_pos this]
  · rw [if_neg hmem, mul_zero]
    simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hmem
    obtain ⟨i, hi⟩ := hmem
    by_cases hiS : i ∈ S
    · simp only [vecOf, if_pos hiS] at hi
      rw [Finset.prod_eq_zero hiS (if_neg hi), zero_mul]
    · simp only [vecOf, if_neg hiS] at hi
      rw [Finset.prod_eq_zero (mem_sdiff.mpr ⟨mem_univ i, hiS⟩) (if_neg hi), mul_zero]

/-- The product measure of a measurable set, as a finite Bernoulli expectation. -/
theorem pi_twoPt_apply (p x y : Fin n → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    {A : Set (Fin n → ℝ)} (hA : MeasurableSet A) :
    haveI := fun i => twoPt_isProbability (x := x i) (y := y i) (hp0 i) (hp1 i)
    (Measure.pi (fun i => twoPt (p i) (x i) (y i)) A).toReal =
      Ex p univ (fun S => if vecOf x y S ∈ A then 1 else 0) := by
  haveI := fun i => twoPt_isProbability (x := x i) (y := y i) (hp0 i) (hp1 i)
  rw [pi_twoPt_eq p x y hp0 hp1]
  simp only [Measure.finsetSum_apply, Measure.smul_apply, Measure.dirac_apply' _ hA,
    smul_eq_mul]
  rw [ENNReal.toReal_sum (fun S _ => by
    rw [Set.indicator_apply]; split_ifs <;> simp)]
  unfold Ex
  apply Finset.sum_congr rfl
  intro S hS
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal
    (wt_nonneg (fun i _ => hp0 i) (fun i _ => hp1 i) (mem_powerset.mp hS))]
  by_cases h : vecOf x y S ∈ A
  · rw [Set.indicator_of_mem h]; simp [h]
  · rw [Set.indicator_of_notMem h]; simp [h]

end

end Samuels

end

/- ===== Bridge/MeanOne.lean ===== -/
section

/-!
# Mean-one product laws (Ling Prop. 2.3, Lemma 2.4, §2.2 for equal means)

For probability measures `νᵢ` on `ℝ` with `νᵢ (-∞, 0) = 0` and mean one,
`(⊗ νᵢ) {z | ∑ zᵢ < n + δ} ≥ min (δ/(1+δ)) e⁻¹`.

The two-point decomposition (Prop. 2.3) and the product mixture (Lemma 2.4) come from the
vendored LeanPool files (`pi_eq_recursiveMeanOneAugmented_mixture`,
`ae_recursiveAugmentedLatent_nonnegative`, `recursiveAugmentedKernel_apply_eq_conditionalProduct`).
For each fixed latent parameter vector, the conditional law is a product of two-point laws,
which `pi_twoPt_apply` turns into a finite Bernoulli sum, bounded by `twoPoint_bound`.
-/

open MeasureTheory ProbabilityTheory Finset Real

namespace Samuels

noncomputable section

open Feige

/-- Bernoulli parameter of an augmented latent coordinate (`0` for the atom at one). -/
def cp : AugmentedTwoPointParams → ℝ
  | Sum.inl _ => 0
  | Sum.inr q => (1 - q.1.1) / (q.1.2 - q.1.1)

/-- Low point of an augmented latent coordinate. -/
def cx : AugmentedTwoPointParams → ℝ
  | Sum.inl _ => 1
  | Sum.inr q => q.1.1

/-- High point of an augmented latent coordinate. -/
def cy : AugmentedTwoPointParams → ℝ
  | Sum.inl _ => 1
  | Sum.inr q => q.1.2

lemma cp_nonneg (a : AugmentedTwoPointParams) : 0 ≤ cp a := by
  cases a with
  | inl _ => simp [cp]
  | inr q =>
    simp only [cp]
    exact div_nonneg (by linarith [q.2.1]) (by linarith [q.2.2.2])

lemma cp_le_one (a : AugmentedTwoPointParams) : cp a ≤ 1 := by
  cases a with
  | inl _ => simp [cp]
  | inr q =>
    simp only [cp]
    rw [div_le_one (by linarith [q.2.2.2])]
    linarith [q.2.2.1]

lemma kernel_eq_twoPt (a : AugmentedTwoPointParams) :
    augmentedTwoPointKernel a = twoPt (cp a) (cx a) (cy a) := by
  cases a with
  | inl u =>
    cases u
    rw [augmentedTwoPointKernel_atom]
    simp [twoPt, cp, cx, cy]
  | inr q =>
    rw [augmentedTwoPointKernel_pair]
    have hxy : q.1.1 < q.1.2 := q.2.2.2
    have hne : q.1.2 - q.1.1 ≠ 0 := by linarith
    simp only [twoPointMeasure, twoPointLowerWeight, twoPointUpperWeight, twoPt, cp, cx, cy]
    congr 3
    field_simp
    ring

lemma props_of_nonneg {a : AugmentedTwoPointParams} (ha : AugmentedParamNonnegative a) :
    0 ≤ cx a ∧ cx a ≤ cy a ∧ cp a < 1 ∧ cp a * (cy a - cx a) = 1 - cx a := by
  cases a with
  | inl _ => simp [cp, cx, cy]
  | inr q =>
    simp only [AugmentedParamNonnegative] at ha
    have hxy : q.1.1 < q.1.2 := q.2.2.2
    have hne : q.1.2 - q.1.1 ≠ 0 := by linarith
    simp only [cp, cx, cy]
    refine ⟨ha.1, hxy.le, ?_, ?_⟩
    · rw [div_lt_one (by linarith)]; linarith [ha.2]
    · field_simp

variable {n : ℕ}

/-- The target event. -/
def evt (n : ℕ) (δ : ℝ) : Set (Fin n → ℝ) := {z | ∑ i, z i < n + δ}

lemma measurableSet_evt (δ : ℝ) : MeasurableSet (evt n δ) :=
  measurableSet_lt (Finset.measurable_sum _ fun i _ => measurable_pi_apply i) measurable_const

/-- The bound for a fixed latent parameter vector. -/
theorem conditional_bound {δ : ℝ} (hδ : 0 < δ) (p : Fin n → AugmentedTwoPointParams)
    (hp : AugmentedParamsNonnegative p) :
    ENNReal.ofReal (min (δ / (1 + δ)) (exp (-1))) ≤ recursiveAugmentedKernel n p (evt n δ) := by
  rw [recursiveAugmentedKernel_apply_eq_conditionalProduct, augmentedConditionalProduct]
  have hfun : (fun i => augmentedTwoPointKernel (p i)) =
      fun i => twoPt (cp (p i)) (cx (p i)) (cy (p i)) := funext fun i => kernel_eq_twoPt (p i)
  rw [hfun]
  have hp0 : ∀ i, 0 ≤ cp (p i) := fun i => cp_nonneg _
  have hp1 : ∀ i, cp (p i) ≤ 1 := fun i => cp_le_one _
  have hval := pi_twoPt_apply (fun i => cp (p i)) (fun i => cx (p i)) (fun i => cy (p i))
    hp0 hp1 (measurableSet_evt (n := n) δ)
  haveI := fun i => twoPt_isProbability (x := cx (p i)) (y := cy (p i)) (hp0 i) (hp1 i)
  rw [ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)]
  refine le_of_le_of_eq ?_ hval.symm
  have hb := twoPoint_bound (fun i => cx (p i)) (fun i => cy (p i)) (fun i => cp (p i)) hδ
    (fun i => (props_of_nonneg (hp i)).1) (fun i => (props_of_nonneg (hp i)).2.1) hp0
    (fun i => (props_of_nonneg (hp i)).2.2.1) (fun i => (props_of_nonneg (hp i)).2.2.2)
  refine hb.trans (le_of_eq ?_)
  apply Ex_congr
  intro S _
  have hsum : ∑ i, vecOf (fun i => cx (p i)) (fun i => cy (p i)) S i =
      ∑ i, cx (p i) + ∑ i ∈ S, (cy (p i) - cx (p i)) := by
    have : ∀ i, vecOf (fun i => cx (p i)) (fun i => cy (p i)) S i =
        cx (p i) + (if i ∈ S then cy (p i) - cx (p i) else 0) := by
      intro i; simp only [vecOf]; split_ifs <;> ring
    simp only [this, Finset.sum_add_distrib]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  simp only [evt, Set.mem_setOf_eq, hsum]

/-- **Mean-one product bound.** -/
theorem pi_meanOne_bound {δ : ℝ} (hδ : 0 < δ) (ν : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (ν i)]
    (hint : ∀ i, Integrable (fun x : ℝ => x) (ν i)) (hmean : ∀ i, (∫ x, x ∂ν i) = 1)
    (hsupp : ∀ i, ν i (Set.Iio 0) = 0) :
    ENNReal.ofReal (min (δ / (1 + δ)) (exp (-1))) ≤ Measure.pi ν (evt n δ) := by
  haveI : ∀ i, IsProbabilityMeasure (meanOneAugmentedLatent (ν i)) :=
    fun i => meanOneAugmentedLatent_isProbability (hint i) (hmean i)
  rw [← pi_eq_recursiveMeanOneAugmented_mixture n ν hint hmean,
    Measure.bind_apply (measurableSet_evt δ) (Kernel.aemeasurable _)]
  have hae := ae_recursiveAugmentedLatent_nonnegative n ν hint hmean hsupp
  calc ENNReal.ofReal (min (δ / (1 + δ)) (exp (-1)))
      = ∫⁻ _, ENNReal.ofReal (min (δ / (1 + δ)) (exp (-1)))
          ∂recursiveAugmentedLatent n (fun i => meanOneAugmentedLatent (ν i)) := by
        rw [lintegral_const, measure_univ, mul_one]
    _ ≤ _ := by
        apply lintegral_mono_ae
        filter_upwards [hae] with p hp
        exact conditional_bound hδ p hp

end

end Samuels

end

/- ===== Main.lean ===== -/
section

/-!
# Sums of independent random variables with unbounded variance

Source: https://www.openproblemgarden.org/op/sums_of_independent_random_variables_with_unbounded_variance

Feige's conjecture for every `δ > 0`, with the sharp constant `min (δ/(1+δ)) e⁻¹`, following
Z. Ling, *On Samuels' Conjecture* (arXiv:2608.18392v2). The statement of `main` is copied
verbatim from `feige-manuscript/inputs/feige-statement.lean`.

Reduction (manuscript M1): `Yᵢ = (Xᵢ + (μ - E Xᵢ))/μ` are independent, nonnegative, of mean one,
and `∑ Xᵢ - E[∑ Xᵢ] < δ μ ↔ ∑ Yᵢ < n + δ`. The joint law of `Y` is the product of its marginals
(`iIndepFun_iff_map_fun_eq_pi_map`, which only needs `AEMeasurable`), and
`Samuels.pi_meanOne_bound` bounds the product measure.
-/

namespace Samuels.Submission

open MeasureTheory ProbabilityTheory

theorem feige_main :
    ∀ (n : ℕ) (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (X : Fin n → Ω → ℝ) (μ δ : ℝ), 0 < μ → 0 < δ →
      iIndepFun X ℙ → (∀ i ω, 0 ≤ X i ω) → (∀ i, Integrable (X i)) → (∀ i, 𝔼[X i] ≤ μ) →
      min (δ / (1 + δ)) (Real.exp (-1)) ≤
        (ℙ {ω | ∑ i, X i ω - 𝔼[fun ω' => ∑ i, X i ω'] < δ * μ}).toReal := by
  intro n Ω _ _ X μ δ hμ hδ hind hnn hint hmean
  set m : Fin n → ℝ := fun i => ∫ ω, X i ω with hm
  let g : Fin n → ℝ → ℝ := fun i x => (x + (μ - m i)) / μ
  have hg : ∀ i, Measurable (g i) := fun i => by fun_prop
  let Y : Fin n → Ω → ℝ := fun i ω => g i (X i ω)
  have hindY : iIndepFun Y ℙ := hind.comp g hg
  have haeX : ∀ i, AEMeasurable (X i) ℙ := fun i => (hint i).aemeasurable
  have haeY : ∀ i, AEMeasurable (Y i) ℙ := fun i => (hg i).comp_aemeasurable (haeX i)
  have hYnn : ∀ i ω, 0 ≤ Y i ω := fun i ω => by
    have := hmean i
    exact div_nonneg (by linarith [hnn i ω]) hμ.le
  have hintY : ∀ i, Integrable (Y i) ℙ := fun i =>
    ((hint i).add (integrable_const (μ - m i))).div_const μ
  have hmeanY : ∀ i, ∫ ω, Y i ω = 1 := fun i => by
    simp only [Y, g]
    rw [integral_div, integral_add (hint i) (integrable_const _), integral_const]
    simp [m, hμ.ne']
  -- marginals
  let ν : Fin n → Measure ℝ := fun i => (ℙ : Measure Ω).map (Y i)
  have : ∀ i, IsProbabilityMeasure (ν i) := fun i =>
    (Measure.isProbabilityMeasure_map_iff (haeY i)).mpr inferInstance
  have hνint : ∀ i, Integrable (fun x : ℝ => x) (ν i) := fun i => by
    exact (integrable_map_measure (g := id) aestronglyMeasurable_id (haeY i)).mpr (hintY i)
  have hνmean : ∀ i, ∫ x, x ∂(ν i) = 1 := fun i => by
    exact (integral_map (φ := Y i) (f := id) (haeY i) aestronglyMeasurable_id).trans (hmeanY i)
  have hνsupp : ∀ i, ν i (Set.Iio 0) = 0 := fun i => by
    rw [Measure.map_apply_of_aemeasurable (haeY i) measurableSet_Iio]
    have : Y i ⁻¹' Set.Iio 0 = ∅ := by
      ext ω; simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_empty_iff_false, iff_false, not_lt]
      exact hYnn i ω
    rw [this, measure_empty]
  have hjoint : (ℙ : Measure Ω).map (fun ω i => Y i ω) = Measure.pi ν :=
    (iIndepFun_iff_map_fun_eq_pi_map haeY).mp hindY
  have hbound := Samuels.pi_meanOne_bound hδ ν hνint hνmean hνsupp
  -- the event
  have hE : 𝔼[fun ω' => ∑ i, X i ω'] = ∑ i, m i := by
    simp only [m]
    exact integral_finsetSum _ (fun i _ => hint i)
  have hevent : {ω | ∑ i, X i ω - 𝔼[fun ω' => ∑ i, X i ω'] < δ * μ} =
      (fun ω i => Y i ω) ⁻¹' Samuels.evt n δ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Samuels.evt, hE, Y, g]
    rw [← Finset.sum_div, div_lt_iff₀ hμ, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    constructor <;> intro h <;> nlinarith
  have haevec : AEMeasurable (fun ω i => Y i ω) ℙ := by
    first
    | exact AEMeasurable.of_eval haeY
    | exact aemeasurable_pi_lambda _ haeY
  rw [hevent, ← Measure.map_apply_of_aemeasurable haevec (Samuels.measurableSet_evt δ), hjoint]
  exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp hbound

end Samuels.Submission

end

theorem OMA.solution : type_of% @OMA.S_opg_sums_of_independent_random_variables_with_unbounded_variance.main :=
  Samuels.Submission.feige_main
