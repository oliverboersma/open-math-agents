import FormalConjectures.ErdosProblems.«1132»
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Order.Filter.IsBounded
import Mathlib.Probability.Distributions.Cauchy
import Mathlib.Tactic
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.ProjIcc

/-!
# Tao's dense lower bound for Lebesgue functions

Terence Tao, Local Bernstein theory, and lower bounds for Lebesgue constants,
Corollary 1.11, https://arxiv.org/abs/2603.21453.

The supporting sharp additive lower bound and its lemmas are adapted from
Anonymous, Sharp pointwise bounds for Lebesgue functions, v9,
https://doi.org/10.5281/zenodo.22646508, licensed under CC BY 4.0
(https://creativecommons.org/licenses/by/4.0/). The imported dependency
closure of the additive theorem is combined in one file, with separate
scopes for the original modules, a distinct namespace, and edits for
the pinned Lean and Mathlib versions.

The final proof relates the two Lagrange formulas by reindexing, then
applies the point-dependent additive estimate and the divergence of ω.
-/

/- Erdos1132.Additive.WeightedLipschitz -/
section SourceErdos1132_Additive_WeightedLipschitz
/- # Uniform Lipschitz bounds for a squared weight divided by a positive density

Main paper: §5, derivative-jump energy.
-/

noncomputable section
open Set Real
namespace TaoAdditive1132

theorem square_div_bound {u r M c : ℝ} (hc : 0 < c) (hr : c ≤ r)
    (hM : 0 ≤ M) (hu : |u| ≤ M) : |u^2/r| ≤ M^2/c := by
  have hr0 := hc.trans_le hr
  rw [abs_of_nonneg (by positivity : 0 ≤ u^2/r)]
  exact div_le_div₀ (sq_nonneg _) (by nlinarith [abs_le.mp hu]) hc hr

theorem inverse_lipschitz_bound {r : ℝ → ℝ} {c D : ℝ} (hc : 0 < c)
    (hr : ∀ x, c ≤ r x) (hD : 0 ≤ D)
    (hlip : ∀ x y, |r x-r y| ≤ D*|x-y|) (x y : ℝ) :
    |(r x)⁻¹-(r y)⁻¹| ≤ (D/c^2)*|x-y| := by
  have hx := hc.trans_le (hr x)
  have hy := hc.trans_le (hr y)
  have he : (r x)⁻¹-(r y)⁻¹ = (r y-r x)/(r x*r y) := by field_simp
  rw [he, abs_div, abs_mul, abs_of_pos hx, abs_of_pos hy, abs_sub_comm]
  calc
    _ ≤ (D*|x-y|)/(c^2) := div_le_div₀ (by positivity) (hlip x y) (sq_pos_of_pos hc)
      (by simpa only [pow_two] using mul_le_mul (hr x) (hr y) hc.le hx.le)
    _ = _ := by ring

theorem square_div_lipschitz {f r : ℝ → ℝ} {M L c D : ℝ}
    (hM : 0 ≤ M) (hL : 0 ≤ L) (hc : 0 < c) (hD : 0 ≤ D)
    (hf : ∀ x, |f x| ≤ M) (hr : ∀ x, c ≤ r x)
    (hfl : ∀ x y, |f x-f y| ≤ L*|x-y|)
    (hrl : ∀ x y, |r x-r y| ≤ D*|x-y|) (x y : ℝ) :
    |(f x)^2/r x-(f y)^2/r y| ≤ (2*M*L/c+M^2*D/c^2)*|x-y| := by
  have hx := hc.trans_le (hr x)
  have hy := hc.trans_le (hr y)
  have hsq : |(f x)^2-(f y)^2| ≤ 2*M*L*|x-y| := by
    rw [show (f x)^2-(f y)^2 = (f x-f y)*(f x+f y) by ring, abs_mul]
    have hsum : |f x+f y| ≤ 2*M := (abs_add_le _ _).trans (by linarith [hf x, hf y])
    have hh := mul_le_mul (hfl x y) hsum (abs_nonneg _) (by positivity : 0 ≤ L*|x-y|)
    exact hh.trans_eq (by ring)
  have hi : |(r x)⁻¹| ≤ 1/c := by
    rw [abs_of_pos (inv_pos.mpr hx)]
    simpa only [one_div] using one_div_le_one_div_of_le hc (hr x)
  have hfy : |(f y)^2| ≤ M^2 := by rw [abs_pow]; gcongr; exact hf y
  have he : (f x)^2/r x-(f y)^2/r y =
      ((f x)^2-(f y)^2)*(r x)⁻¹+(f y)^2*((r x)⁻¹-(r y)⁻¹) := by ring
  rw [he]
  calc
    _ ≤ |((f x)^2-(f y)^2)*(r x)⁻¹|+|(f y)^2*((r x)⁻¹-(r y)⁻¹)| := abs_add_le _ _
    _ = |(f x)^2-(f y)^2| * |(r x)⁻¹|+|(f y)^2| * |(r x)⁻¹-(r y)⁻¹| := by rw [abs_mul, abs_mul]
    _ ≤ (2*M*L*|x-y|)*(1/c)+M^2*((D/c^2)*|x-y|) := add_le_add
      (mul_le_mul hsq hi (abs_nonneg _) (by positivity))
      (mul_le_mul hfy (inverse_lipschitz_bound hc hr hD hrl x y) (abs_nonneg _) (sq_nonneg M))
    _ = _ := by ring

theorem abs_projIcc_sub_le {l r : ℝ} (hlr : l ≤ r) (x y : ℝ) :
    |(projIcc l r hlr x : ℝ)-(projIcc l r hlr y : ℝ)| ≤ |x-y| := by
  simpa only [Subtype.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul] using
    (LipschitzWith.projIcc hlr).dist_le_mul x y

end TaoAdditive1132
end
end SourceErdos1132_Additive_WeightedLipschitz

/- Erdos1132.Shared.PoissonKernel -/
section SourceErdos1132_Shared_PoissonKernel
/- # The Poisson kernel and its mass

Main paper: shared analytic tools for §§2–6.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology NNReal

namespace TaoAdditive1132

def poissonKernel (h t : ℝ) : ℝ := h / (Real.pi * (t ^ 2 + h ^ 2))

theorem poissonKernel_pos {h : ℝ} (hh : 0 < h) (t : ℝ) : 0 < poissonKernel h t := by
  unfold poissonKernel
  positivity

theorem poissonKernel_neg (h t : ℝ) : poissonKernel h (-t) = poissonKernel h t := by
  simp [poissonKernel]

theorem continuous_poissonKernel {h : ℝ} (hh : 0 < h) : Continuous (poissonKernel h) := by
  unfold poissonKernel
  exact continuous_const.div (by fun_prop) (fun t => ne_of_gt (by positivity))

theorem poissonKernel_eq_cauchyPDF {h : ℝ} (hh : 0 ≤ h) :
    poissonKernel h = ProbabilityTheory.cauchyPDFReal 0 ⟨h, hh⟩ := by
  ext t
  change h / (Real.pi * (t ^ 2 + h ^ 2)) =
    Real.pi⁻¹ * h * ((t - 0) ^ 2 + h ^ 2)⁻¹
  simp only [sub_zero, div_eq_mul_inv, mul_inv_rev]
  ring

theorem integrable_poissonKernel {h : ℝ} (hh : 0 ≤ h) : Integrable (poissonKernel h) := by
  rw [poissonKernel_eq_cauchyPDF hh]
  exact ProbabilityTheory.integrable_cauchyPDFReal _

theorem integral_poissonKernel {h : ℝ} (hh : 0 < h) : ∫ t, poissonKernel h t = 1 := by
  rw [poissonKernel_eq_cauchyPDF hh.le]
  apply ProbabilityTheory.integral_cauchyPDFReal_eq_one 0
  change (⟨h, hh.le⟩ : ℝ≥0) ≠ 0
  intro he
  have he' := congrArg (fun a : ℝ≥0 => (a : ℝ)) he
  exact hh.ne' he'

theorem hasDerivAt_poissonPrimitive {h : ℝ} (hh : 0 < h) (x t : ℝ) :
    HasDerivAt (fun y => Real.arctan ((y - x) / h) / Real.pi) (poissonKernel h (t - x)) t := by
  convert! (((((hasDerivAt_id t).sub_const x).div_const h).arctan).div_const Real.pi) using 1
  unfold poissonKernel
  field_simp
  dsimp only [id_eq]
  ring

theorem intervalIntegral_poissonKernel {h : ℝ} (hh : 0 < h) (x a b : ℝ) :
    (∫ t in a..b, poissonKernel h (t - x)) =
      (Real.arctan ((b - x) / h) - Real.arctan ((a - x) / h)) / Real.pi := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_poissonPrimitive hh x t)
    (((continuous_poissonKernel hh).comp (continuous_id.sub continuous_const)).intervalIntegrable a b)]
  ring

theorem integral_poissonKernel_Icc {h : ℝ} (hh : 0 < h) {a b : ℝ} (hab : a ≤ b) :
    (∫ t in Set.Icc a b, poissonKernel h t) =
      (Real.arctan (b / h) - Real.arctan (a / h)) / Real.pi := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  simpa using intervalIntegral_poissonKernel hh 0 a b

theorem poissonKernel_centered_interval {h : ℝ} (hh : 0 < h) {K : ℝ} (hK : 0 ≤ K) :
    (∫ t in Set.Icc (-K * h) (K * h), poissonKernel h t) =
      2 / Real.pi * Real.arctan K := by
  rw [integral_poissonKernel_Icc hh (by nlinarith)]
  simp only [mul_div_cancel_right₀ _ hh.ne', Real.arctan_neg]
  ring

end TaoAdditive1132
end
end SourceErdos1132_Shared_PoissonKernel

/- Erdos1132.Shared.Cayley -/
section SourceErdos1132_Shared_Cayley
/- # Cayley coordinates and the Cauchy boundary integral

Main paper: shared analytic tools for §§2–6.
-/

noncomputable section

open MeasureTheory Filter Complex Metric Set
open scoped Topology

namespace TaoAdditive1132

def cayley (x h : ℝ) (w : ℂ) : ℂ := x + h * I * (1 + w) / (1 - w)

def inverseCayley (t : ℝ) : ℂ := ((t : ℂ) - I) / ((t : ℂ) + I)

theorem cayley_zero (x h : ℝ) : cayley x h 0 = (x : ℂ) + h * I := by
  simp [cayley]

theorem inverseCayley_denom_ne_zero (t : ℝ) : (t : ℂ) + I ≠ 0 := by
  intro he
  have := congrArg Complex.im he
  norm_num at this

theorem inverseCayley_ne_one (t : ℝ) : inverseCayley t ≠ 1 := by
  rw [inverseCayley, ne_eq, div_eq_one_iff_eq (inverseCayley_denom_ne_zero t)]
  intro he
  have := congrArg Complex.im he
  norm_num at this

theorem norm_inverseCayley (t : ℝ) : ‖inverseCayley t‖ = 1 := by
  rw [inverseCayley, norm_div]
  have hn : ‖(t : ℂ) - I‖ = ‖(t : ℂ) + I‖ := by
    convert! norm_conj ((t : ℂ) + I) using 1
    simp [sub_eq_add_neg]
  rw [hn, div_self (norm_ne_zero_iff.mpr (inverseCayley_denom_ne_zero t))]

theorem cayley_inverseCayley (x h t : ℝ) :
    cayley x h (inverseCayley t) = ((x + h * t : ℝ) : ℂ) := by
  unfold cayley inverseCayley
  push_cast
  field_simp [inverseCayley_denom_ne_zero t]
  ring

theorem cayley_im (x h : ℝ) {w : ℂ} :
    (cayley x h w).im = h * (1 - ‖w‖ ^ 2) / normSq (1 - w) := by
  simp [cayley, div_im, normSq_apply, Complex.sq_norm]
  ring

theorem cayley_im_pos (x : ℝ) {h : ℝ} (hh : 0 < h) {w : ℂ} (hw : ‖w‖ < 1) :
    0 < (cayley x h w).im := by
  rw [cayley_im]
  have hn : 0 < 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  have hw1 : 1 - w ≠ 0 := by
    intro he
    have : w = 1 := (sub_eq_zero.mp he).symm
    simp [this] at hw
  exact div_pos (mul_pos hh hn) (normSq_pos.mpr hw1)

theorem analyticAt_cayley (x h : ℝ) {w : ℂ} (hw : w ≠ 1) :
    AnalyticAt ℂ (cayley x h) w := by
  unfold cayley
  fun_prop (disch := exact sub_ne_zero.mpr hw.symm)

theorem continuous_inverseCayley : Continuous inverseCayley := by
  unfold inverseCayley
  exact (continuous_ofReal.sub continuous_const).div
    (continuous_ofReal.add continuous_const) inverseCayley_denom_ne_zero

theorem cayley_radial_tendsto (x h t : ℝ) {r : ℕ → ℝ}
    (hr : Tendsto r atTop (𝓝 1)) :
    Tendsto (fun n => cayley x h ((r n : ℂ) * inverseCayley t)) atTop
      (𝓝 ((x + h * t : ℝ) : ℂ)) := by
  have hc := (analyticAt_cayley x h (inverseCayley_ne_one t)).continuousAt
  have ht : Tendsto (fun n => (r n : ℂ) * inverseCayley t) atTop
      (𝓝 (inverseCayley t)) := by simpa using (continuous_ofReal.tendsto 1 |>.comp hr).mul_const (inverseCayley t)
  simpa only [cayley_inverseCayley, Function.comp_def] using hc.tendsto.comp ht

def cayleyAngle (t : ℝ) : ℝ := 2 * Real.arctan t + Real.pi

theorem hasDerivAt_cayleyAngle (t : ℝ) :
    HasDerivAt cayleyAngle (2 / (1 + t ^ 2)) t := by
  convert! ((Real.hasDerivAt_arctan t).const_mul 2).add_const Real.pi using 1
  simp [div_eq_mul_inv]

theorem injective_cayleyAngle : Function.Injective cayleyAngle := by
  intro x y h
  apply Real.arctan_injective
  dsimp [cayleyAngle] at h
  linarith

theorem range_cayleyAngle : range cayleyAngle = Ioo 0 (2 * Real.pi) := by
  ext θ
  constructor
  · rintro ⟨t, rfl⟩
    have ht := Real.arctan_mem_Ioo t
    dsimp [cayleyAngle]
    constructor <;> linarith [ht.1, ht.2]
  · intro hθ
    refine ⟨Real.tan ((θ - Real.pi) / 2), ?_⟩
    dsimp [cayleyAngle]
    rw [Real.arctan_tan (by linarith [hθ.1]) (by linarith [hθ.2])]
    ring

theorem circleMap_cayleyAngle (t : ℝ) :
    circleMap 0 1 (cayleyAngle t) = inverseCayley t := by
  have hs : Real.sqrt (1 + t ^ 2) ^ 2 = 1 + t ^ 2 := Real.sq_sqrt (by positivity)
  have hs0 : Real.sqrt (1 + t ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  have hc (θ : ℝ) : circleMap 0 1 θ = ⟨Real.cos θ, Real.sin θ⟩ := by
    apply Complex.ext <;> simp [circleMap, Complex.exp_re, Complex.exp_im]
  rw [hc]
  apply Complex.ext <;> simp [cayleyAngle, inverseCayley,
    Complex.div_re, Complex.div_im, Complex.normSq_apply, Real.cos_add_pi,
    Real.sin_add_pi, Real.cos_two_mul, Real.sin_two_mul,
    Real.cos_arctan, Real.sin_arctan]
  · field_simp
    rw [hs]
    ring
  · field_simp
    rw [hs]
    ring

theorem circleMap_cayleyAngle_radius (r t : ℝ) :
    circleMap 0 r (cayleyAngle t) = (r : ℂ) * inverseCayley t := by
  rw [← circleMap_cayleyAngle t]
  simp [circleMap]

/-- Stereographic parametrization expresses a circle mean as a Cauchy integral. -/
theorem circleAverage_eq_cauchy_integral (f : ℂ → ℝ) (r : ℝ) :
    Real.circleAverage f 0 r = ∫ t, poissonKernel 1 t * f ((r : ℂ) * inverseCayley t) := by
  have hpos (t : ℝ) : 0 < 2 / (1 + t ^ 2) := by positivity
  have h := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun t _ => (hasDerivAt_cayleyAngle t).hasDerivWithinAt) injective_cayleyAngle.injOn
    (fun θ => f (circleMap 0 r θ))
  simp only [image_univ, range_cayleyAngle, Measure.restrict_univ, smul_eq_mul,
    abs_of_pos (hpos _)] at h
  rw [Real.circleAverage_def, smul_eq_mul,
    intervalIntegral.integral_of_le (show 0 ≤ 2 * Real.pi by positivity),
    integral_Ioc_eq_integral_Ioo, h, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  rw [circleMap_cayleyAngle_radius]
  unfold poissonKernel
  field_simp
  ring

open InnerProductSpace in
/-- Boundary limits of a bounded harmonic function in stereographic coordinates. -/
theorem harmonic_boundary_cauchy {u : ℂ → ℝ} {M : ℝ}
    (hu : HarmonicOnNhd u (ball 0 1))
    (hb : ∀ z ∈ ball (0 : ℂ) 1, |u z| ≤ M)
    (r : ℕ → ℝ) (hr : ∀ n, r n ∈ Ico 0 1) (b : ℝ → ℝ)
    (hl : ∀ᵐ t, Tendsto (fun n => u ((r n : ℂ) * inverseCayley t)) atTop (𝓝 (b t))) :
    (∫ t, poissonKernel 1 t * b t) = u 0 := by
  have hm (n : ℕ) (t : ℝ) : (r n : ℂ) * inverseCayley t ∈ ball (0 : ℂ) 1 := by
    simp [mem_ball, dist_eq_norm, norm_inverseCayley,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hr n).1, (hr n).2]
  have hcont (n : ℕ) : Continuous (fun t => u ((r n : ℂ) * inverseCayley t)) :=
    hu.contDiffOn.continuousOn.comp_continuous
      (continuous_const.mul continuous_inverseCayley) (hm n)
  have ht := tendsto_integral_of_dominated_convergence (μ := volume)
    (F := fun n t => poissonKernel 1 t * u ((r n : ℂ) * inverseCayley t))
    (f := fun t => poissonKernel 1 t * b t)
    (fun t => poissonKernel 1 t * M)
    (fun n => ((continuous_poissonKernel (h := 1) (by norm_num)).mul (hcont n)).aestronglyMeasurable)
    ((integrable_poissonKernel (by norm_num : (0 : ℝ) ≤ 1)).mul_const M)
    (fun n => ae_of_all _ fun t => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (poissonKernel_pos (by norm_num) t)]
      exact mul_le_mul_of_nonneg_left (hb _ (hm n t)) (poissonKernel_pos (by norm_num) t).le)
    (by filter_upwards [hl] with t ht; exact tendsto_const_nhds.mul ht)
  have hav (n : ℕ) : (∫ t, poissonKernel 1 t * u ((r n : ℂ) * inverseCayley t)) = u 0 := by
    rw [← circleAverage_eq_cauchy_integral]
    apply InnerProductSpace.HarmonicOnNhd.circleAverage_eq
    apply hu.mono
    apply closedBall_subset_ball
    rw [abs_of_nonneg (hr n).1]
    exact (hr n).2
  have he : (fun n => ∫ t, poissonKernel 1 t * u ((r n : ℂ) * inverseCayley t)) =
      fun _ => u 0 := funext hav
  rw [he] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

end TaoAdditive1132
end
end SourceErdos1132_Shared_Cayley

/- Erdos1132.Interpolation -/
section SourceErdos1132_Interpolation
/- # Interpolation nodes, cardinal polynomials, and Lebesgue functions

Both manuscripts: §1, interpolation nodes and Lebesgue functions.
-/

noncomputable section

open scoped BigOperators
open Polynomial Finset

namespace TaoAdditive1132

/-- A row of distinct interpolation nodes in `[-1, 1]`. -/
structure Nodes (n : ℕ) where
  point : Fin n → ℝ
  injective : Function.Injective point
  mem_interval : ∀ i, point i ∈ Set.Icc (-1) 1

namespace Nodes

variable {n : ℕ} (X : Nodes n)

def cardinal (i : Fin n) : ℝ[X] := Lagrange.basis univ X.point i

def lebesgue (x : ℝ) : ℝ := ∑ i, |(X.cardinal i).eval x|

def nodePolynomial : ℝ[X] := Lagrange.nodal univ X.point

def weight (i : Fin n) : ℝ := Lagrange.nodalWeight univ X.point i

def totalWeight : ℝ := ∑ i, |X.weight i|

def mass (i : Fin n) : ℝ := |X.weight i| / X.totalWeight

def signedMass (i : Fin n) : ℝ := X.weight i / X.totalWeight

theorem weight_ne_zero (i : Fin n) : X.weight i ≠ 0 :=
  Lagrange.nodalWeight_ne_zero X.injective.injOn (mem_univ i)

theorem weight_eq_derivative (i : Fin n) :
    X.weight i = ((X.nodePolynomial.derivative).eval (X.point i))⁻¹ :=
  Lagrange.nodalWeight_eq_eval_derivative_nodal (mem_univ i)

theorem totalWeight_pos (hn : 0 < n) : 0 < X.totalWeight := by
  apply sum_pos'
  · intro i _
    exact abs_nonneg _
  · exact ⟨⟨0, hn⟩, mem_univ _, abs_pos.mpr (X.weight_ne_zero _)⟩

theorem mass_pos (hn : 0 < n) (i : Fin n) : 0 < X.mass i :=
  div_pos (abs_pos.mpr (X.weight_ne_zero i)) (X.totalWeight_pos hn)

theorem sum_mass (hn : 0 < n) : ∑ i, X.mass i = 1 := by
  simp only [mass, ← sum_div]
  change X.totalWeight / X.totalWeight = 1
  exact div_self (ne_of_gt (X.totalWeight_pos hn))

theorem abs_signedMass (hn : 0 < n) (i : Fin n) :
    |X.signedMass i| = X.mass i := by
  rw [signedMass, mass, abs_div, abs_of_pos (X.totalWeight_pos hn)]

theorem cardinal_at_node (i j : Fin n) :
    (X.cardinal i).eval (X.point j) = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst j
    simp [cardinal, Lagrange.eval_basis_self X.injective.injOn]
  · simp [cardinal, h, Lagrange.eval_basis_of_ne h]

theorem lebesgue_at_node (j : Fin n) : X.lebesgue (X.point j) = 1 := by
  simp only [lebesgue, X.cardinal_at_node, apply_ite abs, abs_one, abs_zero]
  simp

theorem lebesgue_nonneg (x : ℝ) : 0 ≤ X.lebesgue x :=
  sum_nonneg fun _ _ => abs_nonneg _

theorem continuous_lebesgue : Continuous X.lebesgue := by
  unfold lebesgue
  fun_prop

theorem measurable_lebesgue : Measurable X.lebesgue :=
  X.continuous_lebesgue.measurable

/-- The signed barycentric weights annihilate polynomials of degree below `n - 1`. -/
theorem weight_cancellation {p : ℝ[X]} (hp : p.degree < (n - 1 : ℕ)) :
    ∑ i, X.weight i * p.eval (X.point i) = 0 := by
  have hpn : p.degree < (n : ℕ) :=
    hp.trans_le (by exact_mod_cast Nat.sub_le n 1)
  have h := Lagrange.coeff_eq_sum X.injective.injOn (s := univ) (P := p)
    (by simpa using hpn)
  have hc : p.coeff (n - 1) = 0 := Polynomial.coeff_eq_zero_of_degree_lt hp
  simp only [card_univ, Fintype.card_fin, hc] at h
  apply Eq.trans ?_ h.symm
  apply sum_congr rfl
  intro i _
  simp [weight, Lagrange.nodalWeight, prod_inv_distrib, div_eq_mul_inv, mul_comm]

theorem signedMass_cancellation {p : ℝ[X]} (hp : p.degree < (n - 1 : ℕ)) :
    ∑ i, X.signedMass i * p.eval (X.point i) = 0 := by
  simp only [signedMass, div_mul_eq_mul_div, ← sum_div, X.weight_cancellation hp, zero_div]

theorem sum_signedMass (hn : 2 ≤ n) : ∑ i, X.signedMass i = 0 := by
  simpa using X.signedMass_cancellation (p := 1)
    (by simp only [degree_one]; exact_mod_cast (show 0 < n - 1 by omega))

theorem split_mass_nonneg (hn : 0 < n) (i : Fin n) :
    0 ≤ X.mass i + X.signedMass i ∧ 0 ≤ X.mass i - X.signedMass i := by
  have h := abs_le.mp (le_of_eq (X.abs_signedMass hn i))
  constructor <;> linarith

theorem sum_split_mass (hn : 2 ≤ n) :
    (∑ i, (X.mass i + X.signedMass i)) = 1 ∧
    (∑ i, (X.mass i - X.signedMass i)) = 1 := by
  simp [sum_add_distrib, sum_sub_distrib, X.sum_mass (by omega), X.sum_signedMass hn]

end Nodes

end TaoAdditive1132
end
end SourceErdos1132_Interpolation

/- Erdos1132.Shared.Cauchy -/
section SourceErdos1132_Shared_Cauchy
/- # Positive and signed Cauchy transforms of the node weights

Main paper: shared analytic tools for §§2–6.
-/

noncomputable section

open scoped BigOperators
open Finset

namespace TaoAdditive1132

/-- A finite positive measure of total mass one. -/
structure AtomicProbability (n : ℕ) where
  point : Fin n → ℝ
  mass : Fin n → ℝ
  mass_nonneg : ∀ i, 0 ≤ mass i
  sum_mass : ∑ i, mass i = 1

namespace AtomicProbability

variable {n : ℕ} (μ : AtomicProbability n)

def cauchy (z : ℂ) : ℂ := ∑ i, (μ.mass i : ℂ) / (z - μ.point i)

def boundary (x : ℝ) : ℝ := ∑ i, μ.mass i / (x - μ.point i)

def gamma (h x : ℝ) : ℝ := ∑ i, μ.mass i * h / ((x - μ.point i) ^ 2 + h ^ 2)

theorem exists_mass_pos : ∃ i, 0 < μ.mass i := by
  by_contra! h
  have hs := sum_nonpos (s := univ) (fun i _ => h i)
  rw [μ.sum_mass] at hs
  norm_num at hs

theorem gamma_pos {h : ℝ} (hh : 0 < h) (x : ℝ) : 0 < μ.gamma h x := by
  obtain ⟨i, hi⟩ := μ.exists_mass_pos
  refine sum_pos' (fun j _ => div_nonneg (mul_nonneg (μ.mass_nonneg j) hh.le)
    (by positivity)) ⟨i, mem_univ _, ?_⟩
  exact div_pos (mul_pos hi hh) (by positivity)

theorem cauchy_ofReal (x : ℝ) : μ.cauchy x = (μ.boundary x : ℂ) := by
  simp [cauchy, boundary]

theorem neg_im_cauchy (h x : ℝ) :
    -(μ.cauchy ((x : ℂ) + h * Complex.I)).im = μ.gamma h x := by
  simp only [cauchy, Complex.im_sum, ← sum_neg_distrib, gamma]
  apply sum_congr rfl
  intro i _
  simp [Complex.div_im, Complex.normSq_apply, pow_two]

theorem gamma_lower {h x : ℝ} (hh : 0 < h)
    (hx : x ∈ Set.Icc (-1) 1) (hs : ∀ i, μ.point i ∈ Set.Icc (-1) 1) :
    h / (4 + h ^ 2) ≤ μ.gamma h x := by
  calc
    h / (4 + h ^ 2) = ∑ i, μ.mass i * (h / (4 + h ^ 2)) := by
      rw [← sum_mul, μ.sum_mass, one_mul]
    _ ≤ μ.gamma h x := by
      apply sum_le_sum
      intro i _
      have hi := hs i
      have hsq : (x - μ.point i) ^ 2 ≤ 4 := by
        have h₁ : 0 ≤ 2 - (x - μ.point i) := by linarith [hx.2, hi.1]
        have h₂ : 0 ≤ 2 + (x - μ.point i) := by linarith [hx.1, hi.2]
        nlinarith [mul_nonneg h₁ h₂]
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_left (mul_nonneg (μ.mass_nonneg i) hh.le)
        (by positivity) (by linarith)

end AtomicProbability

namespace Nodes

variable {n : ℕ} (X : Nodes n)

def probability (hn : 0 < n) : AtomicProbability n where
  point := X.point
  mass := X.mass
  mass_nonneg i := (X.mass_pos hn i).le
  sum_mass := X.sum_mass hn

def plusProbability (hn : 2 ≤ n) : AtomicProbability n where
  point := X.point
  mass i := X.mass i + X.signedMass i
  mass_nonneg i := (X.split_mass_nonneg (by omega) i).1
  sum_mass := (X.sum_split_mass hn).1

def minusProbability (hn : 2 ≤ n) : AtomicProbability n where
  point := X.point
  mass i := X.mass i - X.signedMass i
  mass_nonneg i := (X.split_mass_nonneg (by omega) i).2
  sum_mass := (X.sum_split_mass hn).2

def signedCauchy (z : ℂ) : ℂ := ∑ i, (X.signedMass i : ℂ) / (z - X.point i)

def signedBoundary (x : ℝ) : ℝ := ∑ i, X.signedMass i / (x - X.point i)

def absoluteTransform (x : ℝ) : ℝ := ∑ i, X.mass i / |x - X.point i|

theorem cauchy_plus (hn : 2 ≤ n) (z : ℂ) :
    (X.plusProbability hn).cauchy z =
      (X.probability (by omega)).cauchy z + X.signedCauchy z := by
  simp [AtomicProbability.cauchy, plusProbability, probability, signedCauchy,
    add_div, sum_add_distrib]

theorem cauchy_minus (hn : 2 ≤ n) (z : ℂ) :
    (X.minusProbability hn).cauchy z =
      (X.probability (by omega)).cauchy z - X.signedCauchy z := by
  simp [AtomicProbability.cauchy, minusProbability, probability, signedCauchy,
    sub_div, sum_sub_distrib]

theorem nodePolynomial_ne_zero {x : ℝ} (hx : ∀ i, x ≠ X.point i) :
    X.nodePolynomial.eval x ≠ 0 :=
  Lagrange.eval_nodal_not_at_node (fun i _ => hx i)

theorem signedBoundary_eq (hn : 0 < n) {x : ℝ} (hx : ∀ i, x ≠ X.point i) :
    X.signedBoundary x = 1 / (X.totalWeight * X.nodePolynomial.eval x) := by
  have hs : (univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, mem_univ _⟩
  have h := Lagrange.eval_interpolate_not_at_node (1 : Fin n → ℝ)
    (s := univ) (v := X.point) (fun i _ => hx i)
  simp only [Lagrange.interpolate_one X.injective.injOn hs, Polynomial.eval_one,
    Pi.one_apply, mul_one] at h
  have hp := X.nodePolynomial_ne_zero hx
  have hw := ne_of_gt (X.totalWeight_pos hn)
  have hg : ∑ i, X.weight i / (x - X.point i) = (X.nodePolynomial.eval x)⁻¹ := by
    rw [← one_div, eq_div_iff hp]
    simpa [nodePolynomial, weight, div_eq_mul_inv, mul_comm] using h.symm
  simp only [signedBoundary, signedMass, div_right_comm (X.weight _) X.totalWeight,
    ← sum_div, hg]
  field_simp

theorem lebesgue_transform (hn : 0 < n) {x : ℝ} (hx : ∀ i, x ≠ X.point i) :
    X.lebesgue x = X.absoluteTransform x / |X.signedBoundary x| := by
  have hp := X.nodePolynomial_ne_zero hx
  have hw := ne_of_gt (X.totalWeight_pos hn)
  have hb : X.lebesgue x = |X.nodePolynomial.eval x| * X.totalWeight *
      X.absoluteTransform x := by
    simp only [lebesgue, absoluteTransform, mul_sum]
    apply sum_congr rfl
    intro i _
    rw [cardinal, Lagrange.eval_basis_not_at_node (mem_univ _) (hx i)]
    simp only [abs_mul, abs_inv, mass, nodePolynomial, weight]
    field_simp
  rw [hb, X.signedBoundary_eq hn hx, abs_div, abs_one, abs_mul,
    abs_of_pos (X.totalWeight_pos hn)]
  field_simp

end Nodes

end TaoAdditive1132
end
end SourceErdos1132_Shared_Cauchy

/- Erdos1132.Shared.IntervalHarmonic -/
section SourceErdos1132_Shared_IntervalHarmonic
/- # Harmonic measure of a boundary interval

Main paper: shared analytic tools for §§2–6.
-/

noncomputable section

open Complex Filter InnerProductSpace
open scoped Topology

namespace TaoAdditive1132

def intervalHarmonic (a b : ℝ) (z : ℂ) : ℝ := ((z - a) / (z - b)).arg / Real.pi

theorem interval_quotient_im (a b : ℝ) (z : ℂ) :
    ((z - a) / (z - b)).im = (a - b) * z.im / normSq (z - b) := by
  simp [div_im]
  ring

theorem interval_quotient_im_pos {a b : ℝ} (hab : a < b) {z : ℂ} (hz : z.im < 0) :
    0 < ((z - a) / (z - b)).im := by
  rw [interval_quotient_im]
  have hzb : z - (b : ℂ) ≠ 0 := by
    intro he
    have := congrArg Complex.im he
    simp at this
    linarith
  exact div_pos (mul_pos_of_neg_of_neg (sub_neg.mpr hab) hz) (normSq_pos.mpr hzb)

theorem abs_intervalHarmonic_le_one (a b : ℝ) (z : ℂ) : |intervalHarmonic a b z| ≤ 1 := by
  rw [intervalHarmonic, abs_div, abs_of_pos Real.pi_pos]
  exact (div_le_one Real.pi_pos).mpr (abs_arg_le_pi _)

theorem harmonicAt_intervalHarmonic_comp {F : ℂ → ℂ} {z : ℂ} {a b : ℝ}
    (hab : a < b) (hF : AnalyticAt ℂ F z) (hi : (F z).im < 0) :
    HarmonicAt (fun w => intervalHarmonic a b (F w)) z := by
  have hn : F z - (b : ℂ) ≠ 0 := by
    intro he
    have := congrArg Complex.im he
    simp at this
    linarith
  have hq : AnalyticAt ℂ (fun w => (F w - a) / (F w - b)) z := by
    fun_prop (disch := exact hn)
  have hs : (F z - a) / (F z - b) ∈ slitPlane :=
    Or.inr (ne_of_gt (interval_quotient_im_pos hab hi))
  have hh := (hq.clog hs).harmonicAt_im
  convert! hh.const_smul (c := Real.pi⁻¹) using 1
  funext w
  simp [intervalHarmonic, Complex.log_im, div_eq_mul_inv, mul_comm]

theorem tendsto_intervalHarmonic_real {a b t : ℝ} (hab : a < b)
    (hta : t ≠ a) (htb : t ≠ b) {f : ℕ → ℂ}
    (hf : Tendsto f atTop (𝓝 (t : ℂ))) (hi : ∀ n, (f n).im < 0) :
    Tendsto (fun n => intervalHarmonic a b (f n)) atTop
      (𝓝 (if a < t ∧ t < b then 1 else 0)) := by
  have hq := (hf.sub_const (a : ℂ)).div (hf.sub_const (b : ℂ))
    (by exact_mod_cast sub_ne_zero.mpr htb)
  have hq' : Tendsto (fun n => (f n - a) / (f n - b)) atTop
      (𝓝 (((t - a) / (t - b) : ℝ) : ℂ)) := by
    convert! hq using 1
    simp
  by_cases ht : a < t ∧ t < b
  · have hneg : (t - a) / (t - b) < 0 :=
      div_neg_of_pos_of_neg (sub_pos.mpr ht.1) (sub_neg.mpr ht.2)
    have hwithin : Tendsto (fun n => (f n - a) / (f n - b)) atTop
        (𝓝[{z : ℂ | 0 ≤ z.im}] (((t - a) / (t - b) : ℝ) : ℂ)) := by
      apply tendsto_nhdsWithin_iff.mpr
      exact ⟨hq', .of_forall fun n => (interval_quotient_im_pos hab (hi n)).le⟩
    have harg := (tendsto_arg_nhdsWithin_im_nonneg_of_re_neg_of_im_zero hneg rfl).comp hwithin
    simpa [intervalHarmonic, ht, Real.pi_ne_zero] using harg.div_const Real.pi
  · have hpos : 0 < (t - a) / (t - b) := by
      by_cases h : t < a
      · exact div_pos_of_neg_of_neg (sub_neg.mpr h) (sub_neg.mpr (h.trans hab))
      · have h₁ : a < t := lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hta)
        have h₂ : b < t := lt_of_le_of_ne (not_lt.mp (fun h' => ht ⟨h₁, h'⟩)) (Ne.symm htb)
        exact div_pos (sub_pos.mpr h₁) (sub_pos.mpr h₂)
    have harg := (continuousAt_arg (Or.inl hpos)).tendsto.comp hq'
    simpa only [intervalHarmonic, if_neg ht, ← Complex.ofReal_sub, ← Complex.ofReal_div,
      arg_ofReal_of_nonneg hpos.le, zero_div, Function.comp_def] using harg.div_const Real.pi

namespace AtomicProbability

variable {n : ℕ} (μ : AtomicProbability n)

theorem cauchy_im_neg {z : ℂ} (hz : 0 < z.im) : (μ.cauchy z).im < 0 := by
  have h := μ.neg_im_cauchy z.im z.re
  rw [Complex.re_add_im] at h
  linarith [μ.gamma_pos hz z.re]

theorem analyticAt_cauchy {z : ℂ} (hz : ∀ i, z ≠ (μ.point i : ℂ)) :
    AnalyticAt ℂ μ.cauchy z := by
  unfold cauchy
  fun_prop (disch := exact sub_ne_zero.mpr (hz _))

theorem analyticAt_cauchy_upper {z : ℂ} (hz : 0 < z.im) : AnalyticAt ℂ μ.cauchy z := by
  apply μ.analyticAt_cauchy
  intro i hi
  simp [hi] at hz

end AtomicProbability

end TaoAdditive1132
end
end SourceErdos1132_Shared_IntervalHarmonic

/- Erdos1132.Shared.CauchyRational -/
section SourceErdos1132_Shared_CauchyRational
/- # Rational formulas and boundary limits for Cauchy transforms

Main paper: shared analytic tools for §§2–6.
-/

noncomputable section

open scoped BigOperators
open Polynomial Finset Complex Set

namespace TaoAdditive1132.AtomicProbability

variable {n : ℕ} (μ : AtomicProbability n)

def denominator : ℂ[X] := Lagrange.nodal univ (fun i => (μ.point i : ℂ))

def numerator : ℂ[X] :=
  ∑ i, C (μ.mass i : ℂ) * Lagrange.nodal (univ.erase i) (fun j => (μ.point j : ℂ))

theorem denominator_eval_ne_zero {z : ℂ} (hz : ∀ i, z ≠ (μ.point i : ℂ)) :
    μ.denominator.eval z ≠ 0 :=
  Lagrange.eval_nodal_not_at_node (fun i _ => hz i)

theorem numerator_eval {z : ℂ} (hz : ∀ i, z ≠ (μ.point i : ℂ)) :
    μ.numerator.eval z = μ.denominator.eval z * μ.cauchy z := by
  simp only [numerator, eval_finsetSum, eval_mul, eval_C, cauchy, mul_sum]
  apply sum_congr rfl
  intro i _
  have h := congrArg (Polynomial.eval z)
    (Lagrange.nodal_eq_mul_nodal_erase (v := fun j => (μ.point j : ℂ)) (mem_univ i))
  simp only [eval_mul, eval_sub, eval_X, eval_C] at h
  have hzi := sub_ne_zero.mpr (hz i)
  apply (mul_right_cancel₀ hzi)
  rw [mul_assoc _ (_ / _) _, div_mul_cancel₀ _ hzi]
  dsimp [denominator]
  linear_combination -(μ.mass i : ℂ) * h

theorem finite_boundary_fiber (v : ℝ) : {t : ℝ | μ.boundary t = v}.Finite := by
  let q : ℂ[X] := C (v : ℂ) * μ.denominator - μ.numerator
  have heval {z : ℂ} (hz : ∀ i, z ≠ (μ.point i : ℂ)) :
      q.eval z = μ.denominator.eval z * ((v : ℂ) - μ.cauchy z) := by
    simp only [q, eval_sub, eval_mul, eval_C, μ.numerator_eval hz]
    ring
  have hI (i : Fin n) : I ≠ (μ.point i : ℂ) := by
    intro hi
    have := congrArg Complex.im hi
    norm_num at this
  have hq : q ≠ 0 := by
    intro hq
    have h := heval hI
    rw [hq, eval_zero] at h
    have hc : (v : ℂ) = μ.cauchy I := sub_eq_zero.mp
      ((mul_eq_zero.mp h.symm).resolve_left (μ.denominator_eval_ne_zero hI))
    have hi := μ.cauchy_im_neg (z := I) (by simp)
    rw [← hc] at hi
    simp at hi
  have hf : {t : ℝ | q.IsRoot (t : ℂ)}.Finite :=
    Set.Finite.preimage Complex.ofReal_injective.injOn (Polynomial.finite_setOfPred_isRoot hq)
  apply ((Set.finite_range μ.point).union hf).subset
  intro t ht
  by_cases hnode : t ∈ range μ.point
  · exact Or.inl hnode
  · right
    have htn (i : Fin n) : (t : ℂ) ≠ (μ.point i : ℂ) := by
      intro hi
      exact hnode ⟨i, (Complex.ofReal_injective hi).symm⟩
    change q.eval (t : ℂ) = 0
    rw [heval htn, μ.cauchy_ofReal t, ht, sub_self, mul_zero]

theorem ae_regular_boundary_comp (a b : ℝ) {g : ℝ → ℝ} (hg : Function.Injective g) :
    ∀ᵐ t, (∀ i, g t ≠ μ.point i) ∧ μ.boundary (g t) ≠ a ∧ μ.boundary (g t) ≠ b := by
  have hfinite : (range μ.point ∪ {t | μ.boundary t = a} ∪ {t | μ.boundary t = b}).Finite :=
    ((Set.finite_range μ.point).union (μ.finite_boundary_fiber a)).union (μ.finite_boundary_fiber b)
  have hnull := (Set.Finite.preimage hg.injOn hfinite).measure_zero (μ := MeasureTheory.volume)
  have hae : ∀ᵐ t, t ∉ g ⁻¹' (range μ.point ∪ {t | μ.boundary t = a} ∪ {t | μ.boundary t = b}) := by
    apply MeasureTheory.ae_iff.mpr
    simpa only [not_not, Set.ofPred_mem_eq] using hnull
  filter_upwards [hae] with t ht
  simp only [Set.mem_preimage, Set.mem_union, Set.mem_ofPred_eq, not_or] at ht
  exact ⟨fun i hi => ht.1.1 ⟨i, hi.symm⟩, ht.1.2, ht.2⟩

end TaoAdditive1132.AtomicProbability
end
end SourceErdos1132_Shared_CauchyRational

/- Erdos1132.Shared.BoundaryMeasure -/
section SourceErdos1132_Shared_BoundaryMeasure
/- # The boundary harmonic-measure identity

Main paper: shared analytic tools for §§2–6.
-/

noncomputable section

open MeasureTheory Filter InnerProductSpace Metric Set Complex
open scoped Topology

namespace TaoAdditive1132

def radialRadius (j : ℕ) : ℝ := 1 - 1 / ((j : ℝ) + 1)

theorem radialRadius_mem (j : ℕ) : radialRadius j ∈ Ico 0 1 := by
  have hp : 0 < (j : ℝ) + 1 := by positivity
  have hd : 1 / ((j : ℝ) + 1) ≤ 1 := (div_le_one hp).mpr
    (by linarith [Nat.cast_nonneg j (α := ℝ)])
  have hd' : 0 < 1 / ((j : ℝ) + 1) := by positivity
  dsimp [radialRadius]
  constructor <;> linarith

theorem tendsto_radialRadius : Tendsto radialRadius atTop (𝓝 1) := by
  have hc : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  convert! hc.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) using 1
  norm_num

theorem poisson_integral_affine {h : ℝ} (hh : 0 < h) (x : ℝ) (f : ℝ → ℝ) :
    (∫ y, poissonKernel h (y - x) * f y) =
      ∫ t, poissonKernel 1 t * f (x + h * t) := by
  have hi : Function.Injective (fun t : ℝ => x + h * t) := by
    intro s t hst
    exact (mul_left_cancel₀ hh.ne') (add_left_cancel hst)
  have hs : Function.Surjective (fun t : ℝ => x + h * t) := by
    intro y
    refine ⟨(y - x) / h, ?_⟩
    field_simp
    ring
  have hd (t : ℝ) : HasDerivAt (fun t => x + h * t) h t := by
    convert! ((hasDerivAt_id t).const_mul h).const_add x using 1
    simp
  have he := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun t _ => (hd t).hasDerivWithinAt) hi.injOn
    (fun y => poissonKernel h (y - x) * f y)
  simp only [image_univ, hs.range_eq, Measure.restrict_univ, abs_of_pos hh,
    smul_eq_mul] at he
  rw [he]
  apply integral_congr_ae
  filter_upwards with t
  unfold poissonKernel
  field_simp
  ring

namespace AtomicProbability

variable {n : ℕ} (μ : AtomicProbability n)

theorem boundary_measure_stereographic {a b h : ℝ} (hab : a < b) (hh : 0 < h) (x : ℝ) :
    (∫ t, poissonKernel 1 t *
      (if a < μ.boundary (x + h * t) ∧ μ.boundary (x + h * t) < b then 1 else 0)) =
      intervalHarmonic a b (μ.cauchy ((x : ℂ) + h * I)) := by
  let u : ℂ → ℝ := fun w => intervalHarmonic a b (μ.cauchy (cayley x h w))
  have hu : HarmonicOnNhd u (ball 0 1) := by
    intro w hw
    have hwn : ‖w‖ < 1 := by simpa [mem_ball, dist_eq_norm] using hw
    have hc : 0 < (cayley x h w).im := cayley_im_pos x hh hwn
    have hw1 : w ≠ 1 := by intro he; simp [he] at hwn
    exact harmonicAt_intervalHarmonic_comp hab
      ((μ.analyticAt_cauchy_upper hc).comp (f := cayley x h) (analyticAt_cayley x h hw1))
      (μ.cauchy_im_neg hc)
  let r := radialRadius
  have hr := radialRadius_mem
  have hrt := tendsto_radialRadius
  have hinj : Function.Injective (fun t : ℝ => x + h * t) := by
    intro s t hst
    exact (mul_left_cancel₀ hh.ne') (add_left_cancel hst)
  have hl : ∀ᵐ t, Tendsto (fun j => u ((r j : ℂ) * inverseCayley t)) atTop
      (𝓝 (if a < μ.boundary (x + h * t) ∧ μ.boundary (x + h * t) < b then 1 else 0)) := by
    filter_upwards [μ.ae_regular_boundary_comp a b hinj] with t ht
    have hc := (μ.analyticAt_cauchy (z := ((x + h * t : ℝ) : ℂ))
      (fun i hi => ht.1 i (Complex.ofReal_injective hi))).continuousAt
    have hlim := hc.tendsto.comp (cayley_radial_tendsto x h t hrt)
    rw [μ.cauchy_ofReal] at hlim
    apply tendsto_intervalHarmonic_real hab ht.2.1 ht.2.2 hlim
    intro j
    apply μ.cauchy_im_neg
    apply cayley_im_pos x hh
    simpa [norm_inverseCayley, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hr j).1] using (hr j).2
  have he := harmonic_boundary_cauchy hu (fun w _ => abs_intervalHarmonic_le_one a b _)
    r hr _ hl
  simpa only [u, cayley_zero] using he

/-- Boundary harmonic measure for a finite positive Cauchy transform. -/
theorem boundary_harmonic_measure {a b h : ℝ} (hab : a < b) (hh : 0 < h) (x : ℝ) :
    (∫ y, poissonKernel h (x - y) *
      (if a < μ.boundary y ∧ μ.boundary y < b then 1 else 0)) =
      intervalHarmonic a b (μ.cauchy ((x : ℂ) + h * I)) := by
  rw [← μ.boundary_measure_stereographic hab hh x,
    ← poisson_integral_affine hh x (fun y => if a < μ.boundary y ∧ μ.boundary y < b then 1 else 0)]
  apply integral_congr_ae
  filter_upwards with y
  rw [show x - y = -(y - x) by ring, poissonKernel_neg]

end AtomicProbability

end TaoAdditive1132
end
end SourceErdos1132_Shared_BoundaryMeasure

/- Erdos1132.Shared.PoissonSemigroup -/
section SourceErdos1132_Shared_PoissonSemigroup
/- # The convolution identity for Poisson kernels

Main paper: shared analytic tools for §§2–6.
-/

noncomputable section

open scoped BigOperators Topology
open MeasureTheory Filter Complex InnerProductSpace Metric

namespace TaoAdditive1132.AtomicProbability

variable {n : ℕ} (μ : AtomicProbability n)

theorem norm_cauchy_le {z : ℂ} {h : ℝ} (hh : 0 < h) (hz : h ≤ z.im) :
    ‖μ.cauchy z‖ ≤ 1 / h := by
  have hd (i : Fin n) : h ≤ ‖z - (μ.point i : ℂ)‖ := by
    calc
      h ≤ z.im := hz
      _ ≤ |(z - (μ.point i : ℂ)).im| := by simpa using le_abs_self z.im
      _ ≤ ‖z - (μ.point i : ℂ)‖ := Complex.abs_im_le_norm _
  unfold cauchy
  calc
    _ ≤ ∑ i, ‖(μ.mass i : ℂ) / (z - μ.point i)‖ := norm_sum_le _ _
    _ ≤ ∑ i, μ.mass i / h := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (μ.mass_nonneg i)]
      exact div_le_div_of_nonneg_left (μ.mass_nonneg i) hh (hd i)
    _ = 1 / h := by rw [← Finset.sum_div, μ.sum_mass]

theorem gamma_semigroup_add {h s : ℝ} (hh : 0 < h) (hs : 0 < s) (x : ℝ) :
    μ.gamma (h + s) x = ∫ y, poissonKernel s (x - y) * μ.gamma h y := by
  let u : ℂ → ℝ := fun w => -(μ.cauchy (cayley x s w + h * I)).im
  have hu : HarmonicOnNhd u (ball 0 1) := by
    intro w hw
    have hwn : ‖w‖ < 1 := by simpa [mem_ball, dist_eq_norm] using hw
    have hc := cayley_im_pos x hs hwn
    have hcz : 0 < (cayley x s w + h * I).im := by simpa using add_pos hc hh
    have hw1 : w ≠ 1 := by intro he; simp [he] at hwn
    have hca : AnalyticAt ℂ (fun w => cayley x s w + h * I) w := by
      have ha := analyticAt_cayley x s hw1
      fun_prop
    exact ((μ.analyticAt_cauchy_upper hcz).comp
      (f := fun w => cayley x s w + h * I) hca).harmonicAt_im.neg
  have hb : ∀ w ∈ ball (0 : ℂ) 1, |u w| ≤ 1 / h := by
    intro w hw
    have hwn : ‖w‖ < 1 := by simpa [mem_ball, dist_eq_norm] using hw
    have hc := cayley_im_pos x hs hwn
    change |-(μ.cauchy (cayley x s w + h * I)).im| ≤ 1 / h
    rw [abs_neg]
    apply (Complex.abs_im_le_norm _).trans
    apply μ.norm_cauchy_le hh
    simpa using (le_add_of_nonneg_left hc.le : h ≤ (cayley x s w).im + h)
  have hl : ∀ᵐ t, Tendsto (fun j => u ((radialRadius j : ℂ) * inverseCayley t)) atTop
      (𝓝 (μ.gamma h (x + s * t))) := by
    apply ae_of_all
    intro t
    have hz : 0 < (((x + s * t : ℝ) : ℂ) + h * I).im := by simpa using hh
    have ht := (cayley_radial_tendsto x s t tendsto_radialRadius).add_const ((h : ℂ) * I)
    have hc := ((μ.analyticAt_cauchy_upper hz).continuousAt.tendsto.comp ht)
    have hi := (Complex.continuous_im.tendsto _ |>.comp hc).neg
    simpa only [u, Function.comp_def, μ.neg_im_cauchy] using hi
  have he' := harmonic_boundary_cauchy hu hb radialRadius radialRadius_mem
    (fun t => μ.gamma h (x + s * t)) hl
  have hu0 : u 0 = μ.gamma (h + s) x := by
    change -(μ.cauchy (cayley x s 0 + (h : ℂ) * I)).im = μ.gamma (h + s) x
    rw [cayley_zero, show (x : ℂ) + s * I + h * I = (x : ℂ) + (h + s) * I by ring]
    simpa only [Complex.ofReal_add] using μ.neg_im_cauchy (h + s) x
  rw [hu0, ← poisson_integral_affine hs x (μ.gamma h)] at he'
  rw [← he']
  apply integral_congr_ae
  filter_upwards with y
  rw [show x - y = -(y - x) by ring, poissonKernel_neg]

theorem gamma_semigroup {h s : ℝ} (hh : 0 < h) (hs : h < s) (x : ℝ) :
    μ.gamma s x = ∫ y, poissonKernel (s - h) (x - y) * μ.gamma h y := by
  simpa only [show h + (s - h) = s by ring] using μ.gamma_semigroup_add hh (sub_pos.mpr hs) x

end TaoAdditive1132.AtomicProbability
end
end SourceErdos1132_Shared_PoissonSemigroup

/- Erdos1132.Shared.TruncatedPotential -/
section SourceErdos1132_Shared_TruncatedPotential
/- # Harmonic representation of a truncated potential

Main paper: shared analytic tools for §§2–6.
-/

noncomputable section

open MeasureTheory Set Complex
open scoped BigOperators

namespace TaoAdditive1132

theorem inverse_quadratic_integral_bound {η d : ℝ} (hη : 0 ≤ η) (hd : d ≠ 0) :
    (∫ s in η..1, 1 / (d ^ 2 + s ^ 2)) ≤ Real.pi / (2 * |d|) := by
  have hd' : 0 < |d| := abs_pos.mpr hd
  have he : (fun s : ℝ => 1 / (d ^ 2 + s ^ 2)) =
      fun s => (Real.pi / |d|) * poissonKernel |d| s := by
    funext s
    unfold poissonKernel
    rw [sq_abs]
    field_simp
    ring
  rw [he, intervalIntegral.integral_const_mul]
  have hi := intervalIntegral_poissonKernel hd' 0 η 1
  simp only [sub_zero] at hi
  rw [hi]
  have h0 : 0 ≤ Real.arctan (η / |d|) := Real.arctan_nonneg.mpr (div_nonneg hη hd'.le)
  have h1 := Real.arctan_lt_pi_div_two (1 / |d|)
  field_simp
  nlinarith [Real.pi_pos]

theorem quadratic_local_comparison {η s x y v : ℝ} (hη : 0 < η) (hs : η ≤ s) :
    1 / ((x - v) ^ 2 + s ^ 2) ≤
      (1 + |x - y| / η) ^ 2 / ((y - v) ^ 2 + s ^ 2) := by
  let z : ℂ := (x - v : ℝ) + s * I
  let w : ℂ := (y - v : ℝ) + s * I
  have hn : η ≤ ‖z‖ := by
    apply hs.trans
    simpa [z, abs_of_nonneg (hη.le.trans hs)] using Complex.abs_im_le_norm z
  have hw : ‖w‖ ≤ ‖z‖ + |x - y| := by
    have he : w = z + ((y - x : ℝ) : ℂ) := by dsimp [w, z]; push_cast; ring
    rw [he]
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_sub_comm] using norm_add_le z ((y - x : ℝ) : ℂ)
  have hd : |x - y| ≤ (|x - y| / η) * ‖z‖ := by
    calc
      _ = (|x - y| / η) * η := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hn (by positivity)
  have hw' : ‖w‖ ≤ (1 + |x - y| / η) * ‖z‖ := by nlinarith
  have hsq : ‖w‖ ^ 2 ≤ (1 + |x - y| / η) ^ 2 * ‖z‖ ^ 2 := by
    nlinarith [norm_nonneg w, norm_nonneg z, sq_nonneg ((1 + |x - y| / η) * ‖z‖ - ‖w‖)]
  have hposx : 0 < (x - v) ^ 2 + s ^ 2 := by nlinarith
  have hposy : 0 < (y - v) ^ 2 + s ^ 2 := by nlinarith
  apply (div_le_div_iff₀ hposx hposy).mpr
  simp only [Complex.sq_norm] at hsq
  simpa [z, w, normSq_apply, ← pow_two] using hsq

namespace AtomicProbability

variable {n : ℕ} (μ : AtomicProbability n)

def truncatedPotential (η x : ℝ) : ℝ := (2 / Real.pi) * ∫ s in η..1, μ.gamma s x / s

theorem gamma_div {s : ℝ} (hs : s ≠ 0) (x : ℝ) :
    μ.gamma s x / s = ∑ i, μ.mass i / ((x - μ.point i) ^ 2 + s ^ 2) := by
  unfold gamma
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  field_simp

theorem continuousOn_gamma_div {η : ℝ} (hη : 0 < η) (x : ℝ) :
    ContinuousOn (fun s => μ.gamma s x / s) (Ici η) := by
  have hc : ContinuousOn (fun s => ∑ i, μ.mass i / ((x - μ.point i) ^ 2 + s ^ 2)) (Ici η) := by
    apply continuousOn_finsetSum
    intro i _
    exact continuousOn_const.div (by fun_prop) (fun s hs => ne_of_gt (by
      have : η ≤ s := hs
      nlinarith [sq_nonneg (x - μ.point i)]))
  apply hc.congr
  intro s hs
  exact μ.gamma_div (ne_of_gt (lt_of_lt_of_le hη hs)) x

theorem intervalIntegrable_gamma_div {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (x : ℝ) :
    IntervalIntegrable (fun s => μ.gamma s x / s) volume η 1 := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hη1]
  exact (μ.continuousOn_gamma_div hη x).mono Icc_subset_Ici_self

theorem truncatedPotential_nonneg {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (x : ℝ) :
    0 ≤ μ.truncatedPotential η x := by
  apply mul_nonneg (by positivity)
  apply intervalIntegral.integral_nonneg hη1
  intro s hs
  exact div_nonneg (μ.gamma_pos (lt_of_lt_of_le hη hs.1) x).le (hη.le.trans hs.1)

theorem truncatedPotential_local {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (x y : ℝ) :
    μ.truncatedPotential η x ≤ (1 + |x - y| / η) ^ 2 * μ.truncatedPotential η y := by
  unfold truncatedPotential
  rw [mul_left_comm ((1 + |x - y| / η) ^ 2)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on hη1 (μ.intervalIntegrable_gamma_div hη hη1 x)
    ((μ.intervalIntegrable_gamma_div hη hη1 y).const_mul _)
  intro s hs
  rw [μ.gamma_div (ne_of_gt (hη.trans_le hs.1)), μ.gamma_div (ne_of_gt (hη.trans_le hs.1)),
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hb := mul_le_mul_of_nonneg_left (quadratic_local_comparison (x := x) (y := y)
    (v := μ.point i) hη hs.1) (μ.mass_nonneg i)
  convert! hb using 1 <;> ring

theorem truncatedPotential_le_absolute {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    {x : ℝ} (hx : ∀ i, x ≠ μ.point i) :
    μ.truncatedPotential η x ≤ ∑ i, μ.mass i / |x - μ.point i| := by
  have hi (i : Fin n) : IntervalIntegrable
      (fun s => μ.mass i / ((x - μ.point i) ^ 2 + s ^ 2)) volume η 1 := by
    apply Continuous.intervalIntegrable
    exact continuous_const.div (by fun_prop) (fun s => ne_of_gt (by
      have := sq_pos_of_ne_zero (sub_ne_zero.mpr (hx i))
      nlinarith [sq_nonneg s]))
  have he : (∫ s in η..1, μ.gamma s x / s) =
      ∑ i, ∫ s in η..1, μ.mass i / ((x - μ.point i) ^ 2 + s ^ 2) := by
    rw [← intervalIntegral.integral_finsetSum (fun i _ => hi i)]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hη1] at hs
    exact μ.gamma_div (ne_of_gt (hη.trans_le hs.1)) x
  rw [truncatedPotential, he, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have he' : (∫ s in η..1, μ.mass i / ((x - μ.point i) ^ 2 + s ^ 2)) =
      μ.mass i * ∫ s in η..1, 1 / ((x - μ.point i) ^ 2 + s ^ 2) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext s
    ring
  rw [he']
  have hb := mul_le_mul_of_nonneg_left
    (inverse_quadratic_integral_bound hη.le (sub_ne_zero.mpr (hx i))) (μ.mass_nonneg i)
  have hb' := mul_le_mul_of_nonneg_left hb (show 0 ≤ 2 / Real.pi by positivity)
  convert! hb' using 1
  field_simp

end AtomicProbability
end TaoAdditive1132
end
end SourceErdos1132_Shared_TruncatedPotential

/- Erdos1132.Shared.LogKernel -/
section SourceErdos1132_Shared_LogKernel
/- # The logarithmic average of Poisson kernels

Main paper: shared analytic tools for §§2–6.
-/

noncomputable section

open MeasureTheory Set

namespace TaoAdditive1132

def logKernel (h η t : ℝ) : ℝ := (∫ s in Icc η 1, poissonKernel (s - h) t / s) / (-Real.log η)

theorem measurable_poissonKernel : Measurable (fun p : ℝ × ℝ => poissonKernel p.1 p.2) := by
  unfold poissonKernel
  fun_prop

theorem poissonKernel_le {h : ℝ} (hh : 0 < h) (t : ℝ) :
    poissonKernel h t ≤ 1 / (Real.pi * h) := by
  unfold poissonKernel
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [Real.pi_pos, sq_nonneg t]

theorem integrableOn_inverse {η : ℝ} (hη : 0 < η) :
    IntegrableOn (fun s : ℝ => 1 / s) (Icc η 1) := by
  apply ContinuousOn.integrableOn_Icc
  exact continuousOn_const.div continuousOn_id (fun s hs => ne_of_gt (hη.trans_le hs.1))

theorem integral_inverse_Icc {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    (∫ s in Icc η 1, 1 / s) = -Real.log η := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hη1,
    integral_one_div_of_pos hη zero_lt_one]
  simp

theorem integrable_poisson_mixture {h η : ℝ} (hη : 0 < η) (hhη : h < η) :
    Integrable (fun p : ℝ × ℝ => poissonKernel (p.1 - h) p.2 / p.1)
      ((volume.restrict (Icc η 1)).prod volume) := by
  have hm : Measurable (fun p : ℝ × ℝ => poissonKernel (p.1 - h) p.2 / p.1) := by
    unfold poissonKernel
    fun_prop
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact (integrable_poissonKernel (sub_pos.mpr (hhη.trans_le hs.1)).le).div_const s
  · apply (integrableOn_inverse hη).congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    have hsh : 0 < s - h := sub_pos.mpr (hhη.trans_le hs.1)
    have hs0 : 0 < s := hη.trans_le hs.1
    simp only [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (poissonKernel_pos hsh _).le hs0.le),
      integral_div, integral_poissonKernel hsh]

theorem integrable_logKernel {h η : ℝ} (hη : 0 < η) (hhη : h < η) :
    Integrable (logKernel h η) :=
  (integrable_poisson_mixture hη hhη).integral_prod_right.div_const _

theorem logKernel_nonneg {h η : ℝ} (hη : 0 < η) (hhη : h < η) (hη1 : η < 1) (t : ℝ) :
    0 ≤ logKernel h η t := by
  apply div_nonneg _ (neg_nonneg.mpr (Real.log_nonpos hη.le hη1.le))
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  exact div_nonneg (poissonKernel_pos (sub_pos.mpr (hhη.trans_le hs.1)) t).le (hη.le.trans hs.1)

theorem logKernel_neg (h η t : ℝ) : logKernel h η (-t) = logKernel h η t := by
  simp only [logKernel, poissonKernel_neg]

theorem integral_logKernel {h η : ℝ} (hη : 0 < η) (hhη : h < η) (hη1 : η < 1) :
    (∫ t, logKernel h η t) = 1 := by
  simp only [logKernel]
  rw [integral_div,
    ← integral_integral_swap (integrable_poisson_mixture hη hhη)]
  have he : (∫ s in Icc η 1, ∫ t, poissonKernel (s - h) t / s) = -Real.log η := by
    rw [← integral_inverse_Icc hη hη1.le]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    rw [integral_div, integral_poissonKernel (sub_pos.mpr (hhη.trans_le hs.1))]
  rw [he, div_self (ne_of_gt (neg_pos.mpr (Real.log_neg hη hη1)))]

theorem poisson_mixture_bound {h η s : ℝ} (hη : 0 < η) (hhη : h < η) (hs : η ≤ s) (t : ℝ) :
    poissonKernel (s - h) t / s ≤ 1 / (Real.pi * (η - h) * η) := by
  have hs0 := hη.trans_le hs
  have hsh := sub_pos.mpr (hhη.trans_le hs)
  calc
    _ ≤ (1 / (Real.pi * (s - h))) / s :=
      div_le_div_of_nonneg_right (poissonKernel_le hsh t) hs0.le
    _ = 1 / (Real.pi * (s - h) * s) := by rw [div_div]
    _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (by positivity) (by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (by linarith) Real.pi_pos.le
      · exact hs
      · exact hη.le
      · positivity)

theorem continuous_logKernel {h η : ℝ} (hη : 0 < η) (hhη : h < η) :
    Continuous (logKernel h η) := by
  apply Continuous.div_const
  apply continuous_of_dominated (bound := fun _ => 1 / (Real.pi * (η - h) * η))
  · intro t
    have hm : Measurable (fun s => poissonKernel (s - h) t / s) := by
      unfold poissonKernel
      fun_prop
    exact hm.aestronglyMeasurable
  · intro t
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg
      (poissonKernel_pos (sub_pos.mpr (hhη.trans_le hs.1)) t).le (hη.le.trans hs.1))]
    exact poisson_mixture_bound hη hhη hs.1 t
  · exact integrable_const _
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact (continuous_poissonKernel (sub_pos.mpr (hhη.trans_le hs.1))).div_const s

end TaoAdditive1132
end
end SourceErdos1132_Shared_LogKernel

/- Erdos1132.Shared.KernelOperator -/
section SourceErdos1132_Shared_KernelOperator
/- # Integral operators for nonnegative convolution kernels

Main paper: shared analytic tools for §§2–6.
-/

noncomputable section

open MeasureTheory Set Complex

namespace TaoAdditive1132

theorem integrable_poisson_mixture_translate {h η : ℝ} (hη : 0 < η) (hhη : h < η) (x : ℝ) :
    Integrable (fun p : ℝ × ℝ => poissonKernel (p.1 - h) (x - p.2) / p.1)
      ((volume.restrict (Icc η 1)).prod volume) := by
  have hm : Measurable (fun p : ℝ × ℝ => poissonKernel (p.1 - h) (x - p.2) / p.1) := by
    unfold poissonKernel
    fun_prop
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact ((integrable_poissonKernel (sub_pos.mpr (hhη.trans_le hs.1)).le).comp_sub_left x).div_const s
  · apply (integrableOn_inverse hη).congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    have hsh : 0 < s - h := sub_pos.mpr (hhη.trans_le hs.1)
    have hs0 : 0 < s := hη.trans_le hs.1
    simp only [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (poissonKernel_pos hsh _).le hs0.le),
      integral_div, integral_sub_left_eq_self, integral_poissonKernel hsh]

theorem logKernel_operator {h η : ℝ} (hη : 0 < η) (hhη : h < η) (x : ℝ)
    {f : ℝ → ℝ} (hf : Measurable f) {M : ℝ} (hM : ∀ y, |f y| ≤ M) :
    (∫ y, logKernel h η (x - y) * f y) =
      (∫ s in Icc η 1, (∫ y, poissonKernel (s - h) (x - y) * f y) / s) / (-Real.log η) := by
  have hbase := integrable_poisson_mixture_translate hη hhη x
  have hint : Integrable (fun p : ℝ × ℝ =>
      poissonKernel (p.1 - h) (x - p.2) / p.1 * f p.2)
      ((volume.restrict (Icc η 1)).prod volume) := by
    apply (hbase.norm.const_mul M).mono'
    · exact (hbase.aestronglyMeasurable.mul (hf.comp measurable_snd).aestronglyMeasurable)
    · apply ae_of_all
      intro p
      rw [norm_mul]
      calc
        _ ≤ ‖poissonKernel (p.1 - h) (x - p.2) / p.1‖ * M :=
          mul_le_mul_of_nonneg_left (hM p.2) (norm_nonneg _)
        _ = _ := mul_comm _ _
  have he (y : ℝ) : logKernel h η (x - y) * f y =
      (∫ s in Icc η 1, poissonKernel (s - h) (x - y) / s * f y) / (-Real.log η) := by
    rw [integral_mul_const, logKernel]
    ring
  simp_rw [he]
  rw [integral_div, ← integral_integral_swap hint]
  congr 1
  apply integral_congr_ae
  filter_upwards with s
  rw [← integral_div]
  apply integral_congr_ae
  filter_upwards with y
  ring

namespace AtomicProbability

variable {n : ℕ} (μ : AtomicProbability n)

theorem continuous_gamma {h : ℝ} (hh : 0 < h) : Continuous (μ.gamma h) := by
  unfold gamma
  apply continuous_finsetSum
  intro i _
  exact continuous_const.div (by fun_prop) (fun x => ne_of_gt (by positivity))

theorem gamma_le_one_div {h : ℝ} (hh : 0 < h) (x : ℝ) : μ.gamma h x ≤ 1 / h := by
  rw [← μ.neg_im_cauchy h x]
  calc
    _ ≤ |(μ.cauchy ((x : ℂ) + h * I)).im| := neg_le_abs _
    _ ≤ ‖μ.cauchy ((x : ℂ) + h * I)‖ := abs_im_le_norm _
    _ ≤ 1 / h := μ.norm_cauchy_le hh (by simp)

theorem truncatedPotential_operator {h η : ℝ} (hh : 0 < h) (hhη : h < η) (hη1 : η < 1) (x : ℝ) :
    μ.truncatedPotential η x =
      (2 / Real.pi) * (-Real.log η) * ∫ y, logKernel h η (x - y) * μ.gamma h y := by
  have hη : 0 < η := hh.trans hhη
  have hm := logKernel_operator hη hhη x (μ.continuous_gamma hh).measurable
    (fun y => by rw [abs_of_pos (μ.gamma_pos hh y)]; exact μ.gamma_le_one_div hh y)
  rw [hm]
  have he : (∫ s in Icc η 1, (∫ y, poissonKernel (s - h) (x - y) * μ.gamma h y) / s) =
      ∫ s in η..1, μ.gamma s x / s := by
    rw [intervalIntegral.integral_of_le hη1.le, ← integral_Icc_eq_integral_Ioc]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    rw [← μ.gamma_semigroup hh (hhη.trans_le hs.1)]
  rw [he, truncatedPotential]
  have hl : Real.log η ≠ 0 := (Real.log_neg hη hη1).ne
  field_simp

end AtomicProbability
end TaoAdditive1132
end
end SourceErdos1132_Shared_KernelOperator

/- Erdos1132.Shared.Chebyshev -/
section SourceErdos1132_Shared_Chebyshev
/- # Chebyshev approximation to the Cauchy kernel

Main paper: shared analytic tools for §§2–6.
-/

noncomputable section

namespace TaoAdditive1132

open Polynomial.Chebyshev

theorem chebyshev_norm_le_one (k : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (-1) 1) :
    ‖(T ℂ k).eval (t : ℂ)‖ ≤ 1 := by
  rw [← complex_ofReal_eval_T, Complex.norm_real, Real.norm_eq_abs,
    ← Real.cos_arccos ht.1 ht.2, T_real_cos]
  exact Real.abs_cos_le_one _

private theorem sinh_abs (x : ℝ) : Real.sinh |x| = |Real.sinh x| := by
  by_cases hx : 0 ≤ x
  · simp [abs_of_nonneg hx, abs_of_nonneg (Real.sinh_nonneg_iff.mpr hx)]
  · have hx' : x ≤ 0 := le_of_not_ge hx
    simp [abs_of_nonpos hx', Real.sinh_neg,
      abs_of_nonpos (Real.sinh_nonpos_iff.mpr hx')]

theorem norm_cos_sq (z : ℂ) :
    ‖Complex.cos z‖ ^ 2 = Real.cos z.re ^ 2 + Real.sinh z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.cos_eq, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.mul_re, Complex.cos_ofReal_re,
    Complex.cosh_ofReal_re, Complex.cos_ofReal_im, Complex.cosh_ofReal_im,
    Complex.sin_ofReal_re, Complex.sinh_ofReal_re, Complex.sin_ofReal_im,
    Complex.sinh_ofReal_im, Complex.I_re, Complex.I_im, Complex.sub_im,
    Complex.mul_im, mul_zero, zero_mul, add_zero, sub_zero, zero_sub,
    mul_one]
  have h := congrArg (fun a : ℝ => a * Real.sinh z.im ^ 2)
    (Real.sin_sq_add_cos_sq z.re)
  nlinarith [Real.cosh_sq z.im]

theorem sinh_abs_im_le_norm_cos (z : ℂ) :
    Real.sinh |z.im| ≤ ‖Complex.cos z‖ := by
  rw [sinh_abs]
  have h := norm_cos_sq z
  nlinarith [sq_abs (Real.sinh z.im), abs_nonneg (Real.sinh z.im),
    norm_nonneg (Complex.cos z), sq_nonneg (Real.cos z.re)]

theorem abs_im_cos_le_sinh_abs (z : ℂ) :
    |(Complex.cos z).im| ≤ Real.sinh |z.im| := by
  rw [Complex.cos_eq]
  simp only [Complex.sub_im, Complex.mul_im, Complex.cos_ofReal_re,
    Complex.cosh_ofReal_re, Complex.cos_ofReal_im, Complex.cosh_ofReal_im,
    Complex.sin_ofReal_re, Complex.sinh_ofReal_re, Complex.sin_ofReal_im,
    Complex.sinh_ofReal_im, Complex.mul_re, Complex.I_re, Complex.I_im,
    mul_zero, zero_mul, add_zero, sub_zero, zero_sub, mul_one,
    abs_neg, abs_mul]
  rw [sinh_abs]
  exact mul_le_of_le_one_left (abs_nonneg _) (Real.abs_sin_le_one _)

theorem half_le_arsinh {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1) : h / 2 ≤ Real.arsinh h := by
  have hp : 0 < 1 + h := by linarith
  have hs : 1 ≤ Real.sqrt (1 + h ^ 2) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith [sq_nonneg h]
  have hl := Real.one_sub_inv_le_log_of_pos hp
  have hfrac : h / 2 ≤ 1 - (1 + h)⁻¹ := by
    rw [show 1 - (1 + h)⁻¹ = h / (1 + h) by field_simp; ring]
    apply (le_div_iff₀ hp).mpr
    nlinarith
  exact hfrac.trans (hl.trans (Real.log_le_log hp (by linarith)))

/-- Exponential growth off the interval, in the form used for Cauchy cancellation. -/
theorem chebyshev_norm_lower (k : ℕ) {z : ℂ} {h : ℝ}
    (hh : 0 ≤ h) (hh1 : h ≤ 1) (hz : h ≤ |z.im|) :
    Real.sinh ((k : ℝ) * h / 2) ≤ ‖(T ℂ k).eval z‖ := by
  obtain ⟨θ, rfl⟩ := Complex.cos_surjective z
  have hθ : h / 2 ≤ |θ.im| := by
    apply (half_le_arsinh hh hh1).trans
    rw [← Real.arsinh_sinh |θ.im|]
    exact Real.arsinh_le_arsinh.mpr (hz.trans (abs_im_cos_le_sinh_abs θ))
  rw [T_complex_cos]
  apply le_trans _ (sinh_abs_im_le_norm_cos ((k : ℤ) * θ))
  apply Real.sinh_le_sinh.mpr
  simp only [Int.cast_natCast, Complex.mul_im, Complex.natCast_re,
    Complex.natCast_im, zero_mul, add_zero, abs_mul,
    abs_of_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  nlinarith

end TaoAdditive1132
end
end SourceErdos1132_Shared_Chebyshev

/- Erdos1132.Shared.Cancellation -/
section SourceErdos1132_Shared_Cancellation
/- # Chebyshev approximation and signed Cauchy cancellation

Main paper: shared analytic tools for §§2–6.
-/

noncomputable section

open scoped BigOperators
open Polynomial Finset

namespace TaoAdditive1132.Nodes

variable {n : ℕ} (X : Nodes n)

theorem signedMass_cancellation_complex {p : ℂ[X]} (hp : p.degree < (n - 1 : ℕ)) :
    ∑ i, (X.signedMass i : ℂ) * p.eval (X.point i : ℂ) = 0 := by
  have hinj : Function.Injective (fun i => (X.point i : ℂ)) :=
    Complex.ofReal_injective.comp X.injective
  have hpn : p.degree < (n : ℕ) :=
    hp.trans_le (by exact_mod_cast Nat.sub_le n 1)
  have h := Lagrange.coeff_eq_sum hinj.injOn (s := univ) (P := p)
    (by simpa using hpn)
  have hc : p.coeff (n - 1) = 0 := Polynomial.coeff_eq_zero_of_degree_lt hp
  simp only [card_univ, Fintype.card_fin, hc] at h
  have hw : ∑ i, (X.weight i : ℂ) * p.eval (X.point i : ℂ) = 0 := by
    apply Eq.trans ?_ h.symm
    apply sum_congr rfl
    intro i _
    simp [weight, Lagrange.nodalWeight, prod_inv_distrib, div_eq_mul_inv, mul_comm]
  simp only [signedMass, Complex.ofReal_div, div_mul_eq_mul_div, ← sum_div, hw, zero_div]

/-- Polynomial cancellation applied to the divided difference at `z`. -/
theorem cauchy_polynomial_identity {p : ℂ[X]} (hp : p.degree ≤ (n - 1 : ℕ))
    {z : ℂ} (hz : ∀ i, z ≠ (X.point i : ℂ)) :
    p.eval z * X.signedCauchy z =
      ∑ i, (X.signedMass i : ℂ) / (z - X.point i) * p.eval (X.point i : ℂ) := by
  let q := p /ₘ (Polynomial.X - C z)
  have hq : q.degree < (n - 1 : ℕ) := by
    by_cases hp0 : p = 0
    · simp [q, hp0]
    · exact (degree_divByMonic_lt p (Polynomial.X - C z) hp0 (by simp)).trans_le hp
  have hc := X.signedMass_cancellation_complex hq
  have hi (i : Fin n) :
      (X.signedMass i : ℂ) / (z - X.point i) * p.eval (X.point i : ℂ) =
        p.eval z * ((X.signedMass i : ℂ) / (z - X.point i)) -
          (X.signedMass i : ℂ) * q.eval (X.point i : ℂ) := by
    have h := congrArg (Polynomial.eval (X.point i : ℂ))
      (modByMonic_add_div p (Polynomial.X - C z))
    rw [modByMonic_X_sub_C_eq_C_eval] at h
    simp only [eval_add, eval_C, eval_mul, eval_sub, eval_X] at h
    have hzi := sub_ne_zero.mpr (hz i)
    field_simp
    linear_combination -(X.signedMass i : ℂ) * h
  simp_rw [hi]
  rw [sum_sub_distrib, hc, sub_zero, ← mul_sum]
  rfl

theorem cauchy_polynomial_bound (hn : 0 < n) {p : ℂ[X]}
    (hp : p.degree ≤ (n - 1 : ℕ)) (hb : ∀ i, ‖p.eval (X.point i : ℂ)‖ ≤ 1)
    {z : ℂ} {h : ℝ} (hh : 0 < h) (hz : h ≤ |z.im|) :
    ‖p.eval z‖ * ‖X.signedCauchy z‖ ≤ 1 / h := by
  have hzn (i : Fin n) : h ≤ ‖z - (X.point i : ℂ)‖ := by
    exact hz.trans (by simpa using Complex.abs_im_le_norm (z - (X.point i : ℂ)))
  have hzne (i : Fin n) : z ≠ (X.point i : ℂ) := by
    intro he
    simpa [he] using hh.trans_le (hzn i)
  rw [← norm_mul, X.cauchy_polynomial_identity hp hzne]
  calc
    ‖∑ i, (X.signedMass i : ℂ) / (z - X.point i) * p.eval (X.point i : ℂ)‖
        ≤ ∑ i, ‖(X.signedMass i : ℂ) / (z - X.point i) * p.eval (X.point i : ℂ)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i, X.mass i / h := by
      apply sum_le_sum
      intro i _
      rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, X.abs_signedMass hn]
      calc
        X.mass i / ‖z - (X.point i : ℂ)‖ * ‖p.eval (X.point i : ℂ)‖
            ≤ X.mass i / ‖z - (X.point i : ℂ)‖ :=
          mul_le_of_le_one_right (div_nonneg (X.mass_pos hn i).le (norm_nonneg _)) (hb i)
        _ ≤ X.mass i / h :=
          div_le_div_of_nonneg_left (X.mass_pos hn i).le hh (hzn i)
    _ = 1 / h := by rw [← sum_div, X.sum_mass hn]

theorem cauchy_chebyshev_bound (hn : 2 ≤ n) {z : ℂ} {h : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1) (hz : h ≤ |z.im|) :
    ‖X.signedCauchy z‖ ≤ 1 / (h * Real.sinh ((n - 1 : ℕ) * h / 2)) := by
  have hp : (Polynomial.Chebyshev.T ℂ (n - 1 : ℕ)).degree ≤ (n - 1 : ℕ) := by
    simp [Polynomial.Chebyshev.degree_T]
  have hb := X.cauchy_polynomial_bound (by omega) hp
    (fun i => chebyshev_norm_le_one (n - 1) (X.mem_interval i)) hh hz
  have hl := chebyshev_norm_lower (n - 1) hh.le hh1 hz
  have hs : 0 < Real.sinh ((n - 1 : ℕ) * h / 2) := by
    apply Real.sinh_pos_iff.mpr
    have hnn : (0 : ℝ) < (n - 1 : ℕ) := by exact_mod_cast (show 0 < n - 1 by omega)
    positivity
  have hm := (mul_le_mul_of_nonneg_right hl (norm_nonneg (X.signedCauchy z))).trans hb
  rw [← div_div]
  apply (le_div_iff₀ hs).mpr
  simpa [mul_comm] using hm

theorem cancellation_ratio_bound (hn : 2 ≤ n) {h x : ℝ} (hh : 0 < h)
    (hh1 : h ≤ 1) (hx : x ∈ Set.Icc (-1) 1) :
    ‖X.signedCauchy ((x : ℂ) + h * Complex.I)‖ /
        (X.probability (by omega)).gamma h x ≤
      (4 + h ^ 2) / (h ^ 2 * Real.sinh ((n - 1 : ℕ) * h / 2)) := by
  have hg := (X.probability (by omega)).gamma_lower hh hx X.mem_interval
  have hb := X.cauchy_chebyshev_bound hn hh hh1
    (z := (x : ℂ) + h * Complex.I) (by simp [abs_of_pos hh])
  have hd : 0 < h / (4 + h ^ 2) := by positivity
  calc
    _ ≤ ‖X.signedCauchy ((x : ℂ) + h * Complex.I)‖ / (h / (4 + h ^ 2)) :=
      div_le_div_of_nonneg_left (norm_nonneg _) hd hg
    _ ≤ (1 / (h * Real.sinh ((n - 1 : ℕ) * h / 2))) / (h / (4 + h ^ 2)) :=
      div_le_div_of_nonneg_right hb hd.le
    _ = _ := by field_simp

end TaoAdditive1132.Nodes
end
end SourceErdos1132_Shared_Cancellation

/- Erdos1132.Shared.Scales -/
section SourceErdos1132_Shared_Scales
/- # Row sizes, heights, and the cancellation error

Main paper: shared analytic tools for §§2–6.
-/

noncomputable section

open Filter
open scoped Topology

namespace TaoAdditive1132

def rowSize (n : ℕ) : ℝ := n + 2

def height (a : ℝ) (n : ℕ) : ℝ := rowSize n ^ (-a)

theorem rowSize_ge_two (n : ℕ) : 2 ≤ rowSize n := by
  dsimp [rowSize]
  linarith [Nat.cast_nonneg n (α := ℝ)]

theorem rowSize_pos (n : ℕ) : 0 < rowSize n := lt_of_lt_of_le (by norm_num) (rowSize_ge_two n)

theorem tendsto_rowSize : Tendsto rowSize atTop atTop := by
  exact tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop

theorem height_pos (a : ℝ) (n : ℕ) : 0 < height a n := Real.rpow_pos_of_pos (rowSize_pos n) _

theorem height_le_one {a : ℝ} (ha : 0 ≤ a) (n : ℕ) : height a n ≤ 1 := by
  exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [rowSize_ge_two n]) (neg_nonpos.mpr ha)

theorem height_lt_one {a : ℝ} (ha : 0 < a) (n : ℕ) : height a n < 1 := by
  exact Real.rpow_lt_one_of_one_lt_of_neg (by linarith [rowSize_ge_two n]) (neg_neg_of_pos ha)

theorem height_antitone {a b : ℝ} (hab : b < a) (n : ℕ) : height a n < height b n := by
  exact Real.rpow_lt_rpow_of_exponent_lt (by linarith [rowSize_ge_two n]) (neg_lt_neg hab)

theorem tendsto_height {a : ℝ} (ha : 0 < a) : Tendsto (height a) atTop (𝓝 0) :=
  (tendsto_rpow_neg_atTop ha).comp tendsto_rowSize

theorem height_ratio (a b : ℝ) (n : ℕ) : height a n / height b n = height (a - b) n := by
  dsimp [height]
  rw [← Real.rpow_sub (rowSize_pos n)]
  congr 1
  ring

theorem tendsto_height_ratio {a b : ℝ} (hab : b < a) :
    Tendsto (fun n => height a n / height b n) atTop (𝓝 0) := by
  simp_rw [height_ratio]
  exact tendsto_height (sub_pos.mpr hab)

theorem neg_log_height (a : ℝ) (n : ℕ) : -Real.log (height a n) = a * Real.log (rowSize n) := by
  rw [height, Real.log_rpow (rowSize_pos n)]
  ring

theorem rowSize_mul_height (a : ℝ) (n : ℕ) :
    rowSize n * height a n = rowSize n ^ (1 - a) := by
  rw [sub_eq_add_neg, Real.rpow_add (rowSize_pos n), Real.rpow_one]
  rfl

theorem power_exponential_decay {a : ℝ} (ha : a < 1) :
    Tendsto (fun n => rowSize n ^ (2 * a) * Real.exp (-(rowSize n ^ (1 - a)) / 4))
      atTop (𝓝 0) := by
  have ht := (tendsto_rpow_atTop (sub_pos.mpr ha)).comp tendsto_rowSize
  have hl := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    (2 * a / (1 - a)) (1 / 4) (by norm_num)).comp ht
  convert! hl using 1
  funext n
  dsimp only [Function.comp_apply]
  rw [← Real.rpow_mul (rowSize_pos n).le,
    mul_div_cancel₀ _ (sub_ne_zero.mpr ha.ne' )]
  congr 2
  ring

theorem exp_div_four_le_sinh {t : ℝ} (ht : 1 ≤ t) : Real.exp t / 4 ≤ Real.sinh t := by
  have he : 2 ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
  have hn : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  rw [Real.sinh_eq]
  linarith


/-- A uniform error bound for every row with `n + 2` distinct nodes. -/
def cancellationError (a : ℝ) (n : ℕ) : ℝ :=
  20 * (rowSize n ^ (2 * a) * Real.exp (-(rowSize n ^ (1 - a)) / 4))

theorem tendsto_cancellationError {a : ℝ} (ha : a < 1) :
    Tendsto (cancellationError a) atTop (𝓝 0) := by
  convert! (power_exponential_decay ha).const_mul 20 using 1
  norm_num

theorem cancellationError_nonneg (a : ℝ) (n : ℕ) : 0 ≤ cancellationError a n := by
  exact mul_nonneg (by norm_num) (mul_nonneg (Real.rpow_nonneg (rowSize_pos n).le _) (Real.exp_pos _).le)

theorem eventually_cancellation_bound {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    ∀ᶠ n in atTop, ∀ X : Nodes (n + 2), ∀ (x : ℝ), x ∈ Set.Icc (-1) 1 →
      ‖X.signedCauchy ((x : ℂ) + height a n * Complex.I)‖ /
        (X.probability (by omega)).gamma (height a n) x ≤ cancellationError a n := by
  have ht : Tendsto (fun n => rowSize n ^ (1 - a) / 4) atTop atTop :=
    ((tendsto_rpow_atTop (sub_pos.mpr ha1)).comp tendsto_rowSize).atTop_div_const (by norm_num)
  filter_upwards [ht.eventually (eventually_ge_atTop 1)] with n hn X x hx
  let h := height a n
  have hh : 0 < h := height_pos a n
  have hh1 : h ≤ 1 := height_le_one ha.le n
  have heq : rowSize n ^ (1 - a) / 4 = rowSize n * h / 4 := by
    rw [rowSize_mul_height]
  have harg : rowSize n ^ (1 - a) / 4 ≤ ((n + 2 - 1 : ℕ) : ℝ) * h / 2 := by
    rw [heq]
    have he : ((n + 2 - 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by norm_cast
    rw [he]
    dsimp [rowSize]
    nlinarith [Nat.cast_nonneg n (α := ℝ)]
  have hs := (exp_div_four_le_sinh hn).trans (Real.sinh_le_sinh.mpr harg)
  have hden : 0 < h ^ 2 * (Real.exp (rowSize n ^ (1 - a) / 4) / 4) := by positivity
  have hb := X.cancellation_ratio_bound (by omega) hh hh1 hx
  apply hb.trans
  calc
    (4 + h ^ 2) / (h ^ 2 * Real.sinh (((n + 2 - 1 : ℕ) : ℝ) * h / 2))
      ≤ (4 + h ^ 2) / (h ^ 2 * (Real.exp (rowSize n ^ (1 - a) / 4) / 4)) :=
        div_le_div_of_nonneg_left (by positivity) hden (mul_le_mul_of_nonneg_left hs (sq_nonneg h))
    _ ≤ 5 / (h ^ 2 * (Real.exp (rowSize n ^ (1 - a) / 4) / 4)) :=
      div_le_div_of_nonneg_right (by nlinarith) hden.le
    _ = cancellationError a n := by
      have hp : h ^ 2 = (rowSize n ^ (2 * a))⁻¹ := by
        dsimp only [h, height]
        rw [← Real.rpow_mul_natCast (rowSize_pos n).le,
          show (-a) * (2 : ℕ) = -(2 * a) by norm_num; ring,
          Real.rpow_neg (rowSize_pos n).le]
      rw [hp, cancellationError, show -(rowSize n ^ (1 - a)) / 4 = -(rowSize n ^ (1 - a) / 4) by ring,
        Real.exp_neg]
      field_simp
      ring

end TaoAdditive1132
end
end SourceErdos1132_Shared_Scales

/- Erdos1132.Shared.KernelConcentration -/
section SourceErdos1132_Shared_KernelConcentration
/- # Concentration of Poisson and logarithmic kernels

Main paper: shared analytic tools for §§2–6.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace TaoAdditive1132

theorem arctan_le_self_nonneg {t : ℝ} (ht : 0 ≤ t) : Real.arctan t ≤ t := by
  have hf : Continuous (fun s : ℝ => 1 / (1 + s ^ 2)) :=
    continuous_const.div (by fun_prop) (fun s => ne_of_gt (by positivity))
  have he := integral_one_div_one_add_sq (a := 0) (b := t)
  simp only [Real.arctan_zero, sub_zero] at he
  rw [← he]
  calc
    _ ≤ ∫ _ in (0 : ℝ)..t, (1 : ℝ) := by
      apply intervalIntegral.integral_mono_on ht (hf.intervalIntegrable 0 t) intervalIntegrable_const
      intro s _
      exact (div_le_one (by positivity)).mpr (by nlinarith [sq_nonneg s])
    _ = t := by simp

theorem poissonKernel_tail_bound {h δ : ℝ} (hh : 0 < h) (hδ : 0 < δ) :
    (∫ t in (Icc (-δ) δ)ᶜ, poissonKernel h t) ≤ 2 * h / (Real.pi * δ) := by
  rw [setIntegral_compl measurableSet_Icc (integrable_poissonKernel hh.le), integral_poissonKernel hh,
    integral_poissonKernel_Icc hh (by linarith)]
  rw [neg_div, Real.arctan_neg]
  have hi := Real.arctan_inv_of_pos (div_pos hδ hh)
  rw [inv_div] at hi
  have hb := arctan_le_self_nonneg (div_nonneg hh.le hδ.le)
  rw [hi] at hb
  have hb' := (le_div_iff₀ hδ).mp hb
  apply (le_div_iff₀ (mul_pos Real.pi_pos hδ)).mpr
  field_simp
  nlinarith

theorem logKernel_setIntegral {h η : ℝ} (hη : 0 < η) (hhη : h < η)
    {E : Set ℝ} (hE : MeasurableSet E) :
    (∫ t in E, logKernel h η t) =
      (∫ s in Icc η 1, (∫ t in E, poissonKernel (s - h) t) / s) / (-Real.log η) := by
  have he := logKernel_operator hη hhη 0 (f := E.indicator (fun _ => (1 : ℝ)))
    (measurable_const.indicator hE) (M := 1) (fun y => by
      by_cases hy : y ∈ E <;> simp [hy])
  simp only [zero_sub, logKernel_neg, poissonKernel_neg] at he
  have hid (f : ℝ → ℝ) : (fun y => f y * E.indicator (fun _ => (1 : ℝ)) y) = E.indicator f := by
    funext y
    by_cases hy : y ∈ E <;> simp [hy]
  simp_rw [hid, integral_indicator hE] at he
  exact he

theorem logKernel_tail_bound {h η δ : ℝ} (hh : 0 ≤ h) (hη : 0 < η)
    (hhη : h < η) (hη1 : η < 1) (hδ : 0 < δ) :
    (∫ t in (Icc (-δ) δ)ᶜ, logKernel h η t) ≤
      (2 / (Real.pi * δ)) / (-Real.log η) := by
  rw [logKernel_setIntegral hη hhη measurableSet_Icc.compl]
  apply div_le_div_of_nonneg_right _ (neg_nonneg.mpr (Real.log_nonpos hη.le hη1.le))
  have hint : IntegrableOn (fun s => (∫ t in (Icc (-δ) δ)ᶜ, poissonKernel (s - h) t) / s)
      (Icc η 1) := by
    have hm := (integrable_poisson_mixture hη hhη).mono_measure
      (μ := (volume.restrict (Icc η 1)).prod (volume.restrict (Icc (-δ) δ)ᶜ))
      (Measure.prod_mono le_rfl Measure.restrict_le_self)
    have hi := hm.integral_prod_left
    change Integrable _ (volume.restrict (Icc η 1))
    simpa only [integral_div] using hi
  calc
    _ ≤ ∫ _ in Icc η 1, 2 / (Real.pi * δ) := by
      apply setIntegral_mono_on hint (integrable_const _) measurableSet_Icc
      intro s hs
      have hs0 := hη.trans_le hs.1
      have hp := poissonKernel_tail_bound (sub_pos.mpr (hhη.trans_le hs.1)) hδ
      calc
        _ ≤ (2 * (s - h) / (Real.pi * δ)) / s := div_le_div_of_nonneg_right hp hs0.le
        _ ≤ 2 / (Real.pi * δ) := by
          apply (div_le_iff₀ hs0).mpr
          rw [div_mul_eq_mul_div]
          apply div_le_div_of_nonneg_right _ (mul_pos Real.pi_pos hδ).le
          linarith
    _ ≤ 2 / (Real.pi * δ) := by
      rw [setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
      have hc : 0 ≤ 2 / (Real.pi * δ) := by positivity
      nlinarith

theorem tendsto_logKernel_tail {a b δ : ℝ} (hb : 0 < b) (hba : b < a)
    (hδ : 0 < δ) :
    Tendsto (fun n => ∫ t in (Icc (-δ) δ)ᶜ, logKernel (height a n) (height b n) t)
      atTop (𝓝 0) := by
  have hl : Tendsto (fun n => -Real.log (height b n)) atTop atTop := by
    simp_rw [neg_log_height]
    exact (Real.tendsto_log_atTop.comp tendsto_rowSize).const_mul_atTop hb
  have hu : Tendsto (fun n => (2 / (Real.pi * δ)) / (-Real.log (height b n))) atTop (𝓝 0) :=
    hl.const_div_atTop _
  apply squeeze_zero (fun n => integral_nonneg fun t =>
    logKernel_nonneg (height_pos b n) (height_antitone hba n) (height_lt_one hb n) t)
    (fun n => logKernel_tail_bound (height_pos a n).le (height_pos b n)
      (height_antitone hba n) (height_lt_one hb n) hδ) hu

end TaoAdditive1132
end
end SourceErdos1132_Shared_KernelConcentration

/- Erdos1132.Shared.ApproximateIdentity -/
section SourceErdos1132_Shared_ApproximateIdentity
/- # Convergence of approximate identities

Main paper: shared analytic tools for §§2–6.
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped Topology

namespace TaoAdditive1132

/-- Concentration at zero tests against every bounded function continuous at zero. -/
theorem probability_kernel_tendsto {k : ℕ → ℝ → ℝ}
    (hk : ∀ n t, 0 ≤ k n t) (hi : ∀ n, Integrable (k n))
    (hm : ∀ n, ∫ t, k n t = 1)
    (ht : ∀ δ > 0, Tendsto (fun n => ∫ t in (Icc (-δ) δ)ᶜ, k n t) atTop (𝓝 0))
    {f : ℝ → ℝ} (hf : Measurable f) {M : ℝ} (hb : ∀ t, |f t| ≤ M)
    (hc : ContinuousAt f 0) :
    Tendsto (fun n => ∫ t, k n t * f t) atTop (𝓝 (f 0)) := by
  have hM : 0 ≤ M := (abs_nonneg (f 0)).trans (hb 0)
  have hif (n : ℕ) : Integrable (fun t => k n t * f t) :=
    (hi n).mul_bdd hf.aestronglyMeasurable (ae_of_all _ hb)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := Metric.continuousAt_iff.mp hc (ε / 2) (by positivity)
  let d := δ / 2
  have hd0 : 0 < d := by dsimp [d]; positivity
  let B := 2 * M + 1
  have hB : 0 < B := by dsimp [B]; linarith
  filter_upwards [(ht d hd0).eventually (gt_mem_nhds (show (0 : ℝ) < ε / (2 * B) by positivity))]
    with n hn
  have hid : Integrable (fun t => k n t * (f t - f 0)) :=
    (hif n).sub ((hi n).mul_const (f 0)) |>.congr (ae_of_all _ fun t => by dsimp; ring)
  have hie : Integrable ((Icc (-d) d)ᶜ.indicator (k n)) := (hi n).indicator measurableSet_Icc.compl
  have hbound : ∀ t, ‖k n t * (f t - f 0)‖ ≤
      (ε / 2) * k n t + B * (Icc (-d) d)ᶜ.indicator (k n) t := by
    intro t
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hk n t), Real.norm_eq_abs]
    by_cases ht' : t ∈ Icc (-d) d
    · have hdist : dist t 0 < δ := by
        rw [Real.dist_eq, sub_zero, abs_lt]
        dsimp [d] at ht'
        constructor <;> linarith [ht'.1, ht'.2]
      have hsmall : |f t - f 0| < ε / 2 := by simpa [Real.dist_eq] using hd hdist
      simp only [indicator_of_notMem (show t ∉ (Icc (-d) d)ᶜ by simpa), mul_zero, add_zero]
      nlinarith [hk n t]
    · have hdif : |f t - f 0| ≤ 2 * M :=
        (abs_sub _ _).trans (by linarith [hb t, hb 0])
      rw [indicator_of_mem (show t ∈ (Icc (-d) d)ᶜ from ht')]
      dsimp only [B]
      nlinarith [hk n t]
  have heq : (∫ t, k n t * (f t - f 0)) = (∫ t, k n t * f t) - f 0 := by
    simp_rw [mul_sub]
    rw [integral_sub (hif n) ((hi n).mul_const _), integral_mul_const, hm, one_mul]
  have he : ‖(∫ t, k n t * f t) - f 0‖ ≤ ε / 2 + B * ∫ t in (Icc (-d) d)ᶜ, k n t := by
    rw [← heq]
    calc
      _ ≤ ∫ t, ‖k n t * (f t - f 0)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t, (ε / 2) * k n t + B * (Icc (-d) d)ᶜ.indicator (k n) t :=
        integral_mono hid.norm (((hi n).const_mul _).add (hie.const_mul _)) hbound
      _ = _ := by
        rw [integral_add ((hi n).const_mul _) (hie.const_mul _), integral_const_mul,
          integral_const_mul, integral_indicator measurableSet_Icc.compl, hm, mul_one]
  rw [dist_eq_norm]
  apply he.trans_lt
  have hn' : B * (∫ t in (Icc (-d) d)ᶜ, k n t) < ε / 2 := by
    have := mul_lt_mul_of_pos_left hn hB
    convert! this using 1; field_simp
  linarith

end TaoAdditive1132
end
end SourceErdos1132_Shared_ApproximateIdentity

/- Erdos1132.Additive.QuantitativeKernel -/
section SourceErdos1132_Additive_QuantitativeKernel
/- # A quantitative approximate-identity estimate for Lipschitz functions

Main paper: §4, local potential and differentiation estimates.
-/

noncomputable section
open MeasureTheory Set Real
namespace TaoAdditive1132

theorem probability_kernel_lipschitz_bound {k f : ℝ → ℝ} (hk : ∀ t, 0 ≤ k t)
    (hi : Integrable k) (hm : ∫ t, k t = 1) (hf : Measurable f)
    {M L δ : ℝ} (hM : ∀ t, |f t| ≤ M) (hL : 0 ≤ L) (hδ : 0 < δ)
    (hlip : ∀ t, |f t-f 0| ≤ L*|t|) :
    |(∫ t, k t*f t)-f 0| ≤ L*δ+2*M*(∫ t in (Icc (-δ) δ)ᶜ, k t) := by
  have hM0 : 0 ≤ M := (abs_nonneg (f 0)).trans (hM 0)
  have hif : Integrable (fun t => k t*f t) :=
    hi.mul_bdd hf.aestronglyMeasurable (ae_of_all _ hM)
  have hid : Integrable (fun t => k t*(f t-f 0)) := by
    simpa only [mul_sub] using! hif.sub (hi.mul_const (f 0))
  have hie := hi.indicator (s := (Icc (-δ) δ)ᶜ) measurableSet_Icc.compl
  have hpoint (t : ℝ) : |k t*(f t-f 0)| ≤ (L*δ)*k t +
      (2*M)*(Icc (-δ) δ)ᶜ.indicator k t := by
    rw [abs_mul, abs_of_nonneg (hk t)]
    by_cases ht : t ∈ Icc (-δ) δ
    · rw [Set.indicator_of_notMem (show t ∉ (Icc (-δ) δ)ᶜ from not_not.mpr ht), mul_zero, add_zero]
      have hsmall := (hlip t).trans (mul_le_mul_of_nonneg_left (abs_le.mpr ht) hL)
      have hp := mul_le_mul_of_nonneg_left hsmall (hk t)
      nlinarith
    · rw [Set.indicator_of_mem (show t ∈ (Icc (-δ) δ)ᶜ from ht)]
      have hsmall : |f t-f 0| ≤ 2*M := (abs_sub _ _).trans (by linarith [hM t, hM 0])
      have hp := mul_le_mul_of_nonneg_left hsmall (hk t)
      have hplus := mul_nonneg (mul_nonneg hL hδ.le) (hk t)
      nlinarith
  have heq : (∫ t, k t*(f t-f 0)) = (∫ t, k t*f t)-f 0 := by
    simp_rw [mul_sub]
    rw [integral_sub hif (hi.mul_const _), integral_mul_const, hm, one_mul]
  rw [← heq]
  calc
    _ ≤ ∫ t, |k t*(f t-f 0)| := abs_integral_le_integral_abs
    _ ≤ ∫ t, (L*δ)*k t+(2*M)*(Icc (-δ) δ)ᶜ.indicator k t :=
      integral_mono hid.abs ((hi.const_mul _).add (hie.const_mul _)) hpoint
    _ = _ := by
      rw [integral_add (hi.const_mul _) (hie.const_mul _), integral_const_mul,
        integral_const_mul, integral_indicator measurableSet_Icc.compl, hm, mul_one]

end TaoAdditive1132
end
end SourceErdos1132_Additive_QuantitativeKernel

/- Erdos1132.Additive.PoissonLog -/
section SourceErdos1132_Additive_PoissonLog
/- # The Poisson extension of a logarithmic singularity

Main paper: §4, local potential and differentiation estimates.
-/

noncomputable section
open MeasureTheory Set Filter Complex Metric Real
open scoped Topology
namespace TaoAdditive1132

theorem integrable_cauchy_of_circleIntegrable {f : ℂ → ℝ} {r : ℝ}
    (hf : CircleIntegrable f 0 r) :
    Integrable (fun t => poissonKernel 1 t * f ((r : ℂ) * inverseCayley t)) := by
  have hj := integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun t _ => (hasDerivAt_cayleyAngle t).hasDerivWithinAt) injective_cayleyAngle.injOn
    (fun θ => f (circleMap 0 r θ))
  simp only [image_univ, range_cayleyAngle, smul_eq_mul] at hj
  have hcirc : IntegrableOn (fun θ => f (circleMap 0 r θ)) (Ioo 0 (2*Real.pi)) :=
    hf.1.mono_set Ioo_subset_Ioc_self
  have hi := (hj.mp hcirc).const_mul (1/(2*Real.pi))
  rw [Measure.restrict_univ] at hi
  convert hi using 1
  funext t
  rw [circleMap_cayleyAngle_radius, abs_of_pos (show 0 < 2/(1+t^2) by positivity)]
  unfold poissonKernel
  field_simp
  ring

theorem circleAverage_log_norm_linear {A B : ℂ} (hB : B ≠ 0) (hnorm : ‖A‖ = ‖B‖) :
    Real.circleAverage (fun z => Real.log ‖A+B*z‖) 0 1 = Real.log ‖B‖ := by
  have heq : (fun z => Real.log ‖A+B*z‖) =ᶠ[codiscreteWithin (sphere (0 : ℂ) 1)]
      (fun z => Real.log ‖B‖ + Real.log ‖z-(-A/B)‖) := by
    filter_upwards [compl_singleton_mem_codiscreteWithin (-A/B)] with z hz
    have hzne : z ≠ -A/B := hz
    have hfac : A+B*z = B*(z-(-A/B)) := by field_simp; ring
    rw [hfac, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hB)
      (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hzne))]
  have hz : ‖-A/B‖ = 1 := by rw [norm_div, norm_neg, hnorm, div_self (norm_ne_zero_iff.mpr hB)]
  calc
    _ = Real.circleAverage (fun z => Real.log ‖B‖ + Real.log ‖z-(-A/B)‖) 0 1 :=
      Real.circleAverage_congr_codiscreteWithin (by simpa only [abs_one] using heq) one_ne_zero
    _ = _ := by
      rw [Real.circleAverage_fun_add (circleIntegrable_const _ _ _)
        (circleIntegrable_log_norm_sub_const 1), Real.circleAverage_const,
        circleAverage_log_norm_sub_const₁ hz, add_zero]

theorem circleAverage_log_norm_linear_div {A B : ℂ}
    (hB : B ≠ 0) (hnorm : ‖A‖ = ‖B‖) :
    Real.circleAverage (fun z => Real.log ‖(A+B*z)/(1-z)‖) 0 1 = Real.log ‖A‖ := by
  have heq : (fun z => Real.log ‖(A+B*z)/(1-z)‖) =ᶠ[codiscreteWithin (sphere (0 : ℂ) 1)]
      (fun z => Real.log ‖A+B*z‖ - Real.log ‖z-1‖) := by
    filter_upwards [compl_singleton_mem_codiscreteWithin (-A/B),
      compl_singleton_mem_codiscreteWithin (1 : ℂ)] with z hz hz1
    have hnum : A+B*z ≠ 0 := by
      intro he
      apply hz
      apply (eq_div_iff hB).mpr
      linear_combination he
    rw [norm_div, Real.log_div (norm_ne_zero_iff.mpr hnum)
      (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (Ne.symm hz1))), norm_sub_rev (1 : ℂ) z]
  have hnumInt : CircleIntegrable (fun z => Real.log ‖A+B*z‖) 0 1 :=
    MeromorphicOn.circleIntegrable_log_norm (fun z _ => by fun_prop)
  calc
    _ = Real.circleAverage (fun z => Real.log ‖A+B*z‖ - Real.log ‖z-1‖) 0 1 :=
      Real.circleAverage_congr_codiscreteWithin (by simpa only [abs_one] using heq) one_ne_zero
    _ = _ := by
      rw [Real.circleAverage_fun_sub hnumInt (circleIntegrable_log_norm_sub_const 1),
        circleAverage_log_norm_linear hB hnorm,
        circleAverage_log_norm_sub_const₁ (norm_one : ‖(1 : ℂ)‖ = 1), sub_zero, hnorm]

def logarithmicCayley (x h a : ℝ) (w : ℂ) : ℂ :=
  (((x-a : ℝ) : ℂ) + h*I + (-((x-a : ℝ) : ℂ) + h*I)*w)/(1-w)

theorem logarithmicCayley_inverse (x h a t : ℝ) :
    logarithmicCayley x h a (inverseCayley t) = (x+h*t-a : ℝ) := by
  unfold logarithmicCayley inverseCayley
  push_cast
  field_simp [inverseCayley_denom_ne_zero t]
  simp
  ring

theorem logarithmicCayley_coefficients {x h a : ℝ} (hh : 0 < h) :
    (-((x-a : ℝ) : ℂ) + h*I) ≠ 0 ∧
      ‖((x-a : ℝ) : ℂ)+h*I‖ = ‖-((x-a : ℝ) : ℂ)+h*I‖ := by
  constructor
  · intro he
    have hi := congrArg Complex.im he
    simp at hi
    exact hh.ne' hi
  · apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring

theorem integrable_cauchy_log_affine {h : ℝ} (_hh : 0 < h) (x a : ℝ) :
    Integrable (fun t => poissonKernel 1 t * Real.log (x+h*t-a)) := by
  have hmer : MeromorphicOn (logarithmicCayley x h a) (sphere 0 |(1 : ℝ)|) := by
    intro z _
    unfold logarithmicCayley
    fun_prop
  have hi := integrable_cauchy_of_circleIntegrable hmer.circleIntegrable_log_norm
  simpa only [Complex.ofReal_one, one_mul, logarithmicCayley_inverse,
    Complex.norm_real, Real.norm_eq_abs, Real.log_abs] using hi

/-- The Cauchy integral of a real logarithmic singularity, in affine coordinates. -/
theorem integral_cauchy_log_affine {h : ℝ} (hh : 0 < h) (x a : ℝ) :
    (∫ t, poissonKernel 1 t * Real.log (x+h*t-a)) =
      Real.log ‖((x-a : ℝ) : ℂ)+h*I‖ := by
  have he := circleAverage_log_norm_linear_div
    (logarithmicCayley_coefficients (x := x) (a := a) hh).1
    (logarithmicCayley_coefficients (x := x) (a := a) hh).2
  rw [circleAverage_eq_cauchy_integral] at he
  change (∫ t, poissonKernel 1 t * Real.log ‖logarithmicCayley x h a ((1 : ℂ) * inverseCayley t)‖) = _ at he
  simpa only [one_mul,
    logarithmicCayley_inverse, Complex.norm_real, Real.norm_eq_abs, Real.log_abs] using he

/-- The Poisson extension of `log |·-a|` is `log |x+ih-a|`. -/
theorem integral_poisson_log {h : ℝ} (hh : 0 < h) (x a : ℝ) :
    (∫ y, poissonKernel h (y-x) * Real.log (y-a)) =
      Real.log ‖((x-a : ℝ) : ℂ)+h*I‖ := by
  rw [poisson_integral_affine hh]
  exact integral_cauchy_log_affine hh x a

theorem integrable_poisson_affine_iff {h : ℝ} (hh : 0 < h) (x : ℝ) (f : ℝ → ℝ) :
    Integrable (fun y => poissonKernel h (y-x) * f y) ↔
      Integrable (fun t => poissonKernel 1 t * f (x+h*t)) := by
  have hinj : Function.Injective (fun t : ℝ => x+h*t) := by
    intro s t he
    exact (mul_left_cancel₀ hh.ne') (add_left_cancel he)
  have hsurj : Function.Surjective (fun t : ℝ => x+h*t) := by
    intro y
    refine ⟨(y-x)/h, ?_⟩
    field_simp
    ring
  have hd (t : ℝ) : HasDerivAt (fun t => x+h*t) h t := by
    convert! ((hasDerivAt_id t).const_mul h).const_add x using 1
    simp
  have he := integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun t _ => (hd t).hasDerivWithinAt) hinj.injOn
    (fun y => poissonKernel h (y-x) * f y)
  simp only [image_univ, hsurj.range_eq, IntegrableOn, Measure.restrict_univ,
    abs_of_pos hh, smul_eq_mul] at he
  convert he using 2
  funext t
  unfold poissonKernel
  field_simp
  ring

theorem integrable_poisson_log {h : ℝ} (hh : 0 < h) (x a : ℝ) :
    Integrable (fun y => poissonKernel h (y-x) * Real.log (y-a)) :=
  (integrable_poisson_affine_iff hh x _).mpr (integrable_cauchy_log_affine hh x a)

end TaoAdditive1132
end
end SourceErdos1132_Additive_PoissonLog

/- Erdos1132.Additive.DerivativeJumps -/
section SourceErdos1132_Additive_DerivativeJumps
/- # The exact derivative jumps of a Lebesgue function

Main paper: §5, derivative-jump energy.
-/

noncomputable section
open Set Filter Polynomial Finset
open scoped Topology BigOperators

namespace TaoAdditive1132

theorem HasDerivAt.abs_right_of_eq_zero {f : ℝ → ℝ} {d x : ℝ}
    (hf : HasDerivAt f d x) (hx : f x = 0) :
    HasDerivWithinAt (fun y => |f y|) |d| (Ioi x) x := by
  apply (hasDerivWithinAt_iff_tendsto_slope' (by simp)).mpr
  have ht := (hf.tendsto_slope.mono_left (nhdsGT_le_nhdsNE x)).abs
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  simp only [slope_def_field, hx, abs_zero, sub_zero, abs_div,
    abs_of_pos (sub_pos.mpr (show x < y from hy))]

theorem HasDerivAt.abs_left_of_eq_zero {f : ℝ → ℝ} {d x : ℝ}
    (hf : HasDerivAt f d x) (hx : f x = 0) :
    HasDerivWithinAt (fun y => |f y|) (-|d|) (Iio x) x := by
  apply (hasDerivWithinAt_iff_tendsto_slope' (by simp)).mpr
  have ht := (hf.tendsto_slope.mono_left (nhdsLT_le_nhdsNE x)).abs.neg
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  simp only [slope_def_field, hx, abs_zero, sub_zero, abs_div,
    abs_of_neg (sub_neg.mpr (show y < x from hy)), div_neg, neg_neg]

namespace Nodes
variable {n : ℕ} (X : Nodes n)

theorem cardinal_mul_linear (i : Fin n) :
    (Polynomial.X - C (X.point i)) * X.cardinal i = C (X.weight i) * X.nodePolynomial := by
  unfold cardinal weight nodePolynomial
  rw [Lagrange.basis_eq_prod_sub_inv_mul_nodal_div (mem_univ i),
    ← Lagrange.nodal_erase_eq_nodal_div (mem_univ i),
    Lagrange.nodal_eq_mul_nodal_erase (mem_univ i)]
  ring

/-- The derivative of one cardinal polynomial at a different interpolation node. -/
theorem cardinal_derivative_at_other_node (i k : Fin n) (hik : i ≠ k) :
    (X.cardinal i).derivative.eval (X.point k) =
      X.weight i / (X.weight k * (X.point k - X.point i)) := by
  have hid := congrArg (fun P : ℝ[X] => P.derivative.eval (X.point k))
    (X.cardinal_mul_linear i)
  simp only [derivative_mul, derivative_sub, derivative_X, derivative_C,
    sub_zero, eval_add, eval_mul, one_mul, eval_sub, eval_X,
    eval_C, zero_mul, zero_add] at hid
  rw [X.cardinal_at_node, if_neg hik, zero_add] at hid
  have hw : X.nodePolynomial.derivative.eval (X.point k) = (X.weight k)⁻¹ := by
    rw [X.weight_eq_derivative, inv_inv]
  rw [hw] at hid
  have hdiff : X.point k - X.point i ≠ 0 :=
    sub_ne_zero.mpr (X.injective.ne hik.symm)
  apply (eq_div_iff (mul_ne_zero (X.weight_ne_zero k) hdiff)).mpr
  calc
    _ = X.weight k * ((X.point k - X.point i) * (X.cardinal i).derivative.eval (X.point k)) := by ring
    _ = X.weight k * (X.weight i * (X.weight k)⁻¹) := by rw [hid]
    _ = X.weight i := by field_simp [X.weight_ne_zero k]

theorem abs_cardinal_derivative_at_other_node (i k : Fin n) (hik : i ≠ k) :
    |(X.cardinal i).derivative.eval (X.point k)| =
      X.mass i / (X.mass k * |X.point k - X.point i|) := by
  rw [X.cardinal_derivative_at_other_node i k hik, abs_div, abs_mul]
  unfold mass
  have hW : X.totalWeight ≠ 0 := (X.totalWeight_pos (Nat.zero_lt_of_lt i.isLt)).ne'
  field_simp

def derivativeJump (k : Fin n) : ℝ :=
  derivWithin X.lebesgue (Ioi (X.point k)) (X.point k) -
    derivWithin X.lebesgue (Iio (X.point k)) (X.point k)

theorem lebesgue_hasDerivWithinAt_right (k : Fin n) :
    HasDerivWithinAt X.lebesgue
      (∑ i : Fin n, if i = k then (X.cardinal i).derivative.eval (X.point k)
        else |(X.cardinal i).derivative.eval (X.point k)|)
      (Ioi (X.point k)) (X.point k) := by
  apply HasDerivWithinAt.fun_sum
  intro i _
  change HasDerivWithinAt (fun y : ℝ => |(X.cardinal i).eval y|) _ _ _
  have hp : HasDerivAt (fun y : ℝ => (X.cardinal i).eval y)
      ((X.cardinal i).derivative.eval (X.point k)) (X.point k) :=
    (X.cardinal i).hasDerivAt (X.point k)
  by_cases hik : i = k
  · rw [if_pos hik]
    have hpos : 0 < (X.cardinal i).eval (X.point k) := by
      rw [X.cardinal_at_node, if_pos hik]; norm_num
    simpa only [one_mul] using!
      ((hasDerivAt_abs_pos hpos).comp (X.point k) hp).hasDerivWithinAt
  · rw [if_neg hik]
    exact HasDerivAt.abs_right_of_eq_zero hp
      (by rw [X.cardinal_at_node, if_neg hik])

theorem lebesgue_hasDerivWithinAt_left (k : Fin n) :
    HasDerivWithinAt X.lebesgue
      (∑ i : Fin n, if i = k then (X.cardinal i).derivative.eval (X.point k)
        else -|(X.cardinal i).derivative.eval (X.point k)|)
      (Iio (X.point k)) (X.point k) := by
  apply HasDerivWithinAt.fun_sum
  intro i _
  change HasDerivWithinAt (fun y : ℝ => |(X.cardinal i).eval y|) _ _ _
  have hp : HasDerivAt (fun y : ℝ => (X.cardinal i).eval y)
      ((X.cardinal i).derivative.eval (X.point k)) (X.point k) :=
    (X.cardinal i).hasDerivAt (X.point k)
  by_cases hik : i = k
  · rw [if_pos hik]
    have hpos : 0 < (X.cardinal i).eval (X.point k) := by
      rw [X.cardinal_at_node, if_pos hik]; norm_num
    simpa only [one_mul] using!
      ((hasDerivAt_abs_pos hpos).comp (X.point k) hp).hasDerivWithinAt
  · rw [if_neg hik]
    exact HasDerivAt.abs_left_of_eq_zero hp
      (by rw [X.cardinal_at_node, if_neg hik])

/-- The cusp formula includes the first and last nodes, using the exterior
polynomial pieces for their outward derivatives. -/
theorem derivativeJump_eq_cardinal_sum (k : Fin n) :
    X.derivativeJump k = 2 * ∑ i ∈ univ.erase k,
      |(X.cardinal i).derivative.eval (X.point k)| := by
  rw [derivativeJump,
    (X.lebesgue_hasDerivWithinAt_right k).derivWithin (uniqueDiffWithinAt_Ioi _),
    (X.lebesgue_hasDerivWithinAt_left k).derivWithin (uniqueDiffWithinAt_Iio _),
    ← sum_sub_distrib]
  rw [← sum_erase_add _ _ (mem_univ k)]
  simp only [ite_true, sub_self, add_zero, mul_sum]
  apply sum_congr rfl
  intro i hi
  rw [if_neg (mem_erase.mp hi).1, if_neg (mem_erase.mp hi).1]
  ring

/-- The exact mass-weighted jump identity in Section 3. -/
theorem derivativeJump_eq_mass_sum (k : Fin n) :
    X.derivativeJump k = 2 * ∑ i ∈ univ.erase k,
      X.mass i / (X.mass k * |X.point k - X.point i|) := by
  rw [X.derivativeJump_eq_cardinal_sum]
  congr 1
  apply sum_congr rfl
  intro i hi
  exact X.abs_cardinal_derivative_at_other_node i k (mem_erase.mp hi).1

theorem derivativeJump_nonneg (k : Fin n) : 0 ≤ X.derivativeJump k := by
  rw [X.derivativeJump_eq_cardinal_sum]
  positivity

end Nodes
end TaoAdditive1132
end
end SourceErdos1132_Additive_DerivativeJumps

/- Erdos1132.Additive.LocalPotential -/
section SourceErdos1132_Additive_LocalPotential
/- # Elementary bounds for the normalized node polynomial

Main paper: §4, local potential and differentiation estimates.
-/

noncomputable section
open Polynomial Finset Set
open scoped BigOperators
namespace TaoAdditive1132.Nodes
variable {n : ℕ} (X : TaoAdditive1132.Nodes n)

theorem sum_cardinal (hn : 0 < n) : ∑ i, X.cardinal i = 1 := by
  exact Lagrange.sum_basis X.injective.injOn ⟨⟨0, hn⟩, mem_univ _⟩

theorem one_le_lebesgue (hn : 0 < n) (x : ℝ) : 1 ≤ X.lebesgue x := by
  have he : ∑ i, (X.cardinal i).eval x = 1 := by
    rw [← eval_finsetSum, X.sum_cardinal hn, eval_one]
  calc
    1 = |∑ i, (X.cardinal i).eval x| := by rw [he, abs_one]
    _ ≤ _ := abs_sum_le_sum_abs _ _

theorem abs_cardinal_identity (i : Fin n) (x : ℝ) :
    |x - X.point i| * |(X.cardinal i).eval x| =
      |X.weight i| * |X.nodePolynomial.eval x| := by
  have he := congrArg (fun P : ℝ[X] => P.eval x) (X.cardinal_mul_linear i)
  simp only [eval_mul, eval_sub, eval_X, eval_C] at he
  simpa only [abs_mul] using congrArg abs he

/-- The normalized monic polynomial is bounded by twice the Lebesgue function
throughout the interpolation interval, including the nodes. -/
theorem normalized_polynomial_le_lebesgue {x : ℝ} (hx : x ∈ Set.Icc (-1) 1) :
    |X.nodePolynomial.eval x| * X.totalWeight ≤ 2 * X.lebesgue x := by
  unfold totalWeight lebesgue
  rw [mul_sum, mul_sum]
  apply sum_le_sum
  intro i _
  rw [mul_comm |X.nodePolynomial.eval x|, ← X.abs_cardinal_identity]
  have hdist : |x-X.point i| ≤ 2 := by
    apply abs_le.mpr
    have hi := X.mem_interval i
    constructor <;> linarith [hx.1, hx.2, hi.1, hi.2]
  exact mul_le_mul_of_nonneg_right hdist (abs_nonneg _)

/-- A lower bound on every node distance supplies the reverse inequality. -/
theorem distance_mul_lebesgue_le_normalized_polynomial {δ x : ℝ}
    (hδ : ∀ i, δ ≤ |x - X.point i|) :
    δ * X.lebesgue x ≤ |X.nodePolynomial.eval x| * X.totalWeight := by
  unfold lebesgue totalWeight
  rw [mul_sum, mul_sum]
  apply sum_le_sum
  intro i _
  calc
    _ ≤ |x-X.point i| * |(X.cardinal i).eval x| :=
      mul_le_mul_of_nonneg_right (hδ i) (abs_nonneg _)
    _ = _ := by rw [X.abs_cardinal_identity]; ring

theorem distance_le_normalized_polynomial (hn : 0 < n) {δ x : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : ∀ i, δ ≤ |x - X.point i|) :
    δ ≤ |X.nodePolynomial.eval x| * X.totalWeight := by
  calc
    δ = δ * 1 := (mul_one _).symm
    _ ≤ δ * X.lebesgue x := mul_le_mul_of_nonneg_left (X.one_le_lebesgue hn x) hδ0
    _ ≤ _ := X.distance_mul_lebesgue_le_normalized_polynomial hδ

def potentialNormalization : ℝ := Real.log X.totalWeight / n

def realLogPotential (x : ℝ) : ℝ := -Real.log |X.nodePolynomial.eval x| / n

/-- The local polynomial bounds give explicit two-sided logarithmic-potential
bounds away from the nodes. -/
theorem local_potential_bounds (hn : 0 < n) {x δ Λ : ℝ}
    (hx : x ∈ Set.Icc (-1) 1) (hδ0 : 0 < δ) (hδ : ∀ i, δ ≤ |x-X.point i|)
    (hΛ : X.lebesgue x ≤ Λ) :
    X.potentialNormalization - Real.log (2*Λ)/n ≤ X.realLogPotential x ∧
      X.realLogPotential x ≤ X.potentialNormalization - Real.log δ/n := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hlow := X.distance_le_normalized_polynomial hn hδ0.le hδ
  have hupper := (X.normalized_polynomial_le_lebesgue hx).trans
    (mul_le_mul_of_nonneg_left hΛ (by norm_num))
  have hprod : 0 < |X.nodePolynomial.eval x| * X.totalWeight := hδ0.trans_le hlow
  have hP : 0 < |X.nodePolynomial.eval x| :=
    (mul_pos_iff_of_pos_right (X.totalWeight_pos hn)).mp hprod
  have hlo := Real.log_le_log hδ0 hlow
  have hhi := Real.log_le_log hprod hupper
  rw [Real.log_mul hP.ne' (X.totalWeight_pos hn).ne'] at hlo hhi
  unfold potentialNormalization realLogPotential
  constructor
  · apply (le_div_iff₀ hnR).mpr
    have he : (Real.log X.totalWeight/n - Real.log (2*Λ)/n) * n =
        Real.log X.totalWeight - Real.log (2*Λ) := by field_simp
    rw [he]
    linarith
  · apply (div_le_iff₀ hnR).mpr
    have he : (Real.log X.totalWeight/n - Real.log δ/n) * n =
        Real.log X.totalWeight - Real.log δ := by field_simp
    rw [he]
    linarith

end TaoAdditive1132.Nodes
end
end SourceErdos1132_Additive_LocalPotential

/- Erdos1132.Additive.LogSquare -/
section SourceErdos1132_Additive_LogSquare
/- # Local square integrability of the logarithmic kernel

Main paper: §4, local potential and differentiation estimates.
-/

noncomputable section
open MeasureTheory Set intervalIntegral
open scoped Interval
namespace TaoAdditive1132

theorem log_sq_le_rpow_bound {t : ℝ} (ht : 0 ≤ t) :
    (Real.log t)^2 ≤ 16 * (t^(1/2 : ℝ) + t^(-1/2 : ℝ)) := by
  by_cases ht0 : t = 0
  · subst t
    norm_num
  have hpow (r : ℝ) : (t^r)^2 = t^(r*2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht]
    norm_num
  by_cases hlog : 0 ≤ Real.log t
  · have hh := Real.log_le_rpow_div ht (show (0 : ℝ) < 1/4 by norm_num)
    have hs := pow_le_pow_left₀ hlog hh 2
    have he : (t^(1/4 : ℝ)/(1/4 : ℝ))^2 = 16*t^(1/2 : ℝ) := by
      rw [div_pow, hpow]
      norm_num
      ring
    rw [he] at hs
    nlinarith [Real.rpow_nonneg ht (-1/2)]
  · have hh := Real.log_le_rpow_div (inv_nonneg.mpr ht) (show (0 : ℝ) < 1/4 by norm_num)
    rw [Real.log_inv, Real.inv_rpow ht, ← Real.rpow_neg ht] at hh
    have hs := pow_le_pow_left₀ (neg_nonneg.mpr (le_of_not_ge hlog)) hh 2
    have he : (t^(-(1/4) : ℝ)/(1/4 : ℝ))^2 = 16*t^(-1/2 : ℝ) := by
      rw [div_pow, hpow]
      norm_num
      ring
    rw [he, neg_sq] at hs
    nlinarith [Real.rpow_nonneg ht (1/2)]

theorem intervalIntegrable_abs_rpow {r a b : ℝ} (hr : -1 < r) :
    IntervalIntegrable (fun x : ℝ => |x|^r) volume a b := by
  apply intervalIntegrable_of_even (fun x => by rw [abs_neg])
  intro b hb
  apply (intervalIntegrable_rpow' hr (a := 0) (b := b)).congr_uIoo
  intro x hx
  have hx0 : 0 < x := by simpa only [min_eq_left hb.le] using hx.1
  dsimp only
  rw [abs_of_pos hx0]

/-- The logarithmic kernel is square integrable on every bounded interval. -/
theorem intervalIntegrable_log_sq (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => (Real.log x)^2) volume a b := by
  have hb := ((intervalIntegrable_abs_rpow (a := a) (b := b)
    (r := 1/2) (by norm_num)).add
    (intervalIntegrable_abs_rpow (a := a) (b := b) (r := -1/2) (by norm_num))).const_mul 16
  apply hb.mono_fun' ((Real.measurable_log.pow_const 2).aestronglyMeasurable)
  apply ae_of_all
  intro x
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Real.log x)), Real.log_abs] using
    log_sq_le_rpow_bound (abs_nonneg x)

theorem integrableOn_log_sq (a b : ℝ) :
    IntegrableOn (fun x : ℝ => (Real.log x)^2) (Icc a b) := by
  by_cases hab : a ≤ b
  · exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp (intervalIntegrable_log_sq a b)
  · simp [Icc_eq_empty_of_lt (lt_of_not_ge hab)]

theorem integrableOn_log_sub_sq (a b c : ℝ) :
    IntegrableOn (fun x : ℝ => (Real.log (x-c))^2) (Icc a b) := by
  by_cases hab : a ≤ b
  · apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp
    simpa only [sub_add_cancel] using
      (intervalIntegrable_log_sq (a-c) (b-c)).comp_sub_right c
  · simp [Icc_eq_empty_of_lt (lt_of_not_ge hab)]

/-- Translating the singularity within `[-1,1]` leaves a common square-integral
bound on `[-2,2]`. -/
theorem integral_log_sub_sq_le {c : ℝ} (hc : c ∈ Icc (-1 : ℝ) 1) :
    (∫ x in Icc (-2 : ℝ) 2, (Real.log (x-c))^2) ≤
      ∫ x in Icc (-3 : ℝ) 3, (Real.log x)^2 := by
  have heq : (∫ x in Icc (-2 : ℝ) 2, (Real.log (x-c))^2) =
      ∫ x in Icc (-2-c) (2-c), (Real.log x)^2 := by
    rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (show (-2 : ℝ) ≤ 2 by norm_num),
      ← intervalIntegral.integral_of_le (show -2-c ≤ 2-c by linarith)]
    exact intervalIntegral.integral_comp_sub_right (fun x : ℝ => (Real.log x)^2) c
  rw [heq]
  apply setIntegral_mono_set (integrableOn_log_sq (-3) 3)
    (ae_of_all _ fun x => sq_nonneg _) (ae_of_all _ fun x hx => ?_)
  exact ⟨by linarith [hc.2, hx.1], by linarith [hc.1, hx.2]⟩

end TaoAdditive1132
end
end SourceErdos1132_Additive_LogSquare

/- Erdos1132.Additive.PotentialL2 -/
section SourceErdos1132_Additive_PotentialL2
/- # A uniform square-integral bound for empirical logarithmic potentials

Main paper: §4, local potential and differentiation estimates.
-/

noncomputable section
open MeasureTheory Set Polynomial Finset
open scoped BigOperators
namespace TaoAdditive1132.Nodes
variable {n : ℕ} (X : TaoAdditive1132.Nodes n)

def empiricalLogPotential (x : ℝ) : ℝ :=
  -(∑ i, Real.log (x-X.point i)) / n

theorem empiricalLogPotential_eq_realLogPotential {x : ℝ}
    (hx : ∀ i, x ≠ X.point i) : X.empiricalLogPotential x = X.realLogPotential x := by
  unfold empiricalLogPotential realLogPotential
  rw [Real.log_abs]
  congr 2
  unfold nodePolynomial Lagrange.nodal
  simp only [eval_prod, eval_sub, eval_X, eval_C]
  exact (Real.log_prod (fun i _ => sub_ne_zero.mpr (hx i))).symm

theorem ae_empiricalLogPotential_eq_realLogPotential :
    X.empiricalLogPotential =ᵐ[volume] X.realLogPotential := by
  have havoid : ∀ᵐ x : ℝ, x ∉ Set.range X.point := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using
      (Set.finite_range X.point).measure_zero volume
  filter_upwards [havoid] with x hx
  exact X.empiricalLogPotential_eq_realLogPotential
    (fun i hi => hx ⟨i, hi.symm⟩)

theorem measurable_empiricalLogPotential : Measurable X.empiricalLogPotential := by
  unfold empiricalLogPotential
  exact ((Finset.measurable_sum _ fun i _ =>
    Real.measurable_log.comp (measurable_id.sub measurable_const)).neg).div_const _

theorem empiricalLogPotential_sq_le (hn : 0 < n) (x : ℝ) :
    (X.empiricalLogPotential x)^2 ≤ (∑ i, (Real.log (x-X.point i))^2) / n := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hcs := sum_mul_sq_le_sq_mul_sq univ
    (fun i : Fin n => Real.log (x-X.point i)) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one] at hcs
  unfold empiricalLogPotential
  rw [div_pow, neg_sq]
  apply (div_le_div_iff₀ (sq_pos_of_pos hnR) hnR).mpr
  nlinarith

theorem integrableOn_empiricalLogPotential (a b : ℝ) :
    IntegrableOn X.empiricalLogPotential (Set.Icc a b) := by
  by_cases hab : a ≤ b
  · have hi (i : Fin n) : IntegrableOn (fun x => Real.log (x-X.point i)) (Set.Icc a b) := by
      apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp
      simpa only [sub_add_cancel] using
        (intervalIntegral.intervalIntegrable_log' (a := a-X.point i) (b := b-X.point i)).comp_sub_right (X.point i)
    exact ((integrable_finsetSum _ fun i _ => hi i).neg).div_const _
  · simp [Set.Icc_eq_empty_of_lt (lt_of_not_ge hab)]

theorem integrableOn_empiricalLogPotential_sq (hn : 0 < n) (a b : ℝ) :
    IntegrableOn (fun x => (X.empiricalLogPotential x)^2) (Set.Icc a b) := by
  have hi : IntegrableOn (fun x => (∑ i, (Real.log (x-X.point i))^2) / n) (Set.Icc a b) :=
    (integrable_finsetSum _ (fun i _ => integrableOn_log_sub_sq a b (X.point i))).div_const _
  apply hi.mono' ((X.measurable_empiricalLogPotential.pow_const 2).aestronglyMeasurable)
  apply ae_of_all
  intro x
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (X.empiricalLogPotential x))] using
    X.empiricalLogPotential_sq_le hn x

/-- The square-integral bound is independent of the row size and of the node
positions in `[-1,1]`. -/
theorem integral_empiricalLogPotential_sq_le (hn : 0 < n) :
    (∫ x in Set.Icc (-2 : ℝ) 2, (X.empiricalLogPotential x)^2) ≤
      ∫ x in Set.Icc (-3 : ℝ) 3, (Real.log x)^2 := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hi (i : Fin n) := integrableOn_log_sub_sq (-2) 2 (X.point i)
  calc
    _ ≤ ∫ x in Set.Icc (-2 : ℝ) 2, (∑ i, (Real.log (x-X.point i))^2) / n :=
      integral_mono (X.integrableOn_empiricalLogPotential_sq hn _ _)
        ((integrable_finsetSum _ (fun i _ => hi i)).div_const _) (X.empiricalLogPotential_sq_le hn)
    _ = (∑ i, ∫ x in Set.Icc (-2 : ℝ) 2, (Real.log (x-X.point i))^2) / n := by
      rw [integral_div, integral_finsetSum _ (fun i _ => hi i)]
    _ ≤ (∑ _i : Fin n, ∫ x in Set.Icc (-3 : ℝ) 3, (Real.log x)^2) / n := by
      apply div_le_div_of_nonneg_right _ hnR.le
      exact sum_le_sum (fun i _ => integral_log_sub_sq_le (X.mem_interval i))
    _ = _ := by simp [hnR.ne']

end TaoAdditive1132.Nodes
end
end SourceErdos1132_Additive_PotentialL2

/- Erdos1132.Additive.PoissonPotential -/
section SourceErdos1132_Additive_PoissonPotential
/- # Exact Poisson representation of empirical logarithmic potentials

Main paper: §4, local potential and differentiation estimates.
-/

noncomputable section
open MeasureTheory Set Finset Complex
open scoped BigOperators
namespace TaoAdditive1132.Nodes
variable {n : ℕ} (X : TaoAdditive1132.Nodes n)

/-- The logarithmic potential at a complex point in Cartesian coordinates. -/
def complexLogPotential (x h : ℝ) : ℝ :=
  -(∑ i, Real.log ‖((x-X.point i : ℝ) : ℂ)+h*I‖) / n

theorem integrable_poisson_empiricalLogPotential {h : ℝ} (hh : 0 < h) (x : ℝ) :
    Integrable (fun y => poissonKernel h (y-x) * X.empiricalLogPotential y) := by
  have hi := ((integrable_finsetSum Finset.univ
    (fun i _ => integrable_poisson_log hh x (X.point i))).neg).div_const (n : ℝ)
  convert hi using 1
  funext y
  simp only [empiricalLogPotential, ← mul_div_assoc, mul_neg, Finset.mul_sum, Pi.neg_apply]

theorem poisson_empiricalLogPotential {h : ℝ} (hh : 0 < h) (x : ℝ) :
    (∫ y, poissonKernel h (y-x) * X.empiricalLogPotential y) =
      X.complexLogPotential x h := by
  simp_rw [empiricalLogPotential, ← mul_div_assoc, mul_neg, Finset.mul_sum]
  rw [integral_div, integral_neg, integral_finsetSum _
    (fun i _ => integrable_poisson_log hh x (X.point i))]
  simp only [integral_poisson_log hh, complexLogPotential]

theorem integrable_poisson_potential_sub {h : ℝ} (hh : 0 < h) (x α : ℝ) :
    Integrable (fun y => poissonKernel h (y-x) * (X.empiricalLogPotential y-α)) := by
  simpa only [mul_sub, Pi.sub_apply] using! (X.integrable_poisson_empiricalLogPotential hh x).sub
    (((integrable_poissonKernel hh.le).comp_sub_right x).mul_const α)

/-- Centering the Poisson formula at any real normalization constant. -/
theorem poisson_potential_sub {h : ℝ} (hh : 0 < h) (x α : ℝ) :
    X.complexLogPotential x h = α +
      ∫ y, poissonKernel h (y-x) * (X.empiricalLogPotential y-α) := by
  simp_rw [mul_sub]
  rw [integral_sub (X.integrable_poisson_empiricalLogPotential hh x)
    (((integrable_poissonKernel hh.le).comp_sub_right x).mul_const α),
    X.poisson_empiricalLogPotential hh, integral_mul_const,
    integral_sub_right_eq_self, integral_poissonKernel hh]
  ring

theorem complexLogPotential_eq_polynomial {h : ℝ} (hh : 0 < h) (x : ℝ) :
    X.complexLogPotential x h =
      -Real.log ‖X.nodePolynomial.eval₂ (algebraMap ℝ ℂ) ((x : ℂ)+h*I)‖ / n := by
  have hnz (i : Fin n) : ((x-X.point i : ℝ) : ℂ)+h*I ≠ 0 := by
    intro he
    have hi := congrArg Complex.im he
    simp at hi
    exact hh.ne' hi
  have he : X.nodePolynomial.eval₂ (algebraMap ℝ ℂ) ((x : ℂ)+h*I) =
      ∏ i, (((x-X.point i : ℝ) : ℂ)+h*I) := by
    simp only [nodePolynomial, Lagrange.nodal, Polynomial.eval₂_finsetProd,
      Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C]
    apply Finset.prod_congr rfl
    intro i _
    change (x : ℂ)+h*I-(X.point i : ℂ) = ((x-X.point i : ℝ) : ℂ)+h*I
    push_cast
    ring
  rw [he, norm_prod, Real.log_prod (fun i _ => norm_ne_zero_iff.mpr (hnz i))]
  rfl

end TaoAdditive1132.Nodes
end
end SourceErdos1132_Additive_PoissonPotential

/- Erdos1132.Additive.AveragedPoisson -/
section SourceErdos1132_Additive_AveragedPoisson
/- # Averaging the Poisson kernel between two comparable heights

Main paper: §4, local potential and differentiation estimates.
-/

noncomputable section
open MeasureTheory Set Real Filter Complex
namespace TaoAdditive1132

def averagedPoissonKernel (h t : ℝ) : ℝ :=
  (∫ s in Icc h (2*h), poissonKernel s t)/h

theorem integrable_averagedPoisson_product {h : ℝ} (hh : 0 < h) :
    Integrable (fun p : ℝ × ℝ => poissonKernel p.1 p.2)
      ((volume.restrict (Icc h (2*h))).prod volume) := by
  apply (integrable_prod_iff measurable_poissonKernel.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact integrable_poissonKernel (hh.trans_le hs.1).le
  · apply (integrable_const (1 : ℝ)).congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    simp only [Real.norm_eq_abs, abs_of_pos (poissonKernel_pos (hh.trans_le hs.1) _),
      integral_poissonKernel (hh.trans_le hs.1)]

theorem integrable_averagedPoissonKernel {h : ℝ} (hh : 0 < h) :
    Integrable (averagedPoissonKernel h) :=
  (integrable_averagedPoisson_product hh).integral_prod_right.div_const h

theorem averagedPoissonKernel_nonneg {h : ℝ} (hh : 0 < h) (t : ℝ) :
    0 ≤ averagedPoissonKernel h t := by
  apply div_nonneg _ hh.le
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  exact (poissonKernel_pos (hh.trans_le hs.1) _).le

theorem averagedPoissonKernel_neg (h t : ℝ) :
    averagedPoissonKernel h (-t) = averagedPoissonKernel h t := by
  simp only [averagedPoissonKernel, poissonKernel_neg]

theorem integral_averagedPoissonKernel {h : ℝ} (hh : 0 < h) :
    (∫ t, averagedPoissonKernel h t) = 1 := by
  unfold averagedPoissonKernel
  rw [integral_div, ← integral_integral_swap (integrable_averagedPoisson_product hh)]
  have he : (∫ s in Icc h (2*h), ∫ t, poissonKernel s t) = h := by
    calc
      _ = ∫ _s in Icc h (2*h), (1 : ℝ) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
        exact integral_poissonKernel (hh.trans_le hs.1)
      _ = h := by simp [Measure.real, Real.volume_Icc, show 2*h-h = h by ring, hh.le]
  rw [he, div_self hh.ne']

theorem averagedPoissonKernel_operator {h : ℝ} (hh : 0 < h)
    {f : ℝ → ℝ} (hf : Measurable f) {M : ℝ} (hM : ∀ t, |f t| ≤ M) :
    (∫ t, averagedPoissonKernel h t*f t) =
      (∫ s in Icc h (2*h), ∫ t, poissonKernel s t*f t)/h := by
  have hbase := integrable_averagedPoisson_product hh
  have hi : Integrable (fun p : ℝ × ℝ => poissonKernel p.1 p.2*f p.2)
      ((volume.restrict (Icc h (2*h))).prod volume) :=
    hbase.mul_bdd (hf.comp measurable_snd).aestronglyMeasurable (ae_of_all _ (fun p => hM p.2))
  have he (t : ℝ) : averagedPoissonKernel h t*f t =
      (∫ s in Icc h (2*h), poissonKernel s t*f t)/h := by
    rw [integral_mul_const, averagedPoissonKernel]
    ring
  simp_rw [he]
  rw [integral_div, ← integral_integral_swap hi]

theorem averagedPoissonKernel_setIntegral {h : ℝ} (hh : 0 < h)
    {E : Set ℝ} (hE : MeasurableSet E) :
    (∫ t in E, averagedPoissonKernel h t) =
      (∫ s in Icc h (2*h), ∫ t in E, poissonKernel s t)/h := by
  have he := averagedPoissonKernel_operator hh (measurable_const.indicator hE)
    (M := 1) (f := E.indicator (fun _ => 1)) (fun t => by by_cases ht : t ∈ E <;> simp [ht])
  have hid (g : ℝ → ℝ) : (fun t => g t*E.indicator (fun _ => 1) t) = E.indicator g := by
    ext t
    by_cases ht : t ∈ E <;> simp [ht]
  simp_rw [hid, integral_indicator hE] at he
  exact he

theorem averagedPoissonKernel_tail {h δ : ℝ} (hh : 0 < h) (hδ : 0 < δ) :
    (∫ t in (Icc (-δ) δ)ᶜ, averagedPoissonKernel h t) ≤ 4*h/(Real.pi*δ) := by
  rw [averagedPoissonKernel_setIntegral hh measurableSet_Icc.compl]
  have hi := (integrable_averagedPoisson_product hh).mono_measure
    (μ := (volume.restrict (Icc h (2*h))).prod (volume.restrict (Icc (-δ) δ)ᶜ))
    (Measure.prod_mono le_rfl Measure.restrict_le_self)
  have hmono : (∫ s in Icc h (2*h), ∫ t in (Icc (-δ) δ)ᶜ, poissonKernel s t) ≤
      ∫ _s in Icc h (2*h), 4*h/(Real.pi*δ) := by
    apply setIntegral_mono_on hi.integral_prod_left (integrable_const _) measurableSet_Icc
    intro s hs
    exact (poissonKernel_tail_bound (hh.trans_le hs.1) hδ).trans
      (div_le_div_of_nonneg_right (by linarith [hs.2]) (mul_pos Real.pi_pos hδ).le)
  apply (div_le_iff₀ hh).mpr
  have he : (∫ _s in Icc h (2*h), 4*h/(Real.pi*δ)) = h*(4*h/(Real.pi*δ)) := by
    simp [Measure.real, Real.volume_Icc, show 2*h-h = h by ring, hh.le]
  rw [he] at hmono
  nlinarith

/-- The averaged kernel is exactly a difference of logarithmic potentials. -/
theorem averagedPoissonKernel_log {h : ℝ} (hh : 0 < h) (t : ℝ) :
    averagedPoissonKernel h t =
      (Real.log ‖(t : ℂ)+(2*h : ℝ)*I‖-Real.log ‖(t : ℂ)+h*I‖)/(Real.pi*h) := by
  have hd (s : ℝ) (hs : s ∈ Icc h (2*h)) :
      HasDerivAt (fun u => Real.log (t^2+u^2)/(2*Real.pi)) (poissonKernel s t) s := by
    have hs0 := hh.trans_le hs.1
    convert! ((((hasDerivAt_id s).pow 2).const_add (t^2)).log
      (by positivity : t^2+s^2 ≠ 0)).div_const (2*Real.pi) using 1
    unfold poissonKernel
    dsimp
    field_simp
  have hc : ContinuousOn (fun s => poissonKernel s t) (Icc h (2*h)) := by
    apply continuousOn_id.div (by fun_prop)
    intro s hs
    have hs0 := hh.trans_le hs.1
    positivity
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => hd s (by simpa only [uIcc_of_le (by linarith : h ≤ 2*h)] using hs))
    (hc.intervalIntegrable_of_Icc (by linarith))
  have hlog (s : ℝ) : Real.log (t^2+s^2) = 2*Real.log ‖(t : ℂ)+(s : ℝ)*I‖ := by
    have hs : ‖(t : ℂ)+(s : ℝ)*I‖^2 = t^2+s^2 := by
      rw [← Complex.normSq_eq_norm_sq]
      simp [Complex.normSq_apply, pow_two]
    rw [← hs, Real.log_pow]
    norm_num
  unfold averagedPoissonKernel
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : h ≤ 2*h), he]
  simp_rw [hlog]
  field_simp

end TaoAdditive1132
end
end SourceErdos1132_Additive_AveragedPoisson

/- Erdos1132.Additive.AveragedQuadrature -/
section SourceErdos1132_Additive_AveragedQuadrature
/- # Approximation of node averages by differences of complex potentials

Main paper: §4, local potential and differentiation estimates.
-/

noncomputable section
open MeasureTheory Set Finset Real Complex
open scoped BigOperators
namespace TaoAdditive1132

theorem averagedPoisson_convolution_bound {h δ M L : ℝ} (hh : 0 < h) (hδ : 0 < δ)
    {f : ℝ → ℝ} (hf : Measurable f) (hM : ∀ t, |f t| ≤ M) (hL : 0 ≤ L)
    (hlip : ∀ s t, |f s-f t| ≤ L*|s-t|) (x : ℝ) :
    |(∫ y, averagedPoissonKernel h (y-x)*f y)-f x| ≤ L*δ+8*M*h/(Real.pi*δ) := by
  have hM0 := (abs_nonneg (f 0)).trans (hM 0)
  have hft : Measurable (fun t => f (x-t)) := hf.comp (measurable_const.sub measurable_id)
  have hb := probability_kernel_lipschitz_bound (averagedPoissonKernel_nonneg hh)
    (integrable_averagedPoissonKernel hh) (integral_averagedPoissonKernel hh)
    hft (fun t => hM (x-t)) hL hδ
    (fun t => by simpa only [sub_zero, sub_sub_cancel_left, abs_neg] using hlip (x-t) x)
  simp only [sub_zero] at hb
  have he : (∫ y, averagedPoissonKernel h (y-x)*f y) =
      ∫ t, averagedPoissonKernel h t*f (x-t) := by
    have he := integral_sub_left_eq_self
      (f := fun y => averagedPoissonKernel h (y-x)*f y) volume x
    simp only [sub_sub_cancel_left, averagedPoissonKernel_neg] at he
    exact he.symm
  rw [he]
  have htail := mul_le_mul_of_nonneg_left (averagedPoissonKernel_tail hh hδ)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hM0)
  have hb' := hb.trans (add_le_add_right htail (L*δ))
  convert! hb' using 1 <;> ring

namespace Nodes
variable {n : ℕ} (X : Nodes n)

theorem averaged_node_kernel_identity {h : ℝ} (hh : 0 < h) (x : ℝ) :
    (∑ i, averagedPoissonKernel h (x-X.point i))/(n : ℝ) =
      (X.complexLogPotential x h-X.complexLogPotential x (2*h))/(Real.pi*h) := by
  simp_rw [averagedPoissonKernel_log hh]
  unfold complexLogPotential
  rw [← Finset.sum_div, Finset.sum_sub_distrib]
  ring

theorem integrable_averaged_node_kernel_mul {h : ℝ} (hh : 0 < h)
    {f : ℝ → ℝ} (hf : Measurable f) {M : ℝ} (hM : ∀ y, |f y| ≤ M) :
    Integrable (fun y =>
      ((X.complexLogPotential y h-X.complexLogPotential y (2*h))/(Real.pi*h))*f y) := by
  have hi (i : Fin n) : Integrable (fun y => averagedPoissonKernel h (y-X.point i)*f y) :=
    ((integrable_averagedPoissonKernel hh).comp_sub_right (X.point i)).mul_bdd
      hf.aestronglyMeasurable (ae_of_all _ hM)
  have hs := (integrable_finsetSum Finset.univ (fun i _ => hi i)).div_const (n : ℝ)
  convert! hs using 1
  ext y
  rw [← X.averaged_node_kernel_identity hh]
  rw [div_mul_eq_mul_div, Finset.sum_mul]

theorem averaged_node_quadrature_bound (hn : 0 < n) {h δ M L : ℝ}
    (hh : 0 < h) (hδ : 0 < δ) {f : ℝ → ℝ} (hf : Measurable f)
    (hM : ∀ y, |f y| ≤ M) (hL : 0 ≤ L) (hlip : ∀ s t, |f s-f t| ≤ L*|s-t|) :
    |(∑ i, f (X.point i))/(n : ℝ) -
      ∫ y, ((X.complexLogPotential y h-X.complexLogPotential y (2*h))/(Real.pi*h))*f y| ≤
      L*δ+8*M*h/(Real.pi*δ) := by
  have hi (i : Fin n) : Integrable (fun y => averagedPoissonKernel h (y-X.point i)*f y) :=
    ((integrable_averagedPoissonKernel hh).comp_sub_right (X.point i)).mul_bdd
      hf.aestronglyMeasurable (ae_of_all _ hM)
  have he : (∫ y, ((X.complexLogPotential y h-X.complexLogPotential y (2*h))/(Real.pi*h))*f y) =
      (∑ i, ∫ y, averagedPoissonKernel h (y-X.point i)*f y)/(n : ℝ) := by
    simp_rw [← X.averaged_node_kernel_identity hh, div_mul_eq_mul_div, Finset.sum_mul]
    rw [integral_div, integral_finsetSum _ (fun i _ => hi i)]
  rw [he, ← sub_div, ← Finset.sum_sub_distrib, abs_div,
    abs_of_pos (by exact_mod_cast hn : 0 < (n : ℝ))]
  apply (div_le_iff₀ (by exact_mod_cast hn : 0 < (n : ℝ))).mpr
  calc
    _ ≤ ∑ i, |f (X.point i)-(∫ y, averagedPoissonKernel h (y-X.point i)*f y)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, (L*δ+8*M*h/(Real.pi*δ)) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_sub_comm]
      exact averagedPoisson_convolution_bound hh hδ hf hM hL hlip (X.point i)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end Nodes
end TaoAdditive1132
end
end SourceErdos1132_Additive_AveragedQuadrature

/- Erdos1132.Additive.ExteriorKernel -/
section SourceErdos1132_Additive_ExteriorKernel
/- # Bounds for the exterior Poisson kernel separated from an interval

Main paper: §4, local potential and differentiation estimates.
-/

noncomputable section
open Set Real
namespace TaoAdditive1132

/-- A uniform comparison coefficient against the Cauchy kernel at the origin. -/
def exteriorKernelBound (d : ℝ) : ℝ := Real.pi*(2+3/d^2)

theorem exteriorKernelBound_pos {d : ℝ} (hd : 0 < d) : 0 < exteriorKernelBound d := by
  unfold exteriorKernelBound
  positivity

theorem distance_compl_interval {a b d x y : ℝ} (hx : x ∈ Icc (a+d) (b-d))
    (hy : y ∉ Icc a b) : d ≤ |y-x| := by
  rcases not_and_or.mp hy with hya | hyb
  · have hya' : y < a := lt_of_not_ge hya
    have ht := neg_le_abs (y-x)
    linarith [hx.1]
  · have hyb' : b < y := lt_of_not_ge hyb
    have ht := le_abs_self (y-x)
    linarith [hx.2]

theorem exteriorKernel_le_cauchy {d x y : ℝ} (hd : 0 < d)
    (hx : |x| ≤ 1) (hsep : d ≤ |y-x|) (h : ℝ) :
    1/((y-x)^2+h^2) ≤ exteriorKernelBound d * poissonKernel 1 y := by
  have hd2 : 0 < d^2 := sq_pos_of_pos hd
  have hdist : d^2 ≤ (y-x)^2 := by nlinarith [sq_abs (y-x)]
  have hden : 0 < (y-x)^2+h^2 := by nlinarith [sq_nonneg h]
  have hx2 : x^2 ≤ 1 := by nlinarith [sq_abs x, abs_nonneg x]
  have hy2 : y^2+1 ≤ 2*(y-x)^2+3 := by nlinarith [sq_nonneg (y-2*x)]
  have hp : d^2*(y^2+1) ≤ (2*d^2+3)*((y-x)^2+h^2) := by
    have hmul := mul_le_mul_of_nonneg_left hy2 hd2.le
    nlinarith [sq_nonneg h, mul_nonneg hd2.le (sq_nonneg h)]
  unfold exteriorKernelBound poissonKernel
  norm_num only [one_pow]
  field_simp
  nlinarith [Real.pi_pos, mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hp)]

theorem exteriorKernel_height_difference {d t h : ℝ} (hd : 0 < d)
    (ht : d ≤ |t|) :
    |1/(t^2+h^2)-1/t^2| ≤ (h^2/d^2)*(1/t^2) := by
  have ht2 : 0 < t^2 := by nlinarith [sq_abs t]
  have ht0 : t ≠ 0 := by intro he; simp [he] at ht2
  have hd2 : 0 < d^2 := sq_pos_of_pos hd
  have hden : 0 < t^2+h^2 := by positivity
  have hdle : d^2 ≤ t^2+h^2 := by nlinarith [sq_abs t, sq_nonneg h]
  have hnonpos : 1/(t^2+h^2)-1/t^2 ≤ 0 := by
    apply sub_nonpos.mpr
    exact one_div_le_one_div_of_le ht2 (by nlinarith [sq_nonneg h])
  rw [abs_of_nonpos hnonpos]
  have he : -(1/(t^2+h^2)-1/t^2) = (h^2/(t^2+h^2))*(1/t^2) := by
    field_simp [ht0]
    ring
  rw [he]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact div_le_div_of_nonneg_left (sq_nonneg h) hd2 hdle

theorem exteriorKernel_horizontal_difference {d s t : ℝ} (hd : 0 < d)
    (hs : d ≤ |s|) (ht : d ≤ |t|) :
    |1/s^2-1/t^2| ≤ (|s-t|/d)*(1/s^2+1/t^2) := by
  have hs0 : s ≠ 0 := by intro he; simp [he] at hs; linarith
  have ht0 : t ≠ 0 := by intro he; simp [he] at ht; linarith
  have he : |1/s^2-1/t^2| = |s-t| *|s+t|/(s^2*t^2) := by
    rw [div_sub_div _ _ (pow_ne_zero 2 hs0) (pow_ne_zero 2 ht0)]
    rw [abs_div, abs_of_pos (mul_pos (sq_pos_of_ne_zero hs0) (sq_pos_of_ne_zero ht0))]
    congr 1
    simp only [one_mul, mul_one]
    rw [show t^2-s^2 = -(s-t)*(s+t) by ring, abs_mul, abs_neg]
  rw [he]
  have hsum : d*|s+t| ≤ s^2+t^2 := by
    have ha := abs_add_le s t
    have h1 := mul_le_mul_of_nonneg_right hs (abs_nonneg s)
    have h2 := mul_le_mul_of_nonneg_right ht (abs_nonneg t)
    have h3 := mul_le_mul_of_nonneg_left ha hd.le
    nlinarith [sq_abs s, sq_abs t]
  apply (div_le_iff₀ (mul_pos (sq_pos_of_ne_zero hs0) (sq_pos_of_ne_zero ht0))).mpr
  have hre : (|s-t|/d)*(1/s^2+1/t^2)*(s^2*t^2) = |s-t|/d*(s^2+t^2) := by
    field_simp
    ring
  rw [hre, div_mul_eq_mul_div]
  apply (le_div_iff₀ hd).mpr
  nlinarith [mul_le_mul_of_nonneg_left hsum (abs_nonneg (s-t))]

end TaoAdditive1132
end
end SourceErdos1132_Additive_ExteriorKernel

/- Erdos1132.Additive.SecondMoment -/
section SourceErdos1132_Additive_SecondMoment
/- # Second moments and recurrence of measurable sets

Main paper: §6, recurrence and Theorem 1(i).
-/

noncomputable section
open MeasureTheory Set Filter Finset
open scoped BigOperators ENNReal Topology
namespace TaoAdditive1132

/-- Cauchy--Schwarz against the constant function, written without square roots. -/
theorem integral_sq_le_mass_mul_integral_sq {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {f : α → ℝ}
    (hf : Integrable f μ) (hf2 : Integrable (fun x => (f x)^2) μ) :
    (∫ x, f x ∂μ)^2 ≤ μ.real univ * ∫ x, (f x)^2 ∂μ := by
  let m := μ.real univ
  let S := ∫ x, f x ∂μ
  have hm : 0 ≤ m := ENNReal.toReal_nonneg
  by_cases hm0 : m = 0
  · have hμ : μ = 0 := by
      apply Measure.measure_univ_eq_zero.mp
      exact (ENNReal.toReal_eq_zero_iff (μ univ) |>.mp hm0).resolve_right (measure_ne_top μ univ)
    simp [hμ]
  have hmpos : 0 < m := lt_of_le_of_ne hm (Ne.symm hm0)
  have heq (x : α) : (m*f x-S)^2 = m^2*(f x)^2 - (2*m*S)*f x + S^2 := by ring
  have hnonneg : 0 ≤ ∫ x, (m*f x-S)^2 ∂μ := integral_nonneg (fun x => sq_nonneg _)
  simp_rw [heq] at hnonneg
  have hi1 : Integrable (fun x => m^2*(f x)^2) μ := hf2.const_mul _
  have hi2 : Integrable (fun x => (2*m*S)*f x) μ := hf.const_mul _
  have hi3 : Integrable (fun x => m^2*(f x)^2 - (2*m*S)*f x) μ := hi1.sub hi2
  rw [integral_add hi3 (integrable_const (S^2)),
    integral_sub hi1 hi2, integral_const_mul,
    integral_const_mul, integral_const] at hnonneg
  change 0 ≤ m^2 * (∫ x, (f x)^2 ∂μ) - (2*m*S)*S + m*S^2 at hnonneg
  have hprod : 0 ≤ m * (m * (∫ x, (f x)^2 ∂μ) - S^2) := by nlinarith
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right hprod hmpos)

def eventCount {α ι : Type*} (s : Finset ι) (A : ι → Set α) (x : α) : ℝ :=
  ∑ i ∈ s, (A i).indicator (fun _ => (1 : ℝ)) x

theorem eventCount_sq {α ι : Type*} (s : Finset ι) (A : ι → Set α) (x : α) :
    (eventCount s A x)^2 =
      ∑ i ∈ s, ∑ j ∈ s, (A i ∩ A j).indicator (fun _ => (1 : ℝ)) x := by
  rw [eventCount, pow_two, sum_mul]
  apply sum_congr rfl
  intro i hi
  rw [mul_sum]
  apply sum_congr rfl
  intro j hj
  by_cases hx : x ∈ A i <;> by_cases hy : x ∈ A j <;> simp [hx, hy]

theorem integrable_eventCount {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (s : Finset ι) (A : ι → Set α)
    (hA : ∀ i ∈ s, MeasurableSet (A i)) : Integrable (eventCount s A) μ := by
  apply integrable_finsetSum
  intro i hi
  exact (integrable_const _).indicator (hA i hi)

theorem integral_eventCount {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (s : Finset ι) (A : ι → Set α)
    (hA : ∀ i ∈ s, MeasurableSet (A i)) :
    (∫ x, eventCount s A x ∂μ) = ∑ i ∈ s, μ.real (A i) := by
  unfold eventCount
  rw [integral_finsetSum s (fun i hi => (integrable_const _).indicator (hA i hi))]
  apply sum_congr rfl
  intro i hi
  simp [integral_indicator_const, hA i hi]

theorem integrable_eventCount_sq {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (s : Finset ι) (A : ι → Set α)
    (hA : ∀ i ∈ s, MeasurableSet (A i)) :
    Integrable (fun x => (eventCount s A x)^2) μ := by
  simp_rw [eventCount_sq]
  apply integrable_finsetSum
  intro i hi
  exact integrable_eventCount μ s (fun j => A i ∩ A j)
    (fun j hj => (hA i hi).inter (hA j hj))

theorem integral_eventCount_sq {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (s : Finset ι) (A : ι → Set α)
    (hA : ∀ i ∈ s, MeasurableSet (A i)) :
    (∫ x, (eventCount s A x)^2 ∂μ) = ∑ i ∈ s, ∑ j ∈ s, μ.real (A i ∩ A j) := by
  simp_rw [eventCount_sq]
  change (∫ x, ∑ i ∈ s, eventCount s (fun j => A i ∩ A j) x ∂μ) = _
  rw [integral_finsetSum s (fun i hi => integrable_eventCount μ s
    (fun j => A i ∩ A j) (fun j hj => (hA i hi).inter (hA j hj)))]
  apply sum_congr rfl
  intro i hi
  exact integral_eventCount μ s (fun j => A i ∩ A j)
    (fun j hj => (hA i hi).inter (hA j hj))

/-- A finite family of events occupies at least the mass forced by its first
and second moments. -/
theorem finite_union_second_moment {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (s : Finset ι) (A : ι → Set α)
    (hA : ∀ i ∈ s, MeasurableSet (A i)) :
    (∑ i ∈ s, μ.real (A i))^2 ≤
      μ.real (⋃ i ∈ s, A i) * (∑ i ∈ s, ∑ j ∈ s, μ.real (A i ∩ A j)) := by
  let U := ⋃ i ∈ s, A i
  have hzero (x : α) (hx : x ∉ U) : eventCount s A x = 0 := by
    apply sum_eq_zero
    intro i hi
    have hxi : x ∉ A i := fun hh => hx (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, hh⟩⟩)
    simp [hxi]
  have h := integral_sq_le_mass_mul_integral_sq (μ.restrict U)
    (integrable_eventCount μ s A hA).integrableOn
    (integrable_eventCount_sq μ s A hA).integrableOn
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by rw [hzero x hx]; norm_num),
    integral_eventCount μ s A hA, integral_eventCount_sq μ s A hA] at h
  simpa only [Measure.real, Measure.restrict_apply_univ] using h

/-- A uniform second-moment bound on finite subfamilies of every tail gives
a positive-measure set of points belonging to infinitely many events. -/
theorem measure_frequently_pos_of_second_moment
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (A : ℕ → Set α) (hA : ∀ n, MeasurableSet (A n)) {C : ℝ} (hC : 0 < C)
    (htail : ∀ N : ℕ, ∃ s : Finset ℕ, (∀ n ∈ s, N ≤ n) ∧
      0 < ∑ n ∈ s, μ.real (A n) ∧
      (∑ n ∈ s, ∑ m ∈ s, μ.real (A n ∩ A m)) ≤ C * (∑ n ∈ s, μ.real (A n))^2) :
    0 < μ {x | ∃ᶠ n in atTop, x ∈ A n} := by
  let T (N : ℕ) : Set α := ⋃ n ≥ N, A n
  have hTm (N : ℕ) : MeasurableSet (T N) :=
    MeasurableSet.iUnion (fun n => MeasurableSet.iUnion (fun _ => hA n))
  have hTanti : Antitone T := by
    intro N M hNM x hx
    obtain ⟨n, hn, hx⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion₂.mpr ⟨n, hNM.trans hn, hx⟩
  have hTlower (N : ℕ) : ENNReal.ofReal (1/C) ≤ μ (T N) := by
    obtain ⟨s, hs, hsum, hsecond⟩ := htail N
    have hm := finite_union_second_moment μ s A (fun n _ => hA n)
    have hmass : 0 ≤ μ.real (⋃ n ∈ s, A n) := ENNReal.toReal_nonneg
    have hbound := hm.trans (mul_le_mul_of_nonneg_left hsecond hmass)
    have hmul : 1 ≤ μ.real (⋃ n ∈ s, A n) * C := by
      apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hsum)).mp
      nlinarith only [hbound]
    have hdiv : 1/C ≤ μ.real (⋃ n ∈ s, A n) := (div_le_iff₀ hC).mpr hmul
    have hsub : (⋃ n ∈ s, A n) ⊆ T N := by
      intro x hx
      obtain ⟨n, hn, hx⟩ := mem_iUnion₂.mp hx
      exact mem_iUnion₂.mpr ⟨n, hs n hn, hx⟩
    exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top μ _)).mpr
      (hdiv.trans (measureReal_mono hsub (measure_ne_top μ _)))
  have hfreq : {x | ∃ᶠ n in atTop, x ∈ A n} = ⋂ N, T N := by
    ext x
    simp only [mem_ofPred_eq, frequently_atTop, mem_iInter, T, mem_iUnion, exists_prop]
  rw [hfreq, hTanti.measure_iInter (fun N => (hTm N).nullMeasurableSet)
    ⟨0, measure_ne_top μ _⟩]
  exact (ENNReal.ofReal_pos.mpr (one_div_pos.mpr hC)).trans_le (le_iInf hTlower)

end TaoAdditive1132
end
end SourceErdos1132_Additive_SecondMoment

/- Erdos1132.Additive.PotentialNormalization -/
section SourceErdos1132_Additive_PotentialNormalization
/- # Bounds on the normalization and on small-set logarithmic integrals

Main paper: §4, local potential and differentiation estimates.
-/

noncomputable section
open MeasureTheory Set Filter Finset
open scoped BigOperators
namespace TaoAdditive1132

/-- The common square-integral bound for probability averages of logarithms
with poles in the interpolation interval. -/
def logSquareBound : ℝ := ∫ x in Set.Icc (-3 : ℝ) 3, (Real.log x)^2

theorem logSquareBound_nonneg : 0 ≤ logSquareBound :=
  integral_nonneg (fun _x => sq_nonneg _)

namespace Nodes
variable {n : ℕ} (X : Nodes n)

theorem inv_two_pow_le_abs_weight (i : Fin n) : (2 : ℝ)⁻¹^n ≤ |X.weight i| := by
  have hd (j : Fin n) : |X.point i-X.point j| ≤ 2 := by
    have hi := X.mem_interval i
    have hj := X.mem_interval j
    apply abs_le.mpr
    constructor <;> linarith [hi.1, hi.2, hj.1, hj.2]
  have hp : (∏ j ∈ Finset.univ.erase i, |X.point i-X.point j|) ≤ (2 : ℝ)^n := by
    calc
      _ ≤ ∏ _j ∈ Finset.univ.erase i, (2 : ℝ) :=
        Finset.prod_le_prod (fun j _ => abs_nonneg _) (fun j _ => hd j)
      _ = (2 : ℝ)^(n-1) := by simp
      _ ≤ (2 : ℝ)^n := pow_le_pow_right₀ (by norm_num) (Nat.sub_le n 1)
  have hpos : 0 < ∏ j ∈ Finset.univ.erase i, |X.point i-X.point j| := by
    apply Finset.prod_pos
    intro j hj
    apply abs_pos.mpr
    exact sub_ne_zero.mpr (fun he => (Finset.mem_erase.mp hj).1 (X.injective he).symm)
  have he : |X.weight i| = (∏ j ∈ Finset.univ.erase i, |X.point i-X.point j|)⁻¹ := by
    simp only [weight, Lagrange.nodalWeight, abs_prod, abs_inv, Finset.prod_inv_distrib]
  rw [he, inv_pow]
  exact inv_anti₀ hpos hp

theorem potentialNormalization_lower (hn : 0 < n) :
    -Real.log 2 ≤ X.potentialNormalization := by
  let i : Fin n := ⟨0, hn⟩
  have hlow : (2 : ℝ)⁻¹^n ≤ X.totalWeight :=
    (X.inv_two_pow_le_abs_weight i).trans
      (Finset.single_le_sum (fun j _ => abs_nonneg (X.weight j)) (Finset.mem_univ i))
  have hl := Real.log_le_log (by positivity : 0 < (2 : ℝ)⁻¹^n) hlow
  rw [Real.log_pow, Real.log_inv] at hl
  unfold potentialNormalization
  apply (le_div_iff₀ (by exact_mod_cast hn : 0 < (n : ℝ))).mpr
  nlinarith

theorem integral_abs_empiricalLogPotential_le (hn : 0 < n) :
    (∫ x in Set.Icc (-2 : ℝ) 2, |X.empiricalLogPotential x|) ≤
      (4+logSquareBound)/2 := by
  have hf := X.integrableOn_empiricalLogPotential (-2) 2
  have hf2 := X.integrableOn_empiricalLogPotential_sq hn (-2) 2
  have hi : (∫ x in Set.Icc (-2 : ℝ) 2, 2*|X.empiricalLogPotential x|) ≤
      ∫ x in Set.Icc (-2 : ℝ) 2, 1+(X.empiricalLogPotential x)^2 := by
    apply integral_mono (hf.abs.const_mul 2) ((integrable_const 1).add hf2)
    intro x
    change 2*|X.empiricalLogPotential x| ≤ 1+(X.empiricalLogPotential x)^2
    nlinarith [sq_nonneg (|X.empiricalLogPotential x|-1), sq_abs (X.empiricalLogPotential x)]
  rw [integral_const_mul, integral_add (integrable_const 1) hf2, integral_const] at hi
  norm_num [Measure.real, Real.volume_Icc] at hi
  have hsq := X.integral_empiricalLogPotential_sq_le hn
  change _ ≤ logSquareBound at hsq
  linarith

theorem integral_abs_potential_small_set (hn : 0 < n) {s : Set ℝ}
    (hs : s ⊆ Set.Icc (-2) 2) :
    (∫ x in s, |X.empiricalLogPotential x|) ≤
      Real.sqrt (volume.real s * logSquareBound) := by
  have hsfin : volume s ≠ ⊤ := ne_top_of_le_ne_top (by simp) (measure_mono hs)
  have : IsFiniteMeasure (volume.restrict s) := isFiniteMeasure_restrict.mpr hsfin
  have hi := (X.integrableOn_empiricalLogPotential (-2) 2).mono_set hs
  have hi2 := (X.integrableOn_empiricalLogPotential_sq hn (-2) 2).mono_set hs
  have hcs := integral_sq_le_mass_mul_integral_sq (volume.restrict s) hi.abs
    (by simpa only [sq_abs] using! hi2)
  simp only [Measure.real, Measure.restrict_apply_univ, sq_abs] at hcs
  have hb : (∫ x in s, (X.empiricalLogPotential x)^2) ≤ logSquareBound := by
    apply le_trans _ (X.integral_empiricalLogPotential_sq_le hn)
    exact setIntegral_mono_set (X.integrableOn_empiricalLogPotential_sq hn _ _)
      (ae_of_all _ (fun x => sq_nonneg _)) (ae_of_all _ hs)
  apply (Real.le_sqrt (integral_nonneg (fun x => abs_nonneg _))
    (mul_nonneg ENNReal.toReal_nonneg logSquareBound_nonneg)).mpr
  exact hcs.trans (mul_le_mul_of_nonneg_left hb ENNReal.toReal_nonneg)

/-- An intervalwise Lebesgue bound controls the potential normalization with
constants depending only on the interval and its stated upper bound. -/
theorem potentialNormalization_upper (hn : 0 < n) {a b Λ : ℝ}
    (hab : a < b) (hI : Set.Icc a b ⊆ Set.Icc (-1) 1)
    (hΛ : ∀ x ∈ Set.Icc a b, X.lebesgue x ≤ Λ) :
    X.potentialNormalization ≤ Real.log (2*Λ)/n +
      (4+logSquareBound)/(2*(b-a)) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hI2 : Set.Icc a b ⊆ Set.Icc (-2) 2 := by
    intro x hx
    have hx' := hI hx
    constructor <;> linarith [hx'.1, hx'.2]
  have hi := X.integrableOn_empiricalLogPotential a b
  have hlow : ∀ᵐ x ∂volume.restrict (Set.Icc a b),
      X.potentialNormalization - Real.log (2*Λ)/n ≤ X.empiricalLogPotential x := by
    have havoid : ∀ᵐ x : ℝ, x ∉ Set.range X.point := by
      simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using
        (Set.finite_range X.point).measure_zero volume
    filter_upwards [ae_restrict_of_ae havoid, ae_restrict_mem measurableSet_Icc] with x hx hxI
    have hdist : ∀ i, 0 < |x-X.point i| := fun i => abs_pos.mpr
      (sub_ne_zero.mpr (fun he => hx ⟨i, he.symm⟩))
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    let δ := Finset.univ.inf' Finset.univ_nonempty (fun i => |x-X.point i|)
    have hδ : 0 < δ := (Finset.lt_inf'_iff _).mpr (fun i _ => hdist i)
    have hbound := (X.local_potential_bounds hn (hI hxI) hδ
      (fun i => Finset.inf'_le _ (Finset.mem_univ i)) (hΛ x hxI)).1
    rw [X.empiricalLogPotential_eq_realLogPotential (fun i he => hx ⟨i, he.symm⟩)]
    exact hbound
  have hle := integral_mono_ae (integrable_const
    (X.potentialNormalization-Real.log (2*Λ)/n)) hi hlow
  rw [integral_const] at hle
  have hvol : (volume.restrict (Set.Icc a b)).real Set.univ = b-a := by
    simp [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le)]
  change (volume.restrict (Set.Icc a b)).real Set.univ *
    (X.potentialNormalization-Real.log (2*Λ)/n) ≤ _ at hle
  rw [hvol] at hle
  have hupper : (∫ x in Set.Icc a b, X.empiricalLogPotential x) ≤ (4+logSquareBound)/2 := by
    calc
      _ ≤ ∫ x in Set.Icc a b, |X.empiricalLogPotential x| :=
        integral_mono hi hi.abs (fun x => le_abs_self _)
      _ ≤ ∫ x in Set.Icc (-2 : ℝ) 2, |X.empiricalLogPotential x| :=
        setIntegral_mono_set (X.integrableOn_empiricalLogPotential (-2) 2).abs
          (ae_of_all _ (fun x => abs_nonneg _)) (ae_of_all _ hI2)
      _ ≤ _ := X.integral_abs_empiricalLogPotential_le hn
  have hfinal : X.potentialNormalization-Real.log (2*Λ)/n ≤
      ((4+logSquareBound)/2)/(b-a) := (le_div_iff₀ (sub_pos.mpr hab)).mpr (by nlinarith)
  rw [div_div] at hfinal
  linarith

end Nodes
end TaoAdditive1132
end
end SourceErdos1132_Additive_PotentialNormalization

/- Erdos1132.Additive.LocalPoissonEstimate -/
section SourceErdos1132_Additive_LocalPoissonEstimate
/- # Explicit control of the interior contribution to the Poisson integral

Main paper: §4, local potential and differentiation estimates.
-/

noncomputable section
open MeasureTheory Set Filter Finset Real
open scoped BigOperators
namespace TaoAdditive1132

theorem poissonKernel_le_inv_height {h : ℝ} (hh : 0 < h) (t : ℝ) :
    poissonKernel h t ≤ 1/(Real.pi*h) := by
  unfold poissonKernel
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [sq_nonneg t, Real.pi_pos]

namespace Nodes
variable {n : ℕ} (X : Nodes n)

def nodeNeighborhood (δ : ℝ) : Set ℝ :=
  ⋃ i, Set.Ioo (X.point i-δ) (X.point i+δ)

theorem measurableSet_nodeNeighborhood (δ : ℝ) : MeasurableSet (X.nodeNeighborhood δ) :=
  MeasurableSet.iUnion (fun _ => measurableSet_Ioo)

theorem mem_nodeNeighborhood {δ y : ℝ} :
    y ∈ X.nodeNeighborhood δ ↔ ∃ i, |y-X.point i| < δ := by
  simp only [nodeNeighborhood, Set.mem_iUnion, Set.mem_Ioo, abs_lt]
  constructor <;> rintro ⟨i, h1, h2⟩ <;> refine ⟨i, ?_, ?_⟩ <;> linarith

theorem nodeNeighborhood_subset {δ : ℝ} (hδ : δ ≤ 1) :
    X.nodeNeighborhood δ ⊆ Set.Icc (-2) 2 := by
  intro y hy
  obtain ⟨i, hi⟩ := X.mem_nodeNeighborhood.mp hy
  have ha := abs_lt.mp hi
  have hx := X.mem_interval i
  constructor <;> linarith [ha.1, ha.2, hx.1, hx.2]

theorem measureReal_nodeNeighborhood_le {δ : ℝ} (hδ : 0 ≤ δ) :
    volume.real (X.nodeNeighborhood δ) ≤ 2*n*δ := by
  have he (i : Fin n) : volume.real (Set.Ioo (X.point i-δ) (X.point i+δ)) = 2*δ := by
    simp [Measure.real, Real.volume_Ioo, show X.point i+δ-(X.point i-δ) = 2*δ by ring,
      hδ]
  have hb := measureReal_iUnion_fintype_le (μ := volume)
    (fun i => Set.Ioo (X.point i-δ) (X.point i+δ))
  simp_rw [he] at hb
  simpa [nodeNeighborhood, mul_comm, mul_left_comm, mul_assoc] using hb

theorem abs_potential_sub_le_away (hn : 0 < n) {y δ Λ : ℝ}
    (hy : y ∈ Set.Icc (-1) 1) (hδ : 0 < δ)
    (haway : y ∉ X.nodeNeighborhood δ) (hΛ : X.lebesgue y ≤ Λ) :
    |X.empiricalLogPotential y-X.potentialNormalization| ≤
      max (Real.log (2*Λ)) (-Real.log δ)/n := by
  have hdist : ∀ i, δ ≤ |y-X.point i| := by
    intro i
    by_contra he
    exact haway (X.mem_nodeNeighborhood.mpr ⟨i, lt_of_not_ge he⟩)
  have hneq : ∀ i, y ≠ X.point i := by
    intro i he
    have hd := hdist i
    rw [he, sub_self, abs_zero] at hd
    exact hδ.not_ge hd
  rw [X.empiricalLogPotential_eq_realLogPotential hneq]
  have hb := X.local_potential_bounds hn hy hδ hdist hΛ
  have hm1 := div_le_div_of_nonneg_right
    (le_max_left (Real.log (2*Λ)) (-Real.log δ)) (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hm2 := div_le_div_of_nonneg_right
    (le_max_right (Real.log (2*Λ)) (-Real.log δ)) (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  rw [neg_div] at hm2
  apply abs_le.mpr
  constructor <;> linarith

/-- The contribution from the interpolation interval has an explicit error
bound. The exceptional set is the stated union of node neighborhoods. -/
theorem local_poisson_potential_bound (hn : 0 < n) {a b Λ δ h : ℝ}
    (hI : Set.Icc a b ⊆ Set.Icc (-1) 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hh : 0 < h) (hΛ : ∀ y ∈ Set.Icc a b, X.lebesgue y ≤ Λ) (x : ℝ)
    (hΛ1 : 1 ≤ Λ) :
    |∫ y in Set.Icc a b,
      poissonKernel h (y-x) * (X.empiricalLogPotential y-X.potentialNormalization)| ≤
      max (Real.log (2*Λ)) (-Real.log δ)/n +
        (Real.sqrt (2*n*δ*logSquareBound) + |X.potentialNormalization| *(2*n*δ)) /
          (Real.pi*h) := by
  let B := X.nodeNeighborhood δ
  let E := max (Real.log (2*Λ)) (-Real.log δ)/n
  let K := 1/(Real.pi*h)
  let f := fun y => |X.empiricalLogPotential y|+|X.potentialNormalization|
  have hE : 0 ≤ E := by
    apply div_nonneg _ (Nat.cast_nonneg _)
    exact (Real.log_nonneg (by linarith : 1 ≤ 2*Λ)).trans (le_max_left _ _)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hB := X.measurableSet_nodeNeighborhood δ
  have hBs := X.nodeNeighborhood_subset hδ1
  have hBfin : volume B ≠ ⊤ := ne_top_of_le_ne_top (by simp) (measure_mono hBs)
  have : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr hBfin
  have hf : IntegrableOn f B :=
    ((X.integrableOn_empiricalLogPotential (-2) 2).mono_set hBs).abs.add (integrable_const _)
  have hfi : Integrable (B.indicator f) := (integrable_indicator_iff hB).mpr hf
  have hw := (integrable_poissonKernel hh.le).comp_sub_right x
  have hpoint : ∀ y ∈ Set.Icc a b,
      |poissonKernel h (y-x) * (X.empiricalLogPotential y-X.potentialNormalization)| ≤
        E*poissonKernel h (y-x)+K*B.indicator f y := by
    intro y hy
    have hw0 := (poissonKernel_pos hh (y-x)).le
    rw [abs_mul, abs_of_nonneg hw0]
    by_cases hyB : y ∈ B
    · rw [Set.indicator_of_mem hyB]
      have hab : |X.empiricalLogPotential y-X.potentialNormalization| ≤ f y :=
        abs_sub _ _
      have hf0 : 0 ≤ f y := add_nonneg (abs_nonneg _) (abs_nonneg _)
      have hb := mul_le_mul (poissonKernel_le_inv_height hh (y-x)) hab
        (abs_nonneg _) hK
      exact hb.trans (le_add_of_nonneg_left (mul_nonneg hE hw0))
    · rw [Set.indicator_of_notMem hyB, mul_zero, add_zero]
      simpa only [E, mul_comm] using mul_le_mul_of_nonneg_left
        (X.abs_potential_sub_le_away hn (hI hy) hδ hyB (hΛ y hy)) hw0
  have hweighted := X.integrable_poisson_potential_sub hh x X.potentialNormalization
  have hbound := setIntegral_mono_on hweighted.abs.integrableOn
    ((hw.const_mul E).add (hfi.const_mul K)).integrableOn measurableSet_Icc hpoint
  have hintw : (∫ y in Set.Icc a b, poissonKernel h (y-x)) ≤ 1 := by
    apply le_trans (setIntegral_le_integral hw (ae_of_all _ (fun y => (poissonKernel_pos hh _).le)))
    rw [integral_sub_right_eq_self, integral_poissonKernel hh]
  have hintf : (∫ y in Set.Icc a b, B.indicator f y) ≤ ∫ y in B, f y := by
    apply le_trans (setIntegral_le_integral hfi (ae_of_all _
      (fun y => Set.indicator_nonneg (fun y _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) y)))
    rw [integral_indicator hB]
  have hintB : (∫ y in B, f y) ≤
      Real.sqrt (2*n*δ*logSquareBound)+|X.potentialNormalization| *(2*n*δ) := by
    have hv := X.measureReal_nodeNeighborhood_le hδ.le
    have hs := (X.integral_abs_potential_small_set hn hBs).trans
      (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hv logSquareBound_nonneg))
    dsimp [f]
    rw [integral_add (((X.integrableOn_empiricalLogPotential (-2) 2).mono_set hBs).abs)
      (integrable_const _), integral_const]
    simp only [measureReal_restrict_apply_univ, smul_eq_mul]
    change _ + volume.real B * |X.potentialNormalization| ≤ _
    nlinarith [mul_le_mul_of_nonneg_left hv (abs_nonneg X.potentialNormalization)]
  simp only [Pi.add_apply] at hbound
  rw [integral_add (hw.const_mul E).integrableOn (hfi.const_mul K).integrableOn,
    integral_const_mul, integral_const_mul] at hbound
  have hfinal := (abs_integral_le_integral_abs (f := fun y =>
    poissonKernel h (y-x)*(X.empiricalLogPotential y-X.potentialNormalization))).trans hbound
  have h1 := mul_le_mul_of_nonneg_left hintw hE
  have h2 := mul_le_mul_of_nonneg_left (hintf.trans hintB) hK
  calc
    _ ≤ E*1 + K*(Real.sqrt (2*n*δ*logSquareBound) +
        |X.potentialNormalization| * (2*n*δ)) := hfinal.trans (add_le_add h1 h2)
    _ = _ := by dsimp [E, K]; ring

end Nodes
end TaoAdditive1132
end
end SourceErdos1132_Additive_LocalPoissonEstimate

/- Erdos1132.Additive.WeightedPotential -/
section SourceErdos1132_Additive_WeightedPotential
/- # Uniform Cauchy-weighted integrability of the boundary potential

Main paper: §4, local potential and differentiation estimates.
-/

noncomputable section
open MeasureTheory Set Filter Finset Real Complex
open scoped BigOperators
namespace TaoAdditive1132

def weightedLogBound : ℝ := Real.log 2+(4+logSquareBound)/Real.pi

theorem weightedLogBound_nonneg : 0 ≤ weightedLogBound := by
  unfold weightedLogBound
  exact add_nonneg (Real.log_nonneg (by norm_num))
    (div_nonneg (by linarith [logSquareBound_nonneg]) Real.pi_pos.le)

namespace Nodes
variable {n : ℕ} (X : Nodes n)

theorem empiricalLogPotential_nonpos_outside {y : ℝ} (hy : y ∉ Set.Icc (-2) 2) :
    X.empiricalLogPotential y ≤ 0 := by
  have hd (i : Fin n) : 1 ≤ |y-X.point i| := by
    have hi := X.mem_interval i
    rcases lt_or_gt_of_ne (show y ≠ 0 by intro he; simp [he] at hy) with hneg | hpos
    · have hy2 : y < -2 := by
        by_contra he
        exact hy ⟨le_of_not_gt he, by linarith⟩
      rw [abs_of_neg (by linarith [hi.1] : y-X.point i < 0)]
      linarith [hi.1]
    · have hy2 : 2 < y := by
        by_contra he
        exact hy ⟨by linarith, le_of_not_gt he⟩
      exact (by linarith [hi.2] : 1 ≤ y-X.point i).trans (le_abs_self _)
  unfold empiricalLogPotential
  apply div_nonpos_of_nonpos_of_nonneg _ (Nat.cast_nonneg _)
  apply neg_nonpos.mpr
  apply Finset.sum_nonneg
  intro i _
  rw [← Real.log_abs]
  exact Real.log_nonneg (hd i)

theorem complexLogPotential_zero_one_bounds (hn : 0 < n) :
    -Real.log 2 ≤ X.complexLogPotential 0 1 ∧ X.complexLogPotential 0 1 ≤ 0 := by
  have hnorm (i : Fin n) : 1 ≤ ‖((0-X.point i : ℝ) : ℂ)+(1 : ℝ)*I‖ ∧
      ‖((0-X.point i : ℝ) : ℂ)+(1 : ℝ)*I‖ ≤ 2 := by
    have hi := X.mem_interval i
    have hs : (X.point i)^2 ≤ 1 := by nlinarith [hi.1, hi.2]
    have he : ‖((0-X.point i : ℝ) : ℂ)+(1 : ℝ)*I‖^2 = (X.point i)^2+1 := by
      rw [← Complex.normSq_eq_norm_sq]
      simp [Complex.normSq_apply, pow_two]
    constructor <;> nlinarith [norm_nonneg (((0-X.point i : ℝ) : ℂ)+(1 : ℝ)*I),
      sq_nonneg (X.point i)]
  have hsumlo : 0 ≤ ∑ i, Real.log ‖((0-X.point i : ℝ) : ℂ)+(1 : ℝ)*I‖ :=
    Finset.sum_nonneg (fun i _ => Real.log_nonneg (hnorm i).1)
  have hsumhi : (∑ i, Real.log ‖((0-X.point i : ℝ) : ℂ)+(1 : ℝ)*I‖) ≤ n*Real.log 2 := by
    calc
      _ ≤ ∑ _i : Fin n, Real.log 2 := Finset.sum_le_sum
        (fun i _ => Real.log_le_log (lt_of_lt_of_le zero_lt_one (hnorm i).1) (hnorm i).2)
      _ = _ := by simp
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  unfold complexLogPotential
  constructor
  · apply (le_div_iff₀ hnR).mpr
    nlinarith
  · exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hsumlo) hnR.le

theorem integrable_weighted_abs_potential :
    Integrable (fun y => poissonKernel 1 y * |X.empiricalLogPotential y|) := by
  have hi := (X.integrable_poisson_empiricalLogPotential (by norm_num : (0 : ℝ) < 1) 0).abs
  simpa only [sub_zero, abs_mul, abs_of_pos (poissonKernel_pos (by norm_num : (0 : ℝ) < 1) _)] using hi

/-- A bound for the full real-line integral, including the logarithmic tails. -/
theorem integral_weighted_abs_potential_le (hn : 0 < n) :
    (∫ y, poissonKernel 1 y * |X.empiricalLogPotential y|) ≤ weightedLogBound := by
  let J := Set.Icc (-2 : ℝ) 2
  let g := fun y => poissonKernel 1 y * |X.empiricalLogPotential y|
  have hg : Integrable g := X.integrable_weighted_abs_potential
  have hJ : MeasurableSet J := measurableSet_Icc
  have hp : Integrable (fun y => poissonKernel 1 y * X.empiricalLogPotential y) := by
    simpa only [sub_zero] using X.integrable_poisson_empiricalLogPotential (by norm_num) 0
  have hid (y : ℝ) : g y ≤ -(poissonKernel 1 y * X.empiricalLogPotential y) +
      2*J.indicator g y := by
    by_cases hy : y ∈ J
    · rw [Set.indicator_of_mem hy]
      have hw : 0 ≤ poissonKernel 1 y := (poissonKernel_pos (by norm_num) _).le
      have hle := mul_le_mul_of_nonneg_left (le_abs_self (X.empiricalLogPotential y)) hw
      dsimp [g]
      linarith
    · rw [Set.indicator_of_notMem hy]
      dsimp [g]
      rw [abs_of_nonpos (X.empiricalLogPotential_nonpos_outside hy)]
      ring_nf
      exact le_rfl
  have hbound := integral_mono hg (hp.neg.add ((hg.indicator hJ).const_mul 2)) hid
  simp only [Pi.add_apply, Pi.neg_apply] at hbound
  have hpneg : Integrable (fun y => -(poissonKernel 1 y * X.empiricalLogPotential y)) := hp.neg
  rw [integral_add hpneg ((hg.indicator hJ).const_mul 2), integral_neg,
    integral_const_mul, integral_indicator hJ] at hbound
  have he := X.poisson_empiricalLogPotential (by norm_num : (0 : ℝ) < 1) 0
  simp only [sub_zero] at he
  rw [he] at hbound
  have hjbound : (∫ y in J, g y) ≤ (4+logSquareBound)/(2*Real.pi) := by
    have hmono : (∫ y in J, g y) ≤ ∫ y in J, (1/Real.pi)*|X.empiricalLogPotential y| := by
      apply integral_mono hg.integrableOn
        ((X.integrableOn_empiricalLogPotential (-2) 2).abs.const_mul _)
      intro y
      have hk := poissonKernel_le_inv_height (by norm_num : (0 : ℝ) < 1) y
      simp only [mul_one] at hk
      exact mul_le_mul_of_nonneg_right hk (abs_nonneg _)
    rw [integral_const_mul] at hmono
    have hb := mul_le_mul_of_nonneg_left (X.integral_abs_empiricalLogPotential_le hn)
      (by positivity : 0 ≤ 1/Real.pi)
    calc
      _ ≤ (1/Real.pi)*((4+logSquareBound)/2) := hmono.trans hb
      _ = _ := by ring
  have hzero := X.complexLogPotential_zero_one_bounds hn
  unfold weightedLogBound
  have heq : 2*((4+logSquareBound)/(2*Real.pi)) = (4+logSquareBound)/Real.pi := by ring
  linarith

theorem integrable_weighted_abs_potential_sub (α : ℝ) :
    Integrable (fun y => poissonKernel 1 y * |X.empiricalLogPotential y-α|) := by
  have hi := (X.integrable_poisson_potential_sub (by norm_num : (0 : ℝ) < 1) 0 α).abs
  simpa only [sub_zero, abs_mul,
    abs_of_pos (poissonKernel_pos (by norm_num : (0 : ℝ) < 1) _)] using hi

/-- The same weighted estimate after subtracting any real constant. -/
theorem integral_weighted_abs_potential_sub_le (hn : 0 < n) (α : ℝ) :
    (∫ y, poissonKernel 1 y * |X.empiricalLogPotential y-α|) ≤ weightedLogBound+|α| := by
  have hi := (X.integrable_poisson_potential_sub (by norm_num : (0 : ℝ) < 1) 0 α).abs
  simp only [sub_zero, abs_mul,
    abs_of_pos (poissonKernel_pos (by norm_num : (0 : ℝ) < 1) _)] at hi
  have hright := X.integrable_weighted_abs_potential.add
    ((integrable_poissonKernel (by norm_num : (0 : ℝ) ≤ 1)).mul_const |α|)
  have hb := integral_mono hi hright (fun y => by
    change poissonKernel 1 y * |X.empiricalLogPotential y-α| ≤
      poissonKernel 1 y * |X.empiricalLogPotential y| + poissonKernel 1 y * |α|
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (abs_sub _ _) (poissonKernel_pos (by norm_num) _).le)
  simp only [Pi.add_apply] at hb
  rw [integral_add X.integrable_weighted_abs_potential
    ((integrable_poissonKernel (by norm_num : (0 : ℝ) ≤ 1)).mul_const |α|),
    integral_mul_const, integral_poissonKernel (by norm_num : (0 : ℝ) < 1), one_mul] at hb
  exact hb.trans (add_le_add_left (X.integral_weighted_abs_potential_le hn) _)

end Nodes
end TaoAdditive1132
end
end SourceErdos1132_Additive_WeightedPotential

/- Erdos1132.Additive.ExteriorDensity -/
section SourceErdos1132_Additive_ExteriorDensity
/- # The exterior-integral density and its quantitative regularity

Main paper: §4, local potential and differentiation estimates.
-/

noncomputable section
open MeasureTheory Set Filter Real
namespace TaoAdditive1132.Nodes
variable {n : ℕ} (X : Nodes n)

/-- The density obtained from the boundary potential outside a fixed interval. -/
def exteriorDensity (a b α x h : ℝ) : ℝ :=
  -(1/Real.pi^2) * ∫ y in (Icc a b)ᶜ,
    (X.empiricalLogPotential y-α)/((y-x)^2+h^2)

theorem measurable_exteriorDensity (a b α h : ℝ) :
    Measurable (fun x => X.exteriorDensity a b α x h) := by
  have hm : Measurable (fun p : ℝ × ℝ =>
      (X.empiricalLogPotential p.2-α)/((p.2-p.1)^2+h^2)) :=
    ((X.measurable_empiricalLogPotential.comp measurable_snd).sub_const α).div (by fun_prop)
  exact (hm.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Icc a b)ᶜ)).measurable.const_mul _

theorem exterior_integral_bound (hn : 0 < n) {α C : ℝ} (hC : 0 ≤ C)
    {s : Set ℝ} (hs : MeasurableSet s) {g : ℝ → ℝ} (hg : Measurable g)
    (hbound : ∀ y ∈ s, |g y| ≤ C*(poissonKernel 1 y*|X.empiricalLogPotential y-α|)) :
    IntegrableOn g s ∧ |∫ y in s, g y| ≤ C*(weightedLogBound+|α|) := by
  have hi := (X.integrable_weighted_abs_potential_sub α).const_mul C
  have hgi : IntegrableOn g s := hi.integrableOn.mono' hg.aestronglyMeasurable.restrict
    (by filter_upwards [ae_restrict_mem hs] with y hy; simpa only [Real.norm_eq_abs] using hbound y hy)
  refine ⟨hgi, ?_⟩
  have hb := setIntegral_mono_on hgi.abs hi.integrableOn hs hbound
  have hnng : 0 ≤ᵐ[volume] fun y => C*(poissonKernel 1 y*|X.empiricalLogPotential y-α|) :=
    ae_of_all _ (fun y => mul_nonneg hC (mul_nonneg (poissonKernel_pos (by norm_num) _).le (abs_nonneg _)))
  have hall := setIntegral_le_integral (s := s) hi hnng
  simp only [integral_const_mul] at hb hall
  exact (abs_integral_le_integral_abs.trans hb).trans
    (hall.trans (mul_le_mul_of_nonneg_left (X.integral_weighted_abs_potential_sub_le hn α) hC))

theorem exterior_density_integrable_and_bound (hn : 0 < n) {a b d x : ℝ}
    (hd : 0 < d) (hx : x ∈ Icc (a+d) (b-d)) (hx1 : |x| ≤ 1) (α h : ℝ) :
    IntegrableOn (fun y => (X.empiricalLogPotential y-α)/((y-x)^2+h^2)) (Icc a b)ᶜ ∧
      |X.exteriorDensity a b α x h| ≤
        (exteriorKernelBound d/Real.pi^2)*(weightedLogBound+|α|) := by
  have hm : Measurable (fun y => (X.empiricalLogPotential y-α)/((y-x)^2+h^2)) :=
    (X.measurable_empiricalLogPotential.sub_const α).div (by fun_prop)
  have hp := X.exterior_integral_bound hn (α := α) (exteriorKernelBound_pos hd).le
    measurableSet_Icc.compl hm (fun y hy => by
      have hsep := distance_compl_interval hx hy
      have hden : 0 < (y-x)^2+h^2 := by nlinarith [sq_abs (y-x), sq_nonneg h]
      rw [abs_div, abs_of_pos hden]
      have hb := mul_le_mul_of_nonneg_right (exteriorKernel_le_cauchy hd hx1 hsep h)
        (abs_nonneg (X.empiricalLogPotential y-α))
      convert! hb using 1 <;> ring)
  refine ⟨hp.1, ?_⟩
  unfold exteriorDensity
  rw [abs_mul, abs_neg, abs_of_pos (by positivity : 0 < 1/Real.pi^2)]
  have hb := mul_le_mul_of_nonneg_left hp.2 (by positivity : 0 ≤ 1/Real.pi^2)
  convert! hb using 1 <;> ring

theorem exteriorDensity_height_bound (hn : 0 < n) {a b d x : ℝ}
    (hd : 0 < d) (hx : x ∈ Icc (a+d) (b-d)) (hx1 : |x| ≤ 1) (α h : ℝ) :
    |X.exteriorDensity a b α x h-X.exteriorDensity a b α x 0| ≤
      ((exteriorKernelBound d/Real.pi^2)*(weightedLogBound+|α|)/d^2)*h^2 := by
  let C := (h^2/d^2)*exteriorKernelBound d
  have hC : 0 ≤ C := mul_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _))
    (exteriorKernelBound_pos hd).le
  let g := fun y => (X.empiricalLogPotential y-α)*(1/((y-x)^2+h^2)-1/(y-x)^2)
  have hg : Measurable g := (X.measurable_empiricalLogPotential.sub_const α).mul (by fun_prop)
  have hb := X.exterior_integral_bound hn (α := α) hC measurableSet_Icc.compl hg (fun y hy => by
    have hsep := distance_compl_interval hx hy
    have hk := exteriorKernel_height_difference hd hsep (h := h)
    have hc := exteriorKernel_le_cauchy hd hx1 hsep 0
    simp only [zero_pow (by norm_num : 2 ≠ 0), add_zero] at hc
    have hnonneg : 0 ≤ h^2/d^2 := div_nonneg (sq_nonneg _) (sq_nonneg _)
    have hh := hk.trans (mul_le_mul_of_nonneg_left hc hnonneg)
    have hmul := mul_le_mul_of_nonneg_left hh (abs_nonneg (X.empiricalLogPotential y-α))
    dsimp [g]
    rw [abs_mul]
    convert! hmul using 1 <;> simp only [C] <;> ring)
  have hi := (X.exterior_density_integrable_and_bound hn hd hx hx1 α h).1
  have hi0 := (X.exterior_density_integrable_and_bound hn hd hx hx1 α 0).1
  have he : X.exteriorDensity a b α x h-X.exteriorDensity a b α x 0 =
      -(1/Real.pi^2)*(∫ y in (Icc a b)ᶜ, g y) := by
    unfold exteriorDensity
    rw [← mul_sub, ← integral_sub hi hi0]
    congr 1
    apply integral_congr_ae
    filter_upwards with y
    dsimp [g]
    ring
  rw [he, abs_mul, abs_neg, abs_of_pos (by positivity : 0 < 1/Real.pi^2)]
  have hm := mul_le_mul_of_nonneg_left hb.2 (by positivity : 0 ≤ 1/Real.pi^2)
  convert! hm using 1 <;> simp only [C] <;> ring

theorem exteriorDensity_lipschitz_bound (hn : 0 < n) {a b d x x₀ : ℝ}
    (hd : 0 < d) (hx : x ∈ Icc (a+d) (b-d)) (hx0 : x₀ ∈ Icc (a+d) (b-d))
    (hx1 : |x| ≤ 1) (hx01 : |x₀| ≤ 1) (α : ℝ) :
    |X.exteriorDensity a b α x 0-X.exteriorDensity a b α x₀ 0| ≤
      (2*exteriorKernelBound d/Real.pi^2*(weightedLogBound+|α|)/d)*|x-x₀| := by
  let C := (|x-x₀|/d)*(2*exteriorKernelBound d)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (div_nonneg (abs_nonneg _) hd.le)
      (mul_nonneg (by norm_num) (exteriorKernelBound_pos hd).le)
  let g := fun y => (X.empiricalLogPotential y-α)*(1/(y-x)^2-1/(y-x₀)^2)
  have hg : Measurable g := (X.measurable_empiricalLogPotential.sub_const α).mul (by fun_prop)
  have hb := X.exterior_integral_bound hn (α := α) hC measurableSet_Icc.compl hg (fun y hy => by
    have hs := distance_compl_interval hx hy
    have ht := distance_compl_interval hx0 hy
    have hk := exteriorKernel_horizontal_difference hd hs ht
    have h1 := exteriorKernel_le_cauchy hd hx1 hs 0
    have h2 := exteriorKernel_le_cauchy hd hx01 ht 0
    simp only [zero_pow (by norm_num : 2 ≠ 0), add_zero] at h1 h2
    have he : |(y-x)-(y-x₀)| = |x-x₀| := by
      rw [show (y-x)-(y-x₀) = -(x-x₀) by ring, abs_neg]
    rw [he] at hk
    have hsum := add_le_add h1 h2
    have hprod := mul_le_mul_of_nonneg_left hsum (div_nonneg (abs_nonneg (x-x₀)) hd.le)
    have hmul := mul_le_mul_of_nonneg_left (hk.trans hprod)
      (abs_nonneg (X.empiricalLogPotential y-α))
    dsimp [g]
    rw [abs_mul]
    convert! hmul using 1 <;> simp only [C] <;> ring)
  have hi := (X.exterior_density_integrable_and_bound hn hd hx hx1 α 0).1
  have hi0 := (X.exterior_density_integrable_and_bound hn hd hx0 hx01 α 0).1
  have he : X.exteriorDensity a b α x 0-X.exteriorDensity a b α x₀ 0 =
      -(1/Real.pi^2)*(∫ y in (Icc a b)ᶜ, g y) := by
    unfold exteriorDensity
    rw [← mul_sub, ← integral_sub hi hi0]
    congr 1
    apply integral_congr_ae
    filter_upwards with y
    dsimp [g]
    ring
  rw [he, abs_mul, abs_neg, abs_of_pos (by positivity : 0 < 1/Real.pi^2)]
  have hm := mul_le_mul_of_nonneg_left hb.2 (by positivity : 0 ≤ 1/Real.pi^2)
  convert! hm using 1 <;> simp only [C] <;> ring

end TaoAdditive1132.Nodes
end
end SourceErdos1132_Additive_ExteriorDensity

/- Erdos1132.Additive.ComplexPotentialEstimate -/
section SourceErdos1132_Additive_ComplexPotentialEstimate
/- # The local complex-potential expansion with an explicit remainder

Main paper: §4, local potential and differentiation estimates.
-/

noncomputable section
open MeasureTheory Set Filter Real
namespace TaoAdditive1132.Nodes
variable {n : ℕ} (X : Nodes n)

theorem poisson_exterior_decomposition (hn : 0 < n) {a b d x h : ℝ}
    (hd : 0 < d) (hx : x ∈ Icc (a+d) (b-d)) (hx1 : |x| ≤ 1)
    (hh : 0 < h) (α : ℝ) :
    X.complexLogPotential x h = α - Real.pi*h*X.exteriorDensity a b α x h +
      ∫ y in Icc a b, poissonKernel h (y-x)*(X.empiricalLogPotential y-α) := by
  have hi := X.integrable_poisson_potential_sub hh x α
  have he := integral_add_compl (s := Icc a b) measurableSet_Icc hi
  have hout := (X.exterior_density_integrable_and_bound hn hd hx hx1 α h).1
  have hex : (∫ y in (Icc a b)ᶜ, poissonKernel h (y-x)*(X.empiricalLogPotential y-α)) =
      -Real.pi*h*X.exteriorDensity a b α x h := by
    unfold exteriorDensity
    have heq (y : ℝ) : poissonKernel h (y-x)*(X.empiricalLogPotential y-α) =
        (h/Real.pi)*((X.empiricalLogPotential y-α)/((y-x)^2+h^2)) := by
      unfold poissonKernel
      rw [div_mul_eq_div_div]
      ring
    simp_rw [heq]
    rw [integral_const_mul]
    field_simp
  rw [hex] at he
  rw [X.poisson_potential_sub hh x α]
  linarith

/-- The density is its real-axis exterior integral. All error terms are explicit. -/
theorem complex_potential_expansion (hn : 0 < n) {a b d x h δ Λ : ℝ}
    (hd : 0 < d) (hx : x ∈ Icc (a+d) (b-d)) (hx1 : |x| ≤ 1)
    (hI : Icc a b ⊆ Icc (-1) 1) (hh : 0 < h) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hΛ : ∀ y ∈ Icc a b, X.lebesgue y ≤ Λ) (hΛ1 : 1 ≤ Λ) :
    |X.complexLogPotential x h-X.potentialNormalization +
      Real.pi*h*X.exteriorDensity a b X.potentialNormalization x 0| ≤
      max (Real.log (2*Λ)) (-Real.log δ)/n +
        (Real.sqrt (2*n*δ*logSquareBound) + |X.potentialNormalization| *(2*n*δ))/(Real.pi*h) +
        (exteriorKernelBound d*(weightedLogBound+|X.potentialNormalization|)/(Real.pi*d^2))*h^3 := by
  have hp := X.poisson_exterior_decomposition hn hd hx hx1 hh X.potentialNormalization
  have herr := X.local_poisson_potential_bound hn hI hδ hδ1 hh hΛ x hΛ1
  have hheight := X.exteriorDensity_height_bound hn hd hx hx1 X.potentialNormalization h
  have heq : X.complexLogPotential x h-X.potentialNormalization +
      Real.pi*h*X.exteriorDensity a b X.potentialNormalization x 0 =
      (∫ y in Icc a b, poissonKernel h (y-x)*(X.empiricalLogPotential y-X.potentialNormalization)) +
        Real.pi*h*(X.exteriorDensity a b X.potentialNormalization x 0-
          X.exteriorDensity a b X.potentialNormalization x h) := by rw [hp]; ring
  rw [heq]
  have hmul := mul_le_mul_of_nonneg_left hheight (mul_nonneg Real.pi_pos.le hh.le)
  rw [abs_sub_comm] at hmul
  have he : Real.pi*h*((exteriorKernelBound d/Real.pi^2)*
        (weightedLogBound+|X.potentialNormalization|)/d^2*h^2) =
      (exteriorKernelBound d*(weightedLogBound+|X.potentialNormalization|)/(Real.pi*d^2))*h^3 := by
    field_simp
  rw [he] at hmul
  calc
    _ ≤ |∫ y in Icc a b, poissonKernel h (y-x)*(X.empiricalLogPotential y-X.potentialNormalization)| +
        |Real.pi*h*(X.exteriorDensity a b X.potentialNormalization x 0-
          X.exteriorDensity a b X.potentialNormalization x h)| := abs_add_le _ _
    _ ≤ _ := by
      rw [abs_mul, abs_of_pos (mul_pos Real.pi_pos hh)]
      exact add_le_add herr hmul

end TaoAdditive1132.Nodes
end
end SourceErdos1132_Additive_ComplexPotentialEstimate

/- Erdos1132.Additive.PotentialScales -/
section SourceErdos1132_Additive_PotentialScales
/- # Explicit choices of scales for the local potential expansion

Main paper: §4, local potential and differentiation estimates.
-/

noncomputable section
open Set Filter Real
open scoped Topology
namespace TaoAdditive1132

def potentialErrorSize (n : ℕ) : ℝ := (1+Real.log n)/n

theorem tendsto_potentialErrorSize : Tendsto potentialErrorSize atTop (𝓝 0) := by
  have hlog := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
    tendsto_natCast_atTop_atTop
  have hinv := tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)
  convert! hinv.add hlog using 1
  · ext n
    simp [potentialErrorSize, add_div]
  · simp

def normalizationBound (a b : ℝ) : ℝ :=
  Real.log 2+2+(4+logSquareBound)/(2*(b-a))

theorem normalizationBound_pos {a b : ℝ} (hab : a < b) : 0 < normalizationBound a b := by
  have hB := logSquareBound_nonneg
  unfold normalizationBound
  positivity

theorem potentialErrorSize_nonneg {n : ℕ} (hn : 0 < n) : 0 ≤ potentialErrorSize n := by
  unfold potentialErrorSize
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  exact div_nonneg (by linarith [Real.log_nonneg hn1]) (Nat.cast_nonneg _)

theorem local_log_error_scale {N : ℝ} (hN : 1 ≤ N) :
    max (Real.log (2*N)) (-Real.log (1/N^5))/N ≤
      (5+Real.log 2)*((1+Real.log N)/N) := by
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hN0.ne', Real.log_div one_ne_zero (pow_ne_zero _ hN0.ne'),
    Real.log_one, Real.log_pow]
  have hlog := Real.log_nonneg hN
  have hlog2 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
  apply (div_le_iff₀ hN0).mpr
  have he : (5+Real.log 2)*((1+Real.log N)/N)*N = (5+Real.log 2)*(1+Real.log N) := by field_simp
  rw [he]
  apply max_le <;> push_cast <;> nlinarith [mul_nonneg hlog2 hlog]

theorem small_set_error_scale {N A B h : ℝ} (hN : 1 ≤ N) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hh : 1/N ≤ h) :
    (Real.sqrt (2*N*(1/N^5)*B)+A*(2*N*(1/N^5)))/(Real.pi*h) ≤
      ((Real.sqrt (2*B)+2*A)/Real.pi)/N := by
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hh0 : 0 < h := (one_div_pos.mpr hN0).trans_le hh
  have hnum : 2*N*(1/N^5)*B = (2*B)/(N^2)^2 := by field_simp
  have hnum2 : 2*N*(1/N^5) = 2/N^4 := by field_simp
  rw [hnum, Real.sqrt_div (by positivity : 0 ≤ 2*B), Real.sqrt_sq (sq_nonneg N), hnum2]
  have hpow : N^2 ≤ N^4 := by nlinarith [sq_nonneg (N^2-1)]
  have hnsmall : A*(2/N^4) ≤ 2*A/N^2 := by
    have hb := div_le_div_of_nonneg_left (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hA)
      (sq_pos_of_pos hN0) hpow
    convert! hb using 1 <;> ring
  have hsum : Real.sqrt (2*B)/N^2+A*(2/N^4) ≤ (Real.sqrt (2*B)+2*A)/N^2 := by
    rw [add_div]
    linarith
  have hden : Real.pi/N ≤ Real.pi*h := by
    have hm := mul_le_mul_of_nonneg_left hh Real.pi_pos.le
    simpa only [mul_one_div] using hm
  calc
    _ ≤ ((Real.sqrt (2*B)+2*A)/N^2)/(Real.pi*h) :=
      div_le_div_of_nonneg_right hsum (mul_pos Real.pi_pos hh0).le
    _ ≤ ((Real.sqrt (2*B)+2*A)/N^2)/(Real.pi/N) :=
      div_le_div_of_nonneg_left (by positivity) (div_pos Real.pi_pos hN0) hden
    _ = _ := by field_simp

namespace Nodes
variable {n : ℕ} (X : Nodes n)

theorem abs_potentialNormalization_le (hn : 0 < n) {a b : ℝ}
    (hab : a < b) (hI : Icc a b ⊆ Icc (-1) 1)
    (hΛ : ∀ y ∈ Icc a b, X.lebesgue y ≤ n) :
    |X.potentialNormalization| ≤ normalizationBound a b := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hlo := X.potentialNormalization_lower hn
  have hhi := X.potentialNormalization_upper hn hab hI hΛ
  have hlog : Real.log (2*n)/n ≤ 2 := by
    apply (div_le_iff₀ hnR).mpr
    exact (Real.log_le_sub_one_of_pos (by positivity : 0 < (2 : ℝ)*n)).trans (by linarith)
  have hC : 0 ≤ (4+logSquareBound)/(2*(b-a)) := by
    have hB := logSquareBound_nonneg
    positivity
  unfold normalizationBound
  apply abs_le.mpr
  constructor <;> linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]

end Nodes
end TaoAdditive1132
end
end SourceErdos1132_Additive_PotentialScales

/- Erdos1132.Additive.PotentialDrop -/
section SourceErdos1132_Additive_PotentialDrop
/- # A uniform decrease of logarithmic potentials between two positive heights

Main paper: §4, local potential and differentiation estimates.
-/

noncomputable section
open MeasureTheory Set Finset Real Complex
open scoped BigOperators
namespace TaoAdditive1132

theorem log_norm_height_drop {t h : ℝ} (ht : |t| ≤ 2) (hh : 0 < h) (hh1 : h ≤ 1) :
    h^2/32 ≤ Real.log ‖(t : ℂ)+h*I‖ - Real.log ‖(t : ℂ)+(h/2 : ℝ)*I‖ := by
  let A := t^2+h^2
  let B := t^2+(h/2)^2
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hA5 : A ≤ 5 := by
    dsimp [A]
    nlinarith [sq_abs t, abs_nonneg t]
  have he1 : ‖(t : ℂ)+h*I‖^2 = A := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply, A, pow_two]
  have he2 : ‖(t : ℂ)+(h/2 : ℝ)*I‖^2 = B := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply, B, pow_two]
  have hlog := Real.log_le_sub_one_of_pos (div_pos hB hA)
  rw [Real.log_div hB.ne' hA.ne'] at hlog
  have hlogA : Real.log A = 2*Real.log ‖(t : ℂ)+h*I‖ := by
    rw [← he1, Real.log_pow]
    norm_num
  have hlogB : Real.log B = 2*Real.log ‖(t : ℂ)+(h/2 : ℝ)*I‖ := by
    rw [← he2, Real.log_pow]
    norm_num
  have hAB : 1-B/A ≥ 3*h^2/20 := by
    apply (le_sub_iff_add_le).mpr
    apply (mul_le_mul_iff_left₀ hA).mp
    rw [one_mul]
    have he : (3*h^2/20+B/A)*A = 3*h^2*A/20+B := by field_simp
    rw [he]
    dsimp [A, B] at *
    nlinarith [mul_le_mul_of_nonneg_left hA5 (sq_nonneg h)]
  rw [hlogA, hlogB] at hlog
  nlinarith [sq_nonneg h]

namespace Nodes
variable {n : ℕ} (X : Nodes n)

theorem complexLogPotential_height_drop (hn : 0 < n) {x h : ℝ}
    (hx : x ∈ Set.Icc (-1) 1) (hh : 0 < h) (hh1 : h ≤ 1) :
    h^2/32 ≤ X.complexLogPotential x (h/2)-X.complexLogPotential x h := by
  have hpoint (i : Fin n) := log_norm_height_drop (t := x-X.point i)
    (by apply abs_le.mpr; have hi := X.mem_interval i; constructor <;> linarith [hx.1, hx.2, hi.1, hi.2]) hh hh1
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hpoint i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Finset.sum_sub_distrib] at hs
  unfold complexLogPotential
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [← sub_div]
  apply (le_div_iff₀ hnR).mpr
  nlinarith

end Nodes
end TaoAdditive1132
end
end SourceErdos1132_Additive_PotentialDrop

/- Erdos1132.Additive.TaoPotential -/
section SourceErdos1132_Additive_TaoPotential
/- # Local potential estimates under a linear Lebesgue bound

Main paper: §4, local potential and differentiation estimates.
-/

noncomputable section
open MeasureTheory Set Filter Real
open scoped Topology
namespace TaoAdditive1132

/-- A point in the inset interval remains in the original interpolation interval. -/
theorem mem_interval_of_inset {a b d x : ℝ} (hd : 0 ≤ d) (hx : x ∈ Icc (a+d) (b-d)) :
    x ∈ Icc a b := by constructor <;> linarith [hx.1, hx.2]

/-- A direct proof of [Tao, Theorem 4.1(ii)] in the form needed here, with
his hypothesis (4.1) specialized to `λ ≤ n` on the fixed interval.
The normalization and exterior density are defined from the node array. -/
theorem uniform_complex_potential_expansion {a b d : ℝ} (hab : a < b)
    (hI : Icc a b ⊆ Icc (-1) 1) (hd : 0 < d) :
    ∃ C > 0, ∀ (n : ℕ) (X : Nodes n), 0 < n →
      (∀ y ∈ Icc a b, X.lebesgue y ≤ n) →
      ∀ x ∈ Icc (a+d) (b-d), ∀ h : ℝ, 1/(n : ℝ) ≤ h →
        |X.complexLogPotential x h-X.potentialNormalization +
          Real.pi*h*X.exteriorDensity a b X.potentialNormalization x 0| ≤
          C*(potentialErrorSize n+h^3) := by
  let A := normalizationBound a b
  let C₀ := 5+Real.log 2+(Real.sqrt (2*logSquareBound)+2*A)/Real.pi
  let C₃ := exteriorKernelBound d*(weightedLogBound+A)/(Real.pi*d^2)
  have hA : 0 < A := normalizationBound_pos hab
  have hC₀ : 0 < C₀ := by
    have hB := logSquareBound_nonneg
    dsimp [C₀]
    positivity
  have hC₃ : 0 < C₃ := by
    dsimp [C₃]
    exact div_pos (mul_pos (exteriorKernelBound_pos hd)
      (add_pos_of_nonneg_of_pos weightedLogBound_nonneg hA)) (by positivity)
  refine ⟨C₀+C₃+1, by positivity, ?_⟩
  intro n X hn hΛ x hx h hh
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hh0 : 0 < h := (one_div_pos.mpr hnR).trans_le hh
  have hxI := hI (mem_interval_of_inset hd.le hx)
  have hx1 : |x| ≤ 1 := abs_le.mpr hxI
  have hα := X.abs_potentialNormalization_le hn hab hI hΛ
  change |X.potentialNormalization| ≤ A at hα
  let δ : ℝ := 1/(n : ℝ)^5
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := by
    apply (div_le_one (by positivity : 0 < (n : ℝ)^5)).mpr
    exact one_le_pow₀ hn1
  have he := X.complex_potential_expansion hn hd hx hx1 hI hh0 hδ hδ1 hΛ hn1
  have hlog := local_log_error_scale hn1
  have hsmall := small_set_error_scale hn1 (abs_nonneg X.potentialNormalization) logSquareBound_nonneg hh
  have hsmall' : (Real.sqrt (2*n*δ*logSquareBound)+|X.potentialNormalization| *(2*n*δ))/(Real.pi*h) ≤
      ((Real.sqrt (2*logSquareBound)+2*A)/Real.pi)*potentialErrorSize n := by
    have hAmono : ((Real.sqrt (2*logSquareBound)+2*|X.potentialNormalization|)/Real.pi)/(n : ℝ) ≤
        ((Real.sqrt (2*logSquareBound)+2*A)/Real.pi)/(n : ℝ) := by
      apply div_le_div_of_nonneg_right _ hnR.le
      apply div_le_div_of_nonneg_right _ Real.pi_pos.le
      linarith
    have hmult := mul_le_mul_of_nonneg_left (by linarith [Real.log_nonneg hn1] : (1 : ℝ) ≤ 1+Real.log n)
      (by positivity : 0 ≤ (Real.sqrt (2*logSquareBound)+2*A)/Real.pi)
    have hfinal := div_le_div_of_nonneg_right hmult hnR.le
    calc
      _ ≤ ((Real.sqrt (2*logSquareBound)+2*|X.potentialNormalization|)/Real.pi)/(n : ℝ) := hsmall
      _ ≤ ((Real.sqrt (2*logSquareBound)+2*A)/Real.pi)/(n : ℝ) := hAmono
      _ ≤ _ := by simpa only [mul_one, potentialErrorSize, mul_div_assoc] using hfinal
  have hcubic : (exteriorKernelBound d*(weightedLogBound+|X.potentialNormalization|)/(Real.pi*d^2))*h^3 ≤ C₃*h^3 := by
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hh0.le _)
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left (by linarith : weightedLogBound+|X.potentialNormalization| ≤ weightedLogBound+A)
      (exteriorKernelBound_pos hd).le
  have hsum := add_le_add (add_le_add hlog hsmall') hcubic
  have hE := potentialErrorSize_nonneg hn
  calc
    _ ≤ (5+Real.log 2)*potentialErrorSize n +
        ((Real.sqrt (2*logSquareBound)+2*A)/Real.pi)*potentialErrorSize n+C₃*h^3 := he.trans hsum
    _ = C₀*potentialErrorSize n+C₃*h^3 := by dsimp [C₀]; ring
    _ ≤ (C₀+C₃+1)*(potentialErrorSize n+h^3) := by
      nlinarith [mul_nonneg hC₀.le (pow_nonneg hh0.le 3), mul_nonneg hC₃.le hE]

/-- The actual exterior density has uniform size and Lipschitz bounds. -/
theorem uniform_exterior_density_bounds {a b d : ℝ} (hab : a < b)
    (hI : Icc a b ⊆ Icc (-1) 1) (hd : 0 < d) :
    ∃ C > 0, ∀ (n : ℕ) (X : Nodes n), 0 < n →
      (∀ y ∈ Icc a b, X.lebesgue y ≤ n) →
      (∀ x ∈ Icc (a+d) (b-d), |X.exteriorDensity a b X.potentialNormalization x 0| ≤ C) ∧
      (∀ x ∈ Icc (a+d) (b-d), ∀ z ∈ Icc (a+d) (b-d),
        |X.exteriorDensity a b X.potentialNormalization x 0-
          X.exteriorDensity a b X.potentialNormalization z 0| ≤ C*|x-z|) := by
  let A := normalizationBound a b
  let B := (exteriorKernelBound d/Real.pi^2)*(weightedLogBound+A)
  let L := 2*B/d
  have hA := (normalizationBound_pos hab).le
  have hB : 0 ≤ B := mul_nonneg (div_nonneg (exteriorKernelBound_pos hd).le (sq_nonneg _))
    (add_nonneg weightedLogBound_nonneg hA)
  have hL : 0 ≤ L := div_nonneg (mul_nonneg (by norm_num) hB) hd.le
  refine ⟨B+L+1, by positivity, ?_⟩
  intro n X hn hΛ
  have hα := X.abs_potentialNormalization_le hn hab hI hΛ
  change |X.potentialNormalization| ≤ A at hα
  have hx1 (x : ℝ) (hx : x ∈ Icc (a+d) (b-d)) : |x| ≤ 1 :=
    abs_le.mpr (hI (mem_interval_of_inset hd.le hx))
  constructor
  · intro x hx
    have hb := (X.exterior_density_integrable_and_bound hn hd hx (hx1 x hx) X.potentialNormalization 0).2
    have hm := mul_le_mul_of_nonneg_left (by linarith : weightedLogBound+|X.potentialNormalization| ≤ weightedLogBound+A)
      (div_nonneg (exteriorKernelBound_pos hd).le (sq_nonneg Real.pi))
    exact (hb.trans hm).trans (by dsimp [B] at *; linarith)
  · intro x hx z hz
    have hb := X.exteriorDensity_lipschitz_bound hn hd hx hz (hx1 x hx) (hx1 z hz) X.potentialNormalization
    have hc : 2*exteriorKernelBound d/Real.pi^2*(weightedLogBound+|X.potentialNormalization|)/d ≤ L := by
      have hD := exteriorKernelBound_pos hd
      have hm := mul_le_mul_of_nonneg_left (by linarith : weightedLogBound+|X.potentialNormalization| ≤ weightedLogBound+A)
        (by positivity : 0 ≤ 2*exteriorKernelBound d/Real.pi^2/d)
      convert! hm using 1 <;> ring
    exact hb.trans ((mul_le_mul_of_nonneg_right hc (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_right (by linarith : L ≤ B+L+1) (abs_nonneg _)))

end TaoAdditive1132
end
end SourceErdos1132_Additive_TaoPotential

/- Erdos1132.Additive.LocalQuadrature -/
section SourceErdos1132_Additive_LocalQuadrature
/- # Quantitative quadrature for functions supported in an interior interval

Main paper: §4, local potential and differentiation estimates.
-/

noncomputable section
open MeasureTheory Set Finset Real
open scoped BigOperators
namespace TaoAdditive1132

theorem potential_difference_density_bound {C e h α ρ U₁ U₂ : ℝ} (hh : 0 < h)
    (h₁ : |U₁-α+Real.pi*h*ρ| ≤ C*(e+h^3))
    (h₂ : |U₂-α+Real.pi*(2*h)*ρ| ≤ C*(e+(2*h)^3)) :
    |(U₁-U₂)/(Real.pi*h)-ρ| ≤ C*(2*e+9*h^3)/(Real.pi*h) := by
  have he : (U₁-U₂)/(Real.pi*h)-ρ =
      ((U₁-α+Real.pi*h*ρ)-(U₂-α+Real.pi*(2*h)*ρ))/(Real.pi*h) := by
    field_simp
    ring
  rw [he, abs_div, abs_of_pos (mul_pos Real.pi_pos hh)]
  apply div_le_div_of_nonneg_right _ (mul_pos Real.pi_pos hh).le
  calc
    _ ≤ |U₁-α+Real.pi*h*ρ|+|U₂-α+Real.pi*(2*h)*ρ| := abs_sub _ _
    _ ≤ C*(e+h^3)+C*(e+(2*h)^3) := add_le_add h₁ h₂
    _ = _ := by ring

namespace Nodes
variable {n : ℕ} (X : Nodes n)

theorem integrable_exteriorDensity_mul_supported {a b l r α C M : ℝ}
    {f : ℝ → ℝ} (hf : Measurable f) (hM : ∀ x, |f x| ≤ M)
    (hρ : ∀ x ∈ Icc l r, |X.exteriorDensity a b α x 0| ≤ C)
    (hsupp : ∀ x, x ∉ Icc l r → f x = 0) :
    Integrable (fun x => X.exteriorDensity a b α x 0*f x) := by
  have hm : Measurable (fun x => X.exteriorDensity a b α x 0*f x) :=
    (X.measurable_exteriorDensity a b α 0).mul hf
  have hi : IntegrableOn (fun x => X.exteriorDensity a b α x 0*f x) (Icc l r) := by
    apply (integrable_const (C*M)).mono' hm.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    rw [Real.norm_eq_abs, abs_mul]
    have hM0 := (abs_nonneg (f x)).trans (hM x)
    have hC0 := (abs_nonneg (X.exteriorDensity a b α x 0)).trans (hρ x hx)
    exact mul_le_mul (hρ x hx) (hM x) (abs_nonneg _) hC0
  exact hi.integrable_of_forall_notMem_eq_zero (fun x hx => by rw [hsupp x hx, mul_zero])

end Nodes

/-- The error is uniform over all bounded Lipschitz functions with support in
the specified interior interval. -/
theorem uniform_local_quadrature {a b d l r : ℝ} (hab : a < b)
    (hI : Icc a b ⊆ Icc (-1) 1) (hd : 0 < d) (hlr : l ≤ r)
    (hJ : Icc l r ⊆ Icc (a+d) (b-d)) :
    ∃ C > 0, ∀ (n : ℕ) (X : Nodes n), 0 < n →
      (∀ y ∈ Icc a b, X.lebesgue y ≤ n) →
      ∀ (f : ℝ → ℝ) (M L h δ : ℝ), Measurable f →
      (∀ x, |f x| ≤ M) → 0 ≤ L →
      (∀ x y, |f x-f y| ≤ L*|x-y|) →
      (∀ x, x ∉ Icc l r → f x = 0) → 0 < δ → 1/(n : ℝ) ≤ h →
      |(∑ i, f (X.point i))/(n : ℝ)-
        ∫ x, X.exteriorDensity a b X.potentialNormalization x 0*f x| ≤
        L*δ+8*M*h/(Real.pi*δ)+C*M*(potentialErrorSize n/h+h^2) := by
  obtain ⟨Cp, hCp, hpot⟩ := uniform_complex_potential_expansion hab hI hd
  obtain ⟨Cr, hCr, hden⟩ := uniform_exterior_density_bounds hab hI hd
  refine ⟨18*Cp/Real.pi, by positivity, ?_⟩
  intro n X hn hΛ f M L h δ hf hM hL hlip hsupp hδ hnh
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hh : 0 < h := (one_div_pos.mpr hnR).trans_le hnh
  have hM0 := (abs_nonneg (f 0)).trans (hM 0)
  have hE := potentialErrorSize_nonneg hn
  let ρ := fun x => X.exteriorDensity a b X.potentialNormalization x 0
  let D := fun x => (X.complexLogPotential x h-X.complexLogPotential x (2*h))/(Real.pi*h)
  have hpoint (x : ℝ) (hx : x ∈ Icc l r) :
      |D x-ρ x| ≤ Cp*(2*potentialErrorSize n+9*h^3)/(Real.pi*h) :=
    potential_difference_density_bound hh (hpot n X hn hΛ x (hJ hx) h hnh)
      (hpot n X hn hΛ x (hJ hx) (2*h) (hnh.trans (by linarith)))
  have hiD : Integrable (fun x => D x*f x) := X.integrable_averaged_node_kernel_mul hh hf hM
  have hiρ : Integrable (fun x => ρ x*f x) := X.integrable_exteriorDensity_mul_supported hf hM
    (fun x hx => (hden n X hn hΛ).1 x (hJ hx)) hsupp
  have he : (∫ x, D x*f x)-(∫ x, ρ x*f x) = ∫ x, (D x-ρ x)*f x := by
    rw [← integral_sub hiD hiρ]
    apply integral_congr_ae
    filter_upwards with x
    ring
  have hdiff : |(∫ x, D x*f x)-(∫ x, ρ x*f x)| ≤
      (r-l)*(Cp*(2*potentialErrorSize n+9*h^3)/(Real.pi*h)*M) := by
    rw [he, ← setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := Icc l r) (fun x hx => by rw [hsupp x hx, mul_zero])]
    have hb := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Icc l r)
      (f := fun x => (D x-ρ x)*f x) (by simp) (fun x hx => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hpoint x hx) (hM x) (abs_nonneg _)
          (by positivity : 0 ≤ Cp*(2*potentialErrorSize n+9*h^3)/(Real.pi*h)))
    simpa only [Real.norm_eq_abs, Measure.real, Real.volume_Icc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hlr), mul_comm] using hb
  have hlen : r-l ≤ 2 := by
    have hl := hI (mem_interval_of_inset hd.le (hJ (left_mem_Icc.mpr hlr)))
    have hr := hI (mem_interval_of_inset hd.le (hJ (right_mem_Icc.mpr hlr)))
    linarith [hl.1, hr.2]
  have hlast : (r-l)*(Cp*(2*potentialErrorSize n+9*h^3)/(Real.pi*h)*M) ≤
      (18*Cp/Real.pi)*M*(potentialErrorSize n/h+h^2) := by
    have h1 := mul_le_mul_of_nonneg_right hlen
      (by positivity : 0 ≤ Cp*(2*potentialErrorSize n+9*h^3)/(Real.pi*h)*M)
    have h2 : 2*(Cp*(2*potentialErrorSize n+9*h^3)/(Real.pi*h)*M) ≤
        (18*Cp/Real.pi)*M*(potentialErrorSize n/h+h^2) := by
      apply (mul_le_mul_iff_left₀ (mul_pos Real.pi_pos hh)).mp
      field_simp
      nlinarith [mul_nonneg hCp.le (mul_nonneg hM0 hE)]
    exact h1.trans h2
  have hq := X.averaged_node_quadrature_bound hn hh hδ hf hM hL hlip
  calc
    _ ≤ |(∑ i, f (X.point i))/(n : ℝ)-(∫ x, D x*f x)| +
        |(∫ x, D x*f x)-(∫ x, ρ x*f x)| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add hq (hdiff.trans hlast)

end TaoAdditive1132
end
end SourceErdos1132_Additive_LocalQuadrature

/- Erdos1132.Additive.QuadratureRate -/
section SourceErdos1132_Additive_QuadratureRate
/- # A uniform algebraic rate for the local quadrature estimate

Main paper: §4, local potential and differentiation estimates.
-/

noncomputable section
open MeasureTheory Set Finset Filter Real
open scoped BigOperators Topology
namespace TaoAdditive1132

/-- A fourth root records the two nested square-root scales without rounding. -/
def quarterRoot (N : ℝ) : ℝ := Real.sqrt (Real.sqrt N)

theorem quarterRoot_pos {N : ℝ} (hN : 0 < N) : 0 < quarterRoot N := by
  unfold quarterRoot
  positivity

theorem quarterRoot_pow_four {N : ℝ} (hN : 0 ≤ N) : (quarterRoot N)^4 = N := by
  unfold quarterRoot
  have h1 := Real.sq_sqrt (Real.sqrt_nonneg N)
  have h2 := Real.sq_sqrt hN
  nlinarith

theorem one_le_quarterRoot {N : ℝ} (hN : 1 ≤ N) : 1 ≤ quarterRoot N := by
  have h0 : 0 ≤ N := zero_le_one.trans hN
  have hq := quarterRoot_pos (zero_lt_one.trans_le hN)
  have he := quarterRoot_pow_four h0
  by_contra he'
  have hlt : quarterRoot N < 1 := lt_of_not_ge he'
  have h1 : (quarterRoot N)^2 < 1 := by nlinarith
  nlinarith [sq_nonneg ((quarterRoot N)^2)]

theorem tendsto_quarterRoot : Tendsto quarterRoot atTop atTop :=
  Real.tendsto_sqrt_atTop.comp Real.tendsto_sqrt_atTop

theorem tendsto_inv_quarterRoot_nat :
    Tendsto (fun n : ℕ => 1/quarterRoot n) atTop (𝓝 0) :=
  (tendsto_quarterRoot.comp tendsto_natCast_atTop_atTop).const_div_atTop 1

theorem log_div_quarterRoot_le {N : ℝ} (hN : 0 < N) : Real.log N/quarterRoot N ≤ 4 := by
  have hq := quarterRoot_pos hN
  have he := quarterRoot_pow_four hN.le
  have hl := Real.log_le_sub_one_of_pos hq
  apply (div_le_iff₀ hq).mpr
  calc
    Real.log N = Real.log ((quarterRoot N)^4) := congrArg Real.log he.symm
    _ = 4*Real.log (quarterRoot N) := by rw [Real.log_pow]; norm_num
    _ ≤ 4*quarterRoot N := by linarith

theorem quadrature_scale_rate {N C M L : ℝ} (hN : 1 ≤ N) (hC : 0 ≤ C) (hM : 0 ≤ M) :
    L*(1/quarterRoot N)+8*M*(1/(quarterRoot N)^2)/(Real.pi*(1/quarterRoot N)) +
      C*M*(((1+Real.log N)/N)/(1/(quarterRoot N)^2)+(1/(quarterRoot N)^2)^2) ≤
      (L+8*M/Real.pi+5*C*M)/quarterRoot N := by
  let q := quarterRoot N
  have hq : 0 < q := quarterRoot_pos (zero_lt_one.trans_le hN)
  have hq1 : 1 ≤ q := one_le_quarterRoot hN
  have he : q^4 = N := quarterRoot_pow_four (zero_le_one.trans hN)
  have hlog : 1+Real.log N ≤ 4*q := by
    rw [← he, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    have hl := Real.log_le_sub_one_of_pos hq
    linarith
  have hterm : ((1+Real.log N)/N)/(1/q^2) ≤ 4/q := by
    rw [← he]
    have heq : ((1+Real.log (q^4))/q^4)/(1/q^2) = (1+Real.log (q^4))/q^2 := by field_simp
    rw [heq]
    apply (div_le_iff₀ (sq_pos_of_pos hq)).mpr
    have heq2 : 4/q*q^2 = 4*q := by field_simp
    rw [heq2]
    simpa only [he] using hlog
  have hpow : (1/q^2)^2 ≤ 1/q := by
    rw [div_pow, one_pow]
    apply one_div_le_one_div_of_le hq
    nlinarith [sq_nonneg (q^2-1)]
  have hsum : ((1+Real.log N)/N)/(1/q^2)+(1/q^2)^2 ≤ 5/q := by
    have hh := add_le_add hterm hpow
    convert! hh using 1 <;> ring
  have hmul := mul_le_mul_of_nonneg_left hsum (mul_nonneg hC hM)
  have heq : 8*M*(1/q^2)/(Real.pi*(1/q)) = (8*M/Real.pi)/q := by field_simp
  change L*(1/q)+8*M*(1/q^2)/(Real.pi*(1/q))+_ ≤ _
  rw [heq]
  calc
    _ ≤ L*(1/q)+(8*M/Real.pi)/q+C*M*(5/q) := by linarith
    _ = _ := by ring

theorem uniform_local_quadrature_rate {a b d l r M L : ℝ} (hab : a < b)
    (hI : Icc a b ⊆ Icc (-1) 1) (hd : 0 < d) (hlr : l ≤ r)
    (hJ : Icc l r ⊆ Icc (a+d) (b-d)) (hM : 0 ≤ M) (hL : 0 ≤ L) :
    ∃ C > 0, ∀ (n : ℕ) (X : Nodes n), 0 < n →
      (∀ y ∈ Icc a b, X.lebesgue y ≤ n) →
      ∀ f : ℝ → ℝ, Measurable f → (∀ x, |f x| ≤ M) →
      (∀ x y, |f x-f y| ≤ L*|x-y|) → (∀ x, x ∉ Icc l r → f x = 0) →
      |(∑ i, f (X.point i))/(n : ℝ)-
        ∫ x, X.exteriorDensity a b X.potentialNormalization x 0*f x| ≤ C/quarterRoot n := by
  obtain ⟨C, hC, hquad⟩ := uniform_local_quadrature hab hI hd hlr hJ
  refine ⟨L+8*M/Real.pi+5*C*M+1, by positivity, ?_⟩
  intro n X hn hΛ f hf hMf hlip hsupp
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hq : 0 < quarterRoot n := quarterRoot_pos hnR
  have hq1 := one_le_quarterRoot hn1
  have hscale : 1/(n : ℝ) ≤ 1/(quarterRoot n)^2 := by
    apply one_div_le_one_div_of_le (sq_pos_of_pos hq)
    calc
      (quarterRoot n)^2 ≤ (quarterRoot n)^4 := by nlinarith [sq_nonneg ((quarterRoot n)^2-1)]
      _ = _ := quarterRoot_pow_four hnR.le
  have he := hquad n X hn hΛ f M L (1/(quarterRoot n)^2) (1/quarterRoot n)
    hf hMf hL hlip hsupp (by positivity) hscale
  have hb := quadrature_scale_rate (L := L) hn1 hC.le hM
  exact (he.trans hb).trans (div_le_div_of_nonneg_right (by linarith) hq.le)

end TaoAdditive1132
end
end SourceErdos1132_Additive_QuadratureRate

/- Erdos1132.Additive.DensityPositive -/
section SourceErdos1132_Additive_DensityPositive
/- # Positivity of the density forced by a decrease of the logarithmic potential

Main paper: §4, local potential and differentiation estimates.
-/

noncomputable section
open Set Filter Real
open scoped Topology
namespace TaoAdditive1132

theorem density_lower_of_two_heights {C e h ρ α U₁ U₂ : ℝ}
    (hh : 0 < h) (hCh : C*h ≤ 1/256) (hCe : C*e ≤ h^2/1024)
    (hdrop : h^2/32 ≤ U₁-U₂)
    (h₁ : |U₁-α+Real.pi*(h/2)*ρ| ≤ C*(e+(h/2)^3))
    (h₂ : |U₂-α+Real.pi*h*ρ| ≤ C*(e+h^3)) :
    h/(64*Real.pi) ≤ ρ := by
  have h₁' := (abs_le.mp h₁).2
  have h₂' := (abs_le.mp h₂).1
  have hcubic := mul_le_mul_of_nonneg_right hCh (sq_nonneg h)
  have hmain : h^2/64 ≤ Real.pi*h*ρ/2 := by nlinarith
  apply (div_le_iff₀ (mul_pos (by norm_num) Real.pi_pos)).mpr
  have hfactor : h*(h-64*Real.pi*ρ) ≤ 0 := by nlinarith
  have hl : h-64*Real.pi*ρ ≤ 0 := by
    by_contra he
    exact (mul_pos hh (lt_of_not_ge he)).not_ge hfactor
  nlinarith

/-- The density is bounded below uniformly for all sufficiently large rows of
any array with the stated eventual intervalwise Lebesgue bound. -/
theorem eventually_exterior_density_positive (X : ∀ n, Nodes n) {a b d : ℝ}
    (hab : a < b) (hI : Icc a b ⊆ Icc (-1) 1) (hd : 0 < d)
    (hΛ : ∀ᶠ n : ℕ in atTop, ∀ y ∈ Icc a b, (X n).lebesgue y ≤ n) :
    ∃ c > 0, ∀ᶠ n : ℕ in atTop, ∀ x ∈ Icc (a+d) (b-d),
      c ≤ (X n).exteriorDensity a b (X n).potentialNormalization x 0 := by
  obtain ⟨C, hC, hest⟩ := uniform_complex_potential_expansion hab hI hd
  let h := min 1 (1/(256*(C+1)))
  have hh : 0 < h := lt_min (by norm_num) (by positivity)
  have hh1 : h ≤ 1 := min_le_left _ _
  have hCh : C*h ≤ 1/256 := by
    have hhmax : h ≤ 1/(256*(C+1)) := min_le_right _ _
    have hmul := (le_div_iff₀ (by positivity : 0 < 256*(C+1))).mp hhmax
    nlinarith
  have hε : ∀ᶠ n : ℕ in atTop, C*potentialErrorSize n ≤ h^2/1024 := by
    have ht : Tendsto (fun n => C*potentialErrorSize n) atTop (𝓝 0) := by
      simpa only [mul_zero] using tendsto_potentialErrorSize.const_mul C
    exact (ht.eventually (Iio_mem_nhds (by positivity : 0 < h^2/1024))).mono (fun _ hn => hn.le)
  have hinv : ∀ᶠ n : ℕ in atTop, 1/(n : ℝ) ≤ h/2 :=
    (tendsto_one_div_atTop_nhds_zero_nat.eventually
      (Iio_mem_nhds (by positivity : (0 : ℝ) < h/2))).mono (fun _ hn => hn.le)
  refine ⟨h/(64*Real.pi), by positivity, ?_⟩
  filter_upwards [hΛ, hε, hinv, eventually_gt_atTop (0 : ℕ)] with n hnΛ hnε hni hn
  intro x hx
  have h1 := hest n (X n) hn hnΛ x hx (h/2) hni
  have h2 := hest n (X n) hn hnΛ x hx h (hni.trans (by linarith))
  have hdrop := (X n).complexLogPotential_height_drop hn
    (hI (mem_interval_of_inset hd.le hx)) hh hh1
  exact density_lower_of_two_heights hh hCh hnε hdrop h1 h2

end TaoAdditive1132
end
end SourceErdos1132_Additive_DensityPositive

/- Erdos1132.Additive.WeightedQuadrature -/
section SourceErdos1132_Additive_WeightedQuadrature
/- # Quadrature for the actual squared weight divided by the local density

Main paper: §5, derivative-jump energy.
-/

noncomputable section
open MeasureTheory Set Finset Filter Real
open scoped BigOperators Topology
namespace TaoAdditive1132

theorem eventually_weighted_square_quadrature (X : ∀ n, Nodes n)
    {a b d l r M L : ℝ} (hab : a < b) (hI : Icc a b ⊆ Icc (-1) 1)
    (hd : 0 < d) (hlr : l ≤ r) (hJ : Icc l r ⊆ Icc (a+d) (b-d))
    (hM : 0 ≤ M) (hL : 0 ≤ L) {f : ℝ → ℝ} (hf : Measurable f)
    (hMf : ∀ x, |f x| ≤ M) (hlip : ∀ x y, |f x-f y| ≤ L*|x-y|)
    (hsupp : ∀ x, x ∉ Icc l r → f x = 0)
    (hΛ : ∀ᶠ n : ℕ in atTop, ∀ y ∈ Icc a b, (X n).lebesgue y ≤ n) :
    ∃ C > 0, ∀ᶠ n : ℕ in atTop,
      |(∑ i, (f ((X n).point i))^2/
        (X n).exteriorDensity a b (X n).potentialNormalization ((X n).point i) 0)/(n : ℝ)-
        (∫ x, (f x)^2)| ≤ C/quarterRoot n := by
  obtain ⟨c, hc, hpos⟩ := eventually_exterior_density_positive X hab hI hd hΛ
  obtain ⟨D, hD, hDb⟩ := uniform_exterior_density_bounds hab hI hd
  obtain ⟨C, hC, hq⟩ := uniform_local_quadrature_rate (M := M^2/c)
    (L := 2*M*L/c+M^2*D/c^2) hab hI hd hlr hJ (by positivity) (by positivity)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hΛ, hpos, eventually_gt_atTop (0:ℕ)] with n hnΛ hnp hn
  let ρ (x : ℝ) := (X n).exteriorDensity a b (X n).potentialNormalization x 0
  let R (x : ℝ) := ρ (projIcc l r hlr x)
  have hRm : Measurable R :=
    ((X n).measurable_exteriorDensity a b (X n).potentialNormalization 0).comp
      (continuous_subtype_val.comp continuous_projIcc).measurable
  have hRpos (x : ℝ) : c ≤ R x := hnp _ (hJ (projIcc l r hlr x).property)
  have hRlip (x y : ℝ) : |R x-R y| ≤ D*|x-y| := by
    exact ((hDb n (X n) hn hnΛ).2 _ (hJ (projIcc l r hlr x).property)
      _ (hJ (projIcc l r hlr y).property)).trans
        (mul_le_mul_of_nonneg_left (abs_projIcc_sub_le hlr x y) hD.le)
  let g (x : ℝ) := (f x)^2/R x
  have hgm : Measurable g := (hf.pow_const 2).div hRm
  have hgb (x : ℝ) : |g x| ≤ M^2/c := square_div_bound hc (hRpos x) hM (hMf x)
  have hgl (x y : ℝ) : |g x-g y| ≤ (2*M*L/c+M^2*D/c^2)*|x-y| :=
    square_div_lipschitz hM hL hc hD.le hMf hRpos hlip hRlip x y
  have hgs (x : ℝ) (hx : x ∉ Icc l r) : g x = 0 := by simp [g, hsupp x hx]
  have hR_eq (x : ℝ) (hx : x ∈ Icc l r) : R x = ρ x := by
    simp only [R, projIcc_of_mem hlr hx]
  have hg_eq (x : ℝ) : g x = (f x)^2/ρ x := by
    by_cases hx : x ∈ Icc l r
    · dsimp only [g]; rw [hR_eq x hx]
    · simp [hgs x hx, hsupp x hx]
  have hint (x : ℝ) : ρ x*g x = (f x)^2 := by
    by_cases hx : x ∈ Icc l r
    · rw [hg_eq]
      have hρ : ρ x ≠ 0 := (hc.trans_le (hnp x (hJ hx))).ne'
      field_simp
    · rw [hgs x hx, hsupp x hx]; ring
  have h := hq n (X n) hn hnΛ g hgm hgb hgl hgs
  change |(∑ i, g ((X n).point i))/(n : ℝ)-(∫ x, ρ x*g x)| ≤ _ at h
  simp_rw [hint] at h
  simpa only [hg_eq] using h

end TaoAdditive1132
end
end SourceErdos1132_Additive_WeightedQuadrature

/- Erdos1132.Additive.IntervalWeight -/
section SourceErdos1132_Additive_IntervalWeight
/- # An explicit nonzero Lipschitz weight on any compact interval

Main paper: §6, recurrence and Theorem 1(i).
-/

noncomputable section
open Set MeasureTheory Real
namespace TaoAdditive1132

def intervalWeight (l r x : ℝ) : ℝ := max 0 (min (x-l) (r-x))

theorem continuous_intervalWeight (l r : ℝ) : Continuous (intervalWeight l r) := by
  unfold intervalWeight
  fun_prop

theorem intervalWeight_nonneg (l r x : ℝ) : 0 ≤ intervalWeight l r x := le_max_left _ _

theorem intervalWeight_zero_off {l r x : ℝ} (hx : x ∉ Icc l r) : intervalWeight l r x = 0 := by
  unfold intervalWeight
  apply max_eq_left
  by_cases hxl : l ≤ x
  · have hxr : r < x := lt_of_not_ge (fun h => hx ⟨hxl, h⟩)
    exact (min_le_right _ _).trans (by linarith)
  · exact (min_le_left _ _).trans (by linarith)

theorem intervalWeight_bound {l r : ℝ} (hlr : l ≤ r) (x : ℝ) : intervalWeight l r x ≤ r-l := by
  by_cases hx : x ∈ Icc l r
  · apply max_le (by linarith)
    exact (min_le_left _ _).trans (by linarith [hx.2])
  · rw [intervalWeight_zero_off hx]; linarith

theorem intervalWeight_lipschitz (l r x y : ℝ) :
    |intervalWeight l r x-intervalWeight l r y| ≤ |x-y| := by
  have hmin := abs_min_sub_min_le_max (x-l) (r-x) (y-l) (r-y)
  have hmax := abs_max_sub_max_le_max (0:ℝ) (min (x-l) (r-x)) 0 (min (y-l) (r-y))
  have he1 : (x-l)-(y-l) = x-y := by ring
  have he2 : (r-x)-(r-y) = -(x-y) := by ring
  rw [he1, he2, abs_neg, max_self] at hmin
  simp only [sub_self, abs_zero] at hmax
  rw [max_eq_right (abs_nonneg (min (x-l) (r-x)-min (y-l) (r-y)))] at hmax
  exact hmax.trans hmin

theorem hasCompactSupport_intervalWeight (l r : ℝ) : HasCompactSupport (intervalWeight l r) :=
  HasCompactSupport.intro isCompact_Icc (fun x hx => intervalWeight_zero_off hx)

theorem integrable_intervalWeight (l r : ℝ) : Integrable (intervalWeight l r) :=
  (continuous_intervalWeight l r).integrable_of_hasCompactSupport (hasCompactSupport_intervalWeight l r)

theorem integral_intervalWeight_sq_pos {l r : ℝ} (hlr : l < r) :
    0 < ∫ x, (intervalWeight l r x)^2 := by
  have hcomp : HasCompactSupport (fun x => (intervalWeight l r x)^2) :=
    HasCompactSupport.intro isCompact_Icc (fun x hx => by rw [intervalWeight_zero_off hx]; norm_num)
  have hm : intervalWeight l r ((l+r)/2) = (r-l)/2 := by
    have h1 : (l+r)/2-l = (r-l)/2 := by ring
    have h2 : r-(l+r)/2 = (r-l)/2 := by ring
    rw [intervalWeight, h1, h2, min_self, max_eq_right (by linarith)]
  exact ((continuous_intervalWeight l r).pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero
    (x := (l+r)/2) hcomp (fun x => sq_nonneg _) (by
      change (intervalWeight l r ((l+r)/2))^2 ≠ 0
      rw [hm]; positivity)

end TaoAdditive1132
end
end SourceErdos1132_Additive_IntervalWeight

/- Erdos1132.Additive.RieszKernel -/
section SourceErdos1132_Additive_RieszKernel
/- # The regularized inverse-distance kernel and its Gaussian representation

Main paper: §5, derivative-jump energy.
-/

noncomputable section
open Real MeasureTheory
namespace TaoAdditive1132

def rieszKernel (ε t : ℝ) : ℝ := 1/Real.sqrt (t^2+ε^2)

theorem rieszKernel_pos {ε : ℝ} (hε : 0 < ε) (t : ℝ) : 0 < rieszKernel ε t := by
  unfold rieszKernel
  positivity

theorem rieszKernel_even (ε t : ℝ) : rieszKernel ε (-t) = rieszKernel ε t := by
  simp [rieszKernel]

theorem rieszKernel_diagonal {ε : ℝ} (hε : 0 ≤ ε) : rieszKernel ε 0 = 1/ε := by
  simp [rieszKernel, Real.sqrt_sq hε]

theorem rieszKernel_le_diagonal {ε : ℝ} (hε : 0 < ε) (t : ℝ) : rieszKernel ε t ≤ 1/ε := by
  apply one_div_le_one_div_of_le hε
  calc
    ε = Real.sqrt (ε^2) := (Real.sqrt_sq hε.le).symm
    _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg t])

theorem rieszKernel_le_inverse_distance {ε t : ℝ} (ht : t ≠ 0) :
    rieszKernel ε t ≤ 1/|t| := by
  apply one_div_le_one_div_of_le (abs_pos.mpr ht)
  calc
    |t| = Real.sqrt (t^2) := (Real.sqrt_sq_eq_abs t).symm
    _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ε])

theorem continuous_rieszKernel {ε : ℝ} (hε : 0 < ε) : Continuous (rieszKernel ε) := by
  unfold rieszKernel
  apply continuous_const.div (by fun_prop)
  intro t
  exact (Real.sqrt_pos.mpr (by nlinarith [sq_nonneg t, sq_pos_of_pos hε])).ne'

theorem integrable_riesz_gaussian_mixture {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    Integrable (fun s : ℝ => Real.exp (-s^2*ε^2)*Real.exp (-s^2*t^2)) := by
  have hi := integrable_exp_neg_mul_sq (by nlinarith [sq_nonneg t, sq_pos_of_pos hε] : 0 < t^2+ε^2)
  convert hi using 1
  funext s
  rw [← Real.exp_add]
  congr 1
  ring

/-- Integrating over the real Gaussian parameter avoids a separate Gamma-integral
normalization and gives the exact inverse square-root kernel. -/
theorem rieszKernel_gaussian_mixture {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    rieszKernel ε t = (1/Real.sqrt Real.pi)*
      ∫ s : ℝ, Real.exp (-s^2*ε^2)*Real.exp (-s^2*t^2) := by
  have he : (fun s : ℝ => Real.exp (-s^2*ε^2)*Real.exp (-s^2*t^2)) =
      (fun s => Real.exp (-(t^2+ε^2)*s^2)) := by
    funext s
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he, integral_gaussian, Real.sqrt_div Real.pi_pos.le]
  unfold rieszKernel
  have hp : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  field_simp

end TaoAdditive1132
end
end SourceErdos1132_Additive_RieszKernel

/- Erdos1132.Additive.GaussianEnergy -/
section SourceErdos1132_Additive_GaussianEnergy
/- # Positivity of Gaussian energy for bounded signed densities

The exponential series expresses each finite approximation as a sum of
squares of moments. Dominated convergence then proves positivity of the
actual Gaussian kernel.

Main paper: §5, derivative-jump energy.
-/

noncomputable section
open Real MeasureTheory Filter Finset
open scoped Topology BigOperators
namespace TaoAdditive1132

theorem abs_exp_partial_sum_le (z : ℝ) (N : ℕ) :
    |∑ k ∈ range N, z^k/(k.factorial : ℝ)| ≤ Real.exp |z| := by
  calc
    _ ≤ ∑ k ∈ range N, |z^k/(k.factorial : ℝ)| := abs_sum_le_sum_abs _ _
    _ = ∑ k ∈ range N, |z|^k/(k.factorial : ℝ) := by simp only [abs_div, abs_pow, Nat.abs_cast]
    _ ≤ _ := Real.sum_le_exp_of_nonneg (abs_nonneg _) _

theorem tendsto_exp_partial_sum (z : ℝ) :
    Tendsto (fun N : ℕ => ∑ k ∈ range N, z^k/(k.factorial : ℝ))
      atTop (𝓝 (Real.exp z)) := by
  simpa only [Real.exp_eq_exp_ℝ] using
    (NormedSpace.expSeries_div_hasSum_exp z).tendsto_sum_nat

theorem gaussian_energy_nonneg {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {x w : α → ℝ}
    (hx : Measurable x) (hw : Measurable w) {B s : ℝ}
    (hB : 0 ≤ B) (hs : 0 ≤ s)
    (hxb : ∀ u, |x u| ≤ 1) (hwb : ∀ u, |w u| ≤ B) :
    0 ≤ ∫ p : α × α,
      w p.1*w p.2*Real.exp (-s*(x p.1-x p.2)^2) ∂μ.prod μ := by
  let φ (k : ℕ) (u : α) := w u*Real.exp (-s*(x u)^2)*(x u)^k
  have hφm (k : ℕ) : Measurable (φ k) := by dsimp [φ]; fun_prop
  have hφb (k : ℕ) (u : α) : |φ k u| ≤ B := by
    have he : Real.exp (-s*(x u)^2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (x u)])
    have hp : |x u|^k ≤ 1 := pow_le_one₀ (abs_nonneg _) (hxb u)
    dsimp [φ]
    rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_pow]
    calc
      _ ≤ B*1*1 := mul_le_mul (mul_le_mul (hwb u) he (Real.exp_pos _).le hB)
        hp (by positivity) (by positivity)
      _ = B := by ring
  have hφi (k : ℕ) : Integrable (φ k) μ :=
    (integrable_const B).mono' (hφm k).aestronglyMeasurable
      (ae_of_all _ (fun u => by simpa only [Real.norm_eq_abs] using hφb k u))
  let F (N : ℕ) (p : α × α) := ∑ k ∈ range N,
    ((2*s)^k/(k.factorial : ℝ))*(φ k p.1*φ k p.2)
  have hFm (N : ℕ) : Measurable (F N) := by dsimp [F]; fun_prop
  have hFi (N : ℕ) : Integrable (F N) (μ.prod μ) := by
    apply integrable_finsetSum
    intro k hk
    exact ((hφi k).mul_prod (hφi k)).const_mul _
  have hpos (N : ℕ) : 0 ≤ ∫ p, F N p ∂μ.prod μ := by
    rw [show F N = (fun p => ∑ k ∈ range N,
      ((2*s)^k/(k.factorial : ℝ))*(φ k p.1*φ k p.2)) from rfl,
      integral_finsetSum _ (fun k hk => ((hφi k).mul_prod (hφi k)).const_mul _)]
    apply sum_nonneg
    intro k hk
    rw [integral_const_mul, integral_prod_mul]
    exact mul_nonneg (by positivity) (mul_self_nonneg _)
  have hFb (N : ℕ) (p : α × α) : |F N p| ≤ B^2*Real.exp (2*s) := by
    calc
      _ ≤ ∑ k ∈ range N, |((2*s)^k/(k.factorial : ℝ))*(φ k p.1*φ k p.2)| :=
        abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ range N, ((2*s)^k/(k.factorial : ℝ))*B^2 := by
        apply sum_le_sum
        intro k hk
        rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (2*s)^k/(k.factorial : ℝ)), abs_mul]
        gcongr
        simpa only [pow_two] using mul_le_mul (hφb k p.1) (hφb k p.2) (abs_nonneg _) hB
      _ = B^2*(∑ k ∈ range N, (2*s)^k/(k.factorial : ℝ)) := by rw [mul_sum]; congr 1; funext k; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sum_le_exp_of_nonneg (by positivity) N) (sq_nonneg B)
  have hFform (N : ℕ) (p : α × α) : F N p =
      (w p.1*w p.2*Real.exp (-s*(x p.1)^2)*Real.exp (-s*(x p.2)^2))*
        (∑ k ∈ range N, (2*s*x p.1*x p.2)^k/(k.factorial : ℝ)) := by
    dsimp only [F]
    rw [mul_sum]
    apply sum_congr rfl
    intro k hk
    dsimp [φ]
    simp only [mul_pow]
    ring
  have hlim (p : α × α) : Tendsto (fun N => F N p) atTop
      (𝓝 (w p.1*w p.2*Real.exp (-s*(x p.1-x p.2)^2))) := by
    simp_rw [hFform]
    have h := (tendsto_exp_partial_sum (2*s*x p.1*x p.2)).const_mul
      (w p.1*w p.2*Real.exp (-s*(x p.1)^2)*Real.exp (-s*(x p.2)^2))
    convert h using 1
    congr 1
    rw [mul_assoc (w p.1*w p.2), mul_assoc (w p.1*w p.2), ← Real.exp_add, ← Real.exp_add]
    congr 2
    ring
  have hconv := tendsto_integral_of_dominated_convergence (μ := μ.prod μ)
    (fun _ : α × α => B^2*Real.exp (2*s))
    (fun N => (hFm N).aestronglyMeasurable) (integrable_const _)
    (fun N => ae_of_all _ (fun p => by simpa only [Real.norm_eq_abs] using hFb N p))
    (ae_of_all _ hlim)
  exact ge_of_tendsto hconv (Eventually.of_forall hpos)

end TaoAdditive1132
end
end SourceErdos1132_Additive_GaussianEnergy

/- Erdos1132.Additive.RieszEnergy -/
section SourceErdos1132_Additive_RieszEnergy
/- # Positivity of regularized inverse-distance energy

Main paper: §5, derivative-jump energy.
-/

noncomputable section
open Real MeasureTheory Filter
namespace TaoAdditive1132

theorem integrable_weighted_riesz_pair {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {x a : α → ℝ} {y b : β → ℝ} (hx : Measurable x) (ha : Measurable a)
    (hy : Measurable y) (hb : Measurable b) {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε)
    (hab : ∀ u, |a u| ≤ B) (hbb : ∀ v, |b v| ≤ B) :
    Integrable (fun p : α × β => a p.1*b p.2*rieszKernel ε (x p.1-y p.2)) (μ.prod ν) := by
  apply (integrable_const (B^2/ε)).mono'
  · exact (((ha.comp measurable_fst).mul (hb.comp measurable_snd)).mul
      ((continuous_rieszKernel hε).measurable.comp
        ((hx.comp measurable_fst).sub (hy.comp measurable_snd)))).aestronglyMeasurable
  · apply ae_of_all
    intro p
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (rieszKernel_pos hε _)]
    calc
      _ ≤ B^2*(1/ε) := mul_le_mul
        (by simpa only [pow_two] using mul_le_mul (hab p.1) (hbb p.2) (abs_nonneg _) hB)
        (rieszKernel_le_diagonal hε _) (rieszKernel_pos hε _).le (sq_nonneg B)
      _ = _ := by ring

theorem riesz_energy_nonneg {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {x w : α → ℝ}
    (hx : Measurable x) (hw : Measurable w) {B ε : ℝ}
    (hB : 0 ≤ B) (hε : 0 < ε)
    (hxb : ∀ u, |x u| ≤ 1) (hwb : ∀ u, |w u| ≤ B) :
    0 ≤ ∫ p : α × α, w p.1*w p.2*rieszKernel ε (x p.1-x p.2) ∂μ.prod μ := by
  let F (s : ℝ) (p : α × α) := Real.exp (-s^2*ε^2)*
    (w p.1*w p.2*Real.exp (-s^2*(x p.1-x p.2)^2))
  have hFm : Measurable (Function.uncurry F) := by dsimp [F, Function.uncurry]; fun_prop
  have hb (s : ℝ) (p : α × α) : ‖F s p‖ ≤ Real.exp (-ε^2*s^2)*B^2 := by
    have he : Real.exp (-s^2*(x p.1-x p.2)^2) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by
        have hh := mul_nonneg (sq_nonneg s) (sq_nonneg (x p.1-x p.2))
        nlinarith)
    have hw' : |w p.1| * |w p.2| ≤ B^2 := by
      simpa only [pow_two] using mul_le_mul (hwb p.1) (hwb p.2) (abs_nonneg _) hB
    dsimp [F]
    rw [abs_mul, abs_mul, abs_mul,
      abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
    rw [show -s^2*ε^2 = -ε^2*s^2 by ring]
    exact mul_le_mul_of_nonneg_left
      (by simpa using mul_le_mul hw' he (Real.exp_pos _).le (sq_nonneg B)) (Real.exp_pos _).le
  have hi : Integrable (Function.uncurry F) (volume.prod (μ.prod μ)) := by
    have henv := (integrable_exp_neg_mul_sq (sq_pos_of_pos hε)).mul_prod
      (integrable_const (μ := μ.prod μ) (B^2))
    exact henv.mono' hFm.aestronglyMeasurable (ae_of_all _ (fun p => hb p.1 p.2))
  have hnonneg : 0 ≤ ∫ s : ℝ, ∫ p, F s p ∂μ.prod μ := by
    apply integral_nonneg
    intro s
    dsimp only [F]
    rw [integral_const_mul]
    exact mul_nonneg (Real.exp_pos _).le
      (gaussian_energy_nonneg μ hx hw hB (sq_nonneg s) hxb hwb)
  rw [integral_integral_swap hi] at hnonneg
  have hmix (p : α × α) : (∫ s : ℝ, F s p) =
      Real.sqrt Real.pi * (w p.1*w p.2*rieszKernel ε (x p.1-x p.2)) := by
    have he : (fun s : ℝ => F s p) = (fun s => (w p.1*w p.2)*
      (Real.exp (-s^2*ε^2)*Real.exp (-s^2*(x p.1-x p.2)^2))) := by funext s; dsimp [F]; ring
    rw [he, integral_const_mul, rieszKernel_gaussian_mixture hε]
    have hp : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
    field_simp
    congr 1
    apply integral_congr_ae
    exact ae_of_all _ (fun s => by congr 1 <;> ring)
  simp_rw [hmix] at hnonneg
  rw [integral_const_mul] at hnonneg
  exact nonneg_of_mul_nonneg_right hnonneg (Real.sqrt_pos.mpr Real.pi_pos)

end TaoAdditive1132
end
end SourceErdos1132_Additive_RieszEnergy

/- Erdos1132.Additive.DisjointEnergy -/
section SourceErdos1132_Additive_DisjointEnergy
/- # Energy expansion on a disjoint union of two finite measure spaces

Main paper: §5, derivative-jump energy.
-/

noncomputable section
open MeasureTheory
namespace TaoAdditive1132

def disjointMeasure {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) : Measure (α ⊕ β) :=
  Measure.map Sum.inl μ + Measure.map Sum.inr ν

instance {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    IsFiniteMeasure (disjointMeasure μ ν) := by unfold disjointMeasure; infer_instance

theorem integral_disjoint_product {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {H : (α ⊕ β) × (α ⊕ β) → ℝ} (hH : Measurable H)
    {C : ℝ} (hbound : ∀ p, ‖H p‖ ≤ C) :
    (∫ p, H p ∂(disjointMeasure μ ν).prod (disjointMeasure μ ν)) =
      (∫ p : α × α, H (Sum.inl p.1, Sum.inl p.2) ∂μ.prod μ) +
      (∫ p : α × β, H (Sum.inl p.1, Sum.inr p.2) ∂μ.prod ν) +
      (∫ p : β × α, H (Sum.inr p.1, Sum.inl p.2) ∂ν.prod μ) +
      (∫ p : β × β, H (Sum.inr p.1, Sum.inr p.2) ∂ν.prod ν) := by
  have hi (τ : Measure ((α ⊕ β) × (α ⊕ β))) [IsFiniteMeasure τ] : Integrable H τ :=
    (integrable_const C).mono' hH.aestronglyMeasurable (ae_of_all _ hbound)
  unfold disjointMeasure
  rw [Measure.add_prod, Measure.prod_add, Measure.prod_add,
    integral_add_measure (hi _) (hi _),
    integral_add_measure (hi _) (hi _), integral_add_measure (hi _) (hi _)]
  simp_rw [Measure.map_prod_map _ _ measurable_inl measurable_inl,
    Measure.map_prod_map _ _ measurable_inl measurable_inr,
    Measure.map_prod_map _ _ measurable_inr measurable_inl,
    Measure.map_prod_map _ _ measurable_inr measurable_inr,
    integral_map_of_stronglyMeasurable (measurable_inl.prodMap measurable_inl) hH.stronglyMeasurable,
    integral_map_of_stronglyMeasurable (measurable_inl.prodMap measurable_inr) hH.stronglyMeasurable,
    integral_map_of_stronglyMeasurable (measurable_inr.prodMap measurable_inl) hH.stronglyMeasurable,
    integral_map_of_stronglyMeasurable (measurable_inr.prodMap measurable_inr) hH.stronglyMeasurable]
  simp only [add_assoc]
  rfl

/-- Positivity applied to the difference of two bounded weighted measures. -/
theorem riesz_energy_comparison {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {x a : α → ℝ} {y b : β → ℝ} (hx : Measurable x) (ha : Measurable a)
    (hy : Measurable y) (hb : Measurable b) {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε)
    (hxb : ∀ u, |x u| ≤ 1) (hyb : ∀ v, |y v| ≤ 1)
    (hab : ∀ u, |a u| ≤ B) (hbb : ∀ v, |b v| ≤ B) :
    2*(∫ p : α × β, a p.1*b p.2*rieszKernel ε (x p.1-y p.2) ∂μ.prod ν) -
        (∫ p : β × β, b p.1*b p.2*rieszKernel ε (y p.1-y p.2) ∂ν.prod ν) ≤
      ∫ p : α × α, a p.1*a p.2*rieszKernel ε (x p.1-x p.2) ∂μ.prod μ := by
  let X := Sum.elim x y
  let W := Sum.elim a (fun v => -b v)
  have hX : Measurable X := hx.sumElim hy
  have hW : Measurable W := ha.sumElim hb.neg
  have hXb (u : α ⊕ β) : |X u| ≤ 1 := by cases u with
    | inl u => exact hxb u
    | inr v => exact hyb v
  have hWb (u : α ⊕ β) : |W u| ≤ B := by cases u with
    | inl u => exact hab u
    | inr v => simpa [W] using hbb v
  let H (p : (α ⊕ β) × (α ⊕ β)) := W p.1*W p.2*rieszKernel ε (X p.1-X p.2)
  have hHm : Measurable H := by
    exact ((hW.comp measurable_fst).mul (hW.comp measurable_snd)).mul
      ((continuous_rieszKernel hε).measurable.comp
        ((hX.comp measurable_fst).sub (hX.comp measurable_snd)))
  have hHb (p : (α ⊕ β) × (α ⊕ β)) : ‖H p‖ ≤ B^2/ε := by
    dsimp [H]
    rw [abs_mul, abs_mul, abs_of_pos (rieszKernel_pos hε _)]
    calc
      _ ≤ B^2*(1/ε) := mul_le_mul
        (by simpa only [pow_two] using mul_le_mul (hWb p.1) (hWb p.2) (abs_nonneg _) hB)
        (rieszKernel_le_diagonal hε _) (rieszKernel_pos hε _).le (sq_nonneg B)
      _ = _ := by ring
  have hp := riesz_energy_nonneg (disjointMeasure μ ν) hX hW hB hε hXb hWb
  change 0 ≤ ∫ p, H p ∂(disjointMeasure μ ν).prod (disjointMeasure μ ν) at hp
  rw [integral_disjoint_product μ ν hHm hHb] at hp
  dsimp [H, W, X] at hp
  simp only [mul_neg, neg_mul, neg_neg, integral_neg] at hp
  have hswap : (∫ p : β × α, b p.1*a p.2*rieszKernel ε (y p.1-x p.2) ∂ν.prod μ) =
      ∫ p : α × β, a p.1*b p.2*rieszKernel ε (x p.1-y p.2) ∂μ.prod ν := by
    rw [← integral_prod_swap]
    apply integral_congr_ae
    exact ae_of_all _ (fun p => by
      dsimp
      rw [show y p.2-x p.1 = -(x p.1-y p.2) by ring, rieszKernel_even]
      ring)
  rw [hswap] at hp
  linarith

end TaoAdditive1132
end
end SourceErdos1132_Additive_DisjointEnergy

/- Erdos1132.Additive.RieszMass -/
section SourceErdos1132_Additive_RieszMass
/- # Exact local mass of the regularized inverse-distance kernel

Main paper: §5, derivative-jump energy.
-/

noncomputable section
open Real MeasureTheory Set
namespace TaoAdditive1132

theorem rieszKernel_rescale {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    rieszKernel ε t = (1/Real.sqrt (1+(t/ε)^2))/ε := by
  have he : t^2+ε^2 = (1+(t/ε)^2)*ε^2 := by field_simp; ring
  rw [rieszKernel, he, Real.sqrt_mul (by positivity), Real.sqrt_sq hε.le]
  ring

theorem hasDerivAt_arsinh_riesz {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    HasDerivAt (fun t : ℝ => Real.arsinh (t/ε)) (rieszKernel ε t) t := by
  have h := (Real.hasDerivAt_arsinh (t/ε)).comp t ((hasDerivAt_id t).div_const ε)
  simpa only [rieszKernel_rescale hε, one_div, div_eq_mul_inv, Function.comp_def, id_eq, one_mul] using h

theorem integral_rieszKernel_unit {ε : ℝ} (hε : 0 < ε) :
    (∫ t in Icc (-1:ℝ) 1, rieszKernel ε t) = 2*Real.arsinh (1/ε) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (-1:ℝ) ≤ 1),
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hasDerivAt_arsinh_riesz hε t)
      ((continuous_rieszKernel hε).intervalIntegrable _ _)]
  rw [neg_div, Real.arsinh_neg]
  ring

theorem arsinh_inverse_log {ε : ℝ} (hε : 0 < ε) :
    Real.arsinh (1/ε) = Real.log (1/ε) + Real.log (1+Real.sqrt (1+ε^2)) := by
  have hs : Real.sqrt (1+(1/ε)^2) = Real.sqrt (1+ε^2)/ε := by
    have he : 1+(1/ε)^2 = (1+ε^2)/ε^2 := by field_simp; ring
    rw [he, Real.sqrt_div (by positivity), Real.sqrt_sq hε.le]
  rw [Real.arsinh, hs]
  have he : 1/ε+Real.sqrt (1+ε^2)/ε = (1/ε)*(1+Real.sqrt (1+ε^2)) := by ring
  rw [he, Real.log_mul (by positivity) (by positivity)]

theorem integral_rieszKernel_unit_error {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    |(∫ t in Icc (-1:ℝ) 1, rieszKernel ε t)-2*Real.log (1/ε)| ≤ 2*Real.log 3 := by
  rw [integral_rieszKernel_unit hε, arsinh_inverse_log hε]
  have hs0 := Real.sqrt_nonneg (1+ε^2)
  have hs2 : Real.sqrt (1+ε^2) ≤ 2 := by
    apply (Real.sqrt_le_iff).mpr
    constructor <;> nlinarith [sq_nonneg ε]
  have hl0 : 0 ≤ Real.log (1+Real.sqrt (1+ε^2)) := Real.log_nonneg (by linarith)
  have hl3 : Real.log (1+Real.sqrt (1+ε^2)) ≤ Real.log 3 :=
    Real.log_le_log (by positivity) (by linarith)
  rw [show 2*(Real.log (1/ε)+Real.log (1+Real.sqrt (1+ε^2)))-2*Real.log (1/ε) =
    2*Real.log (1+Real.sqrt (1+ε^2)) by ring, abs_of_nonneg (by positivity)]
  linarith

end TaoAdditive1132
end
end SourceErdos1132_Additive_RieszMass

/- Erdos1132.Additive.RieszConvolution -/
section SourceErdos1132_Additive_RieszConvolution
/- # Uniform logarithmic asymptotics of Riesz convolution

Main paper: §5, derivative-jump energy.
-/

noncomputable section
open MeasureTheory Set Real
namespace TaoAdditive1132

def rieszConvolution (ε : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y, rieszKernel ε (x-y)*f y

theorem measurable_rieszConvolution {ε : ℝ} (hε : 0 < ε)
    {f : ℝ → ℝ} (hf : Measurable f) : Measurable (rieszConvolution ε f) := by
  exact ((((continuous_rieszKernel hε).measurable.comp (measurable_fst.sub measurable_snd)).mul
    (hf.comp measurable_snd)).stronglyMeasurable.integral_prod_right').measurable

theorem rieszConvolution_bound {ε : ℝ} (hε : 0 < ε)
    {f : ℝ → ℝ} (hf : Integrable f) (x : ℝ) :
    |rieszConvolution ε f x| ≤ (1/ε)*(∫ y, |f y|) := by
  calc
    _ ≤ ∫ y, |rieszKernel ε (x-y)*f y| := abs_integral_le_integral_abs
    _ ≤ ∫ y, (1/ε)*|f y| := by
      apply integral_mono_of_nonneg (ae_of_all _ (fun y => abs_nonneg _)) (hf.abs.const_mul _)
      exact ae_of_all _ (fun y => by
        dsimp only
        rw [abs_mul, abs_of_pos (rieszKernel_pos hε _)]
        exact mul_le_mul_of_nonneg_right (rieszKernel_le_diagonal hε _) (abs_nonneg _))
    _ = _ := integral_const_mul _ _

theorem integrable_riesz_self_energy {ε : ℝ} (hε : 0 < ε)
    {f : ℝ → ℝ} (hf : Integrable f) (hfm : Measurable f) :
    Integrable (fun x => f x*rieszConvolution ε f x) := by
  apply hf.mul_bdd (measurable_rieszConvolution hε hfm).aestronglyMeasurable
  exact ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using rieszConvolution_bound hε hf x)

theorem rieszKernel_mul_abs_le_one {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    rieszKernel ε t * |t| ≤ 1 := by
  by_cases ht : t = 0
  · simp [ht]
  calc
    _ ≤ (1/|t|)*|t| := mul_le_mul_of_nonneg_right (rieszKernel_le_inverse_distance ht) (abs_nonneg _)
    _ = 1 := by field_simp

theorem integrable_riesz_convolution {ε : ℝ} (hε : 0 < ε)
    {f : ℝ → ℝ} (hf : Integrable f) (x : ℝ) :
    Integrable (fun t => rieszKernel ε t*f (x-t)) := by
  apply (hf.comp_sub_left x).bdd_mul (continuous_rieszKernel hε).aestronglyMeasurable
  exact ae_of_all _ (fun t => by
    rw [Real.norm_eq_abs, abs_of_pos (rieszKernel_pos hε _)]
    exact rieszKernel_le_diagonal hε t)

theorem riesz_convolution_mass_error {ε L : ℝ} (hε : 0 < ε) (hL : 0 ≤ L)
    {f : ℝ → ℝ} (hf : Integrable f)
    (hlip : ∀ s t, |f s-f t| ≤ L*|s-t|) (x : ℝ) :
    |(∫ t, rieszKernel ε t*f (x-t))-f x*(∫ t in Icc (-1:ℝ) 1, rieszKernel ε t)| ≤
      2*L+∫ t, |f t| := by
  let I := Icc (-1:ℝ) 1
  have hki : Integrable (I.indicator (rieszKernel ε)) :=
    (integrable_indicator_iff measurableSet_Icc).mpr
      ((continuous_rieszKernel hε).continuousOn.integrableOn_compact isCompact_Icc)
  have hfi := integrable_riesz_convolution hε hf x
  let g (t : ℝ) := rieszKernel ε t*f (x-t)-f x*I.indicator (rieszKernel ε) t
  have hgi : Integrable g := hfi.sub (hki.const_mul _)
  have hb (t : ℝ) : |g t| ≤ L*I.indicator (fun _ => (1:ℝ)) t+|f (x-t)| := by
    by_cases ht : t ∈ I
    · dsimp only [g]
      rw [indicator_of_mem ht, indicator_of_mem ht]
      have he : rieszKernel ε t*f (x-t)-f x*rieszKernel ε t =
          rieszKernel ε t*(f (x-t)-f x) := by ring
      rw [he, abs_mul, abs_of_pos (rieszKernel_pos hε _)]
      have hdiff : |f (x-t)-f x| ≤ L*|t| := by
        simpa only [sub_sub_cancel_left, abs_neg] using hlip (x-t) x
      calc
        _ ≤ rieszKernel ε t*(L*|t|) := mul_le_mul_of_nonneg_left hdiff (rieszKernel_pos hε _).le
        _ = L*(rieszKernel ε t*|t|) := by ring
        _ ≤ L*1 := mul_le_mul_of_nonneg_left (rieszKernel_mul_abs_le_one hε t) hL
        _ ≤ _ := by nlinarith [abs_nonneg (f (x-t))]
    · have ht1 : 1 < |t| := lt_of_not_ge (fun h => ht (abs_le.mp h))
      have hk1 : rieszKernel ε t ≤ 1 :=
        (rieszKernel_le_inverse_distance (by intro h; rw [h, abs_zero] at ht1; linarith)).trans
          (by simpa using (one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) ht1.le))
      dsimp only [g]
      rw [indicator_of_notMem ht, indicator_of_notMem ht]
      simp only [mul_zero, sub_zero, zero_add, abs_mul, abs_of_pos (rieszKernel_pos hε _)]
      simpa using mul_le_mul_of_nonneg_right hk1 (abs_nonneg (f (x-t)))
  have hbint : Integrable (fun t => L*I.indicator (fun _ => (1:ℝ)) t+|f (x-t)|) := by
    exact ((integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const isCompact_Icc.measure_ne_top)).const_mul L |>.add
      (hf.comp_sub_left x).abs
  have he : (∫ t, g t) = (∫ t, rieszKernel ε t*f (x-t))-
      f x*(∫ t in I, rieszKernel ε t) := by
    rw [show g = (fun t => rieszKernel ε t*f (x-t)-f x*I.indicator (rieszKernel ε) t) from rfl,
      integral_sub hfi (hki.const_mul _), integral_const_mul, integral_indicator measurableSet_Icc]
  rw [← he]
  calc
    _ ≤ ∫ t, |g t| := abs_integral_le_integral_abs
    _ ≤ ∫ t, L*I.indicator (fun _ => (1:ℝ)) t+|f (x-t)| := integral_mono hgi.abs hbint hb
    _ = _ := by
      rw [integral_add (((integrable_indicator_iff measurableSet_Icc).mpr
        (integrableOn_const isCompact_Icc.measure_ne_top)).const_mul L) (hf.comp_sub_left x).abs,
        integral_const_mul, integral_indicator measurableSet_Icc,
        integral_sub_left_eq_self (fun t => |f t|) volume x]
      simp [I]
      ring

theorem riesz_convolution_log_error {ε M L : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hL : 0 ≤ L) {f : ℝ → ℝ} (hf : Integrable f) (hM : ∀ t, |f t| ≤ M)
    (hlip : ∀ s t, |f s-f t| ≤ L*|s-t|) (x : ℝ) :
    |(∫ y, rieszKernel ε (x-y)*f y)-2*Real.log (1/ε)*f x| ≤
      2*L+(∫ t, |f t|)+2*M*Real.log 3 := by
  have he : (∫ y, rieszKernel ε (x-y)*f y) = ∫ t, rieszKernel ε t*f (x-t) := by
    have he := integral_sub_left_eq_self (fun y => rieszKernel ε (x-y)*f y) volume x
    simpa only [sub_sub_cancel] using he.symm
  rw [he]
  have h1 := riesz_convolution_mass_error hε hL hf hlip x
  have h2 := mul_le_mul (hM x) (integral_rieszKernel_unit_error hε hε1)
    (abs_nonneg _) ((abs_nonneg (f 0)).trans (hM 0))
  have hsplit := abs_add_le
    ((∫ t, rieszKernel ε t*f (x-t))-f x*(∫ t in Icc (-1:ℝ) 1, rieszKernel ε t))
    (f x*((∫ t in Icc (-1:ℝ) 1, rieszKernel ε t)-2*Real.log (1/ε)))
  rw [abs_mul] at hsplit
  have hident : ((∫ t, rieszKernel ε t*f (x-t))-f x*(∫ t in Icc (-1:ℝ) 1, rieszKernel ε t)) +
      f x*((∫ t in Icc (-1:ℝ) 1, rieszKernel ε t)-2*Real.log (1/ε)) =
      (∫ t, rieszKernel ε t*f (x-t))-2*Real.log (1/ε)*f x := by ring
  rw [hident] at hsplit
  nlinarith

end TaoAdditive1132
end
end SourceErdos1132_Additive_RieszConvolution

/- Erdos1132.Additive.AtomicRieszEnergy -/
section SourceErdos1132_Additive_AtomicRieszEnergy
/- # Riesz energy comparison for actual finite atomic measures

Main paper: §5, derivative-jump energy.
-/

noncomputable section
open MeasureTheory Set Real Finset
open scoped BigOperators
namespace TaoAdditive1132

def unitClamp (x : ℝ) : ℝ := (projIcc (-1) 1 (by norm_num) x : ℝ)

theorem continuous_unitClamp : Continuous unitClamp := continuous_subtype_val.comp continuous_projIcc

theorem abs_unitClamp_le (x : ℝ) : |unitClamp x| ≤ 1 :=
  abs_le.mpr (projIcc (-1) 1 (by norm_num) x).property

theorem unitClamp_eq {x : ℝ} (hx : x ∈ Icc (-1:ℝ) 1) : unitClamp x = x := by
  simp only [unitClamp, projIcc_of_mem (by norm_num : (-1:ℝ) ≤ 1) hx]

theorem atomic_riesz_energy_comparison {n : ℕ} (x a : Fin n → ℝ)
    (hx : ∀ i, |x i| ≤ 1) {ε B : ℝ} (hε : 0 < ε) (hB : 0 ≤ B)
    (ha : ∀ i, |a i| ≤ B) {f : ℝ → ℝ} (hf : Measurable f)
    (hfb : ∀ t, |f t| ≤ B) (hsupp : ∀ t, t ∉ Icc (-1:ℝ) 1 → f t = 0) :
    2*(∑ i, a i*(∫ y, rieszKernel ε (x i-y)*f y)) -
      (∫ t, f t*(∫ y, rieszKernel ε (t-y)*f y)) ≤
      ∑ i, ∑ j, a i*a j*rieszKernel ε (x i-x j) := by
  let μ : Measure (Fin n) := Measure.count
  let ν := volume.restrict (Icc (-1:ℝ) 1)
  have hxm : Measurable x := measurable_of_finite _
  have ham : Measurable a := measurable_of_finite _
  have hc := continuous_unitClamp.measurable
  have hp := riesz_energy_comparison μ ν hxm ham hc hf hB hε hx abs_unitClamp_le ha hfb
  rw [integral_prod _ (integrable_weighted_riesz_pair μ ν hxm ham hc hf hB hε ha hfb),
    integral_prod _ (integrable_weighted_riesz_pair ν ν hc hf hc hf hB hε hfb hfb),
    integral_prod _ (integrable_weighted_riesz_pair μ μ hxm ham hxm ham hB hε ha ha)] at hp
  dsimp only [μ] at hp
  simp only [integral_count] at hp
  have hinner (t : ℝ) : (∫ y, f y*rieszKernel ε (t-unitClamp y) ∂ν) =
      ∫ y, rieszKernel ε (t-y)*f y := by
    change (∫ y in Icc (-1:ℝ) 1, _) = _
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume) (s := Icc (-1:ℝ) 1)
      (fun y hy => by rw [hsupp y hy]; ring)]
    apply setIntegral_congr_fun measurableSet_Icc
    intro y hy
    dsimp only
    rw [unitClamp_eq hy]
    ring
  have hleft : (∑ i, ∫ y, a i*f y*rieszKernel ε (x i-unitClamp y) ∂ν) =
      ∑ i, a i*(∫ y, rieszKernel ε (x i-y)*f y) := by
    apply sum_congr rfl
    intro i hi
    simp_rw [mul_assoc]
    rw [integral_const_mul, hinner]
  have hright : (∫ t, ∫ y, f t*f y*rieszKernel ε (unitClamp t-unitClamp y) ∂ν ∂ν) =
      ∫ t, f t*(∫ y, rieszKernel ε (t-y)*f y) := by
    simp_rw [mul_assoc, integral_const_mul, hinner]
    change (∫ t in Icc (-1:ℝ) 1, _) = _
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume) (s := Icc (-1:ℝ) 1)
      (fun t ht => by rw [hsupp t ht]; ring)]
    apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    dsimp only
    rw [unitClamp_eq ht]
  rw [hleft, hright] at hp
  exact hp

end TaoAdditive1132
end
end SourceErdos1132_Additive_AtomicRieszEnergy

/- Erdos1132.Additive.AtomicEnergyBound -/
section SourceErdos1132_Additive_AtomicEnergyBound
/- # Quantitative lower bound for atomic Riesz energy

Main paper: §5, derivative-jump energy.
-/

noncomputable section
open MeasureTheory Set Real Finset
open scoped BigOperators
namespace TaoAdditive1132

theorem atomic_riesz_lower_bound {n : ℕ} (hn : 0 < n) (x a : Fin n → ℝ)
    (hx : ∀ i, |x i| ≤ 1) {A M C E : ℝ} (hA : 0 ≤ A) (hM : 0 ≤ M)
    (hC : 0 ≤ C) (ha0 : ∀ i, 0 ≤ a i) (haA : ∀ i, a i ≤ A)
    {f : ℝ → ℝ} (hf : Integrable f) (hfm : Measurable f) (hf0 : ∀ t, 0 ≤ f t)
    (hfM : ∀ t, f t ≤ M) (hsupp : ∀ t, t ∉ Icc (-1:ℝ) 1 → f t = 0)
    (hconv : ∀ t, |rieszConvolution (1/(n:ℝ)) f t-2*Real.log n*f t| ≤ C)
    (hquad : |(∑ i, a i*f (x i))/(n:ℝ)-(∫ t, (f t)^2)| ≤ E) :
    2*Real.log n*(∫ t, (f t)^2)-4*Real.log n*E-2*C*A-C*(∫ t, f t) ≤
      (∑ i, ∑ j, a i*a j*rieszKernel (1/(n:ℝ)) (x i-x j))/(n:ℝ)^2 := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg hn1
  have hε : 0 < 1/(n:ℝ) := by positivity
  let w (i : Fin n) := a i/(n:ℝ)
  have hw0 (i : Fin n) : 0 ≤ w i := div_nonneg (ha0 i) hnR.le
  have hwA (i : Fin n) : w i ≤ A := by
    apply (div_le_iff₀ hnR).mpr
    exact (haA i).trans (by nlinarith)
  have hwtotal : (∑ i, w i) ≤ A := by
    dsimp only [w]
    rw [← sum_div]
    apply (div_le_iff₀ hnR).mpr
    calc
      _ ≤ ∑ _i : Fin n, A := sum_le_sum (fun i _ => haA i)
      _ = _ := by simp; ring
  have hwquad : (∫ t, (f t)^2)-E ≤ ∑ i, w i*f (x i) := by
    have hq := (abs_le.mp hquad).1
    have he : (∑ i, w i*f (x i)) = (∑ i, a i*f (x i))/(n:ℝ) := by
      rw [sum_div]; apply sum_congr rfl; intro i hi; dsimp [w]; ring
    rw [he]
    linarith
  have hmixed : 2*Real.log n*((∫ t, (f t)^2)-E)-C*A ≤
      ∑ i, w i*rieszConvolution (1/(n:ℝ)) f (x i) := by
    have hl (i : Fin n) := mul_le_mul_of_nonneg_left
      (show 2*Real.log n*f (x i)-C ≤ rieszConvolution (1/(n:ℝ)) f (x i) by
        have hh := (abs_le.mp (hconv (x i))).1; linarith) (hw0 i)
    have hs := sum_le_sum (s := univ) (fun i _ => hl i)
    have he : (∑ i, w i*(2*Real.log n*f (x i)-C)) =
        2*Real.log n*(∑ i, w i*f (x i))-C*(∑ i, w i) := by
      rw [mul_sum, mul_sum, ← sum_sub_distrib]
      apply sum_congr rfl; intro i hi; ring
    rw [he] at hs
    have hq := mul_le_mul_of_nonneg_left hwquad (by positivity : 0 ≤ 2*Real.log (n:ℝ))
    have hm := mul_le_mul_of_nonneg_left hwtotal hC
    linarith
  have hfsq : Integrable (fun t => (f t)^2) := by
    simpa only [pow_two] using hf.mul_bdd hfm.aestronglyMeasurable
      (ae_of_all _ (fun t => by rw [Real.norm_eq_abs, abs_of_nonneg (hf0 t)]; exact hfM t))
  have hself : (∫ t, f t*rieszConvolution (1/(n:ℝ)) f t) ≤
      2*Real.log n*(∫ t, (f t)^2)+C*(∫ t, f t) := by
    calc
      _ ≤ ∫ t, (2*Real.log n)*(f t)^2+C*f t := integral_mono
        (integrable_riesz_self_energy hε hf hfm) ((hfsq.const_mul _).add (hf.const_mul _)) (fun t => by
          have hh := mul_le_mul_of_nonneg_left (abs_le.mp (hconv t)).2 (hf0 t)
          nlinarith)
      _ = _ := by rw [integral_add (hfsq.const_mul _) (hf.const_mul _), integral_const_mul, integral_const_mul]
  have hp := atomic_riesz_energy_comparison x w hx hε (by positivity : 0 ≤ A+M)
    (fun i => by rw [abs_of_nonneg (hw0 i)]; exact (hwA i).trans (by linarith))
    hfm (fun t => by rw [abs_of_nonneg (hf0 t)]; exact (hfM t).trans (by linarith)) hsupp
  change 2*(∑ i, w i*rieszConvolution (1/(n:ℝ)) f (x i))-
    (∫ t, f t*rieszConvolution (1/(n:ℝ)) f t) ≤ _ at hp
  have he : (∑ i, ∑ j, w i*w j*rieszKernel (1/(n:ℝ)) (x i-x j)) =
      (∑ i, ∑ j, a i*a j*rieszKernel (1/(n:ℝ)) (x i-x j))/(n:ℝ)^2 := by
    rw [sum_div]
    apply sum_congr rfl
    intro i hi
    rw [sum_div]
    apply sum_congr rfl
    intro j hj
    dsimp only [w]
    ring
  rw [he] at hp
  nlinarith

theorem regularized_energy_le_reciprocal_add_diag {n : ℕ} (x a : Fin n → ℝ)
    (hx : Function.Injective x) (ha : ∀ i, 0 ≤ a i) {ε : ℝ} (hε : 0 < ε) :
    (∑ i, ∑ j, a i*a j*rieszKernel ε (x i-x j)) ≤
      (∑ i, ∑ j, a i*a j/|x i-x j|)+(∑ i, (a i)^2/ε) := by
  classical
  have hp (i j : Fin n) : a i*a j*rieszKernel ε (x i-x j) ≤
      a i*a j/|x i-x j|+if i = j then (a i)^2/ε else 0 := by
    by_cases hij : i = j
    · subst j
      simp [rieszKernel_diagonal hε.le, pow_two, div_eq_mul_inv]
    · have hd : x i-x j ≠ 0 := sub_ne_zero.mpr (fun h => hij (hx h))
      rw [if_neg hij, add_zero]
      simpa only [div_eq_mul_inv, one_div, mul_assoc, one_mul] using
        mul_le_mul_of_nonneg_left (rieszKernel_le_inverse_distance (ε := ε) hd) (mul_nonneg (ha i) (ha j))
  have hh := sum_le_sum (s := univ) (fun i _ => sum_le_sum (s := univ) (fun j _ => hp i j))
  simpa only [sum_add_distrib, sum_ite_eq, Finset.mem_univ, if_true] using hh

end TaoAdditive1132
end
end SourceErdos1132_Additive_AtomicEnergyBound

/- Erdos1132.Additive.JumpEnergy -/
section SourceErdos1132_Additive_JumpEnergy
/- # Symmetrization of the derivative-jump energy

Main paper: §5, derivative-jump energy.
-/

noncomputable section
open Finset
open scoped BigOperators
namespace TaoAdditive1132

/-- Pairing the two orientations of each interaction removes the positive
mass ratios. The amplitudes may vanish. -/
theorem reciprocal_energy_le_weighted {ι : Type*} [Fintype ι]
    (x a ν : ι → ℝ) (hν : ∀ i, 0 < ν i) :
    (∑ k, ∑ j, a k * a j / |x k - x j|) ≤
      ∑ k, ∑ j, (a k)^2 * ν j / (ν k * |x k - x j|) := by
  have hpair (k j : ι) : 2 * (a k * a j / |x k - x j|) ≤
      (a k)^2 * ν j / (ν k * |x k - x j|) +
        (a j)^2 * ν k / (ν j * |x j - x k|) := by
    have hraw : 2 * a k * a j ≤ (a k)^2 * ν j / ν k + (a j)^2 * ν k / ν j := by
      have heq : (a k)^2 * ν j / ν k + (a j)^2 * ν k / ν j =
          ((a k * ν j)^2 + (a j * ν k)^2) / (ν k * ν j) := by
        field_simp
      rw [heq]
      apply (le_div_iff₀ (mul_pos (hν k) (hν j))).mpr
      nlinarith [sq_nonneg (a k * ν j - a j * ν k)]
    calc
      _ = (2 * a k * a j) / |x k - x j| := by ring
      _ ≤ ((a k)^2 * ν j / ν k + (a j)^2 * ν k / ν j) / |x k - x j| :=
        div_le_div_of_nonneg_right hraw (abs_nonneg _)
      _ = _ := by rw [add_div, div_div, div_div, abs_sub_comm (x k) (x j)]
  have hsum := sum_le_sum (s := univ) fun k _ => sum_le_sum (s := univ) fun j _ => hpair k j
  simp only [sum_add_distrib, ← mul_sum] at hsum
  have hswap : (∑ k, ∑ j, (a j)^2 * ν k / (ν j * |x j - x k|)) =
      ∑ k, ∑ j, (a k)^2 * ν j / (ν k * |x k - x j|) := sum_comm
  rw [hswap] at hsum
  linarith

namespace Nodes
variable {n : ℕ} (X : Nodes n)

/-- The ordered-sum normalization of the jump energy, with its diagonal
identically zero under real division. -/
theorem jumpEnergy_eq_weighted (a : Fin n → ℝ) :
    (∑ k, (a k)^2 * X.derivativeJump k / 2) =
      ∑ k, ∑ j, (a k)^2 * X.mass j / (X.mass k * |X.point k - X.point j|) := by
  apply sum_congr rfl
  intro k _
  rw [X.derivativeJump_eq_mass_sum]
  have heq : (a k)^2 * (2 * ∑ i ∈ univ.erase k,
      X.mass i / (X.mass k * |X.point k - X.point i|)) / 2 =
      ∑ i ∈ univ.erase k, (a k)^2 * X.mass i / (X.mass k * |X.point k - X.point i|) := by
    calc
      _ = (a k)^2 * ∑ i ∈ univ.erase k,
          X.mass i / (X.mass k * |X.point k - X.point i|) := by ring
      _ = _ := by
        rw [mul_sum]
        apply sum_congr rfl
        intro i _
        ring
  rw [heq, ← sum_erase_add _ _ (mem_univ k)]
  simp

/-- The reciprocal-distance energy is bounded above by the derivative-jump
energy, including zero amplitudes and endpoint nodes. -/
theorem reciprocal_energy_le_jumpEnergy (a : Fin n → ℝ) :
    (∑ k, ∑ j, a k * a j / |X.point k - X.point j|) ≤
      ∑ k, (a k)^2 * X.derivativeJump k / 2 := by
  rw [X.jumpEnergy_eq_weighted]
  exact reciprocal_energy_le_weighted X.point a X.mass
    (fun i => X.mass_pos (Nat.zero_lt_of_lt i.isLt) i)

end Nodes
end TaoAdditive1132
end
end SourceErdos1132_Additive_JumpEnergy

/- Erdos1132.Additive.JumpEnergyLower -/
section SourceErdos1132_Additive_JumpEnergyLower
/- # The weighted derivative-jump lower bound for an actual node array

Main paper: §5, derivative-jump energy.
-/

noncomputable section
open MeasureTheory Set Finset Filter Real
open scoped BigOperators Topology
namespace TaoAdditive1132

theorem eventually_weighted_jump_lower (X : ∀ n, Nodes n)
    {a b d l r M L : ℝ} (hab : a < b) (hI : Icc a b ⊆ Icc (-1) 1)
    (hd : 0 < d) (hlr : l ≤ r) (hJ : Icc l r ⊆ Icc (a+d) (b-d))
    (hM : 0 ≤ M) (hL : 0 ≤ L) {f : ℝ → ℝ} (hf : Integrable f) (hfm : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hMf : ∀ x, f x ≤ M)
    (hlip : ∀ x y, |f x-f y| ≤ L*|x-y|) (hsupp : ∀ x, x ∉ Icc l r → f x = 0)
    (hΛ : ∀ᶠ n : ℕ in atTop, ∀ y ∈ Icc a b, (X n).lebesgue y ≤ n) :
    ∃ C > 0, ∀ᶠ n : ℕ in atTop,
      (2/Real.pi)*Real.log n*(∫ x, (f x)^2)-C ≤
        ∑ i, ((f ((X n).point i))^2/
          ((n:ℝ)*(X n).exteriorDensity a b (X n).potentialNormalization ((X n).point i) 0))*
          ((X n).derivativeJump i/(2*Real.pi*(n:ℝ)*
            (X n).exteriorDensity a b (X n).potentialNormalization ((X n).point i) 0)) := by
  have hMf' (x : ℝ) : |f x| ≤ M := by rw [abs_of_nonneg (hf0 x)]; exact hMf x
  have hsuppI (x : ℝ) (hx : x ∉ Icc (-1:ℝ) 1) : f x = 0 :=
    hsupp x (fun hxJ => hx (hI (mem_interval_of_inset hd.le (hJ hxJ))))
  obtain ⟨c, hc, hpos⟩ := eventually_exterior_density_positive X hab hI hd hΛ
  obtain ⟨Q, hQ, hquad⟩ := eventually_weighted_square_quadrature X hab hI hd hlr hJ
    hM hL hfm hMf' hlip hsupp hΛ
  let A := M/c
  let B := 2*L+(∫ t, |f t|)+2*M*Real.log 3
  have hA : 0 ≤ A := by positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  let C := 16*Q+2*B*A+B*(∫ t, f t)+A^2+1
  have hC : 0 < C := by
    have hi : 0 ≤ ∫ t, f t := integral_nonneg hf0
    dsimp [C]
    positivity
  refine ⟨C/Real.pi, by positivity, ?_⟩
  filter_upwards [hpos, hquad, eventually_gt_atTop (0:ℕ)] with n hnp hnq hn
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hε : 0 < 1/(n:ℝ) := by positivity
  let ρ (x : ℝ) := (X n).exteriorDensity a b (X n).potentialNormalization x 0
  let w (i : Fin n) := f ((X n).point i)/ρ ((X n).point i)
  have hw (i : Fin n) : 0 ≤ w i ∧ w i ≤ A := by
    by_cases hi : (X n).point i ∈ Icc l r
    · have hρ := hc.trans_le (hnp _ (hJ hi))
      refine ⟨div_nonneg (hf0 _) hρ.le, ?_⟩
      exact div_le_div₀ hM (hMf _) hc (hnp _ (hJ hi))
    · simp [w, hsupp _ hi, hA]
  have hconv (t : ℝ) : |rieszConvolution (1/(n:ℝ)) f t-2*Real.log n*f t| ≤ B := by
    have he := riesz_convolution_log_error hε
      (by simpa using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hn1)
      hL hf hMf' hlip t
    simpa only [one_div, inv_inv, rieszConvolution] using he
  have hqw : |(∑ i, w i*f ((X n).point i))/(n:ℝ)-(∫ t, (f t)^2)| ≤ Q/quarterRoot n := by
    convert! hnq using 2
    congr 2
    apply sum_congr rfl
    intro i hi
    dsimp [w, ρ]
    ring
  have hmain := atomic_riesz_lower_bound hn (X n).point w
    (fun i => abs_le.mpr ((X n).mem_interval i)) hA hM hB
    (fun i => (hw i).1) (fun i => (hw i).2) hf hfm hf0 hMf hsuppI hconv hqw
  have hreg := regularized_energy_le_reciprocal_add_diag (X n).point w
    (X n).injective (fun i => (hw i).1) hε
  have hdiag : (∑ i, (w i)^2/(1/(n:ℝ)))/(n:ℝ)^2 ≤ A^2 := by
    have he : (∑ i, (w i)^2/(1/(n:ℝ)))/(n:ℝ)^2 = (∑ i, (w i)^2)/(n:ℝ) := by
      simp_rw [sum_div]
      apply sum_congr rfl
      intro i hi
      field_simp
    rw [he]
    apply (div_le_iff₀ hnR).mpr
    calc
      _ ≤ ∑ _i : Fin n, A^2 := sum_le_sum (fun i _ => by nlinarith [(hw i).1, (hw i).2])
      _ = _ := by simp; ring
  have hlogQ : 4*Real.log n*(Q/quarterRoot n) ≤ 16*Q := by
    have hh := mul_le_mul_of_nonneg_left (log_div_quarterRoot_le hnR) (by positivity : 0 ≤ 4*Q)
    convert! hh using 1 <;> ring
  have hreg' := div_le_div_of_nonneg_right hreg (sq_nonneg (n:ℝ))
  rw [add_div] at hreg'
  have hrec : 2*Real.log n*(∫ t, (f t)^2)-C ≤
      (∑ i, ∑ j, w i*w j/|(X n).point i-(X n).point j|)/(n:ℝ)^2 := by
    dsimp only [C]
    linarith
  have hjump := div_le_div_of_nonneg_right ((X n).reciprocal_energy_le_jumpEnergy w) (sq_nonneg (n:ℝ))
  have hfinal := div_le_div_of_nonneg_right (hrec.trans hjump) Real.pi_pos.le
  have he : (∑ i, (w i)^2*(X n).derivativeJump i/2)/(n:ℝ)^2/Real.pi =
      ∑ i, ((f ((X n).point i))^2/((n:ℝ)*ρ ((X n).point i)))*
        ((X n).derivativeJump i/(2*Real.pi*(n:ℝ)*ρ ((X n).point i))) := by
    rw [sum_div, sum_div]
    apply sum_congr rfl
    intro i hi
    dsimp only [w]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_pow]
    ring
  rw [he] at hfinal
  convert! hfinal using 1 <;> ring

end TaoAdditive1132
end
end SourceErdos1132_Additive_JumpEnergyLower

/- Erdos1132.Additive.ComplexInterpolant -/
section SourceErdos1132_Additive_ComplexInterpolant
/- # Complex growth of interpolants with bounded nodal data

Main paper: §4, local potential and differentiation estimates.
-/

noncomputable section
open Polynomial Finset Set Complex
open scoped BigOperators
namespace TaoAdditive1132.Nodes
variable {n : ℕ} (X : TaoAdditive1132.Nodes n)

def interpolant (a : Fin n → ℝ) : ℝ[X] := ∑ i, C (a i)*X.cardinal i

theorem degree_interpolant_lt (a : Fin n → ℝ) : (X.interpolant a).degree < n := by
  simpa only [Lagrange.interpolate_apply, interpolant, cardinal, card_univ, Fintype.card_fin]
    using Lagrange.degree_interpolate_lt (s := Finset.univ) a X.injective.injOn

theorem interpolant_eval_le (a : Fin n → ℝ) (ha : ∀ i, |a i| ≤ 1) (x : ℝ) :
    |(X.interpolant a).eval x| ≤ X.lebesgue x := by
  simp only [interpolant, eval_finsetSum, eval_mul, eval_C]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro i _
  rw [abs_mul]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (ha i) (abs_nonneg _)

theorem nodePolynomial_eval₂_ne_zero {z : ℂ} (hz : z.im ≠ 0) :
    X.nodePolynomial.eval₂ (algebraMap ℝ ℂ) z ≠ 0 := by
  simp only [nodePolynomial, Lagrange.nodal, eval₂_finsetProd, eval₂_sub, eval₂_X, eval₂_C]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _ he
  have h := congrArg Complex.im he
  apply hz
  simpa using h

theorem cardinal_eval₂_identity (i : Fin n) (z : ℂ) :
    (z-X.point i)*(X.cardinal i).eval₂ (algebraMap ℝ ℂ) z =
      X.weight i*X.nodePolynomial.eval₂ (algebraMap ℝ ℂ) z := by
  have he := congrArg (fun P : ℝ[X] => P.eval₂ (algebraMap ℝ ℂ) z) (X.cardinal_mul_linear i)
  simpa only [eval₂_mul, eval₂_sub, eval₂_X, eval₂_C] using! he

theorem interpolant_complex_bound (a : Fin n → ℝ) (ha : ∀ i, |a i| ≤ 1)
    {z : ℂ} (hz : 0 < z.im) :
    ‖(X.interpolant a).eval₂ (algebraMap ℝ ℂ) z‖ ≤
      X.totalWeight*‖X.nodePolynomial.eval₂ (algebraMap ℝ ℂ) z‖/z.im := by
  apply (le_div_iff₀ hz).mpr
  have hsum : ‖(X.interpolant a).eval₂ (algebraMap ℝ ℂ) z‖ ≤
      ∑ i, ‖(a i : ℂ)*(X.cardinal i).eval₂ (algebraMap ℝ ℂ) z‖ := by
    simp only [interpolant, eval₂_finsetSum, eval₂_mul, eval₂_C]
    simpa only using! (norm_sum_le (s := Finset.univ)
      (f := fun i => (algebraMap ℝ ℂ) (a i)*(X.cardinal i).eval₂ (algebraMap ℝ ℂ) z))
  have ht := mul_le_mul_of_nonneg_right hsum hz.le
  apply ht.trans
  rw [sum_mul]
  unfold totalWeight
  rw [sum_mul]
  apply sum_le_sum
  intro i _
  have he := congrArg norm (X.cardinal_eval₂_identity i z)
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs] at he
  have hi : z.im ≤ ‖z-(X.point i : ℂ)‖ := by
    simpa only [sub_im, ofReal_im, sub_zero] using Complex.im_le_norm (z-(X.point i : ℂ))
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    |a i| * ‖(X.cardinal i).eval₂ (algebraMap ℝ ℂ) z‖*z.im ≤
        ‖(X.cardinal i).eval₂ (algebraMap ℝ ℂ) z‖*z.im := by
      have hm := mul_le_mul_of_nonneg_right (ha i)
        (mul_nonneg (norm_nonneg ((X.cardinal i).eval₂ (algebraMap ℝ ℂ) z)) hz.le)
      simpa only [mul_assoc, one_mul] using hm
    _ ≤ ‖z-(X.point i : ℂ)‖*‖(X.cardinal i).eval₂ (algebraMap ℝ ℂ) z‖ := by
      nlinarith [norm_nonneg ((X.cardinal i).eval₂ (algebraMap ℝ ℂ) z)]
    _ = _ := he

theorem normalized_complex_polynomial (hn : 0 < n) {h : ℝ} (hh : 0 < h) (x : ℝ) :
    X.totalWeight*‖X.nodePolynomial.eval₂ (algebraMap ℝ ℂ) ((x : ℂ)+h*I)‖ =
      Real.exp ((n : ℝ)*(X.potentialNormalization-X.complexLogPotential x h)) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have hp : 0 < ‖X.nodePolynomial.eval₂ (algebraMap ℝ ℂ) ((x : ℂ)+h*I)‖ := by
    apply norm_pos_iff.mpr
    apply X.nodePolynomial_eval₂_ne_zero
    simpa using hh.ne'
  rw [X.complexLogPotential_eq_polynomial hh, potentialNormalization]
  have he : (n : ℝ)*(Real.log X.totalWeight/n -
      -Real.log ‖X.nodePolynomial.eval₂ (algebraMap ℝ ℂ) ((x : ℂ)+h*I)‖/n) =
      Real.log X.totalWeight+Real.log ‖X.nodePolynomial.eval₂ (algebraMap ℝ ℂ) ((x : ℂ)+h*I)‖ := by
    field_simp
    ring
  rw [he, Real.exp_add, Real.exp_log (X.totalWeight_pos hn), Real.exp_log hp]

end TaoAdditive1132.Nodes

namespace TaoAdditive1132

theorem uniform_complex_interpolant_growth {l r d : ℝ} (hlr : l < r)
    (hI : Icc l r ⊆ Icc (-1) 1) (hd : 0 < d) :
    ∃ C > 0, ∀ (n : ℕ) (X : Nodes n), 0 < n →
      (∀ y ∈ Icc l r, X.lebesgue y ≤ n) →
      ∀ a : Fin n → ℝ, (∀ i, |a i| ≤ 1) →
      ∀ x ∈ Icc (l+d) (r-d), ∀ h : ℝ, 1/(n : ℝ) ≤ h →
        ‖(X.interpolant a).eval₂ (algebraMap ℝ ℂ) ((x : ℂ)+h*I)‖ ≤
          Real.exp (Real.pi*n*h*X.exteriorDensity l r X.potentialNormalization x 0+
            C*(1+Real.log n+n*h^3))/h := by
  obtain ⟨C, hC, hpot⟩ := uniform_complex_potential_expansion hlr hI hd
  refine ⟨C, hC, ?_⟩
  intro n X hn hΛ a ha x hx h hh
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hh0 : 0 < h := (one_div_pos.mpr hnR).trans_le hh
  have hg := X.interpolant_complex_bound a ha (z := (x : ℂ)+h*I) (by simpa using hh0)
  simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_one,
    mul_zero, add_zero, zero_add] at hg
  rw [X.normalized_complex_polynomial hn hh0] at hg
  apply hg.trans
  apply div_le_div_of_nonneg_right _ hh0.le
  apply Real.exp_le_exp.mpr
  have hp := (abs_le.mp (hpot n X hn hΛ x hx h hh)).1
  have hm := mul_le_mul_of_nonneg_left hp hnR.le
  have he : (n : ℝ)*potentialErrorSize n = 1+Real.log n := by
    unfold potentialErrorSize
    field_simp
  nlinarith

end TaoAdditive1132
end
end SourceErdos1132_Additive_ComplexInterpolant

/- Erdos1132.Additive.InterpolantPieces -/
section SourceErdos1132_Additive_InterpolantPieces
/- # Polynomial pieces of the Lebesgue function between interpolation nodes

Main paper: §6, recurrence and Theorem 1(i).
-/

noncomputable section
open Set Filter Polynomial Finset
open scoped Topology BigOperators
namespace TaoAdditive1132

theorem continuous_nonzero_sign_on_interval {f : ℝ → ℝ} (hf : Continuous f)
    {a b : ℝ} (hab : a < b) (hnz : ∀ x ∈ Ioo a b, f x ≠ 0) :
    ∃ s : ℝ, |s| ≤ 1 ∧ ∀ x ∈ Icc a b, s*f x = |f x| := by
  let m := (a+b)/2
  have hm : m ∈ Ioo a b := by constructor <;> dsimp [m] <;> linarith
  have hsign : ∃ s : ℝ, |s| ≤ 1 ∧ ∀ x ∈ Ioo a b, s*f x = |f x| := by
    rcases lt_or_gt_of_ne (hnz m hm) with hneg | hpos
    · refine ⟨-1, by norm_num, ?_⟩
      intro x hx
      have hfx : f x < 0 := by
        by_contra hh
        have hh' := le_of_not_gt hh
        obtain ⟨z, hz, hzero⟩ := isPreconnected_Ioo.intermediate_value hm hx hf.continuousOn
          (show (0:ℝ) ∈ Icc (f m) (f x) from ⟨hneg.le, hh'⟩)
        exact hnz z hz hzero
      rw [abs_of_neg hfx]
      ring
    · refine ⟨1, by norm_num, ?_⟩
      intro x hx
      have hfx : 0 < f x := by
        by_contra hh
        have hh' := le_of_not_gt hh
        obtain ⟨z, hz, hzero⟩ := isPreconnected_Ioo.intermediate_value hx hm hf.continuousOn
          (show (0:ℝ) ∈ Icc (f x) (f m) from ⟨hh', hpos.le⟩)
        exact hnz z hz hzero
      rw [abs_of_pos hfx]
      ring
  obtain ⟨s, hs, hsi⟩ := hsign
  refine ⟨s, hs, ?_⟩
  have hh : closure (Ioo a b) ⊆ {x | s*f x = |f x|} :=
    closure_minimal hsi (isClosed_eq (continuous_const.mul hf) hf.abs)
  rw [closure_Ioo hab.ne] at hh
  exact hh

namespace Nodes
variable {n : ℕ} (X : Nodes n)

theorem cardinal_ne_zero_off_nodes {x : ℝ} (hx : ∀ i, x ≠ X.point i) (i : Fin n) :
    (X.cardinal i).eval x ≠ 0 := by
  have h := congrArg (fun p : ℝ[X] => p.eval x) (X.cardinal_mul_linear i)
  simp only [eval_mul, eval_sub, eval_X, eval_C] at h
  have hPn : X.nodePolynomial.eval x ≠ 0 := Lagrange.eval_nodal_not_at_node (fun j _ => hx j)
  have hr := mul_ne_zero (X.weight_ne_zero i) hPn
  rw [← h] at hr
  exact (mul_ne_zero_iff.mp hr).2

/-- On each closed gap without an interior interpolation node, the Lebesgue
function is one bounded-data interpolation polynomial. -/
theorem exists_interpolant_piece {a b : ℝ} (hab : a < b)
    (hgap : ∀ i, X.point i ∉ Ioo a b) :
    ∃ v : Fin n → ℝ, (∀ i, |v i| ≤ 1) ∧
      ∀ x ∈ Icc a b, (X.interpolant v).eval x = X.lebesgue x := by
  have h (i : Fin n) := continuous_nonzero_sign_on_interval (X.cardinal i).continuous hab
    (fun x hx => X.cardinal_ne_zero_off_nodes (fun j hj => hgap j (hj ▸ hx)) i)
  choose v hv he using h
  refine ⟨v, hv, ?_⟩
  intro x hx
  simp only [interpolant, lebesgue, eval_finsetSum, eval_mul, eval_C]
  exact sum_congr rfl (fun i _ => he i x hx)

theorem piece_derivative_right {a b : ℝ} (hab : a < b) {v : Fin n → ℝ}
    (he : ∀ x ∈ Icc a b, (X.interpolant v).eval x = X.lebesgue x) :
    ((X.interpolant v).derivative).eval a = derivWithin X.lebesgue (Ioi a) a := by
  have hh : X.lebesgue =ᶠ[𝓝[>] a] (fun x => (X.interpolant v).eval x) := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hab)]
      with x hxa hxb
    exact (he x ⟨hxa.le, hxb.le⟩).symm
  have hd := ((X.interpolant v).hasDerivAt a).hasDerivWithinAt.congr_of_eventuallyEq hh
    (he a ⟨le_rfl, hab.le⟩).symm
  exact (hd.derivWithin (uniqueDiffWithinAt_Ioi a)).symm

theorem piece_derivative_left {a b : ℝ} (hab : a < b) {v : Fin n → ℝ}
    (he : ∀ x ∈ Icc a b, (X.interpolant v).eval x = X.lebesgue x) :
    ((X.interpolant v).derivative).eval b = derivWithin X.lebesgue (Iio b) b := by
  have hh : X.lebesgue =ᶠ[𝓝[<] b] (fun x => (X.interpolant v).eval x) := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hab)]
      with x hxb hxa
    exact (he x ⟨hxa.le, hxb.le⟩).symm
  have hd := ((X.interpolant v).hasDerivAt b).hasDerivWithinAt.congr_of_eventuallyEq hh
    (he b ⟨hab.le, le_rfl⟩).symm
  exact (hd.derivWithin (uniqueDiffWithinAt_Iio b)).symm

end Nodes
end TaoAdditive1132
end
end SourceErdos1132_Additive_InterpolantPieces

/- Erdos1132.Additive.InterpolantTopEdge -/
section SourceErdos1132_Additive_InterpolantTopEdge
/- # The upper-edge estimate at the local exponential type

Main paper: §4, local potential and differentiation estimates.
-/

noncomputable section
open Set Complex
namespace TaoAdditive1132

theorem uniform_interpolant_top_edge {l r d : ℝ} (hlr : l < r)
    (hI : Icc l r ⊆ Icc (-1) 1) (hd : 0 < d) :
    ∃ C > 0, ∃ D > 0, ∀ (n : ℕ) (X : Nodes n), 0 < n →
      (∀ y ∈ Icc l r, X.lebesgue y ≤ n) →
      ∀ a : Fin n → ℝ, (∀ i, |a i| ≤ 1) →
      ∀ x ∈ Icc (l+2*d) (r-2*d), ∀ L H ε : ℝ, 0 ≤ L → L ≤ d → 1/(n : ℝ) ≤ H →
        Real.pi*n*H*D*L+C*(1+Real.log n+n*H^3)-Real.log H ≤ Real.pi*n*H*ε →
        ∀ u : ℝ, |u| ≤ L →
          ‖(X.interpolant a).eval₂ (algebraMap ℝ ℂ) ((x+u : ℝ)+H*I)‖ ≤
            Real.exp ((Real.pi*n*(X.exteriorDensity l r X.potentialNormalization x 0+ε))*H) := by
  obtain ⟨C, hC, hgrowth⟩ := uniform_complex_interpolant_growth hlr hI hd
  obtain ⟨D, hD, hdensity⟩ := uniform_exterior_density_bounds hlr hI hd
  refine ⟨C, hC, D, hD, ?_⟩
  intro n X hn hΛ a ha x hx L H ε hL hLd hH hgap u hu
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hH0 : 0 < H := (one_div_pos.mpr hnR).trans_le hH
  have hx' : x ∈ Icc (l+d) (r-d) := by constructor <;> linarith [hx.1, hx.2]
  have hu' : x+u ∈ Icc (l+d) (r-d) := by
    constructor <;> linarith [hx.1, hx.2, (abs_le.mp hu).1, (abs_le.mp hu).2]
  have hg := hgrowth n X hn hΛ a ha (x+u) hu' H hH
  have hlip := (hdensity n X hn hΛ).2 (x+u) hu' x hx'
  simp only [add_sub_cancel_left] at hlip
  have hρ : X.exteriorDensity l r X.potentialNormalization (x+u) 0 ≤
      X.exteriorDensity l r X.potentialNormalization x 0+D*L := by
    have hh := (abs_le.mp hlip).2
    have hm := mul_le_mul_of_nonneg_left hu hD.le
    linarith
  have hmain := mul_le_mul_of_nonneg_left hρ (show 0 ≤ Real.pi*n*H by positivity)
  have he : Real.exp (Real.pi*n*H*X.exteriorDensity l r X.potentialNormalization (x+u) 0+
      C*(1+Real.log n+n*H^3))/H =
      Real.exp (Real.pi*n*H*X.exteriorDensity l r X.potentialNormalization (x+u) 0+
        C*(1+Real.log n+n*H^3)-Real.log H) := by
    rw [Real.exp_sub, Real.exp_log hH0]
  rw [he] at hg
  apply hg.trans
  apply Real.exp_le_exp.mpr
  nlinarith

end TaoAdditive1132
end
end SourceErdos1132_Additive_InterpolantTopEdge

/- Erdos1132.Additive.EquispacedInterpolation -/
section SourceErdos1132_Additive_EquispacedInterpolation
/- # A global complex bound from interpolation on a fixed real interval

Main paper: §4, local potential and differentiation estimates.
-/

noncomputable section
open Polynomial Finset Set Complex
open scoped BigOperators
namespace TaoAdditive1132

def equispacedPoint (n : ℕ) (l r : ℝ) (i : Fin n) : ℝ := l+(r-l)*(i.val : ℝ)/n

theorem equispacedPoint_mem {n : ℕ} {l r : ℝ} (hn : 0 < n) (hlr : l < r) (i : Fin n) :
    equispacedPoint n l r i ∈ Set.Icc l r := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hi : (i.val : ℝ) < n := by exact_mod_cast i.isLt
  have hi0 : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
  have hfrac : 0 ≤ (r-l)*(i.val : ℝ)/n := by positivity
  have hfrac1 : (r-l)*(i.val : ℝ)/n ≤ r-l := by
    apply (div_le_iff₀ hnR).mpr
    nlinarith
  constructor <;> dsimp [equispacedPoint] <;> linarith

theorem equispacedPoint_separated {n : ℕ} {l r : ℝ} (hn : 0 < n) (hlr : l < r)
    {i j : Fin n} (hij : i ≠ j) :
    (r-l)/n ≤ |equispacedPoint n l r i-equispacedPoint n l r j| := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hd : 1 ≤ |(i.val : ℝ)-(j.val : ℝ)| := by
    have hne : i.val ≠ j.val := fun he => hij (Fin.ext he)
    rcases lt_or_gt_of_ne hne with h | h
    · have hc : (i.val : ℝ)+1 ≤ j.val := by exact_mod_cast (show i.val+1 ≤ j.val by omega)
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have hc : (j.val : ℝ)+1 ≤ i.val := by exact_mod_cast (show j.val+1 ≤ i.val by omega)
      rw [abs_of_nonneg (by linarith)]
      linarith
  have he : equispacedPoint n l r i-equispacedPoint n l r j =
      ((r-l)/n)*((i.val : ℝ)-(j.val : ℝ)) := by dsimp [equispacedPoint]; ring
  rw [he, abs_mul, abs_of_nonneg (div_nonneg (sub_nonneg.mpr hlr.le) hnR.le)]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hd (div_nonneg (sub_nonneg.mpr hlr.le) hnR.le)

theorem equispacedPoint_injective {n : ℕ} {l r : ℝ} (hn : 0 < n) (hlr : l < r) :
    Function.Injective (equispacedPoint n l r) := by
  intro i j he
  by_contra hij
  have hs := equispacedPoint_separated hn hlr hij
  rw [he, sub_self, abs_zero] at hs
  exact (div_pos (sub_pos.mpr hlr) (by exact_mod_cast hn)).not_ge hs

theorem equispaced_basis_complex_bound {n : ℕ} {l r : ℝ} (hn : 0 < n) (hlr : l < r)
    (hI : Set.Icc l r ⊆ Set.Icc (-1) 1) (i : Fin n) {z : ℂ} (hz : ‖z‖ ≤ 3) :
    ‖(Lagrange.basis Finset.univ (equispacedPoint n l r) i).eval₂ (algebraMap ℝ ℂ) z‖ ≤
      (1+4*(n : ℝ)/(r-l))^n := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hd : 0 < (r-l)/n := div_pos (sub_pos.mpr hlr) hnR
  let K : ℝ := 1+4*(n : ℝ)/(r-l)
  have hK : 1 ≤ K := by
    have hpos : 0 ≤ 4*(n : ℝ)/(r-l) := div_nonneg (by positivity) (sub_nonneg.mpr hlr.le)
    dsimp [K]
    linarith
  simp only [Lagrange.basis, eval₂_finsetProd, norm_prod]
  apply le_trans (Finset.prod_le_prod (g := fun _ => K) (fun _ _ => norm_nonneg _) ?_) ?_
  · intro j hj
    have hji := (Finset.mem_erase.mp hj).1
    have hdist := equispacedPoint_separated hn hlr hji.symm
    have hpoint := hI (equispacedPoint_mem hn hlr j)
    have habs : |equispacedPoint n l r j| ≤ 1 := abs_le.mpr hpoint
    have hnum : ‖z-(equispacedPoint n l r j : ℂ)‖ ≤ 4 := by
      have ht := norm_sub_le z (equispacedPoint n l r j : ℂ)
      simp only [Complex.norm_real, Real.norm_eq_abs] at ht
      linarith
    simp only [Lagrange.basisDivisor, eval₂_mul, eval₂_C, eval₂_sub, eval₂_X, norm_mul, map_inv₀]
    change ‖((equispacedPoint n l r i-equispacedPoint n l r j : ℝ) : ℂ)⁻¹‖*
      ‖z-(equispacedPoint n l r j : ℂ)‖ ≤ K
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs]
    have hi := one_div_le_one_div_of_le hd hdist
    have hn0 := norm_nonneg (z-(equispacedPoint n l r j : ℂ))
    calc
      _ ≤ ((r-l)/(n : ℝ))⁻¹*4 :=
        mul_le_mul (by simpa only [one_div] using hi) hnum hn0 (inv_nonneg.mpr hd.le)
      _ ≤ K := by dsimp [K]; field_simp; nlinarith
  · rw [Finset.prod_const]
    apply pow_le_pow_right₀ hK
    exact (Finset.card_erase_le).trans (by simp)

theorem polynomial_complex_bound_from_interval {n : ℕ} {l r Λ : ℝ} {p : ℝ[X]}
    (hn : 0 < n) (hlr : l < r) (hI : Set.Icc l r ⊆ Set.Icc (-1) 1)
    (hΛ : 0 ≤ Λ) (hp : p.degree < n) (hbound : ∀ x ∈ Set.Icc l r, |p.eval x| ≤ Λ)
    {z : ℂ} (hz : ‖z‖ ≤ 3) :
    ‖p.eval₂ (algebraMap ℝ ℂ) z‖ ≤ Λ*n*(1+4*(n : ℝ)/(r-l))^n := by
  have hrepr := Lagrange.eq_interpolate (f := p) (s := Finset.univ)
    (equispacedPoint_injective hn hlr).injOn (by simpa using hp)
  conv_lhs => rw [hrepr]
  simp only [Lagrange.interpolate_apply, eval₂_finsetSum, eval₂_mul, eval₂_C]
  apply (norm_sum_le _ _).trans
  have he : Λ*n*(1+4*(n : ℝ)/(r-l))^n =
      ∑ _i : Fin n, Λ*(1+4*(n : ℝ)/(r-l))^n := by simp; ring
  rw [he]
  apply Finset.sum_le_sum
  intro i _
  rw [norm_mul]
  apply mul_le_mul _ (equispaced_basis_complex_bound hn hlr hI i hz) (norm_nonneg _) hΛ
  change ‖((p.eval (equispacedPoint n l r i) : ℝ) : ℂ)‖ ≤ Λ
  simpa only [Complex.norm_real, Real.norm_eq_abs] using
    hbound _ (equispacedPoint_mem hn hlr i)

/-- A deliberately coarse exponential form sufficient on the vertical sides
of the local rectangle. -/
theorem polynomial_complex_exponential_bound {n : ℕ} {l r Λ : ℝ} {p : ℝ[X]}
    (hn : 0 < n) (hlr : l < r) (hI : Set.Icc l r ⊆ Set.Icc (-1) 1)
    (hΛ : 0 ≤ Λ) (hp : p.degree < n) (hbound : ∀ x ∈ Set.Icc l r, |p.eval x| ≤ Λ)
    {z : ℂ} (hz : ‖z‖ ≤ 3) :
    ‖p.eval₂ (algebraMap ℝ ℂ) z‖ ≤ Λ*Real.exp ((2+4/(r-l))*(n : ℝ)^2) := by
  have hb := polynomial_complex_bound_from_interval hn hlr hI hΛ hp hbound hz
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  let c : ℝ := 4/(r-l)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hN : (n : ℝ) ≤ Real.exp ((n : ℝ)^2) := by
    have he := Real.add_one_le_exp ((n : ℝ)^2)
    nlinarith
  have hK : 1+4*(n : ℝ)/(r-l) ≤ Real.exp ((1+c)*n) := by
    have he := Real.add_one_le_exp ((1+c)*(n : ℝ))
    have hid : 4*(n : ℝ)/(r-l) = c*n := by dsimp [c]; ring
    rw [hid]
    nlinarith
  have hpw := pow_le_pow_left₀ (by positivity : 0 ≤ 1+4*(n : ℝ)/(r-l)) hK n
  rw [← Real.exp_nat_mul] at hpw
  have hm := mul_le_mul hN hpw (pow_nonneg (by positivity : 0 ≤ 1+4*(n : ℝ)/(r-l)) n)
    (Real.exp_pos _).le
  rw [← Real.exp_add] at hm
  have he : (n : ℝ)^2+n*((1+c)*n) = (2+4/(r-l))*(n : ℝ)^2 := by dsimp [c]; ring
  rw [he] at hm
  exact hb.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hm hΛ)

end TaoAdditive1132
end
end SourceErdos1132_Additive_EquispacedInterpolation

/- Erdos1132.Additive.LocalPhragmenLindelof -/
section SourceErdos1132_Additive_LocalPhragmenLindelof
/- # An explicit local Phragmén–Lindelöf estimate on a rectangle

Main paper: §4, local potential and differentiation estimates.
-/

noncomputable section
open Complex Real Metric Set
open scoped Topology
namespace TaoAdditive1132

def rectangleBarrier (T B : ℝ) (z : ℂ) : ℂ :=
  2*B*(Complex.exp (z-T)+Complex.exp (-z-T))

theorem rectangleBarrier_re (T B : ℝ) (z : ℂ) :
    (rectangleBarrier T B z).re =
      2*B*(Real.exp (z.re-T)+Real.exp (-z.re-T))*Real.cos z.im := by
  simp [rectangleBarrier, Complex.exp_re, Real.cos_neg]
  ring

theorem cos_ge_half_of_abs_le_half {v : ℝ} (hv : |v| ≤ 1/2) : 1/2 ≤ Real.cos v := by
  have h := Real.lipschitzWith_cos.dist_le_mul v 0
  simp only [Real.dist_eq, Real.cos_zero, NNReal.coe_one, one_mul, sub_zero] at h
  have h' := (abs_le.mp h).1
  linarith

theorem rectangleBarrier_nonneg {T B : ℝ} (hB : 0 ≤ B) {z : ℂ}
    (hz : |z.im| ≤ 1/2) : 0 ≤ (rectangleBarrier T B z).re := by
  rw [rectangleBarrier_re]
  exact mul_nonneg (by positivity) (by linarith [cos_ge_half_of_abs_le_half hz])

theorem rectangleBarrier_side {T B : ℝ} (hB : 0 ≤ B) {z : ℂ}
    (hx : |z.re| = T) (hy : |z.im| ≤ 1/2) : B ≤ (rectangleBarrier T B z).re := by
  have he : 1 ≤ Real.exp (z.re-T)+Real.exp (-z.re-T) := by
    rcases (le_total 0 z.re) with h | h
    · rw [abs_of_nonneg h] at hx
      rw [hx, sub_self, Real.exp_zero]
      linarith [Real.exp_pos (-T-T)]
    · rw [abs_of_nonpos h] at hx
      rw [hx, sub_self, Real.exp_zero]
      linarith [Real.exp_pos (z.re-T)]
  rw [rectangleBarrier_re]
  have hc := cos_ge_half_of_abs_le_half hy
  have hp : B ≤ 2*B*(Real.exp (z.re-T)+Real.exp (-z.re-T))*(1/2) := by nlinarith
  exact hp.trans (mul_le_mul_of_nonneg_left hc (by positivity))

theorem rectangleBarrier_center {T B : ℝ} (hB : 0 ≤ B) {z : ℂ}
    (hx : |z.re| ≤ T/2) : (rectangleBarrier T B z).re ≤ 4*B*Real.exp (-T/2) := by
  have he1 : Real.exp (z.re-T) ≤ Real.exp (-T/2) :=
    Real.exp_le_exp.mpr (by linarith [(abs_le.mp hx).2])
  have he2 : Real.exp (-z.re-T) ≤ Real.exp (-T/2) :=
    Real.exp_le_exp.mpr (by linarith [(abs_le.mp hx).1])
  rw [rectangleBarrier_re]
  have hc := mul_le_mul_of_nonneg_left (Real.cos_le_one z.im)
    (show 0 ≤ 2*B*(Real.exp (z.re-T)+Real.exp (-z.re-T)) by positivity)
  nlinarith

/-- Horizontal boundary bound one, vertical boundary bound `exp B`, and an
explicit exponentially small loss on the middle half of the rectangle. -/
theorem local_pl_unit_strip {f : ℂ → ℂ} {T B : ℝ} (hT : 0 < T) (hB : 0 ≤ B)
    (hf : Differentiable ℂ f)
    (hhorizontal : ∀ z : ℂ, |z.re| ≤ T → |z.im| = 1/2 → ‖f z‖ ≤ 1)
    (hvertical : ∀ z : ℂ, |z.re| = T → |z.im| ≤ 1/2 → ‖f z‖ ≤ Real.exp B)
    {z : ℂ} (hzre : |z.re| ≤ T/2) (hzim : |z.im| ≤ 1/2) :
    ‖f z‖ ≤ Real.exp (4*B*Real.exp (-T/2)) := by
  let U : Set ℂ := Ioo (-T) T ×ℂ Ioo (-(1/2 : ℝ)) (1/2)
  let F : ℂ → ℂ := fun w => f w*Complex.exp (-rectangleBarrier T B w)
  have hd : Differentiable ℂ F := by
    dsimp [F, rectangleBarrier]
    fun_prop
  have hnorm (w : ℂ) : ‖F w‖ = ‖f w‖*Real.exp (-(rectangleBarrier T B w).re) := by
    simp [F, Complex.norm_exp]
  have hb : ∀ w ∈ frontier U, ‖F w‖ ≤ 1 := by
    intro w hw
    dsimp [U] at hw
    rw [frontier_reProdIm, closure_Ioo (neg_lt_self hT).ne,
      closure_Ioo (by norm_num : (-(1/2 : ℝ)) ≠ 1/2),
      frontier_Ioo (a := -T) (b := T) (neg_lt_self hT),
      frontier_Ioo (by norm_num : (-(1/2 : ℝ)) < 1/2)] at hw
    have hcases : (|w.re| ≤ T ∧ |w.im| = 1/2) ∨ (|w.re| = T ∧ |w.im| ≤ 1/2) := by
      rcases hw with hw | hw
      · left
        refine ⟨abs_le.mpr hw.1, ?_⟩
        rcases hw.2 with h | h <;> simp_all
      · right
        refine ⟨?_, abs_le.mpr hw.2⟩
        rcases hw.1 with h | h <;> simp_all [abs_of_nonneg hT.le]
    rw [hnorm]
    rcases hcases with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · have hbar := rectangleBarrier_nonneg (T := T) hB (le_of_eq hy)
      have he : Real.exp (-(rectangleBarrier T B w).re) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        linarith
      exact (mul_le_mul_of_nonneg_right (hhorizontal w hx hy) (Real.exp_pos _).le).trans
        (by simpa using he)
    · have hbar := rectangleBarrier_side hB hx hy
      calc
        ‖f w‖*Real.exp (-(rectangleBarrier T B w).re) ≤
            Real.exp B*Real.exp (-(rectangleBarrier T B w).re) :=
          mul_le_mul_of_nonneg_right (hvertical w hx hy) (Real.exp_pos _).le
        _ = Real.exp (B-(rectangleBarrier T B w).re) := by rw [← Real.exp_add]; rfl
        _ ≤ 1 := Real.exp_le_one_iff.mpr (sub_nonpos.mpr hbar)
  have hz : z ∈ closure U := by
    dsimp [U]
    rw [closure_reProdIm, closure_Ioo (neg_lt_self hT).ne,
      closure_Ioo (by norm_num : (-(1/2 : ℝ)) ≠ 1/2)]
    exact ⟨abs_le.mp (hzre.trans (by linarith)), abs_le.mp hzim⟩
  have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le
    ((isBounded_Ioo _ _).reProdIm (isBounded_Ioo _ _)) hd.diffContOnCl hb hz
  rw [hnorm] at hmax
  have hn : ‖f z‖ ≤ Real.exp (rectangleBarrier T B z).re := by
    have hm := mul_le_mul_of_nonneg_right hmax (Real.exp_pos (rectangleBarrier T B z).re).le
    rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one, one_mul] at hm
    exact hm
  exact hn.trans (Real.exp_le_exp.mpr (rectangleBarrier_center hB hzre))

/-- Rescaled upper-rectangle form, with arbitrary positive horizontal bound. -/
theorem local_pl_rectangle {f : ℂ → ℂ} {L H A B : ℝ}
    (hL : 0 < L) (hH : 0 < H) (hA : 0 < A) (hB : 0 ≤ B)
    (hf : Differentiable ℂ f)
    (hbottom : ∀ w : ℂ, |w.re| ≤ L → w.im = 0 → ‖f w‖ ≤ A)
    (htop : ∀ w : ℂ, |w.re| ≤ L → w.im = H → ‖f w‖ ≤ A)
    (hside : ∀ w : ℂ, |w.re| = L → 0 ≤ w.im → w.im ≤ H → ‖f w‖ ≤ A*Real.exp B)
    {z : ℂ} (hx : |z.re| ≤ L/2) (hy0 : 0 ≤ z.im) (hy1 : z.im ≤ H) :
    ‖f z‖ ≤ A*Real.exp (4*B*Real.exp (-L/(2*H))) := by
  let g : ℂ → ℂ := fun w => f ((H : ℂ)*w+(H/2 : ℝ)*I)/(A : ℂ)
  have hc (w : ℂ) : ((H : ℂ)*w+(H/2 : ℝ)*I).re = H*w.re ∧
      ((H : ℂ)*w+(H/2 : ℝ)*I).im = H*(w.im+1/2) := by
    constructor <;> simp <;> ring
  have hg : Differentiable ℂ g := by dsimp [g]; fun_prop
  have hgn (w : ℂ) : ‖g w‖ = ‖f ((H : ℂ)*w+(H/2 : ℝ)*I)‖/A := by
    simp [g, abs_of_pos hA]
  have hb (w : ℂ) (hw : |w.re| ≤ L/H) : |((H : ℂ)*w+(H/2 : ℝ)*I).re| ≤ L := by
    rw [(hc w).1, abs_mul, abs_of_pos hH]
    have hh := mul_le_mul_of_nonneg_left hw hH.le
    have he : H*(L/H) = L := by field_simp
    rwa [he] at hh
  have hv (w : ℂ) (hw : |w.im| ≤ 1/2) :
      0 ≤ ((H : ℂ)*w+(H/2 : ℝ)*I).im ∧ ((H : ℂ)*w+(H/2 : ℝ)*I).im ≤ H := by
    rw [(hc w).2]
    constructor <;> nlinarith [(abs_le.mp hw).1, (abs_le.mp hw).2]
  let w : ℂ := (z-(H/2 : ℝ)*I)/(H : ℂ)
  have hwre : w.re = z.re/H := by dsimp [w]; simp [Complex.div_ofReal_re]
  have hwim : w.im = z.im/H-1/2 := by
    dsimp [w]
    simp only [Complex.div_ofReal_im, sub_im, mul_im, ofReal_re, I_im, ofReal_im,
      I_re, mul_one, mul_zero, add_zero]
    field_simp
  have hwr : |w.re| ≤ (L/H)/2 := by
    rw [hwre, abs_div, abs_of_pos hH]
    calc
      |z.re|/H ≤ (L/2)/H := div_le_div_of_nonneg_right hx hH.le
      _ = (L/H)/2 := by ring
  have hwi : |w.im| ≤ 1/2 := by
    rw [hwim]
    apply abs_le.mpr
    constructor
    · have hh := div_nonneg hy0 hH.le; linarith
    · have hh := (div_le_one hH).mpr hy1; linarith
  have hresult := local_pl_unit_strip (div_pos hL hH) hB hg (fun u hu hhu => by
      rw [hgn, div_le_one hA]
      rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1/2)).mp hhu with hh | hh
      · apply htop _ (hb u hu)
        rw [(hc u).2, hh]
        ring
      · apply hbottom _ (hb u hu)
        rw [(hc u).2, hh]
        ring)
    (fun u hu hhu => by
      rw [hgn]
      apply (div_le_iff₀ hA).mpr
      have hh := hside ((H : ℂ)*u+(H/2 : ℝ)*I) (by
        rw [(hc u).1, abs_mul, abs_of_pos hH, hu]
        field_simp) (hv u hhu).1 (hv u hhu).2
      simpa only [mul_comm A] using hh) hwr hwi
  have hw : (H : ℂ)*w+(H/2 : ℝ)*I = z := by
    have hn : (H : ℂ) ≠ 0 := by exact_mod_cast hH.ne'
    dsimp [w]
    field_simp [hn]
    ring
  rw [hgn, hw] at hresult
  have hm := (div_le_iff₀ hA).mp hresult
  have he : -(L/H)/2 = -L/(2*H) := by ring
  simpa only [he, mul_comm A] using hm

/-- Removing a prescribed exponential growth on the upper edge gives the same
exponential type in the middle of the rectangle. -/
theorem local_exponential_growth {f : ℂ → ℂ} {L H A B ω : ℝ}
    (hL : 0 < L) (hH : 0 < H) (hA : 0 < A) (hB : 0 ≤ B) (hω : 0 ≤ ω)
    (hf : Differentiable ℂ f)
    (hbottom : ∀ w : ℂ, |w.re| ≤ L → w.im = 0 → ‖f w‖ ≤ A)
    (htop : ∀ w : ℂ, |w.re| ≤ L → w.im = H → ‖f w‖ ≤ A*Real.exp (ω*H))
    (hside : ∀ w : ℂ, |w.re| = L → 0 ≤ w.im → w.im ≤ H → ‖f w‖ ≤ A*Real.exp B)
    {z : ℂ} (hx : |z.re| ≤ L/2) (hy0 : 0 ≤ z.im) (hy1 : z.im ≤ H) :
    ‖f z‖ ≤ A*Real.exp (4*B*Real.exp (-L/(2*H)))*Real.exp (ω*z.im) := by
  let g : ℂ → ℂ := fun w => f w*Complex.exp (I*ω*w)
  have hg : Differentiable ℂ g := by dsimp [g]; fun_prop
  have hn (w : ℂ) : ‖g w‖ = ‖f w‖*Real.exp (-ω*w.im) := by
    simp [g, Complex.norm_exp]
  have hb (w : ℂ) (hw : |w.re| ≤ L) (hi : w.im = 0) : ‖g w‖ ≤ A := by
    rw [hn, hi]
    simpa using hbottom w hw hi
  have ht (w : ℂ) (hw : |w.re| ≤ L) (hi : w.im = H) : ‖g w‖ ≤ A := by
    rw [hn, hi]
    have hh := mul_le_mul_of_nonneg_right (htop w hw hi) (Real.exp_pos (-ω*H)).le
    simpa only [mul_assoc, ← Real.exp_add, mul_neg, neg_mul, add_neg_cancel,
      Real.exp_zero, mul_one] using hh
  have hs (w : ℂ) (hw : |w.re| = L) (hi0 : 0 ≤ w.im) (hi1 : w.im ≤ H) :
      ‖g w‖ ≤ A*Real.exp B := by
    rw [hn]
    have he : Real.exp (-ω*w.im) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    calc
      _ ≤ ‖f w‖*1 := mul_le_mul_of_nonneg_left he (norm_nonneg _)
      _ ≤ _ := by simpa using hside w hw hi0 hi1
  have hp := local_pl_rectangle hL hH hA hB hg hb ht hs hx hy0 hy1
  rw [hn] at hp
  have hh := mul_le_mul_of_nonneg_right hp (Real.exp_pos (ω*z.im)).le
  simpa only [mul_assoc, ← Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero, mul_one] using hh

end TaoAdditive1132
end
end SourceErdos1132_Additive_LocalPhragmenLindelof

/- Erdos1132.Additive.PolynomialRectangle -/
section SourceErdos1132_Additive_PolynomialRectangle
/- # Local exponential growth for a real polynomial

Main paper: §4, local potential and differentiation estimates.
-/

noncomputable section
open Polynomial Finset Set Complex
open scoped ComplexConjugate
namespace TaoAdditive1132

theorem real_polynomial_eval₂_conj (p : ℝ[X]) (z : ℂ) :
    p.eval₂ (algebraMap ℝ ℂ) (conj z) = conj (p.eval₂ (algebraMap ℝ ℂ) z) := by
  exact Polynomial.aeval_conj p z

theorem real_polynomial_eval₂_real (p : ℝ[X]) (x : ℝ) :
    p.eval₂ (algebraMap ℝ ℂ) (x : ℂ) = (p.eval x : ℝ) := by
  exact p.eval₂_at_apply (algebraMap ℝ ℂ) x

/-- The real interval bound supplies the bottom and vertical edges; only the
upper edge needs the logarithmic-potential estimate. -/
theorem polynomial_rectangle_growth {p : ℝ[X]} {n : ℕ} {l r x L H A ω : ℝ}
    (hn : 0 < n) (hlr : l < r) (hI : Set.Icc l r ⊆ Set.Icc (-1) 1)
    (hL : 0 < L) (hH : 0 < H) (hH1 : H ≤ 1) (hA : 0 < A) (hω : 0 ≤ ω)
    (hxL : l ≤ x-L) (hxR : x+L ≤ r) (hp : p.degree < n)
    (hreal : ∀ y ∈ Set.Icc l r, |p.eval y| ≤ A)
    (htop : ∀ u : ℝ, |u| ≤ L →
      ‖p.eval₂ (algebraMap ℝ ℂ) ((x+u : ℝ)+H*I)‖ ≤ A*Real.exp (ω*H))
    {u v : ℝ} (hu : |u| ≤ L/2) (hv : |v| ≤ H) :
    ‖p.eval₂ (algebraMap ℝ ℂ) ((x+u : ℝ)+v*I)‖ ≤
      A*Real.exp (4*((2+4/(r-l))*(n : ℝ)^2)*Real.exp (-L/(2*H)))*Real.exp (ω*|v|) := by
  let B : ℝ := (2+4/(r-l))*(n : ℝ)^2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hi (t : ℝ) (ht : |t| ≤ L) : x+t ∈ Set.Icc l r := by
    constructor <;> linarith [(abs_le.mp ht).1, (abs_le.mp ht).2]
  have hupper (s t : ℝ) (hs : |s| ≤ L/2) (ht0 : 0 ≤ t) (ht1 : t ≤ H) :
      ‖p.eval₂ (algebraMap ℝ ℂ) ((x+s : ℝ)+t*I)‖ ≤
        A*Real.exp (4*B*Real.exp (-L/(2*H)))*Real.exp (ω*t) := by
    let f : ℂ → ℂ := fun z => p.eval₂ (algebraMap ℝ ℂ) ((x : ℂ)+z)
    have hf : Differentiable ℂ f := by
      have ha : Differentiable ℂ (fun z : ℂ => aeval z p) := p.differentiable_aeval
      exact ha.comp (differentiable_id.const_add (x : ℂ))
    have he (z : ℂ) : (x : ℂ)+z = ((x+z.re : ℝ) : ℂ)+z.im*I := by
      rw [ofReal_add, add_assoc, Complex.re_add_im]
    have hb (z : ℂ) (hz : |z.re| ≤ L) (hz0 : z.im = 0) : ‖f z‖ ≤ A := by
      dsimp [f]
      rw [he, hz0]
      simp only [ofReal_zero, zero_mul, add_zero, real_polynomial_eval₂_real,
        Complex.norm_real, Real.norm_eq_abs]
      exact hreal _ (hi _ hz)
    have htop' (z : ℂ) (hz : |z.re| ≤ L) (hzH : z.im = H) : ‖f z‖ ≤ A*Real.exp (ω*H) := by
      dsimp [f]
      rw [he, hzH]
      exact htop z.re hz
    have hside (z : ℂ) (hz : |z.re| = L) (hz0 : 0 ≤ z.im) (hz1 : z.im ≤ H) :
        ‖f z‖ ≤ A*Real.exp B := by
      apply polynomial_complex_exponential_bound hn hlr hI hA.le hp hreal
      rw [he]
      have hx1 := abs_le.mpr (hI (hi z.re hz.le))
      have ht := norm_add_le ((x+z.re : ℝ) : ℂ) ((z.im : ℂ)*I)
      simp only [norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hz0] at ht
      linarith
    have hout := local_exponential_growth hL hH hA hB hω hf hb htop' hside
      (z := (s : ℂ)+t*I) (by simpa using hs) (by simpa using ht0) (by simpa using ht1)
    convert! hout using 1 <;> simp [f, ofReal_add, add_assoc]
  by_cases hv0 : 0 ≤ v
  · simpa only [abs_of_nonneg hv0] using hupper u v hu hv0 ((le_abs_self v).trans hv)
  · have hv' : v ≤ 0 := le_of_not_ge hv0
    have hn := hupper u (-v) hu (neg_nonneg.mpr hv') (by simpa [abs_of_nonpos hv'] using hv)
    have he : (((x+u : ℝ) : ℂ)+(-v : ℝ)*I) = conj (((x+u : ℝ) : ℂ)+v*I) := by simp
    rw [he, real_polynomial_eval₂_conj, norm_conj] at hn
    simpa only [abs_of_nonpos hv'] using hn

end TaoAdditive1132
end
end SourceErdos1132_Additive_PolynomialRectangle

/- Erdos1132.Additive.BernsteinScales -/
section SourceErdos1132_Additive_BernsteinScales
/- # Explicit scales for the local interpolation estimates

Main paper: §4, local potential and differentiation estimates.
-/

noncomputable section
open Real Filter
open scoped Topology
namespace TaoAdditive1132

def eighthRoot (N : ℝ) : ℝ := Real.sqrt (quarterRoot N)

theorem eighthRoot_nonneg (N : ℝ) : 0 ≤ eighthRoot N := Real.sqrt_nonneg _

theorem eighthRoot_pos {N : ℝ} (hN : 0 < N) : 0 < eighthRoot N :=
  Real.sqrt_pos.mpr (quarterRoot_pos hN)

theorem eighthRoot_pow_eight {N : ℝ} (hN : 0 ≤ N) : eighthRoot N^8 = N := by
  have h := Real.sq_sqrt (Real.sqrt_nonneg (Real.sqrt N))
  have he := quarterRoot_pow_four hN
  calc
    eighthRoot N^8 = (eighthRoot N^2)^4 := by ring
    _ = quarterRoot N^4 := by rw [show eighthRoot N^2 = quarterRoot N from h]
    _ = N := he

theorem eighthRoot_ge_one {N : ℝ} (hN : 1 ≤ N) : 1 ≤ eighthRoot N := by
  simpa only [eighthRoot, Real.sqrt_one] using Real.sqrt_le_sqrt (one_le_quarterRoot hN)

theorem tendsto_eighthRoot : Tendsto (fun n : ℕ => eighthRoot n) atTop atTop :=
  (Real.tendsto_sqrt_atTop.comp tendsto_quarterRoot).comp tendsto_natCast_atTop_atTop

theorem top_edge_scale_inequality {t C D : ℝ} (ht : 1 ≤ t) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hlarge : D+10*C+4 ≤ t) :
    Real.pi*t^8*(1/t^4)*D*(1/t^2)+C*(1+Real.log (t^8)+t^8*(1/t^4)^3)-
      Real.log (1/t^4) ≤ Real.pi*t^8*(1/t^4)*(1/t) := by
  have ht0 : 0 < t := by linarith
  have he1 : Real.pi*t^8*(1/t^4)*D*(1/t^2) = Real.pi*D*t^2 := by field_simp
  have he2 : t^8*(1/t^4)^3 = 1/t^4 := by field_simp
  have he3 : Real.pi*t^8*(1/t^4)*(1/t) = Real.pi*t^3 := by field_simp
  rw [he1, he2, he3, Real.log_pow, one_div, Real.log_inv, Real.log_pow]
  have hlog : Real.log t ≤ t := (Real.log_le_sub_one_of_pos ht0).trans (by linarith)
  have hinv : 1/t^4 ≤ 1 := (div_le_one (pow_pos ht0 _)).mpr (one_le_pow₀ ht)
  have ht2 : t ≤ t^2 := by nlinarith
  have hA : π*D*t^2+C*(1+8*Real.log t+1/t^4)+4*Real.log t ≤
      (π*D+10*C+4)*t^2 := by
    have hc1 := mul_le_mul_of_nonneg_left hinv hC
    have hc2 := mul_le_mul_of_nonneg_left hlog hC
    have hc3 := mul_le_mul_of_nonneg_left ht2 hC
    have hc4 := mul_le_mul_of_nonneg_left (show 1 ≤ t^2 by nlinarith) hC
    nlinarith
  have hB : π*D+10*C+4 ≤ π*t := by
    have hp : 1 ≤ π := by linarith [Real.pi_gt_three]
    have hm := mul_le_mul_of_nonneg_left hlarge Real.pi_pos.le
    have hc := mul_le_mul_of_nonneg_left hp (show 0 ≤ 10*C+4 by positivity)
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right hB (sq_nonneg t)
  norm_num at *
  nlinarith

/-- For the scales `L = n⁻¹ᐟ⁴`, `H = n⁻¹ᐟ²`, `ε = n⁻¹ᐟ⁸`, the
upper-edge surplus eventually absorbs the potential error and density variation. -/
theorem eventually_top_edge_scales {C D d : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hd : 0 < d) :
    ∀ᶠ (n : ℕ) in atTop, let t := eighthRoot n;
      0 < n ∧ 0 < t ∧ 1/t^2 ≤ d ∧ 0 < 1/t^4 ∧ 1/t^4 ≤ 1 ∧
      1/(n : ℝ) ≤ 1/t^4 ∧
      π*n*(1/t^4)*D*(1/t^2)+C*(1+Real.log n+n*(1/t^4)^3)-Real.log (1/t^4) ≤
        π*n*(1/t^4)*(1/t) := by
  have ht1 := tendsto_eighthRoot.eventually (eventually_ge_atTop (1 : ℝ))
  have hlarge := tendsto_eighthRoot.eventually (eventually_ge_atTop (D+10*C+4))
  have htd := tendsto_eighthRoot.eventually (eventually_ge_atTop (1/d+1))
  filter_upwards [eventually_ge_atTop 1, ht1, hlarge, htd] with n hn ht hlarge htd
  dsimp only
  let t := eighthRoot (n : ℝ)
  have hn0 : 0 < n := by omega
  have ht0 : 0 < t := eighthRoot_pos (by exact_mod_cast hn0)
  have he : t^8 = (n : ℝ) := eighthRoot_pow_eight (Nat.cast_nonneg n)
  have htd' : 1/t^2 ≤ d := by
    apply (div_le_iff₀ (pow_pos ht0 _)).mpr
    have hh : 1 ≤ d*t := by
      have hh := mul_le_mul_of_nonneg_left htd hd.le
      rw [mul_add, mul_one, mul_one_div_cancel hd.ne'] at hh
      linarith
    have hs : t ≤ t^2 := by change 1 ≤ t at ht; nlinarith
    nlinarith
  have hh1 : 1/t^4 ≤ 1 := (div_le_one (pow_pos ht0 _)).mpr (one_le_pow₀ ht)
  refine ⟨hn0, ht0, htd', by positivity, hh1, ?_, ?_⟩
  · change 1/(n : ℝ) ≤ 1/t^4
    rw [← he]
    apply one_div_le_one_div_of_le (pow_pos ht0 _)
    exact pow_le_pow_right₀ ht (by norm_num)
  · have hg := top_edge_scale_inequality (t := t) ht hC hD hlarge
    rw [he] at hg
    exact hg

end TaoAdditive1132
end
end SourceErdos1132_Additive_BernsteinScales

/- Erdos1132.Additive.InterpolantLocalGrowth -/
section SourceErdos1132_Additive_InterpolantLocalGrowth
/- # Uniform local growth for all interpolants with bounded nodal data

Main paper: §4, local potential and differentiation estimates.
-/

noncomputable section
open Set Complex Filter
open scoped Topology
namespace TaoAdditive1132

def localRectangleLoss (l r : ℝ) (n : ℕ) : ℝ :=
  4*((2+4/(r-l))*(n : ℝ)^2)*Real.exp (-(eighthRoot n)^2/2)

def localFrequency {n : ℕ} (X : Nodes n) (l r x : ℝ) : ℝ :=
  Real.pi*n*(X.exteriorDensity l r X.potentialNormalization x 0+1/eighthRoot n)

/-- The potential estimate and the real interval bound give a common complex
rectangle for every bounded choice of interpolation data. -/
theorem eventually_interpolant_local_growth {l r d : ℝ} (hlr : l < r)
    (hI : Icc l r ⊆ Icc (-1) 1) (hd : 0 < d) :
    ∀ᶠ (n : ℕ) in atTop, ∀ X : Nodes n,
      (∀ y ∈ Icc l r, X.lebesgue y ≤ n) →
      ∀ A : ℝ, 1 ≤ A → (∀ y ∈ Icc l r, X.lebesgue y ≤ A) →
      ∀ x ∈ Icc (l+2*d) (r-2*d), 0 ≤ X.exteriorDensity l r X.potentialNormalization x 0 →
      ∀ a : Fin n → ℝ, (∀ i, |a i| ≤ 1) →
      ∀ u v : ℝ, |u| ≤ (1/(eighthRoot n)^2)/2 → |v| ≤ 1/(eighthRoot n)^4 →
        ‖(X.interpolant a).eval₂ (algebraMap ℝ ℂ) ((x+u : ℝ)+v*I)‖ ≤
          A*Real.exp (localRectangleLoss l r n)*Real.exp (localFrequency X l r x*|v|) := by
  obtain ⟨C, hC, D, hD, htop⟩ := uniform_interpolant_top_edge hlr hI hd
  filter_upwards [eventually_top_edge_scales hC.le hD.le hd] with n hn
  rcases hn with ⟨hn0, ht0, hL, hH0, hH1, hHn, hgap⟩
  intro X hX A hA hXA x hx hρ a ha u v hu hv
  let t := eighthRoot (n : ℝ)
  have hL0 : 0 < 1/t^2 := by positivity
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  have hω : 0 ≤ localFrequency X l r x := by
    dsimp [localFrequency]
    positivity
  have hleft : l ≤ x-1/t^2 := by linarith [hx.1]
  have hright : x+1/t^2 ≤ r := by linarith [hx.2]
  have htop' (s : ℝ) (hs : |s| ≤ 1/t^2) :
      ‖(X.interpolant a).eval₂ (algebraMap ℝ ℂ) ((x+s : ℝ)+((1/t^4 : ℝ) : ℂ)*I)‖ ≤
        A*Real.exp (localFrequency X l r x*(1/t^4)) := by
    have hh := htop n X hn0 hX a ha x hx (1/t^2) (1/t^4) (1/t) hL0.le hL hHn hgap s hs
    have hm := mul_le_mul_of_nonneg_right hA
      (Real.exp_pos (localFrequency X l r x*(1/t^4))).le
    exact hh.trans (by simpa only [one_mul, localFrequency] using hm)
  have hg := polynomial_rectangle_growth hn0 hlr hI hL0 hH0 hH1 hA0 hω
    hleft hright (X.degree_interpolant_lt a)
    (fun y hy => (X.interpolant_eval_le a ha y).trans (hXA y hy)) htop' hu hv
  have he : -(1/t^2)/(2*(1/t^4)) = -t^2/2 := by field_simp
  rw [he] at hg
  exact hg

end TaoAdditive1132
end
end SourceErdos1132_Additive_InterpolantLocalGrowth

/- Erdos1132.Additive.RieszRadius -/
section SourceErdos1132_Additive_RieszRadius
/- # Choosing the finite Riesz contour inside the local growth rectangle

Main paper: §4, local potential and differentiation estimates.
-/

noncomputable section
open Real Filter
open scoped Topology
namespace TaoAdditive1132

def localRieszIndex (n : ℕ) : ℕ := ⌊(eighthRoot n)^2⌋₊

theorem floor_square_bounds {t : ℝ} (ht : 2 ≤ t) :
    1 ≤ ⌊t^2⌋₊ ∧ (⌊t^2⌋₊ : ℝ) ≤ t^2 ∧ t^2/2 ≤ (⌊t^2⌋₊ : ℝ) := by
  have hu := Nat.floor_le (sq_nonneg t)
  have hl := Nat.lt_floor_add_one (t^2)
  have ht2 : 4 ≤ t^2 := by nlinarith
  have hn : (1 : ℝ) ≤ ⌊t^2⌋₊ := by linarith
  refine ⟨by exact_mod_cast hn, hu, ?_⟩
  linarith

theorem riesz_radius_bounds {t c ω : ℝ} (ht : 2 ≤ t) (hc : 0 < c)
    (hct : 2 ≤ c*t^2) (hω : Real.pi*c*t^8 ≤ ω) :
    0 < ω ∧ (⌊t^2⌋₊ : ℝ)*Real.pi ≤ ω*((1/t^2)/2) ∧
      (⌊t^2⌋₊ : ℝ)*Real.pi ≤ ω*(1/t^4) ∧
      16/((⌊t^2⌋₊ : ℝ)*Real.pi) ≤ 32/t^2 := by
  have ht0 : 0 < t := by linarith
  have hm := floor_square_bounds ht
  have hm0 : (0 : ℝ) < ⌊t^2⌋₊ := by exact_mod_cast (show 0 < ⌊t^2⌋₊ by omega)
  have hω0 : 0 < ω := (by positivity : 0 < Real.pi*c*t^8).trans_le hω
  have ht2 : 1 ≤ t^2 := by nlinarith
  have ht4 : 1 ≤ t^4 := by nlinarith [sq_nonneg (t^2)]
  have hch : t^2 ≤ c*t^4 := by nlinarith [mul_nonneg (sub_nonneg.mpr hct) (sq_nonneg t)]
  have hcr : 2*t^2 ≤ c*t^6 := by
    have hm := mul_le_mul_of_nonneg_left ht4 (show 0 ≤ c*t^2 by positivity)
    nlinarith
  have hr' : t^2 ≤ c*t^8*((1/t^2)/2) := by
    have he : c*t^8*((1/t^2)/2) = c*t^6/2 := by field_simp
    rw [he]
    linarith
  have hh' : t^2 ≤ c*t^8*(1/t^4) := by
    have he : c*t^8*(1/t^4) = c*t^4 := by field_simp
    rwa [he]
  refine ⟨hω0, ?_, ?_, ?_⟩
  · have h1 := mul_le_mul_of_nonneg_left hr' Real.pi_pos.le
    have h2 := mul_le_mul_of_nonneg_right hω (show 0 ≤ (1/t^2)/2 by positivity)
    have h3 := mul_le_mul_of_nonneg_right hm.2.1 Real.pi_pos.le
    nlinarith
  · have h1 := mul_le_mul_of_nonneg_left hh' Real.pi_pos.le
    have h2 := mul_le_mul_of_nonneg_right hω (show 0 ≤ 1/t^4 by positivity)
    have h3 := mul_le_mul_of_nonneg_right hm.2.1 Real.pi_pos.le
    nlinarith
  · have hp : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
    have hden : t^2/2 ≤ (⌊t^2⌋₊ : ℝ)*Real.pi := by nlinarith [hm.2.2]
    have hd := one_div_le_one_div_of_le (show 0 < t^2/2 by positivity) hden
    have hmul := mul_le_mul_of_nonneg_left hd (by norm_num : (0 : ℝ) ≤ 16)
    convert! hmul using 1 <;> field_simp <;> ring

theorem eventually_riesz_radius {l r c : ℝ} (hc : 0 < c) :
    ∀ᶠ (n : ℕ) in atTop, ∀ (X : Nodes n) (x : ℝ),
      c ≤ X.exteriorDensity l r X.potentialNormalization x 0 →
      1 ≤ localRieszIndex n ∧ 0 < localFrequency X l r x ∧
      (localRieszIndex n : ℝ)*Real.pi ≤ localFrequency X l r x*((1/(eighthRoot n)^2)/2) ∧
      (localRieszIndex n : ℝ)*Real.pi ≤ localFrequency X l r x*(1/(eighthRoot n)^4) ∧
      16/((localRieszIndex n : ℝ)*Real.pi) ≤ 32/(eighthRoot n)^2 := by
  filter_upwards [tendsto_eighthRoot.eventually (eventually_ge_atTop (2 : ℝ)),
    tendsto_eighthRoot.eventually (eventually_ge_atTop (2/c+2))] with n ht hlarge
  intro X x hρ
  let t := eighthRoot (n : ℝ)
  have ht0 : 0 < t := by change 2 ≤ t at ht; linarith
  have hct : 2 ≤ c*t^2 := by
    have hm := mul_le_mul_of_nonneg_left hlarge hc.le
    rw [mul_add, mul_div_cancel₀ _ hc.ne'] at hm
    have hs : t ≤ t^2 := by nlinarith
    nlinarith
  have he : t^8 = (n : ℝ) := eighthRoot_pow_eight (Nat.cast_nonneg n)
  have hω : Real.pi*c*t^8 ≤ localFrequency X l r x := by
    have hp := mul_le_mul_of_nonneg_left
      (show c ≤ X.exteriorDensity l r X.potentialNormalization x 0+1/t by linarith [one_div_pos.mpr ht0])
      (show 0 ≤ Real.pi*(n : ℝ) by positivity)
    dsimp [localFrequency]
    rw [he]
    nlinarith
  have hb := riesz_radius_bounds ht hc hct hω
  exact ⟨(floor_square_bounds ht).1, hb⟩

end TaoAdditive1132
end
end SourceErdos1132_Additive_RieszRadius

/- Erdos1132.Additive.BernsteinLimits -/
section SourceErdos1132_Additive_BernsteinLimits
/- # Vanishing errors in the local differentiation estimates

Main paper: §4, local potential and differentiation estimates.
-/

noncomputable section
open Real Filter
open scoped Topology
namespace TaoAdditive1132

theorem tendsto_pow_mul_exp_neg_half (k : ℕ) :
    Tendsto (fun t : ℝ => t^k*Real.exp (-t/2)) atTop (𝓝 0) := by
  have ht : Tendsto (fun t : ℝ => t/2) atTop atTop := tendsto_id.atTop_div_const (by norm_num)
  have he := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).comp ht).const_mul ((2 : ℝ)^k)
  simp only [mul_zero, Function.comp_apply] at he
  convert he using 1
  funext t
  simp only [div_pow]
  have htwo : (2 : ℝ)^k ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [show -(t/2) = -t/2 by ring]
  field_simp

theorem tendsto_pow_mul_exp_neg_square_half (k : ℕ) :
    Tendsto (fun t : ℝ => t^k*Real.exp (-t^2/2)) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ (tendsto_pow_mul_exp_neg_half k)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    positivity
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) (pow_nonneg (by linarith) _)
    nlinarith

theorem localRectangleLoss_nonneg {l r : ℝ} (hlr : l < r) (n : ℕ) :
    0 ≤ localRectangleLoss l r n := by unfold localRectangleLoss; positivity

theorem tendsto_localRectangleLoss (l r : ℝ) :
    Tendsto (localRectangleLoss l r) atTop (𝓝 0) := by
  have ht := ((tendsto_pow_mul_exp_neg_square_half 16).comp tendsto_eighthRoot).const_mul
    (4*(2+4/(r-l)))
  simp only [mul_zero, Function.comp_apply] at ht
  convert ht using 1
  funext n
  have he := eighthRoot_pow_eight (Nat.cast_nonneg n)
  unfold localRectangleLoss
  have hp : (n : ℝ)^2 = (eighthRoot n)^16 := by
    calc
      (n : ℝ)^2 = ((eighthRoot n)^8)^2 := congrArg (fun y : ℝ => y^2) he.symm
      _ = _ := by ring
  rw [hp]
  ring

theorem tendsto_n_mul_localRectangleLoss (l r : ℝ) :
    Tendsto (fun n : ℕ => (n : ℝ)*localRectangleLoss l r n) atTop (𝓝 0) := by
  have ht := ((tendsto_pow_mul_exp_neg_square_half 24).comp tendsto_eighthRoot).const_mul
    (4*(2+4/(r-l)))
  simp only [mul_zero, Function.comp_apply] at ht
  convert ht using 1
  funext n
  let t := eighthRoot (n : ℝ)
  have he : t^8 = (n : ℝ) := eighthRoot_pow_eight (Nat.cast_nonneg n)
  change (n : ℝ)*(4*((2+4/(r-l))*(n : ℝ)^2)*Real.exp (-t^2/2)) = _
  have hp : (n : ℝ)*(n : ℝ)^2 = t^24 := by rw [← he]; ring
  calc
    _ = (4*(2+4/(r-l)))*((n : ℝ)*(n : ℝ)^2)*Real.exp (-t^2/2) := by ring
    _ = _ := by rw [hp]; ring

theorem tendsto_n_mul_exp_loss_sub_one {l r : ℝ} (hlr : l < r) :
    Tendsto (fun n : ℕ => (n : ℝ)*(Real.exp (localRectangleLoss l r n)-1)) atTop (𝓝 0) := by
  have ht := (tendsto_n_mul_localRectangleLoss l r).const_mul 2
  simp only [mul_zero, Function.comp_apply] at ht
  apply squeeze_zero' _ _ ht
  · exact Filter.Eventually.of_forall (fun n => mul_nonneg (Nat.cast_nonneg n)
      (sub_nonneg.mpr (Real.one_le_exp_iff.mpr (localRectangleLoss_nonneg hlr n))))
  · filter_upwards [(tendsto_localRectangleLoss l r).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
      with n hn
    have hd := localRectangleLoss_nonneg hlr n
    have he := Real.abs_exp_sub_one_le (x := localRectangleLoss l r n) (by simpa only [abs_of_nonneg hd] using hn.le)
    rw [abs_of_nonneg hd] at he
    have hb := (le_abs_self (Real.exp (localRectangleLoss l r n)-1)).trans he
    have hm := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg n (α := ℝ))
    nlinarith

theorem tendsto_inv_eighthRoot_nat :
    Tendsto (fun n : ℕ => 1/eighthRoot n) atTop (𝓝 0) :=
  tendsto_eighthRoot.const_div_atTop 1

theorem tendsto_log_div_eighthRoot_nat :
    Tendsto (fun n : ℕ => Real.log n/eighthRoot n) atTop (𝓝 0) := by
  have ht : Tendsto (fun t : ℝ => Real.log t/t) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have he := (ht.comp tendsto_eighthRoot).const_mul 8
  simp only [mul_zero, Function.comp_apply] at he
  apply he.congr
  intro n
  have hpow := eighthRoot_pow_eight (Nat.cast_nonneg n)
  have hl : Real.log n = 8*Real.log (eighthRoot n) := by
    calc
      Real.log n = Real.log ((eighthRoot n)^8) := congrArg Real.log hpow.symm
      _ = _ := by rw [Real.log_pow]; norm_num
  rw [hl]
  ring

theorem tendsto_log_affine_div_eighthRoot (a b : ℝ) :
    Tendsto (fun n : ℕ => (a*Real.log n+b)/eighthRoot n) atTop (𝓝 0) := by
  have ht := (tendsto_log_div_eighthRoot_nat.const_mul a).add
    (tendsto_inv_eighthRoot_nat.const_mul b)
  simp only [mul_zero, add_zero] at ht
  convert ht using 1
  funext n
  ring

theorem tendsto_log_affine_div_eighthRoot_sq (a b : ℝ) :
    Tendsto (fun n : ℕ => (a*Real.log n+b)/(eighthRoot n)^2) atTop (𝓝 0) := by
  have ht := (tendsto_log_affine_div_eighthRoot a b).mul tendsto_inv_eighthRoot_nat
  simp only [mul_zero, Function.comp_apply] at ht
  convert ht using 1
  funext n
  simp only [pow_two, div_eq_mul_inv, mul_inv_rev]
  ring

end TaoAdditive1132
end
end SourceErdos1132_Additive_BernsteinLimits

/- Erdos1132.Additive.BernsteinError -/
section SourceErdos1132_Additive_BernsteinError
/- # Additive error control for logarithmic upper levels

Main paper: §4, local potential and differentiation estimates.
-/

noncomputable section
open Real Filter
open scoped Topology
namespace TaoAdditive1132

def logarithmicLevel (a b : ℝ) (n : ℕ) : ℝ := a*Real.log n+b

def localDerivativeMultiplier (l r c : ℝ) (n : ℕ) : ℝ :=
  Real.exp (localRectangleLoss l r n)*(1+1/(c*eighthRoot n))*(1+32/(eighthRoot n)^2)

theorem tendsto_logarithmicLevel_div_nat (a b : ℝ) :
    Tendsto (fun n : ℕ => logarithmicLevel a b n/n) atTop (𝓝 0) := by
  have ht : Tendsto (fun x : ℝ => Real.log x/x) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have h1 := (ht.comp tendsto_natCast_atTop_atTop).const_mul a
  have h2 := (tendsto_natCast_atTop_atTop.const_div_atTop b :
    Tendsto (fun n : ℕ => b/(n : ℝ)) atTop (𝓝 0))
  have h := h1.add h2
  simp only [mul_zero, add_zero, Function.comp_apply] at h
  convert h using 1
  funext n
  dsimp [logarithmicLevel]
  ring

theorem tendsto_level_mul_exp_loss_sub_one {l r : ℝ} (hlr : l < r) (a b : ℝ) :
    Tendsto (fun n => logarithmicLevel a b n*(Real.exp (localRectangleLoss l r n)-1)) atTop (𝓝 0) := by
  have ht := (tendsto_logarithmicLevel_div_nat a b).mul (tendsto_n_mul_exp_loss_sub_one hlr)
  simp only [mul_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  field_simp

theorem tendsto_localDerivativeMultiplier_error {l r c : ℝ} (hlr : l < r) (hc : 0 < c)
    (a b : ℝ) :
    Tendsto (fun n => logarithmicLevel a b n*(localDerivativeMultiplier l r c n-1)) atTop (𝓝 0) := by
  have hbc : Tendsto (fun n : ℕ => 1/(c*eighthRoot n)) atTop (𝓝 0) := by
    have ht := tendsto_inv_eighthRoot_nat.const_mul (1/c)
    simp only [mul_zero] at ht
    convert ht using 1
    funext n
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hdc : Tendsto (fun n : ℕ => 32/(eighthRoot n)^2) atTop (𝓝 0) := by
    have ht := (tendsto_inv_eighthRoot_nat.pow 2).const_mul 32
    simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] at ht
    convert ht using 1
    funext n
    simp only [div_pow, one_pow, mul_one_div]
  have h1 := ((tendsto_level_mul_exp_loss_sub_one hlr a b).mul
    ((tendsto_const_nhds (x := (1 : ℝ))).add hbc)).mul ((tendsto_const_nhds (x := (1 : ℝ))).add hdc)
  have h2 : Tendsto (fun n => logarithmicLevel a b n/(c*eighthRoot n)) atTop (𝓝 0) := by
    have ht := (tendsto_log_affine_div_eighthRoot a b).div_const c
    simp only [zero_div] at ht
    convert ht using 1
    funext n
    dsimp [logarithmicLevel]
    ring
  have h3 := (tendsto_log_affine_div_eighthRoot_sq a b).const_mul 32
  have hsum := (h1.add (h2.mul ((tendsto_const_nhds (x := (1 : ℝ))).add hdc))).add h3
  simp only [zero_mul, mul_zero, zero_add] at hsum
  convert hsum using 1
  funext n
  dsimp [localDerivativeMultiplier, logarithmicLevel]
  ring

theorem tendsto_level_exp_loss_div_root_sq {l r : ℝ} (hlr : l < r) (a b : ℝ) :
    Tendsto (fun n => logarithmicLevel a b n*Real.exp (localRectangleLoss l r n)/(eighthRoot n)^2)
      atTop (𝓝 0) := by
  have ht := (tendsto_log_affine_div_eighthRoot_sq a b).mul
    (Real.continuous_exp.tendsto 0 |>.comp (tendsto_localRectangleLoss l r))
  simp only [zero_mul] at ht
  convert ht using 1
  funext n
  dsimp [logarithmicLevel]
  ring

theorem eventually_logarithmicLevel_bounds {a : ℝ} (ha : 0 < a) (b : ℝ) :
    ∀ᶠ n : ℕ in atTop, 0 < n ∧ 1 ≤ logarithmicLevel a b n ∧ logarithmicLevel a b n ≤ n := by
  have hinf : Tendsto (logarithmicLevel a b) atTop atTop :=
    tendsto_atTop_add_const_right atTop b
      ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop ha)
  have hratio := (tendsto_logarithmicLevel_div_nat a b).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [eventually_ge_atTop 1, hinf.eventually (eventually_ge_atTop 1), hratio]
    with n hn hlevel hratio
  have hn0 : 0 < n := by omega
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn0
  refine ⟨hn0, hlevel, ?_⟩
  exact ((div_lt_one hnR).mp hratio).le

end TaoAdditive1132
end
end SourceErdos1132_Additive_BernsteinError

/- Erdos1132.Additive.CosCircleBound -/
section SourceErdos1132_Additive_CosCircleBound
/- # Uniform cosine bounds on circles of radius an integer multiple of π

Main paper: §4, local potential and differentiation estimates.
-/

noncomputable section
open Complex Real Metric Set
namespace TaoAdditive1132

theorem abs_sinh_le_norm_cos (z : ℂ) : |Real.sinh z.im| ≤ ‖Complex.cos z‖ := by
  have he := norm_cos_sq z
  nlinarith [sq_abs (Real.sinh z.im), sq_nonneg (Real.cos z.re), norm_nonneg (Complex.cos z)]

theorem abs_cos_re_le_norm_cos (z : ℂ) : |Real.cos z.re| ≤ ‖Complex.cos z‖ := by
  have he := norm_cos_sq z
  nlinarith [sq_abs (Real.cos z.re), sq_nonneg (Real.sinh z.im), norm_nonneg (Complex.cos z)]

theorem exp_im_le_eight_norm_cos {m : ℕ} (hm : 1 ≤ m) {z : ℂ}
    (hz : ‖z‖ = m*Real.pi) : Real.exp |z.im| ≤ 8*‖Complex.cos z‖ := by
  have hR : 2 ≤ (m : ℝ)*Real.pi := by
    have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith [Real.pi_gt_three]
  by_cases hi : 1 ≤ |z.im|
  · have hh := exp_div_four_le_sinh hi
    rw [← Real.abs_sinh] at hh
    have hn := abs_sinh_le_norm_cos z
    nlinarith [norm_nonneg (Complex.cos z)]
  · have hi' : |z.im| ≤ 1 := le_of_lt (lt_of_not_ge hi)
    have hu : |z.re| ≤ (m : ℝ)*Real.pi := hz ▸ Complex.abs_re_le_norm z
    have hs : z.re^2+z.im^2 = ((m : ℝ)*Real.pi)^2 := by
      rw [← hz, Complex.sq_norm, Complex.normSq_apply]
      ring
    let d : ℝ := m*Real.pi-|z.re|
    have hd : 0 ≤ d := sub_nonneg.mpr hu
    have hd2 : d ≤ 1/2 := by
      have hi2 : z.im^2 ≤ 1 := by nlinarith [sq_abs z.im, abs_nonneg z.im]
      have hid : d*((m : ℝ)*Real.pi+|z.re|) = z.im^2 := by
        dsimp [d]
        nlinarith [sq_abs z.re]
      have hp : d*2 ≤ d*((m : ℝ)*Real.pi+|z.re|) :=
        mul_le_mul_of_nonneg_left (by linarith [abs_nonneg z.re]) hd
      linarith
    have hc : 1/2 ≤ |Real.cos d| := by
      have hl := Real.lipschitzWith_cos.dist_le_mul d 0
      simp only [Real.dist_eq, Real.cos_zero, NNReal.coe_one, one_mul, sub_zero,
        abs_of_nonneg hd] at hl
      have h := (abs_le.mp hl).1
      exact le_trans (by linarith : 1/2 ≤ Real.cos d) (le_abs_self _)
    have he : |Real.cos z.re| = |Real.cos d| := by
      have heq : |z.re| = (m : ℝ)*Real.pi-d := by dsimp [d]; ring
      rw [← Real.cos_abs z.re, heq, Real.cos_nat_mul_pi_sub, abs_mul, abs_pow]
      norm_num
    have hn : 1/2 ≤ ‖Complex.cos z‖ := by
      rw [← he] at hc
      exact hc.trans (abs_cos_re_le_norm_cos z)
    have hexp := Real.exp_le_exp.mpr hi'
    linarith [Real.exp_one_lt_three]

end TaoAdditive1132
end
end SourceErdos1132_Additive_CosCircleBound

/- Erdos1132.Additive.CosPoles -/
section SourceErdos1132_Additive_CosPoles
/- # The finite set of cosine poles used by the local Riesz formula

Main paper: §4, local potential and differentiation estimates.
-/

noncomputable section
open Complex Real Metric Set Finset
open scoped BigOperators
namespace TaoAdditive1132

def rieszPoint (j : ℤ) : ℝ := ((j : ℝ)+1/2)*Real.pi

def cosinePoles (m : ℕ) : Finset ℂ :=
  (Finset.Ico (-(m : ℤ)) (m : ℤ)).image (fun j => (rieszPoint j : ℂ))

theorem rieszPoint_cos (j : ℤ) : Complex.cos (rieszPoint j) = 0 := by
  apply Complex.cos_eq_zero_iff.mpr
  refine ⟨j, ?_⟩
  simp only [rieszPoint, ofReal_mul, ofReal_add, ofReal_intCast, ofReal_div, ofReal_one,
    ofReal_ofNat]
  ring

theorem rieszPoint_norm_lt {m : ℕ} {j : ℤ}
    (hj : j ∈ Finset.Ico (-(m : ℤ)) (m : ℤ)) : ‖(rieszPoint j : ℂ)‖ < (m : ℝ)*Real.pi := by
  rcases Finset.mem_Ico.mp hj with ⟨hlo, hhi⟩
  have hlo' : -(m : ℝ) ≤ j := by exact_mod_cast hlo
  have hhi' : (j : ℝ)+1 ≤ m := by exact_mod_cast (show j+1 ≤ (m : ℤ) by omega)
  rw [Complex.norm_real, Real.norm_eq_abs, rieszPoint, abs_mul, abs_of_pos Real.pi_pos]
  apply mul_lt_mul_of_pos_right _ Real.pi_pos
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

theorem cosinePoles_inside {m : ℕ} {z : ℂ} (hz : z ∈ cosinePoles m) :
    ‖z‖ < (m : ℝ)*Real.pi := by
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
  exact rieszPoint_norm_lt hj

theorem cosinePoles_real {m : ℕ} {z : ℂ} (hz : z ∈ cosinePoles m) : z.im = 0 := by
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
  simp

theorem cosinePoles_zero {m : ℕ} {z : ℂ} (hz : z ∈ cosinePoles m) : Complex.cos z = 0 := by
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
  exact rieszPoint_cos j

theorem zero_not_mem_cosinePoles (m : ℕ) : (0 : ℂ) ∉ cosinePoles m := by
  intro he
  have h := cosinePoles_zero he
  simpa using h

theorem cos_zero_mem_cosinePoles {m : ℕ} {z : ℂ} (hz : Complex.cos z = 0)
    (hn : ‖z‖ < (m : ℝ)*Real.pi) : z ∈ cosinePoles m := by
  obtain ⟨j, hj⟩ := Complex.cos_eq_zero_iff.mp hz
  have he : z = (rieszPoint j : ℂ) := by
    rw [hj]
    simp only [rieszPoint, ofReal_mul, ofReal_add, ofReal_intCast, ofReal_div, ofReal_one,
      ofReal_ofNat]
    ring
  rw [he] at hn ⊢
  apply Finset.mem_image.mpr
  refine ⟨j, Finset.mem_Ico.mpr ?_, rfl⟩
  rw [Complex.norm_real, Real.norm_eq_abs, rieszPoint, abs_mul, abs_of_pos Real.pi_pos] at hn
  have hab : |(j : ℝ)+1/2| < m := by nlinarith [Real.pi_pos]
  have hb := abs_lt.mp hab
  have hlo : -(m : ℝ)-1 < j := by linarith [hb.1]
  have hhi : (j : ℝ) < m := by linarith [hb.2]
  have hlo' : -(m : ℤ)-1 < j := by exact_mod_cast hlo
  have hhi' : j < (m : ℤ) := by exact_mod_cast hhi
  exact ⟨by omega, hhi'⟩

theorem cosinePoles_exact {m : ℕ} (hm : 1 ≤ m) {z : ℂ}
    (hz : z ∈ closedBall (0 : ℂ) ((m : ℝ)*Real.pi)) :
    Complex.cos z = 0 ↔ z ∈ cosinePoles m := by
  constructor
  · intro hc
    apply cos_zero_mem_cosinePoles hc
    have hn : ‖z‖ ≤ (m : ℝ)*Real.pi := by simpa [mem_closedBall, dist_eq_norm] using hz
    apply lt_of_le_of_ne hn
    intro he
    have hb := exp_im_le_eight_norm_cos hm he
    rw [hc, norm_zero, mul_zero] at hb
    exact (Real.exp_pos _).not_ge hb
  · exact cosinePoles_zero

theorem cosinePoles_sin_sq {m : ℕ} {z : ℂ} (hz : z ∈ cosinePoles m) :
    Complex.sin z ^ 2 = 1 := by
  have h := Complex.sin_sq_add_cos_sq z
  simpa [cosinePoles_zero hz] using h

theorem cosinePoles_simple {m : ℕ} {z : ℂ} (hz : z ∈ cosinePoles m) :
    deriv Complex.cos z ≠ 0 := by
  rw [Complex.deriv_cos]
  apply neg_ne_zero.mpr
  intro he
  have h := cosinePoles_sin_sq hz
  simp [he] at h

theorem cosinePoles_sin_norm {m : ℕ} {z : ℂ} (hz : z ∈ cosinePoles m) :
    ‖Complex.sin z‖ = 1 := by
  have h := congrArg norm (cosinePoles_sin_sq hz)
  rw [norm_pow, norm_one] at h
  nlinarith [norm_nonneg (Complex.sin z)]

theorem first_rieszPoint_mem {m : ℕ} (hm : 1 ≤ m) :
    (Real.pi/2 : ℂ) ∈ cosinePoles m := by
  apply Finset.mem_image.mpr
  refine ⟨0, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩
  simp [rieszPoint]
  ring

end TaoAdditive1132
end
end SourceErdos1132_Additive_CosPoles

/- Erdos1132.Additive.SimplePole -/
section SourceErdos1132_Additive_SimplePole
/- # Analytic cancellation of a simple pole

Main paper: §4, local potential and differentiation estimates.
-/

noncomputable section
open Filter Complex Set
open scoped Topology
namespace TaoAdditive1132

theorem analyticAt_dslope_same {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a) :
    AnalyticAt ℂ (dslope f a) a := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩

/-- Subtracting the principal part of a quotient at a simple zero leaves an
analytic divided difference. -/
theorem simple_pole_subtraction {f g : ℂ → ℂ} {a : ℂ}
    (hf : AnalyticAt ℂ f a) (hg : AnalyticAt ℂ g a)
    (hg0 : g a = 0) (hg1 : deriv g a ≠ 0) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H a ∧
      (fun z => f z/g z-(f a/deriv g a)/(z-a)) =ᶠ[𝓝[≠] a] H := by
  let q := fun z => f z/dslope g a z
  have hD := analyticAt_dslope_same hg
  have hD0 : dslope g a a ≠ 0 := by simpa only [dslope_same] using hg1
  have hq : AnalyticAt ℂ q a := hf.div hD hD0
  refine ⟨dslope q a, analyticAt_dslope_same hq, ?_⟩
  have hev : ∀ᶠ z in 𝓝 a, dslope g a z ≠ 0 := hD.continuousAt.eventually_ne hD0
  filter_upwards [hev.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hza
  have hza' : z ≠ a := hza
  have hgz : g z = (z-a)*dslope g a z := by
    simpa only [smul_eq_mul] using (sub_smul_dslope_of_zero hg0 z).symm
  have hqa : q a = f a/deriv g a := by simp only [q, dslope_same]
  rw [dslope_of_ne _ hza', slope_def_field, hgz, ← hqa]
  dsimp only [q]
  field_simp

/-- A meromorphic function with a local analytic extension has an analytic
normal form there. -/
theorem analyticAt_normalForm_of_extension {g H : ℂ → ℂ} {U : Set ℂ} {a : ℂ}
    (hg : MeromorphicOn g U) (ha : a ∈ U) (hH : AnalyticAt ℂ H a)
    (heq : g =ᶠ[𝓝[≠] a] H) :
    AnalyticAt ℂ (toMeromorphicNFOn g U) a := by
  have hord : 0 ≤ meromorphicOrderAt g a :=
    (hg a ha).meromorphicOrderAt_nonneg_iff.mpr ⟨H, hH, heq⟩
  have hnf := (hg a ha).meromorphicOrderAt_nonneg_iff_analyticAt_toMeromorphicNFAt.mp hord
  exact hnf.congr (toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds hg ha).symm

theorem normalForm_eventuallyEq_of_analyticAt {g : ℂ → ℂ} {U : Set ℂ} {a : ℂ}
    (hg : MeromorphicOn g U) (ha : a ∈ U) (hga : AnalyticAt ℂ g a) :
    toMeromorphicNFOn g U =ᶠ[𝓝 a] g := by
  have he := toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds hg ha
  rw [toMeromorphicNFAt_eq_self.mpr hga.meromorphicNFAt] at he
  exact he

end TaoAdditive1132
end
end SourceErdos1132_Additive_SimplePole

/- Erdos1132.Additive.FinitePoles -/
section SourceErdos1132_Additive_FinitePoles
/- # Removal of finitely many simple poles from an analytic quotient

Main paper: §4, local potential and differentiation estimates.
-/

noncomputable section
open Filter Complex Set Finset Metric
open scoped Topology BigOperators
namespace TaoAdditive1132

def principalParts (S : Finset ℂ) (r : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∑ a ∈ S, r a/(z-a)

def quotientRegularPart (f g : ℂ → ℂ) (S : Finset ℂ) : ℂ → ℂ :=
  toMeromorphicNFOn (fun z => f z/g z-principalParts S (fun a => f a/deriv g a) z) Set.univ

theorem analyticAt_principalParts {S : Finset ℂ} {r : ℂ → ℂ} {z : ℂ} (hz : z ∉ S) :
    AnalyticAt ℂ (principalParts S r) z := by
  apply Finset.analyticAt_fun_sum
  intro a ha
  apply analyticAt_const.div (analyticAt_id.sub analyticAt_const)
  change z-a ≠ 0
  exact sub_ne_zero.mpr (fun he => hz (he.symm ▸ ha))

theorem meromorphic_principalParts (S : Finset ℂ) (r : ℂ → ℂ) (z : ℂ) :
    MeromorphicAt (principalParts S r) z := by
  apply MeromorphicAt.fun_sum
  intro a _
  exact MeromorphicAt.div (by fun_prop) (by fun_prop)

theorem meromorphic_quotient_sub_principalParts {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hg : AnalyticOnNhd ℂ g Set.univ) (S : Finset ℂ) :
    MeromorphicOn (fun z => f z/g z-principalParts S (fun a => f a/deriv g a) z) Set.univ := by
  intro z _
  exact ((hf z trivial).meromorphicAt.div (hg z trivial).meromorphicAt).sub
    (meromorphic_principalParts S _ z)

theorem quotientRegularPart_eventuallyEq {f g : ℂ → ℂ} {S : Finset ℂ} {z : ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hg : AnalyticOnNhd ℂ g Set.univ)
    (hz : z ∉ S) (hgz : g z ≠ 0) :
    quotientRegularPart f g S =ᶠ[𝓝 z]
      (fun w => f w/g w-principalParts S (fun a => f a/deriv g a) w) := by
  apply normalForm_eventuallyEq_of_analyticAt
    (meromorphic_quotient_sub_principalParts hf hg S) (Set.mem_univ z)
  exact ((hf z trivial).div (hg z trivial) hgz).sub (analyticAt_principalParts hz)

/-- At a listed simple zero, the regular part is the analytic divided difference
of the local quotient, minus the other principal parts. -/
theorem analyticAt_quotientRegularPart_of_mem {f g : ℂ → ℂ} {S : Finset ℂ} {a : ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hg : AnalyticOnNhd ℂ g Set.univ)
    (ha : a ∈ S) (hga : g a = 0) (hg'a : deriv g a ≠ 0) :
    AnalyticAt ℂ (quotientRegularPart f g S) a := by
  obtain ⟨H, hH, heq⟩ := simple_pole_subtraction (hf a trivial) (hg a trivial) hga hg'a
  let r := fun a => f a/deriv g a
  have hother : AnalyticAt ℂ (principalParts (S.erase a) r) a :=
    analyticAt_principalParts (Finset.notMem_erase a S)
  apply analyticAt_normalForm_of_extension
    (meromorphic_quotient_sub_principalParts hf hg S) (Set.mem_univ a)
    (hH.sub hother)
  filter_upwards [heq] with z hz
  have hsum : principalParts S r z = r a/(z-a)+principalParts (S.erase a) r z := by
    unfold principalParts
    exact (Finset.add_sum_erase S (fun b => r b/(z-b)) ha).symm
  change f z/g z-principalParts S r z = H z-principalParts (S.erase a) r z
  rw [hsum]
  dsimp [r]
  rw [← hz]
  ring

theorem analyticOnNhd_quotientRegularPart {f g : ℂ → ℂ} {S : Finset ℂ} {V : Set ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hg : AnalyticOnNhd ℂ g Set.univ)
    (hzero : ∀ z ∈ V, g z = 0 ↔ z ∈ S)
    (hsimple : ∀ a ∈ S, deriv g a ≠ 0) :
    AnalyticOnNhd ℂ (quotientRegularPart f g S) V := by
  intro z hz
  by_cases hS : z ∈ S
  · exact analyticAt_quotientRegularPart_of_mem hf hg hS ((hzero z hz).mpr hS) (hsimple z hS)
  · have hgz : g z ≠ 0 := fun he => hS ((hzero z hz).mp he)
    have ha := ((hf z trivial).div (hg z trivial) hgz).sub (analyticAt_principalParts (r := fun a => f a/deriv g a) hS)
    exact ha.congr (quotientRegularPart_eventuallyEq hf hg hS hgz).symm

theorem hasDerivAt_principalParts {S : Finset ℂ} {r : ℂ → ℂ} {z : ℂ} (hz : z ∉ S) :
    HasDerivAt (principalParts S r) (∑ a ∈ S, -(r a/(z-a)^2)) z := by
  apply HasDerivAt.fun_sum
  intro a ha
  have hza : z-a ≠ 0 := sub_ne_zero.mpr (fun he => hz (he ▸ ha))
  convert! (hasDerivAt_const z (r a)).div ((hasDerivAt_id z).sub_const a) hza using 1
  simp only [id_eq, mul_one, zero_mul, zero_sub, neg_div]

theorem deriv_quotientRegularPart_zero {f g : ℂ → ℂ} {S : Finset ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hg : AnalyticOnNhd ℂ g Set.univ)
    (hS : (0 : ℂ) ∉ S) (hg0 : g 0 = 1) (hg'0 : deriv g 0 = 0) :
    deriv (quotientRegularPart f g S) 0 = deriv f 0 +
      ∑ a ∈ S, (f a/deriv g a)/a^2 := by
  have hq := (hf 0 trivial).differentiableAt.hasDerivAt.div
    (hg 0 trivial).differentiableAt.hasDerivAt (by simp [hg0])
  have hp := hasDerivAt_principalParts (r := fun a => f a/deriv g a) hS
  have he := quotientRegularPart_eventuallyEq hf hg hS (by simp [hg0])
  have h := (hq.sub hp).congr_of_eventuallyEq he
  rw [h.deriv]
  simp [hg0, hg'0, Finset.sum_neg_distrib]

end TaoAdditive1132
end
end SourceErdos1132_Additive_FinitePoles

/- Erdos1132.Additive.FiniteResidueFormula -/
section SourceErdos1132_Additive_FiniteResidueFormula
/- # A finite residue formula for the differentiated Cauchy kernel

Main paper: §4, local potential and differentiation estimates.
-/

noncomputable section
open Filter Complex Set Finset Metric
open scoped Topology BigOperators
namespace TaoAdditive1132

theorem circleIntegrable_inv_sub {R : ℝ} {a : ℂ} (hR : 0 < R) (ha : ‖a‖ < R) :
    CircleIntegrable (fun z => (z-a)⁻¹) 0 R := by
  apply ContinuousOn.circleIntegrable hR.le
  apply (continuousOn_id.sub continuousOn_const).inv₀
  intro z hz
  change z-a ≠ 0
  apply sub_ne_zero.mpr
  intro he
  have hn : ‖z‖ = R := by simpa [mem_sphere, dist_eq_norm] using hz
  rw [he] at hn
  exact ha.ne hn

theorem circleIntegrable_inv_sq {R : ℝ} (hR : 0 < R) :
    CircleIntegrable (fun z : ℂ => 1/z^2) 0 R := by
  apply ContinuousOn.circleIntegrable hR.le
  apply continuousOn_const.div (continuousOn_id.pow 2)
  intro z hz
  have hn : ‖z‖ = R := by simpa [mem_sphere, dist_eq_norm] using hz
  change z^2 ≠ 0
  exact pow_ne_zero _ (by intro he; simp [he] at hn; linarith)

theorem circleIntegral_inv_sq (R : ℝ) : (∮ z in C(0, R), (1/z^2 : ℂ)) = 0 := by
  simpa only [sub_zero, zpow_neg, zpow_natCast, one_div] using!
    circleIntegral.integral_sub_zpow_of_ne (by norm_num : (-2 : ℤ) ≠ -1) 0 0 R

/-- The two residues of this rational kernel cancel. -/
theorem circleIntegral_simplePole_div_sq {R : ℝ} {a : ℂ} (hR : 0 < R)
    (ha : ‖a‖ < R) (ha0 : a ≠ 0) :
    (∮ z in C(0, R), 1/((z-a)*z^2)) = 0 := by
  have hi1 := circleIntegrable_inv_sub hR ha
  have hi0 := circleIntegrable_inv_sub hR (by simpa using hR : ‖(0 : ℂ)‖ < R)
  simp only [sub_zero] at hi0
  have hi2 := circleIntegrable_inv_sq hR
  have hid : ∀ z ∈ sphere (0 : ℂ) R,
      1/((z-a)*z^2) = (1/a^2)*((z-a)⁻¹-z⁻¹)-(1/a)*(1/z^2) := by
    intro z hz
    have hn : ‖z‖ = R := by simpa [mem_sphere, dist_eq_norm] using hz
    have hz0 : z ≠ 0 := by intro he; simp [he] at hn; linarith
    have hza : z-a ≠ 0 := sub_ne_zero.mpr (fun he => ha.ne (he ▸ hn))
    field_simp
    ring
  have hiA : CircleIntegrable (fun z => (1/a^2)*((z-a)⁻¹-z⁻¹)) 0 R := by
    simpa only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply] using! (hi1.sub hi0).const_smul (a := (1/a^2))
  have hiB : CircleIntegrable (fun z => (1/a)*(1/z^2)) 0 R := by
    simpa only [Pi.smul_apply, smul_eq_mul] using! hi2.const_smul (a := (1/a))
  rw [circleIntegral.integral_congr hR.le hid,
    circleIntegral.integral_sub hiA hiB,
    circleIntegral.integral_const_mul, circleIntegral.integral_const_mul,
    circleIntegral.integral_sub hi1 hi0,
    circleIntegral.integral_sub_inv_of_mem_ball (by simpa [mem_ball, dist_eq_norm] using ha)]
  have he0 := circleIntegral.integral_sub_inv_of_mem_ball (c := (0 : ℂ)) (w := 0)
    (R := R) (by simpa using hR)
  simp only [sub_zero] at he0
  rw [he0, circleIntegral_inv_sq]
  ring

/-- The finite residue identity used in the local differentiation formula. -/
theorem finite_residue_derivative_formula {f g : ℂ → ℂ} {S : Finset ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hg : AnalyticOnNhd ℂ g Set.univ)
    (hR : 0 < R) (hS : (0 : ℂ) ∉ S)
    (hinside : ∀ a ∈ S, ‖a‖ < R)
    (hzero : ∀ z ∈ closedBall (0 : ℂ) R, g z = 0 ↔ z ∈ S)
    (hsimple : ∀ a ∈ S, deriv g a ≠ 0) (hg0 : g 0 = 1) (hg'0 : deriv g 0 = 0) :
    (∮ z in C(0, R), f z/(g z*z^2)) = (2*Real.pi*I)*
      (deriv f 0+∑ a ∈ S, (f a/deriv g a)/a^2) := by
  let H := quotientRegularPart f g S
  let r := fun a => f a/deriv g a
  have hH := analyticOnNhd_quotientRegularPart hf hg hzero hsimple
  have hHD : DifferentiableOn ℂ H (closedBall 0 R) := hH.differentiableOn
  have hC := hHD.deriv_eq_smul_circleIntegral hR
  have hzdata (z : ℂ) (hz : z ∈ sphere (0 : ℂ) R) : z ∉ S ∧ g z ≠ 0 ∧ z ≠ 0 := by
    have hn : ‖z‖ = R := by simpa [mem_sphere, dist_eq_norm] using hz
    have hnS : z ∉ S := fun he => (hinside z he).ne hn
    refine ⟨hnS, fun he => hnS ((hzero z (sphere_subset_closedBall hz)).mp he), ?_⟩
    intro he
    simp [he] at hn
    linarith
  have hpoint : ∀ z ∈ sphere (0 : ℂ) R,
      f z/(g z*z^2) = (1/z^2)*H z + ∑ a ∈ S, r a*(1/((z-a)*z^2)) := by
    intro z hz
    have hd := hzdata z hz
    have he := (quotientRegularPart_eventuallyEq hf hg hd.1 hd.2.1).eq_of_nhds
    change H z = f z/g z-principalParts S r z at he
    rw [he, principalParts, mul_sub, Finset.mul_sum]
    have heq : (∑ a ∈ S, r a*(1/((z-a)*z^2))) = (∑ a ∈ S, (1/z^2)*(r a/(z-a))) := by
      apply Finset.sum_congr rfl
      intro a ha
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    rw [heq]
    field_simp
    ring
  have hiH : CircleIntegrable (fun z => (1/z^2)*H z) 0 R := by
    apply ContinuousOn.circleIntegrable hR.le
    apply (continuousOn_const.div (continuousOn_id.pow 2)
      (fun z hz => pow_ne_zero _ (hzdata z hz).2.2)).mul
      (hH.continuousOn.mono sphere_subset_closedBall)
  have hip (a : ℂ) (ha : a ∈ S) : CircleIntegrable (fun z => r a*(1/((z-a)*z^2))) 0 R := by
    apply ContinuousOn.circleIntegrable hR.le
    apply continuousOn_const.mul
    apply continuousOn_const.div (by fun_prop)
    intro z hz
    apply mul_ne_zero _ (pow_ne_zero _ (hzdata z hz).2.2)
    exact sub_ne_zero.mpr (fun he => (hzdata z hz).1 (he ▸ ha))
  rw [circleIntegral.integral_congr hR.le hpoint,
    circleIntegral.integral_add hiH (CircleIntegrable.fun_sum S hip),
    circleIntegral.integral_fun_sum hip]
  have hs : (∑ a ∈ S, ∮ z in C(0, R), r a*(1/((z-a)*z^2))) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    rw [circleIntegral.integral_const_mul,
      circleIntegral_simplePole_div_sq hR (hinside a ha) (fun he => hS (he ▸ ha)), mul_zero]
  rw [hs, add_zero]
  simp only [sub_zero, smul_eq_mul] at hC
  rw [hC, deriv_quotientRegularPart_zero hf hg hS hg0 hg'0]

end TaoAdditive1132
end
end SourceErdos1132_Additive_FiniteResidueFormula

/- Erdos1132.Additive.FiniteRiesz -/
section SourceErdos1132_Additive_FiniteRiesz
/- # The local Riesz differentiation formula with an explicit error

Main paper: §4, local potential and differentiation estimates.
-/

noncomputable section
open Complex Real Metric Set Finset
open scoped BigOperators
namespace TaoAdditive1132

def rieszSum (m : ℕ) (f : ℂ → ℂ) : ℂ :=
  ∑ z ∈ cosinePoles m, Complex.sin z*f z/z^2

theorem norm_sin_le_exp_im (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  rw [Complex.sin, norm_div, norm_mul, norm_I, mul_one]
  norm_num only [Complex.norm_ofNat]
  have he1 : ‖Complex.exp (-z*I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simpa using le_abs_self z.im
  have he2 : ‖Complex.exp (z*I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simpa using neg_le_abs z.im
  have ht := norm_sub_le (Complex.exp (-z*I)) (Complex.exp (z*I))
  linarith

theorem cosine_residue_formula {f : ℂ → ℂ} {m : ℕ} (hm : 1 ≤ m)
    (hf : AnalyticOnNhd ℂ f Set.univ) :
    (∮ z in C(0, (m : ℝ)*Real.pi), f z/(Complex.cos z*z^2)) =
      (2*Real.pi*I)*(deriv f 0-rieszSum m f) := by
  have hR : 0 < (m : ℝ)*Real.pi := mul_pos (by exact_mod_cast (show 0 < m by omega)) Real.pi_pos
  have h := finite_residue_derivative_formula hf Complex.analyticOnNhd_cos hR
    (zero_not_mem_cosinePoles m) (fun a ha => cosinePoles_inside ha)
    (fun z hz => cosinePoles_exact hm hz) (fun a ha => cosinePoles_simple ha)
    Complex.cos_zero (by simp)
  rw [h, sub_eq_add_neg, rieszSum, ← Finset.sum_neg_distrib]
  congr 2
  apply Finset.sum_congr rfl
  intro a ha
  rw [Complex.deriv_cos]
  have hs := cosinePoles_sin_sq ha
  have hn : Complex.sin a ≠ 0 := by intro he; simp [he] at hs
  have hdiv : f a/Complex.sin a = Complex.sin a*f a := by
    apply (div_eq_iff hn).mpr
    calc
      f a = f a*(Complex.sin a)^2 := by rw [hs]; ring
      _ = Complex.sin a*f a*Complex.sin a := by ring
  rw [div_neg, hdiv]
  ring

theorem local_riesz_error {f : ℂ → ℂ} {m : ℕ} (hm : 1 ≤ m)
    (hf : AnalyticOnNhd ℂ f Set.univ)
    (hbound : ∀ z ∈ sphere (0 : ℂ) ((m : ℝ)*Real.pi), ‖f z‖ ≤ Real.exp |z.im|) :
    ‖deriv f 0-rieszSum m f‖ ≤ 8/((m : ℝ)*Real.pi) := by
  have hR : 0 < (m : ℝ)*Real.pi := mul_pos (by exact_mod_cast (show 0 < m by omega)) Real.pi_pos
  have hk : ∀ z ∈ sphere (0 : ℂ) ((m : ℝ)*Real.pi),
      ‖f z/(Complex.cos z*z^2)‖ ≤ 8/((m : ℝ)*Real.pi)^2 := by
    intro z hz
    have hn : ‖z‖ = (m : ℝ)*Real.pi := by simpa [mem_sphere, dist_eq_norm] using hz
    have hc := exp_im_le_eight_norm_cos hm hn
    have hc0 : 0 < ‖Complex.cos z‖ := by nlinarith [Real.exp_pos |z.im|]
    rw [norm_div, norm_mul, norm_pow, hn]
    apply (div_le_iff₀ (mul_pos hc0 (sq_pos_of_pos hR))).mpr
    have hh : (8/((m : ℝ)*Real.pi)^2)*(‖Complex.cos z‖*((m : ℝ)*Real.pi)^2) =
        8*‖Complex.cos z‖ := by field_simp
    rw [hh]
    exact (hbound z hz).trans hc
  have h := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hR.le hk
  rw [cosine_residue_formula hm hf, smul_eq_mul, inv_mul_cancel_left₀] at h
  · convert! h using 1 <;> field_simp <;> ring
  · exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero

def rieszWeight (z : ℂ) : ℝ := 1/‖z‖^2

theorem rieszWeight_nonneg (z : ℂ) : 0 ≤ rieszWeight z := by
  exact one_div_nonneg.mpr (sq_nonneg _)

theorem rieszWeight_coe {m : ℕ} {z : ℂ} (hz : z ∈ cosinePoles m) :
    (rieszWeight z : ℂ) = 1/z^2 := by
  have he : z = (z.re : ℂ) := by apply Complex.ext <;> simp [cosinePoles_real hz]
  rw [he]
  simp [rieszWeight, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem rieszSum_sin (m : ℕ) :
    rieszSum m Complex.sin = ((∑ z ∈ cosinePoles m, rieszWeight z : ℝ) : ℂ) := by
  rw [rieszSum, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro z hz
  rw [← pow_two, cosinePoles_sin_sq hz, rieszWeight_coe hz]

theorem rieszWeight_sum_error {m : ℕ} (hm : 1 ≤ m) :
    |1-∑ z ∈ cosinePoles m, rieszWeight z| ≤ 8/((m : ℝ)*Real.pi) := by
  have h := local_riesz_error hm Complex.analyticOnNhd_sin (fun z _ => norm_sin_le_exp_im z)
  rw [Complex.deriv_sin, Complex.cos_zero, rieszSum_sin, ← ofReal_one, ← ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] at h
  exact h

end TaoAdditive1132
end
end SourceErdos1132_Additive_FiniteRiesz

/- Erdos1132.Additive.LocalRiesz -/
section SourceErdos1132_Additive_LocalRiesz
/- # Sharp local differentiation and the near-equality implication

Main paper: §4, local potential and differentiation estimates.
-/

noncomputable section
open Complex Real Metric Set Finset
open scoped BigOperators
namespace TaoAdditive1132

theorem rieszSummand_norm_le {f : ℂ → ℂ} {m : ℕ} {z : ℂ}
    (hz : z ∈ cosinePoles m) (hf : ‖f z‖ ≤ 1) :
    ‖Complex.sin z*f z/z^2‖ ≤ rieszWeight z := by
  rw [norm_div, norm_mul, norm_pow, cosinePoles_sin_norm hz, one_mul]
  exact div_le_div_of_nonneg_right hf (sq_nonneg _)

theorem rieszSum_norm_le {f : ℂ → ℂ} {m : ℕ}
    (hf : ∀ z ∈ cosinePoles m, ‖f z‖ ≤ 1) :
    ‖rieszSum m f‖ ≤ ∑ z ∈ cosinePoles m, rieszWeight z := by
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun z hz => rieszSummand_norm_le hz (hf z hz)))

theorem local_riesz_derivative_bound {f : ℂ → ℂ} {m : ℕ} (hm : 1 ≤ m)
    (hf : AnalyticOnNhd ℂ f Set.univ)
    (hcircle : ∀ z ∈ sphere (0 : ℂ) ((m : ℝ)*Real.pi), ‖f z‖ ≤ Real.exp |z.im|)
    (hreal : ∀ x : ℝ, |x| < (m : ℝ)*Real.pi → ‖f x‖ ≤ 1) :
    ‖deriv f 0‖ ≤ 1+16/((m : ℝ)*Real.pi) := by
  have herr := local_riesz_error hm hf hcircle
  have hw := (abs_le.mp (rieszWeight_sum_error hm)).1
  have hs := rieszSum_norm_le (m := m) (f := f) (by
    intro z hz
    have he : z = (z.re : ℂ) := by apply Complex.ext <;> simp [cosinePoles_real hz]
    rw [he]
    apply hreal
    have hn := cosinePoles_inside hz
    rw [he] at hn
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hn)
  have ht := norm_add_le (deriv f 0-rieszSum m f) (rieszSum m f)
  rw [sub_add_cancel] at ht
  simp only [div_eq_mul_inv] at *
  linarith

theorem rieszSum_re_deficit {f : ℂ → ℂ} {m : ℕ} (hm : 1 ≤ m)
    (hf : ∀ z ∈ cosinePoles m, ‖f z‖ ≤ 1) :
    (rieszSum m f).re ≤ (∑ z ∈ cosinePoles m, rieszWeight z)-
      (4/Real.pi^2)*(1-(f (Real.pi/2)).re) := by
  let p : ℂ := Real.pi/2
  have hp : p ∈ cosinePoles m := first_rieszPoint_mem hm
  have hs : (rieszSum m f).re =
      ∑ z ∈ cosinePoles m, (Complex.sin z*f z/z^2).re := by
    simp only [rieszSum, Complex.re_sum]
  rw [hs, ← Finset.sum_erase_add _ _ hp,
    ← Finset.sum_erase_add (cosinePoles m) rieszWeight hp]
  have hsum : (∑ z ∈ (cosinePoles m).erase p, (Complex.sin z*f z/z^2).re) ≤
      ∑ z ∈ (cosinePoles m).erase p, rieszWeight z := by
    apply Finset.sum_le_sum
    intro z hz
    have hz' := Finset.mem_of_mem_erase hz
    exact (Complex.re_le_norm _).trans (rieszSummand_norm_le hz' (hf z hz'))
  have hpw : rieszWeight p = 4/Real.pi^2 := by
    dsimp [rieszWeight, p]
    simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
      Complex.norm_ofNat]
    field_simp
    norm_num
  have hps : (Complex.sin p*f p/p^2).re = (4/Real.pi^2)*(f p).re := by
    have hsin : Complex.sin p = 1 := Complex.sin_pi_div_two
    rw [hsin, one_mul, div_eq_mul_inv, ← one_div, ← rieszWeight_coe hp, hpw]
    simp only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    ring
  rw [hpw, hps]
  dsimp [p] at *
  linarith

theorem local_riesz_near_equality {f : ℂ → ℂ} {m : ℕ} {δ : ℝ} (hm : 1 ≤ m)
    (hf : AnalyticOnNhd ℂ f Set.univ)
    (hcircle : ∀ z ∈ sphere (0 : ℂ) ((m : ℝ)*Real.pi), ‖f z‖ ≤ Real.exp |z.im|)
    (hreal : ∀ x : ℝ, |x| < (m : ℝ)*Real.pi → ‖f x‖ ≤ 1)
    (hderiv : 1-δ ≤ (deriv f 0).re) :
    1-(Real.pi^2/4)*(δ+16/((m : ℝ)*Real.pi)) ≤ (f (Real.pi/2)).re := by
  have herr := local_riesz_error hm hf hcircle
  have hre := Complex.re_le_norm (deriv f 0-rieszSum m f)
  rw [sub_re] at hre
  have hw := (abs_le.mp (rieszWeight_sum_error hm)).1
  have hs := rieszSum_re_deficit hm (f := f) (by
    intro z hz
    have he : z = (z.re : ℂ) := by apply Complex.ext <;> simp [cosinePoles_real hz]
    rw [he]
    apply hreal
    have hn := cosinePoles_inside hz
    rw [he] at hn
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hn)
  have hdef : (4/Real.pi^2)*(1-(f (Real.pi/2)).re) ≤
      δ+16/((m : ℝ)*Real.pi) := by
    simp only [div_eq_mul_inv] at *
    linarith
  have hp : 0 < Real.pi^2 := sq_pos_of_pos Real.pi_pos
  have hmul := mul_le_mul_of_nonneg_left hdef (show 0 ≤ Real.pi^2/4 by positivity)
  have hc : (Real.pi^2/4)*(4/Real.pi^2) = 1 := by field_simp
  rw [← mul_assoc, hc, one_mul] at hmul
  linarith

end TaoAdditive1132
end
end SourceErdos1132_Additive_LocalRiesz

/- Erdos1132.Additive.RescaledRiesz -/
section SourceErdos1132_Additive_RescaledRiesz
/- # Local differentiation and peak estimates in the original polynomial coordinates

Main paper: §4, local potential and differentiation estimates.
-/

noncomputable section
open Polynomial Real Complex Set Metric
namespace TaoAdditive1132

def rescaledPolynomial (p : ℝ[X]) (x ω M : ℝ) (z : ℂ) : ℂ :=
  p.eval₂ (algebraMap ℝ ℂ) ((x : ℂ)+z/(ω : ℂ))/(M : ℂ)

theorem rescaledPolynomial_differentiable (p : ℝ[X]) (x ω M : ℝ) :
    Differentiable ℂ (rescaledPolynomial p x ω M) := by
  have hp : Differentiable ℂ (fun z : ℂ => aeval z p) := p.differentiable_aeval
  exact (hp.comp ((differentiable_id.div_const (ω : ℂ)).const_add (x : ℂ))).div_const _

theorem rescaledPolynomial_deriv (p : ℝ[X]) (x ω M : ℝ) :
    deriv (rescaledPolynomial p x ω M) 0 = ((p.derivative.eval x/(ω*M) : ℝ) : ℂ) := by
  have hi := ((hasDerivAt_id (0 : ℂ)).div_const (ω : ℂ)).const_add (x : ℂ)
  have hp := ((p.hasDerivAt_aeval _).comp 0 hi).div_const (M : ℂ)
  have he := hp.deriv
  change deriv (rescaledPolynomial p x ω M) 0 = _ at he
  rw [he]
  simp only [id_eq, zero_div, add_zero, aeval_def, real_polynomial_eval₂_real, one_div,
    ofReal_div, ofReal_mul]
  ring

theorem rescaledPolynomial_growth {p : ℝ[X]} {x ω M r h R : ℝ}
    (hω : 0 < ω) (hM : 0 < M) (hr : R ≤ ω*r) (hh : R ≤ ω*h)
    (hgrowth : ∀ u v : ℝ, |u| ≤ r → |v| ≤ h →
      ‖p.eval₂ (algebraMap ℝ ℂ) ((x+u : ℝ)+v*I)‖ ≤ M*Real.exp (ω*|v|))
    {z : ℂ} (hzre : |z.re| ≤ R) (hzim : |z.im| ≤ R) :
    ‖rescaledPolynomial p x ω M z‖ ≤ Real.exp |z.im| := by
  have hu : |z.re/ω| ≤ r := by
    rw [abs_div, abs_of_pos hω]
    exact (div_le_iff₀ hω).mpr (by nlinarith)
  have hv : |z.im/ω| ≤ h := by
    rw [abs_div, abs_of_pos hω]
    exact (div_le_iff₀ hω).mpr (by nlinarith)
  have he : (x : ℂ)+z/(ω : ℂ) = ((x+z.re/ω : ℝ) : ℂ)+(z.im/ω : ℝ)*I := by
    apply Complex.ext <;> simp [Complex.div_ofReal_re, Complex.div_ofReal_im]
  have hg := hgrowth (z.re/ω) (z.im/ω) hu hv
  have hab : ω*|z.im/ω| = |z.im| := by rw [abs_div, abs_of_pos hω]; field_simp
  rw [hab] at hg
  unfold rescaledPolynomial
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM, he]
  exact (div_le_iff₀ hM).mpr (by simpa only [mul_comm M] using hg)

/-- The Riesz derivative estimate after scaling the exponential type to one. -/
theorem polynomial_local_derivative_bound {p : ℝ[X]} {x ω M r h : ℝ} {m : ℕ}
    (hm : 1 ≤ m) (hω : 0 < ω) (hM : 0 < M)
    (hr : (m : ℝ)*Real.pi ≤ ω*r) (hh : (m : ℝ)*Real.pi ≤ ω*h)
    (hgrowth : ∀ u v : ℝ, |u| ≤ r → |v| ≤ h →
      ‖p.eval₂ (algebraMap ℝ ℂ) ((x+u : ℝ)+v*I)‖ ≤ M*Real.exp (ω*|v|)) :
    |p.derivative.eval x| ≤ ω*M*(1+16/((m : ℝ)*Real.pi)) := by
  have hR : 0 < (m : ℝ)*Real.pi := mul_pos (by exact_mod_cast (show 0 < m by omega)) Real.pi_pos
  have hF := rescaledPolynomial_differentiable p x ω M
  have hb := local_riesz_derivative_bound hm (fun z _ => hF.analyticAt z)
    (fun z hz => by
      have hn : ‖z‖ = (m : ℝ)*Real.pi := by simpa [mem_sphere, dist_eq_norm] using hz
      exact rescaledPolynomial_growth hω hM hr hh hgrowth
        ((Complex.abs_re_le_norm z).trans hn.le) ((Complex.abs_im_le_norm z).trans hn.le))
    (fun y hy => by
      have hg := rescaledPolynomial_growth hω hM hr hh hgrowth
        (z := (y : ℂ)) (by simpa using hy.le) (by simpa using hR.le)
      simpa using hg)
  rw [rescaledPolynomial_deriv, Complex.norm_real, Real.norm_eq_abs,
    abs_div, abs_of_pos (mul_pos hω hM)] at hb
  exact (div_le_iff₀ (mul_pos hω hM)).mp hb |>.trans_eq (by ring)

/-- A derivative close to the sharp bound forces a high value a distance
`π/(2ω)` to the right. -/
theorem polynomial_local_near_equality {p : ℝ[X]} {x ω M r h δ : ℝ} {m : ℕ}
    (hm : 1 ≤ m) (hω : 0 < ω) (hM : 0 < M)
    (hr : (m : ℝ)*Real.pi ≤ ω*r) (hh : (m : ℝ)*Real.pi ≤ ω*h)
    (hgrowth : ∀ u v : ℝ, |u| ≤ r → |v| ≤ h →
      ‖p.eval₂ (algebraMap ℝ ℂ) ((x+u : ℝ)+v*I)‖ ≤ M*Real.exp (ω*|v|))
    (hderiv : 1-δ ≤ p.derivative.eval x/(ω*M)) :
    M*(1-(Real.pi^2/4)*(δ+16/((m : ℝ)*Real.pi))) ≤ p.eval (x+Real.pi/(2*ω)) := by
  have hR : 0 < (m : ℝ)*Real.pi := mul_pos (by exact_mod_cast (show 0 < m by omega)) Real.pi_pos
  have hF := rescaledPolynomial_differentiable p x ω M
  have hb := local_riesz_near_equality hm (fun z _ => hF.analyticAt z)
    (fun z hz => by
      have hn : ‖z‖ = (m : ℝ)*Real.pi := by simpa [mem_sphere, dist_eq_norm] using hz
      exact rescaledPolynomial_growth hω hM hr hh hgrowth
        ((Complex.abs_re_le_norm z).trans hn.le) ((Complex.abs_im_le_norm z).trans hn.le))
    (fun y hy => by
      have hg := rescaledPolynomial_growth hω hM hr hh hgrowth
        (z := (y : ℂ)) (by simpa using hy.le) (by simpa using hR.le)
      simpa using hg)
    (by simpa only [rescaledPolynomial_deriv, ofReal_re] using hderiv)
  have he : (rescaledPolynomial p x ω M (Real.pi/2)).re = p.eval (x+Real.pi/(2*ω))/M := by
    unfold rescaledPolynomial
    have hi : (x : ℂ)+(Real.pi/2 : ℂ)/(ω : ℂ) = ((x+Real.pi/(2*ω) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hi, real_polynomial_eval₂_real, ← ofReal_div, ofReal_re]
  rw [he] at hb
  simpa only [mul_comm M] using (le_div_iff₀ hM).mp hb

/-- The absolute derivative version, obtained by changing the sign of the real
polynomial when necessary. -/
theorem polynomial_local_peak_abs {p : ℝ[X]} {x ω M r h δ : ℝ} {m : ℕ}
    (hm : 1 ≤ m) (hω : 0 < ω) (hM : 0 < M)
    (hr : (m : ℝ)*Real.pi ≤ ω*r) (hh : (m : ℝ)*Real.pi ≤ ω*h)
    (hgrowth : ∀ u v : ℝ, |u| ≤ r → |v| ≤ h →
      ‖p.eval₂ (algebraMap ℝ ℂ) ((x+u : ℝ)+v*I)‖ ≤ M*Real.exp (ω*|v|))
    (hderiv : 1-δ ≤ |p.derivative.eval x|/(ω*M)) :
    M*(1-(Real.pi^2/4)*(δ+16/((m : ℝ)*Real.pi))) ≤ |p.eval (x+Real.pi/(2*ω))| := by
  by_cases hp : 0 ≤ p.derivative.eval x
  · have hh := polynomial_local_near_equality hm hω hM hr hh hgrowth
      (by simpa only [abs_of_nonneg hp] using hderiv)
    exact hh.trans (le_abs_self _)
  · have hp' : p.derivative.eval x ≤ 0 := le_of_not_ge hp
    have hg : ∀ u v : ℝ, |u| ≤ r → |v| ≤ h →
        ‖(-p).eval₂ (algebraMap ℝ ℂ) ((x+u : ℝ)+v*I)‖ ≤ M*Real.exp (ω*|v|) := by
      intro u v hu hv
      simpa only [eval₂_neg, norm_neg] using hgrowth u v hu hv
    have hd : 1-δ ≤ (-p).derivative.eval x/(ω*M) := by
      simpa only [derivative_neg, eval_neg, abs_of_nonpos hp'] using hderiv
    have hb := polynomial_local_near_equality hm hω hM hr hh hg hd
    simp only [eval_neg] at hb
    exact hb.trans (neg_le_abs _)

end TaoAdditive1132
end
end SourceErdos1132_Additive_RescaledRiesz

/- Erdos1132.Additive.InterpolantDerivative -/
section SourceErdos1132_Additive_InterpolantDerivative
/- # The sharp local first derivative estimate for actual interpolation rows

Main paper: §4, local potential and differentiation estimates.
-/

noncomputable section
open Real Complex Set Filter
open scoped Topology
namespace TaoAdditive1132

theorem frequency_majorant {N ρ c t : ℝ} (hN : 0 ≤ N) (hc : 0 < c) (hρ : c ≤ ρ) (ht : 0 < t) :
    Real.pi*N*(ρ+1/t) ≤ (Real.pi*N*ρ)*(1+1/(c*t)) := by
  have hm := mul_le_mul_of_nonneg_right hρ (show 0 ≤ 1/(c*t) by positivity)
  have he : c*(1/(c*t)) = 1/t := by field_simp
  rw [he] at hm
  have h' : ρ+1/t ≤ ρ*(1+1/(c*t)) := by nlinarith
  have hp := mul_le_mul_of_nonneg_left h' (show 0 ≤ Real.pi*N by positivity)
  nlinarith

theorem derivative_multiplier_bound {N ρ c t A E e : ℝ}
    (hN : 0 ≤ N) (hc : 0 < c) (hρ : c ≤ ρ) (ht : 0 < t)
    (hA : 0 ≤ A) (hE : 0 ≤ E) (he0 : 0 ≤ e) (he : e ≤ 32/t^2) :
    (Real.pi*N*(ρ+1/t))*(A*E)*(1+e) ≤
      (Real.pi*N*ρ)*(A*(E*(1+1/(c*t))*(1+32/t^2))) := by
  have hρ0 : 0 < ρ := hc.trans_le hρ
  have hf := frequency_majorant hN hc hρ ht
  have h1 := mul_le_mul_of_nonneg_right hf (mul_nonneg hA hE)
  have h2 := mul_le_mul h1 (by linarith : 1+e ≤ 1+32/t^2)
    (by linarith : 0 ≤ 1+e) (by positivity : 0 ≤ (Real.pi*N*ρ)*(1+1/(c*t))*(A*E))
  convert! h2 using 1 <;> ring

/-- Under a local logarithmic upper bound, every bounded-data interpolant has
normalized first derivative at most that upper level plus any fixed positive error. -/
theorem eventually_sharp_interpolant_derivative (X : ∀ n, Nodes n)
    {l r d a b : ℝ} (hlr : l < r) (hI : Icc l r ⊆ Icc (-1) 1) (hd : 0 < d) (ha : 0 < a)
    (hupper : ∀ᶠ n : ℕ in atTop, ∀ y ∈ Icc l r, (X n).lebesgue y ≤ logarithmicLevel a b n)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, ∀ x ∈ Icc (l+2*d) (r-2*d), ∀ v : Fin n → ℝ,
      (∀ i, |v i| ≤ 1) →
      |((X n).interpolant v).derivative.eval x| ≤
        (Real.pi*n*(X n).exteriorDensity l r (X n).potentialNormalization x 0)*
          (logarithmicLevel a b n+η) := by
  have hlevels := eventually_logarithmicLevel_bounds ha b
  have hXn : ∀ᶠ n : ℕ in atTop, ∀ y ∈ Icc l r, (X n).lebesgue y ≤ n := by
    filter_upwards [hupper, hlevels] with n hu hl y hy
    exact (hu y hy).trans hl.2.2
  obtain ⟨c, hc, hdensity⟩ := eventually_exterior_density_positive X hlr hI
    (by linarith : 0 < 2*d) hXn
  have herr := (tendsto_localDerivativeMultiplier_error hlr hc a b).eventually
    (gt_mem_nhds hη)
  filter_upwards [hupper, hlevels, hXn, hdensity, eventually_interpolant_local_growth hlr hI hd,
    eventually_riesz_radius (l := l) (r := r) hc, herr]
    with n hu hl hn hdens hgrow hrad he
  intro x hx v hv
  let ρ := (X n).exteriorDensity l r (X n).potentialNormalization x 0
  let A := logarithmicLevel a b n
  let E := Real.exp (localRectangleLoss l r n)
  let t := eighthRoot (n : ℝ)
  let ω := localFrequency (X n) l r x
  have hρ : c ≤ ρ := hdens x hx
  have ht : 0 < t := eighthRoot_pos (by exact_mod_cast hl.1)
  have hA : 0 < A := zero_lt_one.trans_le hl.2.1
  have hE : 0 < E := Real.exp_pos _
  obtain ⟨hm, hω, hr, hh, herr⟩ := hrad (X n) x hρ
  have hg := hgrow (X n) hn A hl.2.1 hu x hx (hc.le.trans hρ) v hv
  have hbound := polynomial_local_derivative_bound hm hω (mul_pos hA hE) hr hh hg
  have hmajor := derivative_multiplier_bound (N := (n : ℝ)) (A := A) (E := E)
    (Nat.cast_nonneg n) hc hρ ht hA.le hE.le (by positivity) herr
  have hAerr : A*localDerivativeMultiplier l r c n ≤ A+η := by
    change A*(localDerivativeMultiplier l r c n-1) < η at he
    nlinarith
  have hρ0 : 0 < ρ := hc.trans_le hρ
  have hfinal := mul_le_mul_of_nonneg_left hAerr
    (show 0 ≤ Real.pi*n*ρ by positivity)
  exact hbound.trans (hmajor.trans hfinal)

end TaoAdditive1132
end
end SourceErdos1132_Additive_InterpolantDerivative

/- Erdos1132.Additive.SignedInterpolants -/
section SourceErdos1132_Additive_SignedInterpolants
/- # Bounded nodal data attaining Lebesgue values and derivative jumps

Main paper: §6, recurrence and Theorem 1(i).
-/

noncomputable section
open Set Filter Polynomial Finset Real
open scoped Topology BigOperators
namespace TaoAdditive1132

def unitSign (x : ℝ) : ℝ := if 0 ≤ x then 1 else -1

theorem abs_unitSign (x : ℝ) : |unitSign x| = 1 := by unfold unitSign; split <;> norm_num

theorem unitSign_mul (x : ℝ) : unitSign x*x = |x| := by
  unfold unitSign
  split_ifs with hx
  · simp [abs_of_nonneg hx]
  · simp [abs_of_neg (lt_of_not_ge hx)]

namespace Nodes
variable {n : ℕ} (X : Nodes n)

theorem interpolant_derivative_eval (v : Fin n → ℝ) (x : ℝ) :
    (X.interpolant v).derivative.eval x = ∑ i, v i*(X.cardinal i).derivative.eval x := by
  simp [interpolant, derivative_sum, derivative_mul, eval_finsetSum, eval_mul, eval_C]

theorem exists_interpolant_attaining (x : ℝ) :
    ∃ v : Fin n → ℝ, (∀ i, |v i| ≤ 1) ∧ (X.interpolant v).eval x = X.lebesgue x := by
  refine ⟨fun i => unitSign ((X.cardinal i).eval x), fun i => (abs_unitSign _).le, ?_⟩
  simp [interpolant, lebesgue, eval_finsetSum, eval_mul, eval_C, unitSign_mul]

theorem exists_interpolant_jump (k : Fin n) :
    ∃ v : Fin n → ℝ, (∀ i, |v i| ≤ 1) ∧
      (X.interpolant v).derivative.eval (X.point k) = X.derivativeJump k/2 := by
  classical
  let v (i : Fin n) := if i = k then (0:ℝ) else unitSign ((X.cardinal i).derivative.eval (X.point k))
  refine ⟨v, ?_, ?_⟩
  · intro i
    dsimp only [v]
    split_ifs <;> simp [abs_unitSign]
  · rw [X.interpolant_derivative_eval, X.derivativeJump_eq_cardinal_sum,
      ← sum_erase_add _ _ (Finset.mem_univ k)]
    simp only [v, if_true, zero_mul, add_zero]
    have he : (∑ i ∈ univ.erase k, (if i = k then (0:ℝ) else
      unitSign ((X.cardinal i).derivative.eval (X.point k)))*(X.cardinal i).derivative.eval (X.point k)) =
        ∑ i ∈ univ.erase k, |(X.cardinal i).derivative.eval (X.point k)| := by
      apply sum_congr rfl
      intro i hi
      rw [if_neg (mem_erase.mp hi).1, unitSign_mul]
    rw [he]
    ring

theorem derivativeJump_le_of_interpolant_bound (k : Fin n) {D : ℝ}
    (hD : ∀ v : Fin n → ℝ, (∀ i, |v i| ≤ 1) →
      |(X.interpolant v).derivative.eval (X.point k)| ≤ D) : X.derivativeJump k ≤ 2*D := by
  obtain ⟨v, hv, he⟩ := X.exists_interpolant_jump k
  have hh := hD v hv
  rw [he, abs_of_nonneg (div_nonneg (X.derivativeJump_nonneg k) (by norm_num))] at hh
  linarith

end Nodes

theorem eventually_normalized_jump_upper (X : ∀ n, Nodes n)
    {l r d a b : ℝ} (hlr : l < r) (hI : Icc l r ⊆ Icc (-1) 1) (hd : 0 < d) (ha : 0 < a)
    (hupper : ∀ᶠ n : ℕ in atTop, ∀ y ∈ Icc l r, (X n).lebesgue y ≤ logarithmicLevel a b n)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, ∀ k : Fin n, (X n).point k ∈ Icc (l+2*d) (r-2*d) →
      (X n).derivativeJump k ≤
        2*(Real.pi*n*(X n).exteriorDensity l r (X n).potentialNormalization ((X n).point k) 0)*
          (logarithmicLevel a b n+η) := by
  filter_upwards [eventually_sharp_interpolant_derivative X hlr hI hd ha hupper hη]
    with n hn k hk
  have hh := (X n).derivativeJump_le_of_interpolant_bound k (hn _ hk)
  convert! hh using 1 <;> ring

end TaoAdditive1132
end
end SourceErdos1132_Additive_SignedInterpolants

/- Erdos1132.Additive.WeightedDeficit -/
section SourceErdos1132_Additive_WeightedDeficit
/- # Many large values from a bounded weighted deficit

Main paper: §6, recurrence and Theorem 1(i).
-/

noncomputable section
open Finset
open scoped BigOperators
namespace TaoAdditive1132

theorem weighted_good_mass {ι : Type*} [Fintype ι]
    (w T : ι → ℝ) {U D C : ℝ} (hD : 0 < D)
    (hw : ∀ i, 0 ≤ w i) (hupper : ∀ i, 0 < w i → T i ≤ U)
    (hdef : (∑ i, w i*(U-T i)) ≤ C) :
    (∑ i, w i)-C/D ≤ ∑ i ∈ univ.filter (fun i => 0 < w i ∧ U-D ≤ T i), w i := by
  classical
  let G := univ.filter (fun i => 0 < w i ∧ U-D ≤ T i)
  have hpoint (i : ι) : w i ≤ (if i ∈ G then w i else 0)+w i*(U-T i)/D := by
    have hnn : 0 ≤ w i*(U-T i) := by
      by_cases hi : w i = 0
      · simp [hi]
      · exact mul_nonneg (hw i) (sub_nonneg.mpr (hupper i (lt_of_le_of_ne (hw i) (Ne.symm hi))))
    by_cases hi : i ∈ G
    · rw [if_pos hi]
      have hh := div_nonneg hnn hD.le
      linarith
    · rw [if_neg hi, zero_add]
      by_cases hw0 : w i = 0
      · simp [hw0]
      have hwp : 0 < w i := lt_of_le_of_ne (hw i) (Ne.symm hw0)
      have hbad : T i < U-D := by
        by_contra hh
        exact hi (mem_filter.mpr ⟨mem_univ i, hwp, le_of_not_gt hh⟩)
      apply (le_div_iff₀ hD).mpr
      nlinarith
  have hs := sum_le_sum (s := univ) (fun i _ => hpoint i)
  simp only [sum_add_distrib, ← sum_filter, ← sum_div] at hs
  have hd := div_le_div_of_nonneg_right hdef hD.le
  dsimp only [G] at hs
  simp only [filter_mem_eq_inter, univ_inter] at hs
  linarith

theorem many_large_values_of_weighted_deficit {n : ℕ} (hn : 0 < n)
    (w T : Fin n → ℝ) {U D C W B : ℝ} (hD : 0 < D) (hW : 0 < W) (hB : 0 < B)
    (hw : ∀ i, 0 ≤ w i) (hwb : ∀ i, w i ≤ B/(n:ℝ))
    (hupper : ∀ i, 0 < w i → T i ≤ U)
    (htotal : 3*W/4 ≤ ∑ i, w i) (hdef : (∑ i, w i*(U-T i)) ≤ C)
    (hsmall : C/D ≤ W/4) :
    (W/(2*B))*(n:ℝ) ≤
      ((univ.filter (fun i => 0 < w i ∧ U-D ≤ T i)).card : ℝ) := by
  classical
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  let G := univ.filter (fun i => 0 < w i ∧ U-D ≤ T i)
  have hg := weighted_good_mass w T hD hw hupper hdef
  have hm : W/2 ≤ ∑ i ∈ G, w i := by dsimp [G]; linarith
  have hbound : (∑ i ∈ G, w i) ≤ (G.card:ℝ)*(B/(n:ℝ)) := by
    calc
      _ ≤ ∑ _i ∈ G, B/(n:ℝ) := sum_le_sum (fun i hi => hwb i)
      _ = _ := by simp
  have hh := (le_div_iff₀ hnR).mp (show W/2 ≤ (G.card:ℝ)*B/(n:ℝ) by
    simpa only [mul_div_assoc] using hm.trans hbound)
  have hc : W*(n:ℝ)/(2*B) ≤ (G.card:ℝ) := (div_le_iff₀ (by positivity)).mpr (by nlinarith)
  convert! hc using 1 <;> ring

end TaoAdditive1132
end
end SourceErdos1132_Additive_WeightedDeficit

/- Erdos1132.Additive.LargeJumps -/
section SourceErdos1132_Additive_LargeJumps
/- # A positive proportion of nodes have large normalized derivative jumps

Main paper: §6, recurrence and Theorem 1(i).
-/

noncomputable section
open MeasureTheory Set Finset Filter Real
open scoped BigOperators Topology
namespace TaoAdditive1132

namespace Nodes
variable {n : ℕ} (X : Nodes n)

def jumpNodeWeight (a b : ℝ) (f : ℝ → ℝ) (i : Fin n) : ℝ :=
  (f (X.point i))^2/((n:ℝ)*X.exteriorDensity a b X.potentialNormalization (X.point i) 0)

def normalizedJump (a b : ℝ) (i : Fin n) : ℝ :=
  X.derivativeJump i/(2*Real.pi*(n:ℝ)*X.exteriorDensity a b X.potentialNormalization (X.point i) 0)

end Nodes

theorem eventually_many_large_jumps (X : ∀ n, Nodes n)
    {a b d l r M L c : ℝ} (hab : a < b) (hI : Icc a b ⊆ Icc (-1) 1)
    (hd : 0 < d) (hlr : l ≤ r) (hJ : Icc l r ⊆ Icc (a+2*d) (b-2*d))
    (hM : 0 ≤ M) (hL : 0 ≤ L) {f : ℝ → ℝ} (hf : Integrable f) (hfm : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hMf : ∀ x, f x ≤ M)
    (hlip : ∀ x y, |f x-f y| ≤ L*|x-y|) (hsupp : ∀ x, x ∉ Icc l r → f x = 0)
    (hW : 0 < ∫ x, (f x)^2)
    (hupper : ∀ᶠ n : ℕ in atTop, ∀ y ∈ Icc a b,
      (X n).lebesgue y ≤ logarithmicLevel (2/Real.pi) c n) :
    ∃ D > 0, ∃ κ > 0, ∀ᶠ n : ℕ in atTop,
      κ*(n:ℝ) ≤ ((univ.filter (fun i => (X n).point i ∈ Icc l r ∧
        (2/Real.pi)*Real.log n-D ≤ (X n).normalizedJump a b i)).card : ℝ) := by
  have hc0 : 0 < 2/Real.pi := by positivity
  have hlevels := eventually_logarithmicLevel_bounds hc0 c
  have hΛ : ∀ᶠ n : ℕ in atTop, ∀ y ∈ Icc a b, (X n).lebesgue y ≤ n := by
    filter_upwards [hupper, hlevels] with n hu hl y hy
    exact (hu y hy).trans hl.2.2
  have hMf' (x : ℝ) : |f x| ≤ M := by rw [abs_of_nonneg (hf0 x)]; exact hMf x
  obtain ⟨ρ₀, hρ₀, hpos⟩ := eventually_exterior_density_positive X hab hI (by linarith : 0 < 2*d) hΛ
  obtain ⟨Q, hQ, hquad⟩ := eventually_weighted_square_quadrature X hab hI
    (by linarith : 0 < 2*d) hlr hJ hM hL hfm hMf' hlip hsupp hΛ
  obtain ⟨E, hE, henergy⟩ := eventually_weighted_jump_lower X hab hI
    (by linarith : 0 < 2*d) hlr hJ hM hL hf hfm hf0 hMf hlip hsupp hΛ
  let W := ∫ x, (f x)^2
  let B := M^2/ρ₀+1
  let C := E+|c+1| * W+Q*(4*(2/Real.pi)+|c+1|)+1
  have hB : 0 < B := by dsimp [B]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  let D₀ := 4*(C+1)/W
  have hD₀ : 0 < D₀ := by dsimp [D₀]; positivity
  let D := D₀+|c+1|+1
  have hD : 0 < D := by dsimp [D]; positivity
  have hsmall : C/D₀ ≤ W/4 := by
    apply (div_le_iff₀ hD₀).mpr
    have he : (W/4)*D₀ = C+1 := by dsimp [D₀]; field_simp [show W ≠ 0 from hW.ne']
    rw [he]; linarith
  have hqsmall : ∀ᶠ n : ℕ in atTop, Q/quarterRoot n ≤ W/4 := by
    have hh := tendsto_inv_quarterRoot_nat.const_mul Q
    simp only [mul_zero, mul_one_div] at hh
    exact (hh.eventually (gt_mem_nhds (by positivity : (0:ℝ)<W/4))).mono (fun n hn => hn.le)
  refine ⟨D, hD, W/(2*B), by positivity, ?_⟩
  filter_upwards [hpos, hquad, henergy, hlevels, hqsmall,
    eventually_normalized_jump_upper X hab hI hd hc0 hupper (by norm_num : (0:ℝ)<1)]
    with n hnp hnq hne hnl hns hnu
  have hn := hnl.1
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hroot := one_le_quarterRoot hn1
  have hroot0 := quarterRoot_pos hnR
  let w := (X n).jumpNodeWeight a b f
  let T := (X n).normalizedJump a b
  let U := logarithmicLevel (2/Real.pi) c n+1
  have hU : 0 ≤ U := by dsimp [U]; linarith [hnl.2.1]
  have hw0 (i : Fin n) : 0 ≤ w i := by
    by_cases hi : (X n).point i ∈ Icc l r
    · have hρ : 0 < (X n).exteriorDensity a b (X n).potentialNormalization ((X n).point i) 0 :=
        hρ₀.trans_le (hnp _ (hJ hi))
      dsimp [w, Nodes.jumpNodeWeight]; positivity
    · simp [w, Nodes.jumpNodeWeight, hsupp _ hi]
  have hwpos (i : Fin n) (hi : 0 < w i) : (X n).point i ∈ Icc l r := by
    by_contra hh
    simp [w, Nodes.jumpNodeWeight, hsupp _ hh] at hi
  have hwb (i : Fin n) : w i ≤ B/(n:ℝ) := by
    by_cases hi : (X n).point i ∈ Icc l r
    · have hs := square_div_bound hρ₀ (hnp _ (hJ hi)) hM (hMf' ((X n).point i))
      have he : w i = ((f ((X n).point i))^2/
          (X n).exteriorDensity a b (X n).potentialNormalization ((X n).point i) 0)/(n:ℝ) := by
        dsimp [w, Nodes.jumpNodeWeight]; ring
      rw [he]
      exact div_le_div_of_nonneg_right ((le_abs_self _).trans hs |>.trans (by dsimp [B]; linarith)) hnR.le
    · simp [w, Nodes.jumpNodeWeight, hsupp _ hi, (div_pos hB hnR).le]
  have htupper (i : Fin n) (hi : 0 < w i) : T i ≤ U := by
    have hρ := hρ₀.trans_le (hnp _ (hJ (hwpos i hi)))
    apply (div_le_iff₀ (by positivity : 0 < 2*Real.pi*(n:ℝ)*
      (X n).exteriorDensity a b (X n).potentialNormalization ((X n).point i) 0)).mpr
    have hh := hnu i (hJ (hwpos i hi))
    convert! hh using 1 <;> ring
  have hwsum : (∑ i, w i) =
      (∑ i, (f ((X n).point i))^2/
        (X n).exteriorDensity a b (X n).potentialNormalization ((X n).point i) 0)/(n:ℝ) := by
    rw [sum_div]
    apply sum_congr rfl
    intro i hi
    dsimp [w, Nodes.jumpNodeWeight]
    ring
  have hq : |(∑ i, w i)-W| ≤ Q/quarterRoot n := by rw [hwsum]; exact hnq
  have htotal : 3*W/4 ≤ ∑ i, w i := by have hh := (abs_le.mp hq).1; linarith
  have he : (2/Real.pi)*Real.log n*W-E ≤ ∑ i, w i*T i := hne
  have hUQ : U*(Q/quarterRoot n) ≤ Q*(4*(2/Real.pi)+|c+1|) := by
    have hl := mul_le_mul_of_nonneg_left (log_div_quarterRoot_le hnR) hc0.le
    have hb : (c+1)/quarterRoot n ≤ |c+1| := by
      calc
        _ ≤ |c+1|/quarterRoot n := div_le_div_of_nonneg_right (le_abs_self _) hroot0.le
        _ ≤ |c+1| := (div_le_self (abs_nonneg _) hroot)
    have hu : U/quarterRoot n ≤ 4*(2/Real.pi)+|c+1| := by
      dsimp [U, logarithmicLevel]
      have he' : ((2/Real.pi)*Real.log n+c+1)/quarterRoot n =
        (2/Real.pi)*(Real.log n/quarterRoot n)+(c+1)/quarterRoot n := by ring
      rw [he']; linarith
    have hh := mul_le_mul_of_nonneg_left hu hQ.le
    convert! hh using 1 <;> ring
  have hdef : (∑ i, w i*(U-T i)) ≤ C := by
    have hq' := mul_le_mul_of_nonneg_left (abs_le.mp hq).2 hU
    have heq : (∑ i, w i*(U-T i)) = U*(∑ i, w i)-(∑ i, w i*T i) := by
      rw [mul_sum, ← sum_sub_distrib]; apply sum_congr rfl; intro i hi; ring
    rw [heq]
    have hcW := mul_le_mul_of_nonneg_right (le_abs_self (c+1)) hW.le
    dsimp [C, U, logarithmicLevel] at *
    nlinarith
  have hg := many_large_values_of_weighted_deficit hn w T hD₀ hW hB hw0 hwb htupper htotal hdef hsmall
  apply hg.trans
  exact_mod_cast Finset.card_le_card (show (univ.filter (fun i => 0 < w i ∧ U-D₀ ≤ T i)) ⊆
      (univ.filter (fun i => (X n).point i ∈ Icc l r ∧ (2/Real.pi)*Real.log n-D ≤ T i)) by
    intro i hi
    obtain ⟨hi0, hiT⟩ := (mem_filter.mp hi).2
    refine mem_filter.mpr ⟨mem_univ i, hwpos i hi0, ?_⟩
    dsimp [U, logarithmicLevel, D] at *
    have hc := neg_abs_le (c+1)
    linarith)

end TaoAdditive1132
end
end SourceErdos1132_Additive_LargeJumps

/- Erdos1132.Additive.LebesgueLipschitz -/
section SourceErdos1132_Additive_LebesgueLipschitz
/- # A local Lipschitz bound for the whole Lebesgue function

Main paper: §6, recurrence and Theorem 1(i).
-/

noncomputable section
open Set Filter Polynomial Real
open scoped Topology
namespace TaoAdditive1132
namespace Nodes
variable {n : ℕ} (X : Nodes n)

theorem lebesgue_lipschitz_of_interpolant_derivative {a b K : ℝ}
    (hbound : ∀ t ∈ Icc a b, ∀ v : Fin n → ℝ, (∀ i, |v i| ≤ 1) →
      |(X.interpolant v).derivative.eval t| ≤ K)
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    |X.lebesgue x-X.lebesgue y| ≤ K*|x-y| := by
  have hle (x y : ℝ) (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
      X.lebesgue x-X.lebesgue y ≤ K*|x-y| := by
    obtain ⟨v, hv, he⟩ := X.exists_interpolant_attaining x
    have hdiff := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun t ht => (X.interpolant v).differentiableAt)
      (fun t ht => by simpa only [Polynomial.deriv, Real.norm_eq_abs] using hbound t ht v hv)
      (convex_Icc a b) hy hx
    have hyv : (X.interpolant v).eval y ≤ X.lebesgue y :=
      (le_abs_self _).trans (X.interpolant_eval_le v hv y)
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at hdiff
    have hd := (le_abs_self ((X.interpolant v).eval x-(X.interpolant v).eval y)).trans hdiff
    rw [he] at hd
    linarith
  apply abs_le.mpr
  constructor
  · have hh := hle y x hy hx
    rw [abs_sub_comm y x] at hh
    linarith
  · exact hle x y hx hy

end Nodes

theorem eventually_lebesgue_lipschitz (X : ∀ n, Nodes n)
    {l r d a b : ℝ} (hlr : l < r) (hI : Icc l r ⊆ Icc (-1) 1) (hd : 0 < d) (ha : 0 < a)
    (hupper : ∀ᶠ n : ℕ in atTop, ∀ y ∈ Icc l r, (X n).lebesgue y ≤ logarithmicLevel a b n) :
    ∃ C > 0, ∀ᶠ n : ℕ in atTop, ∀ x ∈ Icc (l+2*d) (r-2*d),
      ∀ y ∈ Icc (l+2*d) (r-2*d),
        |(X n).lebesgue x-(X n).lebesgue y| ≤ C*(n:ℝ)*Real.log n*|x-y| := by
  obtain ⟨D, hD, hDb⟩ := uniform_exterior_density_bounds hlr hI (by linarith : 0 < 2*d)
  have hlevels := eventually_logarithmicLevel_bounds ha b
  have hlog : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (n:ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  refine ⟨Real.pi*D*(a+|b|+2), by positivity, ?_⟩
  filter_upwards [hupper, hlevels, hlog,
    eventually_sharp_interpolant_derivative X hlr hI hd ha hupper (by norm_num : (0:ℝ)<1)]
    with n hu hl hln hder
  have hnΛ (y : ℝ) (hy : y ∈ Icc l r) : (X n).lebesgue y ≤ n := (hu y hy).trans hl.2.2
  have hρb := (hDb n (X n) hl.1 hnΛ).1
  have hlev : logarithmicLevel a b n+1 ≤ (a+|b|+2)*Real.log n := by
    dsimp [logarithmicLevel]
    nlinarith [le_abs_self b, abs_nonneg b]
  intro x hx y hy
  apply (X n).lebesgue_lipschitz_of_interpolant_derivative (a := l+2*d) (b := r-2*d) ?_ hx hy
  intro t ht v hv
  have hρ := (le_abs_self _).trans (hρb t ht)
  have h1 := mul_le_mul_of_nonneg_left hρ (by positivity : 0 ≤ Real.pi*(n:ℝ))
  have h2 := mul_le_mul h1 hlev (by linarith [hl.2.1] : 0 ≤ logarithmicLevel a b n+1)
    (by positivity : 0 ≤ Real.pi*(n:ℝ)*D)
  exact (hder t ht v hv).trans (h2.trans_eq (by ring))

end TaoAdditive1132
end
end SourceErdos1132_Additive_LebesgueLipschitz

/- Erdos1132.Additive.NodeIsolation -/
section SourceErdos1132_Additive_NodeIsolation
/- # A large one-sided derivative forces an adjacent empty interval

Main paper: §6, recurrence and Theorem 1(i).
-/

noncomputable section
open Set Filter Polynomial Finset
open scoped Topology BigOperators
namespace TaoAdditive1132

theorem polynomial_endpoint_derivative_bound (p : ℝ[X]) {a b B : ℝ}
    (hab : a < b) (hB : 0 ≤ B) (he : p.eval a = p.eval b)
    (hsecond : ∀ t ∈ Icc a b, |p.derivative.derivative.eval t| ≤ B) :
    |p.derivative.eval a| ≤ B*(b-a) ∧ |p.derivative.eval b| ≤ B*(b-a) := by
  obtain ⟨c, hc, hcz⟩ := exists_hasDerivAt_eq_zero hab p.continuous.continuousOn he
    (fun t ht => p.hasDerivAt t)
  have hbound (z : ℝ) (hz : z ∈ Icc a b) : |p.derivative.eval z| ≤ B*|z-c| := by
    have hh := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun t ht => p.derivative.differentiableAt)
      (fun t ht => by simpa only [Polynomial.deriv, Real.norm_eq_abs] using hsecond t ht)
      (convex_Icc a b) ⟨hc.1.le, hc.2.le⟩ hz
    simpa only [Real.norm_eq_abs, hcz, sub_zero] using hh
  constructor
  · have hh := hbound a ⟨le_rfl, hab.le⟩
    rw [abs_of_neg (sub_neg.mpr hc.1)] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (by linarith [hc.2]) hB)
  · have hh := hbound b ⟨hab.le, le_rfl⟩
    rw [abs_of_pos (sub_pos.mpr hc.2)] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (by linarith [hc.1]) hB)

namespace Nodes
variable {n : ℕ} (X : Nodes n)

theorem exists_next_node (k : Fin n) (hne : ∃ j, X.point k < X.point j) :
    ∃ j, X.point k < X.point j ∧
      (∀ i, X.point k < X.point i → X.point j ≤ X.point i) ∧
      (∀ i, X.point i ∉ Ioo (X.point k) (X.point j)) := by
  classical
  let S := univ.filter (fun i => X.point k < X.point i)
  have hS : S.Nonempty := by obtain ⟨j, hj⟩ := hne; exact ⟨j, mem_filter.mpr ⟨mem_univ j, hj⟩⟩
  obtain ⟨j, hj, hmin⟩ := S.exists_min_image X.point hS
  have hjk : X.point k < X.point j := (mem_filter.mp hj).2
  have hnext (i : Fin n) (hi : X.point k < X.point i) : X.point j ≤ X.point i :=
    hmin i (mem_filter.mpr ⟨mem_univ i, hi⟩)
  exact ⟨j, hjk, hnext, fun i hi => (hnext i hi.1).not_gt hi.2⟩

theorem exists_previous_node (k : Fin n) (hne : ∃ j, X.point j < X.point k) :
    ∃ j, X.point j < X.point k ∧
      (∀ i, X.point i < X.point k → X.point i ≤ X.point j) ∧
      (∀ i, X.point i ∉ Ioo (X.point j) (X.point k)) := by
  classical
  let S := univ.filter (fun i => X.point i < X.point k)
  have hS : S.Nonempty := by obtain ⟨j, hj⟩ := hne; exact ⟨j, mem_filter.mpr ⟨mem_univ j, hj⟩⟩
  obtain ⟨j, hj, hmax⟩ := S.exists_max_image X.point hS
  have hjk : X.point j < X.point k := (mem_filter.mp hj).2
  have hprev (i : Fin n) (hi : X.point i < X.point k) : X.point i ≤ X.point j :=
    hmax i (mem_filter.mpr ⟨mem_univ i, hi⟩)
  exact ⟨j, hjk, hprev, fun i hi => (hprev i hi.2).not_gt hi.1⟩

theorem right_isolation_of_large_derivative (k : Fin n) {a b δ H B : ℝ}
    (hB : 0 < B) (hδ : 0 < δ) (hmargin : Icc (X.point k-δ) (X.point k+δ) ⊆ Icc a b)
    (hδB : B*δ ≤ H)
    (hder : H ≤ |derivWithin X.lebesgue (Ioi (X.point k)) (X.point k)|)
    (hsecond : ∀ v : Fin n → ℝ, (∀ i, |v i| ≤ 1) →
      ∀ t ∈ Icc a b, |(X.interpolant v).derivative.derivative.eval t| ≤ B) :
    ∀ j, X.point k < X.point j → X.point k+δ ≤ X.point j := by
  intro j hj
  by_contra hclose
  have hjclose := lt_of_not_ge hclose
  obtain ⟨i, hi, hmin, hgap⟩ := X.exists_next_node k ⟨j, hj⟩
  obtain ⟨v, hv, he⟩ := X.exists_interpolant_piece hi hgap
  have hend : (X.interpolant v).eval (X.point k) = (X.interpolant v).eval (X.point i) := by
    rw [he _ ⟨le_rfl, hi.le⟩, he _ ⟨hi.le, le_rfl⟩, X.lebesgue_at_node, X.lebesgue_at_node]
  have hh := (polynomial_endpoint_derivative_bound (X.interpolant v) hi hB.le hend
    (fun t ht => hsecond v hv t (hmargin ⟨by linarith [ht.1], by linarith [ht.2, hmin j hj]⟩))).1
  rw [X.piece_derivative_right hi he] at hh
  have hlen : X.point i-X.point k < δ := by linarith [hmin j hj]
  have hh' := mul_lt_mul_of_pos_left hlen hB
  linarith

theorem left_isolation_of_large_derivative (k : Fin n) {a b δ H B : ℝ}
    (hB : 0 < B) (hδ : 0 < δ) (hmargin : Icc (X.point k-δ) (X.point k+δ) ⊆ Icc a b)
    (hδB : B*δ ≤ H)
    (hder : H ≤ |derivWithin X.lebesgue (Iio (X.point k)) (X.point k)|)
    (hsecond : ∀ v : Fin n → ℝ, (∀ i, |v i| ≤ 1) →
      ∀ t ∈ Icc a b, |(X.interpolant v).derivative.derivative.eval t| ≤ B) :
    ∀ j, X.point j < X.point k → X.point j+δ ≤ X.point k := by
  intro j hj
  by_contra hclose
  have hjclose := lt_of_not_ge hclose
  obtain ⟨i, hi, hmax, hgap⟩ := X.exists_previous_node k ⟨j, hj⟩
  obtain ⟨v, hv, he⟩ := X.exists_interpolant_piece hi hgap
  have hend : (X.interpolant v).eval (X.point i) = (X.interpolant v).eval (X.point k) := by
    rw [he _ ⟨le_rfl, hi.le⟩, he _ ⟨hi.le, le_rfl⟩, X.lebesgue_at_node, X.lebesgue_at_node]
  have hh := (polynomial_endpoint_derivative_bound (X.interpolant v) hi hB.le hend
    (fun t ht => hsecond v hv t (hmargin ⟨by linarith [ht.1, hmax j hj], by linarith [ht.2]⟩))).2
  rw [X.piece_derivative_left hi he] at hh
  have hlen : X.point k-X.point i < δ := by linarith [hmax j hj]
  have hh' := mul_lt_mul_of_pos_left hlen hB
  linarith

def OneSidedIsolated (k : Fin n) (δ : ℝ) : Prop :=
  (∀ j, X.point k < X.point j → X.point k+δ ≤ X.point j) ∨
  (∀ j, X.point j < X.point k → X.point j+δ ≤ X.point k)

theorem oneSidedIsolated_of_large_jump (k : Fin n) {a b δ H B : ℝ}
    (hB : 0 < B) (hδ : 0 < δ) (hmargin : Icc (X.point k-δ) (X.point k+δ) ⊆ Icc a b)
    (hδB : B*δ ≤ H) (hjump : 2*H ≤ X.derivativeJump k)
    (hsecond : ∀ v : Fin n → ℝ, (∀ i, |v i| ≤ 1) →
      ∀ t ∈ Icc a b, |(X.interpolant v).derivative.derivative.eval t| ≤ B) :
    X.OneSidedIsolated k δ := by
  have hr := le_abs_self (derivWithin X.lebesgue (Ioi (X.point k)) (X.point k))
  have hl := neg_abs_le (derivWithin X.lebesgue (Iio (X.point k)) (X.point k))
  rw [derivativeJump] at hjump
  by_cases hright : H ≤ |derivWithin X.lebesgue (Ioi (X.point k)) (X.point k)|
  · exact Or.inl (X.right_isolation_of_large_derivative k hB hδ hmargin hδB hright hsecond)
  · exact Or.inr (X.left_isolation_of_large_derivative k hB hδ hmargin hδB (by linarith) hsecond)

end Nodes
end TaoAdditive1132
end
end SourceErdos1132_Additive_NodeIsolation

/- Erdos1132.Additive.IsolatedPacking -/
section SourceErdos1132_Additive_IsolatedPacking
/- # Local counting bounds from empty intervals on one side of every point

Main paper: §6, recurrence and Theorem 1(i).
-/

noncomputable section
open Set Finset MeasureTheory
open scoped BigOperators
namespace TaoAdditive1132

theorem separated_interval_card_bound {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ)
    (hx : ∀ i ∈ s, x i ∈ Icc a b)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ |x i-x j|) :
    δ*(s.card:ℝ) ≤ b-a+δ := by
  let A (i : ι) := Ico (x i) (x i+δ)
  have hd : (s : Set ι).PairwiseDisjoint A := by
    intro i hi j hj hij
    apply Set.disjoint_left.mpr
    intro t ht ht'
    have hs := hsep i hi j hj hij
    have hh : |x i-x j| < δ := abs_lt.mpr ⟨by linarith [ht'.1, ht.2], by linarith [ht.1, ht'.2]⟩
    exact hs.not_gt hh
  have hsub : (⋃ i ∈ s, A i) ⊆ Ico a (b+δ) := by
    intro t ht
    obtain ⟨i, hi, ht⟩ := mem_iUnion₂.mp ht
    exact ⟨(hx i hi).1.trans ht.1, by linarith [ht.2, (hx i hi).2]⟩
  have hh := measureReal_mono (μ := volume) hsub (by exact measure_Ico_lt_top.ne)
  rw [measureReal_biUnion_finset hd (fun i hi => measurableSet_Ico)
    (fun i hi => measure_Ico_lt_top.ne)] at hh
  have hm (i : ι) : volume.real (A i) = δ := by
    simp [A, Real.volume_real_Ico, hδ.le]
  simp_rw [hm] at hh
  have hbig : volume.real (Ico a (b+δ)) = b-a+δ := by
    rw [Real.volume_real_Ico, max_eq_left (by linarith)]
    ring
  rw [hbig] at hh
  simpa only [sum_const, nsmul_eq_mul, mul_comm δ] using hh

namespace Nodes
variable {n : ℕ} (X : Nodes n)

theorem isolated_interval_card_bound (s : Finset (Fin n)) {a b δ : ℝ}
    (hab : a ≤ b) (hδ : 0 < δ) (hx : ∀ i ∈ s, X.point i ∈ Icc a b)
    (hiso : ∀ i ∈ s, X.OneSidedIsolated i δ) :
    δ*(s.card:ℝ) ≤ 2*(b-a)+2*δ := by
  classical
  let P (i : Fin n) := ∀ j, X.point i < X.point j → X.point i+δ ≤ X.point j
  let R := s.filter P
  let L := s.filter (fun i => ¬P i)
  have hR (i : Fin n) (hi : i ∈ R) : P i := (mem_filter.mp hi).2
  have hL (i : Fin n) (hi : i ∈ L) : ∀ j, X.point j < X.point i → X.point j+δ ≤ X.point i :=
    (hiso i (mem_filter.mp hi).1).resolve_left (mem_filter.mp hi).2
  have hsepR : ∀ i ∈ R, ∀ j ∈ R, i ≠ j → δ ≤ |X.point i-X.point j| := by
    intro i hi j hj hij
    rcases lt_or_gt_of_ne (X.injective.ne hij) with hh | hh
    · rw [abs_of_neg (sub_neg.mpr hh)]
      linarith [hR i hi j hh]
    · rw [abs_of_pos (sub_pos.mpr hh)]
      linarith [hR j hj i hh]
  have hsepL : ∀ i ∈ L, ∀ j ∈ L, i ≠ j → δ ≤ |X.point i-X.point j| := by
    intro i hi j hj hij
    rcases lt_or_gt_of_ne (X.injective.ne hij) with hh | hh
    · rw [abs_of_neg (sub_neg.mpr hh)]
      linarith [hL j hj i hh]
    · rw [abs_of_pos (sub_pos.mpr hh)]
      linarith [hL i hi j hh]
  have hbR := separated_interval_card_bound R X.point hab hδ
    (fun i hi => hx i (mem_filter.mp hi).1) hsepR
  have hbL := separated_interval_card_bound L X.point hab hδ
    (fun i hi => hx i (mem_filter.mp hi).1) hsepL
  have hc : (R.card:ℝ)+(L.card:ℝ) = (s.card:ℝ) := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := s) P
  nlinarith

end Nodes
end TaoAdditive1132
end
end SourceErdos1132_Additive_IsolatedPacking

/- Erdos1132.Additive.PolynomialSecondDerivative -/
section SourceErdos1132_Additive_PolynomialSecondDerivative
/- # The second derivative bound from local complex growth

Main paper: §4, local potential and differentiation estimates.
-/

noncomputable section
open Polynomial Real Complex Set Metric
namespace TaoAdditive1132

theorem polynomial_second_derivative_bound {p : ℝ[X]} {x ω M r h : ℝ}
    (hω : 0 < ω) (hM : 0 ≤ M) (hr : 1/ω ≤ r) (hh : 1/ω ≤ h)
    (hgrowth : ∀ u v : ℝ, |u| ≤ r → |v| ≤ h →
      ‖p.eval₂ (algebraMap ℝ ℂ) ((x+u : ℝ)+v*I)‖ ≤ M*Real.exp (ω*|v|)) :
    |p.derivative.derivative.eval x| ≤ 2*M*Real.exp 1*ω^2 := by
  have hf : Differentiable ℂ (fun z : ℂ => aeval z p) := p.differentiable_aeval
  have hb := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    (f := fun z : ℂ => aeval z p) (c := (x : ℂ)) 2 (one_div_pos.mpr hω) hf.diffContOnCl
    (C := M*Real.exp 1) (by
      intro z hz
      have hn : ‖z-(x : ℂ)‖ = 1/ω := by simpa [mem_sphere, dist_eq_norm] using hz
      have hu : |z.re-x| ≤ 1/ω := by
        have ht := Complex.abs_re_le_norm (z-(x : ℂ))
        simpa only [sub_re, ofReal_re, hn] using ht
      have hv : |z.im| ≤ 1/ω := by
        have ht := Complex.abs_im_le_norm (z-(x : ℂ))
        simpa only [sub_im, ofReal_im, sub_zero, hn] using ht
      have hg := hgrowth (z.re-x) z.im (hu.trans hr) (hv.trans hh)
      have he : (((x+(z.re-x) : ℝ) : ℂ)+z.im*I) = z := by
        rw [add_sub_cancel, re_add_im]
      rw [he] at hg
      apply hg.trans
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) hM
      have ht := mul_le_mul_of_nonneg_left hv hω.le
      simpa only [mul_one_div_cancel hω.ne'] using ht)
  have hder : iteratedDeriv 2 (fun z : ℂ => aeval z p) (x : ℂ) =
      ((p.derivative.derivative.eval x : ℝ) : ℂ) := by
    rw [show (2 : ℕ) = 1+1 by rfl, iteratedDeriv_succ, iteratedDeriv_one]
    have he : deriv (fun z : ℂ => aeval z p) = (fun z : ℂ => aeval z p.derivative) :=
      funext (fun _ => p.deriv_aeval)
    rw [he, Polynomial.deriv_aeval]
    exact real_polynomial_eval₂_real _ _
  rw [hder, Complex.norm_real, Real.norm_eq_abs] at hb
  norm_num only [Nat.factorial, Nat.cast_ofNat, Nat.cast_one, Nat.cast_mul, mul_one] at hb
  convert hb using 1 <;> field_simp <;> ring

end TaoAdditive1132
end
end SourceErdos1132_Additive_PolynomialSecondDerivative

/- Erdos1132.Additive.InterpolantSecondDerivative -/
section SourceErdos1132_Additive_InterpolantSecondDerivative
/- # A uniform second derivative bound for bounded-data interpolants

Main paper: §4, local potential and differentiation estimates.
-/

noncomputable section
open Real Complex Set Filter
open scoped Topology
namespace TaoAdditive1132

theorem eventually_interpolant_second_derivative (X : ∀ n, Nodes n)
    {l r d a b : ℝ} (hlr : l < r) (hI : Icc l r ⊆ Icc (-1) 1) (hd : 0 < d) (ha : 0 < a)
    (hupper : ∀ᶠ n : ℕ in atTop, ∀ y ∈ Icc l r, (X n).lebesgue y ≤ logarithmicLevel a b n) :
    ∃ C > 0, ∀ᶠ n : ℕ in atTop, ∀ x ∈ Icc (l+2*d) (r-2*d), ∀ v : Fin n → ℝ,
      (∀ i, |v i| ≤ 1) →
      |((X n).interpolant v).derivative.derivative.eval x| ≤ C*(n : ℝ)^2*Real.log n := by
  have hlevels := eventually_logarithmicLevel_bounds ha b
  have hXn : ∀ᶠ n : ℕ in atTop, ∀ y ∈ Icc l r, (X n).lebesgue y ≤ n := by
    filter_upwards [hupper, hlevels] with n hu hl y hy
    exact (hu y hy).trans hl.2.2
  obtain ⟨c, hc, hdensity⟩ := eventually_exterior_density_positive X hlr hI
    (by linarith : 0 < 2*d) hXn
  obtain ⟨D, hD, hDbound⟩ := uniform_exterior_density_bounds hlr hI (by linarith : 0 < 2*d)
  let K : ℝ := a+|b|+1
  let C : ℝ := 2*Real.exp 1*Real.exp 1*(Real.pi*(D+1))^2*K
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  have hloss := (tendsto_localRectangleLoss l r).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop (1 : ℝ))
  filter_upwards [hupper, hlevels, hXn, hdensity, eventually_interpolant_local_growth hlr hI hd,
    eventually_riesz_radius (l := l) (r := r) hc, hloss, hlog,
    tendsto_eighthRoot.eventually (eventually_ge_atTop (1 : ℝ))]
    with n hu hl hn hdens hgrow hrad hloss hlog ht
  change 1 ≤ Real.log (n : ℝ) at hlog
  intro x hx v hv
  let ρ := (X n).exteriorDensity l r (X n).potentialNormalization x 0
  let A := logarithmicLevel a b n
  let E := Real.exp (localRectangleLoss l r n)
  let t := eighthRoot (n : ℝ)
  let ω := localFrequency (X n) l r x
  have hρ : c ≤ ρ := hdens x hx
  have hA : 0 < A := zero_lt_one.trans_le hl.2.1
  have hE : 0 < E := Real.exp_pos _
  obtain ⟨hm, hω, hr, hh, herr⟩ := hrad (X n) x hρ
  have hR : 1 ≤ (localRieszIndex n : ℝ)*Real.pi := by
    have hmR : (1 : ℝ) ≤ localRieszIndex n := by exact_mod_cast hm
    nlinarith [Real.pi_gt_three]
  have hr' : 1/ω ≤ (1/t^2)/2 := by apply (div_le_iff₀ hω).mpr; nlinarith
  have hh' : 1/ω ≤ 1/t^4 := by apply (div_le_iff₀ hω).mpr; nlinarith
  have hg := hgrow (X n) hn A hl.2.1 hu x hx (hc.le.trans hρ) v hv
  have hbound := polynomial_second_derivative_bound hω (mul_pos hA hE).le hr' hh' hg
  have hDb := (abs_le.mp ((hDbound n (X n) hl.1 hn).1 x hx)).2
  have hωD : ω ≤ (Real.pi*(D+1))*(n : ℝ) := by
    have hinv : 1/t ≤ 1 := (div_le_one (by linarith : 0 < t)).mpr ht
    have hp := mul_le_mul_of_nonneg_left (show ρ+1/t ≤ D+1 by linarith)
      (show 0 ≤ Real.pi*(n : ℝ) by positivity)
    exact hp.trans_eq (by ring)
  have hE1 : E ≤ Real.exp 1 := Real.exp_le_exp.mpr hloss.le
  have hAK : A ≤ K*Real.log n := by
    have hb := le_abs_self b
    have hm := mul_le_mul_of_nonneg_left hlog (abs_nonneg b)
    dsimp [A, K, logarithmicLevel]
    nlinarith
  have hstep : 2*(A*E)*Real.exp 1*ω^2 ≤
      2*((K*Real.log n)*Real.exp 1)*Real.exp 1*((Real.pi*(D+1))*(n : ℝ))^2 := by
    gcongr
  exact hbound.trans (hstep.trans_eq (by dsimp [C]; ring))

end TaoAdditive1132
end
end SourceErdos1132_Additive_InterpolantSecondDerivative

/- Erdos1132.Additive.PeakArithmetic -/
section SourceErdos1132_Additive_PeakArithmetic
/- # Quantitative transfer from a large derivative to the Riesz peak

Main paper: §4, local potential and differentiation estimates.
-/

noncomputable section
open Real
namespace TaoAdditive1132

theorem frequency_ratio_lower {ρ c t A K q : ℝ} (hc : 0 < c) (hρ : c ≤ ρ) (ht : 0 < t)
    (hA : 0 ≤ A) (hK : 0 ≤ K) (hq : A-K ≤ q) :
    A-K-A/(c*t) ≤ q*(ρ/(ρ+1/t)) := by
  have hρ0 : 0 < ρ := hc.trans_le hρ
  have hden : 0 < ρ+1/t := by positivity
  have hθ0 : 0 ≤ ρ/(ρ+1/t) := div_nonneg hρ0.le hden.le
  have hθ1 : ρ/(ρ+1/t) ≤ 1 := (div_le_one hden).mpr (by linarith [one_div_pos.mpr ht])
  have hθ : 1-1/(c*t) ≤ ρ/(ρ+1/t) := by
    apply (le_div_iff₀ hden).mpr
    have hm := mul_le_mul_of_nonneg_right hρ (show 0 ≤ 1/(c*t) by positivity)
    have he : c*(1/(c*t)) = 1/t := by field_simp
    rw [he] at hm
    have hp := mul_nonneg (show 0 ≤ 1/t by positivity) (show 0 ≤ 1/(c*t) by positivity)
    nlinarith
  have h1 := mul_le_mul_of_nonneg_left hθ hA
  have h2 := mul_le_mul_of_nonneg_left hθ1 hK
  have h3 := mul_le_mul_of_nonneg_right hq hθ0
  simp only [div_eq_mul_inv] at *
  nlinarith

theorem peak_deficit_bound {M A Q ω e K : ℝ} (hM : 0 < M) (hω : 0 < ω)
    (hMA : A ≤ M) (hM1 : M ≤ A+1) (hQ : A-K-1 ≤ Q/ω) (he : M*e ≤ 1) :
    A-(Real.pi^2/4)*(K+3) ≤ M*(1-(Real.pi^2/4)*(1-Q/(ω*M)+e)) := by
  have hid : M*(1-Q/(ω*M)+e) = M-Q/ω+M*e := by field_simp
  have hdef : M*(1-Q/(ω*M)+e) ≤ K+3 := by rw [hid]; linarith
  have hp := mul_le_mul_of_nonneg_left hdef (show 0 ≤ Real.pi^2/4 by positivity)
  nlinarith

end TaoAdditive1132
end
end SourceErdos1132_Additive_PeakArithmetic

/- Erdos1132.Additive.InterpolantPeak -/
section SourceErdos1132_Additive_InterpolantPeak
/- # A large interpolation derivative forces a nearby high Lebesgue value

Main paper: §4, local potential and differentiation estimates.
-/

noncomputable section
open Real Complex Set Filter
open scoped Topology
namespace TaoAdditive1132

theorem eventually_interpolant_peak (X : ∀ n, Nodes n)
    {l r d a b : ℝ} (hlr : l < r) (hI : Icc l r ⊆ Icc (-1) 1) (hd : 0 < d) (ha : 0 < a)
    (hupper : ∀ᶠ n : ℕ in atTop, ∀ y ∈ Icc l r, (X n).lebesgue y ≤ logarithmicLevel a b n)
    (D : ℝ) :
    ∃ K > 0, ∀ᶠ n : ℕ in atTop, ∀ x ∈ Icc (l+2*d) (r-2*d), ∀ v : Fin n → ℝ,
      (∀ i, |v i| ≤ 1) →
      a*Real.log n-D ≤ |((X n).interpolant v).derivative.eval x|/
        (Real.pi*n*(X n).exteriorDensity l r (X n).potentialNormalization x 0) →
      ∃ y ∈ Icc (l+d) (r-d), |y-x| ≤ K/n ∧ a*Real.log n-K ≤ (X n).lebesgue y := by
  have hlevels := eventually_logarithmicLevel_bounds ha b
  have hXn : ∀ᶠ n : ℕ in atTop, ∀ y ∈ Icc l r, (X n).lebesgue y ≤ n := by
    filter_upwards [hupper, hlevels] with n hu hl y hy
    exact (hu y hy).trans hl.2.2
  obtain ⟨c, hc, hdensity⟩ := eventually_exterior_density_positive X hlr hI
    (by linarith : 0 < 2*d) hXn
  let K : ℝ := |b|+(Real.pi^2/4)*(|b+D|+3)+1/c+1
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  have hratio : Tendsto (fun n : ℕ => logarithmicLevel a b n/(c*eighthRoot n)) atTop (𝓝 0) := by
    have ht := (tendsto_log_affine_div_eighthRoot a b).div_const c
    simp only [zero_div] at ht
    convert ht using 1
    funext n
    dsimp [logarithmicLevel]
    ring
  have hrem := (tendsto_level_exp_loss_div_root_sq hlr a b).const_mul 32
  simp only [mul_zero] at hrem
  have hmove : Tendsto (fun n : ℕ => (1/c)/(n : ℝ)) atTop (𝓝 0) :=
    tendsto_natCast_atTop_atTop.const_div_atTop (1/c)
  filter_upwards [hupper, hlevels, hXn, hdensity, eventually_interpolant_local_growth hlr hI hd,
    eventually_riesz_radius (l := l) (r := r) hc,
    hratio.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    (tendsto_level_mul_exp_loss_sub_one hlr a b).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hrem.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)), hmove.eventually (gt_mem_nhds hd)]
    with n hu hl hn hdens hgrow hrad hratio hsmall hrem hmove
  intro x hx v hv hderiv
  let ρ := (X n).exteriorDensity l r (X n).potentialNormalization x 0
  let A := logarithmicLevel a b n
  let E := Real.exp (localRectangleLoss l r n)
  let M := A*E
  let t := eighthRoot (n : ℝ)
  let ω := localFrequency (X n) l r x
  let Q := |((X n).interpolant v).derivative.eval x|
  have hρ : c ≤ ρ := hdens x hx
  have hρ0 : 0 < ρ := hc.trans_le hρ
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hl.1
  have ht : 0 < t := eighthRoot_pos hnR
  have hA : 0 < A := zero_lt_one.trans_le hl.2.1
  have hE : 0 < E := Real.exp_pos _
  have hM : 0 < M := mul_pos hA hE
  obtain ⟨hm, hω, hr, hh, herr⟩ := hrad (X n) x hρ
  have hg := hgrow (X n) hn A hl.2.1 hu x hx hρ0.le v hv
  have hq : A-|b+D| ≤ Q/(Real.pi*n*ρ) := by
    dsimp [A, Q, ρ, logarithmicLevel]
    linarith [le_abs_self (b+D)]
  have hscale := frequency_ratio_lower hc hρ ht hA.le (abs_nonneg (b+D)) hq
  have hscaleid : Q/(Real.pi*n*ρ)*(ρ/(ρ+1/t)) = Q/ω := by
    have hden : ρ+1/t ≠ 0 := by positivity
    dsimp [ω, localFrequency]
    change Q/(Real.pi*n*ρ)*(ρ/(ρ+1/t)) = Q/(Real.pi*n*(ρ+1/t))
    field_simp
  rw [hscaleid] at hscale
  have hQ : A-|b+D|-1 ≤ Q/ω := by
    change A/(c*t) < 1 at hratio
    linarith
  have hMA : A ≤ M := by
    have he := Real.one_le_exp_iff.mpr (localRectangleLoss_nonneg hlr n)
    have hh := mul_le_mul_of_nonneg_left he hA.le
    simpa only [mul_one] using hh
  have hM1 : M ≤ A+1 := by
    change A*(E-1) < 1 at hsmall
    dsimp [M]
    nlinarith
  have heM : M*(16/((localRieszIndex n : ℝ)*Real.pi)) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left herr hM.le
    change 32*(A*E/t^2) < 1 at hrem
    calc
      _ ≤ M*(32/t^2) := hh
      _ = 32*(A*E/t^2) := by dsimp [M]; ring
      _ ≤ 1 := hrem.le
  have hp := polynomial_local_peak_abs hm hω hM hr hh hg
    (δ := 1-Q/(ω*M)) (by change 1-(1-Q/(ω*M)) ≤ Q/(ω*M); linarith)
  have hpeak := (peak_deficit_bound hM hω hMA hM1 hQ heM).trans hp
  let y := x+Real.pi/(2*ω)
  have hωlow : Real.pi*c*n ≤ ω := by
    have ht' := mul_le_mul_of_nonneg_left
      (show c ≤ ρ+1/t by linarith [one_div_pos.mpr ht])
      (show 0 ≤ Real.pi*(n : ℝ) by positivity)
    dsimp [ω, localFrequency]
    nlinarith
  have hshift0 : 0 ≤ Real.pi/(2*ω) := by positivity
  have hshift : Real.pi/(2*ω) ≤ (1/c)/(n : ℝ) := by
    have hid : (1/c)/(n : ℝ) = 1/(c*n) := by ring
    rw [hid]
    apply (div_le_div_iff₀ (by positivity : 0 < 2*ω) (mul_pos hc hnR)).mpr
    nlinarith
  have hy : y ∈ Icc (l+d) (r-d) := by
    dsimp [y]
    constructor <;> linarith [hx.1, hx.2]
  refine ⟨y, hy, ?_, ?_⟩
  · have he : |y-x| = Real.pi/(2*ω) := by dsimp [y]; rw [add_sub_cancel_left, abs_of_nonneg hshift0]
    rw [he]
    apply hshift.trans
    apply div_le_div_of_nonneg_right _ hnR.le
    dsimp [K]
    have hb : 0 ≤ (Real.pi^2/4)*(|b+D|+3) := by positivity
    linarith [abs_nonneg b]
  · have hh := (X n).interpolant_eval_le v hv y
    have hle : a*Real.log n-K ≤ A-(Real.pi^2/4)*(|b+D|+3) := by
      dsimp [A, K, logarithmicLevel]
      linarith [neg_le_abs b, one_div_pos.mpr hc]
    exact hle.trans (hpeak.trans hh)

end TaoAdditive1132
end
end SourceErdos1132_Additive_InterpolantPeak

/- Erdos1132.Additive.IsolatedPeaks -/
section SourceErdos1132_Additive_IsolatedPeaks
/- # Large-jump nodes yield nearby high values and one-sided separation

Main paper: §6, recurrence and Theorem 1(i).
-/

noncomputable section
open Set Filter Polynomial Real
open scoped Topology
namespace TaoAdditive1132

theorem eventually_isolated_peaks (X : ∀ n, Nodes n)
    {l r d c : ℝ} (hlr : l < r) (hI : Icc l r ⊆ Icc (-1) 1) (hd : 0 < d)
    (hupper : ∀ᶠ n : ℕ in atTop, ∀ y ∈ Icc l r,
      (X n).lebesgue y ≤ logarithmicLevel (2/Real.pi) c n) (D : ℝ) :
    ∃ s > 0, ∃ K > 0, ∀ᶠ n : ℕ in atTop,
      ∀ k : Fin n, (X n).point k ∈ Icc (l+4*d) (r-4*d) →
        (2/Real.pi)*Real.log n-D ≤ (X n).normalizedJump l r k →
        (X n).OneSidedIsolated k (s/(n:ℝ)) ∧
        ∃ y ∈ Icc (l+d) (r-d), |y-(X n).point k| ≤ K/n ∧
          (2/Real.pi)*Real.log n-K ≤ (X n).lebesgue y := by
  have hc0 : 0 < 2/Real.pi := by positivity
  have hlevels := eventually_logarithmicLevel_bounds hc0 c
  have hΛ : ∀ᶠ n : ℕ in atTop, ∀ y ∈ Icc l r, (X n).lebesgue y ≤ n := by
    filter_upwards [hupper, hlevels] with n hu hl y hy
    exact (hu y hy).trans hl.2.2
  obtain ⟨c₀, hc₀, hpos⟩ := eventually_exterior_density_positive X hlr hI (by linarith : 0 < 4*d) hΛ
  obtain ⟨B, hB, hsecond⟩ := eventually_interpolant_second_derivative X hlr hI hd hc0 hupper
  obtain ⟨K, hK, hpeak⟩ := eventually_interpolant_peak X hlr hI hd hc0 hupper D
  let s := min d (c₀/(B+1))
  have hs : 0 < s := lt_min hd (by positivity)
  have hsB : B*s ≤ c₀ := by
    have hh := min_le_right d (c₀/(B+1))
    have hh' := (le_div_iff₀ (by positivity : 0 < B+1)).mp hh
    change s*(B+1) ≤ c₀ at hh'
    nlinarith
  have hlog : ∀ᶠ n : ℕ in atTop, max 1 (Real.pi*D) ≤ Real.log (n:ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop _)
  refine ⟨s, hs, K, hK, ?_⟩
  filter_upwards [hlevels, hpos, hsecond, hpeak, hlog] with n hnl hnp hns hnk hln
  have hn := hnl.1
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hlog1 : 1 ≤ Real.log (n:ℝ) := (le_max_left _ _).trans hln
  have hlog0 : 0 < Real.log (n:ℝ) := by linarith
  intro k hk hlarge
  let x := (X n).point k
  let ρ := (X n).exteriorDensity l r (X n).potentialNormalization x 0
  have hρc : c₀ ≤ ρ := hnp _ hk
  have hρ : 0 < ρ := hc₀.trans_le hρc
  have hx2 : x ∈ Icc (l+2*d) (r-2*d) := ⟨by linarith [hk.1], by linarith [hk.2]⟩
  have hδ : 0 < s/(n:ℝ) := by positivity
  have hδd : s/(n:ℝ) ≤ d := (div_le_self hs.le hn1).trans (min_le_left _ _)
  have hmargin : Icc (x-s/(n:ℝ)) (x+s/(n:ℝ)) ⊆ Icc (l+2*d) (r-2*d) := by
    intro y hy
    exact ⟨by linarith [hy.1, hk.1], by linarith [hy.2, hk.2]⟩
  have hBd : (B*(n:ℝ)^2*Real.log n)*(s/(n:ℝ)) ≤ c₀*(n:ℝ)*Real.log n := by
    have hh := mul_le_mul_of_nonneg_right hsB (by positivity : 0 ≤ (n:ℝ)*Real.log n)
    convert! hh using 1 <;> field_simp <;> ring
  have hlarge' : ((2/Real.pi)*Real.log n-D)*(2*Real.pi*(n:ℝ)*ρ) ≤ (X n).derivativeJump k :=
    (le_div_iff₀ (by positivity : 0 < 2*Real.pi*(n:ℝ)*ρ)).mp hlarge
  have hDlog : D ≤ Real.log n/Real.pi := by
    apply (le_div_iff₀ Real.pi_pos).mpr
    simpa only [mul_comm D] using (le_max_right 1 (Real.pi*D)).trans hln
  have hmain : (Real.log n/Real.pi)*(2*Real.pi*(n:ℝ)*ρ) ≤ (X n).derivativeJump k := by
    have hh : Real.log n/Real.pi ≤ (2/Real.pi)*Real.log n-D := by
      have he : (2/Real.pi)*Real.log n = 2*(Real.log n/Real.pi) := by ring
      rw [he]; linarith
    exact (mul_le_mul_of_nonneg_right hh (by positivity)).trans hlarge'
  have hmain' : 2*ρ*(n:ℝ)*Real.log n ≤ (X n).derivativeJump k := by
    convert! hmain using 1 <;> field_simp <;> ring
  have hjump : 2*(c₀*(n:ℝ)*Real.log n) ≤ (X n).derivativeJump k := by
    have hh := mul_le_mul_of_nonneg_right hρc (by positivity : 0 ≤ 2*(n:ℝ)*Real.log n)
    nlinarith
  constructor
  · exact (X n).oneSidedIsolated_of_large_jump k (by positivity) hδ hmargin hBd hjump
      (fun v hv t ht => hns t ht v hv)
  · obtain ⟨v, hv, he⟩ := (X n).exists_interpolant_jump k
    apply hnk x hx2 v hv
    have hident : |((X n).interpolant v).derivative.eval x|/(Real.pi*(n:ℝ)*ρ) =
        (X n).normalizedJump l r k := by
      rw [he, abs_of_nonneg (div_nonneg ((X n).derivativeJump_nonneg k) (by norm_num))]
      dsimp [Nodes.normalizedJump, ρ, x]
      ring
    rw [hident]
    exact hlarge

end TaoAdditive1132
end
end SourceErdos1132_Additive_IsolatedPeaks

/- Erdos1132.Additive.FiniteOverlap -/
section SourceErdos1132_Additive_FiniteOverlap
/- # Lower bounds for a finite union with bounded multiplicity

Main paper: §6, recurrence and Theorem 1(i).
-/

noncomputable section
open MeasureTheory Set Finset
open scoped BigOperators
namespace TaoAdditive1132

theorem eventCount_eq_card {α ι : Type*} (s : Finset ι) (A : ι → Set α) (x : α)
    [DecidablePred (fun i => x ∈ A i)] :
    eventCount s A x = ((s.filter (fun i => x ∈ A i)).card : ℝ) := by
  classical
  simp only [eventCount, Set.indicator_apply, Finset.card_filter]
  push_cast
  rfl

theorem finite_union_lower_of_multiplicity {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (s : Finset ι) (A : ι → Set α)
    (hA : ∀ i ∈ s, MeasurableSet (A i)) {B : ℝ}
    (hB : ∀ x, eventCount s A x ≤ B) :
    (∑ i ∈ s, μ.real (A i)) ≤ B*μ.real (⋃ i ∈ s, A i) := by
  let U := ⋃ i ∈ s, A i
  have hu : MeasurableSet U := s.measurableSet_biUnion hA
  have hz (x : α) (hx : x ∉ U) : eventCount s A x = 0 := by
    apply sum_eq_zero
    intro i hi
    have hxi : x ∉ A i := fun h => hx (mem_iUnion₂.mpr ⟨i, hi, h⟩)
    simp [hxi]
  have hh : (∫ x in U, eventCount s A x ∂μ) ≤ ∫ _x in U, B ∂μ :=
    integral_mono (integrable_eventCount μ s A hA).integrableOn (integrable_const _) hB
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hz, integral_eventCount μ s A hA] at hh
  simpa only [integral_const, Measure.real, Measure.restrict_apply_univ, smul_eq_mul, mul_comm B] using hh

end TaoAdditive1132
end
end SourceErdos1132_Additive_FiniteOverlap

/- Erdos1132.Additive.CenteredCover -/
section SourceErdos1132_Additive_CenteredCover
/- # Measures of unions of short intervals around displaced isolated nodes

Main paper: §6, recurrence and Theorem 1(i).
-/

noncomputable section
open Set Finset MeasureTheory
open scoped BigOperators
namespace TaoAdditive1132

def centeredCover {ι : Type*} (s : Finset ι) (y : ι → ℝ) (r : ℝ) : Set ℝ :=
  ⋃ i ∈ s, Icc (y i-r) (y i+r)

theorem isCompact_centeredCover {ι : Type*} (s : Finset ι) (y : ι → ℝ) (r : ℝ) :
    IsCompact (centeredCover s y r) := s.isCompact_biUnion (fun i hi => isCompact_Icc)

theorem measurableSet_centeredCover {ι : Type*} (s : Finset ι) (y : ι → ℝ) (r : ℝ) :
    MeasurableSet (centeredCover s y r) := (isCompact_centeredCover s y r).measurableSet

theorem measure_centeredCover_le {ι : Type*} (s : Finset ι) (y : ι → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (centeredCover s y r) ≤ 2*r*(s.card:ℝ) := by
  have hh := measureReal_biUnion_finset_le (μ := volume) s (fun i => Icc (y i-r) (y i+r))
  have hm (i : ι) : volume.real (Icc (y i-r) (y i+r)) = 2*r := by
    rw [Real.volume_real_Icc, max_eq_left (by linarith)]
    ring
  simp_rw [hm] at hh
  simpa only [sum_const, nsmul_eq_mul, mul_comm (2*r)] using! hh

theorem measure_centeredCover_lower {ι : Type*} (s : Finset ι) (y : ι → ℝ) {r B : ℝ}
    (hr : 0 ≤ r)
    (hcount : ∀ x, ((s.filter (fun i => x ∈ Icc (y i-r) (y i+r))).card:ℝ) ≤ B) :
    2*r*(s.card:ℝ) ≤ B*volume.real (centeredCover s y r) := by
  classical
  let U := centeredCover s y r
  have hu := measurableSet_centeredCover s y r
  let μ := volume.restrict U
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr (isCompact_centeredCover s y r).measure_ne_top
  have hh := finite_union_lower_of_multiplicity μ s (fun i => Icc (y i-r) (y i+r))
    (fun i hi => measurableSet_Icc) (fun x => by rw [eventCount_eq_card]; exact hcount x)
  have hm (i : ι) (hi : i ∈ s) : μ.real (Icc (y i-r) (y i+r)) = 2*r := by
    have hsub : Icc (y i-r) (y i+r) ⊆ U := fun x hx => mem_iUnion₂.mpr ⟨i, hi, hx⟩
    dsimp only [μ]
    rw [measureReal_restrict_apply measurableSet_Icc, inter_eq_left.mpr hsub,
      Real.volume_real_Icc, max_eq_left (by linarith)]
    ring
  have hsum : (∑ i ∈ s, μ.real (Icc (y i-r) (y i+r))) = 2*r*(s.card:ℝ) := by
    rw [sum_congr rfl hm]
    simp only [sum_const, nsmul_eq_mul]
    ring
  rw [hsum] at hh
  change _ ≤ B*(volume.restrict U).real U at hh
  simpa only [measureReal_restrict_apply_self] using hh

namespace Nodes
variable {n : ℕ} (X : Nodes n)

theorem displaced_isolated_card_bound (s : Finset (Fin n)) (y : Fin n → ℝ)
    {a b δ h : ℝ} (hab : a ≤ b) (hδ : 0 < δ) (hh : 0 ≤ h)
    (hiso : ∀ i ∈ s, X.OneSidedIsolated i δ) (hmove : ∀ i ∈ s, |y i-X.point i| ≤ h) :
    δ*((s.filter (fun i => y i ∈ Icc a b)).card:ℝ) ≤ 2*(b-a)+4*h+2*δ := by
  classical
  have hp := X.isolated_interval_card_bound (s.filter (fun i => y i ∈ Icc a b))
    (by linarith : a-h ≤ b+h) hδ
    (fun i hi => by
      have hm := abs_le.mp (hmove i (mem_filter.mp hi).1)
      have hy := (mem_filter.mp hi).2
      exact ⟨by linarith [hy.1], by linarith [hy.2]⟩)
    (fun i hi => hiso i (mem_filter.mp hi).1)
  convert! hp using 1 <;> ring

theorem displaced_cover_multiplicity (s : Finset (Fin n)) (y : Fin n → ℝ)
    {δ h r : ℝ} (hδ : 0 < δ) (hh : 0 ≤ h) (hr : 0 ≤ r)
    (hiso : ∀ i ∈ s, X.OneSidedIsolated i δ) (hmove : ∀ i ∈ s, |y i-X.point i| ≤ h)
    (x : ℝ) :
    ((s.filter (fun i => x ∈ Icc (y i-r) (y i+r))).card:ℝ) ≤ (4*r+4*h+2*δ)/δ := by
  classical
  have he : s.filter (fun i => x ∈ Icc (y i-r) (y i+r)) =
      s.filter (fun i => y i ∈ Icc (x-r) (x+r)) := by
    ext i
    simp only [mem_filter, Set.mem_Icc]
    constructor <;> rintro ⟨hi, h1, h2⟩ <;> exact ⟨hi, by linarith, by linarith⟩
  rw [he]
  have hp := X.displaced_isolated_card_bound s y (by linarith : x-r ≤ x+r) hδ hh hiso hmove
  apply (le_div_iff₀ hδ).mpr
  nlinarith

theorem displaced_cover_intersection_bound (s : Finset (Fin n)) (y : Fin n → ℝ)
    {δ h r a b : ℝ} (hδ : 0 < δ) (hh : 0 ≤ h) (hr : 0 ≤ r) (hab : a ≤ b)
    (hiso : ∀ i ∈ s, X.OneSidedIsolated i δ) (hmove : ∀ i ∈ s, |y i-X.point i| ≤ h) :
    volume.real (centeredCover s y r ∩ Icc a b) ≤
      (2*r/δ)*(2*(b-a)+4*r+4*h+2*δ) := by
  classical
  let T := s.filter (fun i => y i ∈ Icc (a-r) (b+r))
  have hsub : centeredCover s y r ∩ Icc a b ⊆ centeredCover T y r := by
    intro x hx
    obtain ⟨i, hi, hix⟩ := mem_iUnion₂.mp hx.1
    refine mem_iUnion₂.mpr ⟨i, mem_filter.mpr ⟨hi, ?_⟩, hix⟩
    exact ⟨by linarith [hx.2.1, hix.2], by linarith [hx.2.2, hix.1]⟩
  have hm := (measureReal_mono (μ := volume) hsub (isCompact_centeredCover T y r).measure_ne_top).trans
    (measure_centeredCover_le T y hr)
  have hc := X.displaced_isolated_card_bound s y (by linarith : a-r ≤ b+r) hδ hh hiso hmove
  have hc' : (T.card:ℝ) ≤ (2*(b-a)+4*r+4*h+2*δ)/δ := by
    apply (le_div_iff₀ hδ).mpr
    change δ*(T.card:ℝ) ≤ _ at hc
    nlinarith
  exact hm.trans ((mul_le_mul_of_nonneg_left hc' (by positivity)).trans_eq (by ring))

end Nodes
end TaoAdditive1132
end
end SourceErdos1132_Additive_CenteredCover

/- Erdos1132.Additive.ScaledCover -/
section SourceErdos1132_Additive_ScaledCover
/- # Measure bounds at the high-value interval scale

Main paper: §6, recurrence and Theorem 1(i).
-/

noncomputable section
open Set Finset MeasureTheory Real
open scoped BigOperators
namespace TaoAdditive1132

def coverMultiplicity (d K β : ℝ) : ℝ := (4*β+4*K+2*d)/d

theorem coverMultiplicity_pos {d K β : ℝ} (hd : 0 < d) (hK : 0 ≤ K) (hβ : 0 < β) :
    0 < coverMultiplicity d K β := by unfold coverMultiplicity; positivity

namespace Nodes
variable {n : ℕ} (X : Nodes n)

theorem scaled_cover_bounds (s : Finset (Fin n)) (y : Fin n → ℝ)
    {d K β κ : ℝ} (hn : 0 < n) (hln : 1 ≤ Real.log (n:ℝ))
    (hd : 0 < d) (hK : 0 ≤ K) (hβ : 0 < β) (hκ : 0 < κ)
    (hcard : κ*(n:ℝ) ≤ (s.card:ℝ))
    (hiso : ∀ i ∈ s, X.OneSidedIsolated i (d/(n:ℝ)))
    (hmove : ∀ i ∈ s, |y i-X.point i| ≤ K/(n:ℝ)) :
    let A := centeredCover s y (β/((n:ℝ)*Real.log n))
    volume.real A ≤ 2*β/Real.log n ∧
    (2*β*κ/coverMultiplicity d K β)/Real.log n ≤ volume.real A ∧
    ∀ a b : ℝ, a ≤ b → volume.real (A ∩ Icc a b) ≤
      (4*β/d+2*β*coverMultiplicity d K β+1)*
        ((b-a)/Real.log n+1/((n:ℝ)*Real.log n)) := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hl : 0 < Real.log (n:ℝ) := by linarith
  let r := β/((n:ℝ)*Real.log n)
  let B := coverMultiplicity d K β
  have hr : 0 < r := by dsimp [r]; positivity
  have hB : 0 < B := coverMultiplicity_pos hd hK hβ
  have hsmall : r ≤ β/(n:ℝ) := by
    dsimp [r]
    exact div_le_div_of_nonneg_left hβ.le hnR (by nlinarith)
  have hmultiplicity : (4*r+4*(K/(n:ℝ))+2*(d/(n:ℝ)))/(d/(n:ℝ)) ≤ B := by
    apply (div_le_iff₀ (by positivity : 0 < d/(n:ℝ))).mpr
    have he : B*(d/(n:ℝ)) = (4*β+4*K+2*d)/(n:ℝ) := by dsimp [B, coverMultiplicity]; field_simp
    rw [he]
    have he' : (4*β+4*K+2*d)/(n:ℝ) = 4*(β/(n:ℝ))+4*(K/(n:ℝ))+2*(d/(n:ℝ)) := by ring
    rw [he']; linarith
  have hcount (x : ℝ) : ((s.filter (fun i => x ∈ Icc (y i-r) (y i+r))).card:ℝ) ≤ B :=
    (X.displaced_cover_multiplicity s y (by positivity) (by positivity) hr.le hiso hmove x).trans hmultiplicity
  have hupper := measure_centeredCover_le s y hr.le
  have hsn : (s.card:ℝ) ≤ n := by
    exact_mod_cast (show s.card ≤ n by simpa using Finset.card_le_univ (s := s))
  have hlow := measure_centeredCover_lower s y hr.le hcount
  constructor
  · have hh := mul_le_mul_of_nonneg_left hsn (by positivity : 0 ≤ 2*r)
    have he : 2*r*(n:ℝ) = 2*β/Real.log n := by dsimp [r]; field_simp
    exact hupper.trans (hh.trans_eq he)
  constructor
  · have hh := mul_le_mul_of_nonneg_left hcard (by positivity : 0 ≤ 2*r)
    have he : 2*r*(κ*(n:ℝ)) = (2*β*κ/Real.log n) := by dsimp [r]; field_simp
    rw [he] at hh
    have h := (div_le_iff₀ hB).mpr (show (2*β*κ/Real.log n) ≤
      volume.real (centeredCover s y r)*B by nlinarith)
    convert! h using 1 <;> ring
  · intro a b hab
    have hh := X.displaced_cover_intersection_bound s y (by positivity) (by positivity) hr.le hab hiso hmove
    have he : 2*r/(d/(n:ℝ)) = 2*β/(d*Real.log n) := by dsimp [r]; field_simp
    rw [he] at hh
    have hsmall' : 2*(b-a)+4*r+4*(K/(n:ℝ))+2*(d/(n:ℝ)) ≤
        2*(b-a)+(4*β+4*K+2*d)/(n:ℝ) := by
      have he' : (4*β+4*K+2*d)/(n:ℝ) = 4*(β/(n:ℝ))+4*(K/(n:ℝ))+2*(d/(n:ℝ)) := by ring
      rw [he']; linarith
    have hh' := hh.trans (mul_le_mul_of_nonneg_left hsmall' (by positivity))
    have he' : (2*β/(d*Real.log n))*(2*(b-a)+(4*β+4*K+2*d)/(n:ℝ)) =
        (4*β/d)*((b-a)/Real.log n)+(2*β*B)*(1/((n:ℝ)*Real.log n)) := by
      dsimp [B, coverMultiplicity]
      ring
    rw [he'] at hh'
    have h1 : 0 ≤ (b-a)/Real.log n := div_nonneg (sub_nonneg.mpr hab) hl.le
    have h2 : 0 ≤ 1/((n:ℝ)*Real.log n) := by positivity
    have h3 : 0 ≤ 4*β/d := by positivity
    have h4 : 0 ≤ 2*β*B := by positivity
    have hleft := mul_le_mul_of_nonneg_right (by linarith : 4*β/d ≤ 4*β/d+2*β*B+1) h1
    have hright := mul_le_mul_of_nonneg_right (by linarith : 2*β*B ≤ 4*β/d+2*β*B+1) h2
    dsimp only [B] at *
    nlinarith

end Nodes
end TaoAdditive1132
end
end SourceErdos1132_Additive_ScaledCover

/- Erdos1132.Additive.CoverIntersection -/
section SourceErdos1132_Additive_CoverIntersection
/- # Intersections of high-value interval unions in two different rows

Main paper: §6, recurrence and Theorem 1(i).
-/

noncomputable section
open MeasureTheory Set Finset Real
open scoped BigOperators
namespace TaoAdditive1132

theorem centeredCover_intersection_from_local_bound {ι : Type*}
    (s : Finset ι) (y : ι → ℝ) {r C L m : ℝ} (hr : 0 ≤ r) (T : Set ℝ)
    (hlocal : ∀ a b : ℝ, a ≤ b → volume.real (T ∩ Icc a b) ≤ C*((b-a)/L+1/(m*L))) :
    volume.real (centeredCover s y r ∩ T) ≤
      C*((2*r*(s.card:ℝ))/L+(s.card:ℝ)/(m*L)) := by
  have he : centeredCover s y r ∩ T = ⋃ i ∈ s, T ∩ Icc (y i-r) (y i+r) := by
    ext x
    simp only [centeredCover, Set.mem_inter_iff, mem_iUnion, exists_prop]
    constructor
    · rintro ⟨⟨i, hi, hx⟩, ht⟩
      exact ⟨i, hi, ht, hx⟩
    · rintro ⟨i, hi, ht, hx⟩
      exact ⟨⟨i, hi, hx⟩, ht⟩
  rw [he]
  have h1 := measureReal_biUnion_finset_le (μ := volume) s (fun i => T ∩ Icc (y i-r) (y i+r))
  have h2 := sum_le_sum (s := s) (fun i hi => hlocal (y i-r) (y i+r) (by linarith))
  have heq : (∑ i ∈ s, C*(((y i+r)-(y i-r))/L+1/(m*L))) =
      C*((2*r*(s.card:ℝ))/L+(s.card:ℝ)/(m*L)) := by
    simp_rw [show ∀ i : ι, (y i+r)-(y i-r) = 2*r by intro i; ring]
    simp only [sum_const, nsmul_eq_mul]
    ring
  exact h1.trans (h2.trans_eq heq)

theorem scaled_cover_intersection {n m : ℕ} (s : Finset (Fin n)) (y : Fin n → ℝ)
    {β C : ℝ} (hβ : 0 ≤ β) (hC : 0 ≤ C) (hn : 0 < n) (hm : 0 < m)
    (hln : 0 < Real.log (n:ℝ)) (hlm : 0 < Real.log (m:ℝ)) (T : Set ℝ)
    (hlocal : ∀ a b : ℝ, a ≤ b → volume.real (T ∩ Icc a b) ≤
      C*((b-a)/Real.log m+1/((m:ℝ)*Real.log m))) :
    volume.real (centeredCover s y (β/((n:ℝ)*Real.log n)) ∩ T) ≤
      C*(2*β/(Real.log n*Real.log m)+(n:ℝ)/((m:ℝ)*Real.log m)) := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hmR : 0 < (m:ℝ) := by exact_mod_cast hm
  have hsn : (s.card:ℝ) ≤ n := by
    exact_mod_cast (show s.card ≤ n by simpa using Finset.card_le_univ (s := s))
  have hh := centeredCover_intersection_from_local_bound s y
    (r := β/((n:ℝ)*Real.log n)) (by positivity) T hlocal
  have h1 := mul_le_mul_of_nonneg_left hsn (by positivity : 0 ≤ 2*(β/((n:ℝ)*Real.log n)))
  have h2 := div_le_div_of_nonneg_right h1 hlm.le
  have h3 := div_le_div_of_nonneg_right hsn (by positivity : 0 ≤ (m:ℝ)*Real.log m)
  have h4 := mul_le_mul_of_nonneg_left (add_le_add h2 h3) hC
  have he : C*((2*(β/((n:ℝ)*Real.log n))*(n:ℝ))/Real.log m+(n:ℝ)/((m:ℝ)*Real.log m)) =
      C*(2*β/(Real.log n*Real.log m)+(n:ℝ)/((m:ℝ)*Real.log m)) := by field_simp
  exact hh.trans (h4.trans_eq he)

end TaoAdditive1132
end
end SourceErdos1132_Additive_CoverIntersection

/- Erdos1132.Additive.HighCovers -/
section SourceErdos1132_Additive_HighCovers
/- # Actual high-value sets with uniform measure and intersection bounds

Main paper: §6, recurrence and Theorem 1(i).
-/

noncomputable section
open MeasureTheory Set Finset Filter Real
open scoped Topology BigOperators
namespace TaoAdditive1132

theorem exists_high_covers (X : ∀ n, Nodes n) {a b c : ℝ}
    (hab : a < b) (hI : Icc a b ⊆ Icc (-1) 1)
    (hupper : ∀ᶠ n : ℕ in atTop, ∀ x ∈ Icc a b,
      (X n).lebesgue x ≤ logarithmicLevel (2/Real.pi) c n) :
    ∃ A : ℕ → Set ℝ, ∃ D > 0, ∃ c₁ > 0, ∃ C > 0, ∃ N : ℕ,
      (∀ n, MeasurableSet (A n)) ∧
      (∀ n ≥ N, 0 < n ∧ 1 ≤ Real.log (n:ℝ) ∧ A n ⊆ Icc a b ∧
        (∀ x ∈ A n, (2/Real.pi)*Real.log n-D ≤ (X n).lebesgue x) ∧
        c₁/Real.log n ≤ volume.real (A n) ∧ volume.real (A n) ≤ C/Real.log n) ∧
      (∀ n m : ℕ, N ≤ n → N ≤ m → n < m → volume.real (A n ∩ A m) ≤
        C*(1/(Real.log n*Real.log m)+(n:ℝ)/((m:ℝ)*Real.log m))) := by
  classical
  let d := (b-a)/16
  have hd : 0 < d := by dsimp [d]; linarith
  let l := a+4*d
  let r := b-4*d
  have hlr : l < r := by dsimp [l, r, d]; linarith
  let f := intervalWeight l r
  have hf := integrable_intervalWeight l r
  have hfm := (continuous_intervalWeight l r).measurable
  have hfl (x y : ℝ) : |f x-f y| ≤ 1*|x-y| := by simpa using intervalWeight_lipschitz l r x y
  obtain ⟨D, hD, κ, hκ, hmany⟩ := eventually_many_large_jumps X hab hI
    (by linarith : 0 < 2*d) hlr.le
    (show Icc l r ⊆ Icc (a+2*(2*d)) (b-2*(2*d)) by
      intro x hx; dsimp [l, r] at hx; exact ⟨by linarith [hx.1], by linarith [hx.2]⟩)
    (sub_nonneg.mpr hlr.le) (by norm_num : (0:ℝ) ≤ 1) hf hfm
    (intervalWeight_nonneg l r) (intervalWeight_bound hlr.le) hfl
    (fun x hx => intervalWeight_zero_off hx) (integral_intervalWeight_sq_pos hlr) hupper
  obtain ⟨δ, hδ, K, hK, hpeaks⟩ := eventually_isolated_peaks X hab hI hd hupper D
  obtain ⟨L, hL, hlipschitz⟩ := eventually_lebesgue_lipschitz X hab hI
    (by linarith : 0 < d/4) (by positivity : 0 < 2/Real.pi) hupper
  let β := 1/(L+1)
  have hβ : 0 < β := by dsimp [β]; positivity
  have hβL : L*β ≤ 1 := by
    dsimp [β]; rw [mul_one_div]
    apply (div_le_iff₀ (by positivity : 0 < L+1)).mpr
    linarith
  let S (n : ℕ) := univ.filter (fun i : Fin n => (X n).point i ∈ Icc l r ∧
    (2/Real.pi)*Real.log n-D ≤ (X n).normalizedJump a b i)
  have hlog : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (n:ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  have hsmall : ∀ᶠ n : ℕ in atTop, β/(n:ℝ) ≤ d/2 := by
    have ht : Tendsto (fun n : ℕ => β/(n:ℝ)) atTop (𝓝 0) := tendsto_natCast_atTop_atTop.const_div_atTop β
    exact (ht.eventually (gt_mem_nhds (by positivity : (0:ℝ)<d/2))).mono (fun n hn => hn.le)
  have hall := (eventually_gt_atTop (0:ℕ)).and (hlog.and (hmany.and (hpeaks.and (hlipschitz.and hsmall))))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hall
  have hex (n : ℕ) (i : Fin n) : ∃ y : ℝ, N ≤ n → i ∈ S n →
      y ∈ Icc (a+d) (b-d) ∧ |y-(X n).point i| ≤ K/n ∧
        (2/Real.pi)*Real.log n-K ≤ (X n).lebesgue y := by
    by_cases hn : N ≤ n
    · by_cases hi : i ∈ S n
      · have hh := (mem_filter.mp hi).2
        have hp := (hN n hn).2.2.2.1 i hh.1 hh.2
        obtain ⟨y, hy, hm, hv⟩ := hp.2
        exact ⟨y, fun _ _ => ⟨hy, hm, hv⟩⟩
      · exact ⟨0, fun _ hi' => False.elim (hi hi')⟩
    · exact ⟨0, fun hn' _ => False.elim (hn hn')⟩
  choose y hy using hex
  let A (n : ℕ) := centeredCover (S n) (y n) (β/((n:ℝ)*Real.log n))
  let B := coverMultiplicity δ K β
  let C₀ := 4*β/δ+2*β*B+1
  let C := 2*β+C₀*(2*β+2)+1
  have hB : 0 < B := coverMultiplicity_pos hδ hK.le hβ
  have hC₀ : 0 < C₀ := by dsimp [C₀]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hrow (n : ℕ) (hn : N ≤ n) : A n ⊆ Icc a b ∧
      (∀ x ∈ A n, (2/Real.pi)*Real.log n-(K+1) ≤ (X n).lebesgue x) ∧
      (2*β*κ/B)/Real.log n ≤ volume.real (A n) ∧ volume.real (A n) ≤ 2*β/Real.log n ∧
      (∀ u v : ℝ, u ≤ v → volume.real (A n ∩ Icc u v) ≤ C₀*((v-u)/Real.log n+1/((n:ℝ)*Real.log n))) := by
    obtain ⟨hn0, hln, hcard, hp, hLip, hsmall⟩ := hN n hn
    have hnR : 0 < (n:ℝ) := by exact_mod_cast hn0
    have hl : 0 < Real.log (n:ℝ) := by linarith
    let rad := β/((n:ℝ)*Real.log n)
    have hrad : 0 < rad := by dsimp [rad]; positivity
    have hradd : rad ≤ d/2 :=
      (div_le_div_of_nonneg_left hβ.le hnR (by nlinarith : (n:ℝ) ≤ (n:ℝ)*Real.log n)).trans hsmall
    have hiso (i : Fin n) (hi : i ∈ S n) : (X n).OneSidedIsolated i (δ/(n:ℝ)) :=
      (hp i (mem_filter.mp hi).2.1 (mem_filter.mp hi).2.2).1
    have hmove (i : Fin n) (hi : i ∈ S n) : |y n i-(X n).point i| ≤ K/(n:ℝ) := (hy n i hn hi).2.1
    have hmeasure := (X n).scaled_cover_bounds (S n) (y n) hn0 hln hδ hK.le hβ hκ hcard hiso hmove
    have hpoint (x : ℝ) (hx : x ∈ A n) : x ∈ Icc (a+2*(d/4)) (b-2*(d/4)) ∧
        (2/Real.pi)*Real.log n-(K+1) ≤ (X n).lebesgue x := by
      obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
      have hiy := (hy n i hn hi).1
      have hix : x ∈ Icc (a+2*(d/4)) (b-2*(d/4)) :=
        ⟨by linarith [hxi.1, hiy.1], by linarith [hxi.2, hiy.2]⟩
      have hiy' : y n i ∈ Icc (a+2*(d/4)) (b-2*(d/4)) :=
        ⟨by linarith [hiy.1], by linarith [hiy.2]⟩
      have hdist : |x-y n i| ≤ rad := abs_le.mpr ⟨by linarith [hxi.1], by linarith [hxi.2]⟩
      have hdif := (hLip x hix (y n i) hiy').trans
        (mul_le_mul_of_nonneg_left hdist (by positivity : 0 ≤ L*(n:ℝ)*Real.log n))
      have he : L*(n:ℝ)*Real.log n*rad = L*β := by dsimp [rad]; field_simp
      rw [he] at hdif
      have hv := (hy n i hn hi).2.2
      have hh := (abs_le.mp hdif).1
      exact ⟨hix, by linarith⟩
    refine ⟨?_, fun x hx => (hpoint x hx).2, hmeasure.2.1, hmeasure.1, hmeasure.2.2⟩
    intro x hx
    exact ⟨by linarith [(hpoint x hx).1.1], by linarith [(hpoint x hx).1.2]⟩
  refine ⟨A, K+1, by positivity, 2*β*κ/B, by positivity, C, hC, N,
    fun n => measurableSet_centeredCover _ _ _, ?_, ?_⟩
  · intro n hn
    have hh := hrow n hn
    refine ⟨(hN n hn).1, (hN n hn).2.1, hh.1, hh.2.1, hh.2.2.1, ?_⟩
    exact hh.2.2.2.1.trans (div_le_div_of_nonneg_right (by dsimp [C]; nlinarith)
      (by linarith [(hN n hn).2.1]))
  · intro n m hn hm hnm
    have hn0 := (hN n hn).1
    have hm0 := (hN m hm).1
    have hln : 0 < Real.log (n:ℝ) := by linarith [(hN n hn).2.1]
    have hlm : 0 < Real.log (m:ℝ) := by linarith [(hN m hm).2.1]
    have hmR : 0 < (m:ℝ) := by exact_mod_cast hm0
    have hh := scaled_cover_intersection (S n) (y n) hβ.le hC₀.le hn0 hm0 hln hlm (A m)
      (hrow m hm).2.2.2.2
    have hC1 : C₀*(2*β) ≤ C := by dsimp [C]; nlinarith
    have hC2 : C₀ ≤ C := by dsimp [C]; nlinarith
    have h1 := mul_le_mul_of_nonneg_right hC1 (by positivity : 0 ≤ 1/(Real.log n*Real.log m))
    have h2 := mul_le_mul_of_nonneg_right hC2 (by positivity : 0 ≤ (n:ℝ)/((m:ℝ)*Real.log m))
    have he : C₀*(2*β/(Real.log n*Real.log m)+(n:ℝ)/((m:ℝ)*Real.log m)) =
        C₀*(2*β)*(1/(Real.log n*Real.log m))+C₀*((n:ℝ)/((m:ℝ)*Real.log m)) := by ring
    rw [he] at hh
    exact hh.trans (by nlinarith)

end TaoAdditive1132
end
end SourceErdos1132_Additive_HighCovers

/- Erdos1132.Additive.DyadicRecurrence -/
section SourceErdos1132_Additive_DyadicRecurrence
/- # Recurrence from the dyadic intersection estimates in Section 4

Main paper: §6, recurrence and Theorem 1(i).
-/

noncomputable section
open MeasureTheory Filter Finset
open scoped BigOperators Topology
namespace TaoAdditive1132

def harmonicWeight (j : ℕ) : ℝ := 1 / (j + 1 : ℝ)

def dyadicOverlapError (j k : ℕ) : ℝ :=
  if j < k then (2 : ℝ)^j / ((2 : ℝ)^k * (k + 1 : ℝ)) else 0

theorem harmonicWeight_pos (j : ℕ) : 0 < harmonicWeight j := by
  unfold harmonicWeight
  positivity

theorem sum_two_pow_le (k : ℕ) : (∑ j ∈ range k, (2 : ℝ)^j) ≤ 2^k := by
  induction k with
  | zero => norm_num
  | succ k ih => rw [sum_range_succ, pow_succ]; linarith

theorem sum_dyadicOverlapError_le (s : Finset ℕ) (k : ℕ) :
    (∑ j ∈ s, dyadicOverlapError j k) ≤ harmonicWeight k := by
  unfold dyadicOverlapError harmonicWeight
  rw [← sum_filter, ← sum_div]
  have hsum : (∑ j ∈ s.filter (fun j => j < k), (2 : ℝ)^j) ≤ 2^k := by
    apply le_trans _ (sum_two_pow_le k)
    apply sum_le_sum_of_subset_of_nonneg
    · intro j hj
      exact mem_range.mpr (mem_filter.mp hj).2
    · intro j _ _
      positivity
  calc
    _ ≤ (2 : ℝ)^k / ((2 : ℝ)^k * (k+1 : ℝ)) :=
      div_le_div_of_nonneg_right hsum (by positivity)
    _ = _ := by field_simp

theorem dyadic_second_moment_bound
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (A : ℕ → Set α) {C : ℝ} (hC : 0 ≤ C)
    (hupper : ∀ j, μ.real (A j) ≤ C * harmonicWeight j)
    (hpair : ∀ j k : ℕ, j < k → μ.real (A j ∩ A k) ≤
      C * (harmonicWeight j * harmonicWeight k + dyadicOverlapError j k))
    (s : Finset ℕ) :
    (∑ j ∈ s, ∑ k ∈ s, μ.real (A j ∩ A k)) ≤
      C * ((∑ j ∈ s, harmonicWeight j)^2 + 3 * ∑ j ∈ s, harmonicWeight j) := by
  have hfull (j k : ℕ) : μ.real (A j ∩ A k) ≤ C *
      (harmonicWeight j * harmonicWeight k + dyadicOverlapError j k +
        dyadicOverlapError k j + if j = k then harmonicWeight j else 0) := by
    rcases lt_trichotomy j k with hjk | rfl | hkj
    · have hh := hpair j k hjk
      simpa [dyadicOverlapError, hjk, not_lt_of_ge hjk.le, ne_of_lt hjk] using hh
    · simp only [Set.inter_self, dyadicOverlapError, lt_self_iff_false, ite_false,
        ite_true, add_zero]
      have hw := harmonicWeight_pos j
      nlinarith [hupper j]
    · have hh := hpair k j hkj
      rw [Set.inter_comm] at hh
      simpa [dyadicOverlapError, hkj, not_lt_of_ge hkj.le, ne_of_gt hkj,
        mul_comm, add_comm] using hh
  have hb := sum_le_sum (s := s) fun j _ => sum_le_sum (s := s) fun k _ => hfull j k
  simp only [sum_add_distrib, ← mul_sum] at hb
  have he1 : (∑ j ∈ s, ∑ k ∈ s, dyadicOverlapError j k) ≤
      ∑ j ∈ s, harmonicWeight j := by
    rw [sum_comm]
    exact sum_le_sum (fun k _ => sum_dyadicOverlapError_le s k)
  have he2 : (∑ j ∈ s, ∑ k ∈ s, dyadicOverlapError k j) ≤
      ∑ j ∈ s, harmonicWeight j :=
    sum_le_sum (fun j _ => sum_dyadicOverlapError_le s j)
  have hdiag : (∑ j ∈ s, ∑ k ∈ s, if j = k then harmonicWeight j else 0) =
      ∑ j ∈ s, harmonicWeight j := by
    apply sum_congr rfl
    intro j hj
    simp [hj]
  rw [hdiag] at hb
  have hprod : (∑ j ∈ s, harmonicWeight j * ∑ k ∈ s, harmonicWeight k) =
      (∑ j ∈ s, harmonicWeight j)^2 := by rw [← sum_mul]; ring
  rw [hprod] at hb
  nlinarith

/-- The reciprocal first moments and dyadic overlap bound force positive
measure recurrence, with no independence hypothesis. -/
theorem measure_frequently_pos_of_dyadic_bounds
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (A : ℕ → Set α) (hA : ∀ j, MeasurableSet (A j)) {c C : ℝ}
    (hc : 0 < c) (hC : 0 < C)
    (hlower : ∀ j, c * harmonicWeight j ≤ μ.real (A j))
    (hupper : ∀ j, μ.real (A j) ≤ C * harmonicWeight j)
    (hpair : ∀ j k : ℕ, j < k → μ.real (A j ∩ A k) ≤
      C * (harmonicWeight j * harmonicWeight k + dyadicOverlapError j k)) :
    0 < μ {x | ∃ᶠ j in atTop, x ∈ A j} := by
  apply measure_frequently_pos_of_second_moment μ A hA
    (C := 4*C/c^2) (by positivity)
  intro N
  have hdiverge : Tendsto (fun m => ∑ j ∈ range m, harmonicWeight j) atTop atTop :=
    Real.tendsto_sum_range_one_div_nat_succ_atTop
  obtain ⟨m, hmN, hm⟩ := ((eventually_ge_atTop N).and
    (hdiverge.eventually_ge_atTop (1 + ∑ j ∈ range N, harmonicWeight j))).exists
  let s := Ico N m
  have hH : 1 ≤ ∑ j ∈ s, harmonicWeight j := by
    dsimp [s]
    rw [sum_Ico_eq_sub _ hmN]
    linarith
  have hS : c * (∑ j ∈ s, harmonicWeight j) ≤ ∑ j ∈ s, μ.real (A j) := by
    rw [mul_sum]
    exact sum_le_sum (fun j _ => hlower j)
  have hSpos : 0 < ∑ j ∈ s, μ.real (A j) :=
    (mul_pos hc (zero_lt_one.trans_le hH)).trans_le hS
  refine ⟨s, fun n hn => (mem_Ico.mp hn).1, hSpos, ?_⟩
  have hQ := dyadic_second_moment_bound μ A hC.le hupper hpair s
  have hSsq : (c * (∑ j ∈ s, harmonicWeight j))^2 ≤ (∑ j ∈ s, μ.real (A j))^2 :=
    pow_le_pow_left₀ (by positivity) hS 2
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (sq_pos_of_pos hc)).mpr
  have hc2 := sq_nonneg c
  have hHS : (∑ j ∈ s, harmonicWeight j) ≤ (∑ j ∈ s, harmonicWeight j)^2 := by nlinarith
  have hQ' : (∑ j ∈ s, ∑ k ∈ s, μ.real (A j ∩ A k)) ≤
      4*C*(∑ j ∈ s, harmonicWeight j)^2 := by nlinarith
  have hh := mul_le_mul_of_nonneg_right hQ' hc2
  have hh' := mul_le_mul_of_nonneg_left hSsq (show 0 ≤ 4*C by positivity)
  nlinarith

theorem harmonicWeight_add_le (j N : ℕ) : harmonicWeight (j+N) ≤ harmonicWeight j := by
  unfold harmonicWeight
  apply one_div_le_one_div_of_le (by positivity)
  push_cast
  linarith [Nat.cast_nonneg (α := ℝ) N]

theorem harmonicWeight_le_add_mul (j N : ℕ) :
    harmonicWeight j / (N+1 : ℝ) ≤ harmonicWeight (j+N) := by
  unfold harmonicWeight
  rw [div_div]
  apply one_div_le_one_div_of_le (by positivity)
  push_cast
  nlinarith [Nat.cast_nonneg (α := ℝ) N, Nat.cast_nonneg (α := ℝ) j]

theorem dyadicOverlapError_add_le (j k N : ℕ) :
    dyadicOverlapError (j+N) (k+N) ≤ dyadicOverlapError j k := by
  by_cases hjk : j < k
  · have hjk' : j+N < k+N := Nat.add_lt_add_right hjk N
    unfold dyadicOverlapError
    rw [if_pos hjk, if_pos hjk']
    have heq : (2 : ℝ)^(j+N) / ((2 : ℝ)^(k+N) * (k+N+1 : ℝ)) =
        (2 : ℝ)^j / (2 : ℝ)^k * harmonicWeight (k+N) := by
      unfold harmonicWeight
      rw [pow_add, pow_add]
      push_cast
      field_simp
    push_cast
    rw [heq]
    calc
      _ ≤ (2 : ℝ)^j / (2 : ℝ)^k * harmonicWeight k :=
        mul_le_mul_of_nonneg_left (harmonicWeight_add_le k N) (by positivity)
      _ = _ := by unfold harmonicWeight; field_simp
  · simp [dyadicOverlapError, hjk]

/-- The same recurrence conclusion holds when the dyadic estimates start
only after an arbitrary finite index. -/
theorem measure_frequently_pos_of_eventual_dyadic_bounds
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (A : ℕ → Set α) (hA : ∀ j, MeasurableSet (A j)) {c C : ℝ}
    (hc : 0 < c) (hC : 0 < C) (N : ℕ)
    (hlower : ∀ j ≥ N, c * harmonicWeight j ≤ μ.real (A j))
    (hupper : ∀ j ≥ N, μ.real (A j) ≤ C * harmonicWeight j)
    (hpair : ∀ j k : ℕ, N ≤ j → j < k → μ.real (A j ∩ A k) ≤
      C * (harmonicWeight j * harmonicWeight k + dyadicOverlapError j k)) :
    0 < μ {x | ∃ᶠ j in atTop, x ∈ A j} := by
  have hh := measure_frequently_pos_of_dyadic_bounds μ (fun j => A (j+N))
    (fun j => hA _) (c := c/(N+1)) (C := C) (by positivity) hC
    (fun j => ?_) (fun j => ?_) (fun j k hjk => ?_)
  · apply hh.trans_le
    apply measure_mono
    intro x hx
    exact (tendsto_add_atTop_nat N).frequently hx
  · calc
      _ = c * (harmonicWeight j / (N+1 : ℝ)) := by ring
      _ ≤ c * harmonicWeight (j+N) :=
        mul_le_mul_of_nonneg_left (harmonicWeight_le_add_mul j N) hc.le
      _ ≤ _ := hlower _ (Nat.le_add_left _ _)
  · exact (hupper _ (Nat.le_add_left _ _)).trans
      (mul_le_mul_of_nonneg_left (harmonicWeight_add_le j N) hC.le)
  · apply (hpair _ _ (Nat.le_add_left _ _) (Nat.add_lt_add_right hjk N)).trans
    apply mul_le_mul_of_nonneg_left _ hC.le
    exact add_le_add
      (mul_le_mul (harmonicWeight_add_le j N) (harmonicWeight_add_le k N)
        (harmonicWeight_pos _).le (harmonicWeight_pos _).le)
      (dyadicOverlapError_add_le j k N)

end TaoAdditive1132
end
end SourceErdos1132_Additive_DyadicRecurrence

/- Erdos1132.Additive.LogarithmicRecurrence -/
section SourceErdos1132_Additive_LogarithmicRecurrence
/- # Positive-measure recurrence from logarithmic row estimates

Main paper: §6, recurrence and Theorem 1(i).
-/

noncomputable section
open MeasureTheory Set Filter Real
open scoped Topology
namespace TaoAdditive1132

def dyadicRow (j : ℕ) : ℕ := 2^(j+1)

theorem lt_dyadicRow (j : ℕ) : j < dyadicRow j := by
  induction j with
  | zero => norm_num [dyadicRow]
  | succ j ih =>
    simp only [dyadicRow, pow_succ] at *
    omega

theorem dyadicRow_strictMono : StrictMono dyadicRow := by
  intro j k hjk
  exact Nat.pow_lt_pow_right (by norm_num : 1 < (2:ℕ)) (by omega : j+1 < k+1)

theorem tendsto_dyadicRow : Tendsto dyadicRow atTop atTop :=
  tendsto_atTop_mono (fun j => (lt_dyadicRow j).le) tendsto_id

theorem log_dyadicRow (j : ℕ) : Real.log (dyadicRow j : ℝ) = (j+1:ℝ)*Real.log 2 := by
  simp [dyadicRow, Nat.cast_pow, Real.log_pow]

theorem measure_frequently_pos_of_logarithmic_bounds
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (A : ℕ → Set α) (hA : ∀ n, MeasurableSet (A n)) {c C : ℝ}
    (hc : 0 < c) (hC : 0 < C) (N : ℕ)
    (hlower : ∀ n ≥ N, c/Real.log n ≤ μ.real (A n))
    (hupper : ∀ n ≥ N, μ.real (A n) ≤ C/Real.log n)
    (hpair : ∀ n m : ℕ, N ≤ n → N ≤ m → n < m → μ.real (A n ∩ A m) ≤
      C*(1/(Real.log n*Real.log m)+(n:ℝ)/((m:ℝ)*Real.log m))) :
    0 < μ {x | ∃ᶠ n in atTop, x ∈ A n} := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let C' := C/(Real.log 2)^2+C/Real.log 2+1
  have hC' : 0 < C' := by dsimp [C']; positivity
  have hcoef1 : 0 ≤ C/(Real.log 2)^2 := by positivity
  have hcoef2 : 0 ≤ C/Real.log 2 := by positivity
  have hN (j : ℕ) (hj : N ≤ j) : N ≤ dyadicRow j := hj.trans (lt_dyadicRow j).le
  have hfreq := measure_frequently_pos_of_eventual_dyadic_bounds μ (fun j => A (dyadicRow j))
    (fun j => hA _) (c := c/Real.log 2) (C := C') (by positivity) hC' N
    (fun j hj => ?_) (fun j hj => ?_) (fun j k hj hjk => ?_)
  · apply hfreq.trans_le
    apply measure_mono
    intro x hx
    exact tendsto_dyadicRow.frequently hx
  · have hh := hlower _ (hN j hj)
    rw [log_dyadicRow] at hh
    convert! hh using 1 <;> dsimp [harmonicWeight] <;> field_simp
  · have hh := hupper _ (hN j hj)
    rw [log_dyadicRow] at hh
    have he : C/((j+1:ℝ)*Real.log 2) = (C/Real.log 2)*harmonicWeight j := by
      dsimp [harmonicWeight]; field_simp
    rw [he] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (by dsimp [C']; linarith)
      (harmonicWeight_pos j).le)
  · have hh := hpair _ _ (hN j hj) (hN k (hj.trans hjk.le)) (dyadicRow_strictMono hjk)
    have he : C*(1/(Real.log (dyadicRow j)*Real.log (dyadicRow k))+
        (dyadicRow j:ℝ)/((dyadicRow k:ℝ)*Real.log (dyadicRow k))) =
        (C/(Real.log 2)^2)*(harmonicWeight j*harmonicWeight k)+
          (C/Real.log 2)*dyadicOverlapError j k := by
      rw [log_dyadicRow, log_dyadicRow]
      simp only [dyadicRow, Nat.cast_pow, Nat.cast_ofNat, pow_succ, Nat.cast_mul,
        harmonicWeight, dyadicOverlapError, if_pos hjk]
      field_simp
    rw [he] at hh
    have h1 := mul_le_mul_of_nonneg_right (show C/(Real.log 2)^2 ≤ C' by dsimp [C']; linarith)
      (mul_nonneg (harmonicWeight_pos j).le (harmonicWeight_pos k).le)
    have h2 := mul_le_mul_of_nonneg_right (show C/Real.log 2 ≤ C' by dsimp [C']; linarith)
      (show 0 ≤ dyadicOverlapError j k by simp only [dyadicOverlapError, if_pos hjk]; positivity)
    exact hh.trans (by nlinarith)

end TaoAdditive1132
end
end SourceErdos1132_Additive_LogarithmicRecurrence

/- Erdos1132.Additive.LocalRecurrence -/
section SourceErdos1132_Additive_LocalRecurrence
/- # Positive-measure recurrence of the sharp additive lower bound

Main paper: §6, recurrence and Theorem 1(i).
-/

noncomputable section
open MeasureTheory Set Filter Real
open scoped Topology
namespace TaoAdditive1132

theorem local_additive_recurrence (X : ∀ n, Nodes n) {a b c : ℝ}
    (hab : a < b) (hI : Icc a b ⊆ Icc (-1) 1)
    (hupper : ∀ᶠ n : ℕ in atTop, ∀ x ∈ Icc a b,
      (X n).lebesgue x ≤ logarithmicLevel (2/Real.pi) c n) :
    ∃ D > 0, 0 < volume {x | x ∈ Icc a b ∧
      ∃ᶠ n : ℕ in atTop, (2/Real.pi)*Real.log n-D < (X n).lebesgue x} := by
  obtain ⟨A, D, hD, c₁, hc₁, C, hC, N, hAm, hrow, hpair⟩ := exists_high_covers X hab hI hupper
  let μ := volume.restrict (Icc a b)
  have hμ (n : ℕ) (hn : N ≤ n) : μ.real (A n) = volume.real (A n) := by
    rw [measureReal_restrict_apply (hAm n), inter_eq_left.mpr (hrow n hn).2.2.1]
  have hμpair (n m : ℕ) (hn : N ≤ n) : μ.real (A n ∩ A m) = volume.real (A n ∩ A m) := by
    rw [measureReal_restrict_apply ((hAm n).inter (hAm m)),
      inter_eq_left.mpr (Set.inter_subset_left.trans (hrow n hn).2.2.1)]
  have hfreq := measure_frequently_pos_of_logarithmic_bounds μ A hAm hc₁ hC N
    (fun n hn => by rw [hμ n hn]; exact (hrow n hn).2.2.2.2.1)
    (fun n hn => by rw [hμ n hn]; exact (hrow n hn).2.2.2.2.2)
    (fun n m hn hm hnm => by rw [hμpair n m hn]; exact hpair n m hn hm hnm)
  refine ⟨D+1, by positivity, ?_⟩
  have hle : μ {x | ∃ᶠ n : ℕ in atTop, x ∈ A n} ≤
      volume {x | ∃ᶠ n : ℕ in atTop, x ∈ A n} := Measure.restrict_apply_le (Icc a b) _
  apply (hfreq.trans_le hle).trans_le
  apply measure_mono
  intro x hx
  have htail : ∃ᶠ n : ℕ in atTop, x ∈ A n ∧ N ≤ n := hx.and_eventually (eventually_ge_atTop N)
  obtain ⟨n, hxn, hn⟩ := htail.exists
  refine ⟨(hrow n hn).2.2.1 hxn, ?_⟩
  apply htail.mono
  intro m hm
  have hh := (hrow m hm.2).2.2.2.1 x hm.1
  linarith

end TaoAdditive1132
end
end SourceErdos1132_Additive_LocalRecurrence

/- Erdos1132.Shared.BaireBounds -/
section SourceErdos1132_Shared_BaireBounds
/- # Interval lower bounds and dense sets of recurrent points

Main paper, §6, and companion note, §5: the Baire arguments for density and interval constants.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace TaoAdditive1132

/-- Every nonempty relatively open subset of `(-1,1)` contains a
nondegenerate compact real interval. -/
theorem exists_Icc_in_relative_open
    {V : Set (Ioo (-1 : ℝ) 1)} (hV : IsOpen V) (hne : V.Nonempty) :
    ∃ l r : ℝ, l < r ∧ ∃ hI : Icc l r ⊆ Ioo (-1 : ℝ) 1,
      ∀ x (hx : x ∈ Icc l r), (⟨x, hI hx⟩ :
        Ioo (-1 : ℝ) 1) ∈ V := by
  have ho : IsOpen (Subtype.val '' V : Set ℝ) :=
    isOpen_Ioo.isOpenMap_subtype_val _ hV
  obtain ⟨x, hx⟩ := hne
  obtain ⟨a, b, ⟨hax, hxb⟩, hab⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (ho.mem_nhds (mem_image_of_mem _ hx))
  let l := (a + (x : ℝ)) / 2
  let r := ((x : ℝ) + b) / 2
  have hsub : Icc l r ⊆ Subtype.val '' V := by
    intro y hy
    apply hab
    dsimp [l, r] at hy
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hI : Icc l r ⊆ Ioo (-1 : ℝ) 1 := by
    rintro y hy
    obtain ⟨z, _, rfl⟩ := hsub hy
    exact z.property
  refine ⟨l, r, by dsimp [l, r]; linarith, hI, ?_⟩
  intro y hy
  obtain ⟨z, hz, heq⟩ := hsub hy
  have heq' : z = (⟨y, hI hy⟩ : Ioo (-1 : ℝ) 1) := Subtype.ext heq
  exact heq' ▸ hz

/-- Continuous functions whose high-value tail sets are dense exceed the
prescribed thresholds infinitely often on a dense set. -/
theorem dense_frequently_of_dense_tails
    {α : Type*} [TopologicalSpace α] [BaireSpace α]
    (f : ℕ → α → ℝ) (hf : ∀ n, Continuous (f n)) (a : ℕ → ℝ)
    (htail : ∀ N, Dense {x | ∃ n ≥ N, a n < f n x}) :
    Dense {x | ∃ᶠ n in atTop, a n < f n x} := by
  have hopen (N : ℕ) : IsOpen {x | ∃ n ≥ N, a n < f n x} := by
    have heq : {x | ∃ n ≥ N, a n < f n x} =
        ⋃ n ≥ N, {x | a n < f n x} := by ext; simp
    rw [heq]
    exact isOpen_iUnion fun n => isOpen_iUnion fun _ => isOpen_lt continuous_const (hf n)
  have hd := dense_iInter_of_isOpen hopen htail
  apply hd.mono
  intro x hx
  exact frequently_atTop.mpr (fun N => mem_iInter.mp hx N)

/-- An eventual lower bound for the supremum on every compact interior
interval gives a dense set of infinitely many strict occurrences, with any
fixed positive slack. The starting index can depend on the interval. -/
theorem dense_frequently_of_interval_sup
    (f : ℕ → ℝ → ℝ) (hf : ∀ n, Continuous (f n)) (a : ℕ → ℝ)
    {ε : ℝ} (hε : 0 < ε)
    (hlower : ∀ l r : ℝ, l < r → Icc l r ⊆ Ioo (-1 : ℝ) 1 →
      ∀ᶠ n in atTop, a n ≤ sSup (f n '' Icc l r)) :
    Dense {x : Ioo (-1 : ℝ) 1 | ∃ᶠ n in atTop, a n - ε < f n x} := by
  let : BaireSpace (Ioo (-1 : ℝ) 1) := isOpen_Ioo.baireSpace
  apply dense_frequently_of_dense_tails (fun n (x : Ioo (-1 : ℝ) 1) => f n x)
    (fun n => (hf n).comp continuous_subtype_val) (fun n => a n - ε)
  intro N
  rw [dense_iff_inter_open]
  intro V hV hne
  obtain ⟨l, r, hlr, hI, hVlr⟩ := exists_Icc_in_relative_open hV hne
  obtain ⟨n, hn, hsup⟩ := ((eventually_ge_atTop N).and (hlower l r hlr hI)).exists
  obtain ⟨_, ⟨x, hx, rfl⟩, hfx⟩ :=
    exists_lt_of_lt_csSup ((nonempty_Icc.mpr hlr.le).image (f n))
      (show a n - ε < sSup (f n '' Icc l r) by linarith)
  exact ⟨⟨x, hI hx⟩, hVlr x hx, n, hn, hfx⟩

/-- Pointwise eventual upper bounds on a sequence have finite upper bounds
including the initial rows. A natural number can be used for the bound. -/
theorem exists_nat_bound_of_eventually_le {f a : ℕ → ℝ}
    (hf : ∀ᶠ n in atTop, f n ≤ a n) :
    ∃ M : ℕ, ∀ n, f n ≤ a n + M := by
  have hb : atTop.IsBoundedUnder (· ≤ ·) (fun n => f n - a n) := by
    refine ⟨0, ?_⟩
    change ∀ᶠ n in atTop, f n - a n ≤ 0
    filter_upwards [hf] with n hn
    exact sub_nonpos.mpr hn
  obtain ⟨C, hC⟩ := hb.bddAbove_range
  obtain ⟨M, hM⟩ := exists_nat_ge C
  refine ⟨M, fun n => ?_⟩
  have hn := hC (mem_range_self n)
  linarith

/-- Baire category turns local recurrence under a uniform upper estimate into
density of the points having some finite additive loss. -/
theorem dense_additive_good_of_local_recurrence
    (f : ℕ → ℝ → ℝ) (hf : ∀ n, Continuous (f n)) (a : ℕ → ℝ)
    (hrec : ∀ l r : ℝ, l < r → Icc l r ⊆ Ioo (-1 : ℝ) 1 → ∀ C : ℝ,
      (∀ᶠ n in atTop, ∀ x ∈ Icc l r, f n x ≤ a n + C) →
      ∃ x ∈ Icc l r, ∃ D : ℝ, ∃ᶠ n in atTop, a n - D < f n x) :
    Dense {x : Ioo (-1 : ℝ) 1 | ∃ C : ℝ, ∃ᶠ n in atTop, a n - C < f n x} := by
  let : BaireSpace (Ioo (-1 : ℝ) 1) := isOpen_Ioo.baireSpace
  rw [dense_iff_inter_open]
  intro V hV hne
  by_contra hempty
  have hbad (x : Ioo (-1 : ℝ) 1) (hx : x ∈ V) :
      ¬∃ C : ℝ, ∃ᶠ n in atTop, a n - C < f n x := by
    intro h
    exact hempty ⟨x, hx, h⟩
  have hbound (x : V) : ∃ M : ℕ, ∀ n, f n x.val ≤ a n + M := by
    apply exists_nat_bound_of_eventually_le
    have hnot : ¬∃ᶠ n in atTop, a n < f n x.val := by
      intro hh
      exact hbad x.val x.property ⟨0, by simpa using hh⟩
    simpa only [not_frequently, not_lt] using hnot
  let F (M : ℕ) : Set V := {x | ∀ n, f n x.val ≤ a n + M}
  have hclosed (M : ℕ) : IsClosed (F M) := by
    have heq : F M = ⋂ n : ℕ, {x : V | f n x.val ≤ a n + M} := by ext; simp [F]
    rw [heq]
    exact isClosed_iInter fun n => isClosed_le
      ((hf n).comp (continuous_subtype_val.comp continuous_subtype_val)) continuous_const
  have hcover : ⋃ M, F M = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨M, hM⟩ := hbound x
    exact mem_iUnion.mpr ⟨M, hM⟩
  let : BaireSpace V := hV.baireSpace
  let : Nonempty V := hne.to_subtype
  obtain ⟨M, hM⟩ := nonempty_interior_of_iUnion_of_closed hclosed hcover
  let W : Set (Ioo (-1 : ℝ) 1) := Subtype.val '' interior (F M)
  have hW : IsOpen W := hV.isOpenMap_subtype_val _ isOpen_interior
  obtain ⟨l, r, hlr, hI, hWI⟩ := exists_Icc_in_relative_open hW (hM.image Subtype.val)
  have hupper : ∀ n, ∀ x ∈ Icc l r, f n x ≤ a n + M := by
    intro n x hx
    obtain ⟨z, hz, heq⟩ := hWI x hx
    have hz' := (interior_subset hz : z ∈ F M) n
    have heq' : (z.val : ℝ) = x := congrArg Subtype.val heq
    simpa only [heq'] using hz'
  obtain ⟨x, hx, D, hD⟩ := hrec l r hlr hI M (Eventually.of_forall hupper)
  obtain ⟨z, _, heq⟩ := hWI x hx
  exact hbad ⟨x, hI hx⟩ (heq ▸ z.property) ⟨D, hD⟩

end TaoAdditive1132
end
end SourceErdos1132_Shared_BaireBounds

/- Erdos1132.Additive.Main -/
section SourceErdos1132_Additive_Main
/- # The sharp additive lower bound on a dense set

This is Theorem 1(i), with exactly `n` distinct interpolation nodes in row `n`.
The additive constant can depend on the chosen point.

Main paper: §6, recurrence and Theorem 1(i).
-/

noncomputable section
open MeasureTheory Set Filter Real
open scoped Topology
namespace TaoAdditive1132

theorem dense_additive_lower_bound (X : ∀ n, Nodes n) :
    Dense {x : Ioo (-1:ℝ) 1 | ∃ C : ℝ, ∃ᶠ n : ℕ in atTop,
      (2/Real.pi)*Real.log n-C < (X n).lebesgue x} := by
  apply dense_additive_good_of_local_recurrence (fun n x => (X n).lebesgue x)
    (fun n => (X n).continuous_lebesgue) (fun n => (2/Real.pi)*Real.log n)
  intro l r hlr hI C hupper
  have hI' : Icc l r ⊆ Icc (-1:ℝ) 1 := hI.trans Ioo_subset_Icc_self
  obtain ⟨D, hD, hrec⟩ := local_additive_recurrence X hlr hI' hupper
  obtain ⟨x, hx, hxf⟩ := nonempty_of_measure_ne_zero hrec.ne'
  exact ⟨x, hx, D, hxf⟩

end TaoAdditive1132
end
end SourceErdos1132_Additive_Main

section Tao1132Adapter

open Filter Set
open scoped Topology BigOperators

namespace TaoAdditive1132

private theorem prod_fin_erase_eq_prod_range {n : ℕ} (i : Fin n) (f : ℕ → ℝ) :
    (∏ j ∈ Finset.univ.erase i, f j.val) =
      ∏ k ∈ (Finset.range n).erase i.val, f k := by
  classical
  refine Finset.prod_bij (fun j _ => j.val) ?_ ?_ ?_ ?_
  · intro j hj
    rw [Finset.mem_erase] at hj ⊢
    exact ⟨fun h => hj.1 (Fin.ext h), Finset.mem_range.mpr j.isLt⟩
  · intro a _ b _ h
    exact Fin.ext h
  · intro k hk
    obtain ⟨hne, hlt⟩ := Finset.mem_erase.mp hk
    let j : Fin n := ⟨k, Finset.mem_range.mp hlt⟩
    exact ⟨j, Finset.mem_erase.mpr ⟨fun h => hne (congrArg Fin.val h),
      Finset.mem_univ j⟩, rfl⟩
  · intro j _
    rfl

private theorem lebesgue_eq_explicit {n : ℕ} (x : ℕ → ℝ) (X : Nodes n)
    (hpoint : ∀ i : Fin n, X.point i = x i.val) (t : ℝ) :
    X.lebesgue t = Erdos1132.lebesgueFunction n x t := by
  classical
  unfold Nodes.lebesgue Erdos1132.lebesgueFunction
  refine Finset.sum_bij (fun i _ => i.val) ?_ ?_ ?_ ?_
  · intro i _
    exact Finset.mem_range.mpr i.isLt
  · intro i _ j _ h
    exact Fin.ext h
  · intro k hk
    let i : Fin n := ⟨k, Finset.mem_range.mp hk⟩
    exact ⟨i, Finset.mem_univ i, rfl⟩
  · intro i _
    congr 1
    simp only [Nodes.cardinal, Lagrange.basis, Lagrange.basisDivisor,
      Polynomial.eval_prod, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
      Polynomial.eval_X, hpoint, Finset.prod_mul_distrib, ← Finset.prod_inv_distrib,
      div_eq_mul_inv, Erdos1132.lagrangeBasis]
    exact (congrArg₂ (· * ·)
      (prod_fin_erase_eq_prod_range i (fun k => (x i.val - x k)⁻¹))
      (prod_fin_erase_eq_prod_range i (fun k => t - x k))).trans (mul_comm _ _)

end TaoAdditive1132

theorem OMA.solution : type_of% @Erdos1132.erdos_1132.variants.tao := by
  intro x hx hinj ω hω t ht
  let rows : ∀ n, TaoAdditive1132.Nodes n := fun n =>
    ⟨fun k => x n k.val,
      fun i j hij => Fin.ext (hinj n i.isLt j.isLt hij),
      fun i => hx n i.val i.isLt⟩
  let good : Set (Ioo (-1 : ℝ) 1) := {u | ∃ C : ℝ, ∃ᶠ n : ℕ in atTop,
    (2 / Real.pi) * Real.log n - C < (rows n).lebesgue u}
  have hdense : Dense good := TaoAdditive1132.dense_additive_lower_bound rows
  have hclose : t ∈ closure (Subtype.val '' good) :=
    image_closure_subset_closure_image continuous_subtype_val
      ⟨⟨t, ht⟩, hdense ⟨t, ht⟩, rfl⟩
  refine closure_mono ?_ hclose
  rintro _ ⟨u, hu, rfl⟩
  obtain ⟨C, hC⟩ := hu
  refine ⟨u.property, (hC.and_eventually ((tendsto_atTop.1 hω) C)).mono ?_⟩
  rintro n ⟨hn, hCn⟩
  rw [TaoAdditive1132.lebesgue_eq_explicit (x n) (rows n) (fun _ => rfl)] at hn
  exact le_of_lt ((sub_le_sub_left hCn _).trans_lt hn)

end Tao1132Adapter
