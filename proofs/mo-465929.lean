import OMAStatements.S_mo_465929
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.SesquilinearForm.Star
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic
import Mathlib.Tactic.Ring

/-!
# A sharp dimension-free comparison of Gaussian Wasserstein distances

Question by Vladimir Zolotov: https://mathoverflow.net/questions/465929.
Proof and formalization by OpenAI Codex for @LDJAI.

An orthogonal change of the common standard Gaussian input aligns the covariance
factors. A second orthogonal change of basis makes corresponding coordinate
rows nonnegative multiples of the same scalar linear form, allowing zero rows.
The absolute value of each coordinate is a nonexpansive test. Its expectation
converts the coordinate standard deviation into a first absolute moment.
Combining the coordinates gives the sharp factor, including for singular laws.
-/

section

open MeasureTheory

namespace OMA.S_mo_465929

private abbrev V (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Coordinatewise absolute value in the specified orthonormal coordinates. -/
def foldCoordinates {d : ℕ} (x : V d) : V d := WithLp.toLp 2 (fun i ↦ |x i|)

/-- Folding all coordinates at the origin is nonexpansive for the Euclidean distance. -/
theorem foldCoordinates_lipschitz {d : ℕ} : LipschitzWith 1 (@foldCoordinates d) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, dist_eq_norm, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  change ‖|x i| - |y i|‖ ^ 2 ≤ ‖x i - y i‖ ^ 2
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  simpa only [Real.norm_eq_abs] using abs_norm_sub_norm_le (x i) (y i)

@[simp] theorem foldCoordinates_zero {d : ℕ} : foldCoordinates (0 : V d) = 0 := by
  ext i
  change |(0 : ℝ)| = 0
  simp

/-- A coupling-independent lower bound on Euclidean first transport cost: the
    distance between the means of its folded marginals. -/
theorem folded_mean_distance_le_cost {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X Y : Ω → V d} (hX : Integrable X μ) (hY : Integrable Y μ) :
    ‖(∫ ω, foldCoordinates (X ω) ∂μ) - (∫ ω, foldCoordinates (Y ω) ∂μ)‖ ≤
      ∫ ω, dist (X ω) (Y ω) ∂μ := by
  have hFX : Integrable (fun ω ↦ foldCoordinates (X ω)) μ := by
    exact memLp_one_iff_integrable.mp (foldCoordinates_lipschitz.comp_memLp foldCoordinates_zero (memLp_one_iff_integrable.mpr hX))
  have hFY : Integrable (fun ω ↦ foldCoordinates (Y ω)) μ := by
    exact memLp_one_iff_integrable.mp (foldCoordinates_lipschitz.comp_memLp foldCoordinates_zero (memLp_one_iff_integrable.mpr hY))
  rw [← integral_sub hFX hFY]
  refine (norm_integral_le_integral_norm _).trans ?_
  apply integral_mono (hFX.sub hFY).norm (hX.sub hY).norm
  intro ω
  change ‖foldCoordinates (X ω) - foldCoordinates (Y ω)‖ ≤ ‖X ω - Y ω‖
  simpa only [dist_eq_norm, NNReal.coe_one, one_mul] using
    (foldCoordinates_lipschitz.dist_le_mul (X ω) (Y ω))

/-- Integration of the folded vector records each first absolute moment. -/
theorem folded_mean_apply {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → V d} (hX : Integrable X μ) (i : Fin d) :
    (∫ ω, foldCoordinates (X ω) ∂μ) i = ∫ ω, |X ω i| ∂μ := by
  have hF : Integrable (fun ω ↦ foldCoordinates (X ω)) μ :=
    memLp_one_iff_integrable.mp
      (foldCoordinates_lipschitz.comp_memLp foldCoordinates_zero (memLp_one_iff_integrable.mpr hX))
  exact ((EuclideanSpace.proj i).integral_comp_comm hF).symm

/-- Every joint measure has first transport cost at least the norm of the
difference of the two marginal folded mean vectors, in any orthonormal basis. -/
theorem folded_marginals_le_coupling_cost {d : ℕ} (b : V d ≃ₗᵢ[ℝ] V d)
    {μ ν : Measure (V d)} {π : Measure (V d × V d)}
    (hm : π.map Prod.fst = μ) (hn : π.map Prod.snd = ν)
    (hμ : Integrable (fun x ↦ x) μ) (hν : Integrable (fun x ↦ x) ν) :
    ‖(∫ x, foldCoordinates (b x) ∂μ) - (∫ y, foldCoordinates (b y) ∂ν)‖ ≤
      ∫ z, dist z.1 z.2 ∂π := by
  subst μ ν
  have hX : Integrable (fun z : V d × V d ↦ b z.1) π :=
    (b.toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp hμ).comp_measurable measurable_fst
  have hY : Integrable (fun z : V d × V d ↦ b z.2) π :=
    (b.toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp hν).comp_measurable measurable_snd
  have hf : Continuous (fun x : V d ↦ foldCoordinates (b x)) :=
    foldCoordinates_lipschitz.continuous.comp b.continuous
  rw [integral_map measurable_fst.aemeasurable hf.aestronglyMeasurable,
      integral_map measurable_snd.aemeasurable hf.aestronglyMeasurable]
  simpa only [b.isometry.dist_eq] using folded_mean_distance_le_cost hX hY

/-- Taking the infimum over all couplings preserves the lower bound. The set
of admissible costs is nonempty because it contains the independent coupling. -/
theorem folded_marginals_le_first_transport {d : ℕ} (b : V d ≃ₗᵢ[ℝ] V d)
    {μ ν : Measure (V d)} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun x ↦ x) μ) (hν : Integrable (fun x ↦ x) ν) :
    ‖(∫ x, foldCoordinates (b x) ∂μ) - (∫ y, foldCoordinates (b y) ∂ν)‖ ≤
      sInf {r : ℝ | ∃ π : Measure (V d × V d), (π.map Prod.fst = μ ∧ π.map Prod.snd = ν) ∧
        r = ∫ z, dist z.1 z.2 ^ 1 ∂π} := by
  apply le_csInf
  · exact ⟨_, μ.prod ν, ⟨by simp, by simp⟩, rfl⟩
  · rintro _ ⟨π, ⟨hm, hn⟩, rfl⟩
    simpa only [pow_one] using folded_marginals_le_coupling_cost b hm hn hμ hν

end OMA.S_mo_465929

end

section

open MeasureTheory
namespace OMA.S_mo_465929

/-- In an aligned direction, both coordinates are nonnegative multiples of the
same variable. Its first absolute moment and second moment determine the exact
ratio between squared folded mean separation and quadratic transport cost. -/
theorem aligned_scalar_cost {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {U : Ω → ℝ} {s t k : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hU : (∫ x, |U x| ∂μ)^2 = k^2 * ∫ x, (U x)^2 ∂μ) :
    ((∫ x, |s * U x| ∂μ) - (∫ x, |t * U x| ∂μ)) ^ 2 =
      k ^ 2 * ∫ x, (s * U x - t * U x)^2 ∂μ := by
  simp_rw [abs_mul, abs_of_nonneg hs, abs_of_nonneg ht]
  rw [integral_const_mul, integral_const_mul]
  have hp : (fun x ↦ (s * U x - t * U x)^2) = fun x ↦ (s - t)^2 * (U x)^2 := by
    funext x
    ring
  rw [hp, integral_const_mul]
  calc
    _ = (s-t)^2 * (∫ x, |U x| ∂μ)^2 := by ring
    _ = _ := by rw [hU]; ring

/-- Coordinatewise equalities aggregate to an exact squared Euclidean coupling
cost when an orthogonal coordinate system is used. -/
theorem aggregate_coordinate_cost {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {d : ℕ} (X Y : Ω → EuclideanSpace ℝ (Fin d))
    (a b : EuclideanSpace ℝ (Fin d)) (k : ℝ)
    (hint : ∀ i, Integrable (fun x ↦ (X x i - Y x i)^2) μ)
    (h : ∀ i, (a i - b i)^2 = k^2 * ∫ x, (X x i - Y x i)^2 ∂μ) :
    ‖a - b‖^2 = k^2 * ∫ x, dist (X x) (Y x)^2 ∂μ := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [dist_eq_norm, EuclideanSpace.real_norm_sq_eq, PiLp.sub_apply]
  simp_rw [h]
  rw [integral_finsetSum _ (fun i _ ↦ hint i), Finset.mul_sum]

end OMA.S_mo_465929

end

section

open MeasureTheory ProbabilityTheory Real Set
open scoped NNReal

namespace OMA.S_mo_465929

/-- The Euclidean half-normal moment in variance parametrization, including variance zero. -/
theorem abs_moment_gaussianReal_zero (v : ℝ≥0) :
    (∫ x : ℝ, |x| ∂gaussianReal 0 v) = Real.sqrt (2 / Real.pi) * Real.sqrt (v : ℝ) := by
  have hRay : (∫ x : ℝ in Ioi 0, x * Real.exp (-(1/2 : ℝ) * x ^ 2)) = 1 := by
    have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 1) (b := 1/2)
      (by norm_num) (by norm_num) (by norm_num)
    norm_num [Real.Gamma_one, Real.rpow_neg_one] at h
    simpa only [neg_mul] using h
  have hStd : (∫ x : ℝ, |x| ∂gaussianReal 0 1) = Real.sqrt (2 / Real.pi) := by
    rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
    calc
      _ = (Real.sqrt (2 * Real.pi))⁻¹ * ∫ x : ℝ, |x| * Real.exp (-(1/2 : ℝ) * |x| ^ 2) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with x
        simp only [gaussianPDFReal, sub_zero, NNReal.coe_one, mul_one, smul_eq_mul, sq_abs]
        ring_nf
      _ = (Real.sqrt (2 * Real.pi))⁻¹ * (2 * 1) := by
        rw [integral_comp_abs (f := fun y : ℝ ↦ y * Real.exp (-(1/2 : ℝ) * y ^ 2)), hRay]
      _ = _ := by
        rw [Real.sqrt_div (by norm_num), Real.sqrt_mul (by norm_num)]
        field_simp
        nlinarith [Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]
  have hmap : (gaussianReal 0 1).map (Real.sqrt (v : ℝ) * ·) = gaussianReal 0 v := by
    rw [gaussianReal_map_const_mul]
    simp only [mul_zero, mul_one]
    congr 1
    exact NNReal.eq (Real.sq_sqrt v.coe_nonneg)
  rw [← hmap, integral_map (by fun_prop) (by fun_prop)]
  simp_rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [integral_const_mul, hStd, mul_comm]

/-- A real-valued centered Gaussian observable has a fixed ratio between its
absolute first moment squared and its second moment. -/
theorem abs_moment_sq_of_gaussianReal_map {Ω : Type*} [MeasurableSpace Ω]
    {ρ : Measure Ω} {U : Ω → ℝ} {v : ℝ≥0} (hU : AEMeasurable U ρ)
    (hlaw : ρ.map U = gaussianReal 0 v) :
    (∫ x, |U x| ∂ρ) ^ 2 =
      Real.sqrt (2 / Real.pi) ^ 2 * ∫ x, (U x) ^ 2 ∂ρ := by
  have hfirst : (∫ x, |U x| ∂ρ) = Real.sqrt (2 / Real.pi) * Real.sqrt (v : ℝ) := by
    rw [← abs_moment_gaussianReal_zero v, ← hlaw, integral_map hU (by fun_prop)]
  have hvar := variance_fun_id_gaussianReal (μ := 0) (v := v)
  rw [variance_eq_integral measurable_id'.aemeasurable] at hvar
  simp only [integral_id_gaussianReal, sub_zero] at hvar
  have hsecond : (∫ x, (U x) ^ 2 ∂ρ) = (v : ℝ) := by
    rw [← hvar, ← hlaw, integral_map hU (by fun_prop)]
  rw [hfirst, hsecond, mul_pow, Real.sq_sqrt v.coe_nonneg]

end OMA.S_mo_465929

end

section

namespace OMA.S_mo_465929

open MeasureTheory ProbabilityTheory

variable {d : ℕ} {μ ν : Measure (E d)} {π : Measure (E d × E d)}

/-- A specified coupling gives an upper bound on optimal powered transport cost. -/
theorem transportCost_le_of_coupling (p : ℕ) (hπ : IsCoupling π μ ν) :
    transportCost p μ ν ≤ ∫ z, dist z.1 z.2 ^ p ∂π := by
  unfold transportCost
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro _ ⟨ρ, _, rfl⟩
    exact integral_nonneg fun z ↦ pow_nonneg dist_nonneg p
  · exact ⟨π, hπ, rfl⟩

/-- A lower bound valid for every coupling descends to the optimal cost. -/
theorem le_transportCost_of_forall [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (p : ℕ) (a : ℝ)
    (h : ∀ ρ : Measure (E d × E d), IsCoupling ρ μ ν → a ≤ ∫ z, dist z.1 z.2 ^ p ∂ρ) :
    a ≤ transportCost p μ ν := by
  apply le_csInf
  · refine ⟨_, μ.prod ν, ?_, rfl⟩
    constructor <;> simp
  · rintro _ ⟨ρ, hρ, rfl⟩
    exact h ρ hρ

end OMA.S_mo_465929
namespace OMA.S_mo_465929
open MeasureTheory ProbabilityTheory

/-- An aligned linear coupling of the two Gaussian laws gives the sharp bound.
    Singular covariances are permitted in the row hypothesis. -/
theorem comparison_of_aligned_gaussian_factors {d : ℕ} {μ ν : Measure (E d)}
    [IsGaussian μ] [IsGaussian ν] (b : E d ≃ₗᵢ[ℝ] E d) (G H : E d →L[ℝ] E d)
    (hG : (stdGaussian (E d)).map G = μ) (hH : (stdGaussian (E d)).map H = ν)
    (hrows : ∀ i : Fin d, ∃ (s t : ℝ) (U : StrongDual ℝ (E d)) (v : NNReal),
       0 ≤ s ∧ 0 ≤ t ∧ (stdGaussian (E d)).map U = gaussianReal 0 v ∧
       (∀ x, b (G x) i = s * U x) ∧ (∀ x, b (H x) i = t * U x)) :
    Real.sqrt (transportCost 2 μ ν) ≤ (Real.sqrt (2 / Real.pi))⁻¹ * transportCost 1 μ ν := by
  let ρ := stdGaussian (E d)
  let k := Real.sqrt (2 / Real.pi)
  have hk : 0 < k := Real.sqrt_pos.mpr (div_pos (by norm_num) Real.pi_pos)
  let X : E d →L[ℝ] E d := b.toContinuousLinearEquiv.toContinuousLinearMap.comp G
  let Y : E d →L[ℝ] E d := b.toContinuousLinearEquiv.toContinuousLinearMap.comp H
  have hX : Integrable X ρ := X.integrable_comp (IsGaussian.integrable_id (μ := ρ))
  have hY : Integrable Y ρ := Y.integrable_comp (IsGaussian.integrable_id (μ := ρ))
  let a : E d := ∫ x, foldCoordinates (X x) ∂ρ
  let c : E d := ∫ x, foldCoordinates (Y x) ∂ρ
  have hsq : ‖a-c‖^2 = k^2 * ∫ x, dist (G x) (H x)^2 ∂ρ := by
    have he : ∀ x, dist (G x) (H x) = dist (X x) (Y x) := fun x ↦ (b.isometry.dist_eq _ _).symm
    simp_rw [he]
    apply aggregate_coordinate_cost X Y a c k
    · intro i
      let L := (EuclideanSpace.proj i).comp (X - Y)
      exact (L.lipschitz.comp_memLp L.map_zero (IsGaussian.memLp_two_id (μ := ρ))).integrable_sq
    · intro i
      obtain ⟨s,t,U,v,hs,ht,hlaw,hx,hy⟩ := hrows i
      rw [show a i = _ from folded_mean_apply hX i, show c i = _ from folded_mean_apply hY i]
      change ((∫ x, |b (G x) i| ∂ρ) - (∫ x, |b (H x) i| ∂ρ)) ^ 2 =
        k ^ 2 * ∫ x, (b (G x) i - b (H x) i) ^ 2 ∂ρ
      simp_rw [hx, hy]
      exact aligned_scalar_cost hs ht (abs_moment_sq_of_gaussianReal_map U.measurable.aemeasurable hlaw)
  have hf : Continuous (fun x : E d ↦ foldCoordinates (b x)) := foldCoordinates_lipschitz.continuous.comp b.continuous
  have ha : (∫ x, foldCoordinates (b x) ∂μ) = a := by
    rw [← hG, integral_map G.measurable.aemeasurable hf.aestronglyMeasurable]
    rfl
  have hc : (∫ x, foldCoordinates (b x) ∂ν) = c := by
    rw [← hH, integral_map H.measurable.aemeasurable hf.aestronglyMeasurable]
    rfl
  have hl : ‖a-c‖ ≤ transportCost 1 μ ν := by
    rw [← ha, ← hc]
    exact folded_marginals_le_first_transport b IsGaussian.integrable_id IsGaussian.integrable_id
  let J := fun x : E d ↦ (G x,H x)
  have hJ : Measurable J := G.measurable.prodMk H.measurable
  have hπ : IsCoupling (ρ.map J) μ ν := by
    constructor
    · rw [Measure.map_map measurable_fst hJ]
      exact hG
    · rw [Measure.map_map measurable_snd hJ]
      exact hH
  have hub : transportCost 2 μ ν ≤ ∫ x, dist (G x) (H x)^2 ∂ρ := by
    have h := transportCost_le_of_coupling 2 hπ
    rwa [integral_map hJ.aemeasurable (by fun_prop)] at h
  have hn : 0 ≤ ∫ x, dist (G x) (H x)^2 ∂ρ := integral_nonneg fun _ ↦ sq_nonneg _
  have hsqrt : ‖a-c‖ = k * Real.sqrt (∫ x, dist (G x) (H x)^2 ∂ρ) := by
    rw [← Real.sqrt_sq (norm_nonneg (a-c)), hsq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hk.le]
  calc
    _ ≤ Real.sqrt (∫ x, dist (G x) (H x)^2 ∂ρ) := Real.sqrt_le_sqrt hub
    _ = k⁻¹ * ‖a-c‖ := by rw [hsqrt, ← mul_assoc, inv_mul_cancel₀ hk.ne', one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hl (inv_nonneg.mpr hk.le)

end OMA.S_mo_465929

end

section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace OMA.S_mo_465929

noncomputable section

private abbrev MatrixSpace (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The covariance form in the standard Euclidean orthonormal basis. -/
def gaussianCovMatrix {d : ℕ} (μ : Measure (MatrixSpace d)) : Matrix (Fin d) (Fin d) ℝ :=
  LinearMap.BilinForm.toMatrix (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
    (covarianceBilin μ).toBilinForm

theorem gaussianCovMatrix_posSemidef {d : ℕ} (μ : Measure (MatrixSpace d)) :
    (gaussianCovMatrix μ).PosSemidef := by
  apply (LinearMap.isPosSemidef_iff_posSemidef_toMatrix
    (EuclideanSpace.basisFun (Fin d) ℝ).toBasis).mp
  exact ⟨⟨fun x y ↦ covarianceBilin_comm (μ := μ) x y⟩,
    ⟨fun x ↦ covarianceBilin_self_nonneg (μ := μ) x⟩⟩

/-- Every centered Gaussian measure agrees with the matrix law for its covariance. -/
theorem centeredGaussian_eq_matrix {d : ℕ} (μ : Measure (MatrixSpace d))
    [IsGaussian μ] (hm : (∫ x, x ∂μ) = 0) :
    μ = multivariateGaussian 0 (gaussianCovMatrix μ) := by
  apply IsGaussian.ext
  · simpa using hm
  · rw [← ContinuousLinearMap.toBilinForm_inj]
    refine LinearMap.BilinForm.ext_basis
      (EuclideanSpace.basisFun (Fin d) ℝ).toBasis fun i j ↦ ?_
    rw [ContinuousLinearMap.toBilinForm_apply, ContinuousLinearMap.toBilinForm_apply,
      covarianceBilin_multivariateGaussian (gaussianCovMatrix_posSemidef μ)]
    simp [gaussianCovMatrix]

end
end OMA.S_mo_465929

end

section

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder

namespace OMA.S_mo_465929

theorem exists_stdGaussian_factor {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d)))
    [IsGaussian μ] (hm : (∫ x, x ∂μ) = 0) :
    ∃ G : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d),
      (stdGaussian _).map G = μ := by
  refine ⟨Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (gaussianCovMatrix μ)), ?_⟩
  simpa only [multivariateGaussian, zero_add] using (centeredGaussian_eq_matrix μ hm).symm

/-- Rotating the common standard Gaussian input preserves the output law. -/
theorem stdGaussian_map_comp_orthogonal {d : ℕ}
    (H : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (U : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) :
    (stdGaussian _).map (H.comp U.toContinuousLinearEquiv.toContinuousLinearMap) =
      (stdGaussian _).map H := by
  change (stdGaussian _).map (H ∘ U) = (stdGaussian _).map H
  rw [← Measure.map_map H.measurable U.continuous.measurable, stdGaussian_map]

end OMA.S_mo_465929

end

section

namespace OMA.S_mo_465929

/-- Maps with equal pointwise norms are related by an ambient orthogonal
change of basis, including maps with nontrivial kernels. -/
theorem exists_orthogonal_of_equal_norm {D V : Type*}
    [AddCommGroup D] [Module ℝ D] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (G H : D →ₗ[ℝ] V) (hn : ∀ x, ‖G x‖ = ‖H x‖) :
    ∃ U : V ≃ₗᵢ[ℝ] V, ∀ x, U (G x) = H x := by
  have hk : G.ker ≤ H.ker := by
    intro x hx
    apply norm_eq_zero.mp
    rw [← hn, show G x = 0 from hx, norm_zero]
  let L := (G.ker.liftQ H hk).comp G.quotKerEquivRange.symm.toLinearMap
  have hL (x : D) : L (G.rangeRestrict x) = H x := by
    change G.ker.liftQ H hk (G.quotKerEquivRange.symm ⟨G x, _⟩) = _
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  let Lᵢ : G.range →ₗᵢ[ℝ] V := ⟨L, by
    intro v
    obtain ⟨x, rfl⟩ := G.surjective_rangeRestrict v
    rw [hL]
    exact (hn x).symm⟩
  refine ⟨Lᵢ.extend.toLinearIsometryEquiv rfl, ?_⟩
  intro x
  change Lᵢ.extend (G.rangeRestrict x : G.range) = H x
  rw [LinearIsometry.extend_apply]
  exact hL x

end OMA.S_mo_465929

open scoped InnerProductSpace
open LinearMap

namespace OMA.S_mo_465929

/-- Polar-aligned factors induce a positive operator on the support of the first
factor, also when either factor is singular and their ranges differ. -/
theorem exists_positive_projected_factor {D V : Type*}
    [AddCommGroup D] [Module ℝ D] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (G H : D →ₗ[ℝ] V)
    (hsym : ∀ x y, ⟪H x, G y⟫_ℝ = ⟪G x, H y⟫_ℝ)
    (hpos : ∀ x, 0 ≤ ⟪H x, G x⟫_ℝ) :
    ∃ T : G.range →ₗ[ℝ] G.range, T.IsPositive ∧
      ∀ x, T (G.rangeRestrict x) = G.range.orthogonalProjectionOnto (H x) := by
  let F := G.range.orthogonalProjectionOnto.toLinearMap.comp H
  have hker : G.ker ≤ F.ker := by
    intro x hx
    change G.range.orthogonalProjectionOnto (H x) = 0
    apply (Submodule.orthogonalProjectionOnto_eq_zero_iff).mpr
    apply (Submodule.mem_orthogonal G.range _).mpr
    rintro _ ⟨z, rfl⟩
    rw [← hsym, show G x = 0 from hx, inner_zero_right]
  let T := (G.ker.liftQ F hker).comp G.quotKerEquivRange.symm.toLinearMap
  have apply_T (x : D) : T (G.rangeRestrict x) = G.range.orthogonalProjectionOnto (H x) := by
    change G.ker.liftQ F hker (G.quotKerEquivRange.symm ⟨G x, _⟩) = _
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  refine ⟨T, ⟨?_, ?_⟩, apply_T⟩
  · intro p q
    obtain ⟨x, rfl⟩ := G.surjective_rangeRestrict p
    obtain ⟨y, rfl⟩ := G.surjective_rangeRestrict q
    rw [apply_T, apply_T, Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right,
      Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
    exact hsym x y
  · intro p
    obtain ⟨x, rfl⟩ := G.surjective_rangeRestrict p
    rw [apply_T, Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]
    exact hpos x

end OMA.S_mo_465929

open scoped InnerProductSpace
open LinearMap

namespace OMA.S_mo_465929

/-- An orthonormal basis makes the rows of polar-aligned maps nonnegative
multiples of one another wherever the row of the first map is nonzero. -/
theorem exists_aligned_basis {D : Type*} [AddCommGroup D] [Module ℝ D]
    {d : ℕ} (G H : D →ₗ[ℝ] EuclideanSpace ℝ (Fin d))
    (hsym : ∀ x y, ⟪H x, G y⟫_ℝ = ⟪G x, H y⟫_ℝ)
    (hpos : ∀ x, 0 ≤ ⟪H x, G x⟫_ℝ) :
    ∃ b : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d),
      ∀ i, (∃ r : ℝ, 0 ≤ r ∧ ∀ z, b (H z) i = r * b (G z) i) ∨
        (∀ z, b (G z) i = 0) := by
  classical
  obtain ⟨T, hT, hmap⟩ := exists_positive_projected_factor G H hsym hpos
  let e := hT.isSymmetric.eigenvectorBasis rfl
  let f := G.range.subtypeₗᵢ ∘ ⇑e
  have hf : Orthonormal ℝ f := e.orthonormal.comp_linearIsometry _
  obtain ⟨S, b, hS, hb⟩ := hf.toSubtypeRange.exists_orthonormalBasis_extension
  have hbval (s : S) : b s = (s : EuclideanSpace ℝ (Fin d)) := congrFun hb s
  have hcard : Fintype.card S = d := by
    rw [← Module.finrank_eq_card_basis b.toBasis, finrank_euclideanSpace_fin]
  let bij := Fintype.equivFinOfCardEq hcard
  refine ⟨(b.reindex bij).repr, ?_⟩
  intro i
  let s := bij.symm i
  have hbi : (b.reindex bij) i = b s := by simp [s]
  simp only [OrthonormalBasis.repr_apply_apply, hbi]
  by_cases hs : (s : EuclideanSpace ℝ (Fin d)) ∈ Set.range f
  · obtain ⟨j, hj⟩ := hs
    left
    refine ⟨_, hT.nonneg_eigenvalues rfl j, ?_⟩
    intro z
    rw [hbval, ← hj]
    change ⟪(e j : EuclideanSpace ℝ (Fin d)), H z⟫_ℝ =
      _ * ⟪(e j : EuclideanSpace ℝ (Fin d)), G z⟫_ℝ
    rw [← Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left (e j) (H z), ← hmap]
    change ⟪e j, T (G.rangeRestrict z)⟫_ℝ = _ * ⟪e j, G.rangeRestrict z⟫_ℝ
    simpa only [OrthonormalBasis.repr_apply_apply, RCLike.ofReal_real_eq_id, id_eq, e] using
      hT.isSymmetric.eigenvectorBasis_apply_self_apply rfl (G.rangeRestrict z) j
  · right
    have hz : G.range.orthogonalProjectionOnto (b s) = 0 := by
      apply e.repr.injective
      ext j
      rw [map_zero, OrthonormalBasis.repr_apply_apply,
        Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
      let t : S := ⟨f j, hS ⟨j, rfl⟩⟩
      have ht : b t = f j := hbval t
      have hne : t ≠ s := by
        intro hts
        exact hs ⟨j, congrArg Subtype.val hts⟩
      change ⟪f j, b s⟫_ℝ = 0
      rw [← ht]
      exact b.orthonormal.2 hne
    intro z
    change ⟪b s, (G.rangeRestrict z : EuclideanSpace ℝ (Fin d))⟫_ℝ = 0
    rw [← Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right, hz, inner_zero_left]

end OMA.S_mo_465929

end

section

namespace OMA.S_mo_465929

open scoped MatrixOrder

/-- A possibly singular Euclidean endomorphism can be made positive by rotating
its input. This is the finite-dimensional polar decomposition with a full orthogonal factor. -/
theorem exists_right_positive_rotation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) :
    ∃ U : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι,
      (F * (U : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)).IsPositive := by
  let φ := Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)
  let M := φ.symm F
  let S := CFC.abs (star M)
  have hS : (0 : Matrix ι ι ℝ) ≤ S := CFC.abs_nonneg _
  have hSsq : S * S = M * star M := by simpa only [star_star] using CFC.abs_mul_abs (star M)
  have hGram : (φ (star M)).adjoint * φ (star M) = (φ S).adjoint * φ S := by
    change star (φ (star M)) * φ (star M) = star (φ S) * φ S
    simp only [← map_star, ← map_mul, star_star, hS.star_eq, hSsq]
  have hn (x : EuclideanSpace ℝ ι) : ‖φ (star M) x‖ = ‖φ S x‖ := by
    rw [ContinuousLinearMap.apply_norm_eq_sqrt_inner_adjoint_left,
      ContinuousLinearMap.apply_norm_eq_sqrt_inner_adjoint_left (φ S)]
    exact congrArg (fun g : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι ↦
      Real.sqrt (RCLike.re (inner ℝ (g x) x))) hGram
  obtain ⟨U, hU⟩ := exists_orthogonal_of_equal_norm (φ (star M)).toLinearMap (φ S).toLinearMap hn
  have hUS : (U : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) * φ (star M) = φ S := by
    ext x : 1
    exact hU x
  have hpos : (φ S).IsPositive := Matrix.isPositive_toEuclideanLin_iff.mpr (Matrix.nonneg_iff_posSemidef.mp hS)
  refine ⟨U.symm, ?_⟩
  have hstar := congrArg star hUS
  simp only [star_mul, ← map_star, star_star, LinearIsometryEquiv.star_eq_symm,
    hS.star_eq] at hstar
  have hFM : φ M = F := φ.apply_symm_apply F
  rw [← hFM, hstar]
  exact hpos

end OMA.S_mo_465929

namespace OMA.S_mo_465929

open scoped InnerProductSpace

/-- Rotate the input of the second factor until its cross form with the
first factor is symmetric positive semidefinite. -/
theorem exists_polar_cross_alignment {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G H : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) :
    ∃ U : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι,
      (∀ x y, ⟪H (U x), G y⟫_ℝ = ⟪G x, H (U y)⟫_ℝ) ∧
      (∀ x, 0 ≤ ⟪H (U x), G x⟫_ℝ) := by
  obtain ⟨U, hp⟩ := exists_right_positive_rotation (G.adjoint * H)
  refine ⟨U, ?_, ?_⟩
  · intro x y
    rw [← G.adjoint_inner_left y (H (U x)), ← G.adjoint_inner_right x (H (U y))]
    exact hp.isSymmetric x y
  · intro x
    rw [← G.adjoint_inner_left x (H (U x))]
    exact hp.re_inner_nonneg_left x

end OMA.S_mo_465929


open MeasureTheory ProbabilityTheory

namespace OMA.S_mo_465929

/-- Two linearly aligned rows of a Gaussian factor have a single scalar Gaussian
law after taking nonnegative multiples. Zero rows are allowed on either side. -/
theorem comparable_rows_gaussian {d : ℕ} (L M : StrongDual ℝ (EuclideanSpace ℝ (Fin d)))
    (h : (∃ r : ℝ, 0 ≤ r ∧ ∀ z, M z = r * L z) ∨ (∀ z, L z = 0)) :
    ∃ (s t : ℝ) (U : StrongDual ℝ (EuclideanSpace ℝ (Fin d))) (v : NNReal),
      0 ≤ s ∧ 0 ≤ t ∧ (stdGaussian (EuclideanSpace ℝ (Fin d))).map U = gaussianReal 0 v ∧
        (∀ z, L z = s * U z) ∧ (∀ z, M z = t * U z) := by
  have law (U : StrongDual ℝ (EuclideanSpace ℝ (Fin d))) :
      ∃ v : NNReal, (stdGaussian (EuclideanSpace ℝ (Fin d))).map U = gaussianReal 0 v := by
    rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian]
    exact ⟨_, rfl⟩
  rcases h with ⟨r, hr, hM⟩ | hL
  · obtain ⟨v, hv⟩ := law L
    exact ⟨1, r, L, v, zero_le_one, hr, hv, by simp, hM⟩
  · obtain ⟨v, hv⟩ := law M
    exact ⟨0, 1, M, v, le_rfl, zero_le_one, hv, by simpa only [zero_mul] using hL, by simp⟩

end OMA.S_mo_465929
namespace OMA.S_mo_465929

open MeasureTheory ProbabilityTheory

/-- The sharp dimension-free constant in the comparison of centered Gaussian costs. -/
theorem centered_gaussian_transport_comparison {d : ℕ} (μ ν : Measure (E d))
    [IsGaussian μ] [IsGaussian ν] (hμ : (∫ x, x ∂μ) = 0) (hν : (∫ x, x ∂ν) = 0) :
    Real.sqrt (transportCost 2 μ ν) ≤ (Real.sqrt (2 / Real.pi))⁻¹ * transportCost 1 μ ν := by
  obtain ⟨G, hG⟩ := exists_stdGaussian_factor μ hμ
  obtain ⟨H, hH⟩ := exists_stdGaussian_factor ν hν
  obtain ⟨U, hsym, hpos⟩ := exists_polar_cross_alignment G H
  let K := H.comp U.toContinuousLinearEquiv.toContinuousLinearMap
  have hK : (stdGaussian (E d)).map K = ν := (stdGaussian_map_comp_orthogonal H U).trans hH
  obtain ⟨b, hb⟩ := exists_aligned_basis G.toLinearMap K.toLinearMap hsym hpos
  apply comparison_of_aligned_gaussian_factors b G K hG hK
  intro i
  let B := b.toContinuousLinearEquiv.toContinuousLinearMap
  exact comparable_rows_gaussian ((EuclideanSpace.proj i).comp (B.comp G))
    ((EuclideanSpace.proj i).comp (B.comp K)) (hb i)

/-- A dimension-independent comparison, including singular centered Gaussian laws. -/
theorem centered_gaussian_transport_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (μ ν : Measure (E d)),
      IsGaussian μ → IsGaussian ν → (∫ x, x ∂μ) = 0 → (∫ x, x ∂ν) = 0 →
      Real.sqrt (transportCost 2 μ ν) ≤ C * transportCost 1 μ ν := by
  refine ⟨(Real.sqrt (2 / Real.pi))⁻¹, inv_pos.mpr (Real.sqrt_pos.mpr (div_pos (by norm_num) Real.pi_pos)), ?_⟩
  intro d μ ν hGμ hGν hμ hν
  exact centered_gaussian_transport_comparison μ ν hμ hν

end OMA.S_mo_465929

end

section

namespace OMA.S_mo_465929

open MeasureTheory ProbabilityTheory

/-- Transport to a single atom has the same cost under every coupling. -/
theorem transportCost_to_zero {d : ℕ} (μ : Measure (E d)) [IsProbabilityMeasure μ] (p : ℕ) :
    transportCost p μ (Measure.dirac 0) = ∫ x, ‖x‖ ^ p ∂μ := by
  have heq (ρ : Measure (E d × E d)) (h : IsCoupling ρ μ (Measure.dirac 0)) :
      (∫ z, dist z.1 z.2 ^ p ∂ρ) = ∫ x, ‖x‖ ^ p ∂μ := by
    have hz : ∀ᵐ z ∂ρ, z.2 = (0 : E d) := by
      apply (ae_map_iff (f := Prod.snd) measurable_snd.aemeasurable
        (p := fun y : E d ↦ y = 0) (measurableSet_singleton 0)).mp
      rw [h.2]
      simp
    rw [← h.1, integral_map measurable_fst.aemeasurable (by fun_prop)]
    apply integral_congr_ae
    filter_upwards [hz] with z hzero
    simp [hzero]
  apply le_antisymm
  · have hp : IsCoupling (μ.prod (Measure.dirac 0)) μ (Measure.dirac 0) := by
      constructor <;> simp
    exact (transportCost_le_of_coupling p hp).trans_eq (heq _ hp)
  · exact le_transportCost_of_forall p _ (fun ρ hρ ↦ (heq ρ hρ).symm.le)

/-- In the dimension and metric of the registered question, equality is attained
by a standard Gaussian against the zero point mass. -/
theorem one_dimensional_gaussian_attains_constant :
    ∃ μ ν : Measure (E 1), IsGaussian μ ∧ IsGaussian ν ∧
      (∫ x, x ∂μ) = 0 ∧ (∫ x, x ∂ν) = 0 ∧
      transportCost 1 μ ν = Real.sqrt (2 / Real.pi) ∧ transportCost 2 μ ν = 1 := by
  let e := (OrthonormalBasis.singleton (Fin 1) ℝ).repr
  let f := e.toContinuousLinearEquiv.toContinuousLinearMap
  let η := gaussianReal 0 1
  let μ := η.map f
  refine ⟨μ, Measure.dirac 0, inferInstanceAs (IsGaussian (η.map f)), inferInstance, ?_, ?_, ?_, ?_⟩
  · change (∫ x, x ∂η.map f) = 0
    rw [ContinuousLinearMap.integral_id_map IsGaussian.integrable_id]
    simp [η]
  · simp
  · rw [transportCost_to_zero]
    simp only [pow_one]
    change (∫ x, ‖x‖ ∂η.map f) = _
    rw [integral_map f.measurable.aemeasurable (by fun_prop)]
    change (∫ x, ‖e x‖ ∂η) = _
    simp_rw [show ∀ x : ℝ, ‖e x‖ = |x| from fun x ↦ (e.norm_map x).trans (Real.norm_eq_abs x)]
    simpa [η] using abs_moment_gaussianReal_zero 1
  · rw [transportCost_to_zero]
    change (∫ x, ‖x‖ ^ 2 ∂η.map f) = _
    rw [integral_map f.measurable.aemeasurable (by fun_prop)]
    change (∫ x, ‖e x‖ ^ 2 ∂η) = _
    simp_rw [show ∀ x : ℝ, ‖e x‖ = |x| from fun x ↦ (e.norm_map x).trans (Real.norm_eq_abs x), sq_abs]
    have h := variance_fun_id_gaussianReal (μ := 0) (v := 1)
    rw [variance_eq_integral measurable_id'.aemeasurable] at h
    simpa only [η, integral_id_gaussianReal, sub_zero, NNReal.coe_one] using h

/-- Any dimension-uniform constant in the registered comparison is at least the
sharp constant, already forced by a one-dimensional Gaussian law. -/
theorem comparison_constant_lower_bound {C : ℝ}
    (hC : ∀ (d : ℕ) (μ ν : Measure (E d)), IsGaussian μ → IsGaussian ν →
      (∫ x, x ∂μ) = 0 → (∫ x, x ∂ν) = 0 →
      Real.sqrt (transportCost 2 μ ν) ≤ C * transportCost 1 μ ν) :
    Real.sqrt (Real.pi / 2) ≤ C := by
  obtain ⟨μ, ν, hg, hg', hm, hm', ha, hb⟩ := one_dimensional_gaussian_attains_constant
  have h := hC 1 μ ν hg hg' hm hm'
  rw [ha, hb, Real.sqrt_one] at h
  have hk : 0 < Real.sqrt (2 / Real.pi) := Real.sqrt_pos.mpr (by positivity)
  rw [show Real.pi / 2 = (2 / Real.pi)⁻¹ by rw [inv_div], Real.sqrt_inv, ← one_div]
  exact (div_le_iff₀ hk).mpr h

end OMA.S_mo_465929

end

theorem OMA.solution : type_of% @OMA.S_mo_465929.main := by
  exact OMA.S_mo_465929.centered_gaussian_transport_uniform
