import OMAReductions.R_Borsuk_borsuk_conjecture_not_of_nine_le_R1_H1_R1

/-!
Adapted from OpenAI, A nine-dimensional counterexample to Borsuk's covering assertion.
Source: github.com/openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a,
lean/OAI/Geometry/Borsuk, used under Apache-2.0.

The original development passes from a small projector cover to a smooth partition of
unity, then proves purity and incidence of its supports. This port selects the
declarations needed by those arguments and adapts them to the squared-distance cover.
-/
namespace OAI
abbrev Euc (ι : Type*) := EuclideanSpace ℝ ι
abbrev SqMat (ι : Type*) := Matrix ι ι ℝ
abbrev PreComplex (ι : Type*) := PreAbstractSimplicialComplex ι
noncomputable abbrev matrixOp (ι : Type*) [Fintype ι] [DecidableEq ι] := Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)
end OAI

namespace OAI.BorsukNine


section
section
open scoped RealInnerProductSpace ContDiff
open scoped Manifold
open MeasureTheory Set Metric
open scoped ENNReal Pointwise Matrix
section SphereMeasure
variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V]
abbrev UnitSphere := Metric.sphere (0 : V) 1
noncomputable def sphereProbability : Measure (UnitSphere V) :=
  ((volume : Measure V).toSphere Set.univ)⁻¹ • volume.toSphere
instance sphereMeasure_neZero : NeZero ((volume : Measure V).toSphere) := by
  constructor
  exact (Measure.toSphere_eq_zero_iff_finrank volume).not.mpr
    (ne_of_gt (Module.finrank_pos (R := ℝ) (M := V)))
instance sphereProbability_isProbability : IsProbabilityMeasure (sphereProbability V) := by
  unfold sphereProbability
  infer_instance
instance sphereProbability_openPos : (sphereProbability V).IsOpenPosMeasure := by
  unfold sphereProbability
  exact Measure.isOpenPosMeasure_smul volume.toSphere (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _))
variable {V}
noncomputable def sphereRotation (e : V ≃ₗᵢ[ℝ] V) : UnitSphere V ≃ₜ UnitSphere V :=
  e.toHomeomorph.subtype (fun x => by simp only [mem_sphere_zero_iff_norm, LinearIsometryEquiv.coe_toHomeomorph, e.norm_map])
omit [Nontrivial V] in
lemma sphereRotation_preserves_toSphere (e : V ≃ₗᵢ[ℝ] V) :
    MeasurePreserving (sphereRotation e) volume.toSphere volume.toSphere := by
  refine ⟨(sphereRotation e).measurable, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (sphereRotation e).measurable hs,
    Measure.toSphere_apply' _ ((sphereRotation e).measurable hs), Measure.toSphere_apply' _ hs]
  congr 1
  have hset : Ioo (0 : ℝ) 1 • (Subtype.val '' (sphereRotation e ⁻¹' s)) =
      e ⁻¹' (Ioo (0 : ℝ) 1 • (Subtype.val '' s)) := by
    ext x
    constructor
    · rintro ⟨r, hr, v, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨r, hr, e u, ⟨sphereRotation e u, hu, rfl⟩, by simp⟩
    · rintro ⟨r, hr, v, ⟨u, hu, rfl⟩, he⟩
      refine ⟨r, hr, e.symm u, ⟨(sphereRotation e).symm u, ?_, rfl⟩, ?_⟩
      · simpa using hu
      · apply e.injective
        simpa using he
  rw [hset]
  have he := e.measurePreserving.map_eq
  have hm := e.toMeasurableEquiv.measurableEmbedding.map_apply volume
    (Ioo (0 : ℝ) 1 • (Subtype.val '' s))
  simp only [LinearIsometryEquiv.coe_toMeasurableEquiv] at hm
  rw [he] at hm
  exact hm.symm
omit [Nontrivial V] in
lemma sphereRotation_preserves_probability (e : V ≃ₗᵢ[ℝ] V) :
    MeasurePreserving (sphereRotation e) (sphereProbability V) (sphereProbability V) := by
  exact (sphereRotation_preserves_toSphere e).smul_measure _
omit [Nontrivial V] in
lemma integral_sphere_rotation (e : V ≃ₗᵢ[ℝ] V) (g : UnitSphere V → ℝ) :
    (∫ x, g (sphereRotation e x) ∂sphereProbability V) =
      ∫ x, g x ∂sphereProbability V :=
  (sphereRotation_preserves_probability e).integral_comp
    (sphereRotation e).measurableEmbedding g
end SphereMeasure
end
end

section
section
open scoped RealInnerProductSpace ContDiff
open scoped Manifold
open MeasureTheory Set Metric
open scoped ENNReal Pointwise Matrix
section SphereMoments
variable {ι : Type*} [Fintype ι] [Nonempty ι]
lemma sphere_coord_integrable (i j : ι) :
    Integrable (fun x : UnitSphere (Euc ι) => (x : (Euc ι)) i * (x : (Euc ι)) j) (sphereProbability (Euc ι)) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact ((PiLp.continuous_apply 2 _ i).comp continuous_subtype_val).mul
      ((PiLp.continuous_apply 2 _ j).comp continuous_subtype_val)
  · exact HasCompactSupport.of_compactSpace _
omit [Nonempty ι] in
lemma sphere_coord_cross {i j : ι} (hij : i ≠ j) :
    (∫ x : UnitSphere (Euc ι), (x : (Euc ι)) i * (x : (Euc ι)) j ∂sphereProbability (Euc ι)) = 0 := by
  classical
  let e : (Euc ι) ≃ₗᵢ[ℝ] (Euc ι) := LinearIsometryEquiv.piLpCongrRight 2
    (fun k => if k = i then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ)
  have hi := integral_sphere_rotation e (fun x : UnitSphere (Euc ι) => (x : (Euc ι)) i * (x : (Euc ι)) j)
  have he : (fun x : UnitSphere (Euc ι) => (sphereRotation e x : (Euc ι)) i * (sphereRotation e x : (Euc ι)) j) =
      fun x : UnitSphere (Euc ι) => -((x : (Euc ι)) i * (x : (Euc ι)) j) := by
    funext x
    simp [sphereRotation, e, hij.symm]
  rw [he, integral_neg] at hi
  linarith
omit [Nonempty ι] in
lemma sphere_coord_diag_eq (i j : ι) :
    (∫ x : UnitSphere (Euc ι), (x : (Euc ι)) i * (x : (Euc ι)) i ∂sphereProbability (Euc ι)) =
      ∫ x : UnitSphere (Euc ι), (x : (Euc ι)) j * (x : (Euc ι)) j ∂sphereProbability (Euc ι) := by
  classical
  let e : (Euc ι) ≃ₗᵢ[ℝ] (Euc ι) := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i j)
  have hi := integral_sphere_rotation e (fun x : UnitSphere (Euc ι) => (x : (Euc ι)) j * (x : (Euc ι)) j)
  convert hi using 1
  congr 1
  ext x
  simp [sphereRotation, e, Equiv.piCongrLeft']
lemma sphere_coord_diag (i : ι) :
    (∫ x : UnitSphere (Euc ι), (x : (Euc ι)) i * (x : (Euc ι)) i ∂sphereProbability (Euc ι)) =
      (Fintype.card ι : ℝ)⁻¹ := by
  classical
  have hs : (∑ j, ∫ x : UnitSphere (Euc ι), (x : (Euc ι)) j * (x : (Euc ι)) j ∂sphereProbability (Euc ι)) = 1 := by
    rw [← integral_finsetSum _ (fun j _ => sphere_coord_integrable j j)]
    have he : (fun x : UnitSphere (Euc ι) => ∑ j, (x : (Euc ι)) j * (x : (Euc ι)) j) = fun _ => (1 : ℝ) := by
      funext x
      have hn : ‖(x : (Euc ι))‖ = 1 := mem_sphere_zero_iff_norm.mp x.property
      have hh := EuclideanSpace.real_norm_sq_eq (x : (Euc ι))
      rw [hn] at hh
      simpa only [one_pow, pow_two, one_mul] using hh.symm
    rw [he]
    simp
  have hval : (Fintype.card ι : ℝ) *
      (∫ x : UnitSphere (Euc ι), (x : (Euc ι)) i * (x : (Euc ι)) i ∂sphereProbability (Euc ι)) = 1 := by
    rw [← hs]
    rw [Finset.sum_congr rfl (fun j _ => sphere_coord_diag_eq j i)]
    simp
  exact eq_inv_of_mul_eq_one_right hval
lemma sphere_quadratic_integral (A : SqMat ι) :
    (∫ x : UnitSphere (Euc ι), (x : (Euc ι)).ofLp ⬝ᵥ A *ᵥ (x : (Euc ι)).ofLp ∂sphereProbability (Euc ι)) =
      Matrix.trace A * (Fintype.card ι : ℝ)⁻¹ := by
  classical
  have hc (i j : ι) : Integrable (fun x : UnitSphere (Euc ι) =>
      A i j * ((x : (Euc ι)) i * (x : (Euc ι)) j)) (sphereProbability (Euc ι)) :=
    (sphere_coord_integrable i j).const_mul _
  have he : (fun x : UnitSphere (Euc ι) => (x : (Euc ι)).ofLp ⬝ᵥ A *ᵥ (x : (Euc ι)).ofLp) =
      fun x : UnitSphere (Euc ι) => ∑ i, ∑ j, A i j * ((x : (Euc ι)) i * (x : (Euc ι)) j) := by
    funext x
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he, integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hc i j))]
  simp_rw [integral_finsetSum _ (fun j _ => hc _ j), integral_const_mul]
  calc
    _ = ∑ i, A i i * (Fintype.card ι : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_eq_single i]
      · rw [sphere_coord_diag]
      · intro j _ hji
        rw [sphere_coord_cross hji.symm, mul_zero]
      · simp
    _ = _ := by rw [← Finset.sum_mul]; rfl
end SphereMoments
end
end

section
section
abbrev Vector4 := Euc (Fin 4)
abbrev Matrix4 := Euc (Fin 4 × Fin 4)
def projector (u : Vector4) : Matrix4 :=
  WithLp.toLp 2 (fun ij => u ij.1 * u ij.2)
def projectorSet : Set Matrix4 :=
  projector '' {u : Vector4 | ‖u‖ = 1}
def HasTenSmallCover : Prop :=
  ∃ C : Fin 10 → Set Matrix4,
    (∀ i, C i ⊆ projectorSet) ∧
    projectorSet ⊆ ⋃ i, C i ∧
    ∀ i, Metric.diam (C i) < Real.sqrt 2
end
end

section
section
open scoped RealInnerProductSpace ContDiff
@[simp] theorem projector_apply (u : Vector4) (i j : Fin 4) :
    projector u (i, j) = u i * u j := rfl
@[simp] theorem projector_neg (u : Vector4) : projector (-u) = projector u := by
  ext ⟨i, j⟩
  simp [projector]
theorem continuous_projector : Continuous projector := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro ij
  exact (PiLp.continuous_apply 2 _ ij.1).mul (PiLp.continuous_apply 2 _ ij.2)
theorem isCompact_projectorSet : IsCompact projectorSet := by
  have h : {u : Vector4 | ‖u‖ = 1} = Metric.sphere 0 1 := by
    ext u
    simp
  rw [projectorSet, h]
  exact (isCompact_sphere (0 : Vector4) 1).image continuous_projector
theorem projector_inner (u v : Vector4) :
    ⟪projector u, projector v⟫ = ⟪u, v⟫ ^ 2 := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, projector]
  change (∑ ij : Fin 4 × Fin 4, (v ij.1 * v ij.2) * (u ij.1 * u ij.2)) =
    (∑ i : Fin 4, v i * u i) ^ 2
  rw [Fintype.sum_prod_type]
  simp only [pow_two, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring
theorem projector_norm_sq (u : Vector4) : ‖projector u‖ ^ 2 = ‖u‖ ^ 4 := by
  rw [← real_inner_self_eq_norm_sq, projector_inner, real_inner_self_eq_norm_sq]
  ring
theorem projector_dist_sq (u v : Vector4) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    dist (projector u) (projector v) ^ 2 = 2 - 2 * ⟪u, v⟫ ^ 2 := by
  rw [dist_eq_norm, norm_sub_sq_real, projector_norm_sq, projector_norm_sq,
    projector_inner, hu, hv]
  ring
theorem projector_dist_eq_sqrt_two_iff (u v : Vector4)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    dist (projector u) (projector v) = Real.sqrt 2 ↔ ⟪u, v⟫ = 0 := by
  have hd := projector_dist_sq u v hu hv
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  constructor
  · intro h
    rw [h] at hd
    nlinarith [sq_nonneg ⟪u, v⟫]
  · intro h
    rw [h] at hd
    have hn := dist_nonneg (x := projector u) (y := projector v)
    have hp := Real.sqrt_nonneg (2 : ℝ)
    nlinarith
structure Admissible {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {ι : Type*} [Fintype ι] (f : V → ι → ℝ) : Prop where
  smooth : ∀ i, ContDiff ℝ ∞ (fun u => f u i)
  antipodal : ∀ u i, f (-u) i = f u i
  nonneg : ∀ u, ‖u‖ = 1 → ∀ i, 0 ≤ f u i
  sum_one : ∀ u, ‖u‖ = 1 → ∑ i, f u i = 1
  orthogonal : ∀ u v, ‖u‖ = 1 → ‖v‖ = 1 → ⟪u, v⟫ = 0 →
    ∀ i, ¬ (0 < f u i ∧ 0 < f v i)
theorem contDiff_projector : ContDiff ℝ ∞ projector := by
  apply (contDiff_piLp 2).mpr
  intro ij
  exact (contDiff_piLp_apply (p := 2) (i := ij.1)).mul (contDiff_piLp_apply (p := 2) (i := ij.2))
theorem dist_lt_of_mem_thickening_small {C : Set Matrix4}
    (hC : C ⊆ projectorSet) (hd : Metric.diam C < Real.sqrt 2)
    {P Q : Matrix4}
    (hP : P ∈ Metric.thickening ((Real.sqrt 2 - Metric.diam C) / 4) C)
    (hQ : Q ∈ Metric.thickening ((Real.sqrt 2 - Metric.diam C) / 4) C) :
    dist P Q < Real.sqrt 2 := by
  rcases Metric.mem_thickening_iff.mp hP with ⟨p, hp, hPp⟩
  rcases Metric.mem_thickening_iff.mp hQ with ⟨q, hq, hQq⟩
  have hb := isCompact_projectorSet.isBounded.subset hC
  have hpq := Metric.dist_le_diam_of_mem hb hp hq
  have ht : dist P Q ≤ dist P p + dist p q + dist Q q := by
    calc
      dist P Q ≤ dist P p + dist p Q := dist_triangle P p Q
      _ ≤ dist P p + (dist p q + dist q Q) :=
        add_le_add le_rfl (dist_triangle p q Q)
      _ = dist P p + dist p q + dist Q q := by rw [dist_comm q Q]; ring
  linarith
open scoped Manifold
theorem cover_to_admissible (h : HasTenSmallCover) :
    ∃ f : Vector4 → Fin 10 → ℝ, Admissible f := by
  classical
  rcases h with ⟨C, hCX, hcov, hdiam⟩
  let U : Fin 10 → Set Matrix4 := fun i =>
    Metric.thickening ((Real.sqrt 2 - Metric.diam (C i)) / 4) (C i)
  have hU : ∀ i, IsOpen (U i) := fun _ => Metric.isOpen_thickening
  have hCU : ∀ i, C i ⊆ U i := by
    intro i
    apply Metric.self_subset_thickening
    linarith [hdiam i]
  have hXU : projectorSet ⊆ ⋃ i, U i := by
    intro P hP
    rcases Set.mem_iUnion.mp (hcov hP) with ⟨i, hi⟩
    exact Set.mem_iUnion.mpr ⟨i, hCU i hi⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (I := 𝓘(ℝ, Matrix4)) isCompact_projectorSet.isClosed U hU hXU
  refine ⟨fun u i => ρ i (projector u), ?_⟩
  constructor
  · intro i
    exact (contMDiff_iff_contDiff.mp (ρ i).contMDiff).comp contDiff_projector
  · intro u i
    simp
  · intro u _ i
    exact ρ.nonneg i (projector u)
  · intro u hu
    simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (show projector u ∈ projectorSet
      from ⟨u, hu, rfl⟩)
  · intro u v hu hv huv i ⟨hui, hvi⟩
    have huU : projector u ∈ U i := hρ i (subset_tsupport _ (ne_of_gt hui))
    have hvU : projector v ∈ U i := hρ i (subset_tsupport _ (ne_of_gt hvi))
    have hd := dist_lt_of_mem_thickening_small (hCX i) (hdiam i) huU hvU
    rw [(projector_dist_eq_sqrt_two_iff u v hu hv).mpr huv] at hd
    exact lt_irrefl _ hd
noncomputable def positiveSupport {ι : Type*} [Fintype ι]
    {V : Type*} (f : V → ι → ℝ) (u : V) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => 0 < f u i)
@[simp] theorem mem_positiveSupport {ι : Type*} [Fintype ι]
    {V : Type*} (f : V → ι → ℝ) (u : V) (i : ι) :
    i ∈ positiveSupport f u ↔ 0 < f u i := by
  classical
  simp [positiveSupport]
lemma Admissible.support_nonempty {ι : Type*} [Fintype ι]
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {f : V → ι → ℝ} (hf : Admissible f) {u : V} (hu : ‖u‖ = 1) :
    (positiveSupport f u).Nonempty := by
  classical
  have hs : 0 < ∑ i, f u i := by rw [hf.sum_one u hu]; norm_num
  obtain ⟨i, _, hi⟩ := (Finset.sum_pos_iff_of_nonneg (fun i _ => hf.nonneg u hu i)).mp hs
  exact ⟨i, (mem_positiveSupport f u i).mpr hi⟩
lemma Admissible.disjoint_supports {ι : Type*} [Fintype ι]
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {f : V → ι → ℝ} (hf : Admissible f) {u v : V}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (horth : ⟪u, v⟫ = 0) :
    Disjoint (positiveSupport f u) (positiveSupport f v) := by
  classical
  apply Finset.disjoint_left.mpr
  intro i hi hj
  exact hf.orthogonal u v hu hv horth i
    ⟨(mem_positiveSupport f u i).mp hi, (mem_positiveSupport f v i).mp hj⟩
end
end

section
section
open scoped RealInnerProductSpace ContDiff
open scoped Manifold
section HomogeneousLift
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {ι : Type*}
noncomputable def homogeneousLift (f : V → ι → ℝ) (v : V) : ι → ℝ :=
  fun i => ‖v‖ ^ 2 * f ((‖v‖⁻¹ : ℝ) • v) i
@[simp] lemma homogeneousLift_zero (f : V → ι → ℝ) : homogeneousLift f 0 = 0 := by
  ext i
  simp [homogeneousLift]
lemma homogeneousLift_unit (f : V → ι → ℝ) {v : V} (hv : ‖v‖ = 1) :
    homogeneousLift f v = f v := by
  ext i
  simp [homogeneousLift, hv]
variable [Fintype ι]
lemma Admissible.lift_nonneg {f : V → ι → ℝ} (hf : Admissible f) (v : V) (i : ι) :
    0 ≤ homogeneousLift f v i := by
  by_cases hv : v = 0
  · simp [hv]
  · exact mul_nonneg (sq_nonneg _) (hf.nonneg _ (norm_smul_inv_norm (𝕜 := ℝ) hv) i)
lemma Admissible.lift_sum {f : V → ι → ℝ} (hf : Admissible f) (v : V) :
    ∑ i, homogeneousLift f v i = ‖v‖ ^ 2 := by
  classical
  by_cases hv : v = 0
  · simp [hv]
  · simp only [homogeneousLift, ← Finset.mul_sum]
    have hn : ‖(‖v‖⁻¹ : ℝ) • v‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg v))]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)
    rw [hf.sum_one _ hn, mul_one]
lemma Admissible.lift_le {f : V → ι → ℝ} (hf : Admissible f) (v : V) (i : ι) :
    homogeneousLift f v i ≤ ‖v‖ ^ 2 := by
  classical
  rw [← hf.lift_sum v]
  exact Finset.single_le_sum (fun j _ => hf.lift_nonneg v j) (Finset.mem_univ i)
lemma Admissible.lift_norm_le {f : V → ι → ℝ} (hf : Admissible f) (v : V) :
    ‖homogeneousLift f v‖ ≤ ‖v‖ ^ 2 := by
  rw [pi_norm_le_iff_of_nonneg (sq_nonneg _)]
  intro i
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hf.lift_nonneg v i)] using hf.lift_le v i
lemma Admissible.lift_even {f : V → ι → ℝ} (hf : Admissible f) (v : V) :
    homogeneousLift f (-v) = homogeneousLift f v := by
  ext i
  simp [homogeneousLift, smul_neg, hf.antipodal]
omit [Fintype ι] in
lemma homogeneousLift_smul_pos (f : V → ι → ℝ) (v : V) {t : ℝ} (ht : 0 < t) :
    homogeneousLift f (t • v) = t ^ 2 • homogeneousLift f v := by
  ext i
  have he : (‖t • v‖⁻¹ : ℝ) • (t • v) = (‖v‖⁻¹ : ℝ) • v := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht, mul_inv_rev, smul_smul]
    congr 1
    field_simp
  change ‖t • v‖ ^ 2 * f ((‖t • v‖⁻¹ : ℝ) • (t • v)) i = t ^ 2 * (‖v‖ ^ 2 * f ((‖v‖⁻¹ : ℝ) • v) i)
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  ring
omit [Fintype ι] in
lemma homogeneousLift_smul_nonneg (f : V → ι → ℝ) (v : V) {t : ℝ} (ht : 0 ≤ t) :
    homogeneousLift f (t • v) = t ^ 2 • homogeneousLift f v := by
  rcases ht.eq_or_lt with rfl | hp
  · simp
  · exact homogeneousLift_smul_pos f v hp
lemma Admissible.lift_continuous {f : V → ι → ℝ} (hf : Admissible f) :
    Continuous (homogeneousLift f) := by
  apply continuous_iff_continuousAt.mpr
  intro v
  by_cases hv : v = 0
  · subst v
    rw [ContinuousAt, homogeneousLift_zero]
    apply squeeze_zero_norm (fun x => hf.lift_norm_le x)
    have hc : Continuous (fun x : V => ‖x‖ ^ 2) := continuous_norm.pow 2
    simpa using hc.tendsto (0 : V)
  · have hn : ContinuousAt (fun x : V => (‖x‖⁻¹ : ℝ) • x) v :=
      (continuous_norm.continuousAt.inv₀ (norm_ne_zero_iff.mpr hv)).smul continuousAt_id
    apply continuousAt_pi.mpr
    intro i
    exact (continuous_norm.continuousAt.pow 2).mul ((hf.smooth i).continuous.continuousAt.comp hn)
lemma Admissible.lift_orthogonal {f : V → ι → ℝ} (hf : Admissible f)
    {u v : V} (huv : ⟪u, v⟫ = 0) (i : ι) :
    homogeneousLift f u i * homogeneousLift f v i = 0 := by
  by_cases hu : u = 0
  · simp [hu]
  by_cases hv : v = 0
  · simp [hv]
  have hn : ⟪(‖u‖⁻¹ : ℝ) • u, (‖v‖⁻¹ : ℝ) • v⟫ = 0 := by
    simp [inner_smul_left, inner_smul_right, huv]
  have h := hf.orthogonal _ _ (norm_smul_inv_norm (𝕜 := ℝ) hu) (norm_smul_inv_norm (𝕜 := ℝ) hv) hn i
  have hnu := hf.nonneg _ (norm_smul_inv_norm (𝕜 := ℝ) hu) i
  have hnv := hf.nonneg _ (norm_smul_inv_norm (𝕜 := ℝ) hv) i
  have hz : f ((‖u‖⁻¹ : ℝ) • u) i = 0 ∨ f ((‖v‖⁻¹ : ℝ) • v) i = 0 := by
    by_contra hh
    push Not at hh
    exact h ⟨lt_of_le_of_ne hnu (Ne.symm hh.1), lt_of_le_of_ne hnv (Ne.symm hh.2)⟩
  rcases hz with hz | hz <;> simp [homogeneousLift, hz]
end HomogeneousLift
open MeasureTheory Set Metric
open scoped ENNReal Pointwise Matrix
end
end

section
section
open scoped RealInnerProductSpace ContDiff
open scoped Manifold
open MeasureTheory Set Metric
open scoped ENNReal Pointwise Matrix
section IntegralLift
variable {ν ι : Type*} [Fintype ν] [Nonempty ν] [Fintype ι]
noncomputable def integralLift (f : (Euc ν) → ι → ℝ) (T : (Euc ν) →L[ℝ] (Euc ν)) : ι → ℝ :=
  fun i => (Fintype.card ν : ℝ) *
    ∫ x : UnitSphere (Euc ν), homogeneousLift f (T x) i ∂sphereProbability (Euc ν)
omit [Nonempty ν] in
lemma Admissible.integrand_continuous {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    (T : (Euc ν) →L[ℝ] (Euc ν)) (i : ι) :
    Continuous (fun x : UnitSphere (Euc ν) => homogeneousLift f (T x) i) :=
  (continuous_apply i).comp (hf.lift_continuous.comp (T.continuous.comp continuous_subtype_val))
lemma Admissible.integrand_integrable {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    (T : (Euc ν) →L[ℝ] (Euc ν)) (i : ι) :
    Integrable (fun x : UnitSphere (Euc ν) => homogeneousLift f (T x) i) (sphereProbability (Euc ν)) :=
  (hf.integrand_continuous T i).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
omit [Nonempty ν] in
lemma Admissible.integralLift_nonneg {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    (T : (Euc ν) →L[ℝ] (Euc ν)) (i : ι) : 0 ≤ integralLift f T i :=
  mul_nonneg (Nat.cast_nonneg _) (integral_nonneg (fun _ => hf.lift_nonneg _ i))
lemma Admissible.integralLift_sum {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    (T : (Euc ν) →L[ℝ] (Euc ν)) : ∑ i, integralLift f T i =
      (Fintype.card ν : ℝ) * ∫ x : UnitSphere (Euc ν), ‖T x‖ ^ 2 ∂sphereProbability (Euc ν) := by
  classical
  simp only [integralLift, ← Finset.mul_sum]
  rw [← integral_finsetSum _ (fun i _ => hf.integrand_integrable T i)]
  simp only [hf.lift_sum]
lemma Admissible.integralLift_pos_iff_sphere {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    (T : (Euc ν) →L[ℝ] (Euc ν)) (i : ι) :
    0 < integralLift f T i ↔ ∃ x : UnitSphere (Euc ν), 0 < homogeneousLift f (T x) i := by
  have hc : (0 : ℝ) < Fintype.card ν := Nat.cast_pos.mpr Fintype.card_pos
  rw [integralLift, mul_pos_iff_of_pos_left hc]
  constructor
  · intro h
    by_contra hn
    push Not at hn
    have he : (fun x : UnitSphere (Euc ν) => homogeneousLift f (T x) i) = 0 := by
      funext x
      exact le_antisymm (hn x) (hf.lift_nonneg _ i)
    rw [he] at h
    change 0 < ∫ _ : UnitSphere (Euc ν), (0 : ℝ) ∂sphereProbability (Euc ν) at h
    simp only [integral_zero, lt_self_iff_false] at h
  · rintro ⟨x, hx⟩
    exact integral_pos_of_integrable_nonneg_nonzero (hf.integrand_continuous T i)
      (hf.integrand_integrable T i) (fun _ => hf.lift_nonneg _ i) hx.ne'
lemma Admissible.integralLift_continuous {f : (Euc ν) → ι → ℝ} (hf : Admissible f) :
    Continuous (integralLift f) := by
  apply continuous_pi
  intro i
  apply continuous_const.mul
  have hc : Continuous (fun p : ((Euc ν) →L[ℝ] (Euc ν)) × UnitSphere (Euc ν) =>
      homogeneousLift f (p.1 p.2) i) :=
    (continuous_apply i).comp (hf.lift_continuous.comp
      (continuous_fst.clm_apply (continuous_subtype_val.comp continuous_snd)))
  have hi := continuous_parametric_integral_of_continuous
    (μ := sphereProbability (Euc ν))
    (f := fun (T : (Euc ν) →L[ℝ] (Euc ν)) (x : UnitSphere (Euc ν)) => homogeneousLift f (T x) i)
    hc isCompact_univ
  simpa only [setIntegral_univ] using hi
lemma Admissible.integralLift_pos_iff {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    (T : (Euc ν) →L[ℝ] (Euc ν)) (i : ι) :
    0 < integralLift f T i ↔ ∃ x : (Euc ν), 0 < homogeneousLift f (T x) i := by
  rw [hf.integralLift_pos_iff_sphere]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hx
    have hn : 0 < ‖x‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hx0)
    refine ⟨⟨‖x‖⁻¹ • x, mem_sphere_zero_iff_norm.mpr (norm_smul_inv_norm (𝕜 := ℝ) hx0)⟩, ?_⟩
    simp only [map_smul, homogeneousLift_smul_pos f _ hn, Pi.smul_apply, smul_eq_mul]
    exact mul_pos (sq_pos_of_pos hn) hx
lemma Admissible.integralLift_support {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    (T : (Euc ν) →L[ℝ] (Euc ν)) (i : ι) :
    0 < integralLift f T i ↔ ∃ v : (Euc ν),
      v ∈ LinearMap.range T.toLinearMap ∧ ‖v‖ = 1 ∧ 0 < f v i := by
  rw [hf.integralLift_pos_iff]
  constructor
  · rintro ⟨x, hx⟩
    have hx0 : T x ≠ 0 := by
      intro hz
      simp only [hz, homogeneousLift_zero, Pi.zero_apply, lt_self_iff_false] at hx
    refine ⟨‖T x‖⁻¹ • T x, ⟨‖T x‖⁻¹ • x, by simp⟩,
      norm_smul_inv_norm (𝕜 := ℝ) hx0, ?_⟩
    exact (mul_pos_iff_of_pos_left (sq_pos_of_pos (norm_pos_iff.mpr hx0))).mp hx
  · rintro ⟨v, ⟨x, rfl⟩, hv, hx⟩
    refine ⟨x, ?_⟩
    rw [homogeneousLift_unit f (show ‖T x‖ = 1 from hv)]
    exact hx
omit [Nonempty ν] [Fintype ι] in
lemma integralLift_smul_nonneg (f : (Euc ν) → ι → ℝ) (T : (Euc ν) →L[ℝ] (Euc ν))
    {t : ℝ} (ht : 0 ≤ t) : integralLift f (t • T) = t ^ 2 • integralLift f T := by
  ext i
  simp only [integralLift, smul_apply, homogeneousLift_smul_nonneg f _ ht,
    Pi.smul_apply, smul_eq_mul, integral_const_mul]
  ring
end IntegralLift
end
end

section
section
open scoped RealInnerProductSpace ContDiff
open scoped Manifold
open MeasureTheory Set Metric
open scoped ENNReal Pointwise Matrix
section MatrixNorm
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ν : Type*} [Fintype ν] [DecidableEq ν]
lemma matrix_action_norm_sq (A : SqMat ν) (x : (Euc ν)) :
    ‖(matrixOp ν) A x‖ ^ 2 =
      ⟪x, (matrixOp ν) (star A * A) x⟫ := by
  rw [map_mul, map_star]
  change ‖(matrixOp ν) A x‖ ^ 2 =
    ⟪x, (star ((matrixOp ν) A)) ((matrixOp ν) A x)⟫
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
    real_inner_self_eq_norm_sq]
lemma sqrt_action_norm_sq (Q : SqMat ν) (hQ : 0 ≤ Q) (x : (Euc ν)) :
    ‖(matrixOp ν) (CFC.sqrt Q) x‖ ^ 2 = ⟪x, (matrixOp ν) Q x⟫ := by
  rw [matrix_action_norm_sq, (CFC.sqrt_nonneg Q).star_eq, CFC.sqrt_mul_sqrt_self Q hQ]
lemma matrix_sqrt_smul {Q : SqMat ν} (hQ : 0 ≤ Q) {t : ℝ} (ht : 0 ≤ t) :
    CFC.sqrt (t • Q) = Real.sqrt t • CFC.sqrt Q := by
  apply (CFC.sqrt_eq_iff _ _ (smul_nonneg ht hQ)
    (smul_nonneg (Real.sqrt_nonneg _) (CFC.sqrt_nonneg _))).mpr
  rw [smul_mul_smul, CFC.sqrt_mul_sqrt_self Q hQ, Real.mul_self_sqrt ht]
end MatrixNorm
section MatrixRange
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ν : Type*} [Fintype ν] [DecidableEq ν]
lemma matrix_sqrt_range (Q : SqMat ν) (hQ : 0 ≤ Q) :
    LinearMap.range ((matrixOp ν) (CFC.sqrt Q)).toLinearMap = LinearMap.range ((matrixOp ν) Q).toLinearMap := by
  have hs : star ((matrixOp ν) (CFC.sqrt Q)) = (matrixOp ν) (CFC.sqrt Q) := by
    rw [← map_star, (CFC.sqrt_nonneg Q).star_eq]
  have hh := LinearMap.range_adjoint_comp_self ((matrixOp ν) (CFC.sqrt Q)).toLinearMap
  have ha : ((matrixOp ν) (CFC.sqrt Q)).toLinearMap.adjoint = ((matrixOp ν) (CFC.sqrt Q)).toLinearMap := by
    change (ContinuousLinearMap.adjoint ((matrixOp ν) (CFC.sqrt Q))).toLinearMap = _
    rw [← ContinuousLinearMap.star_eq_adjoint, hs]
  rw [ha] at hh
  have hm : ((matrixOp ν) (CFC.sqrt Q)).toLinearMap.comp ((matrixOp ν) (CFC.sqrt Q)).toLinearMap = ((matrixOp ν) Q).toLinearMap := by
    change ((matrixOp ν) (CFC.sqrt Q) * (matrixOp ν) (CFC.sqrt Q)).toLinearMap = _
    rw [← map_mul, CFC.sqrt_mul_sqrt_self Q hQ]
  rw [hm] at hh
  exact hh.symm
end MatrixRange
end
end

section
section
open scoped RealInnerProductSpace ContDiff
open scoped Manifold
open MeasureTheory Set Metric
open scoped ENNReal Pointwise Matrix
section MatrixKernel
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ν : Type*} [Fintype ν] [DecidableEq ν]
lemma matrix_abs_action_norm_sq (A : SqMat ν) (x : (Euc ν)) :
    ‖(matrixOp ν) (CFC.abs A) x‖ ^ 2 = ‖(matrixOp ν) A x‖ ^ 2 := by
  rw [matrix_action_norm_sq, (CFC.abs_nonneg A).star_eq, CFC.abs_mul_abs,
    ← matrix_action_norm_sq]
lemma matrix_abs_kernel {A : SqMat ν} {x : (Euc ν)} (hx : (matrixOp ν) A x = 0) :
    (matrixOp ν) (CFC.abs A) x = 0 := by
  apply norm_eq_zero.mp
  apply sq_eq_zero_iff.mp
  rw [matrix_abs_action_norm_sq, hx, norm_zero, zero_pow (by decide : 2 ≠ 0)]
lemma matrix_parts_kernel {A : SqMat ν} (hA : IsSelfAdjoint A)
    {x : (Euc ν)} (hx : (matrixOp ν) A x = 0) : (matrixOp ν) A⁺ x = 0 ∧ (matrixOp ν) A⁻ x = 0 := by
  have habs := matrix_abs_kernel hx
  constructor
  · have h := congrArg (fun B : SqMat ν => (matrixOp ν) B x) (CFC.abs_add_self A hA)
    have hh : (2 : ℝ) • (matrixOp ν) A⁺ x = 0 := by
      simpa only [map_add, add_apply, two_smul, hx, habs, add_zero] using h.symm
    exact (smul_eq_zero.mp hh).resolve_left (by norm_num)
  · have h := congrArg (fun B : SqMat ν => (matrixOp ν) B x) (CFC.abs_sub_self A hA)
    have hh : (2 : ℝ) • (matrixOp ν) A⁻ x = 0 := by
      simpa only [map_sub, sub_apply, two_smul, hx, habs, sub_zero,
        map_add, add_apply] using h.symm
    exact (smul_eq_zero.mp hh).resolve_left (by norm_num)
lemma matrix_image_orthogonal_kernel {A : SqMat ν} (hA : IsSelfAdjoint A)
    {x : (Euc ν)} (hx : (matrixOp ν) A x = 0) (y : (Euc ν)) : ⟪x, (matrixOp ν) A y⟫ = 0 := by
  rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint,
    ← map_star, hA.star_eq, hx, inner_zero_left]
end MatrixKernel
section PositiveExtension
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι]
noncomputable def positiveExtension (f : (Euc ν) → ι → ℝ) (Q : SqMat ν) : ι → ℝ :=
  integralLift f ((matrixOp ν) (CFC.sqrt Q))
omit [Nonempty ν] in
lemma Admissible.positiveExtension_nonneg {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    (Q : SqMat ν) (i : ι) : 0 ≤ positiveExtension f Q i :=
  hf.integralLift_nonneg _ _
lemma Admissible.positiveExtension_sum {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {Q : SqMat ν} (hQ : 0 ≤ Q) : ∑ i, positiveExtension f Q i = Matrix.trace Q := by
  classical
  rw [positiveExtension, hf.integralLift_sum]
  simp_rw [sqrt_action_norm_sq Q hQ, Matrix.inner_toEuclideanCLM]
  rw [sphere_quadratic_integral]
  have hn : (Fintype.card ν : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt Fintype.card_pos)
  field_simp
lemma Admissible.positiveExtension_continuousOn {f : (Euc ν) → ι → ℝ} (hf : Admissible f) :
    ContinuousOn (positiveExtension f) {Q : SqMat ν | 0 ≤ Q} := by
  have hc : Continuous (fun Q : SqMat ν => (matrixOp ν) Q) :=
    ((matrixOp ν)).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional
  exact hf.integralLift_continuous.comp_continuousOn
    (hc.comp_continuousOn CFC.continuousOn_sqrt)
omit [Nonempty ν] [Fintype ι] in
lemma positiveExtension_smul_nonneg (f : (Euc ν) → ι → ℝ)
    {Q : SqMat ν} (hQ : 0 ≤ Q) {t : ℝ} (ht : 0 ≤ t) :
    positiveExtension f (t • Q) = t • positiveExtension f Q := by
  unfold positiveExtension
  rw [matrix_sqrt_smul hQ ht, map_smul,
    integralLift_smul_nonneg f _ (Real.sqrt_nonneg t), Real.sq_sqrt ht]
lemma Admissible.positiveExtension_support {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {Q : SqMat ν} (hQ : 0 ≤ Q) (i : ι) :
    0 < positiveExtension f Q i ↔ ∃ v : (Euc ν),
      v ∈ LinearMap.range ((matrixOp ν) Q).toLinearMap ∧ ‖v‖ = 1 ∧ 0 < f v i := by
  rw [positiveExtension, hf.integralLift_support, matrix_sqrt_range Q hQ]
end PositiveExtension
end
end

section
section
open scoped RealInnerProductSpace ContDiff
open scoped Manifold
open MeasureTheory Set Metric
open scoped ENNReal Pointwise Matrix
section SignedExtension
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι]
omit [Nonempty ν] in
lemma matrix_images_orthogonal {P N : SqMat ν} (hP : 0 ≤ P) (hPN : P * N = 0)
    (x y : (Euc ν)) : ⟪(matrixOp ν) P x, (matrixOp ν) N y⟫ = 0 := by
  rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint]
  have hs : star ((matrixOp ν) P) = (matrixOp ν) P := by rw [← map_star, hP.star_eq]
  rw [hs]
  change ⟪x, ((matrixOp ν) P * (matrixOp ν) N) y⟫ = 0
  rw [← map_mul, hPN, map_zero]
  simp
lemma Admissible.positiveExtension_orthogonal {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {P N : SqMat ν} (hP : 0 ≤ P) (hN : 0 ≤ N) (hPN : P * N = 0) (i : ι) :
    positiveExtension f P i * positiveExtension f N i = 0 := by
  apply mul_eq_zero.mpr
  by_contra hn
  push Not at hn
  have hp := lt_of_le_of_ne (hf.positiveExtension_nonneg P i) (Ne.symm hn.1)
  have hn' := lt_of_le_of_ne (hf.positiveExtension_nonneg N i) (Ne.symm hn.2)
  obtain ⟨v, ⟨x, rfl⟩, hv, hx⟩ := (hf.positiveExtension_support hP i).mp hp
  obtain ⟨w, ⟨y, rfl⟩, hw, hy⟩ := (hf.positiveExtension_support hN i).mp hn'
  exact hf.orthogonal _ _ hv hw (matrix_images_orthogonal hP hPN x y) i ⟨hx, hy⟩
noncomputable def signedExtension (f : (Euc ν) → ι → ℝ) (A : SqMat ν) : ι → ℝ :=
  positiveExtension f A⁺ - positiveExtension f A⁻
omit [Nonempty ν] [Fintype ι] in
lemma signedExtension_odd (f : (Euc ν) → ι → ℝ) (A : SqMat ν) :
    signedExtension f (-A) = -signedExtension f A := by
  simp [signedExtension, CFC.posPart_neg, CFC.negPart_neg]
lemma Admissible.signedExtension_abs_sum {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {A : SqMat ν} (hA : IsSelfAdjoint A) :
    ∑ i, |signedExtension f A i| = Matrix.trace (CFC.abs A) := by
  classical
  have hcoord (i : ι) : |signedExtension f A i| =
      positiveExtension f A⁺ i + positiveExtension f A⁻ i := by
    have hp := hf.positiveExtension_nonneg A⁺ i
    have hn := hf.positiveExtension_nonneg A⁻ i
    have hprod := hf.positiveExtension_orthogonal (CFC.posPart_nonneg A)
      (CFC.negPart_nonneg A) (CFC.posPart_mul_negPart A) i
    rcases mul_eq_zero.mp hprod with hz | hz
    · simp [signedExtension, hz, abs_of_nonneg hn]
    · simp [signedExtension, hz, abs_of_nonneg hp]
  simp_rw [hcoord]
  rw [Finset.sum_add_distrib, hf.positiveExtension_sum (CFC.posPart_nonneg A),
    hf.positiveExtension_sum (CFC.negPart_nonneg A), ← Matrix.trace_add,
    CFC.posPart_add_negPart A hA]
omit [Nonempty ν] in
lemma matrix_posPart_continuousOn :
    ContinuousOn (fun A : SqMat ν => A⁺) {A | IsSelfAdjoint A} := by
  have hc : Continuous (fun A : SqMat ν => (1 / 2 : ℝ) • (CFC.abs A + A)) :=
    (continuous_const (y := (1 / 2 : ℝ))).smul (CFC.continuous_abs.add continuous_id)
  apply hc.continuousOn.congr
  intro A hA
  change A⁺ = (1 / 2 : ℝ) • (CFC.abs A + A)
  rw [CFC.abs_add_self A hA, two_smul, smul_add]
  module
omit [Nonempty ν] in
lemma matrix_negPart_continuousOn :
    ContinuousOn (fun A : SqMat ν => A⁻) {A | IsSelfAdjoint A} := by
  have hc : Continuous (fun A : SqMat ν => (1 / 2 : ℝ) • (CFC.abs A - A)) :=
    (continuous_const (y := (1 / 2 : ℝ))).smul (CFC.continuous_abs.sub continuous_id)
  apply hc.continuousOn.congr
  intro A hA
  change A⁻ = (1 / 2 : ℝ) • (CFC.abs A - A)
  rw [CFC.abs_sub_self A hA, two_smul, smul_add]
  module
lemma Admissible.signedExtension_continuousOn {f : (Euc ν) → ι → ℝ} (hf : Admissible f) :
    ContinuousOn (signedExtension f) {A : SqMat ν | IsSelfAdjoint A} := by
  apply ContinuousOn.sub
  · exact hf.positiveExtension_continuousOn.comp matrix_posPart_continuousOn
      (fun A _ => CFC.posPart_nonneg A)
  · exact hf.positiveExtension_continuousOn.comp matrix_negPart_continuousOn
      (fun A _ => CFC.negPart_nonneg A)
end SignedExtension
end
end

section
section
open scoped RealInnerProductSpace ContDiff
open scoped Manifold
open MeasureTheory Set Metric
open scoped ENNReal Pointwise Matrix
section FullSupport
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι]
lemma Admissible.positiveExtension_kernel {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {Q : SqMat ν} (hQ : 0 ≤ Q) {w : (Euc ν)} (hw : ‖w‖ = 1)
    (hk : (matrixOp ν) Q w = 0) {i : ι} (hi : 0 < f w i) : positiveExtension f Q i = 0 := by
  apply le_antisymm _ (hf.positiveExtension_nonneg Q i)
  apply le_of_not_gt
  intro hp
  obtain ⟨v, ⟨x, rfl⟩, hv, hx⟩ := (hf.positiveExtension_support hQ i).mp hp
  exact hf.orthogonal _ _ hw hv (matrix_image_orthogonal_kernel hQ.isSelfAdjoint hk x) i
    ⟨hi, hx⟩
lemma Admissible.signedExtension_kernel {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {A : SqMat ν} (hA : IsSelfAdjoint A) {w : (Euc ν)} (hw : ‖w‖ = 1)
    (hk : (matrixOp ν) A w = 0) : ∃ i, signedExtension f A i = 0 := by
  obtain ⟨i, hi⟩ := hf.support_nonempty hw
  have hi' := (mem_positiveSupport f w i).mp hi
  obtain ⟨hp, hn⟩ := matrix_parts_kernel hA hk
  refine ⟨i, ?_⟩
  simp only [signedExtension, Pi.sub_apply,
    hf.positiveExtension_kernel (CFC.posPart_nonneg A) hw hp hi',
    hf.positiveExtension_kernel (CFC.negPart_nonneg A) hw hn hi', sub_self]
lemma Admissible.signedExtension_kernel_eq_zero {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {A : SqMat ν} (hA : IsSelfAdjoint A) (hs : ∀ i, signedExtension f A i ≠ 0)
    {w : (Euc ν)} (hk : (matrixOp ν) A w = 0) : w = 0 := by
  by_contra hw
  have hunit : ‖‖w‖⁻¹ • w‖ = 1 := by simp [norm_smul, norm_inv, hw]
  have hk' : (matrixOp ν) A (‖w‖⁻¹ • w) = 0 := by rw [map_smul, hk, smul_zero]
  obtain ⟨i, hi⟩ := hf.signedExtension_kernel hA hunit hk'
  exact hs i hi
lemma Admissible.signedExtension_fullSupport {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {A : SqMat ν} (hA : IsSelfAdjoint A) (hs : ∀ i, signedExtension f A i ≠ 0) :
    IsUnit A := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro u v huv
  have hz : (matrixOp ν) A (WithLp.toLp 2 u - WithLp.toLp 2 v) = 0 := by
    rw [map_sub, Matrix.toEuclideanCLM_toLp, Matrix.toEuclideanCLM_toLp, huv, sub_self]
  have h := sub_eq_zero.mp (hf.signedExtension_kernel_eq_zero hA hs hz)
  exact WithLp.toLp_injective 2 h
omit [Nonempty ν] in
lemma matrix_psd_trace_zero {Q : SqMat ν} (hQ : 0 ≤ Q)
    (htrace : Matrix.trace Q = 0) : Q = 0 := by
  have hprod : (CFC.sqrt Q)ᴴ * CFC.sqrt Q = Q := by
    rw [← Matrix.star_eq_conjTranspose, (CFC.sqrt_nonneg Q).star_eq, CFC.sqrt_mul_sqrt_self Q hQ]
  have hz : CFC.sqrt Q = 0 := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp
    (hprod.symm ▸ htrace)
  rw [← hprod, hz]
  simp
end FullSupport
end
end

section
section
open scoped RealInnerProductSpace ContDiff
open scoped Manifold
open MeasureTheory Set Metric
open scoped ENNReal Pointwise Matrix
section SphereExtension
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι]
lemma Admissible.signedExtension_eq_zero_iff {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {A : SqMat ν} (hA : IsSelfAdjoint A) : signedExtension f A = 0 ↔ A = 0 := by
  constructor
  · intro hz
    have ht : Matrix.trace (CFC.abs A) = 0 := by
      rw [← hf.signedExtension_abs_sum hA, hz]
      simp
    have habs : CFC.abs A = 0 := matrix_psd_trace_zero (CFC.abs_nonneg A) ht
    have hsq := CFC.abs_mul_abs A
    rw [habs, zero_mul] at hsq
    apply Matrix.conjTranspose_mul_self_eq_zero.mp
    simpa only [Matrix.star_eq_conjTranspose] using hsq.symm
  · rintro rfl
    simp [signedExtension]
noncomputable def normalizedSignedExtension (f : (Euc ν) → ι → ℝ) (A : SqMat ν) :
    Euc ι :=
  ‖WithLp.toLp 2 (signedExtension f A)‖⁻¹ • WithLp.toLp 2 (signedExtension f A)
lemma Admissible.normalizedSignedExtension_norm {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {A : SqMat ν} (hA : IsSelfAdjoint A) (hneq : A ≠ 0) :
    ‖normalizedSignedExtension f A‖ = 1 := by
  have hn : WithLp.toLp 2 (signedExtension f A) ≠ 0 := by
    intro hz
    have hs : signedExtension f A = 0 := WithLp.toLp_injective 2 hz
    exact hneq ((hf.signedExtension_eq_zero_iff hA).mp hs)
  simp [normalizedSignedExtension, norm_smul, norm_inv, hn]
omit [Nonempty ν] in
lemma normalizedSignedExtension_odd (f : (Euc ν) → ι → ℝ) (A : SqMat ν) :
    normalizedSignedExtension f (-A) = -normalizedSignedExtension f A := by
  simp [normalizedSignedExtension, signedExtension_odd, WithLp.toLp_neg]
lemma Admissible.normalizedSignedExtension_continuousOn {f : (Euc ν) → ι → ℝ} (hf : Admissible f) :
    ContinuousOn (normalizedSignedExtension f) {A : SqMat ν | IsSelfAdjoint A ∧ A ≠ 0} := by
  have hc : ContinuousOn (fun A : SqMat ν => WithLp.toLp 2 (signedExtension f A))
      {A | IsSelfAdjoint A ∧ A ≠ 0} :=
    (PiLp.continuous_toLp 2 _).comp_continuousOn
      (hf.signedExtension_continuousOn.mono (fun _ h => h.1))
  apply ContinuousOn.smul (ContinuousOn.inv₀ hc.norm _) hc
  intro A hA
  rw [norm_ne_zero_iff]
  intro hh
  have hs : signedExtension f A = 0 := WithLp.toLp_injective 2 hh
  exact hA.2 ((hf.signedExtension_eq_zero_iff hA.1).mp hs)
end SphereExtension
end
end

section
section
open scoped RealInnerProductSpace ContDiff
open scoped Manifold
open MeasureTheory Set Metric
open scoped ENNReal Pointwise Matrix
section SymmetricCoordinates
variable {ν : Type*} [Fintype ν] [LinearOrder ν]
abbrev UpperTriangle (ν : Type*) [LE ν] := {p : ν × ν // p.1 ≤ p.2}
noncomputable def symmetricCoordinates :
    Euc (UpperTriangle ν) →ₗ[ℝ] SqMat ν where
  toFun x i j := if h : i ≤ j then x ⟨(i,j),h⟩ else x ⟨(j,i),le_of_not_ge h⟩
  map_add' x y := by
    ext i j
    change (if h : i ≤ j then (x+y) ⟨(i,j),h⟩ else (x+y) ⟨(j,i),le_of_not_ge h⟩) =
      (if h : i ≤ j then x ⟨(i,j),h⟩ else x ⟨(j,i),le_of_not_ge h⟩) +
      (if h : i ≤ j then y ⟨(i,j),h⟩ else y ⟨(j,i),le_of_not_ge h⟩)
    split_ifs <;> rfl
  map_smul' t x := by
    ext i j
    change (if h : i ≤ j then (t • x) ⟨(i,j),h⟩ else (t • x) ⟨(j,i),le_of_not_ge h⟩) =
      t * (if h : i ≤ j then x ⟨(i,j),h⟩ else x ⟨(j,i),le_of_not_ge h⟩)
    split_ifs <;> rfl
omit [Fintype ν] in
lemma symmetricCoordinates_upper (x : Euc (UpperTriangle ν))
    (i j : ν) (hij : i ≤ j) : symmetricCoordinates x i j = x ⟨(i,j), hij⟩ := by
  change (if h : i ≤ j then x ⟨(i,j),h⟩ else x ⟨(j,i),le_of_not_ge h⟩) = _
  exact dif_pos hij
omit [Fintype ν] in
lemma symmetricCoordinates_selfAdjoint (x : Euc (UpperTriangle ν)) :
    IsSelfAdjoint (symmetricCoordinates x) := by
  change (symmetricCoordinates x)ᴴ = symmetricCoordinates x
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial]
  change (if h : j ≤ i then x ⟨(j,i),h⟩ else x ⟨(i,j),le_of_not_ge h⟩) =
    (if h : i ≤ j then x ⟨(i,j),h⟩ else x ⟨(j,i),le_of_not_ge h⟩)
  by_cases hij : i ≤ j
  · by_cases hji : j ≤ i
    · have he := le_antisymm hij hji
      subst j
      rfl
    · simp [hij, hji]
  · have hji : j ≤ i := le_of_not_ge hij
    simp [hij, hji]
omit [Fintype ν] in
lemma symmetricCoordinates_injective : Function.Injective (symmetricCoordinates (ν := ν)) := by
  intro x y hxy
  apply PiLp.ext
  intro p
  have h := congrArg (fun A : SqMat ν => A p.val.1 p.val.2) hxy
  simpa only [symmetricCoordinates_upper _ _ _ p.property] using h
end SymmetricCoordinates
end
end

section
section
open scoped RealInnerProductSpace ContDiff
open scoped Manifold
open MeasureTheory Set Metric
open scoped ENNReal Pointwise Matrix
section OddSphereMap
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ν ι : Type*} [Fintype ν] [LinearOrder ν] [Nonempty ν] [Fintype ι]
noncomputable def sphereExtension (f : (Euc ν) → ι → ℝ)
    (x : Euc (UpperTriangle ν)) : Euc ι :=
  normalizedSignedExtension f (symmetricCoordinates x)
lemma Admissible.sphereExtension_norm {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {x : Euc (UpperTriangle ν)} (hx : ‖x‖ = 1) : ‖sphereExtension f x‖ = 1 := by
  apply hf.normalizedSignedExtension_norm (symmetricCoordinates_selfAdjoint x)
  intro hh
  have hn : x = 0 := symmetricCoordinates_injective (hh.trans (map_zero _).symm)
  simp [hn] at hx
omit [Nonempty ν] in
lemma sphereExtension_odd (f : (Euc ν) → ι → ℝ) (x : Euc (UpperTriangle ν)) :
    sphereExtension f (-x) = -sphereExtension f x := by
  simp only [sphereExtension, map_neg, normalizedSignedExtension_odd]
lemma Admissible.sphereExtension_continuousOn {f : (Euc ν) → ι → ℝ} (hf : Admissible f) :
    ContinuousOn (sphereExtension f) {x : Euc (UpperTriangle ν) | ‖x‖ = 1} := by
  apply hf.normalizedSignedExtension_continuousOn.comp
    (symmetricCoordinates.continuous_of_finiteDimensional.continuousOn) (fun x hx => ?_)
  refine ⟨symmetricCoordinates_selfAdjoint x, ?_⟩
  intro hh
  have hn : x = 0 := symmetricCoordinates_injective (hh.trans (map_zero _).symm)
  simp [hn] at hx
end OddSphereMap
end
namespace SmithTheory
variable {K P Q : Type*} [Field K] [AddCommGroup P] [Module K P]
  [AddCommGroup Q] [Module K Q]
lemma exists_factor_of_ker_le (N : P →ₗ[K] P) (φ : P →ₗ[K] Q)
    (h : LinearMap.ker N ≤ LinearMap.ker φ) : ∃ ψ : P →ₗ[K] Q, ψ.comp N = φ := by
  let ψ₀ : LinearMap.range N →ₗ[K] Q :=
    (N.ker.liftQ φ h).comp N.quotKerEquivRange.symm.toLinearMap
  obtain ⟨ψ, hψ⟩ := ψ₀.exists_extend
  refine ⟨ψ, ?_⟩
  ext x
  have he := LinearMap.congr_fun hψ ⟨N x, LinearMap.mem_range_self N x⟩
  simpa only [LinearMap.comp_apply, Submodule.subtype_apply, ψ₀,
    LinearEquiv.coe_toLinearMap, LinearMap.quotKerEquivRange_symm_apply_image,
    Submodule.mkQ_apply, Submodule.liftQ_apply] using he
lemma exists_factor_of_vanish_norm (N : P →ₗ[K] P)
    (hexact : LinearMap.ker N ≤ LinearMap.range N) (φ : P →ₗ[K] Q)
    (hφ : φ.comp N = 0) : ∃ ψ : P →ₗ[K] Q, ψ.comp N = φ := by
  apply exists_factor_of_ker_le N φ
  intro x hx
  obtain ⟨y, rfl⟩ := hexact hx
  exact LinearMap.congr_fun hφ y
lemma tower_augmentation_zero (d N : P →ₗ[K] P)
    (hd : d.comp d = 0) (hcomm : d.comp N = N.comp d)
    (hexact : LinearMap.ker N ≤ LinearMap.range N)
    (n : ℕ) (φ : P →ₗ[K] Q) (hφN : φ.comp N = 0) (hφd : φ.comp d = 0)
    (c : ℕ → P) (htower : ∀ i < n, d (c (i + 1)) = N (c i))
    (htop : N (c n) = 0) : φ (c 0) = 0 := by
  induction n generalizing φ c with
  | zero =>
    obtain ⟨ψ, hψ⟩ := exists_factor_of_vanish_norm N hexact φ hφN
    rw [← hψ, LinearMap.comp_apply, htop, map_zero]
  | succ n ih =>
    obtain ⟨ψ, hψ⟩ := exists_factor_of_vanish_norm N hexact φ hφN
    have hN : (ψ.comp d).comp N = 0 := by
      rw [LinearMap.comp_assoc, hcomm, ← LinearMap.comp_assoc, hψ, hφd]
    have hd' : (ψ.comp d).comp d = 0 := by
      rw [LinearMap.comp_assoc, hd, LinearMap.comp_zero]
    have hh := ih (ψ.comp d) hN hd' (fun i => c (i + 1))
      (fun i hi => htower (i + 1) (Nat.add_lt_add_right hi 1)) htop
    rw [← hψ, LinearMap.comp_apply, ← htower 0 (Nat.zero_lt_succ n)]
    exact hh
end SmithTheory
end

section
namespace SmithTheory
variable {K P Q : Type*} [Field K] [AddCommGroup P] [Module K P]
  [AddCommGroup Q] [Module K Q]
section Involution
variable {ι : Type*}
noncomputable def involutionNorm (τ : ι ≃ ι) :
    (ι →₀ ZMod 2) →ₗ[ZMod 2] (ι →₀ ZMod 2) :=
  LinearMap.id + (Finsupp.domLCongr τ).toLinearMap
lemma involutionNorm_apply (τ : ι ≃ ι) (c : ι →₀ ZMod 2) (a : ι) :
    involutionNorm τ c a = c a + c (τ.symm a) := by
  simp [involutionNorm, Finsupp.domCongr, Finsupp.equivMapDomain_apply]
lemma involutionNorm_exact (τ : ι ≃ ι) (hτ : Function.Involutive τ)
    (hfree : ∀ a, τ a ≠ a) :
    LinearMap.ker (involutionNorm τ) ≤ LinearMap.range (involutionNorm τ) := by
  classical
  let : LinearOrder ι := linearOrderOfSTO WellOrderingRel
  intro c hc
  have ht (a : ι) : τ (τ a) = a := hτ a
  have hsymm (a : ι) : τ.symm a = τ a := by
    apply τ.injective
    rw [τ.apply_symm_apply, ht]
  have heq (a : ι) : c (τ a) = c a := by
    have h := congrArg (fun b : ι →₀ ZMod 2 => b a) hc
    simp only [involutionNorm_apply, Finsupp.zero_apply, hsymm] at h
    have hh := eq_neg_of_add_eq_zero_right h
    rwa [CharTwo.neg_eq] at hh
  refine ⟨c.filter (fun a => a < τ a), ?_⟩
  ext a
  rw [involutionNorm_apply, hsymm]
  simp only [Finsupp.filter_apply, ht]
  by_cases ha : a < τ a
  · simp [ha, not_lt_of_gt ha]
  · have hb : τ a < a := lt_of_le_of_ne (le_of_not_gt ha) (hfree a)
    simp [ha, hb, heq]
lemma involutionNorm_sq (τ : ι ≃ ι) (hτ : Function.Involutive τ) :
    (involutionNorm τ).comp (involutionNorm τ) = 0 := by
  apply LinearMap.ext
  intro c
  apply Finsupp.ext
  intro a
  have ht (a : ι) : τ (τ a) = a := hτ a
  have hsymm (a : ι) : τ.symm a = τ a := by
    apply τ.injective
    rw [τ.apply_symm_apply, ht]
  simp only [LinearMap.comp_apply, involutionNorm_apply, hsymm, ht,
    LinearMap.zero_apply, Finsupp.zero_apply]
  simp [add_comm, CharTwo.add_self_eq_zero]
end Involution
end SmithTheory
end

section
namespace SimplicialChains
open Finset
variable {V : Type*} [DecidableEq V]
abbrev F₂ := ZMod 2
abbrev Chain (K : PreComplex V) := {s : Finset V // s ∈ K} →₀ F₂
noncomputable def simplex (K : PreComplex V) (s : Finset V) : Chain K := by
  classical
  exact if h : s ∈ K then Finsupp.single ⟨s, h⟩ 1 else 0
omit [DecidableEq V] in
lemma simplex_of_mem (K : PreComplex V) {s : Finset V} (hs : s ∈ K) :
    simplex K s = Finsupp.single ⟨s, hs⟩ 1 := by simp [simplex, hs]
omit [DecidableEq V] in
@[simp] lemma simplex_empty (K : PreComplex V) : simplex K ∅ = 0 := by
  have h : (∅ : Finset V) ∉ K := fun h => (K.isRelLowerSet_faces h).1.ne_empty rfl
  simp [simplex, h]
noncomputable def boundary (K : PreComplex V) : Chain K →ₗ[F₂] Chain K := by
  classical
  exact Finsupp.linearCombination F₂ (fun s => ∑ a ∈ s.val, simplex K (s.val.erase a))
lemma boundary_simplex (K : PreComplex V) {s : Finset V} (hs : s ∈ K) :
    boundary K (simplex K s) = ∑ a ∈ s, simplex K (s.erase a) := by
  classical
  simp [simplex_of_mem K hs, boundary, Finsupp.linearCombination_single]
lemma boundary_simplex_subset (K : PreComplex V)
    {s t : Finset V} (ht : t ∈ K) (hs : s ⊆ t) :
    boundary K (simplex K s) = ∑ a ∈ s, simplex K (s.erase a) := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hn
  · simp
  · exact boundary_simplex K ((K.isRelLowerSet_faces ht).2 hs hn)
omit [DecidableEq V] in
lemma chain_add_self (K : PreComplex V) (c : Chain K) : c + c = 0 := by
  ext s
  exact CharTwo.add_self_eq_zero _
lemma double_erase_sum (K : PreComplex V) (s : Finset V) :
    (∑ a ∈ s, ∑ b ∈ s.erase a, simplex K ((s.erase a).erase b)) = 0 := by
  classical
  let g (p : V × V) : Chain K := if p.1 = p.2 then 0 else simplex K ((s.erase p.1).erase p.2)
  have hg : (∑ a ∈ s, ∑ b ∈ s.erase a, simplex K ((s.erase a).erase b)) =
      ∑ p ∈ s ×ˢ s, g p := by
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro a _ha
    rw [← Finset.filter_ne, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro b _hb
    by_cases hab : a = b <;> simp [g, hab, Finset.filter_ne]
  rw [hg]
  apply Finset.sum_involution (fun p _ => p.swap)
  · intro p hp
    dsimp [g]
    by_cases he : p.1 = p.2
    · simp [he]
    · simp only [he, ite_false, Ne.symm he, Finset.erase_right_comm]
      exact chain_add_self K _
  · intro p hp hg he
    have h : p.1 = p.2 := congrArg Prod.snd he
    exact hg (by simp [g, h])
  · intro p hp
    exact Prod.swap_swap p
  · intro p hp
    exact Finset.mem_product.mpr (And.symm (Finset.mem_product.mp hp))
lemma boundary_twice_simplex (K : PreComplex V)
    {s : Finset V} (hs : s ∈ K) : boundary K (boundary K (simplex K s)) = 0 := by
  classical
  rw [boundary_simplex K hs, map_sum]
  have h (a : V) : boundary K (simplex K (s.erase a)) =
      ∑ b ∈ s.erase a, simplex K ((s.erase a).erase b) :=
    boundary_simplex_subset K hs (Finset.erase_subset a s)
  simp_rw [h]
  exact double_erase_sum K s
lemma boundary_sq (K : PreComplex V) :
    (boundary K).comp (boundary K) = 0 := by
  apply Finsupp.lhom_ext
  intro s r
  have hs := boundary_twice_simplex K s.property
  rw [simplex_of_mem K s.property] at hs
  have he : Finsupp.single s r = r • Finsupp.single s (1 : F₂) := by simp
  simp only [LinearMap.comp_apply, he, map_smul, hs, smul_zero, LinearMap.zero_apply]
noncomputable def augmentation (K : PreComplex V) : Chain K →ₗ[F₂] F₂ :=
  Finsupp.linearCombination F₂ (fun s => if s.val.card = 1 then 1 else 0)
omit [DecidableEq V] in
lemma augmentation_simplex (K : PreComplex V) {s : Finset V} (hs : s ∈ K) :
    augmentation K (simplex K s) = if s.card = 1 then 1 else 0 := by
  simp [simplex_of_mem K hs, augmentation, Finsupp.linearCombination_single]
omit [DecidableEq V] in
lemma augmentation_simplex_subset (K : PreComplex V)
    {s t : Finset V} (ht : t ∈ K) (hs : s ⊆ t) :
    augmentation K (simplex K s) = if s.card = 1 then 1 else 0 := by
  rcases s.eq_empty_or_nonempty with rfl | hn
  · simp
  · exact augmentation_simplex K ((K.isRelLowerSet_faces ht).2 hs hn)
lemma augmentation_boundary_simplex (K : PreComplex V)
    {s : Finset V} (hs : s ∈ K) : augmentation K (boundary K (simplex K s)) = 0 := by
  classical
  rw [boundary_simplex K hs, map_sum]
  have hh (a : V) (ha : a ∈ s) : augmentation K (simplex K (s.erase a)) =
      if s.card = 2 then 1 else 0 := by
    rw [augmentation_simplex_subset K hs (Finset.erase_subset a s), Finset.card_erase_of_mem ha]
    have hc : s.card - 1 = 1 ↔ s.card = 2 := by omega
    simp only [hc]
  rw [Finset.sum_congr rfl hh]
  by_cases hc : s.card = 2
  · simpa [hc] using (show (2 : F₂) = 0 by decide)
  · simp [hc]
lemma augmentation_boundary (K : PreComplex V) :
    (augmentation K).comp (boundary K) = 0 := by
  apply Finsupp.lhom_ext
  intro s r
  have hs := augmentation_boundary_simplex K s.property
  rw [simplex_of_mem K s.property] at hs
  have he : Finsupp.single s r = r • Finsupp.single s (1 : F₂) := by simp
  simp only [LinearMap.comp_apply, he, map_smul, hs, smul_zero, LinearMap.zero_apply]
end SimplicialChains
end

section
namespace SimplicialChains
open Finset
variable {V : Type*} [DecidableEq V]
section Maps
variable {W : Type*} [DecidableEq W]
noncomputable def mapSimplex (L : PreComplex W) (f : V → W)
    (s : Finset V) : Chain L :=
  if (s.image f).card = s.card then simplex L (s.image f) else 0
omit [DecidableEq V] in
@[simp] lemma mapSimplex_empty (L : PreComplex W) (f : V → W) :
    mapSimplex L f ∅ = 0 := by simp [mapSimplex]
noncomputable def mapChains (K : PreComplex V)
    (L : PreComplex W) (f : V → W) : Chain K →ₗ[F₂] Chain L :=
  Finsupp.linearCombination F₂ (fun s => mapSimplex L f s.val)
omit [DecidableEq V] in
lemma mapChains_simplex (K : PreComplex V)
    (L : PreComplex W) (f : V → W)
    {s : Finset V} (hs : s ∈ K) : mapChains K L f (simplex K s) = mapSimplex L f s := by
  simp [simplex_of_mem K hs, mapChains, Finsupp.linearCombination_single]
omit [DecidableEq V] in
lemma mapChains_simplex_subset (K : PreComplex V)
    (L : PreComplex W) (f : V → W)
    {s t : Finset V} (ht : t ∈ K) (hs : s ⊆ t) :
    mapChains K L f (simplex K s) = mapSimplex L f s := by
  rcases s.eq_empty_or_nonempty with rfl | hn
  · simp
  · exact mapChains_simplex K L f ((K.isRelLowerSet_faces ht).2 hs hn)
lemma image_erase_of_injOn (f : V → W) (s : Finset V) (h : Set.InjOn f s)
    {a : V} (ha : a ∈ s) : (s.erase a).image f = (s.image f).erase (f a) := by
  ext b
  constructor
  · intro hb
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hb
    apply Finset.mem_erase.mpr
    constructor
    · intro he
      exact (Finset.mem_erase.mp hx).1 (h (Finset.mem_of_mem_erase hx) ha he)
    · exact Finset.mem_image_of_mem f (Finset.mem_of_mem_erase hx)
  · intro hb
    obtain ⟨hne, hb⟩ := Finset.mem_erase.mp hb
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hb
    exact Finset.mem_image.mpr ⟨x, Finset.mem_erase.mpr ⟨fun he => hne (congrArg f he), hx⟩, rfl⟩
lemma image_erase_collision (f : V → W) (s : Finset V) {a b : V}
    (hb : b ∈ s) (hne : a ≠ b) (he : f a = f b) : (s.erase a).image f = s.image f := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_image_of_mem f (Finset.mem_of_mem_erase hx)
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    by_cases ha : x = a
    · subst x
      exact Finset.mem_image.mpr ⟨b, Finset.mem_erase.mpr ⟨Ne.symm hne, hb⟩, he.symm⟩
    · exact Finset.mem_image.mpr ⟨x, Finset.mem_erase.mpr ⟨ha, hx⟩, rfl⟩
lemma mapSimplex_boundary_degenerate (L : PreComplex W)
    (f : V → W) (s : Finset V) (h : ¬ Set.InjOn f s) :
    (∑ a ∈ s, mapSimplex L f (s.erase a)) = 0 := by
  classical
  change ¬ ∀ a ∈ s, ∀ b ∈ s, f a = f b → a = b at h
  push Not at h
  obtain ⟨a, ha, b, hb, he, hne⟩ := h
  rw [Finset.sum_eq_add a b hne]
  · have hima := image_erase_collision f s hb hne he
    have himb := image_erase_collision f s ha hne.symm he.symm
    have hc : mapSimplex L f (s.erase a) = mapSimplex L f (s.erase b) := by
      simp only [mapSimplex, hima, himb, Finset.card_erase_of_mem ha, Finset.card_erase_of_mem hb]
    rw [hc]
    exact chain_add_self L _
  · intro c hc hca
    have hn : ¬ Set.InjOn f (s.erase c) := by
      intro hinj
      exact hne (hinj (Finset.mem_erase.mpr ⟨Ne.symm hca.1, ha⟩)
        (Finset.mem_erase.mpr ⟨Ne.symm hca.2, hb⟩) he)
    simp only [mapSimplex, Finset.card_image_iff, if_neg hn]
  · exact fun hn => (hn ha).elim
  · exact fun hn => (hn hb).elim
lemma mapChains_boundary_simplex (K : PreComplex V)
    (L : PreComplex W) (f : V → W)
    (hf : ∀ s ∈ K, s.image f ∈ L) {s : Finset V} (hs : s ∈ K) :
    boundary L (mapChains K L f (simplex K s)) =
      mapChains K L f (boundary K (simplex K s)) := by
  rw [mapChains_simplex K L f hs, boundary_simplex K hs, map_sum]
  have h (a : V) : mapChains K L f (simplex K (s.erase a)) = mapSimplex L f (s.erase a) :=
    mapChains_simplex_subset K L f hs (Finset.erase_subset a s)
  simp_rw [h]
  by_cases hinj : Set.InjOn f s
  · rw [mapSimplex, if_pos (Finset.card_image_iff.mpr hinj), boundary_simplex L (hf s hs)]
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro a ha
      have hj : Set.InjOn f (s.erase a) := hinj.mono (Finset.erase_subset a s)
      rw [mapSimplex, if_pos (Finset.card_image_iff.mpr hj), image_erase_of_injOn f s hinj ha]
    · exact hinj
  · rw [mapSimplex, if_neg (mt Finset.card_image_iff.mp hinj), map_zero,
      mapSimplex_boundary_degenerate L f s hinj]
lemma mapChains_boundary (K : PreComplex V)
    (L : PreComplex W) (f : V → W)
    (hf : ∀ s ∈ K, s.image f ∈ L) :
    (boundary L).comp (mapChains K L f) = (mapChains K L f).comp (boundary K) := by
  apply Finsupp.lhom_ext
  intro s r
  have hs := mapChains_boundary_simplex K L f hf s.property
  rw [simplex_of_mem K s.property] at hs
  have he : Finsupp.single s r = r • Finsupp.single s (1 : F₂) := by simp
  simp only [LinearMap.comp_apply, he, map_smul, hs]
omit [DecidableEq V] in
lemma mapChains_augmentation_simplex (K : PreComplex V)
    (L : PreComplex W) (f : V → W)
    (hf : ∀ s ∈ K, s.image f ∈ L) {s : Finset V} (hs : s ∈ K) :
    augmentation L (mapChains K L f (simplex K s)) = augmentation K (simplex K s) := by
  rw [mapChains_simplex K L f hs, augmentation_simplex K hs]
  by_cases hcard : (s.image f).card = s.card
  · rw [mapSimplex, if_pos hcard, augmentation_simplex L (hf s hs), hcard]
  · have hne : s.card ≠ 1 := by
      intro hc
      obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hc
      simp at hcard
    simp [mapSimplex, hcard, hne]
omit [DecidableEq V] in
lemma mapChains_augmentation (K : PreComplex V)
    (L : PreComplex W) (f : V → W)
    (hf : ∀ s ∈ K, s.image f ∈ L) :
    (augmentation L).comp (mapChains K L f) = augmentation K := by
  apply Finsupp.lhom_ext
  intro s r
  have hs := mapChains_augmentation_simplex K L f hf s.property
  rw [simplex_of_mem K s.property] at hs
  have he : Finsupp.single s r = r • Finsupp.single s (1 : F₂) := by simp
  simp only [LinearMap.comp_apply, he, map_smul, hs]
end Maps
end SimplicialChains
end

section
namespace SimplicialChains
open Finset
variable {V : Type*} [DecidableEq V]
section Equivariance
variable (K : PreComplex V) (e : V ≃ V)
    (he : ∀ s, s ∈ K ↔ s.image e ∈ K)
noncomputable def faceEquiv : {s : Finset V // s ∈ K} ≃ {s : Finset V // s ∈ K} where
  toFun s := ⟨s.val.image e, (he s.val).mp s.property⟩
  invFun s := ⟨s.val.image e.symm, (he _).mpr (by simp [Finset.image_image, s.property])⟩
  left_inv s := Subtype.ext (by simp [Finset.image_image])
  right_inv s := Subtype.ext (by simp [Finset.image_image])
lemma faceEquiv_involutive (hi : Function.Involutive e) :
    Function.Involutive (faceEquiv K e he) := by
  intro s
  apply Subtype.ext
  change (s.val.image e).image e = s.val
  rw [Finset.image_image]
  have h : e ∘ e = id := funext hi
  rw [h, Finset.image_id]
lemma faceEquiv_free (hf : ∀ s ∈ K, s.image e ≠ s) :
    ∀ s, faceEquiv K e he s ≠ s := by
  intro s hh
  exact hf s.val s.property (congrArg Subtype.val hh)
lemma mapChains_equiv :
    mapChains K K e = (Finsupp.domLCongr (faceEquiv K e he)).toLinearMap := by
  apply Finsupp.lhom_ext
  intro s r
  have hc : (s.val.image e).card = s.val.card := Finset.card_image_iff.mpr e.injective.injOn
  simp only [mapChains, Finsupp.linearCombination_single, mapSimplex, if_pos hc,
    simplex_of_mem K ((he s.val).mp s.property), LinearEquiv.coe_toLinearMap,
    Finsupp.domLCongr_single, Finsupp.smul_single, smul_eq_mul, mul_one]
  rfl
end Equivariance
section Cone
noncomputable def cone (K : PreComplex V) (a : V) : Chain K →ₗ[F₂] Chain K :=
  Finsupp.linearCombination F₂ (fun s => if a ∈ s.val then 0 else simplex K (insert a s.val))
lemma cone_simplex (K : PreComplex V) (a : V) {s : Finset V} (hs : s ∈ K) :
    cone K a (simplex K s) = if a ∈ s then 0 else simplex K (insert a s) := by
  simp [simplex_of_mem K hs, cone, Finsupp.linearCombination_single]
lemma cone_boundary_simplex (K : PreComplex V) (a : V)
    {s : Finset V} (hs : s ∈ K) (hinsert : insert a s ∈ K) (ha : a ∉ s) :
    boundary K (cone K a (simplex K s)) = simplex K s + cone K a (boundary K (simplex K s)) +
      augmentation K (simplex K s) • simplex K {a} := by
  classical
  by_cases hc : s.card = 1
  · obtain ⟨b, rfl⟩ := Finset.card_eq_one.mp hc
    have hab : a ≠ b := by simpa using ha
    have hs' : ({a} : Finset V) ∈ K :=
      (K.isRelLowerSet_faces hinsert).2 (by simp) (Finset.singleton_nonempty a)
    rw [cone_simplex K a hs, if_neg ha, boundary_simplex K hinsert,
      boundary_simplex K hs, augmentation_simplex K hs]
    simp [ha, Finset.erase_insert_of_ne hab]
  · have hn : s.Nonempty := (K.isRelLowerSet_faces hs).1
    have hc' : 2 ≤ s.card := by have := hn.card_pos; omega
    have he (b : V) (hb : b ∈ s) : (s.erase b).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem hb]
      omega
    have heK (b : V) (hb : b ∈ s) : s.erase b ∈ K :=
      (K.isRelLowerSet_faces hs).2 (Finset.erase_subset b s) (he b hb)
    rw [cone_simplex K a hs, if_neg ha, boundary_simplex K hinsert,
      augmentation_simplex K hs, if_neg hc, zero_smul, add_zero,
      boundary_simplex K hs, map_sum, Finset.sum_insert ha, Finset.erase_insert ha]
    apply congrArg (fun z => simplex K s + z)
    apply Finset.sum_congr rfl
    intro b hb
    have hab : a ≠ b := by intro hh; subst b; exact ha hb
    have hn : a ∉ s.erase b := fun hh => ha (Finset.mem_of_mem_erase hh)
    rw [cone_simplex K a (heK b hb), if_neg hn, Finset.erase_insert_of_ne hab]
lemma cone_boundary_simplex_all (K : PreComplex V) (a : V)
    {s : Finset V} (hs : s ∈ K) (hinsert : insert a s ∈ K) :
    boundary K (cone K a (simplex K s)) = simplex K s + cone K a (boundary K (simplex K s)) +
      augmentation K (simplex K s) • simplex K {a} := by
  classical
  by_cases ha : a ∈ s
  · by_cases hc : s.card = 1
    · obtain ⟨b, rfl⟩ := Finset.card_eq_one.mp hc
      have hab : a = b := Finset.mem_singleton.mp ha
      subst b
      rw [cone_simplex K a hs, if_pos ha, map_zero, boundary_simplex K hs,
        augmentation_simplex K hs]
      simp [chain_add_self]
    · have hcn (b : V) (hb : b ∈ s) : (s.erase b).Nonempty := by
        have hn := (K.isRelLowerSet_faces hs).1.card_pos
        rw [← Finset.card_pos, Finset.card_erase_of_mem hb]
        omega
      have hcon : cone K a (boundary K (simplex K s)) = simplex K s := by
        rw [boundary_simplex K hs, map_sum]
        rw [Finset.sum_eq_single a]
        · rw [cone_simplex K a ((K.isRelLowerSet_faces hs).2 (Finset.erase_subset a s) (hcn a ha))]
          simp [Finset.insert_erase ha]
        · intro b hb hba
          rw [cone_simplex K a ((K.isRelLowerSet_faces hs).2 (Finset.erase_subset b s) (hcn b hb))]
          simp [Finset.mem_erase.mpr ⟨Ne.symm hba, ha⟩]
        · exact fun hn => False.elim (hn ha)
      rw [cone_simplex K a hs, if_pos ha, map_zero, hcon,
        augmentation_simplex K hs, if_neg hc, zero_smul, add_zero, chain_add_self]
  · exact cone_boundary_simplex K a hs hinsert ha
omit [DecidableEq V] in
lemma chain_eq_sum (K : PreComplex V) (c : Chain K) :
    c = ∑ s ∈ c.support, c s • simplex K s.val := by
  conv_lhs => rw [← c.sum_single]
  simp [Finsupp.sum, simplex_of_mem K, Finsupp.smul_single]
lemma cone_boundary (K : PreComplex V) (a : V) (c : Chain K)
    (hc : ∀ s ∈ c.support, insert a s.val ∈ K) :
    boundary K (cone K a c) = c + cone K a (boundary K c) +
      augmentation K c • simplex K {a} := by
  classical
  conv_lhs => rw [chain_eq_sum K c]
  rw [map_sum, map_sum]
  have he (s : { s : Finset V // s ∈ K }) (hs : s ∈ c.support) :
      boundary K (cone K a (c s • simplex K s.val)) =
        c s • simplex K s.val + cone K a (boundary K (c s • simplex K s.val)) +
        augmentation K (c s • simplex K s.val) • simplex K {a} := by
    rw [map_smul, map_smul, cone_boundary_simplex_all K a s.property (hc s hs)]
    simp only [smul_add, map_smul, smul_smul, smul_eq_mul]
  rw [Finset.sum_congr rfl he, Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [← map_sum, ← map_sum, ← Finset.sum_smul, ← map_sum, ← chain_eq_sum K c]
end Cone
end SimplicialChains
end

section
namespace SimplicialChains
open Finset
variable {V W : Type*} [DecidableEq V] [DecidableEq W]
noncomputable def normMap (K : PreComplex V) (e : V ≃ V) :
    Chain K →ₗ[F₂] Chain K := LinearMap.id + mapChains K K e
lemma normMap_eq (K : PreComplex V) (e : V ≃ V)
    (he : ∀ s, s ∈ K ↔ s.image e ∈ K) :
    normMap K e = SmithTheory.involutionNorm (faceEquiv K e he) := by
  unfold normMap SmithTheory.involutionNorm
  rw [mapChains_equiv K e he]
lemma boundary_normMap (K : PreComplex V) (e : V ≃ V)
    (he : ∀ s ∈ K, s.image e ∈ K) :
    (boundary K).comp (normMap K e) = (normMap K e).comp (boundary K) := by
  unfold normMap
  rw [LinearMap.comp_add, LinearMap.add_comp, LinearMap.comp_id, LinearMap.id_comp,
    mapChains_boundary K K e he]
lemma augmentation_normMap (K : PreComplex V) (e : V ≃ V)
    (he : ∀ s ∈ K, s.image e ∈ K) :
    (augmentation K).comp (normMap K e) = 0 := by
  unfold normMap
  rw [LinearMap.comp_add, LinearMap.comp_id, mapChains_augmentation K K e he]
  ext c
  exact CharTwo.add_self_eq_zero _
lemma antipodal_tower_augmentation_zero (K : PreComplex V)
    (e : V ≃ V) (he : ∀ s, s ∈ K ↔ s.image e ∈ K) (hi : Function.Involutive e)
    (hfree : ∀ s ∈ K, s.image e ≠ s)
    (n : ℕ) (c : ℕ → Chain K)
    (htower : ∀ i < n, boundary K (c (i+1)) = normMap K e (c i))
    (htop : normMap K e (c n) = 0) : augmentation K (c 0) = 0 := by
  apply SmithTheory.tower_augmentation_zero (boundary K) (normMap K e)
    (boundary_sq K) (boundary_normMap K e (fun s hs => (he s).mp hs))
    _ n (augmentation K) (augmentation_normMap K e (fun s hs => (he s).mp hs))
    (augmentation_boundary K) c htower htop
  rw [normMap_eq K e he]
  exact SmithTheory.involutionNorm_exact _ (faceEquiv_involutive K e he hi)
    (faceEquiv_free K e he hfree)
noncomputable def degreeChains (K : PreComplex V) (d : ℕ) :
    Submodule F₂ (Chain K) := Finsupp.supported F₂ F₂ {s | s.val.card = d}
omit [DecidableEq V] in
lemma simplex_mem_degree (K : PreComplex V) {s : Finset V}
    (hs : s ∈ K) : simplex K s ∈ degreeChains K s.card := by
  rw [simplex_of_mem K hs]
  exact Finsupp.single_mem_supported _ _ rfl
omit [DecidableEq V] [DecidableEq W] in
lemma grade_map (K : PreComplex V) (L : PreComplex W)
    (T : Chain K →ₗ[F₂] Chain L) (d e : ℕ)
    (hT : ∀ s ∈ K, s.card = d → T (simplex K s) ∈ degreeChains L e) :
    degreeChains K d ≤ (degreeChains L e).comap T := by
  rw [degreeChains, Finsupp.supported_eq_span_single]
  apply Submodule.span_le.mpr
  rintro _ ⟨s, hs, rfl⟩
  change T (Finsupp.single s 1) ∈ degreeChains L e
  rw [← simplex_of_mem K s.property]
  exact hT s.val s.property hs
omit [DecidableEq V] in
lemma mapChains_degree (K : PreComplex V) (L : PreComplex W)
    (f : V → W) (hf : ∀ s ∈ K, s.image f ∈ L) (d : ℕ) :
    degreeChains K d ≤ (degreeChains L d).comap (mapChains K L f) := by
  apply grade_map K L _ d d
  intro s hs hd
  rw [mapChains_simplex K L f hs, mapSimplex]
  split_ifs with hh
  · rw [← hd, ← hh]
    exact simplex_mem_degree L (hf s hs)
  · exact Submodule.zero_mem _
omit [DecidableEq V] in
lemma degreeChains_eq_bot_of_card_bound (K : PreComplex V) (d : ℕ)
    (hK : ∀ s ∈ K, s.card < d) : degreeChains K d = ⊥ := by
  apply eq_bot_iff.mpr
  intro c hc
  apply Finsupp.ext
  intro s
  have hne : s.val.card ≠ d := ne_of_lt (hK s.val s.property)
  exact (Finsupp.mem_supported' F₂ c).mp hc s hne
omit [DecidableEq V] in
lemma augmentation_eq_zero_of_degree (K : PreComplex V) (d : ℕ)
    (hd : d ≠ 1) {c : Chain K} (hc : c ∈ degreeChains K d) : augmentation K c = 0 := by
  have hle : degreeChains K d ≤ LinearMap.ker (augmentation K) := by
    rw [degreeChains, Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨s, hs, rfl⟩
    change augmentation K (Finsupp.single s 1) = 0
    rw [← simplex_of_mem K s.property, augmentation_simplex K s.property]
    simp [show s.val.card ≠ 1 by simpa only [Set.mem_ofPred_eq] using hs ▸ hd]
  exact hle hc
end SimplicialChains
end

section
namespace SimplicialChains
open Finset
variable {V W : Type*} [DecidableEq V] [DecidableEq W]
omit [DecidableEq V] in
lemma mem_support_simplex (K : PreComplex V) (s : Finset V)
    (t : {s : Finset V // s ∈ K}) :
    t ∈ (simplex K s).support ↔ t.val = s := by
  classical
  by_cases hs : s ∈ K
  · rw [simplex_of_mem K hs, Finsupp.support_single _ one_ne_zero]
    simp only [Finset.mem_singleton, Subtype.ext_iff]
  · simp only [simplex, dif_neg hs, Finsupp.support_zero, Finset.notMem_empty, false_iff]
    intro he
    exact hs (he ▸ t.property)
omit [DecidableEq V] [DecidableEq W] in
lemma support_linearMap (K : PreComplex V) (L : PreComplex W)
    (T : Chain K →ₗ[F₂] Chain L) (c : Chain K)
    {t : {s : Finset W // s ∈ L}} (ht : t ∈ (T c).support) :
    ∃ s ∈ c.support, t ∈ (T (simplex K s.val)).support := by
  classical
  by_contra hn
  push Not at hn
  have hh : (T c) t = 0 := by
    conv_lhs => rw [chain_eq_sum K c]
    rw [map_sum, Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro s hs
    rw [map_smul, Finsupp.smul_apply, Finsupp.notMem_support_iff.mp (hn s hs), smul_zero]
  exact (Finsupp.mem_support_iff.mp ht) hh
lemma support_cone (K : PreComplex V) (a : V) (c : Chain K)
    {t : {s : Finset V // s ∈ K}} (ht : t ∈ (cone K a c).support) :
    ∃ s ∈ c.support, a ∉ s.val ∧ t.val = insert a s.val := by
  obtain ⟨s, hs, ht⟩ := support_linearMap K K (cone K a) c ht
  rw [cone_simplex K a s.property] at ht
  split_ifs at ht with ha
  · simp at ht
  · exact ⟨s, hs, ha, (mem_support_simplex K _ t).mp ht⟩
lemma cone_degree (K : PreComplex V) (a : V) (d : ℕ) :
    degreeChains K d ≤ (degreeChains K (d+1)).comap (cone K a) := by
  intro c hc t ht
  obtain ⟨s, hs, ha, he⟩ := support_cone K a c ht
  change t.val.card = d+1
  rw [he, Finset.card_insert_of_notMem ha, hc hs]
end SimplicialChains
end

section
namespace SimplicialChains
open Finset
variable {V W : Type*} [DecidableEq V] [DecidableEq W]
noncomputable def subdivSimplex (L : PreComplex W) (b : Finset V → W)
    (s : Finset V) : Chain L :=
  if _hs : s.Nonempty then
    if s.card = 1 then simplex L {b s}
    else cone L (b s) (∑ a ∈ s.attach, subdivSimplex L b (s.erase a.val))
  else 0
termination_by s.card
decreasing_by exact Finset.card_erase_lt_of_mem a.property
@[simp] lemma subdivSimplex_empty (L : PreComplex W) (b : Finset V → W) :
    subdivSimplex L b ∅ = 0 := by rw [subdivSimplex]; simp
lemma subdivSimplex_one (L : PreComplex W) (b : Finset V → W)
    {s : Finset V} (hc : s.card = 1) : subdivSimplex L b s = simplex L {b s} := by
  have hn : s.Nonempty := Finset.card_pos.mp (by omega)
  rw [subdivSimplex, dif_pos hn, if_pos hc]
lemma subdivSimplex_many (L : PreComplex W) (b : Finset V → W)
    {s : Finset V} (hn : s.Nonempty) (hc : s.card ≠ 1) :
    subdivSimplex L b s = cone L (b s) (∑ a ∈ s, subdivSimplex L b (s.erase a)) := by
  rw [subdivSimplex, dif_pos hn, if_neg hc]
  exact congrArg (cone L (b s)) (Finset.sum_attach s (fun a : V => subdivSimplex L b (s.erase a)))
def vertexCarrier (b : Finset V → W) (s : Finset V) : Set W :=
  {w | ∃ t : Finset V, t.Nonempty ∧ t ⊆ s ∧ b t = w}
omit [DecidableEq V] [DecidableEq W] in
lemma vertexCarrier_mono (b : Finset V → W) {s t : Finset V} (hst : s ⊆ t) :
    vertexCarrier b s ⊆ vertexCarrier b t := by
  rintro w ⟨u, hu, hus, hb⟩
  exact ⟨u, hu, hus.trans hst, hb⟩
omit [DecidableEq V] [DecidableEq W] in
lemma center_mem_carrier (b : Finset V → W) {s : Finset V} (hs : s.Nonempty) :
    b s ∈ vertexCarrier b s := ⟨s, hs, Finset.Subset.refl _, rfl⟩
lemma support_sum_chains (L : PreComplex W) {α : Type*}
    (s : Finset α) (c : α → Chain L) {t : {s : Finset W // s ∈ L}}
    (ht : t ∈ (∑ a ∈ s, c a).support) : ∃ a ∈ s, t ∈ (c a).support := by
  classical
  by_contra hn
  push Not at hn
  have hh : (∑ a ∈ s, c a) t = 0 := by
    rw [Finsupp.finsetSum_apply]
    exact Finset.sum_eq_zero (fun a ha => Finsupp.notMem_support_iff.mp (hn a ha))
  exact Finsupp.mem_support_iff.mp ht hh
lemma subdivSimplex_carrier (L : PreComplex W) (b : Finset V → W)
    (s : Finset V) {t : {s : Finset W // s ∈ L}}
    (ht : t ∈ (subdivSimplex L b s).support) : ↑t.val ⊆ vertexCarrier b s := by
  induction s using Finset.strongInductionOn generalizing t with
  | _ s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hn
    · simp at ht
    by_cases hc : s.card = 1
    · rw [subdivSimplex_one L b hc, mem_support_simplex] at ht
      rw [ht]
      exact Finset.singleton_subset_set_iff.mpr (center_mem_carrier b hn)
    · rw [subdivSimplex_many L b hn hc] at ht
      obtain ⟨u, hu, _, htu⟩ := support_cone L (b s) _ ht
      obtain ⟨a, ha, hua⟩ := support_sum_chains L s _ hu
      have hu' := ih (s.erase a) (Finset.erase_ssubset ha) hua
      rw [htu, Finset.coe_insert]
      exact Set.insert_subset (center_mem_carrier b hn)
        (hu'.trans (vertexCarrier_mono b (Finset.erase_subset a s)))
end SimplicialChains
end

section
namespace SimplicialChains
open Finset
variable {V W : Type*} [DecidableEq V] [DecidableEq W]
omit [DecidableEq V] in
lemma simplex_mem_degree_all (K : PreComplex V) (s : Finset V) :
    simplex K s ∈ degreeChains K s.card := by
  classical
  by_cases hs : s ∈ K
  · exact simplex_mem_degree K hs
  · simp only [simplex, dif_neg hs]
    exact Submodule.zero_mem _
lemma subdivSimplex_degree (L : PreComplex W) (b : Finset V → W)
    (s : Finset V) : subdivSimplex L b s ∈ degreeChains L s.card := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hn
    · rw [subdivSimplex_empty]
      exact Submodule.zero_mem _
    by_cases hc : s.card = 1
    · rw [subdivSimplex_one L b hc, hc]
      exact simplex_mem_degree_all L {b s}
    · rw [subdivSimplex_many L b hn hc]
      have hsum : (∑ a ∈ s, subdivSimplex L b (s.erase a)) ∈ degreeChains L (s.card-1) := by
        apply Submodule.sum_mem
        intro a ha
        have hh := ih (s.erase a) (Finset.erase_ssubset ha)
        simpa only [Finset.card_erase_of_mem ha] using hh
      have hpos := hn.card_pos
      simpa only [Submodule.mem_comap, Nat.sub_add_cancel hpos] using
        cone_degree L (b s) (s.card-1) hsum
def SubdivisionCarrier (K : PreComplex V) (L : PreComplex W)
    (b : Finset V → W) : Prop :=
  ∀ s ∈ K, ∀ t : Finset W, t.Nonempty → ↑t ⊆ vertexCarrier b s → t ∈ L
omit [DecidableEq V] [DecidableEq W] in
lemma SubdivisionCarrier.center (K : PreComplex V)
    (L : PreComplex W) (b : Finset V → W) (hb : SubdivisionCarrier K L b)
    {s : Finset V} (hs : s ∈ K) : {b s} ∈ L :=
  hb s hs {b s} (Finset.singleton_nonempty _) (Finset.singleton_subset_set_iff.mpr
    (center_mem_carrier b (K.isRelLowerSet_faces hs).1))
lemma subdivSimplex_augmentation (K : PreComplex V)
    (L : PreComplex W) (b : Finset V → W) (hb : SubdivisionCarrier K L b)
    {s : Finset V} (hs : s ∈ K) :
    augmentation L (subdivSimplex L b s) = augmentation K (simplex K s) := by
  rw [augmentation_simplex K hs]
  by_cases hc : s.card = 1
  · rw [subdivSimplex_one L b hc, augmentation_simplex L (hb.center K L b hs)]
    simp [hc]
  · rw [if_neg hc]
    exact augmentation_eq_zero_of_degree L _ hc (subdivSimplex_degree L b s)
noncomputable def subdivMap (K : PreComplex V)
    (L : PreComplex W) (b : Finset V → W) : Chain K →ₗ[F₂] Chain L :=
  Finsupp.linearCombination F₂ (fun s => subdivSimplex L b s.val)
lemma subdivMap_simplex (K : PreComplex V)
    (L : PreComplex W) (b : Finset V → W) {s : Finset V} (hs : s ∈ K) :
    subdivMap K L b (simplex K s) = subdivSimplex L b s := by
  simp [simplex_of_mem K hs, subdivMap, Finsupp.linearCombination_single]
lemma subdivMap_simplex_subset (K : PreComplex V)
    (L : PreComplex W) (b : Finset V → W) {s t : Finset V}
    (ht : t ∈ K) (hs : s ⊆ t) : subdivMap K L b (simplex K s) = subdivSimplex L b s := by
  rcases s.eq_empty_or_nonempty with rfl | hn
  · simp
  · exact subdivMap_simplex K L b ((K.isRelLowerSet_faces ht).2 hs hn)
lemma subdivMap_augmentation (K : PreComplex V)
    (L : PreComplex W) (b : Finset V → W) (hb : SubdivisionCarrier K L b) :
    (augmentation L).comp (subdivMap K L b) = augmentation K := by
  apply Finsupp.lhom_ext
  intro s r
  have hs := subdivSimplex_augmentation K L b hb s.property
  have hm := subdivMap_simplex K L b s.property
  rw [simplex_of_mem K s.property] at hs hm
  have he : Finsupp.single s r = r • Finsupp.single s (1 : F₂) := by simp
  simp only [LinearMap.comp_apply, he, map_smul, hm, hs]
lemma subdivMap_boundary_simplex (K : PreComplex V)
    (L : PreComplex W) (b : Finset V → W) {s : Finset V} (hs : s ∈ K) :
    subdivMap K L b (boundary K (simplex K s)) =
      ∑ a ∈ s, subdivSimplex L b (s.erase a) := by
  rw [boundary_simplex K hs, map_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact subdivMap_simplex_subset K L b hs (Finset.erase_subset a s)
lemma subdivSimplex_boundary (K : PreComplex V)
    (L : PreComplex W) (b : Finset V → W) (hb : SubdivisionCarrier K L b)
    {s : Finset V} (hs : s ∈ K) :
    boundary L (subdivSimplex L b s) = subdivMap K L b (boundary K (simplex K s)) := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    have hn := (K.isRelLowerSet_faces hs).1
    by_cases hc : s.card = 1
    · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hc
      rw [subdivSimplex_one L b hc, boundary_simplex L (hb.center K L b hs),
        boundary_simplex K hs]
      simp
    · have hd : boundary L (subdivMap K L b (boundary K (simplex K s))) = 0 := by
        have he : boundary L (subdivMap K L b (boundary K (simplex K s))) =
            subdivMap K L b (boundary K (boundary K (simplex K s))) := by
          rw [boundary_simplex K hs]
          simp only [map_sum]
          apply Finset.sum_congr rfl
          intro a ha
          rcases (s.erase a).eq_empty_or_nonempty with heq | hne
          · simp [heq]
          · have hK : s.erase a ∈ K := (K.isRelLowerSet_faces hs).2 (Finset.erase_subset a s) hne
            rw [subdivMap_simplex K L b hK]
            exact ih (s.erase a) (Finset.erase_ssubset ha) hK
        rw [he, boundary_twice_simplex K hs, map_zero]
      have hε : augmentation L (subdivMap K L b (boundary K (simplex K s))) = 0 := by
        have hh := LinearMap.congr_fun (subdivMap_augmentation K L b hb)
          (boundary K (simplex K s))
        rw [LinearMap.comp_apply, augmentation_boundary_simplex K hs] at hh
        exact hh
      have hcone : ∀ t ∈ (subdivMap K L b (boundary K (simplex K s))).support,
          insert (b s) t.val ∈ L := by
        rw [subdivMap_boundary_simplex K L b hs]
        intro t ht
        obtain ⟨a, ha, hta⟩ := support_sum_chains L s _ ht
        have ht' := (subdivSimplex_carrier L b _ hta).trans
          (vertexCarrier_mono b (Finset.erase_subset a s))
        apply hb s hs _ (Finset.insert_nonempty _ _)
        rw [Finset.coe_insert]
        exact Set.insert_subset (center_mem_carrier b hn) ht'
      rw [subdivSimplex_many L b hn hc, ← subdivMap_boundary_simplex K L b hs,
        cone_boundary L (b s) _ hcone, hd, hε, map_zero, zero_smul, add_zero, add_zero]
lemma subdivMap_boundary (K : PreComplex V)
    (L : PreComplex W) (b : Finset V → W) (hb : SubdivisionCarrier K L b) :
    (boundary L).comp (subdivMap K L b) = (subdivMap K L b).comp (boundary K) := by
  apply Finsupp.lhom_ext
  intro s r
  have hs := subdivSimplex_boundary K L b hb s.property
  have hm := subdivMap_simplex K L b s.property
  rw [simplex_of_mem K s.property] at hs hm
  have he : Finsupp.single s r = r • Finsupp.single s (1 : F₂) := by simp
  simp only [LinearMap.comp_apply, he, map_smul, hm, hs]
end SimplicialChains
end

section
namespace SimplicialChains
open Finset
variable {V W U : Type*} [DecidableEq V] [DecidableEq W] [DecidableEq U]
omit [DecidableEq W] [DecidableEq U] in
lemma mapChains_equiv_simplex_all (K : PreComplex V) (e : V ≃ V)
    (he : ∀ s, s ∈ K ↔ s.image e ∈ K) (s : Finset V) :
    mapChains K K e (simplex K s) = simplex K (s.image e) := by
  classical
  by_cases hs : s ∈ K
  · rw [mapChains_simplex K K e hs, mapSimplex,
      if_pos (Finset.card_image_iff.mpr e.injective.injOn)]
  · have ht : s.image e ∉ K := (he s).not.mp hs
    simp [simplex, hs, ht]
omit [DecidableEq W] [DecidableEq U] in
lemma cone_equivariant (K : PreComplex V) (e : V ≃ V)
    (he : ∀ s, s ∈ K ↔ s.image e ∈ K) (a : V) :
    (mapChains K K e).comp (cone K a) = (cone K (e a)).comp (mapChains K K e) := by
  apply Finsupp.lhom_ext
  intro s r
  have hm := mapChains_equiv_simplex_all K e he s.val
  have hc := cone_simplex K a s.property
  have hsc := cone_simplex K (e a) ((he s.val).mp s.property)
  have hh : mapChains K K e (cone K a (simplex K s.val)) =
      cone K (e a) (mapChains K K e (simplex K s.val)) := by
    rw [hc, hm, hsc]
    by_cases ha : a ∈ s.val
    · rw [if_pos ha, if_pos (Finset.mem_image_of_mem e ha), map_zero]
    · have hna : e a ∉ s.val.image e := by
        intro h
        obtain ⟨b, hb, heq⟩ := Finset.mem_image.mp h
        exact ha (e.injective heq ▸ hb)
      rw [if_neg ha, if_neg hna, mapChains_equiv_simplex_all K e he,
        Finset.image_insert]
  rw [simplex_of_mem K s.property] at hh
  have hr : Finsupp.single s r = r • Finsupp.single s (1 : F₂) := by simp
  simp only [LinearMap.comp_apply, hr, map_smul, hh]
omit [DecidableEq U] in
lemma subdivSimplex_equivariant (L : PreComplex W)
    (e : V ≃ V) (d : W ≃ W) (hd : ∀ s, s ∈ L ↔ s.image d ∈ L)
    (b : Finset V → W) (hb : ∀ s, b (s.image e) = d (b s)) (s : Finset V) :
    mapChains L L d (subdivSimplex L b s) = subdivSimplex L b (s.image e) := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hn
    · simp
    have hc : (s.image e).card = s.card := Finset.card_image_iff.mpr e.injective.injOn
    by_cases hs : s.card = 1
    · rw [subdivSimplex_one L b hs, subdivSimplex_one L b (hc.trans hs),
        mapChains_equiv_simplex_all L d hd, Finset.image_singleton, hb]
    · rw [subdivSimplex_many L b hn hs,
        subdivSimplex_many L b (hn.image e) (by omega)]
      have hcone := LinearMap.congr_fun (cone_equivariant L d hd (b s))
        (∑ a ∈ s, subdivSimplex L b (s.erase a))
      rw [LinearMap.comp_apply, LinearMap.comp_apply] at hcone
      rw [hcone, map_sum, hb, Finset.sum_image (fun a _ b _ he => e.injective he)]
      apply congrArg (cone L (d (b s)))
      apply Finset.sum_congr rfl
      intro a ha
      rw [ih (s.erase a) (Finset.erase_ssubset ha), image_erase_of_injOn e s e.injective.injOn ha]
omit [DecidableEq U] in
lemma subdivMap_equivariant (K : PreComplex V)
    (L : PreComplex W) (e : V ≃ V) (d : W ≃ W)
    (he : ∀ s, s ∈ K ↔ s.image e ∈ K) (hd : ∀ s, s ∈ L ↔ s.image d ∈ L)
    (b : Finset V → W) (hb : ∀ s, b (s.image e) = d (b s)) :
    (mapChains L L d).comp (subdivMap K L b) =
      (subdivMap K L b).comp (mapChains K K e) := by
  apply Finsupp.lhom_ext
  intro s r
  have hh : mapChains L L d (subdivMap K L b (simplex K s.val)) =
      subdivMap K L b (mapChains K K e (simplex K s.val)) := by
    rw [subdivMap_simplex K L b s.property, subdivSimplex_equivariant L e d hd b hb,
      mapChains_equiv_simplex_all K e he, subdivMap_simplex K L b ((he s.val).mp s.property)]
  rw [simplex_of_mem K s.property] at hh
  have hr : Finsupp.single s r = r • Finsupp.single s (1 : F₂) := by simp
  simp only [LinearMap.comp_apply, hr, map_smul, hh]
omit [DecidableEq U] in
lemma subdivMap_norm (K : PreComplex V)
    (L : PreComplex W) (e : V ≃ V) (d : W ≃ W)
    (he : ∀ s, s ∈ K ↔ s.image e ∈ K) (hd : ∀ s, s ∈ L ↔ s.image d ∈ L)
    (b : Finset V → W) (hb : ∀ s, b (s.image e) = d (b s)) :
    (normMap L d).comp (subdivMap K L b) =
      (subdivMap K L b).comp (normMap K e) := by
  simp only [normMap, LinearMap.add_comp, LinearMap.comp_add, LinearMap.id_comp,
    LinearMap.comp_id, subdivMap_equivariant K L e d he hd b hb]
omit [DecidableEq U] in
lemma subdivMap_degree (K : PreComplex V)
    (L : PreComplex W) (b : Finset V → W) (d : ℕ) :
    degreeChains K d ≤ (degreeChains L d).comap (subdivMap K L b) := by
  apply grade_map K L _ d d
  intro s hs hsd
  rw [subdivMap_simplex K L b hs, ← hsd]
  exact subdivSimplex_degree L b s
end SimplicialChains
end

section
namespace SimplicialChains
open Finset
variable {V W : Type*} [DecidableEq V] [DecidableEq W]
omit [DecidableEq V] in
lemma linearMap_eq_of_support {K : PreComplex V}
    {M : Type*} [AddCommMonoid M] [Module F₂ M]
    (T U : Chain K →ₗ[F₂] M) (c : Chain K)
    (hc : ∀ s ∈ c.support, T (simplex K s.val) = U (simplex K s.val)) : T c = U c := by
  rw [chain_eq_sum K c, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [map_smul, map_smul, hc s hs]
lemma mapChains_boundary_simplex_of_image (K : PreComplex V)
    (L : PreComplex W) (f : V → W)
    {s : Finset V} (hs : s ∈ K) (ht : s.image f ∈ L) :
    boundary L (mapChains K L f (simplex K s)) =
      mapChains K L f (boundary K (simplex K s)) := by
  rw [mapChains_simplex K L f hs, boundary_simplex K hs, map_sum]
  have h (a : V) : mapChains K L f (simplex K (s.erase a)) = mapSimplex L f (s.erase a) :=
    mapChains_simplex_subset K L f hs (Finset.erase_subset a s)
  simp_rw [h]
  by_cases hinj : Set.InjOn f s
  · rw [mapSimplex, if_pos (Finset.card_image_iff.mpr hinj), boundary_simplex L ht]
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro a ha
      have hj : Set.InjOn f (s.erase a) := hinj.mono (Finset.erase_subset a s)
      rw [mapSimplex, if_pos (Finset.card_image_iff.mpr hj), image_erase_of_injOn f s hinj ha]
    · exact hinj
  · rw [mapSimplex, if_neg (mt Finset.card_image_iff.mp hinj), map_zero,
      mapSimplex_boundary_degenerate L f s hinj]
lemma mapChains_boundary_of_support (K : PreComplex V)
    (L : PreComplex W) (f : V → W) (c : Chain K)
    (hc : ∀ s ∈ c.support, s.val.image f ∈ L) :
    boundary L (mapChains K L f c) = mapChains K L f (boundary K c) := by
  apply linearMap_eq_of_support ((boundary L).comp (mapChains K L f))
    ((mapChains K L f).comp (boundary K)) c
  intro s hs
  exact mapChains_boundary_simplex_of_image K L f s.property (hc s hs)
omit [DecidableEq V] in
lemma mapChains_augmentation_simplex_of_image (K : PreComplex V)
    (L : PreComplex W) (f : V → W)
    {s : Finset V} (hs : s ∈ K) (ht : s.image f ∈ L) :
    augmentation L (mapChains K L f (simplex K s)) = augmentation K (simplex K s) := by
  rw [mapChains_simplex K L f hs, augmentation_simplex K hs]
  by_cases hcard : (s.image f).card = s.card
  · rw [mapSimplex, if_pos hcard, augmentation_simplex L ht, hcard]
  · have hne : s.card ≠ 1 := by
      intro hc
      obtain ⟨v,rfl⟩ := Finset.card_eq_one.mp hc
      simp at hcard
    simp [mapSimplex, hcard, hne]
omit [DecidableEq V] in
lemma mapChains_augmentation_of_support (K : PreComplex V)
    (L : PreComplex W) (f : V → W) (c : Chain K)
    (hc : ∀ s ∈ c.support, s.val.image f ∈ L) :
    augmentation L (mapChains K L f c) = augmentation K c := by
  apply linearMap_eq_of_support ((augmentation L).comp (mapChains K L f)) (augmentation K) c
  intro s hs
  exact mapChains_augmentation_simplex_of_image K L f s.property (hc s hs)
omit [DecidableEq V] in
lemma mapChains_degree_all (K : PreComplex V)
    (L : PreComplex W) (f : V → W) (d : ℕ) :
    degreeChains K d ≤ (degreeChains L d).comap (mapChains K L f) := by
  apply grade_map K L _ d d
  intro s hs hd
  rw [mapChains_simplex K L f hs, mapSimplex]
  split_ifs with hh
  · rw [← hd, ← hh]
    exact simplex_mem_degree_all L _
  · exact Submodule.zero_mem _
lemma mapChains_equivariant (K : PreComplex V)
    (L : PreComplex W) (e : V ≃ V) (d : W ≃ W)
    (he : ∀ s, s ∈ K ↔ s.image e ∈ K) (hd : ∀ s, s ∈ L ↔ s.image d ∈ L)
    (f : V → W) (hf : ∀ s ∈ K, ∀ x ∈ s, f (e x) = d (f x)) :
    (mapChains L L d).comp (mapChains K L f) =
      (mapChains K L f).comp (mapChains K K e) := by
  apply Finsupp.lhom_ext
  intro s r
  have him : (s.val.image e).image f = (s.val.image f).image d := by
    simp only [Finset.image_image]
    exact Finset.image_congr (fun x hx => hf s.val s.property x hx)
  have hcard : (s.val.image e).card = s.val.card := Finset.card_image_iff.mpr e.injective.injOn
  have hcard' : ((s.val.image f).image d).card = (s.val.image f).card :=
    Finset.card_image_iff.mpr d.injective.injOn
  have hh : mapChains L L d (mapChains K L f (simplex K s.val)) =
      mapChains K L f (mapChains K K e (simplex K s.val)) := by
    rw [mapChains_simplex K L f s.property, mapChains_equiv_simplex_all K e he,
      mapChains_simplex K L f ((he s.val).mp s.property)]
    simp only [mapSimplex, him, hcard, hcard']
    split_ifs
    · exact mapChains_equiv_simplex_all L d hd _
    · exact map_zero _
  rw [simplex_of_mem K s.property] at hh
  have hr : Finsupp.single s r = r • Finsupp.single s (1 : F₂) := by simp
  simp only [LinearMap.comp_apply, hr, map_smul, hh]
lemma mapChains_norm (K : PreComplex V)
    (L : PreComplex W) (e : V ≃ V) (d : W ≃ W)
    (he : ∀ s, s ∈ K ↔ s.image e ∈ K) (hd : ∀ s, s ∈ L ↔ s.image d ∈ L)
    (f : V → W) (hf : ∀ s ∈ K, ∀ x ∈ s, f (e x) = d (f x)) :
    (normMap L d).comp (mapChains K L f) =
      (mapChains K L f).comp (normMap K e) := by
  simp only [normMap, LinearMap.add_comp, LinearMap.comp_add, LinearMap.id_comp,
    LinearMap.comp_id, mapChains_equivariant K L e d he hd f hf]
end SimplicialChains
end

section
namespace SimplicialChains
open Finset
abbrev SignedVertex := ℕ × Bool
def flip : SignedVertex ≃ SignedVertex :=
  Equiv.prodCongr (Equiv.refl ℕ) Equiv.boolNot
@[simp] lemma flip_apply (v : SignedVertex) : flip v = (v.1, !v.2) := rfl
lemma flip_involutive : Function.Involutive flip := by
  intro v
  simp
lemma flip_ne (v : SignedVertex) : flip v ≠ v := by
  intro equality
  exact Bool.not_ne_self v.2 (congrArg Prod.snd equality)
def cross (n : ℕ) : PreComplex SignedVertex where
  faces := {s | s.Nonempty ∧ (∀ v ∈ s, v.1 < n) ∧ Set.InjOn Prod.fst (s : Set SignedVertex)}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨hs.1, ?_⟩
    intro t hts ht
    exact ⟨ht, fun v hv => hs.2.1 v (hts hv), hs.2.2.mono hts⟩
lemma cross_flip_forward (n : ℕ) (s : Finset SignedVertex) (hs : s ∈ cross n) :
    s.image flip ∈ cross n := by
  refine ⟨hs.1.image _, ?_, ?_⟩
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    exact hs.2.1 w hw
  · intro v hv w hw he
    obtain ⟨v', hv', rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨w', hw', rfl⟩ := Finset.mem_image.mp hw
    exact congrArg flip (hs.2.2 hv' hw' he)
lemma cross_flip (n : ℕ) (s : Finset SignedVertex) :
    s ∈ cross n ↔ s.image flip ∈ cross n := by
  refine ⟨cross_flip_forward n s, ?_⟩
  intro hs
  have h := cross_flip_forward n _ hs
  rw [Finset.image_image] at h
  have hh : flip ∘ flip = id := funext flip_involutive
  simpa only [hh, Finset.image_id] using h
lemma cross_free (n : ℕ) (s : Finset SignedVertex) (hs : s ∈ cross n) :
    s.image flip ≠ s := by
  intro he
  obtain ⟨v, hv⟩ := hs.1
  have hv' : flip v ∈ s := he ▸ Finset.mem_image_of_mem flip hv
  exact flip_ne v (hs.2.2 hv' hv rfl)
lemma cross_card (n : ℕ) (s : Finset SignedVertex) (hs : s ∈ cross n) : s.card ≤ n := by
  calc
    s.card = (s.image Prod.fst).card := (Finset.card_image_iff.mpr hs.2.2).symm
    _ ≤ (Finset.range n).card := Finset.card_le_card (by
      intro i hi
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
      exact Finset.mem_range.mpr (hs.2.1 v hv))
    _ = n := Finset.card_range n
lemma cross_singleton (n i : ℕ) (hi : i < n) (b : Bool) :
    ({(i,b)} : Finset SignedVertex) ∈ cross n := by
  refine ⟨Finset.singleton_nonempty _, ?_, ?_⟩
  · simpa using hi
  · simpa only [Finset.coe_singleton] using Set.injOn_singleton Prod.fst (i,b)
lemma cross_insert (n i : ℕ) (hi : i < n) (s : Finset SignedVertex)
    (hs : s ∈ cross n) (hsi : ∀ v ∈ s, v.1 < i) (b : Bool) :
    insert (i,b) s ∈ cross n := by
  refine ⟨Finset.insert_nonempty _ _, ?_, ?_⟩
  · intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact hi
    · exact hs.2.1 v hv
  · intro v hv w hw he
    rcases Finset.mem_insert.mp hv with rfl | hv <;>
      rcases Finset.mem_insert.mp hw with rfl | hw
    · rfl
    · exact False.elim ((ne_of_lt (hsi w hw)) he.symm)
    · exact False.elim ((ne_of_lt (hsi v hv)) he)
    · exact hs.2.2 hv hw he
variable {V W : Type*} [DecidableEq V] [DecidableEq W]
omit [DecidableEq V] in
lemma support_mapChains_injective (K : PreComplex V)
    (L : PreComplex W) (f : V → W) (hf : Function.Injective f)
    (c : Chain K) {t : {s : Finset W // s ∈ L}}
    (ht : t ∈ (mapChains K L f c).support) :
    ∃ s ∈ c.support, t.val = s.val.image f := by
  obtain ⟨s, hs, hst⟩ := support_linearMap K L (mapChains K L f) c ht
  rw [mapChains_simplex K L f s.property, mapSimplex,
    if_pos (Finset.card_image_iff.mpr hf.injOn), mem_support_simplex] at hst
  exact ⟨s, hs, hst⟩
lemma normMap_sq (K : PreComplex V) (e : V ≃ V)
    (he : ∀ s, s ∈ K ↔ s.image e ∈ K) (hi : Function.Involutive e) :
    (normMap K e).comp (normMap K e) = 0 := by
  rw [normMap_eq K e he]
  exact SmithTheory.involutionNorm_sq _ (faceEquiv_involutive K e he hi)
lemma normMap_degree (K : PreComplex V) (e : V ≃ V)
    (he : ∀ s ∈ K, s.image e ∈ K) (d : ℕ) :
    degreeChains K d ≤ (degreeChains K d).comap (normMap K e) := by
  intro c hc
  exact (degreeChains K d).add_mem hc (mapChains_degree K K e he d hc)
noncomputable def crossTower (n : ℕ) : ℕ → Chain (cross n)
  | 0 => simplex (cross n) {(0,false)}
  | i+1 => cone (cross n) (i+1,false) (normMap (cross n) flip (crossTower n i))
lemma crossTower_support (n i : ℕ) {s : {s : Finset SignedVertex // s ∈ cross n}}
    (hs : s ∈ (crossTower n i).support) : ∀ v ∈ s.val, v.1 ≤ i := by
  induction i generalizing s with
  | zero =>
    have he := (mem_support_simplex (cross n) {(0,false)} s).mp hs
    rw [he]
    intro v hv
    have he' := Finset.mem_singleton.mp hv
    exact he' ▸ Nat.le_refl 0
  | succ i ih =>
    obtain ⟨t, ht, _, he⟩ := support_cone (cross n) (i+1,false) _ hs
    rw [he]
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact le_rfl
    · have hu : t ∈ (crossTower n i).support ∪
          (mapChains (cross n) (cross n) flip (crossTower n i)).support :=
        Finsupp.support_add ht
      rcases Finset.mem_union.mp hu with ht | ht
      · exact (ih ht v hv).trans (Nat.le_succ i)
      · obtain ⟨u, hu, he⟩ := support_mapChains_injective (cross n) (cross n) flip
          flip.injective _ ht
        rw [he] at hv
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
        exact (ih hu w hw).trans (Nat.le_succ i)
lemma crossTower_degree (n i : ℕ) : crossTower n i ∈ degreeChains (cross n) (i+1) := by
  induction i with
  | zero => exact simplex_mem_degree_all (cross n) {(0,false)}
  | succ i ih =>
    exact cone_degree (cross n) (i+1,false) (i+1)
      (normMap_degree (cross n) flip (cross_flip_forward n) (i+1) ih)
lemma crossTower_cone_faces (n i : ℕ) (hi : i+1 < n)
    {s : {s : Finset SignedVertex // s ∈ cross n}}
    (hs : s ∈ (normMap (cross n) flip (crossTower n i)).support) :
    insert (i+1,false) s.val ∈ cross n := by
  apply cross_insert n (i+1) hi s.val s.property
  intro v hv
  have hu : s ∈ (crossTower n i).support ∪
      (mapChains (cross n) (cross n) flip (crossTower n i)).support :=
    Finsupp.support_add hs
  rcases Finset.mem_union.mp hu with hs | hs
  · exact Nat.lt_succ_of_le (crossTower_support n i hs v hv)
  · obtain ⟨t, ht, he⟩ := support_mapChains_injective (cross n) (cross n) flip
      flip.injective _ hs
    rw [he] at hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    exact Nat.lt_succ_of_le (crossTower_support n i ht w hw)
lemma crossTower_norm_boundary (n i : ℕ) (hi : i < n) :
    boundary (cross n) (normMap (cross n) flip (crossTower n i)) = 0 := by
  induction i with
  | zero =>
    have hc := LinearMap.congr_fun (boundary_normMap (cross n) flip (cross_flip_forward n))
      (crossTower n 0)
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at hc
    rw [hc]
    change normMap (cross n) flip (boundary (cross n) (simplex (cross n) {(0,false)})) = 0
    rw [boundary_simplex (cross n) (cross_singleton n 0 hi false)]
    simp
  | succ i ih =>
    have hc := LinearMap.congr_fun (boundary_normMap (cross n) flip (cross_flip_forward n))
      (crossTower n (i+1))
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at hc
    rw [hc]
    change normMap (cross n) flip (boundary (cross n)
      (cone (cross n) (i+1,false) (normMap (cross n) flip (crossTower n i)))) = 0
    rw [cone_boundary (cross n) _ _ (fun s hs => crossTower_cone_faces n i hi hs),
      ih (by omega)]
    have ha := LinearMap.congr_fun (augmentation_normMap (cross n) flip (cross_flip_forward n))
      (crossTower n i)
    rw [LinearMap.comp_apply, LinearMap.zero_apply] at ha
    rw [ha, map_zero, zero_smul, add_zero, add_zero]
    exact LinearMap.congr_fun (normMap_sq (cross n) flip (cross_flip n) flip_involutive) _
lemma crossTower_boundary (n i : ℕ) (hi : i+1 < n) :
    boundary (cross n) (crossTower n (i+1)) = normMap (cross n) flip (crossTower n i) := by
  change boundary (cross n) (cone (cross n) (i+1,false)
    (normMap (cross n) flip (crossTower n i))) = _
  rw [cone_boundary (cross n) _ _ (fun s hs => crossTower_cone_faces n i hi hs),
    crossTower_norm_boundary n i (by omega)]
  have ha := LinearMap.congr_fun (augmentation_normMap (cross n) flip (cross_flip_forward n))
    (crossTower n i)
  rw [LinearMap.comp_apply, LinearMap.zero_apply] at ha
  rw [ha, map_zero, zero_smul, add_zero, add_zero]
lemma crossTower_augmentation (n : ℕ) (hn : 0 < n) :
    augmentation (cross n) (crossTower n 0) = 1 := by
  rw [crossTower, augmentation_simplex (cross n) (cross_singleton n 0 hn false)]
  simp
end SimplicialChains
end

section
namespace SimplicialChains
lemma cross_chain_dimension_bound (n m : ℕ)
    (T : Chain (cross n) →ₗ[F₂] Chain (cross m))
    (hd : (boundary (cross m)).comp T = T.comp (boundary (cross n)))
    (hN : (normMap (cross m) flip).comp T = T.comp (normMap (cross n) flip))
    (ha : (augmentation (cross m)).comp T = augmentation (cross n))
    (hgrade : ∀ d, degreeChains (cross n) d ≤ (degreeChains (cross m) d).comap T) :
    n ≤ m := by
  by_contra hnm
  have hmn : m < n := Nat.lt_of_not_ge hnm
  let c : ℕ → Chain (cross m) := fun i => T (crossTower n i)
  have hstep : ∀ i < m, boundary (cross m) (c (i+1)) =
      normMap (cross m) flip (c i) := by
    intro i hi
    change boundary (cross m) (T (crossTower n (i+1))) =
      normMap (cross m) flip (T (crossTower n i))
    rw [← LinearMap.comp_apply, hd, LinearMap.comp_apply,
      crossTower_boundary n i (by omega), ← LinearMap.comp_apply, ← hN,
      LinearMap.comp_apply]
  have htop : c m = 0 := by
    have hg := hgrade (m+1) (crossTower_degree n m)
    change c m ∈ degreeChains (cross m) (m+1) at hg
    rw [degreeChains_eq_bot_of_card_bound (cross m) (m+1)
      (fun s hs => Nat.lt_succ_of_le (cross_card m s hs)), Submodule.mem_bot] at hg
    exact hg
  have hh := antipodal_tower_augmentation_zero (cross m) flip (cross_flip m)
    flip_involutive (cross_free m) m c hstep (by rw [htop, map_zero])
  change augmentation (cross m) (T (crossTower n 0)) = 0 at hh
  rw [← LinearMap.comp_apply, ha, crossTower_augmentation n (by omega)] at hh
  exact one_ne_zero hh
end SimplicialChains
namespace SimplicialChains
open Finset
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
noncomputable def barycenter (s : Finset E) : E := (s.card : ℝ)⁻¹ • ∑ x ∈ s, x
lemma barycenter_eq_centerMass (s : Finset E) :
    barycenter s = s.centerMass (fun _ => (1 : ℝ)) id := by
  simp [barycenter, Finset.centerMass]
lemma barycenter_mem_convex {A : Set E} (hA : Convex ℝ A) {s : Finset E}
    (hs : s.Nonempty) (hsA : (s : Set E) ⊆ A) : barycenter s ∈ A := by
  rw [barycenter_eq_centerMass]
  apply hA.centerMass_mem
  · intro x hx; exact zero_le_one
  · simpa using (Nat.cast_pos.mpr hs.card_pos : (0 : ℝ) < s.card)
  · intro x hx; exact hsA hx
lemma barycenter_norm_le {s : Finset E} (hs : s.Nonempty) {D : ℝ}
    (hD : ∀ x ∈ s, ‖x‖ ≤ D) : ‖barycenter s‖ ≤ D := by
  have h := barycenter_mem_convex (convex_closedBall (0 : E) D) hs (A := Metric.closedBall 0 D)
    (fun x hx => by simpa only [Metric.mem_closedBall, dist_zero_right] using hD x hx)
  simpa only [Metric.mem_closedBall, dist_zero_right] using h
lemma barycenter_inner {s : Finset E} (hs : s.Nonempty) (w : E)
    (hw : ∀ x ∈ s, ⟪w,x⟫ = 1) : ⟪w,barycenter s⟫ = 1 := by
  rw [barycenter, real_inner_smul_right, inner_sum]
  simp only [Finset.sum_congr rfl hw, Finset.sum_const, nsmul_eq_mul, mul_one]
  exact inv_mul_cancel₀ (by exact_mod_cast hs.card_ne_zero)
def hemisphereComplex (R : ℝ) : PreComplex E where
  faces := {s | s.Nonempty ∧ ∃ w : E, ‖w‖ ≤ R ∧ ∀ x ∈ s, ‖x‖ ≤ 1 ∧ ⟪w,x⟫ = 1}
  isRelLowerSet_faces := by
    rintro s ⟨hs, w, hw, hs'⟩
    refine ⟨hs, ?_⟩
    intro t hts ht
    exact ⟨ht, w, hw, fun x hx => hs' x (hts hx)⟩
lemma barycenter_sub_eq {s : Finset E} (hs : s.Nonempty) (x : E) :
    barycenter s - x = (s.card : ℝ)⁻¹ • ∑ y ∈ s, (y-x) := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ]
  rw [smul_sub, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hs.card_ne_zero), one_smul]
  rfl
lemma barycenter_dist_vertex [DecidableEq E] {s : Finset E} {x : E} (hx : x ∈ s)
    {D : ℝ} (hD : ∀ y ∈ s, ∀ z ∈ s, dist y z ≤ D) :
    dist (barycenter s) x ≤ ((s.card : ℝ)-1) / s.card * D := by
  have hs : s.Nonempty := ⟨x,hx⟩
  have hc : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  rw [dist_eq_norm, barycenter_sub_eq hs x, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (le_of_lt hc))]
  have hh : (∑ y ∈ s, (y-x)) = ∑ y ∈ s.erase x, (y-x) := by
    rw [← Finset.sum_erase_add _ _ hx]
    simp
  rw [hh]
  calc
    (s.card : ℝ)⁻¹ * ‖∑ y ∈ s.erase x, (y-x)‖ ≤
        (s.card : ℝ)⁻¹ * ∑ y ∈ s.erase x, ‖y-x‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr (le_of_lt hc))
    _ ≤ (s.card : ℝ)⁻¹ * ∑ y ∈ s.erase x, D := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (le_of_lt hc))
      apply Finset.sum_le_sum
      intro y hy
      simpa only [dist_eq_norm] using hD y (Finset.mem_of_mem_erase hy) x hx
    _ = ((s.card : ℝ)-1) / s.card * D := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem hx,
        Nat.cast_sub hs.card_pos, Nat.cast_one]
      ring
lemma barycenter_dist_carrier [DecidableEq E] {s t : Finset E} (ht : t.Nonempty)
    (hts : t ⊆ s) {D : ℝ} (hD : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ D) :
    dist (barycenter s) (barycenter t) ≤ ((s.card : ℝ)-1) / s.card * D := by
  have h := barycenter_mem_convex
    (convex_closedBall (barycenter s) (((s.card : ℝ)-1) / s.card * D)) ht
    (fun x hx => (Metric.mem_closedBall').mpr (barycenter_dist_vertex (hts hx) hD))
  exact (Metric.mem_closedBall').mp h
lemma barycenter_mesh_factor {a n : ℕ} (ha : 0 < a) (han : a ≤ n) :
    ((a : ℝ)-1) / a ≤ ((n : ℝ)-1) / n := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hn' : (0 : ℝ) < n := by exact_mod_cast lt_of_lt_of_le ha han
  apply (div_le_div_iff₀ ha' hn').mpr
  have han' : (a : ℝ) ≤ n := by exact_mod_cast han
  nlinarith
end SimplicialChains
end

section
namespace SimplicialChains
open Finset
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [DecidableEq E]
lemma barycenter_neg (s : Finset E) : barycenter (s.image Neg.neg) = -barycenter s := by
  rw [barycenter, Finset.card_image_iff.mpr neg_injective.injOn,
    Finset.sum_image neg_injective.injOn, Finset.sum_neg_distrib,
    smul_neg, barycenter]
lemma hemisphere_neg (R : ℝ) (s : Finset E) :
    s ∈ hemisphereComplex R ↔ s.image Neg.neg ∈ hemisphereComplex R := by
  constructor
  · rintro ⟨hn,w,hw,hh⟩
    refine ⟨hn.image _, -w, by simpa using hw, ?_⟩
    intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    simpa using hh y hy
  · rintro ⟨hn,w,hw,hh⟩
    refine ⟨Finset.image_nonempty.mp hn, -w, by simpa using hw, ?_⟩
    intro x hx
    have h := hh (-x) (Finset.mem_image_of_mem Neg.neg hx)
    simpa using h
omit [DecidableEq E] in
lemma hemisphere_subdivision_carrier (R : ℝ) :
    SubdivisionCarrier (hemisphereComplex R : PreComplex E)
      (hemisphereComplex R) barycenter := by
  rintro s ⟨hn,w,hw,hh⟩ t ht hts
  refine ⟨ht,w,hw,?_⟩
  intro x hx
  obtain ⟨u,hu,hus,rfl⟩ := hts hx
  exact ⟨barycenter_norm_le hu (fun y hy => (hh y (hus hy)).1),
    barycenter_inner hu w (fun y hy => (hh y (hus hy)).2)⟩
lemma subdivSimplex_mesh (R : ℝ) (s : Finset E) (n : ℕ) (hsn : s.card ≤ n)
    (D : ℝ) (hD : 0 ≤ D) (hsD : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ D)
    {t : {s : Finset E // s ∈ hemisphereComplex R}}
    (ht : t ∈ (subdivSimplex (hemisphereComplex R) barycenter s).support) :
    ∀ x ∈ t.val, ∀ y ∈ t.val, dist x y ≤ ((n : ℝ)-1) / n * D := by
  induction s using Finset.strongInductionOn generalizing t with
  | _ s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hn
    · simp at ht
    have hfac : 0 ≤ ((n : ℝ)-1) / n := by
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast le_trans hn.card_pos hsn
      exact div_nonneg (by linarith) (by positivity)
    by_cases hc : s.card = 1
    · rw [subdivSimplex_one _ _ hc, mem_support_simplex] at ht
      intro x hx y hy
      rw [ht, Finset.mem_singleton] at hx hy
      subst x; subst y
      simpa only [dist_self] using mul_nonneg hfac hD
    · rw [subdivSimplex_many _ _ hn hc] at ht
      obtain ⟨u,hu,_,htu⟩ := support_cone _ (barycenter s) _ ht
      obtain ⟨a,ha,hua⟩ := support_sum_chains _ s _ hu
      have hsmall := ih (s.erase a) (Finset.erase_ssubset ha)
        (le_trans (Finset.card_le_card (Finset.erase_subset a s)) hsn)
        (fun x hx y hy => hsD x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy)) hua
      have hcarrier := (subdivSimplex_carrier _ barycenter _ hua).trans
        (vertexCarrier_mono barycenter (Finset.erase_subset a s))
      have hcenter (x : E) (hx : x ∈ u.val) :
          dist (barycenter s) x ≤ ((n : ℝ)-1) / n * D := by
        obtain ⟨v,hv,hvs,rfl⟩ := hcarrier hx
        exact (barycenter_dist_carrier hv hvs hsD).trans
          (mul_le_mul_of_nonneg_right (barycenter_mesh_factor hn.card_pos hsn) hD)
      intro x hx y hy
      rw [htu, Finset.mem_insert] at hx hy
      rcases hx with rfl | hx <;> rcases hy with rfl | hy
      · simpa only [dist_self] using mul_nonneg hfac hD
      · exact hcenter y hy
      · rw [dist_comm]; exact hcenter x hx
      · exact hsmall x hx y hy
end SimplicialChains
end

section
namespace SimplicialChains
open Finset
open scoped RealInnerProductSpace
noncomputable def crossEmbedding (n : ℕ) (v : SignedVertex) : Euc (Fin n) :=
  if h : v.1 < n then (if v.2 then (-1:ℝ) else 1) • EuclideanSpace.single ⟨v.1,h⟩ 1 else 0
lemma crossEmbedding_norm (n : ℕ) (v : SignedVertex) (hv : v.1 < n) :
    ‖crossEmbedding n v‖ = 1 := by
  simp only [crossEmbedding, dif_pos hv, norm_smul, PiLp.norm_single]
  cases v.2 <;> norm_num
lemma crossEmbedding_flip (n : ℕ) (v : SignedVertex) :
    crossEmbedding n (flip v) = -crossEmbedding n v := by
  rcases v with ⟨i,b⟩
  cases b <;> simp only [crossEmbedding, flip_apply] <;> split_ifs <;> simp_all
lemma crossEmbedding_inner_ne (n : ℕ) {v w : SignedVertex}
    (hvw : v.1 ≠ w.1) : ⟪crossEmbedding n v, crossEmbedding n w⟫ = 0 := by
  unfold crossEmbedding
  split_ifs <;> simp_all [EuclideanSpace.inner_single_left]
lemma crossEmbedding_inner_self (n : ℕ) (v : SignedVertex) (hv : v.1 < n) :
    ⟪crossEmbedding n v, crossEmbedding n v⟫ = 1 := by
  rw [real_inner_self_eq_norm_sq, crossEmbedding_norm n v hv]
  norm_num
lemma crossEmbedding_face (n : ℕ) (s : Finset SignedVertex) (hs : s ∈ cross n) :
    s.image (crossEmbedding n) ∈ hemisphereComplex (n:ℝ) := by
  refine ⟨hs.1.image _, ∑ v ∈ s, crossEmbedding n v, ?_, ?_⟩
  · calc
      ‖∑ v ∈ s, crossEmbedding n v‖ ≤ ∑ v ∈ s, ‖crossEmbedding n v‖ := norm_sum_le _ _
      _ = s.card := by simp only [Finset.sum_congr rfl (fun v hv => crossEmbedding_norm n v (hs.2.1 v hv)), Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ (n:ℝ) := by exact_mod_cast cross_card n s hs
  · intro x hx
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hx
    refine ⟨le_of_eq (crossEmbedding_norm n v (hs.2.1 v hv)), ?_⟩
    rw [sum_inner, Finset.sum_eq_single v]
    · exact crossEmbedding_inner_self n v (hs.2.1 v hv)
    · intro w hw hwv
      exact crossEmbedding_inner_ne n (fun he => hwv (hs.2.2 hw hv he))
    · exact fun hn => False.elim (hn hv)
noncomputable def crossGeometricMap (n : ℕ) :
    Chain (cross n) →ₗ[F₂] Chain (hemisphereComplex (n:ℝ) :
      PreComplex (Euc (Fin n))) :=
  mapChains (cross n) (hemisphereComplex (n:ℝ)) (crossEmbedding n)
lemma crossGeometricMap_boundary (n : ℕ) :
    (boundary (hemisphereComplex (n:ℝ))).comp (crossGeometricMap n) =
      (crossGeometricMap n).comp (boundary (cross n)) :=
  mapChains_boundary _ _ _ (crossEmbedding_face n)
lemma crossGeometricMap_augmentation (n : ℕ) :
    (augmentation (hemisphereComplex (n:ℝ))).comp (crossGeometricMap n) =
      augmentation (cross n) := mapChains_augmentation _ _ _ (crossEmbedding_face n)
lemma crossGeometricMap_degree (n d : ℕ) :
    degreeChains (cross n) d ≤ (degreeChains (hemisphereComplex (n:ℝ)) d).comap
      (crossGeometricMap n) := mapChains_degree _ _ _ (crossEmbedding_face n) d
lemma crossGeometricMap_norm (n : ℕ) :
    (normMap (hemisphereComplex (n:ℝ)) (Equiv.neg _)).comp (crossGeometricMap n) =
      (crossGeometricMap n).comp (normMap (cross n) flip) := by
  apply mapChains_norm _ _ flip (Equiv.neg _) (cross_flip n) (hemisphere_neg (n:ℝ))
  intro s hs x hx
  exact crossEmbedding_flip n x
end SimplicialChains
end

section
namespace SimplicialChains
open Finset
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [DecidableEq E]
noncomputable def refinement (R : ℝ) : ℕ →
    Chain (hemisphereComplex R : PreComplex E) →ₗ[F₂]
      Chain (hemisphereComplex R : PreComplex E)
  | 0 => LinearMap.id
  | r+1 => (subdivMap (hemisphereComplex R) (hemisphereComplex R) barycenter).comp
      (refinement R r)
lemma refinement_boundary (R : ℝ) (r : ℕ) :
    (boundary (hemisphereComplex R : PreComplex E)).comp (refinement R r) =
      (refinement R r).comp (boundary (hemisphereComplex R)) := by
  induction r with
  | zero => simp only [refinement, LinearMap.comp_id, LinearMap.id_comp]
  | succ r ih =>
    rw [refinement, ← LinearMap.comp_assoc, subdivMap_boundary _ _ _ (hemisphere_subdivision_carrier R),
      LinearMap.comp_assoc, ih, ← LinearMap.comp_assoc]
lemma refinement_augmentation (R : ℝ) (r : ℕ) :
    (augmentation (hemisphereComplex R : PreComplex E)).comp
      (refinement R r) = augmentation (hemisphereComplex R) := by
  induction r with
  | zero => simp only [refinement, LinearMap.comp_id]
  | succ r ih =>
    rw [refinement, ← LinearMap.comp_assoc,
      subdivMap_augmentation _ _ _ (hemisphere_subdivision_carrier R), ih]
lemma refinement_norm (R : ℝ) (r : ℕ) :
    (normMap (hemisphereComplex R : PreComplex E) (Equiv.neg E)).comp
      (refinement R r) = (refinement R r).comp (normMap (hemisphereComplex R) (Equiv.neg E)) := by
  induction r with
  | zero => simp only [refinement, LinearMap.comp_id, LinearMap.id_comp]
  | succ r ih =>
    rw [refinement, ← LinearMap.comp_assoc,
      subdivMap_norm _ _ (Equiv.neg E) (Equiv.neg E) (hemisphere_neg R) (hemisphere_neg R)
        barycenter (barycenter_neg), LinearMap.comp_assoc, ih, ← LinearMap.comp_assoc]
lemma refinement_degree (R : ℝ) (r d : ℕ) :
    degreeChains (hemisphereComplex R : PreComplex E) d ≤
      (degreeChains (hemisphereComplex R) d).comap (refinement R r) := by
  induction r with
  | zero => intro c hc; exact hc
  | succ r ih =>
    intro c hc
    change subdivMap (hemisphereComplex R) (hemisphereComplex R) barycenter
      (refinement R r c) ∈ degreeChains (hemisphereComplex R) d
    exact subdivMap_degree (hemisphereComplex R : PreComplex E)
      (hemisphereComplex R) barycenter d (ih hc)
lemma refinement_mesh (R : ℝ) (r n : ℕ) {c : Chain (hemisphereComplex R : PreComplex E)}
    (hc : c ∈ degreeChains (hemisphereComplex R) n) {D : ℝ} (hD : 0 ≤ D)
    (hmesh : ∀ s ∈ c.support, ∀ x ∈ s.val, ∀ y ∈ s.val, dist x y ≤ D)
    {t : {s : Finset E // s ∈ hemisphereComplex R}}
    (ht : t ∈ (refinement R r c).support) :
    ∀ x ∈ t.val, ∀ y ∈ t.val, dist x y ≤ (((n:ℝ)-1)/n)^r * D := by
  induction r generalizing t with
  | zero => simpa only [refinement, LinearMap.id_apply, pow_zero, one_mul] using hmesh t ht
  | succ r ih =>
    change t ∈ (subdivMap (hemisphereComplex R) (hemisphereComplex R) barycenter
      (refinement R r c)).support at ht
    obtain ⟨s,hs,hts⟩ := support_linearMap _ _ _ _ ht
    rw [subdivMap_simplex _ _ _ s.property] at hts
    have hdeg := refinement_degree R r n hc hs
    change s.val.card = n at hdeg
    have hn : 0 < n := hdeg ▸ s.property.1.card_pos
    have hfac : 0 ≤ ((n:ℝ)-1)/n := by
      have hh : (1:ℝ) ≤ n := by exact_mod_cast hn
      exact div_nonneg (by linarith) (by positivity)
    have hh := subdivSimplex_mesh R s.val n (le_of_eq hdeg)
      ((((n:ℝ)-1)/n)^r * D) (mul_nonneg (pow_nonneg hfac _) hD) (ih hs) hts
    simpa only [pow_succ', mul_assoc] using hh
omit [DecidableEq E] in
lemma hemisphere_mesh_two (R : ℝ) {s : Finset E} (hs : s ∈ hemisphereComplex R)
    {x y : E} (hx : x ∈ s) (hy : y ∈ s) : dist x y ≤ 2 := by
  obtain ⟨_, _, _, unit_norm⟩ := hs
  calc
    dist x y ≤ ‖x‖ + ‖y‖ := dist_le_norm_add_norm x y
    _ ≤ 2 := by linarith [(unit_norm x hx).1, (unit_norm y hy).1]
lemma refinement_mesh_uniform (R : ℝ) (r n d : ℕ) (hd : d ≤ n)
    {c : Chain (hemisphereComplex R : PreComplex E)}
    (hc : c ∈ degreeChains (hemisphereComplex R) d)
    {t : {s : Finset E // s ∈ hemisphereComplex R}}
    (ht : t ∈ (refinement R r c).support) :
    ∀ x ∈ t.val, ∀ y ∈ t.val, dist x y ≤ (((n:ℝ)-1)/n)^r * 2 := by
  have hdeg := refinement_degree R r d hc ht
  have htpos := t.property.1.card_pos
  change t.val.card = d at hdeg
  have hdpos : 0 < d := hdeg ▸ htpos
  have hfac : 0 ≤ ((d:ℝ)-1)/d := by
    have hh : (1:ℝ) ≤ d := by exact_mod_cast hdpos
    exact div_nonneg (by linarith) (by positivity)
  have hm := refinement_mesh R r d hc (D := 2) (by norm_num)
    (fun simplex _ _ first_mem _ second_mem =>
      hemisphere_mesh_two R simplex.property first_mem second_mem) ht
  intro x hx y hy
  exact (hm x hx y hy).trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ hfac (barycenter_mesh_factor hdpos hd) r) (by norm_num))
end SimplicialChains
end

section
namespace SimplicialChains
open Finset
noncomputable def maxIndex {m : ℕ} [NeZero m] (g : Fin m → ℝ) : Fin m :=
  (Finset.exists_max_image Finset.univ g Finset.univ_nonempty).choose
lemma maxIndex_le {m : ℕ} [NeZero m] (g : Fin m → ℝ) (i : Fin m) :
    g i ≤ g (maxIndex g) :=
  (Finset.exists_max_image Finset.univ g Finset.univ_nonempty).choose_spec.2 i (Finset.mem_univ _)
noncomputable def peakIndex {m : ℕ} [NeZero m] (y : Euc (Fin m)) : Fin m :=
  maxIndex (fun i => |y i|)
lemma peakIndex_neg {m : ℕ} [NeZero m] (y : Euc (Fin m)) :
    peakIndex (-y) = peakIndex y := by
  unfold peakIndex
  congr 1
  ext i
  simp
lemma euclidean_norm_le_sum_abs {m : ℕ} (y : Euc (Fin m)) :
    ‖y‖ ≤ ∑ i, |y i| := by
  have hy : y = ∑ i, EuclideanSpace.single i (y i) := by
    ext i
    simp
  calc
    ‖y‖ = ‖∑ i, EuclideanSpace.single i (y i)‖ := congrArg norm hy
    _ ≤ ∑ i, ‖EuclideanSpace.single i (y i)‖ := norm_sum_le _ _
    _ = ∑ i, |y i| := by simp
lemma peak_large {m : ℕ} [NeZero m] (y : Euc (Fin m)) (hy : ‖y‖ = 1) :
    (1:ℝ) / m ≤ |y (peakIndex y)| := by
  have h := euclidean_norm_le_sum_abs y
  rw [hy] at h
  have hsum : ∑ i : Fin m, |y i| ≤ (m:ℝ) * |y (peakIndex y)| := by
    calc
      ∑ i : Fin m, |y i| ≤ ∑ _ : Fin m, |y (peakIndex y)| :=
        Finset.sum_le_sum (fun i _ => maxIndex_le (fun j => |y j|) i)
      _ = _ := by simp
  exact (div_le_iff₀ (by exact_mod_cast NeZero.pos m)).mpr (by nlinarith)
noncomputable def sphereLabel {m : ℕ} [NeZero m] (y : Euc (Fin m)) : SignedVertex :=
  ((peakIndex y).val, decide (y (peakIndex y) < 0))
lemma sphereLabel_bound {m : ℕ} [NeZero m] (y : Euc (Fin m)) :
    (sphereLabel y).1 < m := (peakIndex y).isLt
lemma sphereLabel_neg {m : ℕ} [NeZero m] (y : Euc (Fin m)) (hy : ‖y‖ = 1) :
    sphereLabel (-y) = flip (sphereLabel y) := by
  have hpeak : y (peakIndex y) ≠ 0 := by
    have h := peak_large y hy
    have hm : (0:ℝ) < (1:ℝ)/m := div_pos zero_lt_one (by exact_mod_cast NeZero.pos m)
    intro he
    rw [he, abs_zero] at h
    linarith
  apply Prod.ext
  · simp only [sphereLabel, peakIndex_neg, flip_apply]
  · simp only [sphereLabel, peakIndex_neg, flip_apply, PiLp.neg_apply]
    by_cases h : y (peakIndex y) < 0
    · have h' : ¬ -y (peakIndex y) < 0 := by linarith
      simp [h,h']
    · have h' : -y (peakIndex y) < 0 := by rcases lt_or_gt_of_ne hpeak with hn | hp <;> linarith
      simp [h,h']
lemma sphereLabel_compatible {m : ℕ} [NeZero m]
    (y z : Euc (Fin m)) (hy : ‖y‖ = 1) (hz : ‖z‖ = 1)
    (hd : dist y z < (1:ℝ)/m) (hi : (sphereLabel y).1 = (sphereLabel z).1) :
    sphereLabel y = sphereLabel z := by
  have he : peakIndex y = peakIndex z := Fin.ext hi
  have hcoord : |y (peakIndex y) - z (peakIndex y)| ≤ dist y z := by
    simpa only [Real.dist_eq] using PiLp.dist_apply_le y z (peakIndex y)
  have hym := peak_large y hy
  have hzm := peak_large z hz
  rw [← he] at hzm
  apply Prod.ext hi
  change decide (y (peakIndex y) < 0) = decide (z (peakIndex z) < 0)
  rw [← he]
  congr 1
  apply propext
  constructor
  · intro hyneg
    by_contra hzneg
    have hzpos := le_of_not_gt hzneg
    rw [abs_of_neg hyneg] at hym
    rw [abs_of_nonpos (by linarith)] at hcoord
    linarith
  · intro hzneg
    by_contra hyneg
    have hypos := le_of_not_gt hyneg
    rw [abs_of_neg hzneg] at hzm
    rw [abs_of_nonneg (by linarith)] at hcoord
    linarith
end SimplicialChains
end

section
namespace SimplicialChains
open Finset
open scoped RealInnerProductSpace
noncomputable def fineCrossMap (n r : ℕ) :
    Chain (cross n) →ₗ[F₂] Chain (hemisphereComplex (n:ℝ) :
      PreComplex (Euc (Fin n))) :=
  (refinement (n:ℝ) r).comp (crossGeometricMap n)
lemma fineCrossMap_boundary (n r : ℕ) :
    (boundary (hemisphereComplex (n:ℝ))).comp (fineCrossMap n r) =
      (fineCrossMap n r).comp (boundary (cross n)) := by
  rw [fineCrossMap, ← LinearMap.comp_assoc, refinement_boundary,
    LinearMap.comp_assoc, crossGeometricMap_boundary, ← LinearMap.comp_assoc]
lemma fineCrossMap_augmentation (n r : ℕ) :
    (augmentation (hemisphereComplex (n:ℝ))).comp (fineCrossMap n r) = augmentation (cross n) := by
  rw [fineCrossMap, ← LinearMap.comp_assoc, refinement_augmentation,
    crossGeometricMap_augmentation]
lemma fineCrossMap_norm (n r : ℕ) :
    (normMap (hemisphereComplex (n:ℝ)) (Equiv.neg _)).comp (fineCrossMap n r) =
      (fineCrossMap n r).comp (normMap (cross n) flip) := by
  rw [fineCrossMap, ← LinearMap.comp_assoc, refinement_norm,
    LinearMap.comp_assoc, crossGeometricMap_norm, ← LinearMap.comp_assoc]
lemma fineCrossMap_degree (n r d : ℕ) :
    degreeChains (cross n) d ≤ (degreeChains (hemisphereComplex (n:ℝ)) d).comap
      (fineCrossMap n r) := by
  intro c hc
  change refinement (n:ℝ) r (crossGeometricMap n c) ∈ degreeChains (hemisphereComplex (n:ℝ)) d
  exact refinement_degree (E := Euc (Fin n)) (n:ℝ) r d
    (crossGeometricMap_degree n d hc)
lemma fineCrossMap_simplex_mesh (n r : ℕ) {s : Finset SignedVertex} (hs : s ∈ cross n)
    {t : {s : Finset (Euc (Fin n)) // s ∈ hemisphereComplex (n:ℝ)}}
    (ht : t ∈ (fineCrossMap n r (simplex (cross n) s)).support) :
    ∀ x ∈ t.val, ∀ y ∈ t.val, dist x y ≤ (((n:ℝ)-1)/n)^r * 2 := by
  apply refinement_mesh_uniform (n:ℝ) r n s.card (cross_card n s hs)
    (crossGeometricMap_degree n s.card (simplex_mem_degree _ hs)) ht
def annulus (n : ℕ) : Set (Euc (Fin n)) :=
  {x | (1:ℝ)/n ≤ ‖x‖ ∧ ‖x‖ ≤ 1}
lemma annulus_compact (n : ℕ) : IsCompact (annulus n) := by
  apply (isCompact_closedBall (0 : Euc (Fin n)) 1).of_isClosed_subset
  · exact (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  · intro x hx
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx.2
lemma hemisphere_vertex_annulus (n : ℕ) (hn : 0 < n)
    {s : Finset (Euc (Fin n))} (hs : s ∈ hemisphereComplex (n:ℝ))
    {x : Euc (Fin n)} (hx : x ∈ s) : x ∈ annulus n := by
  obtain ⟨_,w,hw,hh⟩ := hs
  refine ⟨?_,(hh x hx).1⟩
  apply (div_le_iff₀ (by exact_mod_cast hn)).mpr
  have h := real_inner_le_norm w x
  rw [(hh x hx).2] at h
  calc
    1 ≤ ‖w‖ * ‖x‖ := h
    _ ≤ (n:ℝ) * ‖x‖ := mul_le_mul_of_nonneg_right hw (norm_nonneg x)
    _ = ‖x‖ * (n:ℝ) := mul_comm _ _
lemma annular_odd_dimension_bound (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (g : Euc (Fin n) → Euc (Fin m))
    (hg : ContinuousOn g (annulus n)) (hgn : ∀ x ∈ annulus n, ‖g x‖ = 1)
    (hgo : ∀ x ∈ annulus n, g (-x) = -g x) : n ≤ m := by
  classical
  let : NeZero m := ⟨by omega⟩
  have hunif := (annulus_compact n).uniformContinuousOn_of_continuous hg
  obtain ⟨δ,hδ,hclose⟩ := Metric.uniformContinuousOn_iff.mp hunif ((1:ℝ)/m)
    (div_pos zero_lt_one (by exact_mod_cast hm))
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hq : ((n:ℝ)-1)/n < 1 := (div_lt_one hn').mpr (by linarith)
  obtain ⟨r,hr⟩ := exists_pow_lt_of_lt_one (show (0:ℝ) < δ/2 by linarith) hq
  have hmeshδ : (((n:ℝ)-1)/n)^r * 2 < δ := by linarith
  let K : PreComplex (Euc (Fin n)) := hemisphereComplex (n:ℝ)
  let f : Euc (Fin n) → SignedVertex := fun x => sphereLabel (g x)
  let U : Chain K →ₗ[F₂] Chain (cross m) := mapChains K (cross m) f
  let T : Chain (cross n) →ₗ[F₂] Chain (cross m) := U.comp (fineCrossMap n r)
  have hfine (s : Finset SignedVertex) (hs : s ∈ cross n)
      (t : {s : Finset (Euc (Fin n)) // s ∈ K})
      (ht : t ∈ (fineCrossMap n r (simplex (cross n) s)).support) : t.val.image f ∈ cross m := by
    refine ⟨t.property.1.image _, ?_, ?_⟩
    · intro v hv
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
      exact sphereLabel_bound (g x)
    · intro v hv w hw he
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hw
      have hxa := hemisphere_vertex_annulus n hn t.property hx
      have hya := hemisphere_vertex_annulus n hn t.property hy
      apply sphereLabel_compatible (g x) (g y) (hgn x hxa) (hgn y hya) _ he
      exact hclose x hxa y hya ((fineCrossMap_simplex_mesh n r hs ht x hx y hy).trans_lt hmeshδ)
  have hdb : (boundary (cross m)).comp T = T.comp (boundary (cross n)) := by
    apply Finsupp.lhom_ext
    intro s a
    have hh : boundary (cross m) (T (simplex (cross n) s.val)) =
        T (boundary (cross n) (simplex (cross n) s.val)) := by
      change boundary (cross m) (mapChains K (cross m) f
        (fineCrossMap n r (simplex (cross n) s.val))) = _
      rw [mapChains_boundary_of_support K (cross m) f _ (hfine s.val s.property)]
      have hb := LinearMap.congr_fun (fineCrossMap_boundary n r) (simplex (cross n) s.val)
      rw [LinearMap.comp_apply, LinearMap.comp_apply] at hb
      rw [hb]
      rfl
    rw [simplex_of_mem (cross n) s.property] at hh
    have ha : Finsupp.single s a = a • Finsupp.single s (1:F₂) := by simp
    simp only [LinearMap.comp_apply, ha, map_smul, hh]
  have haug : (augmentation (cross m)).comp T = augmentation (cross n) := by
    apply Finsupp.lhom_ext
    intro s a
    have hh : augmentation (cross m) (T (simplex (cross n) s.val)) =
        augmentation (cross n) (simplex (cross n) s.val) := by
      change augmentation (cross m) (mapChains K (cross m) f
        (fineCrossMap n r (simplex (cross n) s.val))) = _
      rw [mapChains_augmentation_of_support K (cross m) f _ (hfine s.val s.property)]
      exact LinearMap.congr_fun (fineCrossMap_augmentation n r) _
    rw [simplex_of_mem (cross n) s.property] at hh
    have ha : Finsupp.single s a = a • Finsupp.single s (1:F₂) := by simp
    simp only [LinearMap.comp_apply, ha, map_smul, hh]
  have hnorm : (normMap (cross m) flip).comp T = T.comp (normMap (cross n) flip) := by
    have hu : (normMap (cross m) flip).comp U = U.comp (normMap K (Equiv.neg _)) := by
      apply mapChains_norm K (cross m) (Equiv.neg _) flip
        (hemisphere_neg (n:ℝ)) (cross_flip m) f
      intro s hs x hx
      have hxa := hemisphere_vertex_annulus n hn hs hx
      change sphereLabel (g (-x)) = flip (sphereLabel (g x))
      rw [hgo x hxa, sphereLabel_neg _ (hgn x hxa)]
    change (normMap (cross m) flip).comp (U.comp (fineCrossMap n r)) =
      (U.comp (fineCrossMap n r)).comp (normMap (cross n) flip)
    rw [← LinearMap.comp_assoc, hu, LinearMap.comp_assoc,
      fineCrossMap_norm, ← LinearMap.comp_assoc]
  apply cross_chain_dimension_bound n m T hdb hnorm haug
  intro d c hc
  change mapChains K (cross m) f (fineCrossMap n r c) ∈ degreeChains (cross m) d
  exact mapChains_degree_all K (cross m) f d (fineCrossMap_degree n r d hc)
end SimplicialChains
end

section
namespace SimplicialChains
open Finset
open scoped RealInnerProductSpace
noncomputable def unitRadial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (x : E) : E :=
  ‖x‖⁻¹ • x
lemma unitRadial_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x : E} (hx : x ≠ 0) : ‖unitRadial x‖ = 1 := by
  rw [unitRadial, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
lemma unitRadial_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (x : E) :
    unitRadial (-x) = -unitRadial x := by simp [unitRadial]
lemma unitRadial_continuousOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} (hS : ∀ x ∈ S, x ≠ 0) : ContinuousOn unitRadial S := by
  exact (continuous_norm.continuousOn.inv₀ (fun x hx => norm_ne_zero_iff.mpr (hS x hx))).smul
    continuous_id.continuousOn
lemma odd_sphere_dimension_bound (n m : ℕ) (hn : 0 < n)
    (f : Euc (Fin n) → Euc (Fin m))
    (hf : ContinuousOn f {x | ‖x‖ = 1}) (hfn : ∀ x, ‖x‖ = 1 → ‖f x‖ = 1)
    (hfo : ∀ x, ‖x‖ = 1 → f (-x) = -f x) : n ≤ m := by
  by_cases hm : 0 < m
  · have ha : ∀ x ∈ annulus n, x ≠ 0 := by
      intro x hx hzero
      have hn' : (0:ℝ) < n := by exact_mod_cast hn
      have hp : (0:ℝ) < 1/(n:ℝ) := div_pos zero_lt_one hn'
      simp only [annulus, Set.mem_ofPred_eq, hzero, norm_zero] at hx
      linarith [hx.1]
    apply annular_odd_dimension_bound n m hn hm (fun x => f (unitRadial x))
    · exact hf.comp (unitRadial_continuousOn ha) (fun x hx => unitRadial_norm (ha x hx))
    · intro x hx
      exact hfn _ (unitRadial_norm (ha x hx))
    · intro x hx
      rw [unitRadial_neg, hfo _ (unitRadial_norm (ha x hx))]
  · have hm0 : m = 0 := by omega
    subst m
    let x : Euc (Fin n) := EuclideanSpace.single ⟨0,hn⟩ 1
    have hx : ‖x‖ = 1 := by simp [x]
    have hzero : f x = 0 := Subsingleton.elim _ _
    have hh := hfn x hx
    rw [hzero, norm_zero] at hh
    exact False.elim (zero_ne_one hh)
noncomputable def dropLast (n : ℕ) :
    Euc (Fin (n+1)) →ₗ[ℝ] Euc (Fin n) where
  toFun x := WithLp.toLp 2 (fun i => x i.castSucc)
  map_add' x y := by ext i; rfl
  map_smul' a x := by ext i; rfl
lemma dropLast_zero_iff (n : ℕ) (x : Euc (Fin (n+1))) :
    dropLast n x = 0 ↔ x = x (Fin.last n) • EuclideanSpace.single (Fin.last n) 1 := by
  constructor
  · intro hx
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · have hj := congrArg (fun y : Euc (Fin n) => y j) hx
      simpa [dropLast] using hj
  · intro hx
    rw [hx]
    ext i
    simp [dropLast]
lemma dropLast_nonzero (n : ℕ) (x : Euc (Fin (n+1))) (hx : ‖x‖ = 1)
    (hxp : x ≠ EuclideanSpace.single (Fin.last n) 1)
    (hxm : x ≠ -EuclideanSpace.single (Fin.last n) 1) : dropLast n x ≠ 0 := by
  intro hz
  have he := (dropLast_zero_iff n x).mp hz
  have ha : |x (Fin.last n)| = 1 := by
    conv_rhs => rw [← hx, he]
    simp [norm_smul]
  rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp ha with hp | hm
  · apply hxp
    simpa [hp] using he
  · apply hxm
    simpa [hm] using he
lemma odd_sphere_surjective (n : ℕ)
    (f : Euc (Fin (n+1)) → Euc (Fin (n+1)))
    (hf : ContinuousOn f {x | ‖x‖ = 1}) (hfn : ∀ x, ‖x‖ = 1 → ‖f x‖ = 1)
    (hfo : ∀ x, ‖x‖ = 1 → f (-x) = -f x) :
    ∀ y, ‖y‖ = 1 → ∃ x, ‖x‖ = 1 ∧ f x = y := by
  intro y hy
  by_contra hmiss
  push Not at hmiss
  let e : Euc (Fin (n+1)) := EuclideanSpace.single (Fin.last n) 1
  have he : ‖e‖ = 1 := by simp [e]
  let R : Euc (Fin (n+1)) ≃ₗᵢ[ℝ] Euc (Fin (n+1)) :=
    Submodule.reflection (ℝ ∙ (y-e))ᗮ
  have hRy : R y = e := Submodule.reflection_sub (hy.trans he.symm)
  have hnzero (x : Euc (Fin (n+1))) (hx : ‖x‖ = 1) :
      dropLast n (R (f x)) ≠ 0 := by
    apply dropLast_nonzero n (R (f x)) (by rw [R.norm_map, hfn x hx])
    · intro hp
      exact hmiss x hx (R.injective (hp.trans hRy.symm))
    · intro hm
      have hneg : R (f (-x)) = e := by rw [hfo x hx, map_neg, hm, neg_neg]
      exact hmiss (-x) (by simpa using hx) (R.injective (hneg.trans hRy.symm))
  let g : Euc (Fin (n+1)) → Euc (Fin n) :=
    fun x => unitRadial (dropLast n (R (f x)))
  have hicont : ContinuousOn (fun x => dropLast n (R (f x))) {x | ‖x‖ = 1} :=
    (dropLast n).continuous_of_finiteDimensional.comp_continuousOn (R.continuous.comp_continuousOn hf)
  have hgc : ContinuousOn g {x | ‖x‖ = 1} := by
    apply (unitRadial_continuousOn (S := {z : Euc (Fin n) | z ≠ 0})
      (fun _ h => h)).comp hicont
    exact fun x hx => hnzero x hx
  have hgn (x) (hx : ‖x‖ = 1) : ‖g x‖ = 1 := unitRadial_norm (hnzero x hx)
  have hgo (x) (hx : ‖x‖ = 1) : g (-x) = -g x := by
    dsimp [g]
    rw [hfo x hx, map_neg, map_neg, unitRadial_neg]
  have hd := odd_sphere_dimension_bound (n+1) n (by omega) g hgc hgn hgo
  omega
end SimplicialChains
end

section
namespace SimplicialChains
lemma odd_sphere_dimension_bound_fintype {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] (f : Euc α → Euc β)
    (hf : ContinuousOn f {x | ‖x‖ = 1}) (hfn : ∀ x, ‖x‖ = 1 → ‖f x‖ = 1)
    (hfo : ∀ x, ‖x‖ = 1 → f (-x) = -f x) : Fintype.card α ≤ Fintype.card β := by
  let A := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fintype.equivFin α)
  let B := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fintype.equivFin β)
  apply odd_sphere_dimension_bound (Fintype.card α) (Fintype.card β)
    Fintype.card_pos (fun x => B (f (A.symm x)))
  · exact B.continuous.comp_continuousOn (hf.comp A.symm.continuous.continuousOn
      (fun x hx => by simpa using hx))
  · intro x hx
    rw [B.norm_map, hfn _ (by simpa using hx)]
  · intro x hx
    rw [map_neg, hfo _ (by simpa using hx), map_neg]
lemma odd_sphere_surjective_fintype {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] (hc : Fintype.card α = Fintype.card β)
    (f : Euc α → Euc β)
    (hf : ContinuousOn f {x | ‖x‖ = 1}) (hfn : ∀ x, ‖x‖ = 1 → ‖f x‖ = 1)
    (hfo : ∀ x, ‖x‖ = 1 → f (-x) = -f x) :
    ∀ y, ‖y‖ = 1 → ∃ x, ‖x‖ = 1 ∧ f x = y := by
  obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt (Fintype.card_pos (α := α)))
  let ea : α ≃ Fin (n+1) := (Fintype.equivFin α).trans (finCongr hn)
  let eb : β ≃ Fin (n+1) := (Fintype.equivFin β).trans (finCongr (hc.symm.trans hn))
  let A := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ ea
  let B := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ eb
  have hg := odd_sphere_surjective n (fun x => B (f (A.symm x)))
    (B.continuous.comp_continuousOn (hf.comp A.symm.continuous.continuousOn
      (fun x hx => by simpa using hx)))
    (fun x hx => by rw [B.norm_map, hfn _ (by simpa using hx)])
    (fun x hx => by rw [map_neg, hfo _ (by simpa using hx), map_neg])
  intro y hy
  obtain ⟨x,hx,he⟩ := hg (B y) (by simpa using hy)
  exact ⟨A.symm x, by simpa using hx, B.injective he⟩
end SimplicialChains
section
open scoped RealInnerProductSpace
section LabelBound
variable {ν ι : Type*} [Fintype ν] [LinearOrder ν] [Nonempty ν] [Fintype ι]
lemma Admissible.label_bound {f : Euc ν → ι → ℝ} (hf : Admissible f) :
    Fintype.card (UpperTriangle ν) ≤ Fintype.card ι := by
  let : Nonempty (UpperTriangle ν) := by
    obtain ⟨index⟩ := ‹Nonempty ν›
    exact ⟨⟨(index, index), le_rfl⟩⟩
  exact SimplicialChains.odd_sphere_dimension_bound_fintype (sphereExtension f)
    hf.sphereExtension_continuousOn (fun _ hx => hf.sphereExtension_norm hx)
    (fun x _ => sphereExtension_odd f x)
lemma Admissible.sphereExtension_surjective {f : Euc ν → ι → ℝ}
    (hf : Admissible f) (hc : Fintype.card (UpperTriangle ν) = Fintype.card ι) :
    ∀ y, ‖y‖ = 1 → ∃ x, ‖x‖ = 1 ∧ sphereExtension f x = y := by
  let : Nonempty (UpperTriangle ν) := by
    obtain ⟨index⟩ := ‹Nonempty ν›
    exact ⟨⟨(index, index), le_rfl⟩⟩
  exact SimplicialChains.odd_sphere_surjective_fintype hc (sphereExtension f)
    hf.sphereExtension_continuousOn (fun _ hx => hf.sphereExtension_norm hx)
    (fun x _ => sphereExtension_odd f x)
lemma Admissible.signedExtension_ray {f : Euc ν → ι → ℝ}
    (hf : Admissible f) (hc : Fintype.card (UpperTriangle ν) = Fintype.card ι)
    {y : ι → ℝ} (hy : y ≠ 0) :
    ∃ A : SqMat ν, IsSelfAdjoint A ∧ ∃ t : ℝ, 0 < t ∧ signedExtension f A = t • y := by
  let Y : Euc ι := WithLp.toLp 2 y
  have hY : Y ≠ 0 := fun hh => hy (WithLp.toLp_injective 2 hh)
  obtain ⟨x,hx,he⟩ := hf.sphereExtension_surjective hc (SimplicialChains.unitRadial Y)
    (SimplicialChains.unitRadial_norm hY)
  let A := symmetricCoordinates x
  have hA : A ≠ 0 := by
    intro hzero
    have hh : x = 0 := symmetricCoordinates_injective (hzero.trans (map_zero _).symm)
    simp [hh] at hx
  have hs : signedExtension f A ≠ 0 := fun hh => hA
    ((hf.signedExtension_eq_zero_iff (symmetricCoordinates_selfAdjoint x)).mp hh)
  let Z : Euc ι := WithLp.toLp 2 (signedExtension f A)
  have hZ : Z ≠ 0 := fun hh => hs (WithLp.toLp_injective 2 hh)
  refine ⟨A, symmetricCoordinates_selfAdjoint x, ‖Z‖ / ‖Y‖,
    div_pos (norm_pos_iff.mpr hZ) (norm_pos_iff.mpr hY), ?_⟩
  change ‖Z‖⁻¹ • Z = ‖Y‖⁻¹ • Y at he
  have he' := congrArg (fun z => ‖Z‖ • z) he
  rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hZ), one_smul, smul_smul,
    ← div_eq_mul_inv] at he'
  exact WithLp.toLp_injective 2 he'
end LabelBound
end
end

section
section
open scoped RealInnerProductSpace
section Restrict
variable {V W ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [Fintype ι]
lemma Admissible.comp_isometry {f : V → ι → ℝ} (hf : Admissible f) (e : W →ₗᵢ[ℝ] V) :
    Admissible (fun x => f (e x)) := by
  refine ⟨fun i => (hf.smooth i).comp e.contDiff,?_,?_,?_,?_⟩
  · intro x i
    rw [map_neg,hf.antipodal]
  · intro x hx i
    exact hf.nonneg _ ((e.norm_map x).trans hx) i
  · intro x hx
    exact hf.sum_one _ ((e.norm_map x).trans hx)
  · intro x y hx hy hxy i
    exact hf.orthogonal _ _ ((e.norm_map x).trans hx) ((e.norm_map y).trans hy)
      ((e.inner_map_map x y).trans hxy) i
lemma Admissible.restrict_labels {f : V → ι → ℝ} (hf : Admissible f)
    (s : Finset ι) (hzero : ∀ x, ‖x‖ = 1 → ∀ i ∉ s, f x i = 0) :
    Admissible (fun x (i : s) => f x i.val) := by
  classical
  refine ⟨fun i => hf.smooth i.val,fun x i => hf.antipodal x i.val,
    fun x hx i => hf.nonneg x hx i.val,?_,fun x y hx hy hxy i => hf.orthogonal x y hx hy hxy i.val⟩
  intro x hx
  rw [← hf.sum_one x hx]
  rw [Finset.sum_coe_sort]
  exact Finset.sum_subset (Finset.subset_univ s) (fun i _ hi => hzero x hx i hi)
end Restrict
lemma orthogonal_isometry (k : ℕ) {u : Euc (Fin (k+1))} (hu : ‖u‖ = 1) :
    ∃ e : Euc (Fin k) →ₗᵢ[ℝ] Euc (Fin (k+1)),
      ∀ x, ⟪u,e x⟫ = 0 := by
  let W := (Submodule.span ℝ {u})ᗮ
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  have hdim : Module.finrank ℝ W = k := by
    let : Fact (Module.finrank ℝ (Euc (Fin (k+1))) = k+1) := ⟨by simp⟩
    exact Submodule.finrank_orthogonal_span_singleton hu0
  let b := (stdOrthonormalBasis ℝ W).reindex (finCongr hdim)
  refine ⟨W.subtypeₗᵢ.comp b.repr.symm.toLinearIsometry,?_⟩
  intro x
  exact (Submodule.mem_orthogonal_singleton_iff_inner_right.mp (b.repr.symm x).property)
lemma Admissible.support_card_four_le {f : Vector4 → Fin 10 → ℝ} (hf : Admissible f)
    {u : Vector4} (hu : ‖u‖ = 1) : (positiveSupport f u).card ≤ 4 := by
  classical
  obtain ⟨e,he⟩ := orthogonal_isometry 3 hu
  let s := (positiveSupport f u)ᶜ
  have hzero : ∀ x, ‖x‖ = 1 → ∀ i ∉ s, f (e x) i = 0 := by
    intro x hx i hi
    have hip : 0 < f u i := (mem_positiveSupport _ _ _).mp (by simpa [s] using hi)
    have hn := hf.nonneg (e x) (by simpa using hx) i
    exact le_antisymm (le_of_not_gt (fun hp => hf.orthogonal u (e x) hu
      (by simpa using hx) (he x) i ⟨hip,hp⟩)) hn
  have hb := ((hf.comp_isometry e).restrict_labels s hzero).label_bound
  have hc : Fintype.card (UpperTriangle (Fin 3)) = 6 := by decide
  rw [hc,Fintype.card_coe,Finset.card_compl] at hb
  rw [Fintype.card_fin] at hb
  omega
end
end

section
section
open scoped RealInnerProductSpace
section Chambers
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
def safeNormals (Z : Set E) : Set E := {x | ∀ z ∈ Z, ⟪x,z⟫ ≠ 0}
def signChamber (Z : Set E) (c : E) : Set E := {x | ∀ z ∈ Z, 0 < ⟪c,z⟫ * ⟪x,z⟫}
lemma mem_signChamber_self {Z : Set E} {c : E} (hc : c ∈ safeNormals Z) :
    c ∈ signChamber Z c := by
  intro z hz
  exact mul_self_pos.mpr (hc z hz)
lemma signChamber_subset_safeNormals (Z : Set E) (c : E) :
    signChamber Z c ⊆ safeNormals Z := by
  intro x hx z hz h
  simpa [h] using hx z hz
lemma signChamber_convex (Z : Set E) (c : E) : Convex ℝ (signChamber Z c) := by
  intro x hx y hy a b ha hb hab z hz
  simp only [inner_add_left,real_inner_smul_left,mul_add]
  have h1 := hx z hz
  have h2 := hy z hz
  have hn1 := mul_nonneg ha h1.le
  have hn2 := mul_nonneg hb h2.le
  have he : ⟪c,z⟫ * (a * ⟪x,z⟫) + ⟪c,z⟫ * (b * ⟪y,z⟫) =
      a * (⟪c,z⟫ * ⟪x,z⟫) + b * (⟪c,z⟫ * ⟪y,z⟫) := by ring
  rw [he]
  rcases lt_or_eq_of_le ha with ha' | ha'
  · exact add_pos_of_pos_of_nonneg (mul_pos ha' h1) hn2
  · have hb' : b = 1 := by linarith
    simp [← ha',hb',h2]
lemma signChamber_eq_of_mem {Z : Set E} {c d x : E}
    (hc : x ∈ signChamber Z c) (hd : x ∈ signChamber Z d) :
    signChamber Z c = signChamber Z d := by
  ext y
  constructor <;> intro hy z hz
  · have h1 := hc z hz
    have h2 := hd z hz
    have h3 := hy z hz
    rcases mul_pos_iff.mp h1 with h1 | h1 <;>
      rcases mul_pos_iff.mp h2 with h2 | h2 <;>
      rcases mul_pos_iff.mp h3 with h3 | h3
    all_goals first | exact mul_pos h2.1 h3.2 | exact mul_pos_of_neg_of_neg h2.1 h3.2 | linarith [h1.1,h1.2,h2.1,h2.2,h3.1,h3.2]
  · have h1 := hc z hz
    have h2 := hd z hz
    have h3 := hy z hz
    rcases mul_pos_iff.mp h1 with h1 | h1 <;>
      rcases mul_pos_iff.mp h2 with h2 | h2 <;>
      rcases mul_pos_iff.mp h3 with h3 | h3
    all_goals first | exact mul_pos h1.1 h3.2 | exact mul_pos_of_neg_of_neg h1.1 h3.2 | linarith [h1.1,h1.2,h2.1,h2.2,h3.1,h3.2]
lemma signChamber_eq_or_disjoint (Z : Set E) (c d : E) :
    signChamber Z c = signChamber Z d ∨ Disjoint (signChamber Z c) (signChamber Z d) := by
  by_cases h : Disjoint (signChamber Z c) (signChamber Z d)
  · exact Or.inr h
  · rw [Set.disjoint_left] at h
    push Not at h
    obtain ⟨x,hc,hd⟩ := h
    exact Or.inl (signChamber_eq_of_mem hc hd)
lemma interior_safe_mem_chamber {Z : Set E} {c x : E}
    (hx : x ∈ interior (safeNormals Z)) (hxc : x ∈ signChamber Z c) :
    x ∈ interior (signChamber Z c) := by
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset (Metric.ball_mem_nhds x hε)
  intro y hy z hz
  have hc := hxc z hz
  have hn : ∀ w ∈ Metric.ball x ε, ⟪w,z⟫ ≠ 0 := fun w hw => hball hw z hz
  have hf : ContinuousOn (fun w : E => ⟪w,z⟫) (Metric.ball x ε) :=
    (continuous_id.inner continuous_const).continuousOn
  have hxball : x ∈ Metric.ball x ε := Metric.mem_ball_self hε
  rcases mul_pos_iff.mp hc with hc | hc
  · exact mul_pos hc.1 ((convex_ball x ε).isPreconnected.lt_of_ne hf hn ⟨x,hxball,hc.2⟩ hy)
  · exact mul_pos_of_neg_of_neg hc.1 ((convex_ball x ε).isPreconnected.gt_of_ne hf hn ⟨x,hxball,hc.2⟩ hy)
lemma interior_safe_mem_own_chamber {Z : Set E} {c : E}
    (hc : c ∈ interior (safeNormals Z)) : c ∈ interior (signChamber Z c) :=
  interior_safe_mem_chamber hc (mem_signChamber_self (interior_subset hc))
lemma compact_finite_chambers {Z K : Set E} (hK : IsCompact K)
    (hsub : K ⊆ interior (safeNormals Z)) :
    ∃ C : Finset E, (↑C : Set E) ⊆ K ∧ K ⊆ ⋃ c ∈ (↑C : Set E), interior (signChamber Z c) := by
  classical
  obtain ⟨C,hCK,hCf,hcover⟩ := hK.elim_finite_subcover_image
    (b := K) (c := fun c : E => interior (signChamber Z c)) (fun _ _ => isOpen_interior)
    (fun c hc => Set.mem_iUnion₂.mpr ⟨c,hc,interior_safe_mem_own_chamber (hsub hc)⟩)
  exact ⟨hCf.toFinset,by simpa using hCK,by simpa using hcover⟩
end Chambers
end
end

section
section
open scoped RealInnerProductSpace
section ActiveChambers
variable {E W ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [Fintype ι]
def activeVectors (f : E → ι → ℝ) (I : Finset ι) : Set E :=
  {z | ∃ i ∈ I, 0 < homogeneousLift f z i}
def commonPositiveCone (f : E → ι → ℝ) (I : Finset ι) : Set E :=
  {z | ∀ i ∈ I, 0 < homogeneousLift f z i}
lemma Admissible.commonPositiveCone_isOpen {f : E → ι → ℝ} (hf : Admissible f)
    (I : Finset ι) : IsOpen (commonPositiveCone f I) := by
  have he : commonPositiveCone f I =
      ⋂ i ∈ (I : Set ι), {x | 0 < homogeneousLift f x i} := by ext x; simp [commonPositiveCone]
  rw [he]
  exact isOpen_biInter_finset (fun i _ => isOpen_lt continuous_const
    ((continuous_apply i).comp hf.lift_continuous))
lemma Admissible.commonPositiveCone_safe {f : E → ι → ℝ} (hf : Admissible f)
    (I : Finset ι) : commonPositiveCone f I ⊆ safeNormals (activeVectors f I) := by
  intro x hx z hz horth
  obtain ⟨i,hi,hzi⟩ := hz
  have hxz := mul_pos (hx i hi) hzi
  rw [hf.lift_orthogonal horth i] at hxz
  exact (lt_irrefl 0) hxz
lemma Admissible.commonPositiveCone_interior_safe {f : E → ι → ℝ}
    (hf : Admissible f) (I : Finset ι) :
    commonPositiveCone f I ⊆ interior (safeNormals (activeVectors f I)) :=
  interior_maximal (hf.commonPositiveCone_safe I) (hf.commonPositiveCone_isOpen I)
omit [Fintype ι] in
lemma commonPositiveCone_active {f : E → ι → ℝ} {I : Finset ι} (hI : I.Nonempty)
    {c : E} (hc : c ∈ commonPositiveCone f I) : c ∈ activeVectors f I := by
  obtain ⟨i,hi⟩ := hI
  exact ⟨i,hi,hc i hi⟩
end ActiveChambers
end
end

section
section
open scoped RealInnerProductSpace ContDiff
open scoped Manifold
open MeasureTheory Set Metric
open scoped ENNReal Pointwise Matrix
section RankOne
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι]
omit [DecidableEq ν] [Nonempty ν] in
lemma Admissible.lift_smul {f : (Euc ν) → ι → ℝ} (hf : Admissible f) (v : (Euc ν)) (t : ℝ) :
    homogeneousLift f (t • v) = t ^ 2 • homogeneousLift f v := by
  rcases le_total 0 t with ht | ht
  · exact homogeneousLift_smul_nonneg f v ht
  · have h := homogeneousLift_smul_nonneg f v (neg_nonneg.mpr ht)
    rw [neg_smul, hf.lift_even, neg_sq] at h
    exact h
noncomputable def rankOne (u : (Euc ν)) : SqMat ν := fun i j => u i * u j
omit [Nonempty ν] in
lemma rankOne_action (u x : (Euc ν)) : (matrixOp ν) (rankOne u) x = ⟪u, x⟫ • u := by
  ext i
  change ∑ j, (u i * u j) * x j = ⟪u, x⟫ * u i
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  simp only [mul_comm]
omit [DecidableEq ν] [Nonempty ν] in
lemma rankOne_nonneg (u : (Euc ν)) : 0 ≤ rankOne u := by
  apply Matrix.nonneg_iff_posSemidef.mpr
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  constructor
  · ext i j
    simp [rankOne, Matrix.conjTranspose_apply, mul_comm]
  · intro x
    have he : star x ⬝ᵥ (rankOne u) *ᵥ x = (∑ i, u i * x i) ^ 2 := by
      simp only [dotProduct, Matrix.mulVec, rankOne, Pi.star_apply, star_trivial]
      simp_rw [mul_assoc, ← Finset.mul_sum]
      simp_rw [← mul_assoc, mul_comm (x _) (u _)]
      rw [← Finset.sum_mul, pow_two]
    rw [he]
    exact sq_nonneg _
omit [DecidableEq ν] [Nonempty ν] in
lemma rankOne_trace (u : (Euc ν)) : Matrix.trace (rankOne u) = ‖u‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
  simp [Matrix.trace, Matrix.diag, rankOne, pow_two]
omit [Nonempty ν] in
lemma rankOne_mul_self (u : (Euc ν)) (hu : ‖u‖ = 1) : rankOne u * rankOne u = rankOne u := by
  apply ((matrixOp ν)).injective
  rw [map_mul]
  apply ContinuousLinearMap.ext
  intro x
  change (matrixOp ν) (rankOne u) ((matrixOp ν) (rankOne u) x) = (matrixOp ν) (rankOne u) x
  simp only [rankOne_action, inner_smul_right, real_inner_self_eq_norm_sq, hu, one_pow, mul_one]
omit [Nonempty ν] in
lemma rankOne_sqrt (u : (Euc ν)) (hu : ‖u‖ = 1) : CFC.sqrt (rankOne u) = rankOne u :=
  (CFC.sqrt_eq_iff _ _ (rankOne_nonneg u) (rankOne_nonneg u)).mpr
    (rankOne_mul_self u hu)
lemma Admissible.positiveExtension_rankOne {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    (u : (Euc ν)) (hu : ‖u‖ = 1) : positiveExtension f (rankOne u) = f u := by
  have hcoord (x : UnitSphere (Euc ν)) (i : ι) :
      homogeneousLift f ((matrixOp ν) (rankOne u) x) i = ⟪u, (x : (Euc ν))⟫ ^ 2 * f u i := by
    rw [rankOne_action, hf.lift_smul, homogeneousLift_unit f hu]
    rfl
  have hm : (Fintype.card ν : ℝ) *
      ∫ x : UnitSphere (Euc ν), ⟪u, (x : (Euc ν))⟫ ^ 2 ∂sphereProbability (Euc ν) = 1 := by
    have hs := hf.positiveExtension_sum (rankOne_nonneg u)
    rw [rankOne_trace, hu, one_pow] at hs
    simp only [positiveExtension, rankOne_sqrt u hu, integralLift] at hs
    simp_rw [hcoord] at hs
    simp only [integral_mul_const, ← Finset.mul_sum] at hs
    rw [hf.sum_one u hu, mul_one] at hs
    exact hs
  ext i
  simp only [positiveExtension, rankOne_sqrt u hu, integralLift]
  simp_rw [hcoord]
  rw [integral_mul_const, ← mul_assoc, hm, one_mul]
end RankOne
end
end

section
section
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
section SpectralSupport
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι]
lemma Admissible.signedExtension_pos_iff {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    (A : SqMat ν) (i : ι) :
    0 < signedExtension f A i ↔ 0 < positiveExtension f A⁺ i := by
  have hp := hf.positiveExtension_nonneg A⁺ i
  have hn := hf.positiveExtension_nonneg A⁻ i
  have hpn := hf.positiveExtension_orthogonal (CFC.posPart_nonneg A)
    (CFC.negPart_nonneg A) (CFC.posPart_mul_negPart A) i
  change 0 < positiveExtension f A⁺ i - positiveExtension f A⁻ i ↔ _
  constructor
  · intro h; linarith
  · intro h
    have hz := (mul_eq_zero.mp hpn).resolve_left (ne_of_gt h)
    rwa [hz,sub_zero]
lemma Admissible.signedExtension_neg_iff {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    (A : SqMat ν) (i : ι) :
    signedExtension f A i < 0 ↔ 0 < positiveExtension f A⁻ i := by
  have hp := hf.positiveExtension_nonneg A⁺ i
  have hn := hf.positiveExtension_nonneg A⁻ i
  have hpn := hf.positiveExtension_orthogonal (CFC.posPart_nonneg A)
    (CFC.negPart_nonneg A) (CFC.posPart_mul_negPart A) i
  change positiveExtension f A⁺ i - positiveExtension f A⁻ i < 0 ↔ _
  constructor
  · intro h; linarith
  · intro h
    have hz := (mul_eq_zero.mp hpn).resolve_right (ne_of_gt h)
    rw [hz,zero_sub]
    exact neg_neg_of_pos h
lemma Admissible.signedExtension_positive_support {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    (A : SqMat ν) (i : ι) :
    0 < signedExtension f A i ↔ ∃ v : (Euc ν),
      v ∈ LinearMap.range ((matrixOp ν) A⁺).toLinearMap ∧ ‖v‖ = 1 ∧ 0 < f v i := by
  rw [hf.signedExtension_pos_iff,hf.positiveExtension_support (CFC.posPart_nonneg A)]
lemma Admissible.signedExtension_range_labels {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {A : SqMat ν} {I : Finset ι}
    (hI : ∀ i ∉ I, signedExtension f A i ≤ 0)
    {v : (Euc ν)} (hv : v ∈ LinearMap.range ((matrixOp ν) A⁺).toLinearMap) (hvn : ‖v‖ = 1)
    {i : ι} (hi : i ∉ I) : f v i = 0 := by
  apply le_antisymm _ (hf.nonneg v hvn i)
  by_contra hn
  have hp : 0 < f v i := lt_of_not_ge hn
  exact (not_lt_of_ge (hI i hi)) ((hf.signedExtension_positive_support A i).mpr ⟨v,hv,hvn,hp⟩)
omit [DecidableEq ν] [Nonempty ν] in
lemma subspace_eq_span_of_inner_separates (W : Submodule ℝ (Euc ν)) (w u : (Euc ν))
    (hu : u ∈ W) (huw : ⟪w,u⟫ ≠ 0)
    (hsep : ∀ v ∈ W, ⟪w,v⟫ = 0 → v = 0) : W = Submodule.span ℝ {u} := by
  apply le_antisymm
  · intro v hv
    have hz : v - (⟪w,v⟫ / ⟪w,u⟫) • u = 0 := hsep _
      (W.sub_mem hv (W.smul_mem _ hu)) (by rw [inner_sub_right,inner_smul_right]; field_simp; ring)
    rw [sub_eq_zero] at hz
    rw [hz]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton u))
  · exact Submodule.span_le.mpr (by simpa using hu)
lemma Admissible.positive_range_separated {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {A : SqMat ν} {I : Finset ι} {w : (Euc ν)} (hw : ‖w‖ = 1)
    (hwi : ∀ i ∈ I, 0 < f w i)
    (hI : ∀ i ∉ I, signedExtension f A i ≤ 0)
    {v : (Euc ν)} (hv : v ∈ LinearMap.range ((matrixOp ν) A⁺).toLinearMap) (hwv : ⟪w,v⟫ = 0) : v = 0 := by
  by_contra hn
  let u : (Euc ν) := ‖v‖⁻¹ • v
  have hu : ‖u‖ = 1 := by simp [u,norm_smul,norm_inv,hn]
  have hur : u ∈ LinearMap.range ((matrixOp ν) A⁺).toLinearMap := Submodule.smul_mem _ _ hv
  obtain ⟨i,hi⟩ := hf.support_nonempty hu
  have hip : 0 < f u i := by simpa [positiveSupport] using hi
  by_cases hiI : i ∈ I
  · exact hf.orthogonal w u hw hu (by simp [u,inner_smul_right,hwv]) i ⟨hwi i hiI,hip⟩
  · have hz := hf.signedExtension_range_labels hI hur hu hiI
    rw [hz] at hip
    exact (lt_irrefl 0) hip
end SpectralSupport
end
end

section
section
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
section RankOnePreimage
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι]
omit [Nonempty ν] in
lemma symmetric_inner_action {A : SqMat ν} (hA : IsSelfAdjoint A) (u v : (Euc ν)) :
    ⟪u,(matrixOp ν) A v⟫ = ⟪(matrixOp ν) A u,v⟫ := by
  rw [← ContinuousLinearMap.adjoint_inner_right,← ContinuousLinearMap.star_eq_adjoint,
    ← map_star,hA.star_eq]
omit [Nonempty ν] in
lemma symmetric_eq_rankOne_of_range {A : SqMat ν} (hA : IsSelfAdjoint A)
    {u : (Euc ν)} (hu : ‖u‖ = 1)
    (hR : LinearMap.range ((matrixOp ν) A).toLinearMap ≤ Submodule.span ℝ {u}) :
    A = ⟪u,(matrixOp ν) A u⟫ • rankOne u := by
  have he (v : (Euc ν)) : (matrixOp ν) A v = ⟪u,(matrixOp ν) A v⟫ • u := by
    obtain ⟨t,ht⟩ := Submodule.mem_span_singleton.mp (hR (LinearMap.mem_range_self _ v))
    change t • u = ((matrixOp ν) A) v at ht
    rw [← ht,inner_smul_right,real_inner_self_eq_norm_sq,hu,one_pow,mul_one]
  have hscalar (v : (Euc ν)) : ⟪u,(matrixOp ν) A v⟫ = ⟪u,(matrixOp ν) A u⟫ * ⟪u,v⟫ := by
    calc
      ⟪u,(matrixOp ν) A v⟫ = ⟪(matrixOp ν) A u,v⟫ := symmetric_inner_action hA u v
      _ = ⟪u,(matrixOp ν) A u⟫ * ⟪u,v⟫ := by
        conv_lhs => rw [he u]
        simp only [inner_smul_left,conj_trivial]
  apply (matrixOp ν).injective
  change (matrixOp ν) A = (matrixOp ν) (⟪u,(matrixOp ν) A u⟫ • rankOne u)
  rw [map_smul]
  apply ContinuousLinearMap.ext
  intro v
  rw [smul_apply,rankOne_action,smul_smul,← hscalar,← he]
lemma Admissible.signedExtension_positive_rankOne {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {A : SqMat ν} {I : Finset ι} {w : (Euc ν)} (hw : ‖w‖ = 1)
    (hwi : ∀ i ∈ I, 0 < f w i)
    (hI : ∀ i ∉ I, signedExtension f A i ≤ 0)
    (hpos : ∃ i, 0 < signedExtension f A i) :
    ∃ u : (Euc ν), ‖u‖ = 1 ∧ ∃ lam : ℝ, 0 < lam ∧ A⁺ = lam • rankOne u := by
  obtain ⟨i,hi⟩ := hpos
  obtain ⟨u,hur,hu,hui⟩ := (hf.signedExtension_positive_support A i).mp hi
  have hwu : ⟪w,u⟫ ≠ 0 := by
    intro he
    have hz := hf.positive_range_separated hw hwi hI hur he
    simp [hz] at hu
  have hr : LinearMap.range ((matrixOp ν) A⁺).toLinearMap = Submodule.span ℝ {u} :=
    subspace_eq_span_of_inner_separates _ w u hur hwu
      (fun v hv horth => hf.positive_range_separated hw hwi hI hv horth)
  have hP := symmetric_eq_rankOne_of_range (CFC.posPart_nonneg A).isSelfAdjoint hu hr.le
  let lam : ℝ := ⟪u,(matrixOp ν) A⁺ u⟫
  have hlam : 0 ≤ lam := by
    change 0 ≤ ⟪u,(matrixOp ν) A⁺ u⟫
    rw [← sqrt_action_norm_sq A⁺ (CFC.posPart_nonneg A) u]
    positivity
  have hlam0 : lam ≠ 0 := by
    intro hz
    have hp0 : A⁺ = 0 := by simpa only [lam,hz,zero_smul] using hP
    obtain ⟨v,hv⟩ := hur
    rw [hp0,map_zero] at hv
    have hu0 : u = 0 := by simpa using hv.symm
    simp [hu0] at hu
  exact ⟨u,hu,lam,lt_of_le_of_ne hlam (Ne.symm hlam0),hP⟩
lemma Admissible.signedExtension_splitting {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {A : SqMat ν} (hA : IsSelfAdjoint A) {u : (Euc ν)} (hu : ‖u‖ = 1)
    {lam : ℝ} (hlam : 0 < lam) (he : A⁺ = lam • rankOne u) :
    A = lam • rankOne u - A⁻ ∧
      positiveExtension f A⁺ = lam • f u ∧
      signedExtension f A = lam • f u - positiveExtension f A⁻ := by
  have hp : positiveExtension f A⁺ = lam • f u := by
    rw [he,positiveExtension_smul_nonneg f (rankOne_nonneg u) hlam.le,
      hf.positiveExtension_rankOne u hu]
  refine ⟨?_,hp,?_⟩
  · rw [← he]
    exact (CFC.posPart_sub_negPart A hA).symm
  · exact congrArg (fun v => v - positiveExtension f A⁻) hp
lemma Admissible.signedExtension_line_labels {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {A : SqMat ν} {u : (Euc ν)} (hu : ‖u‖ = 1)
    {lam : ℝ} (hlam : 0 < lam) (he : A⁺ = lam • rankOne u) (i : ι) :
    0 < signedExtension f A i ↔ 0 < f u i := by
  rw [hf.signedExtension_pos_iff,he,
    positiveExtension_smul_nonneg f (rankOne_nonneg u) hlam.le,
    hf.positiveExtension_rankOne u hu,Pi.smul_apply,smul_eq_mul]
  exact mul_pos_iff_of_pos_left hlam
end RankOnePreimage
end
end

section
section
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator Topology
section SpectralChart
variable {ν : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν]
noncomputable def positiveProjection (A : (SqMat ν)) : (SqMat ν) := Ring.inverse A * A⁺
omit [Nonempty ν] in
lemma positiveProjection_action {A : (SqMat ν)} (hA : IsSelfAdjoint A) (hU : IsUnit A)
    {v : (Euc ν)} (hv : v ∈ LinearMap.range ((matrixOp ν) A⁺).toLinearMap) :
    (matrixOp ν) (positiveProjection A) v = v := by
  obtain ⟨x,rfl⟩ := hv
  have hAP : A * A⁺ = A⁺ * A⁺ := by
    calc
      A * A⁺ = (A⁺ - A⁻) * A⁺ := by rw [CFC.posPart_sub_negPart A hA]
      _ = A⁺ * A⁺ := by rw [sub_mul,CFC.negPart_mul_posPart,sub_zero]
  have he : positiveProjection A * A⁺ = A⁺ := by
    dsimp [positiveProjection]
    rw [mul_assoc,← hAP,← mul_assoc,Ring.inverse_mul_cancel A hU,one_mul]
  have hh := congrArg (fun B : (SqMat ν) => (matrixOp ν) B x) he
  simpa only [map_mul,mul_apply_eq_comp,ContinuousLinearMap.coe_coe] using hh
omit [Nonempty ν] in
lemma positiveProjection_kills {A : (SqMat ν)} {u v : (Euc ν)} {lam : ℝ}
    (hP : A⁺ = lam • rankOne u) (hv : ⟪u,v⟫ = 0) :
    (matrixOp ν) (positiveProjection A) v = 0 := by
  simp only [positiveProjection,map_mul,mul_apply_eq_comp,hP,map_smul,
    smul_apply,rankOne_action,hv,zero_smul,map_zero,smul_zero]
omit [Nonempty ν] in
lemma positiveRange_separated_of_close {A B : (SqMat ν)} (hB : IsSelfAdjoint B)
    (hBU : IsUnit B) {u : (Euc ν)} {lam : ℝ} (hP : A⁺ = lam • rankOne u)
    (hclose : ‖(matrixOp ν) (positiveProjection B) - (matrixOp ν) (positiveProjection A)‖ < 1)
    {v : (Euc ν)} (hv : v ∈ LinearMap.range ((matrixOp ν) B⁺).toLinearMap) (horth : ⟪u,v⟫ = 0) : v = 0 := by
  have he : ((matrixOp ν) (positiveProjection B) - (matrixOp ν) (positiveProjection A)) v = v := by
    rw [sub_apply,positiveProjection_action hB hBU hv,
      positiveProjection_kills hP horth,sub_zero]
  have hn := ContinuousLinearMap.le_opNorm ((matrixOp ν) (positiveProjection B) - (matrixOp ν) (positiveProjection A)) v
  rw [he] at hn
  apply norm_eq_zero.mp
  have hp := norm_nonneg v
  nlinarith
omit [Nonempty ν] in
lemma positive_eq_rankOne_of_separated {A : (SqMat ν)} {w : (Euc ν)}
    (hAw : (matrixOp ν) A⁺ w ≠ 0)
    (hsep : ∀ v ∈ LinearMap.range ((matrixOp ν) A⁺).toLinearMap, ⟪w,v⟫ = 0 → v = 0) :
    ∃ u : (Euc ν), ‖u‖ = 1 ∧ ∃ lam : ℝ, 0 < lam ∧ A⁺ = lam • rankOne u := by
  let v : (Euc ν) := (matrixOp ν) A⁺ w
  let u : (Euc ν) := ‖v‖⁻¹ • v
  have hu : ‖u‖ = 1 := by simp [u,norm_smul,norm_inv,hAw,v]
  have hur : u ∈ LinearMap.range ((matrixOp ν) A⁺).toLinearMap :=
    Submodule.smul_mem _ _ (LinearMap.mem_range_self _ w)
  have hwu : ⟪w,u⟫ ≠ 0 := by
    intro hz
    have hu0 := hsep u hur hz
    simp [hu0] at hu
  have hr := subspace_eq_span_of_inner_separates
    (LinearMap.range ((matrixOp ν) A⁺).toLinearMap) w u hur hwu hsep
  have he := symmetric_eq_rankOne_of_range (CFC.posPart_nonneg A).isSelfAdjoint hu hr.le
  have hl : 0 ≤ ⟪u,(matrixOp ν) A⁺ u⟫ := by
    rw [← sqrt_action_norm_sq A⁺ (CFC.posPart_nonneg A) u]
    positivity
  have hl0 : ⟪u,(matrixOp ν) A⁺ u⟫ ≠ 0 := by
    intro hz
    have hP0 : A⁺ = 0 := by simpa only [hz,zero_smul] using he
    apply hAw
    simp [hP0]
  exact ⟨u,hu,_,lt_of_le_of_ne hl (Ne.symm hl0),he⟩
omit [Nonempty ν] in
lemma positiveProjection_continuousAt {X : Type*} [TopologicalSpace X]
    (A : X → (SqMat ν)) (hA : Continuous A) (hSA : ∀ x, IsSelfAdjoint (A x))
    {x : X} (hU : IsUnit (A x)) : ContinuousAt (positiveProjection ∘ A) x := by
  have hP : Continuous (fun x => (A x)⁺) :=
    (matrix_posPart_continuousOn.comp_continuous hA (fun y => hSA y))
  have hInv : ContinuousAt (fun y => Ring.inverse (A y)) x := by
    obtain ⟨a,ha⟩ := hU
    have hi := NormedRing.inverse_continuousAt a
    rw [ha] at hi
    exact hi.comp hA.continuousAt
  exact hInv.mul hP.continuousAt
omit [Nonempty ν] in
lemma positive_line_eventually {X : Type*} [TopologicalSpace X]
    (A : X → (SqMat ν)) (hA : Continuous A) (hSA : ∀ x, IsSelfAdjoint (A x))
    {x : X} (hU : IsUnit (A x)) {w : (Euc ν)} (hw : ‖w‖ = 1)
    {lam : ℝ} (hlam : 0 < lam) (hP : (A x)⁺ = lam • rankOne w) :
    ∀ᶠ y in 𝓝 x, IsUnit (A y) ∧ ∃ u : (Euc ν), ‖u‖ = 1 ∧
      ∃ t : ℝ, 0 < t ∧ (A y)⁺ = t • rankOne u := by
  have hop : Continuous (fun B : (SqMat ν) => (matrixOp ν) B) :=
    ((matrixOp ν)).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional
  have hQ := hop.continuousAt.comp (positiveProjection_continuousAt A hA hSA hU)
  have hclose : ∀ᶠ y in 𝓝 x, ‖(matrixOp ν) (positiveProjection (A y)) - (matrixOp ν) (positiveProjection (A x))‖ < 1 := by
    have ht := (hQ.sub (continuousAt_const (y := (matrixOp ν) (positiveProjection (A x))))).norm
    exact ht.eventually_lt continuousAt_const (by simp)
  have hPcont : Continuous (fun y => (A y)⁺) :=
    matrix_posPart_continuousOn.comp_continuous hA (fun y => hSA y)
  have hvcont : Continuous (fun y => (matrixOp ν) (A y)⁺ w) := (hop.comp hPcont).clm_apply continuous_const
  have hw0 : (matrixOp ν) (A x)⁺ w ≠ 0 := by
    rw [hP,map_smul,smul_apply,rankOne_action,real_inner_self_eq_norm_sq,hw]
    have hwne : w ≠ 0 := by intro he; simp only [he,norm_zero] at hw; norm_num at hw
    simpa only [one_pow,one_smul] using smul_ne_zero (ne_of_gt hlam) hwne
  have hv : ∀ᶠ y in 𝓝 x, (matrixOp ν) (A y)⁺ w ≠ 0 := hvcont.continuousAt.eventually_ne hw0
  have hunit : ∀ᶠ y in 𝓝 x, IsUnit (A y) :=
    hA.continuousAt.preimage_mem_nhds (Units.isOpen.mem_nhds hU)
  filter_upwards [hclose,hv,hunit] with y hy hyv hyU
  refine ⟨hyU,positive_eq_rankOne_of_separated hyv ?_⟩
  exact fun v hv he => positiveRange_separated_of_close (hSA y) hyU hP hy hv he
end SpectralChart
end
end

section
section
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator Topology
section LineRepresentative
variable {ν : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν]
omit [Fintype ν] [DecidableEq ν] [Nonempty ν] in
lemma rankOne_smul (t : ℝ) (u : (Euc ν)) : rankOne (t • u) = t^2 • rankOne u := by
  ext i j
  simp only [rankOne,PiLp.smul_apply,Matrix.smul_apply,smul_eq_mul]
  ring
omit [DecidableEq ν] [Nonempty ν] in
lemma rankOne_unit_span {u v : (Euc ν)} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hsp : v ∈ Submodule.span ℝ {u}) : rankOne v = rankOne u := by
  obtain ⟨t,ht⟩ := Submodule.mem_span_singleton.mp hsp
  change t • u = v at ht
  have hn : |t| = 1 := by simpa only [← ht,norm_smul,Real.norm_eq_abs,hu,mul_one] using hv
  have hs : t^2 = 1 := by nlinarith [sq_abs t]
  rw [← ht,rankOne_smul,hs,one_smul]
noncomputable def lineRepresentative (w : (Euc ν)) (A : (SqMat ν)) : (Euc ν) :=
  ‖(matrixOp ν) A⁺ w‖⁻¹ • (matrixOp ν) A⁺ w
def HasPositiveLine (A : (SqMat ν)) : Prop :=
  ∃ u : (Euc ν), ‖u‖ = 1 ∧ ∃ lam : ℝ, 0 < lam ∧ A⁺ = lam • rankOne u
omit [Nonempty ν] in
lemma lineRepresentative_norm {w : (Euc ν)} {A : (SqMat ν)} (hAw : (matrixOp ν) A⁺ w ≠ 0) :
    ‖lineRepresentative w A‖ = 1 := by
  simp [lineRepresentative,norm_smul,norm_inv,hAw]
omit [Nonempty ν] in
lemma hasPositiveLine_trace_pos {A : (SqMat ν)} (hA : HasPositiveLine A) :
    0 < Matrix.trace A⁺ := by
  obtain ⟨u,hu,lam,hl,he⟩ := hA
  rwa [he,Matrix.trace_smul,rankOne_trace,hu,one_pow,smul_eq_mul,mul_one]
omit [Nonempty ν] in
lemma positive_line_representative {w : (Euc ν)} {A : (SqMat ν)} (hA : HasPositiveLine A)
    (hAw : (matrixOp ν) A⁺ w ≠ 0) : A⁺ = Matrix.trace A⁺ • rankOne (lineRepresentative w A) := by
  obtain ⟨u,hu,lam,hl,he⟩ := hA
  have hsp : lineRepresentative w A ∈ Submodule.span ℝ {u} := by
    rw [lineRepresentative,he,map_smul,smul_apply,rankOne_action]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _
      (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton u))))
  have hp := rankOne_unit_span hu (lineRepresentative_norm hAw) hsp
  rw [hp,he,Matrix.trace_smul,rankOne_trace,hu,one_pow,smul_eq_mul,mul_one]
omit [Nonempty ν] in
lemma lineRepresentative_inner_pos {w : (Euc ν)} {A : (SqMat ν)} (hA : HasPositiveLine A)
    (hAw : (matrixOp ν) A⁺ w ≠ 0) : 0 < ⟪w,lineRepresentative w A⟫ := by
  obtain ⟨u,hu,lam,hl,he⟩ := hA
  have hi : ⟪u,w⟫ ≠ 0 := by
    intro hz
    apply hAw
    rw [he,map_smul,smul_apply,rankOne_action,hz,zero_smul,smul_zero]
  have hp : 0 < ⟪w,(matrixOp ν) A⁺ w⟫ := by
    rw [he,map_smul,smul_apply,rankOne_action,inner_smul_right,
      inner_smul_right,real_inner_comm w u]
    exact mul_pos hl (mul_self_pos.mpr (by simpa only [real_inner_comm] using hi))
  rw [lineRepresentative,inner_smul_right]
  exact mul_pos (inv_pos.mpr (norm_pos_iff.mpr hAw)) hp
omit [Nonempty ν] in
lemma lineRepresentative_continuousOn {X : Type*} [TopologicalSpace X]
    (A : X → (SqMat ν)) (hA : Continuous A) (hSA : ∀ x, IsSelfAdjoint (A x)) (w : (Euc ν)) :
    ContinuousOn (fun x => lineRepresentative w (A x)) {x | (matrixOp ν) (A x)⁺ w ≠ 0} := by
  have hop : Continuous (fun B : (SqMat ν) => (matrixOp ν) B) :=
    ((matrixOp ν)).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional
  have hP : Continuous (fun x => (A x)⁺) :=
    matrix_posPart_continuousOn.comp_continuous hA hSA
  have hv : Continuous (fun x => (matrixOp ν) (A x)⁺ w) := (hop.comp hP).clm_apply continuous_const
  exact (hv.norm.continuousOn.inv₀ (fun _ hx => norm_ne_zero_iff.mpr hx)).smul hv.continuousOn
omit [Nonempty ν] in
lemma positive_line_isOpen {X : Type*} [TopologicalSpace X]
    (A : X → (SqMat ν)) (hA : Continuous A) (hSA : ∀ x, IsSelfAdjoint (A x)) :
    IsOpen {x | IsUnit (A x) ∧ HasPositiveLine (A x)} := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨u,hu,lam,hl,he⟩ := hx.2
  exact positive_line_eventually A hA hSA hx.1 hu hl he
lemma unit_rankOne_inner_nonzero {A : (SqMat ν)} (_hA : HasPositiveLine A) {w u : (Euc ν)}
    (hu : ‖u‖ = 1) {lam : ℝ} (hl : 0 < lam) (he : A⁺ = lam • rankOne u)
    (hwu : ⟪w,u⟫ ≠ 0) : (matrixOp ν) A⁺ w ≠ 0 := by
  rw [he,map_smul,smul_apply,rankOne_action]
  apply smul_ne_zero (ne_of_gt hl)
  apply smul_ne_zero (by simpa only [real_inner_comm] using hwu)
  intro hz
  simp [hz] at hu
end LineRepresentative
end
end

section
section
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator
section PositiveSlice
variable {ν : Type*} [Fintype ν] [DecidableEq ν]
noncomputable def unflattenMatrix : Euc (ν × ν) →ₗ[ℝ] (SqMat ν) where
  toFun x i j := x (i,j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
noncomputable def flatGram (x : Euc (ν × ν)) : (SqMat ν) :=
  unflattenMatrix x * (unflattenMatrix x)ᴴ
omit [DecidableEq ν] in
lemma flatGram_nonneg (x : Euc (ν × ν)) : 0 ≤ flatGram x :=
  (Matrix.posSemidef_self_mul_conjTranspose _).nonneg
omit [DecidableEq ν] in
lemma flatGram_trace (x : Euc (ν × ν)) : Matrix.trace (flatGram x) = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [flatGram,Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.conjTranspose_apply,
    star_trivial,Fintype.sum_prod_type]
  simp only [pow_two]
  rfl
omit [DecidableEq ν] in
lemma flatGram_continuous : Continuous (flatGram (ν := ν)) := by
  have h := (unflattenMatrix (ν := ν)).continuous_of_finiteDimensional
  exact h.mul h.star
lemma positive_slice_image : {Q : (SqMat ν) | 0 ≤ Q ∧ Matrix.trace Q = 1} =
    flatGram '' Metric.sphere (0 : Euc (ν × ν)) 1 := by
  ext Q
  constructor
  · rintro ⟨hQ,htr⟩
    let x : Euc (ν × ν) := WithLp.toLp 2 (fun p => CFC.sqrt Q p.1 p.2)
    have hxQ : flatGram x = Q := by
      change CFC.sqrt Q * star (CFC.sqrt Q) = Q
      rw [(CFC.sqrt_nonneg Q).isSelfAdjoint.star_eq]
      exact CFC.sqrt_mul_sqrt_self Q
    have hn : ‖x‖ ^ 2 = 1 := by rw [← flatGram_trace,hxQ,htr]
    have hnorm : ‖x‖ = 1 := by nlinarith [norm_nonneg x]
    exact ⟨x,by simpa [dist_zero_right] using hnorm,hxQ⟩
  · rintro ⟨x,hx,rfl⟩
    refine ⟨flatGram_nonneg x,?_⟩
    have hnorm : ‖x‖ = 1 := by simpa [dist_zero_right] using hx
    rw [flatGram_trace,hnorm,one_pow]
lemma positive_slice_compact : IsCompact {Q : (SqMat ν) | 0 ≤ Q ∧ Matrix.trace Q = 1} := by
  rw [positive_slice_image]
  exact (isCompact_sphere (0 : Euc (ν × ν)) 1).image flatGram_continuous
end PositiveSlice
end
end

section
section
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator
section TraceSphere
variable {ν : Type*} [Fintype ν] [DecidableEq ν]
omit [DecidableEq ν] in
lemma matrix_trace_continuous : Continuous (Matrix.trace : (SqMat ν) → ℝ) :=
  (Matrix.traceLinearMap ν ℝ ℝ).continuous_of_finiteDimensional
omit [DecidableEq ν] in
lemma matrix_trace_nonneg {A : (SqMat ν)} (hA : 0 ≤ A) : 0 ≤ Matrix.trace A :=
  (Matrix.nonneg_iff_posSemidef.mp hA).trace_nonneg
lemma positive_ball_image : {Q : (SqMat ν) | 0 ≤ Q ∧ Matrix.trace Q ≤ 1} =
    flatGram '' Metric.closedBall (0 : Euc (ν × ν)) 1 := by
  ext Q
  constructor
  · rintro ⟨hQ,htr⟩
    let x : Euc (ν × ν) := WithLp.toLp 2 (fun p => CFC.sqrt Q p.1 p.2)
    have hxQ : flatGram x = Q := by
      change CFC.sqrt Q * star (CFC.sqrt Q) = Q
      rw [(CFC.sqrt_nonneg Q).isSelfAdjoint.star_eq]
      exact CFC.sqrt_mul_sqrt_self Q
    have hn : ‖x‖ ^ 2 ≤ 1 := by rw [← flatGram_trace,hxQ]; exact htr
    have hn' : ‖x‖ ≤ 1 := by nlinarith [norm_nonneg x]
    exact ⟨x,by simpa [dist_zero_right] using hn',hxQ⟩
  · rintro ⟨x,hx,rfl⟩
    refine ⟨flatGram_nonneg x,?_⟩
    have hn : ‖x‖ ≤ 1 := by simpa [dist_zero_right] using hx
    rw [flatGram_trace]
    nlinarith [norm_nonneg x]
lemma positive_ball_compact : IsCompact {Q : (SqMat ν) | 0 ≤ Q ∧ Matrix.trace Q ≤ 1} := by
  rw [positive_ball_image]
  exact (isCompact_closedBall (0 : Euc (ν × ν)) 1).image flatGram_continuous
noncomputable def traceSphere (ν : Type*) [Fintype ν] [DecidableEq ν] : Set (SqMat ν) :=
  {A | IsSelfAdjoint A ∧ Matrix.trace (CFC.abs A) = 1}
lemma traceSphere_closed : IsClosed (traceSphere ν) :=
  (isClosed_eq continuous_star continuous_id).inter
    (isClosed_eq (matrix_trace_continuous.comp CFC.continuous_abs) continuous_const)
lemma traceSphere_compact : IsCompact (traceSphere ν) := by
  have hK : IsCompact ((fun p : (SqMat ν) × (SqMat ν) => p.1 - p.2) ''
      ({Q : (SqMat ν) | 0 ≤ Q ∧ Matrix.trace Q ≤ 1} ×ˢ {Q : (SqMat ν) | 0 ≤ Q ∧ Matrix.trace Q ≤ 1})) :=
    (positive_ball_compact.prod positive_ball_compact).image (continuous_fst.sub continuous_snd)
  apply hK.of_isClosed_subset traceSphere_closed
  intro A hA
  have htr : Matrix.trace A⁺ + Matrix.trace A⁻ = 1 := by
    rw [← Matrix.trace_add,CFC.posPart_add_negPart A hA.1]
    exact hA.2
  refine ⟨(A⁺,A⁻),⟨⟨CFC.posPart_nonneg A,?_⟩,⟨CFC.negPart_nonneg A,?_⟩⟩,
    CFC.posPart_sub_negPart A hA.1⟩
  · linarith [matrix_trace_nonneg (CFC.negPart_nonneg A)]
  · linarith [matrix_trace_nonneg (CFC.posPart_nonneg A)]
lemma traceSphere_ne_zero {A : (SqMat ν)} (hA : A ∈ traceSphere ν) : A ≠ 0 := by
  intro h
  simpa [h] using hA.2
lemma traceAbs_pos {A : (SqMat ν)} (hA : A ≠ 0) : 0 < Matrix.trace (CFC.abs A) := by
  have hp := matrix_trace_nonneg (CFC.abs_nonneg A)
  apply lt_of_le_of_ne hp
  intro hz
  have habs := (Matrix.nonneg_iff_posSemidef.mp (CFC.abs_nonneg A)).trace_eq_zero_iff.mp hz.symm
  have he := CFC.abs_mul_abs A
  rw [habs,zero_mul] at he
  exact hA (Matrix.conjTranspose_mul_self_eq_zero.mp he.symm)
noncomputable def traceRadial (A : (SqMat ν)) : (SqMat ν) := (Matrix.trace (CFC.abs A))⁻¹ • A
lemma traceRadial_mem {A : (SqMat ν)} (hA : IsSelfAdjoint A) (hAz : A ≠ 0) :
    traceRadial A ∈ traceSphere ν := by
  have hp := traceAbs_pos hAz
  refine ⟨(IsSelfAdjoint.all (_ : ℝ)).smul hA,?_⟩
  change Matrix.trace (CFC.abs ((Matrix.trace (CFC.abs A))⁻¹ • A)) = 1
  rw [CFC.abs_smul,Matrix.trace_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hp)]
  exact inv_mul_cancel₀ (ne_of_gt hp)
lemma traceRadial_continuousOn : ContinuousOn (traceRadial (ν := ν)) {A | A ≠ 0} :=
  ((matrix_trace_continuous.comp CFC.continuous_abs).continuousOn.inv₀
    (fun _A hA => ne_of_gt (traceAbs_pos hA))).smul continuous_id.continuousOn
lemma traceRadial_neg (A : (SqMat ν)) : traceRadial (-A) = -traceRadial A := by
  simp only [traceRadial,CFC.abs_neg,smul_neg]
end TraceSphere
end
end

section
section
open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
section MatrixFibre
variable {ν : Type*} [Fintype ν] [DecidableEq ν]
lemma psd_inner_nonneg {Q : (SqMat ν)} (hQ : 0 ≤ Q) (v : (Euc ν)) : 0 ≤ ⟪v,(matrixOp ν) Q v⟫ := by
  have h := (Matrix.nonneg_iff_posSemidef.mp hQ).re_dotProduct_nonneg v.ofLp
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial]
  change 0 ≤ ∑ i, (Q *ᵥ v.ofLp) i * v i
  simpa only [RCLike.re_to_real,dotProduct,Pi.star_apply,star_trivial,mul_comm] using h
lemma rankOne_mul_of_kernel {Q : (SqMat ν)} (hQ : IsSelfAdjoint Q) {u : (Euc ν)}
    (hu : (matrixOp ν) Q u = 0) : rankOne u * Q = 0 := by
  apply (matrixOp ν).injective
  change (matrixOp ν) (rankOne u * Q) = (matrixOp ν) 0
  rw [map_mul,map_zero]
  apply ContinuousLinearMap.ext
  intro v
  change (matrixOp ν) (rankOne u) ((matrixOp ν) Q v) = 0
  rw [rankOne_action]
  have hi : ⟪u,(matrixOp ν) Q v⟫ = 0 := by
    rw [← ContinuousLinearMap.adjoint_inner_left,
      ← ContinuousLinearMap.star_eq_adjoint,← map_star,hQ.star_eq,hu,inner_zero_left]
  rw [hi,zero_smul]
lemma rankOne_split_parts {Q : (SqMat ν)} (hQ : 0 ≤ Q) {u : (Euc ν)} (hu : (matrixOp ν) Q u = 0)
    {lam mu : ℝ} (hl : 0 ≤ lam) (hm : 0 ≤ mu) :
    (lam • rankOne u - mu • Q)⁺ = lam • rankOne u ∧
    (lam • rankOne u - mu • Q)⁻ = mu • Q := by
  apply CFC.posPart_negPart_unique rfl _ (smul_nonneg hl (rankOne_nonneg u)) (smul_nonneg hm hQ)
  rw [Matrix.smul_mul,Matrix.mul_smul,rankOne_mul_of_kernel hQ.isSelfAdjoint hu,smul_zero,smul_zero]
lemma nonunit_has_kernel (A : (SqMat ν)) (hA : ¬ IsUnit A) :
    ∃ v : (Euc ν), v ≠ 0 ∧ (matrixOp ν) A v = 0 := by
  have hdet : A.det = 0 := by
    by_contra h
    exact hA ((Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr h))
  obtain ⟨v,hv,hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  refine ⟨WithLp.toLp 2 v,fun h => hv (WithLp.toLp_injective 2 h),?_⟩
  rw [Matrix.toEuclideanCLM_toLp,hAv,WithLp.toLp_zero]
lemma fibre_boundary_kernel {Q : (SqMat ν)} (hQ : 0 ≤ Q) (u : (Euc ν))
    (hnot : ¬ IsUnit (rankOne u + Q)) :
    ∃ v : (Euc ν), ‖v‖ = 1 ∧ ⟪u,v⟫ = 0 ∧ (matrixOp ν) Q v = 0 := by
  obtain ⟨v,hv,hAv⟩ := nonunit_has_kernel _ hnot
  have hsum : ⟪v,(matrixOp ν) (rankOne u + Q) v⟫ = 0 := by rw [hAv,inner_zero_right]
  rw [map_add,add_apply,inner_add_right,rankOne_action,
    inner_smul_right,real_inner_comm u v] at hsum
  have hi : ⟪u,v⟫ = 0 := by
    nlinarith [psd_inner_nonneg hQ v,sq_nonneg ⟪u,v⟫]
  have hQv : (matrixOp ν) Q v = 0 := by
    simpa only [map_add,add_apply,rankOne_action,hi,zero_smul,zero_add] using hAv
  refine ⟨‖v‖⁻¹ • v,by simp [norm_smul,norm_inv,hv],?_,?_⟩
  · simp only [inner_smul_right,hi,mul_zero]
  · rw [map_smul,hQv,smul_zero]
noncomputable def matrixFibre (u : (Euc ν)) : Set (SqMat ν) :=
  {Q | 0 ≤ Q ∧ Matrix.trace Q = 1 ∧ (matrixOp ν) Q u = 0}
end MatrixFibre
end
end

section
section
open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
section NegativeFibre
variable {ν : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν]
lemma negPart_kernel_of_positiveLine {A : (SqMat ν)} {u : (Euc ν)} (hu : ‖u‖ = 1)
    {lam : ℝ} (hl : 0 < lam) (he : A⁺ = lam • rankOne u) : (matrixOp ν) A⁻ u = 0 := by
  have hz : (matrixOp ν) A⁻ ((matrixOp ν) A⁺ u) = 0 := by
    have h := congrArg (fun B : (SqMat ν) => (matrixOp ν) B u) (CFC.negPart_mul_posPart A)
    simpa only [map_mul,map_zero,mul_apply_eq_comp,zero_apply] using h
  rw [he,map_smul,smul_apply,rankOne_action,real_inner_self_eq_norm_sq,
    hu,one_pow,one_smul,map_smul] at hz
  exact (smul_eq_zero.mp hz).resolve_left (ne_of_gt hl)
noncomputable def negativeFibre (A : (SqMat ν)) : (SqMat ν) := (Matrix.trace A⁻)⁻¹ • A⁻
lemma negativeFibre_mem {A : (SqMat ν)} (hA : HasPositiveLine A) {w : (Euc ν)}
    (hAw : (matrixOp ν) A⁺ w ≠ 0) (hm : 0 < Matrix.trace A⁻) :
    negativeFibre A ∈ matrixFibre (lineRepresentative w A) := by
  have hu := lineRepresentative_norm hAw
  have hl := hasPositiveLine_trace_pos hA
  have he := positive_line_representative hA hAw
  refine ⟨smul_nonneg (inv_nonneg.mpr hm.le) (CFC.negPart_nonneg A),?_,?_⟩
  · rw [negativeFibre,Matrix.trace_smul,smul_eq_mul,inv_mul_cancel₀ (ne_of_gt hm)]
  · rw [negativeFibre,map_smul,smul_apply,
      negPart_kernel_of_positiveLine hu hl he,smul_zero]
omit [Nonempty ν] in
lemma negativeFibre_smul {A : (SqMat ν)} (hm : Matrix.trace A⁻ ≠ 0) :
    Matrix.trace A⁻ • negativeFibre A = A⁻ := by
  rw [negativeFibre,smul_smul,mul_inv_cancel₀ hm,one_smul]
omit [Nonempty ν] in
lemma negativeFibre_splitting {A : (SqMat ν)} (hSA : IsSelfAdjoint A) (hA : HasPositiveLine A)
    {w : (Euc ν)} (hAw : (matrixOp ν) A⁺ w ≠ 0) (hm : 0 < Matrix.trace A⁻) :
    A = Matrix.trace A⁺ • rankOne (lineRepresentative w A) - Matrix.trace A⁻ • negativeFibre A := by
  rw [negativeFibre_smul (ne_of_gt hm),← positive_line_representative hA hAw,
    CFC.posPart_sub_negPart A hSA]
omit [Nonempty ν] in
lemma negativeFibre_continuousOn {X : Type*} [TopologicalSpace X]
    (A : X → (SqMat ν)) (hA : Continuous A) (hSA : ∀ x, IsSelfAdjoint (A x)) :
    ContinuousOn (fun x => negativeFibre (A x)) {x | Matrix.trace (A x)⁻ ≠ 0} := by
  have hP : Continuous (fun x => (A x)⁻) :=
    matrix_negPart_continuousOn.comp_continuous hA hSA
  exact ((matrix_trace_continuous.comp hP).continuousOn.inv₀ (fun _ hx => hx)).smul hP.continuousOn
end NegativeFibre
end
end

section
section
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator Topology
open Set
section PurityChart
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι]
noncomputable def purityChart (f : (Euc ν) → ι → ℝ) (I : Finset ι) (w c : (Euc ν)) : Set (SqMat ν) :=
  {A | IsUnit A ∧ HasPositiveLine A ∧ (matrixOp ν) A⁺ w ≠ 0 ∧ 0 < Matrix.trace A⁻ ∧
    lineRepresentative w A ∈ commonPositiveCone f I ∧
    lineRepresentative w A ∈ interior (signChamber (activeVectors f I) c)}
omit [Nonempty ν] in
lemma Admissible.purityChart_isOpen {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    (I : Finset ι) (w c : (Euc ν)) {X : Type*} [TopologicalSpace X]
    (A : X → (SqMat ν)) (hA : Continuous A) (hSA : ∀ x, IsSelfAdjoint (A x)) :
    IsOpen (A ⁻¹' purityChart f I w c) := by
  have hop : Continuous (fun x => (matrixOp ν) (A x)⁺ w) :=
    ((((matrixOp ν)).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional).comp
      (matrix_posPart_continuousOn.comp_continuous hA hSA)).clm_apply continuous_const
  have hopen : IsOpen {x | (matrixOp ν) (A x)⁺ w ≠ 0} := (isClosed_eq hop continuous_const).isOpen_compl
  have hrep := lineRepresentative_continuousOn A hA hSA w
  have hpre : IsOpen ({x | (matrixOp ν) (A x)⁺ w ≠ 0} ∩
      (fun x => lineRepresentative w (A x)) ⁻¹'
      (commonPositiveCone f I ∩ interior (signChamber (activeVectors f I) c))) :=
    hrep.isOpen_inter_preimage hopen ((hf.commonPositiveCone_isOpen I).inter isOpen_interior)
  have hn : IsOpen {x | 0 < Matrix.trace (A x)⁻} := isOpen_lt continuous_const
    (matrix_trace_continuous.comp (matrix_negPart_continuousOn.comp_continuous hA hSA))
  have he : A ⁻¹' purityChart f I w c =
      ({x | IsUnit (A x) ∧ HasPositiveLine (A x)} ∩ {x | 0 < Matrix.trace (A x)⁻}) ∩
        ({x | (matrixOp ν) (A x)⁺ w ≠ 0} ∩ (fun x => lineRepresentative w (A x)) ⁻¹'
          (commonPositiveCone f I ∩ interior (signChamber (activeVectors f I) c))) := by
    ext x
    simp only [purityChart,mem_preimage,mem_ofPred_eq,mem_inter_iff]
    tauto
  rw [he]
  exact ((positive_line_isOpen A hA hSA).inter hn).inter hpre
omit [Fintype ι] in
omit [Nonempty ν] in
lemma purityChart_unit {f : (Euc ν) → ι → ℝ} {I : Finset ι} {w c : (Euc ν)} {A : (SqMat ν)}
    (hA : A ∈ purityChart f I w c) : ‖lineRepresentative w A‖ = 1 :=
  lineRepresentative_norm hA.2.2.1
omit [Fintype ι] in
lemma purityChart_fibre {f : (Euc ν) → ι → ℝ} {I : Finset ι} {w c : (Euc ν)} {A : (SqMat ν)}
    (hA : A ∈ purityChart f I w c) : negativeFibre A ∈ matrixFibre (lineRepresentative w A) :=
  negativeFibre_mem hA.2.1 hA.2.2.1 hA.2.2.2.1
end PurityChart
end
end

section
section
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
section BalancedChart
variable {ν : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν]
lemma split_unit_of_fibre_unit {u : (Euc ν)} (hu : ‖u‖ = 1) {Q : (SqMat ν)} (hQ : 0 ≤ Q)
    (hQu : (matrixOp ν) Q u = 0) {lam mu : ℝ} (hl : 0 < lam) (hm : 0 < mu)
    (hunit : IsUnit (rankOne u + Q)) : IsUnit (lam • rankOne u - mu • Q) := by
  apply (isUnit_map_iff ((matrixOp ν)) _).mp
  apply ContinuousLinearMap.isUnit_iff_bijective.mpr
  have hi : Function.Injective ((matrixOp ν) (lam • rankOne u - mu • Q)) := by
    apply (LinearMap.ker_eq_bot).mp
    rw [Submodule.eq_bot_iff]
    intro v hv
    have hv0 : (matrixOp ν) (lam • rankOne u - mu • Q) v = 0 := hv
    have hi := congrArg (fun b : (Euc ν) => ⟪u,b⟫) hv0
    have hQv : ⟪u,(matrixOp ν) Q v⟫ = 0 := matrix_image_orthogonal_kernel hQ.isSelfAdjoint hQu v
    simp only [map_sub,map_smul,sub_apply,smul_apply,
      rankOne_action,inner_sub_right,inner_smul_right,real_inner_self_eq_norm_sq,hu,one_pow,
      mul_one,hQv,mul_zero,sub_zero,inner_zero_right] at hi
    have huv : ⟪u,v⟫ = 0 := (mul_eq_zero.mp hi).resolve_left (ne_of_gt hl)
    have hzero : (matrixOp ν) Q v = 0 := by
      simp only [map_sub,map_smul,sub_apply,smul_apply,
        rankOne_action,huv,zero_smul,smul_zero,zero_sub,neg_eq_zero] at hv0
      exact (smul_eq_zero.mp hv0).resolve_left (ne_of_gt hm)
    have huop := ContinuousLinearMap.isUnit_iff_bijective.mp (hunit.map ((matrixOp ν)).toMonoidHom)
    apply huop.1
    change (matrixOp ν) (rankOne u + Q) v = (matrixOp ν) (rankOne u + Q) 0
    simp only [map_add,add_apply,rankOne_action,huv,zero_smul,hzero,add_zero,map_zero]
  exact ⟨hi,(LinearMap.injective_iff_surjective).mp hi⟩
omit [Nonempty ν] in
lemma lineRepresentative_split {u w : (Euc ν)} (hu : ‖u‖ = 1) {A : (SqMat ν)} {lam : ℝ}
    (hl : 0 < lam) (he : A⁺ = lam • rankOne u) (hwu : 0 < ⟪w,u⟫) :
    lineRepresentative w A = u := by
  have hp : 0 < lam * ⟪u,w⟫ := mul_pos hl (by simpa only [real_inner_comm] using hwu)
  have hop : (matrixOp ν) A⁺ w = (lam * ⟪u,w⟫) • u := by
    rw [he,map_smul,smul_apply,rankOne_action,smul_smul]
  rw [lineRepresentative,hop,norm_smul,Real.norm_eq_abs,abs_of_pos hp,hu,mul_one,smul_smul,inv_mul_cancel₀ (ne_of_gt hp),one_smul]
lemma balancedFibre_chart {ι : Type*} [Fintype ι] {f : (Euc ν) → ι → ℝ} {I : Finset ι}
    {w c u : (Euc ν)} (hu : ‖u‖ = 1) (hwu : 0 < ⟪w,u⟫)
    (huc : u ∈ commonPositiveCone f I)
    (hch : u ∈ interior (signChamber (activeVectors f I) c)) {Q : (SqMat ν)}
    (hQ : Q ∈ matrixFibre u) (hunit : IsUnit (rankOne u + Q)) :
    ((1/2:ℝ) • rankOne u - (1/2:ℝ) • Q) ∈ purityChart f I w c := by
  have hp : (0:ℝ) < 1/2 := by norm_num
  obtain ⟨he,hn⟩ := rankOne_split_parts hQ.1 hQ.2.2 hp.le hp.le
  have hline : HasPositiveLine ((1/2:ℝ) • rankOne u - (1/2:ℝ) • Q) := ⟨u,hu,1/2,hp,he⟩
  have hrep := lineRepresentative_split hu hp he hwu
  refine ⟨split_unit_of_fibre_unit hu hQ.1 hQ.2.2 hp hp hunit,hline,
    unit_rankOne_inner_nonzero hline hu hp he (ne_of_gt hwu),?_,?_,?_⟩
  · rw [hn,Matrix.trace_smul,hQ.2.1,smul_eq_mul,mul_one]; exact hp
  · rwa [hrep]
  · rwa [hrep]
end BalancedChart
end
end

section
section
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
section MatrixTransport
variable {ν : Type*} [Fintype ν] [DecidableEq ν]
noncomputable def matrixConjugate (e : (Euc ν) ≃ₗᵢ[ℝ] (Euc ν)) : (SqMat ν) ≃⋆ₐ[ℝ] (SqMat ν) :=
  ((matrixOp ν)).trans (e.conjStarAlgEquiv.trans ((matrixOp ν)).symm)
lemma matrixConjugate_action (e : (Euc ν) ≃ₗᵢ[ℝ] (Euc ν)) (A : (SqMat ν)) (v : (Euc ν)) :
    (matrixOp ν) (matrixConjugate e A) v = e ((matrixOp ν) A (e.symm v)) := by
  simp only [matrixConjugate,StarAlgEquiv.trans_apply,StarAlgEquiv.apply_symm_apply,
    LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
lemma matrixConjugate_nonneg (e : (Euc ν) ≃ₗᵢ[ℝ] (Euc ν)) {A : (SqMat ν)} (hA : 0 ≤ A) :
    0 ≤ matrixConjugate e A := map_nonneg _ hA
lemma matrixConjugate_rankOne (e : (Euc ν) ≃ₗᵢ[ℝ] (Euc ν)) (u : (Euc ν)) :
    matrixConjugate e (rankOne u) = rankOne (e u) := by
  apply (matrixOp ν).injective
  change (matrixOp ν) (matrixConjugate e (rankOne u)) = (matrixOp ν) (rankOne (e u))
  apply ContinuousLinearMap.ext
  intro v
  rw [matrixConjugate_action,rankOne_action,rankOne_action,map_smul]
  congr 1
  simpa using (e.inner_map_map u (e.symm v)).symm
lemma matrix_operator_trace (A : (SqMat ν)) : LinearMap.trace ℝ (Euc ν) ((matrixOp ν) A).toLinearMap = Matrix.trace A := by
  rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin,Matrix.toEuclideanLin_eq_toLin_orthonormal]
  exact Matrix.trace_toLin_eq A _
lemma matrixConjugate_trace (e : (Euc ν) ≃ₗᵢ[ℝ] (Euc ν)) (A : (SqMat ν)) :
    Matrix.trace (matrixConjugate e A) = Matrix.trace A := by
  rw [← matrix_operator_trace,← matrix_operator_trace]
  have he : ((matrixOp ν) (matrixConjugate e A)).toLinearMap = e.toLinearEquiv.conj ((matrixOp ν) A).toLinearMap := by
    apply LinearMap.ext
    intro v
    exact matrixConjugate_action e A v
  rw [he,LinearMap.trace_conj']
lemma matrixConjugate_kernel (e : (Euc ν) ≃ₗᵢ[ℝ] (Euc ν)) {A : (SqMat ν)} {v : (Euc ν)} (hv : (matrixOp ν) A v = 0) :
    (matrixOp ν) (matrixConjugate e A) (e v) = 0 := by
  rw [matrixConjugate_action,e.symm_apply_apply,hv,map_zero]
lemma matrixConjugate_selfAdjoint (e : (Euc ν) ≃ₗᵢ[ℝ] (Euc ν)) {A : (SqMat ν)} (hA : IsSelfAdjoint A) :
    IsSelfAdjoint (matrixConjugate e A) := by
  rw [IsSelfAdjoint,← map_star,hA.star_eq]
lemma matrixConjugate_involutive {e : (Euc ν) ≃ₗᵢ[ℝ] (Euc ν)}
    (he : ∀ v, e (e v) = v) (A : (SqMat ν)) : matrixConjugate e (matrixConjugate e A) = A := by
  have hes : ∀ v, e.symm v = e v := by intro v; apply e.injective; simp [he]
  apply (matrixOp ν).injective
  change (matrixOp ν) (matrixConjugate e (matrixConjugate e A)) = (matrixOp ν) A
  apply ContinuousLinearMap.ext
  intro v
  simp only [matrixConjugate_action,hes,he]
end MatrixTransport
end
end

section
section
open scoped RealInnerProductSpace
section ReflectionTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
noncomputable def householder (c x : E) : E ≃ₗᵢ[ℝ] E :=
  (Submodule.span ℝ {c+x}).reflection
lemma householder_apply (c x v : E) :
    householder c x v = (2 * (⟪c+x,v⟫ / ‖c+x‖ ^ 2)) • (c+x) - v := by
  rw [householder,Submodule.reflection_singleton_apply]
  simp only [RCLike.ofReal_real_eq_id, id_eq, two_smul, two_mul, add_smul]
lemma householder_send {c x : E} (h : ‖c‖ = ‖x‖) : householder c x c = x := by
  have hh := Submodule.reflection_sub (v := c) (w := -x) (by simpa using h)
  rw [sub_neg_eq_add,Submodule.reflection_orthogonal_apply] at hh
  exact neg_injective hh
lemma householder_at_self {c v : E} (hv : ⟪c,v⟫ = 0) :
    householder c c v = -v := by
  rw [householder_apply]
  simp [inner_add_left,hv]
end ReflectionTransport
end
end

section
section
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
section MatrixReflection
variable {ν : Type*} [Fintype ν] [DecidableEq ν]
omit [Fintype ν] [DecidableEq ν] in
lemma rankOne_continuous : Continuous (rankOne (ν := ν)) := by
  apply continuous_matrix
  intro i j
  exact (PiLp.continuous_apply 2 (fun _ : ν => ℝ) i).mul
    (PiLp.continuous_apply 2 (fun _ : ν => ℝ) j)
noncomputable def reflectionMatrix (c u : (Euc ν)) : (SqMat ν) :=
  (2 / ‖c+u‖^2) • rankOne (c+u) - 1
lemma reflectionMatrix_action (c u v : (Euc ν)) :
    (matrixOp ν) (reflectionMatrix c u) v = householder c u v := by
  rw [reflectionMatrix,map_sub,map_smul,map_one,sub_apply,
    smul_apply,one_apply_eq_self,rankOne_action,householder_apply,
    smul_smul]
  congr 2
  ring
omit [DecidableEq ν] in
lemma householder_involutive (c u : (Euc ν)) : Function.Involutive (householder c u) :=
  (Submodule.span ℝ {c+u}).reflection_involutive
lemma reflectionMatrix_conjugate (c u : (Euc ν)) (B : (SqMat ν)) :
    matrixConjugate (householder c u) B = reflectionMatrix c u * B * reflectionMatrix c u := by
  apply (matrixOp ν).injective
  change (matrixOp ν) (matrixConjugate (householder c u) B) = (matrixOp ν) (reflectionMatrix c u * B * reflectionMatrix c u)
  rw [map_mul,map_mul]
  apply ContinuousLinearMap.ext
  intro v
  rw [matrixConjugate_action]
  change _ = (matrixOp ν) (reflectionMatrix c u) ((matrixOp ν) B ((matrixOp ν) (reflectionMatrix c u) v))
  rw [reflectionMatrix_action,reflectionMatrix_action]
  congr 2
lemma reflectionMatrix_continuousOn (c : (Euc ν)) :
    ContinuousOn (reflectionMatrix c) {u | c+u ≠ 0} := by
  have hn : Continuous (fun u : (Euc ν) => ‖c+u‖^2) := (continuous_const.add continuous_id).norm.pow 2
  have hd : ContinuousOn (fun u : (Euc ν) => 2 / ‖c+u‖^2) {u | c+u ≠ 0} :=
    continuous_const.continuousOn.div hn.continuousOn
      (fun u hu => pow_ne_zero 2 (norm_ne_zero_iff.mpr hu))
  exact (hd.smul (rankOne_continuous.comp (continuous_const.add continuous_id)).continuousOn).sub
    continuous_const.continuousOn
lemma householder_matrix_joint_continuousOn (c : (Euc ν)) :
    ContinuousOn (fun p : (Euc ν) × (SqMat ν) => matrixConjugate (householder c p.1) p.2)
      {p | c+p.1 ≠ 0} := by
  simp_rw [reflectionMatrix_conjugate]
  have hR : ContinuousOn (fun p : (Euc ν) × (SqMat ν) => reflectionMatrix c p.1) {p | c+p.1 ≠ 0} :=
    (reflectionMatrix_continuousOn c).comp continuous_fst.continuousOn (fun _ h => h)
  exact (hR.mul continuous_snd.continuousOn).mul hR
end MatrixReflection
end
end

section
section
open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
section FibreTransport
variable {ν : Type*} [Fintype ν] [DecidableEq ν]
omit [DecidableEq ν] in
lemma householder_swap {c u : (Euc ν)} (h : ‖c‖ = ‖u‖) : householder c u u = c := by
  calc
    householder c u u = householder c u (householder c u c) := congrArg (householder c u) (householder_send h).symm
    _ = c := householder_involutive c u c
lemma matrixConjugate_householder_self {c : (Euc ν)} {Q : (SqMat ν)} (hQ : IsSelfAdjoint Q)
    (hc : (matrixOp ν) Q c = 0) : matrixConjugate (householder c c) Q = Q := by
  apply (matrixOp ν).injective
  change (matrixOp ν) (matrixConjugate (householder c c) Q) = (matrixOp ν) Q
  apply ContinuousLinearMap.ext
  intro v
  rw [matrixConjugate_action]
  have hs : (householder c c).symm v = householder c c v := by
    apply (householder c c).injective
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact (householder_involutive c c v).symm
  have hcz : (matrixOp ν) Q (c+c) = 0 := by rw [map_add,hc,add_zero]
  have hact : (matrixOp ν) Q (householder c c v) = -((matrixOp ν) Q v) := by
    rw [householder_apply,map_sub,map_smul,hcz,smul_zero,zero_sub]
  rw [hs,hact,map_neg]
  have ho : ⟪c,(matrixOp ν) Q v⟫ = 0 := by
    rw [← ContinuousLinearMap.adjoint_inner_left,← ContinuousLinearMap.star_eq_adjoint,
      ← map_star,hQ.star_eq,hc,inner_zero_left]
  rw [householder_at_self ho,neg_neg]
noncomputable def fibreTransport (c u v : (Euc ν)) (Q : (SqMat ν)) : (SqMat ν) :=
  matrixConjugate (householder c v) (matrixConjugate (householder c u) Q)
lemma fibreTransport_nonneg (c u v : (Euc ν)) {Q : (SqMat ν)} (hQ : 0 ≤ Q) :
    0 ≤ fibreTransport c u v Q :=
  matrixConjugate_nonneg _ (matrixConjugate_nonneg _ hQ)
lemma fibreTransport_trace (c u v : (Euc ν)) (Q : (SqMat ν)) :
    Matrix.trace (fibreTransport c u v Q) = Matrix.trace Q := by
  simp only [fibreTransport,matrixConjugate_trace]
lemma fibreTransport_kernel {c u v : (Euc ν)} {Q : (SqMat ν)} (hu : ‖c‖ = ‖u‖) (hv : ‖c‖ = ‖v‖)
    (hQ : (matrixOp ν) Q u = 0) : (matrixOp ν) (fibreTransport c u v Q) v = 0 := by
  have hQc : (matrixOp ν) (matrixConjugate (householder c u) Q) c = 0 := by
    simpa only [householder_swap hu] using matrixConjugate_kernel (householder c u) hQ
  simpa only [fibreTransport,householder_send hv] using matrixConjugate_kernel (householder c v) hQc
lemma fibreTransport_self (c u : (Euc ν)) (Q : (SqMat ν)) : fibreTransport c u u Q = Q :=
  matrixConjugate_involutive (householder_involutive c u) Q
lemma fibreTransport_center {c u : (Euc ν)} {Q : (SqMat ν)} (hQ : IsSelfAdjoint Q) (hu : ‖c‖ = ‖u‖)
    (hz : (matrixOp ν) Q u = 0) : fibreTransport c u c Q = matrixConjugate (householder c u) Q := by
  apply matrixConjugate_householder_self (matrixConjugate_selfAdjoint _ hQ)
  simpa only [householder_swap hu] using matrixConjugate_kernel (householder c u) hz
lemma fibreTransport_unit_iff {c u v : (Euc ν)} {Q : (SqMat ν)} (hu : ‖c‖ = ‖u‖) (hv : ‖c‖ = ‖v‖) :
    IsUnit (rankOne v + fibreTransport c u v Q) ↔ IsUnit (rankOne u + Q) := by
  have he : rankOne v + fibreTransport c u v Q =
      matrixConjugate (householder c v) (matrixConjugate (householder c u) (rankOne u + Q)) := by
    rw [map_add,map_add,matrixConjugate_rankOne,householder_swap hu,
      matrixConjugate_rankOne,householder_send hv]; rfl
  rw [he]
  exact (isUnit_map_iff (matrixConjugate (householder c v)) _).trans
    (isUnit_map_iff (matrixConjugate (householder c u)) _)
lemma fibreTransport_continuousOn (c : (Euc ν)) :
    ContinuousOn (fun p : (Euc ν) × (Euc ν) × (SqMat ν) => fibreTransport c p.1 p.2.1 p.2.2)
      {p | c+p.1 ≠ 0 ∧ c+p.2.1 ≠ 0} := by
  have hR₁ : ContinuousOn (fun p : (Euc ν) × (Euc ν) × (SqMat ν) => reflectionMatrix c p.1)
      {p | c+p.1 ≠ 0 ∧ c+p.2.1 ≠ 0} :=
    (reflectionMatrix_continuousOn c).comp continuous_fst.continuousOn (fun _ h => h.1)
  have hR₂ : ContinuousOn (fun p : (Euc ν) × (Euc ν) × (SqMat ν) => reflectionMatrix c p.2.1)
      {p | c+p.1 ≠ 0 ∧ c+p.2.1 ≠ 0} :=
    (reflectionMatrix_continuousOn c).comp continuous_snd.fst.continuousOn (fun _ h => h.2)
  simp only [fibreTransport,reflectionMatrix_conjugate]
  exact (hR₂.mul ((hR₁.mul continuous_snd.snd.continuousOn).mul hR₁)).mul hR₂
end FibreTransport
end
end

section
section
open scoped RealInnerProductSpace
section ChamberPath
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
noncomputable def chamberPath (c u : E) (t : ℝ) : E :=
  ‖(1-t) • u + t • c‖⁻¹ • ((1-t) • u + t • c)
lemma signChamber_smul {Z : Set E} {c u : E} (hu : u ∈ signChamber Z c)
    {t : ℝ} (ht : 0 < t) : t • u ∈ signChamber Z c := by
  intro z hz
  rw [real_inner_smul_left,mul_left_comm]
  exact mul_pos ht (hu z hz)
lemma chamber_interpolation_mem {Z : Set E} {c u : E} (hc : c ∈ safeNormals Z)
    (hu : u ∈ signChamber Z c) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    (1-t) • u + t • c ∈ signChamber Z c :=
  signChamber_convex Z c hu (mem_signChamber_self hc) (sub_nonneg.mpr ht.2) ht.1 (by ring)
lemma chamber_interpolation_ne_zero {Z : Set E} {c u : E} (hcZ : c ∈ Z)
    (hc : c ∈ safeNormals Z) (hu : u ∈ signChamber Z c)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) : (1-t) • u + t • c ≠ 0 := by
  intro he
  have h := chamber_interpolation_mem hc hu ht c hcZ
  simp [he] at h
lemma chamberPath_norm {Z : Set E} {c u : E} (hcZ : c ∈ Z)
    (hc : c ∈ safeNormals Z) (hu : u ∈ signChamber Z c)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) : ‖chamberPath c u t‖ = 1 := by
  have hn := chamber_interpolation_ne_zero hcZ hc hu ht
  simp only [chamberPath,norm_smul,norm_inv,norm_norm,inv_mul_cancel₀ (norm_ne_zero_iff.mpr hn)]
lemma chamberPath_mem {Z : Set E} {c u : E} (hcZ : c ∈ Z)
    (hc : c ∈ safeNormals Z) (hu : u ∈ signChamber Z c)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) : chamberPath c u t ∈ signChamber Z c :=
  signChamber_smul (chamber_interpolation_mem hc hu ht)
    (inv_pos.mpr (norm_pos_iff.mpr (chamber_interpolation_ne_zero hcZ hc hu ht)))
lemma chamberPath_zero (c u : E) (hu : ‖u‖ = 1) : chamberPath c u 0 = u := by
  simp [chamberPath,hu]
lemma chamberPath_one (c u : E) (hc : ‖c‖ = 1) : chamberPath c u 1 = c := by
  simp [chamberPath,hc]
lemma chamber_add_ne_zero {Z : Set E} {c u : E} (hcZ : c ∈ Z)
    (hc : c ∈ safeNormals Z) (hu : u ∈ signChamber Z c) : c+u ≠ 0 := by
  intro he
  have h := hu c hcZ
  have hn := hc c hcZ
  have hei : ⟪c,c⟫ + ⟪u,c⟫ = 0 := by rw [← inner_add_left,he,inner_zero_left]
  have hei' : ⟪u,c⟫ = -⟪c,c⟫ := by linarith
  rw [hei'] at h
  nlinarith [sq_nonneg ⟪c,c⟫]
lemma chamberPath_continuousOn {Z : Set E} {c : E} (hcZ : c ∈ Z)
    (hc : c ∈ safeNormals Z) : ContinuousOn (fun p : ℝ × E => chamberPath c p.2 p.1)
      (Set.Icc (0:ℝ) 1 ×ˢ signChamber Z c) := by
  have hs : Continuous (fun p : ℝ × E => (1-p.1) • p.2 + p.1 • c) :=
    ((continuous_const.sub continuous_fst).smul continuous_snd).add
      (continuous_fst.smul continuous_const)
  exact (hs.norm.continuousOn.inv₀ (fun p hp => norm_ne_zero_iff.mpr
    (chamber_interpolation_ne_zero hcZ hc hp.2 hp.1))).smul hs.continuousOn
end ChamberPath
end
end

section
section
open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
section PurityGeometry
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι] [DecidableEq ι]
omit [DecidableEq ν] [Nonempty ν] [DecidableEq ι] in
lemma Admissible.safe_orthogonal_zero {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {I : Finset ι} {u v : (Euc ν)} (hu : u ∈ safeNormals (activeVectors f I))
    (hv : ‖v‖ = 1) (horth : ⟪u,v⟫ = 0) {i : ι} (hi : i ∈ I) : f v i = 0 := by
  apply le_antisymm _ (hf.nonneg v hv i)
  apply le_of_not_gt
  intro hp
  exact hu v ⟨i,hi,by rwa [homogeneousLift_unit f hv]⟩ horth
omit [DecidableEq ι] in
lemma Admissible.positiveExtension_safe_zero {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {I : Finset ι} {u : (Euc ν)} (hu : u ∈ safeNormals (activeVectors f I))
    {Q : (SqMat ν)} (hQ : 0 ≤ Q) (hQu : (matrixOp ν) Q u = 0) {i : ι} (hi : i ∈ I) :
    positiveExtension f Q i = 0 := by
  apply le_antisymm _ (hf.positiveExtension_nonneg Q i)
  apply le_of_not_gt
  intro hp
  obtain ⟨v,⟨x,hx⟩,hv,hvi⟩ := (hf.positiveExtension_support hQ i).mp hp
  have horth : ⟪u,v⟫ = 0 := by rw [← hx]; exact matrix_image_orthogonal_kernel hQ.isSelfAdjoint hQu x
  exact (ne_of_gt hvi) (hf.safe_orthogonal_zero hu hv horth hi)
lemma Admissible.fibre_boundary_missing {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {I : Finset ι} {u : (Euc ν)} (hu : u ∈ safeNormals (activeVectors f I))
    {Q : (SqMat ν)} (hQ : 0 ≤ Q) (hnot : ¬ IsUnit (rankOne u + Q)) :
    ∃ i ∈ Iᶜ, positiveExtension f Q i = 0 := by
  obtain ⟨v,hv,huv,hQv⟩ := fibre_boundary_kernel hQ u hnot
  obtain ⟨i,hi⟩ := hf.support_nonempty hv
  have hip := (mem_positiveSupport f v i).mp hi
  refine ⟨i,?_,hf.positiveExtension_kernel hQ hv hQv hip⟩
  exact Finset.mem_compl.mpr (fun h => (ne_of_gt hip) (hf.safe_orthogonal_zero hu hv huv h))
noncomputable def orientedLevel (f : (Euc ν) → ι → ℝ) (w : (Euc ν)) (r : ι → ℝ) : Set (Euc ν) :=
  {u | ‖u‖ = 1 ∧ f u = r ∧ 0 ≤ ⟪w,u⟫}
omit [DecidableEq ν] [Nonempty ν] [DecidableEq ι] in
lemma Admissible.orientedLevel_compact {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    (w : (Euc ν)) (r : ι → ℝ) : IsCompact (orientedLevel f w r) := by
  have hc : Continuous f := continuous_pi (fun i => (hf.smooth i).continuous)
  have he : orientedLevel f w r = Metric.sphere (0:(Euc ν)) 1 ∩
      {u | f u = r ∧ 0 ≤ ⟪w,u⟫} := by ext u; simp [orientedLevel]
  rw [he]
  exact (isCompact_sphere (0:(Euc ν)) 1).inter_right ((isClosed_eq hc continuous_const).inter
    (isClosed_le continuous_const (show Continuous (fun u : (Euc ν) => ⟪w,u⟫) from
      (continuous_const.inner continuous_id))))
omit [DecidableEq ν] [Nonempty ν] [DecidableEq ι] in
lemma Admissible.orientedLevel_inner_pos {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {I : Finset ι} (hI : I.Nonempty) {w : (Euc ν)} (hw : ‖w‖ = 1)
    (hwi : ∀ i ∈ I, 0 < f w i) {r : ι → ℝ} (hr : ∀ i ∈ I, 0 < r i)
    {u : (Euc ν)} (hu : u ∈ orientedLevel f w r) : 0 < ⟪w,u⟫ := by
  apply lt_of_le_of_ne hu.2.2
  intro he
  obtain ⟨i,hi⟩ := hI
  exact hf.orthogonal w u hw hu.1 he.symm i ⟨hwi i hi,by rw [hu.2.1]; exact hr i hi⟩
omit [DecidableEq ν] [Nonempty ν] [Fintype ι] [DecidableEq ι] in
lemma orientedLevel_cone {f : (Euc ν) → ι → ℝ} {I : Finset ι} {w : (Euc ν)} {r : ι → ℝ}
    (hr : ∀ i ∈ I, 0 < r i) {u : (Euc ν)} (hu : u ∈ orientedLevel f w r) :
    u ∈ commonPositiveCone f I := by
  intro i hi
  rw [homogeneousLift_unit f hu.1,hu.2.1]
  exact hr i hi
noncomputable def levelFibre (f : (Euc ν) → ι → ℝ) (w : (Euc ν)) (r : ι → ℝ) : Set ((Euc ν) × (SqMat ν)) :=
  {p | p.1 ∈ orientedLevel f w r ∧ 0 ≤ p.2 ∧ Matrix.trace p.2 = 1 ∧ (matrixOp ν) p.2 p.1 = 0}
omit [Nonempty ν] [DecidableEq ι] in
lemma Admissible.levelFibre_compact {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    (w : (Euc ν)) (r : ι → ℝ) : IsCompact (levelFibre f w r) := by
  have hA : Continuous (fun p : (Euc ν) × (SqMat ν) => (matrixOp ν) p.2) :=
    ((matrixOp ν)).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional.comp continuous_snd
  have he : levelFibre f w r = (orientedLevel f w r ×ˢ {Q : (SqMat ν) | 0 ≤ Q ∧ Matrix.trace Q = 1}) ∩
      {p | (matrixOp ν) p.2 p.1 = 0} := by ext p; simp only [levelFibre,Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_prod,and_assoc]
  rw [he]
  exact ((hf.orientedLevel_compact w r).prod positive_slice_compact).inter_right
    (isClosed_eq (hA.clm_apply continuous_fst) continuous_const)
omit [Nonempty ν] in
lemma balancedFibre_mem {u : (Euc ν)} (hu : ‖u‖ = 1) {Q : (SqMat ν)}
    (hQ : 0 ≤ Q) (htr : Matrix.trace Q = 1) (hQu : (matrixOp ν) Q u = 0) :
    ((1/2:ℝ) • rankOne u - (1/2:ℝ) • Q) ∈ traceSphere ν := by
  have hSA : IsSelfAdjoint ((1/2:ℝ) • rankOne u - (1/2:ℝ) • Q) :=
    ((IsSelfAdjoint.all (_:ℝ)).smul (rankOne_nonneg u).isSelfAdjoint).sub
      ((IsSelfAdjoint.all (_:ℝ)).smul hQ.isSelfAdjoint)
  refine ⟨hSA,?_⟩
  obtain ⟨hp,hn⟩ := rankOne_split_parts hQ hQu (show (0:ℝ) ≤ 1/2 by norm_num)
    (show (0:ℝ) ≤ 1/2 by norm_num)
  rw [← CFC.posPart_add_negPart _ hSA,hp,hn,Matrix.trace_add,Matrix.trace_smul,Matrix.trace_smul,
    rankOne_trace,hu,one_pow,htr]
  norm_num
end PurityGeometry
end
end

section
section
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
open Set
section FibreHomotopy
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι] [DecidableEq ι]
noncomputable def negativeCoordinates (f : (Euc ν) → ι → ℝ) (I : Finset ι) (Q : (SqMat ν)) :
    Euc ↥(Iᶜ : Finset ι) :=
  WithLp.toLp 2 (fun i => positiveExtension f Q i.val)
lemma Admissible.negativeCoordinates_sum {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {I : Finset ι} {u : (Euc ν)} (hu : u ∈ safeNormals (activeVectors f I))
    {Q : (SqMat ν)} (hQ : Q ∈ matrixFibre u) :
    (∑ i, negativeCoordinates f I Q i) = 1 := by
  have hz : ∀ i ∈ I, positiveExtension f Q i = 0 := fun i hi =>
    hf.positiveExtension_safe_zero hu hQ.1 hQ.2.2 hi
  have hs := hf.positiveExtension_sum hQ.1
  rw [hQ.2.1] at hs
  have he : ∑ i : ↥(Iᶜ : Finset ι), positiveExtension f Q i.val =
      ∑ i : ι, positiveExtension f Q i := by
    rw [Finset.sum_coe_sort]
    exact Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => hz i (by simpa using hi))
  exact he.trans hs
noncomputable def transportedFibre (c : (Euc ν)) (t : ℝ) (u : (Euc ν)) (Q : (SqMat ν)) : (SqMat ν) :=
  fibreTransport c u (chamberPath c u t) Q
noncomputable def centeredFibre (c u : (Euc ν)) (Q : (SqMat ν)) : (SqMat ν) :=
  matrixConjugate (householder c u) Q
omit [Nonempty ν] in
lemma centeredFibre_mem {c u : (Euc ν)} (hc : ‖c‖ = 1) (hu : ‖u‖ = 1) {Q : (SqMat ν)}
    (hQ : Q ∈ matrixFibre u) : centeredFibre c u Q ∈ matrixFibre c := by
  refine ⟨matrixConjugate_nonneg _ hQ.1,?_,?_⟩
  · rw [centeredFibre,matrixConjugate_trace,hQ.2.1]
  · simpa only [centeredFibre,householder_swap (hc.trans hu.symm)] using
      matrixConjugate_kernel (householder c u) hQ.2.2
omit [Nonempty ν] [DecidableEq ι] in
lemma transportedFibre_mem {f : (Euc ν) → ι → ℝ} (hf : Admissible f) {I : Finset ι}
    (hI : I.Nonempty) {c u : (Euc ν)} (hc : c ∈ commonPositiveCone f I) (hcn : ‖c‖ = 1)
    (hun : ‖u‖ = 1) (hu : u ∈ signChamber (activeVectors f I) c)
    {t : ℝ} (ht : t ∈ Icc 0 1) {Q : (SqMat ν)} (hQ : Q ∈ matrixFibre u) :
    transportedFibre c t u Q ∈ matrixFibre (chamberPath c u t) := by
  have hcs := hf.commonPositiveCone_safe I hc
  have hvn := chamberPath_norm (commonPositiveCone_active hI hc) hcs hu ht
  refine ⟨fibreTransport_nonneg _ _ _ hQ.1,?_,?_⟩
  · rw [transportedFibre,fibreTransport_trace,hQ.2.1]
  · exact fibreTransport_kernel (hcn.trans hun.symm) (hcn.trans hvn.symm) hQ.2.2
noncomputable def fibreHomotopy (f : (Euc ν) → ι → ℝ) (I : Finset ι) (c : (Euc ν))
    (g : (SqMat ν) → Euc ↥(Iᶜ : Finset ι)) (t : ℝ) (u : (Euc ν)) (Q : (SqMat ν)) :=
  negativeCoordinates f I (transportedFibre c t u Q) +
    t • (g (centeredFibre c u Q) - negativeCoordinates f I (centeredFibre c u Q))
omit [Nonempty ν] in
lemma fibreHomotopy_zero (f : (Euc ν) → ι → ℝ) (I : Finset ι) (c : (Euc ν))
    (g : (SqMat ν) → Euc ↥(Iᶜ : Finset ι)) {u : (Euc ν)} (hu : ‖u‖ = 1) (Q : (SqMat ν)) :
    fibreHomotopy f I c g 0 u Q = negativeCoordinates f I Q := by
  simp only [fibreHomotopy,zero_smul,add_zero,transportedFibre,chamberPath_zero c u hu,
    fibreTransport_self]
omit [Nonempty ν] in
lemma fibreHomotopy_one (f : (Euc ν) → ι → ℝ) (I : Finset ι) {c u : (Euc ν)} (hc : ‖c‖ = 1)
    (hu : ‖u‖ = 1) (g : (SqMat ν) → Euc ↥(Iᶜ : Finset ι)) {Q : (SqMat ν)}
    (hQ : Q ∈ matrixFibre u) : fibreHomotopy f I c g 1 u Q = g (centeredFibre c u Q) := by
  simp only [fibreHomotopy,one_smul,transportedFibre,chamberPath_one c u hc,
    fibreTransport_center hQ.1.isSelfAdjoint (hc.trans hu.symm) hQ.2.2]
  simp only [centeredFibre]
  abel
lemma Admissible.fibreHomotopy_sum {f : (Euc ν) → ι → ℝ} (hf : Admissible f) {I : Finset ι}
    (hI : I.Nonempty) {c u : (Euc ν)} (hc : c ∈ commonPositiveCone f I) (hcn : ‖c‖ = 1)
    (hun : ‖u‖ = 1) (hu : u ∈ signChamber (activeVectors f I) c)
    (g : (SqMat ν) → Euc ↥(Iᶜ : Finset ι))
    (hg : ∀ Q ∈ matrixFibre c, ∑ i, g Q i = 1)
    {t : ℝ} (ht : t ∈ Icc 0 1) {Q : (SqMat ν)} (hQ : Q ∈ matrixFibre u) :
    (∑ i, fibreHomotopy f I c g t u Q i) = 1 := by
  have hcs := hf.commonPositiveCone_safe I hc
  have hvs := signChamber_subset_safeNormals _ _ (chamberPath_mem (commonPositiveCone_active hI hc) hcs hu ht)
  have hT := transportedFibre_mem hf hI hc hcn hun hu ht hQ
  have hC := centeredFibre_mem hcn hun hQ
  simp only [fibreHomotopy,PiLp.add_apply,PiLp.smul_apply,PiLp.sub_apply,smul_eq_mul,
    Finset.sum_add_distrib]
  rw [← Finset.mul_sum,Finset.sum_sub_distrib]
  rw [hf.negativeCoordinates_sum hvs hT,hg _ hC,hf.negativeCoordinates_sum hcs hC]
  ring
lemma Admissible.fibreHomotopy_boundary_misses {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {I : Finset ι} (hI : I.Nonempty) {c u : (Euc ν)} (hc : c ∈ commonPositiveCone f I)
    (hcn : ‖c‖ = 1) (hun : ‖u‖ = 1) (hu : u ∈ signChamber (activeVectors f I) c)
    (g : (SqMat ν) → Euc ↥(Iᶜ : Finset ι)) {ε : ℝ} (hε : 0 < ε)
    (hg : ∀ Q ∈ matrixFibre c, ‖g Q - negativeCoordinates f I Q‖ < ε)
    (z : Euc ↥(Iᶜ : Finset ι)) (hz : ∀ i, ε < z i)
    {t : ℝ} (ht : t ∈ Icc 0 1) {Q : (SqMat ν)} (hQ : Q ∈ matrixFibre u)
    (hn : ¬ IsUnit (rankOne u + Q)) : fibreHomotopy f I c g t u Q ≠ z := by
  have hcs := hf.commonPositiveCone_safe I hc
  have hvmem := chamberPath_mem (commonPositiveCone_active hI hc) hcs hu ht
  have hvn := chamberPath_norm (commonPositiveCone_active hI hc) hcs hu ht
  have hT := transportedFibre_mem hf hI hc hcn hun hu ht hQ
  have htn : ¬ IsUnit (rankOne (chamberPath c u t) + transportedFibre c t u Q) := by
    intro h
    exact hn ((fibreTransport_unit_iff (hcn.trans hun.symm) (hcn.trans hvn.symm)).mp h)
  obtain ⟨i,hi,hzi⟩ := hf.fibre_boundary_missing (signChamber_subset_safeNormals _ _ hvmem) hT.1 htn
  let j : ↥(Iᶜ : Finset ι) := ⟨i,hi⟩
  have hC := centeredFibre_mem hcn hun hQ
  have hb : |(g (centeredFibre c u Q) - negativeCoordinates f I (centeredFibre c u Q)) j| < ε :=
    lt_of_le_of_lt (by simpa only [Real.norm_eq_abs] using
      (PiLp.norm_apply_le (g (centeredFibre c u Q) - negativeCoordinates f I (centeredFibre c u Q)) j)) (hg _ hC)
  intro he
  have hj := congrArg (fun v : Euc ↥(Iᶜ : Finset ι) => v j) he
  change positiveExtension f (transportedFibre c t u Q) i +
    t * ((g (centeredFibre c u Q) - negativeCoordinates f I (centeredFibre c u Q)) j) = z j at hj
  rw [hzi,zero_add] at hj
  have hjb := hz j
  have hab := abs_lt.mp hb
  have hle := mul_le_mul_of_nonneg_left hab.2.le ht.1
  have hh : t * ε ≤ ε := by nlinarith [ht.2]
  linarith
end FibreHomotopy
end
end

section
section
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
open Set
section FibreContinuity
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι] [DecidableEq ι]
lemma Admissible.negativeCoordinates_continuousOn {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    (I : Finset ι) : ContinuousOn (negativeCoordinates f I) {Q : (SqMat ν) | 0 ≤ Q} := by
  apply (PiLp.continuous_toLp 2 _).comp_continuousOn
  apply continuousOn_pi.mpr
  intro i
  exact (continuous_apply i.val).comp_continuousOn hf.positiveExtension_continuousOn
omit [Nonempty ν] in
lemma centeredFibre_continuousOn (c : (Euc ν)) :
    ContinuousOn (fun p : (Euc ν) × (SqMat ν) => centeredFibre c p.1 p.2) {p | c+p.1 ≠ 0} :=
  householder_matrix_joint_continuousOn c
omit [Nonempty ν] in
lemma fibreTransport_continuousOn_comp {X : Type*} [TopologicalSpace X]
    {S : Set X} (c : (Euc ν)) {u v : X → (Euc ν)} {Q : X → (SqMat ν)}
    (hu : ContinuousOn u S) (hv : ContinuousOn v S) (hQ : ContinuousOn Q S)
    (hc : ∀ x ∈ S, c+u x ≠ 0 ∧ c+v x ≠ 0) :
    ContinuousOn (fun x => fibreTransport c (u x) (v x) (Q x)) S := by
  exact ContinuousOn.comp' (g := fun p : (Euc ν) × (Euc ν) × (SqMat ν) => fibreTransport c p.1 p.2.1 p.2.2)
    (f := fun x : X => (u x,v x,Q x)) (s := S)
    (fibreTransport_continuousOn c) (hu.prodMk (hv.prodMk hQ)) hc
omit [DecidableEq ν] [Nonempty ν] in
lemma chamberPath_matrix_continuousOn {Z : Set (Euc ν)} {c : (Euc ν)} (hcz : c ∈ Z)
    (hcs : c ∈ safeNormals Z) :
    ContinuousOn (fun p : ℝ × (Euc ν) × (SqMat ν) => chamberPath c p.2.1 p.1)
      {p | p.1 ∈ Icc 0 1 ∧ p.2.1 ∈ signChamber Z c} := by
  have hp : Continuous (fun p : ℝ × (Euc ν) × (SqMat ν) => (p.1,p.2.1)) :=
    continuous_fst.prodMk continuous_snd.fst
  exact ContinuousOn.comp' (g := fun p : ℝ × (Euc ν) => chamberPath c p.2 p.1)
    (f := fun p : ℝ × (Euc ν) × (SqMat ν) => (p.1,p.2.1))
    (chamberPath_continuousOn hcz hcs) hp.continuousOn (fun _ h => h)
omit [DecidableEq ι] in
omit [Nonempty ν] in
lemma transportedFibre_continuousOn {f : (Euc ν) → ι → ℝ} (hf : Admissible f) {I : Finset ι}
    (hI : I.Nonempty) {c : (Euc ν)} (hc : c ∈ commonPositiveCone f I) :
    ContinuousOn (fun p : ℝ × (Euc ν) × (SqMat ν) => transportedFibre c p.1 p.2.1 p.2.2)
      {p | p.1 ∈ Icc 0 1 ∧ p.2.1 ∈ signChamber (activeVectors f I) c} := by
  have hcs := hf.commonPositiveCone_safe I hc
  have hcz := commonPositiveCone_active hI hc
  apply fibreTransport_continuousOn_comp c continuous_snd.fst.continuousOn
    (chamberPath_matrix_continuousOn hcz hcs) continuous_snd.snd.continuousOn
  intro p hp
  exact ⟨chamber_add_ne_zero hcz hcs hp.2,
    chamber_add_ne_zero hcz hcs (chamberPath_mem hcz hcs hp.2 hp.1)⟩
lemma Admissible.fibreHomotopy_continuousOn {f : (Euc ν) → ι → ℝ} (hf : Admissible f) {I : Finset ι}
    (hI : I.Nonempty) {c : (Euc ν)} (hc : c ∈ commonPositiveCone f I) (hcn : ‖c‖ = 1)
    (g : (SqMat ν) → Euc ↥(Iᶜ : Finset ι)) (hg : Continuous g) :
    ContinuousOn (fun p : ℝ × (Euc ν) × (SqMat ν) => fibreHomotopy f I c g p.1 p.2.1 p.2.2)
      {p | p.1 ∈ Icc 0 1 ∧ ‖p.2.1‖ = 1 ∧
        p.2.1 ∈ signChamber (activeVectors f I) c ∧ p.2.2 ∈ matrixFibre p.2.1} := by
  have hcs := hf.commonPositiveCone_safe I hc
  have hcz := commonPositiveCone_active hI hc
  let S : Set (ℝ × (Euc ν) × (SqMat ν)) := {p | p.1 ∈ Icc 0 1 ∧ ‖p.2.1‖ = 1 ∧
        p.2.1 ∈ signChamber (activeVectors f I) c ∧ p.2.2 ∈ matrixFibre p.2.1}
  have hT : ContinuousOn (fun p : ℝ × (Euc ν) × (SqMat ν) => transportedFibre c p.1 p.2.1 p.2.2) S :=
    (transportedFibre_continuousOn hf hI hc).mono (fun _ hp => ⟨hp.1,hp.2.2.1⟩)
  have hC : ContinuousOn (fun p : ℝ × (Euc ν) × (SqMat ν) => centeredFibre c p.2.1 p.2.2) S :=
    (centeredFibre_continuousOn c).comp continuous_snd.continuousOn
      (fun _ hp => chamber_add_ne_zero hcz hcs hp.2.2.1)
  have hET := (hf.negativeCoordinates_continuousOn I).comp hT
    (fun _ hp => (transportedFibre_mem hf hI hc hcn hp.2.1 hp.2.2.1 hp.1 hp.2.2.2).1)
  have hEC := (hf.negativeCoordinates_continuousOn I).comp hC
    (fun _ hp => (centeredFibre_mem hcn hp.2.1 hp.2.2.2).1)
  exact hET.add (continuous_fst.continuousOn.smul ((hg.comp_continuousOn hC).sub hEC))
end FibreContinuity
end
end

section
section
open scoped BigOperators
section BlockVector
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
noncomputable def blockVector (I : Finset ι) (lam : ℝ) (r : ι → ℝ) (mu : ℝ)
    (z : Euc ↥(Iᶜ : Finset ι)) : Euc ι :=
  WithLp.toLp 2 (fun i => if hi : i ∈ I then lam * r i else -mu * z ⟨i,Finset.mem_compl.mpr hi⟩)
lemma blockVector_in (I : Finset ι) (lam : ℝ) (r : ι → ℝ) (mu : ℝ)
    (z : Euc ↥(Iᶜ : Finset ι)) {i : ι} (hi : i ∈ I) :
    blockVector I lam r mu z i = lam * r i := by simp [blockVector,hi]
lemma blockVector_out (I : Finset ι) (lam : ℝ) (r : ι → ℝ) (mu : ℝ)
    (z : Euc ↥(Iᶜ : Finset ι)) (i : ↥(Iᶜ : Finset ι)) :
    blockVector I lam r mu z i.val = -mu * z i := by simp [blockVector,Finset.mem_compl.mp i.property]
lemma blockVector_continuous {X : Type*} [TopologicalSpace X] (I : Finset ι)
    {lam mu : X → ℝ} {r : X → ι → ℝ} {z : X → Euc ↥(Iᶜ : Finset ι)}
    (hl : Continuous lam) (hr : Continuous r) (hm : Continuous mu) (hz : Continuous z) :
    Continuous (fun x => blockVector I (lam x) (r x) (mu x) (z x)) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  by_cases hi : i ∈ I
  · simp only [dif_pos hi]
    exact hl.mul ((continuous_apply i).comp hr)
  · simp only [dif_neg hi]
    let j : ↥(Iᶜ : Finset ι) := ⟨i,Finset.mem_compl.mpr hi⟩
    have hj : Continuous (fun x => z x j) := (PiLp.continuous_apply 2 _ j).comp hz
    exact hm.neg.mul hj
lemma blockVector_continuousOn {X : Type*} [TopologicalSpace X] (I : Finset ι) {S : Set X}
    {lam mu : X → ℝ} {r : X → ι → ℝ} {z : X → Euc ↥(Iᶜ : Finset ι)}
    (hl : ContinuousOn lam S) (hr : ContinuousOn r S) (hm : ContinuousOn mu S) (hz : ContinuousOn z S) :
    ContinuousOn (fun x => blockVector I (lam x) (r x) (mu x) (z x)) S := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  exact blockVector_continuous I (continuousOn_iff_continuous_domRestrict.mp hl)
    (continuousOn_iff_continuous_domRestrict.mp hr) (continuousOn_iff_continuous_domRestrict.mp hm)
    (continuousOn_iff_continuous_domRestrict.mp hz)
lemma blockVector_nonzero {I : Finset ι} (hI : I.Nonempty) {lam mu : ℝ} (hl : 0 < lam)
    {r : ι → ℝ} (hr : ∀ i ∈ I, 0 < r i) (z : Euc ↥(Iᶜ : Finset ι)) :
    blockVector I lam r mu z ≠ 0 := by
  obtain ⟨i,hi⟩ := hI
  intro h
  have he := congrArg (fun v : Euc ι => v i) h
  rw [blockVector_in _ _ _ _ _ hi] at he
  exact (ne_of_gt (mul_pos hl (hr i hi))) he
lemma blockVector_ray {I : Finset ι} {lam mu t : ℝ} (_hl : 0 < lam) (_hm : 0 < mu)
    (hlm : lam + mu = 1) (_ht : 0 < t) {a r : ι → ℝ}
    (hao : ∀ i ∉ I, a i = 0) (hro : ∀ i ∉ I, r i = 0)
    (has : ∑ i, a i = 1) (hrs : ∑ i, r i = 1)
    {b z : Euc ↥(Iᶜ : Finset ι)} (hbs : ∑ i, b i = 1) (hzs : ∑ i, z i = 1)
    (he : blockVector I lam a mu b = t • blockVector I (1/2:ℝ) r (1/2:ℝ) z) :
    t = 1 ∧ lam = 1/2 ∧ mu = 1/2 ∧ a = r ∧ b = z := by
  have hei (i : ι) (hi : i ∈ I) : lam * a i = t * ((1/2:ℝ) * r i) := by
    have h := congrArg (fun v : Euc ι => v i) he
    simpa only [PiLp.smul_apply,smul_eq_mul,blockVector_in _ _ _ _ _ hi] using h
  have heo (i : ↥(Iᶜ : Finset ι)) : -mu * b i = t * (-(1/2:ℝ) * z i) := by
    have h := congrArg (fun v : Euc ι => v i.val) he
    simpa only [PiLp.smul_apply,smul_eq_mul,blockVector_out] using h
  have hia : ∑ i ∈ I, a i = 1 := by
    rw [← has]; exact Finset.sum_subset (Finset.subset_univ I) (fun i _ hi => hao i hi)
  have hir : ∑ i ∈ I, r i = 1 := by
    rw [← hrs]; exact Finset.sum_subset (Finset.subset_univ I) (fun i _ hi => hro i hi)
  have hl' : lam = t*(1/2:ℝ) := by
    have hs := Finset.sum_congr (s₁ := I) (rfl) hei
    simpa only [← Finset.mul_sum,hia,hir,mul_one] using hs
  have hm' : -mu = t*(-(1/2:ℝ)) := by
    have hs := congrArg (fun v : ↥(Iᶜ : Finset ι) → ℝ => ∑ i, v i) (funext heo)
    simpa only [← Finset.mul_sum,hbs,hzs,mul_one] using hs
  have ht1 : t = 1 := by linarith
  have hl2 : lam = 1/2 := by linarith
  have hm2 : mu = 1/2 := by linarith
  refine ⟨ht1,hl2,hm2,?_,?_⟩
  · funext i
    by_cases hi : i ∈ I
    · have h := hei i hi; rw [ht1,hl2] at h; linarith
    · rw [hao i hi,hro i hi]
  · apply PiLp.ext
    intro i
    have h := heo i; rw [ht1,hm2] at h; linarith
end BlockVector
end
end

section
section
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
open Set
section MixedHomotopy
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι] [DecidableEq ι]
omit [DecidableEq ν] [Nonempty ν] [DecidableEq ι] in
lemma Admissible.cone_unit_positive {f : (Euc ν) → ι → ℝ} (_hf : Admissible f)
    {I : Finset ι} {u : (Euc ν)} (hu : ‖u‖ = 1) (hc : u ∈ commonPositiveCone f I) :
    ∀ i ∈ I, 0 < f u i := by
  intro i hi
  simpa only [homogeneousLift_unit f hu] using hc i hi
omit [DecidableEq ν] [Nonempty ν] [DecidableEq ι] in
lemma Admissible.maximal_cone_zero {f : (Euc ν) → ι → ℝ} (hf : Admissible f) {I : Finset ι}
    (hmax : ∀ u : (Euc ν), ‖u‖ = 1 → I ⊆ positiveSupport f u → positiveSupport f u = I)
    {u : (Euc ν)} (hu : ‖u‖ = 1) (hc : u ∈ commonPositiveCone f I) :
    ∀ i ∉ I, f u i = 0 := by
  have he : positiveSupport f u = I := hmax u hu (fun i hi =>
    (mem_positiveSupport f u i).mpr (hf.cone_unit_positive hu hc i hi))
  intro i hi
  apply le_antisymm _ (hf.nonneg u hu i)
  by_contra hp
  have hh := (mem_positiveSupport f u i).mpr (lt_of_not_ge hp)
  rw [he] at hh
  exact hi hh
omit [Nonempty ν] in
lemma traceSphere_weights {A : (SqMat ν)} (hA : A ∈ traceSphere ν) :
    Matrix.trace A⁺ + Matrix.trace A⁻ = 1 := by
  rw [← Matrix.trace_add,CFC.posPart_add_negPart A hA.1]; exact hA.2
noncomputable def mixedHomotopy (f : (Euc ν) → ι → ℝ) (I : Finset ι) (w c : (Euc ν))
    (g : (SqMat ν) → Euc ↥(Iᶜ : Finset ι)) (t : ℝ) (A : (SqMat ν)) : (Euc ι) :=
  blockVector I (Matrix.trace A⁺) (f (lineRepresentative w A)) (Matrix.trace A⁻)
    (fibreHomotopy f I c g t (lineRepresentative w A) (negativeFibre A))
lemma Admissible.mixedHomotopy_zero {f : (Euc ν) → ι → ℝ} (hf : Admissible f) {I : Finset ι}
    (hmax : ∀ u : (Euc ν), ‖u‖ = 1 → I ⊆ positiveSupport f u → positiveSupport f u = I)
    {w c : (Euc ν)} (g : (SqMat ν) → Euc ↥(Iᶜ : Finset ι)) {A : (SqMat ν)}
    (hSA : IsSelfAdjoint A) (hA : A ∈ purityChart f I w c) :
    mixedHomotopy f I w c g 0 A = WithLp.toLp 2 (signedExtension f A) := by
  have hu := purityChart_unit hA
  have hQ := purityChart_fibre hA
  have hl := hasPositiveLine_trace_pos hA.2.1
  have hm := hA.2.2.2.1
  have hs := (hf.signedExtension_splitting hSA hu hl (positive_line_representative hA.2.1 hA.2.2.1)).2.2
  have hneg : positiveExtension f A⁻ = Matrix.trace A⁻ • positiveExtension f (negativeFibre A) := by
    calc
      positiveExtension f A⁻ = positiveExtension f (Matrix.trace A⁻ • negativeFibre A) :=
        congrArg (positiveExtension f) (negativeFibre_smul (ne_of_gt hm)).symm
      _ = _ := positiveExtension_smul_nonneg f hQ.1 hm.le
  have hpos := hf.cone_unit_positive hu hA.2.2.2.2.1
  have hzero := hf.maximal_cone_zero hmax hu hA.2.2.2.2.1
  have hsafe := hf.commonPositiveCone_safe I hA.2.2.2.2.1
  apply PiLp.ext
  intro i
  change blockVector I (Matrix.trace A⁺) (f (lineRepresentative w A)) (Matrix.trace A⁻)
    (fibreHomotopy f I c g 0 (lineRepresentative w A) (negativeFibre A)) i = signedExtension f A i
  rw [fibreHomotopy_zero f I c g hu,hs,hneg]
  by_cases hi : i ∈ I
  · rw [blockVector_in _ _ _ _ _ hi]
    have hz := hf.positiveExtension_safe_zero hsafe hQ.1 hQ.2.2 hi
    simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,hz,mul_zero,sub_zero]
  · let j : ↥(Iᶜ : Finset ι) := ⟨i,Finset.mem_compl.mpr hi⟩
    have hj := blockVector_out I (Matrix.trace A⁺) (f (lineRepresentative w A)) (Matrix.trace A⁻)
      (negativeCoordinates f I (negativeFibre A)) j
    rw [hj]
    simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,hzero i hi,mul_zero,zero_sub]
    exact neg_mul _ _
omit [Nonempty ν] in
lemma Admissible.mixedHomotopy_nonzero {f : (Euc ν) → ι → ℝ} (hf : Admissible f) {I : Finset ι}
    (hI : I.Nonempty) {w c : (Euc ν)} (g : (SqMat ν) → Euc ↥(Iᶜ : Finset ι))
    (t : ℝ) {A : (SqMat ν)} (hA : A ∈ purityChart f I w c) : mixedHomotopy f I w c g t A ≠ 0 :=
  blockVector_nonzero hI (hasPositiveLine_trace_pos hA.2.1)
    (hf.cone_unit_positive (purityChart_unit hA) hA.2.2.2.2.1) _
lemma Admissible.mixedHomotopy_continuousOn {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {I : Finset ι} (hI : I.Nonempty) {w c : (Euc ν)} (hc : c ∈ commonPositiveCone f I) (hcn : ‖c‖ = 1)
    (g : (SqMat ν) → Euc ↥(Iᶜ : Finset ι)) (hg : Continuous g) :
    ContinuousOn (fun p : ℝ × traceSphere ν => mixedHomotopy f I w c g p.1 p.2.val)
      (Icc (0:ℝ) 1 ×ˢ {A : traceSphere ν | A.val ∈ purityChart f I w c}) := by
  let S : Set (ℝ × traceSphere ν) := Icc (0:ℝ) 1 ×ˢ {A : traceSphere ν | A.val ∈ purityChart f I w c}
  have hA : Continuous (fun p : ℝ × traceSphere ν => p.2.val) := continuous_subtype_val.comp continuous_snd
  have hSA : ∀ p : ℝ × traceSphere ν, IsSelfAdjoint p.2.val := fun p => p.2.property.1
  have hu : ContinuousOn (fun p : ℝ × traceSphere ν => lineRepresentative w p.2.val) S :=
    (lineRepresentative_continuousOn _ hA hSA w).mono (fun p hp => hp.2.2.2.1)
  have hQ : ContinuousOn (fun p : ℝ × traceSphere ν => negativeFibre p.2.val) S :=
    (negativeFibre_continuousOn _ hA hSA).mono (fun p hp => ne_of_gt hp.2.2.2.2.1)
  have htuple : ContinuousOn (fun p : ℝ × traceSphere ν =>
      (p.1,lineRepresentative w p.2.val,negativeFibre p.2.val)) S :=
    continuous_fst.continuousOn.prodMk (hu.prodMk hQ)
  have hF : ContinuousOn (fun p : ℝ × traceSphere ν =>
      fibreHomotopy f I c g p.1 (lineRepresentative w p.2.val) (negativeFibre p.2.val)) S :=
    ContinuousOn.comp' (g := fun p : ℝ × (Euc ν) × (SqMat ν) => fibreHomotopy f I c g p.1 p.2.1 p.2.2)
      (f := fun p : ℝ × traceSphere ν => (p.1,lineRepresentative w p.2.val,negativeFibre p.2.val))
      (hf.fibreHomotopy_continuousOn hI hc hcn g hg) htuple
      (fun p hp => ⟨hp.1,purityChart_unit hp.2,interior_subset hp.2.2.2.2.2.2,purityChart_fibre hp.2⟩)
  have hl : Continuous (fun p : ℝ × traceSphere ν => Matrix.trace p.2.val⁺) :=
    matrix_trace_continuous.comp (matrix_posPart_continuousOn.comp_continuous hA hSA)
  have hm : Continuous (fun p : ℝ × traceSphere ν => Matrix.trace p.2.val⁻) :=
    matrix_trace_continuous.comp (matrix_negPart_continuousOn.comp_continuous hA hSA)
  have hfC : Continuous f := continuous_pi (fun i => (hf.smooth i).continuous)
  exact blockVector_continuousOn I hl.continuousOn (hfC.comp_continuousOn hu) hm.continuousOn hF
end MixedHomotopy
end
end

section
section
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
open Set
section MixedHits
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι] [DecidableEq ι]
lemma Admissible.mixedHomotopy_hit {f : (Euc ν) → ι → ℝ} (hf : Admissible f) {I : Finset ι}
    (hI : I.Nonempty)
    (hmax : ∀ u : (Euc ν), ‖u‖ = 1 → I ⊆ positiveSupport f u → positiveSupport f u = I)
    {w c : (Euc ν)} (hc : c ∈ commonPositiveCone f I) (hcn : ‖c‖ = 1)
    (g : (SqMat ν) → Euc ↥(Iᶜ : Finset ι)) (hg : ∀ Q ∈ matrixFibre c, ∑ i, g Q i = 1)
    {r : ι → ℝ} (hro : ∀ i ∉ I, r i = 0) (hrs : ∑ i, r i = 1)
    {z : Euc ↥(Iᶜ : Finset ι)} (hzs : ∑ i, z i = 1)
    {t d : ℝ} (ht : t ∈ Icc 0 1) (hd : 0 < d) {A : (SqMat ν)}
    (hSA : A ∈ traceSphere ν) (hA : A ∈ purityChart f I w c)
    (he : mixedHomotopy f I w c g t A = d • blockVector I (1/2:ℝ) r (1/2:ℝ) z) :
    lineRepresentative w A ∈ orientedLevel f w r ∧
      fibreHomotopy f I c g t (lineRepresentative w A) (negativeFibre A) = z ∧
      A = (1/2:ℝ) • rankOne (lineRepresentative w A) - (1/2:ℝ) • negativeFibre A := by
  have hu := purityChart_unit hA
  have hQ := purityChart_fibre hA
  have hl := hasPositiveLine_trace_pos hA.2.1
  have hm := hA.2.2.2.1
  have hzero := hf.maximal_cone_zero hmax hu hA.2.2.2.2.1
  have hsum := hf.fibreHomotopy_sum hI hc hcn hu (interior_subset hA.2.2.2.2.2) g hg ht hQ
  obtain ⟨-,hl2,hm2,ha,hb⟩ := blockVector_ray hl hm (traceSphere_weights hSA) hd hzero hro
    (hf.sum_one _ hu) hrs hsum hzs he
  refine ⟨⟨hu,ha,(lineRepresentative_inner_pos hA.2.1 hA.2.2.1).le⟩,hb,?_⟩
  calc
    A = Matrix.trace A⁺ • rankOne (lineRepresentative w A) - Matrix.trace A⁻ • negativeFibre A :=
      negativeFibre_splitting hSA.1 hA.2.1 hA.2.2.1 hm
    _ = _ := by rw [hl2,hm2]
omit [DecidableEq ι] in
lemma Admissible.negative_trace_pos {f : (Euc ν) → ι → ℝ} (hf : Admissible f) {A : (SqMat ν)} {i : ι}
    (hi : signedExtension f A i < 0) : 0 < Matrix.trace A⁻ := by
  have hp := (hf.signedExtension_neg_iff A i).mp hi
  have hle : positiveExtension f A⁻ i ≤ Matrix.trace A⁻ := by
    rw [← hf.positiveExtension_sum (CFC.negPart_nonneg A)]
    exact Finset.single_le_sum (fun j _ => hf.positiveExtension_nonneg A⁻ j) (Finset.mem_univ i)
  exact hp.trans_le hle
lemma Admissible.original_ray_level {f : (Euc ν) → ι → ℝ} (hf : Admissible f) {I : Finset ι}
    (hI : I.Nonempty) [Nonempty ↥(Iᶜ : Finset ι)]
    (hmax : ∀ u : (Euc ν), ‖u‖ = 1 → I ⊆ positiveSupport f u → positiveSupport f u = I)
    {w : (Euc ν)} (hw : ‖w‖ = 1) (hwi : ∀ i ∈ I, 0 < f w i)
    {r : ι → ℝ} (hr : ∀ i ∈ I, 0 < r i) (hro : ∀ i ∉ I, r i = 0) (hrs : ∑ i, r i = 1)
    {z : Euc ↥(Iᶜ : Finset ι)} (hz : ∀ i, 0 < z i) (hzs : ∑ i, z i = 1)
    {A : (SqMat ν)} (hA : A ∈ traceSphere ν) {d : ℝ} (hd : 0 < d)
    (he : WithLp.toLp 2 (signedExtension f A) = d • blockVector I (1/2:ℝ) r (1/2:ℝ) z) :
    IsUnit A ∧ HasPositiveLine A ∧ (matrixOp ν) A⁺ w ≠ 0 ∧ 0 < Matrix.trace A⁻ ∧
      lineRepresentative w A ∈ orientedLevel f w r := by
  have hpos (i : ι) (hi : i ∈ I) : 0 < signedExtension f A i := by
    have hh := congrArg (fun v : (Euc ι) => v i) he
    change signedExtension f A i = d * blockVector I (1/2:ℝ) r (1/2:ℝ) z i at hh
    rw [hh,blockVector_in _ _ _ _ _ hi]
    exact mul_pos hd (mul_pos (by norm_num) (hr i hi))
  have hneg (i : ↥(Iᶜ : Finset ι)) : signedExtension f A i.val < 0 := by
    have hh := congrArg (fun v : (Euc ι) => v i.val) he
    change signedExtension f A i.val = d * blockVector I (1/2:ℝ) r (1/2:ℝ) z i.val at hh
    rw [hh,blockVector_out]
    exact mul_neg_of_pos_of_neg hd (mul_neg_of_neg_of_pos (by norm_num) (hz i))
  have hunit : IsUnit A := hf.signedExtension_fullSupport hA.1 (fun i => by
    by_cases hi : i ∈ I
    · exact ne_of_gt (hpos i hi)
    · exact ne_of_lt (hneg ⟨i,Finset.mem_compl.mpr hi⟩))
  obtain ⟨i,hi⟩ := hI
  have hline : HasPositiveLine A := hf.signedExtension_positive_rankOne hw hwi
    (fun j hj => (hneg ⟨j,Finset.mem_compl.mpr hj⟩).le) ⟨i,hpos i hi⟩
  have hAw : (matrixOp ν) A⁺ w ≠ 0 := by
    obtain ⟨u,hu,lam,hl,hP⟩ := hline
    have hui : 0 < f u i := (hf.signedExtension_line_labels hu hl hP i).mp (hpos i hi)
    have hwu : ⟪w,u⟫ ≠ 0 := fun heq => hf.orthogonal w u hw hu heq i ⟨hwi i hi,hui⟩
    exact unit_rankOne_inner_nonzero ⟨u,hu,lam,hl,hP⟩ hu hl hP hwu
  have hu := lineRepresentative_norm hAw
  have hc : lineRepresentative w A ∈ commonPositiveCone f I := by
    intro j hj
    rw [homogeneousLift_unit f hu]
    exact (hf.signedExtension_line_labels hu (hasPositiveLine_trace_pos hline)
      (positive_line_representative hline hAw) j).mp (hpos j hj)
  have hm := hf.negative_trace_pos (hneg (Classical.arbitrary ↥(Iᶜ : Finset ι)))
  have hchart : A ∈ purityChart f I w (lineRepresentative w A) :=
    ⟨hunit,hline,hAw,hm,hc,interior_safe_mem_own_chamber (hf.commonPositiveCone_interior_safe I hc)⟩
  have hg := hf.mixedHomotopy_zero hmax (fun _ => (0 : Euc ↥(Iᶜ : Finset ι))) hA.1 hchart
  have hb : blockVector I (Matrix.trace A⁺) (f (lineRepresentative w A)) (Matrix.trace A⁻)
      (negativeCoordinates f I (negativeFibre A)) = d • blockVector I (1/2:ℝ) r (1/2:ℝ) z := by
    rw [← he,← hg]
    exact congrArg (blockVector I (Matrix.trace A⁺) (f (lineRepresentative w A)) (Matrix.trace A⁻))
      (fibreHomotopy_zero f I (lineRepresentative w A) (fun _ => 0) hu (negativeFibre A)).symm
  have hQ := purityChart_fibre hchart
  obtain ⟨-,-,-,ha,-⟩ := blockVector_ray (hasPositiveLine_trace_pos hline) hm (traceSphere_weights hA) hd
    (hf.maximal_cone_zero hmax hu hc) hro (hf.sum_one _ hu) hrs
    (hf.negativeCoordinates_sum (hf.commonPositiveCone_safe I hc) hQ) hzs hb
  exact ⟨hunit,hline,hAw,hm,hu,ha,(lineRepresentative_inner_pos hline hAw).le⟩
end MixedHits
end
end

section
section
open scoped BigOperators Topology
noncomputable def finiteOpenGlue {κ X Y : Type*} [Fintype κ] [AddCommMonoid Y]
    (S : κ → Set X) (f : κ → X → Y) : X → Y :=
  by classical exact fun x => ∑ i, if x ∈ S i then f i x else 0
lemma finiteOpenGlue_eq {κ X Y : Type*} [Fintype κ] [AddCommMonoid Y]
    {S : κ → Set X} (hS : Pairwise (fun i j => Disjoint (S i) (S j))) (f : κ → X → Y)
    {i : κ} {x : X} (hx : x ∈ S i) : finiteOpenGlue S f x = f i x := by
  classical
  rw [finiteOpenGlue,Finset.sum_eq_single i]
  · simp [hx]
  · intro j hj hji
    have hjx : x ∉ S j := fun hp => Set.disjoint_left.mp (hS hji) hp hx
    simp [hjx]
  · simp
lemma finiteOpenGlue_continuousOn_prod {κ X Y : Type*} [Fintype κ]
    [TopologicalSpace X] [TopologicalSpace Y] [AddCommMonoid Y]
    {S : κ → Set X} (hSo : ∀ i, IsOpen (S i)) (hS : Pairwise (fun i j => Disjoint (S i) (S j)))
    (f : κ → ℝ × X → Y) (hf : ∀ i, ContinuousOn (f i) (Set.Icc (0:ℝ) 1 ×ˢ S i)) :
    ContinuousOn (finiteOpenGlue (fun i => {p : ℝ × X | p.2 ∈ S i}) f)
      (Set.Icc (0:ℝ) 1 ×ˢ ⋃ i, S i) := by
  intro p hp
  obtain ⟨i,hpi⟩ := Set.mem_iUnion.mp hp.2
  have hn : ∀ᶠ q in 𝓝 p, q.2 ∈ S i :=
    continuous_snd.continuousAt.preimage_mem_nhds ((hSo i).mem_nhds hpi)
  have hs : Set.Icc (0:ℝ) 1 ×ˢ S i ∈ 𝓝[Set.Icc (0:ℝ) 1 ×ˢ ⋃ i, S i] p := by
    filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds hn,self_mem_nhdsWithin] with q hq hqi
    exact ⟨hqi.1,hq⟩
  have hSp : Pairwise (fun i j => Disjoint {p : ℝ × X | p.2 ∈ S i} {p : ℝ × X | p.2 ∈ S j}) := by
    intro i j hij
    exact Set.disjoint_left.mpr (fun p hi hj => Set.disjoint_left.mp (hS hij) hi hj)
  apply ((hf i p ⟨hp.1,hpi⟩).mono_of_mem_nhdsWithin hs).congr_of_eventuallyEq
  · filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds hn] with q hq
    exact finiteOpenGlue_eq hSp f hq
  · exact finiteOpenGlue_eq hSp f hpi
end
end

section
section
open Set
lemma compact_target_hits {P X Y : Type*} [TopologicalSpace P] [CompactSpace P]
    [TopologicalSpace X] [TopologicalSpace Y] [T1Space Y]
    (φ : P → X) (hφ : Continuous φ) (K : ℝ × P → Y)
    (hK : ContinuousOn K (Icc (0:ℝ) 1 ×ˢ univ)) (y : Y) :
    IsCompact {x : X | ∃ p : P, φ p = x ∧ ∃ t ∈ Icc (0:ℝ) 1, K (t,p) = y} := by
  have hC : IsCompact ((Icc (0:ℝ) 1 ×ˢ (univ : Set P)) ∩ K ⁻¹' {y}) :=
    ((isCompact_Icc.prod isCompact_univ) : IsCompact (Icc (0:ℝ) 1 ×ˢ (univ : Set P))).of_isClosed_subset
      (hK.preimage_isClosed_of_isClosed (isClosed_Icc.prod isClosed_univ) isClosed_singleton) inter_subset_left
  have he : {x : X | ∃ p : P, φ p = x ∧ ∃ t ∈ Icc (0:ℝ) 1, K (t,p) = y} =
      (fun q : ℝ × P => φ q.2) '' ((Icc (0:ℝ) 1 ×ˢ (univ : Set P)) ∩ K ⁻¹' {y}) := by
    ext x
    constructor
    · rintro ⟨p,hp,t,ht,hk⟩
      exact ⟨(t,p),⟨⟨ht,mem_univ _⟩,hk⟩,hp⟩
    · rintro ⟨⟨t,p⟩,⟨⟨ht,-⟩,hk⟩,hp⟩
      exact ⟨p,hp,t,ht,hk⟩
  rw [he]
  exact hC.image (hφ.comp continuous_snd)
end
section
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
open Set
section LevelModel
variable {ν ι κ : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι] [DecidableEq ι] [Fintype κ]
noncomputable def balancedModel {f : (Euc ν) → ι → ℝ} {w : (Euc ν)} {r : ι → ℝ}
    (p : levelFibre f w r) : traceSphere ν :=
  ⟨(1/2:ℝ) • rankOne p.val.1 - (1/2:ℝ) • p.val.2,
    balancedFibre_mem p.property.1.1 p.property.2.1 p.property.2.2.1 p.property.2.2.2⟩
omit [Fintype ι] [DecidableEq ι] in
omit [Nonempty ν] in
lemma balancedModel_continuous (f : (Euc ν) → ι → ℝ) (w : (Euc ν)) (r : ι → ℝ) :
    Continuous (balancedModel (f := f) (w := w) (r := r)) := by
  apply Continuous.subtype_mk
  change Continuous (fun p : levelFibre f w r => (1/2:ℝ) • rankOne p.val.1 - (1/2:ℝ) • p.val.2)
  exact ((continuous_const : Continuous (fun _ : levelFibre f w r => (1/2:ℝ))).smul
    (rankOne_continuous.comp continuous_subtype_val.fst)).sub
    ((continuous_const : Continuous (fun _ : levelFibre f w r => (1/2:ℝ))).smul continuous_subtype_val.snd)
noncomputable def modelChambers (f : (Euc ν) → ι → ℝ) (I : Finset ι) (w : (Euc ν)) (r : ι → ℝ)
    (c : κ → (Euc ν)) (j : κ) : Set (levelFibre f w r) :=
  {p | p.val.1 ∈ interior (signChamber (activeVectors f I) (c j))}
omit [Nonempty ν] [Fintype ι] [DecidableEq ι] [Fintype κ] in
lemma modelChambers_open (f : (Euc ν) → ι → ℝ) (I : Finset ι) (w : (Euc ν)) (r : ι → ℝ) (c : κ → (Euc ν)) (j : κ) :
    IsOpen (modelChambers f I w r c j) :=
  isOpen_interior.preimage continuous_subtype_val.fst
omit [Nonempty ν] [Fintype ι] [DecidableEq ι] [Fintype κ] in
lemma modelChambers_disjoint {f : (Euc ν) → ι → ℝ} {I : Finset ι} {w : (Euc ν)} {r : ι → ℝ} {c : κ → (Euc ν)}
    (hd : Pairwise (fun i j => Disjoint (interior (signChamber (activeVectors f I) (c i)))
      (interior (signChamber (activeVectors f I) (c j))))) :
    Pairwise (fun i j => Disjoint (modelChambers f I w r c i) (modelChambers f I w r c j)) := by
  intro i j hij
  exact Set.disjoint_left.mpr (fun p hp hq => Set.disjoint_left.mp (hd hij) hp hq)
omit [Nonempty ν] [Fintype ι] [DecidableEq ι] [Fintype κ] in
lemma modelChambers_cover {f : (Euc ν) → ι → ℝ} {I : Finset ι} {w : (Euc ν)} {r : ι → ℝ} {c : κ → (Euc ν)}
    (hc : orientedLevel f w r ⊆ ⋃ j, interior (signChamber (activeVectors f I) (c j))) :
    (⋃ j, modelChambers f I w r c j) = univ := by
  apply eq_univ_of_forall
  intro p
  obtain ⟨j,hj⟩ := mem_iUnion.mp (hc p.property.1)
  exact mem_iUnion.mpr ⟨j,hj⟩
noncomputable def levelHomotopy (f : (Euc ν) → ι → ℝ) (I : Finset ι) (w : (Euc ν)) (r : ι → ℝ)
    (c : κ → (Euc ν)) (g : κ → (SqMat ν) → Euc ↥(Iᶜ : Finset ι)) :
    ℝ × levelFibre f w r → Euc ↥(Iᶜ : Finset ι) :=
  finiteOpenGlue (fun j => {p | p.2 ∈ modelChambers f I w r c j})
    (fun j p => fibreHomotopy f I (c j) (g j) p.1 p.2.val.1 p.2.val.2)
omit [Nonempty ν] in
lemma levelHomotopy_eq {f : (Euc ν) → ι → ℝ} {I : Finset ι} {w : (Euc ν)} {r : ι → ℝ} {c : κ → (Euc ν)}
    (hd : Pairwise (fun i j => Disjoint (interior (signChamber (activeVectors f I) (c i)))
      (interior (signChamber (activeVectors f I) (c j)))))
    (g : κ → (SqMat ν) → Euc ↥(Iᶜ : Finset ι)) {p : levelFibre f w r} {j : κ}
    (hp : p.val.1 ∈ interior (signChamber (activeVectors f I) (c j))) (t : ℝ) :
    levelHomotopy f I w r c g (t,p) = fibreHomotopy f I (c j) (g j) t p.val.1 p.val.2 := by
  apply finiteOpenGlue_eq
  · intro a b hab
    exact Set.disjoint_left.mpr (fun q ha hb => Set.disjoint_left.mp (hd hab) ha hb)
  · exact hp
lemma Admissible.levelHomotopy_continuousOn {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {I : Finset ι} (hI : I.Nonempty) {w : (Euc ν)} {r : ι → ℝ} (c : κ → (Euc ν))
    (hc : ∀ j, c j ∈ commonPositiveCone f I) (hcn : ∀ j, ‖c j‖ = 1)
    (hd : Pairwise (fun i j => Disjoint (interior (signChamber (activeVectors f I) (c i)))
      (interior (signChamber (activeVectors f I) (c j)))))
    (hcover : orientedLevel f w r ⊆ ⋃ j, interior (signChamber (activeVectors f I) (c j)))
    (g : κ → (SqMat ν) → Euc ↥(Iᶜ : Finset ι)) (hg : ∀ j, Continuous (g j)) :
    ContinuousOn (levelHomotopy f I w r c g) (Icc (0:ℝ) 1 ×ˢ univ) := by
  rw [← modelChambers_cover hcover]
  apply finiteOpenGlue_continuousOn_prod (modelChambers_open f I w r c) (modelChambers_disjoint hd)
  intro j
  have hpar : Continuous (fun p : ℝ × levelFibre f w r => (p.1,p.2.val.1,p.2.val.2)) :=
    continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).fst.prodMk
      (continuous_subtype_val.comp continuous_snd).snd)
  have hmap : MapsTo (fun p : ℝ × levelFibre f w r => (p.1,p.2.val.1,p.2.val.2))
      (Icc (0:ℝ) 1 ×ˢ modelChambers f I w r c j)
      {p : ℝ × (Euc ν) × (SqMat ν) | p.1 ∈ Icc 0 1 ∧ ‖p.2.1‖ = 1 ∧
        p.2.1 ∈ signChamber (activeVectors f I) (c j) ∧ p.2.2 ∈ matrixFibre p.2.1} :=
    fun p hp => ⟨hp.1,p.2.property.1.1,interior_subset hp.2,p.2.property.2⟩
  exact ContinuousOn.comp' (g := fun p : ℝ × (Euc ν) × (SqMat ν) => fibreHomotopy f I (c j) (g j) p.1 p.2.1 p.2.2)
    (f := fun p : ℝ × levelFibre f w r => (p.1,p.2.val.1,p.2.val.2))
    (hf.fibreHomotopy_continuousOn hI (hc j) (hcn j) (g j) (hg j)) hpar.continuousOn hmap
lemma Admissible.level_hits_compact {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {I : Finset ι} (hI : I.Nonempty) {w : (Euc ν)} {r : ι → ℝ} (c : κ → (Euc ν))
    (hc : ∀ j, c j ∈ commonPositiveCone f I) (hcn : ∀ j, ‖c j‖ = 1)
    (hd : Pairwise (fun i j => Disjoint (interior (signChamber (activeVectors f I) (c i)))
      (interior (signChamber (activeVectors f I) (c j)))))
    (hcover : orientedLevel f w r ⊆ ⋃ j, interior (signChamber (activeVectors f I) (c j)))
    (g : κ → (SqMat ν) → Euc ↥(Iᶜ : Finset ι)) (hg : ∀ j, Continuous (g j))
    (z : Euc ↥(Iᶜ : Finset ι)) :
    IsCompact {A : traceSphere ν | ∃ p : levelFibre f w r, balancedModel p = A ∧
      ∃ t ∈ Icc (0:ℝ) 1, levelHomotopy f I w r c g (t,p) = z} := by
  let : CompactSpace (levelFibre f w r) := isCompact_iff_compactSpace.mp (hf.levelFibre_compact w r)
  exact compact_target_hits balancedModel (balancedModel_continuous f w r)
    (levelHomotopy f I w r c g) (hf.levelHomotopy_continuousOn hI c hc hcn hd hcover g hg) z
end LevelModel
end
end

section
namespace SmithTheory
section CharacteristicCochains
variable {P : Type*} [AddCommGroup P] [Module (ZMod 2) P]
variable (d N : P →ₗ[ZMod 2] P)
def SmithCocycle : Submodule (ZMod 2) (P →ₗ[ZMod 2] ZMod 2) where
  carrier := {φ | φ.comp N = 0 ∧ φ.comp d = 0}
  zero_mem' := by simp
  add_mem' := by intro φ ψ hφ hψ; simp [LinearMap.add_comp, hφ.1, hφ.2, hψ.1, hψ.2]
  smul_mem' := by intro a φ hφ; simp [LinearMap.smul_comp, hφ.1, hφ.2]
noncomputable def smithLift (hexact : LinearMap.ker N ≤ LinearMap.range N)
    (φ : SmithCocycle d N) : P →ₗ[ZMod 2] ZMod 2 :=
  Classical.choose (exists_factor_of_vanish_norm N hexact φ.val φ.property.1)
lemma smithLift_comp_norm (hexact : LinearMap.ker N ≤ LinearMap.range N)
    (φ : SmithCocycle d N) : (smithLift d N hexact φ).comp N = φ.val :=
  Classical.choose_spec (exists_factor_of_vanish_norm N hexact φ.val φ.property.1)
noncomputable def smithNext (hd : d.comp d = 0) (hcomm : d.comp N = N.comp d)
    (hexact : LinearMap.ker N ≤ LinearMap.range N) (φ : SmithCocycle d N) :
    SmithCocycle d N :=
  ⟨(smithLift d N hexact φ).comp d, by
    constructor
    · rw [LinearMap.comp_assoc, hcomm, ← LinearMap.comp_assoc,
        smithLift_comp_norm, φ.property.2]
    · rw [LinearMap.comp_assoc, hd, LinearMap.comp_zero]⟩
noncomputable def smithCochain (hd : d.comp d = 0) (hcomm : d.comp N = N.comp d)
    (hexact : LinearMap.ker N ≤ LinearMap.range N) (φ : SmithCocycle d N) :
    ℕ → SmithCocycle d N
  | 0 => φ
  | n+1 => smithNext d N hd hcomm hexact (smithCochain hd hcomm hexact φ n)
noncomputable def smithDegree (hd : d.comp d = 0) (hcomm : d.comp N = N.comp d)
    (hexact : LinearMap.ker N ≤ LinearMap.range N) (φ : SmithCocycle d N) (n : ℕ) :
    P →ₗ[ZMod 2] ZMod 2 :=
  smithLift d N hexact (smithCochain d N hd hcomm hexact φ n)
lemma smithDegree_norm (hd : d.comp d = 0) (hcomm : d.comp N = N.comp d)
    (hexact : LinearMap.ker N ≤ LinearMap.range N) (φ : SmithCocycle d N) (n : ℕ) (c : P) :
    smithDegree d N hd hcomm hexact φ n (N c) =
      (smithCochain d N hd hcomm hexact φ n).val c :=
  LinearMap.congr_fun (smithLift_comp_norm d N hexact _) c
lemma smithCochain_succ (hd : d.comp d = 0) (hcomm : d.comp N = N.comp d)
    (hexact : LinearMap.ker N ≤ LinearMap.range N) (φ : SmithCocycle d N) (n : ℕ) (c : P) :
    (smithCochain d N hd hcomm hexact φ (n+1)).val c =
      smithDegree d N hd hcomm hexact φ n (d c) := rfl
variable {Q : Type*} [AddCommGroup Q] [Module (ZMod 2) Q]
lemma smithDegree_natural
    (hd : d.comp d = 0) (hcomm : d.comp N = N.comp d)
    (hexact : LinearMap.ker N ≤ LinearMap.range N) (φ : SmithCocycle d N)
    (d' N' : Q →ₗ[ZMod 2] Q) (hd' : d'.comp d' = 0) (hcomm' : d'.comp N' = N'.comp d')
    (hexact' : LinearMap.ker N' ≤ LinearMap.range N') (φ' : SmithCocycle d' N')
    (T : P →ₗ[ZMod 2] Q) (hTd : d'.comp T = T.comp d) (hTN : N'.comp T = T.comp N)
    (hTφ : φ'.val.comp T = φ.val) (n : ℕ) (c : P) (hNc : N c = 0) (hdc : d c = 0) :
    smithDegree d' N' hd' hcomm' hexact' φ' n (T c) =
      smithDegree d N hd hcomm hexact φ n c := by
  induction n generalizing c with
  | zero =>
    obtain ⟨x,hx⟩ := hexact hNc
    rw [← hx, ← LinearMap.comp_apply T N, ← hTN, LinearMap.comp_apply,
      smithDegree_norm, smithDegree_norm]
    exact LinearMap.congr_fun hTφ x
  | succ n ih =>
    obtain ⟨x,hx⟩ := hexact hNc
    rw [← hx, ← LinearMap.comp_apply T N, ← hTN, LinearMap.comp_apply,
      smithDegree_norm, smithDegree_norm, smithCochain_succ, smithCochain_succ,
      ← LinearMap.comp_apply d' T, hTd, LinearMap.comp_apply]
    apply ih
    · rw [← LinearMap.comp_apply N d, ← hcomm, LinearMap.comp_apply, hx, hdc]
    · exact LinearMap.congr_fun hd x
end CharacteristicCochains
end SmithTheory
end

section
namespace SimplicialChains
open Finset
open BorsukNine.SmithTheory
section CharacteristicDegree
variable {V : Type*} [DecidableEq V]
variable (K : PreComplex V) (e : V ≃ V)
variable (he : ∀ s, s ∈ K ↔ s.image e ∈ K) (hi : Function.Involutive e)
variable (hfree : ∀ s ∈ K, s.image e ≠ s)
noncomputable def characteristicAugmentation : SmithCocycle (boundary K) (normMap K e) :=
  ⟨augmentation K, augmentation_normMap K e (fun s hs => (he s).mp hs),
    augmentation_boundary K⟩
include he hi hfree in
lemma normMap_exact : LinearMap.ker (normMap K e) ≤ LinearMap.range (normMap K e) := by
  rw [normMap_eq K e he]
  exact involutionNorm_exact _ (faceEquiv_involutive K e he hi)
    (faceEquiv_free K e he hfree)
noncomputable def characteristicDegree (n : ℕ) : Chain K →ₗ[F₂] F₂ :=
  smithDegree (boundary K) (normMap K e) (boundary_sq K)
    (boundary_normMap K e (fun s hs => (he s).mp hs)) (normMap_exact K e he hi hfree)
    (characteristicAugmentation K e he) n
end CharacteristicDegree
end SimplicialChains
namespace SimplicialChains
open Finset BorsukNine.SmithTheory
section NaturalDegree
variable {V W : Type*} [DecidableEq V] [DecidableEq W]
lemma characteristicDegree_natural
    (K : PreComplex V) (e : V ≃ V)
    (he : ∀ s, s ∈ K ↔ s.image e ∈ K) (hi : Function.Involutive e)
    (hfree : ∀ s ∈ K, s.image e ≠ s)
    (L : PreComplex W) (d : W ≃ W)
    (hd : ∀ s, s ∈ L ↔ s.image d ∈ L) (hdi : Function.Involutive d)
    (hdfree : ∀ s ∈ L, s.image d ≠ s)
    (T : Chain K →ₗ[F₂] Chain L)
    (hTbd : (boundary L).comp T = T.comp (boundary K))
    (hTN : (normMap L d).comp T = T.comp (normMap K e))
    (hTa : (augmentation L).comp T = augmentation K)
    (n : ℕ) (c : Chain K) (hcN : normMap K e c = 0) (hcb : boundary K c = 0) :
    characteristicDegree L d hd hdi hdfree n (T c) =
      characteristicDegree K e he hi hfree n c := by
  exact smithDegree_natural (boundary K) (normMap K e) (boundary_sq K)
    (boundary_normMap K e (fun s hs => (he s).mp hs)) (normMap_exact K e he hi hfree)
    (characteristicAugmentation K e he) (boundary L) (normMap L d) (boundary_sq L)
    (boundary_normMap L d (fun s hs => (hd s).mp hs)) (normMap_exact L d hd hdi hdfree)
    (characteristicAugmentation L d hd) T hTbd hTN hTa n c hcN hcb
end NaturalDegree
noncomputable def crossFundamental (n : ℕ) : Chain (cross n) :=
  normMap (cross n) flip (crossTower n (n-1))
lemma crossFundamental_norm (n : ℕ) : normMap (cross n) flip (crossFundamental n) = 0 :=
  LinearMap.congr_fun (normMap_sq (cross n) flip (cross_flip n) flip_involutive) _
lemma crossFundamental_boundary (n : ℕ) (hn : 0 < n) :
    boundary (cross n) (crossFundamental n) = 0 :=
  crossTower_norm_boundary n (n-1) (by omega)
lemma crossFundamental_degree (n : ℕ) (hn : 0 < n) :
    crossFundamental n ∈ degreeChains (cross n) n := by
  have h := normMap_degree (cross n) flip (cross_flip_forward n) (n-1+1)
    (crossTower_degree n (n-1))
  change normMap (cross n) flip (crossTower n (n-1)) ∈
    degreeChains (cross n) (n-1+1) at h
  simpa only [crossFundamental, Nat.sub_add_cancel (by omega : 1 ≤ n)] using h
lemma characteristicCochain_crossTower (n i : ℕ) (hi : i < n) :
    (smithCochain (boundary (cross n)) (normMap (cross n) flip) (boundary_sq (cross n))
      (boundary_normMap (cross n) flip (cross_flip_forward n))
      (normMap_exact (cross n) flip (cross_flip n) flip_involutive (cross_free n))
      (characteristicAugmentation (cross n) flip (cross_flip n)) i).val
        (crossTower n i) = 1 := by
  induction i with
  | zero => exact crossTower_augmentation n (by omega)
  | succ i ih =>
    rw [smithCochain_succ, crossTower_boundary n i hi, smithDegree_norm]
    exact ih (by omega)
lemma characteristicDegree_crossFundamental (n : ℕ) (hn : 0 < n) :
    characteristicDegree (cross n) flip (cross_flip n) flip_involutive (cross_free n)
      (n-1) (crossFundamental n) = 1 := by
  unfold characteristicDegree crossFundamental
  rw [smithDegree_norm]
  exact characteristicCochain_crossTower n (n-1) (by omega)
lemma cross_equivariant_degree_one (n : ℕ) (hn : 0 < n)
    (T : Chain (cross n) →ₗ[F₂] Chain (cross n))
    (hTbd : (boundary (cross n)).comp T = T.comp (boundary (cross n)))
    (hTN : (normMap (cross n) flip).comp T = T.comp (normMap (cross n) flip))
    (hTa : (augmentation (cross n)).comp T = augmentation (cross n)) :
    characteristicDegree (cross n) flip (cross_flip n) flip_involutive (cross_free n)
      (n-1) (T (crossFundamental n)) = 1 := by
  rw [characteristicDegree_natural (cross n) flip (cross_flip n) flip_involutive
    (cross_free n) (cross n) flip (cross_flip n) flip_involutive (cross_free n)
    T hTbd hTN hTa (n-1) (crossFundamental n) (crossFundamental_norm n)
    (crossFundamental_boundary n hn), characteristicDegree_crossFundamental n hn]
end SimplicialChains
end

section
namespace SimplicialChains
open Finset
section Coefficients
variable {V : Type*} [DecidableEq V] (K : PreComplex V)
omit [DecidableEq V] in
lemma degreeChains_card_of_ne_zero (n : ℕ) {c : Chain K}
    (hc : c ∈ degreeChains K n) (s : {s : Finset V // s ∈ K}) (hs : c s ≠ 0) :
    s.val.card = n := by
  by_contra h
  exact hs ((Finsupp.mem_supported' F₂ c).mp hc s h)
lemma simplex_coeff (s : Finset V) (t : {t : Finset V // t ∈ K}) :
    simplex K s t = if s = t.val then 1 else 0 := by
  classical
  by_cases hs : s ∈ K
  · rw [simplex_of_mem K hs]
    simp only [Finsupp.single_apply]
    congr 1
    exact propext Subtype.ext_iff
  · have hst : s ≠ t.val := fun h => hs (h ▸ t.property)
    simp [simplex, hs, hst]
lemma boundary_simplex_coeff {s : Finset V} (hs : s ∈ K)
    (t : {t : Finset V // t ∈ K}) (hcard : t.val.card + 1 = s.card) :
    boundary K (simplex K s) t = if t.val ⊆ s then 1 else 0 := by
  classical
  rw [boundary_simplex K hs, Finsupp.finsetSum_apply]
  simp_rw [simplex_coeff]
  by_cases hts : t.val ⊆ s
  · rw [if_pos hts]
    obtain ⟨a,ha,rfl⟩ := Finset.exists_eq_insert_iff.mpr ⟨hts,hcard⟩
    rw [Finset.sum_insert ha, Finset.erase_insert ha, if_pos rfl]
    have hz : ∀ b ∈ t.val, (if (insert a t.val).erase b = t.val then (1:F₂) else 0) = 0 := by
      intro b hb
      rw [if_neg]
      intro he
      have hab : a ≠ b := fun h => ha (h ▸ hb)
      have hh : a ∈ (insert a t.val).erase b := Finset.mem_erase.mpr
        ⟨hab, Finset.mem_insert_self _ _⟩
      exact ha (he ▸ hh)
    rw [Finset.sum_eq_zero hz, add_zero]
  · rw [if_neg hts]
    apply Finset.sum_eq_zero
    intro a ha
    rw [if_neg]
    intro he
    exact hts (he ▸ Finset.erase_subset a s)
end Coefficients
noncomputable def crossFacet (n : ℕ) (b : Fin n → Bool) : Finset SignedVertex :=
  Finset.univ.image (fun i : Fin n => (i.val,b i))
lemma mem_crossFacet (n : ℕ) (b : Fin n → Bool) (v : SignedVertex) :
    v ∈ crossFacet n b ↔ ∃ i : Fin n, v = (i.val,b i) := by
  classical
  simp only [crossFacet, Finset.mem_image, Finset.mem_univ, true_and]
  exact exists_congr (fun _ => eq_comm)
lemma crossFacet_card (n : ℕ) (b : Fin n → Bool) : (crossFacet n b).card = n := by
  classical
  rw [crossFacet, Finset.card_image_iff.mpr, Finset.card_univ, Fintype.card_fin]
  intro i _ j _ hij
  exact Fin.ext (congrArg Prod.fst hij)
lemma crossFacet_mem (n : ℕ) (hn : 0 < n) (b : Fin n → Bool) : crossFacet n b ∈ cross n := by
  classical
  refine ⟨?_,?_,?_⟩
  · exact Finset.card_pos.mp (by rw [crossFacet_card]; exact hn)
  · intro v hv
    obtain ⟨i,rfl⟩ := (mem_crossFacet n b v).mp hv
    exact i.isLt
  · intro v hv w hw he
    obtain ⟨i,rfl⟩ := (mem_crossFacet n b v).mp hv
    obtain ⟨j,rfl⟩ := (mem_crossFacet n b w).mp hw
    have hij : i = j := Fin.ext he
    rw [hij]
lemma cross_top_exists_signs (n : ℕ) (s : Finset SignedVertex) (hs : s ∈ cross n)
    (hcard : s.card = n) : ∃ b : Fin n → Bool, s = crossFacet n b := by
  classical
  have hproj : s.image Prod.fst = Finset.range n := by
    apply Finset.eq_of_subset_of_card_le
    · intro i hi
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hi
      exact Finset.mem_range.mpr (hs.2.1 v hv)
    · rw [Finset.card_image_iff.mpr hs.2.2, Finset.card_range, hcard]
  have hex (i : Fin n) : ∃ v ∈ s, v.1 = i.val := by
    apply Finset.mem_image.mp
    rw [hproj]
    exact Finset.mem_range.mpr i.isLt
  choose v hv hvi using hex
  refine ⟨fun i => (v i).2, ?_⟩
  ext w
  constructor
  · intro hw
    let i : Fin n := ⟨w.1,hs.2.1 w hw⟩
    have he : w = v i := hs.2.2 hw (hv i) (hvi i).symm
    apply (mem_crossFacet n _ w).mpr
    refine ⟨i, ?_⟩
    apply Prod.ext
    · rfl
    · change w.2 = (v i).2
      exact congrArg Prod.snd he
  · intro hw
    obtain ⟨i,rfl⟩ := (mem_crossFacet n _ w).mp hw
    have he : (i.val,(v i).2) = v i := Prod.ext (hvi i).symm rfl
    rw [he]
    exact hv i
end SimplicialChains
end

section
namespace SimplicialChains
open Finset
noncomputable def flipAt {n : ℕ} (b : Fin n → Bool) (i : Fin n) : Fin n → Bool :=
  Function.update b i (! b i)
lemma flipAt_ne {n : ℕ} (b : Fin n → Bool) (i : Fin n) : flipAt b i ≠ b := by
  intro he
  have hi := congrFun he i
  simp [flipAt] at hi
lemma crossFacet_injective (n : ℕ) : Function.Injective (crossFacet n) := by
  intro b c he
  funext i
  have hi : (i.val,b i) ∈ crossFacet n c := he ▸ (mem_crossFacet n b _).mpr ⟨i,rfl⟩
  obtain ⟨j,hj⟩ := (mem_crossFacet n c _).mp hi
  have hij : i = j := Fin.ext (congrArg Prod.fst hj)
  simpa only [← hij] using congrArg Prod.snd hj
noncomputable def crossRidge (n : ℕ) (b : Fin n → Bool) (i : Fin n) : Finset SignedVertex :=
  (crossFacet n b).erase (i.val,b i)
lemma crossRidge_card (n : ℕ) (b : Fin n → Bool) (i : Fin n) :
    (crossRidge n b i).card = n-1 := by
  rw [crossRidge, Finset.card_erase_of_mem ((mem_crossFacet n b _).mpr ⟨i,rfl⟩),
    crossFacet_card]
lemma crossRidge_mem (n : ℕ) (hn : 1 < n) (b : Fin n → Bool) (i : Fin n) :
    crossRidge n b i ∈ cross n := by
  apply ((cross n).isRelLowerSet_faces (crossFacet_mem n (by omega) b)).2
    (Finset.erase_subset _ _)
  apply Finset.card_pos.mp
  change 0 < (crossRidge n b i).card
  rw [crossRidge_card]
  omega
lemma mem_crossRidge (n : ℕ) (b : Fin n → Bool) (i : Fin n) (v : SignedVertex) :
    v ∈ crossRidge n b i ↔ ∃ j : Fin n, j ≠ i ∧ v = (j.val,b j) := by
  classical
  simp only [crossRidge, Finset.mem_erase, mem_crossFacet]
  constructor
  · rintro ⟨hne,j,rfl⟩
    exact ⟨j, fun h => hne (h ▸ rfl), rfl⟩
  · rintro ⟨j,hji,rfl⟩
    refine ⟨?_,j,rfl⟩
    exact fun h => hji (Fin.ext (congrArg Prod.fst h))
lemma crossRidge_subset_iff (n : ℕ) (b c : Fin n → Bool) (i : Fin n) :
    crossRidge n b i ⊆ crossFacet n c ↔ ∀ j : Fin n, j ≠ i → c j = b j := by
  constructor
  · intro h j hji
    have hj := h ((mem_crossRidge n b i _).mpr ⟨j,hji,rfl⟩)
    obtain ⟨k,hk⟩ := (mem_crossFacet n c _).mp hj
    have hjk : j = k := Fin.ext (congrArg Prod.fst hk)
    simpa only [← hjk] using (congrArg Prod.snd hk).symm
  · intro h v hv
    obtain ⟨j,hji,rfl⟩ := (mem_crossRidge n b i v).mp hv
    exact (mem_crossFacet n c _).mpr ⟨j, by rw [h j hji]⟩
lemma crossRidge_parents (n : ℕ) (b c : Fin n → Bool) (i : Fin n) :
    crossRidge n b i ⊆ crossFacet n c ↔ c = b ∨ c = flipAt b i := by
  rw [crossRidge_subset_iff]
  constructor
  · intro h
    by_cases hi : c i = b i
    · left
      funext j
      by_cases hj : j = i
      · subst j; exact hi
      · exact h j hj
    · right
      have hb : c i = !b i := by cases hci : c i <;> cases hbi : b i <;> simp_all
      funext j
      by_cases hj : j = i
      · subst j; simpa [flipAt] using hb
      · simpa [flipAt, hj] using h j hj
  · rintro (rfl | rfl) j hj
    · rfl
    · simp [flipAt, hj]
lemma boundary_ridge_coefficient (n : ℕ) (hn : 1 < n) (b : Fin n → Bool) (i : Fin n)
    (c : Chain (cross n)) (hc : c ∈ degreeChains (cross n) n) :
    boundary (cross n) c ⟨crossRidge n b i,crossRidge_mem n hn b i⟩ =
      c ⟨crossFacet n b,crossFacet_mem n (by omega) b⟩ +
      c ⟨crossFacet n (flipAt b i),crossFacet_mem n (by omega) (flipAt b i)⟩ := by
  classical
  let r : {s : Finset SignedVertex // s ∈ cross n} :=
    ⟨crossRidge n b i,crossRidge_mem n hn b i⟩
  let s : {s : Finset SignedVertex // s ∈ cross n} :=
    ⟨crossFacet n b,crossFacet_mem n (by omega) b⟩
  let t : {s : Finset SignedVertex // s ∈ cross n} :=
    ⟨crossFacet n (flipAt b i),crossFacet_mem n (by omega) (flipAt b i)⟩
  let α : Chain (cross n) →ₗ[F₂] F₂ := Finsupp.lapply s + Finsupp.lapply t
  change ((Finsupp.lapply r).comp (boundary (cross n))) c = α c
  apply linearMap_eq_of_support
  intro a ha
  have hcard : a.val.card = n := degreeChains_card_of_ne_zero (cross n) n hc a (Finsupp.mem_support_iff.mp ha)
  obtain ⟨d,hd⟩ := cross_top_exists_signs n a.val a.property hcard
  have hcoeff := boundary_simplex_coeff (cross n) a.property r (by
    change (crossRidge n b i).card + 1 = a.val.card
    rw [crossRidge_card, hcard]
    omega)
  simp only [α, LinearMap.comp_apply, Finsupp.lapply_apply, LinearMap.add_apply]
  rw [hcoeff, simplex_coeff, simplex_coeff]
  change (if crossRidge n b i ⊆ a.val then (1:F₂) else 0) =
    (if a.val = crossFacet n b then 1 else 0) +
    (if a.val = crossFacet n (flipAt b i) then 1 else 0)
  rw [hd]
  simp only [crossRidge_parents, crossFacet_injective n |>.eq_iff]
  have hne : flipAt b i ≠ b := flipAt_ne b i
  by_cases hb : d = b <;> by_cases ht : d = flipAt b i <;> simp_all
lemma cross_cycle_adjacent_coeff (n : ℕ) (hn : 1 < n) (b : Fin n → Bool) (i : Fin n)
    (c : Chain (cross n)) (hc : c ∈ degreeChains (cross n) n) (hd : boundary (cross n) c = 0) :
    c ⟨crossFacet n b,crossFacet_mem n (by omega) b⟩ =
      c ⟨crossFacet n (flipAt b i),crossFacet_mem n (by omega) (flipAt b i)⟩ := by
  have h := boundary_ridge_coefficient n hn b i c hc
  rw [hd, Finsupp.zero_apply] at h
  have he := eq_neg_of_add_eq_zero_left h.symm
  simpa only [CharTwo.neg_eq] using he
end SimplicialChains
end

section
namespace SimplicialChains
open Finset
lemma bool_cube_constant {n : ℕ} {A : Type*} (p : (Fin n → Bool) → A)
    (hp : ∀ b i, p b = p (flipAt b i)) (b c : Fin n → Bool) : p b = p c := by
  classical
  suffices hs : ∀ (s : Finset (Fin n)) (b c : Fin n → Bool),
      (∀ i ∉ s, b i = c i) → p b = p c by
    exact hs Finset.univ b c (by simp)
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro b c h
    have he : b = c := funext (fun i => h i (by simp))
    rw [he]
  | @insert i s _ ih =>
    intro b c h
    let d := Function.update b i (c i)
    have hd : ∀ j ∉ s, d j = c j := by
      intro j hj
      by_cases he : j = i
      · subst j; simp [d]
      · simpa [d, he] using h j (by simp [hj, he])
    have he : p b = p d := by
      by_cases hb : b i = c i
      · have hbd : b = d := by
          funext j
          by_cases hji : j = i
          · subst j; simpa [d] using hb
          · simp [d, hji]
        rw [hbd]
      · have hflip : c i = !b i := by
          cases hbi : b i <;> cases hci : c i <;> simp_all
        have hdflip : d = flipAt b i := by simp only [d, flipAt, hflip]
        rw [hdflip]
        exact hp b i
    exact he.trans (ih d c hd)
lemma cross_cycle_coeff_constant (n : ℕ) (hn : 1 < n)
    (c : Chain (cross n)) (hc : c ∈ degreeChains (cross n) n)
    (hd : boundary (cross n) c = 0) (b d : Fin n → Bool) :
    c ⟨crossFacet n b,crossFacet_mem n (by omega) b⟩ =
      c ⟨crossFacet n d,crossFacet_mem n (by omega) d⟩ :=
  bool_cube_constant _ (fun b i => cross_cycle_adjacent_coeff n hn b i c hc hd) b d
lemma crossFundamental_coeff (n : ℕ) (hn : 1 < n) (b : Fin n → Bool) :
    crossFundamental n ⟨crossFacet n b,crossFacet_mem n (by omega) b⟩ = 1 := by
  have hnonzero : crossFundamental n ≠ 0 := by
    intro h
    have hd := characteristicDegree_crossFundamental n (by omega)
    rw [h, map_zero] at hd
    exact zero_ne_one hd
  obtain ⟨s,hs⟩ : ∃ s, crossFundamental n s ≠ 0 := by
    by_contra h
    push Not at h
    exact hnonzero (Finsupp.ext h)
  have hcard : s.val.card = n := degreeChains_card_of_ne_zero (cross n) n
    (crossFundamental_degree n (by omega)) s hs
  obtain ⟨d,hd⟩ := cross_top_exists_signs n s.val s.property hcard
  have hsd : s = ⟨crossFacet n d,crossFacet_mem n (by omega) d⟩ := Subtype.ext hd
  rw [hsd] at hs
  have hconst := cross_cycle_coeff_constant n hn (crossFundamental n)
    (crossFundamental_degree n (by omega)) (crossFundamental_boundary n (by omega)) b d
  rw [hconst]
  have h₂ : ∀ x : F₂, x = 0 ∨ x = 1 := by decide
  exact (h₂ _).resolve_left hs
lemma cross_top_cycle_eq (n : ℕ) (hn : 1 < n)
    (c : Chain (cross n)) (hc : c ∈ degreeChains (cross n) n)
    (hd : boundary (cross n) c = 0) (b : Fin n → Bool) :
    c = c ⟨crossFacet n b,crossFacet_mem n (by omega) b⟩ • crossFundamental n := by
  classical
  ext s
  rw [Finsupp.smul_apply, smul_eq_mul]
  by_cases hcard : s.val.card = n
  · obtain ⟨d,hd'⟩ := cross_top_exists_signs n s.val s.property hcard
    have hsd : s = ⟨crossFacet n d,crossFacet_mem n (by omega) d⟩ := Subtype.ext hd'
    rw [hsd, crossFundamental_coeff n hn d, mul_one]
    exact cross_cycle_coeff_constant n hn c hc hd d b
  · have hz : c s = 0 := by
      by_contra hs
      exact hcard (degreeChains_card_of_ne_zero (cross n) n hc s hs)
    have hz' : crossFundamental n s = 0 := by
      by_contra hs
      exact hcard (degreeChains_card_of_ne_zero (cross n) n
        (crossFundamental_degree n (by omega)) s hs)
    rw [hz, hz', mul_zero]
lemma cross_characteristicDegree_eq_coeff (n : ℕ) (hn : 1 < n)
    (c : Chain (cross n)) (hc : c ∈ degreeChains (cross n) n)
    (hd : boundary (cross n) c = 0) (b : Fin n → Bool) :
    characteristicDegree (cross n) flip (cross_flip n) flip_involutive (cross_free n)
      (n-1) c = c ⟨crossFacet n b,crossFacet_mem n (by omega) b⟩ := by
  conv_lhs => rw [cross_top_cycle_eq n hn c hc hd b]
  rw [map_smul, characteristicDegree_crossFundamental n (by omega), smul_eq_mul, mul_one]
end SimplicialChains
end

section
namespace SimplicialChains
open Finset
variable {V W : Type*} [DecidableEq V] [DecidableEq W]
omit [DecidableEq W] in
lemma double_erase_sum_fun (L : PreComplex W) (H : Finset V → Chain L)
    (s : Finset V) : (∑ a ∈ s, ∑ b ∈ s.erase a, H ((s.erase a).erase b)) = 0 := by
  classical
  let g (p : V × V) : Chain L := if p.1 = p.2 then 0 else H ((s.erase p.1).erase p.2)
  have hg : (∑ a ∈ s, ∑ b ∈ s.erase a, H ((s.erase a).erase b)) =
      ∑ p ∈ s ×ˢ s, g p := by
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro a _
    rw [← Finset.filter_ne, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hab : a = b <;> simp [g, hab, Finset.filter_ne]
  rw [hg]
  apply Finset.sum_involution (fun p _ => p.swap)
  · intro p _
    dsimp [g]
    by_cases he : p.1 = p.2
    · simp [he]
    · simp only [he, ite_false, Ne.symm he, Finset.erase_right_comm]
      exact chain_add_self L _
  · intro p _ hg he
    have h : p.1 = p.2 := congrArg Prod.snd he
    exact hg (by simp [g, h])
  · intro p _; exact Prod.swap_swap p
  · intro p hp; exact Finset.mem_product.mpr (And.symm (Finset.mem_product.mp hp))
omit [DecidableEq V] in
lemma support_mapSimplex (L : PreComplex W) (f : V → W)
    (s : Finset V) {t : {t : Finset W // t ∈ L}}
    (ht : t ∈ (mapSimplex L f s).support) : t.val = s.image f := by
  unfold mapSimplex at ht
  split_ifs at ht
  · exact (mem_support_simplex L _ t).mp ht
  · simp at ht
omit [DecidableEq V] in
lemma mapSimplex_degree (L : PreComplex W) (f : V → W) (s : Finset V) :
    mapSimplex L f s ∈ degreeChains L s.card := by
  unfold mapSimplex
  split_ifs with h
  · rw [← h]; exact simplex_mem_degree_all L _
  · exact Submodule.zero_mem _
lemma mapSimplex_boundary (L : PreComplex W) (f : V → W)
    {s : Finset V} (hs : s.image f ∈ L) :
    boundary L (mapSimplex L f s) = ∑ a ∈ s, mapSimplex L f (s.erase a) := by
  by_cases hinj : Set.InjOn f s
  · rw [mapSimplex, if_pos (Finset.card_image_iff.mpr hinj), boundary_simplex L hs,
      Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro a ha
      rw [mapSimplex, if_pos (Finset.card_image_iff.mpr (hinj.mono (Finset.erase_subset a s))),
        image_erase_of_injOn f s hinj ha]
    · exact hinj
  · rw [mapSimplex, if_neg (mt Finset.card_image_iff.mp hinj), map_zero,
      mapSimplex_boundary_degenerate L f s hinj]
omit [DecidableEq V] in
lemma mapSimplex_augmentation (L : PreComplex W) (f : V → W)
    {s : Finset V} (hs : s.image f ∈ L) :
    augmentation L (mapSimplex L f s) = if s.card = 1 then 1 else 0 := by
  by_cases hinj : (s.image f).card = s.card
  · rw [mapSimplex, if_pos hinj, augmentation_simplex L hs, hinj]
  · have hc : s.card ≠ 1 := by
      intro h
      obtain ⟨a,rfl⟩ := Finset.card_eq_one.mp h
      simp at hinj
    simp [mapSimplex, hinj, hc]
noncomputable def contigSimplex (L : PreComplex W) (f g : V → W)
    (s : Finset V) : Chain L :=
  if hs : s.Nonempty then
    cone L (f hs.choose) (mapSimplex L f s + mapSimplex L g s +
      ∑ a ∈ s.attach, contigSimplex L f g (s.erase a.val))
  else 0
termination_by s.card
decreasing_by exact Finset.card_erase_lt_of_mem a.property
@[simp] lemma contigSimplex_empty (L : PreComplex W) (f g : V → W) :
    contigSimplex L f g ∅ = 0 := by rw [contigSimplex]; simp
lemma contigSimplex_nonempty (L : PreComplex W) (f g : V → W)
    {s : Finset V} (hs : s.Nonempty) :
    contigSimplex L f g s = cone L (f hs.choose)
      (mapSimplex L f s + mapSimplex L g s + ∑ a ∈ s, contigSimplex L f g (s.erase a)) := by
  rw [contigSimplex, dif_pos hs]
  exact congrArg (fun z => cone L (f hs.choose) (mapSimplex L f s + mapSimplex L g s + z))
    (Finset.sum_attach s (fun a : V => contigSimplex L f g (s.erase a)))
lemma contigSimplex_carrier (L : PreComplex W) (f g : V → W)
    (s : Finset V) {t : {t : Finset W // t ∈ L}}
    (ht : t ∈ (contigSimplex L f g s).support) : t.val ⊆ s.image f ∪ s.image g := by
  induction s using Finset.strongInductionOn generalizing t with
  | _ s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simp at ht
    rw [contigSimplex_nonempty L f g hs] at ht
    obtain ⟨u,hu,_,htu⟩ := support_cone L _ _ ht
    rw [htu]
    apply Finset.insert_subset
    · exact Finset.mem_union_left _ (Finset.mem_image_of_mem f hs.choose_spec)
    have hsub : ∀ a ∈ s, (s.erase a).image f ∪ (s.erase a).image g ⊆ s.image f ∪ s.image g := by
      intro a _
      exact Finset.union_subset_union (Finset.image_subset_image (Finset.erase_subset a s))
        (Finset.image_subset_image (Finset.erase_subset a s))
    rcases Finset.mem_union.mp (Finsupp.support_add hu) with hu | hu
    · rcases Finset.mem_union.mp (Finsupp.support_add hu) with hf | hg
      · rw [support_mapSimplex L f s hf]; exact Finset.subset_union_left
      · rw [support_mapSimplex L g s hg]; exact Finset.subset_union_right
    · obtain ⟨a,ha,hua⟩ := support_sum_chains L s _ hu
      exact (ih (s.erase a) (Finset.erase_ssubset ha) hua).trans (hsub a ha)
lemma contigSimplex_degree (L : PreComplex W) (f g : V → W)
    (s : Finset V) : contigSimplex L f g s ∈ degreeChains L (s.card+1) := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hs
    · rw [contigSimplex_empty]; exact Submodule.zero_mem _
    rw [contigSimplex_nonempty L f g hs]
    apply cone_degree L _ s.card
    apply Submodule.add_mem _
    · exact Submodule.add_mem _ (mapSimplex_degree L f s) (mapSimplex_degree L g s)
    · apply Submodule.sum_mem
      intro a ha
      have h := ih (s.erase a) (Finset.erase_ssubset ha)
      simpa only [Finset.card_erase_of_mem ha, Nat.sub_add_cancel hs.card_pos] using h
lemma contigSimplex_augmentation (L : PreComplex W) (f g : V → W)
    (s : Finset V) : augmentation L (contigSimplex L f g s) = 0 := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  exact augmentation_eq_zero_of_degree L (s.card+1) (by have := hs.card_pos; omega)
    (contigSimplex_degree L f g s)
end SimplicialChains
end

section
namespace SimplicialChains
open Finset
variable {V W : Type*} [DecidableEq V] [DecidableEq W]
lemma contigSimplex_boundary (L : PreComplex W) (f g : V → W)
    {s : Finset V} (hs : s.image f ∪ s.image g ∈ L) :
    boundary L (contigSimplex L f g s) =
      mapSimplex L f s + mapSimplex L g s + ∑ a ∈ s, contigSimplex L f g (s.erase a) := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    have hn : s.Nonempty := by
      by_contra h
      have he := Finset.not_nonempty_iff_eq_empty.mp h
      have hs' : (∅ : Finset W) ∈ L := by simpa [he] using hs
      simpa using (L.isRelLowerSet_faces hs').1
    have hf : s.image f ∈ L := (L.isRelLowerSet_faces hs).2 Finset.subset_union_left (hn.image f)
    have hg : s.image g ∈ L := (L.isRelLowerSet_faces hs).2 Finset.subset_union_right (hn.image g)
    have hb : f hn.choose ∈ s.image f ∪ s.image g :=
      Finset.mem_union_left _ (Finset.mem_image_of_mem f hn.choose_spec)
    let z := mapSimplex L f s + mapSimplex L g s + ∑ a ∈ s, contigSimplex L f g (s.erase a)
    have hi (a : V) (ha : a ∈ s) : boundary L (contigSimplex L f g (s.erase a)) =
        mapSimplex L f (s.erase a) + mapSimplex L g (s.erase a) +
          ∑ b ∈ s.erase a, contigSimplex L f g ((s.erase a).erase b) := by
      rcases (s.erase a).eq_empty_or_nonempty with he | hne
      · simp [he, mapSimplex]
      · apply ih (s.erase a) (Finset.erase_ssubset ha)
        apply (L.isRelLowerSet_faces hs).2
        · exact Finset.union_subset_union (Finset.image_subset_image (Finset.erase_subset a s))
            (Finset.image_subset_image (Finset.erase_subset a s))
        · exact (hne.image f).mono Finset.subset_union_left
    have hzbd : boundary L z = 0 := by
      simp only [z, map_add, map_sum, mapSimplex_boundary L f hf, mapSimplex_boundary L g hg]
      rw [Finset.sum_congr rfl hi]
      simp only [Finset.sum_add_distrib]
      rw [double_erase_sum_fun, add_zero]
      exact chain_add_self L _
    have hzaug : augmentation L z = 0 := by
      simp only [z, map_add, map_sum, mapSimplex_augmentation L f hf,
        mapSimplex_augmentation L g hg, contigSimplex_augmentation, Finset.sum_const_zero, add_zero]
      exact CharTwo.add_self_eq_zero _
    have hzcone : ∀ t ∈ z.support, insert (f hn.choose) t.val ∈ L := by
      intro t ht
      apply (L.isRelLowerSet_faces hs).2 _ (Finset.insert_nonempty _ _)
      apply Finset.insert_subset hb
      rcases Finset.mem_union.mp (Finsupp.support_add ht) with ht | ht
      · rcases Finset.mem_union.mp (Finsupp.support_add ht) with htf | htg
        · rw [support_mapSimplex L f s htf]; exact Finset.subset_union_left
        · rw [support_mapSimplex L g s htg]; exact Finset.subset_union_right
      · obtain ⟨a,ha,hta⟩ := support_sum_chains L s _ ht
        exact (contigSimplex_carrier L f g (s.erase a) hta).trans
          (Finset.union_subset_union (Finset.image_subset_image (Finset.erase_subset a s))
            (Finset.image_subset_image (Finset.erase_subset a s)))
    rw [contigSimplex_nonempty L f g hn]
    change boundary L (cone L (f hn.choose) z) = z
    rw [cone_boundary L _ z hzcone, hzbd, hzaug, map_zero, zero_smul, add_zero, add_zero]
noncomputable def contigMap (K : PreComplex V)
    (L : PreComplex W) (f g : V → W) : Chain K →ₗ[F₂] Chain L :=
  Finsupp.linearCombination F₂ (fun s => contigSimplex L f g s.val)
lemma contigMap_simplex (K : PreComplex V)
    (L : PreComplex W) (f g : V → W) {s : Finset V} (hs : s ∈ K) :
    contigMap K L f g (simplex K s) = contigSimplex L f g s := by
  simp [simplex_of_mem K hs, contigMap, Finsupp.linearCombination_single]
lemma contigMap_simplex_subset (K : PreComplex V)
    (L : PreComplex W) (f g : V → W) {s t : Finset V}
    (ht : t ∈ K) (hs : s ⊆ t) :
    contigMap K L f g (simplex K s) = contigSimplex L f g s := by
  rcases s.eq_empty_or_nonempty with rfl | hn
  · simp
  · exact contigMap_simplex K L f g ((K.isRelLowerSet_faces ht).2 hs hn)
lemma contigMap_degree (K : PreComplex V)
    (L : PreComplex W) (f g : V → W) (d : ℕ) :
    degreeChains K d ≤ (degreeChains L (d+1)).comap (contigMap K L f g) := by
  apply grade_map K L _ d (d+1)
  intro s hs hd
  rw [contigMap_simplex K L f g hs, ← hd]
  exact contigSimplex_degree L f g s
lemma contigMap_boundary_of_support (K : PreComplex V)
    (L : PreComplex W) (f g : V → W) (c : Chain K)
    (hc : ∀ s ∈ c.support, s.val.image f ∪ s.val.image g ∈ L) :
    boundary L (contigMap K L f g c) = mapChains K L f c + mapChains K L g c +
      contigMap K L f g (boundary K c) := by
  let A : Chain K →ₗ[F₂] Chain L :=
    mapChains K L f + mapChains K L g + (contigMap K L f g).comp (boundary K)
  change ((boundary L).comp (contigMap K L f g)) c = A c
  apply linearMap_eq_of_support
  intro s hs
  simp only [LinearMap.comp_apply, A, LinearMap.add_apply]
  rw [contigMap_simplex K L f g s.property, contigSimplex_boundary L f g (hc s hs),
    mapChains_simplex K L f s.property, mapChains_simplex K L g s.property,
    boundary_simplex K s.property, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  exact (contigMap_simplex_subset K L f g s.property (Finset.erase_subset a s.val)).symm
lemma contig_maps_agree_top (K : PreComplex V)
    (L : PreComplex W) (f g : V → W) (d : ℕ) (c : Chain K)
    (hc : c ∈ degreeChains K d) (hbd : boundary K c = 0)
    (hfg : ∀ s ∈ c.support, s.val.image f ∪ s.val.image g ∈ L)
    (hL : ∀ s ∈ L, s.card ≤ d) : mapChains K L f c = mapChains K L g c := by
  have hh : contigMap K L f g c = 0 := by
    have ht := contigMap_degree K L f g d hc
    rw [degreeChains_eq_bot_of_card_bound L (d+1) (fun s hs => by have := hL s hs; omega)] at ht
    exact ht
  have he := contigMap_boundary_of_support K L f g c hfg
  rw [hh, map_zero, hbd, map_zero, add_zero] at he
  have h := eq_neg_of_add_eq_zero_left he.symm
  have hn : -(mapChains K L g c) = mapChains K L g c := by
    ext s
    exact CharTwo.neg_eq _
  exact h.trans hn
end SimplicialChains
end

section
namespace SimplicialChains
open Finset
noncomputable def approximation (n m r : ℕ)
    (f : Euc (Fin n) → SignedVertex) : Chain (cross n) →ₗ[F₂] Chain (cross m) :=
  (mapChains (hemisphereComplex (n:ℝ)) (cross m) f).comp (fineCrossMap n r)
def IsFineLabel (n m r : ℕ) (f : Euc (Fin n) → SignedVertex) : Prop :=
  ∀ (s : Finset SignedVertex), s ∈ cross n →
    ∀ (t : {s : Finset (Euc (Fin n)) // s ∈ hemisphereComplex (n:ℝ)}),
      t ∈ (fineCrossMap n r (simplex (cross n) s)).support → t.val.image f ∈ cross m
lemma approximation_boundary (n m r : ℕ) (f : Euc (Fin n) → SignedVertex)
    (hf : IsFineLabel n m r f) :
    (boundary (cross m)).comp (approximation n m r f) =
      (approximation n m r f).comp (boundary (cross n)) := by
  apply Finsupp.lhom_ext
  intro s a
  have hh : boundary (cross m) (approximation n m r f (simplex (cross n) s.val)) =
      approximation n m r f (boundary (cross n) (simplex (cross n) s.val)) := by
    change boundary (cross m) (mapChains (hemisphereComplex (n:ℝ)) (cross m) f
      (fineCrossMap n r (simplex (cross n) s.val))) = _
    rw [mapChains_boundary_of_support _ (cross m) f _ (hf s.val s.property)]
    have hb := LinearMap.congr_fun (fineCrossMap_boundary n r) (simplex (cross n) s.val)
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at hb
    rw [hb]
    rfl
  rw [simplex_of_mem (cross n) s.property] at hh
  have ha : Finsupp.single s a = a • Finsupp.single s (1:F₂) := by simp
  simp only [LinearMap.comp_apply, ha, map_smul, hh]
lemma approximation_augmentation (n m r : ℕ) (f : Euc (Fin n) → SignedVertex)
    (hf : IsFineLabel n m r f) :
    (augmentation (cross m)).comp (approximation n m r f) = augmentation (cross n) := by
  apply Finsupp.lhom_ext
  intro s a
  have hh : augmentation (cross m) (approximation n m r f (simplex (cross n) s.val)) =
      augmentation (cross n) (simplex (cross n) s.val) := by
    change augmentation (cross m) (mapChains (hemisphereComplex (n:ℝ)) (cross m) f
      (fineCrossMap n r (simplex (cross n) s.val))) = _
    rw [mapChains_augmentation_of_support _ (cross m) f _ (hf s.val s.property)]
    exact LinearMap.congr_fun (fineCrossMap_augmentation n r) _
  rw [simplex_of_mem (cross n) s.property] at hh
  have ha : Finsupp.single s a = a • Finsupp.single s (1:F₂) := by simp
  simp only [LinearMap.comp_apply, ha, map_smul, hh]
lemma approximation_norm (n m r : ℕ) (hn : 0 < n)
    (f : Euc (Fin n) → SignedVertex)
    (hf : ∀ x ∈ annulus n, f (-x) = flip (f x)) :
    (normMap (cross m) flip).comp (approximation n m r f) =
      (approximation n m r f).comp (normMap (cross n) flip) := by
  have hu : (normMap (cross m) flip).comp (mapChains (hemisphereComplex (n:ℝ)) (cross m) f) =
      (mapChains (hemisphereComplex (n:ℝ)) (cross m) f).comp
        (normMap (hemisphereComplex (n:ℝ)) (Equiv.neg _)) := by
    apply mapChains_norm _ (cross m) (Equiv.neg _) flip (hemisphere_neg (n:ℝ)) (cross_flip m) f
    intro s hs x hx
    exact hf x (hemisphere_vertex_annulus n hn hs hx)
  rw [approximation, ← LinearMap.comp_assoc, hu, LinearMap.comp_assoc,
    fineCrossMap_norm, ← LinearMap.comp_assoc]
lemma approximation_degree (n m r d : ℕ) (f : Euc (Fin n) → SignedVertex) :
    degreeChains (cross n) d ≤ (degreeChains (cross m) d).comap (approximation n m r f) := by
  intro c hc
  exact mapChains_degree_all _ (cross m) f d (fineCrossMap_degree n r d hc)
lemma cross_equivariant_fundamental (n : ℕ) (hn : 1 < n)
    (T : Chain (cross n) →ₗ[F₂] Chain (cross n))
    (hTbd : (boundary (cross n)).comp T = T.comp (boundary (cross n)))
    (hTN : (normMap (cross n) flip).comp T = T.comp (normMap (cross n) flip))
    (hTa : (augmentation (cross n)).comp T = augmentation (cross n))
    (hTd : ∀ c ∈ degreeChains (cross n) n, T c ∈ degreeChains (cross n) n) :
    T (crossFundamental n) = crossFundamental n := by
  have hc := hTd _ (crossFundamental_degree n (by omega))
  have hb : boundary (cross n) (T (crossFundamental n)) = 0 := by
    rw [← LinearMap.comp_apply, hTbd, LinearMap.comp_apply,
      crossFundamental_boundary n (by omega), map_zero]
  have hd : T (crossFundamental n) ⟨crossFacet n (fun _ => false),
      crossFacet_mem n (by omega) (fun _ => false)⟩ = 1 := by
    rw [← cross_characteristicDegree_eq_coeff n hn _ hc hb]
    exact cross_equivariant_degree_one n (by omega) T hTbd hTN hTa
  rw [cross_top_cycle_eq n hn _ hc hb (fun _ => false), hd, one_smul]
lemma approximation_odd_fundamental (n r : ℕ) (hn : 1 < n)
    (f : Euc (Fin n) → SignedVertex) (hf : IsFineLabel n n r f)
    (ho : ∀ x ∈ annulus n, f (-x) = flip (f x)) :
    approximation n n r f (crossFundamental n) = crossFundamental n := by
  apply cross_equivariant_fundamental n hn _ (approximation_boundary n n r f hf)
    (approximation_norm n n r (by omega) f ho) (approximation_augmentation n n r f hf)
  intro c hc
  exact approximation_degree n n r n f hc
lemma approximation_agree_top (n m r : ℕ) (hn : 0 < n)
    (f g : Euc (Fin n) → SignedVertex)
    (hcard : m ≤ n)
    (hfg : ∀ s ∈ (fineCrossMap n r (crossFundamental n)).support,
      s.val.image f ∪ s.val.image g ∈ cross m) :
    approximation n m r f (crossFundamental n) = approximation n m r g (crossFundamental n) := by
  apply contig_maps_agree_top _ (cross m) f g n _
    (fineCrossMap_degree n r n (crossFundamental_degree n hn)) _ hfg
    (fun s hs => (cross_card m s hs).trans hcard)
  rw [← LinearMap.comp_apply, fineCrossMap_boundary, LinearMap.comp_apply,
    crossFundamental_boundary n hn, map_zero]
end SimplicialChains
end

section
namespace SimplicialChains
open Finset
open scoped Topology
lemma fineCrossMap_mesh (n r : ℕ) (c : Chain (cross n))
    {t : {s : Finset (Euc (Fin n)) // s ∈ hemisphereComplex (n:ℝ)}}
    (ht : t ∈ (fineCrossMap n r c).support) :
    ∀ x ∈ t.val, ∀ y ∈ t.val, dist x y ≤ (((n:ℝ)-1)/n)^r * 2 := by
  obtain ⟨s,_,ht⟩ := support_linearMap (cross n) (hemisphereComplex (n:ℝ)) _ c ht
  exact fineCrossMap_simplex_mesh n r s.property ht
lemma cross_union_labels_mem {m : ℕ} [NeZero m] {V : Type*} [DecidableEq V]
    (s : Finset V) (hs : s.Nonempty) (f g : V → Euc (Fin m))
    (hn : ∀ x ∈ s, ‖f x‖ = 1 ∧ ‖g x‖ = 1)
    (hclose : ∀ x ∈ s, ∀ y ∈ s,
      dist (f x) (f y) < (1:ℝ)/m ∧ dist (f x) (g y) < (1:ℝ)/m ∧
      dist (g x) (f y) < (1:ℝ)/m ∧ dist (g x) (g y) < (1:ℝ)/m) :
    s.image (fun x => sphereLabel (f x)) ∪ s.image (fun x => sphereLabel (g x)) ∈ cross m := by
  refine ⟨(hs.image _).mono Finset.subset_union_left, ?_, ?_⟩
  · intro v hv
    rcases Finset.mem_union.mp hv with hf | hg <;>
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ‹_› <;> exact sphereLabel_bound _
  · intro v hv w hw he
    rcases Finset.mem_union.mp hv with hf | hg <;>
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ‹_› <;>
      rcases Finset.mem_union.mp hw with hff | hgg <;>
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp ‹_›
    · exact sphereLabel_compatible _ _ (hn x hx).1 (hn y hy).1 (hclose x hx y hy).1 he
    · exact sphereLabel_compatible _ _ (hn x hx).1 (hn y hy).2 (hclose x hx y hy).2.1 he
    · exact sphereLabel_compatible _ _ (hn x hx).2 (hn y hy).1 (hclose x hx y hy).2.2.1 he
    · exact sphereLabel_compatible _ _ (hn x hx).2 (hn y hy).2 (hclose x hx y hy).2.2.2 he
lemma sphere_homotopy_chains (n m : ℕ) (hn : 0 < n) [NeZero m] (hmn : m ≤ n)
    (H : ℝ × Euc (Fin n) → Euc (Fin m))
    (hH : ContinuousOn H (Set.Icc (0:ℝ) 1 ×ˢ annulus n))
    (hHn : ∀ p ∈ Set.Icc (0:ℝ) 1 ×ˢ annulus n, ‖H p‖ = 1) :
    ∃ δ > 0, ∀ r : ℕ, (((n:ℝ)-1)/n)^r * 2 < δ →
      ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ u ∈ Set.Icc (0:ℝ) 1,
      approximation n m r (fun x => sphereLabel (H (t,x))) (crossFundamental n) =
      approximation n m r (fun x => sphereLabel (H (u,x))) (crossFundamental n) := by
  classical
  have hcompact : IsCompact (Set.Icc (0:ℝ) 1 ×ˢ annulus n) := isCompact_Icc.prod (annulus_compact n)
  obtain ⟨δ,hδ,hclose⟩ := Metric.uniformContinuousOn_iff.mp
    (hcompact.uniformContinuousOn_of_continuous hH) ((1:ℝ)/m)
      (div_pos zero_lt_one (by exact_mod_cast NeZero.pos m))
  refine ⟨δ,hδ,?_⟩
  intro r hr
  let C : Set.Icc (0:ℝ) 1 → Chain (cross m) :=
    fun t => approximation n m r (fun x => sphereLabel (H (t.val,x))) (crossFundamental n)
  have hClocal : IsLocallyConstant C := by
    apply (IsLocallyConstant.iff_eventually_eq C).mpr
    intro t
    filter_upwards [Metric.ball_mem_nhds t hδ] with u hu
    apply approximation_agree_top n m r hn _ _ hmn
    intro s hs
    have hmesh := fineCrossMap_mesh n r (crossFundamental n) hs
    have ha : ∀ x ∈ s.val, x ∈ annulus n :=
      fun x hx => hemisphere_vertex_annulus n hn s.property hx
    have hh (v w : Set.Icc (0:ℝ) 1) (hv : dist v.val w.val < δ)
        (x : Euc (Fin n)) (hx : x ∈ s.val)
        (y : Euc (Fin n)) (hy : y ∈ s.val) :
        dist (H (v.val,x)) (H (w.val,y)) < (1:ℝ)/m := by
      apply hclose (v.val,x) ⟨v.property,ha x hx⟩ (w.val,y) ⟨w.property,ha y hy⟩
      rw [Prod.dist_eq]
      exact max_lt hv ((hmesh x hx y hy).trans_lt hr)
    have hut : dist u.val t.val < δ := hu
    have htu : dist t.val u.val < δ := by simpa only [dist_comm] using hut
    apply cross_union_labels_mem s.val s.property.1 _ _
    · intro x hx
      exact ⟨hHn (u.val,x) ⟨u.property,ha x hx⟩,hHn (t.val,x) ⟨t.property,ha x hx⟩⟩
    · intro x hx y hy
      exact ⟨hh u u (by simpa using hδ) x hx y hy,hh u t hut x hx y hy,
        hh t u htu x hx y hy,hh t t (by simpa using hδ) x hx y hy⟩
  let : PreconnectedSpace (Set.Icc (0:ℝ) 1) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  intro t ht u hu
  exact hClocal.apply_eq_of_preconnectedSpace ⟨t,ht⟩ ⟨u,hu⟩
lemma exists_small_cross_mesh (n : ℕ) (hn : 0 < n) {δ : ℝ} (hδ : 0 < δ) :
    ∃ r : ℕ, (((n:ℝ)-1)/n)^r * 2 < δ := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hq : ((n:ℝ)-1)/n < 1 := (div_lt_one hn').mpr (by linarith)
  obtain ⟨r,hr⟩ := exists_pow_lt_of_lt_one (show (0:ℝ) < δ/2 by linarith) hq
  exact ⟨r,by linarith⟩
end SimplicialChains
end

section
namespace SimplicialChains
open Finset
noncomputable def labelRegion {m : ℕ} (i : Fin m) (b : Bool) :
    Set (Euc (Fin m)) :=
  {y | (∀ j, |y j| ≤ |y i|) ∧ if b then y i ≤ 0 else 0 ≤ y i}
lemma labelRegion_closed {m : ℕ} (i : Fin m) (b : Bool) : IsClosed (labelRegion i b) := by
  have hc (j : Fin m) : Continuous (fun y : Euc (Fin m) => y j) :=
    PiLp.continuous_apply 2 _ j
  apply IsClosed.inter
  · change IsClosed {y : Euc (Fin m) | ∀ j, |y j| ≤ |y i|}
    rw [Set.ofPred_forall]
    exact isClosed_iInter (fun j => isClosed_le (hc j).abs (hc i).abs)
  · cases b
    · exact isClosed_le continuous_const (hc i)
    · exact isClosed_le (hc i) continuous_const
lemma sphereLabel_mem_region {m : ℕ} [NeZero m] (y : Euc (Fin m))
    (i : Fin m) (b : Bool) (hy : sphereLabel y = (i.val,b)) : y ∈ labelRegion i b := by
  have hi : peakIndex y = i := Fin.ext (congrArg Prod.fst hy)
  have hb : decide (y (peakIndex y) < 0) = b := congrArg Prod.snd hy
  refine ⟨?_,?_⟩
  · intro j
    rw [← hi]
    exact maxIndex_le (fun j => |y j|) j
  · rw [← hb, hi]
    by_cases h : y i < 0
    · simp only [h, decide_true, ↓reduceIte]
      exact h.le
    · simp only [h, decide_false]
      exact le_of_not_gt h
lemma compact_label_locality {X : Type*} [MetricSpace X] [CompactSpace X]
    {m : ℕ} [NeZero m] (b : Fin m → Bool)
    (f g : X → Euc (Fin m)) (hf : Continuous f) (hg : Continuous g)
    (U : Set X) (hU : IsOpen U)
    (heq : ∀ x ∈ U, f x = g x)
    (hfull : ∀ x, (∀ i, f x ∈ labelRegion i (b i)) ∨
      (∀ i, g x ∈ labelRegion i (b i)) → x ∈ U) :
    ∃ δ > 0, ∀ x : X,
      (∀ y, dist y x < δ → f y = g y) ∨
      ∃ i j : Fin m,
        (∀ y, dist y x < δ → sphereLabel (f y) ≠ (i.val,b i)) ∧
        (∀ y, dist y x < δ → sphereLabel (g y) ≠ (j.val,b j)) := by
  let c : Option (Fin m × Fin m) → Set X := fun o => match o with
    | none => U
    | some (i,j) => (f ⁻¹' labelRegion i (b i))ᶜ ∩ (g ⁻¹' labelRegion j (b j))ᶜ
  have hc : ∀ i, IsOpen (c i) := by
    intro o
    cases o with
    | none => exact hU
    | some p =>
      exact ((labelRegion_closed p.1 (b p.1)).preimage hf).isOpen_compl.inter
        ((labelRegion_closed p.2 (b p.2)).preimage hg).isOpen_compl
  have hcover : (Set.univ : Set X) ⊆ ⋃ o, c o := by
    intro x _
    by_cases hx : x ∈ U
    · exact Set.mem_iUnion.mpr ⟨none,hx⟩
    · have hnf : ¬ ∀ i, f x ∈ labelRegion i (b i) := fun hh => hx (hfull x (Or.inl hh))
      have hng : ¬ ∀ i, g x ∈ labelRegion i (b i) := fun hh => hx (hfull x (Or.inr hh))
      obtain ⟨i,hi⟩ := not_forall.mp hnf
      obtain ⟨j,hj⟩ := not_forall.mp hng
      exact Set.mem_iUnion.mpr ⟨some (i,j),hi,hj⟩
  obtain ⟨δ,hδ,hball⟩ := lebesgue_number_lemma_of_metric isCompact_univ hc hcover
  refine ⟨δ,hδ,?_⟩
  intro x
  obtain ⟨o,ho⟩ := hball x (Set.mem_univ _)
  cases o with
  | none => exact Or.inl (fun y hy => heq y (ho hy))
  | some p =>
    refine Or.inr ⟨p.1,p.2,?_,?_⟩
    · intro y hy he
      exact (ho hy).1 (sphereLabel_mem_region _ _ _ he)
    · intro y hy he
      exact (ho hy).2 (sphereLabel_mem_region _ _ _ he)
lemma mapSimplex_coeff_zero_of_ne {V W : Type*} [DecidableEq V] [DecidableEq W]
    (L : PreComplex W) (f : V → W) (s : Finset V)
    (t : {s : Finset W // s ∈ L}) (hne : s.image f ≠ t.val) :
    mapSimplex L f s t = 0 := by
  rw [mapSimplex]
  split_ifs <;> simp_all [simplex_coeff]
lemma image_ne_crossFacet_of_missing {V : Type*} [DecidableEq V] {m : ℕ}
    (s : Finset V) (f : V → SignedVertex) (b : Fin m → Bool)
    (i : Fin m) (hi : ∀ x ∈ s, f x ≠ (i.val,b i)) : s.image f ≠ crossFacet m b := by
  intro h
  have hm : (i.val,b i) ∈ s.image f := by
    rw [h]
    exact (mem_crossFacet m b _).mpr ⟨i,rfl⟩
  obtain ⟨x,hx,he⟩ := Finset.mem_image.mp hm
  exact hi x hx he
lemma localized_approximation_coeff (n m : ℕ) (hn : 0 < n) [NeZero m]
    (b : Fin m → Bool)
    (f g : Euc (Fin n) → Euc (Fin m))
    (hf : ContinuousOn f (annulus n)) (hg : ContinuousOn g (annulus n))
    (U : Set (annulus n)) (hU : IsOpen U)
    (heq : ∀ x : annulus n, x ∈ U → f x.val = g x.val)
    (hfull : ∀ x : annulus n, (∀ i, f x.val ∈ labelRegion i (b i)) ∨
      (∀ i, g x.val ∈ labelRegion i (b i)) → x ∈ U) :
    ∃ δ > 0, ∀ r : ℕ, (((n:ℝ)-1)/n)^r * 2 < δ →
      approximation n m r (fun x => sphereLabel (f x)) (crossFundamental n)
        ⟨crossFacet m b,crossFacet_mem m (NeZero.pos m) b⟩ =
      approximation n m r (fun x => sphereLabel (g x)) (crossFundamental n)
        ⟨crossFacet m b,crossFacet_mem m (NeZero.pos m) b⟩ := by
  classical
  let : CompactSpace (annulus n) := isCompact_iff_compactSpace.mp (annulus_compact n)
  obtain ⟨δ,hδ,hlocal⟩ := compact_label_locality b (fun x : annulus n => f x.val)
    (fun x : annulus n => g x.val) hf.domRestrict hg.domRestrict U hU heq hfull
  refine ⟨δ,hδ,?_⟩
  intro r hr
  let K := hemisphereComplex (n:ℝ) (E := Euc (Fin n))
  let t : {s : Finset SignedVertex // s ∈ cross m} :=
    ⟨crossFacet m b,crossFacet_mem m (NeZero.pos m) b⟩
  let T : Chain K →ₗ[F₂] F₂ := (Finsupp.lapply t).comp (mapChains K (cross m) (fun x => sphereLabel (f x)))
  let R : Chain K →ₗ[F₂] F₂ := (Finsupp.lapply t).comp (mapChains K (cross m) (fun x => sphereLabel (g x)))
  change T (fineCrossMap n r (crossFundamental n)) = R (fineCrossMap n r (crossFundamental n))
  apply linearMap_eq_of_support T R _
  intro s hs
  change mapChains K (cross m) (fun x => sphereLabel (f x)) (simplex K s.val) t =
    mapChains K (cross m) (fun x => sphereLabel (g x)) (simplex K s.val) t
  rw [mapChains_simplex K (cross m) _ s.property,mapChains_simplex K (cross m) _ s.property]
  have ha : ∀ x ∈ s.val, x ∈ annulus n := fun x hx => hemisphere_vertex_annulus n hn s.property hx
  obtain ⟨x,hx⟩ := s.property.1
  have hmesh := fineCrossMap_mesh n r (crossFundamental n) hs
  rcases hlocal ⟨x,ha x hx⟩ with he | ⟨i,j,hi,hj⟩
  · have himg : s.val.image (fun y => sphereLabel (f y)) = s.val.image (fun y => sphereLabel (g y)) := by
      apply Finset.image_congr
      intro y hy
      exact congrArg sphereLabel (he ⟨y,ha y hy⟩ ((hmesh y hy x hx).trans_lt hr))
    simp only [mapSimplex,himg]
  · rw [mapSimplex_coeff_zero_of_ne (cross m) _ s.val t, mapSimplex_coeff_zero_of_ne (cross m) _ s.val t]
    · apply image_ne_crossFacet_of_missing s.val _ b j
      intro y hy
      exact hj ⟨y,ha y hy⟩ ((hmesh y hy x hx).trans_lt hr)
    · apply image_ne_crossFacet_of_missing s.val _ b i
      intro y hy
      exact hi ⟨y,ha y hy⟩ ((hmesh y hy x hx).trans_lt hr)
end SimplicialChains
end

section
namespace SimplicialChains
open Finset
noncomputable def signVector (m : ℕ) (b : Fin m → Bool) : Euc (Fin m) :=
  WithLp.toLp 2 (fun i => if b i then (-1:ℝ) else 1)
@[simp] lemma signVector_apply (m : ℕ) (b : Fin m → Bool) (i : Fin m) :
    signVector m b i = if b i then (-1:ℝ) else 1 := rfl
lemma signVector_norm (m : ℕ) (b : Fin m → Bool) : ‖signVector m b‖ = Real.sqrt m := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  have h (i : Fin m) : ‖signVector m b i‖ ^ 2 = (1:ℝ) := by
    simp only [signVector_apply]
    cases b i <;> norm_num
  simp only [h, Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin, mul_one]
noncomputable def facetCenter (m : ℕ) (b : Fin m → Bool) : Euc (Fin m) :=
  (Real.sqrt m)⁻¹ • signVector m b
lemma facetCenter_norm (m : ℕ) [NeZero m] (b : Fin m → Bool) : ‖facetCenter m b‖ = 1 := by
  rw [facetCenter, norm_smul, signVector_norm, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  exact inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos_of_pos (by exact_mod_cast NeZero.pos m)))
lemma facetCenter_region (m : ℕ) (b : Fin m → Bool) (i : Fin m) :
    facetCenter m b ∈ labelRegion i (b i) := by
  have ha (j : Fin m) : |facetCenter m b j| = (Real.sqrt m)⁻¹ := by
    simp only [facetCenter, PiLp.smul_apply, smul_eq_mul, signVector_apply, abs_mul,
      abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
    cases b j <;> norm_num
  refine ⟨fun j => by rw [ha j,ha i],?_⟩
  change (if b i then (Real.sqrt m)⁻¹ * (if b i then (-1:ℝ) else 1) ≤ 0
    else 0 ≤ (Real.sqrt m)⁻¹ * (if b i then (-1:ℝ) else 1))
  have h := inv_nonneg.mpr (Real.sqrt_nonneg (m:ℝ))
  cases b i <;> simp_all
lemma all_labelRegions_iff_center (m : ℕ) [NeZero m] (b : Fin m → Bool)
    (y : Euc (Fin m)) (hy : ‖y‖ = 1) :
    (∀ i, y ∈ labelRegion i (b i)) ↔ y = facetCenter m b := by
  refine ⟨?_,fun he i => he ▸ facetCenter_region m b i⟩
  intro hyc
  let i₀ : Fin m := ⟨0,NeZero.pos m⟩
  let d : ℝ := |y i₀|
  have hd : 0 ≤ d := abs_nonneg _
  have hcoord (i : Fin m) : |y i| = d :=
    le_antisymm ((hyc i₀).1 i) ((hyc i).1 i₀)
  have hv : y = d • signVector m b := by
    ext i
    simp only [PiLp.smul_apply, smul_eq_mul, signVector_apply]
    have hsign := (hyc i).2
    change (if b i then y i ≤ 0 else 0 ≤ y i) at hsign
    cases hb : b i
    · simp only [hb, Bool.false_eq_true, ↓reduceIte] at hsign ⊢
      simpa only [abs_of_nonneg hsign, mul_one] using hcoord i
    · simp only [hb, ↓reduceIte] at hsign ⊢
      have he := hcoord i
      rw [abs_of_nonpos hsign] at he
      linarith
  have hdval : d = (Real.sqrt m)⁻¹ := by
    have he := hy
    rw [hv,norm_smul,Real.norm_eq_abs,abs_of_nonneg hd,signVector_norm] at he
    exact eq_inv_of_mul_eq_one_left he
  rw [hv,hdval]
  rfl
lemma constant_approximation_facet_zero (n m r : ℕ) (hm : 1 < m) [NeZero m]
    (b : Fin m → Bool) (y : Euc (Fin m)) :
    approximation n m r (fun _ => sphereLabel y) (crossFundamental n)
      ⟨crossFacet m b,crossFacet_mem m (NeZero.pos m) b⟩ = 0 := by
  classical
  let K := hemisphereComplex (n:ℝ) (E := Euc (Fin n))
  let t : {s : Finset SignedVertex // s ∈ cross m} := ⟨crossFacet m b,crossFacet_mem m (NeZero.pos m) b⟩
  let T : Chain K →ₗ[F₂] F₂ := (Finsupp.lapply t).comp (mapChains K (cross m) (fun _ => sphereLabel y))
  change T (fineCrossMap n r (crossFundamental n)) = 0
  have ht : T = 0 := by
    apply Finsupp.lhom_ext
    intro s a
    have hh : T (simplex K s.val) = 0 := by
      change mapChains K (cross m) (fun _ => sphereLabel y) (simplex K s.val) t = 0
      rw [mapChains_simplex K (cross m) _ s.property]
      apply mapSimplex_coeff_zero_of_ne
      intro he
      have hc : (s.val.image (fun _ => sphereLabel y)).card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro a ha c hc
        obtain ⟨_,_,rfl⟩ := Finset.mem_image.mp ha
        obtain ⟨_,_,rfl⟩ := Finset.mem_image.mp hc
        rfl
      rw [he,crossFacet_card] at hc
      omega
    rw [simplex_of_mem K s.property] at hh
    have ha : Finsupp.single s a = a • Finsupp.single s (1:F₂) := by simp
    simp only [ha,map_smul,hh,smul_zero,LinearMap.zero_apply]
  rw [ht,LinearMap.zero_apply]
lemma continuous_missed_facet_zero (n m : ℕ) (hn : 0 < n) (hm : 1 < m) [NeZero m]
    (b : Fin m → Bool) (f : Euc (Fin n) → Euc (Fin m))
    (hf : ContinuousOn f (annulus n)) (hfn : ∀ x ∈ annulus n, ‖f x‖ = 1)
    (hmiss : ∀ x ∈ annulus n, f x ≠ facetCenter m b) :
    ∃ δ > 0, ∀ r : ℕ, (((n:ℝ)-1)/n)^r * 2 < δ →
      approximation n m r (fun x => sphereLabel (f x)) (crossFundamental n)
        ⟨crossFacet m b,crossFacet_mem m (NeZero.pos m) b⟩ = 0 := by
  have hfneg : -(facetCenter m b) ≠ facetCenter m b := by
    intro he
    have hz : facetCenter m b = 0 := by
      ext i
      have hi := congrArg (fun z : Euc (Fin m) => z i) he
      simp only [PiLp.neg_apply] at hi
      change facetCenter m b i = 0
      linarith
    have hn := facetCenter_norm m b
    rw [hz,norm_zero] at hn
    exact zero_ne_one hn
  obtain ⟨δ,hδ,hh⟩ := localized_approximation_coeff n m hn b f (fun _ => -(facetCenter m b))
    hf continuousOn_const ∅ isOpen_empty (by simp) (by
      intro x hx
      rcases hx with h | h
      · exact False.elim (hmiss x.val x.property ((all_labelRegions_iff_center m b _ (hfn _ x.property)).mp h))
      · exact False.elim (hfneg ((all_labelRegions_iff_center m b _ (by simp [facetCenter_norm])).mp h)))
  refine ⟨δ,hδ,fun r hr => ?_⟩
  rw [hh r hr,constant_approximation_facet_zero n m r hm b]
end SimplicialChains
end

section
namespace SimplicialChains
open Finset
open scoped RealInnerProductSpace
lemma eventually_fine_sphereLabel (n m : ℕ) (hn : 0 < n) [NeZero m]
    (g : Euc (Fin n) → Euc (Fin m))
    (hg : ContinuousOn g (annulus n)) (hgn : ∀ x ∈ annulus n, ‖g x‖ = 1) :
    ∃ δ > 0, ∀ r, (((n:ℝ)-1)/n)^r * 2 < δ → IsFineLabel n m r (fun x => sphereLabel (g x)) := by
  obtain ⟨δ,hδ,hclose⟩ := Metric.uniformContinuousOn_iff.mp
    ((annulus_compact n).uniformContinuousOn_of_continuous hg) ((1:ℝ)/m)
      (div_pos zero_lt_one (by exact_mod_cast NeZero.pos m))
  refine ⟨δ,hδ,?_⟩
  intro r hr s hs t ht
  refine ⟨t.property.1.image _, ?_, ?_⟩
  · intro v hv
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
    exact sphereLabel_bound _
  · intro v hv w hw he
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hw
    have hx' := hemisphere_vertex_annulus n hn t.property hx
    have hy' := hemisphere_vertex_annulus n hn t.property hy
    exact sphereLabel_compatible _ _ (hgn x hx') (hgn y hy')
      (hclose x hx' y hy' ((fineCrossMap_simplex_mesh n r hs ht x hx y hy).trans_lt hr)) he
lemma eventually_odd_sphere_degree (n : ℕ) (hn : 1 < n) [NeZero n]
    (g : Euc (Fin n) → Euc (Fin n))
    (hg : ContinuousOn g (annulus n)) (hgn : ∀ x ∈ annulus n, ‖g x‖ = 1)
    (hgo : ∀ x ∈ annulus n, g (-x) = -g x) :
    ∃ δ > 0, ∀ r, (((n:ℝ)-1)/n)^r * 2 < δ →
      approximation n n r (fun x => sphereLabel (g x)) (crossFundamental n) = crossFundamental n := by
  obtain ⟨δ,hδ,hr⟩ := eventually_fine_sphereLabel n n (by omega) g hg hgn
  refine ⟨δ,hδ,fun r hh => approximation_odd_fundamental n r hn _ (hr r hh) ?_⟩
  intro x hx
  rw [hgo x hx,sphereLabel_neg _ (hgn x hx)]
lemma normalized_homotopy_chains (n m : ℕ) (hn : 0 < n) [NeZero m] (hmn : m ≤ n)
    (H : ℝ × Euc (Fin n) → Euc (Fin m))
    (hH : ContinuousOn H (Set.Icc (0:ℝ) 1 ×ˢ annulus n))
    (hHz : ∀ p ∈ Set.Icc (0:ℝ) 1 ×ˢ annulus n, H p ≠ 0) :
    ∃ δ > 0, ∀ r, (((n:ℝ)-1)/n)^r * 2 < δ →
      approximation n m r (fun x => sphereLabel (unitRadial (H (0,x)))) (crossFundamental n) =
      approximation n m r (fun x => sphereLabel (unitRadial (H (1,x)))) (crossFundamental n) := by
  obtain ⟨δ,hδ,hh⟩ := sphere_homotopy_chains n m hn hmn (fun p => unitRadial (H p))
    ((unitRadial_continuousOn (S := {y | y ≠ 0}) (fun _ h => h)).comp hH hHz)
    (fun p hp => unitRadial_norm (hHz p hp))
  exact ⟨δ,hδ,fun r hr => hh r hr 0 ⟨le_rfl,zero_le_one⟩ 1 ⟨zero_le_one,le_rfl⟩⟩
end SimplicialChains
end

section
namespace SimplicialChains
open scoped RealInnerProductSpace
lemma odd_homotopy_surjective (n : ℕ) (hn : 1 < n) [NeZero n]
    (H : ℝ × Euc (Fin n) → Euc (Fin n))
    (hH : ContinuousOn H (Set.Icc (0:ℝ) 1 ×ˢ annulus n))
    (hHz : ∀ p ∈ Set.Icc (0:ℝ) 1 ×ˢ annulus n, H p ≠ 0)
    (hHo : ∀ x ∈ annulus n, H (0,-x) = -H (0,x))
    {y : Euc (Fin n)} (hy : ‖y‖ = 1) :
    ∃ x ∈ annulus n, unitRadial (H (1,x)) = y := by
  classical
  by_contra hmiss
  push Not at hmiss
  let b : Fin n → Bool := fun _ => false
  let L := householder y (facetCenter n b)
  have hLy : L y = facetCenter n b := householder_send (hy.trans (facetCenter_norm n b).symm)
  let K : ℝ × Euc (Fin n) → Euc (Fin n) := fun p => L (H p)
  have hK : ContinuousOn K (Set.Icc (0:ℝ) 1 ×ˢ annulus n) := L.continuous.comp_continuousOn hH
  have hKz : ∀ p ∈ Set.Icc (0:ℝ) 1 ×ˢ annulus n, K p ≠ 0 := by
    intro p hp hz
    exact hHz p hp (L.injective (hz.trans (map_zero L).symm))
  let f : Euc (Fin n) → Euc (Fin n) := fun x => unitRadial (K (0,x))
  let g : Euc (Fin n) → Euc (Fin n) := fun x => unitRadial (K (1,x))
  have hU : ContinuousOn (fun p => unitRadial (K p)) (Set.Icc (0:ℝ) 1 ×ˢ annulus n) :=
    (unitRadial_continuousOn (S := {z | z ≠ 0}) (fun _ h => h)).comp hK hKz
  have hf : ContinuousOn f (annulus n) := hU.comp
    (continuous_const.prodMk continuous_id).continuousOn (fun x hx => ⟨⟨le_rfl,zero_le_one⟩,hx⟩)
  have hg : ContinuousOn g (annulus n) := hU.comp
    (continuous_const.prodMk continuous_id).continuousOn (fun x hx => ⟨⟨zero_le_one,le_rfl⟩,hx⟩)
  have hfn : ∀ x ∈ annulus n, ‖f x‖ = 1 := fun x hx =>
    unitRadial_norm (hKz (0,x) ⟨⟨le_rfl,zero_le_one⟩,hx⟩)
  have hgn : ∀ x ∈ annulus n, ‖g x‖ = 1 := fun x hx =>
    unitRadial_norm (hKz (1,x) ⟨⟨zero_le_one,le_rfl⟩,hx⟩)
  have hfo : ∀ x ∈ annulus n, f (-x) = -f x := by
    intro x hx
    simp only [f,K,hHo x hx,map_neg,unitRadial_neg]
  have hgm : ∀ x ∈ annulus n, g x ≠ facetCenter n b := by
    intro x hx he
    have hnorm : L (unitRadial (H (1,x))) = unitRadial (K (1,x)) := by
      simp [unitRadial,K]
    apply hmiss x hx
    exact L.injective (hnorm.trans (he.trans hLy.symm))
  obtain ⟨δ₀,hδ₀,hdeg⟩ := eventually_odd_sphere_degree n hn f hf hfn hfo
  obtain ⟨δ₁,hδ₁,hhom⟩ := normalized_homotopy_chains n n (by omega) le_rfl K hK hKz
  obtain ⟨δ₂,hδ₂,hzero⟩ := continuous_missed_facet_zero n n (by omega) hn b g hg hgn hgm
  have hnp : (0:ℝ) < n := by exact_mod_cast NeZero.pos n
  have hq : ((n:ℝ)-1)/n < 1 := by apply (div_lt_one hnp).mpr; linarith
  obtain ⟨r,hr⟩ := exists_pow_lt_of_lt_one
    (show (0:ℝ) < min δ₀ (min δ₁ δ₂) / 2 by positivity) hq
  have hr0 : (((n:ℝ)-1)/n)^r * 2 < δ₀ := by
    have hh := min_le_left δ₀ (min δ₁ δ₂); linarith
  have hr1 : (((n:ℝ)-1)/n)^r * 2 < δ₁ := by
    have hh := (min_le_right δ₀ (min δ₁ δ₂)).trans (min_le_left δ₁ δ₂); linarith
  have hr2 : (((n:ℝ)-1)/n)^r * 2 < δ₂ := by
    have hh := (min_le_right δ₀ (min δ₁ δ₂)).trans (min_le_right δ₁ δ₂); linarith
  have he := hhom r hr1
  change approximation n n r (fun x => sphereLabel (f x)) (crossFundamental n) =
    approximation n n r (fun x => sphereLabel (g x)) (crossFundamental n) at he
  rw [hdeg r hr0] at he
  have hc := congrArg (fun c : Chain (cross n) => c ⟨crossFacet n b,crossFacet_mem n (NeZero.pos n) b⟩) he
  rw [crossFundamental_coeff n hn b,hzero r hr2] at hc
  exact one_ne_zero hc
end SimplicialChains
end

section
section
open scoped MatrixOrder Matrix.Norms.L2Operator
open SimplicialChains
section TraceHomotopy
variable {ν ι : Type*} [Fintype ν] [LinearOrder ν] [Nonempty ν] [Fintype ι]
omit [Nonempty ν] in
lemma Admissible.traceHomotopy_ray {f : Euc ν → ι → ℝ} (_hf : Admissible f)
    (hc : Fintype.card (UpperTriangle ν) = Fintype.card ι) (hn : 1 < Fintype.card ι)
    (G : ℝ × traceSphere ν → (Euc ι))
    (hG : ContinuousOn G (Set.Icc (0:ℝ) 1 ×ˢ Set.univ))
    (hG0 : ∀ A : traceSphere ν, G (0,A) = WithLp.toLp 2 (signedExtension f A.val))
    (hGz : ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ A : traceSphere ν, G (t,A) ≠ 0)
    {y : (Euc ι)} (hy : y ≠ 0) :
    ∃ A : traceSphere ν, ∃ t : ℝ, 0 < t ∧ G (1,A) = t • y := by
  classical
  let n := Fintype.card ι
  have hnz : n ≠ 0 := by dsimp [n]; omega
  let : NeZero n := ⟨hnz⟩
  let ea : UpperTriangle ν ≃ Fin n := (Fintype.equivFin _).trans (finCongr hc)
  let eaL := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ ea
  let ebL := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fintype.equivFin ι)
  let A : Euc (Fin n) → (SqMat ν) := fun x => symmetricCoordinates (eaL.symm x)
  have hAc : Continuous A := symmetricCoordinates.continuous_of_finiteDimensional.comp eaL.symm.continuous
  have hAs (x : Euc (Fin n)) : IsSelfAdjoint (A x) := symmetricCoordinates_selfAdjoint _
  have hAz (x : Euc (Fin n)) (hx : x ∈ annulus n) : A x ≠ 0 := by
    intro hz
    have h0 : eaL.symm x = 0 := symmetricCoordinates_injective (hz.trans (map_zero _).symm)
    have hx0 : x = 0 := eaL.symm.injective (h0.trans (map_zero _).symm)
    have hd := hx.1
    rw [hx0,norm_zero] at hd
    norm_num at hd
    exact hnz hd
  let N : annulus n → traceSphere ν := fun x =>
    ⟨traceRadial (A x.val),traceRadial_mem (hAs _) (hAz _ x.property)⟩
  have hN : Continuous N := by
    apply Continuous.subtype_mk
    exact traceRadial_continuousOn.comp_continuous (hAc.comp continuous_subtype_val)
      (fun x => hAz _ x.property)
  let H : ℝ × Euc (Fin n) → Euc (Fin n) := fun p =>
    if hx : p.2 ∈ annulus n then ebL (G (p.1,N ⟨p.2,hx⟩)) else 0
  have hH : ContinuousOn H (Set.Icc (0:ℝ) 1 ×ˢ annulus n) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    let S := Set.Icc (0:ℝ) 1 ×ˢ annulus n
    have hcN : Continuous (fun p : S => N ⟨p.val.2,p.property.2⟩) :=
      hN.comp (continuous_subtype_val.snd.subtype_mk _)
    have hg := hG.comp_continuous (continuous_subtype_val.fst.prodMk hcN)
      (fun p : S => ⟨p.property.1,Set.mem_univ _⟩)
    apply (ebL.continuous.comp hg).congr
    intro p
    change ebL (G (p.val.1,N ⟨p.val.2,p.property.2⟩)) = H p.val
    simp only [H,dif_pos p.property.2]
  have hHz : ∀ p ∈ Set.Icc (0:ℝ) 1 ×ˢ annulus n, H p ≠ 0 := by
    intro p hp hz
    have he : G (p.1,N ⟨p.2,hp.2⟩) = 0 := ebL.injective (by simpa only [H,dif_pos hp.2,map_zero] using hz)
    exact hGz _ hp.1 _ he
  have hHo : ∀ x ∈ annulus n, H (0,-x) = -H (0,x) := by
    intro x hx
    have hxn : -x ∈ annulus n := by simpa only [annulus,Set.mem_ofPred_eq,norm_neg] using hx
    simp only [H,dif_pos hx,dif_pos hxn,hG0,N]
    have hAn : A (-x) = -A x := by simp only [A,map_neg]
    rw [hAn,traceRadial_neg,signedExtension_odd,WithLp.toLp_neg,map_neg]
  have hY : ‖ebL (unitRadial y)‖ = 1 := by rw [ebL.norm_map,unitRadial_norm hy]
  obtain ⟨x,hx,he⟩ := odd_homotopy_surjective n hn H hH hHz hHo hY
  let z : (Euc ι) := G (1,N ⟨x,hx⟩)
  have hz : z ≠ 0 := hGz _ ⟨zero_le_one,le_rfl⟩ _
  have he' : unitRadial z = unitRadial y := by
    apply ebL.injective
    have heL : ebL (unitRadial z) = unitRadial (ebL z) := by simp only [unitRadial,map_smul,ebL.norm_map]
    rw [heL]
    simpa only [H,dif_pos hx] using he
  refine ⟨N ⟨x,hx⟩,‖z‖ / ‖y‖,div_pos (norm_pos_iff.mpr hz) (norm_pos_iff.mpr hy),?_⟩
  have hh := congrArg (fun v : (Euc ι) => ‖z‖ • v) he'
  simpa only [unitRadial,smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz),one_smul,
    ← div_eq_mul_inv] using hh
end TraceHomotopy
end
end

section
section
open Set
open scoped Topology
lemma compact_local_homotopy {X E : Type*} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [TopologicalSpace E] [Zero E]
    {U C : Set X} (hU : IsOpen U) (hC : IsCompact C) (hCU : C ⊆ U)
    (H : X → E) (hH : Continuous H) (hHz : ∀ x, H x ≠ 0)
    (K : ℝ × X → E) (hK : ContinuousOn K (Icc (0:ℝ) 1 ×ˢ U))
    (hK0 : ∀ x ∈ U, K (0,x) = H x)
    (hKz : ∀ t ∈ Icc (0:ℝ) 1, ∀ x ∈ U, K (t,x) ≠ 0)
    (B : Set E) (houtside : ∀ x ∉ U, H x ∉ B)
    (hhits : ∀ t ∈ Icc (0:ℝ) 1, ∀ x ∈ U, K (t,x) ∈ B → x ∈ C)
    (hend : ∀ x ∈ U, K (1,x) ∉ B) :
    ∃ G : ℝ × X → E, ContinuousOn G (Icc (0:ℝ) 1 ×ˢ Set.univ) ∧
      (∀ x, G (0,x) = H x) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ x, G (t,x) ≠ 0) ∧
      (∀ x, G (1,x) ∉ B) := by
  classical
  obtain ⟨q,hq1,-,hqs,hqb⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hC hU hCU
  let G : ℝ × X → E := fun p => if p.2 ∈ U then K (p.1 * q p.2,p.2) else H p.2
  have htm (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (x : X) : t * q x ∈ Icc (0:ℝ) 1 :=
    ⟨mul_nonneg ht.1 (hqb x).1,
      (mul_le_mul_of_nonneg_right ht.2 (hqb x).1).trans (by simpa using (hqb x).2)⟩
  have hG : ContinuousOn G (Icc (0:ℝ) 1 ×ˢ Set.univ) := by
    intro p hp
    by_cases hx : p.2 ∈ U
    · have hc : ContinuousOn (fun p : ℝ × X => K (p.1 * q p.2,p.2))
          (Icc (0:ℝ) 1 ×ˢ U) := hK.comp
        ((continuous_fst.mul (q.continuous.comp continuous_snd)).prodMk continuous_snd).continuousOn
        (fun p hp => ⟨htm p.1 hp.1 p.2,hp.2⟩)
      have hnear : ∀ᶠ p' in 𝓝 p, p'.2 ∈ U :=
        continuous_snd.continuousAt.preimage_mem_nhds (hU.mem_nhds hx)
      have hset : Icc (0:ℝ) 1 ×ˢ U ∈ 𝓝[Icc (0:ℝ) 1 ×ˢ Set.univ] p := by
        filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds hnear,
          self_mem_nhdsWithin] with p' hu hi
        exact ⟨hi.1,hu⟩
      apply ((hc p ⟨hp.1,hx⟩).mono_of_mem_nhdsWithin hset).congr_of_eventuallyEq
      · filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds hnear] with p' hu
        simp [G,hu]
      · simp [G,hx]
    · have hxq : p.2 ∉ tsupport q := fun h => hx (hqs h)
      have hnear : ∀ᶠ p' in 𝓝 p, p'.2 ∉ tsupport q :=
        continuous_snd.continuousAt.preimage_mem_nhds ((isClosed_tsupport q).isOpen_compl.mem_nhds hxq)
      apply (hH.comp continuous_snd).continuousAt.continuousWithinAt.congr_of_eventuallyEq
      · filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds hnear] with p' hq
        have hz : q p'.2 = 0 := image_eq_zero_of_notMem_tsupport hq
        by_cases hu : p'.2 ∈ U
        · simp [G,hu,hz,hK0 p'.2 hu]
        · simp [G,hu]
      · simp [G,hx]
  refine ⟨G,hG,?_,?_,?_⟩
  · intro x
    by_cases hx : x ∈ U
    · simp [G,hx,hK0 x hx]
    · simp [G,hx]
  · intro t ht x
    by_cases hx : x ∈ U
    · simpa only [G,if_pos hx] using hKz _ (htm t ht x) x hx
    · simpa only [G,if_neg hx] using hHz x
  · intro x hb
    by_cases hx : x ∈ U
    · have hh : K (q x,x) ∈ B := by simpa only [G,if_pos hx,one_mul] using hb
      have hc := hhits _ (hqb x) x hx hh
      rw [hq1 hc] at hh
      exact hend x hx hh
    · exact houtside x hx (by simpa only [G,if_neg hx] using hb)
end
end

section
section
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
open Set
section ChartSurgery
variable {ν ι κ : Type*} [Fintype ν] [LinearOrder ν] [Nonempty ν] [Fintype ι] [DecidableEq ι] [Fintype κ]
lemma Admissible.chart_surgery_impossible {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    (hdim : Fintype.card (UpperTriangle ν) = Fintype.card ι) (hn : 1 < Fintype.card ι)
    {I : Finset ι} (hI : I.Nonempty) [Nonempty ↥(Iᶜ : Finset ι)]
    (hmax : ∀ u : (Euc ν), ‖u‖ = 1 → I ⊆ positiveSupport f u → positiveSupport f u = I)
    {w : (Euc ν)} (hw : ‖w‖ = 1) (hwi : ∀ i ∈ I, 0 < f w i)
    {r : ι → ℝ} (hr : ∀ i ∈ I, 0 < r i) (hro : ∀ i ∉ I, r i = 0) (hrs : ∑ i, r i = 1)
    (c : κ → (Euc ν)) (hc : ∀ j, c j ∈ commonPositiveCone f I) (hcn : ∀ j, ‖c j‖ = 1)
    (hd : Pairwise (fun i j => Disjoint (interior (signChamber (activeVectors f I) (c i)))
      (interior (signChamber (activeVectors f I) (c j)))))
    (hcover : orientedLevel f w r ⊆ ⋃ j, interior (signChamber (activeVectors f I) (c j)))
    {ε : ℝ} (hε : 0 < ε) (g : κ → (SqMat ν) → Euc ↥(Iᶜ : Finset ι))
    (hg : ∀ j, Continuous (g j)) (hgs : ∀ j, ∀ Q ∈ matrixFibre (c j), ∑ i, g j Q i = 1)
    (hge : ∀ j, ∀ Q ∈ matrixFibre (c j), ‖g j Q - negativeCoordinates f I Q‖ < ε)
    (z : Euc ↥(Iᶜ : Finset ι)) (hz : ∀ i, ε < z i) (hzs : ∑ i, z i = 1)
    (hgm : ∀ j, ∀ Q ∈ matrixFibre (c j), g j Q ≠ z) : False := by
  classical
  let S : κ → Set (traceSphere ν) := fun j => {A | A.val ∈ purityChart f I w (c j)}
  let U : Set (traceSphere ν) := ⋃ j, S j
  let C : Set (traceSphere ν) := {A | ∃ p : levelFibre f w r, balancedModel p = A ∧
    ∃ t ∈ Icc (0:ℝ) 1, levelHomotopy f I w r c g (t,p) = z}
  let K : ℝ × traceSphere ν → (Euc ι) := finiteOpenGlue (fun j => {p | p.2 ∈ S j})
    (fun j p => mixedHomotopy f I w (c j) (g j) p.1 p.2.val)
  let H : traceSphere ν → (Euc ι) := fun A => WithLp.toLp 2 (signedExtension f A.val)
  let y : (Euc ι) := blockVector I (1/2:ℝ) r (1/2:ℝ) z
  let B : Set (Euc ι) := {v | ∃ d : ℝ, 0 < d ∧ v = d • y}
  have hSo : ∀ j, IsOpen (S j) := fun j =>
    hf.purityChart_isOpen I w (c j) Subtype.val continuous_subtype_val (fun A => A.property.1)
  have hSd : Pairwise (fun i j => Disjoint (S i) (S j)) := by
    intro i j hij
    exact Set.disjoint_left.mpr (fun A hA hB => Set.disjoint_left.mp (hd hij) hA.2.2.2.2.2 hB.2.2.2.2.2)
  have hKd : Pairwise (fun i j => Disjoint {p : ℝ × traceSphere ν | p.2 ∈ S i}
      {p : ℝ × traceSphere ν | p.2 ∈ S j}) := by
    intro i j hij
    exact Set.disjoint_left.mpr (fun p ha hb => Set.disjoint_left.mp (hSd hij) ha hb)
  have hKe (j : κ) (A : traceSphere ν) (hA : A ∈ S j) (t : ℝ) :
      K (t,A) = mixedHomotopy f I w (c j) (g j) t A.val :=
    finiteOpenGlue_eq hKd _ hA
  have hK : ContinuousOn K (Icc (0:ℝ) 1 ×ˢ U) :=
    finiteOpenGlue_continuousOn_prod hSo hSd _
      (fun j => hf.mixedHomotopy_continuousOn hI (hc j) (hcn j) (g j) (hg j))
  have hC : IsCompact C := hf.level_hits_compact hI c hc hcn hd hcover g hg z
  have hCU : C ⊆ U := by
    rintro A ⟨p,rfl,t,ht,he⟩
    obtain ⟨j,hj⟩ := mem_iUnion.mp (hcover p.property.1)
    have hF : fibreHomotopy f I (c j) (g j) t p.val.1 p.val.2 = z :=
      (levelHomotopy_eq hd g hj t).symm.trans he
    have hunit : IsUnit (rankOne p.val.1 + p.val.2) := by
      by_contra hnu
      exact hf.fibreHomotopy_boundary_misses hI (hc j) (hcn j) p.property.1.1
        (interior_subset hj) (g j) hε (hge j) z hz ht p.property.2 hnu hF
    apply mem_iUnion.mpr
    refine ⟨j,?_⟩
    exact balancedFibre_chart p.property.1.1 (hf.orientedLevel_inner_pos hI hw hwi hr p.property.1)
      (orientedLevel_cone hr p.property.1) hj p.property.2 hunit
  have hH : Continuous H := (PiLp.continuous_toLp 2 _).comp
    (hf.signedExtension_continuousOn.comp_continuous continuous_subtype_val (fun A => A.property.1))
  have hHz : ∀ A : traceSphere ν, H A ≠ 0 := by
    intro A h
    have hzero : signedExtension f A.val = 0 := WithLp.toLp_injective 2 h
    exact traceSphere_ne_zero A.property ((hf.signedExtension_eq_zero_iff A.property.1).mp hzero)
  have hK0 : ∀ A ∈ U, K (0,A) = H A := by
    intro A hA
    obtain ⟨j,hj⟩ := mem_iUnion.mp hA
    rw [hKe j A hj 0]
    exact hf.mixedHomotopy_zero hmax (g j) A.property.1 hj
  have hKz : ∀ t ∈ Icc (0:ℝ) 1, ∀ A ∈ U, K (t,A) ≠ 0 := by
    intro t ht A hA
    obtain ⟨j,hj⟩ := mem_iUnion.mp hA
    rw [hKe j A hj t]
    exact hf.mixedHomotopy_nonzero hI (g j) t hj
  have houtside : ∀ A ∉ U, H A ∉ B := by
    rintro A hAU ⟨d,hdp,he⟩
    obtain ⟨hunit,hline,hAw,hm,hlevel⟩ := hf.original_ray_level hI hmax hw hwi hr hro hrs
      (fun i => hε.trans (hz i)) hzs A.property hdp he
    obtain ⟨j,hj⟩ := mem_iUnion.mp (hcover hlevel)
    exact hAU (mem_iUnion.mpr ⟨j,hunit,hline,hAw,hm,orientedLevel_cone hr hlevel,hj⟩)
  have hhits : ∀ t ∈ Icc (0:ℝ) 1, ∀ A ∈ U, K (t,A) ∈ B → A ∈ C := by
    rintro t ht A hAU ⟨d,hdp,he⟩
    obtain ⟨j,hj⟩ := mem_iUnion.mp hAU
    rw [hKe j A hj t] at he
    obtain ⟨hl,hF,hA⟩ := hf.mixedHomotopy_hit hI hmax (hc j) (hcn j) (g j) (hgs j)
      hro hrs hzs ht hdp A.property hj he
    let p : levelFibre f w r := ⟨(lineRepresentative w A.val,negativeFibre A.val),hl,purityChart_fibre hj⟩
    refine ⟨p,Subtype.ext hA.symm,t,ht,?_⟩
    exact (levelHomotopy_eq hd g hj.2.2.2.2.2 t).trans hF
  have hend : ∀ A ∈ U, K (1,A) ∉ B := by
    rintro A hAU ⟨d,hdp,he⟩
    obtain ⟨j,hj⟩ := mem_iUnion.mp hAU
    rw [hKe j A hj 1] at he
    obtain ⟨-,hF,-⟩ := hf.mixedHomotopy_hit hI hmax (hc j) (hcn j) (g j) (hgs j)
      hro hrs hzs ⟨zero_le_one,le_rfl⟩ hdp A.property hj he
    rw [fibreHomotopy_one f I (hcn j) (purityChart_unit hj) (g j) (purityChart_fibre hj)] at hF
    exact hgm j _ (centeredFibre_mem (hcn j) (purityChart_unit hj) (purityChart_fibre hj)) hF
  let : CompactSpace (traceSphere ν) := isCompact_iff_compactSpace.mp traceSphere_compact
  obtain ⟨G,hG,hG0,hGz,hGm⟩ := compact_local_homotopy (isOpen_iUnion hSo) hC hCU H hH hHz
    K hK hK0 hKz B houtside hhits hend
  have hy : y ≠ 0 := blockVector_nonzero hI (by norm_num) hr z
  obtain ⟨A,d,hd,he⟩ := hf.traceHomotopy_ray hdim hn G hG hG0 hGz hy
  exact hGm A ⟨d,hd,he⟩
end ChartSurgery
end
end

section
section
open scoped RealInnerProductSpace
section DisjointChambers
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
lemma compact_disjoint_chambers {Z K : Set E} (hK : IsCompact K)
    (hsub : K ⊆ interior (safeNormals Z)) :
    ∃ C : Finset E, (↑C : Set E) ⊆ K ∧
      (Pairwise (fun c d : ↥C => Disjoint (interior (signChamber Z c.val))
        (interior (signChamber Z d.val)))) ∧
      K ⊆ ⋃ c : ↥C, interior (signChamber Z c.val) := by
  classical
  obtain ⟨C,hCK,hcover⟩ := compact_finite_chambers hK hsub
  let g : E → Set E := fun c => interior (signChamber Z c)
  have hsurj : (↑C : Set E).SurjOn g (↑(C.image g) : Set (Set E)) := by
    intro U hU
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hU
    exact ⟨c,hc,rfl⟩
  obtain ⟨D,hDC,hDinj,hDimage⟩ := Finset.exists_subset_injOn_image_eq_of_surjOn
    (↑C : Set E) (C.image g) hsurj
  refine ⟨D,fun c hc => hCK (hDC hc),?_,?_⟩
  · intro c d hne
    rcases signChamber_eq_or_disjoint Z c.val d.val with he | hdj
    · exfalso
      exact hne (Subtype.ext (hDinj c.property d.property (congrArg interior he)))
    · exact hdj.mono interior_subset interior_subset
  · intro x hx
    obtain ⟨c,hc,hxc⟩ := Set.mem_iUnion₂.mp (hcover hx)
    have hg : g c ∈ D.image g := by rw [hDimage]; exact Finset.mem_image.mpr ⟨c,hc,rfl⟩
    obtain ⟨d,hd,hgd⟩ := Finset.mem_image.mp hg
    exact Set.mem_iUnion.mpr ⟨⟨d,hd⟩,by change x ∈ g d; rw [hgd]; exact hxc⟩
end DisjointChambers
end
section
open scoped Matrix RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
section MatrixEmbedding
variable {μ ν : Type*} [Fintype μ] [Fintype ν] [DecidableEq μ] [DecidableEq ν]
lemma toEuclideanLin_mul {α β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
    (A : Matrix α β ℝ) (B : Matrix β γ ℝ) :
    Matrix.toEuclideanLin (A*B) = (Matrix.toEuclideanLin A).comp (Matrix.toEuclideanLin B) := by
  apply LinearMap.ext
  intro v
  apply PiLp.ext
  intro i
  change ((A*B)*ᵥ v) i = (A *ᵥ (B *ᵥ v)) i
  rw [Matrix.mulVec_mulVec]
noncomputable def isometryMatrix (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) : Matrix ν μ ℝ :=
  Matrix.toEuclideanLin.symm e.toLinearMap
omit [DecidableEq ν] in
lemma isometryMatrix_action (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) (x : (Euc μ)) :
    Matrix.toEuclideanLin (isometryMatrix e) x = e x :=
  LinearMap.congr_fun (Matrix.toEuclideanLin.apply_symm_apply e.toLinearMap) x
lemma isometryMatrix_star_mul (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) :
    (isometryMatrix e)ᴴ * isometryMatrix e = 1 := by
  apply Matrix.toEuclideanLin.injective
  rw [toEuclideanLin_mul,Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  have he : Matrix.toEuclideanLin (isometryMatrix e) = e.toLinearMap :=
    Matrix.toEuclideanLin.apply_symm_apply _
  rw [he]
  rw [e.adjoint_comp_self']
  apply LinearMap.ext
  intro x
  simp only [LinearMap.id_apply,Matrix.toLpLin_apply,Matrix.one_mulVec,WithLp.toLp_ofLp]
noncomputable def matrixEmbed (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) : SqMat μ →ₗ[ℝ] SqMat ν where
  toFun B := isometryMatrix e * B * (isometryMatrix e)ᴴ
  map_add' B C := by simp only [Matrix.mul_add,Matrix.add_mul]
  map_smul' t B := by simp only [Matrix.mul_smul,Matrix.smul_mul]; rfl
omit [DecidableEq ν] in
lemma matrixEmbed_nonneg (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) {B : SqMat μ} (hB : 0 ≤ B) :
    0 ≤ matrixEmbed e B := ((Matrix.nonneg_iff_posSemidef.mp hB).mul_mul_conjTranspose_same _).nonneg
lemma matrixEmbed_trace (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) (B : SqMat μ) :
    Matrix.trace (matrixEmbed e B) = Matrix.trace B := by
  change Matrix.trace (isometryMatrix e * B * (isometryMatrix e)ᴴ) = Matrix.trace B
  rw [Matrix.trace_mul_comm,← Matrix.mul_assoc,isometryMatrix_star_mul,Matrix.one_mul]
lemma matrixEmbed_action (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) (B : SqMat μ) (x : (Euc μ)) :
    Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ) (matrixEmbed e B) (e x) =
      e (Matrix.toEuclideanCLM (n := μ) (𝕜 := ℝ) B x) := by
  change Matrix.toEuclideanLin (matrixEmbed e B) (e x) = e (Matrix.toEuclideanLin B x)
  change Matrix.toEuclideanLin (isometryMatrix e * B * (isometryMatrix e)ᴴ) (e x) = _
  rw [toEuclideanLin_mul,toEuclideanLin_mul]
  change Matrix.toEuclideanLin (isometryMatrix e)
    (Matrix.toEuclideanLin B (Matrix.toEuclideanLin (isometryMatrix e)ᴴ (e x))) = _
  have hh : Matrix.toEuclideanLin (isometryMatrix e)ᴴ (e x) = x := by
    rw [← isometryMatrix_action e x]
    change ((Matrix.toEuclideanLin (isometryMatrix e)ᴴ).comp
      (Matrix.toEuclideanLin (isometryMatrix e))) x = x
    rw [← toEuclideanLin_mul,isometryMatrix_star_mul]
    simp only [Matrix.toLpLin_apply,Matrix.one_mulVec,WithLp.toLp_ofLp]
  rw [hh,isometryMatrix_action]
lemma matrixEmbed_kernel (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) (B : SqMat μ) {u : (Euc ν)}
    (hu : ∀ x : (Euc μ), ⟪u,e x⟫ = 0) :
    Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ) (matrixEmbed e B) u = 0 := by
  have hz : Matrix.toEuclideanLin (isometryMatrix e)ᴴ u = 0 := by
    apply ext_inner_left ℝ
    intro x
    rw [inner_zero_right,Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    change ⟪x,(Matrix.toEuclideanLin (isometryMatrix e)).adjoint u⟫ = 0
    rw [LinearMap.adjoint_inner_right,isometryMatrix_action,real_inner_comm]
    exact hu x
  change Matrix.toEuclideanLin (isometryMatrix e * B * (isometryMatrix e)ᴴ) u = 0
  rw [toEuclideanLin_mul]
  change Matrix.toEuclideanLin (isometryMatrix e * B) (Matrix.toEuclideanLin (isometryMatrix e)ᴴ u) = 0
  rw [hz,map_zero]
end MatrixEmbedding
end
end

section
section
open scoped Matrix RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
section MatrixCompression
variable {μ ν : Type*} [Fintype μ] [Fintype ν] [DecidableEq μ] [DecidableEq ν]
noncomputable def matrixCompress (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) : SqMat ν →ₗ[ℝ] SqMat μ where
  toFun Q := (isometryMatrix e)ᴴ * Q * isometryMatrix e
  map_add' Q R := by simp only [Matrix.mul_add,Matrix.add_mul]
  map_smul' t Q := by simp only [Matrix.mul_smul,Matrix.smul_mul]; rfl
omit [DecidableEq ν] in
lemma matrixCompress_nonneg (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) {Q : SqMat ν} (hQ : 0 ≤ Q) :
    0 ≤ matrixCompress e Q :=
  ((Matrix.nonneg_iff_posSemidef.mp hQ).conjTranspose_mul_mul_same _).nonneg
lemma isometryMatrix_adjoint_action (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) (x : (Euc μ)) :
    Matrix.toEuclideanLin (isometryMatrix e)ᴴ (e x) = x := by
  rw [← isometryMatrix_action e x]
  change ((Matrix.toEuclideanLin (isometryMatrix e)ᴴ).comp
    (Matrix.toEuclideanLin (isometryMatrix e))) x = x
  rw [← toEuclideanLin_mul,isometryMatrix_star_mul]
  simp only [Matrix.toLpLin_apply,Matrix.one_mulVec,WithLp.toLp_ofLp]
lemma matrixEmbed_compress (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) {Q : SqMat ν}
    (hQ : IsSelfAdjoint Q)
    (hR : LinearMap.range (Matrix.toEuclideanLin Q) ≤ LinearMap.range e.toLinearMap) :
    matrixEmbed e (matrixCompress e Q) = Q := by
  let T := isometryMatrix e
  have hleft : (T * Tᴴ) * Q = Q := by
    apply Matrix.toEuclideanLin.injective
    apply LinearMap.ext
    intro v
    obtain ⟨x,hx⟩ := hR (LinearMap.mem_range_self (Matrix.toEuclideanLin Q) v)
    change e x = Matrix.toEuclideanLin Q v at hx
    rw [toEuclideanLin_mul,toEuclideanLin_mul]
    change Matrix.toEuclideanLin T (Matrix.toEuclideanLin Tᴴ (Matrix.toEuclideanLin Q v)) = _
    rw [← hx,isometryMatrix_adjoint_action,isometryMatrix_action]
  have hright : Q * (T*Tᴴ) = Q := by
    have he := congrArg Matrix.conjTranspose hleft
    rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose] at he
    simpa only [← Matrix.star_eq_conjTranspose,hQ.star_eq] using he
  change T * (Tᴴ * Q * T) * Tᴴ = Q
  calc
    _ = ((T*Tᴴ)*Q)*(T*Tᴴ) := by simp only [Matrix.mul_assoc]
    _ = Q := by rw [hleft,hright]
lemma matrixCompress_trace (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) {Q : SqMat ν}
    (hQ : IsSelfAdjoint Q)
    (hR : LinearMap.range (Matrix.toEuclideanLin Q) ≤ LinearMap.range e.toLinearMap) :
    Matrix.trace (matrixCompress e Q) = Matrix.trace Q := by
  rw [← matrixEmbed_trace e,matrixEmbed_compress e hQ hR]
end MatrixCompression
end
end

section
section
open scoped Matrix RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
section SymmetricEntries
variable {ν : Type*} [Fintype ν] [LinearOrder ν]
noncomputable def symmetricEntries : SqMat ν →ₗ[ℝ] Euc (UpperTriangle ν) where
  toFun Q := WithLp.toLp 2 (fun p => Q p.val.1 p.val.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
omit [Fintype ν] in
lemma symmetricCoordinates_entries {Q : SqMat ν} (hQ : IsSelfAdjoint Q) :
    symmetricCoordinates (symmetricEntries Q) = Q := by
  ext i j
  change (if h : i ≤ j then Q i j else Q j i) = Q i j
  split_ifs with h
  · rfl
  · have he := congrArg (fun B : SqMat ν => B i j) hQ.star_eq
    simpa only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply,star_trivial] using he
end SymmetricEntries
end
section
open scoped RealInnerProductSpace
lemma orthogonal_frame (k : ℕ) {u : Euc (Fin (k+1))} (hu : ‖u‖ = 1) :
    ∃ e : Euc (Fin k) →ₗᵢ[ℝ] Euc (Fin (k+1)),
      (∀ x, ⟪u,e x⟫ = 0) ∧
      (∀ v, ⟪u,v⟫ = 0 → ∃ x, e x = v) := by
  let W := (Submodule.span ℝ {u})ᗮ
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  have hdim : Module.finrank ℝ W = k := by
    let : Fact (Module.finrank ℝ (Euc (Fin (k+1))) = k+1) := ⟨by simp⟩
    exact Submodule.finrank_orthogonal_span_singleton hu0
  let b := (stdOrthonormalBasis ℝ W).reindex (finCongr hdim)
  refine ⟨W.subtypeₗᵢ.comp b.repr.symm.toLinearIsometry,?_,?_⟩
  · intro x
    exact (Submodule.mem_orthogonal_singleton_iff_inner_right.mp (b.repr.symm x).property)
  · intro v hv
    have hvW : v ∈ W := Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hv
    refine ⟨b.repr ⟨v,hvW⟩,?_⟩
    change (b.repr.symm (b.repr ⟨v,hvW⟩)).val = v
    rw [LinearIsometryEquiv.symm_apply_apply]
end
end

section
section
open scoped BigOperators
noncomputable def coordinateSum {ι : Type*} [Fintype ι] : Euc ι →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => ∑ i, x i
      map_add' := by intro x y; simp only [PiLp.add_apply,Finset.sum_add_distrib]
      map_smul' := by intro t x; simp only [PiLp.smul_apply,smul_eq_mul,Finset.mul_sum,RingHom.id_apply] }
lemma coordinateSum_apply {ι : Type*} [Fintype ι] (x : Euc ι) :
    coordinateSum x = ∑ i, x i := rfl
noncomputable def uniformVector (ι : Type*) [Fintype ι] : Euc ι :=
  WithLp.toLp 2 (fun _ => (Fintype.card ι : ℝ)⁻¹)
lemma coordinateSum_uniform (ι : Type*) [Fintype ι] [Nonempty ι] :
    coordinateSum (uniformVector ι) = 1 := by
  simp only [coordinateSum_apply,uniformVector,Finset.sum_const,
    Finset.card_univ,nsmul_eq_mul]
  exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (ne_of_gt (Fintype.card_pos)))
noncomputable def zeroSumProjection (ι : Type*) [Fintype ι] :
    Euc ι →L[ℝ] Euc ι :=
  ContinuousLinearMap.id ℝ _ - coordinateSum.smulRight (uniformVector ι)
noncomputable def simplexProjection {ι : Type*} [Fintype ι] (x : Euc ι) :=
  zeroSumProjection ι x + uniformVector ι
lemma simplexProjection_sum {ι : Type*} [Fintype ι] [Nonempty ι] (x : Euc ι) :
    coordinateSum (simplexProjection x) = 1 := by
  simp only [simplexProjection,zeroSumProjection,sub_apply,ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply,map_add,map_sub,map_smul,coordinateSum_uniform,
    smul_eq_mul,mul_one,sub_self,zero_add]
lemma simplexProjection_fixed {ι : Type*} [Fintype ι] {x : Euc ι}
    (hx : coordinateSum x = 1) : simplexProjection x = x := by
  simp only [simplexProjection,zeroSumProjection,sub_apply,ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply,hx,one_smul,sub_add_cancel]
lemma simplexProjection_sub_fixed {ι : Type*} [Fintype ι] {x y : Euc ι}
    (hy : coordinateSum y = 1) : simplexProjection x - y = zeroSumProjection ι (x-y) := by
  rw [map_sub]
  have hy' := simplexProjection_fixed hy
  change zeroSumProjection ι y + uniformVector ι = y at hy'
  change (zeroSumProjection ι x + uniformVector ι) - y = _
  calc
    _ = (zeroSumProjection ι x + uniformVector ι) -
      (zeroSumProjection ι y + uniformVector ι) := by rw [hy']
    _ = _ := by abel
lemma continuous_simplex_approx {D ι : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [Fintype ι] [Nonempty ι]
    (g : D → Euc ι) (hg : Continuous g)
    {K : Set D} (hK : ∀ x ∈ K, coordinateSum (g x) = 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : D → Euc ι, ContDiff ℝ (⊤ : ℕ∞) a ∧
      (∀ x, coordinateSum (a x) = 1) ∧ (∀ x ∈ K, ‖a x - g x‖ < ε) := by
  have hp := norm_nonneg (zeroSumProjection ι)
  have hδ : 0 < ε / (‖zeroSumProjection ι‖ + 1) := div_pos hε (by positivity)
  obtain ⟨b,hb,hbg,-⟩ := hg.exists_contDiff_approx (⊤ : ℕ∞)
    (continuous_const : Continuous (fun _ : D => ε / (‖zeroSumProjection ι‖ + 1))) (fun _ => hδ)
  let a := fun x => simplexProjection (b x)
  refine ⟨a,?_,fun x => simplexProjection_sum (b x),?_⟩
  · exact ((zeroSumProjection ι).contDiff.comp hb).add contDiff_const
  · intro x hx
    change ‖simplexProjection (b x) - g x‖ < ε
    rw [simplexProjection_sub_fixed (hK x hx)]
    have hd : ‖b x - g x‖ < ε / (‖zeroSumProjection ι‖ + 1) := by
      simpa only [dist_eq_norm] using hbg x
    calc
      _ ≤ ‖zeroSumProjection ι‖ * ‖b x - g x‖ := (zeroSumProjection ι).le_opNorm _
      _ ≤ ‖zeroSumProjection ι‖ * (ε / (‖zeroSumProjection ι‖ + 1)) := mul_le_mul_of_nonneg_left hd.le hp
      _ < ε := by
        have he : (‖zeroSumProjection ι‖+1) * (ε / (‖zeroSumProjection ι‖+1)) = ε :=
          mul_div_cancel₀ ε (by positivity)
        nlinarith
end
end

section
section
open Set MeasureTheory
open scoped Topology
section NullImage
variable {D T : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [FiniteDimensional ℝ T]
  [MeasurableSpace T] [BorelSpace T]
lemma differentiable_image_null_of_projection (μ : Measure T) [μ.IsAddHaarMeasure]
    (p : T →L[ℝ] D) (hp : Function.Surjective p) (hpn : ¬ Function.Injective p)
    {f : D → T} {S : Set D} (hf : ∀ x ∈ S, DifferentiableAt ℝ f x) : μ (f '' S) = 0 := by
  let g : T → T := fun x => f (p x)
  let g' : T → T →L[ℝ] T := fun x => (fderiv ℝ f (p x)).comp p
  have hd : ∀ x ∈ p ⁻¹' S, HasFDerivWithinAt g (g' x) (p ⁻¹' S) x := by
    intro x hx
    exact ((hf (p x) hx).hasFDerivAt.comp x p.hasFDerivAt).hasFDerivWithinAt
  have hdet : ∀ x ∈ p ⁻¹' S, (g' x).det = 0 := by
    intro x _
    change ((g' x).toLinearMap).det = 0
    apply LinearMap.det_eq_zero_iff_ker_ne_bot.mpr
    apply mt LinearMap.ker_eq_bot.mp
    intro hinj
    exact hpn (fun u v huv => hinj (by change fderiv ℝ f (p x) (p u) = fderiv ℝ f (p x) (p v); rw [huv]))
  have he : g '' (p ⁻¹' S) = f '' S := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨p x,hx,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      obtain ⟨z,rfl⟩ := hp x
      exact ⟨z,hx,rfl⟩
  rw [← he]
  exact addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ hd hdet
end NullImage
noncomputable def initialProjection (n m : ℕ) (h : n ≤ m) :
    Euc (Fin m) →L[ℝ] Euc (Fin n) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 (fun i => x (Fin.castLE h i))
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
lemma initialProjection_surjective (n m : ℕ) (h : n ≤ m) :
    Function.Surjective (initialProjection n m h) := by
  intro x
  refine ⟨WithLp.toLp 2 (fun j : Fin m => if h : j.val < n then x ⟨j.val,h⟩ else 0),?_⟩
  apply PiLp.ext
  intro i
  change (if hj : i.val < n then x ⟨i.val,hj⟩ else 0) = x i
  simp only [dif_pos i.isLt]
lemma initialProjection_not_injective (n m : ℕ) (h : n < m) :
    ¬ Function.Injective (initialProjection n m h.le) := by
  intro hh
  have hl := LinearMap.finrank_le_finrank_of_injective
    (f := (initialProjection n m h.le).toLinearMap) hh
  simp only [finrank_euclideanSpace_fin] at hl
  omega
lemma differentiable_image_null_of_dim_lt (n m : ℕ) (h : n < m)
    {f : Euc (Fin n) → Euc (Fin m)}
    {S : Set (Euc (Fin n))} (hf : ∀ x ∈ S, DifferentiableAt ℝ f x) :
    volume (f '' S) = 0 :=
  differentiable_image_null_of_projection volume (initialProjection n m h.le)
    (initialProjection_surjective n m h.le) (initialProjection_not_injective n m h) hf
end
end

section
section
open scoped BigOperators
open MeasureTheory Set
lemma finite_smooth_slice_misses (n m : ℕ) (hnm : n < m)
    {κ : Type*} [Fintype κ] (L : κ → Euc (Fin n) →L[ℝ] ℝ)
    (g : κ → Euc (Fin n) → Euc (Fin m))
    (hg : ∀ c, ContDiff ℝ (⊤ : ℕ∞) (g c))
    {V : Set (Euc (Fin m))} (hVo : IsOpen V) (hVn : V.Nonempty)
    (hVp : ∀ y ∈ V, ∀ i, 0 < y i) :
    ∃ z : Euc (Fin m), (∃ y ∈ V, z = (∑ i, y i)⁻¹ • y) ∧
      (∀ i, 0 < z i) ∧ (∑ i, z i) = 1 ∧
      ∀ c x, L c x = 1 → g c x ≠ z := by
  classical
  let C (c : κ) (x : Euc (Fin n)) := L c x • g c ((L c x)⁻¹ • x)
  have hCd (c : κ) : ∀ x ∈ {x | L c x ≠ 0}, DifferentiableAt ℝ (C c) x := by
    intro x hx
    exact (L c).differentiableAt.smul
      (((hg c).differentiable (by simp)).differentiableAt.comp x
        (((L c).differentiableAt.inv hx).smul differentiableAt_id))
  have hnull : volume (⋃ c : κ, C c '' {x | L c x ≠ 0}) = 0 := by
    exact measure_iUnion_null (fun c => differentiable_image_null_of_dim_lt n m hnm (hCd c))
  obtain ⟨y,hy,hym⟩ : ∃ y ∈ V, y ∉ ⋃ c : κ, C c '' {x | L c x ≠ 0} := by
    by_contra hn
    push Not at hn
    have hl : volume V ≤ volume (⋃ c : κ, C c '' {x | L c x ≠ 0}) := measure_mono hn
    rw [hnull] at hl
    exact hVo.measure_ne_zero volume hVn (le_antisymm hl (zero_le))
  let s : ℝ := ∑ i, y i
  have hs : 0 < s := Finset.sum_pos (fun i _ => hVp y hy i)
    (Finset.univ_nonempty_iff.mpr ⟨⟨0,by omega⟩⟩)
  let z : Euc (Fin m) := s⁻¹ • y
  refine ⟨z,⟨y,hy,rfl⟩,fun i => ?_,?_,?_⟩
  · change 0 < s⁻¹ * y i
    exact mul_pos (inv_pos.mpr hs) (hVp y hy i)
  · change (∑ i, s⁻¹ * y i) = 1
    rw [← Finset.mul_sum]
    exact inv_mul_cancel₀ (ne_of_gt hs)
  · intro c x hx he
    apply hym
    apply Set.mem_iUnion.mpr
    refine ⟨c,s • x,?_,?_⟩
    · simp only [Set.mem_ofPred_eq,map_smul,hx,smul_eq_mul,mul_one]
      exact ne_of_gt hs
    · simp only [C,map_smul,hx,smul_eq_mul,mul_one,inv_smul_smul₀ (ne_of_gt hs),he,z,
        smul_inv_smul₀ (ne_of_gt hs)]
end
end

section
section
open scoped BigOperators
lemma finite_smooth_slice_misses_bounded (n m : ℕ) (hnm : n < m)
    {κ : Type*} [Fintype κ] (L : κ → Euc (Fin n) →L[ℝ] ℝ)
    (g : κ → Euc (Fin n) → Euc (Fin m))
    (hg : ∀ c, ContDiff ℝ (⊤ : ℕ∞) (g c)) :
    ∃ z : Euc (Fin m), (∀ i, (2*(m:ℝ))⁻¹ < z i) ∧
      (∑ i, z i) = 1 ∧ ∀ c x, L c x = 1 → g c x ≠ z := by
  have hm : 0 < m := by omega
  let V : Set (Euc (Fin m)) := {y | ∀ i, 1 < y i ∧ y i < 2}
  have hVo : IsOpen V := by
    have he : V = ⋂ i, {y : Euc (Fin m) | 1 < y i ∧ y i < 2} := by
      ext y; simp [V]
    rw [he]
    exact isOpen_iInter_of_finite (fun i => (isOpen_lt continuous_const
      (PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) i)).inter
      (isOpen_lt (PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) i) continuous_const))
  have hVn : V.Nonempty := ⟨WithLp.toLp 2 (fun _ => (3/2:ℝ)),fun _ => by norm_num⟩
  obtain ⟨z,⟨y,hy,hz⟩,hp,hs,hmiss⟩ := finite_smooth_slice_misses n m hnm L g hg
    hVo hVn (fun y hy i => lt_trans zero_lt_one (hy i).1)
  have hmm : (0:ℝ) < m := Nat.cast_pos.mpr hm
  have hsum : 0 < ∑ i, y i := Finset.sum_pos (fun i _ => by linarith [(hy i).1])
    (Finset.univ_nonempty_iff.mpr ⟨⟨0,hm⟩⟩)
  have hbound : ∑ i, y i < 2*(m:ℝ) := by
    have hh := Finset.sum_lt_sum_of_nonempty (s := Finset.univ)
      (Finset.univ_nonempty_iff.mpr ⟨⟨0,hm⟩⟩) (fun i _ => (hy i).2)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_comm] using hh
  refine ⟨z,?_,hs,hmiss⟩
  intro i
  rw [hz]
  change (2*(m:ℝ))⁻¹ < (∑ i, y i)⁻¹ * y i
  have hinv : (2*(m:ℝ))⁻¹ < (∑ i, y i)⁻¹ := by
    exact (inv_lt_inv₀ (by positivity) hsum).mpr hbound
  exact hinv.trans (by nlinarith [(hy i).1,inv_pos.mpr hsum])
lemma finite_smooth_slice_misses_general {D ι κ : Type*}
    [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]
    [Fintype ι] [Fintype κ]
    (hd : Module.finrank ℝ D < Fintype.card ι)
    (L : κ → D →L[ℝ] ℝ) (g : κ → D → Euc ι)
    (hg : ∀ c, ContDiff ℝ (⊤ : ℕ∞) (g c)) :
    ∃ z : Euc ι, (∀ i, (2*(Fintype.card ι:ℝ))⁻¹ < z i) ∧
      (∑ i, z i) = 1 ∧ ∀ c x, L c x = 1 → g c x ≠ z := by
  let eD := (stdOrthonormalBasis ℝ D).repr
  let eY := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fintype.equivFin ι)
  let L' := fun c => (L c).comp eD.symm.toContinuousLinearEquiv.toContinuousLinearMap
  let g' := fun c x => eY (g c (eD.symm x))
  have hg' (c : κ) : ContDiff ℝ (⊤ : ℕ∞) (g' c) :=
    eY.toContinuousLinearEquiv.contDiff.comp ((hg c).comp eD.symm.toContinuousLinearEquiv.contDiff)
  obtain ⟨z,hp,hs,hm⟩ := finite_smooth_slice_misses_bounded _ _ hd L' g' hg'
  have heY (q : Euc (Fin (Fintype.card ι))) (i : ι) :
      (eY.symm q) i = q ((Fintype.equivFin ι) i) := by
    simp [eY, LinearIsometryEquiv.piLpCongrLeft_symm,
      LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']
  refine ⟨eY.symm z,?_,?_,?_⟩
  · intro i
    rw [heY]
    exact hp ((Fintype.equivFin ι) i)
  · simp only [heY]
    rw [Equiv.sum_comp]
    exact hs
  · intro c x hx he
    apply hm c (eD x)
    · simpa only [L',ContinuousLinearMap.comp_apply,LinearIsometryEquiv.coe_toContinuousLinearEquiv,
        ContinuousLinearEquiv.coe_coe,LinearIsometryEquiv.symm_apply_apply] using hx
    · change eY (g c (eD.symm (eD x))) = z
      rw [LinearIsometryEquiv.symm_apply_apply,he,LinearIsometryEquiv.apply_symm_apply]
end
end

section
section
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
open Set
section CenterApproximation
variable {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma matrixFibre_range {u : (Euc (Fin (k+1)))} (e : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc (Fin (k+1))))
    (he : ∀ v, ⟪u,v⟫ = 0 → ∃ x, e x = v) {Q : (SqMat (Fin (k+1)))} (hQ : Q ∈ matrixFibre u) :
    LinearMap.range (Matrix.toEuclideanLin Q) ≤ LinearMap.range e.toLinearMap := by
  rintro v ⟨b,rfl⟩
  obtain ⟨x,hx⟩ := he ((matrixOp (Fin (k+1))) Q b) (matrix_image_orthogonal_kernel hQ.1.isSelfAdjoint hQ.2.2 b)
  exact ⟨x,hx⟩
lemma matrixCompress_mem_slice {u : (Euc (Fin (k+1)))} (e : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc (Fin (k+1))))
    (he : ∀ v, ⟪u,v⟫ = 0 → ∃ x, e x = v) {Q : (SqMat (Fin (k+1)))} (hQ : Q ∈ matrixFibre u) :
    0 ≤ matrixCompress e Q ∧ Matrix.trace (matrixCompress e Q) = 1 :=
  ⟨matrixCompress_nonneg e hQ.1,
    (matrixCompress_trace e hQ.1.isSelfAdjoint (matrixFibre_range e he hQ)).trans hQ.2.1⟩
lemma Admissible.center_approximation {f : (Euc (Fin (k+1))) → ι → ℝ} (hf : Admissible f)
    {I : Finset ι} [Nonempty ↥(Iᶜ : Finset ι)] {c : (Euc (Fin (k+1)))}
    (hc : c ∈ safeNormals (activeVectors f I)) (e : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc (Fin (k+1))))
    (he : ∀ x, ⟪c,e x⟫ = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : (Euc (UpperTriangle (Fin k))) → Euc ↥(Iᶜ : Finset ι), ContDiff ℝ (⊤ : ℕ∞) a ∧
      (∀ x, ∑ i, a x i = 1) ∧
      ∀ x, 0 ≤ symmetricCoordinates x → Matrix.trace (symmetricCoordinates x) = 1 →
        ‖a x - negativeCoordinates f I (matrixEmbed e (symmetricCoordinates x))‖ < ε := by
  let g : (Euc (UpperTriangle (Fin k))) → Euc ↥(Iᶜ : Finset ι) :=
    fun x => negativeCoordinates f I (matrixEmbed e ((symmetricCoordinates x)⁺))
  have hP : Continuous (fun x : (Euc (UpperTriangle (Fin k))) => (symmetricCoordinates x)⁺) :=
    matrix_posPart_continuousOn.comp_continuous symmetricCoordinates.continuous_of_finiteDimensional
      (fun x => symmetricCoordinates_selfAdjoint x)
  have hg : Continuous g :=
    (hf.negativeCoordinates_continuousOn I).comp_continuous
      ((matrixEmbed e).continuous_of_finiteDimensional.comp hP)
      (fun x => matrixEmbed_nonneg e (CFC.posPart_nonneg _))
  let K : Set (Euc (UpperTriangle (Fin k))) := {x | 0 ≤ symmetricCoordinates x ∧ Matrix.trace (symmetricCoordinates x) = 1}
  have hs : ∀ x ∈ K, coordinateSum (g x) = 1 := by
    intro x hx
    change ∑ i, negativeCoordinates f I (matrixEmbed e ((symmetricCoordinates x)⁺)) i = 1
    rw [(CFC.posPart_eq_self _).mpr hx.1]
    apply hf.negativeCoordinates_sum hc
    exact ⟨matrixEmbed_nonneg _ hx.1,(matrixEmbed_trace _ _).trans hx.2,matrixEmbed_kernel e _ he⟩
  obtain ⟨a,ha,has,hae⟩ := continuous_simplex_approx g hg hs hε
  refine ⟨a,ha,has,?_⟩
  intro x hx ht
  have hh := hae x ⟨hx,ht⟩
  simpa only [g,(CFC.posPart_eq_self _).mpr hx] using hh
lemma Admissible.finite_center_approximations {κ : Type*} [Fintype κ]
    {f : (Euc (Fin (k+1))) → ι → ℝ} (hf : Admissible f) {I : Finset ι}
    (hd : Fintype.card (UpperTriangle (Fin k)) < Fintype.card ↥(Iᶜ : Finset ι))
    (c : κ → (Euc (Fin (k+1)))) (hc : ∀ j, c j ∈ safeNormals (activeVectors f I)) (hcn : ∀ j, ‖c j‖ = 1) :
    ∃ z : Euc ↥(Iᶜ : Finset ι), (∀ i, (2*(Fintype.card ↥(Iᶜ : Finset ι):ℝ))⁻¹ < z i) ∧
      (∑ i, z i) = 1 ∧
      ∃ g : κ → (SqMat (Fin (k+1))) → Euc ↥(Iᶜ : Finset ι), (∀ j, Continuous (g j)) ∧
        (∀ j, ∀ Q ∈ matrixFibre (c j), (∑ i, g j Q i) = 1) ∧
        (∀ j, ∀ Q ∈ matrixFibre (c j), ‖g j Q - negativeCoordinates f I Q‖ <
          (2*(Fintype.card ↥(Iᶜ : Finset ι):ℝ))⁻¹) ∧
        (∀ j, ∀ Q ∈ matrixFibre (c j), g j Q ≠ z) := by
  have hj : 0 < Fintype.card ↥(Iᶜ : Finset ι) := lt_of_le_of_lt (Nat.zero_le _) hd
  let : Nonempty ↥(Iᶜ : Finset ι) := Fintype.card_pos_iff.mp hj
  let ε : ℝ := (2*(Fintype.card ↥(Iᶜ : Finset ι):ℝ))⁻¹
  have hε : 0 < ε := by dsimp [ε]; positivity
  choose e he hes using (fun j => orthogonal_frame k (hcn j))
  choose a ha has hae using (fun j => hf.center_approximation (hc j) (e j) (he j) hε)
  let L : (Euc (UpperTriangle (Fin k))) →L[ℝ] ℝ := (Matrix.traceLinearMap (Fin k) ℝ ℝ).toContinuousLinearMap.comp
    (symmetricCoordinates (ν := Fin k)).toContinuousLinearMap
  have hendim : Module.finrank ℝ (Euc (UpperTriangle (Fin k))) < Fintype.card ↥(Iᶜ : Finset ι) := by simpa using hd
  obtain ⟨z,hzp,hzs,hzm⟩ := finite_smooth_slice_misses_general hendim (fun _ : κ => L) a ha
  let g : κ → (SqMat (Fin (k+1))) → Euc ↥(Iᶜ : Finset ι) :=
    fun j Q => a j (symmetricEntries (matrixCompress (e j) Q))
  refine ⟨z,hzp,hzs,g,?_,?_,?_,?_⟩
  · intro j
    exact (ha j).continuous.comp (symmetricEntries.continuous_of_finiteDimensional.comp
      (matrixCompress (e j)).continuous_of_finiteDimensional)
  · intro j Q hQ
    exact has j _
  · intro j Q hQ
    have hCQ := matrixCompress_mem_slice (e j) (hes j) hQ
    have hSC := symmetricCoordinates_entries hCQ.1.isSelfAdjoint
    have hEQ := matrixEmbed_compress (e j) hQ.1.isSelfAdjoint (matrixFibre_range (e j) (hes j) hQ)
    have hh := hae j (symmetricEntries (matrixCompress (e j) Q))
      (by rw [hSC]; exact hCQ.1) (by rw [hSC]; exact hCQ.2)
    simpa only [hSC,hEQ,g,ε] using hh
  · intro j Q hQ
    apply hzm j _
    change Matrix.trace (symmetricCoordinates (symmetricEntries (matrixCompress (e j) Q))) = 1
    have hCQ := matrixCompress_mem_slice (e j) (hes j) hQ
    rw [symmetricCoordinates_entries hCQ.1.isSelfAdjoint]
    exact hCQ.2
end CenterApproximation
end
end

section
section
open scoped RealInnerProductSpace
open Set
section Purity
variable {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma Admissible.maximal_support_complement_bound {f : (Euc (Fin (k+1))) → ι → ℝ} (hf : Admissible f)
    (hdim : Fintype.card (UpperTriangle (Fin (k+1))) = Fintype.card ι)
    (hn : 1 < Fintype.card ι) {w : (Euc (Fin (k+1)))} (hw : ‖w‖ = 1)
    (hmax : ∀ u : (Euc (Fin (k+1))), ‖u‖ = 1 → positiveSupport f w ⊆ positiveSupport f u →
      positiveSupport f u = positiveSupport f w) :
    Fintype.card ↥((positiveSupport f w)ᶜ : Finset ι) ≤ Fintype.card (UpperTriangle (Fin k)) := by
  classical
  by_contra hb
  have hd : Fintype.card (UpperTriangle (Fin k)) <
      Fintype.card ↥((positiveSupport f w)ᶜ : Finset ι) := lt_of_not_ge hb
  let I := positiveSupport f w
  have hI : I.Nonempty := hf.support_nonempty hw
  have hr : ∀ i ∈ I, 0 < f w i := fun i hi => (mem_positiveSupport f w i).mp hi
  have hro : ∀ i ∉ I, f w i = 0 := by
    intro i hi
    exact le_antisymm (not_lt.mp (fun hp => hi ((mem_positiveSupport f w i).mpr hp))) (hf.nonneg w hw i)
  obtain ⟨C,hCK,hCD,hcover⟩ := compact_disjoint_chambers (hf.orientedLevel_compact w (f w))
    (fun u hu => hf.commonPositiveCone_interior_safe I (orientedLevel_cone hr hu))
  let c : ↥C → (Euc (Fin (k+1))) := Subtype.val
  have hc : ∀ j, c j ∈ commonPositiveCone f I := fun j => orientedLevel_cone hr (hCK j.property)
  have hcn : ∀ j, ‖c j‖ = 1 := fun j => (hCK j.property).1
  obtain ⟨z,hz,hzs,g,hg,hgs,hge,hgm⟩ := hf.finite_center_approximations hd c
    (fun j => hf.commonPositiveCone_safe I (hc j)) hcn
  have hj : 0 < Fintype.card ↥(Iᶜ : Finset ι) := lt_of_le_of_lt (Nat.zero_le _) hd
  let : Nonempty ↥(Iᶜ : Finset ι) := Fintype.card_pos_iff.mp hj
  have hε : 0 < (2*(Fintype.card ↥(Iᶜ : Finset ι):ℝ))⁻¹ := by positivity
  exact hf.chart_surgery_impossible hdim hn hI hmax hw hr hr hro (hf.sum_one w hw)
    c hc hcn hCD hcover hε g hg hgs hge z hz hzs hgm
end Purity
end
section
open scoped RealInnerProductSpace
section PureFacets
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype ι] [DecidableEq ι]
omit [InnerProductSpace ℝ E] [DecidableEq ι] in
lemma exists_maximal_support (f : E → ι → ℝ) {w : E} (hw : ‖w‖ = 1) :
    ∃ u, ‖u‖ = 1 ∧ positiveSupport f w ⊆ positiveSupport f u ∧
      ∀ v, ‖v‖ = 1 → positiveSupport f u ⊆ positiveSupport f v →
        positiveSupport f v = positiveSupport f u := by
  classical
  let S : Set (Finset ι) := {s | ∃ u, ‖u‖ = 1 ∧ positiveSupport f w ⊆ s ∧ positiveSupport f u = s}
  obtain ⟨s,hs,hm⟩ := (Set.toFinite S).exists_maximal (show S.Nonempty from ⟨_,w,hw,Finset.Subset.rfl,rfl⟩)
  obtain ⟨u,hu,hwu,rfl⟩ := hs
  refine ⟨u,hu,hwu,?_⟩
  intro v hv huv
  exact le_antisymm (hm ⟨v,hv,hwu.trans huv,rfl⟩ huv) huv
end PureFacets
lemma Admissible.maximal_support_card_four {f : Vector4 → Fin 10 → ℝ} (hf : Admissible f)
    {w : Vector4} (hw : ‖w‖ = 1)
    (hm : ∀ u, ‖u‖ = 1 → positiveSupport f w ⊆ positiveSupport f u →
      positiveSupport f u = positiveSupport f w) : (positiveSupport f w).card = 4 := by
  have hl := hf.support_card_four_le hw
  have hb := hf.maximal_support_complement_bound (k := 3) (by decide) (by decide) hw hm
  have hc : Fintype.card (UpperTriangle (Fin 3)) = 6 := by decide
  rw [Fintype.card_coe,Finset.card_compl,Fintype.card_fin,hc] at hb
  omega
lemma Admissible.support_extends_four {f : Vector4 → Fin 10 → ℝ} (hf : Admissible f)
    {w : Vector4} (hw : ‖w‖ = 1) :
    ∃ u, ‖u‖ = 1 ∧ positiveSupport f w ⊆ positiveSupport f u ∧ (positiveSupport f u).card = 4 := by
  obtain ⟨u,hu,hwu,hm⟩ := exists_maximal_support f hw
  exact ⟨u,hu,hwu,hf.maximal_support_card_four hu hm⟩
end
open Set MeasureTheory
end

section
open Set MeasureTheory
section
open scoped RealInnerProductSpace
open SimplicialChains
section HemisphereChart
variable {E W : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
variable (w : E) (e : W →ₗᵢ[ℝ] E)
noncomputable def hemisphereChart (v : W) : E := unitRadial (w + e v)
noncomputable def hemisphereInverse (u : E) : W := ⟪w,u⟫⁻¹ • e.toContinuousLinearMap.adjoint u
lemma adjoint_isometry_apply (v : W) : e.toContinuousLinearMap.adjoint (e v) = v := by
  have hh := congrArg (fun T : W →L[ℝ] W => T v) e.adjoint_comp_self
  exact hh
lemma adjoint_normal (he : ∀ v, ⟪w,e v⟫ = 0) : e.toContinuousLinearMap.adjoint w = 0 := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_zero_left,ContinuousLinearMap.adjoint_inner_left]
  exact he v
lemma frame_decomposition (hw : ‖w‖ = 1)
    (he : ∀ v, ⟪w,e v⟫ = 0) (hes : ∀ u, ⟪w,u⟫ = 0 → ∃ v, e v = u) (u : E) :
    e (e.toContinuousLinearMap.adjoint u) = u - ⟪w,u⟫ • w := by
  obtain ⟨v,hv⟩ := hes (u - ⟪w,u⟫ • w) (by simp [inner_sub_right,inner_smul_right,hw])
  have ha := congrArg e.toContinuousLinearMap.adjoint hv
  rw [adjoint_isometry_apply,map_sub,map_smul,adjoint_normal w e he,smul_zero,sub_zero] at ha
  rw [← ha,hv]
omit [CompleteSpace E] [CompleteSpace W] in
lemma hemisphere_add_ne_zero (hw : ‖w‖ = 1) (he : ∀ v, ⟪w,e v⟫ = 0) (v : W) :
    w + e v ≠ 0 := by
  intro hz
  have h := congrArg (fun u => ⟪w,u⟫) hz
  simp [inner_add_right,he,hw] at h
omit [CompleteSpace E] [CompleteSpace W] in
lemma hemisphereChart_contDiff (hw : ‖w‖ = 1) (he : ∀ v, ⟪w,e v⟫ = 0) :
    ContDiff ℝ (⊤ : ℕ∞) (hemisphereChart w e) := by
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun v => w + e v) := contDiff_const.add e.contDiff
  exact (hc.norm ℝ (hemisphere_add_ne_zero w e hw he)).inv
    (fun v => norm_ne_zero_iff.mpr (hemisphere_add_ne_zero w e hw he v)) |>.smul hc
omit [CompleteSpace E] [CompleteSpace W] in
lemma hemisphereChart_norm (hw : ‖w‖ = 1) (he : ∀ v, ⟪w,e v⟫ = 0) (v : W) :
    ‖hemisphereChart w e v‖ = 1 := unitRadial_norm (hemisphere_add_ne_zero w e hw he v)
lemma hemisphereInverse_chart (hw : ‖w‖ = 1) (he : ∀ v, ⟪w,e v⟫ = 0) (v : W) :
    hemisphereInverse w e (hemisphereChart w e v) = v := by
  have hn : ‖w + e v‖ ≠ 0 := norm_ne_zero_iff.mpr (hemisphere_add_ne_zero w e hw he v)
  simp only [hemisphereInverse,hemisphereChart,unitRadial,inner_smul_right,inner_add_right,
    real_inner_self_eq_norm_sq,hw,one_pow,he,add_zero,mul_one,inv_inv,map_smul,map_add,
    adjoint_normal w e he,adjoint_isometry_apply,zero_add,smul_smul,mul_inv_cancel₀ hn,one_smul]
lemma hemisphereChart_inverse (hw : ‖w‖ = 1) (he : ∀ v, ⟪w,e v⟫ = 0)
    (hes : ∀ u, ⟪w,u⟫ = 0 → ∃ v, e v = u) {u : E} (hu : ‖u‖ = 1) (hwu : 0 < ⟪w,u⟫) :
    hemisphereChart w e (hemisphereInverse w e u) = u := by
  have heq : w + e (hemisphereInverse w e u) = ⟪w,u⟫⁻¹ • u := by
    rw [hemisphereInverse,map_smul,frame_decomposition w e hw he hes,smul_sub,smul_smul,
      inv_mul_cancel₀ (ne_of_gt hwu),one_smul]
    abel
  rw [hemisphereChart,heq,unitRadial,norm_smul,Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hwu),hu,mul_one,inv_inv,smul_smul,
    mul_inv_cancel₀ (ne_of_gt hwu),one_smul]
lemma hemisphereInverse_continuousOn :
    ContinuousOn (hemisphereInverse w e) {u | 0 < ⟪w,u⟫} :=
  ((continuous_const.inner continuous_id).continuousOn.inv₀ (fun _ h => ne_of_gt h)).smul
    e.toContinuousLinearMap.adjoint.continuous.continuousOn
end HemisphereChart
end
end

section
open Set MeasureTheory
section
open scoped RealInnerProductSpace Topology
open Filter Set
section NegativeQuadratic
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace X]
def NegativeQuadratic (B : E →L[ℝ] E) : Prop := ∀ v, v ≠ 0 → ⟪v,B v⟫ < 0
omit [FiniteDimensional ℝ E] in
lemma negativeQuadratic_of_unit (B : E →L[ℝ] E)
    (h : ∀ v, ‖v‖ = 1 → ⟪v,B v⟫ < 0) : NegativeQuadratic B := by
  intro v hv
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hh := h (‖v‖⁻¹ • v) (by simp [norm_smul,norm_inv,hv])
  rw [map_smul,real_inner_smul_left,real_inner_smul_right] at hh
  by_contra hge
  exact not_lt_of_ge (mul_nonneg (inv_nonneg.mpr hn.le)
    (mul_nonneg (inv_nonneg.mpr hn.le) (le_of_not_gt hge))) hh
lemma negativeQuadratic_isOpen (B : X → E →L[ℝ] E) (hB : Continuous B) :
    IsOpen {x | NegativeQuadratic (B x)} := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  have hcont : Continuous (fun p : X × E => ⟪p.2,B p.1 p.2⟫) :=
    continuous_snd.inner ((hB.comp continuous_fst).clm_apply continuous_snd)
  have hev := (isCompact_sphere (0:E) 1).eventually_forall_of_forall_eventually
    (P := fun y v => ⟪v,B y v⟫ < 0) (x₀ := x) (fun v hv =>
      hcont.continuousAt.eventually_lt continuousAt_const
        (hx v (fun he => by simp [he] at hv)))
  filter_upwards [hev] with y hy
  exact negativeQuadratic_of_unit (B y) (fun v hv => hy v (by simpa using hv))
omit [FiniteDimensional ℝ E] in
lemma negativeQuadratic_pos_sub {B : E →L[ℝ] E} (hB : NegativeQuadratic B)
    {v : E} (hv : v ≠ 0) {lam : ℝ} (hl : 0 < lam) : 0 < ⟪v,lam • v - B v⟫ := by
  rw [inner_sub_right,real_inner_smul_right,real_inner_self_eq_norm_sq]
  exact sub_pos.mpr ((hB v hv).trans_le (mul_nonneg hl.le (sq_nonneg _)))
end NegativeQuadratic
end
section
open scoped Matrix RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
section MatrixBlocks
variable {μ ν : Type*} [Fintype μ] [Fintype ν] [DecidableEq μ] [DecidableEq ν]
omit [DecidableEq ν] in
lemma matrixEmbed_selfAdjoint (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) {B : SqMat μ} (hB : IsSelfAdjoint B) :
    IsSelfAdjoint (matrixEmbed e B) := by
  change ((isometryMatrix e) * B * (isometryMatrix e)ᴴ)ᴴ = _
  simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]
  rw [show Bᴴ = B from hB.star_eq]
  exact (Matrix.mul_assoc _ _ _).symm
omit [DecidableEq ν] in
lemma matrixCompress_selfAdjoint (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) {A : (SqMat ν)} (hA : IsSelfAdjoint A) :
    IsSelfAdjoint (matrixCompress e A) := by
  change ((isometryMatrix e)ᴴ * A * (isometryMatrix e))ᴴ = _
  simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]
  rw [show Aᴴ = A from hA.star_eq]
  exact (Matrix.mul_assoc _ _ _).symm
lemma matrixCompress_embed (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) (B : SqMat μ) :
    matrixCompress e (matrixEmbed e B) = B := by
  change (isometryMatrix e)ᴴ * (isometryMatrix e * B * (isometryMatrix e)ᴴ) * isometryMatrix e = B
  calc
    _ = ((isometryMatrix e)ᴴ * isometryMatrix e) * B * ((isometryMatrix e)ᴴ * isometryMatrix e) := by
      simp only [Matrix.mul_assoc]
    _ = B := by rw [isometryMatrix_star_mul,Matrix.one_mul,Matrix.mul_one]
lemma isometryMatrix_star_action (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) (v : (Euc ν)) :
    Matrix.toEuclideanLin (isometryMatrix e)ᴴ v = e.toContinuousLinearMap.adjoint v := by
  apply ext_inner_left ℝ
  intro x
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  change ⟪x,(Matrix.toEuclideanLin (isometryMatrix e)).adjoint v⟫ = _
  rw [LinearMap.adjoint_inner_right,isometryMatrix_action,ContinuousLinearMap.adjoint_inner_right]
  rfl
lemma matrixCompress_action (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) (A : (SqMat ν)) (v : (Euc μ)) :
    (Matrix.toEuclideanCLM (𝕜 := ℝ)) (matrixCompress e A) v = e.toContinuousLinearMap.adjoint ((Matrix.toEuclideanCLM (𝕜 := ℝ)) A (e v)) := by
  change Matrix.toEuclideanLin ((isometryMatrix e)ᴴ * A * isometryMatrix e) v = _
  rw [toEuclideanLin_mul,toEuclideanLin_mul]
  change Matrix.toEuclideanLin (isometryMatrix e)ᴴ (Matrix.toEuclideanLin A
    (Matrix.toEuclideanLin (isometryMatrix e) v)) = _
  rw [isometryMatrix_action,isometryMatrix_star_action]
  rfl
noncomputable def blockScalar (c : (Euc ν)) (A : (SqMat ν)) : ℝ := ⟪c,(Matrix.toEuclideanCLM (𝕜 := ℝ)) A c⟫
noncomputable def blockOff (c : (Euc ν)) (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) (A : (SqMat ν)) : (Euc μ) := e.toContinuousLinearMap.adjoint ((Matrix.toEuclideanCLM (𝕜 := ℝ)) A c)
noncomputable def blockCorner (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) (A : (SqMat ν)) : (SqMat ν) := matrixEmbed e (matrixCompress e A)
omit [DecidableEq ν] in
lemma blockCorner_selfAdjoint (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) {A : (SqMat ν)} (hA : IsSelfAdjoint A) :
    IsSelfAdjoint (blockCorner e A) := matrixEmbed_selfAdjoint e (matrixCompress_selfAdjoint e hA)
lemma blockCorner_kernel (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) {c : (Euc ν)} (he : ∀ v, ⟪c,e v⟫ = 0) (A : (SqMat ν)) :
    (Matrix.toEuclideanCLM (𝕜 := ℝ)) (blockCorner e A) c = 0 := matrixEmbed_kernel e _ he
lemma blockCorner_of_kernel (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) {c : (Euc ν)}
    (hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u) {A : (SqMat ν)} (hA : IsSelfAdjoint A) (hAc : (Matrix.toEuclideanCLM (𝕜 := ℝ)) A c = 0) :
    blockCorner e A = A := by
  apply matrixEmbed_compress e hA
  rintro _ ⟨x,rfl⟩
  exact hes _ (matrix_image_orthogonal_kernel hA hAc x)
lemma block_data_zero (c : (Euc ν)) (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) (hc : ‖c‖ = 1)
    (he : ∀ v, ⟪c,e v⟫ = 0) (hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u)
    {A : (SqMat ν)} (hA : IsSelfAdjoint A) (ha : blockScalar c A = 0)
    (hb : blockOff c e A = 0) (hC : blockCorner e A = 0) : A = 0 := by
  have hAc : (Matrix.toEuclideanCLM (𝕜 := ℝ)) A c = 0 := by
    have hd := frame_decomposition c e hc he hes ((Matrix.toEuclideanCLM (𝕜 := ℝ)) A c)
    change e (blockOff c e A) = (Matrix.toEuclideanCLM (𝕜 := ℝ)) A c - blockScalar c A • c at hd
    simpa only [hb,ha,map_zero,zero_smul,sub_zero] using hd.symm
  rw [blockCorner_of_kernel e hes hA hAc] at hC
  exact hC
lemma blockScalar_continuous (c : (Euc ν)) : Continuous (blockScalar c : (SqMat ν) → ℝ) :=
  continuous_const.inner (((matrixOp ν).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional).clm_apply continuous_const)
omit [DecidableEq μ] in
lemma blockOff_continuous (c : (Euc ν)) (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) : Continuous (blockOff c e : (SqMat ν) → (Euc μ)) :=
  e.toContinuousLinearMap.adjoint.continuous.comp
    (((matrixOp ν).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional).clm_apply continuous_const)
omit [DecidableEq ν] in
lemma blockCorner_continuous (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) : Continuous (blockCorner e : (SqMat ν) → (SqMat ν)) :=
  (matrixEmbed e).continuous_of_finiteDimensional.comp (matrixCompress e).continuous_of_finiteDimensional
lemma blockOff_eigenvector {c u : (Euc ν)} (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) (hc : ‖c‖ = 1)
    (he : ∀ v, ⟪c,e v⟫ = 0) (hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u)
    {A : (SqMat ν)} {lam : ℝ} (_hu : ‖u‖ = 1) (hcu : 0 < ⟪c,u⟫) (hAu : (Matrix.toEuclideanCLM (𝕜 := ℝ)) A u = lam • u) :
    blockOff c e A = lam • hemisphereInverse c e u - (Matrix.toEuclideanCLM (𝕜 := ℝ)) (matrixCompress e A) (hemisphereInverse c e u) := by
  let v := hemisphereInverse c e u
  have heq : c + e v = ⟪c,u⟫⁻¹ • u := by
    rw [show v = hemisphereInverse c e u from rfl,hemisphereInverse,map_smul,
      frame_decomposition c e hc he hes,smul_sub,smul_smul,inv_mul_cancel₀ (ne_of_gt hcu),one_smul]
    abel
  have hae : (Matrix.toEuclideanCLM (𝕜 := ℝ)) A (c + e v) = lam • (c + e v) := by
    rw [heq,map_smul,hAu,smul_comm]
  have hb := congrArg e.toContinuousLinearMap.adjoint hae
  rw [map_add,map_add,map_smul,map_add,adjoint_normal c e he,zero_add] at hb
  rw [adjoint_isometry_apply,← matrixCompress_action] at hb
  exact eq_sub_iff_add_eq.mpr hb
end MatrixBlocks
end
end

section
open Set MeasureTheory
section
open scoped BigOperators
section FacetTangent
variable {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
noncomputable def facetTangent {I : Finset ι} (a : Fin (k+1) ≃ ↥I) : (Euc (Fin k)) →ₗ[ℝ] (ι → ℝ) where
  toFun v i := if hi : i ∈ I then Fin.cases (-∑ j, v j) (fun j => v j) (a.symm ⟨i,hi⟩) else 0
  map_add' x y := by
    ext i
    dsimp
    split_ifs with hi
    · generalize a.symm ⟨i,hi⟩ = j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp [Finset.sum_add_distrib]; ring
      · rfl
    · simp
  map_smul' t x := by
    ext i
    dsimp
    split_ifs with hi
    · generalize a.symm ⟨i,hi⟩ = j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp [Finset.mul_sum]
      · rfl
    · simp
omit [Fintype ι] in
lemma facetTangent_apply {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (v : (Euc (Fin k))) (j : Fin (k+1)) :
    facetTangent a v (a j).val = Fin.cases (-∑ j, v j) (fun j => v j) j := by
  simp [facetTangent]
omit [Fintype ι] in
lemma facetTangent_zero_outside {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (v : (Euc (Fin k))) {i : ι} (hi : i ∉ I) :
    facetTangent a v i = 0 := by simp [facetTangent,hi]
omit [Fintype ι] in
lemma facetTangent_sum {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (v : (Euc (Fin k))) : ∑ i ∈ I, facetTangent a v i = 0 := by
  calc
    _ = ∑ i : ↥I, facetTangent a v i.val := (Finset.sum_coe_sort I _).symm
    _ = ∑ j : Fin (k+1), facetTangent a v (a j).val := (Equiv.sum_comp a _).symm
    _ = 0 := by simp only [facetTangent_apply,Fin.sum_univ_succ,Fin.cases_zero,Fin.cases_succ]; ring
omit [Fintype ι] in
lemma facetTangent_injective {I : Finset ι} (a : Fin (k+1) ≃ ↥I) : Function.Injective (facetTangent a) := by
  intro x y h
  ext j
  have hh := congrFun h (a j.succ).val
  simpa only [facetTangent_apply,Fin.cases_succ] using hh
end FacetTangent
end
end

section
open Set MeasureTheory
section
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
section LocalModel
variable {k : ℕ} {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι] in
lemma Admissible.signedExtension_kernel_coordinate {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {A : (SqMat ν)} (hA : IsSelfAdjoint A) {c : (Euc ν)} (hc : ‖c‖ = 1) (hAc : (matrixOp ν) A c = 0)
    {i : ι} (hi : 0 < f c i) : signedExtension f A i = 0 := by
  obtain ⟨hp,hn⟩ := matrix_parts_kernel hA hAc
  simp only [signedExtension,Pi.sub_apply,
    hf.positiveExtension_kernel (CFC.posPart_nonneg A) hc hp hi,
    hf.positiveExtension_kernel (CFC.negPart_nonneg A) hc hn hi,sub_self]
noncomputable def localBlockModel (f : (Euc ν) → ι → ℝ) (c : (Euc ν)) (e : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc ν))
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (D : (Euc (Fin k)) ≃L[ℝ] (Euc (Fin k))) (A : (SqMat ν)) : ι → ℝ :=
  blockScalar c A • f c + facetTangent a (D (blockOff c e A)) + signedExtension f (blockCorner e A)
omit [Nonempty ν] [Fintype ι] in
lemma localBlockModel_odd (f : (Euc ν) → ι → ℝ) (c : (Euc ν)) (e : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc ν))
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (D : (Euc (Fin k)) ≃L[ℝ] (Euc (Fin k))) (A : (SqMat ν)) :
    localBlockModel f c e a D (-A) = -localBlockModel f c e a D A := by
  simp only [localBlockModel,blockScalar,blockOff,blockCorner,map_neg,neg_apply,inner_neg_right,neg_smul,
    signedExtension_odd,neg_add_rev]
  abel
lemma Admissible.localBlockModel_continuousOn {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    (c : (Euc ν)) (e : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc ν)) {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (D : (Euc (Fin k)) ≃L[ℝ] (Euc (Fin k))) :
    ContinuousOn (localBlockModel f c e a D) {A : (SqMat ν) | IsSelfAdjoint A} := by
  apply ContinuousOn.add
  · exact ((blockScalar_continuous c).smul continuous_const).continuousOn.add
      ((facetTangent a).continuous_of_finiteDimensional.comp
        (D.continuous.comp (blockOff_continuous c e))).continuousOn
  · exact hf.signedExtension_continuousOn.comp (blockCorner_continuous e).continuousOn
      (fun A hA => blockCorner_selfAdjoint e hA)
lemma Admissible.localBlockModel_on_facet {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {c : (Euc ν)} (hc : ‖c‖ = 1) (e : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc ν)) (he : ∀ v, ⟪c,e v⟫ = 0)
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (hI : ∀ i ∈ I, 0 < f c i)
    (D : (Euc (Fin k)) ≃L[ℝ] (Euc (Fin k))) {A : (SqMat ν)} (hA : IsSelfAdjoint A) {i : ι} (hi : i ∈ I) :
    localBlockModel f c e a D A i = blockScalar c A * f c i + facetTangent a (D (blockOff c e A)) i := by
  have hz := hf.signedExtension_kernel_coordinate (blockCorner_selfAdjoint e hA) hc
    (blockCorner_kernel e he A) (hI i hi)
  simp only [localBlockModel,Pi.add_apply,Pi.smul_apply,smul_eq_mul,hz,add_zero]
lemma Admissible.localBlockModel_sum_facet {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {c : (Euc ν)} (hc : ‖c‖ = 1) (e : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc ν)) (he : ∀ v, ⟪c,e v⟫ = 0)
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (hIc : positiveSupport f c = I)
    (D : (Euc (Fin k)) ≃L[ℝ] (Euc (Fin k))) {A : (SqMat ν)} (hA : IsSelfAdjoint A) :
    ∑ i ∈ I, localBlockModel f c e a D A i = blockScalar c A := by
  have hp : ∀ i ∈ I, 0 < f c i := fun i hi => (mem_positiveSupport f c i).mp (hIc.symm ▸ hi)
  have hs : ∑ i ∈ I, f c i = 1 := by
    rw [← hf.sum_one c hc]
    apply Finset.sum_subset (Finset.subset_univ I)
    intro i _ hi
    apply le_antisymm _ (hf.nonneg c hc i)
    exact le_of_not_gt (fun h => hi (hIc ▸ (mem_positiveSupport f c i).mpr h))
  calc
    _ = ∑ i ∈ I, (blockScalar c A * f c i + facetTangent a (D (blockOff c e A)) i) :=
      Finset.sum_congr rfl (fun i hi => hf.localBlockModel_on_facet hc e he a hp D hA hi)
    _ = _ := by rw [Finset.sum_add_distrib,← Finset.mul_sum,hs,facetTangent_sum,mul_one,add_zero]
lemma Admissible.localBlockModel_ne_zero {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {c : (Euc ν)} (hc : ‖c‖ = 1) (e : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc ν)) (he : ∀ v, ⟪c,e v⟫ = 0)
    (hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u)
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (hIc : positiveSupport f c = I)
    (D : (Euc (Fin k)) ≃L[ℝ] (Euc (Fin k))) {A : (SqMat ν)} (hA : IsSelfAdjoint A) (hAz : A ≠ 0) :
    localBlockModel f c e a D A ≠ 0 := by
  intro hz
  have ha : blockScalar c A = 0 := by
    rw [← hf.localBlockModel_sum_facet hc e he a hIc D hA,hz]
    simp
  have hb : blockOff c e A = 0 := by
    apply D.injective
    apply (facetTangent_injective a)
    rw [map_zero,map_zero]
    ext i
    by_cases hi : i ∈ I
    · have hp : ∀ j ∈ I, 0 < f c j := fun j hj => (mem_positiveSupport f c j).mp (hIc.symm ▸ hj)
      have hh := hf.localBlockModel_on_facet hc e he a hp D hA hi
      rw [hz,ha] at hh
      simpa using hh.symm
    · exact facetTangent_zero_outside a _ hi
  have hC : blockCorner e A = 0 := by
    apply (hf.signedExtension_eq_zero_iff (blockCorner_selfAdjoint e hA)).mp
    simpa only [localBlockModel,ha,hb,zero_smul,map_zero,zero_add] using hz
  exact hAz (block_data_zero c e hc he hes hA ha hb hC)
end LocalModel
end
end

section
open Set MeasureTheory
section
open scoped MatrixOrder RealInnerProductSpace Matrix.Norms.L2Operator
section BlockParts
variable {μ ν ι : Type*} [Fintype μ] [Fintype ν] [DecidableEq μ] [DecidableEq ν]
  [Nonempty ν] [Fintype ι]
omit [Nonempty ν] in
lemma matrixCompress_rankOne (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) {c : (Euc ν)} (he : ∀ v, ⟪c,e v⟫ = 0) :
    matrixCompress e (rankOne c) = 0 := by
  apply (matrixOp μ).injective
  apply ContinuousLinearMap.ext
  intro v
  change (Matrix.toEuclideanCLM (𝕜 := ℝ)) (matrixCompress e (rankOne c)) v = (Matrix.toEuclideanCLM (𝕜 := ℝ)) (0 : SqMat μ) v
  rw [matrixCompress_action,rankOne_action,he,zero_smul,map_zero,map_zero,
    zero_apply]
omit [Nonempty ν] in
lemma block_decomposition {c : (Euc ν)} (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) (hc : ‖c‖ = 1)
    (he : ∀ v, ⟪c,e v⟫ = 0) (hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u)
    {A : (SqMat ν)} (hA : IsSelfAdjoint A) (hb : blockOff c e A = 0) :
    A = blockScalar c A • rankOne c + blockCorner e A := by
  have hAc : (Matrix.toEuclideanCLM (𝕜 := ℝ)) A c = blockScalar c A • c := by
    have hd := frame_decomposition c e hc he hes ((Matrix.toEuclideanCLM (𝕜 := ℝ)) A c)
    change e (blockOff c e A) = (Matrix.toEuclideanCLM (𝕜 := ℝ)) A c - blockScalar c A • c at hd
    rw [hb,map_zero] at hd
    exact sub_eq_zero.mp hd.symm
  have hP := (rankOne_nonneg c).isSelfAdjoint
  have hB : IsSelfAdjoint (A - blockScalar c A • rankOne c) := hA.sub ((IsSelfAdjoint.all _).smul hP)
  have hk : (Matrix.toEuclideanCLM (𝕜 := ℝ)) (A - blockScalar c A • rankOne c) c = 0 := by
    rw [map_sub,sub_apply,map_smul,smul_apply,
      rankOne_action,real_inner_self_eq_norm_sq,hc,one_pow,one_smul,hAc,sub_self]
  have hh := blockCorner_of_kernel e hes hB hk
  have hC : blockCorner e (A - blockScalar c A • rankOne c) = blockCorner e A := by
    simp only [blockCorner,map_sub,map_smul,matrixCompress_rankOne e he,smul_zero,sub_zero]
  rw [hC] at hh
  rw [hh]
  abel
lemma Admissible.signedExtension_nonpos {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {A : (SqMat ν)} (hA : IsSelfAdjoint A) (hs : ∀ i, signedExtension f A i ≤ 0) : A ≤ 0 := by
  have hp (i : ι) : positiveExtension f A⁺ i = 0 := by
    apply le_antisymm _ (hf.positiveExtension_nonneg A⁺ i)
    apply le_of_not_gt
    intro h
    have hd := hf.positiveExtension_orthogonal (CFC.posPart_nonneg A)
      (CFC.negPart_nonneg A) (CFC.posPart_mul_negPart A) i
    have hn := (mul_eq_zero.mp hd).resolve_left (ne_of_gt h)
    have hh := hs i
    simp only [signedExtension,Pi.sub_apply,hn,sub_zero] at hh
    exact (not_lt_of_ge hh) h
  have hz : A⁺ = 0 := matrix_psd_trace_zero (CFC.posPart_nonneg A) (by
    rw [← hf.positiveExtension_sum (CFC.posPart_nonneg A)]
    simp [hp])
  have he := CFC.posPart_sub_negPart A hA
  rw [hz,zero_sub] at he
  rw [← he]
  exact neg_nonpos.mpr (CFC.negPart_nonneg A)
omit [Nonempty ν] in
lemma block_parts {c : (Euc ν)} (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) (hc : ‖c‖ = 1)
    (he : ∀ v, ⟪c,e v⟫ = 0) (hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u)
    {A : (SqMat ν)} (hA : IsSelfAdjoint A) (hb : blockOff c e A = 0)
    (ha : 0 ≤ blockScalar c A) (hC : blockCorner e A ≤ 0) :
    A⁺ = blockScalar c A • rankOne c ∧ A⁻ = -blockCorner e A := by
  have hk : (Matrix.toEuclideanCLM (𝕜 := ℝ)) (-blockCorner e A) c = 0 := by
    rw [map_neg,neg_apply,blockCorner_kernel e he,neg_zero]
  have hp := rankOne_split_parts (neg_nonneg.mpr hC) hk ha (show (0:ℝ) ≤ 1 by norm_num)
  have heq : A = blockScalar c A • rankOne c - (1:ℝ) • (-blockCorner e A) := by
    rw [one_smul,sub_neg_eq_add]
    exact block_decomposition e hc he hes hA hb
  rw [← heq] at hp
  simpa only [one_smul] using hp
lemma Admissible.block_extension {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {c : (Euc ν)} (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) (hc : ‖c‖ = 1)
    (he : ∀ v, ⟪c,e v⟫ = 0) (hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u)
    {A : (SqMat ν)} (hA : IsSelfAdjoint A) (hb : blockOff c e A = 0)
    (ha : 0 ≤ blockScalar c A) (hC : blockCorner e A ≤ 0) :
    signedExtension f A = blockScalar c A • f c + signedExtension f (blockCorner e A) := by
  obtain ⟨hp,hn⟩ := block_parts e hc he hes hA hb ha hC
  have hCp : (blockCorner e A)⁺ = 0 := (CFC.posPart_eq_zero_iff _ (blockCorner_selfAdjoint e hA)).mpr hC
  have hCn : (blockCorner e A)⁻ = -blockCorner e A := by
    have h := CFC.posPart_sub_negPart (blockCorner e A) (blockCorner_selfAdjoint e hA)
    rw [hCp,zero_sub] at h
    exact (neg_eq_iff_eq_neg.mp h)
  ext i
  simp only [signedExtension,Pi.sub_apply,hp,hn,hCp,hCn,positiveExtension_smul_nonneg f (rankOne_nonneg c) ha,
    hf.positiveExtension_rankOne c hc,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  have hz : positiveExtension f (0:(SqMat ν)) = 0 := by
    simpa only [zero_smul] using positiveExtension_smul_nonneg f (Q := (0:(SqMat ν))) le_rfl (t := 0) le_rfl
  rw [hz]
  simp only [Pi.zero_apply,sub_eq_add_neg,zero_add]
end BlockParts
end
end

section
open Set MeasureTheory
section
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
section ModelRay
variable {k : ℕ} {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι] [DecidableEq ι]
lemma Admissible.localBlockModel_ray {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {c : (Euc ν)} (hc : ‖c‖ = 1) (e : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc ν)) (he : ∀ v, ⟪c,e v⟫ = 0)
    (hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u)
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (hIc : positiveSupport f c = I)
    (D : (Euc (Fin k)) ≃L[ℝ] (Euc (Fin k))) {A : (SqMat ν)} (hA : IsSelfAdjoint A)
    {y : ι → ℝ} {rho d : ℝ} (hr : 0 < rho) (hd : 0 < d)
    (hyi : ∀ i ∈ I, y i = rho * f c i) (hyo : ∀ i ∉ I, y i ≤ 0)
    (hM : localBlockModel f c e a D A = d • y) :
    blockOff c e A = 0 ∧ 0 < blockScalar c A ∧
    localBlockModel f c e a D A = signedExtension f A ∧
    A⁺ = blockScalar c A • rankOne c := by
  have hp : ∀ i ∈ I, 0 < f c i := fun i hi => (mem_positiveSupport f c i).mp (hIc.symm ▸ hi)
  have hfo : ∀ i ∉ I, f c i = 0 := by
    intro i hi
    apply le_antisymm _ (hf.nonneg c hc i)
    exact le_of_not_gt (fun h => hi (hIc ▸ (mem_positiveSupport f c i).mpr h))
  have hs : ∑ i ∈ I, f c i = 1 := by
    rw [← hf.sum_one c hc]
    exact Finset.sum_subset (Finset.subset_univ I) (fun i _ hi => hfo i hi)
  have ha : blockScalar c A = d*rho := by
    rw [← hf.localBlockModel_sum_facet hc e he a hIc D hA,hM]
    simp only [Pi.smul_apply,smul_eq_mul]
    calc
      _ = ∑ i ∈ I, d * (rho * f c i) := Finset.sum_congr rfl (fun i hi => by rw [hyi i hi])
      _ = _ := by simp only [← Finset.mul_sum,hs,mul_one]
  have ht (i : ι) (hi : i ∈ I) : facetTangent a (D (blockOff c e A)) i = 0 := by
    have hh := hf.localBlockModel_on_facet hc e he a hp D hA hi
    rw [hM,ha] at hh
    simp only [Pi.smul_apply,smul_eq_mul,hyi i hi] at hh
    nlinarith
  have hb : blockOff c e A = 0 := by
    apply D.injective
    apply (facetTangent_injective a)
    rw [map_zero,map_zero]
    ext i
    by_cases hi : i ∈ I
    · exact ht i hi
    · exact facetTangent_zero_outside a _ hi
  have hC : blockCorner e A ≤ 0 := by
    apply hf.signedExtension_nonpos (blockCorner_selfAdjoint e hA)
    intro i
    by_cases hi : i ∈ I
    · exact (hf.signedExtension_kernel_coordinate (blockCorner_selfAdjoint e hA) hc
        (blockCorner_kernel e he A) (hp i hi)).le
    · have hh := congrFun hM i
      simp only [localBlockModel,Pi.add_apply,Pi.smul_apply,smul_eq_mul,hb,map_zero,
        add_zero,hfo i hi,mul_zero,zero_add] at hh
      rw [hh]
      exact mul_nonpos_of_nonneg_of_nonpos hd.le (hyo i hi)
  have hap : 0 < blockScalar c A := ha ▸ mul_pos hd hr
  refine ⟨hb,hap,?_,(block_parts e hc he hes hA hb hap.le hC).1⟩
  rw [hf.block_extension e hc he hes hA hb hap.le hC]
  simp only [localBlockModel,hb,map_zero,add_zero]
end ModelRay
end
end

section
open Set MeasureTheory
section
section Sard
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
lemma exists_regular_value (f : E → E) (hf : Differentiable ℝ f)
    {U : Set E} (hU : IsOpen U) (hUn : U.Nonempty) :
    ∃ y ∈ U, ∀ x, f x = y → (fderiv ℝ f x).det ≠ 0 := by
  let μ := (Module.finBasis ℝ E).addHaar
  let C : Set E := {x | (fderiv ℝ f x).det = 0}
  have hz : μ (f '' C) = 0 := addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ
    (fun x _ => (hf x).hasFDerivAt.hasFDerivWithinAt) (fun _ h => h)
  have hUp : 0 < μ U := hU.measure_pos μ hUn
  have hns : ¬ U ⊆ f '' C := by
    intro hs
    have hh : μ U ≤ μ (f '' C) := measure_mono hs
    rw [hz] at hh
    exact (not_le_of_gt hUp) hh
  obtain ⟨y,hy,hny⟩ := Set.not_subset.mp hns
  refine ⟨y,hy,?_⟩
  intro x hx hc
  exact hny ⟨x,hc,hx⟩
omit [MeasurableSpace E] [BorelSpace E] in
lemma compact_regular_level_finite (f : E → E) (hf : ContDiff ℝ 1 f) {y : E}
    {K : Set E} (hc : IsCompact K) (hK : ∀ x ∈ K, f x = y) (hr : ∀ x, f x = y → (fderiv ℝ f x).det ≠ 0) :
    K.Finite := by
  apply hc.finite
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro x hx
  have hdet := hr x (hK x hx)
  let e : E ≃L[ℝ] E := (LinearMap.equivOfIsUnitDet
    (f := (fderiv ℝ f x).toLinearMap) (isUnit_iff_ne_zero.mpr hdet)).toContinuousLinearEquiv
  have he : e.toContinuousLinearMap = fderiv ℝ f x := by
    ext z
    exact LinearMap.equivOfIsUnitDet_apply _ z
  have hd : HasStrictFDerivAt f e.toContinuousLinearMap x := by
    rw [he]
    exact hf.hasStrictFDerivAt one_ne_zero
  let p := hd.toOpenPartialHomeomorph f
  refine ⟨p.source, p.open_source,?_⟩
  ext z
  constructor
  · intro hz
    exact Set.mem_singleton_iff.mpr (p.injOn hz.1 hd.mem_toOpenPartialHomeomorph_source
      ((hK z hz.2).trans (hK x hx).symm))
  · rintro rfl
    exact ⟨hd.mem_toOpenPartialHomeomorph_source,hx⟩
end Sard
end
end

section
open Set MeasureTheory
section
open Set
noncomputable def simplexPoint {n : ℕ} (z : Euc (Fin n)) : Fin (n+1) → ℝ :=
  Fin.cases (1 - ∑ i, z i) (fun i => z i)
def simplexInterior (n : ℕ) : Set (Euc (Fin n)) :=
  {z | (∀ i, 0 < z i) ∧ ∑ i, z i < 1}
lemma simplexInterior_isOpen (n : ℕ) : IsOpen (simplexInterior n) := by
  have h₁ : IsOpen {z : Euc (Fin n) | ∀ i, 0 < z i} := by
    rw [show {z : Euc (Fin n) | ∀ i, 0 < z i} =
      ⋂ i, {z : Euc (Fin n) | 0 < z i} from by ext; simp]
    exact isOpen_iInter_of_finite (fun i => isOpen_lt continuous_const (EuclideanSpace.proj i).continuous)
  exact h₁.inter (isOpen_lt (continuous_finsetSum Finset.univ
    (fun i _ => (EuclideanSpace.proj i).continuous)) continuous_const)
lemma simplexInterior_nonempty (n : ℕ) : (simplexInterior n).Nonempty := by
  refine ⟨WithLp.toLp 2 (fun _ : Fin n => (1:ℝ)/(n+1)),?_,?_⟩
  · intro i
    change 0 < (1:ℝ)/(n+1)
    positivity
  · change ∑ _i : Fin n, (1:ℝ)/(n+1) < 1
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    rw [mul_one_div]
    exact (div_lt_one (by positivity)).mpr (by linarith)
lemma simplexPoint_pos {n : ℕ} {z : Euc (Fin n)} (hz : z ∈ simplexInterior n) :
    ∀ i, 0 < simplexPoint z i := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact sub_pos.mpr hz.2
  · exact hz.1 j
lemma simplexPoint_sum {n : ℕ} (z : Euc (Fin n)) : ∑ i, simplexPoint z i = 1 := by
  rw [Fin.sum_univ_succ]
  simp only [simplexPoint,Fin.cases_zero,Fin.cases_succ]
  ring
lemma simplexPoint_succ {n : ℕ} (z : Euc (Fin n)) (i : Fin n) :
    simplexPoint z i.succ = z i := rfl
end
section
open Set
open scoped RealInnerProductSpace
end
end

section
open Set MeasureTheory
section
open Set
open scoped RealInnerProductSpace
section RegularBase
variable {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
noncomputable def baseCoordinates (f : (Euc (Fin (k+1))) → ι → ℝ) (w : (Euc (Fin (k+1)))) (e : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc (Fin (k+1))))
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) : (Euc (Fin k)) → (Euc (Fin k)) :=
  fun v => WithLp.toLp 2 (fun j => f (hemisphereChart w e v) (a j.succ).val)
omit [DecidableEq ι] in
lemma Admissible.baseCoordinates_contDiff {f : (Euc (Fin (k+1))) → ι → ℝ} (hf : Admissible f)
    {w : (Euc (Fin (k+1)))} (hw : ‖w‖ = 1) (e : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc (Fin (k+1)))) (he : ∀ v, ⟪w,e v⟫ = 0)
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) : ContDiff ℝ (⊤ : ℕ∞) (baseCoordinates f w e a) := by
  apply (contDiff_piLp 2).mpr
  intro j
  exact (hf.smooth (a j.succ).val).comp (hemisphereChart_contDiff w e hw he)
noncomputable def facetPoint {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (z : (Euc (Fin k))) : ι → ℝ :=
  fun i => if hi : i ∈ I then simplexPoint z (a.symm ⟨i,hi⟩) else 0
omit [Fintype ι] in
lemma facetPoint_apply {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (z : (Euc (Fin k))) (j : Fin (k+1)) :
    facetPoint a z (a j).val = simplexPoint z j := by
  simp [facetPoint]
omit [Fintype ι] in
lemma facetPoint_pos {I : Finset ι} (a : Fin (k+1) ≃ ↥I) {z : (Euc (Fin k))} (hz : z ∈ simplexInterior k) :
    ∀ i ∈ I, 0 < facetPoint a z i := by
  intro i hi
  simp only [facetPoint,dif_pos hi]
  exact simplexPoint_pos hz _
omit [Fintype ι] in
lemma facetPoint_zero {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (z : (Euc (Fin k))) {i : ι} (hi : i ∉ I) :
    facetPoint a z i = 0 := by simp [facetPoint,hi]
lemma facetPoint_sum {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (z : (Euc (Fin k))) : ∑ i, facetPoint a z i = 1 := by
  have h : ∑ i, facetPoint a z i = ∑ i : ↥I, simplexPoint z (a.symm i) := by
    calc
      _ = ∑ i ∈ I, facetPoint a z i := (Finset.sum_subset (Finset.subset_univ I)
        (fun i _ hi => facetPoint_zero a z hi)).symm
      _ = ∑ i : ↥I, facetPoint a z i.val := (Finset.sum_coe_sort I _).symm
      _ = _ := Finset.sum_congr rfl (fun i _ => by simp [facetPoint])
  rw [h,Equiv.sum_comp a.symm]
  exact simplexPoint_sum z
lemma Admissible.exists_regular_facet_point {f : (Euc (Fin (k+1))) → ι → ℝ} (hf : Admissible f)
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) {w : (Euc (Fin (k+1)))} (hw : ‖w‖ = 1)
    (hwi : ∀ i ∈ I, 0 < f w i) :
    ∃ (e : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc (Fin (k+1)))) (z : (Euc (Fin k))), (∀ v, ⟪w,e v⟫ = 0) ∧
      (∀ u, ⟪w,u⟫ = 0 → ∃ v, e v = u) ∧ z ∈ simplexInterior k ∧
      (∀ v, baseCoordinates f w e a v = z → (fderiv ℝ (baseCoordinates f w e a) v).det ≠ 0) ∧
      (orientedLevel f w (facetPoint a z)).Finite := by
  obtain ⟨e,he,hes⟩ := orthogonal_frame k hw
  obtain ⟨z,hz,hr⟩ := exists_regular_value (baseCoordinates f w e a)
    ((hf.baseCoordinates_contDiff hw e he a).differentiable (by simp)) (simplexInterior_isOpen k) (simplexInterior_nonempty k)
  refine ⟨e,z,he,hes,hz,hr,?_⟩
  let K := orientedLevel f w (facetPoint a z)
  have hI : I.Nonempty := ⟨(a 0).val,(a 0).property⟩
  have hp : K ⊆ {u | 0 < ⟪w,u⟫} := fun u hu =>
    hf.orientedLevel_inner_pos hI hw hwi (facetPoint_pos a hz) hu
  have hcont : ContinuousOn (hemisphereInverse w e) K := (hemisphereInverse_continuousOn w e).mono hp
  have hc := (hf.orientedLevel_compact w (facetPoint a z)).image_of_continuousOn hcont
  have hK : ∀ v ∈ hemisphereInverse w e '' K, baseCoordinates f w e a v = z := by
    rintro v ⟨u,hu,rfl⟩
    ext j
    change f (hemisphereChart w e (hemisphereInverse w e u)) (a j.succ).val = z j
    rw [hemisphereChart_inverse w e hw he hes hu.1 (hp hu),hu.2.1,facetPoint_apply,simplexPoint_succ]
  have hfin := compact_regular_level_finite (baseCoordinates f w e a)
    ((hf.baseCoordinates_contDiff hw e he a).of_le (by simp)) hc hK hr
  apply (Set.finite_image_iff ?_).mp hfin
  intro u hu v hv huv
  have hh := congrArg (hemisphereChart w e) huv
  rwa [hemisphereChart_inverse w e hw he hes hu.1 (hp hu),
    hemisphereChart_inverse w e hw he hes hv.1 (hp hv)] at hh
end RegularBase
end
end

section
open Set MeasureTheory
section
open scoped RealInnerProductSpace Topology
open Filter
section ChartRegular
variable {E W : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W] [FiniteDimensional ℝ W]
omit [CompleteSpace E] [CompleteSpace W] [FiniteDimensional ℝ W] in
lemma hemisphereChart_zero {c : E} (hc : ‖c‖ = 1) (e : W →ₗᵢ[ℝ] E) : hemisphereChart c e 0 = c := by
  simp [hemisphereChart,SimplicialChains.unitRadial,hc]
omit [FiniteDimensional ℝ W] in
lemma hemisphereInverse_contDiffAt (w : E) (e : W →ₗᵢ[ℝ] E) {u : E} (hu : ⟪w,u⟫ ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (hemisphereInverse w e) u :=
  ((contDiffAt_const.inner ℝ contDiffAt_id).inv hu).smul e.toContinuousLinearMap.adjoint.contDiff.contDiffAt
omit [FiniteDimensional ℝ W] in
lemma hemisphere_transition_regular {w c : E} (hw : ‖w‖ = 1) (hc : ‖c‖ = 1)
    (e d : W →ₗᵢ[ℝ] E) (he : ∀ v, ⟪w,e v⟫ = 0) (hd : ∀ v, ⟪c,d v⟫ = 0)
    (hes : ∀ u, ⟪w,u⟫ = 0 → ∃ v, e v = u) (_hds : ∀ u, ⟪c,u⟫ = 0 → ∃ v, d v = u)
    (hwc : 0 < ⟪w,c⟫) (f : E → W) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hr : (fderiv ℝ (fun v => f (hemisphereChart w e v)) (hemisphereInverse w e c)).det ≠ 0) :
    (fderiv ℝ (fun v => f (hemisphereChart c d v)) 0).det ≠ 0 := by
  let T : W → W := fun v => hemisphereInverse w e (hemisphereChart c d v)
  let S : W → W := fun v => hemisphereInverse c d (hemisphereChart w e v)
  let v₀ := hemisphereInverse w e c
  have hTc : T 0 = v₀ := by simp [T,v₀,hemisphereChart_zero hc]
  have hwc' : hemisphereChart w e v₀ = c := hemisphereChart_inverse w e hw he hes hc hwc
  have hT : ContDiffAt ℝ (⊤ : ℕ∞) T 0 :=
    (hemisphereInverse_contDiffAt w e (by simpa only [hemisphereChart_zero hc] using ne_of_gt hwc)).comp 0
      (hemisphereChart_contDiff c d hc hd).contDiffAt
  have hS : ContDiffAt ℝ (⊤ : ℕ∞) S v₀ :=
    (hemisphereInverse_contDiffAt c d (by rw [hwc']; simp [hc])).comp v₀
      (hemisphereChart_contDiff w e hw he).contDiffAt
  have hnear : ∀ᶠ v in 𝓝 (0:W), 0 < ⟪w,hemisphereChart c d v⟫ :=
    (continuous_const.inner (hemisphereChart_contDiff c d hc hd).continuous).continuousAt
      (isOpen_Ioi.mem_nhds (by simpa only [hemisphereChart_zero hc,Set.mem_Ioi] using hwc))
  have hST : (fun v => S (T v)) =ᶠ[𝓝 (0:W)] id := by
    filter_upwards [hnear] with v hv
    dsimp [S,T]
    rw [hemisphereChart_inverse w e hw he hes (hemisphereChart_norm c d hc hd v) hv,
      hemisphereInverse_chart c d hc hd]
  have hdT := hT.differentiableAt (by simp)
  have hdS := hS.differentiableAt (by simp)
  have hdS' : HasFDerivAt S (fderiv ℝ S v₀) (T 0) := by rw [hTc]; exact hdS.hasFDerivAt
  have hcomp : (fderiv ℝ S v₀).comp (fderiv ℝ T 0) = ContinuousLinearMap.id ℝ W :=
    (hdS'.comp 0 hdT.hasFDerivAt).unique ((hasFDerivAt_id (0:W)).congr_of_eventuallyEq hST)
  have hTdet : (fderiv ℝ T 0).det ≠ 0 := by
    have composition_det := congrArg ContinuousLinearMap.det hcomp
    change LinearMap.det ((fderiv ℝ S v₀).toLinearMap.comp (fderiv ℝ T 0).toLinearMap) =
      LinearMap.det (LinearMap.id : W →ₗ[ℝ] W) at composition_det
    rw [LinearMap.det_comp, LinearMap.det_id] at composition_det
    have nonzero_product : (fderiv ℝ S v₀).det * (fderiv ℝ T 0).det ≠ 0 := by
      rw [composition_det]
      exact one_ne_zero
    exact (mul_ne_zero_iff.mp nonzero_product).2
  let g : W → W := fun v => f (hemisphereChart w e v)
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := hf.comp (hemisphereChart_contDiff w e hw he)
  have hfg : (fun v => f (hemisphereChart c d v)) =ᶠ[𝓝 (0:W)] (fun v => g (T v)) := by
    filter_upwards [hnear] with v hv
    dsimp [g,T]
    rw [hemisphereChart_inverse w e hw he hes (hemisphereChart_norm c d hc hd v) hv]
  have hgT : HasFDerivAt g (fderiv ℝ g v₀) (T 0) := by
    rw [hTc]
    exact (hg.differentiable (by simp) v₀).hasFDerivAt
  have hfinal := (hgT.comp 0 hdT.hasFDerivAt).congr_of_eventuallyEq hfg
  rw [hfinal.fderiv]
  change LinearMap.det ((fderiv ℝ g v₀).toLinearMap.comp (fderiv ℝ T 0).toLinearMap) ≠ 0
  rw [LinearMap.det_comp]
  exact mul_ne_zero hr hTdet
end ChartRegular
end
end

section
open Set MeasureTheory
section
open scoped Matrix MatrixOrder RealInnerProductSpace Matrix.Norms.L2Operator
section BlockLine
variable {μ ν : Type*} [Fintype μ] [Fintype ν] [DecidableEq μ] [DecidableEq ν]
  [Nonempty ν]
lemma positiveLine_eigenvector {A : (SqMat ν)} (hA : IsSelfAdjoint A) {c : (Euc ν)} (hc : ‖c‖ = 1)
    {lam : ℝ} (hl : 0 < lam) (hP : A⁺ = lam • rankOne c) : (Matrix.toEuclideanCLM (𝕜 := ℝ)) A c = lam • c := by
  rw [← CFC.posPart_sub_negPart A hA,map_sub,sub_apply,
    negPart_kernel_of_positiveLine hc hl hP,sub_zero,hP,map_smul,smul_apply,
    rankOne_action,real_inner_self_eq_norm_sq,hc,one_pow,one_smul]
lemma blockScalar_positiveLine {A : (SqMat ν)} (hA : IsSelfAdjoint A) {c : (Euc ν)} (hc : ‖c‖ = 1)
    {lam : ℝ} (hl : 0 < lam) (hP : A⁺ = lam • rankOne c) : blockScalar c A = lam := by
  rw [blockScalar,positiveLine_eigenvector hA hc hl hP,inner_smul_right,real_inner_self_eq_norm_sq,hc,one_pow,mul_one]
omit [DecidableEq μ] in
lemma blockOff_positiveLine (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) {A : (SqMat ν)} (hA : IsSelfAdjoint A) {c : (Euc ν)} (hc : ‖c‖ = 1)
    (he : ∀ v, ⟪c,e v⟫ = 0) {lam : ℝ} (hl : 0 < lam) (hP : A⁺ = lam • rankOne c) :
    blockOff c e A = 0 := by
  rw [blockOff,positiveLine_eigenvector hA hc hl hP,map_smul,adjoint_normal c e he,smul_zero]
lemma blockCorner_positiveLine (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) {A : (SqMat ν)} (hA : IsSelfAdjoint A) {c : (Euc ν)} (hc : ‖c‖ = 1)
    (he : ∀ v, ⟪c,e v⟫ = 0) (hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u)
    {lam : ℝ} (hl : 0 < lam) (hP : A⁺ = lam • rankOne c) : blockCorner e A = -A⁻ := by
  have hd := block_decomposition e hc he hes hA (blockOff_positiveLine e hA hc he hl hP)
  rw [blockScalar_positiveLine hA hc hl hP] at hd
  have hp := CFC.posPart_sub_negPart A hA
  rw [hP] at hp
  exact (add_left_cancel (show lam • rankOne c + -A⁻ = lam • rankOne c + blockCorner e A by simpa only [sub_eq_add_neg] using hp.trans hd)).symm
omit [Nonempty ν] in
lemma blockCompress_isUnit (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) {A : (SqMat ν)} (hA : IsSelfAdjoint A) (hU : IsUnit A)
    {c : (Euc ν)} (hc : ‖c‖ = 1) (he : ∀ v, ⟪c,e v⟫ = 0)
    (hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u) (hb : blockOff c e A = 0) :
    IsUnit (matrixCompress e A) := by
  have hopU : IsUnit ((Matrix.toEuclideanCLM (𝕜 := ℝ)) A) := IsUnit.map (matrixOp ν) hU
  have hAi : Function.Injective ((Matrix.toEuclideanCLM (𝕜 := ℝ)) A) := (ContinuousLinearMap.isUnit_iff_bijective.mp hopU).1
  apply (isUnit_map_iff ((Matrix.toEuclideanCLM (𝕜 := ℝ))) _).mp
  apply ContinuousLinearMap.isUnit_iff_bijective.mpr
  have hi : Function.Injective ((Matrix.toEuclideanCLM (𝕜 := ℝ)) (matrixCompress e A)) := by
    apply (LinearMap.ker_eq_bot).mp
    rw [Submodule.eq_bot_iff]
    intro v hv
    have hv0 : (Matrix.toEuclideanCLM (𝕜 := ℝ)) (matrixCompress e A) v = 0 := hv
    have hAv : (Matrix.toEuclideanCLM (𝕜 := ℝ)) A (e v) = 0 := by
      conv_lhs => rw [block_decomposition e hc he hes hA hb]
      rw [map_add,add_apply,map_smul,smul_apply,
        rankOne_action,he,zero_smul,smul_zero,zero_add]
      change (Matrix.toEuclideanCLM (𝕜 := ℝ)) (matrixEmbed e (matrixCompress e A)) (e v) = 0
      rw [show (Matrix.toEuclideanCLM (𝕜 := ℝ)) (matrixEmbed e (matrixCompress e A)) (e v) = e ((Matrix.toEuclideanCLM (𝕜 := ℝ)) (matrixCompress e A) v) from matrixEmbed_action e _ v,hv0,map_zero]
    apply e.injective
    exact hAi (by simpa only [map_zero] using hAv)
  exact ⟨hi,(LinearMap.injective_iff_surjective).mp hi⟩
lemma posDef_inner_pos {B : SqMat μ} (hB : B.PosDef) {v : (Euc μ)} (hv : v ≠ 0) :
    0 < ⟪v,(Matrix.toEuclideanCLM (𝕜 := ℝ)) B v⟫ := by
  have hv' : v.ofLp ≠ 0 := fun h => hv (WithLp.ofLp_injective 2 h)
  have h := hB.dotProduct_mulVec_pos hv'
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial]
  change 0 < ∑ i, (B *ᵥ v.ofLp) i * v i
  simpa only [dotProduct,Pi.star_apply,star_trivial,mul_comm] using h
lemma blockCompress_negative (e : (Euc μ) →ₗᵢ[ℝ] (Euc ν)) {A : (SqMat ν)} (hA : IsSelfAdjoint A) (hU : IsUnit A)
    {c : (Euc ν)} (hc : ‖c‖ = 1) (he : ∀ v, ⟪c,e v⟫ = 0)
    (hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u) {lam : ℝ} (hl : 0 < lam)
    (hP : A⁺ = lam • rankOne c) : NegativeQuadratic ((Matrix.toEuclideanCLM (𝕜 := ℝ)) (matrixCompress e A)) := by
  have hC := blockCorner_positiveLine e hA hc he hes hl hP
  have hcomp : -(matrixCompress e A) = matrixCompress e A⁻ := by
    have hh := congrArg (matrixCompress e) hC
    rw [blockCorner,matrixCompress_embed,map_neg] at hh
    exact neg_eq_iff_eq_neg.mpr hh
  have hn : 0 ≤ -(matrixCompress e A) := by rw [hcomp]; exact matrixCompress_nonneg e (CFC.negPart_nonneg A)
  have hunit := (blockCompress_isUnit e hA hU hc he hes (blockOff_positiveLine e hA hc he hl hP)).neg
  have hpd := (Matrix.nonneg_iff_posSemidef.mp hn).posDef_iff_isUnit.mpr hunit
  intro v hv
  have h := posDef_inner_pos hpd hv
  rw [map_neg,neg_apply,inner_neg_right] at h
  exact neg_pos.mp h
end BlockLine
end
end

section
open Set MeasureTheory
section
open scoped RealInnerProductSpace Topology
section LocalRegular
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
lemma regular_inner_positive (D : E ≃L[ℝ] E) {g : E → E}
    (h0 : g 0 = 0) (hd : HasFDerivAt g D.toContinuousLinearMap 0) :
    ∃ δ > 0, ∀ v, ‖v‖ < δ → v ≠ 0 → 0 < ⟪v,D.symm (g v)⟫ := by
  let H : E → E := fun v => D.symm (g v)
  have hH : HasFDerivAt H (ContinuousLinearMap.id ℝ E) 0 := by
    convert D.symm.hasFDerivAt.comp 0 hd using 1 <;> ext v <;> simp [H]
  have hH0 : H 0 = 0 := by simp [H,h0]
  have herr := hH.isLittleO.def (show (0:ℝ) < 1/2 by norm_num)
  obtain ⟨δ,hδ,hball⟩ := Metric.eventually_nhds_iff.mp herr
  refine ⟨δ,hδ,?_⟩
  intro v hv hv0
  have hb := hball (by simpa only [dist_zero_right] using hv)
  simp only [hH0,sub_zero,ContinuousLinearMap.id_apply] at hb
  have hi : |⟪v,H v - v⟫| ≤ ‖v‖ * ((1/2:ℝ)*‖v‖) :=
    (abs_real_inner_le_norm v _).trans (mul_le_mul_of_nonneg_left hb (norm_nonneg _))
  have hp : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  rw [inner_sub_right,real_inner_self_eq_norm_sq] at hi
  change 0 < ⟪v,H v⟫
  nlinarith [neg_abs_le ⟪v,H v⟫,neg_abs_le (⟪v,H v⟫-‖v‖^2)]
lemma positive_inner_convex {v x y : E} (hx : 0 < ⟪v,x⟫) (hy : 0 < ⟪v,y⟫)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) : 0 < ⟪v,(1-t) • x + t • y⟫ := by
  simp only [inner_add_right,real_inner_smul_right]
  by_cases ht0 : t = 0
  · simpa [ht0] using hx
  · exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr ht.2) hx.le)
      (mul_pos (lt_of_le_of_ne ht.1 (Ne.symm ht0)) hy)
lemma regular_mixed_zero (D : E ≃L[ℝ] E) {g : E → E} {v b : E} {lam t : ℝ}
    (hp : v ≠ 0 → 0 < ⟪v,D.symm (g v)⟫) (hb : v ≠ 0 → 0 < ⟪v,b⟫)
    (hl : 0 < lam) (ht : t ∈ Set.Icc 0 1)
    (hz : (1-t) • (lam • g v) + t • D b = 0) : v = 0 := by
  by_contra hv
  have hh := positive_inner_convex (by simpa only [real_inner_smul_right] using mul_pos hl (hp hv)) (hb hv) ht
    (v := v) (x := lam • D.symm (g v))
  have he := congrArg D.symm hz
  simp only [map_add,map_smul,D.symm_apply_apply,map_zero] at he
  rw [he,inner_zero_right] at hh
  exact (lt_irrefl (0:ℝ)) hh
end LocalRegular
end
end

section
open Set MeasureTheory
section
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
section LocalMix
variable {k : ℕ} {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι] [DecidableEq ι]
omit [DecidableEq ν] [Nonempty ν] [DecidableEq ι] in
lemma Admissible.sum_on_support {f : (Euc ν) → ι → ℝ} (hf : Admissible f) {u : (Euc ν)} (hu : ‖u‖ = 1)
    {I : Finset ι} (hI : positiveSupport f u = I) : ∑ i ∈ I, f u i = 1 := by
  rw [← hf.sum_one u hu]
  apply Finset.sum_subset (Finset.subset_univ I)
  intro i _ hi
  apply le_antisymm _ (hf.nonneg u hu i)
  exact le_of_not_gt (fun h => hi (hI ▸ (mem_positiveSupport f u i).mpr h))
omit [DecidableEq ι] in
lemma Admissible.extension_on_positiveLine {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {A : (SqMat ν)} {u : (Euc ν)} (hu : ‖u‖ = 1) {lam : ℝ} (hl : 0 < lam)
    (hP : A⁺ = lam • rankOne u) {i : ι} (hi : 0 < f u i) :
    signedExtension f A i = lam * f u i := by
  have hn := hf.positiveExtension_kernel (CFC.negPart_nonneg A) hu
    (negPart_kernel_of_positiveLine hu hl hP) hi
  simp only [signedExtension,Pi.sub_apply,hn,sub_zero,hP,
    positiveExtension_smul_nonneg f (rankOne_nonneg u) hl.le,
    hf.positiveExtension_rankOne u hu,Pi.smul_apply,smul_eq_mul]
lemma Admissible.localBlockModel_eq_of_positiveLine {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {A : (SqMat ν)} (hA : IsSelfAdjoint A) {c : (Euc ν)} (hc : ‖c‖ = 1) (e : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc ν))
    (he : ∀ v, ⟪c,e v⟫ = 0) (hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u)
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (D : (Euc (Fin k)) ≃L[ℝ] (Euc (Fin k)))
    {lam : ℝ} (hl : 0 < lam) (hP : A⁺ = lam • rankOne c) :
    localBlockModel f c e a D A = signedExtension f A := by
  have hb := blockOff_positiveLine e hA hc he hl hP
  have hC : blockCorner e A ≤ 0 := by rw [blockCorner_positiveLine e hA hc he hes hl hP]; exact neg_nonpos.mpr (CFC.negPart_nonneg A)
  have ha : 0 ≤ blockScalar c A := by rw [blockScalar_positiveLine hA hc hl hP]; exact hl.le
  rw [hf.block_extension e hc he hes hA hb ha hC]
  simp only [localBlockModel,hb,map_zero,add_zero]
noncomputable def localBlockMix (f : (Euc ν) → ι → ℝ) (c : (Euc ν)) (e : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc ν))
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (D : (Euc (Fin k)) ≃L[ℝ] (Euc (Fin k))) (t : ℝ) (A : (SqMat ν)) : ι → ℝ :=
  (1-t) • signedExtension f A + t • localBlockModel f c e a D A
lemma Admissible.localBlockMix_sum {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {A : (SqMat ν)} (hA : IsSelfAdjoint A) {c u : (Euc ν)} (hc : ‖c‖ = 1) (hu : ‖u‖ = 1)
    (e : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc ν)) (he : ∀ v, ⟪c,e v⟫ = 0)
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (hIc : positiveSupport f c = I) (hIu : positiveSupport f u = I)
    (D : (Euc (Fin k)) ≃L[ℝ] (Euc (Fin k))) {lam : ℝ} (hl : 0 < lam) (hP : A⁺ = lam • rankOne u) (t : ℝ) :
    ∑ i ∈ I, localBlockMix f c e a D t A i = (1-t)*lam + t*blockScalar c A := by
  have hF : ∑ i ∈ I, signedExtension f A i = lam := by
    calc
      _ = ∑ i ∈ I, lam * f u i := Finset.sum_congr rfl (fun i hi =>
        hf.extension_on_positiveLine hu hl hP ((mem_positiveSupport f u i).mp (hIu.symm ▸ hi)))
      _ = _ := by rw [← Finset.mul_sum,hf.sum_on_support hu hIu,mul_one]
  simp only [localBlockMix,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_add_distrib,
    ← Finset.mul_sum,hF,hf.localBlockModel_sum_facet hc e he a hIc D hA]
lemma Admissible.localBlockMix_ne_zero {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {A : (SqMat ν)} (hA : IsSelfAdjoint A) {c u : (Euc ν)} (hc : ‖c‖ = 1) (hu : ‖u‖ = 1)
    (e : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc ν)) (he : ∀ v, ⟪c,e v⟫ = 0)
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (hIc : positiveSupport f c = I) (hIu : positiveSupport f u = I)
    (D : (Euc (Fin k)) ≃L[ℝ] (Euc (Fin k))) {lam : ℝ} (hl : 0 < lam) (hP : A⁺ = lam • rankOne u)
    (ha : 0 < blockScalar c A) {t : ℝ} (ht : t ∈ Set.Icc 0 1) : localBlockMix f c e a D t A ≠ 0 := by
  intro hz
  have hh := hf.localBlockMix_sum hA hc hu e he a hIc hIu D hl hP t
  rw [hz] at hh
  simp only [Pi.zero_apply,Finset.sum_const_zero] at hh
  have hp : 0 < (1-t)*lam + t*blockScalar c A := by
    by_cases ht0 : t = 0
    · simpa [ht0] using hl
    · exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr ht.2) hl.le)
        (mul_pos (lt_of_le_of_ne ht.1 (Ne.symm ht0)) ha)
  linarith
noncomputable def facetTail {I : Finset ι} (a : Fin (k+1) ≃ ↥I) : (ι → ℝ) →ₗ[ℝ] (Euc (Fin k)) where
  toFun r := WithLp.toLp 2 (fun j => r (a j.succ).val)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
lemma Admissible.localBlockMix_tangent_zero {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {A : (SqMat ν)} (hA : IsSelfAdjoint A) {c u : (Euc ν)} (hc : ‖c‖ = 1) (hu : ‖u‖ = 1)
    (e : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc ν)) (he : ∀ v, ⟪c,e v⟫ = 0) (_hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u)
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (hIc : positiveSupport f c = I) (hIu : positiveSupport f u = I)
    (D : (Euc (Fin k)) ≃L[ℝ] (Euc (Fin k))) {lam : ℝ} (hl : 0 < lam) (hP : A⁺ = lam • rankOne u) (_hcu : 0 < ⟪c,u⟫)
    (_hB : NegativeQuadratic (Matrix.toEuclideanCLM (𝕜 := ℝ) (matrixCompress e A)))
    (_hreg : hemisphereInverse c e u ≠ 0 →
      0 < ⟪hemisphereInverse c e u,D.symm (facetTail a (f u - f c))⟫)
    {y : ι → ℝ} {rho d t : ℝ} (hyi : ∀ i ∈ I, y i = rho * f c i)
    (_ht : t ∈ Set.Icc 0 1) (hM : localBlockMix f c e a D t A = d • y) :
    (1-t) • (lam • facetTail a (f u - f c)) + t • D (blockOff c e A) = 0 := by
  have hp : ∀ i ∈ I, 0 < f c i := fun i hi => (mem_positiveSupport f c i).mp (hIc.symm ▸ hi)
  have hpu : ∀ i ∈ I, 0 < f u i := fun i hi => (mem_positiveSupport f u i).mp (hIu.symm ▸ hi)
  have hs : (1-t)*lam+t*blockScalar c A = d*rho := by
    rw [← hf.localBlockMix_sum hA hc hu e he a hIc hIu D hl hP t,hM]
    simp only [Pi.smul_apply,smul_eq_mul]
    calc
      _ = ∑ i ∈ I, d*(rho*f c i) := Finset.sum_congr rfl (fun i hi => by rw [hyi i hi])
      _ = _ := by rw [← Finset.mul_sum,← Finset.mul_sum,hf.sum_on_support hc hIc,mul_one]
  apply PiLp.ext
  intro j
  have hi := (a j.succ).property
  have hh := congrFun hM (a j.succ).val
  simp only [localBlockMix,Pi.add_apply,Pi.smul_apply,smul_eq_mul,
    hf.extension_on_positiveLine hu hl hP (hpu _ hi),
    hf.localBlockModel_on_facet hc e he a hp D hA hi,facetTangent_apply,Fin.cases_succ,hyi _ hi] at hh
  change (1-t)*(lam*(f u (a j.succ).val - f c (a j.succ).val)) + t*(D (blockOff c e A)) j = 0
  nlinarith [congrArg (fun x : ℝ => x * f c (a j.succ).val) hs]
lemma Admissible.localBlockMix_hit {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    {A : (SqMat ν)} (hA : IsSelfAdjoint A) {c u : (Euc ν)} (hc : ‖c‖ = 1) (hu : ‖u‖ = 1)
    (e : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc ν)) (he : ∀ v, ⟪c,e v⟫ = 0) (hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u)
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (hIc : positiveSupport f c = I) (hIu : positiveSupport f u = I)
    (D : (Euc (Fin k)) ≃L[ℝ] (Euc (Fin k))) {lam : ℝ} (hl : 0 < lam) (hP : A⁺ = lam • rankOne u) (hcu : 0 < ⟪c,u⟫)
    (hB : NegativeQuadratic (Matrix.toEuclideanCLM (𝕜 := ℝ) (matrixCompress e A)))
    (hreg : hemisphereInverse c e u ≠ 0 →
      0 < ⟪hemisphereInverse c e u,D.symm (facetTail a (f u - f c))⟫)
    {y : ι → ℝ} {rho d t : ℝ} (hyi : ∀ i ∈ I, y i = rho * f c i)
    (ht : t ∈ Set.Icc 0 1) (hM : localBlockMix f c e a D t A = d • y) :
    u = c ∧ localBlockMix f c e a D t A = signedExtension f A := by
  have hz := hf.localBlockMix_tangent_zero hA hc hu e he hes a hIc hIu D hl hP hcu hB hreg hyi ht hM
  have hb : hemisphereInverse c e u ≠ 0 → 0 < ⟪hemisphereInverse c e u,blockOff c e A⟫ := by
    intro hv
    rw [blockOff_eigenvector e hc he hes hu hcu (positiveLine_eigenvector hA hu hl hP)]
    exact negativeQuadratic_pos_sub hB hv hl
  have hv : hemisphereInverse c e u = 0 := regular_mixed_zero D (g := fun _ : (Euc (Fin k)) => facetTail a (f u-f c)) (v := hemisphereInverse c e u) (b := blockOff c e A) hreg hb hl ht hz
  have huc : u = c := by
    have hh := hemisphereChart_inverse c e hc he hes hu hcu
    rw [hv] at hh
    simpa only [hemisphereChart,SimplicialChains.unitRadial,map_zero,add_zero,hc,inv_one,one_smul] using hh.symm
  refine ⟨huc,?_⟩
  have hm := hf.localBlockModel_eq_of_positiveLine hA hc e he hes a D hl (huc ▸ hP)
  rw [localBlockMix,hm,← add_smul,sub_add_cancel,one_smul]
end LocalMix
end
end

section
open Set MeasureTheory
section
open scoped RealInnerProductSpace
section RegularModel
variable {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma Admissible.regular_model_data {f : (Euc (Fin (k+1))) → ι → ℝ} (hf : Admissible f)
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) {w c : (Euc (Fin (k+1)))} (hw : ‖w‖ = 1) (hc : ‖c‖ = 1)
    (e : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc (Fin (k+1)))) (he : ∀ v, ⟪w,e v⟫ = 0) (hes : ∀ u, ⟪w,u⟫ = 0 → ∃ v, e v = u)
    (hwc : 0 < ⟪w,c⟫) {z : (Euc (Fin k))} (hcval : f c = facetPoint a z)
    (hr : ∀ v, baseCoordinates f w e a v = z → (fderiv ℝ (baseCoordinates f w e a) v).det ≠ 0) :
    ∃ (d : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc (Fin (k+1)))) (D : (Euc (Fin k)) ≃L[ℝ] (Euc (Fin k))) (δ : ℝ),
      (∀ v, ⟪c,d v⟫ = 0) ∧ (∀ u, ⟪c,u⟫ = 0 → ∃ v, d v = u) ∧ 0 < δ ∧
      ∀ u : (Euc (Fin (k+1))), ‖u‖ = 1 → 0 < ⟪c,u⟫ → ‖hemisphereInverse c d u‖ < δ →
        hemisphereInverse c d u ≠ 0 → 0 < ⟪hemisphereInverse c d u,D.symm (facetTail a (f u-f c))⟫ := by
  obtain ⟨d,hd,hds⟩ := orthogonal_frame k hc
  let F : (Euc (Fin (k+1))) → (Euc (Fin k)) := fun u => facetTail a (f u)
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := by
    apply (contDiff_piLp 2).mpr
    intro j
    exact hf.smooth (a j.succ).val
  have hz : baseCoordinates f w e a (hemisphereInverse w e c) = z := by
    ext j
    change f (hemisphereChart w e (hemisphereInverse w e c)) (a j.succ).val = z j
    rw [hemisphereChart_inverse w e hw he hes hc hwc,hcval,facetPoint_apply,simplexPoint_succ]
  have hdet : (fderiv ℝ (baseCoordinates f c d a) 0).det ≠ 0 :=
    hemisphere_transition_regular hw hc e d he hd hes hds hwc F hF (hr _ hz)
  let D : (Euc (Fin k)) ≃L[ℝ] (Euc (Fin k)) :=
    (fderiv ℝ (baseCoordinates f c d a) 0).toContinuousLinearEquivOfDetNeZero hdet
  have hD : D.toContinuousLinearMap = fderiv ℝ (baseCoordinates f c d a) 0 := by
    exact ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ hdet
  let g : (Euc (Fin k)) → (Euc (Fin k)) := fun v => baseCoordinates f c d a v - F c
  have hg0 : g 0 = 0 := by
    change F (hemisphereChart c d 0) - F c = 0
    rw [hemisphereChart_zero hc,sub_self]
  have hgd : HasFDerivAt g D.toContinuousLinearMap 0 := by
    rw [hD]
    exact (((hf.baseCoordinates_contDiff hc d hd a).differentiable (by simp) 0).hasFDerivAt).sub_const (F c)
  obtain ⟨δ,hδ,hpos⟩ := regular_inner_positive D hg0 hgd
  refine ⟨d,D,δ,hd,hds,hδ,?_⟩
  intro u hu hcu hδu hv
  have hg : g (hemisphereInverse c d u) = facetTail a (f u-f c) := by
    change F (hemisphereChart c d (hemisphereInverse c d u)) - F c = _
    rw [hemisphereChart_inverse c d hc hd hds hu hcu]
    exact (map_sub (facetTail a) _ _).symm
  rw [← hg]
  exact hpos _ hδu hv
end RegularModel
end
end

section
open Set MeasureTheory
section
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
open Set
section RegularPatch
variable {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
noncomputable def regularPatch (f : (Euc (Fin (k+1))) → ι → ℝ) (I : Finset ι) (w c : (Euc (Fin (k+1))))
    (e : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc (Fin (k+1)))) (δ : ℝ) : Set (traceSphere (Fin (k+1))) :=
  {A | IsUnit A.val ∧ HasPositiveLine A.val ∧ (matrixOp (Fin (k+1))) A.val⁺ w ≠ 0 ∧
    (∀ i ∈ I, 0 < f (lineRepresentative w A.val) i) ∧
    0 < ⟪c,lineRepresentative w A.val⟫ ∧
    ‖hemisphereInverse c e (lineRepresentative w A.val)‖ < δ ∧
    0 < blockScalar c A.val ∧
    NegativeQuadratic (Matrix.toEuclideanCLM (𝕜 := ℝ) (matrixCompress e A.val))}
end RegularPatch
section RegularPatchContinuity
variable {domainIndices rangeIndices labels : Type*}
  [Fintype domainIndices] [Fintype rangeIndices] [Fintype labels]
  [DecidableEq domainIndices] [DecidableEq rangeIndices]
private lemma regularPatch_negative_isOpen (frame : (Euc domainIndices) →ₗᵢ[ℝ] (Euc rangeIndices)) :
    IsOpen {point : traceSphere rangeIndices |
      NegativeQuadratic (Matrix.toEuclideanCLM (𝕜 := ℝ) (matrixCompress frame point.val))} := by
  have hoperator : Continuous (fun matrix : Matrix domainIndices domainIndices ℝ =>
      Matrix.toEuclideanCLM (𝕜 := ℝ) matrix) :=
    (matrixOp domainIndices).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional
  exact negativeQuadratic_isOpen _
    (hoperator.comp ((matrixCompress frame).continuous_of_finiteDimensional.comp continuous_subtype_val))
omit [DecidableEq domainIndices] [DecidableEq rangeIndices] in
private lemma regularPatch_target_isOpen {f : (Euc rangeIndices) → labels → ℝ} (hf : Admissible f)
    (indices : Finset labels) (center : (Euc rangeIndices)) (frame : (Euc domainIndices) →ₗᵢ[ℝ] (Euc rangeIndices)) (radius : ℝ) :
    IsOpen ({vector : (Euc rangeIndices) | ∀ index ∈ indices, 0 < f vector index} ∩
      ({vector : (Euc rangeIndices) | 0 < ⟪center,vector⟫} ∩
        (fun vector => ‖hemisphereInverse center frame vector‖) ⁻¹' Iio radius)) := by
  have hpos : IsOpen {vector : (Euc rangeIndices) | ∀ index ∈ indices, 0 < f vector index} := by
    have he : {vector : (Euc rangeIndices) | ∀ index ∈ indices, 0 < f vector index} =
        ⋂ index ∈ indices, {vector : (Euc rangeIndices) | 0 < f vector index} := by ext vector; simp
    rw [he]
    exact isOpen_biInter_finset (fun index _ => isOpen_lt continuous_const (hf.smooth index).continuous)
  have hinner : IsOpen {vector : (Euc rangeIndices) | 0 < ⟪center,vector⟫} :=
    isOpen_lt continuous_const (continuous_const.inner continuous_id)
  exact hpos.inter ((hemisphereInverse_continuousOn center frame).norm.isOpen_inter_preimage
    hinner (isOpen_Iio : IsOpen (Iio radius)))
private lemma regularPatch_representative_isOpen (vector : (Euc rangeIndices)) {target : Set (Euc rangeIndices)}
    (htarget : IsOpen target) :
    IsOpen {point : traceSphere rangeIndices | (matrixOp rangeIndices) point.val⁺ vector ≠ 0 ∧
      lineRepresentative vector point.val ∈ target} := by
  have hval : Continuous (fun point : traceSphere rangeIndices => point.val) :=
    continuous_subtype_val
  have hself : ∀ point : traceSphere rangeIndices, IsSelfAdjoint point.val :=
    fun point => point.property.1
  have hmatrix : Continuous (fun matrix : Matrix rangeIndices rangeIndices ℝ => (matrixOp rangeIndices) matrix) :=
    ((matrixOp rangeIndices)).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional
  have hpositive : Continuous (fun point : traceSphere rangeIndices => point.val⁺) :=
    matrix_posPart_continuousOn.comp_continuous hval hself
  have hoperator : Continuous (fun point : traceSphere rangeIndices => (matrixOp rangeIndices) point.val⁺ vector) :=
    (hmatrix.comp hpositive).clm_apply continuous_const
  exact (lineRepresentative_continuousOn _ hval hself vector).isOpen_inter_preimage
    (isClosed_eq hoperator continuous_const).isOpen_compl htarget
private lemma regularPatch_isOpen_aux {f : (Euc rangeIndices) → labels → ℝ} (hf : Admissible f)
    (I : Finset labels) (w c : (Euc rangeIndices)) (e : (Euc domainIndices) →ₗᵢ[ℝ] (Euc rangeIndices)) (δ : ℝ) :
    IsOpen {A : traceSphere rangeIndices |
      IsUnit A.val ∧ HasPositiveLine A.val ∧ (matrixOp rangeIndices) A.val⁺ w ≠ 0 ∧
      (∀ i ∈ I, 0 < f (lineRepresentative w A.val) i) ∧
      0 < ⟪c,lineRepresentative w A.val⟫ ∧
      ‖hemisphereInverse c e (lineRepresentative w A.val)‖ < δ ∧
      0 < blockScalar c A.val ∧
      NegativeQuadratic (Matrix.toEuclideanCLM (𝕜 := ℝ) (matrixCompress e A.val))} := by
  let T := traceSphere rangeIndices
  have hA : Continuous (fun A : T => A.val) := continuous_subtype_val
  have hSA : ∀ A : T, IsSelfAdjoint A.val := fun A => A.property.1
  have hpre := regularPatch_representative_isOpen w (regularPatch_target_isOpen hf I c e δ)
  have hscalar : IsOpen {A : T | 0 < blockScalar c A.val} :=
    isOpen_lt continuous_const ((blockScalar_continuous c).comp hA)
  have hneg := regularPatch_negative_isOpen e
  apply isOpen_iff_mem_nhds.mpr
  rintro point ⟨hunit,hline,hvector,hlabels,hinner,hnorm,hblock,hquadratic⟩
  filter_upwards [(positive_line_isOpen _ hA hSA).mem_nhds ⟨hunit,hline⟩,
    hpre.mem_nhds ⟨hvector,hlabels,hinner,hnorm⟩,
    hscalar.mem_nhds hblock, hneg.mem_nhds hquadratic]
    with nearby hpositive hrepresentative hscalar hnegative
  exact ⟨hpositive.1,hpositive.2,hrepresentative.1,hrepresentative.2.1,
    hrepresentative.2.2.1,hrepresentative.2.2.2,hscalar,hnegative⟩
end RegularPatchContinuity
section RegularPatch
variable {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι] in
lemma Admissible.regularPatch_isOpen {f : (Euc (Fin (k+1))) → ι → ℝ} (hf : Admissible f)
    (I : Finset ι) (w c : (Euc (Fin (k+1)))) (e : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc (Fin (k+1)))) (δ : ℝ) : IsOpen (regularPatch f I w c e δ) :=
  regularPatch_isOpen_aux hf I w c e δ
end RegularPatch
end
end

section
open Set MeasureTheory
section
noncomputable def raySet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (y : E) : Set E :=
  {v | v = (‖v‖ / ‖y‖) • y}
lemma raySet_isClosed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (y : E) :
    IsClosed (raySet y) := isClosed_eq continuous_id ((continuous_norm.div_const _).smul continuous_const)
lemma mem_raySet_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v y : E} (hv : v ≠ 0) (hy : y ≠ 0) : v ∈ raySet y ↔ ∃ d : ℝ, 0 < d ∧ v = d • y := by
  constructor
  · intro h
    exact ⟨‖v‖ / ‖y‖,div_pos (norm_pos_iff.mpr hv) (norm_pos_iff.mpr hy),h⟩
  · rintro ⟨d,hd,rfl⟩
    change d • y = (‖d • y‖ / ‖y‖) • y
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hd,mul_div_cancel_right₀ _ (norm_ne_zero_iff.mpr hy)]
end
section
open Set
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
section MatrixFibres
variable {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
noncomputable def matrixRayFibre (F : (traceSphere (Fin (k+1))) → (Euc ι)) (y : (Euc ι)) (c : (Euc (Fin (k+1)))) : Set (traceSphere (Fin (k+1))) :=
  {A | F A ∈ raySet y ∧ A.val⁺ = Matrix.trace A.val⁺ • rankOne c}
omit [DecidableEq ι] in
lemma matrixRayFibre_closed (F : (traceSphere (Fin (k+1))) → (Euc ι)) (hF : Continuous F) (y : (Euc ι)) (c : (Euc (Fin (k+1)))) :
    IsClosed (matrixRayFibre F y c) := by
  have hp : Continuous (fun A : (traceSphere (Fin (k+1))) => A.val⁺) :=
    matrix_posPart_continuousOn.comp_continuous continuous_subtype_val (fun A => A.property.1)
  exact ((raySet_isClosed y).preimage hF).inter
    (isClosed_eq hp ((matrix_trace_continuous.comp hp).smul continuous_const))
lemma Admissible.facet_support {f : (Euc (Fin (k+1))) → ι → ℝ} (_hf : Admissible f)
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) {z : (Euc (Fin k))} (hz : z ∈ simplexInterior k)
    {c : (Euc (Fin (k+1)))} (hc : f c = facetPoint a z) : positiveSupport f c = I := by
  ext i
  rw [mem_positiveSupport,hc]
  by_cases hi : i ∈ I
  · exact iff_of_true (facetPoint_pos a hz i hi) hi
  · rw [facetPoint_zero a z hi]
    simp [hi]
omit [DecidableEq ι] in
lemma matrixRayFibre_representative {F : (traceSphere (Fin (k+1))) → (Euc ι)} {y : (Euc ι)} {w c : (Euc (Fin (k+1)))} (hc : ‖c‖ = 1)
    (hwc : 0 < ⟪w,c⟫) {A : (traceSphere (Fin (k+1)))} (hline : HasPositiveLine A.val)
    (hK : A ∈ matrixRayFibre F y c) : lineRepresentative w A.val = c :=
  lineRepresentative_split hc (hasPositiveLine_trace_pos hline) hK.2 hwc
omit [DecidableEq ι] in
lemma Admissible.matrixRayFibre_subset_patch {f : (Euc (Fin (k+1))) → ι → ℝ} (_hf : Admissible f)
    {F : (traceSphere (Fin (k+1))) → (Euc ι)} {y : (Euc ι)} {w c : (Euc (Fin (k+1)))} (hc : ‖c‖ = 1) (hwc : 0 < ⟪w,c⟫)
    {I : Finset ι} (hp : ∀ i ∈ I, 0 < f c i)
    (e : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc (Fin (k+1)))) (he : ∀ v, ⟪c,e v⟫ = 0)
    (hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u) {δ : ℝ} (hδ : 0 < δ)
    {A : (traceSphere (Fin (k+1)))} (hK : A ∈ matrixRayFibre F y c)
    (hU : IsUnit A.val) (hline : HasPositiveLine A.val) (hAw : (matrixOp (Fin (k+1))) A.val⁺ w ≠ 0) :
    A ∈ regularPatch f I w c e δ := by
  have hr := matrixRayFibre_representative hc hwc hline hK
  have ht := hasPositiveLine_trace_pos hline
  refine ⟨hU,hline,hAw,?_,?_,?_,?_,?_⟩
  · simpa only [hr] using hp
  · rw [hr,real_inner_self_eq_norm_sq,hc]; norm_num
  · rw [hr,hemisphereInverse,adjoint_normal c e he,smul_zero,norm_zero]
    exact hδ
  · rw [blockScalar_positiveLine A.property.1 hc ht hK.2]
    exact ht
  · exact blockCompress_negative e A.property.1 hU hc he hes ht hK.2
end MatrixFibres
end
end

section
namespace SimplicialChains
open Finset
section Supports
variable {E ι : Type*} [NormedAddCommGroup E] [DecidableEq ι]
end Supports
lemma annulus_ne_zero (n : ℕ) (hn : 0 < n) {x : Euc (Fin n)}
    (hx : x ∈ annulus n) : x ≠ 0 := by
  intro hzero
  have hp : (0:ℝ) < 1/(n:ℝ) := div_pos zero_lt_one (by exact_mod_cast hn)
  simp only [annulus, Set.mem_ofPred_eq, hzero, norm_zero] at hx
  linarith [hx.1]
end SimplicialChains
end

section
namespace SimplicialChains
open Finset
lemma compact_additive_locality {X A : Type*} [MetricSpace X] [CompactSpace X]
    [Fintype A] [DecidableEq A] {m : ℕ} [NeZero m]
    (b : Fin m → Bool) (f : X → Euc (Fin m))
    (g : A → X → Euc (Fin m)) (hf : Continuous f) (hg : ∀ a, Continuous (g a))
    (U : A → Set X) (hU : ∀ a, IsOpen (U a))
    (heq : ∀ a x, x ∈ U a → f x = g a x)
    (hcover : ∀ x, (∀ i, f x ∈ labelRegion i (b i)) → ∃ a, x ∈ U a)
    (hroot : ∀ a x, (∀ i, g a x ∈ labelRegion i (b i)) → x ∈ U a)
    (hdis : Pairwise (fun a a' => Disjoint (U a) (U a'))) :
    ∃ δ > 0, ∀ x : X,
      (∃ i : Fin m, (∀ y, dist y x < δ → sphereLabel (f y) ≠ (i.val,b i)) ∧
        ∀ a, ∃ j : Fin m, ∀ y, dist y x < δ → sphereLabel (g a y) ≠ (j.val,b j)) ∨
      ∃ a, (∀ y, dist y x < δ → f y = g a y) ∧
        ∀ a' ≠ a, ∃ j : Fin m, ∀ y, dist y x < δ → sphereLabel (g a' y) ≠ (j.val,b j) := by
  classical
  let c : Option A × (Option A → Fin m) → Set X := fun p => match p.1 with
    | none => (f ⁻¹' labelRegion (p.2 none) (b (p.2 none)))ᶜ ∩
        ⋂ a, (g a ⁻¹' labelRegion (p.2 (some a)) (b (p.2 (some a))))ᶜ
    | some a => U a ∩ ⋂ a' : {a' : A // a' ≠ a},
        (g a'.val ⁻¹' labelRegion (p.2 (some a'.val)) (b (p.2 (some a'.val))))ᶜ
  have hopen : ∀ p, IsOpen (c p) := by
    intro p
    cases ho : p.1 with
    | none =>
      simp only [c,ho]
      exact (((labelRegion_closed _ _).preimage hf).isOpen_compl).inter
        (isOpen_iInter_of_finite (fun a => ((labelRegion_closed _ _).preimage (hg a)).isOpen_compl))
    | some a =>
      simp only [c,ho]
      exact (hU a).inter (isOpen_iInter_of_finite
        (fun a' => ((labelRegion_closed _ _).preimage (hg a'.val)).isOpen_compl))
  have hc : (Set.univ : Set X) ⊆ ⋃ p, c p := by
    intro x _
    by_cases hx : ∃ a, x ∈ U a
    · obtain ⟨a,ha⟩ := hx
      have hm : ∀ a' : {a' : A // a' ≠ a}, ∃ j, g a'.val x ∉ labelRegion j (b j) := by
        intro a'
        apply not_forall.mp
        intro hh
        exact Set.disjoint_left.mp (hdis a'.property) (hroot a'.val x hh) ha
      choose j hj using hm
      let ji : Option A → Fin m := fun o => match o with
        | none => ⟨0,NeZero.pos m⟩
        | some a' => if h : a' ≠ a then j ⟨a',h⟩ else ⟨0,NeZero.pos m⟩
      refine Set.mem_iUnion.mpr ⟨(some a,ji),ha,Set.mem_iInter.mpr ?_⟩
      intro a'
      simpa only [ji,dif_pos a'.property,Set.mem_compl_iff,Set.mem_preimage] using hj a'
    · have hm : ∀ o : Option A, ∃ j, (match o with | none => f x | some a => g a x) ∉ labelRegion j (b j) := by
        intro o
        apply not_forall.mp
        intro hh
        cases o with
        | none => exact hx (hcover x hh)
        | some a => exact hx ⟨a,hroot a x hh⟩
      choose j hj using hm
      exact Set.mem_iUnion.mpr ⟨(none,j),hj none,Set.mem_iInter.mpr (fun a => hj (some a))⟩
  obtain ⟨δ,hδ,hball⟩ := lebesgue_number_lemma_of_metric isCompact_univ hopen hc
  refine ⟨δ,hδ,?_⟩
  intro x
  obtain ⟨⟨o,j⟩,hj⟩ := hball x (Set.mem_univ _)
  cases o with
  | none =>
    refine Or.inl ⟨j none,?_,?_⟩
    · intro y hy he
      exact (hj hy).1 (sphereLabel_mem_region _ _ _ he)
    · intro a
      refine ⟨j (some a),?_⟩
      intro y hy he
      exact Set.mem_iInter.mp (hj hy).2 a (sphereLabel_mem_region _ _ _ he)
  | some a =>
    refine Or.inr ⟨a,fun y hy => heq a y (hj hy).1,?_⟩
    intro a' ha'
    refine ⟨j (some a'),?_⟩
    intro y hy he
    exact Set.mem_iInter.mp (hj hy).2 ⟨a',ha'⟩ (sphereLabel_mem_region _ _ _ he)
lemma additive_approximation_coeff {A : Type*} [Fintype A] [DecidableEq A]
    (n m : ℕ) (hn : 0 < n) [NeZero m] (b : Fin m → Bool)
    (f : Euc (Fin n) → Euc (Fin m))
    (g : A → Euc (Fin n) → Euc (Fin m))
    (hf : ContinuousOn f (annulus n)) (hg : ∀ a, ContinuousOn (g a) (annulus n))
    (U : A → Set (annulus n)) (hU : ∀ a, IsOpen (U a))
    (heq : ∀ a (x : annulus n), x ∈ U a → f x.val = g a x.val)
    (hcover : ∀ x : annulus n, (∀ i, f x.val ∈ labelRegion i (b i)) → ∃ a, x ∈ U a)
    (hroot : ∀ a (x : annulus n), (∀ i, g a x.val ∈ labelRegion i (b i)) → x ∈ U a)
    (hdis : Pairwise (fun a a' => Disjoint (U a) (U a'))) :
    ∃ δ > 0, ∀ r : ℕ, (((n:ℝ)-1)/n)^r * 2 < δ →
      approximation n m r (fun x => sphereLabel (f x)) (crossFundamental n)
        ⟨crossFacet m b,crossFacet_mem m (NeZero.pos m) b⟩ =
      ∑ a, approximation n m r (fun x => sphereLabel (g a x)) (crossFundamental n)
        ⟨crossFacet m b,crossFacet_mem m (NeZero.pos m) b⟩ := by
  classical
  let : CompactSpace (annulus n) := isCompact_iff_compactSpace.mp (annulus_compact n)
  obtain ⟨δ,hδ,hlocal⟩ := compact_additive_locality b (fun x : annulus n => f x.val)
    (fun a (x : annulus n) => g a x.val) hf.domRestrict (fun a => (hg a).domRestrict)
    U hU heq hcover hroot hdis
  refine ⟨δ,hδ,?_⟩
  intro r hr
  let K := hemisphereComplex (n:ℝ) (E := Euc (Fin n))
  let t : {s : Finset SignedVertex // s ∈ cross m} :=
    ⟨crossFacet m b,crossFacet_mem m (NeZero.pos m) b⟩
  let T : Chain K →ₗ[F₂] F₂ := (Finsupp.lapply t).comp (mapChains K (cross m) (fun x => sphereLabel (f x)))
  let R : A → Chain K →ₗ[F₂] F₂ := fun a =>
    (Finsupp.lapply t).comp (mapChains K (cross m) (fun x => sphereLabel (g a x)))
  change T (fineCrossMap n r (crossFundamental n)) = ∑ a, R a (fineCrossMap n r (crossFundamental n))
  rw [← LinearMap.sum_apply]
  apply linearMap_eq_of_support T (∑ a, R a) _
  intro s hs
  rw [LinearMap.sum_apply]
  have heT : T (simplex K s.val) = mapSimplex (cross m) (fun x => sphereLabel (f x)) s.val t := by
    exact congrArg (fun c : Chain (cross m) => c t) (mapChains_simplex K (cross m) _ s.property)
  have heR (a : A) : R a (simplex K s.val) = mapSimplex (cross m) (fun x => sphereLabel (g a x)) s.val t := by
    exact congrArg (fun c : Chain (cross m) => c t) (mapChains_simplex K (cross m) _ s.property)
  simp only [heT,heR]
  have ha : ∀ x ∈ s.val, x ∈ annulus n := fun x hx => hemisphere_vertex_annulus n hn s.property hx
  obtain ⟨x,hx⟩ := s.property.1
  have hmesh := fineCrossMap_mesh n r (crossFundamental n) hs
  have hball (y) (hy : y ∈ s.val) : dist (⟨y,ha y hy⟩ : annulus n) ⟨x,ha x hx⟩ < δ :=
    (hmesh y hy x hx).trans_lt hr
  rcases hlocal ⟨x,ha x hx⟩ with ⟨i,hi,hgmiss⟩ | ⟨a,heq,hgmiss⟩
  · rw [mapSimplex_coeff_zero_of_ne (cross m) _ s.val t
      (image_ne_crossFacet_of_missing s.val _ b i (fun y hy => hi ⟨y,ha y hy⟩ (hball y hy)))]
    symm
    apply Finset.sum_eq_zero
    intro a _
    obtain ⟨j,hj⟩ := hgmiss a
    exact mapSimplex_coeff_zero_of_ne (cross m) _ s.val t
      (image_ne_crossFacet_of_missing s.val _ b j (fun y hy => hj ⟨y,ha y hy⟩ (hball y hy)))
  · rw [Finset.sum_eq_single a]
    · have himg : s.val.image (fun y => sphereLabel (f y)) = s.val.image (fun y => sphereLabel (g a y)) := by
        apply Finset.image_congr
        intro y hy
        exact congrArg sphereLabel (heq ⟨y,ha y hy⟩ (hball y hy))
      simp only [mapSimplex,himg]
    · intro a' _ ha'
      obtain ⟨j,hj⟩ := hgmiss a' ha'
      exact mapSimplex_coeff_zero_of_ne (cross m) _ s.val t
        (image_ne_crossFacet_of_missing s.val _ b j (fun y hy => hj ⟨y,ha y hy⟩ (hball y hy)))
    · simp
end SimplicialChains
end

section
open Set MeasureTheory
section
open Finset Set
open scoped Topology
lemma finite_positive_bound {A : Type*} [Fintype A] (d : A → ℝ) (hd : ∀ a, 0 < d a) :
    ∃ ε > 0, ∀ a, ε < d a := by
  classical
  by_cases hne : Nonempty A
  · let r : ℝ := Finset.univ.inf' Finset.univ_nonempty d
    have hr : 0 < r := (Finset.lt_inf'_iff _).mpr (by simpa using hd)
    refine ⟨r/2,by positivity,fun a => ?_⟩
    exact (by linarith : r/2 < r).trans_le (Finset.inf'_le _ (Finset.mem_univ a))
  · exact ⟨1,zero_lt_one,fun a => False.elim (hne ⟨a⟩)⟩
end
namespace SimplicialChains
open Finset Set
lemma odd_homotopy_local_models {A : Type*} [Fintype A] [DecidableEq A]
    (n : ℕ) (hn : 1 < n) [NeZero n] (b : Fin n → Bool)
    (H : ℝ × Euc (Fin n) → Euc (Fin n))
    (hH : ContinuousOn H (Icc (0:ℝ) 1 ×ˢ annulus n))
    (hHz : ∀ p ∈ Icc (0:ℝ) 1 ×ˢ annulus n, H p ≠ 0)
    (hHo : ∀ x ∈ annulus n, H (0,-x) = -H (0,x))
    (G : A → Euc (Fin n) → Euc (Fin n))
    (hG : ∀ a, ContinuousOn (G a) (annulus n))
    (hGz : ∀ a x, x ∈ annulus n → G a x ≠ 0)
    (hGo : ∀ a x, x ∈ annulus n → G a (-x) = -G a x)
    (U : A → Set (annulus n)) (hU : ∀ a, IsOpen (U a))
    (heq : ∀ a (x : annulus n), x ∈ U a → H (1,x.val) = G a x.val)
    (hcover : ∀ x : annulus n, unitRadial (H (1,x.val)) = facetCenter n b → ∃ a, x ∈ U a)
    (hroot : ∀ a (x : annulus n), unitRadial (G a x.val) = facetCenter n b → x ∈ U a)
    (hdis : Pairwise (fun a a' => Disjoint (U a) (U a'))) : (Fintype.card A : F₂) = 1 := by
  classical
  let f : Euc (Fin n) → Euc (Fin n) := fun x => unitRadial (H (1,x))
  let g : A → Euc (Fin n) → Euc (Fin n) := fun a x => unitRadial (G a x)
  have hfc : ContinuousOn f (annulus n) :=
    (unitRadial_continuousOn (S := {y | y ≠ 0}) (fun _ h => h)).comp
      (hH.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ hx => ⟨⟨zero_le_one,le_rfl⟩,hx⟩))
      (fun x hx => hHz (1,x) ⟨⟨zero_le_one,le_rfl⟩,hx⟩)
  have hfn (x) (hx : x ∈ annulus n) : ‖f x‖ = 1 := unitRadial_norm (hHz (1,x) ⟨⟨zero_le_one,le_rfl⟩,hx⟩)
  have hgc (a) : ContinuousOn (g a) (annulus n) :=
    (unitRadial_continuousOn (S := {y | y ≠ 0}) (fun _ h => h)).comp (hG a) (hGz a)
  have hgn (a x) (hx : x ∈ annulus n) : ‖g a x‖ = 1 := unitRadial_norm (hGz a x hx)
  obtain ⟨δa,hδa,hadd⟩ := additive_approximation_coeff n n (by omega) b f g hfc hgc U hU
    (fun a x hx => congrArg unitRadial (heq a x hx))
    (fun x hx => hcover x ((all_labelRegions_iff_center n b _ (hfn _ x.property)).mp hx))
    (fun a x hx => hroot a x ((all_labelRegions_iff_center n b _ (hgn a _ x.property)).mp hx)) hdis
  obtain ⟨δh,hδh,hhom⟩ := normalized_homotopy_chains n n (by omega) le_rfl H hH hHz
  have hc0 : ContinuousOn (fun x => unitRadial (H (0,x))) (annulus n) :=
    (unitRadial_continuousOn (S := {y | y ≠ 0}) (fun _ h => h)).comp
      (hH.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ hx => ⟨⟨le_rfl,zero_le_one⟩,hx⟩))
      (fun x hx => hHz (0,x) ⟨⟨le_rfl,zero_le_one⟩,hx⟩)
  obtain ⟨δ0,hδ0,hdeg0⟩ := eventually_odd_sphere_degree n hn _ hc0
    (fun x hx => unitRadial_norm (hHz (0,x) ⟨⟨le_rfl,zero_le_one⟩,hx⟩))
    (fun x hx => by rw [hHo x hx,unitRadial_neg])
  have hgodd : ∀ a, ∃ δ > 0, ∀ r, (((n:ℝ)-1)/n)^r * 2 < δ →
      approximation n n r (fun x => sphereLabel (g a x)) (crossFundamental n) = crossFundamental n := by
    intro a
    apply eventually_odd_sphere_degree n hn _ (hgc a) (hgn a)
    intro x hx
    change unitRadial (G a (-x)) = -unitRadial (G a x)
    rw [hGo a x hx,unitRadial_neg]
  choose dg hdg hdgprop using hgodd
  obtain ⟨δg,hδg,hδgb⟩ := finite_positive_bound dg hdg
  obtain ⟨r,hr⟩ := exists_small_cross_mesh n (by omega) (lt_min hδ0 (lt_min hδh (lt_min hδa hδg)))
  have hr0 := hr.trans_le (min_le_left _ _)
  have hrh := hr.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hra := hr.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hrg := hr.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have he0 : approximation n n r (fun x => sphereLabel (f x)) (crossFundamental n) = crossFundamental n :=
    (hhom r hrh).symm.trans (hdeg0 r hr0)
  have hadd' := hadd r hra
  rw [he0,crossFundamental_coeff n hn b] at hadd'
  have hm (a : A) : approximation n n r (fun x => sphereLabel (g a x)) (crossFundamental n)
      ⟨crossFacet n b,crossFacet_mem n (NeZero.pos n) b⟩ = 1 := by
    rw [hdgprop a r (hrg.trans (hδgb a)),crossFundamental_coeff n hn b]
  simpa only [hm,Finset.sum_const,Finset.card_univ,nsmul_one] using hadd'.symm
end SimplicialChains
end

section
open Set MeasureTheory
section
open scoped MatrixOrder Matrix.Norms.L2Operator
open SimplicialChains Set
section TraceLocalModels
variable {ν ι κ : Type*} [Fintype ν] [LinearOrder ν] [Nonempty ν] [Fintype ι]
  [Fintype κ] [DecidableEq κ]
omit [Nonempty ν] in
lemma trace_odd_local_models
    (hc : Fintype.card (UpperTriangle ν) = Fintype.card ι) (hn : 1 < Fintype.card ι)
    (H : ℝ × traceSphere ν → (Euc ι))
    (hH : ContinuousOn H (Icc (0:ℝ) 1 ×ˢ univ))
    (hHz : ∀ t ∈ Icc (0:ℝ) 1, ∀ A : traceSphere ν, H (t,A) ≠ 0)
    (hHo : ∀ A B : traceSphere ν, B.val = -A.val → H (0,B) = -H (0,A))
    (G : κ → traceSphere ν → (Euc ι)) (hG : ∀ a, Continuous (G a))
    (hGz : ∀ a A, G a A ≠ 0)
    (hGo : ∀ a (A B : traceSphere ν), B.val = -A.val → G a B = -G a A)
    (U : κ → Set (traceSphere ν)) (hU : ∀ a, IsOpen (U a))
    (heq : ∀ a A, A ∈ U a → H (1,A) = G a A)
    {y : (Euc ι)} (hy : y ≠ 0)
    (hcover : ∀ A : traceSphere ν, (∃ d : ℝ, 0 < d ∧ H (1,A) = d • y) → ∃ a, A ∈ U a)
    (hroot : ∀ a A, (∃ d : ℝ, 0 < d ∧ G a A = d • y) → A ∈ U a)
    (hdis : Pairwise (fun a a' => Disjoint (U a) (U a'))) : (Fintype.card κ : F₂) = 1 := by
  classical
  let n := Fintype.card ι
  have hnz : n ≠ 0 := by dsimp [n]; omega
  let : NeZero n := ⟨hnz⟩
  let ea : UpperTriangle ν ≃ Fin n := (Fintype.equivFin _).trans (finCongr hc)
  let eaL := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ ea
  let ebL := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fintype.equivFin ι)
  let b : Fin n → Bool := fun _ => false
  let R := Submodule.reflection (ℝ ∙ (ebL (unitRadial y) - facetCenter n b))ᗮ
  let L : (Euc ι) ≃ₗᵢ[ℝ] Euc (Fin n) := ebL.trans R
  have hRy : L (unitRadial y) = facetCenter n b :=
    Submodule.reflection_sub ((ebL.norm_map _).trans (unitRadial_norm hy) |>.trans (facetCenter_norm n b).symm)
  have hray (v : (Euc ι)) (hv : v ≠ 0) (he : unitRadial (L v) = facetCenter n b) :
      ∃ d : ℝ, 0 < d ∧ v = d • y := by
    have hu : unitRadial v = unitRadial y := by
      apply L.injective
      rw [hRy]
      simpa only [unitRadial,map_smul,L.norm_map] using he
    refine ⟨‖v‖ / ‖y‖,div_pos (norm_pos_iff.mpr hv) (norm_pos_iff.mpr hy),?_⟩
    have hh := congrArg (fun z : (Euc ι) => ‖v‖ • z) hu
    simpa only [unitRadial,smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv),one_smul,div_eq_mul_inv] using hh
  let A : Euc (Fin n) → (SqMat ν) := fun x => symmetricCoordinates (eaL.symm x)
  have hAc : Continuous A := symmetricCoordinates.continuous_of_finiteDimensional.comp eaL.symm.continuous
  have hAs (x) : IsSelfAdjoint (A x) := symmetricCoordinates_selfAdjoint _
  have hAz (x) (hx : x ∈ annulus n) : A x ≠ 0 := by
    intro hz
    have h0 : eaL.symm x = 0 := symmetricCoordinates_injective (hz.trans (map_zero _).symm)
    exact annulus_ne_zero n (by omega) hx (eaL.symm.injective (h0.trans (map_zero _).symm))
  let N : annulus n → traceSphere ν := fun x =>
    ⟨traceRadial (A x.val),traceRadial_mem (hAs _) (hAz _ x.property)⟩
  have hN : Continuous N := by
    apply Continuous.subtype_mk
    exact traceRadial_continuousOn.comp_continuous (hAc.comp continuous_subtype_val) (fun x => hAz _ x.property)
  have hNneg (x) (hx : x ∈ annulus n) (hxn : -x ∈ annulus n) :
      (N ⟨-x,hxn⟩).val = -(N ⟨x,hx⟩).val := by simp only [N,A,map_neg,traceRadial_neg]
  let H' : ℝ × Euc (Fin n) → Euc (Fin n) := fun p =>
    if hx : p.2 ∈ annulus n then L (H (p.1,N ⟨p.2,hx⟩)) else 0
  have hH' : ContinuousOn H' (Icc (0:ℝ) 1 ×ˢ annulus n) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    let S := Icc (0:ℝ) 1 ×ˢ annulus n
    have hcN : Continuous (fun p : S => N ⟨p.val.2,p.property.2⟩) :=
      hN.comp (continuous_subtype_val.snd.subtype_mk _)
    have hg := hH.comp_continuous (continuous_subtype_val.fst.prodMk hcN) (fun p : S => ⟨p.property.1,mem_univ _⟩)
    apply (L.continuous.comp hg).congr
    intro p
    simp only [Set.domRestrict_apply,Function.comp_apply,H',dif_pos p.property.2]
  have hHz' : ∀ p ∈ Icc (0:ℝ) 1 ×ˢ annulus n, H' p ≠ 0 := by
    intro p hp hz
    exact hHz _ hp.1 _ (L.injective (by simpa only [H',dif_pos hp.2,map_zero] using hz))
  have hHo' : ∀ x ∈ annulus n, H' (0,-x) = -H' (0,x) := by
    intro x hx
    have hxn : -x ∈ annulus n := by simpa only [annulus,Set.mem_ofPred_eq,norm_neg] using hx
    simp only [H',dif_pos hx,dif_pos hxn,hHo _ _ (hNneg x hx hxn),map_neg]
  let G' : κ → Euc (Fin n) → Euc (Fin n) := fun a x =>
    if hx : x ∈ annulus n then L (G a (N ⟨x,hx⟩)) else 0
  have hG' (a) : ContinuousOn (G' a) (annulus n) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    apply (L.continuous.comp ((hG a).comp hN)).congr
    intro x
    simp only [Set.domRestrict_apply,Function.comp_apply,G',dif_pos x.property]
  have hGz' (a x) (hx : x ∈ annulus n) : G' a x ≠ 0 := by
    intro hz
    exact hGz a _ (L.injective (by simpa only [G',dif_pos hx,map_zero] using hz))
  have hGo' (a x) (hx : x ∈ annulus n) : G' a (-x) = -G' a x := by
    have hxn : -x ∈ annulus n := by simpa only [annulus,Set.mem_ofPred_eq,norm_neg] using hx
    simp only [G',dif_pos hx,dif_pos hxn,hGo a _ _ (hNneg x hx hxn),map_neg]
  apply odd_homotopy_local_models n hn b H' hH' hHz' hHo' G' hG' hGz' hGo'
    (fun a => N ⁻¹' U a) (fun a => (hU a).preimage hN)
  · intro a x hx
    simp only [H',G',dif_pos x.property,heq a _ hx]
  · intro x hx
    apply hcover (N x)
    apply hray _ (hHz _ ⟨zero_le_one,le_rfl⟩ _)
    simpa only [H',dif_pos x.property] using hx
  · intro a x hx
    apply hroot a (N x)
    apply hray _ (hGz a _)
    simpa only [G',dif_pos x.property] using hx
  · intro a a' haa
    exact (hdis haa).preimage N
end TraceLocalModels
end
end

section
open Set MeasureTheory
section
open Finset
open scoped RealInnerProductSpace
section FinitePatch
variable {X E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Fintype A]
noncomputable def finitePatch (f : X → E) (g : A → X → E) (q : A → X → ℝ)
    (t : ℝ) (x : X) : E := f x + ∑ a, (t * q a x) • (g a x - f x)
lemma finitePatch_continuous [TopologicalSpace X] {f : X → E} {g : A → X → E} {q : A → X → ℝ}
    (hf : Continuous f) (hg : ∀ a, Continuous (g a)) (hq : ∀ a, Continuous (q a)) :
    Continuous (fun p : ℝ × X => finitePatch f g q p.1 p.2) := by
  apply (hf.comp continuous_snd).add
  apply continuous_finsetSum
  intro a _
  exact (continuous_fst.mul ((hq a).comp continuous_snd)).smul
    (((hg a).comp continuous_snd).sub (hf.comp continuous_snd))
lemma finitePatch_zero (f : X → E) (g : A → X → E) (q : A → X → ℝ) (x : X) :
    finitePatch f g q 0 x = f x := by simp [finitePatch]
lemma finitePatch_of_all_zero (f : X → E) (g : A → X → E) (q : A → X → ℝ)
    (t : ℝ) (x : X) (hq : ∀ a, q a x = 0) : finitePatch f g q t x = f x := by
  simp [finitePatch,hq]
lemma finitePatch_of_disjoint [DecidableEq A]
    (f : X → E) (g : A → X → E) (q : A → X → ℝ) (t : ℝ) (x : X) (a : A)
    (hq : ∀ a' ≠ a, q a' x = 0) :
    finitePatch f g q t x = (1-t*q a x) • f x + (t*q a x) • g a x := by
  unfold finitePatch
  rw [Finset.sum_eq_single a]
  · module
  · intro a' _ ha'
    simp [hq a' ha']
  · simp
lemma finitePatch_one_of_disjoint [DecidableEq A]
    (f : X → E) (g : A → X → E) (q : A → X → ℝ) (x : X) (a : A)
    (h1 : q a x = 1) (hq : ∀ a' ≠ a, q a' x = 0) :
    finitePatch f g q 1 x = g a x := by
  rw [finitePatch_of_disjoint f g q 1 x a hq,h1]
  simp
lemma finitePatch_cases [DecidableEq A] (f : X → E) (g : A → X → E)
    (q : A → X → ℝ) (t : ℝ) (x : X)
    (hq : Pairwise (fun a a' => Disjoint (Function.support (q a)) (Function.support (q a')))) :
    finitePatch f g q t x = f x ∨ ∃ a, q a x ≠ 0 ∧
      finitePatch f g q t x = (1-t*q a x) • f x + (t*q a x) • g a x := by
  by_cases hh : ∃ a, q a x ≠ 0
  · obtain ⟨a,ha⟩ := hh
    refine Or.inr ⟨a,ha,finitePatch_of_disjoint f g q t x a ?_⟩
    intro a' ha'
    by_contra hn
    exact Set.disjoint_left.mp (hq ha') hn ha
  · push Not at hh
    exact Or.inl (finitePatch_of_all_zero f g q t x hh)
lemma finitePatch_ne_zero [DecidableEq A] (f : X → E) (g : A → X → E)
    (q : A → X → ℝ) (t : ℝ) (x : X)
    (hq : Pairwise (fun a a' => Disjoint (Function.support (q a)) (Function.support (q a'))))
    (ht : t ∈ Set.Icc (0:ℝ) 1) (hqb : ∀ a, q a x ∈ Set.Icc (0:ℝ) 1)
    (hf : f x ≠ 0)
    (hseg : ∀ a, q a x ≠ 0 → ∀ s ∈ Set.Icc (0:ℝ) 1,
      (1-s) • f x + s • g a x ≠ 0) : finitePatch f g q t x ≠ 0 := by
  rcases finitePatch_cases f g q t x hq with he | ⟨a,ha,he⟩
  · rwa [he]
  · rw [he]
    exact hseg a ha (t*q a x) ⟨mul_nonneg ht.1 (hqb a).1,
      (mul_le_mul_of_nonneg_left (hqb a).2 ht.1).trans (by simpa using ht.2)⟩
end FinitePatch
end
end

section
open Set MeasureTheory
section
open Set Finset
lemma finite_closed_cutoffs {A X : Type*} [Fintype A] [DecidableEq A]
    [TopologicalSpace X] [NormalSpace X]
    (K S : A → Set X) (hK : ∀ a, IsClosed (K a)) (hS : ∀ a, IsOpen (S a))
    (hKS : ∀ a, K a ⊆ S a) (hdis : Pairwise (fun a b => Disjoint (K a) (K b))) :
    ∃ U : A → Set X, ∃ q : A → C(X,ℝ), (∀ a, IsOpen (U a)) ∧
      (∀ a, K a ⊆ U a) ∧ (∀ a x, q a x ∈ Icc (0:ℝ) 1) ∧
      (∀ a x, x ∈ U a → q a x = 1) ∧
      (∀ a x, q a x ≠ 0 → x ∈ S a) ∧
      Pairwise (fun a b => Disjoint (Function.support (q a)) (Function.support (q b))) := by
  classical
  let Z : A → Set X := fun a => (S a)ᶜ ∪ ⋃ b ∈ (Finset.univ.erase a : Finset A), K b
  have hZ (a) : IsClosed (Z a) := (hS a).isClosed_compl.union (isClosed_biUnion_finset fun b _ => hK b)
  have hd (a) : Disjoint (Z a) (K a) := by
    apply Set.disjoint_left.mpr
    intro x hx hxa
    rcases hx with hs | hb
    · exact hs (hKS a hxa)
    · obtain ⟨b,hb,hxb⟩ := Set.mem_iUnion₂.mp hb
      exact Set.disjoint_left.mp (hdis (Finset.ne_of_mem_erase hb)) hxb hxa
  have hs (a) := exists_continuous_zero_one_of_isClosed (hZ a) (hK a) (hd a)
  choose p hp0 hp1 hpb using hs
  let score : A → X → ℝ := fun a x => 2*p a x - ∑ b, p b x
  have hscore (a) : Continuous (score a) :=
    ((p a).continuous.const_mul 2).sub (continuous_finsetSum _ (fun b _ => (p b).continuous))
  have hscoreK (a x) (hx : x ∈ K a) : score a x = 1 := by
    have hpothers (b) (hb : b ≠ a) : p b x = 0 := hp0 b (Or.inr (Set.mem_iUnion₂.mpr ⟨a,Finset.mem_erase.mpr ⟨Ne.symm hb,Finset.mem_univ _⟩,hx⟩))
    dsimp [score]
    rw [Finset.sum_eq_single a]
    · rw [hp1 a hx]; norm_num
    · intro b _ hb; exact hpothers b hb
    · simp
  let U : A → Set X := fun a => {x | (3/4:ℝ) < score a x}
  let q : A → C(X,ℝ) := fun a => ⟨fun x => max 0 (min 1 (4*(score a x-1/2))),
    continuous_const.max (continuous_const.min (((hscore a).sub continuous_const).const_mul 4))⟩
  have hpos (a x) (hx : q a x ≠ 0) : (1/2:ℝ) < score a x := by
    change max 0 (min 1 (4*(score a x-1/2))) ≠ 0 at hx
    by_contra hn
    apply hx
    exact max_eq_left (le_trans (min_le_right _ _) (by linarith))
  refine ⟨U,q,fun a => isOpen_lt continuous_const (hscore a),?_,?_,?_,?_,?_⟩
  · intro a x hx
    change (3/4:ℝ) < score a x
    rw [hscoreK a x hx]; norm_num
  · intro a x
    exact ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩
  · intro a x hx
    change max 0 (min 1 (4*(score a x-1/2))) = 1
    rw [min_eq_left (by change (3/4:ℝ) < score a x at hx; linarith)]
    norm_num
  · intro a x hx
    by_contra hn
    have hz : p a x = 0 := hp0 a (Or.inl hn)
    have hsum : 0 ≤ ∑ b, p b x := Finset.sum_nonneg (fun b _ => (hpb b x).1)
    have hh := hpos a x hx
    dsimp [score] at hh
    rw [hz] at hh
    linarith
  · intro a b hab
    apply Set.disjoint_left.mpr
    intro x hxa hxb
    have ha := hpos a x hxa
    have hb := hpos b x hxb
    have hs : p a x + p b x ≤ ∑ c, p c x := by
      calc
        _ = ∑ c ∈ ({a,b} : Finset A), p c x := by simp [hab]
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun c _ _ => (hpb c x).1)
    dsimp [score] at ha hb
    linarith
end
end

section
open Set MeasureTheory
section
open Set SimplicialChains
open scoped MatrixOrder Matrix.Norms.L2Operator
section TracePatchModels
variable {ν ι κ : Type*} [Fintype ν] [LinearOrder ν] [Nonempty ν] [Fintype ι]
  [Fintype κ] [DecidableEq κ]
omit [Nonempty ν] in
lemma trace_patch_models
    (hc : Fintype.card (UpperTriangle ν) = Fintype.card ι) (hn : 1 < Fintype.card ι)
    (F : traceSphere ν → (Euc ι)) (hF : Continuous F) (hFz : ∀ A, F A ≠ 0)
    (hFo : ∀ A B : traceSphere ν, B.val = -A.val → F B = -F A)
    (G : κ → traceSphere ν → (Euc ι)) (hG : ∀ a, Continuous (G a))
    (hGz : ∀ a A, G a A ≠ 0)
    (hGo : ∀ a (A B : traceSphere ν), B.val = -A.val → G a B = -G a A)
    (K S : κ → Set (traceSphere ν)) (hK : ∀ a, IsClosed (K a)) (hS : ∀ a, IsOpen (S a))
    (hKS : ∀ a, K a ⊆ S a) (hKd : Pairwise (fun a b => Disjoint (K a) (K b)))
    {y : (Euc ι)} (hy : y ≠ 0)
    (hcover : ∀ A, (∃ d : ℝ, 0 < d ∧ F A = d • y) → ∃ a, A ∈ K a)
    (hroot : ∀ a A, (∃ d : ℝ, 0 < d ∧ G a A = d • y) → A ∈ K a)
    (hseg : ∀ a A, A ∈ S a → ∀ t ∈ Icc (0:ℝ) 1, (1-t) • F A + t • G a A ≠ 0)
    (hhit : ∀ a A, A ∈ S a → ∀ t ∈ Icc (0:ℝ) 1,
      (∃ d : ℝ, 0 < d ∧ (1-t) • F A + t • G a A = d • y) → A ∈ K a) :
    (Fintype.card κ : F₂) = 1 := by
  classical
  obtain ⟨U,q,hU,hKU,hqb,hq1,hqS,hqd⟩ := finite_closed_cutoffs K S hK hS hKS hKd
  let H : ℝ × traceSphere ν → (Euc ι) := fun p => finitePatch F G (fun a => q a) p.1 p.2
  have hH : Continuous H := finitePatch_continuous hF hG (fun a => (q a).continuous)
  have hHz (t) (ht : t ∈ Icc (0:ℝ) 1) (A) : H (t,A) ≠ 0 :=
    finitePatch_ne_zero F G (fun a => q a) t A hqd ht (fun a => hqb a A) (hFz A)
      (fun a ha => hseg a A (hqS a A ha))
  refine trace_odd_local_models hc hn H hH.continuousOn hHz
    (fun A B hB => by simpa only [H,finitePatch_zero] using hFo A B hB)
    G hG hGz hGo U hU ?_ hy ?_ ?_ ?_
  · intro a A hA
    apply finitePatch_one_of_disjoint F G (fun a => q a) A a (hq1 a A hA)
    intro b hba
    by_contra hb
    exact Set.disjoint_left.mp (hqd hba) hb (by
      change q a A ≠ 0
      rw [hq1 a A hA]; exact one_ne_zero)
  · intro A hA
    rcases finitePatch_cases F G (fun a => q a) 1 A hqd with he | ⟨a,ha,he⟩
    · have hr : ∃ d : ℝ, 0 < d ∧ F A = d • y := by
        simpa only [H,he] using hA
      obtain ⟨a,ha⟩ := hcover A hr
      exact ⟨a,hKU a ha⟩
    · refine ⟨a,hKU a (hhit a A (hqS a A ha) (q a A) (hqb a A) ?_)⟩
      simpa only [H,he,one_mul] using hA
  · intro a A hA
    exact hKU a (hroot a A hA)
  · intro a b hab
    exact (hqd hab).mono
      (fun A hA => by change q a A ≠ 0; rw [hq1 a A hA]; exact one_ne_zero)
      (fun A hA => by change q b A ≠ 0; rw [hq1 b A hA]; exact one_ne_zero)
end TracePatchModels
end
end

section
open Set MeasureTheory
section
open Set SimplicialChains
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
section MatrixParity
variable {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma Admissible.regular_facet_level_odd {f : (Euc (Fin (k+1))) → ι → ℝ} (hf : Admissible f)
    (hdim : Fintype.card (UpperTriangle (Fin (k+1))) = Fintype.card ι)
    (hn : 1 < Fintype.card ι) {I : Finset ι} [Nonempty ↥(Iᶜ : Finset ι)]
    (a : Fin (k+1) ≃ ↥I)
    (hmax : ∀ u : (Euc (Fin (k+1))), ‖u‖ = 1 → I ⊆ positiveSupport f u → positiveSupport f u = I)
    {w : (Euc (Fin (k+1)))} (hw : ‖w‖ = 1) (hwi : ∀ i ∈ I, 0 < f w i)
    (e : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc (Fin (k+1)))) (he : ∀ v, ⟪w,e v⟫ = 0)
    (hes : ∀ u, ⟪w,u⟫ = 0 → ∃ v, e v = u) {z : (Euc (Fin k))} (hz : z ∈ simplexInterior k)
    (hr : ∀ v, baseCoordinates f w e a v = z → (fderiv ℝ (baseCoordinates f w e a) v).det ≠ 0)
    (hfin : (orientedLevel f w (facetPoint a z)).Finite) :
    (Nat.card (orientedLevel f w (facetPoint a z)) : F₂) = 1 := by
  classical
  let L := orientedLevel f w (facetPoint a z)
  let : Fintype L := hfin.fintype
  have hI : I.Nonempty := ⟨(a 0).val,(a 0).property⟩
  have hc (c : L) : ‖c.val‖ = 1 := c.property.1
  have hcv (c : L) : f c.val = facetPoint a z := c.property.2.1
  have hcw (c : L) : 0 < ⟪w,c.val⟫ := hf.orientedLevel_inner_pos hI hw hwi (facetPoint_pos a hz) c.property
  have hcp (c : L) : positiveSupport f c.val = I := hf.facet_support a hz (hcv c)
  have hdata (c : L) := hf.regular_model_data a hw (hc c) e he hes (hcw c) (hcv c) hr
  choose d D δ hd hds hδ hreg using hdata
  let v := uniformVector ↥(Iᶜ : Finset ι)
  have hv (i : ↥(Iᶜ : Finset ι)) : 0 < v i := by
    change 0 < (Fintype.card ↥(Iᶜ : Finset ι) : ℝ)⁻¹
    positivity
  have hvs : ∑ i, v i = 1 := coordinateSum_uniform _
  let y : (Euc ι) := blockVector I (1/2:ℝ) (facetPoint a z) (1/2:ℝ) v
  have hy : y ≠ 0 := blockVector_nonzero hI (by norm_num) (facetPoint_pos a hz) _
  let F : (traceSphere (Fin (k+1))) → (Euc ι) := fun A => WithLp.toLp 2 (signedExtension f A.val)
  let G : L → (traceSphere (Fin (k+1))) → (Euc ι) := fun c A => WithLp.toLp 2 (localBlockModel f c.val (d c) a (D c) A.val)
  let K : L → Set (traceSphere (Fin (k+1))) := fun c => matrixRayFibre F y c.val
  let S : L → Set (traceSphere (Fin (k+1))) := fun c => regularPatch f I w c.val (d c) (δ c)
  have hF : Continuous F := (PiLp.continuous_toLp 2 _).comp
    (hf.signedExtension_continuousOn.comp_continuous continuous_subtype_val (fun A => A.property.1))
  have hFz (A : (traceSphere (Fin (k+1)))) : F A ≠ 0 := by
    intro hzA
    exact traceSphere_ne_zero A.property ((hf.signedExtension_eq_zero_iff A.property.1).mp (WithLp.toLp_injective 2 hzA))
  have hFroot (A : (traceSphere (Fin (k+1)))) (hA : F A ∈ raySet y) :
      IsUnit A.val ∧ HasPositiveLine A.val ∧
      (Matrix.toEuclideanCLM (n := Fin (k+1)) (𝕜 := ℝ) A.val⁺) w ≠ 0 ∧
      0 < Matrix.trace A.val⁻ ∧ lineRepresentative w A.val ∈ L := by
    obtain ⟨t,ht,hAt⟩ := (mem_raySet_iff (hFz A) hy).mp hA
    exact hf.original_ray_level hI hmax hw hwi (facetPoint_pos a hz) (fun i hi => facetPoint_zero a z hi)
      (facetPoint_sum a z) hv hvs A.property ht hAt
  have hG (c : L) : Continuous (G c) := (PiLp.continuous_toLp 2 _).comp
    ((hf.localBlockModel_continuousOn c.val (d c) a (D c)).comp_continuous continuous_subtype_val
      (fun A => A.property.1))
  have hGz (c : L) (A : (traceSphere (Fin (k+1)))) : G c A ≠ 0 := by
    intro hzA
    exact hf.localBlockModel_ne_zero (hc c) (d c) (hd c) (hds c) a (hcp c) (D c)
      A.property.1 (traceSphere_ne_zero A.property) (WithLp.toLp_injective 2 hzA)
  have hKS (c : L) : K c ⊆ S c := by
    intro A hA
    have hh := hFroot A hA.1
    exact hf.matrixRayFibre_subset_patch (hc c) (hcw c) (by simpa only [hcv c] using facetPoint_pos a hz)
      (d c) (hd c) (hds c) (hδ c) hA hh.1 hh.2.1 hh.2.2.1
  have hKd : Pairwise (fun c c' => Disjoint (K c) (K c')) := by
    intro c c' hcc
    apply Set.disjoint_left.mpr
    intro A hA hA'
    have hh := hFroot A hA.1
    apply hcc
    apply Subtype.ext
    exact (matrixRayFibre_representative (hc c) (hcw c) hh.2.1 hA).symm.trans
      (matrixRayFibre_representative (hc c') (hcw c') hh.2.1 hA')
  have hyi (c : L) (i : ι) (hi : i ∈ I) : y i = (1/2:ℝ)*f c.val i := by
    rw [hcv c]
    exact blockVector_in I _ _ _ _ hi
  have hyo (i : ι) (hi : i ∉ I) : y i ≤ 0 := by
    have hh := blockVector_out I (1/2:ℝ) (facetPoint a z) (1/2:ℝ) v ⟨i,Finset.mem_compl.mpr hi⟩
    change y i = _ at hh
    rw [hh]
    exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (hv _).le
  have hcover (A : (traceSphere (Fin (k+1)))) (hA : ∃ t : ℝ, 0 < t ∧ F A = t • y) : ∃ c, A ∈ K c := by
    have hray := (mem_raySet_iff (hFz A) hy).mpr hA
    have hh := hFroot A hray
    exact ⟨⟨lineRepresentative w A.val,hh.2.2.2.2⟩,hray,positive_line_representative hh.2.1 hh.2.2.1⟩
  have hroot (c : L) (A : (traceSphere (Fin (k+1)))) (hA : ∃ t : ℝ, 0 < t ∧ G c A = t • y) : A ∈ K c := by
    obtain ⟨t,ht,hAt⟩ := hA
    have hm : localBlockModel f c.val (d c) a (D c) A.val = t • y.ofLp := WithLp.toLp_injective 2 hAt
    obtain ⟨hb,ha,heq,hP⟩ := hf.localBlockModel_ray (hc c) (d c) (hd c) (hds c) a (hcp c) (D c)
      A.property.1 (by norm_num : (0:ℝ) < 1/2) ht (hyi c) hyo hm
    have hFt : F A = t • y := by simpa only [F,G,heq] using hAt
    refine ⟨(mem_raySet_iff (hFz A) hy).mpr ⟨t,ht,hFt⟩,?_⟩
    have htr : Matrix.trace A.val⁺ = blockScalar c.val A.val := by
      rw [hP,Matrix.trace_smul,rankOne_trace,hc c,one_pow,smul_eq_mul,mul_one]
    rwa [htr]
  have hseg (c : L) (A : (traceSphere (Fin (k+1)))) (hA : A ∈ S c) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      (1-t) • F A + t • G c A ≠ 0 := by
    have hnU := lineRepresentative_norm hA.2.2.1
    have hIU : positiveSupport f (lineRepresentative w A.val) = I := hmax _ hnU
      (fun i hi => (mem_positiveSupport f _ i).mpr (hA.2.2.2.1 i hi))
    have hh := hf.localBlockMix_ne_zero A.property.1 (hc c) hnU (d c) (hd c) a (hcp c) hIU (D c)
      (hasPositiveLine_trace_pos hA.2.1) (positive_line_representative hA.2.1 hA.2.2.1) hA.2.2.2.2.2.2.1 ht
    intro hzA
    exact hh (WithLp.toLp_injective 2 hzA)
  have hhit (c : L) (A : (traceSphere (Fin (k+1)))) (hA : A ∈ S c) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1)
      (hAt : ∃ b : ℝ, 0 < b ∧ (1-t) • F A + t • G c A = b • y) : A ∈ K c := by
    obtain ⟨b,hb,heq⟩ := hAt
    have hnU := lineRepresentative_norm hA.2.2.1
    have hIU : positiveSupport f (lineRepresentative w A.val) = I := hmax _ hnU
      (fun i hi => (mem_positiveSupport f _ i).mpr (hA.2.2.2.1 i hi))
    have hmix : localBlockMix f c.val (d c) a (D c) t A.val = b • y.ofLp := WithLp.toLp_injective 2 heq
    obtain ⟨huc,hme⟩ := hf.localBlockMix_hit A.property.1 (hc c) hnU (d c) (hd c) (hds c) a (hcp c) hIU (D c)
      (hasPositiveLine_trace_pos hA.2.1) (positive_line_representative hA.2.1 hA.2.2.1)
      hA.2.2.2.2.1 hA.2.2.2.2.2.2.2
      (hreg c _ hnU hA.2.2.2.2.1 hA.2.2.2.2.2.1) (hyi c) ht hmix
    refine ⟨(mem_raySet_iff (hFz A) hy).mpr ⟨b,hb,?_⟩,?_⟩
    · exact congrArg (WithLp.toLp 2) (hme.symm.trans hmix)
    · rw [← huc]
      exact positive_line_representative hA.2.1 hA.2.2.1
  have hp := trace_patch_models hdim hn F hF hFz (by
      intro A B hB
      simp only [F,hB,signedExtension_odd,WithLp.toLp_neg])
    G hG hGz (by
      intro c A B hB
      simp only [G,hB,localBlockModel_odd,WithLp.toLp_neg])
    K S (fun c => matrixRayFibre_closed F hF y c.val) (fun c => hf.regularPatch_isOpen I w c.val (d c) (δ c))
    hKS hKd hy hcover hroot hseg hhit
  simpa only [Nat.card_eq_fintype_card] using hp
end MatrixParity
end
end

section
open Set MeasureTheory
namespace SimplicialChains
open Finset Set
lemma null_homotopy_local_models {A : Type*} [Fintype A] [DecidableEq A]
    (n : ℕ) (hn : 1 < n) [NeZero n] (b : Fin n → Bool)
    (H : ℝ × Euc (Fin n) → Euc (Fin n))
    (hH : ContinuousOn H (Icc (0:ℝ) 1 ×ˢ annulus n))
    (hHz : ∀ p ∈ Icc (0:ℝ) 1 ×ˢ annulus n, H p ≠ 0)
    (C : ℝ × Euc (Fin n) → Euc (Fin n))
    (hC : ContinuousOn C (Icc (0:ℝ) 1 ×ˢ annulus n))
    (hCz : ∀ p ∈ Icc (0:ℝ) 1 ×ˢ annulus n, C p ≠ 0)
    (hC1 : ∀ x, C (1,x) = H (0,x))
    (hCmiss : ∀ x ∈ annulus n, unitRadial (C (0,x)) ≠ facetCenter n b)
    (G : A → Euc (Fin n) → Euc (Fin n))
    (hG : ∀ a, ContinuousOn (G a) (annulus n))
    (hGz : ∀ a x, x ∈ annulus n → G a x ≠ 0)
    (hGo : ∀ a x, x ∈ annulus n → G a (-x) = -G a x)
    (U : A → Set (annulus n)) (hU : ∀ a, IsOpen (U a))
    (heq : ∀ a (x : annulus n), x ∈ U a → H (1,x.val) = G a x.val)
    (hcover : ∀ x : annulus n, unitRadial (H (1,x.val)) = facetCenter n b → ∃ a, x ∈ U a)
    (hroot : ∀ a (x : annulus n), unitRadial (G a x.val) = facetCenter n b → x ∈ U a)
    (hdis : Pairwise (fun a a' => Disjoint (U a) (U a'))) : (Fintype.card A : F₂) = 0 := by
  classical
  let f : Euc (Fin n) → Euc (Fin n) := fun x => unitRadial (H (1,x))
  let g : A → Euc (Fin n) → Euc (Fin n) := fun a x => unitRadial (G a x)
  have hfc : ContinuousOn f (annulus n) :=
    (unitRadial_continuousOn (S := {y | y ≠ 0}) (fun _ h => h)).comp
      (hH.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ hx => ⟨⟨zero_le_one,le_rfl⟩,hx⟩))
      (fun x hx => hHz (1,x) ⟨⟨zero_le_one,le_rfl⟩,hx⟩)
  have hfn (x) (hx : x ∈ annulus n) : ‖f x‖ = 1 := unitRadial_norm (hHz (1,x) ⟨⟨zero_le_one,le_rfl⟩,hx⟩)
  have hgc (a) : ContinuousOn (g a) (annulus n) :=
    (unitRadial_continuousOn (S := {y | y ≠ 0}) (fun _ h => h)).comp (hG a) (hGz a)
  have hgn (a x) (hx : x ∈ annulus n) : ‖g a x‖ = 1 := unitRadial_norm (hGz a x hx)
  obtain ⟨δa,hδa,hadd⟩ := additive_approximation_coeff n n (by omega) b f g hfc hgc U hU
    (fun a x hx => congrArg unitRadial (heq a x hx))
    (fun x hx => hcover x ((all_labelRegions_iff_center n b _ (hfn _ x.property)).mp hx))
    (fun a x hx => hroot a x ((all_labelRegions_iff_center n b _ (hgn a _ x.property)).mp hx)) hdis
  obtain ⟨δh,hδh,hhom⟩ := normalized_homotopy_chains n n (by omega) le_rfl H hH hHz
  have hc0 : ContinuousOn (fun x => unitRadial (C (0,x))) (annulus n) :=
    (unitRadial_continuousOn (S := {y | y ≠ 0}) (fun _ h => h)).comp
      (hC.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ hx => ⟨⟨le_rfl,zero_le_one⟩,hx⟩))
      (fun x hx => hCz (0,x) ⟨⟨le_rfl,zero_le_one⟩,hx⟩)
  obtain ⟨δc,hδc,hhomC⟩ := normalized_homotopy_chains n n (by omega) le_rfl C hC hCz
  obtain ⟨δm,hδm,hmiss⟩ := continuous_missed_facet_zero n n (by omega) hn b _ hc0
    (fun x hx => unitRadial_norm (hCz (0,x) ⟨⟨le_rfl,zero_le_one⟩,hx⟩)) hCmiss
  have hdeg0 : ∃ δ > 0, ∀ r, (((n:ℝ)-1)/n)^r * 2 < δ →
      approximation n n r (fun x => sphereLabel (unitRadial (H (0,x)))) (crossFundamental n)
        ⟨crossFacet n b,crossFacet_mem n (NeZero.pos n) b⟩ = 0 := by
    refine ⟨min δc δm,lt_min hδc hδm,fun r hr => ?_⟩
    have hh := hhomC r (hr.trans_le (min_le_left _ _))
    simp only [hC1] at hh
    rw [← hh]
    exact hmiss r (hr.trans_le (min_le_right _ _))
  obtain ⟨δ0,hδ0,hdeg0⟩ := hdeg0
  have hgodd : ∀ a, ∃ δ > 0, ∀ r, (((n:ℝ)-1)/n)^r * 2 < δ →
      approximation n n r (fun x => sphereLabel (g a x)) (crossFundamental n) = crossFundamental n := by
    intro a
    apply eventually_odd_sphere_degree n hn _ (hgc a) (hgn a)
    intro x hx
    change unitRadial (G a (-x)) = -unitRadial (G a x)
    rw [hGo a x hx,unitRadial_neg]
  choose dg hdg hdgprop using hgodd
  obtain ⟨δg,hδg,hδgb⟩ := finite_positive_bound dg hdg
  obtain ⟨r,hr⟩ := exists_small_cross_mesh n (by omega) (lt_min hδ0 (lt_min hδh (lt_min hδa hδg)))
  have hr0 := hr.trans_le (min_le_left _ _)
  have hrh := hr.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hra := hr.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hrg := hr.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have he0 : approximation n n r (fun x => sphereLabel (f x)) (crossFundamental n)
      ⟨crossFacet n b,crossFacet_mem n (NeZero.pos n) b⟩ = 0 := by
    dsimp only [f]
    rw [← hhom r hrh]
    exact hdeg0 r hr0
  have hadd' := hadd r hra
  rw [he0] at hadd'
  have hm (a : A) : approximation n n r (fun x => sphereLabel (g a x)) (crossFundamental n)
      ⟨crossFacet n b,crossFacet_mem n (NeZero.pos n) b⟩ = 1 := by
    rw [hdgprop a r (hrg.trans (hδgb a)),crossFundamental_coeff n hn b]
  simpa only [hm,Finset.sum_const,Finset.card_univ,nsmul_one] using hadd'.symm
end SimplicialChains
end

section
open Set MeasureTheory
section
open Set SimplicialChains
noncomputable def normSphere (n : ℕ) : Set (Euc (Fin n)) := {u | ‖u‖ = 1}
section SphereNullModels
variable {n : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
lemma sphere_null_local_models (hn : 1 < n)
    (H C : ℝ × (normSphere n) → (Euc (Fin n)))
    (hH : ContinuousOn H (Icc (0:ℝ) 1 ×ˢ univ))
    (hHz : ∀ t ∈ Icc (0:ℝ) 1, ∀ u : (normSphere n), H (t,u) ≠ 0)
    (hC : ContinuousOn C (Icc (0:ℝ) 1 ×ˢ univ))
    (hCz : ∀ t ∈ Icc (0:ℝ) 1, ∀ u : (normSphere n), C (t,u) ≠ 0)
    (hC1 : ∀ u, C (1,u) = H (0,u))
    (G : κ → (normSphere n) → (Euc (Fin n))) (hG : ∀ a, Continuous (G a)) (hGz : ∀ a u, G a u ≠ 0)
    (hGo : ∀ a (u v : (normSphere n)), v.val = -u.val → G a v = -G a u)
    (U : κ → Set (normSphere n)) (hU : ∀ a, IsOpen (U a))
    (heq : ∀ a u, u ∈ U a → H (1,u) = G a u)
    {y : (Euc (Fin n))} (hy : y ≠ 0)
    (hmiss : ∀ u : (normSphere n), ¬ ∃ d : ℝ, 0 < d ∧ C (0,u) = d • y)
    (hcover : ∀ u : (normSphere n), (∃ d : ℝ, 0 < d ∧ H (1,u) = d • y) → ∃ a, u ∈ U a)
    (hroot : ∀ a u, (∃ d : ℝ, 0 < d ∧ G a u = d • y) → u ∈ U a)
    (hdis : Pairwise (fun a b => Disjoint (U a) (U b))) : (Fintype.card κ : F₂) = 0 := by
  classical
  let : NeZero n := ⟨by omega⟩
  let b : Fin n → Bool := fun _ => false
  let L := Submodule.reflection (ℝ ∙ (unitRadial y - facetCenter n b))ᗮ
  have hRy : L (unitRadial y) = facetCenter n b :=
    Submodule.reflection_sub ((unitRadial_norm hy).trans (facetCenter_norm n b).symm)
  have hray (v : (Euc (Fin n))) (hv : v ≠ 0) (he : unitRadial (L v) = facetCenter n b) :
      ∃ d : ℝ, 0 < d ∧ v = d • y := by
    have hu : unitRadial v = unitRadial y := by
      apply L.injective
      rw [hRy]
      simpa only [unitRadial,map_smul,L.norm_map] using he
    refine ⟨‖v‖ / ‖y‖,div_pos (norm_pos_iff.mpr hv) (norm_pos_iff.mpr hy),?_⟩
    have hh := congrArg (fun z : (Euc (Fin n)) => ‖v‖ • z) hu
    simpa only [unitRadial,smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv),one_smul,div_eq_mul_inv] using hh
  let N : annulus n → (normSphere n) := fun x => ⟨unitRadial x.val,unitRadial_norm (annulus_ne_zero n (by omega) x.property)⟩
  have hN : Continuous N := by
    apply Continuous.subtype_mk
    exact (unitRadial_continuousOn (fun _ hx => annulus_ne_zero n (by omega) hx)).domRestrict
  have hNneg (x) (hx : x ∈ annulus n) (hxn : -x ∈ annulus n) : (N ⟨-x,hxn⟩).val = -(N ⟨x,hx⟩).val := unitRadial_neg x
  let extH (P : ℝ × (normSphere n) → (Euc (Fin n))) : ℝ × (Euc (Fin n)) → (Euc (Fin n)) := fun p => if hx : p.2 ∈ annulus n then L (P (p.1,N ⟨p.2,hx⟩)) else 0
  have hext (P : ℝ × (normSphere n) → (Euc (Fin n))) (hP : ContinuousOn P (Icc (0:ℝ) 1 ×ˢ univ)) :
      ContinuousOn (extH P) (Icc (0:ℝ) 1 ×ˢ annulus n) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    let Q := Icc (0:ℝ) 1 ×ˢ annulus n
    have hcN : Continuous (fun p : Q => N ⟨p.val.2,p.property.2⟩) := hN.comp (continuous_subtype_val.snd.subtype_mk _)
    have hg := hP.comp_continuous (continuous_subtype_val.fst.prodMk hcN) (fun p : Q => ⟨p.property.1,mem_univ _⟩)
    apply (L.continuous.comp hg).congr
    intro p
    simp only [Set.domRestrict_apply,Function.comp_apply,extH,dif_pos p.property.2]
  have hextz (P : ℝ × (normSphere n) → (Euc (Fin n))) (hPz : ∀ t ∈ Icc (0:ℝ) 1, ∀ u, P (t,u) ≠ 0) :
      ∀ p ∈ Icc (0:ℝ) 1 ×ˢ annulus n, extH P p ≠ 0 := by
    intro p hp hz
    exact hPz _ hp.1 _ (L.injective (by simpa only [extH,dif_pos hp.2,map_zero] using hz))
  let G' : κ → (Euc (Fin n)) → (Euc (Fin n)) := fun a x => if hx : x ∈ annulus n then L (G a (N ⟨x,hx⟩)) else 0
  have hG' (a) : ContinuousOn (G' a) (annulus n) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    apply (L.continuous.comp ((hG a).comp hN)).congr
    intro x
    simp only [Set.domRestrict_apply,Function.comp_apply,G',dif_pos x.property]
  have hGz' (a x) (hx : x ∈ annulus n) : G' a x ≠ 0 := by
    intro hz
    exact hGz a _ (L.injective (by simpa only [G',dif_pos hx,map_zero] using hz))
  have hGo' (a x) (hx : x ∈ annulus n) : G' a (-x) = -G' a x := by
    have hxn : -x ∈ annulus n := by simpa only [annulus,Set.mem_ofPred_eq,norm_neg] using hx
    simp only [G',dif_pos hx,dif_pos hxn,hGo a _ _ (hNneg x hx hxn),map_neg]
  refine null_homotopy_local_models n hn b (extH H) (hext H hH) (hextz H hHz) (extH C) (hext C hC) (hextz C hCz)
    (fun x => by simp only [extH,hC1]) ?_ G' hG' hGz' hGo'
    (fun a => N ⁻¹' U a) (fun a => (hU a).preimage hN) ?_ ?_ ?_ ?_
  · intro x hx he
    apply hmiss (N ⟨x,hx⟩)
    apply hray _ (hCz _ ⟨le_rfl,zero_le_one⟩ _)
    simpa only [extH,dif_pos hx] using he
  · intro a x hx
    simp only [extH,G',dif_pos x.property,heq a _ hx]
  · intro x hx
    apply hcover (N x)
    apply hray _ (hHz _ ⟨zero_le_one,le_rfl⟩ _)
    simpa only [extH,dif_pos x.property] using hx
  · intro a x hx
    apply hroot a (N x)
    apply hray _ (hGz a _)
    simpa only [G',dif_pos x.property] using hx
  · intro a a' haa
    exact (hdis haa).preimage N
end SphereNullModels
end
end

section
open Set MeasureTheory
section
open Set SimplicialChains
section SphereNullPatch
variable {n : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
lemma sphere_null_patch_models (hn : 1 < n)
    (F : normSphere n → (Euc (Fin n))) (hF : Continuous F) (hFz : ∀ A, F A ≠ 0)
    (C : ℝ × normSphere n → (Euc (Fin n))) (hC : ContinuousOn C (Icc (0:ℝ) 1 ×ˢ univ))
    (hCz : ∀ t ∈ Icc (0:ℝ) 1, ∀ u, C (t,u) ≠ 0)
    (hC1 : ∀ u, C (1,u) = F u)
    (G : κ → normSphere n → (Euc (Fin n))) (hG : ∀ a, Continuous (G a))
    (hGz : ∀ a A, G a A ≠ 0)
    (hGo : ∀ a (A B : normSphere n), B.val = -A.val → G a B = -G a A)
    (K S : κ → Set (normSphere n)) (hK : ∀ a, IsClosed (K a)) (hS : ∀ a, IsOpen (S a))
    (hKS : ∀ a, K a ⊆ S a) (hKd : Pairwise (fun a b => Disjoint (K a) (K b)))
    {y : (Euc (Fin n))} (hy : y ≠ 0)
    (hmiss : ∀ u, ¬ ∃ d : ℝ, 0 < d ∧ C (0,u) = d • y)
    (hcover : ∀ A, (∃ d : ℝ, 0 < d ∧ F A = d • y) → ∃ a, A ∈ K a)
    (hroot : ∀ a A, (∃ d : ℝ, 0 < d ∧ G a A = d • y) → A ∈ K a)
    (hseg : ∀ a A, A ∈ S a → ∀ t ∈ Icc (0:ℝ) 1, (1-t) • F A + t • G a A ≠ 0)
    (hhit : ∀ a A, A ∈ S a → ∀ t ∈ Icc (0:ℝ) 1,
      (∃ d : ℝ, 0 < d ∧ (1-t) • F A + t • G a A = d • y) → A ∈ K a) :
    (Fintype.card κ : F₂) = 0 := by
  classical
  obtain ⟨U,q,hU,hKU,hqb,hq1,hqS,hqd⟩ := finite_closed_cutoffs K S hK hS hKS hKd
  let H : ℝ × normSphere n → (Euc (Fin n)) := fun p => finitePatch F G (fun a => q a) p.1 p.2
  have hH : Continuous H := finitePatch_continuous hF hG (fun a => (q a).continuous)
  have hHz (t) (ht : t ∈ Icc (0:ℝ) 1) (A) : H (t,A) ≠ 0 :=
    finitePatch_ne_zero F G (fun a => q a) t A hqd ht (fun a => hqb a A) (hFz A)
      (fun a ha => hseg a A (hqS a A ha))
  refine sphere_null_local_models hn H C hH.continuousOn hHz hC hCz
    (fun u => by simpa only [H,finitePatch_zero] using hC1 u)
    G hG hGz hGo U hU ?_ hy hmiss ?_ ?_ ?_
  · intro a A hA
    apply finitePatch_one_of_disjoint F G (fun a => q a) A a (hq1 a A hA)
    intro b hba
    by_contra hb
    exact Set.disjoint_left.mp (hqd hba) hb (by
      change q a A ≠ 0
      rw [hq1 a A hA]; exact one_ne_zero)
  · intro A hA
    rcases finitePatch_cases F G (fun a => q a) 1 A hqd with he | ⟨a,ha,he⟩
    · have hr : ∃ d : ℝ, 0 < d ∧ F A = d • y := by
        simpa only [H,he] using hA
      obtain ⟨a,ha⟩ := hcover A hr
      exact ⟨a,hKU a ha⟩
    · refine ⟨a,hKU a (hhit a A (hqS a A ha) (q a A) (hqb a A) ?_)⟩
      simpa only [H,he,one_mul] using hA
  · intro a A hA
    exact hKU a (hroot a A hA)
  · intro a b hab
    exact (hqd hab).mono
      (fun A hA => by change q a A ≠ 0; rw [hq1 a A hA]; exact one_ne_zero)
      (fun A hA => by change q b A ≠ 0; rw [hq1 b A hA]; exact one_ne_zero)
end SphereNullPatch
end
end

section
open Set MeasureTheory
section
open scoped RealInnerProductSpace
section SphereBlock
variable {k : ℕ}
noncomputable def sphereBlock (s : ℝ) (v : (Euc (Fin k))) : (Euc (Fin (k+1))) := WithLp.toLp 2 (Fin.cases s (fun i => v i))
lemma sphereBlock_zero (s : ℝ) (v : (Euc (Fin k))) : sphereBlock s v 0 = s := rfl
lemma sphereBlock_succ (s : ℝ) (v : (Euc (Fin k))) (i : Fin k) : sphereBlock s v i.succ = v i := rfl
lemma sphereBlock_continuous {X : Type*} [TopologicalSpace X] {s : X → ℝ} {v : X → (Euc (Fin k))}
    (hs : Continuous s) (hv : Continuous v) : Continuous (fun x => sphereBlock (s x) (v x)) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hs
  · exact (PiLp.continuous_apply 2 _ j).comp hv
lemma sphereBlock_neg (s : ℝ) (v : (Euc (Fin k))) : sphereBlock (-s) (-v) = -sphereBlock s v := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl
lemma sphereBlock_eq_zero {s : ℝ} {v : (Euc (Fin k))} (h : sphereBlock s v = 0) : s = 0 ∧ v = 0 := by
  refine ⟨congrArg (fun u : (Euc (Fin (k+1))) => u 0) h,?_⟩
  ext i
  exact congrArg (fun u : (Euc (Fin (k+1))) => u i.succ) h
noncomputable def sphereBlockModel (c : (Euc (Fin (k+1)))) (e : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc (Fin (k+1)))) (D : (Euc (Fin k)) ≃L[ℝ] (Euc (Fin k))) (u : (Euc (Fin (k+1)))) : (Euc (Fin (k+1))) :=
  sphereBlock ⟪c,u⟫ (D (e.toContinuousLinearMap.adjoint u))
lemma sphereBlockModel_continuous (c : (Euc (Fin (k+1)))) (e : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc (Fin (k+1)))) (D : (Euc (Fin k)) ≃L[ℝ] (Euc (Fin k))) : Continuous (sphereBlockModel c e D) :=
  sphereBlock_continuous (continuous_const.inner continuous_id) (D.continuous.comp (e.toContinuousLinearMap.adjoint.continuous))
lemma sphereBlockModel_odd (c : (Euc (Fin (k+1)))) (e : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc (Fin (k+1)))) (D : (Euc (Fin k)) ≃L[ℝ] (Euc (Fin k))) (u : (Euc (Fin (k+1)))) :
    sphereBlockModel c e D (-u) = -sphereBlockModel c e D u := by
  simp only [sphereBlockModel,inner_neg_right,map_neg,sphereBlock_neg]
lemma hemisphereInverse_eq_zero_iff {c u : (Euc (Fin (k+1)))} (hc : ‖c‖ = 1) (hu : ‖u‖ = 1)
    (e : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc (Fin (k+1)))) (he : ∀ v, ⟪c,e v⟫ = 0) (hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u)
    (hcu : 0 < ⟪c,u⟫) : hemisphereInverse c e u = 0 ↔ u = c := by
  constructor
  · intro hv
    have hh := hemisphereChart_inverse c e hc he hes hu hcu
    rw [hv,hemisphereChart_zero hc] at hh
    exact hh.symm
  · intro hh
    subst u
    rw [hemisphereInverse,adjoint_normal c e he,smul_zero]
lemma sphereBlockModel_ne_zero {c u : (Euc (Fin (k+1)))} (hc : ‖c‖ = 1)
    (e : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc (Fin (k+1)))) (he : ∀ v, ⟪c,e v⟫ = 0) (hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u)
    (D : (Euc (Fin k)) ≃L[ℝ] (Euc (Fin k))) (hu : u ≠ 0) : sphereBlockModel c e D u ≠ 0 := by
  intro hz
  obtain ⟨h1,h2⟩ := sphereBlock_eq_zero hz
  have he0 : e.toContinuousLinearMap.adjoint u = 0 := D.injective (h2.trans D.map_zero.symm)
  have hd := frame_decomposition c e hc he hes u
  rw [h1,he0,zero_smul,map_zero,sub_zero] at hd
  exact hu hd.symm
lemma sphereBlockModel_ray {c u : (Euc (Fin (k+1)))} (hc : ‖c‖ = 1) (hu : ‖u‖ = 1)
    (e : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc (Fin (k+1)))) (he : ∀ v, ⟪c,e v⟫ = 0) (hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u)
    (D : (Euc (Fin k)) ≃L[ℝ] (Euc (Fin k))) {b : ℝ} (hb : 0 < b)
    (h : sphereBlockModel c e D u = b • sphereBlock 1 (0 : (Euc (Fin k)))) : u = c := by
  have hs : ⟪c,u⟫ = b := by
    have hh := congrArg (fun v : (Euc (Fin (k+1))) => v 0) h
    simpa only [sphereBlockModel,sphereBlock_zero,PiLp.smul_apply,mul_one,smul_eq_mul] using hh
  have ht : D (e.toContinuousLinearMap.adjoint u) = 0 := by
    ext i
    have hh := congrArg (fun v : (Euc (Fin (k+1))) => v i.succ) h
    simpa only [sphereBlockModel,sphereBlock_succ,PiLp.smul_apply,PiLp.zero_apply,smul_eq_mul,mul_zero] using hh
  apply (hemisphereInverse_eq_zero_iff hc hu e he hes (hs ▸ hb)).mp
  rw [hemisphereInverse,D.injective (ht.trans D.map_zero.symm),smul_zero]
lemma sphereBlock_mix_nonzero {c w u : (Euc (Fin (k+1)))} (e : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc (Fin (k+1)))) (D : (Euc (Fin k)) ≃L[ℝ] (Euc (Fin k)))
    (g : (Euc (Fin k))) (hw : 0 < ⟪w,u⟫) (hc : 0 < ⟪c,u⟫) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    (1-t) • sphereBlock ⟪w,u⟫ g + t • sphereBlockModel c e D u ≠ 0 := by
  intro hz
  have hh := congrArg (fun v : (Euc (Fin (k+1))) => v 0) hz
  simp only [PiLp.add_apply,PiLp.smul_apply,sphereBlockModel,sphereBlock_zero,smul_eq_mul,PiLp.zero_apply] at hh
  rcases lt_or_eq_of_le ht.2 with hl | rfl
  · have hp : 0 < (1-t)*⟪w,u⟫ := mul_pos (sub_pos.mpr hl) hw
    have hn : 0 ≤ t*⟪c,u⟫ := mul_nonneg ht.1 hc.le
    linarith
  · linarith
lemma sphereBlock_mix_ray {c w u : (Euc (Fin (k+1)))} (hc : ‖c‖ = 1) (hu : ‖u‖ = 1)
    (e : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc (Fin (k+1)))) (he : ∀ v, ⟪c,e v⟫ = 0) (hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u)
    (D : (Euc (Fin k)) ≃L[ℝ] (Euc (Fin k))) (g : (Euc (Fin k))) (hcu : 0 < ⟪c,u⟫)
    (hr : hemisphereInverse c e u ≠ 0 → 0 < ⟪hemisphereInverse c e u,D.symm g⟫)
    {t b : ℝ} (ht : t ∈ Set.Icc 0 1)
    (hm : (1-t) • sphereBlock ⟪w,u⟫ g + t • sphereBlockModel c e D u = b • sphereBlock 1 (0 : (Euc (Fin k)))) :
    u = c := by
  have hz : (1-t) • g + t • D (e.toContinuousLinearMap.adjoint u) = 0 := by
    ext i
    have hh := congrArg (fun v : (Euc (Fin (k+1))) => v i.succ) hm
    simpa only [PiLp.add_apply,PiLp.smul_apply,sphereBlockModel,sphereBlock_succ,PiLp.zero_apply,smul_eq_mul,mul_zero] using hh
  have hb : hemisphereInverse c e u ≠ 0 → 0 < ⟪hemisphereInverse c e u,e.toContinuousLinearMap.adjoint u⟫ := by
    intro hv
    have hvv : e.toContinuousLinearMap.adjoint u = ⟪c,u⟫ • hemisphereInverse c e u := by
      rw [hemisphereInverse,smul_smul,mul_inv_cancel₀ (ne_of_gt hcu),one_smul]
    rw [hvv,inner_smul_right,real_inner_self_eq_norm_sq]
    exact mul_pos hcu (sq_pos_of_pos (norm_pos_iff.mpr hv))
  have hv := regular_mixed_zero D (g := fun _ : (Euc (Fin k)) => g) (v := hemisphereInverse c e u)
    (b := e.toContinuousLinearMap.adjoint u) hr hb (show (0:ℝ)<1 from zero_lt_one) ht (by simpa only [one_smul] using hz)
  exact (hemisphereInverse_eq_zero_iff hc hu e he hes hcu).mp hv
end SphereBlock
end
end

section
open Set MeasureTheory
section
open Set SimplicialChains
open scoped RealInnerProductSpace
section SphereParity
variable {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [Fintype ι] in
lemma facetTail_point {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (z : (Euc (Fin k))) :
    facetTail a (facetPoint a z) = z := by
  ext j
  exact (facetPoint_apply a z j.succ).trans (simplexPoint_succ z j)
lemma Admissible.eq_facetPoint_of_tail {f : (Euc (Fin (k+1))) → ι → ℝ} (hf : Admissible f)
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) {u : (Euc (Fin (k+1)))} (hu : ‖u‖ = 1)
    (hs : positiveSupport f u ⊆ I) {z : (Euc (Fin k))} (hz : facetTail a (f u) = z) :
    f u = facetPoint a z := by
  have he (i : ι) (hi : i ≠ (a 0).val) : f u i = facetPoint a z i := by
    by_cases hI : i ∈ I
    · obtain ⟨j,hj⟩ := a.surjective ⟨i,hI⟩
      have hji : (a j).val = i := congrArg Subtype.val hj
      have hj0 : j ≠ 0 := fun h => hi (by simpa only [h] using hji.symm)
      obtain ⟨l,rfl⟩ := Fin.eq_succ_of_ne_zero hj0
      rw [← hji,facetPoint_apply,simplexPoint_succ]
      exact congrArg (fun v : (Euc (Fin k)) => v l) hz
    · rw [facetPoint_zero a z hI]
      apply le_antisymm _ (hf.nonneg u hu i)
      exact le_of_not_gt (fun h => hI (hs ((mem_positiveSupport f u i).mpr h)))
  have hall : ∑ i, (f u i-facetPoint a z i) = f u (a 0).val-facetPoint a z (a 0).val := by
    apply Finset.sum_eq_single (a 0).val
    · intro i _ hi
      exact sub_eq_zero.mpr (he i hi)
    · simp
  rw [Finset.sum_sub_distrib,hf.sum_one u hu,facetPoint_sum,sub_self] at hall
  funext i
  by_cases hi : i = (a 0).val
  · subst i
    exact sub_eq_zero.mp hall.symm
  · exact he i hi
noncomputable def sphereRegularPatch (w c : (Euc (Fin (k+1)))) (d : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc (Fin (k+1)))) (δ : ℝ) : Set (normSphere (k+1)) :=
  {u | 0 < ⟪w,u.val⟫ ∧ 0 < ⟪c,u.val⟫ ∧ ‖hemisphereInverse c d u.val‖ < δ}
lemma sphereRegularPatch_isOpen (w c : (Euc (Fin (k+1)))) (d : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc (Fin (k+1)))) (δ : ℝ) :
    IsOpen (sphereRegularPatch w c d δ) := by
  have hc : IsOpen {u : (Euc (Fin (k+1))) | 0 < ⟪c,u⟫} := isOpen_lt continuous_const (continuous_const.inner continuous_id)
  have hp := (hemisphereInverse_continuousOn c d).norm.isOpen_inter_preimage hc (isOpen_Iio : IsOpen (Iio δ))
  exact ((isOpen_lt (f := fun u : (Euc (Fin (k+1))) => (0 : ℝ)) (g := fun u : (Euc (Fin (k+1))) => ⟪w,u⟫) continuous_const (continuous_const.inner continuous_id)).inter hp).preimage continuous_subtype_val
lemma Admissible.regular_facet_level_even {f : (Euc (Fin (k+1))) → ι → ℝ} (hf : Admissible f)
    (hk : 0 < k) {I : Finset ι} (a : Fin (k+1) ≃ ↥I)
    (hfree : ∀ u : (Euc (Fin (k+1))), ‖u‖ = 1 → (∀ j : Fin k, 0 < f u (a j.succ).val) → positiveSupport f u ⊆ I)
    {w : (Euc (Fin (k+1)))} (hw : ‖w‖ = 1) (hwi : ∀ i ∈ I, 0 < f w i)
    (e : (Euc (Fin k)) →ₗᵢ[ℝ] (Euc (Fin (k+1)))) (he : ∀ v, ⟪w,e v⟫ = 0)
    (hes : ∀ u, ⟪w,u⟫ = 0 → ∃ v, e v = u) {z : (Euc (Fin k))} (hz : z ∈ simplexInterior k)
    (hr : ∀ v, baseCoordinates f w e a v = z → (fderiv ℝ (baseCoordinates f w e a) v).det ≠ 0)
    (hfin : (orientedLevel f w (facetPoint a z)).Finite) :
    (Nat.card (orientedLevel f w (facetPoint a z)) : F₂) = 0 := by
  classical
  let L := orientedLevel f w (facetPoint a z)
  let : Fintype L := hfin.fintype
  have hI : I.Nonempty := ⟨(a 0).val,(a 0).property⟩
  have hc (c : L) : ‖c.val‖ = 1 := c.property.1
  have hcv (c : L) : f c.val = facetPoint a z := c.property.2.1
  have hcw (c : L) : 0 < ⟪w,c.val⟫ := hf.orientedLevel_inner_pos hI hw hwi (facetPoint_pos a hz) c.property
  have hdata (c : L) := hf.regular_model_data a hw (hc c) e he hes (hcw c) (hcv c) hr
  choose d D δ hd hds hδ hreg using hdata
  let g : (Euc (Fin (k+1))) → (Euc (Fin k)) := fun u => facetTail a (f u)
  have hg : Continuous g := (facetTail a).continuous_of_finiteDimensional.comp (continuous_pi (fun i => (hf.smooth i).continuous))
  let C : ℝ × normSphere (k+1) → (Euc (Fin (k+1))) := fun p => sphereBlock ⟪w,p.2.val⟫ (p.1 • g p.2.val-z)
  have hC : Continuous C := sphereBlock_continuous (continuous_const.inner continuous_snd.subtype_val)
    ((continuous_fst.smul (hg.comp continuous_snd.subtype_val)).sub continuous_const)
  have hCz (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (u : normSphere (k+1)) : C (t,u) ≠ 0 := by
    intro hzero
    obtain ⟨hwu,hv⟩ := sphereBlock_eq_zero hzero
    have htail : g u.val = 0 := by
      ext j
      apply le_antisymm _ (hf.nonneg _ u.property _)
      exact le_of_not_gt (fun hp => hf.orthogonal w u.val hw u.property hwu (a j.succ).val ⟨hwi _ (a j.succ).property,hp⟩)
    change t • g u.val-z = 0 at hv
    rw [htail,smul_zero,zero_sub,neg_eq_zero] at hv
    have hpos := hz.1 (⟨0,hk⟩ : Fin k)
    rw [hv] at hpos
    exact lt_irrefl 0 hpos
  let F : normSphere (k+1) → (Euc (Fin (k+1))) := fun u => sphereBlock ⟪w,u.val⟫ (g u.val-z)
  have hF : Continuous F := sphereBlock_continuous (continuous_const.inner continuous_subtype_val)
    ((hg.comp continuous_subtype_val).sub continuous_const)
  have hFz (u) : F u ≠ 0 := by simpa only [C,F,one_smul] using hCz 1 ⟨zero_le_one,le_rfl⟩ u
  let G : L → normSphere (k+1) → (Euc (Fin (k+1))) := fun c u => sphereBlockModel c.val (d c) (D c) u.val
  let K : L → Set (normSphere (k+1)) := fun c => {u | u.val = c.val}
  let S : L → Set (normSphere (k+1)) := fun c => sphereRegularPatch w c.val (d c) (δ c)
  let y : (Euc (Fin (k+1))) := sphereBlock 1 (0 : (Euc (Fin k)))
  have hy : y ≠ 0 := fun h => one_ne_zero (sphereBlock_eq_zero h).1
  have hKS (c : L) : K c ⊆ S c := by
    intro u hu
    change u.val = c.val at hu
    change 0 < ⟪w,u.val⟫ ∧ 0 < ⟪c.val,u.val⟫ ∧ ‖hemisphereInverse c.val (d c) u.val‖ < δ c
    rw [hu,real_inner_self_eq_norm_sq,hc c,one_pow]
    refine ⟨hcw c,zero_lt_one,?_⟩
    rw [hemisphereInverse,adjoint_normal c.val (d c) (hd c),smul_zero,norm_zero]
    exact hδ c
  have hKd : Pairwise (fun c c' => Disjoint (K c) (K c')) := by
    intro c c' hcc
    apply Set.disjoint_left.mpr
    intro u hu hu'
    exact hcc (Subtype.ext (hu.symm.trans hu'))
  have hmiss (u : normSphere (k+1)) : ¬ ∃ b : ℝ, 0 < b ∧ C (0,u) = b • y := by
    rintro ⟨b,hb,hbEq⟩
    have hv := congrArg (fun v : (Euc (Fin (k+1))) => v (Fin.succ ⟨0,hk⟩)) hbEq
    have hpos := hz.1 (⟨0,hk⟩ : Fin k)
    simp only [C,y,zero_smul,zero_sub,sphereBlock_succ,PiLp.neg_apply,PiLp.smul_apply,PiLp.zero_apply,smul_eq_mul,mul_zero] at hv
    linarith
  have hcover (u : normSphere (k+1)) (hu : ∃ b : ℝ, 0 < b ∧ F u = b • y) : ∃ c, u ∈ K c := by
    obtain ⟨b,hb,hbu⟩ := hu
    have hwu : 0 < ⟪w,u.val⟫ := by
      have hh := congrArg (fun v : (Euc (Fin (k+1))) => v 0) hbu
      have hh' : ⟪w,u.val⟫ = b := by simpa only [F,y,sphereBlock_zero,PiLp.smul_apply,smul_eq_mul,mul_one] using hh
      exact hh' ▸ hb
    have hgz : g u.val = z := by
      ext j
      have hh := congrArg (fun v : (Euc (Fin (k+1))) => v j.succ) hbu
      have hh' : g u.val j-z j = 0 := by simpa only [F,y,sphereBlock_succ,PiLp.sub_apply,PiLp.smul_apply,PiLp.zero_apply,smul_eq_mul,mul_zero] using hh
      exact sub_eq_zero.mp hh'
    have hup : ∀ j : Fin k, 0 < f u.val (a j.succ).val := by
      intro j
      have hh := congrArg (fun v : (Euc (Fin k)) => v j) hgz
      change f u.val (a j.succ).val = z j at hh
      rw [hh]
      exact hz.1 j
    have huf := hf.eq_facetPoint_of_tail a u.property (hfree u.val u.property hup) hgz
    exact ⟨⟨u.val,u.property,huf,hwu.le⟩,rfl⟩
  have hcount := sphere_null_patch_models (by omega : 1 < k+1) F hF hFz C hC.continuousOn hCz
    (fun u => by simp only [C,F,one_smul]) G
    (fun c => (sphereBlockModel_continuous c.val (d c) (D c)).comp continuous_subtype_val)
    (fun c u => sphereBlockModel_ne_zero (hc c) (d c) (hd c) (hds c) (D c) (norm_ne_zero_iff.mp (by rw [u.property]; exact one_ne_zero)))
    (by intro c u v hv; simp only [G,hv,sphereBlockModel_odd]) K S
    (fun c => isClosed_eq continuous_subtype_val continuous_const)
    (fun c => sphereRegularPatch_isOpen w c.val (d c) (δ c)) hKS hKd hy hmiss hcover
    (by
      intro c u hu
      obtain ⟨b,hb,hbu⟩ := hu
      exact sphereBlockModel_ray (hc c) u.property (d c) (hd c) (hds c) (D c) hb hbu)
    (by
      intro c u hu t ht
      exact sphereBlock_mix_nonzero (d c) (D c) (g u.val-z) hu.1 hu.2.1 ht)
    (by
      intro c u hu t ht htu
      obtain ⟨b,hb,hbu⟩ := htu
      apply sphereBlock_mix_ray (hc c) u.property (d c) (hd c) (hds c) (D c) (g u.val-z) hu.2.1 _ ht hbu
      have hge : g u.val-z = facetTail a (f u.val-f c.val) := by
        rw [map_sub,hcv c,facetTail_point]
      rw [hge]
      exact hreg c u.val u.property hu.2.1 hu.2.2)
  simpa only [Nat.card_eq_fintype_card] using hcount
end SphereParity
end
end

section
open Set MeasureTheory
section
open Set SimplicialChains
open scoped RealInnerProductSpace
section NoFreeRidge
variable {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma Admissible.no_free_indexed_facet {f : (Euc (Fin (k+1))) → ι → ℝ} (hf : Admissible f)
    (hk : 0 < k) (hdim : Fintype.card (UpperTriangle (Fin (k+1))) = Fintype.card ι)
    (hn : 1 < Fintype.card ι) {I : Finset ι} [Nonempty ↥(Iᶜ : Finset ι)]
    (a : Fin (k+1) ≃ ↥I)
    (hmax : ∀ u : (Euc (Fin (k+1))), ‖u‖ = 1 → I ⊆ positiveSupport f u → positiveSupport f u = I)
    {w : (Euc (Fin (k+1)))} (hw : ‖w‖ = 1) (hwi : ∀ i ∈ I, 0 < f w i) :
    ∃ u : (Euc (Fin (k+1))), ‖u‖ = 1 ∧ (∀ j : Fin k, 0 < f u (a j.succ).val) ∧ ¬ positiveSupport f u ⊆ I := by
  classical
  by_contra hnfree
  push Not at hnfree
  obtain ⟨e,z,he,hes,hz,hr,hfin⟩ := hf.exists_regular_facet_point a hw hwi
  have ho := hf.regular_facet_level_odd hdim hn a hmax hw hwi e he hes hz hr hfin
  have heven := hf.regular_facet_level_even hk a hnfree hw hwi e he hes hz hr hfin
  rw [heven] at ho
  exact zero_ne_one ho
lemma Admissible.no_free_ridge {f : (Euc (Fin (k+1))) → ι → ℝ} (hf : Admissible f)
    (hk : 0 < k) (hdim : Fintype.card (UpperTriangle (Fin (k+1))) = Fintype.card ι)
    (hn : 1 < Fintype.card ι) {I U : Finset ι} [Nonempty ↥(Iᶜ : Finset ι)]
    (hI : I.card = k+1) (hUI : U ⊆ I) (hU : U.card = k)
    (hmax : ∀ u : (Euc (Fin (k+1))), ‖u‖ = 1 → I ⊆ positiveSupport f u → positiveSupport f u = I)
    {w : (Euc (Fin (k+1)))} (hw : ‖w‖ = 1) (hwi : ∀ i ∈ I, 0 < f w i) :
    ∃ u : (Euc (Fin (k+1))), ‖u‖ = 1 ∧ U ⊆ positiveSupport f u ∧ ¬ positiveSupport f u ⊆ I := by
  classical
  have hdiff : (I \ U).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_sdiff_of_subset hUI,hI,hU]
    omega
  obtain ⟨i,hi⟩ := hdiff
  have hiI := (Finset.mem_sdiff.mp hi).1
  have hiU := (Finset.mem_sdiff.mp hi).2
  let b : Fin (k+1) ≃ ↥I := (Fintype.equivFinOfCardEq (by simpa using hI)).symm
  let a : Fin (k+1) ≃ ↥I := (Equiv.swap 0 (b.symm ⟨i,hiI⟩)).trans b
  have ha : (a 0).val = i := by simp [a]
  obtain ⟨u,hu,hup,hnot⟩ := hf.no_free_indexed_facet hk hdim hn a hmax hw hwi
  refine ⟨u,hu,?_,hnot⟩
  intro j hj
  obtain ⟨l,hl⟩ := a.surjective ⟨j,hUI hj⟩
  have hlj : (a l).val = j := congrArg Subtype.val hl
  have hl0 : l ≠ 0 := by
    intro hl0
    rw [hl0,ha] at hlj
    exact hiU (hlj ▸ hj)
  obtain ⟨q,rfl⟩ := Fin.eq_succ_of_ne_zero hl0
  rw [← hlj]
  exact (mem_positiveSupport f u _).mpr (hup q)
end NoFreeRidge
end
end

section
open Set MeasureTheory
section
open scoped RealInnerProductSpace
section SupportIncidence
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
def SupportFace (f : V → ι → ℝ) (S : Finset ι) : Prop :=
  ∃ u : V, ‖u‖ = 1 ∧ S ⊆ positiveSupport f u
omit [InnerProductSpace ℝ V] [DecidableEq ι] in
lemma SupportFace.mono {f : V → ι → ℝ} {S U : Finset ι} (h : SupportFace f S) (hUS : U ⊆ S) : SupportFace f U := by
  obtain ⟨u,hu,hSu⟩ := h
  exact ⟨u,hu,hUS.trans hSu⟩
end SupportIncidence
lemma exists_unit_orthogonal_dim {k n : ℕ} (hn : n < k) (v : Fin n → Euc (Fin k)) :
    ∃ w : Euc (Fin k), ‖w‖ = 1 ∧ ∀ i, ⟪v i,w⟫ = 0 := by
  classical
  let W : Submodule ℝ (Euc (Fin k)) := Submodule.span ℝ (Set.range v)
  have hW : W ≠ ⊤ := by
    intro he
    have hh := finrank_le_of_span_eq_top he
    have hd : Module.finrank ℝ (Euc (Fin k)) = k := by simp
    rw [hd,Fintype.card_fin] at hh
    omega
  have hO : Wᗮ ≠ ⊥ := fun he => hW (Submodule.orthogonal_eq_bot_iff.mp he)
  obtain ⟨w,hw,hwne⟩ := (Submodule.ne_bot_iff Wᗮ).mp hO
  refine ⟨(‖w‖⁻¹ : ℝ) • w,norm_smul_inv_norm hwne,?_⟩
  intro i
  rw [inner_smul_right,Submodule.inner_right_of_mem_orthogonal
    (show v i ∈ W from Submodule.subset_span (Set.mem_range_self i)) hw,mul_zero]
lemma Admissible.exists_label_absent_dim {k n : ℕ} {ι : Type*} [Fintype ι]
    {f : Euc (Fin k) → ι → ℝ} (hf : Admissible f) (hn : n < k)
    (v : Fin n → Euc (Fin k)) (hv : ∀ j, ‖v j‖ = 1) :
    ∃ i, ∀ j, i ∉ positiveSupport f (v j) := by
  obtain ⟨w,hw,hvw⟩ := exists_unit_orthogonal_dim hn v
  obtain ⟨i,hi⟩ := hf.support_nonempty hw
  exact ⟨i,fun j hj => Finset.disjoint_left.mp (hf.disjoint_supports (hv j) hw (hvw j)) hj hi⟩
section SixPure
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma Admissible.support_card_three_le_of_card {f : (Euc (Fin 3)) → ι → ℝ}
    (hf : Admissible f) (hcard : Fintype.card ι = 6) {u : (Euc (Fin 3))} (hu : ‖u‖ = 1) :
    (positiveSupport f u).card ≤ 3 := by
  classical
  obtain ⟨e,he⟩ := orthogonal_isometry 2 hu
  let s := (positiveSupport f u)ᶜ
  have hzero : ∀ x, ‖x‖ = 1 → ∀ i ∉ s, f (e x) i = 0 := by
    intro x hx i hi
    have hip : 0 < f u i := (mem_positiveSupport _ _ _).mp (by simpa [s] using hi)
    have hn := hf.nonneg (e x) (by simpa using hx) i
    exact le_antisymm (le_of_not_gt (fun hp => hf.orthogonal u (e x) hu
      (by simpa using hx) (he x) i ⟨hip,hp⟩)) hn
  have hb := ((hf.comp_isometry e).restrict_labels s hzero).label_bound
  have hc : Fintype.card (UpperTriangle (Fin 2)) = 3 := by decide
  rw [hc,Fintype.card_coe,Finset.card_compl,hcard] at hb
  omega
lemma Admissible.support_extends_three_of_card {f : (Euc (Fin 3)) → ι → ℝ} (hf : Admissible f)
    (hcard : Fintype.card ι = 6) {w : (Euc (Fin 3))} (hw : ‖w‖ = 1) :
    ∃ u, ‖u‖ = 1 ∧ positiveSupport f w ⊆ positiveSupport f u ∧ (positiveSupport f u).card = 3 := by
  obtain ⟨u,hu,hwu,hm⟩ := exists_maximal_support f hw
  have hl := hf.support_card_three_le_of_card hcard hu
  have hdim : Fintype.card (UpperTriangle (Fin 3)) = Fintype.card ι := by rw [hcard]; decide
  have hb := hf.maximal_support_complement_bound (k := 2) hdim (by omega) hu hm
  have hc : Fintype.card (UpperTriangle (Fin 2)) = 3 := by decide
  rw [Fintype.card_coe,Finset.card_compl,hcard,hc] at hb
  exact ⟨u,hu,hwu,by omega⟩
lemma Admissible.face_extends_three {f : (Euc (Fin 3)) → ι → ℝ} (hf : Admissible f)
    (hcard : Fintype.card ι = 6) {U : Finset ι} (hU : SupportFace f U) :
    ∃ I : Finset ι, I.card = 3 ∧ SupportFace f I ∧ U ⊆ I := by
  obtain ⟨w,hw,hUw⟩ := hU
  obtain ⟨u,hu,hwu,huc⟩ := hf.support_extends_three_of_card hcard hw
  exact ⟨positiveSupport f u,huc,⟨u,hu,Finset.Subset.refl _⟩,hUw.trans hwu⟩
lemma Admissible.triangle_no_free_edge {f : (Euc (Fin 3)) → ι → ℝ} (hf : Admissible f)
    (hcard : Fintype.card ι = 6) {I U : Finset ι} (hIc : I.card = 3)
    (hIf : SupportFace f I) (hUI : U ⊆ I) (hUc : U.card = 2) :
    ∃ I' : Finset ι, I'.card = 3 ∧ SupportFace f I' ∧ U ⊆ I' ∧ I' ≠ I := by
  classical
  obtain ⟨w,hw,hIw⟩ := hIf
  have hmax (u : (Euc (Fin 3))) (hu : ‖u‖ = 1) (hIu : I ⊆ positiveSupport f u) : positiveSupport f u = I :=
    (Finset.eq_of_subset_of_card_le hIu (by rw [hIc]; exact hf.support_card_three_le_of_card hcard hu)).symm
  have hcomp : (Iᶜ : Finset ι).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_compl,hcard,hIc]
    decide
  let : Nonempty ↥(Iᶜ : Finset ι) := hcomp.to_subtype
  have hdim : Fintype.card (UpperTriangle (Fin 3)) = Fintype.card ι := by rw [hcard]; decide
  obtain ⟨u,hu,hUu,hnu⟩ := hf.no_free_ridge (k := 2) (by decide) hdim (by omega) hIc hUI hUc hmax hw
    (fun i hi => (mem_positiveSupport f w i).mp (hIw hi))
  obtain ⟨I',hI'c,hI'f,hI'u⟩ := hf.face_extends_three hcard (⟨u,hu,Finset.Subset.refl _⟩ : SupportFace f (positiveSupport f u))
  exact ⟨I',hI'c,hI'f,hUu.trans hI'u,fun he => hnu (he ▸ hI'u)⟩
end SixPure
end
end

section
open Set MeasureTheory
section
open scoped RealInnerProductSpace
section TenPure
lemma Admissible.face_extends_four {f : Vector4 → Fin 10 → ℝ} (hf : Admissible f)
    {U : Finset (Fin 10)} (hU : SupportFace f U) :
    ∃ I : Finset (Fin 10), I.card = 4 ∧ SupportFace f I ∧ U ⊆ I := by
  obtain ⟨w,hw,hUw⟩ := hU
  obtain ⟨u,hu,hwu,huc⟩ := hf.support_extends_four hw
  exact ⟨positiveSupport f u,huc,⟨u,hu,Finset.Subset.refl _⟩,hUw.trans hwu⟩
lemma Admissible.tetra_no_free_triangle {f : Vector4 → Fin 10 → ℝ} (hf : Admissible f)
    {I U : Finset (Fin 10)} (hIc : I.card = 4) (hIf : SupportFace f I)
    (hUI : U ⊆ I) (hUc : U.card = 3) :
    ∃ I' : Finset (Fin 10), I'.card = 4 ∧ SupportFace f I' ∧ U ⊆ I' ∧ I' ≠ I := by
  classical
  obtain ⟨w,hw,hIw⟩ := hIf
  have hmax (u : Vector4) (hu : ‖u‖ = 1) (hIu : I ⊆ positiveSupport f u) : positiveSupport f u = I :=
    (Finset.eq_of_subset_of_card_le hIu (by rw [hIc]; exact hf.support_card_four_le hu)).symm
  have hcomp : (Iᶜ : Finset (Fin 10)).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_compl,Fintype.card_fin,hIc]
    decide
  let : Nonempty ↥(Iᶜ : Finset (Fin 10)) := hcomp.to_subtype
  obtain ⟨u,hu,hUu,hnu⟩ := hf.no_free_ridge (k := 3) (by decide) (by decide) (by decide) hIc hUI hUc hmax hw
    (fun i hi => (mem_positiveSupport f w i).mp (hIw hi))
  obtain ⟨I',hI'c,hI'f,hI'u⟩ := hf.face_extends_four (⟨u,hu,Finset.Subset.refl _⟩ : SupportFace f (positiveSupport f u))
  exact ⟨I',hI'c,hI'f,hUu.trans hI'u,fun he => hnu (he ▸ hI'u)⟩
end TenPure
end
section
open Set SimplicialChains
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
section TwoLabels
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma Admissible.sum_two_labels {f : V → ι → ℝ} (hf : Admissible f)
    {u : V} (hu : ‖u‖ = 1) {i j : ι} (hij : i ≠ j)
    (hzero : ∀ l, l ≠ i → l ≠ j → f u l = 0) : f u i + f u j = 1 := by
  have hsum : ∑ l, f u l = ∑ l ∈ ({i,j} : Finset ι), f u l :=
    (Finset.sum_subset (Finset.subset_univ _) (fun l _ hl => hzero l (by aesop) (by aesop))).symm
  simpa only [Finset.sum_pair hij] using hsum.symm.trans (hf.sum_one u hu)
lemma Admissible.two_labels_meet {f : V → ι → ℝ} (hf : Admissible f)
    (W : Submodule ℝ V) {i j : ι} (hij : i ≠ j)
    (hzero : ∀ u ∈ W, ‖u‖ = 1 → ∀ l, l ≠ i → l ≠ j → f u l = 0)
    {u v : V} (huW : u ∈ W) (hu : ‖u‖ = 1) (hui : 0 < f u i)
    (hvW : v ∈ W) (hv : ‖v‖ = 1) (hvj : 0 < f v j) :
    ∃ w : V, ‖w‖ = 1 ∧ 0 < f w i ∧ 0 < f w j := by
  classical
  by_contra hn
  have hnot (w : V) (hw : ‖w‖ = 1) : ¬ (0 < f w i ∧ 0 < f w j) := fun hh => hn ⟨w,hw,hh⟩
  have hui' : f u i = 1 := by
    have hj0 : f u j = 0 := le_antisymm (not_lt.mp (fun hp => hnot u hu ⟨hui,hp⟩)) (hf.nonneg u hu j)
    have hh := hf.sum_two_labels hu hij (hzero u huW hu)
    linarith
  have hvi : f v i = 0 := le_antisymm (not_lt.mp (fun hp => hnot v hv ⟨hp,hvj⟩)) (hf.nonneg v hv i)
  obtain ⟨v',hv'W,hv',hv'i,hinner⟩ : ∃ v' : V, v' ∈ W ∧ ‖v'‖ = 1 ∧ f v' i = 0 ∧ 0 ≤ ⟪u,v'⟫ := by
    by_cases hi : 0 ≤ ⟪u,v⟫
    · exact ⟨v,hvW,hv,hvi,hi⟩
    · exact ⟨-v,W.neg_mem hvW,by simpa using hv,by simpa only [hf.antipodal] using hvi,by simp only [inner_neg_right]; linarith⟩
  let p : ℝ → V := fun t => (1-t) • u + t • v'
  have hp : Continuous p := ((continuous_const.sub continuous_id).smul continuous_const).add (continuous_id.smul continuous_const)
  have hpW (t : ℝ) : p t ∈ W := W.add_mem (W.smul_mem _ huW) (W.smul_mem _ hv'W)
  have hpz (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : p t ≠ 0 := by
    intro hz
    have hi := congrArg (fun x : V => ⟪u,x⟫) hz
    have hi' : (1-t)+t*⟪u,v'⟫ = 0 := by
      simpa only [p,inner_add_right,inner_smul_right,real_inner_self_eq_norm_sq,hu,one_pow,mul_one,inner_zero_right] using hi
    have ht1 : t = 1 := by nlinarith [ht.2,mul_nonneg ht.1 hinner]
    have hv0 : v' = 0 := by simpa only [p,ht1,sub_self,zero_smul,one_smul,zero_add] using hz
    simp [hv0] at hv'
  let q : ℝ → V := fun t => unitRadial (p t)
  have hq : ContinuousOn q (Icc (0:ℝ) 1) :=
    (unitRadial_continuousOn (S := p '' Icc (0:ℝ) 1) (by rintro x ⟨t,ht,rfl⟩; exact hpz t ht)).comp hp.continuousOn (fun t ht => ⟨t,ht,rfl⟩)
  have hqn (t) (ht : t ∈ Icc (0:ℝ) 1) : ‖q t‖ = 1 := unitRadial_norm (hpz t ht)
  have hqW (t) : q t ∈ W := W.smul_mem _ (hpW t)
  have hq0 : q 0 = u := by simp only [q,p,sub_zero,one_smul,zero_smul,add_zero,unitRadial,hu,inv_one,one_smul]
  have hq1 : q 1 = v' := by simp only [q,p,sub_self,zero_smul,one_smul,zero_add,unitRadial,hv',inv_one,one_smul]
  have hcont : ContinuousOn (fun t => f (q t) i) (Icc (0:ℝ) 1) := (hf.smooth i).continuous.comp_continuousOn hq
  have hhalf : (1/2 : ℝ) ∈ Icc (f (q 1) i) (f (q 0) i) := by rw [hq0,hq1,hui',hv'i]; constructor <;> norm_num
  obtain ⟨t,ht,hth⟩ := intermediate_value_Icc' (zero_le_one : (0:ℝ) ≤ 1) hcont hhalf
  have hsum := hf.sum_two_labels (hqn t ht) hij (hzero (q t) (hqW t) (hqn t ht))
  exact hnot (q t) (hqn t ht) ⟨by linarith,by linarith⟩
end TwoLabels
end
end

section
open Set MeasureTheory
section
open Set SimplicialChains
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
section AllPairs
variable {ν ι : Type*} [Fintype ν] [LinearOrder ν] [Nonempty ν] [Fintype ι] [DecidableEq ι]
lemma Admissible.all_pairs {f : (Euc ν) → ι → ℝ} (hf : Admissible f)
    (hdim : Fintype.card (UpperTriangle ν) = Fintype.card ι) {i j : ι} (hij : i ≠ j) :
    ∃ u : (Euc ν), ‖u‖ = 1 ∧ 0 < f u i ∧ 0 < f u j := by
  classical
  let y : ι → ℝ := fun l => if l = i ∨ l = j then 1 else -1
  have hy : y ≠ 0 := by intro h; have hi := congrFun h i; simp [y] at hi
  obtain ⟨A,hA,t,ht,hAt⟩ := hf.signedExtension_ray hdim hy
  have hai : 0 < signedExtension f A i := by rw [hAt]; simpa [y] using ht
  have haj : 0 < signedExtension f A j := by rw [hAt]; simpa [y] using ht
  obtain ⟨u,huW,hu,hui⟩ := (hf.signedExtension_positive_support A i).mp hai
  obtain ⟨v,hvW,hv,hvj⟩ := (hf.signedExtension_positive_support A j).mp haj
  apply hf.two_labels_meet (LinearMap.range ((matrixOp ν) A⁺).toLinearMap) hij ?_ huW hu hui hvW hv hvj
  intro w hw hwn l hli hlj
  apply hf.signedExtension_range_labels (I := {i,j}) ?_ hw hwn (by simp [hli,hlj])
  intro l hl
  have hli : l ≠ i := by aesop
  have hlj : l ≠ j := by aesop
  rw [hAt]
  simp only [Pi.smul_apply,smul_eq_mul,y,if_neg (not_or.mpr ⟨hli,hlj⟩),mul_neg_one]
  linarith
end AllPairs
end
namespace SixCounting
variable {α : Type*} [DecidableEq α]
noncomputable local instance : DecidablePred (fun p : Prop => p) := Classical.propDecidable
noncomputable def triangles (C : Finset α) (T : Finset α → Prop) : Finset (Finset α) :=
  (C.powersetCard 3).filter T
omit [DecidableEq α] in
@[simp] lemma mem_triangles {C U : Finset α} {T : Finset α → Prop} :
    U ∈ triangles C T ↔ U ⊆ C ∧ U.card = 3 ∧ T U := by
  simp only [triangles, Finset.mem_filter, Finset.mem_powersetCard, and_assoc]
lemma pair_incidence_count (C : Finset α) (T : Finset α → Prop) :
    ∑ P ∈ C.powersetCard 2, ((triangles C T).filter (P ⊆ ·)).card =
      3 * (triangles C T).card := by
  classical
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  calc
    ∑ U ∈ triangles C T, ∑ P ∈ C.powersetCard 2, (if P ⊆ U then (1 : ℕ) else 0) =
        ∑ U ∈ triangles C T, (U.powersetCard 2).card := by
      apply Finset.sum_congr rfl
      intro U hU
      rw [← Finset.card_filter]
      congr 1
      ext P
      simp only [Finset.mem_filter, Finset.mem_powersetCard]
      exact ⟨fun h => ⟨h.2, h.1.2⟩,
        fun h => ⟨⟨h.1.trans (mem_triangles.mp hU).1, h.2⟩, h.1⟩⟩
    _ = 3 * (triangles C T).card := by
      have he : ∀ U ∈ triangles C T, (U.powersetCard 2).card = 3 := by
        intro U hU
        rw [Finset.card_powersetCard, (mem_triangles.mp hU).2.1]
        decide
      rw [Finset.sum_congr rfl he]
      simp [mul_comm]
lemma complement_triangle {C U : Finset α} (hC : C.card = 6)
    (hU : U ∈ C.powersetCard 3) : C \ U ∈ C.powersetCard 3 := by
  apply Finset.mem_powersetCard.mpr
  refine ⟨Finset.sdiff_subset, ?_⟩
  rw [Finset.card_sdiff_of_subset (Finset.mem_powersetCard.mp hU).1,
    hC, (Finset.mem_powersetCard.mp hU).2]
lemma triangle_count_upper {C : Finset α} {T : Finset α → Prop} (hC : C.card = 6)
    (hdisj : ∀ U ∈ C.powersetCard 3, T U → ¬T (C \ U)) :
    (triangles C T).card ≤ 10 := by
  classical
  let A := triangles C T
  let B := C.powersetCard 3 \ A
  have hA : A ⊆ C.powersetCard 3 := Finset.filter_subset _ _
  have hi : (A.image (fun U => C \ U)) ⊆ B := by
    intro U hU
    obtain ⟨V, hV, rfl⟩ := Finset.mem_image.mp hU
    apply Finset.mem_sdiff.mpr
    refine ⟨complement_triangle hC (hA hV), ?_⟩
    intro hh
    exact hdisj V (hA hV) (mem_triangles.mp hV).2.2 (mem_triangles.mp hh).2.2
  have hinj : Set.InjOn (fun U => C \ U) (↑A : Set (Finset α)) := by
    intro U hU V hV he
    have hh := congrArg (fun W => C \ W) he
    simpa only [Finset.sdiff_sdiff_eq_self (mem_triangles.mp hU).1,
      Finset.sdiff_sdiff_eq_self (mem_triangles.mp hV).1] using hh
  have hc : A.card ≤ B.card := calc
    A.card = (A.image (fun U => C \ U)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ B.card := Finset.card_le_card hi
  have hB : B.card = 20 - A.card := by
    rw [Finset.card_sdiff_of_subset hA, Finset.card_powersetCard, hC]
    norm_num [Nat.choose]
  change A.card ≤ 10
  omega
lemma triangle_count_eq_ten {C : Finset α} {T : Finset α → Prop} (hC : C.card = 6)
    (hdisj : ∀ U ∈ C.powersetCard 3, T U → ¬T (C \ U))
    (hpairs : ∀ P ∈ C.powersetCard 2, 2 ≤ ((triangles C T).filter (P ⊆ ·)).card) :
    (triangles C T).card = 10 := by
  have hupper := triangle_count_upper hC hdisj
  have hlower : 30 ≤ ∑ P ∈ C.powersetCard 2,
      ((triangles C T).filter (P ⊆ ·)).card := by
    calc
      30 = ∑ _P ∈ C.powersetCard 2, 2 := by
        norm_num [Finset.card_powersetCard, hC, Nat.choose]
      _ ≤ _ := Finset.sum_le_sum hpairs
  rw [pair_incidence_count] at hlower
  omega
lemma pair_degree_eq_two {C : Finset α} {T : Finset α → Prop} (hC : C.card = 6)
    (hdisj : ∀ U ∈ C.powersetCard 3, T U → ¬T (C \ U))
    (hpairs : ∀ P ∈ C.powersetCard 2, 2 ≤ ((triangles C T).filter (P ⊆ ·)).card)
    {P : Finset α} (hP : P ∈ C.powersetCard 2) :
    ((triangles C T).filter (P ⊆ ·)).card = 2 := by
  have hsum : (∑ _P ∈ C.powersetCard 2, 2) =
      ∑ P ∈ C.powersetCard 2, ((triangles C T).filter (P ⊆ ·)).card := by
    rw [pair_incidence_count, triangle_count_eq_ten hC hdisj hpairs]
    norm_num [Finset.card_powersetCard, hC, Nat.choose]
  exact ((Finset.sum_eq_sum_iff_of_le hpairs).mp hsum P hP).symm
lemma complementary_iff {C : Finset α} {T : Finset α → Prop} (hC : C.card = 6)
    (hdisj : ∀ U ∈ C.powersetCard 3, T U → ¬T (C \ U))
    (hpairs : ∀ P ∈ C.powersetCard 2, 2 ≤ ((triangles C T).filter (P ⊆ ·)).card)
    {U : Finset α} (hU : U ∈ C.powersetCard 3) : T U ↔ ¬T (C \ U) := by
  classical
  refine ⟨hdisj U hU, ?_⟩
  intro hn
  let A := triangles C T
  let B := C.powersetCard 3 \ A
  have hA : A ⊆ C.powersetCard 3 := Finset.filter_subset _ _
  have hi : (A.image (fun U => C \ U)) ⊆ B := by
    intro U hU
    obtain ⟨V, hV, rfl⟩ := Finset.mem_image.mp hU
    apply Finset.mem_sdiff.mpr
    refine ⟨complement_triangle hC (hA hV), ?_⟩
    intro hh
    exact hdisj V (hA hV) (mem_triangles.mp hV).2.2 (mem_triangles.mp hh).2.2
  have hinj : Set.InjOn (fun U => C \ U) (↑A : Set (Finset α)) := by
    intro U hU V hV he
    have hh := congrArg (fun W => C \ W) he
    simpa only [Finset.sdiff_sdiff_eq_self (mem_triangles.mp hU).1,
      Finset.sdiff_sdiff_eq_self (mem_triangles.mp hV).1] using hh
  have he : A.image (fun U => C \ U) = B := by
    apply Finset.eq_of_subset_of_card_le hi
    rw [Finset.card_image_of_injOn hinj, Finset.card_sdiff_of_subset hA,
      Finset.card_powersetCard, hC]
    change Nat.choose 6 3 - (triangles C T).card ≤ (triangles C T).card
    rw [triangle_count_eq_ten hC hdisj hpairs]
    decide
  have hcU : C \ U ∈ B := by
    apply Finset.mem_sdiff.mpr
    refine ⟨complement_triangle hC hU, ?_⟩
    intro hh
    exact hn (mem_triangles.mp hh).2.2
  rw [← he] at hcU
  obtain ⟨V, hV, hVU⟩ := Finset.mem_image.mp hcU
  have hEq : V = U := by
    have hh := congrArg (fun W => C \ W) hVU
    simpa only [Finset.sdiff_sdiff_eq_self (mem_triangles.mp hV).1,
      Finset.sdiff_sdiff_eq_self (Finset.mem_powersetCard.mp hU).1] using hh
  exact hEq ▸ (mem_triangles.mp hV).2.2
end SixCounting
end

section
open Set MeasureTheory
section
open scoped Classical
open scoped RealInnerProductSpace
section SixFaces
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma Admissible.six_complement_exclusion {f : (Euc (Fin 3)) → ι → ℝ} (hf : Admissible f)
    {U : Finset ι} (hU : SupportFace f U) : ¬ SupportFace f Uᶜ := by
  classical
  rintro ⟨v,hv,hUv⟩
  obtain ⟨u,hu,hUu⟩ := hU
  obtain ⟨i,hi⟩ := hf.exists_label_absent_dim (n := 2) (by decide) ![u,v] (by
    intro j
    fin_cases j <;> simp [hu,hv])
  by_cases h : i ∈ U
  · exact hi 0 (hUu h)
  · exact hi 1 (hUv (Finset.mem_compl.mpr h))
lemma Admissible.six_pair_lower {f : (Euc (Fin 3)) → ι → ℝ} (hf : Admissible f)
    (hcard : Fintype.card ι = 6) {P : Finset ι} (hPc : P.card = 2) :
    2 ≤ ((SixCounting.triangles Finset.univ (SupportFace f)).filter (P ⊆ ·)).card := by
  classical
  obtain ⟨i,j,hij,rfl⟩ := Finset.card_eq_two.mp hPc
  have hdim : Fintype.card (UpperTriangle (Fin 3)) = Fintype.card ι := by rw [hcard]; decide
  obtain ⟨u,hu,hui,huj⟩ := hf.all_pairs hdim hij
  have hpair : SupportFace f {i,j} := ⟨u,hu,by
    intro l hl
    simp only [Finset.mem_insert,Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact (mem_positiveSupport _ _ _).mpr hui
    · exact (mem_positiveSupport _ _ _).mpr huj⟩
  obtain ⟨I,hIc,hIf,hPI⟩ := hf.face_extends_three hcard hpair
  obtain ⟨I',hI'c,hI'f,hPI',hne⟩ := hf.triangle_no_free_edge hcard hIc hIf hPI (by simp [hij])
  have hsub : {I,I'} ⊆ (SixCounting.triangles Finset.univ (SupportFace f)).filter ({i,j} ⊆ ·) := by
    intro J hJ
    simp only [Finset.mem_insert,Finset.mem_singleton] at hJ
    rcases hJ with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨SixCounting.mem_triangles.mpr ⟨Finset.subset_univ _,hIc,hIf⟩,hPI⟩
    · exact Finset.mem_filter.mpr ⟨SixCounting.mem_triangles.mpr ⟨Finset.subset_univ _,hI'c,hI'f⟩,hPI'⟩
  have hc := Finset.card_le_card hsub
  simpa [hne.symm] using hc
lemma Admissible.six_complementary {f : (Euc (Fin 3)) → ι → ℝ} (hf : Admissible f)
    (hcard : Fintype.card ι = 6) {U : Finset ι} (hUc : U.card = 3) :
    SupportFace f U ↔ ¬ SupportFace f Uᶜ := by
  classical
  have hC : (Finset.univ : Finset ι).card = 6 := by simpa using hcard
  have hd : ∀ U ∈ (Finset.univ : Finset ι).powersetCard 3,
      SupportFace f U → ¬ SupportFace f (Finset.univ \ U) := by
    intro U _ hU
    simpa only [← Finset.compl_eq_univ_sdiff] using hf.six_complement_exclusion hU
  have hp : ∀ P ∈ (Finset.univ : Finset ι).powersetCard 2,
      2 ≤ ((SixCounting.triangles Finset.univ (SupportFace f)).filter (P ⊆ ·)).card := by
    intro P hP
    exact hf.six_pair_lower hcard (Finset.mem_powersetCard.mp hP).2
  simpa only [← Finset.compl_eq_univ_sdiff] using SixCounting.complementary_iff hC hd hp
    (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ U,hUc⟩)
lemma Admissible.six_pair_degree {f : (Euc (Fin 3)) → ι → ℝ} (hf : Admissible f)
    (hcard : Fintype.card ι = 6) {P : Finset ι} (hPc : P.card = 2) :
    ((SixCounting.triangles Finset.univ (SupportFace f)).filter (P ⊆ ·)).card = 2 := by
  classical
  apply SixCounting.pair_degree_eq_two
    (C := Finset.univ) (by simpa using hcard) ?_ ?_ (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,hPc⟩)
  · intro U _ hU
    simpa only [← Finset.compl_eq_univ_sdiff] using hf.six_complement_exclusion hU
  · intro P hP
    exact hf.six_pair_lower hcard (Finset.mem_powersetCard.mp hP).2
end SixFaces
lemma pair_triangle_card {α : Type*} [DecidableEq α] (C P : Finset α) (T : Finset α → Prop)
    (hPC : P ⊆ C) (hPc : P.card = 2) :
    (SixCounting.triangles C T |>.filter (P ⊆ ·)).card =
      ((C \ P).filter (fun w => T (insert w P))).card := by
  classical
  symm
  apply Finset.card_bij (fun w _ => insert w P)
  · intro w hw
    obtain ⟨hw,hT⟩ := Finset.mem_filter.mp hw
    obtain ⟨hwC,hwP⟩ := Finset.mem_sdiff.mp hw
    exact Finset.mem_filter.mpr ⟨SixCounting.mem_triangles.mpr
      ⟨Finset.insert_subset hwC hPC,by rw [Finset.card_insert_of_notMem hwP,hPc],hT⟩,Finset.subset_insert _ _⟩
  · intro w hw v hv he
    have hwP := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hw).1).2
    have hm : w ∈ insert v P := he ▸ Finset.mem_insert_self w P
    exact (Finset.mem_insert.mp hm).resolve_right hwP
  · intro U hU
    obtain ⟨hU,hPU⟩ := Finset.mem_filter.mp hU
    obtain ⟨hUC,hUc,hT⟩ := SixCounting.mem_triangles.mp hU
    have hd : (U \ P).card = 1 := by rw [Finset.card_sdiff_of_subset hPU,hUc,hPc]
    obtain ⟨w,hw⟩ := Finset.card_eq_one.mp hd
    have hwm : w ∈ U \ P := by rw [hw]; simp
    obtain ⟨hwU,hwP⟩ := Finset.mem_sdiff.mp hwm
    have he : insert w P = U := by
      have hh := Finset.sdiff_union_of_subset hPU
      simpa only [hw,Finset.singleton_union] using hh
    exact ⟨w,Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hUC hwU,hwP⟩,he ▸ hT⟩,he⟩
lemma Admissible.six_pair_count {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : Euc (Fin 3) → ι → ℝ} (hf : Admissible f)
    (hcard : Fintype.card ι = 6) {P : Finset ι} (hPc : P.card = 2) :
    ((Pᶜ : Finset ι).filter (fun w => SupportFace f (insert w P))).card = 2 := by
  classical
  rw [Finset.compl_eq_univ_sdiff,← pair_triangle_card _ _ _ (Finset.subset_univ P) hPc]
  exact hf.six_pair_degree hcard hPc
end
end

section
open Set MeasureTheory
section
open scoped RealInnerProductSpace
open scoped Classical
section Within
variable {α : Type*} [DecidableEq α]
noncomputable def withinLabels (C U : Finset α) : Finset C := U.subtype (· ∈ C)
@[simp] lemma mem_withinLabels {C U : Finset α} {i : C} :
    i ∈ withinLabels C U ↔ i.val ∈ U := Finset.mem_subtype
lemma withinLabels_card {C U : Finset α} (hUC : U ⊆ C) : (withinLabels C U).card = U.card := by
  rw [withinLabels,Finset.card_subtype,Finset.filter_true_of_mem]
  exact fun _ hi => hUC hi
lemma withinLabels_compl (C U : Finset α) :
    withinLabels C (C \ U) = (withinLabels C U)ᶜ := by
  ext i
  simp [i.property]
lemma withinLabels_insert (C U : Finset α) (i : C) :
    withinLabels C (insert i.val U) = insert i (withinLabels C U) := by
  ext j
  simp only [mem_withinLabels,Finset.mem_insert,Subtype.ext_iff]
end Within
section FacetSix
variable {f : Vector4 → Fin 10 → ℝ}
lemma Admissible.facet_complement_exclusion (hf : Admissible f) {S U : Finset (Fin 10)}
    (hS : SupportFace f S) (hU : SupportFace f U) : ¬ SupportFace f (Sᶜ \ U) := by
  classical
  rintro ⟨v,hv,hCv⟩
  obtain ⟨w,hw,hSw⟩ := hS
  obtain ⟨u,hu,hUu⟩ := hU
  obtain ⟨i,hi⟩ := hf.exists_label_absent_dim (n := 3) (by decide) ![w,u,v] (by
    intro j
    fin_cases j <;> simp [hw,hu,hv])
  by_cases hiS : i ∈ S
  · exact hi 0 (hSw hiS)
  by_cases hiU : i ∈ U
  · exact hi 1 (hUu hiU)
  exact hi 2 (hCv (Finset.mem_sdiff.mpr ⟨Finset.mem_compl.mpr hiS,hiU⟩))
lemma restricted_face_image {C U : Finset (Fin 10)} (hUC : U ⊆ C)
    (e : Euc (Fin 3) →ₗᵢ[ℝ] Vector4)
    (hU : SupportFace (fun x (i : C) => f (e x) i.val) (withinLabels C U)) :
    SupportFace f U := by
  obtain ⟨x,hx,hUx⟩ := hU
  refine ⟨e x,by simpa using hx,?_⟩
  intro i hi
  exact (mem_positiveSupport _ _ _).mpr ((mem_positiveSupport _ _ (⟨i,hUC hi⟩ : C)).mp
    (hUx (mem_withinLabels.mpr hi)))
lemma Admissible.facet_six_properties (hf : Admissible f) {S : Finset (Fin 10)}
    (hSc : S.card = 4) (hSf : SupportFace f S) :
    (∀ U ⊆ Sᶜ, U.card = 3 → (SupportFace f U ↔ ¬ SupportFace f (Sᶜ \ U))) ∧
    (∀ P ⊆ Sᶜ, P.card = 2 →
      ((Sᶜ \ P).filter (fun w => SupportFace f (insert w P))).card = 2) := by
  classical
  obtain ⟨w,hw,hSw⟩ := hSf
  obtain ⟨e,he⟩ := orthogonal_isometry 3 hw
  let C : Finset (Fin 10) := Sᶜ
  let g : Euc (Fin 3) → C → ℝ := fun x i => f (e x) i.val
  have hCc : C.card = 6 := by dsimp [C]; rw [Finset.card_compl,Fintype.card_fin,hSc]
  have hcard : Fintype.card C = 6 := by simpa using hCc
  have hzero : ∀ x, ‖x‖ = 1 → ∀ i ∉ C, f (e x) i = 0 := by
    intro x hx i hi
    have hiS : i ∈ S := by simpa [C] using hi
    have hwpos : 0 < f w i := (mem_positiveSupport _ _ _).mp (hSw hiS)
    exact le_antisymm (le_of_not_gt (fun hp => hf.orthogonal w (e x) hw
      (by simpa using hx) (he x) i ⟨hwpos,hp⟩)) (hf.nonneg _ (by simpa using hx) i)
  have hg : Admissible g := (hf.comp_isometry e).restrict_labels C hzero
  have hmap {U : Finset (Fin 10)} (hUC : U ⊆ C) :
      SupportFace g (withinLabels C U) → SupportFace f U := restricted_face_image hUC e
  have hfaces {U : Finset (Fin 10)} (hUC : U ⊆ C) (hUc : U.card = 3) :
      SupportFace g (withinLabels C U) ↔ SupportFace f U := by
    refine ⟨hmap hUC,?_⟩
    intro hU
    apply (hg.six_complementary hcard (by rw [withinLabels_card hUC,hUc])).mpr
    rw [← withinLabels_compl]
    intro hcomp
    exact hf.facet_complement_exclusion ⟨w,hw,hSw⟩ hU (hmap Finset.sdiff_subset hcomp)
  constructor
  · intro U hUC hUc
    have hcUc : (C \ U).card = 3 := by rw [Finset.card_sdiff_of_subset hUC,hCc,hUc]
    rw [← hfaces hUC hUc,← hfaces Finset.sdiff_subset hcUc,withinLabels_compl]
    exact hg.six_complementary hcard (by rw [withinLabels_card hUC,hUc])
  · intro P hPC hPc
    let P' := withinLabels C P
    have hP'c : P'.card = 2 := by rw [withinLabels_card hPC,hPc]
    have hinsert {i : C} (hi : i ∉ P') :
        SupportFace g (insert i P') ↔ SupportFace f (insert i.val P) := by
      have hiP : i.val ∉ P := by simpa only [P',mem_withinLabels] using hi
      have hh := hfaces (Finset.insert_subset i.property hPC)
        (by rw [Finset.card_insert_of_notMem hiP,hPc])
      simpa only [withinLabels_insert] using hh
    have hc := hg.six_pair_count hcard hP'c
    have hcount : ((P'ᶜ).filter (fun i => SupportFace g (insert i P'))).card =
        ((C \ P).filter (fun i => SupportFace f (insert i P))).card := by
      apply Finset.card_bij (fun i _ => i.val)
      · intro i hi
        obtain ⟨hiP,hif⟩ := Finset.mem_filter.mp hi
        have hiP' := Finset.mem_compl.mp hiP
        exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨i.property,by
          simpa only [P',mem_withinLabels] using hiP'⟩,(hinsert hiP').mp hif⟩
      · intro i _ j _ hij
        exact Subtype.ext hij
      · intro i hi
        obtain ⟨hiC,hif⟩ := Finset.mem_filter.mp hi
        obtain ⟨hiC,hiP⟩ := Finset.mem_sdiff.mp hiC
        have hiP' : (⟨i,hiC⟩ : C) ∉ P' := by simpa only [P',mem_withinLabels] using hiP
        exact ⟨⟨i,hiC⟩,Finset.mem_filter.mpr ⟨Finset.mem_compl.mpr hiP',(hinsert hiP').mpr hif⟩,rfl⟩
    exact hcount.symm.trans hc
end FacetSix
end
end

section
open Set MeasureTheory
namespace FiniteObstruction
abbrev Labels := Fin 10
abbrev Family := Finset Labels → Prop
open scoped Classical
structure TenSystem (T Q : Family) : Prop where
  tetra_card : ∀ S, Q S → S.card = 4
  down : ∀ S U, Q S → U ⊆ S → U.card = 3 → T U
  pure : ∀ U, T U → ∃ S, Q S ∧ U ⊆ S
  no_boundary : ∀ S U, Q S → U ⊆ S → U.card = 3 →
    ∃ S', Q S' ∧ U ⊆ S' ∧ S' ≠ S
  complementary : ∀ S U, Q S → U ⊆ Sᶜ → U.card = 3 →
    (T U ↔ ¬ T (Sᶜ \ U))
  pair_count : ∀ S P, Q S → P ⊆ Sᶜ → P.card = 2 →
    ((Sᶜ \ P).filter (fun w => T (insert w P))).card = 2
variable {T Q : Family}
@[simp] lemma map_compl (e : Equiv.Perm Labels) (S : Finset Labels) :
    Sᶜ.map e.toEmbedding = (S.map e.toEmbedding)ᶜ := by
  ext x
  simp
@[simp] lemma map_symm_map (e : Equiv.Perm Labels) (S : Finset Labels) :
    (S.map e.symm.toEmbedding).map e.toEmbedding = S := by
  ext x
  simp
@[simp] lemma symm_map_map (e : Equiv.Perm Labels) (S : Finset Labels) :
    (S.map e.toEmbedding).map e.symm.toEmbedding = S := by
  ext x
  simp
end FiniteObstruction
end

section
open Set MeasureTheory
section
open scoped Classical
theorem Admissible.support_ten_system {f : Vector4 → Fin 10 → ℝ} (hf : Admissible f) :
    FiniteObstruction.TenSystem (fun U => U.card = 3 ∧ SupportFace f U)
      (fun S => S.card = 4 ∧ SupportFace f S) := by
  classical
  constructor
  · intro S hS
    exact hS.1
  · intro S U hS hUS hUc
    exact ⟨hUc,hS.2.mono hUS⟩
  · intro U hU
    obtain ⟨S,hSc,hSf,hUS⟩ := hf.face_extends_four hU.2
    exact ⟨S,⟨hSc,hSf⟩,hUS⟩
  · intro S U hS hUS hUc
    obtain ⟨S',hS'c,hS'f,hUS',hne⟩ := hf.tetra_no_free_triangle hS.1 hS.2 hUS hUc
    exact ⟨S',⟨hS'c,hS'f⟩,hUS',hne⟩
  · intro S U hS hUC hUc
    have hCc : (Sᶜ \ U).card = 3 := by
      rw [Finset.card_sdiff_of_subset hUC,Finset.card_compl,Fintype.card_fin,hS.1,hUc]
    simpa only [hUc,hCc,true_and] using (hf.facet_six_properties hS.1 hS.2).1 U hUC hUc
  · intro S P hS hPC hPc
    trans ((Sᶜ \ P).filter (fun w => SupportFace f (insert w P))).card
    · apply congrArg Finset.card
      ext w
      simp only [Finset.mem_filter]
      constructor
      · intro support_mem
        exact ⟨support_mem.1, support_mem.2.2⟩
      · intro support_mem
        refine ⟨support_mem.1, ⟨?_, support_mem.2⟩⟩
        rw [Finset.card_insert_of_notMem (Finset.mem_sdiff.mp support_mem.1).2, hPc]
    · exact (hf.facet_six_properties hS.1 hS.2).2 P hPC hPc
end
end

end OAI.BorsukNine


namespace OAI.BorsukNine
open scoped RealInnerProductSpace

theorem input_projector_cover (U : Fin 10 → Set Vector4)
    (hc : ∀ x, ‖x‖ = 1 → ∃ i, x ∈ U i)
    (hb : ∀ i, ∃ b : ℝ, b < 2 ∧ ∀ x ∈ U i, ∀ y ∈ U i,
      ‖x‖ = 1 → ‖y‖ = 1 → 2*(1-⟪x,y⟫^2) ≤ b) : HasTenSmallCover := by
  let C (i : Fin 10) : Set Matrix4 := projector '' (U i ∩ {x : Vector4 | ‖x‖=1})
  refine ⟨C, ?_, ?_, ?_⟩
  · rintro i _ ⟨x,hx,rfl⟩
    exact ⟨x,hx.2,rfl⟩
  · rintro _ ⟨x,hx,rfl⟩
    obtain ⟨i,hi⟩ := hc x hx
    exact Set.mem_iUnion.mpr ⟨i,x,⟨hi,hx⟩,rfl⟩
  · intro i
    obtain ⟨b,hs,hd⟩ := hb i
    refine lt_of_le_of_lt (Metric.diam_le_of_forall_dist_le (Real.sqrt_nonneg (max b 0)) ?_)
      (Real.sqrt_lt_sqrt (by positivity) (max_lt hs (by norm_num)))
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
    have hn := hd x hx.1 y hy.1 hx.2 hy.2
    have hsq := projector_dist_sq x y hx.2 hy.2
    have hroot := Real.sq_sqrt (le_max_right b 0)
    nlinarith [le_max_left b 0,Real.sqrt_nonneg (max b 0), dist_nonneg (x:=projector x) (y:=projector y)]

end OAI.BorsukNine

open OAI.BorsukNine

theorem OMA.solution : OMA.R_Borsuk_borsuk_conjecture_not_of_nine_le_R1_H1_R1.H2 := by
  classical
  intro U hcov hsmall
  obtain ⟨f,hf⟩ := cover_to_admissible (input_projector_cover U hcov hsmall)
  let T (s : Finset (Fin 10)) := s.card=3 ∧ SupportFace f s
  let Q (s : Finset (Fin 10)) := s.card=4 ∧ SupportFace f s
  have h := hf.support_ten_system
  have hempty : SupportFace f ∅ :=
    ⟨EuclideanSpace.single 0 1,by simp,Finset.empty_subset _⟩
  obtain ⟨s,hs,hface,_⟩ := hf.face_extends_four hempty
  exact ⟨T,Q,⟨h.tetra_card,h.down,h.pure,h.no_boundary,h.complementary,h.pair_count⟩,s,hs,hface⟩

