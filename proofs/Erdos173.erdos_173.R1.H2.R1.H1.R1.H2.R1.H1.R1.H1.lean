import OMAReductions.R_Erdos173_erdos_173_R1_H2_R1_H1_R1_H2_R1_H1_R1

/-! Ergodic decomposition for a bounded observable. Adapted from OpenAI,
openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a, via Jacob Parish,
plasma-ai/erdos-173@4a368a652753. Both sources are Apache-2.0. -/


-- OAI.Analysis.PlaneSpectrum.InvariantMean
section
namespace ParishMix

noncomputable section
open scoped ComplexConjugate
noncomputable section
open scoped BigOperators

noncomputable section
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
namespace PlaneFiveColor.InvariantMean

local instance (α : Type*) : DecidableEq α := Classical.decEq α

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]

private def shift (g : G) (f : G →ᵇ ℝ) : G →ᵇ ℝ :=
  f.compContinuous ⟨fun x => x + g, continuous_of_discreteTopology⟩

@[simp] lemma shift_apply (g x : G) (f : G →ᵇ ℝ) : shift g f x = f (x+g) := rfl

lemma shift_comm (g h : G) (f : G →ᵇ ℝ) : shift g (shift h f) = shift h (shift g f) := by
  ext x
  simp only [shift_apply, add_assoc, add_comm g h]

@[simp] lemma shift_add (g : G) (f h : G →ᵇ ℝ) : shift g (f+h) = shift g f + shift g h := by
  ext x
  rfl

@[simp] lemma shift_sub (g : G) (f h : G →ᵇ ℝ) : shift g (f-h) = shift g f - shift g h := by
  ext x
  rfl

@[simp] lemma shift_smul (g : G) (c : ℝ) (f : G →ᵇ ℝ) : shift g (c • f) = c • shift g f := by
  ext x
  rfl

lemma shift_norm_le (g : G) (f : G →ᵇ ℝ) : ‖shift g f‖ ≤ ‖f‖ := by
  exact BoundedContinuousFunction.norm_compContinuous_le _ _

private def single (g : G) (n : ℕ) (f : G →ᵇ ℝ) : G →ᵇ ℝ :=
  ((n+1 : ℕ) : ℝ)⁻¹ • ∑ k ∈ Finset.range (n+1), shift (k • g) f

@[simp] lemma single_apply (g x : G) (n : ℕ) (f : G →ᵇ ℝ) :
    single g n f x = ((n+1 : ℕ) : ℝ)⁻¹ * ∑ k ∈ Finset.range (n+1), f (x+k • g) := by
  simp [single]

lemma single_norm_le (g : G) (n : ℕ) (f : G →ᵇ ℝ) : ‖single g n f‖ ≤ ‖f‖ := by
  have hn : (0 : ℝ) < (n+1 : ℕ) := Nat.cast_pos.mpr (Nat.succ_pos _)
  calc
    ‖single g n f‖ = ((n+1 : ℕ) : ℝ)⁻¹ * ‖∑ k ∈ Finset.range (n+1), shift (k • g) f‖ := by
      rw [single, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn)]
    _ ≤ ((n+1 : ℕ) : ℝ)⁻¹ * (∑ _k ∈ Finset.range (n+1), ‖f‖) := by
      gcongr
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => shift_norm_le _ _)
    _ = ‖f‖ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ hn.ne', one_mul]

@[simp] lemma single_add (g : G) (n : ℕ) (f h : G →ᵇ ℝ) :
    single g n (f+h) = single g n f + single g n h := by
  simp only [single, shift_add, Finset.sum_add_distrib, smul_add]

@[simp] lemma single_sub (g : G) (n : ℕ) (f h : G →ᵇ ℝ) :
    single g n (f-h) = single g n f - single g n h := by
  simp only [single, shift_sub, Finset.sum_sub_distrib, smul_sub]

@[simp] lemma single_smul (g : G) (n : ℕ) (c : ℝ) (f : G →ᵇ ℝ) :
    single g n (c • f) = c • single g n f := by
  simp only [single, shift_smul, ← Finset.smul_sum]
  exact smul_comm _ _ _

lemma single_shift (g h : G) (n : ℕ) (f : G →ᵇ ℝ) :
    single g n (shift h f) = shift h (single g n f) := by
  ext x
  simp only [single_apply, shift_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  abel

lemma single_const (g : G) (n : ℕ) (c : ℝ) :
    single g n (BoundedContinuousFunction.const G c) = BoundedContinuousFunction.const G c := by
  ext x
  simp only [single_apply, BoundedContinuousFunction.const_apply, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)), one_mul]

lemma single_nonneg (g : G) (n : ℕ) (f : G →ᵇ ℝ) (hf : ∀ x, 0 ≤ f x) :
    ∀ x, 0 ≤ single g n f x := by
  intro x
  rw [single_apply]
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg fun k hk => hf _

lemma single_telescope (g x : G) (n : ℕ) (f : G →ᵇ ℝ) :
    single g n (shift g f - f) x =
      ((n+1 : ℕ) : ℝ)⁻¹ * (f (x+(n+1) • g) - f x) := by
  rw [single_apply]
  congr 1
  have he (k : ℕ) : (shift g f - f) (x+k • g) =
      f (x+(k+1) • g) - f (x+k • g) := by
    simp only [BoundedContinuousFunction.sub_apply, shift_apply, add_nsmul, one_nsmul, add_assoc]
  simp_rw [he]
  simpa only [zero_nsmul, add_zero] using Finset.sum_range_sub (fun k => f (x+k • g)) (n+1)

lemma single_coboundary_norm (g : G) (n : ℕ) (f : G →ᵇ ℝ) :
    ‖single g n (shift g f - f)‖ ≤ 2 * ‖f‖ / (n+1 : ℕ) := by
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro x
  rw [single_telescope, Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < ((n+1 : ℕ) : ℝ)⁻¹)]
  have hb : |f (x+(n+1) • g) - f x| ≤ 2 * ‖f‖ := by
    calc
      _ ≤ |f (x+(n+1) • g)| + |f x| := abs_sub _ _
      _ ≤ ‖f‖ + ‖f‖ := add_le_add (f.norm_coe_le_norm _) (f.norm_coe_le_norm _)
      _ = _ := by ring
  calc
    _ ≤ ((n+1 : ℕ) : ℝ)⁻¹ * (2 * ‖f‖) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

private def cube : List G → ℕ → (G →ᵇ ℝ) → (G →ᵇ ℝ)
  | [], _, f => f
  | g::L, n, f => single g n (cube L n f)

lemma cube_norm_le (L : List G) (n : ℕ) (f : G →ᵇ ℝ) : ‖cube L n f‖ ≤ ‖f‖ := by
  induction L with
  | nil => exact le_rfl
  | cons g L ih => exact (single_norm_le g n _).trans ih

lemma cube_shift (L : List G) (g : G) (n : ℕ) (f : G →ᵇ ℝ) :
    cube L n (shift g f) = shift g (cube L n f) := by
  induction L with
  | nil => rfl
  | cons h L ih => simp only [cube, ih, single_shift]

@[simp] lemma cube_add (L : List G) (n : ℕ) (f h : G →ᵇ ℝ) :
    cube L n (f+h) = cube L n f + cube L n h := by
  induction L with
  | nil => rfl
  | cons g L ih => simp only [cube, ih, single_add]

@[simp] lemma cube_sub (L : List G) (n : ℕ) (f h : G →ᵇ ℝ) :
    cube L n (f-h) = cube L n f - cube L n h := by
  induction L with
  | nil => rfl
  | cons g L ih => simp only [cube, ih, single_sub]

@[simp] lemma cube_smul (L : List G) (n : ℕ) (c : ℝ) (f : G →ᵇ ℝ) :
    cube L n (c • f) = c • cube L n f := by
  induction L with
  | nil => rfl
  | cons g L ih => simp only [cube, ih, single_smul]

lemma cube_const (L : List G) (n : ℕ) (c : ℝ) :
    cube L n (BoundedContinuousFunction.const G c) = BoundedContinuousFunction.const G c := by
  induction L with
  | nil => rfl
  | cons g L ih => simp only [cube, ih, single_const]

lemma cube_nonneg (L : List G) (n : ℕ) (f : G →ᵇ ℝ) (hf : ∀ x, 0 ≤ f x) :
    ∀ x, 0 ≤ cube L n f x := by
  induction L with
  | nil => exact hf
  | cons g L ih => exact single_nonneg g n _ ih

lemma cube_coboundary_norm (L : List G) (g : G) (hg : g ∈ L) (n : ℕ) (f : G →ᵇ ℝ) :
    ‖cube L n (shift g f-f)‖ ≤ 2 * ‖f‖ / (n+1 : ℕ) := by
  induction L with
  | nil => simp at hg
  | cons h L ih =>
    rcases List.mem_cons.mp hg with rfl | hg
    · rw [cube, cube_sub, cube_shift]
      apply (single_coboundary_norm g n _).trans
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (cube_norm_le L n f) (by norm_num)) (by positivity)
    · exact (single_norm_le h n _).trans (ih hg)

private def approx (i : Finset G × ℕ) (f : G →ᵇ ℝ) : ℝ :=
  cube i.1.toList i.2 f 0

lemma approx_norm_le (i : Finset G × ℕ) (f : G →ᵇ ℝ) : ‖approx i f‖ ≤ ‖f‖ :=
  ((cube i.1.toList i.2 f).norm_coe_le_norm 0).trans (cube_norm_le _ _ _)

private def averagingUF (G : Type*) [AddCommGroup G] : Ultrafilter (Finset G × ℕ) :=
  Ultrafilter.of atTop

omit [TopologicalSpace G] [DiscreteTopology G] in
lemma averagingUF_le : (averagingUF G : Filter (Finset G × ℕ)) ≤ atTop :=
  Ultrafilter.of_le _

lemma approx_has_limit (f : G →ᵇ ℝ) :
    ∃ r : ℝ, Tendsto (fun i => approx i f) (averagingUF G : Filter _) (𝓝 r) := by
  have hb : (Ultrafilter.map (fun i => approx i f) (averagingUF G) : Filter ℝ) ≤
      𝓟 (Set.Icc (-‖f‖) ‖f‖) := by
    rw [Ultrafilter.coe_map, Filter.le_principal_iff, Filter.mem_map]
    apply Filter.Eventually.of_forall
    intro i
    exact abs_le.mp (approx_norm_le i f)
  obtain ⟨r, _, hr⟩ := isCompact_Icc.ultrafilter_le_nhds
    (Ultrafilter.map (fun i => approx i f) (averagingUF G)) hb
  exact ⟨r, hr⟩

private def mean (f : G →ᵇ ℝ) : ℝ :=
  (averagingUF G : Filter _).limUnder (fun i => approx i f)

lemma tendsto_approx (f : G →ᵇ ℝ) :
    Tendsto (fun i => approx i f) (averagingUF G : Filter _) (𝓝 (mean f)) :=
  tendsto_nhds_limUnder (approx_has_limit f)

lemma mean_add (f h : G →ᵇ ℝ) : mean (f+h) = mean f + mean h := by
  apply Tendsto.limUnder_eq
  convert (tendsto_approx f).add (tendsto_approx h) using 1
  simp only [approx, cube_add, BoundedContinuousFunction.add_apply]

lemma mean_smul (c : ℝ) (f : G →ᵇ ℝ) : mean (c • f) = c * mean f := by
  apply Tendsto.limUnder_eq
  convert (tendsto_approx f).const_mul c using 1
  simp only [approx, cube_smul, BoundedContinuousFunction.smul_apply, smul_eq_mul]

lemma mean_const (c : ℝ) : mean (BoundedContinuousFunction.const G c) = c := by
  apply Tendsto.limUnder_eq
  convert (tendsto_const_nhds : Tendsto (fun _ : Finset G × ℕ => c)
    (averagingUF G : Filter _) (𝓝 c)) using 1
  simp only [approx, cube_const, BoundedContinuousFunction.const_apply]

lemma mean_nonneg (f : G →ᵇ ℝ) (hf : ∀ x, 0 ≤ f x) : 0 ≤ mean f := by
  exact ge_of_tendsto (tendsto_approx f) (Filter.Eventually.of_forall fun i =>
    cube_nonneg i.1.toList i.2 f hf 0)

lemma mean_norm_le (f : G →ᵇ ℝ) : ‖mean f‖ ≤ ‖f‖ := by
  exact le_of_tendsto (tendsto_approx f).norm
    (Filter.Eventually.of_forall fun i => approx_norm_le i f)

omit [TopologicalSpace G] [DiscreteTopology G] in
lemma eventually_mem (g : G) : ∀ᶠ i : Finset G × ℕ in (averagingUF G : Filter _), g ∈ i.1 := by
  classical
  apply Filter.Eventually.filter_mono averagingUF_le
  apply Filter.eventually_atTop.mpr
  refine ⟨({g}, 0), fun i hi => ?_⟩
  exact hi.1 (Finset.mem_singleton_self g)

omit [TopologicalSpace G] [DiscreteTopology G] in
lemma tendsto_index : Tendsto (fun i : Finset G × ℕ => i.2)
    (averagingUF G : Filter _) atTop := by
  apply Tendsto.mono_left _ averagingUF_le
  apply tendsto_atTop.mpr
  intro n
  apply Filter.eventually_atTop.mpr
  exact ⟨(∅, n), fun i hi => hi.2⟩

omit [DiscreteTopology G] in
lemma tendsto_boundary (f : G →ᵇ ℝ) :
    Tendsto (fun i : Finset G × ℕ => 2 * ‖f‖ / (i.2+1 : ℕ))
      (averagingUF G : Filter _) (𝓝 0) := by
  have hn : Tendsto (fun i : Finset G × ℕ => ((i.2+1 : ℕ) : ℝ))
      (averagingUF G : Filter _) atTop :=
    tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp tendsto_index)
  simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
    (tendsto_inv_atTop_zero.comp hn).const_mul (2 * ‖f‖)

lemma mean_shift (g : G) (f : G →ᵇ ℝ) : mean (shift g f) = mean f := by
  have hz : Tendsto (fun i : Finset G × ℕ => approx i (shift g f) - approx i f)
      (averagingUF G : Filter _) (𝓝 0) := by
    apply squeeze_zero_norm' _ (tendsto_boundary f)
    filter_upwards [eventually_mem g] with i hi
    have h := ((cube i.1.toList i.2 (shift g f-f)).norm_coe_le_norm 0).trans
      (cube_coboundary_norm i.1.toList g (Finset.mem_toList.mpr hi) i.2 f)
    simpa only [cube_sub, BoundedContinuousFunction.sub_apply, approx] using h
  exact sub_eq_zero.mp (tendsto_nhds_unique ((tendsto_approx _).sub (tendsto_approx _)) hz)

private def meanCLM : (G →ᵇ ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := mean, map_add' := mean_add, map_smul' := mean_smul }
    1 (by intro f; change ‖mean f‖ ≤ 1 * ‖f‖; simpa only [one_mul] using mean_norm_le f)

@[simp] lemma meanCLM_apply (f : G →ᵇ ℝ) : meanCLM f = mean f := rfl
end PlaneFiveColor.InvariantMean
end
end
end
end ParishMix
end

-- OAI.MeasureTheory.CompactFactors.Amenability
section
namespace ParishMix

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal

open scoped RealInnerProductSpace BoundedContinuousFunction
namespace EuclideanFiveColor.Amenable
variable (G : Type*) [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]

private def shift {E : Type*} [PseudoMetricSpace E] (g : G) (f : G →ᵇ E) : G →ᵇ E :=
  f.compContinuous ⟨fun x => x + g, continuous_of_discreteTopology⟩

@[simp] lemma shift_apply {E : Type*} [PseudoMetricSpace E] (g x : G) (f : G →ᵇ E) :
    shift G g f x = f (x+g) := rfl

private structure Mean where
  map : (G →ᵇ ℝ) →L[ℝ] ℝ
  map_const : ∀ c, map (BoundedContinuousFunction.const G c) = c
  positive : ∀ f, (∀ x, 0 ≤ f x) → 0 ≤ map f
  invariant : ∀ g f, map (shift G g f) = map f

variable {G}
namespace Mean
variable (M : Mean G)
lemma mono (f h : G →ᵇ ℝ) (hf : ∀ x, f x ≤ h x) : M.map f ≤ M.map h := by
  have hm := M.positive (h-f) (fun x => sub_nonneg.mpr (hf x))
  simpa only [map_sub, sub_nonneg] using hm

lemma abs_le (f h : G →ᵇ ℝ) (hf : ∀ x, |f x| ≤ h x) : |M.map f| ≤ M.map h := by
  rw [_root_.abs_le]
  constructor
  · have := M.mono (-h) f (fun x => (_root_.abs_le.mp (hf x)).1)
    simpa only [map_neg] using this
  · exact M.mono f h fun x => (_root_.abs_le.mp (hf x)).2

lemma exists_lt {f : G →ᵇ ℝ} {ε : ℝ} (h : M.map f < ε) : ∃ g, f g < ε := by
  by_contra hn
  push Not at hn
  have := M.mono (BoundedContinuousFunction.const G ε) f hn
  rw [M.map_const] at this
  exact (not_lt_of_ge this) h

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

private def normFn (V : G →ᵇ H) : G →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => ‖V x‖)
    (continuous_norm.comp V.continuous) ‖V‖ (fun x => by simpa using V.norm_coe_le_norm x)
omit [AddCommGroup G] [DiscreteTopology G] [InnerProductSpace ℝ H] [CompleteSpace H] in
@[simp] lemma normFn_apply (V : G →ᵇ H) (x : G) : normFn V x = ‖V x‖ := rfl

private def pairing (V : G →ᵇ H) (v : H) : G →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => inner ℝ (V x) v)
    (V.continuous.inner continuous_const) (‖V‖ * ‖v‖)
    (fun x => (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (V.norm_coe_le_norm x) (norm_nonneg v)))
omit [AddCommGroup G] [DiscreteTopology G] [CompleteSpace H] in
@[simp] lemma pairing_apply (V : G →ᵇ H) (v : H) (x : G) : pairing V v x = inner ℝ (V x) v := rfl

omit [CompleteSpace H] in
lemma pairing_bound (V : G →ᵇ H) (v : H) :
    |M.map (pairing V v)| ≤ M.map (normFn V) * ‖v‖ := by
  have he : M.map (‖v‖ • normFn V) = M.map (normFn V) * ‖v‖ := by
    rw [map_smul]; simp [mul_comm]
  rw [← he]
  apply M.abs_le
  intro x
  simpa [mul_comm] using (norm_inner_le_norm (𝕜 := ℝ) (V x) v)

private def pairingMap (V : G →ᵇ H) : H →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun v => M.map (pairing V v)
      map_add' := by
        intro v w
        have he : pairing V (v+w) = pairing V v + pairing V w := by ext; simp [inner_add_right]
        rw [he, map_add]
      map_smul' := by
        intro c v
        have he : pairing V (c • v) = c • pairing V v := by ext; simp [inner_smul_right]
        rw [he, map_smul]; rfl }
    (M.map (normFn V)) (fun v => M.pairing_bound V v)

private def vector (V : G →ᵇ H) : H := (InnerProductSpace.toDual ℝ H).symm (M.pairingMap V)

lemma vector_pair (V : G →ᵇ H) (v : H) :
    inner ℝ (M.vector V) v = M.map (pairing V v) := InnerProductSpace.toDual_symm_apply

lemma vector_norm_le (V : G →ᵇ H) : ‖M.vector V‖ ≤ M.map (normFn V) := by
  rw [vector, LinearIsometryEquiv.norm_map]
  apply (M.pairingMap V).opNorm_le_bound (M.positive _ (fun x => by simp))
  exact M.pairing_bound V

lemma vector_add (V W : G →ᵇ H) : M.vector (V+W) = M.vector V + M.vector W := by
  apply ext_inner_right ℝ; intro v
  rw [inner_add_left, M.vector_pair, M.vector_pair, M.vector_pair]
  have he : pairing (V+W) v = pairing V v + pairing W v := by ext; simp [inner_add_left]
  rw [he, map_add]

lemma vector_smul (c : ℝ) (V : G →ᵇ H) : M.vector (c • V) = c • M.vector V := by
  apply ext_inner_right ℝ; intro v
  rw [real_inner_smul_left, M.vector_pair, M.vector_pair]
  have he : pairing (c • V) v = c • pairing V v := by ext; simp [real_inner_smul_left]
  rw [he, map_smul]; rfl

lemma vector_shift (V : G →ᵇ H) (g : G) : M.vector (shift G g V) = M.vector V := by
  apply ext_inner_right ℝ; intro v
  rw [M.vector_pair, M.vector_pair]
  exact M.invariant g (pairing V v)

lemma vector_map {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℝ J] [CompleteSpace J]
    (L : H →L[ℝ] J) (V : G →ᵇ H) :
    M.vector (L.compLeftContinuousBounded G V) = L (M.vector V) := by
  apply ext_inner_right ℝ; intro v
  rw [M.vector_pair, ← L.adjoint_inner_right, M.vector_pair]
  congr 1; ext x
  exact (L.adjoint_inner_right (V x) v).symm

end Mean
end EuclideanFiveColor.Amenable

namespace EuclideanFiveColor.Amenable.Mean
open scoped BoundedContinuousFunction
variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
variable (M : Mean G)
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

private def orbit (U : G → H ≃ₗᵢ[ℝ] H) (v : H) : G →ᵇ H :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun g => U g v)
    continuous_of_discreteTopology ‖v‖ (fun g => le_of_eq ((U g).norm_map v))

omit [AddCommGroup G] [CompleteSpace H] in
@[simp] lemma orbit_apply (U : G → H ≃ₗᵢ[ℝ] H) (v : H) (g : G) : orbit U v g = U g v := rfl

lemma vector_orbit_invariant (U : G → H ≃ₗᵢ[ℝ] H)
    (hU : ∀ g h v, U (g+h) v = U g (U h v)) (v : H) (g : G) :
    U g (M.vector (orbit U v)) = M.vector (orbit U v) := by
  change (U g).toLinearIsometry.toContinuousLinearMap (M.vector (orbit U v)) = _
  rw [← M.vector_map (U g).toLinearIsometry.toContinuousLinearMap]
  have he : (U g).toLinearIsometry.toContinuousLinearMap.compLeftContinuousBounded G (orbit U v) =
      shift G g (orbit U v) := by
    ext h
    change U g (U h v) = U (h+g) v
    rw [add_comm h g, hU]
  rw [he, M.vector_shift]

end EuclideanFiveColor.Amenable.Mean

namespace EuclideanFiveColor.Amenable.Koopman
open MeasureTheory Filter
section Action
variable {G X E : Type*} [AddCommGroup G] [MeasurableSpace X]
  [AddAction G X] [MeasurableConstVAdd G X] (μ : Measure X)
  [VAddInvariantMeasure G X μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private def linear (g : G) : Lp E 2 μ →ₗᵢ[ℝ] Lp E 2 μ :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun x => g +ᵥ x) (measurePreserving_vadd g μ)

lemma linear_add (g h : G) (f : Lp E 2 μ) :
    linear μ (g+h) f = linear μ g (linear μ h f) := by
  change Lp.compMeasurePreserving (fun x => (g+h) +ᵥ x) _ f =
    Lp.compMeasurePreserving (fun x => g +ᵥ x) _
      (Lp.compMeasurePreserving (fun x => h +ᵥ x) _ f)
  have he : (fun x : X => (g+h) +ᵥ x) =
      (fun x => h +ᵥ x) ∘ (fun x => g +ᵥ x) := by
    funext x
    simp only [Function.comp_apply, ← add_vadd, add_comm]
  simpa only [he] using Lp.compMeasurePreserving_comp_apply f
    (measurePreserving_vadd h μ) (measurePreserving_vadd g μ)

@[simp] lemma linear_zero (f : Lp E 2 μ) : linear μ (0 : G) f = f := by
  change Lp.compMeasurePreserving (fun x => (0 : G) +ᵥ x) _ f = f
  have he : (fun x : X => (0 : G) +ᵥ x) = id := funext (fun x => zero_vadd G x)
  simpa only [he] using Lp.compMeasurePreserving_id_apply f

private def action (g : G) : Lp E 2 μ ≃ₗᵢ[ℝ] Lp E 2 μ :=
  LinearIsometryEquiv.ofSurjective (linear μ g) (fun f =>
    ⟨linear μ (-g) f, by rw [← linear_add, add_neg_cancel, linear_zero]⟩)

@[simp] lemma action_apply (g : G) (f : Lp E 2 μ) : action μ g f = linear μ g f := rfl

lemma action_add (g h : G) (f : Lp E 2 μ) :
    action μ (g+h) f = action μ g (action μ h f) := linear_add μ g h f

lemma coe_action (g : G) (f : Lp E 2 μ) :
    action μ g f =ᵐ[μ] (fun x => f (g +ᵥ x)) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_vadd g μ)

end Action
end EuclideanFiveColor.Amenable.Koopman
end
end ParishMix
end

-- OAI.MeasureTheory.CompactFactors.BoundedFunctions
section
namespace ParishMix

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal
namespace EuclideanFiveColor.BoundedMeasurable

section
variable (X : Type*) [MeasurableSpace X]

private def algebra : Subalgebra ℂ (X → ℂ) where
  carrier := {f | Measurable f ∧ ∃ C : ℝ≥0, ∀ x, ‖f x‖ ≤ C}
  zero_mem' := ⟨measurable_const, ⟨0, by simp⟩⟩
  one_mem' := ⟨measurable_const, ⟨1, by simp⟩⟩
  add_mem' := by
    rintro f g ⟨hf, C, hC⟩ ⟨hg, D, hD⟩
    exact ⟨hf.add hg, C+D, fun x => (norm_add_le _ _).trans (add_le_add (hC x) (hD x))⟩
  mul_mem' := by
    rintro f g ⟨hf, C, hC⟩ ⟨hg, D, hD⟩
    refine ⟨hf.mul hg, C*D, fun x => ?_⟩
    simpa only [Pi.mul_apply, norm_mul, NNReal.coe_mul] using
      mul_le_mul (hC x) (hD x) (norm_nonneg _) C.coe_nonneg
  algebraMap_mem' c := ⟨measurable_const, ‖c‖₊, fun _ => le_rfl⟩

private abbrev Func := ↥(algebra X)
variable {X}
private instance : CoeFun (Func X) (fun _ => X → ℂ) := ⟨Subtype.val⟩

lemma measurable (f : Func X) : Measurable (f : X → ℂ) := f.property.1

private def bound (f : Func X) : ℝ≥0 := f.property.2.choose
lemma norm_le_bound (f : Func X) (x : X) : ‖f x‖ ≤ bound f := f.property.2.choose_spec x

lemma ext {f g : Func X} (h : ∀ x, f x = g x) : f = g := Subtype.ext (funext h)
@[simp] lemma add_apply (f g : Func X) (x : X) : (f+g) x = f x + g x := rfl
@[simp] lemma mul_apply (f g : Func X) (x : X) : (f*g) x = f x * g x := rfl
@[simp] lemma sub_apply (f g : Func X) (x : X) : (f-g) x = f x - g x := rfl
@[simp] lemma zero_apply (x : X) : (0 : Func X) x = 0 := rfl
@[simp] lemma one_apply (x : X) : (1 : Func X) x = 1 := rfl
@[simp] lemma smul_apply (c : ℂ) (f : Func X) (x : X) : (c • f) x = c * f x := rfl
@[simp] lemma real_smul_apply (c : ℝ) (f : Func X) (x : X) : (c • f) x = c • f x := rfl

private def bmConj (f : Func X) : Func X :=
  ⟨fun x => star (f x), continuous_star.measurable.comp (measurable f), bound f, fun x => by simpa using norm_le_bound f x⟩
@[simp] lemma conj_apply (f : Func X) (x : X) : bmConj f x = star (f x) := rfl

private def comp {Y : Type*} [MeasurableSpace Y] (f : Func Y) (q : X → Y) (hq : Measurable q) : Func X :=
  ⟨fun x => f (q x), (measurable f).comp hq, bound f, fun x => norm_le_bound f (q x)⟩
@[simp] lemma comp_apply {Y : Type*} [MeasurableSpace Y]
    (f : Func Y) (q : X → Y) (hq : Measurable q) (x : X) : comp f q hq x = f (q x) := rfl

variable (μ : Measure X) [IsFiniteMeasure μ]

lemma memLp (f : Func X) (p : ℝ≥0∞) : MemLp (f : X → ℂ) p μ :=
  MemLp.of_bound (measurable f).aestronglyMeasurable (bound f) (.of_forall (norm_le_bound f))

private def lp (p : ℝ≥0∞) (f : Func X) : Lp ℂ p μ := (memLp μ f p).toLp f
lemma coe_lp (p : ℝ≥0∞) (f : Func X) : lp μ p f =ᵐ[μ] f := MemLp.coeFn_toLp _

lemma lp_congr (p : ℝ≥0∞) {f g : Func X} (h : f =ᵐ[μ] g) : lp μ p f = lp μ p g :=
  MemLp.toLp_congr _ _ h

lemma lp_add (p : ℝ≥0∞) (f g : Func X) : lp μ p (f+g) = lp μ p f + lp μ p g :=
  (MemLp.toLp_add (memLp μ f p) (memLp μ g p)).symm

lemma lp_smul (p : ℝ≥0∞) (c : ℝ) (f : Func X) : lp μ p (c • f) = c • lp μ p f := rfl

def l2 : Func X →ₗ[ℝ] Lp ℂ 2 μ where
  toFun := lp μ 2
  map_add' := lp_add μ 2
  map_smul' := lp_smul μ 2

lemma l2_ae (f : Func X) : l2 μ f =ᵐ[μ] f := coe_lp μ 2 f

end
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

lemma integrable (μ : Measure X) [IsFiniteMeasure μ] (f : Func X) : Integrable (f : X → ℂ) μ :=
  (memLp μ f 1).integrable le_rfl
end EuclideanFiveColor.BoundedMeasurable
end
end ParishMix
end

-- OAI.MeasureTheory.CompactFactors.RelativeProducts
section
namespace ParishMix

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal RealInnerProductSpace NNReal
namespace EuclideanFiveColor.BoundedMeasurable
section
variable {G X : Type*} [AddCommGroup G] [MeasurableSpace X]
  [AddAction G X] [MeasurableConstVAdd G X]

private def act (g : G) (f : Func X) : Func X := comp f (fun x => g +ᵥ x) (measurable_const_vadd g)
@[simp] lemma act_apply (g : G) (f : Func X) (x : X) : act g f x = f (g +ᵥ x) := rfl
lemma act_add (g h : G) (f : Func X) : act (g+h) f = act g (act h f) := by
  apply ext
  intro x
  simp only [act_apply, ← add_vadd, add_comm g h]
lemma act_mul (g : G) (f h : Func X) : act g (f*h) = act g f * act g h := rfl
lemma act_conj (g : G) (f : Func X) : act g (bmConj f) = bmConj (act g f) := rfl
lemma act_sub (g : G) (f h : Func X) : act g (f-h) = act g f - act g h := rfl

variable (μ : Measure X) [IsProbabilityMeasure μ] [VAddInvariantMeasure G X μ]
lemma l2_act (g : G) (f : Func X) :
    l2 μ (act g f) = Amenable.Koopman.action μ g (l2 μ f) := by
  apply Lp.ext
  exact (l2_ae μ (act g f)).trans ((MeasureTheory.measurePreserving_vadd g μ).quasiMeasurePreserving.ae_eq_comp
    (l2_ae μ f)).symm |>.trans (Amenable.Koopman.coe_action μ g (l2 μ f)).symm
end
end EuclideanFiveColor.BoundedMeasurable
end
end ParishMix
end

-- OAI.MeasureTheory.CompactFactors.RelativeCenters
section
namespace ParishMix

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace EuclideanFiveColor.KernelSupport

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

lemma compProd_map_base (ν : Measure Y) [SFinite ν] (κ : Kernel Y Z)
    [IsSFiniteKernel κ] (R : Y ≃ᵐ Y) :
    (ν.map R) ⊗ₘ (κ.comap R.symm R.symm.measurable) =
      (ν ⊗ₘ κ).map (Prod.map R id) := by
  ext s hs
  rw [Measure.compProd_apply hs,
    Measure.map_apply (R.measurable.prodMap measurable_id) hs,
    Measure.compProd_apply ((R.measurable.prodMap measurable_id) hs),
    lintegral_map (Kernel.measurable_kernel_prodMk_left hs) R.measurable]
  apply lintegral_congr
  intro y
  simp only [Kernel.comap_apply, R.symm_apply_apply]
  rfl

lemma condDistrib_comp_equiv [StandardBorelSpace Z] [Nonempty Z]
    (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → Z) (p : X → Y) (hf : Measurable f) (hp : Measurable p)
    (R : Y ≃ᵐ Y) :
    condDistrib f (R ∘ p) μ =ᵐ[μ.map (R ∘ p)]
      (condDistrib f p μ).comap R.symm R.symm.measurable := by
  apply condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    (R.measurable.comp hp) hf
  rw [← Measure.map_map R.measurable hp, compProd_map_base,
    compProd_map_condDistrib hf.aemeasurable,
    Measure.map_map (R.measurable.prodMap measurable_id) (hp.prodMk hf)]
  rfl

lemma condDistrib_equivariant [StandardBorelSpace Z] [Nonempty Z]
    (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → Z) (p : X → Y) (hf : Measurable f) (hp : Measurable p)
    (S : X ≃ᵐ X) (R : Y ≃ᵐ Y) (T : Z → Z) (hT : Measurable T)
    (hS : MeasurePreserving S μ μ)
    (hRp : p ∘ S =ᵐ[μ] R ∘ p) (hTf : f ∘ S =ᵐ[μ] T ∘ f) :
    ∀ᵐ y ∂μ.map p, condDistrib f p μ (R y) = (condDistrib f p μ y).map T := by
  have hR : (μ.map p).map R = μ.map p := by
    rw [Measure.map_map R.measurable hp, ← Measure.map_congr hRp,
      ← Measure.map_map hp S.measurable, hS.map_eq]
  have hRS : μ.map (p ∘ S) = μ.map p := by
    rw [← Measure.map_map hp S.measurable, hS.map_eq]
  have hm := condDistrib_map (X := p) (Y := f) (ν := μ) (f := S)
    (hp.aemeasurable) (hf.aemeasurable) S.measurable.aemeasurable
  simp only [hS.map_eq, hRS] at hm
  rw [condDistrib_congr hTf hRp] at hm
  have hc := condDistrib_comp_equiv μ (T ∘ f) p (hT.comp hf) hp R
  have hh : μ.map (R ∘ p) = μ.map p := by
    rw [← Measure.map_map R.measurable hp, hR]
  rw [hh] at hc
  have he := condDistrib_comp (mβ := ‹MeasurableSpace Y›) (μ := μ) p hf.aemeasurable hT
  have hcomp : ∀ᵐ y ∂μ.map p,
      condDistrib f p μ y = (condDistrib f p μ (R.symm y)).map T := by
    have he' : ∀ᵐ y ∂μ.map p,
        condDistrib (T ∘ f) p μ (R.symm y) =
          (condDistrib f p μ (R.symm y)).map T := by
      have hRinv : MeasurePreserving R.symm (μ.map p) (μ.map p) := by
        refine ⟨R.symm.measurable, ?_⟩
        calc
          (μ.map p).map R.symm = ((μ.map p).map R).map R.symm := by rw [hR]
          _ = μ.map p := R.map_symm_map
      exact hRinv.quasiMeasurePreserving.ae <| he.mono fun y hy => by
        simpa only [Kernel.map_apply _ hT] using hy
    filter_upwards [hm, hc, he'] with y h₁ h₂ h₃
    simpa only [Kernel.comap_apply] using h₁.trans (h₂.trans h₃)
  have hRpres : MeasurePreserving R (μ.map p) (μ.map p) := ⟨R.measurable, hR⟩
  have hfinal := hRpres.quasiMeasurePreserving.ae hcomp
  filter_upwards [hfinal] with y hy
  simpa only [R.symm_apply_apply] using hy

end EuclideanFiveColor.KernelSupport
end
end ParishMix
end

-- OAI.MeasureTheory.CompactFactors.ConditionalSelection
section
namespace ParishMix

noncomputable section
open MeasureTheory ProbabilityTheory
namespace EuclideanFiveColor.ConditionalFiber
variable {X W G V : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
  [MeasurableSpace W] [MeasurableSpace G] [StandardBorelSpace G] [Nonempty G]

omit [MeasurableSpace G] [StandardBorelSpace G] [Nonempty G] in
lemma comp_identity_fiber (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → W) (hp : Measurable p) :
    (condDistrib id p μ) ∘ₘ μ.map p = μ := by
  simpa using condDistrib_comp_map hp.aemeasurable (measurable_id.aemeasurable (μ := μ))

omit [MeasurableSpace G] [StandardBorelSpace G] [Nonempty G] in
lemma ae_fiber_of_ae (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → W) (hp : Measurable p) {P : X → Prop} (hP : ∀ᵐ x ∂μ, P x) :
    ∀ᵐ w ∂μ.map p, ∀ᵐ x ∂condDistrib id p μ w, P x := by
  exact Measure.ae_ae_of_ae_comp (by rwa [comp_identity_fiber μ p hp])

lemma map_identity_fiber (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → W) (hp : AEMeasurable p μ) (b : X → G) (hb : Measurable b) :
    ∀ᵐ w ∂μ.map p, (condDistrib id p μ w).map b = condDistrib b p μ w := by
  filter_upwards [condDistrib_comp p
    (measurable_id.aemeasurable (μ := μ)) hb] with w hw
  simpa [Kernel.map_apply _ hb] using hw.symm

omit [MeasurableSpace G] [StandardBorelSpace G] [Nonempty G] in
lemma ae_in_own_fiber [StandardBorelSpace W] [Nonempty W]
    (μ : Measure X) [IsFiniteMeasure μ] (p : X → W) (hp : Measurable p) :
    ∀ᵐ w ∂μ.map p, ∀ᵐ x ∂condDistrib id p μ w, p x = w := by
  filter_upwards [map_identity_fiber μ p hp.aemeasurable p hp,
    condDistrib_self (μ := μ) p] with w hw hs
  have he : (condDistrib id p μ w).map p = Measure.dirac w := by
    rw [hw, hs]; rfl
  apply ae_of_ae_map (p := fun z : W => z = w) hp.aemeasurable
  rw [he]
  simp

variable [NormedAddCommGroup V] [NormedSpace ℝ V]
omit [MeasurableSpace G] [StandardBorelSpace G] [Nonempty G] in
lemma integral_fiber (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → W) (hp : Measurable p) (f : X → V) (hf : Integrable f μ) :
    ∫ w, (∫ x, f x ∂condDistrib id p μ w) ∂μ.map p = ∫ x, f x ∂μ := by
  have hi : Integrable f ((condDistrib id p μ) ∘ₘ μ.map p) := by
    rwa [comp_identity_fiber μ p hp]
  rw [Measure.comp_eq_comp_const_apply] at hi
  have he := Kernel.integral_comp hi
  simpa [Kernel.const_apply, ← Measure.comp_eq_comp_const_apply,
    comp_identity_fiber μ p hp] using he.symm
end EuclideanFiveColor.ConditionalFiber
end
end ParishMix
end

-- OAI.Analysis.PlaneSpectrum.Ergodicity
section
namespace ParishMix
noncomputable section
open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction RealInnerProductSpace
namespace EuclideanFiveColor.Amenable.Mean
variable {G H : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
lemma vector_mem_closedConvexHull (M : Amenable.Mean G) (V : G →ᵇ H) :
    M.vector V ∈ closedConvexHull ℝ (Set.range V) := by
  by_contra hn
  obtain ⟨L,c,hL,hc⟩ := geometric_hahn_banach_closed_point convex_closedConvexHull isClosed_closedConvexHull hn
  have he : L (M.vector V) = M.map (L.compLeftContinuousBounded G V) := by
    rw [← M.vector_map]
    apply ext_inner_right ℝ
    intro x
    simp only [M.vector_pair, RCLike.inner_apply, conj_trivial]
    change M.map (pairing (L.compLeftContinuousBounded G V) x) = x * M.map (L.compLeftContinuousBounded G V)
    have hp : pairing (L.compLeftContinuousBounded G V) x = x • L.compLeftContinuousBounded G V := by
      ext g; simp [pairing_apply]
    rw [hp,map_smul]; rfl
  have hb : M.map (L.compLeftContinuousBounded G V) ≤ c := by
    rw [← M.map_const c]
    apply M.mono
    intro g
    exact le_of_lt (hL _ (subset_closedConvexHull (𝕜 := ℝ) (Set.mem_range_self g)))
  linarith
end EuclideanFiveColor.Amenable.Mean
namespace EuclideanFiveColor
private structure ConvexAverage (G : Type*) where
  n : ℕ
  pt : Fin n → G
  weight : Fin n → ℝ
  nonneg : ∀ i, 0 ≤ weight i
  total : ∑ i, weight i = 1
namespace ConvexAverage
variable {G H : Type*}
variable [NormedAddCommGroup H] [NormedSpace ℝ H]
private def apply (A : ConvexAverage G) (f : G → H) : H := ∑ i, A.weight i • f (A.pt i)
lemma norm_le (A : ConvexAverage G) (f : G → H) {C : ℝ} (hf : ∀ g, ‖f g‖ ≤ C) : ‖A.apply f‖ ≤ C := by
  calc
    _ ≤ ∑ i, ‖A.weight i • f (A.pt i)‖ := norm_sum_le _ _
    _ ≤ ∑ i, A.weight i * C := Finset.sum_le_sum fun i _ => by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (A.nonneg i)]
      exact mul_le_mul_of_nonneg_left (hf _) (A.nonneg i)
    _ = C := by rw [← Finset.sum_mul,A.total,one_mul]
lemma of_mem_convexHull {f : G → H} {v : H} (hv : v ∈ convexHull ℝ (Set.range f)) :
    ∃ A : ConvexAverage G, A.apply f = v := by
  classical
  obtain ⟨ι,hi,w,z,hw,ht,hz,he⟩ := mem_convexHull_iff_exists_fintype.mp hv
  choose g hg using hz
  let e := (Fintype.equivFin ι).symm
  refine ⟨⟨Fintype.card ι,g ∘ e,w ∘ e,fun i => hw _,?_⟩,?_⟩
  · simpa only [Function.comp_apply] using (e.sum_comp w).trans ht
  · dsimp [apply]
    simp only [hg]
    exact (e.sum_comp (fun i => w i • z i)).trans he
end ConvexAverage
namespace Amenable.Mean
variable {G H : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
lemma exists_finite_approx (M : Mean G) (V : G →ᵇ H) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : ConvexAverage G, ‖A.apply V - M.vector V‖ < ε := by
  have h := M.vector_mem_closedConvexHull V
  rw [closedConvexHull_eq_closure_convexHull] at h
  obtain ⟨v,hv,he⟩ := Metric.mem_closure_iff.mp h ε hε
  obtain ⟨A,rfl⟩ := ConvexAverage.of_mem_convexHull hv
  exact ⟨A,by simpa [dist_eq_norm,norm_sub_rev] using (show dist (M.vector V) (A.apply V) < ε from he)⟩
end Amenable.Mean
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction RealInnerProductSpace
namespace EuclideanFiveColor
namespace ConvexAverage
open BoundedMeasurable
variable {G X : Type*} [AddCommGroup G] [MeasurableSpace X]
  [AddAction G X] [MeasurableConstVAdd G X]
private def bm (A : ConvexAverage G) (f : Func X) : Func X := ∑ i, A.weight i • act (A.pt i) f
lemma bm_apply (A : ConvexAverage G) (f : Func X) (x : X) : A.bm f x = A.apply (fun g => f (g +ᵥ x)) := by
  simp [bm,apply,Func,Finset.sum_apply]
lemma bm_bound (A : ConvexAverage G) (f : Func X) (x : X) : ‖A.bm f x‖ ≤ bound f := by
  rw [bm_apply]; exact A.norm_le _ (fun g => norm_le_bound f _)
variable (μ : Measure X) [IsProbabilityMeasure μ] [VAddInvariantMeasure G X μ]
lemma l2_bm (A : ConvexAverage G) (f : Func X) :
    l2 μ (A.bm f) = A.apply (fun g => Amenable.Koopman.action μ g (l2 μ f)) := by
  simp only [bm,apply,map_sum,map_smul,l2_act]
end ConvexAverage
namespace InvariantSequence
open BoundedMeasurable
variable {G X : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace X] [AddAction G X] [MeasurableConstVAdd G X]
  (μ : Measure X) [IsProbabilityMeasure μ] [VAddInvariantMeasure G X μ]
  (M : Amenable.Mean G)
private def limit (f : Func X) : Lp ℂ 2 μ := M.vector (Amenable.Mean.orbit (Amenable.Koopman.action μ) (l2 μ f))
lemma limit_measurable (f : Func X) : Measurable (limit μ M f : X → ℂ) := (Lp.stronglyMeasurable _).measurable
lemma limit_fixed (f : Func X) (g : G) :
    (fun x => limit μ M f (g +ᵥ x)) =ᵐ[μ] (limit μ M f : X → ℂ) := by
  have h := M.vector_orbit_invariant (Amenable.Koopman.action μ) (Amenable.Koopman.action_add μ) (l2 μ f) g
  exact (Amenable.Koopman.coe_action μ g _).symm.trans (by rw [show Amenable.Koopman.action μ g (limit μ M f) = limit μ M f from h])
lemma exists_averages (f : Func X) : ∃ A : ℕ → ConvexAverage G,
    ∀ᵐ x ∂μ, Tendsto (fun n => A n |>.bm f x) atTop (𝓝 (limit μ M f x)) := by
  classical
  let V := Amenable.Mean.orbit (Amenable.Koopman.action (G := G) μ) (l2 μ f)
  choose A hA using (fun n : ℕ => M.exists_finite_approx V (show (0:ℝ) < 1/(n+1:ℝ) by positivity))
  have ht : Tendsto (fun n => l2 μ ((A n).bm f)) atTop (𝓝 (limit μ M f)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    apply squeeze_zero (fun n => norm_nonneg _) (fun n => le_of_lt ?_) (tendsto_one_div_add_atTop_nhds_zero_nat)
    simpa only [ConvexAverage.l2_bm, ConvexAverage.apply, V, limit, Amenable.Mean.orbit_apply] using hA n
  have hm := (tendstoInMeasure_of_tendsto_Lp ht).congr_left (fun n => l2_ae μ ((A n).bm f))
  obtain ⟨r,_,hr⟩ := hm.exists_seq_tendsto_ae
  exact ⟨fun n => A (r n),hr⟩
end InvariantSequence
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
namespace EuclideanFiveColor
open BoundedMeasurable
namespace ConvexAverage
variable {G X : Type*} [AddCommGroup G] [MeasurableSpace X]
  [AddAction G X] [MeasurableConstVAdd G X]
  (μ : Measure X) [IsProbabilityMeasure μ] [VAddInvariantMeasure G X μ]
lemma setIntegral_bm (A : ConvexAverage G) (f : Func X) (s : Set X) (hs : MeasurableSet s)
    (hinv : ∀ g : G, (fun x => g +ᵥ x) ⁻¹' s =ᵐ[μ] s) :
    ∫ x in s, A.bm f x ∂μ = ∫ x in s, f x ∂μ := by
  have hpres (g : G) : MeasurePreserving (fun x : X => g +ᵥ x) (μ.restrict s) (μ.restrict s) := by
    convert (measurePreserving_vadd g μ).restrict_preimage hs using 1
    exact (Measure.restrict_congr_set (hinv g)).symm
  simp only [bm_apply,apply]
  rw [integral_finsetSum _ (fun i _ => by
    have hh : Integrable (fun x => f (A.pt i +ᵥ x)) μ := integrable μ (act (A.pt i) f)
    exact hh.restrict.smul (A.weight i))]
  simp only [integral_smul]
  have he (i : Fin A.n) : ∫ x in s, f (A.pt i +ᵥ x) ∂μ = ∫ x in s, f x ∂μ :=
    (hpres _).integral_comp (MeasurableEquiv.vadd _).measurableEmbedding _
  simp only [he,← Finset.sum_smul,A.total,one_smul]
lemma setIntegral_of_limit (f : Func X) (A : ℕ → ConvexAverage G) (c : ℂ)
    (hc : ∀ᵐ x ∂μ, Tendsto (fun n => (A n).bm f x) atTop (𝓝 c))
    (s : Set X) (hs : MeasurableSet s)
    (hinv : ∀ g : G, (fun x => g +ᵥ x) ⁻¹' s =ᵐ[μ] s) :
    ∫ x in s, f x ∂μ = μ.real s • c := by
  have ht := tendsto_integral_of_dominated_convergence (fun _ : X => (bound f : ℝ))
    (fun n => (measurable ((A n).bm f)).aestronglyMeasurable)
    (integrable_const (bound f : ℝ) : Integrable (fun _ : X => (bound f : ℝ)) (μ.restrict s))
    (fun n => Eventually.of_forall (fun x => (A n).bm_bound f x)) (ae_restrict_of_ae hc)
  simp only [setIntegral_bm μ _ _ s hs hinv,integral_const,Measure.real,Measure.restrict_apply_univ] at ht
  exact tendsto_nhds_unique tendsto_const_nhds ht
end ConvexAverage
namespace ErgodicCriterion
variable (X : Type*) [MeasurableSpace X] [MeasurableSpace.CountablyGenerated X]
private def testSet (s : Finset ℕ) : Set X := ⋂ n ∈ s, MeasurableSpace.natGeneratingSequence X n
lemma measurable_testSet (s : Finset ℕ) : MeasurableSet (testSet X s) :=
  Finset.measurableSet_biInter s (fun n _ => MeasurableSpace.measurableSet_natGeneratingSequence n)
lemma testSet_union (s t : Finset ℕ) : testSet X (s ∪ t) = testSet X s ∩ testSet X t := by
  ext x; simp [testSet]; aesop
lemma pi_testSet : IsPiSystem (Set.range (testSet X)) := by
  rintro a ⟨s,rfl⟩ b ⟨t,rfl⟩ _
  exact ⟨s ∪ t,testSet_union X s t⟩
lemma generate_testSet : MeasurableSpace.generateFrom (Set.range (testSet X)) = ‹MeasurableSpace X› := by
  apply le_antisymm
  · apply MeasurableSpace.generateFrom_le
    rintro _ ⟨s,rfl⟩; exact measurable_testSet X s
  · conv_lhs => rw [← MeasurableSpace.generateFrom_natGeneratingSequence X]
    apply MeasurableSpace.generateFrom_mono
    rintro _ ⟨n,rfl⟩
    exact ⟨{n},by simp [testSet]⟩
private def test (s : Finset ℕ) : Func X :=
  ⟨(testSet X s).indicator (fun _ => 1),(measurable_const.indicator (measurable_testSet X s)),1,
    fun x => by by_cases hx : x ∈ testSet X s <;> simp [hx]⟩
lemma test_apply (s : Finset ℕ) (x : X) : test X s x = (testSet X s).indicator (fun _ => (1:ℂ)) x := rfl
variable {X}
variable {G : Type*} [AddCommGroup G] [AddAction G X] [MeasurableConstVAdd G X]
  (μ : Measure X) [IsProbabilityMeasure μ] [VAddInvariantMeasure G X μ]
lemma ergodic_of_test_limits (A : Finset ℕ → ℕ → ConvexAverage G) (c : Finset ℕ → ℂ)
    (hA : ∀ i, ∀ᵐ x ∂μ, Tendsto (fun n => (A i n).bm (test X i) x) atTop (𝓝 (c i))) :
    ErgodicVAdd G X μ := by
  refine ⟨fun {s} hs hinv => ?_⟩
  have hall (i : Finset ℕ) : ∫ x, test X i x ∂μ = c i := by
    simpa using ConvexAverage.setIntegral_of_limit μ (test X i) (A i) (c i) (hA i)
      Set.univ MeasurableSet.univ (fun _ => Eventually.of_forall (fun _ => rfl))
  have htest (i : Finset ℕ) : (μ.restrict s).real (testSet X i) = μ.real s * μ.real (testSet X i) := by
    have he := ConvexAverage.setIntegral_of_limit μ (test X i) (A i) (c i) (hA i) s hs hinv
    rw [← hall i] at he
    simp only [test_apply] at he
    rw [integral_indicator_const _ (measurable_testSet X i),
      integral_indicator_const _ (measurable_testSet X i)] at he
    simpa using congrArg Complex.re he
  have he : μ.restrict s = μ s • μ := by
    apply ext_of_generate_finite (Set.range (testSet X)) (generate_testSet X).symm (pi_testSet X)
    · rintro _ ⟨i,rfl⟩
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by simp; finiteness)).mp
      simpa [Measure.real,Measure.smul_apply,ENNReal.toReal_mul] using htest i
    · simp
  have hr : μ.real s = μ.real s * μ.real s := by
    have hh := congrArg (fun ν : Measure X => ν.real s) he
    simpa [Measure.real,Measure.restrict_apply hs,Set.inter_self] using hh
  have hz : μ.real s = 0 ∨ μ.real s = 1 := by
    have hh : μ.real s * (μ.real s-1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hh with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  rw [eventuallyConst_set]
  rcases hz with h | h
  · right
    rw [ae_iff]
    simpa using (show μ s = 0 by rw [← ofReal_measureReal]; simp [h])
  · left
    apply (ae_iff_measure_eq hs.nullMeasurableSet).mpr
    change μ s = μ Set.univ
    rw [← ofReal_measureReal (μ := μ) (s := s)]
    simp [h]
end ErgodicCriterion
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
namespace EuclideanFiveColor.InvariantDecomposition
open BoundedMeasurable ErgodicCriterion
variable {G X : Type*} [AddCommGroup G] [Countable G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
  [AddAction G X] [MeasurableConstVAdd G X]
  (μ : Measure X) [IsProbabilityMeasure μ] [VAddInvariantMeasure G X μ]
  (M : Amenable.Mean G)
private def code (x : X) : Finset ℕ → ℂ := fun i => InvariantSequence.limit μ M (test X i) x
omit [Countable G] [Nonempty X] in
lemma code_measurable : Measurable (code μ M) :=
  measurable_pi_iff.mpr (fun i => InvariantSequence.limit_measurable μ M (test X i))
omit [Countable G] [Nonempty X] in
lemma code_fixed (g : G) : (fun x => code μ M (g +ᵥ x)) =ᵐ[μ] code μ M := by
  have h := (ae_all_iff.mpr (fun i => InvariantSequence.limit_fixed μ M (test X i) g))
  exact h.mono fun x hx => funext hx
lemma fiber_invariant : ∀ᵐ y ∂μ.map (code μ M), VAddInvariantMeasure G X (condDistrib id (code μ M) μ y) := by
  have h (g : G) : ∀ᵐ y ∂μ.map (code μ M),
      (condDistrib id (code μ M) μ y).map (fun x => g +ᵥ x) = condDistrib id (code μ M) μ y := by
    have h := KernelSupport.condDistrib_equivariant μ id (code μ M) measurable_id (code_measurable μ M)
      (MeasurableEquiv.vadd g) (MeasurableEquiv.refl _) (fun x => g +ᵥ x)
      (measurable_const_vadd g) (measurePreserving_vadd g μ) (code_fixed μ M g)
      (Eventually.of_forall (fun _ => rfl))
    exact h.mono fun _ hy => hy.symm
  filter_upwards [ae_all_iff.mpr h] with y hy
  constructor
  intro g s hs
  rw [← Measure.map_apply (measurable_const_vadd _) hs,hy]
lemma fiber_ergodic : ∀ᵐ y ∂μ.map (code μ M), ErgodicVAdd G X (condDistrib id (code μ M) μ y) := by
  choose A hA using (fun i => InvariantSequence.exists_averages μ M (test X i))
  have hc := ConditionalFiber.ae_fiber_of_ae μ (code μ M) (code_measurable μ M) (ae_all_iff.mpr hA)
  filter_upwards [fiber_invariant μ M,hc, ConditionalFiber.ae_in_own_fiber μ (code μ M) (code_measurable μ M)] with y hy hlim hcode
  let := hy
  apply ergodic_of_test_limits (condDistrib id (code μ M) μ y) A y
  intro i
  filter_upwards [hlim,hcode] with x hx he
  have hh := hx i
  change Tendsto _ atTop (𝓝 (code μ M x i)) at hh
  rwa [he] at hh
end EuclideanFiveColor.InvariantDecomposition
end
end ParishMix
end
open MeasureTheory ProbabilityTheory Filter
open ParishMix ParishMix.EuclideanFiveColor
open scoped BoundedContinuousFunction

theorem OMA.solution : OMA.R_Erdos173_erdos_173_R1_H2_R1_H1_R1_H2_R1_H1_R1.H1 := by
  intro G X hG hc mX hX hnon hact hmeas μ hprob hinv s hs hnull f hf hbound hall
  let A := Additive G
  letI : Countable A := hc
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  letI : AddAction A X := {
    vadd a x := Additive.toMul a • x
    zero_vadd := one_smul G
    add_vadd a b x := mul_smul (Additive.toMul a) (Additive.toMul b) x }
  letI : MeasurableConstVAdd A X := ⟨fun a => measurable_const_smul (Additive.toMul a)⟩
  letI : VAddInvariantMeasure A X μ := ⟨fun a t _ => measure_preimage_smul μ (Additive.toMul a) t⟩
  let M : Amenable.Mean A := {
    map := PlaneFiveColor.InvariantMean.meanCLM
    map_const := PlaneFiveColor.InvariantMean.mean_const
    positive := PlaneFiveColor.InvariantMean.mean_nonneg
    invariant := PlaneFiveColor.InvariantMean.mean_shift }
  let q := InvariantDecomposition.code μ M
  have hq : Measurable q := InvariantDecomposition.code_measurable μ M
  have hc' : ∀ᵐ x ∂μ, x ∉ s := by simpa [ae_iff] using hnull
  have hs' := ConditionalFiber.ae_fiber_of_ae μ q hq hc'
  have hz : ∀ᵐ y ∂μ.map q, ∫ x, f x ∂condDistrib id q μ y = 0 := by
    filter_upwards [InvariantDecomposition.fiber_ergodic μ M,hs'] with y he h0
    let ρ := condDistrib id q μ y
    letI : ErgodicVAdd A X ρ := he
    letI : SMulInvariantMeasure G X ρ := ⟨fun g t _ => measure_preimage_vadd ρ (Additive.ofMul g) t⟩
    letI : ErgodicSMul G X ρ := ⟨fun hm hin =>
      ErgodicVAdd.aeconst_of_forall_preimage_vadd_ae_eq (G := A) hm (fun a => hin (Additive.toMul a))⟩
    exact hall ρ (by simpa [ae_iff,ρ] using h0)
  rw [← ConditionalFiber.integral_fiber μ q hq f
    (Integrable.of_bound hf.aestronglyMeasurable 1 (Eventually.of_forall hbound))]
  exact integral_eq_zero_of_ae hz

