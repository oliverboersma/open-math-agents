import OMAReductions.R_Erdos173_erdos_173_R1_H2_R1_H1_R1_H2_R1_H1_R1_H2_R1
-- PORT OF A PUBLIC PROOF, NOT A NEW RESULT.
-- Source: Jacob Parish (Plasma AI), github.com/plasma-ai/erdos-173 at commit 4a368a652753,
-- licensed Apache-2.0. Its OAI modules come from OpenAI, github.com/openai/math at commit
-- adc7f1241b42e322a6451854ab7e4b4c146bf78a, licensed Apache-2.0. Used here under the Apache
-- License 2.0 (the source files carry no separate copyright lines). Changes: the modules were
-- flattened into one file, unused parts dropped, lemma names adapted to the pinned Mathlib, and
-- a bridge to this reduction step added (agents moon-4 and opus-4 for marcusbuffett).

/-! Conditional Fourier vanishing on a relatively ergodic terminal factor.
The radial energy argument is adapted from Jacob Parish, plasma-ai/erdos-173
at 4a368a652753, and OpenAI, openai/math at adc7f1241b42e322a6451854ab7e4b4c146bf78a,
both under Apache-2.0. -/
-- OAI.MeasureTheory.CompactFactors.Amenability
section
namespace ParishFactor

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

private def squareNorm (V : G →ᵇ H) : G →ᵇ ℝ := normFn V * normFn V
omit [AddCommGroup G] [DiscreteTopology G] [InnerProductSpace ℝ H] [CompleteSpace H] in
@[simp] lemma squareNorm_apply (V : G →ᵇ H) (x : G) : squareNorm V x = ‖V x‖^2 := by
  simp [squareNorm, pow_two]

lemma jensen (V : G →ᵇ H) : ‖M.vector V‖^2 ≤ M.map (squareNorm V) := by
  let c := M.vector V
  have he : squareNorm (V - BoundedContinuousFunction.const G c) =
      squareNorm V - (2 : ℝ) • pairing V c + BoundedContinuousFunction.const G (‖c‖^2) := by
    ext x
    simp only [squareNorm_apply, BoundedContinuousFunction.sub_apply, BoundedContinuousFunction.const_apply,
      BoundedContinuousFunction.add_apply, BoundedContinuousFunction.smul_apply, pairing_apply, smul_eq_mul]
    rw [norm_sub_sq_real]
  have hp := M.positive (squareNorm (V - BoundedContinuousFunction.const G c)) (fun x => by
    rw [squareNorm_apply]; positivity)
  rw [he, map_add, map_sub, map_smul, M.map_const, ← M.vector_pair] at hp
  change 0 ≤ M.map (squareNorm V) - 2 * inner ℝ c c + ‖c‖^2 at hp
  rw [real_inner_self_eq_norm_sq] at hp
  dsimp [c] at hp
  linarith
end Mean
end EuclideanFiveColor.Amenable

namespace EuclideanFiveColor.Amenable.Mean

section
open scoped BoundedContinuousFunction
variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
variable (M : Mean G)
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

private def cross (V W : G →ᵇ H) : G →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => inner ℝ (V x) (W x))
    (V.continuous.inner W.continuous) (‖V‖ * ‖W‖) (fun x => by
      exact (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
        (mul_le_mul (V.norm_coe_le_norm x) (W.norm_coe_le_norm x) (norm_nonneg _) (norm_nonneg _)))

omit [AddCommGroup G] [DiscreteTopology G] [CompleteSpace H] in
@[simp] lemma cross_apply (V W : G →ᵇ H) (x : G) : cross V W x = inner ℝ (V x) (W x) := rfl

omit [AddCommGroup G] [DiscreteTopology G] [CompleteSpace H] in
lemma cross_comm (V W : G →ᵇ H) : cross V W = cross W V := by
  ext x; exact real_inner_comm _ _

omit [AddCommGroup G] [DiscreteTopology G] [CompleteSpace H] in
lemma squareNorm_add (V W : G →ᵇ H) :
    squareNorm (V+W) = squareNorm V + squareNorm W + (2 : ℝ) • cross V W := by
  ext x
  simp only [squareNorm_apply, BoundedContinuousFunction.add_apply,
    BoundedContinuousFunction.smul_apply, cross_apply, smul_eq_mul]
  rw [norm_add_sq_real]; ring

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
lemma squareNorm_shift (V : G →ᵇ H) (g : G) :
    M.map (squareNorm (shift G g V)) = M.map (squareNorm V) :=
  M.invariant g (squareNorm V)

private def correlation (V W : G →ᵇ H) : G →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun g => M.map (cross (shift G g V) W)) continuous_of_discreteTopology
    (‖V‖ * ‖W‖) (fun g => by
      rw [Real.norm_eq_abs, ← M.map_const (‖V‖ * ‖W‖)]
      apply M.abs_le
      intro x
      exact (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
        (mul_le_mul (V.norm_coe_le_norm (x+g)) (W.norm_coe_le_norm x) (norm_nonneg _) (norm_nonneg _)))

omit [CompleteSpace H] in
@[simp] lemma correlation_apply (V W : G →ᵇ H) (g : G) :
    M.correlation V W g = M.map (cross (shift G g V) W) := rfl

omit [CompleteSpace H] in
lemma correlation_add (V W Z : G →ᵇ H) :
    M.correlation V (W+Z) = M.correlation V W + M.correlation V Z := by
  ext g
  simp only [correlation_apply, BoundedContinuousFunction.add_apply]
  rw [← map_add]
  congr 1; ext x
  simp only [cross_apply, BoundedContinuousFunction.add_apply, inner_add_right]

omit [CompleteSpace H] in
lemma correlation_zero (V : G →ᵇ H) : M.correlation V 0 = 0 := by
  ext g
  change M.map (cross (shift G g V) (0 : G →ᵇ H)) = 0
  have he : cross (shift G g V) (0 : G →ᵇ H) = 0 := by ext; simp
  rw [he, map_zero]

omit [CompleteSpace H] in
lemma correlation_shift (V W : G →ᵇ H) (g : G) :
    M.correlation V (shift G g W) = shift G (-g) (M.correlation V W) := by
  ext h
  change M.map (cross (shift G h V) (shift G g W)) =
    M.map (cross (shift G (h+-g) V) W)
  rw [← M.invariant (-g) (cross (shift G h V) (shift G g W))]
  congr 1; ext x
  simp only [shift_apply, cross_apply]
  congr 2 <;> abel

theorem vector_eq_zero_of_correlation_nonpos (V : G →ᵇ H)
    (hc : M.map (M.correlation V V) ≤ 0) : M.vector V = 0 := by
  classical
  let C : ℝ := M.map (squareNorm V) + 2
  have hC : 0 < C := by
    have := M.positive (squareNorm V) (fun x => by rw [squareNorm_apply]; positivity)
    dsimp [C]; linarith
  have hW (n : ℕ) : ∃ W : G →ᵇ H, M.vector W = (n : ℝ) • M.vector V ∧
      M.map (M.correlation V W) ≤ 0 ∧ M.map (squareNorm W) ≤ (n : ℝ)*C := by
    induction n with
    | zero =>
      refine ⟨0, ?_, ?_, ?_⟩
      · have he : M.vector (0 : G →ᵇ H) = 0 := by
          apply ext_inner_right ℝ; intro v
          rw [M.vector_pair, inner_zero_left]
          have he : pairing (0 : G →ᵇ H) v = 0 := by ext; simp
          rw [he, map_zero]
        simpa using he
      · simp [M.correlation_zero]
      · have he : squareNorm (0 : G →ᵇ H) = 0 := by ext; simp
        simp [he]
    | succ n ih =>
      obtain ⟨W, hv, hwc, hwe⟩ := ih
      obtain ⟨g, hg⟩ := M.exists_lt (lt_of_le_of_lt hwc zero_lt_one)
      refine ⟨W+shift G g V, ?_, ?_, ?_⟩
      · rw [M.vector_add, M.vector_shift, hv]
        simp [Nat.cast_add, add_smul]
      · rw [M.correlation_add, map_add, M.correlation_shift, M.invariant]
        linarith
      · rw [squareNorm_add, map_add, map_add, map_smul, M.squareNorm_shift,
          cross_comm W _, ← M.correlation_apply V W g]
        have hn : ((n+1 : ℕ) : ℝ) = (n : ℝ)+1 := by simp
        rw [hn]
        dsimp [C] at *
        change M.map (squareNorm W) + M.map (squareNorm V) + 2 * M.correlation V W g ≤
          ((n : ℝ)+1) * (M.map (squareNorm V) + 2)
        change M.correlation V W g < 1 at hg
        nlinarith
  have hn (n : ℕ) (hp : 0 < n) : (n : ℝ) * ‖M.vector V‖^2 ≤ C := by
    obtain ⟨W, hw, _, he⟩ := hW n
    have hj := (M.jensen W).trans he
    rw [hw, norm_smul, Real.norm_natCast] at hj
    have hnr : 0 < (n : ℝ) := by exact_mod_cast hp
    apply (mul_le_mul_iff_right₀ hnr).mp
    nlinarith
  by_contra hv
  have hnorm : 0 < ‖M.vector V‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
  obtain ⟨n, hn'⟩ := exists_nat_gt (max 0 (C / ‖M.vector V‖^2))
  have hn0 : 0 < n := by exact_mod_cast (lt_of_le_of_lt (le_max_left _ _) hn')
  have hratio := lt_of_le_of_lt (le_max_right _ _) hn'
  have hbad := (div_lt_iff₀ hnorm).mp hratio
  have hgood := hn n hn0
  linarith

end

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

lemma vector_orbit_pair_fixed (U : G → H ≃ₗᵢ[ℝ] H) (v w : H)
    (hw : ∀ g, U g w = w) : inner ℝ (M.vector (orbit U v)) w = inner ℝ v w := by
  rw [M.vector_pair]
  have he : pairing (orbit U v) w = BoundedContinuousFunction.const G (inner ℝ v w) := by
    ext g
    change inner ℝ (U g v) w = inner ℝ v w
    calc
      inner ℝ (U g v) w = inner ℝ (U g v) (U g w) := by rw [hw g]
      _ = inner ℝ v w := (U g).inner_map_map v w
  rw [he, M.map_const]

theorem vector_orbit_eq_zero (U : G → H ≃ₗᵢ[ℝ] H)
    (hU : ∀ g h v, U (g+h) v = U g (U h v)) (v : H)
    (hv : ∀ w, (∀ g, U g w = w) → inner ℝ v w = 0) :
    M.vector (orbit U v) = 0 := by
  have hf := M.vector_orbit_invariant U hU v
  have hi := M.vector_orbit_pair_fixed U v (M.vector (orbit U v)) hf
  rw [hv _ hf] at hi
  exact inner_self_eq_zero.mp hi

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

variable {G X E : Type*} [AddCommGroup G] [MeasurableSpace X]
  [AddAction G X] [MeasurableConstVAdd G X] (μ : Measure X)
  [IsProbabilityMeasure μ] [ErgodicVAdd G X μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace.CountablySeparated E]

omit [IsProbabilityMeasure μ] [CompleteSpace E] in
lemma ae_eq_const_of_fixed (f : Lp E 2 μ)
    (hf : ∀ g : G, action μ g f = f) : ∃ c : E, f =ᵐ[μ] fun _ => c := by
  apply exists_eventuallyEq_const_of_forall_separating MeasurableSet
  intro A hA
  have := ErgodicVAdd.aeconst_of_forall_preimage_vadd_ae_eq (G := G)
    ((Lp.stronglyMeasurable f).measurable hA) (fun g => by
      have ha := coe_action μ g f
      rw [hf g] at ha
      exact ha.symm.mono (fun x hx =>
        propext (show f (g +ᵥ x) ∈ A ↔ f x ∈ A by change f (g +ᵥ x) = f x at hx; rw [hx])))
  exact Filter.eventuallyConst_set.mp this

lemma inner_fixed_zero (v : Lp E 2 μ)
    (hv : ∫ x, v x ∂μ = 0) (w : Lp E 2 μ) (hw : ∀ g : G, action μ g w = w) :
    inner ℝ v w = 0 := by
  obtain ⟨c, hc⟩ := ae_eq_const_of_fixed (G := G) μ w hw
  rw [L2.inner_def]
  calc
    (∫ x, inner ℝ (v x) (w x) ∂μ) = ∫ x, inner ℝ c (v x) ∂μ :=
      integral_congr_ae (hc.mono (fun x hx => by dsimp only at hx ⊢; rw [hx, real_inner_comm]))
    _ = inner ℝ c (∫ x, v x ∂μ) := integral_inner ((Lp.memLp v).integrable (by norm_num)) c
    _ = 0 := by rw [hv, inner_zero_right]

variable [TopologicalSpace G] [DiscreteTopology G]

theorem vector_orbit_zero (M : Mean G) (v : Lp E 2 μ)
    (hv : ∫ x, v x ∂μ = 0) : M.vector (H := Lp E 2 μ) (Mean.orbit (action (G := G) (E := E) μ) v) = 0 :=
by
  apply M.vector_orbit_eq_zero (H := Lp E 2 μ) (action (G := G) (E := E) μ)
    (action_add (G := G) (E := E) μ) v
  exact inner_fixed_zero (G := G) (E := E) μ v hv

end EuclideanFiveColor.Amenable.Koopman

end

end ParishFactor
end

-- OAI.Analysis.PlaneSpectrum.Carrier
section
noncomputable section

namespace ParishFactor.PlaneFiveColor.Spectral

private def TemplateProperty (E : Set ℂ) : Prop :=
  ∀ Q : Finset ℂ, (∀ q ∈ Q, q ∈ E ∧ ‖q‖ = 1) →
    ∃ S : Finset ℂ, (∀ s ∈ S, s ∈ E ∧ ‖s‖ = 1) ∧
      ∀ j : ℂ → ℂ, (∀ s ∈ S, j s ∈ Q) →
        (1 : ℂ) ∈ Submodule.span ℚ ((fun s => j s * s) '' (S : Set ℂ)) ∧
        Complex.I ∈ Submodule.span ℚ ((fun s => j s * s) '' (S : Set ℂ))

private class Carrier where
  
  E : IntermediateField ℚ ℂ
  
  F : IntermediateField ℚ ℝ
  
  countable : Countable E
  
  mem_iff : ∀ z : ℂ, z ∈ E ↔ z.re ∈ F ∧ z.im ∈ F
  
  algClosed : ∀ p : Polynomial ℂ, p ≠ 0 → (∀ n, p.coeff n ∈ E) →
    ∀ z : ℂ, p.eval z = 0 → z ∈ E
  
  template : TemplateProperty (E : Set ℂ)

namespace Carrier

variable [Carrier]

theorem re_mem {z : ℂ} (hz : z ∈ E) : z.re ∈ F := ((mem_iff z).mp hz).1

theorem im_mem {z : ℂ} (hz : z ∈ E) : z.im ∈ F := ((mem_iff z).mp hz).2

theorem ofReal_mem {t : ℝ} (ht : t ∈ F) : (t : ℂ) ∈ E :=
  (mem_iff _).mpr ⟨by simpa using ht, by simp⟩

theorem I_mem : Complex.I ∈ E :=
  (mem_iff _).mpr ⟨by simp, by simp⟩

theorem ratCast_mem (q : ℚ) : (q : ℝ) ∈ F := SubfieldClass.ratCast_mem F q

theorem mem_of_pow_mem {w : ℂ} {n : ℕ} (hn : n ≠ 0) (hw : w ^ n ∈ E) : w ∈ E := by
  classical
  have hdeg : (Polynomial.X ^ n - Polynomial.C (w ^ n)).natDegree = n :=
    Polynomial.natDegree_X_pow_sub_C
  apply algClosed (Polynomial.X ^ n - Polynomial.C (w ^ n))
  · intro h
    rw [h, Polynomial.natDegree_zero] at hdeg
    exact hn hdeg.symm
  · intro k
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C]
    split_ifs
    · exact E.sub_mem E.one_mem hw
    · simp
    · simpa using E.neg_mem hw
    · simp
  · simp

theorem sqrt_mem {t : ℝ} (ht : t ∈ F) : Real.sqrt t ∈ F := by
  by_cases h : 0 ≤ t
  · have hc : ((Real.sqrt t : ℝ) : ℂ) ∈ E := by
      apply mem_of_pow_mem (n := 2) (by norm_num)
      rw [← Complex.ofReal_pow, Real.sq_sqrt h]
      exact ofReal_mem ht
    simpa using re_mem hc
  · rw [Real.sqrt_eq_zero_of_nonpos (le_of_not_ge h)]
    exact F.zero_mem

theorem norm_mem {z : ℂ} (hz : z ∈ E) : ‖z‖ ∈ F := by
  have h : ‖z‖ = Real.sqrt (z.re * z.re + z.im * z.im) := by
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg z)]
  rw [h]
  exact sqrt_mem (F.add_mem (F.mul_mem (re_mem hz) (re_mem hz))
    (F.mul_mem (im_mem hz) (im_mem hz)))

theorem countable_F : Countable F := by
  have := countable
  let f : F → E := fun t => ⟨((t : ℝ) : ℂ), ofReal_mem t.property⟩
  apply Function.Injective.countable (f := f)
  intro s t h
  exact Subtype.ext (Complex.ofReal_injective (congrArg Subtype.val h))

end Carrier

private def fieldOf (x : ℝ) : IntermediateField ℚ ℂ :=
  (algebraicClosure (IntermediateField.adjoin ℚ {(x : ℂ)}) ℂ).restrictScalars ℚ

private def realFieldOf (x : ℝ) : IntermediateField ℚ ℝ :=
  (algebraicClosure (IntermediateField.adjoin ℚ {x}) ℝ).restrictScalars ℚ

end ParishFactor.PlaneFiveColor.Spectral
end

-- OAI.Analysis.PlaneSpectrum.Basic
section
namespace ParishFactor

noncomputable section
open scoped ComplexConjugate
namespace PlaneFiveColor.Spectral

variable [Carrier]

private abbrev E : IntermediateField ℚ ℂ := Carrier.E

private def K : Subgroup Circle where
  carrier := {u | (u : ℂ) ∈ E}
  one_mem' := by simp
  mul_mem' := by intro a b ha hb; simpa using E.mul_mem ha hb
  inv_mem' := by intro a ha; simpa using E.inv_mem ha

theorem K_pow_surjective (n : ℕ) (hn : n ≠ 0) :
    Function.Surjective (fun u : K => u ^ n) := by
  intro u
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (u.val : ℂ) (Nat.pos_of_ne_zero hn)
  have ha : z ∈ E := Carrier.mem_of_pow_mem hn (by
    rw [hz]; exact u.property)
  have hnrm : ‖z‖ = 1 := by
    have hpow : ‖z‖ ^ n = (1 : ℝ) ^ n := by
      simp only [← norm_pow, hz, Circle.norm_coe, one_pow]
    exact (pow_left_inj₀ (norm_nonneg z) zero_le_one hn).mp hpow
  refine ⟨⟨⟨z, mem_sphere_zero_iff_norm.mpr hnrm⟩, ha⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact hz

private instance K_rootable : RootableBy K ℕ := rootableByOfPowLeftSurj K ℕ (fun {n} hn => K_pow_surjective n hn)

omit [Carrier] in

theorem finite_image_trivial {G H : Type*} [Group G] [Group H] [Finite H]
    [RootableBy G ℕ] (f : G →* H) (g : G) : f g = 1 := by
  classical
  let := Fintype.ofFinite H
  obtain ⟨x, hx⟩ := RootableBy.surjective_pow G ℕ (Fintype.card_ne_zero : Fintype.card H ≠ 0) g
  rw [← hx, map_pow, pow_card_eq_one]

private def DiscreteE := Multiplicative E deriving CommGroup
private instance : TopologicalSpace DiscreteE := ⊥
private instance : DiscreteTopology DiscreteE := ⟨rfl⟩
private instance : IsTopologicalGroup DiscreteE := inferInstance
private abbrev D := PontryaginDual DiscreteE

example : CompactSpace D := inferInstance
example : CommGroup D := inferInstance

private instance E_countable : Countable E := Carrier.countable

private instance : Countable DiscreteE := inferInstanceAs (Countable E)

private instance : SecondCountableTopology D :=
  ContinuousMonoidHom.isClosedEmbedding_coe.isEmbedding.secondCountableTopology

private def embed (z : DiscreteE) : ℂ := ((Multiplicative.toAdd z : E) : ℂ)

@[simp] theorem embed_one : embed 1 = 0 := rfl
@[simp] theorem embed_mul (z w : DiscreteE) : embed (z * w) = embed z + embed w := rfl

private def j (ξ : ℂ) : D where
  toFun z := Circle.exp (inner ℝ ξ (embed z))
  map_one' := by simp
  map_mul' z w := by simp only [embed_mul, inner_add_right, Circle.exp_add]
  continuous_toFun := continuous_of_discreteTopology

@[simp] theorem j_apply (ξ : ℂ) (z : DiscreteE) :
    j ξ z = Circle.exp (inner ℝ ξ (embed z)) := rfl

@[simp] theorem j_zero : j 0 = 1 := by
  apply PontryaginDual.ext
  intro z
  simp

@[simp] theorem j_add (ξ η : ℂ) : j (ξ + η) = j ξ * j η := by
  apply PontryaginDual.ext
  intro z
  change Circle.exp (inner ℝ (ξ + η) (embed z)) =
    Circle.exp (inner ℝ ξ (embed z)) * Circle.exp (inner ℝ η (embed z))
  rw [inner_add_left, Circle.exp_add]

private def jHom : Multiplicative ℂ →* D where
  toFun ξ := j (Multiplicative.toAdd ξ)
  map_one' := j_zero
  map_mul' ξ η := j_add (Multiplicative.toAdd ξ) (Multiplicative.toAdd η)

private def C : Subgroup D := jHom.range

theorem continuous_j : Continuous j := by
  apply ContinuousMonoidHom.isClosedEmbedding_coe.isEmbedding.isInducing.continuous_iff.mpr
  apply continuous_pi
  intro z
  exact Circle.exp.continuous.comp (continuous_id.inner continuous_const)

omit [Carrier] in

theorem fixed_of_finite_orbit {G X : Type*} [Group G] [MulAction G X]
    [RootableBy G ℕ] (x : X) (hf : (MulAction.orbit G x).Finite) (g : G) :
    g • x = x := by
  let := hf.fintype
  have h := finite_image_trivial (MulAction.toPermHom G (MulAction.orbit G x)) g
  have h' := congrArg (fun p : Equiv.Perm (MulAction.orbit G x) =>
    (p ⟨x, MulAction.mem_orbit_self x⟩).val) h
  exact h'

private instance : MeasurableSpace D := borel D
private instance : BorelSpace D := ⟨rfl⟩

theorem measurableSet_C : MeasurableSet (C : Set D) := by
  change MeasurableSet (Set.range j)
  rw [← Set.image_univ, ← Metric.iUnion_closedBall_nat (0 : ℂ), Set.image_iUnion]
  exact MeasurableSet.iUnion fun n =>
    ((isCompact_closedBall (0 : ℂ) (n : ℝ)).image continuous_j).measurableSet

private def scaleE (a : E) : DiscreteE →ₜ* DiscreteE where
  toFun z := Multiplicative.ofAdd (a * Multiplicative.toAdd z)
  map_one' := by change Multiplicative.ofAdd (a * 0) = 1; simp
  map_mul' z w := by
    change Multiplicative.ofAdd (a * (_ + _)) = _
    rw [mul_add]
    rfl
  continuous_toFun := continuous_of_discreteTopology

private def scalar (a : E) (d : D) : D := d.comp (scaleE a)

@[simp] theorem scalar_apply (a : E) (d : D) (z : DiscreteE) :
    scalar a d z = d (Multiplicative.ofAdd (a * Multiplicative.toAdd z)) := rfl

@[simp] theorem scalar_one (d : D) : scalar 1 d = d := by
  apply PontryaginDual.ext
  intro z
  change d (Multiplicative.ofAdd (1 * Multiplicative.toAdd z)) = d z
  rw [one_mul]
  rfl

@[simp] theorem scalar_mul (a b : E) (d : D) :
    scalar a (scalar b d) = scalar (a * b) d := by
  apply PontryaginDual.ext
  intro z
  change d (Multiplicative.ofAdd (b * (a * Multiplicative.toAdd z))) =
    d (Multiplicative.ofAdd ((a * b) * Multiplicative.toAdd z))
  rw [mul_left_comm, ← mul_assoc]

@[simp] theorem scalar_add (a b : E) (d : D) :
    scalar (a + b) d = scalar a d * scalar b d := by
  apply PontryaginDual.ext
  intro z
  change d (Multiplicative.ofAdd ((a + b) * Multiplicative.toAdd z)) = _
  rw [add_mul]
  exact map_mul d _ _

@[simp] theorem scalar_j (a : E) (ξ : ℂ) :
    scalar a (j ξ) = j (conj (a : ℂ) * ξ) := by
  apply PontryaginDual.ext
  intro z
  change Circle.exp (inner ℝ ξ ((a : ℂ) * embed z)) = _
  rw [j_apply]
  congr 1
  simp only [Complex.inner, map_mul, starRingEnd_self_apply]
  congr 1
  ring

theorem scalar_mem_C (a : E) {d : D} (hd : d ∈ C) : scalar a d ∈ C := by
  obtain ⟨ξ, rfl⟩ := hd
  exact ⟨Multiplicative.ofAdd (conj (a : ℂ) * Multiplicative.toAdd ξ), scalar_j a _ |>.symm⟩

theorem scalar_mem_C_iff {a : E} (ha : a ≠ 0) (d : D) : scalar a d ∈ C ↔ d ∈ C := by
  constructor
  · intro h
    have h' := scalar_mem_C a⁻¹ h
    simpa [ha] using h'
  · exact scalar_mem_C a

omit [Carrier] in

theorem fixed_of_positive_fiber {G X Y : Type*} [Group G] [RootableBy G ℕ]
    [MulAction G X] [MulAction G Y] [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsFiniteMeasure μ]
    (π : X → Y) (heq : ∀ (g : G) (x : X), π (g • x) = g • π x)
    (hmeas : ∀ y, MeasurableSet (π ⁻¹' {y}))
    (hinv : ∀ g : G, MeasureTheory.MeasurePreserving (fun x : X => g • x) μ μ)
    (y : Y) (hpos : 0 < μ (π ⁻¹' {y})) (g : G) : g • y = y := by
  classical
  let A (z : MulAction.orbit G y) : Set X := π ⁻¹' {z.val}
  have hm (z : MulAction.orbit G y) : μ (A z) = μ (π ⁻¹' {y}) := by
    obtain ⟨g, hg⟩ := z.property
    have hs : (fun x : X => g • x) ⁻¹' A z = π ⁻¹' {y} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, A, heq, ← hg]
      constructor
      · intro h
        have h' := congrArg (fun z : Y => g⁻¹ • z) h
        simpa only [inv_smul_smul] using h'
      · exact congrArg (fun z : Y => g • z)
    rw [← (hinv g).measure_preimage ((hmeas z.val).nullMeasurableSet), hs]
  have hd : Pairwise (Function.onFun Disjoint A) := by
    intro z w hzw
    change Disjoint (A z) (A w)
    rw [Set.disjoint_left]
    intro x hz hw
    exact hzw (Subtype.ext (hz.symm.trans hw))
  have hf := MeasureTheory.Measure.finite_const_le_meas_of_disjoint_iUnion μ hpos (As := A)
    (fun z => hmeas z.val) hd (MeasureTheory.measure_ne_top μ _)
  have hu : {z : MulAction.orbit G y | μ (π ⁻¹' {y}) ≤ μ (A z)} = Set.univ := by
    ext z
    simp [hm]
  rw [hu] at hf
  let := Set.finite_univ_iff.mp hf
  exact fixed_of_finite_orbit y (Set.toFinite _) g

private def kCoeff (u : K) : E := ⟨(u.val : ℂ), u.property⟩

@[simp] theorem kCoeff_one : kCoeff 1 = 1 := rfl
@[simp] theorem kCoeff_mul (u v : K) : kCoeff (u * v) = kCoeff u * kCoeff v := rfl

private def scalarHom (a : E) : D →* D where
  toFun := scalar a
  map_one' := by apply PontryaginDual.ext; intro z; rfl
  map_mul' d e := by apply PontryaginDual.ext; intro z; rfl

private instance : MulAction K D where
  smul u d := scalar (kCoeff u) d
  one_smul d := scalar_one d
  mul_smul u v d := (scalar_mul (kCoeff u) (kCoeff v) d).symm

private abbrev Cosets := D ⧸ C

private def cosetScalar (u : K) : Cosets →* Cosets :=
  QuotientGroup.map C C (scalarHom (kCoeff u)) (fun _ h => scalar_mem_C _ h)

private instance : MulAction K Cosets where
  smul u q := cosetScalar u q
  one_smul q := by
    induction q using QuotientGroup.induction_on with
    | H d =>
      change QuotientGroup.mk (scalar 1 d) = QuotientGroup.mk d
      rw [scalar_one]
  mul_smul u v q := by
    induction q using QuotientGroup.induction_on with
    | H d =>
      change QuotientGroup.mk (scalar (kCoeff (u * v)) d) =
        QuotientGroup.mk (scalar (kCoeff u) (scalar (kCoeff v) d))
      rw [scalar_mul, kCoeff_mul]

@[simp] theorem quotient_equivariant (u : K) (d : D) :
    QuotientGroup.mk (u • d) = u • (QuotientGroup.mk d : Cosets) := rfl

theorem measurableSet_coset (q : Cosets) :
    MeasurableSet ((QuotientGroup.mk : D → Cosets) ⁻¹' {q}) := by
  induction q using QuotientGroup.induction_on with
  | H d =>
    have h : (QuotientGroup.mk : D → Cosets) ⁻¹' {QuotientGroup.mk d} =
        (fun x => x / d) ⁻¹' (C : Set D) := by
      ext x
      exact QuotientGroup.eq_iff_div_mem
    rw [h]
    exact measurableSet_C.preimage (continuous_id.div_const d).measurable

@[simp] theorem scalar_neg (a : E) (d : D) : scalar (-a) d = (scalar a d)⁻¹ := by
  apply PontryaginDual.ext
  intro z
  change d (Multiplicative.ofAdd ((-a) * Multiplicative.toAdd z)) =
    (d (Multiplicative.ofAdd (a * Multiplicative.toAdd z)))⁻¹
  rw [neg_mul]
  exact map_inv d _

@[simp] theorem scalar_sub (a b : E) (d : D) :
    scalar (a - b) d = scalar a d / scalar b d := by
  rw [sub_eq_add_neg, scalar_add, scalar_neg, div_eq_mul_inv]

private def minusOne : K := ⟨-1, by
  change (-1 : ℂ) ∈ E
  exact E.neg_mem E.one_mem⟩

@[simp] theorem kCoeff_minusOne : kCoeff minusOne = -1 := rfl

theorem coset_fixed_minusOne (q : Cosets) (h : minusOne • q = q) : q = 1 := by
  induction q using QuotientGroup.induction_on with
  | H d =>
    change QuotientGroup.mk (scalar (-1) d) = QuotientGroup.mk d at h
    have hm : scalar ((-1 : E) - 1) d ∈ C := by
      rw [scalar_sub, scalar_one]
      exact QuotientGroup.eq_iff_div_mem.mp h
    exact (QuotientGroup.eq_one_iff d).mpr ((scalar_mem_C_iff (by norm_num) d).mp hm)

private def IsWild (ν : MeasureTheory.Measure D) : Prop :=
  (∀ u : K, MeasureTheory.MeasurePreserving (fun d : D => u • d) ν ν) ∧
    ν (C : Set D) = 0

theorem wild_coset_null (ν : MeasureTheory.Measure D) [MeasureTheory.IsProbabilityMeasure ν]
    (hν : IsWild ν) (q : Cosets) :
    ν ((QuotientGroup.mk : D → Cosets) ⁻¹' {q}) = 0 := by
  by_contra hn
  have hp : 0 < ν ((QuotientGroup.mk : D → Cosets) ⁻¹' {q}) := pos_iff_ne_zero.mpr hn
  have hfix := fixed_of_positive_fiber ν (QuotientGroup.mk : D → Cosets)
    quotient_equivariant measurableSet_coset hν.1 q hp minusOne
  have hq := coset_fixed_minusOne q hfix
  subst q
  have hs : (QuotientGroup.mk : D → Cosets) ⁻¹' {1} = C := by
    ext d
    exact QuotientGroup.eq_one_iff d
  rw [hs, hν.2] at hn
  exact hn rfl

theorem wild_div_mem_null (ν : MeasureTheory.Measure D) [MeasureTheory.IsProbabilityMeasure ν]
    (hν : IsWild ν) (d : D) : ν {x | x / d ∈ C} = 0 := by
  convert wild_coset_null ν hν (QuotientGroup.mk d) using 1
  congr 1
  ext x
  exact (QuotientGroup.eq_iff_div_mem (N := C) (x := x) (y := d)).symm

theorem wild_independent_difference (ν : MeasureTheory.Measure D)
    [MeasureTheory.IsProbabilityMeasure ν] (hν : IsWild ν) :
    (ν.prod ν) {p : D × D | p.1 / p.2 ∈ C} = 0 := by
  have hm : MeasurableSet {p : D × D | p.1 / p.2 ∈ C} :=
    measurableSet_C.preimage (continuous_fst.div' continuous_snd).measurable
  rw [MeasureTheory.Measure.prod_apply_symm hm]
  have h (d : D) : ν ((fun x => (x, d)) ⁻¹' {p : D × D | p.1 / p.2 ∈ C}) = 0 :=
    wild_div_mem_null ν hν d
  simp_rw [h]
  simp

theorem continuous_scalar (a : E) : Continuous (scalar a) :=
  (scaleE a).continuous_comp_left

omit [Carrier] in

theorem frequency_zero_of_rational_tests (a : ℝ)
    (h : ∀ q : ℚ, Circle.exp (a * (q : ℝ)) = 1) : a = 0 := by
  have heq : (fun t : ℝ => Circle.exp (a * t)) = fun _ => 1 :=
    Rat.denseRange_cast.equalizer
      (Circle.exp.continuous.comp (continuous_const.mul continuous_id))
      continuous_const (funext h)
  have hpi : Circle.exp Real.pi ≠ 1 := by
    intro hone
    have ha := congrArg (fun u : Circle => (u : ℂ).arg) hone
    rw [Circle.arg_exp (by linarith [Real.pi_pos]) le_rfl] at ha
    simp at ha
  by_contra ha
  have ht := congrFun heq (Real.pi / a)
  have hmul : a * (Real.pi / a) = Real.pi := by field_simp
  rw [hmul] at ht
  exact hpi ht

private def imagUnit : E := ⟨Complex.I, Carrier.I_mem⟩

@[simp] theorem coe_imagUnit : (imagUnit : ℂ) = Complex.I := rfl

theorem j_eq_one_iff (ξ : ℂ) : j ξ = 1 ↔ ξ = 0 := by
  constructor
  · intro h
    have hre : ξ.re = 0 := frequency_zero_of_rational_tests ξ.re (by
      intro q
      have ht := congrArg (fun d : D => d (Multiplicative.ofAdd (q : E))) h
      change Circle.exp (inner ℝ ξ ((q : E) : ℂ)) = 1 at ht
      simpa [Complex.inner, Complex.mul_re, mul_comm] using ht)
    have him : ξ.im = 0 := frequency_zero_of_rational_tests ξ.im (by
      intro q
      have ht := congrArg (fun d : D => d (Multiplicative.ofAdd ((q : E) * imagUnit))) h
      change Circle.exp (inner ℝ ξ (((q : E) * imagUnit : E) : ℂ)) = 1 at ht
      simpa [Complex.inner, Complex.mul_re, mul_comm] using ht)
    exact Complex.ext hre him
  · rintro rfl
    exact j_zero

@[simp] theorem j_neg (ξ : ℂ) : j (-ξ) = (j ξ)⁻¹ :=
  map_inv jHom (Multiplicative.ofAdd ξ)

@[simp] theorem j_sub (ξ η : ℂ) : j (ξ - η) = j ξ / j η := by
  rw [sub_eq_add_neg, j_add, j_neg, div_eq_mul_inv]

theorem j_injective : Function.Injective j := by
  intro ξ η h
  apply sub_eq_zero.mp
  apply (j_eq_one_iff _).mp
  rw [j_sub, h, div_self']

theorem j_measurableEmbedding : MeasurableEmbedding j :=
  continuous_j.measurableEmbedding j_injective

omit [Carrier] in

theorem real_character (f : ℝ → Circle) (hf : Continuous f)
    (hmul : ∀ x y, f (x + y) = f x * f y) :
    ∃ a : ℝ, ∀ t, f t = Circle.exp (a * t) := by
  have hzero : f 0 = 1 := by
    have h := hmul 0 0
    exact (mul_left_cancel (show f 0 * 1 = f 0 * f 0 by simpa using h)).symm
  obtain ⟨F, ⟨hFzero, hFexp⟩, hFuniq⟩ :=
    Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts
      ⟨f, hf⟩ 0 0 (by simpa using hzero.symm)
  have hF (t : ℝ) : Circle.exp (F t) = f t := congrFun hFexp t
  have hadd (x y : ℝ) : F (x + y) = F x + F y := by
    let G : C(ℝ, ℝ) := ⟨fun t => F (t + y) - F y,
      (F.continuous.comp (continuous_id.add continuous_const)).sub continuous_const⟩
    have hG : G = F := hFuniq G ⟨by simp [G], by
      funext t
      change Circle.exp (F (t + y) - F y) = f t
      rw [Circle.exp_sub, hF, hF, hmul, mul_div_cancel_right]⟩
    have hh := congrArg (fun g : C(ℝ, ℝ) => g x) hG
    dsimp [G] at hh
    linarith
  let Fadd : ℝ →+ ℝ := { toFun := F, map_zero' := hFzero, map_add' := hadd }
  have hrat (q : ℚ) : F (q : ℝ) = (q : ℝ) * F 1 := by
    simpa [Fadd, Rat.smul_def] using map_rat_smul Fadd q (1 : ℝ)
  have hlinear : (fun t : ℝ => F t) = fun t => t * F 1 :=
    Rat.denseRange_cast.equalizer F.continuous
      (continuous_id.mul continuous_const) (funext hrat)
  refine ⟨F 1, fun t => ?_⟩
  rw [← hF, congrFun hlinear t, mul_comm]
private abbrev F : IntermediateField ℚ ℝ := Carrier.F

theorem dense_F : Dense (F : Set ℝ) :=
  Dense.mono (Set.range_subset_iff.mpr fun q : ℚ => Carrier.ratCast_mem q)
    (Rat.denseRange_cast : DenseRange ((↑) : ℚ → ℝ))

theorem algebraic_real_character (f : F → Circle) (hf : Continuous f)
    (hmul : ∀ x y, f (x + y) = f x * f y) :
    ∃ a : ℝ, ∀ t : F, f t = Circle.exp (a * (t : ℝ)) := by
  have hzero : f 0 = 1 := by
    have h := hmul 0 0
    exact (mul_left_cancel (show f 0 * 1 = f 0 * f 0 by simpa using h)).symm
  let fHom : Multiplicative F →* Circle := {
    toFun := fun t => f t.toAdd
    map_one' := hzero
    map_mul' := fun _ _ => hmul _ _ }
  have hu : UniformContinuous f :=
    uniformContinuous_monoidHom_of_continuous (f := fHom) hf
  let g := dense_F.extend f
  have hg : Continuous g := (dense_F.uniformContinuous_extend hu).continuous
  have hext (t : F) : g (t : ℝ) = f t := dense_F.extend_eq hf t
  have hgmul : ∀ x y : ℝ, g (x + y) = g x * g y := by
    intro x y
    refine dense_F.denseRange_val.induction_on₂
      (p := fun x y => g (x + y) = g x * g y) ?_ ?_ x y
    · exact isClosed_eq (hg.comp (continuous_fst.add continuous_snd))
        ((hg.comp continuous_fst).mul (hg.comp continuous_snd))
    · intro x y
      change g ((x + y : F) : ℝ) = g (x : ℝ) * g (y : ℝ)
      simp only [hext, hmul]
  obtain ⟨a, ha⟩ := real_character g hg hgmul
  exact ⟨a, fun t => (hext t).symm.trans (ha t)⟩

private def ofF : F →+* E where
  toFun t := ⟨(t : ℝ), Carrier.ofReal_mem t.property⟩
  map_zero' := by ext; simp
  map_one' := by ext; simp
  map_add' _ _ := by ext; simp
  map_mul' _ _ := by ext; simp

@[simp] theorem coe_ofF (t : F) : (ofF t : ℂ) = (t : ℝ) := rfl

private def DiscreteF := Multiplicative F deriving CommGroup
private instance : TopologicalSpace DiscreteF := ⊥
private instance : DiscreteTopology DiscreteF := ⟨rfl⟩
private instance : IsTopologicalGroup DiscreteF := inferInstance
private abbrev DF := PontryaginDual DiscreteF
private instance : MeasurableSpace DF := borel DF
private instance : BorelSpace DF := ⟨rfl⟩

private def embedF (t : DiscreteF) : ℝ := (Multiplicative.toAdd t : F)
@[simp] theorem embedF_one : embedF 1 = 0 := rfl
@[simp] theorem embedF_mul (t s : DiscreteF) : embedF (t * s) = embedF t + embedF s := rfl

private def jF (l : ℝ) : DF where
  toFun t := Circle.exp (l * embedF t)
  map_one' := by simp
  map_mul' t s := by simp only [embedF_mul, mul_add, Circle.exp_add]
  continuous_toFun := continuous_of_discreteTopology

@[simp] theorem jF_apply (l : ℝ) (t : DiscreteF) :
    jF l t = Circle.exp (l * (Multiplicative.toAdd t : F)) := rfl

private def CF : Set DF := Set.range jF

theorem continuous_jF : Continuous jF := by
  apply ContinuousMonoidHom.isClosedEmbedding_coe.isEmbedding.isInducing.continuous_iff.mpr
  apply continuous_pi
  intro z
  exact Circle.exp.continuous.comp (continuous_id.mul continuous_const)

theorem measurableSet_CF : MeasurableSet CF := by
  change MeasurableSet (Set.range jF)
  rw [← Set.image_univ, ← Metric.iUnion_closedBall_nat (0 : ℝ), Set.image_iUnion]
  exact MeasurableSet.iUnion fun n =>
    ((isCompact_closedBall (0 : ℝ) (n : ℝ)).image continuous_jF).measurableSet

private def lineHom (a : E) : DiscreteF →ₜ* DiscreteE where
  toFun t := Multiplicative.ofAdd (a * ofF (Multiplicative.toAdd t))
  map_one' := by change Multiplicative.ofAdd (a * ofF 0) = 1; simp
  map_mul' t s := by
    change Multiplicative.ofAdd (a * ofF (_ + _)) = _
    rw [map_add, mul_add]
    rfl
  continuous_toFun := continuous_of_discreteTopology

private def restrictLine (a : E) (d : D) : DF := d.comp (lineHom a)

theorem continuous_restrictLine (a : E) : Continuous (restrictLine a) :=
  (lineHom a).continuous_comp_left

private def L (a : E) : Set D := {d | Continuous (fun t : F =>
  d (Multiplicative.ofAdd (a * ofF t)))}

theorem mem_L_iff (a : E) (d : D) : d ∈ L a ↔ restrictLine a d ∈ CF := by
  constructor
  · intro hd
    obtain ⟨l, hl⟩ := algebraic_real_character
      (fun t : F => d (Multiplicative.ofAdd (a * ofF t))) hd (by
        intro t s
        rw [map_add, mul_add]
        exact map_mul d _ _)
    use l
    apply PontryaginDual.ext
    intro t
    exact (hl (Multiplicative.toAdd t)).symm
  · rintro ⟨l, hl⟩
    have h (t : F) : d (Multiplicative.ofAdd (a * ofF t)) = Circle.exp (l * (t : ℝ)) :=
      (congrArg (fun χ : DF => χ (Multiplicative.ofAdd t)) hl).symm
    change Continuous (fun t : F => d (Multiplicative.ofAdd (a * ofF t)))
    simp_rw [h]
    exact Circle.exp.continuous.comp (continuous_const.mul continuous_subtype_val)

theorem measurableSet_L (a : E) : MeasurableSet (L a) := by
  have h : L a = restrictLine a ⁻¹' CF := by ext d; exact mem_L_iff a d
  rw [h]
  exact measurableSet_CF.preimage (continuous_restrictLine a).measurable

private def reF (z : E) : F := ⟨(z : ℂ).re, Carrier.re_mem z.property⟩
private def imF (z : E) : F := ⟨(z : ℂ).im, Carrier.im_mem z.property⟩

@[simp] theorem coe_reF (z : E) : (reF z : ℝ) = (z : ℂ).re := rfl
@[simp] theorem coe_imF (z : E) : (imF z : ℝ) = (z : ℂ).im := rfl

theorem reF_add_imF (z : E) : ofF (reF z) + imagUnit * ofF (imF z) = z := by
  apply Subtype.ext
  change ((z : ℂ).re : ℂ) + Complex.I * (z : ℂ).im = (z : ℂ)
  rw [mul_comm, Complex.re_add_im]

theorem line_add {a b : E} {d : D} (ha : d ∈ L a) (hb : d ∈ L b) :
    d ∈ L (a + b) := by
  have h (t : F) : d (Multiplicative.ofAdd ((a + b) * ofF t)) =
      d (Multiplicative.ofAdd (a * ofF t)) * d (Multiplicative.ofAdd (b * ofF t)) := by
    rw [add_mul]; exact map_mul d _ _
  change Continuous _
  simp_rw [h]
  exact ha.mul hb

theorem line_mul_real {a : E} {d : D} (ha : d ∈ L a) (t : F) :
    d ∈ L (a * ofF t) := by
  change Continuous _ at ha ⊢
  convert ha.comp (continuous_const.mul continuous_id : Continuous (fun s : F => t * s)) using 1
  funext s
  simp only [Function.comp_apply, Pi.mul_apply, map_mul, mul_assoc]

theorem line_sub {a b : E} {d : D} (ha : d ∈ L a) (hb : d ∈ L b) :
    d ∈ L (a - b) := by
  have hn : d ∈ L (-b) := by simpa using line_mul_real hb (-1)
  simpa only [sub_eq_add_neg] using line_add ha hn

theorem orthogonal_lines {d : D} (h1 : d ∈ L 1) (hi : d ∈ L imagUnit) : d ∈ C := by
  obtain ⟨l, hl⟩ := (mem_L_iff 1 d).mp h1
  obtain ⟨e, he⟩ := (mem_L_iff imagUnit d).mp hi
  refine ⟨Multiplicative.ofAdd ((l : ℂ) + (e : ℂ) * Complex.I), ?_⟩
  apply PontryaginDual.ext
  intro z
  have hr (t : F) : d (Multiplicative.ofAdd (ofF t)) = Circle.exp (l * (t : ℝ)) := by
    have hh := congrArg (fun f : DF => f (Multiplicative.ofAdd t)) hl
    change Circle.exp (l * (t : ℝ)) = d (Multiplicative.ofAdd (1 * ofF t)) at hh
    simpa only [one_mul] using hh.symm
  have hi' (t : F) : d (Multiplicative.ofAdd (imagUnit * ofF t)) = Circle.exp (e * (t : ℝ)) :=
    (congrArg (fun f : DF => f (Multiplicative.ofAdd t)) he).symm
  change Circle.exp (inner ℝ ((l : ℂ) + (e : ℂ) * Complex.I) (embed z)) = d z
  have hd : d z = d (Multiplicative.ofAdd (ofF (reF (Multiplicative.toAdd z)))) *
      d (Multiplicative.ofAdd (imagUnit * ofF (imF (Multiplicative.toAdd z)))) := by
    calc
      d z = d (Multiplicative.ofAdd (ofF (reF (Multiplicative.toAdd z)) +
        imagUnit * ofF (imF (Multiplicative.toAdd z)))) :=
          congrArg d (congrArg Multiplicative.ofAdd (reF_add_imF (Multiplicative.toAdd z))).symm
      _ = _ := map_mul d _ _
  rw [hd, hr, hi', ← Circle.exp_add]
  congr 1
  simp [Complex.inner, embed, Complex.mul_re, Complex.mul_im, mul_comm]

theorem line_one_and_nonreal {d : D} (h1 : d ∈ L 1) {w : E}
    (hw : d ∈ L w) (hn : imF w ≠ 0) : d ∈ C := by
  have hr : d ∈ L (ofF (reF w)) := by simpa using line_mul_real h1 (reF w)
  have hsub := line_sub hw hr
  have him := line_mul_real hsub (imF w)⁻¹
  have heq : (w - ofF (reF w)) * ofF (imF w)⁻¹ = imagUnit := by
    have hz := reF_add_imF w
    have hzero : ofF (imF w) ≠ 0 := fun h => hn (ofF.injective (by simpa using h))
    rw [map_inv₀]
    calc
      (w - ofF (reF w)) * (ofF (imF w))⁻¹ =
        (imagUnit * ofF (imF w)) * (ofF (imF w))⁻¹ := by congr 1; linear_combination -hz
      _ = imagUnit := by rw [mul_assoc, mul_inv_cancel₀ hzero, mul_one]
  rw [heq] at him
  exact orthogonal_lines h1 him

@[simp] theorem scalar_line (a b : E) (d : D) : scalar a d ∈ L b ↔ d ∈ L (a * b) := by
  change Continuous (fun t : F => d (Multiplicative.ofAdd (a * (b * ofF t)))) ↔ _
  simp only [← mul_assoc]
  rfl

theorem independent_lines {a b : E} (ha : a ≠ 0) (hn : imF (a⁻¹ * b) ≠ 0)
    {d : D} (hda : d ∈ L a) (hdb : d ∈ L b) : d ∈ C := by
  apply (scalar_mem_C_iff ha d).mp
  apply line_one_and_nonreal (w := a⁻¹ * b) (by simpa using hda) _ hn
  simpa [← mul_assoc, ha] using hdb

@[simp] theorem kCoeff_inv (u : K) : kCoeff u⁻¹ = (kCoeff u)⁻¹ := by
  apply Subtype.ext
  change ((u.val)⁻¹ : Circle).val = (u.val : ℂ)⁻¹
  exact Circle.coe_inv u.val

@[simp] theorem kCoeff_ne_zero (u : K) : kCoeff u ≠ 0 := by
  intro h
  have hz : (u.val : ℂ) = 0 := congrArg (fun x : E => (x : ℂ)) h
  exact u.val.coe_ne_zero hz

theorem real_rotation_square (u : K) (hi : imF (kCoeff u) = 0) : u ^ 2 = 1 := by
  have him : (u.val : ℂ).im = 0 := congrArg (fun x : F => (x : ℝ)) hi
  have hn : (u.val : ℂ).re * (u.val : ℂ).re = 1 := by
    have hh := Complex.sq_norm (u.val : ℂ)
    rw [Circle.norm_coe] at hh
    simpa [Complex.normSq_apply, him] using hh.symm
  apply Subtype.ext
  apply Subtype.ext
  change (u.val : ℂ) ^ 2 = 1
  apply Complex.ext <;> simp [pow_two, Complex.mul_re, Complex.mul_im, him, hn]

theorem rotated_directions_independent {a : E} (ha : a ≠ 0) {u v : K}
    (huv : u ^ 2 ≠ v ^ 2) : imF ((a * kCoeff u)⁻¹ * (a * kCoeff v)) ≠ 0 := by
  intro h
  have heq : (a * kCoeff u)⁻¹ * (a * kCoeff v) = kCoeff (u⁻¹ * v) := by
    simp [mul_inv_rev, mul_assoc, ha]
  rw [heq] at h
  have hp := real_rotation_square (u⁻¹ * v) h
  apply huv
  have hp' : (u ^ 2)⁻¹ * (v ^ 2) = 1 := by simpa only [mul_pow, inv_pow] using hp
  exact inv_mul_eq_one.mp hp'

theorem wild_line_null (ν : MeasureTheory.Measure D) [MeasureTheory.IsProbabilityMeasure ν]
    (hν : IsWild ν) {a : E} (ha : a ≠ 0) : ν (L a) = 0 := by
  classical
  by_contra hn
  have hp : 0 < ν (L a) := pos_iff_ne_zero.mpr hn
  let root : K → K := fun u => Classical.choose (K_pow_surjective 2 (by norm_num) u)
  have hroot (u : K) : (root u) ^ 2 = u := Classical.choose_spec (K_pow_surjective 2 (by norm_num) u)
  let B (u : K) : Set D := L (a * kCoeff (root u)) \ (C : Set D)
  have hBm (u : K) : MeasurableSet (B u) := (measurableSet_L _).diff measurableSet_C
  have hpre (u : K) : (fun d : D => (root u) • d) ⁻¹' L a = L (a * kCoeff (root u)) := by
    ext d
    change scalar (kCoeff (root u)) d ∈ L a ↔ _
    rw [scalar_line, mul_comm]
  have hmass (u : K) : ν (B u) = ν (L a) := by
    change ν (L (a * kCoeff (root u)) \ (C : Set D)) = _
    rw [MeasureTheory.measure_sdiff_null hν.2, ← hpre]
    exact (hν.1 (root u)).measure_preimage (measurableSet_L a).nullMeasurableSet
  have hd : Pairwise (Function.onFun Disjoint B) := by
    intro u v huv
    change Disjoint (B u) (B v)
    rw [Set.disjoint_left]
    rintro d ⟨hdu, hdc⟩ ⟨hdv, _⟩
    apply hdc
    apply independent_lines (mul_ne_zero ha (kCoeff_ne_zero _))
      (rotated_directions_independent ha _) hdu hdv
    simpa only [hroot] using huv
  have hf := MeasureTheory.Measure.finite_const_le_meas_of_disjoint_iUnion ν hp (As := B)
    hBm hd (MeasureTheory.measure_ne_top ν _)
  have hu : {u : K | ν (L a) ≤ ν (B u)} = Set.univ := by ext u; simp [hmass]
  rw [hu] at hf
  let := Set.finite_univ_iff.mp hf
  have hm := finite_image_trivial (MonoidHom.id K) minusOne
  have hb := congrArg (fun u : K => (u.val : ℂ)) hm
  norm_num [minusOne] at hb

end PlaneFiveColor.Spectral

end

end ParishFactor
end

-- OAI.Analysis.PlaneSpectrum.Characters
section
namespace ParishFactor

noncomputable section
open scoped ComplexConjugate

noncomputable section
open scoped BigOperators
namespace PlaneFiveColor.ContinuousCharacters

theorem abs_arg_exp_le (t : ℝ) : |Complex.arg (Circle.exp t : ℂ)| ≤ |t| := by
  by_cases h : |t| ≤ Real.pi
  · rcases (abs_le.mp h) with ⟨hl, hr⟩
    rcases eq_or_lt_of_le hl with hh | hh
    · have ht : t = -Real.pi := hh.symm
      rw [ht, Circle.coe_exp]
      simp [Complex.arg_neg_one]
    · rw [Circle.arg_exp hh hr]
  · have ha : |Complex.arg (Circle.exp t : ℂ)| ≤ Real.pi :=
      abs_le.mpr ⟨(Complex.neg_pi_lt_arg _).le, Complex.arg_le_pi _⟩
    exact ha.trans (le_of_not_ge h)

theorem abs_arg_pow_le (z : Circle) (n : ℕ) :
    |Complex.arg (z ^ n : Circle)| ≤ n * |Complex.arg (z : ℂ)| := by
  have he : Circle.exp ((n : ℝ) * Complex.arg (z : ℂ)) = z ^ n := by
    rw [Circle.exp_natCast_mul, Circle.exp_arg]
  rw [← he]
  simpa [abs_mul] using abs_arg_exp_le ((n : ℝ) * Complex.arg (z : ℂ))

private def frequency (X : ℕ → Circle) (n : ℕ) : ℝ :=
  (2 : ℝ) ^ n * Complex.arg (X n : ℂ)

theorem frequency_abs_mono (X : ℕ → Circle) (hX : ∀ n, X n = X (n+1) ^ 2) :
    Monotone (fun n => |frequency X n|) := by
  apply monotone_nat_of_le_succ
  intro n
  simp only [frequency, abs_mul, abs_of_pos (pow_pos (by norm_num : (0 : ℝ) < 2) _)]
  rw [hX n]
  calc
    2 ^ n * |Complex.arg (X (n+1) ^ 2 : Circle)| ≤
        2 ^ n * (2 * |Complex.arg (X (n+1) : ℂ)|) := by
      gcongr
      simpa using abs_arg_pow_le (X (n+1)) 2
    _ = _ := by ring

@[simp] theorem exp_frequency_div (X : ℕ → Circle) (n : ℕ) :
    Circle.exp (frequency X n / (2 : ℝ)^n) = X n := by
  rw [frequency, mul_div_cancel_left₀ _ (pow_ne_zero _ (by norm_num)), Circle.exp_arg]

theorem frequency_exp_previous (X : ℕ → Circle) (hX : ∀ n, X n = X (n+1)^2)
    (n : ℕ) : Circle.exp (frequency X (n+1) / (2 : ℝ)^n) = X n := by
  rw [hX n, ← exp_frequency_div X (n+1), ← Circle.exp_natCast_mul]
  congr 1
  push_cast
  rw [pow_succ]
  field_simp

theorem frequency_stabilizes (X : ℕ → Circle) (hX : ∀ n, X n = X (n+1)^2)
    (R : ℝ) (hR : ∀ n, |frequency X n| ≤ R) :
    ∃ N, ∀ n, N ≤ n → frequency X n = frequency X N := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 ((Filter.tendsto_atTop.1
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)))
    (R / Real.pi + 1))
  have hp (n : ℕ) (hn : N ≤ n) : R < Real.pi * (2 : ℝ)^n := by
    have ht := hN n hn
    have hπ := Real.pi_pos
    have heq : R / Real.pi * Real.pi = R := div_mul_cancel₀ _ Real.pi_ne_zero
    nlinarith
  have hstep (n : ℕ) (hn : N ≤ n) : frequency X (n+1) = frequency X n := by
    have hb (m : ℕ) : |frequency X m / (2 : ℝ)^n| < Real.pi := by
      rw [abs_div, abs_of_pos (pow_pos (by norm_num : (0 : ℝ) < 2) _)]
      exact (div_lt_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) _)).mpr
        ((hR m).trans_lt (hp n hn))
    have he : frequency X (n+1) / (2 : ℝ)^n = frequency X n / (2 : ℝ)^n := by
      apply Circle.exp_injOn_Ico (a := -Real.pi) (b := Real.pi) (by linarith)
      · exact ⟨(abs_lt.mp (hb (n+1))).1.le, (abs_lt.mp (hb (n+1))).2⟩
      · exact ⟨(abs_lt.mp (hb n)).1.le, (abs_lt.mp (hb n)).2⟩
      · rw [frequency_exp_previous X hX, exp_frequency_div]
    exact (div_left_inj' (pow_ne_zero _ (by norm_num))).mp he
  refine ⟨N, fun n hn => ?_⟩
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih => exact (hstep n hn).trans ih

theorem chord_bound (z : Circle) :
    2 / Real.pi * |Complex.arg (z : ℂ)| ≤ ‖(z : ℂ) - 1‖ := by
  have ha : |Complex.arg (z : ℂ)| ≤ Real.pi :=
    abs_le.mpr ⟨(Complex.neg_pi_lt_arg _).le, Complex.arg_le_pi _⟩
  have hc := Real.cos_le_one_sub_mul_cos_sq ha
  have hr := Complex.norm_mul_cos_arg (z : ℂ)
  have hn := Complex.normSq_sub (z : ℂ) 1
  simp only [Circle.norm_coe, one_mul] at hr
  simp only [Complex.normSq_eq_norm_sq, Circle.norm_coe, map_one,
    mul_one, one_pow] at hn
  have hp := Real.pi_pos
  have hπ : (0 : ℝ) < Real.pi ^ 2 := sq_pos_of_pos hp
  have h0 : 0 ≤ 2 / Real.pi * |Complex.arg (z : ℂ)| := by positivity
  have hsq : (2 / Real.pi * |Complex.arg (z : ℂ)|)^2 ≤ ‖(z : ℂ)-1‖^2 := by
    rw [mul_pow, sq_abs, div_pow]
    rw [hr] at hc
    calc
      2 ^ 2 / Real.pi ^ 2 * (Complex.arg (z : ℂ))^2 =
          2 * (2 / Real.pi ^ 2 * (Complex.arg (z : ℂ))^2) := by ring
      _ ≤ 2 * (1 - (z : ℂ).re) := by linarith
      _ = _ := by linarith
  exact (sq_le_sq₀ h0 (norm_nonneg _)).mp hsq

theorem geom_sum_chord_bound (z : Circle) (m : ℕ) :
    ‖∑ k ∈ Finset.range m, (z : ℂ)^k‖ * ‖(z : ℂ)-1‖ ≤ 2 := by
  rw [← norm_mul, geom_sum_mul]
  calc
    ‖(z : ℂ)^m-1‖ ≤ ‖(z : ℂ)^m‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by simp only [norm_pow, Circle.norm_coe, norm_one, one_pow]; norm_num

theorem average_deviation (z : Circle) (m : ℕ)
    (h : 4 ≤ (m : ℝ) * ‖(z : ℂ)-1‖) :
    (m : ℝ) / 2 ≤ ∑ k ∈ Finset.range m, (1 - ((z : ℂ)^k).re) := by
  have hn : 0 < ‖(z : ℂ)-1‖ := by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    by_contra hh
    have hz := le_antisymm (le_of_not_gt hh) (norm_nonneg ((z : ℂ)-1))
    rw [hz, mul_zero] at h
    norm_num at h
  have hb := geom_sum_chord_bound z m
  have hr := (Complex.re_le_norm (∑ k ∈ Finset.range m, (z : ℂ)^k))
  have hs : (∑ k ∈ Finset.range m, (z : ℂ)^k).re ≤ (m : ℝ)/2 := by
    nlinarith [norm_nonneg (∑ k ∈ Finset.range m, (z : ℂ)^k)]
  simp only [Complex.re_sum] at hs
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  linarith

open MeasureTheory

private def deviation (z : Circle) (k : ℕ) : ℝ := 1 - ((z : ℂ)^k).re

lemma deviation_bound (z : Circle) (k : ℕ) : 0 ≤ deviation z k ∧ deviation z k ≤ 2 := by
  have h := Complex.abs_re_le_norm ((z : ℂ)^k)
  simp only [norm_pow, Circle.norm_coe, one_pow] at h
  have hh := abs_le.mp h
  constructor <;> dsimp [deviation] <;> linarith

lemma deviation_measurable {Ω : Type*} [MeasurableSpace Ω] (X : Ω → Circle)
    (hX : Measurable (fun x => (X x : ℂ))) (k : ℕ) : Measurable (fun x => deviation (X x) k) := by
  exact measurable_const.sub (Complex.measurable_re.comp (hX.pow_const k))

lemma deviation_integrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (X : Ω → Circle) (hX : Measurable (fun x => (X x : ℂ))) (k : ℕ) :
    Integrable (fun x => deviation (X x) k) μ := by
  apply Integrable.of_bound (deviation_measurable X hX k).aestronglyMeasurable 2
  filter_upwards [] with x
  simpa only [Real.norm_eq_abs, abs_of_nonneg (deviation_bound (X x) k).1] using
    (deviation_bound (X x) k).2

theorem frequency_tail_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (X : Ω → Circle) (hX : Measurable (fun x => (X x : ℂ)))
    (n m : ℕ) (hm : 0 < m) (R ε : ℝ)
    (hR : 4 ≤ (m : ℝ) * (2 / Real.pi) * (R / (2 : ℝ)^n))
    (hε : ∀ k ∈ Finset.range m, ∫ x, deviation (X x) k ∂μ ≤ ε) :
    μ.real {x | R ≤ |(2 : ℝ)^n * Complex.arg (X x : ℂ)|} ≤ 2 * ε := by
  let S : Ω → ℝ := fun x => ∑ k ∈ Finset.range m, deviation (X x) k
  have hS : Integrable S μ := by
    apply integrable_finsetSum
    intro k hk
    exact deviation_integrable μ X hX k
  have hSn : 0 ≤ᵐ[μ] S := Filter.Eventually.of_forall fun x =>
    Finset.sum_nonneg fun k hk => (deviation_bound (X x) k).1
  have hi : ∫ x, S x ∂μ ≤ (m : ℝ)*ε := by
    dsimp [S]
    rw [integral_finsetSum _ (fun k _ => deviation_integrable μ X hX k)]
    calc
      _ ≤ ∑ _k ∈ Finset.range m, ε := Finset.sum_le_sum hε
      _ = _ := by simp
  have ht : {x | R ≤ |(2 : ℝ)^n * Complex.arg (X x : ℂ)|} ⊆
      {x | (m : ℝ)/2 ≤ S x} := by
    intro x hx
    apply average_deviation (X x) m
    have hn : 0 < (2 : ℝ)^n := pow_pos (by norm_num) _
    have hf : R / (2 : ℝ)^n ≤ |Complex.arg (X x : ℂ)| := by
      apply (div_le_iff₀ hn).mpr
      simpa only [Set.mem_ofPred_eq, abs_mul, abs_of_pos hn, mul_comm] using hx
    calc
      4 ≤ (m : ℝ) * (2 / Real.pi) * (R / (2 : ℝ)^n) := hR
      _ ≤ (m : ℝ) * (2 / Real.pi) * |Complex.arg (X x : ℂ)| := by gcongr
      _ = (m : ℝ) * (2 / Real.pi * |Complex.arg (X x : ℂ)|) := by ring
      _ ≤ _ := by gcongr; exact chord_bound (X x)
  have hmark := mul_meas_ge_le_integral_of_nonneg hSn hS ((m : ℝ)/2)
  have hmono := measureReal_mono (μ := μ) ht
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  nlinarith

theorem dyadic_tail_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (X : ℕ → Ω → Circle) (hX : ∀ n, Measurable (fun x => (X n x : ℂ)))
    (δ ε : ℝ) (hδ : 0 < δ)
    (he : ∀ (n k : ℕ), (k : ℝ)/(2 : ℝ)^n < δ →
      ∫ x, deviation (X n x) k ∂μ ≤ ε) (n : ℕ) :
    μ.real {x | 2 * Real.pi / δ ≤ |frequency (fun j => X j x) n|} ≤ 2*ε := by
  let m := Nat.ceil (δ * (2 : ℝ)^n)
  have hn : 0 < (2 : ℝ)^n := pow_pos (by norm_num) _
  have hm : 0 < m := Nat.ceil_pos.mpr (mul_pos hδ hn)
  apply frequency_tail_bound μ (X n) (hX n) n m hm
  · calc
      4 = (δ * (2 : ℝ)^n) * (2 / Real.pi) * ((2 * Real.pi / δ)/(2 : ℝ)^n) := by
        field_simp
        ring
      _ ≤ _ := by
        gcongr
        exact Nat.le_ceil _
  · intro k hk
    apply he
    apply (div_lt_iff₀ hn).mpr
    simpa only [mul_comm] using Nat.lt_ceil.mp (Finset.mem_range.mp hk)

theorem dyadic_frequencies_ae_bounded {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (X : ℕ → Ω → Circle) (hX : ∀ n, Measurable (fun x => (X n x : ℂ)))
    (hcoh : ∀ x n, X n x = X (n+1) x ^ 2)
    (hcont : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ (n k : ℕ), (k : ℝ)/(2 : ℝ)^n < δ → ∫ x, deviation (X n x) k ∂μ ≤ ε) :
    ∀ᵐ x ∂μ, ∃ R : ℝ, ∀ n, |frequency (fun j => X j x) n| ≤ R := by
  rw [ae_iff]
  apply (measureReal_eq_zero_iff (μ := μ)).mp
  apply le_antisymm _ measureReal_nonneg
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨δ, hδ, he⟩ := hcont (ε/2) (by positivity)
  let R := 2 * Real.pi / δ
  let A : ℕ → Set Ω := fun n => {x | R ≤ |frequency (fun j => X j x) n|}
  have hmono : Monotone A := by
    intro n m hnm x hx
    exact hx.trans (frequency_abs_mono _ (hcoh x) hnm)
  have hA (n : ℕ) : μ (A n) ≤ ENNReal.ofReal ε := by
    apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ _) hε.le).mpr
    have ht := dyadic_tail_bound μ X hX δ (ε/2) hδ he n
    dsimp [A, R]
    simpa only [measureReal_def, mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using ht
  have hi : μ (⋃ n, A n) ≤ ENNReal.ofReal ε := by
    rw [hmono.measure_iUnion]
    exact iSup_le hA
  have hsub : {x | ¬ ∃ R : ℝ, ∀ n, |frequency (fun j => X j x) n| ≤ R} ⊆
      ⋃ n, A n := by
    intro x hx
    push Not at hx
    obtain ⟨n, hn⟩ := hx R
    exact Set.mem_iUnion.mpr ⟨n, hn.le⟩
  have hz := ENNReal.toReal_le_of_le_ofReal hε.le ((measure_mono hsub).trans hi)
  simpa only [zero_add, measureReal_def] using hz

theorem dyadic_frequencies_ae_stable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (X : ℕ → Ω → Circle) (hX : ∀ n, Measurable (fun x => (X n x : ℂ)))
    (hcoh : ∀ x n, X n x = X (n+1) x ^ 2)
    (hcont : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ (n k : ℕ), (k : ℝ)/(2 : ℝ)^n < δ → ∫ x, deviation (X n x) k ∂μ ≤ ε) :
    ∀ᵐ x ∂μ, ∃ N, ∀ n, N ≤ n →
      frequency (fun j => X j x) n = frequency (fun j => X j x) N := by
  filter_upwards [dyadic_frequencies_ae_bounded μ X hX hcoh hcont] with x hx
  obtain ⟨R, hR⟩ := hx
  exact frequency_stabilizes _ (hcoh x) R hR

theorem ordinary_of_stable (X : ℕ → Circle) (hX : ∀ n, X n = X (n+1)^2)
    (N : ℕ) (hN : ∀ n, N ≤ n → frequency X n = frequency X N) :
    ∀ n, X n = Circle.exp (frequency X N / (2 : ℝ)^n) := by
  intro n
  refine Nat.decreasingInduction (n := max N n)
    (motive := fun k _ => X k = Circle.exp (frequency X N / (2 : ℝ)^k))
    ?_ ?_ (Nat.le_max_right N n)
  · intro k hk ih
    rw [hX k, ih, ← Circle.exp_natCast_mul]
    congr 1
    push_cast
    rw [pow_succ]
    field_simp
  · rw [← exp_frequency_div X (max N n), hN _ (Nat.le_max_left N n)]

variable [Spectral.Carrier]

private abbrev F : IntermediateField ℚ ℝ := Spectral.Carrier.F

private def dyadicApprox (t : F) (n : ℕ) : F :=
  (Int.floor ((2 : ℝ)^n * (t : ℝ)) : F) / (2 : F)^n

lemma dyadicApprox_error (t : F) (n : ℕ) :
    |(dyadicApprox t n : ℝ) - (t : ℝ)| ≤ ((2 : ℝ)^n)⁻¹ := by
  have hpos : 0 < (2 : ℝ)^n := pow_pos (by norm_num) _
  have hl := Int.floor_le ((2 : ℝ)^n * (t : ℝ))
  have hr := Int.lt_floor_add_one ((2 : ℝ)^n * (t : ℝ))
  change |(Int.floor ((2 : ℝ)^n * (t : ℝ)) : ℝ)/(2 : ℝ)^n - (t : ℝ)| ≤ _
  calc
    _ = |(Int.floor ((2 : ℝ)^n * (t : ℝ)) : ℝ) - (2 : ℝ)^n * (t : ℝ)| /
        (2 : ℝ)^n := by
      have heq : (Int.floor ((2 : ℝ)^n * (t : ℝ)) : ℝ)/(2 : ℝ)^n - (t : ℝ) =
          ((Int.floor ((2 : ℝ)^n * (t : ℝ)) : ℝ) - (2 : ℝ)^n * (t : ℝ))/(2 : ℝ)^n := by
        field_simp
      rw [heq, abs_div, abs_of_pos hpos]
    _ ≤ 1 / (2 : ℝ)^n := by
      gcongr
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    _ = _ := one_div _

lemma dyadicApprox_tendsto (t : F) :
    Filter.Tendsto (fun n => (dyadicApprox t n : ℝ)) Filter.atTop (nhds (t : ℝ)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) (fun n => dyadicApprox_error t n)
  exact tendsto_inv_atTop_zero.comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))

omit [Spectral.Carrier] in

lemma circle_sq_dist (z w : Circle) :
    ‖(z : ℂ)-(w : ℂ)‖^2 = 2 * deviation (z/w) 1 := by
  have h := Complex.normSq_sub (z : ℂ) (w : ℂ)
  simp only [Complex.normSq_eq_norm_sq, Circle.norm_coe, one_pow] at h
  rw [← Circle.coe_inv_eq_conj, ← Circle.coe_mul, ← div_eq_mul_inv] at h
  simp only [Circle.coe_div] at h
  dsimp [deviation]
  rw [pow_one]
  linarith

variable {Ω : Type*} [MeasurableSpace Ω]

private def coeff (μ : Measure Ω) (χ : Ω → Multiplicative F →* Circle) (t : F) : ℝ :=
  ∫ x, deviation (χ x (Multiplicative.ofAdd t)) 1 ∂μ

@[simp] lemma coeff_zero (μ : Measure Ω) (χ : Ω → Multiplicative F →* Circle) :
    coeff μ χ 0 = 0 := by
  simp [coeff, deviation]

lemma coeff_small (μ : Measure Ω) (χ : Ω → Multiplicative F →* Circle)
    (hc : ContinuousAt (coeff μ χ) 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : F, |(t : ℝ)| < δ → coeff μ χ t ≤ ε := by
  obtain ⟨δ, hδ, hh⟩ := Metric.continuousAt_iff.mp hc ε hε
  refine ⟨δ, hδ, fun t ht => ?_⟩
  have hdist : dist t 0 < δ := by
    rw [dist_eq_norm, sub_zero]
    change ‖(t : ℝ)‖ < δ
    exact ht
  have hb := hh hdist
  rw [coeff_zero, dist_zero_right, Real.norm_eq_abs] at hb
  exact (le_abs_self _).trans hb.le

lemma char_nat_dyadic (χ : Multiplicative F →* Circle) (n k : ℕ) :
    χ (Multiplicative.ofAdd (((2 : F)^n)⁻¹)) ^ k =
      χ (Multiplicative.ofAdd ((k : F)/(2 : F)^n)) := by
  rw [← map_pow]
  congr 1
  change Multiplicative.ofAdd ((k : ℕ) • ((2 : F)^n)⁻¹) = _
  simp only [nsmul_eq_mul, div_eq_mul_inv]

lemma char_int_dyadic (χ : Multiplicative F →* Circle) (k : ℤ) (m : ℕ) :
    χ (Multiplicative.ofAdd (((2 : F)^m)⁻¹)) ^ k =
      χ (Multiplicative.ofAdd ((k : F)/(2 : F)^m)) := by
  rw [← map_zpow]
  congr 1
  change Multiplicative.ofAdd ((k : ℤ) • ((2 : F)^m)⁻¹) = _
  simp only [zsmul_eq_mul, div_eq_mul_inv]

lemma char_dyadic_coherent (χ : Multiplicative F →* Circle) (n : ℕ) :
    χ (Multiplicative.ofAdd (((2 : F)^n)⁻¹)) =
      χ (Multiplicative.ofAdd (((2 : F)^(n+1))⁻¹)) ^ 2 := by
  rw [char_nat_dyadic]
  congr 2
  norm_num only [Nat.cast_ofNat]
  rw [pow_succ]
  field_simp

theorem character_ae_dyadic (μ : Measure Ω) [IsFiniteMeasure μ]
    (χ : Ω → Multiplicative F →* Circle)
    (hχ : ∀ t : F, Measurable (fun x => (χ x (Multiplicative.ofAdd t) : ℂ)))
    (hc : ContinuousAt (coeff μ χ) 0) :
    ∀ᵐ x ∂μ, ∃ l : ℝ, ∀ n : ℕ,
      χ x (Multiplicative.ofAdd (((2 : F)^n)⁻¹)) = Circle.exp (l/(2 : ℝ)^n) := by
  let X : ℕ → Ω → Circle := fun n x => χ x (Multiplicative.ofAdd (((2 : F)^n)⁻¹))
  have hX : ∀ n, Measurable (fun x => (X n x : ℂ)) := fun n => hχ _
  have hcoh : ∀ x n, X n x = X (n+1) x ^ 2 := fun x n => char_dyadic_coherent _ _
  have hcont : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ (n k : ℕ), (k : ℝ)/(2 : ℝ)^n < δ → ∫ x, deviation (X n x) k ∂μ ≤ ε := by
    intro ε hε
    obtain ⟨δ, hδ, hh⟩ := coeff_small μ χ hc ε hε
    refine ⟨δ, hδ, fun n k hk => ?_⟩
    have he : (∫ x, deviation (X n x) k ∂μ) = coeff μ χ ((k : F)/(2 : F)^n) := by
      apply integral_congr_ae
      filter_upwards [] with x
      dsimp [coeff, deviation, X]
      rw [← Circle.coe_pow, char_nat_dyadic, pow_one]
    rw [he]
    apply hh
    change |(k : ℝ)/(2 : ℝ)^n| < δ
    simpa only [abs_of_nonneg
      (div_nonneg (Nat.cast_nonneg k) (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n))] using hk
  filter_upwards [dyadic_frequencies_ae_stable μ X hX hcoh hcont] with x hx
  obtain ⟨N, hN⟩ := hx
  exact ⟨frequency (fun n => X n x) N, ordinary_of_stable _ (hcoh x) N hN⟩

lemma char_sub (χ : Multiplicative F →* Circle) (t s : F) :
    χ (Multiplicative.ofAdd (t-s)) =
      χ (Multiplicative.ofAdd t) / χ (Multiplicative.ofAdd s) := by
  exact map_div χ (Multiplicative.ofAdd t) (Multiplicative.ofAdd s)

lemma char_sq_distance (χ : Multiplicative F →* Circle) (t s : F) :
    ‖(χ (Multiplicative.ofAdd t) : ℂ)-(χ (Multiplicative.ofAdd s) : ℂ)‖^2 =
      2 * deviation (χ (Multiplicative.ofAdd (t-s))) 1 := by
  rw [circle_sq_dist, char_sub]

lemma char_sq_integrable (μ : Measure Ω) [IsFiniteMeasure μ]
    (χ : Ω → Multiplicative F →* Circle)
    (hχ : ∀ t : F, Measurable (fun x => (χ x (Multiplicative.ofAdd t) : ℂ))) (t s : F) :
    Integrable (fun x => ‖(χ x (Multiplicative.ofAdd t) : ℂ)-
      (χ x (Multiplicative.ofAdd s) : ℂ)‖^2) μ := by
  simp_rw [char_sq_distance]
  exact (deviation_integrable μ _ (hχ (t-s)) 1).const_mul 2

lemma char_sq_integral (μ : Measure Ω) (χ : Ω → Multiplicative F →* Circle) (t s : F) :
    (∫ x, ‖(χ x (Multiplicative.ofAdd t) : ℂ)-
      (χ x (Multiplicative.ofAdd s) : ℂ)‖^2 ∂μ) = 2 * coeff μ χ (t-s) := by
  simp_rw [char_sq_distance]
  exact integral_const_mul _ _

lemma character_tendstoInMeasure (μ : Measure Ω) [IsFiniteMeasure μ]
    (χ : Ω → Multiplicative F →* Circle)
    (hχ : ∀ t : F, Measurable (fun x => (χ x (Multiplicative.ofAdd t) : ℂ)))
    (hc : ContinuousAt (coeff μ χ) 0) (r : ℕ → F) (t : F)
    (hr : Filter.Tendsto r Filter.atTop (nhds t)) :
    TendstoInMeasure μ (fun n x => (χ x (Multiplicative.ofAdd (r n)) : ℂ))
      Filter.atTop (fun x => (χ x (Multiplicative.ofAdd t) : ℂ)) := by
  apply tendstoInMeasure_iff_measureReal_norm.mpr
  intro ε hε
  have hpos : 0 < ε^2 := sq_pos_of_pos hε
  have hdiff : Filter.Tendsto (fun n => r n - t) Filter.atTop (nhds 0) := by
    simpa only [sub_self] using hr.sub (tendsto_const_nhds (x := t))
  have hint : Filter.Tendsto (fun n => (∫ x, ‖(χ x (Multiplicative.ofAdd (r n)) : ℂ)-
      (χ x (Multiplicative.ofAdd t) : ℂ)‖^2 ∂μ)/ε^2) Filter.atTop (nhds 0) := by
    simp_rw [char_sq_integral]
    simpa only [Function.comp_def, coeff_zero, mul_zero, zero_div] using
      ((hc.tendsto.comp hdiff).const_mul 2).div_const (ε^2)
  apply squeeze_zero (fun n => measureReal_nonneg) _ hint
  intro n
  apply (le_div_iff₀ hpos).mpr
  have hh := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun x => sq_nonneg
      ‖(χ x (Multiplicative.ofAdd (r n)) : ℂ)-(χ x (Multiplicative.ofAdd t) : ℂ)‖)
    (char_sq_integrable μ χ hχ (r n) t) (ε^2)
  have heq : {x | ε^2 ≤ ‖(χ x (Multiplicative.ofAdd (r n)) : ℂ)-
    (χ x (Multiplicative.ofAdd t) : ℂ)‖^2} =
      {x | ε ≤ ‖(χ x (Multiplicative.ofAdd (r n)) : ℂ)-
    (χ x (Multiplicative.ofAdd t) : ℂ)‖} := by
    ext x
    exact sq_le_sq₀ hε.le (norm_nonneg _)
  rw [heq] at hh
  simpa only [mul_comm] using hh

private instance F_countable : Countable F := Spectral.Carrier.countable_F

lemma char_dyadicApprox_eq (χ : Multiplicative F →* Circle) (l : ℝ)
    (hl : ∀ n : ℕ, χ (Multiplicative.ofAdd (((2 : F)^n)⁻¹)) =
      Circle.exp (l/(2 : ℝ)^n)) (t : F) (n : ℕ) :
    χ (Multiplicative.ofAdd (dyadicApprox t n)) = Circle.exp (l * (dyadicApprox t n : ℝ)) := by
  rw [dyadicApprox, ← char_int_dyadic, hl, ← Circle.exp_intCast_mul]
  congr 1
  change (Int.floor ((2 : ℝ)^n * (t : ℝ)) : ℝ) * (l/(2 : ℝ)^n) =
    l * ((Int.floor ((2 : ℝ)^n * (t : ℝ)) : ℝ)/(2 : ℝ)^n)
  ring

theorem character_ae_ordinary (μ : Measure Ω) [IsFiniteMeasure μ]
    (χ : Ω → Multiplicative F →* Circle)
    (hχ : ∀ t : F, Measurable (fun x => (χ x (Multiplicative.ofAdd t) : ℂ)))
    (hc : ContinuousAt (coeff μ χ) 0) :
    ∀ᵐ x ∂μ, ∃ l : ℝ, ∀ t : F,
      χ x (Multiplicative.ofAdd t) = Circle.exp (l*(t : ℝ)) := by
  have ha (t : F) : ∀ᵐ x ∂μ, ∀ l : ℝ,
      (∀ n : ℕ, χ x (Multiplicative.ofAdd (((2 : F)^n)⁻¹)) = Circle.exp (l/(2 : ℝ)^n)) →
      χ x (Multiplicative.ofAdd t) = Circle.exp (l*(t : ℝ)) := by
    have hr : Filter.Tendsto (dyadicApprox t) Filter.atTop (nhds t) :=
      tendsto_subtype_rng.mpr (dyadicApprox_tendsto t)
    obtain ⟨ns, hns, hae⟩ :=
      (character_tendstoInMeasure μ χ hχ hc (dyadicApprox t) t hr).exists_seq_tendsto_ae
    filter_upwards [hae] with x hx
    intro l hl
    have hlim : Filter.Tendsto
        (fun n => (Circle.exp (l*(dyadicApprox t (ns n) : ℝ)) : ℂ)) Filter.atTop
        (nhds (Circle.exp (l*(t : ℝ)) : ℂ)) := by
      apply (continuous_subtype_val.comp Circle.exp.continuous).continuousAt.tendsto.comp
      exact tendsto_const_nhds.mul ((dyadicApprox_tendsto t).comp hns.tendsto_atTop)
    have heq : (fun n => (χ x (Multiplicative.ofAdd (dyadicApprox t (ns n))) : ℂ)) =
        fun n => (Circle.exp (l*(dyadicApprox t (ns n) : ℝ)) : ℂ) := by
      funext n
      rw [char_dyadicApprox_eq _ l hl]
    rw [heq] at hx
    exact Subtype.ext (tendsto_nhds_unique hx hlim)
  have hall : ∀ᵐ x ∂μ, ∀ t : F, ∀ l : ℝ,
      (∀ n : ℕ, χ x (Multiplicative.ofAdd (((2 : F)^n)⁻¹)) = Circle.exp (l/(2 : ℝ)^n)) →
      χ x (Multiplicative.ofAdd t) = Circle.exp (l*(t : ℝ)) := ae_all_iff.mpr ha
  filter_upwards [character_ae_dyadic μ χ hχ hc, hall] with x hx hxall
  obtain ⟨l, hl⟩ := hx
  exact ⟨l, fun t => hxall t l hl⟩

end PlaneFiveColor.ContinuousCharacters

namespace PlaneFiveColor.Spectral
open MeasureTheory

variable [Carrier]

private def lineCharacter (a : E) (d : D) : Multiplicative F →* Circle :=
  (restrictLine a d).toMonoidHom

theorem lineCharacter_measurable (a : E) (t : F) :
    Measurable (fun d : D => (lineCharacter a d (Multiplicative.ofAdd t) : ℂ)) := by
  apply Continuous.measurable
  apply continuous_subtype_val.comp
  exact (continuous_apply (Multiplicative.ofAdd (a * ofF t))).comp
    ContinuousMonoidHom.isClosedEmbedding_coe.continuous

theorem wild_continuous_coefficient_zero (ν μ : Measure D) [IsProbabilityMeasure ν]
    [IsFiniteMeasure μ] (hν : IsWild ν) (hμ : μ ≪ ν) {a : E} (ha : a ≠ 0)
    (hc : ContinuousAt (ContinuousCharacters.coeff μ (lineCharacter a)) 0) : μ = 0 := by
  have hs := ContinuousCharacters.character_ae_ordinary μ (lineCharacter a)
    (lineCharacter_measurable a) hc
  have hL : ∀ᵐ d ∂μ, d ∈ L a := by
    filter_upwards [hs] with d hd
    obtain ⟨l, hl⟩ := hd
    apply (mem_L_iff a d).mpr
    refine ⟨l, ?_⟩
    apply PontryaginDual.ext
    intro t
    exact (hl (Multiplicative.toAdd t)).symm
  have hnull : μ (L a) = 0 := hμ (wild_line_null ν hν ha)
  have hnot : ∀ᵐ d ∂μ, d ∉ L a := (measure_eq_zero_iff_ae_notMem).mp hnull
  have hf : ∀ᵐ _d ∂μ, False := by
    filter_upwards [hL, hnot] with d hl hn
    exact hn hl
  apply Measure.measure_univ_eq_zero.mp
  simpa only [ae_iff, not_false_eq_true, Set.ofPred_true] using hf

end PlaneFiveColor.Spectral

end
end

end ParishFactor
end

-- OAI.Analysis.PlaneSpectrum.InvariantMean
section
namespace ParishFactor

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

private def realPart (f : G →ᵇ ℂ) : G →ᵇ ℝ := Complex.reCLM.compLeftContinuousBounded G f

private def imagPart (f : G →ᵇ ℂ) : G →ᵇ ℝ := Complex.imCLM.compLeftContinuousBounded G f

omit [AddCommGroup G] [DiscreteTopology G] in
@[simp] lemma realPart_apply (f : G →ᵇ ℂ) (x : G) : realPart f x = (f x).re := rfl
omit [AddCommGroup G] [DiscreteTopology G] in
@[simp] lemma imagPart_apply (f : G →ᵇ ℂ) (x : G) : imagPart f x = (f x).im := rfl

private def cmean (f : G →ᵇ ℂ) : ℂ := (mean (realPart f) : ℂ) + (mean (imagPart f) : ℂ) * Complex.I

lemma cmean_add (f h : G →ᵇ ℂ) : cmean (f+h) = cmean f + cmean h := by
  have hr : realPart (f+h) = realPart f + realPart h := by ext x; simp
  have hi : imagPart (f+h) = imagPart f + imagPart h := by ext x; simp
  simp only [cmean, hr, hi, mean_add, Complex.ofReal_add]
  ring

lemma cmean_smul (c : ℂ) (f : G →ᵇ ℂ) : cmean (c • f) = c * cmean f := by
  have hr : realPart (c • f) = c.re • realPart f - c.im • imagPart f := by
    ext x; simp [Complex.mul_re]
  have hi : imagPart (c • f) = c.re • imagPart f + c.im • realPart f := by
    ext x; simp [Complex.mul_im]
  have hs (f h : G →ᵇ ℝ) : mean (f-h) = mean f - mean h := meanCLM.map_sub f h
  apply Complex.ext <;>
    simp [cmean, hr, hi, hs, mean_smul, mean_add, Complex.mul_re, Complex.mul_im]

omit [AddCommGroup G] [DiscreteTopology G] in
lemma realPart_norm_le (f : G →ᵇ ℂ) : ‖realPart f‖ ≤ ‖f‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
  intro x
  exact (Complex.abs_re_le_norm (f x)).trans (f.norm_coe_le_norm x)

omit [AddCommGroup G] [DiscreteTopology G] in
lemma imagPart_norm_le (f : G →ᵇ ℂ) : ‖imagPart f‖ ≤ ‖f‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
  intro x
  exact (Complex.abs_im_le_norm (f x)).trans (f.norm_coe_le_norm x)

lemma cmean_norm_le (f : G →ᵇ ℂ) : ‖cmean f‖ ≤ 2 * ‖f‖ := by
  calc
    _ ≤ ‖(mean (realPart f) : ℂ)‖ + ‖(mean (imagPart f) : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = ‖mean (realPart f)‖ + ‖mean (imagPart f)‖ := by simp
    _ ≤ ‖f‖ + ‖f‖ := add_le_add ((mean_norm_le _).trans (realPart_norm_le f))
        ((mean_norm_le _).trans (imagPart_norm_le f))
    _ = _ := by ring

private def cmeanCLM : (G →ᵇ ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := cmean, map_add' := cmean_add, map_smul' := cmean_smul }
    2 (by intro f; exact cmean_norm_le f)

@[simp] lemma cmeanCLM_apply (f : G →ᵇ ℂ) : cmeanCLM f = cmean f := rfl

lemma cmean_const (z : ℂ) : cmean (BoundedContinuousFunction.const G z) = z := by
  have hr : realPart (BoundedContinuousFunction.const G z) = BoundedContinuousFunction.const G z.re := rfl
  have hi : imagPart (BoundedContinuousFunction.const G z) = BoundedContinuousFunction.const G z.im := rfl
  simp only [cmean, hr, hi, mean_const, Complex.re_add_im]

private def cshift (g : G) (f : G →ᵇ ℂ) : G →ᵇ ℂ :=
  f.compContinuous ⟨fun x => x + g, continuous_of_discreteTopology⟩

@[simp] lemma cshift_apply (g x : G) (f : G →ᵇ ℂ) : cshift g f x = f (x+g) := rfl

lemma cmean_shift (g : G) (f : G →ᵇ ℂ) : cmean (cshift g f) = cmean f := by
  have hr : realPart (cshift g f) = shift g (realPart f) := rfl
  have hi : imagPart (cshift g f) = shift g (imagPart f) := rfl
  simp only [cmean, hr, hi, mean_shift]

open MeasureTheory AddCircle

private def circlePull (ρ : G →+ UnitAddCircle) (f : C(UnitAddCircle, ℂ)) : G →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun x => f (ρ x)) ‖f‖ (fun _x => f.norm_coe_le_norm _)

@[simp] lemma circlePull_apply (ρ : G →+ UnitAddCircle) (f : C(UnitAddCircle, ℂ)) (x : G) :
    circlePull ρ f x = f (ρ x) := rfl

lemma circlePull_norm_le (ρ : G →+ UnitAddCircle) (f : C(UnitAddCircle, ℂ)) :
    ‖circlePull ρ f‖ ≤ ‖f‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
  exact fun x => f.norm_coe_le_norm _

private def circleMean (ρ : G →+ UnitAddCircle) : C(UnitAddCircle, ℂ) →L[ℂ] ℂ :=
  cmeanCLM.comp (LinearMap.mkContinuous
    ({ toFun := circlePull ρ
       map_add' := by intro f h; ext x; rfl
       map_smul' := by intro c f; ext x; rfl } : C(UnitAddCircle, ℂ) →ₗ[ℂ] (G →ᵇ ℂ))
    1 (by intro f; change ‖circlePull ρ f‖ ≤ 1 * ‖f‖
          simpa only [one_mul] using circlePull_norm_le ρ f))

@[simp] lemma circleMean_apply (ρ : G →+ UnitAddCircle) (f : C(UnitAddCircle, ℂ)) :
    circleMean ρ f = cmean (circlePull ρ f) := rfl

private def circleIntegral : C(UnitAddCircle, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ x, f x ∂haarAddCircle
      map_add' := by
        intro f h
        exact integral_add (BoundedContinuousFunction.mkOfCompact f |>.integrable _)
          (BoundedContinuousFunction.mkOfCompact h |>.integrable _)
      map_smul' := by intro c f; exact integral_smul c f }
    1 (by
      intro f
      change ‖∫ x, f x ∂haarAddCircle‖ ≤ 1 * ‖f‖
      simpa only [one_mul, BoundedContinuousFunction.norm_mkOfCompact, BoundedContinuousFunction.mkOfCompact_apply] using
        (BoundedContinuousFunction.mkOfCompact f).norm_integral_le_norm haarAddCircle)

@[simp] lemma circleIntegral_apply (f : C(UnitAddCircle, ℂ)) :
    circleIntegral f = ∫ x, f x ∂haarAddCircle := rfl

lemma circleMean_fourier_nonzero (ρ : G →+ UnitAddCircle) {n : ℤ} (hn : n ≠ 0)
    (hρ : ∃ g, ρ g = ((1 / 2 / n : ℝ) : UnitAddCircle)) : circleMean ρ (fourier n) = 0 := by
  obtain ⟨g, hg⟩ := hρ
  have he : cshift g (circlePull ρ (fourier n)) = -(circlePull ρ (fourier n)) := by
    ext x
    simp only [cshift_apply, circlePull_apply, map_add, hg, BoundedContinuousFunction.neg_apply]
    exact fourier_add_half_inv_index hn zero_lt_one _
  have hm := cmean_shift g (circlePull ρ (fourier n))
  rw [he] at hm
  have hn' : cmean (-circlePull ρ (fourier n)) = -cmean (circlePull ρ (fourier n)) :=
    cmeanCLM.map_neg _
  rw [hn'] at hm
  apply neg_eq_self.mp at hm
  exact hm

theorem circleMean_eq_integral (ρ : G →+ UnitAddCircle)
    (hρ : ∀ n : ℤ, n ≠ 0 → ∃ g, ρ g = ((1 / 2 / n : ℝ) : UnitAddCircle))
    (f : C(UnitAddCircle, ℂ)) : cmean (circlePull ρ f) = ∫ x, f x ∂haarAddCircle := by
  have he : circleMean ρ = circleIntegral := by
    apply ContinuousLinearMap.ext_on (s := Set.range (@fourier 1))
    · exact Submodule.dense_iff_topologicalClosure_eq_top.mpr span_fourier_closure_eq_top
    · rintro _ ⟨n, rfl⟩
      by_cases hn : n = 0
      · subst n
        have hp : circlePull ρ (fourier 0) = BoundedContinuousFunction.const G 1 := by
          ext x; simp
        simp only [circleMean_apply, hp, cmean_const, circleIntegral_apply]
        simp
      · rw [circleMean_fourier_nonzero ρ hn (hρ n hn), circleIntegral_apply]
        exact (integral_eq_zero_of_add_right_eq_neg
          (fourier_add_half_inv_index hn zero_lt_one)).symm
  exact DFunLike.congr_fun he f

section
variable [Spectral.Carrier]

private abbrev AF : IntermediateField ℚ ℝ := Spectral.Carrier.F

private def PeriodGroup := AF ⧸ AddSubgroup.zmultiples (1 : AF) deriving AddCommGroup
private instance : TopologicalSpace PeriodGroup := ⊥
private instance : DiscreteTopology PeriodGroup := ⟨rfl⟩

private def periodMk : AF →+ PeriodGroup := QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : AF))

private def fieldCircle : AF →+ UnitAddCircle :=
  (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))).comp
    AF.subtype.toAddMonoidHom

@[simp] lemma fieldCircle_apply (t : AF) : fieldCircle t = ((t : ℝ) : UnitAddCircle) := rfl

private def periodMap : PeriodGroup →+ UnitAddCircle :=
  QuotientAddGroup.lift (AddSubgroup.zmultiples (1 : AF)) fieldCircle (by
    rw [AddSubgroup.zmultiples_le]
    change (((1 : AF) : ℝ) : UnitAddCircle) = 0
    exact (QuotientAddGroup.eq_zero_iff (1 : ℝ)).mpr (AddSubgroup.mem_zmultiples 1))

@[simp] lemma periodMap_apply (t : AF) :
    periodMap (QuotientAddGroup.mk t) = ((t : ℝ) : UnitAddCircle) := rfl

lemma periodMap_half_period (n : ℤ) : ∃ g, periodMap g = ((1 / 2 / n : ℝ) : UnitAddCircle) := by
  refine ⟨QuotientAddGroup.mk (1 / 2 / n : AF), ?_⟩
  rw [periodMap_apply]
  congr 1

theorem ordinary_mean_integral (f : C(UnitAddCircle, ℂ)) :
    cmean (circlePull periodMap f) = ∫ x, f x ∂haarAddCircle :=
  circleMean_eq_integral periodMap (fun n _ => periodMap_half_period n) f
end

lemma mean_mono (f h : G →ᵇ ℝ) (hf : ∀ x, f x ≤ h x) : mean f ≤ mean h := by
  have hn : 0 ≤ mean (h-f) := mean_nonneg _ (fun x => sub_nonneg.mpr (hf x))
  have he : mean (h-f) = mean h - mean f := meanCLM.map_sub h f
  rw [he] at hn
  exact sub_nonneg.mp hn

lemma mean_abs_le (f h : G →ᵇ ℝ) (hf : ∀ x, |f x| ≤ h x) : |mean f| ≤ mean h := by
  apply abs_le.mpr
  constructor
  · have he : mean (-h) = -mean h := meanCLM.map_neg h
    rw [← he]
    exact mean_mono _ _ (fun x => (abs_le.mp (hf x)).1)
  · exact mean_mono _ _ (fun x => (abs_le.mp (hf x)).2)

section WeakMean
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

private def normFn (V : G →ᵇ H) : G →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun x => ‖V x‖) ‖V‖ (fun x => by simpa only [norm_norm] using V.norm_coe_le_norm x)

omit [AddCommGroup G] [InnerProductSpace ℝ H] [CompleteSpace H] in
@[simp] lemma normFn_apply (V : G →ᵇ H) (x : G) : normFn V x = ‖V x‖ := rfl

private def pairing (V : G →ᵇ H) (v : H) : G →ᵇ ℝ :=
  (innerSL ℝ v).compLeftContinuousBounded G V

omit [AddCommGroup G] [DiscreteTopology G] [CompleteSpace H] in
@[simp] lemma pairing_apply (V : G →ᵇ H) (v : H) (x : G) : pairing V v x = inner ℝ v (V x) := rfl

omit [CompleteSpace H] in
lemma pairing_mean_bound (V : G →ᵇ H) (v : H) :
    |mean (pairing V v)| ≤ ‖v‖ * mean (normFn V) := by
  rw [← mean_smul]
  apply mean_abs_le
  intro x
  exact norm_inner_le_norm (𝕜 := ℝ) v (V x)

private def pairingMean (V : G →ᵇ H) : H →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun v => mean (pairing V v)
      map_add' := by
        intro v w
        have he : pairing V (v+w) = pairing V v + pairing V w := by
          ext x; simp [inner_add_left]
        rw [he, mean_add]
      map_smul' := by
        intro c v
        have he : pairing V (c • v) = c • pairing V v := by
          ext x; simp [real_inner_smul_left]
        rw [he, mean_smul]
        rfl }
    (mean (normFn V)) (by
      intro v
      change |mean (pairing V v)| ≤ mean (normFn V) * ‖v‖
      simpa only [mul_comm] using pairing_mean_bound V v)

private def weakMean (V : G →ᵇ H) : H := (InnerProductSpace.toDual ℝ H).symm (pairingMean V)

lemma weakMean_pair (V : G →ᵇ H) (v : H) :
    inner ℝ (weakMean V) v = mean (pairing V v) :=
  InnerProductSpace.toDual_symm_apply

lemma weakMean_norm_bound (V : G →ᵇ H) : ‖weakMean V‖ ≤ mean (normFn V) := by
  rw [weakMean, LinearIsometryEquiv.norm_map]
  apply (pairingMean V).opNorm_le_bound (mean_nonneg _ (fun x => by rw [normFn_apply]; exact norm_nonneg _))
  intro v
  change |mean (pairing V v)| ≤ mean (normFn V) * ‖v‖
  simpa only [mul_comm] using pairing_mean_bound V v

lemma weakMean_add (V W : G →ᵇ H) : weakMean (V+W) = weakMean V + weakMean W := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_add_left, weakMean_pair, weakMean_pair, weakMean_pair]
  have he : pairing (V+W) v = pairing V v + pairing W v := by
    ext x; simp [inner_add_right]
  rw [he, mean_add]

lemma weakMean_sub (V W : G →ᵇ H) : weakMean (V-W) = weakMean V - weakMean W := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_sub_left, weakMean_pair, weakMean_pair, weakMean_pair]
  have he : pairing (V-W) v = pairing V v - pairing W v := by
    ext x; simp [inner_sub_right]
  rw [he]
  exact meanCLM.map_sub _ _

lemma weakMean_shift (V : G →ᵇ H) (g : G) :
    weakMean (V.compContinuous ⟨fun x => x+g, continuous_of_discreteTopology⟩) = weakMean V := by
  apply ext_inner_right ℝ
  intro v
  rw [weakMean_pair, weakMean_pair]
  exact mean_shift g (pairing V v)

lemma weakMean_map {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℝ J]
    [CompleteSpace J] (L : H →L[ℝ] J) (V : G →ᵇ H) :
    weakMean (L.compLeftContinuousBounded G V) = L (weakMean V) := by
  apply ext_inner_right ℝ
  intro v
  rw [weakMean_pair, ← L.adjoint_inner_right, weakMean_pair]
  congr 1
  ext x
  exact (L.adjoint_inner_left (V x) v).symm

end WeakMean

section Periodization
variable [Spectral.Carrier]
variable {H : Type*} [NormedAddCommGroup H]

private def periodSum (h : AF → H) (t : AF) : H := ∑' k : ℤ, h (t + k)

lemma periodSum_periodic (h : AF → H) : Function.Periodic (periodSum h) 1 := by
  intro t
  unfold periodSum
  calc
    (∑' k : ℤ, h (t+1+k)) = ∑' k : ℤ, h (t+((k+1 : ℤ) : AF)) := by
      apply tsum_congr
      intro k
      congr 1
      push_cast
      ring
    _ = ∑' k : ℤ, h (t+k) := (Equiv.addRight (1 : ℤ)).tsum_eq (fun k : ℤ => h (t+k))

private def periodLift (h : AF → H) : PeriodGroup → H := (periodSum_periodic h).lift

@[simp] lemma periodLift_mk (h : AF → H) (t : AF) :
    periodLift h (QuotientAddGroup.mk t) = periodSum h t := rfl

lemma period_term_zero {h : AF → H} {N : ℕ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0)
    {t : AF} (ht0 : 0 ≤ (t : ℝ)) (ht1 : (t : ℝ) < 1) (k : ℤ)
    (hk : k ∉ Finset.Icc (-(N : ℤ)-2) ((N : ℤ)+2)) : h (t+k) = 0 := by
  apply hs
  simp only [Finset.mem_Icc, not_and_or, not_le] at hk
  change (N : ℝ) < |(t : ℝ)+(k : ℝ)|
  rcases hk with hk | hk
  · have hk' : (k : ℝ) < -(N : ℝ)-2 := by exact_mod_cast hk
    rw [abs_of_neg] <;> linarith
  · have hk' : (N : ℝ)+2 < (k : ℝ) := by exact_mod_cast hk
    rw [abs_of_pos] <;> linarith

lemma periodSum_norm_le {h : AF → H} {N : ℕ} {B : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0)
    (hb : ∀ t, ‖h t‖ ≤ B) (t : AF) :
    ‖periodSum h t‖ ≤ (Finset.Icc (-(N : ℤ)-2) ((N : ℤ)+2)).card * B := by
  let t' : AF := t - (⌊(t : ℝ)⌋ : ℤ)
  have ht0 : 0 ≤ (t' : ℝ) := Int.fract_nonneg (t : ℝ)
  have ht1 : (t' : ℝ) < 1 := Int.fract_lt_one (t : ℝ)
  have he : periodSum h t = periodSum h t' := by
    simpa only [t', mul_one] using
      ((periodSum_periodic h).sub_int_mul_eq (x := t) ⌊(t : ℝ)⌋).symm
  rw [he, periodSum, tsum_eq_sum (period_term_zero hs ht0 ht1)]
  calc
    _ ≤ ∑ k ∈ Finset.Icc (-(N : ℤ)-2) ((N : ℤ)+2), ‖h (t'+k)‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.Icc (-(N : ℤ)-2) ((N : ℤ)+2), B :=
      Finset.sum_le_sum (fun k _ => hb (t'+k))
    _ = _ := by simp

private def periodBCF (h : AF → H) {N : ℕ} {B : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0)
    (hb : ∀ t, ‖h t‖ ≤ B) : PeriodGroup →ᵇ H :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (periodLift h)
    ((Finset.Icc (-(N : ℤ)-2) ((N : ℤ)+2)).card * B) (fun x => by
      induction x using QuotientAddGroup.induction_on with
      | H t => exact periodSum_norm_le hs hb t)

lemma period_summable {h : AF → H} {N : ℕ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0) (t : AF) :
    Summable (fun k : ℤ => h (t+k)) := by
  obtain ⟨M, hM⟩ := exists_nat_gt |(t : ℝ)|
  apply summable_of_hasFiniteSupport
  apply Set.Finite.subset (Finset.finite_toSet (Finset.Icc
    (-((N+M : ℕ) : ℤ)-2) (((N+M : ℕ) : ℤ)+2)))
  intro k hk
  by_contra hn
  apply hk
  apply hs
  simp only [Finset.mem_coe, Finset.mem_Icc, not_and_or, not_le] at hn
  change (N : ℝ) < |(t : ℝ)+(k : ℝ)|
  have hM1 := (abs_lt.mp hM).1
  have hM2 := (abs_lt.mp hM).2
  rcases hn with hn | hn
  · have hk' : (k : ℝ) < -((N : ℝ)+M)-2 := by exact_mod_cast hn
    rw [abs_of_neg] <;> linarith
  · have hk' : (N : ℝ)+M+2 < (k : ℝ) := by exact_mod_cast hn
    rw [abs_of_pos] <;> linarith

lemma periodSum_add {h j : AF → H} {N M : ℕ}
    (hh : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0)
    (hj : ∀ t : AF, (M : ℝ) < |(t : ℝ)| → j t = 0) (t : AF) :
    periodSum (h+j) t = periodSum h t + periodSum j t :=
  (period_summable hh t).tsum_add (period_summable hj t)

lemma periodSum_shift (h : AF → H) (s t : AF) :
    periodSum (fun x => h (x+s)) t = periodSum h (t+s) := by
  unfold periodSum
  congr 1
  ext k
  abel_nf

@[simp] lemma periodBCF_mk (h : AF → H) {N : ℕ} {B : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0)
    (hb : ∀ t, ‖h t‖ ≤ B) (t : AF) :
    periodBCF h hs hb (QuotientAddGroup.mk t) = periodSum h t := rfl

lemma periodBCF_norm_le (h : AF → H) {N : ℕ} {B : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0)
    (hb : ∀ t, ‖h t‖ ≤ B) (hB : 0 ≤ B) :
    ‖periodBCF h hs hb‖ ≤ (Finset.Icc (-(N : ℤ)-2) ((N : ℤ)+2)).card * B := by
  apply BoundedContinuousFunction.norm_le (mul_nonneg (Nat.cast_nonneg _) hB) |>.mpr
  intro x
  induction x using QuotientAddGroup.induction_on with
  | H t => exact periodSum_norm_le hs hb t

private def integralReal (h : AF → ℝ) {N : ℕ} {B : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0)
    (hb : ∀ t, ‖h t‖ ≤ B) : ℝ := mean (periodBCF h hs hb)

private def integralComplex (h : AF → ℂ) {N : ℕ} {B : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0)
    (hb : ∀ t, ‖h t‖ ≤ B) : ℂ := cmean (periodBCF h hs hb)

lemma integralReal_nonneg (h : AF → ℝ) {N : ℕ} {B : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0)
    (hb : ∀ t, ‖h t‖ ≤ B) (hp : ∀ t, 0 ≤ h t) : 0 ≤ integralReal h hs hb := by
  apply mean_nonneg
  intro x
  induction x using QuotientAddGroup.induction_on with
  | H t => exact tsum_nonneg (fun k => hp (t+k))

lemma integralReal_shift (h : AF → ℝ) (s : AF) {N M : ℕ} {B C : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0)
    (hb : ∀ t, ‖h t‖ ≤ B)
    (hss : ∀ t : AF, (M : ℝ) < |(t : ℝ)| → h (t+s) = 0)
    (hbs : ∀ t, ‖h (t+s)‖ ≤ C) :
    integralReal (fun t => h (t+s)) hss hbs = integralReal h hs hb := by
  have he : periodBCF (fun t => h (t+s)) hss hbs =
      shift (G := PeriodGroup) (periodMk s) (periodBCF h hs hb) := by
    ext x
    induction x using QuotientAddGroup.induction_on with
    | H t => exact periodSum_shift h s t
  unfold integralReal
  rw [he, mean_shift]

lemma integralReal_mono (h j : AF → ℝ) {N M : ℕ} {B C : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0)
    (hb : ∀ t, ‖h t‖ ≤ B)
    (js : ∀ t : AF, (M : ℝ) < |(t : ℝ)| → j t = 0)
    (jb : ∀ t, ‖j t‖ ≤ C) (hle : ∀ t, h t ≤ j t) :
    integralReal h hs hb ≤ integralReal j js jb := by
  apply mean_mono
  intro x
  induction x using QuotientAddGroup.induction_on with
  | H t => exact (period_summable hs t).tsum_le_tsum (fun k => hle (t+k)) (period_summable js t)

variable [InnerProductSpace ℝ H] [CompleteSpace H]

private def weakIntegral (h : AF → H) {N : ℕ} {B : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0)
    (hb : ∀ t, ‖h t‖ ≤ B) : H := weakMean (periodBCF h hs hb)

lemma weakIntegral_pair (h : AF → H) {N M : ℕ} {B C : ℝ} (v : H)
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0)
    (hb : ∀ t, ‖h t‖ ≤ B)
    (vs : ∀ t : AF, (M : ℝ) < |(t : ℝ)| → inner ℝ v (h t) = 0)
    (vb : ∀ t, ‖inner ℝ v (h t)‖ ≤ C) :
    inner ℝ (weakIntegral h hs hb) v = integralReal (fun t => inner ℝ v (h t)) vs vb := by
  rw [weakIntegral, weakMean_pair]
  unfold integralReal
  congr 1
  ext x
  induction x using QuotientAddGroup.induction_on with
  | H t => exact (innerSL ℝ v).map_tsum (period_summable hs t)

lemma weakIntegral_norm_bound (h : AF → H) {N : ℕ} {B : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0)
    (hb : ∀ t, ‖h t‖ ≤ B) (hB : 0 ≤ B) :
    ‖weakIntegral h hs hb‖ ≤ (Finset.Icc (-(N : ℤ)-2) ((N : ℤ)+2)).card * B := by
  apply (weakMean_norm_bound _).trans
  rw [← mean_const (G := PeriodGroup) ((Finset.Icc (-(N : ℤ)-2) ((N : ℤ)+2)).card * B)]
  apply mean_mono
  intro x
  exact ((periodBCF h hs hb).norm_coe_le_norm x).trans (periodBCF_norm_le h hs hb hB)

lemma weakIntegral_shift (h : AF → H) (s : AF) {N M : ℕ} {B C : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0)
    (hb : ∀ t, ‖h t‖ ≤ B)
    (hss : ∀ t : AF, (M : ℝ) < |(t : ℝ)| → h (t+s) = 0)
    (hbs : ∀ t, ‖h (t+s)‖ ≤ C) :
    weakIntegral (fun t => h (t+s)) hss hbs = weakIntegral h hs hb := by
  have he : periodBCF (fun t => h (t+s)) hss hbs =
      (periodBCF h hs hb).compContinuous
        (⟨fun x : PeriodGroup => x+periodMk s,
          continuous_of_discreteTopology⟩) := by
    ext x
    induction x using QuotientAddGroup.induction_on with
    | H t => exact periodSum_shift h s t
  unfold weakIntegral
  rw [he, weakMean_shift]

lemma weakIntegral_sub (h j : AF → H) {N M L : ℕ} {B C Q : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0)
    (hb : ∀ t, ‖h t‖ ≤ B)
    (js : ∀ t : AF, (M : ℝ) < |(t : ℝ)| → j t = 0)
    (jb : ∀ t, ‖j t‖ ≤ C)
    (ds : ∀ t : AF, (L : ℝ) < |(t : ℝ)| → h t-j t = 0)
    (db : ∀ t, ‖h t-j t‖ ≤ Q) :
    weakIntegral (fun t => h t-j t) ds db = weakIntegral h hs hb - weakIntegral j js jb := by
  have he : periodBCF (fun t => h t-j t) ds db = periodBCF h hs hb - periodBCF j js jb := by
    ext x
    induction x using QuotientAddGroup.induction_on with
    | H t => exact (period_summable hs t).tsum_sub (period_summable js t)
  unfold weakIntegral
  rw [he, weakMean_sub]

lemma weakIntegral_map {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℝ J]
    [CompleteSpace J] (L : H →L[ℝ] J) (h : AF → H) {N M : ℕ} {B C : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0)
    (hb : ∀ t, ‖h t‖ ≤ B)
    (js : ∀ t : AF, (M : ℝ) < |(t : ℝ)| → L (h t) = 0)
    (jb : ∀ t, ‖L (h t)‖ ≤ C) :
    weakIntegral (fun t => L (h t)) js jb = L (weakIntegral h hs hb) := by
  have he : periodBCF (fun t => L (h t)) js jb =
      L.compLeftContinuousBounded PeriodGroup (periodBCF h hs hb) := by
    ext x
    induction x using QuotientAddGroup.induction_on with
    | H t => exact (L.map_tsum (period_summable hs t)).symm
  unfold weakIntegral
  rw [he, weakMean_map]

end Periodization
section OrdinaryIntegral
variable [Spectral.Carrier]
open ContinuousMap TopologicalSpace

omit [Spectral.Carrier] in

lemma compact_local_summable (f : C(ℝ, ℂ)) {N : ℕ}
    (hs : ∀ t : ℝ, (N : ℝ) < |t| → f t = 0) (K : Compacts ℝ) :
    Summable (fun k : ℤ => ‖(f.comp (ContinuousMap.addRight k)).restrict K‖) := by
  obtain ⟨C, hC⟩ := K.isCompact.isBounded.exists_norm_le
  obtain ⟨M, hM⟩ := exists_nat_gt C
  apply summable_of_hasFiniteSupport
  apply Set.Finite.subset (Finset.finite_toSet (Finset.Icc
    (-((N+M : ℕ) : ℤ)-2) (((N+M : ℕ) : ℤ)+2)))
  intro k hk
  by_contra hn
  apply hk
  rw [norm_eq_zero]
  ext x
  apply hs
  change (N : ℝ) < |(x : ℝ)+(k : ℝ)|
  have hx : |(x : ℝ)| < (M : ℝ) := lt_of_le_of_lt (hC x x.property) hM
  simp only [Finset.mem_coe, Finset.mem_Icc, not_and_or, not_le] at hn
  have hx1 := (abs_lt.mp hx).1
  have hx2 := (abs_lt.mp hx).2
  rcases hn with hn | hn
  · have hk' : (k : ℝ) < -((N : ℝ)+M)-2 := by exact_mod_cast hn
    rw [abs_of_neg] <;> linarith
  · have hk' : (N : ℝ)+M+2 < (k : ℝ) := by exact_mod_cast hn
    rw [abs_of_pos] <;> linarith

private def ordinaryPeriod (f : C(ℝ, ℂ)) : C(UnitAddCircle, ℂ) :=
  ⟨(f.periodic_tsum_comp_add_zsmul 1).lift,
    continuous_coinduced_dom.mpr (map_continuous _)⟩

omit [Spectral.Carrier] in
lemma ordinaryPeriod_apply (f : C(ℝ, ℂ)) {N : ℕ}
    (hs : ∀ t : ℝ, (N : ℝ) < |t| → f t = 0) (t : ℝ) :
    ordinaryPeriod f (t : UnitAddCircle) = ∑' k : ℤ, f (t+k) := by
  change (∑' k : ℤ, f.comp (ContinuousMap.addRight (k • (1 : ℝ)) )) t = _
  have hf := ContinuousMap.summable_of_locally_summable_norm (compact_local_summable f hs)
  simpa only [zsmul_eq_mul, mul_one, ContinuousMap.comp_apply,
    ContinuousMap.addRight, ContinuousMap.coe_mk] using (ContinuousMap.tsum_apply hf t).symm

theorem integralComplex_ordinary (f : C(ℝ, ℂ)) {N : ℕ} {B : ℝ}
    (hs : ∀ t : ℝ, (N : ℝ) < |t| → f t = 0) (hb : ∀ t, ‖f t‖ ≤ B) :
    integralComplex (fun t : AF => f t) (fun t ht => hs t ht) (fun t => hb t) =
      ∫ t : ℝ, f t := by
  have he : periodBCF (fun t : AF => f t) (fun t ht => hs t ht) (fun t => hb t) =
      circlePull periodMap (ordinaryPeriod f) := by
    ext x
    induction x using QuotientAddGroup.induction_on with
    | H t =>
      change (∑' k : ℤ, f ((t+k : AF) : ℝ)) = ordinaryPeriod f ((t : ℝ) : UnitAddCircle)
      rw [ordinaryPeriod_apply f hs]
      rfl
  unfold integralComplex
  rw [he, ordinary_mean_integral]
  have hf := Real.fourierCoeff_tsum_comp_add (compact_local_summable f hs) 0
  simpa only [fourierCoeff, neg_zero, fourier_zero, one_smul, Int.cast_zero,
    Real.fourier_real_eq_integral_exp_smul, mul_zero, zero_mul, Complex.exp_zero, Complex.ofReal_zero,
    ordinaryPeriod, ContinuousMap.coe_mk] using hf

lemma integralComplex_re (h : AF → ℂ) {N M : ℕ} {B C : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0)
    (hb : ∀ t, ‖h t‖ ≤ B)
    (rs : ∀ t : AF, (M : ℝ) < |(t : ℝ)| → (h t).re = 0)
    (rb : ∀ t, ‖(h t).re‖ ≤ C) :
    (integralComplex h hs hb).re = integralReal (fun t => (h t).re) rs rb := by
  have he : realPart (periodBCF h hs hb) = periodBCF (fun t => (h t).re) rs rb := by
    ext x
    induction x using QuotientAddGroup.induction_on with
    | H t => exact Complex.reCLM.map_tsum (period_summable hs t)
  simp only [integralComplex, cmean, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, zero_mul, sub_self, add_zero, he, integralReal]

theorem integralReal_ordinary (f : C(ℝ, ℝ)) {N : ℕ} {B : ℝ}
    (hs : ∀ t : ℝ, (N : ℝ) < |t| → f t = 0) (hb : ∀ t, ‖f t‖ ≤ B) :
    integralReal (fun t : AF => f t) (fun t ht => hs t ht) (fun t => hb t) =
      ∫ t : ℝ, f t := by
  let fc : C(ℝ, ℂ) := ⟨fun t => (f t : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
  have hcs : ∀ t : ℝ, (N : ℝ) < |t| → fc t = 0 := by
    intro t ht
    simp [fc, hs t ht]
  have hcb : ∀ t, ‖fc t‖ ≤ B := by
    intro t
    simpa only [fc, coe_mk, Complex.norm_real] using hb t
  have hi := integralComplex_ordinary fc hcs hcb
  have hre := congrArg Complex.re hi
  rw [integralComplex_re _ _ _ (fun t ht => hs t ht) (fun t => hb t)] at hre
  change integralReal (fun t : AF => f t) _ _ = (∫ t : ℝ, (f t : ℂ)).re at hre
  rw [integral_complex_ofReal] at hre
  exact hre

end OrdinaryIntegral

section Smoothing
variable [Spectral.Carrier]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

lemma weakIntegral_congr (h j : AF → H) {N M : ℕ} {B C : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0)
    (hb : ∀ t, ‖h t‖ ≤ B)
    (js : ∀ t : AF, (M : ℝ) < |(t : ℝ)| → j t = 0)
    (jb : ∀ t, ‖j t‖ ≤ C) (he : ∀ t, h t = j t) :
    weakIntegral h hs hb = weakIntegral j js jb := by
  unfold weakIntegral
  congr 1
  ext x
  induction x using QuotientAddGroup.induction_on with
  | H t => exact tsum_congr (fun k => he (t+k))

lemma shifted_support {φ : AF → ℝ} {N : ℕ}
    (hφ : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → φ t = 0)
    (s : AF) (hs : |(s : ℝ)| ≤ 1) :
    ∀ t : AF, ((N+1 : ℕ) : ℝ) < |(t : ℝ)| → φ (t-s) = 0 := by
  intro t ht
  apply hφ
  have hi : |(t : ℝ)| ≤ |(t : ℝ)-(s : ℝ)| + |(s : ℝ)| := by
    simpa using abs_add_le ((t : ℝ)-(s : ℝ)) (s : ℝ)
  change (N : ℝ) < |(t : ℝ)-(s : ℝ)|
  push_cast at ht
  linarith

variable (U : AF → H ≃ₗᵢ[ℝ] H)

omit [CompleteSpace H] in
lemma smoothed_support (φ : AF → ℝ) {N : ℕ}
    (hφ : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → φ t = 0) (v : H) :
    ∀ t : AF, (N : ℝ) < |(t : ℝ)| → φ t • U t v = 0 := by
  intro t ht
  rw [hφ t ht, zero_smul]

omit [CompleteSpace H] in
lemma smoothed_bound (φ : AF → ℝ) {B : ℝ} (hb : ∀ t, |φ t| ≤ B) (v : H) :
    ∀ t, ‖φ t • U t v‖ ≤ B * ‖v‖ := by
  intro t
  rw [norm_smul, Real.norm_eq_abs, (U t).norm_map]
  exact mul_le_mul_of_nonneg_right (hb t) (norm_nonneg v)

private def smoothedVector (φ : AF → ℝ) {N : ℕ} {B : ℝ}
    (hφ : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → φ t = 0)
    (hb : ∀ t, |φ t| ≤ B) (v : H) : H :=
  weakIntegral (fun t => φ t • U t v) (smoothed_support U φ hφ v)
    (smoothed_bound U φ hb v)

theorem smoothed_translation_bound
    (hu : ∀ s t v, U s (U t v) = U (s+t) v)
    (φ : AF → ℝ) {N : ℕ} {B C : ℝ}
    (hφ : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → φ t = 0)
    (hb : ∀ t, |φ t| ≤ B) (v : H) (s : AF) (hs : |(s : ℝ)| ≤ 1)
    (hC : 0 ≤ C) (hd : ∀ t, |φ (t-s)-φ t| ≤ C) :
    ‖U s (smoothedVector U φ hφ hb v) - smoothedVector U φ hφ hb v‖ ≤
      (Finset.Icc (-((N+1 : ℕ) : ℤ)-2) (((N+1 : ℕ) : ℤ)+2)).card * (C * ‖v‖) := by
  let h : AF → H := fun t => φ t • U t v
  let j : AF → H := fun t => φ (t-s) • U t v
  have hh := smoothed_support U φ hφ v
  have bh := smoothed_bound U φ hb v
  have hj := smoothed_support U (fun t => φ (t-s)) (shifted_support hφ s hs) v
  have bj := smoothed_bound U (fun t => φ (t-s)) (fun t => hb (t-s)) v
  have dh : ∀ t : AF, ((N+1 : ℕ) : ℝ) < |(t : ℝ)| → j t-h t = 0 := by
    intro t ht
    change φ (t-s) • U t v - φ t • U t v = 0
    rw [hj t ht, hh t (by push_cast at ht; linarith), sub_self]
  have db : ∀ t, ‖j t-h t‖ ≤ C*‖v‖ := by
    intro t
    change ‖φ (t-s) • U t v - φ t • U t v‖ ≤ _
    rw [← sub_smul, norm_smul, Real.norm_eq_abs, (U t).norm_map]
    exact mul_le_mul_of_nonneg_right (hd t) (norm_nonneg v)
  have kh : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → U s (h t) = 0 := by
    intro t ht
    change U s (φ t • U t v) = 0
    rw [hh t ht, map_zero]
  have kb : ∀ t, ‖U s (h t)‖ ≤ B*‖v‖ := by
    intro t
    rw [(U s).norm_map]
    exact bh t
  have je : ∀ t, j t = U s (h (t+(-s))) := by
    intro t
    simp only [j, h, map_smul, hu, sub_eq_add_neg]
    congr 2
    abel_nf
  have kjs : ∀ t : AF, ((N+1 : ℕ) : ℝ) < |(t : ℝ)| → U s (h (t+(-s))) = 0 := by
    intro t ht
    rw [← je]
    exact hj t ht
  have kjb : ∀ t, ‖U s (h (t+(-s)))‖ ≤ B*‖v‖ := by
    intro t
    rw [← je]
    exact bj t
  have ji : weakIntegral j hj bj = U s (weakIntegral h hh bh) := by
    calc
      _ = weakIntegral (fun t => U s (h (t+(-s)))) kjs kjb :=
        weakIntegral_congr _ _ _ _ _ _ je
      _ = weakIntegral (fun t => U s (h t)) kh kb :=
        weakIntegral_shift (fun t => U s (h t)) (-s) kh kb kjs kjb
      _ = U s (weakIntegral h hh bh) :=
        weakIntegral_map (U s).toContinuousLinearEquiv.toContinuousLinearMap h hh bh kh kb
  have di := weakIntegral_sub j h hj bj hh bh dh db
  change ‖U s (weakIntegral h hh bh) - weakIntegral h hh bh‖ ≤ _
  rw [← ji, ← di]
  exact weakIntegral_norm_bound _ dh db (mul_nonneg hC (norm_nonneg v))

theorem smoothed_tendsto
    (hu : ∀ s t v, U s (U t v) = U (s+t) v)
    (φ : ℝ → ℝ) (hc : UniformContinuous φ) {N : ℕ} {B : ℝ}
    (hφ : ∀ t : ℝ, (N : ℝ) < |t| → φ t = 0)
    (hb : ∀ t, |φ t| ≤ B) (v : H) :
    Tendsto (fun s : AF => U s
      (smoothedVector U (fun t => φ t) (fun t ht => hφ t ht) (fun t => hb t) v))
      (𝓝 0) (𝓝 (smoothedVector U (fun t => φ t)
        (fun t ht => hφ t ht) (fun t => hb t) v)) := by
  apply tendsto_sub_nhds_zero_iff.mp
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let Q : ℝ := (Finset.Icc (-((N+1 : ℕ) : ℤ)-2) (((N+1 : ℕ) : ℤ)+2)).card * ‖v‖
  have hQ : 0 ≤ Q := mul_nonneg (Nat.cast_nonneg _) (norm_nonneg v)
  have hp : 0 < ε/(Q+1) := div_pos hε (by positivity)
  obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuous_iff.mp hc _ hp
  have hnorm : ∀ᶠ s : AF in 𝓝 0, ‖s‖ < min δ 1 :=
    (show Tendsto (fun s : AF => ‖s‖) (𝓝 0) (𝓝 (0 : ℝ)) by
      simpa using continuous_norm.tendsto (0 : AF)).eventually
        (eventually_lt_nhds (lt_min hδ zero_lt_one))
  filter_upwards [hnorm] with s hs
  have hsδ : |(s : ℝ)| < δ := (lt_min_iff.mp hs).1
  have hs1 : |(s : ℝ)| ≤ 1 := le_of_lt (lt_min_iff.mp hs).2
  have hdiff : ∀ t : AF, |φ ((t-s : AF) : ℝ) - φ t| ≤ ε/(Q+1) := by
    intro t
    apply le_of_lt
    apply hd
    change |(t : ℝ)-(s : ℝ)-(t : ℝ)| < δ
    rw [show (t : ℝ)-(s : ℝ)-(t : ℝ) = -(s : ℝ) by ring, abs_neg]
    exact hsδ
  have hbound := smoothed_translation_bound U hu (fun t => φ t)
    (fun t ht => hφ t ht) (fun t => hb t) v s hs1 hp.le hdiff
  rw [dist_zero_right]
  apply hbound.trans_lt
  have hr : Q * (ε/(Q+1)) < ε := by
    rw [← mul_div_assoc, div_lt_iff₀ (by positivity : 0 < Q+1)]
    nlinarith
  simpa only [Q, mul_assoc, mul_comm (ε/(Q+1)) ‖v‖] using hr

end Smoothing
end PlaneFiveColor.InvariantMean
end
end
end

end ParishFactor
end

-- OAI.Analysis.PlaneSpectrum.Multipliers
section
namespace ParishFactor

noncomputable section
open scoped ComplexConjugate
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
noncomputable section
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
namespace PlaneFiveColor.LpMultiplier
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

lemma mul_memLp (h : X → ℂ) (hm : AEStronglyMeasurable h μ)
    (hn : ∀ x, ‖h x‖ = 1) (v : Lp ℂ 2 μ) :
    MemLp (fun x => h x * v x) 2 μ := by
  apply (Lp.memLp v).of_le (hm.mul (Lp.aestronglyMeasurable v))
  exact Eventually.of_forall (fun x => by simp [hn])

private def mul (h : X → ℂ) (hm : AEStronglyMeasurable h μ)
    (hn : ∀ x, ‖h x‖ = 1) (v : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  (mul_memLp h hm hn v).toLp _

lemma mul_ae (h : X → ℂ) (hm : AEStronglyMeasurable h μ)
    (hn : ∀ x, ‖h x‖ = 1) (v : Lp ℂ 2 μ) :
    mul h hm hn v =ᵐ[μ] (fun x => h x * v x) := MemLp.coeFn_toLp _

lemma mul_norm (h : X → ℂ) (hm : AEStronglyMeasurable h μ)
    (hn : ∀ x, ‖h x‖ = 1) (v : Lp ℂ 2 μ) :
    ‖mul h hm hn v‖ = ‖v‖ := by
  simp only [Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae
  filter_upwards [mul_ae h hm hn v] with x hx
  simp [hx, hn]

private def mulIsometry (h : X → ℂ) (hm : AEStronglyMeasurable h μ)
    (hn : ∀ x, ‖h x‖ = 1) : Lp ℂ 2 μ →ₗᵢ[ℝ] Lp ℂ 2 μ where
  toFun := mul h hm hn
  map_add' v w := by
    apply Lp.ext
    filter_upwards [mul_ae h hm hn (v+w), mul_ae h hm hn v, mul_ae h hm hn w,
      Lp.coeFn_add v w, Lp.coeFn_add (mul h hm hn v) (mul h hm hn w)] with x ha hb hc hd he
    simp only [ha, hd, he, Pi.add_apply, hb, hc, mul_add]
  map_smul' r v := by
    apply Lp.ext
    filter_upwards [mul_ae h hm hn (r • v), mul_ae h hm hn v,
      Lp.coeFn_smul r v, Lp.coeFn_smul r (mul h hm hn v)] with x ha hb hc hd
    simp only [ha, hc, hd, Pi.smul_apply, hb, RingHom.id_apply, mul_smul_comm]
  norm_map' := mul_norm h hm hn

lemma mul_inverse (h : X → ℂ) (hm : AEStronglyMeasurable h μ)
    (hn : ∀ x, ‖h x‖ = 1) (v : Lp ℂ 2 μ) :
    mul h hm hn (mul (fun x => conj (h x)) (continuous_star.comp_aestronglyMeasurable hm) (fun x => by simp [hn]) v) = v := by
  apply Lp.ext
  filter_upwards [mul_ae h hm hn (mul (fun x => conj (h x)) (continuous_star.comp_aestronglyMeasurable hm) (fun x => by simp [hn]) v),
    mul_ae (fun x => conj (h x)) (continuous_star.comp_aestronglyMeasurable hm) (fun x => by simp [hn]) v] with x hx hy
  rw [hx, hy, ← mul_assoc]
  have hh : h x * conj (h x) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]
    norm_num
  rw [hh, one_mul]

private def mulEquiv (h : X → ℂ) (hm : AEStronglyMeasurable h μ)
    (hn : ∀ x, ‖h x‖ = 1) : Lp ℂ 2 μ ≃ₗᵢ[ℝ] Lp ℂ 2 μ :=
  LinearIsometryEquiv.ofSurjective (mulIsometry h hm hn) (fun v =>
    ⟨mul (fun x => conj (h x)) (continuous_star.comp_aestronglyMeasurable hm) (fun x => by simp [hn]) v, mul_inverse h hm hn v⟩)

private def weight (v : Lp ℂ 2 μ) : Measure X :=
  μ.withDensity (fun x => ENNReal.ofReal (‖v x‖^2))

lemma weight_measurable (v : Lp ℂ 2 μ) :
    AEMeasurable (fun x => ENNReal.ofReal (‖v x‖^2)) μ :=
  ((Lp.aestronglyMeasurable v).norm.pow 2).aemeasurable.ennreal_ofReal

private instance weight_finite (v : Lp ℂ 2 μ) : IsFiniteMeasure (weight v) := by
  apply isFiniteMeasure_withDensity
  apply (lintegral_ofReal_ne_top_iff_integrable
    ((Lp.aestronglyMeasurable v).norm.pow 2) (Eventually.of_forall (fun x => sq_nonneg ‖v x‖))).mpr
  exact (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable v)).mp (Lp.memLp v)

lemma weight_ac (v : Lp ℂ 2 μ) : weight v ≪ μ :=
  withDensity_absolutelyContinuous _ _

lemma weight_inner (h : X → ℂ) (hm : AEStronglyMeasurable h μ)
    (hn : ∀ x, ‖h x‖ = 1) (v : Lp ℂ 2 μ) :
    (∫ x, h x ∂weight v) = inner ℂ v (mul h hm hn v) := by
  rw [weight, integral_withDensity_eq_integral_toReal_smul₀ (weight_measurable v)
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)), L2.inner_def]
  apply integral_congr_ae
  filter_upwards [mul_ae h hm hn v] with x hx
  rw [hx, ENNReal.toReal_ofReal (sq_nonneg _)]
  simp only [RCLike.inner_apply, Complex.real_smul]
  rw [← Complex.normSq_eq_norm_sq]
  have hh := Complex.mul_conj (v x)
  calc
    _ = (v x * conj (v x)) * h x := by rw [hh]
    _ = _ := by ring

lemma weight_eq_zero_iff (v : Lp ℂ 2 μ) : weight v = 0 ↔ v = 0 := by
  constructor
  · intro hz
    have he := (withDensity_eq_zero_iff (weight_measurable v)).mp hz
    apply Lp.eq_zero_iff_ae_eq_zero.mpr
    filter_upwards [he] with x hx
    have hsq : ‖v x‖^2 = 0 := le_antisymm (ENNReal.ofReal_eq_zero.mp hx) (sq_nonneg _)
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hsq)
  · intro hv
    apply (withDensity_eq_zero_iff (weight_measurable v)).mpr
    filter_upwards [Lp.eq_zero_iff_ae_eq_zero.mp hv] with x hx
    simp [hx]

lemma norm_mul_sub_sq (z w : ℂ) (hz : ‖z‖ = 1) :
    ‖z*w-w‖^2 = 2 * (‖w‖^2 * (1-z.re)) := by
  have he := Complex.normSq_sub z 1
  simp only [Complex.normSq_eq_norm_sq, hz, one_pow, map_one, mul_one] at he
  rw [show z*w-w = (z-1)*w by ring, norm_mul, mul_pow, he]
  ring

lemma lp_norm_sq_integral (v : Lp ℂ 2 μ) :
    (∫ x, ‖v x‖^2 ∂μ) = ‖v‖^2 := by
  have he := L2.inner_def (𝕜 := ℝ) v v
  simpa only [real_inner_self_eq_norm_sq] using he.symm

lemma weight_deviation (h : X → ℂ) (hm : AEStronglyMeasurable h μ)
    (hn : ∀ x, ‖h x‖ = 1) (v : Lp ℂ 2 μ) :
    (∫ x, 1-(h x).re ∂weight v) = ‖mul h hm hn v - v‖^2 / 2 := by
  rw [weight, integral_withDensity_eq_integral_toReal_smul₀ (weight_measurable v)
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  calc
    _ = ∫ x, ‖(mul h hm hn v-v) x‖^2 /2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [mul_ae h hm hn v, Lp.coeFn_sub (mul h hm hn v) v] with x hx hy
      rw [hy, Pi.sub_apply, hx, norm_mul_sub_sq _ _ (hn x),
        ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul]
      ring
    _ = _ := by rw [integral_div, lp_norm_sq_integral]

end PlaneFiveColor.LpMultiplier

namespace PlaneFiveColor.Spectral
open MeasureTheory Filter Topology
open scoped ENNReal
variable [Carrier]

private def lineU (ν : Measure D) (a : E) (t : F) : Lp ℂ 2 ν ≃ₗᵢ[ℝ] Lp ℂ 2 ν :=
  LpMultiplier.mulEquiv (fun d => (lineCharacter a d (Multiplicative.ofAdd t) : ℂ))
    (lineCharacter_measurable a t).aestronglyMeasurable (fun _ => Circle.norm_coe _)

lemma lineU_apply (ν : Measure D) (a : E) (t : F) (v : Lp ℂ 2 ν) :
    lineU ν a t v = LpMultiplier.mul
      (fun d => (lineCharacter a d (Multiplicative.ofAdd t) : ℂ))
      (lineCharacter_measurable a t).aestronglyMeasurable (fun _ => Circle.norm_coe _) v := rfl

lemma lineU_ae (ν : Measure D) (a : E) (t : F) (v : Lp ℂ 2 ν) :
    lineU ν a t v =ᵐ[ν] (fun d => (lineCharacter a d (Multiplicative.ofAdd t) : ℂ) * v d) :=
  LpMultiplier.mul_ae _ (lineCharacter_measurable a t).aestronglyMeasurable
    (fun _ => Circle.norm_coe _) v

lemma lineU_add (ν : Measure D) (a : E) (s t : F) (v : Lp ℂ 2 ν) :
    lineU ν a s (lineU ν a t v) = lineU ν a (s+t) v := by
  apply Lp.ext
  filter_upwards [lineU_ae ν a s (lineU ν a t v), lineU_ae ν a t v,
    lineU_ae ν a (s+t) v] with d hs ht hst
  rw [hs, ht, hst]
  have he := congrArg (fun z : Circle => (z : ℂ))
    ((lineCharacter a d).map_mul (Multiplicative.ofAdd s) (Multiplicative.ofAdd t))
  change (lineCharacter a d (Multiplicative.ofAdd (s+t)) : ℂ) =
    (lineCharacter a d (Multiplicative.ofAdd s) : ℂ) *
      (lineCharacter a d (Multiplicative.ofAdd t) : ℂ) at he
  rw [he, mul_assoc]

lemma lineU_zero (ν : Measure D) (a : E) (v : Lp ℂ 2 ν) : lineU ν a 0 v = v := by
  apply Lp.ext
  filter_upwards [lineU_ae ν a 0 v] with d hd
  simpa using hd

lemma weighted_coeff (ν : Measure D) (a : E) (v : Lp ℂ 2 ν) (t : F) :
    ContinuousCharacters.coeff (LpMultiplier.weight v) (lineCharacter a) t =
      ‖lineU ν a t v-v‖^2/2 := by
  rw [lineU_apply]
  simpa only [ContinuousCharacters.coeff, ContinuousCharacters.deviation, pow_one]
    using LpMultiplier.weight_deviation
      (fun d => (lineCharacter a d (Multiplicative.ofAdd t) : ℂ))
      (lineCharacter_measurable a t).aestronglyMeasurable (fun _ => Circle.norm_coe _) v

theorem strong_vector_zero (ν : Measure D) [IsProbabilityMeasure ν]
    (hν : IsWild ν) {a : E} (ha : a ≠ 0) (v : Lp ℂ 2 ν)
    (hc : Tendsto (fun t => lineU ν a t v) (𝓝 0) (𝓝 v)) : v = 0 := by
  have hcoef : ContinuousAt
      (ContinuousCharacters.coeff (LpMultiplier.weight v) (lineCharacter a)) 0 := by
    have he : ContinuousCharacters.coeff (LpMultiplier.weight v) (lineCharacter a) =
        fun t => ‖lineU ν a t v-v‖^2/2 := funext (weighted_coeff ν a v)
    rw [he]
    change Tendsto _ (𝓝 0) (𝓝 (_ / 2))
    have hh := ((hc.sub (tendsto_const_nhds (x := v))).norm.pow 2).div_const 2
    simpa only [lineU_zero, sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_div]
      using hh
  exact (LpMultiplier.weight_eq_zero_iff v).mp
    (wild_continuous_coefficient_zero ν (LpMultiplier.weight v) hν
      (LpMultiplier.weight_ac v) ha hcoef)

theorem wild_smoothed_zero (ν : Measure D) [IsProbabilityMeasure ν]
    (hν : IsWild ν) {a : E} (ha : a ≠ 0)
    (φ : ℝ → ℝ) (hc : UniformContinuous φ) {N : ℕ} {B : ℝ}
    (hs : ∀ t : ℝ, (N : ℝ) < |t| → φ t = 0)
    (hb : ∀ t, |φ t| ≤ B) (v : Lp ℂ 2 ν) :
    InvariantMean.smoothedVector (lineU ν a) (fun t => φ t)
      (fun t ht => hs t ht) (fun t => hb t) v = 0 := by
  apply strong_vector_zero ν hν ha
  exact InvariantMean.smoothed_tendsto (lineU ν a) (lineU_add ν a) φ hc hs hb v

end PlaneFiveColor.Spectral

namespace PlaneFiveColor.InvariantMean
open MeasureTheory
variable [Spectral.Carrier]
omit [Spectral.Carrier] in
lemma weakMean_complex {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    [DiscreteTopology G] (V : G →ᵇ ℂ) : weakMean V = cmean V := by
  have hr := weakMean_pair V (1 : ℂ)
  have hi := weakMean_pair V Complex.I
  have hpr : pairing V (1 : ℂ) = realPart V := by
    ext x
    simp [pairing_apply, real_inner_eq_re_inner ℂ, RCLike.inner_apply]
  have hpi : pairing V Complex.I = imagPart V := by
    ext x
    simp [pairing_apply, real_inner_eq_re_inner ℂ, RCLike.inner_apply]
  rw [hpr] at hr
  rw [hpi] at hi
  apply Complex.ext <;>
    simp_all [real_inner_eq_re_inner ℂ, RCLike.inner_apply, cmean]

lemma weakIntegral_complex (h : AF → ℂ) {N : ℕ} {B : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0)
    (hb : ∀ t, ‖h t‖ ≤ B) : weakIntegral h hs hb = integralComplex h hs hb :=
  weakMean_complex _
end PlaneFiveColor.InvariantMean

namespace PlaneFiveColor.Spectral
open MeasureTheory Filter Topology
open scoped ENNReal
variable [Carrier]

private def lineFourier (ν : Measure D) (a : E) (t : F) : ℂ :=
  ∫ d, (lineCharacter a d (Multiplicative.ofAdd t) : ℂ) ∂ν

lemma lineFourier_norm_le (ν : Measure D) [IsProbabilityMeasure ν] (a : E) (t : F) :
    ‖lineFourier ν a t‖ ≤ 1 := by
  simpa [lineFourier] using (norm_integral_le_of_norm_le_const (μ := ν)
    (C := (1 : ℝ)) (Eventually.of_forall (fun d => (Circle.norm_coe
      (lineCharacter a d (Multiplicative.ofAdd t))).le)))

lemma lineFourier_inner (ν : Measure D) [IsProbabilityMeasure ν] (a : E) (t : F) :
    inner ℂ (Lp.const 2 ν (1 : ℂ)) (lineU ν a t (Lp.const 2 ν (1 : ℂ))) =
      lineFourier ν a t := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [lineU_ae ν a t (Lp.const 2 ν (1 : ℂ)),
    Lp.coeFn_const (2 : ℝ≥0∞) ν (1 : ℂ)] with d hu hc
  simp [hu, RCLike.inner_apply]

theorem wild_line_average_zero (ν : Measure D) [IsProbabilityMeasure ν]
    (hν : IsWild ν) {a : E} (ha : a ≠ 0)
    (φ : ℝ → ℝ) (hc : UniformContinuous φ) {N : ℕ} {B : ℝ}
    (hs : ∀ t : ℝ, (N : ℝ) < |t| → φ t = 0)
    (hb : ∀ t, |φ t| ≤ B) :
    InvariantMean.integralComplex (B := B)
      (fun t : F => (φ t : ℂ) * lineFourier ν a t)
      (fun t ht => by rw [hs t ht, Complex.ofReal_zero, zero_mul])
      (fun t => by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact (mul_le_of_le_one_right (abs_nonneg _) (lineFourier_norm_le ν a t)).trans (hb t)) = 0 := by
  let v := Lp.const 2 ν (1 : ℂ)
  let L : Lp ℂ 2 ν →L[ℝ] ℂ := (innerSL ℂ v).restrictScalars ℝ
  have he (t : F) : L (φ t • lineU ν a t v) = (φ t : ℂ) * lineFourier ν a t := by
    rw [map_smul]
    change φ t • inner ℂ v (lineU ν a t v) = _
    rw [lineFourier_inner]
    rfl
  have hjs : ∀ t : F, (N : ℝ) < |(t : ℝ)| → L (φ t • lineU ν a t v) = 0 := by
    intro t ht
    rw [he, hs t ht, Complex.ofReal_zero, zero_mul]
  have hjb : ∀ t : F, ‖L (φ t • lineU ν a t v)‖ ≤ B := by
    intro t
    rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_of_le_one_right (abs_nonneg _) (lineFourier_norm_le ν a t)).trans (hb t)
  have hm := InvariantMean.weakIntegral_map L
    (fun t : F => φ t • lineU ν a t v)
    (InvariantMean.smoothed_support (lineU ν a) (fun t => φ t) (fun t ht => hs t ht) v)
    (InvariantMean.smoothed_bound (lineU ν a) (fun t => φ t) (fun t => hb t) v)
    hjs hjb
  change InvariantMean.weakIntegral _ _ _ = L (InvariantMean.smoothedVector
    (lineU ν a) (fun t : F => φ t) (fun t ht => hs t ht) (fun t => hb t) v) at hm
  rw [wild_smoothed_zero ν hν ha φ hc hs hb v, map_zero] at hm
  rw [← InvariantMean.weakIntegral_complex]
  exact (InvariantMean.weakIntegral_congr _ _ _ _ hjs hjb (fun t => (he t).symm)).trans hm

end PlaneFiveColor.Spectral
end
end
end
end

end ParishFactor
end

-- OAI.Analysis.PlaneSpectrum.FourierTests
section
namespace ParishFactor

noncomputable section
open scoped ComplexConjugate
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
noncomputable section
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate

namespace PlaneFiveColor.InvariantMean
open scoped BigOperators
open MeasureTheory Filter Topology
variable [Spectral.Carrier]

lemma integralReal_congr (f g : AF → ℝ) {N M : ℕ} {B C : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → f t = 0)
    (hb : ∀ t, ‖f t‖ ≤ B)
    (gs : ∀ t : AF, (M : ℝ) < |(t : ℝ)| → g t = 0)
    (gb : ∀ t, ‖g t‖ ≤ C) (he : ∀ t, f t = g t) :
    integralReal f hs hb = integralReal g gs gb := by
  unfold integralReal
  congr 1
  ext x
  induction x using QuotientAddGroup.induction_on with
  | H t => simp only [periodBCF_mk, periodSum, he]

lemma integralReal_mul (f : AF → ℝ) (c : ℝ) {N M : ℕ} {B C : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → f t = 0)
    (hb : ∀ t, ‖f t‖ ≤ B)
    (gs : ∀ t : AF, (M : ℝ) < |(t : ℝ)| → c*f t = 0)
    (gb : ∀ t, ‖c*f t‖ ≤ C) :
    integralReal (fun t => c*f t) gs gb = c * integralReal f hs hb := by
  have he : periodBCF (fun t => c*f t) gs gb = c • periodBCF f hs hb := by
    ext x
    induction x using QuotientAddGroup.induction_on with
    | H t =>
      change (∑' k : ℤ, c * f (t+k)) = c * (∑' k : ℤ, f (t+k))
      exact tsum_mul_left
  exact (congrArg mean he).trans (mean_smul _ _)

lemma integralReal_sum {ι : Type*} (s : Finset ι) (f : ι → AF → ℝ)
    {N M : ℕ} {B : ι → ℝ} {C : ℝ}
    (hs : ∀ i, ∀ t : AF, (N : ℝ) < |(t : ℝ)| → f i t = 0)
    (hb : ∀ i t, ‖f i t‖ ≤ B i)
    (gs : ∀ t : AF, (M : ℝ) < |(t : ℝ)| → (∑ i ∈ s, f i t) = 0)
    (gb : ∀ t, ‖∑ i ∈ s, f i t‖ ≤ C) :
    integralReal (fun t => ∑ i ∈ s, f i t) gs gb =
      ∑ i ∈ s, integralReal (f i) (hs i) (hb i) := by
  have he : periodBCF (fun t => ∑ i ∈ s, f i t) gs gb =
      ∑ i ∈ s, periodBCF (f i) (hs i) (hb i) := by
    ext x
    rw [BoundedContinuousFunction.sum_apply]
    induction x using QuotientAddGroup.induction_on with
    | H t =>
      simp only [periodBCF_mk, periodSum]
      exact Summable.tsum_finsetSum (fun i _ => period_summable (hs i) t)
  unfold integralReal
  rw [he]
  exact map_sum (meanCLM (G := PeriodGroup)) _ _

lemma weighted_bound (φ f : AF → ℝ) {B : ℝ}
    (hb : ∀ t, ‖φ t‖ ≤ B) (hf : ∀ t, 0 ≤ f t ∧ f t ≤ 1) :
    ∀ t, ‖φ t * f t‖ ≤ B := by
  intro t
  rw [norm_mul, Real.norm_of_nonneg (hf t).1]
  exact (mul_le_of_le_one_right (norm_nonneg _) (hf t).2).trans (hb t)

theorem exists_small_nonnegative_tests {ι : Type*} (s : Finset ι)
    (φ : AF → ℝ) (f : ι → AF → ℝ) {N : ℕ} {B ε : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → φ t = 0)
    (hb : ∀ t, ‖φ t‖ ≤ B) (hp : ∀ t, 0 ≤ φ t)
    (hI : 0 < integralReal φ hs hb) (hε : 0 < ε)
    (hf : ∀ i t, 0 ≤ f i t ∧ f i t ≤ 1)
    (hz : ∀ i, integralReal (fun t => φ t * f i t)
      (fun t ht => by rw [hs t ht, zero_mul])
      (weighted_bound φ (f i) hb (hf i)) = 0) :
    ∃ t : AF, 0 < φ t ∧ ∀ i ∈ s, f i t < ε := by
  classical
  by_contra hn
  push Not at hn
  let g : AF → ℝ := fun t => ∑ i ∈ s, φ t * f i t
  have gs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → g t = 0 := by
    intro t ht
    simp [g, hs t ht]
  have gb : ∀ t, ‖g t‖ ≤ (s.card : ℝ) * B := by
    intro t
    calc
      _ ≤ ∑ i ∈ s, ‖φ t*f i t‖ := norm_sum_le _ _
      _ ≤ ∑ _i ∈ s, B := Finset.sum_le_sum (fun i _ => weighted_bound φ (f i) hb (hf i) t)
      _ = _ := by simp
  have gi : integralReal g gs gb = 0 := by
    rw [integralReal_sum s (fun i t => φ t*f i t)
      (fun i t ht => by rw [hs t ht, zero_mul])
      (fun i => weighted_bound φ (f i) hb (hf i)) gs gb]
    simp only [hz, Finset.sum_const_zero]
  have cs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → ε*φ t = 0 := by
    intro t ht; rw [hs t ht, mul_zero]
  have cb : ∀ t, ‖ε*φ t‖ ≤ |ε| * B := by
    intro t
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hb t) (abs_nonneg _)
  have hle : ∀ t, ε*φ t ≤ g t := by
    intro t
    by_cases ht : 0 < φ t
    · obtain ⟨i, hi, hfi⟩ := hn t ht
      have hterm : φ t*f i t ≤ g t :=
        Finset.single_le_sum (fun j _ => mul_nonneg (hp t) (hf j t).1) hi
      exact (by nlinarith : ε*φ t ≤ φ t*f i t).trans hterm
    · have hφ : φ t = 0 := le_antisymm (le_of_not_gt ht) (hp t)
      simp [g, hφ]
  have hmono := integralReal_mono (fun t => ε*φ t) g cs cb gs gb hle
  rw [integralReal_mul φ ε hs hb cs cb, gi] at hmono
  exact (not_le_of_gt (mul_pos hε hI)) hmono

end PlaneFiveColor.InvariantMean

namespace PlaneFiveColor.Spectral
open MeasureTheory Filter Topology
open scoped BigOperators
open InvariantMean
variable [Carrier]

@[simp] lemma lineFourier_zero (ν : Measure D) [IsProbabilityMeasure ν] (a : E) :
    lineFourier ν a 0 = 1 := by
  simp [lineFourier]

lemma lineFourier_re_le_one (ν : Measure D) [IsProbabilityMeasure ν] (a : E) (t : F) :
    (lineFourier ν a t).re ≤ 1 :=
  (Complex.re_le_norm _).trans (lineFourier_norm_le ν a t)

lemma wild_line_average_re_zero (ν : Measure D) [IsProbabilityMeasure ν]
    (hν : IsWild ν) {a : E} (ha : a ≠ 0)
    (φ : ℝ → ℝ) (hc : UniformContinuous φ) {N : ℕ} {B : ℝ}
    (hs : ∀ t : ℝ, (N : ℝ) < |t| → φ t = 0)
    (hb : ∀ t, |φ t| ≤ B) :
    integralReal (B := B) (fun t : F => φ t * (lineFourier ν a t).re)
      (fun t ht => by rw [hs t ht, zero_mul])
      (fun t => by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        exact (mul_le_of_le_one_right (abs_nonneg _)
          ((Complex.abs_re_le_norm _).trans (lineFourier_norm_le ν a t))).trans (hb t)) = 0 := by
  let f : F → ℂ := fun t => (φ t : ℂ) * lineFourier ν a t
  have fs : ∀ t : F, (N : ℝ) < |(t : ℝ)| → f t = 0 := by
    intro t ht; simp [f, hs t ht]
  have fb : ∀ t, ‖f t‖ ≤ B := by
    intro t
    dsimp [f]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_of_le_one_right (abs_nonneg _) (lineFourier_norm_le ν a t)).trans (hb t)
  have rs : ∀ t : F, (N : ℝ) < |(t : ℝ)| → (f t).re = 0 := by
    intro t ht; rw [fs t ht]; rfl
  have rb : ∀ t, ‖(f t).re‖ ≤ B := by
    intro t
    simpa only [Real.norm_eq_abs] using (Complex.abs_re_le_norm (f t)).trans (fb t)
  have hz : integralReal (fun t => (f t).re) rs rb = 0 := by
    rw [← integralComplex_re f fs fb rs rb]
    rw [show integralComplex f fs fb = 0 from wild_line_average_zero ν hν ha φ hc hs hb]
    rfl
  exact (integralReal_congr _ _ _ _ rs rb (fun t => by simp [f])).trans hz

omit [Carrier] in

lemma exists_positive_window {r : ℝ} (hr : 0 < r) :
    ∃ (φ : C(ℝ, ℝ)) (N : ℕ) (B : ℝ),
      (∀ t : ℝ, (N : ℝ) < |t| → φ t = 0) ∧
      (∀ t, ‖φ t‖ ≤ B) ∧ (∀ t, 0 ≤ φ t) ∧
      UniformContinuous φ ∧ (0 < ∫ t : ℝ, φ t) ∧
      (∀ t, 0 < φ t → |t| < r) := by
  let φ : C(ℝ, ℝ) := ⟨fun t => max 0 (r-|t|), by fun_prop⟩
  have hp (t : ℝ) : 0 ≤ φ t := le_max_left _ _
  have hb (t : ℝ) : ‖φ t‖ ≤ r := by
    rw [Real.norm_of_nonneg (hp t)]
    exact max_le hr.le (sub_le_self _ (abs_nonneg _))
  have houtside (t : ℝ) (ht : r ≤ |t|) : φ t = 0 := max_eq_left (sub_nonpos.mpr ht)
  have hcomp : HasCompactSupport φ := by
    apply HasCompactSupport.intro' (K := Set.Icc (-r) r) isCompact_Icc isClosed_Icc
    intro t ht
    apply houtside
    by_contra hn
    exact ht (abs_le.mp (le_of_lt (lt_of_not_ge hn)))
  have hi : 0 < ∫ t : ℝ, φ t :=
    φ.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hcomp hp
      (show φ 0 ≠ 0 by simpa [φ, max_eq_right hr.le] using hr.ne')
  obtain ⟨N, hN⟩ := exists_nat_gt r
  refine ⟨φ, N, r, (fun t ht => houtside t (le_of_lt (hN.trans ht))), hb, hp,
    hcomp.uniformContinuous_of_continuous φ.continuous, hi, ?_⟩
  intro t ht
  by_contra hn
  rw [houtside t (le_of_not_gt hn)] at ht
  exact lt_irrefl _ ht

theorem exists_small_wild_parameter {ι : Type*} (s : Finset ι) (hne : s.Nonempty)
    (ν : Measure D) [IsProbabilityMeasure ν] (hν : IsWild ν)
    (a : ι → E) (ha : ∀ i, a i ≠ 0)
    (hn : ∀ i t, 0 ≤ (lineFourier ν (a i) t).re)
    {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ t : F, t ≠ 0 ∧ |(t : ℝ)| < r ∧
      ∀ i ∈ s, (lineFourier ν (a i) t).re < ε := by
  obtain ⟨φ, N, B, hs, hb, hp, hc, hi, hradius⟩ := exists_positive_window hr
  have hz := fun i => wild_line_average_re_zero ν hν (ha i) φ hc hs
    (fun t => by simpa only [← Real.norm_eq_abs] using hb t)
  have hI : 0 < integralReal (fun t : F => φ t)
      (fun t ht => hs t ht) (fun t => hb t) := by
    rw [integralReal_ordinary φ hs hb]
    exact hi
  obtain ⟨t, ht, htest⟩ := exists_small_nonnegative_tests s
    (fun t : F => φ t) (fun i t => (lineFourier ν (a i) t).re)
    (fun t ht => hs t ht) (fun t => hb t) (fun t => hp t) hI hε
    (fun i t => ⟨hn i t, lineFourier_re_le_one ν (a i) t⟩)
    (fun i => by convert hz i using 1)
  refine ⟨t, ?_, hradius t ht, htest⟩
  intro he
  obtain ⟨i, his⟩ := hne
  have hh := htest i his
  rw [he, lineFourier_zero, Complex.one_re] at hh
  exact (not_lt_of_ge hε1) hh

end PlaneFiveColor.Spectral

open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
namespace EuclideanFiveColor.DifferenceFourier

variable {G Y : Type*} [MeasurableSpace G] [MeasurableSpace Y]
  [CommGroup G] [MeasurableMul₂ G] [MeasurableInv G]

private noncomputable def differenceLaw (ν : Measure Y) (κ : Kernel Y G) [IsMarkovKernel κ] :
    Measure G := ((κ ×ₖ κ) ∘ₘ ν).map (fun p : G × G => p.1 / p.2)

private instance differenceLaw_probability (ν : Measure Y) [IsProbabilityMeasure ν]
    (κ : Kernel Y G) [IsMarkovKernel κ] : IsProbabilityMeasure (differenceLaw ν κ) := by
  unfold differenceLaw
  exact Measure.isProbabilityMeasure_map (measurable_fst.div measurable_snd).aemeasurable

variable (χ : G →* Circle)

omit [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G] in
lemma coe_character_div (d e : G) :
    (χ (d / e) : ℂ) = (χ d : ℂ) * conj (χ e : ℂ) := by
  rw [map_div, div_eq_mul_inv, Circle.coe_mul, Circle.coe_inv_eq_conj]

omit [MeasurableMul₂ G] [MeasurableInv G] in
lemma independent_coefficient (κ : Measure G) [IsProbabilityMeasure κ] :
    (∫ p : G × G, (χ (p.1 / p.2) : ℂ) ∂κ.prod κ) =
      (‖∫ d, (χ d : ℂ) ∂κ‖ ^ 2 : ℝ) := by
  calc
    _ = ∫ p : G × G, (χ p.1 : ℂ) * conj (χ p.2 : ℂ) ∂κ.prod κ :=
      integral_congr_ae (Filter.Eventually.of_forall (fun p => coe_character_div χ p.1 p.2))
    _ = (∫ d, (χ d : ℂ) ∂κ) * (∫ d, conj (χ d : ℂ) ∂κ) := by
      convert integral_prod_mul (fun d => (χ d : ℂ)) (fun d => conj (χ d : ℂ)) using 1 <;> infer_instance
    _ = _ := by rw [integral_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq]

lemma difference_coefficient (hχ : Measurable (fun d => (χ d : ℂ))) (ν : Measure Y) [IsProbabilityMeasure ν]
    (κ : Kernel Y G) [IsMarkovKernel κ] :
    (∫ d, (χ d : ℂ) ∂differenceLaw ν κ) =
      ((∫ y, (‖∫ d, (χ d : ℂ) ∂κ y‖ ^ 2 : ℝ) ∂ν : ℝ) : ℂ) := by
  have hm := hχ
  have hdiv : Measurable (fun p : G × G => p.1 / p.2) :=
    measurable_fst.div measurable_snd
  rw [differenceLaw, integral_map hdiv.aemeasurable hm.aestronglyMeasurable,
    Measure.comp_eq_comp_const_apply]
  rw [Kernel.integral_comp]
  · simp only [Kernel.const_apply, Kernel.prod_apply]
    change (∫ y, (∫ p : G × G, (χ (p.1 / p.2) : ℂ) ∂(κ y).prod (κ y)) ∂ν) = _
    rw [← integral_complex_ofReal]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun y => independent_coefficient χ (κ y))
  · exact Integrable.of_bound (hm.comp hdiv).aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun _ => (Circle.norm_coe _).le))

lemma difference_coefficient_nonneg (hχ : Measurable (fun d => (χ d : ℂ))) (ν : Measure Y) [IsProbabilityMeasure ν]
    (κ : Kernel Y G) [IsMarkovKernel κ] :
    0 ≤ (∫ d, (χ d : ℂ) ∂differenceLaw ν κ).re := by
  rw [difference_coefficient χ hχ]
  simp only [Complex.ofReal_re]
  apply integral_nonneg
  intro y
  positivity

end EuclideanFiveColor.DifferenceFourier

end
end
end
end

end ParishFactor
end

-- OAI.Analysis.PlaneSpectrum.SmallArcs
section
namespace ParishFactor

noncomputable section
open scoped ComplexConjugate
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
noncomputable section
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators
open Polynomial
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open MeasureTheory ProbabilityTheory
open scoped BigOperators

open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace EuclideanFiveColor.SmallArc
noncomputable section

private def phaseSum (z : ℂ) (N : ℕ) : ℂ := ∑ n ∈ Finset.range N, z ^ n

lemma pow_sub_one_bound (z : ℂ) (hz : ‖z‖ = 1) (n : ℕ) :
    ‖z ^ n - 1‖ ≤ n * ‖z - 1‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he : z ^ (n+1) - 1 = z ^ n * (z - 1) + (z ^ n - 1) := by ring
    rw [he]
    calc
      _ ≤ ‖z ^ n * (z - 1)‖ + ‖z ^ n - 1‖ := norm_add_le _ _
      _ ≤ ‖z - 1‖ + n * ‖z - 1‖ := by
        simpa only [norm_mul, norm_pow, hz, one_pow, one_mul] using
          add_le_add_right ih ‖z - 1‖
      _ = _ := by push_cast; ring

lemma phaseSum_sub_bound (z : ℂ) (hz : ‖z‖ = 1) (N : ℕ) :
    ‖phaseSum z N - (N : ℂ)‖ ≤ (N : ℝ)^2 * ‖z-1‖ := by
  have he : phaseSum z N - (N : ℂ) = ∑ n ∈ Finset.range N, (z^n-1) := by
    simp [phaseSum, Finset.sum_sub_distrib]
  rw [he]
  calc
    _ ≤ ∑ n ∈ Finset.range N, ‖z^n-1‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.range N, (N : ℝ) * ‖z-1‖ := by
      apply Finset.sum_le_sum
      intro n hn
      exact (pow_sub_one_bound z hz n).trans
        (mul_le_mul_of_nonneg_right (by exact_mod_cast (Finset.mem_range.mp hn).le)
          (norm_nonneg _))
    _ = _ := by simp; ring

lemma phaseSum_lower (z : ℂ) (hz : ‖z‖ = 1) {N : ℕ} (hN : 0 < N)
    (hd : ‖z-1‖ ≤ 1 / (2 * (N : ℝ))) : (N : ℝ) / 2 ≤ ‖phaseSum z N‖ := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hb := phaseSum_sub_bound z hz N
  have he : (N : ℝ)^2 * ‖z-1‖ ≤ (N : ℝ)/2 := by
    have := mul_le_mul_of_nonneg_left hd (sq_nonneg (N : ℝ))
    calc
      _ ≤ (N : ℝ)^2 * (1 / (2 * (N : ℝ))) := this
      _ = _ := by field_simp
  have ht := norm_sub_norm_le (N : ℂ) (phaseSum z N)
  rw [norm_sub_rev] at ht
  have hn : ‖(N : ℂ)‖ = (N : ℝ) := by simp
  rw [hn] at ht
  linarith

lemma phase_energy (z : ℂ) (N : ℕ) :
    ‖phaseSum z N‖ ^ 2 = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
      (z^i * conj (z^j)).re := by
  calc
    _ = (phaseSum z N * conj (phaseSum z N)).re := by
      rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    _ = _ := by
      simp only [phaseSum, map_sum, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      change Complex.reCLM (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, _) = _
      simp only [map_sum]
      rfl

lemma pow_mul_conj_pow (z : ℂ) (hz : ‖z‖ = 1) {i j : ℕ} (hji : j ≤ i) :
    z^i * conj (z^j) = z^(i-j) := by
  nth_rw 1 [← Nat.sub_add_cancel hji]
  rw [pow_add, mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_pow,
    hz, one_pow, one_pow, Complex.ofReal_one, mul_one]

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
  (z : X → ℂ) (hz : Measurable z) (hu : ∀ x, ‖z x‖ = 1)

include hz hu
lemma integrable_pair (i j : ℕ) : Integrable (fun x => z x ^ i * conj (z x ^ j)) μ := by
  apply Integrable.of_bound (by fun_prop) 1
  exact Filter.Eventually.of_forall (fun x => by simp [hu])

omit hz in
lemma pair_moment_bound {N : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (hm : ∀ n, 0 < n → n < N → ‖∫ x, z x ^ n ∂μ‖ ≤ c)
    {i j : ℕ} (hi : i < N) (hj : j < N) :
    (∫ x, z x^i * conj (z x^j) ∂μ).re ≤ (if i=j then 1 else 0) + c := by
  by_cases he : i = j
  · subst j
    have he : (fun x => z x^i * conj (z x^i)) = fun _ => (1 : ℂ) := by
      funext x
      simpa using pow_mul_conj_pow (z x) (hu x) (le_refl i)
    rw [he, integral_const]
    simp [hc]
  · simp only [he, ↓reduceIte, zero_add]
    by_cases hji : j ≤ i
    · have he : (fun x => z x^i * conj (z x^j)) = fun x => z x^(i-j) := by
        funext x
        exact pow_mul_conj_pow (z x) (hu x) hji
      rw [he]
      exact (Complex.re_le_norm _).trans (hm (i-j) (by omega) (by omega))
    · have he : (fun x => z x^i * conj (z x^j)) =
          fun x => conj (z x^(j-i)) := by
        funext x
        rw [← pow_mul_conj_pow (z x) (hu x) (by omega : i ≤ j)]
        simp only [map_mul, starRingEnd_self_apply]
        exact mul_comm _ _
      rw [he, integral_conj]
      exact (Complex.re_le_norm _).trans (by simpa using hm (j-i) (by omega) (by omega))

lemma phase_energy_integral_bound {N : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (hm : ∀ n, 0 < n → n < N → ‖∫ x, z x ^ n ∂μ‖ ≤ c) :
    (∫ x, ‖phaseSum (z x) N‖ ^ 2 ∂μ) ≤ N + (N : ℝ)^2 * c := by
  simp_rw [phase_energy]
  rw [integral_finsetSum]
  · calc
      _ = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
          (∫ x, z x^i * conj (z x^j) ∂μ).re := by
        apply Finset.sum_congr rfl
        intro i _
        rw [integral_finsetSum]
        · apply Finset.sum_congr rfl
          intro j _
          exact (integral_re (integrable_pair μ z hz hu i j))
        · intro j _
          exact (integrable_pair μ z hz hu i j).re
      _ ≤ ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
          ((if i=j then (1 : ℝ) else 0) + c) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        exact pair_moment_bound μ z hu hc hm (Finset.mem_range.mp hi)
          (Finset.mem_range.mp hj)
      _ = _ := by
        rw [Finset.sum_congr rfl (fun i hi => by
          rw [Finset.sum_add_distrib, Finset.sum_ite_eq, if_pos hi])]
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
  · intro i _
    exact integrable_finsetSum _ (fun j _ => (integrable_pair μ z hz hu i j).re)

lemma integrable_energy (N : ℕ) : Integrable (fun x => ‖phaseSum (z x) N‖^2) μ := by
  have h : ∀ x, ‖phaseSum (z x) N‖ ≤ N := by
    intro x
    calc
      _ ≤ ∑ n ∈ Finset.range N, ‖z x ^ n‖ := norm_sum_le _ _
      _ = N := by simp [hu]
  apply Integrable.of_bound (by unfold phaseSum; fun_prop) ((N : ℝ)^2)
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (h x) 2)

theorem small_arc_bound {N : ℕ} (hN : 0 < N) {c : ℝ} (hc : 0 ≤ c)
    (hm : ∀ n, 0 < n → n < N → ‖∫ x, z x ^ n ∂μ‖ ≤ c) :
    μ.real {x | ‖z x-1‖ ≤ 1 / (2 * (N : ℝ))} ≤ 4 / N + 4*c := by
  have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hs : {x | ‖z x-1‖ ≤ 1 / (2 * (N : ℝ))} ⊆
      {x | (N : ℝ)^2 / 4 ≤ ‖phaseSum (z x) N‖ ^ 2} := by
    intro x hx
    have hh := phaseSum_lower (z x) (hu x) hN hx
    change (N : ℝ)^2 / 4 ≤ _
    nlinarith [norm_nonneg (phaseSum (z x) N)]
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun x => sq_nonneg ‖phaseSum (z x) N‖))
    (integrable_energy μ z hz hu N) ((N : ℝ)^2/4)
  have he := phase_energy_integral_bound μ z hz hu hc hm
  have hreal := measureReal_mono (μ := μ) hs
  have hm' : (N : ℝ)^2/4 * μ.real {x | ‖z x-1‖ ≤ 1 / (2 * (N : ℝ))} ≤
      N + (N : ℝ)^2*c :=
    (mul_le_mul_of_nonneg_left hreal (by positivity)).trans (hmark.trans he)
  calc
    _ ≤ (N + (N : ℝ)^2*c)/((N : ℝ)^2/4) :=
      (le_div_iff₀ (by positivity)).mpr (by nlinarith [hm'])
    _ = _ := by field_simp

local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩

omit [MeasurableSpace X] hz hu in

theorem exists_small_arc_constants (m : ℕ) (hm : 0 < m) :
    ∃ (ρ c : ℝ) (N : ℕ), 0 < ρ ∧ 0 < c ∧ 0 < N ∧
      ∀ (ω : Measure Circle) [IsProbabilityMeasure ω],
      (∀ n, 0 < n → n ≤ N → ‖∫ w, (w : ℂ)^n ∂ω‖ < c) →
      ω.real {w | ‖(w : ℂ)-1‖ ≤ 4*ρ} < 1/(4*(m : ℝ)^2) := by
  let N := 64*m^2
  have hN : 0 < N := by dsimp [N]; positivity
  have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hmp : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  refine ⟨1/(8*N), 1/N, N, by positivity, by positivity, hN, ?_⟩
  intro ω _ hω
  have hco : Continuous (fun w : Circle => (w : ℂ)) := continuous_subtype_val
  have hcm : Measurable (fun w : Circle => (w : ℂ)) := hco.measurable
  have hb := small_arc_bound ω (fun w : Circle => (w : ℂ))
    hcm Circle.norm_coe hN (by positivity : (0 : ℝ) ≤ 1/N)
    (fun n hn hnN => (hω n hn (le_of_lt hnN)).le)
  have hr : 4*(1/(8*(N : ℝ))) = 1/(2*N) := by ring
  rw [hr]
  apply hb.trans_lt
  have he : (N : ℝ) = 64*(m : ℝ)^2 := by dsimp [N]; push_cast; rfl
  rw [he]
  field_simp
  norm_num

end
end EuclideanFiveColor.SmallArc

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace EuclideanFiveColor.SampledAtoms
noncomputable section
variable {X Y G : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace G] [MeasurableEq G]

lemma measurable_atom_mass (κ : Kernel Y G) [IsSFiniteKernel κ] :
    Measurable (fun p : Y × G => κ p.1 {p.2}) := by
  classical
  let η : Kernel (Y × G) G := κ.comap Prod.fst measurable_fst
  have hm : Measurable (fun p : (Y × G) × G =>
      if p.2 = p.1.2 then (1 : ℝ≥0∞) else 0) :=
    Measurable.ite (measurableSet_eq_fun measurable_snd (measurable_snd.comp measurable_fst))
      measurable_const measurable_const
  have h := hm.lintegral_kernel_prod_right' (κ := η)
  convert h using 1
  ext p
  change κ p.1 {p.2} = ∫⁻ d, (if d=p.2 then (1:ℝ≥0∞) else 0) ∂κ p.1
  simpa only [Set.indicator_apply, Set.mem_singleton_iff, Pi.one_apply] using
    (lintegral_indicator_one (μ := κ p.1) (measurableSet_singleton p.2)).symm

variable [StandardBorelSpace G] [Nonempty G]
lemma ae_sampled_positive_atom (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → Y) (b : X → G) (hp : Measurable p) (hb : Measurable b)
    (ha : ∀ᵐ y ∂μ.map p, ∀ᵐ d ∂condDistrib b p μ y, 0 < condDistrib b p μ y {d}) :
    ∀ᵐ x ∂μ, 0 < condDistrib b p μ (p x) {b x} := by
  have hm : MeasurableSet {z : Y × G | 0 < condDistrib b p μ z.1 {z.2}} :=
    measurableSet_lt measurable_const (measurable_atom_mass _)
  have he : ∀ᵐ z ∂μ.map p ⊗ₘ condDistrib b p μ,
      0 < condDistrib b p μ z.1 {z.2} := (Measure.ae_compProd_iff hm).mpr ha
  rw [compProd_map_condDistrib hb.aemeasurable] at he
  exact ae_of_ae_map (hp.prodMk hb).aemeasurable he

omit [StandardBorelSpace G] [Nonempty G] in
lemma uniform_list_positive_atoms (μ : Measure G) {m : ℕ} (_hm : 0 < m)
    (g : Fin m → G) (hμ : μ = (m : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (g i)) :
    ∀ᵐ d ∂μ, 0 < μ {d} := by
  classical
  have hi : (m : ℝ≥0∞)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr (by simp)
  have hpt (i : Fin m) : 0 < μ {g i} := by
    rw [hμ, Measure.smul_apply, smul_eq_mul]
    apply ENNReal.mul_pos hi
    have hle : (1 : ℝ≥0∞) ≤ (∑ j, Measure.dirac (g j)) {g i} := by
      rw [Measure.finsetSum_apply]
      calc
        _ = Measure.dirac (g i) {g i} := by simp
        _ ≤ ∑ j, Measure.dirac (g j) {g i} :=
          Finset.single_le_sum (f := fun j : Fin m => Measure.dirac (g j) {g i})
            (fun j _ => bot_le) (Finset.mem_univ i)
    exact ne_of_gt (lt_of_lt_of_le (by norm_num) hle)
  rw [hμ] at hpt ⊢
  rw [Measure.ae_ennreal_smul_measure_iff hi, ae_finsetSum_measure_iff]
  intro i _
  simpa only [ae_dirac_eq, Filter.eventually_pure] using hpt i

omit [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace G] [Nonempty G] in
lemma in_list_of_positive_atom (μ : Measure G) {m : ℕ} (g : Fin m → G)
    (hμ : μ = (m : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (g i))
    {d : G} (hd : 0 < μ {d}) : ∃ i, d = g i := by
  classical
  by_contra hn
  have hne (i : Fin m) : g i ≠ d := by intro hi; exact hn ⟨i, hi.symm⟩
  have hz : μ {d} = 0 := by
    rw [hμ, Measure.smul_apply, Measure.finsetSum_apply]
    simp [Measure.dirac_apply', hne]
  exact (ne_of_gt hd) hz

lemma ae_sampled_list (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → Y) (b : X → G) (hp : Measurable p) (hb : Measurable b)
    {m : ℕ} (hm : 0 < m) (g : Y → Fin m → G)
    (hg : ∀ᵐ y ∂μ.map p, condDistrib b p μ y =
      (m : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (g y i)) :
    ∀ᵐ x ∂μ, ∃ i, b x = g (p x) i := by
  have hat := ae_sampled_positive_atom μ p b hp hb
    (hg.mono fun y hy => uniform_list_positive_atoms _ hm (g y) hy)
  filter_upwards [hat, ae_of_ae_map hp.aemeasurable hg] with x hx hxl
  exact in_list_of_positive_atom _ _ hxl hx

end
end EuclideanFiveColor.SampledAtoms

end
end
end
end

end ParishFactor
end

-- OAI.Analysis.PlaneSpectrum.PhaseEncoding
section
namespace ParishFactor

noncomputable section

open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
open scoped BigOperators

open scoped BigOperators
open Polynomial
namespace EuclideanFiveColor.PhaseEncoding

section

private def phases {m : ℕ} (z : Fin m → Circle) : Multiset ℂ :=
  Finset.univ.val.map (fun i => (z i : ℂ))

private def elem {m : ℕ} (z : Fin m → Circle) (n : ℕ) : ℂ := (phases z).esymm n

private def encoding {m : ℕ} (z : Fin m → Circle) : Fin m → ℂ :=
  fun i => elem z (i.val + 1)

private def phasePolynomial {m : ℕ} (z : Fin m → Circle) : ℂ[X] :=
  ∏ i : Fin m, (X - C (z i : ℂ))

@[simp] theorem card_phases {m : ℕ} (z : Fin m → Circle) : (phases z).card = m := by
  simp [phases]

@[simp] theorem elem_zero {m : ℕ} (z : Fin m → Circle) : elem z 0 = 1 := by
  simp [elem, Multiset.esymm]

theorem elem_eq_sum {m : ℕ} (z : Fin m → Circle) (n : ℕ) :
    elem z n = ∑ t ∈ (Finset.univ : Finset (Fin m)).powersetCard n,
      ∏ i ∈ t, (z i : ℂ) :=
  Finset.esymm_map_val _ _ n

theorem continuous_encoding {m : ℕ} : Continuous (encoding (m := m)) := by
  apply continuous_pi
  intro i
  simp only [encoding, elem_eq_sum]
  fun_prop

theorem polynomial_expansion {m : ℕ} (z : Fin m → Circle) :
    phasePolynomial z = ∑ n ∈ Finset.range (m + 1),
      (-1) ^ n * (C (elem z n) * X ^ (m - n)) := by
  have he : phasePolynomial z = ((phases z).map (fun t => X - C t)).prod := by
    rw [phasePolynomial, Finset.prod_eq_multiset_prod]
    simp only [phases, Multiset.map_map, Function.comp_def]
  rw [he, Multiset.prod_X_sub_X_eq_sum_esymm, card_phases]
  rfl

@[simp] theorem eval_at_phase {m : ℕ} (z : Fin m → Circle) (i : Fin m) :
    (phasePolynomial z).eval (z i : ℂ) = 0 := by
  rw [phasePolynomial, Polynomial.eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp

theorem eval_expansion {m : ℕ} (z : Fin m → Circle) (a : ℂ) :
    (phasePolynomial z).eval a = ∑ n ∈ Finset.range (m + 1),
      (-1 : ℂ) ^ n * (elem z n * a ^ (m - n)) := by
  rw [polynomial_expansion, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro n _
  simp

theorem eval_difference {m : ℕ} (z w : Fin m → Circle) (a : ℂ) :
    (phasePolynomial w).eval a - (phasePolynomial z).eval a =
      ∑ n ∈ Finset.range m,
        (-1 : ℂ) ^ (n+1) * ((elem w (n+1) - elem z (n+1)) * a ^ (m-(n+1))) := by
  rw [eval_expansion, eval_expansion, ← Finset.sum_sub_distrib,
    Finset.sum_range_succ']
  simp only [pow_zero, elem_zero, one_mul, sub_self, add_zero]
  apply Finset.sum_congr rfl
  intro n _
  ring

theorem eval_difference_bound {m : ℕ} (z w : Fin m → Circle) (a : Circle) :
    ‖(phasePolynomial w).eval (a : ℂ) - (phasePolynomial z).eval (a : ℂ)‖ ≤
      m * dist (encoding z) (encoding w) := by
  rw [eval_difference]
  calc
    _ ≤ ∑ n ∈ Finset.range m,
      ‖(-1 : ℂ) ^ (n+1) * ((elem w (n+1) - elem z (n+1)) * (a : ℂ) ^ (m-(n+1)))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.range m, dist (encoding z) (encoding w) := by
      apply Finset.sum_le_sum
      intro n hn
      simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, Circle.norm_coe,
        one_mul, mul_one]
      have h := dist_le_pi_dist (encoding z) (encoding w) ⟨n, Finset.mem_range.mp hn⟩
      simpa only [dist_eq_norm, encoding, norm_sub_rev] using h
    _ = _ := by simp

theorem close_encoding_each_phase {m : ℕ} (hm : 0 < m)
    (z w : Fin m → Circle) {ρ : ℝ} (hρ : 0 < ρ)
    (hzw : dist (encoding z) (encoding w) < ρ ^ m / m) :
    ∀ i, ∃ j, dist (z i : ℂ) (w j : ℂ) < ρ := by
  intro i
  by_contra h
  push Not at h
  have hl : ρ ^ m ≤ ‖(phasePolynomial w).eval (z i : ℂ)‖ := by
    rw [phasePolynomial, Polynomial.eval_prod]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    rw [norm_prod]
    calc
      ρ ^ m = ∏ _j : Fin m, ρ := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => hρ.le) (fun j _ => by
        simpa only [dist_eq_norm] using h j)
  have hu := eval_difference_bound z w (z i)
  rw [eval_at_phase, sub_zero] at hu
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hb : (m : ℝ) * dist (encoding z) (encoding w) < ρ ^ m := by
    simpa only [mul_comm] using (lt_div_iff₀ hm').mp hzw
  exact (not_lt_of_ge (hl.trans hu)) hb

open scoped BigOperators

private def fromPowers (p : ℕ → ℂ) (n : ℕ) : ℂ :=
  match n with
  | 0 => 1
  | k + 1 => (k + 1 : ℂ)⁻¹ * (-1) ^ (k + 2) *
      ∑ i : Fin (k + 1), (-1) ^ (i : ℕ) * fromPowers p i * p (k + 1 - i)
termination_by n
decreasing_by
  exact i.isLt

lemma measurable_fromPowers {Y : Type*} [MeasurableSpace Y] (p : Y → ℕ → ℂ)
    (hp : ∀ n, Measurable (fun y => p y n)) (n : ℕ) :
    Measurable (fun y => fromPowers (p y) n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp only [fromPowers]; exact measurable_const
    | succ k =>
      simp only [fromPowers]
      apply Measurable.const_mul
      apply Finset.measurable_sum
      intro i _
      exact (Measurable.const_mul (ih i i.isLt) _).mul (hp _)

lemma newton_elem {m : ℕ} (z : Fin m → Circle) (k : ℕ) :
    (k : ℂ) * elem z k = (-1) ^ (k + 1) *
      ∑ a ∈ (Finset.HasAntidiagonal.antidiagonal k).filter (fun a => a.1 < k),
        (-1) ^ a.1 * elem z a.1 * (∑ i, (z i : ℂ) ^ a.2) := by
  have h := congrArg (MvPolynomial.aeval (fun i => (z i : ℂ)))
    (MvPolynomial.mul_esymm_eq_sum (Fin m) ℂ k)
  simpa only [map_mul, map_natCast, map_pow, map_neg, map_one, map_sum,
    MvPolynomial.aeval_esymm_eq_multiset_esymm, MvPolynomial.psum, MvPolynomial.aeval_X,
    elem, phases] using h

lemma filtered_antidiagonal_sum (f : ℕ → ℕ → ℂ) (k : ℕ) :
    (∑ a ∈ (Finset.HasAntidiagonal.antidiagonal (k+1)).filter (fun a => a.1 < k+1), f a.1 a.2) =
      ∑ i : Fin (k+1), f i (k+1-i) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => f i (k+1-i)) (k+1), Finset.sum_filter, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ]
  simp only [lt_self_iff_false, ↓reduceIte, add_zero]
  apply Finset.sum_congr rfl
  intro i hi
  simp [Finset.mem_range.mp hi]

theorem fromPowers_eq_elem {m : ℕ} (z : Fin m → Circle) (n : ℕ) :
    fromPowers (fun k => ∑ i, (z i : ℂ) ^ k) n = elem z n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [fromPowers]
    | succ k =>
      rw [fromPowers]
      have hs : (∑ i : Fin (k+1), (-1 : ℂ)^(i : ℕ) *
          fromPowers (fun n => ∑ j, (z j : ℂ)^n) i * (∑ j, (z j : ℂ)^(k+1-i))) =
          ∑ i : Fin (k+1), (-1 : ℂ)^(i : ℕ) * elem z i *
            (∑ j, (z j : ℂ)^(k+1-i)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [ih i i.isLt]
      rw [hs, mul_assoc, ← filtered_antidiagonal_sum
        (fun i j => (-1 : ℂ)^i * elem z i * (∑ l, (z l : ℂ)^j)) k]
      have hn := newton_elem z (k+1)
      rw [Nat.cast_add, Nat.cast_one] at hn
      rw [← hn, inv_mul_cancel_left₀]
      exact_mod_cast (Nat.succ_ne_zero k)

end

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

variable {Y G : Type*} [MeasurableSpace Y] [MeasurableSpace G]

private def kernelEncoding (β : Kernel Y G) (χ : G → ℂ) (m : ℕ) (y : Y) : Fin m → ℂ :=
  fun i => fromPowers (fun n => (m : ℂ) * ∫ d, χ d ^ n ∂β y) (i.val + 1)

theorem measurable_kernelEncoding (β : Kernel Y G) [IsMarkovKernel β]
    (χ : G → ℂ) (hχ : Measurable χ) (m : ℕ) :
    Measurable (kernelEncoding β χ m) := by
  apply measurable_pi_iff.mpr
  intro i
  apply measurable_fromPowers
  intro n
  exact (((hχ.pow_const n).stronglyMeasurable.integral_kernel).measurable).const_mul _

theorem moments_uniform_list [MeasurableSingletonClass G] (χ : G → ℂ) (m : ℕ) (hm : 0 < m) (g : Fin m → G)
    (μ : Measure G) (hμ : μ = (m : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (g i))
    (n : ℕ) :
    (m : ℂ) * (∫ d, χ d ^ n ∂μ) = ∑ i, χ (g i) ^ n := by
  classical
  rw [hμ, integral_smul_measure, integral_finsetSum_measure]
  · simp only [integral_dirac, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast]
    rw [← mul_assoc, mul_inv_cancel₀, one_mul]
    exact_mod_cast hm.ne'
  · intro i _
    exact integrable_dirac (by simp)

theorem kernelEncoding_eq_encoding [MeasurableSingletonClass G] (β : Kernel Y G) (χ : G → Circle)
    (m : ℕ) (hm : 0 < m) (y : Y) (g : Fin m → G)
    (hβ : β y = (m : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (g i)) :
    kernelEncoding β (fun d => (χ d : ℂ)) m y = encoding (fun i => χ (g i)) := by
  have hp : (fun n => (m : ℂ) * ∫ d, (χ d : ℂ)^n ∂β y) =
      fun n => ∑ i, (χ (g i) : ℂ)^n := by
    funext n
    exact moments_uniform_list (fun d => (χ d : ℂ)) m hm g (β y) hβ n
  funext i
  change fromPowers _ (i.val+1) = elem _ (i.val+1)
  rw [hp]
  exact fromPowers_eq_elem (fun i => χ (g i)) (i.val+1)

end

theorem exists_encoding_bound (m : ℕ) :
    ∃ B : ℝ, ∀ z : Fin m → Circle, ‖encoding z‖ ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_range (continuous_encoding (m := m))).isBounded.exists_norm_le
  exact ⟨B, fun z => hB _ ⟨z, rfl⟩⟩
end EuclideanFiveColor.PhaseEncoding

end

end ParishFactor
end

-- OAI.Analysis.PlaneSpectrum.PhaseCollision
section
namespace ParishFactor

noncomputable section

open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate

open scoped BigOperators
namespace EuclideanFiveColor.PhaseCollision

section

variable {ι κ V : Type*} [Fintype ι] [Fintype κ]
local instance : DecidableEq ι := Classical.decEq ι
local instance : DecidableEq κ := Classical.decEq κ

private def repeatedPairs (s : Finset ι) (f : ι → κ) : Finset (ι × ι) := by
  classical
  exact (s ×ˢ s).filter (fun p => p.1 ≠ p.2 ∧ f p.1 = f p.2)

omit [Fintype ι] in
lemma sameBin_card (s : Finset ι) (f : ι → κ) :
    ((s ×ˢ s).filter (fun p => f p.1 = f p.2)).card =
      ∑ b : κ, (s.filter (fun i => f i = b)).card ^ 2 := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := fun p : ι × ι => f p.1)
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro b _
  have he : (((s ×ˢ s).filter (fun p => f p.1 = f p.2)).filter
      (fun p => f p.1 = b)) =
      (s.filter (fun i => f i = b)) ×ˢ (s.filter (fun i => f i = b)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_product]
    aesop
  rw [he, Finset.card_product, pow_two]

omit [Fintype ι] [Fintype κ] in
lemma sameBin_card_eq (s : Finset ι) (f : ι → κ) :
    ((s ×ˢ s).filter (fun p => f p.1 = f p.2)).card =
      (repeatedPairs s f).card + s.card := by
  classical
  let T := (s ×ˢ s).filter (fun p => f p.1 = f p.2)
  have hsplit := Finset.card_filter_add_card_filter_not (s := T)
    (p := fun p => p.1 ≠ p.2)
  have hfirst : T.filter (fun p => p.1 ≠ p.2) = repeatedPairs s f := by
    ext p
    simp only [T, repeatedPairs, Finset.mem_filter, Finset.mem_product]
    tauto
  have hsecond : T.filter (fun p => ¬p.1 ≠ p.2) = s.diag := by
    ext p
    simp only [T, Finset.mem_filter, Finset.mem_product, not_not, Finset.mem_diag]
    aesop
  rw [hfirst, hsecond, Finset.diag_card] at hsplit
  exact hsplit.symm

omit [Fintype ι] in
theorem repeated_bin_lower_bound (s : Finset ι) (f : ι → κ) :
    (s.card : ℝ) ^ 2 ≤ (Fintype.card κ : ℝ) *
      ((repeatedPairs s f).card + (s.card : ℝ)) := by
  classical
  have hs : ∑ b : κ, (s.filter (fun i => f i = b)).card = s.card := by
    symm
    exact Finset.card_eq_sum_card_fiberwise (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
  have hs' : ∑ b : κ, ((s.filter (fun i => f i = b)).card : ℝ) = s.card := by
    exact_mod_cast hs
  have hpair : ∑ b : κ, ((s.filter (fun i => f i = b)).card : ℝ) ^ 2 =
      (repeatedPairs s f).card + (s.card : ℝ) := by
    exact_mod_cast (sameBin_card s f).symm.trans (sameBin_card_eq s f)
  simpa only [hs', hpair, Finset.card_univ] using
    (sq_sum_le_card_mul_sum_sq (s := Finset.univ)
      (f := fun b : κ => ((s.filter (fun i => f i = b)).card : ℝ)))

variable [PseudoMetricSpace V]

private def closePairs (v : ι → V) (r : ℝ) : Finset (ι × ι) := by
  classical
  exact Finset.univ.filter (fun p => p.1 ≠ p.2 ∧ dist (v p.1) (v p.2) ≤ r)

theorem close_pair_lower_bound (s : Finset ι) (f : ι → κ)
    (v : ι → V) (w : κ → V) (r : ℝ)
    (h : ∀ i ∈ s, dist (v i) (w (f i)) ≤ r) :
    (s.card : ℝ) ^ 2 ≤ (Fintype.card κ : ℝ) *
      ((closePairs v (2 * r)).card + (Fintype.card ι : ℝ)) := by
  classical
  have hsub : repeatedPairs s f ⊆ closePairs v (2 * r) := by
    intro p hp
    simp only [repeatedPairs, Finset.mem_filter, Finset.mem_product] at hp
    simp only [closePairs, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hp.2.1, ?_⟩
    calc
      dist (v p.1) (v p.2) ≤ dist (v p.1) (w (f p.1)) +
          dist (w (f p.1)) (v p.2) := dist_triangle _ _ _
      _ ≤ r + r := by
        apply add_le_add (h p.1 hp.1.1)
        rw [hp.2.2, dist_comm]
        exact h p.2 hp.1.2
      _ = 2 * r := by ring
  calc
    _ ≤ (Fintype.card κ : ℝ) * ((repeatedPairs s f).card + (s.card : ℝ)) :=
      repeated_bin_lower_bound s f
    _ ≤ _ := by
      exact mul_le_mul_of_nonneg_left (add_le_add
        (Nat.cast_le.mpr (Finset.card_le_card hsub))
        (Nat.cast_le.mpr (Finset.card_le_univ s))) (Nat.cast_nonneg _)

theorem normalized_close_pair_lower_bound [Nonempty ι] [Nonempty κ]
    (s : Finset ι) (f : ι → κ) (v : ι → V) (w : κ → V) (r : ℝ)
    (h : ∀ i ∈ s, dist (v i) (w (f i)) ≤ r) :
    ((s.card : ℝ) / Fintype.card ι) ^ 2 / Fintype.card κ - 1 / Fintype.card ι ≤
      (closePairs v (2 * r)).card / (Fintype.card ι : ℝ) ^ 2 := by
  have hn : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hm : (0 : ℝ) < Fintype.card κ := Nat.cast_pos.mpr Fintype.card_pos
  have hc := close_pair_lower_bound s f v w r h
  apply (le_div_iff₀ (sq_pos_of_pos hn)).mpr
  field_simp
  nlinarith

end

open MeasureTheory
open scoped BigOperators

variable {Ω ι κ V : Type*} [MeasurableSpace Ω]
variable [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ] [PseudoMetricSpace V]

theorem average_cover_forces_collision (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s : Ω → Finset ι) (f : Ω → ι → κ) (v : Ω → ι → V) (w : Ω → κ → V)
    (r : ℝ)
    (hcov : ∀ᵐ x ∂μ, ∀ i ∈ s x, dist (v x i) (w x (f x i)) ≤ r)
    (hm : ∀ i j, Measurable (fun x => dist (v x i) (v x j)))
    (hq : Measurable (fun x => ((s x).card : ℝ) / Fintype.card ι))
    (hlarge : 10 * Fintype.card κ < Fintype.card ι)
    (havg : (19/20 : ℝ) < ∫ x, ((s x).card : ℝ) / Fintype.card ι ∂μ) :
    ∃ i j : ι, i ≠ j ∧
      1 / (4 * (Fintype.card κ : ℝ)) ≤ μ.real {x | dist (v x i) (v x j) ≤ 2*r} := by
  classical
  let n : ℝ := Fintype.card ι
  let k : ℝ := Fintype.card κ
  have hn : 0 < n := Nat.cast_pos.mpr Fintype.card_pos
  have hk : 0 < k := Nat.cast_pos.mpr Fintype.card_pos
  have hlarge' : 10*k < n := by dsimp [k, n]; exact_mod_cast hlarge
  let q : Ω → ℝ := fun x => (s x).card / n
  have hq0 (x) : 0 ≤ q x := div_nonneg (Nat.cast_nonneg _) hn.le
  have hq1 (x) : q x ≤ 1 := by
    apply (div_le_one hn).mpr
    dsimp [n]
    exact_mod_cast Finset.card_le_univ (s x)
  have hiq : Integrable q μ := Integrable.of_bound hq.aestronglyMeasurable 1
    (Filter.Eventually.of_forall (fun x => by rw [Real.norm_of_nonneg (hq0 x)]; exact hq1 x))
  have hiq2 : Integrable (fun x => (q x)^2) μ := Integrable.of_bound
    (hq.pow_const 2).aestronglyMeasurable 1 (Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_one₀ (hq0 x) (hq1 x)))
  have hsq : (19/20 : ℝ)^2 < ∫ x, (q x)^2 ∂μ := by
    have hv : 0 ≤ ∫ x, (q x-19/20)^2 ∂μ :=
      integral_nonneg (fun x => sq_nonneg (q x - 19/20))
    have he : (fun x => (q x-19/20)^2) =
        (fun x => (q x)^2 - (19/10)*q x + (19/20)^2) := by funext x; ring
    have hsub : Integrable (fun x => (q x)^2 - (19/10)*q x) μ :=
      hiq2.sub (hiq.const_mul (19/10))
    rw [he, integral_add hsub (integrable_const ((19/20 : ℝ)^2)),
      integral_sub hiq2 (hiq.const_mul (19/10)), integral_const_mul] at hv
    simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one,
      smul_eq_mul, one_mul] at hv
    change 19/20 < ∫ x, q x ∂μ at havg
    linarith
  let a : (ι × ι) → Ω → ℝ := fun p x =>
    if p.1 ≠ p.2 ∧ dist (v x p.1) (v x p.2) ≤ 2*r then 1 else 0
  have hma (p : ι × ι) : Measurable (a p) := by
    have hset : MeasurableSet {x | p.1 ≠ p.2 ∧ dist (v x p.1) (v x p.2) ≤ 2*r} := by
      by_cases h : p.1 = p.2
      · simp [h]
      · simpa [h] using
          (measurableSet_le (hm p.1 p.2) (measurable_const (a := 2*r)))
    exact measurable_const.ite hset measurable_const
  have hia (p : ι × ι) : Integrable (a p) μ := Integrable.of_bound
    (hma p).aestronglyMeasurable 1 (Filter.Eventually.of_forall (fun x => by
      dsimp [a]; split_ifs <;> norm_num))
  have hcnt (x : Ω) : ((closePairs (v x) (2*r)).card : ℝ) = ∑ p, a p x := by
    simp only [closePairs, a, Finset.cast_card, Finset.sum_filter]
  have hic : Integrable (fun x => ((closePairs (v x) (2*r)).card : ℝ)/n^2) μ := by
    simp_rw [hcnt]
    exact (integrable_finsetSum _ (fun p _ => hia p)).div_const _
  have hlow := integral_mono_ae (μ := μ) ((hiq2.div_const k).sub (integrable_const (1/n))) hic
    (hcov.mono (fun x hx =>
      normalized_close_pair_lower_bound (s x) (f x) (v x) (w x) r hx))
  simp only [Pi.sub_apply] at hlow
  rw [integral_sub (hiq2.div_const k) (integrable_const (1/n)), integral_div,
    integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul] at hlow
  have hstrict : 1/(4*k) < (∫ x, (q x)^2 ∂μ)/k - 1/n := by
    have hi : 1/n < 1/(10*k) := one_div_lt_one_div_of_lt (by positivity) hlarge'
    have hsq' := (div_lt_div_iff_of_pos_right hk).mpr hsq
    apply lt_of_lt_of_le _ (le_of_lt (sub_lt_sub hsq' hi))
    field_simp
    norm_num
  by_contra hh
  push Not at hh
  have hailt (p : ι × ι) : ∫ x, a p x ∂μ < 1/(4*k) := by
    by_cases hp : p.1 = p.2
    · simp only [a, hp, ne_eq, not_true_eq_false, false_and, ↓reduceIte, integral_zero]
      positivity
    · have he : a p = Set.indicator {x | dist (v x p.1) (v x p.2) ≤ 2*r}
          (fun _ => (1 : ℝ)) := by
        funext x
        simp [a, hp, Set.indicator_apply]
      rw [he, integral_indicator (measurableSet_le (hm p.1 p.2) measurable_const)]
      simpa only [setIntegral_const, Measure.real, smul_eq_mul, mul_one] using hh p.1 p.2 hp
  have hiupper : (∫ x, ((closePairs (v x) (2*r)).card : ℝ)/n^2 ∂μ) < 1/(4*k) := by
    simp_rw [hcnt]
    rw [integral_div, integral_finsetSum _ (fun p _ => hia p)]
    have hsum := Finset.sum_lt_sum_of_nonempty (s := (Finset.univ : Finset (ι × ι)))
      Finset.univ_nonempty (fun p _ => hailt p)
    have hnum : (∑ _p : ι × ι, 1/(4*k)) = n^2/(4*k) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul,
        Nat.cast_mul, n, pow_two, mul_div_assoc]
      ring
    rw [hnum] at hsum
    apply (div_lt_iff₀ (sq_pos_of_pos hn)).mpr
    convert hsum using 1
    ring
  exact (not_lt_of_ge (hstrict.le.trans hlow)) hiupper

end EuclideanFiveColor.PhaseCollision

open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators
open Polynomial

open MeasureTheory
open scoped BigOperators
namespace EuclideanFiveColor.AverageErrors
variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]

private def goodFraction (e : ι → Ω → ℝ) (t : ℝ) (x : Ω) : ℝ := by
  classical
  exact ((Finset.univ.filter (fun i => e i x < t)).card : ℝ) / Fintype.card ι

omit [MeasurableSpace Ω] [Nonempty ι] in
lemma goodFraction_eq_sum (e : ι → Ω → ℝ) (t : ℝ) (x : Ω) :
    goodFraction e t x = (∑ i, if e i x < t then (1 : ℝ) else 0) / Fintype.card ι := by
  classical
  simp only [goodFraction, Finset.cast_card, Finset.sum_filter]

omit [Nonempty ι] in
lemma measurable_goodFraction (e : ι → Ω → ℝ) (t : ℝ)
    (he : ∀ i, Measurable (e i)) : Measurable (goodFraction e t) := by
  classical
  change Measurable (fun x => goodFraction e t x)
  simp_rw [goodFraction_eq_sum]
  exact (Finset.measurable_sum _ (fun i _ => measurable_const.ite
    (measurableSet_lt (he i) measurable_const) measurable_const)).div_const _

omit [MeasurableSpace Ω] [Nonempty ι] in
lemma goodFraction_nonneg (e : ι → Ω → ℝ) (t : ℝ) (x : Ω) :
    0 ≤ goodFraction e t x := by unfold goodFraction; positivity

omit [MeasurableSpace Ω] in
lemma goodFraction_le_one (e : ι → Ω → ℝ) (t : ℝ) (x : Ω) :
    goodFraction e t x ≤ 1 := by
  classical
  apply (div_le_one (Nat.cast_pos.mpr Fintype.card_pos)).mpr
  exact_mod_cast Finset.card_le_univ (Finset.univ.filter (fun i => e i x < t))

lemma integrable_goodFraction (μ : Measure Ω) [IsFiniteMeasure μ]
    (e : ι → Ω → ℝ) (t : ℝ) (he : ∀ i, Measurable (e i)) :
    Integrable (goodFraction e t) μ :=
  Integrable.of_bound (measurable_goodFraction e t he).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (goodFraction_nonneg e t x)]
      exact goodFraction_le_one e t x)

theorem average_goodFraction (μ : Measure Ω) [IsProbabilityMeasure μ]
    (e : ι → Ω → ℝ) (t : ℝ) (ht : 0 < t)
    (he : ∀ i, Measurable (e i)) (hi : ∀ i, Integrable (e i) μ)
    (hn : ∀ᵐ x ∂μ, ∀ i, 0 ≤ e i x)
    (havg : ∀ i, ∫ x, e i x ∂μ < t/20) :
    (19/20 : ℝ) < ∫ x, goodFraction e t x ∂μ := by
  classical
  let n : ℝ := Fintype.card ι
  have hnpos : 0 < n := Nat.cast_pos.mpr Fintype.card_pos
  have hpoint : ∀ᵐ x ∂μ,
      1 - (∑ i, e i x) / (n*t) ≤ goodFraction e t x := by
    filter_upwards [hn] with x hx
    have hi' (i) : 1 - e i x / t ≤ if e i x < t then (1 : ℝ) else 0 := by
      split_ifs with h
      · have : 0 ≤ e i x / t := div_nonneg (hx i) ht.le
        linarith
      · have : 1 ≤ e i x / t := (le_div_iff₀ ht).mpr (by simpa using le_of_not_gt h)
        linarith
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi' i)
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one, ← Finset.sum_div] at hs
    rw [goodFraction_eq_sum]
    apply (le_div_iff₀ hnpos).mpr
    have heq : (1 - (∑ i, e i x)/(n*t))*n = n - (∑ i, e i x)/t := by
      field_simp
    rw [heq]
    exact hs
  have hil : Integrable (fun x => 1 - (∑ i, e i x)/(n*t)) μ :=
    (integrable_const 1).sub ((integrable_finsetSum _ (fun i _ => hi i)).div_const _)
  have hlow := integral_mono_ae hil (integrable_goodFraction μ e t he) hpoint
  rw [integral_sub (integrable_const 1) ((integrable_finsetSum _ (fun i _ => hi i)).div_const _),
    integral_div, integral_finsetSum _ (fun i _ => hi i)] at hlow
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hlow
  have hu := Finset.sum_lt_sum_of_nonempty (s := (Finset.univ : Finset ι))
    Finset.univ_nonempty (fun i _ => havg i)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hu
  have hr : (∑ i, ∫ x, e i x ∂μ) / (n*t) < 1/20 := by
    apply (div_lt_iff₀ (mul_pos hnpos ht)).mpr
    convert hu using 1
    dsimp [n]
    ring
  linarith

end EuclideanFiveColor.AverageErrors

namespace EuclideanFiveColor.PhaseCollision
open MeasureTheory
open scoped BigOperators

variable {Ω ι κ V : Type*} [MeasurableSpace Ω]
variable [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ] [PseudoMetricSpace V]

theorem average_exists_cover_forces_collision (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s : Ω → Finset ι) (v : Ω → ι → V) (w : Ω → κ → V) (r : ℝ)
    (hcov : ∀ᵐ x ∂μ, ∀ i ∈ s x, ∃ j, dist (v x i) (w x j) ≤ r)
    (hm : ∀ i j, Measurable (fun x => dist (v x i) (v x j)))
    (hq : Measurable (fun x => ((s x).card : ℝ) / Fintype.card ι))
    (hlarge : 10 * Fintype.card κ < Fintype.card ι)
    (havg : (19/20 : ℝ) < ∫ x, ((s x).card : ℝ) / Fintype.card ι ∂μ) :
    ∃ i j : ι, i ≠ j ∧
      1 / (4 * (Fintype.card κ : ℝ)) ≤ μ.real {x | dist (v x i) (v x j) ≤ 2*r} := by
  classical
  let f : Ω → ι → κ := fun x i =>
    if h : ∃ j, dist (v x i) (w x j) ≤ r then h.choose else Classical.choice inferInstance
  apply average_cover_forces_collision μ s f v w r _ hm hq hlarge havg
  filter_upwards [hcov] with x hx
  intro i hi
  dsimp [f]
  rw [dif_pos (hx i hi)]
  exact (hx i hi).choose_spec

omit [MeasurableSpace Ω] [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]
  [PseudoMetricSpace V] in
lemma circle_product_dist (a b c d : Circle) :
    dist ((a : ℂ)*(b : ℂ)) ((c : ℂ)*(d : ℂ)) ≤
      dist (a : ℂ) (c : ℂ) + dist (b : ℂ) (d : ℂ) := by
  simp only [dist_eq_norm]
  have he : (a : ℂ)*(b : ℂ)-(c : ℂ)*(d : ℂ) =
      ((a : ℂ)-(c : ℂ))*(b : ℂ) + (c : ℂ)*((b : ℂ)-(d : ℂ)) := by ring
  rw [he]
  simpa only [norm_mul, Circle.norm_coe, mul_one, one_mul] using
    norm_add_le (((a : ℂ)-(c : ℂ))*(b : ℂ)) ((c : ℂ)*((b : ℂ)-(d : ℂ)))

end EuclideanFiveColor.PhaseCollision

namespace EuclideanFiveColor.EncodedCollision
local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩
open MeasureTheory
open scoped BigOperators
open PhaseEncoding AverageErrors PhaseCollision
variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]

theorem collision_from_close_encodings (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : ℕ) (hm : 0 < m) (ρ : ℝ) (hρ : 0 < ρ)
    (zp zm : Ω → ι → Fin m → Circle) (ap am : ι → Ω → Circle) (j₀ : ι)
    (hap : ∀ j, Measurable (ap j)) (ham : ∀ j, Measurable (am j))
    (hDp : ∀ j, Measurable (fun x => dist (encoding (zp x j)) (encoding (zp x j₀))))
    (hDm : ∀ j, Measurable (fun x => dist (encoding (zm x j)) (encoding (zm x j₀))))
    (hmem : ∀ᵐ x ∂μ, ∀ j, (∃ r, ap j x = zp x j r) ∧ (∃ r, am j x = zm x j r))
    (hi : ∀ j, Integrable (fun x =>
       dist (encoding (zp x j)) (encoding (zp x j₀))^2 +
       dist (encoding (zm x j)) (encoding (zm x j₀))^2) μ)
    (he : ∀ j, (∫ x,
       dist (encoding (zp x j)) (encoding (zp x j₀))^2 +
       dist (encoding (zm x j)) (encoding (zm x j₀))^2 ∂μ) <
       (ρ^m / m)^2 / 20)
    (hlarge : 10 * m^2 < Fintype.card ι) :
    ∃ i j : ι, i ≠ j ∧ 1/(4*(m : ℝ)^2) ≤ μ.real {x |
      dist ((ap i x : ℂ)*(am i x : ℂ)) ((ap j x : ℂ)*(am j x : ℂ)) ≤ 4*ρ} := by
  classical
  let δ : ℝ := ρ^m / m
  have hδ : 0 < δ := div_pos (pow_pos hρ _) (Nat.cast_pos.mpr hm)
  let e : ι → Ω → ℝ := fun j x =>
    dist (encoding (zp x j)) (encoding (zp x j₀))^2 +
    dist (encoding (zm x j)) (encoding (zm x j₀))^2
  have hem (i) : Measurable (e i) :=
    (hDp i |>.pow_const 2).add (hDm i |>.pow_const 2)
  have hen (x) (i) : 0 ≤ e i x := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have havg := average_goodFraction μ e (δ^2) (sq_pos_of_pos hδ) hem hi
    (Filter.Eventually.of_forall hen) he
  let s : Ω → Finset ι := fun x => Finset.univ.filter (fun i => e i x < δ^2)
  let v : Ω → ι → ℂ := fun x i => (ap i x : ℂ)*(am i x : ℂ)
  let w : Ω → (Fin m × Fin m) → ℂ := fun x p =>
    (zp x j₀ p.1 : ℂ)*(zm x j₀ p.2 : ℂ)
  have hcover : ∀ᵐ x ∂μ, ∀ i ∈ s x, ∃ p, dist (v x i) (w x p) ≤ 2*ρ := by
    filter_upwards [hmem] with x hx
    intro i hi'
    have hie : e i x < δ^2 := (Finset.mem_filter.mp hi').2
    have hp : dist (encoding (zp x i)) (encoding (zp x j₀)) < δ := by
      dsimp [e] at hie
      nlinarith [sq_nonneg (dist (encoding (zm x i)) (encoding (zm x j₀))), dist_nonneg
        (x := encoding (zp x i)) (y := encoding (zp x j₀))]
    have hm' : dist (encoding (zm x i)) (encoding (zm x j₀)) < δ := by
      dsimp [e] at hie
      nlinarith [sq_nonneg (dist (encoding (zp x i)) (encoding (zp x j₀))), dist_nonneg
        (x := encoding (zm x i)) (y := encoding (zm x j₀))]
    obtain ⟨⟨rp, hrp⟩, ⟨rm, hrm⟩⟩ := hx i
    obtain ⟨cp, hcp⟩ := close_encoding_each_phase hm (zp x i) (zp x j₀) hρ hp rp
    obtain ⟨cm, hcm⟩ := close_encoding_each_phase hm (zm x i) (zm x j₀) hρ hm' rm
    refine ⟨(cp, cm), ?_⟩
    dsimp [v, w]
    rw [hrp, hrm]
    exact (circle_product_dist _ _ _ _).trans (by linarith)
  let : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hv' (i j) : Measurable (fun x => dist (v x i) (v x j)) := by
    have hco : Continuous (fun z : Circle => (z : ℂ)) := continuous_subtype_val
    have hvm (i) : Measurable (fun x => v x i) :=
      (hco.measurable.comp (hap i)).mul (hco.measurable.comp (ham i))
    exact (hvm i).dist (hvm j)
  obtain ⟨i, j, hij, hc⟩ := average_exists_cover_forces_collision μ s v w (2*ρ)
    hcover hv' (measurable_goodFraction e (δ^2) hem)
    (by simpa only [Fintype.card_prod, Fintype.card_fin, pow_two] using hlarge) havg
  refine ⟨i, j, hij, ?_⟩
  simpa only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, pow_two,
    v, show 2*(2*ρ)=4*ρ by ring] using hc

theorem collision_from_measurable_encodings (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : ℕ) (hm : 0 < m) (ρ : ℝ) (hρ : 0 < ρ)
    (zp zm : Ω → ι → Fin m → Circle) (ap am : ι → Ω → Circle) (j₀ : ι)
    (Hp Hm : ι → Ω → Fin m → ℂ)
    (henc : ∀ᵐ x ∂μ, ∀ j, encoding (zp x j) = Hp j x ∧ encoding (zm x j) = Hm j x)
    (hap : ∀ j, Measurable (ap j)) (ham : ∀ j, Measurable (am j))
    (hDp : ∀ j, Measurable (fun x => dist (Hp j x) (Hp j₀ x)))
    (hDm : ∀ j, Measurable (fun x => dist (Hm j x) (Hm j₀ x)))
    (hmem : ∀ᵐ x ∂μ, ∀ j, (∃ r, ap j x = zp x j r) ∧ (∃ r, am j x = zm x j r))
    (hi : ∀ j, Integrable (fun x =>
       dist (Hp j x) (Hp j₀ x)^2 +
       dist (Hm j x) (Hm j₀ x)^2) μ)
    (he : ∀ j, (∫ x,
       dist (Hp j x) (Hp j₀ x)^2 +
       dist (Hm j x) (Hm j₀ x)^2 ∂μ) <
       (ρ^m / m)^2 / 20)
    (hlarge : 10 * m^2 < Fintype.card ι) :
    ∃ i j : ι, i ≠ j ∧ 1/(4*(m : ℝ)^2) ≤ μ.real {x |
      dist ((ap i x : ℂ)*(am i x : ℂ)) ((ap j x : ℂ)*(am j x : ℂ)) ≤ 4*ρ} := by
  classical
  let δ : ℝ := ρ^m / m
  have hδ : 0 < δ := div_pos (pow_pos hρ _) (Nat.cast_pos.mpr hm)
  let e : ι → Ω → ℝ := fun j x =>
    dist (Hp j x) (Hp j₀ x)^2 +
    dist (Hm j x) (Hm j₀ x)^2
  have hem (i) : Measurable (e i) :=
    (hDp i |>.pow_const 2).add (hDm i |>.pow_const 2)
  have hen (x) (i) : 0 ≤ e i x := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have havg := average_goodFraction μ e (δ^2) (sq_pos_of_pos hδ) hem hi
    (Filter.Eventually.of_forall hen) he
  let s : Ω → Finset ι := fun x => Finset.univ.filter (fun i => e i x < δ^2)
  let v : Ω → ι → ℂ := fun x i => (ap i x : ℂ)*(am i x : ℂ)
  let w : Ω → (Fin m × Fin m) → ℂ := fun x p =>
    (zp x j₀ p.1 : ℂ)*(zm x j₀ p.2 : ℂ)
  have hcover : ∀ᵐ x ∂μ, ∀ i ∈ s x, ∃ p, dist (v x i) (w x p) ≤ 2*ρ := by
    filter_upwards [hmem, henc] with x hx hxe
    intro i hi'
    have hie : e i x < δ^2 := (Finset.mem_filter.mp hi').2
    have hp : dist (Hp i x) (Hp j₀ x) < δ := by
      dsimp [e] at hie
      nlinarith [sq_nonneg (dist (Hm i x) (Hm j₀ x)), dist_nonneg
        (x := Hp i x) (y := Hp j₀ x)]
    have hm' : dist (Hm i x) (Hm j₀ x) < δ := by
      dsimp [e] at hie
      nlinarith [sq_nonneg (dist (Hp i x) (Hp j₀ x)), dist_nonneg
        (x := Hm i x) (y := Hm j₀ x)]
    have hp' : dist (encoding (zp x i)) (encoding (zp x j₀)) < δ := by
      rw [(hxe i).1, (hxe j₀).1]; exact hp
    have hm'' : dist (encoding (zm x i)) (encoding (zm x j₀)) < δ := by
      rw [(hxe i).2, (hxe j₀).2]; exact hm'
    obtain ⟨⟨rp, hrp⟩, ⟨rm, hrm⟩⟩ := hx i
    obtain ⟨cp, hcp⟩ := close_encoding_each_phase hm (zp x i) (zp x j₀) hρ hp' rp
    obtain ⟨cm, hcm⟩ := close_encoding_each_phase hm (zm x i) (zm x j₀) hρ hm'' rm
    refine ⟨(cp, cm), ?_⟩
    dsimp [v, w]
    rw [hrp, hrm]
    exact (circle_product_dist _ _ _ _).trans (by linarith)
  let : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hv' (i j) : Measurable (fun x => dist (v x i) (v x j)) := by
    have hco : Continuous (fun z : Circle => (z : ℂ)) := continuous_subtype_val
    have hvm (i) : Measurable (fun x => v x i) :=
      (hco.measurable.comp (hap i)).mul (hco.measurable.comp (ham i))
    exact (hvm i).dist (hvm j)
  obtain ⟨i, j, hij, hc⟩ := average_exists_cover_forces_collision μ s v w (2*ρ)
    hcover hv' (measurable_goodFraction e (δ^2) hem)
    (by simpa only [Fintype.card_prod, Fintype.card_fin, pow_two] using hlarge) havg
  refine ⟨i, j, hij, ?_⟩
  simpa only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, pow_two,
    v, show 2*(2*ρ)=4*ρ by ring] using hc

end EuclideanFiveColor.EncodedCollision

end

end ParishFactor
end

-- OAI.MeasureTheory.CompactFactors.ConditionalSelection
section
namespace ParishFactor

noncomputable section

open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators
open Polynomial
open MeasureTheory
open scoped BigOperators

open MeasureTheory
open scoped BigOperators
namespace EuclideanFiveColor.GoodFiber

variable {W ι T : Type*} [MeasurableSpace W] [Fintype ι] [Nonempty ι] [Fintype T]

omit [Fintype ι] [Nonempty ι] [Fintype T] in
theorem exists_lt_on_conull (μ : Measure W) [IsProbabilityMeasure μ]
    (g : W → ℝ) (hg : Integrable g μ) (havg : ∫ w, g w ∂μ < 1)
    (P : W → Prop) (hP : ∀ᵐ w ∂μ, P w) : ∃ w, P w ∧ g w < 1 := by
  by_contra h
  push Not at h
  have hle : ∀ᵐ w ∂μ, (1 : ℝ) ≤ g w := hP.mono fun w hw => h w hw
  have hi := integral_mono_ae (integrable_const 1) hg hle
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hi
  exact (not_lt_of_ge hi) havg

omit [MeasurableSpace W] [Fintype T] in
lemma fraction_lower_bound (e : ι → ℝ) (he : ∀ i, 0 ≤ e i) (τ : ℝ) (hτ : 0 < τ) :
    (1 - (∑ i, e i)/((Fintype.card ι : ℝ)*τ)) ≤
      ((Finset.univ.filter (fun i => e i < τ)).card : ℝ) / Fintype.card ι := by
  classical
  have hn : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hpoint (i) : 1-e i/τ ≤ if e i < τ then (1 : ℝ) else 0 := by
    split_ifs with h
    · have := div_nonneg (he i) hτ.le; linarith
    · have : 1 ≤ e i/τ := (le_div_iff₀ hτ).mpr (by simpa using le_of_not_gt h)
      linarith
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, ← Finset.sum_div] at hs
  simp only [Finset.cast_card, Finset.sum_filter]
  apply (le_div_iff₀ hn).mpr
  have heq : (1 - (∑ i, e i)/((Fintype.card ι : ℝ)*τ)) * Fintype.card ι =
      Fintype.card ι - (∑ i, e i)/τ := by field_simp
  rw [heq]
  exact hs

theorem simultaneous_good_fiber (μ : Measure W) [IsProbabilityMeasure μ]
    (f : T → W → ℝ) (e : ι → W → ℝ) (c τ : ℝ) (hc : 0 < c) (hτ : 0 < τ)
    (hf : ∀ t, Integrable (f t) μ) (he : ∀ i, Integrable (e i) μ)
    (hf0 : ∀ᵐ w ∂μ, ∀ t, 0 ≤ f t w) (he0 : ∀ᵐ w ∂μ, ∀ i, 0 ≤ e i w)
    (hbudget : (∑ t, ∫ w, f t w ∂μ)/c +
      10*(∑ i, ∫ w, e i w ∂μ)/((Fintype.card ι : ℝ)*τ) < 1)
    (P : W → Prop) (hP : ∀ᵐ w ∂μ, P w) :
    ∃ w, P w ∧ (∀ t, f t w < c) ∧
      (9/10 : ℝ)*(Fintype.card ι) <
        (Finset.univ.filter (fun i => e i w < τ)).card := by
  classical
  let n : ℝ := Fintype.card ι
  have hn : 0 < n := Nat.cast_pos.mpr Fintype.card_pos
  let g : W → ℝ := fun w => (∑ t, f t w)/c + 10*(∑ i, e i w)/(n*τ)
  have hig : Integrable g μ := ((integrable_finsetSum _ (fun t _ => hf t)).div_const c).add
    (((integrable_finsetSum _ (fun i _ => he i)).const_mul 10).div_const _)
  have hi : ∫ w, g w ∂μ < 1 := by
    dsimp [g]
    rw [integral_add ((integrable_finsetSum _ (fun t _ => hf t)).div_const c)
      (((integrable_finsetSum _ (fun i _ => he i)).const_mul 10).div_const _),
      integral_div, integral_div, integral_const_mul,
      integral_finsetSum _ (fun t _ => hf t), integral_finsetSum _ (fun i _ => he i)]
    exact hbudget
  obtain ⟨w, ⟨hwP, hwf, hwe⟩, hw⟩ := exists_lt_on_conull μ g hig hi
    (fun w => P w ∧ (∀ t, 0 ≤ f t w) ∧ ∀ i, 0 ≤ e i w) (hP.and (hf0.and he0))
  have hfs : 0 ≤ ∑ t, f t w := Finset.sum_nonneg (fun t _ => hwf t)
  have hes : 0 ≤ ∑ i, e i w := Finset.sum_nonneg (fun i _ => hwe i)
  refine ⟨w, hwP, ?_, ?_⟩
  · intro t
    have ht : f t w ≤ ∑ t, f t w :=
      Finset.single_le_sum (fun t _ => hwf t) (Finset.mem_univ t)
    have hb : f t w/c ≤ g w := by
      dsimp [g]
      have := div_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 10) hes) (mul_pos hn hτ).le
      have := (div_le_div_iff_of_pos_right hc).mpr ht
      linarith
    exact (div_lt_one hc).mp (hb.trans_lt hw)
  · have hew : (∑ i, e i w)/(n*τ) < 1/10 := by
      dsimp [g] at hw
      have : 0 ≤ (∑ t, f t w)/c := div_nonneg hfs hc.le
      rw [mul_div_assoc] at hw
      linarith
    have hlo := fraction_lower_bound (fun i => e i w) hwe τ hτ
    have hfrac : (9/10 : ℝ) <
        ((Finset.univ.filter (fun i => e i w < τ)).card : ℝ)/n := by
      change 1 - (∑ i, e i w)/(n*τ) ≤ _ at hlo
      linarith
    exact (lt_div_iff₀ hn).mp hfrac

omit [MeasurableSpace W] [Fintype T] [Nonempty ι] in

theorem large_common_bin {L B : ℕ} (s : Finset ι) (b : ι → Fin L)
    (hs : (9/10 : ℝ)*Fintype.card ι < s.card)
    (hLB : (L : ℝ)*B < (9/10 : ℝ)*Fintype.card ι) :
    ∃ J : Finset ι, J ⊆ s ∧ B < J.card ∧ ∀ i ∈ J, ∀ j ∈ J, b i = b j := by
  classical
  have hcard : L*B < s.card := by exact_mod_cast hLB.trans hs
  obtain ⟨k, _, hk⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s := s) (t := Finset.univ) (f := b) (fun _ _ => Finset.mem_univ _)
    (by simpa using hcard)
  refine ⟨s.filter (fun i => b i = k), Finset.filter_subset _ _, hk, ?_⟩
  intro i hi j hj
  exact (Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm

end EuclideanFiveColor.GoodFiber

open MeasureTheory
namespace EuclideanFiveColor.Approximation
variable {A X : Type*} [PseudoMetricSpace A] [MeasurableSpace X]

omit [MeasurableSpace X] in
lemma dist_sq_four_points (a b c d : A) :
    dist a d ^ 2 ≤ 3*(dist a b ^ 2 + dist b c ^ 2 + dist d c ^ 2) := by
  have ht : dist a d ≤ dist a b + dist b c + dist d c := by
    have := dist_triangle a b d
    have := dist_triangle b c d
    rw [dist_comm c d] at this
    linarith
  have ha := dist_nonneg (x := a) (y := b)
  have hb := dist_nonneg (x := b) (y := c)
  have hc := dist_nonneg (x := d) (y := c)
  have hd := dist_nonneg (x := a) (y := d)
  nlinarith [sq_nonneg (dist a b - dist b c), sq_nonneg (dist a b - dist d c),
    sq_nonneg (dist b c - dist d c)]

variable [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]

theorem integrated_distance_bound (μ : Measure X) [IsProbabilityMeasure μ]
    (H A' H₀ A₀ : X → A) (τ : ℝ)
    (hHm : Measurable H) (hH₀m : Measurable H₀)
    (hj : Integrable (fun x => dist (H x) (A' x)^2) μ)
    (h₀ : Integrable (fun x => dist (H₀ x) (A₀ x)^2) μ)
    (hAj : ∫ x, dist (H x) (A' x)^2 ∂μ < τ^2)
    (hA₀ : ∫ x, dist (H₀ x) (A₀ x)^2 ∂μ < τ^2)
    (hbin : ∀ᵐ x ∂μ, dist (A' x) (A₀ x) ≤ τ) :
    Integrable (fun x => dist (H x) (H₀ x)^2) μ ∧
      (∫ x, dist (H x) (H₀ x)^2 ∂μ) < 9*τ^2 := by
  have hdom : Integrable (fun x => 3*(dist (H x) (A' x)^2 + τ^2 +
      dist (H₀ x) (A₀ x)^2)) μ := ((hj.add (integrable_const _)).add h₀).const_mul 3
  have hle : ∀ᵐ x ∂μ, dist (H x) (H₀ x)^2 ≤
      3*(dist (H x) (A' x)^2 + τ^2 + dist (H₀ x) (A₀ x)^2) := by
    filter_upwards [hbin] with x hx
    have hs : dist (A' x) (A₀ x)^2 ≤ τ^2 :=
      pow_le_pow_left₀ dist_nonneg hx 2
    exact (dist_sq_four_points _ _ _ _).trans (by linarith)
  have hi : Integrable (fun x => dist (H x) (H₀ x)^2) μ := by
    apply hdom.mono' ((hHm.dist hH₀m).pow_const 2).aestronglyMeasurable
    exact hle.mono fun x hx => by simpa only [Real.norm_eq_abs, abs_sq] using hx
  refine ⟨hi, ?_⟩
  have he := integral_mono_ae hi hdom hle
  have hc : Integrable (fun _ : X => τ^2) μ := integrable_const _
  have hjc : Integrable (fun x => dist (H x) (A' x)^2 + τ^2) μ := hj.add hc
  rw [integral_const_mul, integral_add hjc h₀,
    integral_add hj hc, integral_const, probReal_univ, smul_eq_mul, one_mul] at he
  linarith

end EuclideanFiveColor.Approximation

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

omit [MeasurableSpace G] [StandardBorelSpace G] [Nonempty G] [NormedSpace ℝ V] in
lemma integrable_ae_fiber (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → W) (hp : Measurable p) (f : X → V) (hf : Integrable f μ) :
    ∀ᵐ w ∂μ.map p, Integrable f (condDistrib id p μ w) := by
  have hi : Integrable f ((condDistrib id p μ) ∘ₘ μ.map p) := by
    rwa [comp_identity_fiber μ p hp]
  exact ((Measure.integrable_comp_iff hi.aestronglyMeasurable).mp hi).1

omit [MeasurableSpace G] [StandardBorelSpace G] [Nonempty G] in
lemma integrable_fiber_integral (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → W) (hp : Measurable p) (f : X → V) (hf : Integrable f μ) :
    Integrable (fun w => ∫ x, f x ∂condDistrib id p μ w) (μ.map p) := by
  have hi : Integrable f ((condDistrib id p μ) ∘ₘ μ.map p) := by
    rwa [comp_identity_fiber μ p hp]
  rw [Measure.comp_eq_comp_const_apply] at hi
  exact hi.integral_comp

end EuclideanFiveColor.ConditionalFiber

namespace EuclideanFiveColor.FiniteModule
open MeasureTheory ProbabilityTheory
open scoped BigOperators
open ConditionalFiber
local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩
variable {X W ι T : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
  [MeasurableSpace W] [Fintype ι] [Nonempty ι] [Fintype T]

theorem common_fiber_contradiction (μ : Measure X) [IsProbabilityMeasure μ]
    (p : X → W) (hp : Measurable p) (m : ℕ) (hm : 0 < m)
    (ρ τ c : ℝ) (hρ : 0 < ρ) (hτ : 0 < τ) (hc : 0 < c)
    (hτδ : 18*τ^2 < (ρ^m/m)^2/20)
    (Hp Hm Ap Am : ι → X → Fin m → ℂ)
    (hHp : ∀ j, Measurable (Hp j)) (hHm : ∀ j, Measurable (Hm j))
    (hIp : ∀ j, Integrable (fun x => dist (Hp j x) (Ap j x)^2) μ)
    (hIm : ∀ j, Integrable (fun x => dist (Hm j x) (Am j x)^2) μ)
    (zp zm : X → ι → Fin m → Circle) (ap am : ι → X → Circle)
    (hap : ∀ j, Measurable (ap j)) (ham : ∀ j, Measurable (am j))
    (henc : ∀ᵐ x ∂μ, ∀ j, PhaseEncoding.encoding (zp x j) = Hp j x ∧
      PhaseEncoding.encoding (zm x j) = Hm j x)
    (hmem : ∀ᵐ x ∂μ, ∀ j, (∃ r, ap j x = zp x j r) ∧ (∃ r, am j x = zm x j r))
    (f : T → W → ℝ) (hf : ∀ t, Integrable (f t) (μ.map p))
    (hf0 : ∀ᵐ w ∂μ.map p, ∀ t, 0 ≤ f t w)
    (hbudget : (∑ t, ∫ w, f t w ∂μ.map p)/c +
      10*(∑ j, ((∫ x, dist (Hp j x) (Ap j x)^2 ∂μ) +
        (∫ x, dist (Hm j x) (Am j x)^2 ∂μ)))/((Fintype.card ι : ℝ)*τ^2) < 1)
    (L : ℕ) (bin : W → ι → Fin L)
    (hlarge : (L : ℝ)*(10*m^2 : ℕ) < (9/10 : ℝ)*Fintype.card ι)
    (hbin : ∀ᵐ w ∂μ.map p, ∀ i j, bin w i = bin w j →
      ∀ᵐ x ∂condDistrib id p μ w, dist (Ap i x) (Ap j x) ≤ τ ∧
        dist (Am i x) (Am j x) ≤ τ)
    (hupper : ∀ᵐ w ∂μ.map p, (∀ t, f t w < c) → ∀ i j, i ≠ j →
      (condDistrib id p μ w).real {x |
        dist ((ap i x : ℂ)*(am i x : ℂ)) ((ap j x : ℂ)*(am j x : ℂ)) ≤ 4*ρ}
        < 1/(4*(m : ℝ)^2)) : False := by
  classical
  let e : ι → W → ℝ := fun j w =>
    (∫ x, dist (Hp j x) (Ap j x)^2 ∂condDistrib id p μ w) +
    (∫ x, dist (Hm j x) (Am j x)^2 ∂condDistrib id p μ w)
  have he (j : ι) : Integrable (e j) (μ.map p) :=
    (integrable_fiber_integral μ p hp _ (hIp j)).add
      (integrable_fiber_integral μ p hp _ (hIm j))
  have hinte (j : ι) : (∫ w, e j w ∂μ.map p) =
      (∫ x, dist (Hp j x) (Ap j x)^2 ∂μ) +
      (∫ x, dist (Hm j x) (Am j x)^2 ∂μ) := by
    rw [show e j = fun w =>
      (∫ x, dist (Hp j x) (Ap j x)^2 ∂condDistrib id p μ w) +
      (∫ x, dist (Hm j x) (Am j x)^2 ∂condDistrib id p μ w) from rfl,
      integral_add (integrable_fiber_integral μ p hp _ (hIp j))
        (integrable_fiber_integral μ p hp _ (hIm j)),
      integral_fiber μ p hp _ (hIp j), integral_fiber μ p hp _ (hIm j)]
  have he0 (w) (j) : 0 ≤ e j w :=
    add_nonneg (integral_nonneg fun x => sq_nonneg _) (integral_nonneg fun x => sq_nonneg _)
  have hbudget' : (∑ t, ∫ w, f t w ∂μ.map p)/c +
      10*(∑ j, ∫ w, e j w ∂μ.map p)/((Fintype.card ι : ℝ)*τ^2) < 1 := by
    simpa only [hinte] using hbudget
  have hcondp : ∀ᵐ w ∂μ.map p, ∀ j, Integrable
      (fun x => dist (Hp j x) (Ap j x)^2) (condDistrib id p μ w) :=
    ae_all_iff.mpr fun j => integrable_ae_fiber μ p hp _ (hIp j)
  have hcondm : ∀ᵐ w ∂μ.map p, ∀ j, Integrable
      (fun x => dist (Hm j x) (Am j x)^2) (condDistrib id p μ w) :=
    ae_all_iff.mpr fun j => integrable_ae_fiber μ p hp _ (hIm j)
  let P : W → Prop := fun w =>
    (∀ᵐ x ∂condDistrib id p μ w, ∀ j, PhaseEncoding.encoding (zp x j) = Hp j x ∧
      PhaseEncoding.encoding (zm x j) = Hm j x) ∧
    (∀ᵐ x ∂condDistrib id p μ w, ∀ j, (∃ r, ap j x = zp x j r) ∧ (∃ r, am j x = zm x j r)) ∧
    (∀ j, Integrable (fun x => dist (Hp j x) (Ap j x)^2) (condDistrib id p μ w)) ∧
    (∀ j, Integrable (fun x => dist (Hm j x) (Am j x)^2) (condDistrib id p μ w)) ∧
    (∀ i j, bin w i = bin w j → ∀ᵐ x ∂condDistrib id p μ w,
      dist (Ap i x) (Ap j x) ≤ τ ∧ dist (Am i x) (Am j x) ≤ τ) ∧
    ((∀ t, f t w < c) → ∀ i j, i ≠ j →
      (condDistrib id p μ w).real {x |
        dist ((ap i x : ℂ)*(am i x : ℂ)) ((ap j x : ℂ)*(am j x : ℂ)) ≤ 4*ρ}
        < 1/(4*(m : ℝ)^2))
  have hP : ∀ᵐ w ∂μ.map p, P w := by
    filter_upwards [ae_fiber_of_ae μ p hp henc, ae_fiber_of_ae μ p hp hmem,
      hcondp, hcondm, hbin, hupper] with w h₁ h₂ h₃ h₄ h₅ h₆
    exact ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩
  haveI := Measure.isProbabilityMeasure_map (μ := μ) hp.aemeasurable
  obtain ⟨w, ⟨hwenc, hwmem, hwIp, hwIm, hwbin, hwup⟩, hwf, hmany⟩ :=
    GoodFiber.simultaneous_good_fiber (μ.map p) f e c (τ^2) hc (sq_pos_of_pos hτ)
      hf he hf0 (Filter.Eventually.of_forall he0) hbudget' P hP
  let s := Finset.univ.filter (fun j => e j w < τ^2)
  obtain ⟨J, hJs, hJ, hJbin⟩ := GoodFiber.large_common_bin s (bin w) hmany hlarge
  have hJpos : 0 < J.card := lt_of_le_of_lt (Nat.zero_le _) hJ
  let : Nonempty J := Set.Nonempty.to_subtype (Finset.card_pos.mp hJpos)
  obtain ⟨j₀⟩ := (inferInstance : Nonempty J)
  have herr (j : J) :
      (∫ x, dist (Hp j x) (Ap j x)^2 ∂condDistrib id p μ w) < τ^2 ∧
      (∫ x, dist (Hm j x) (Am j x)^2 ∂condDistrib id p μ w) < τ^2 := by
    have hj : e j w < τ^2 := (Finset.mem_filter.mp (hJs j.property)).2
    have hn1 : 0 ≤ ∫ x, dist (Hp j x) (Ap j x)^2 ∂condDistrib id p μ w :=
      integral_nonneg fun _ => sq_nonneg _
    have hn2 : 0 ≤ ∫ x, dist (Hm j x) (Am j x)^2 ∂condDistrib id p μ w :=
      integral_nonneg fun _ => sq_nonneg _
    dsimp [e] at hj
    constructor <;> linarith
  have hd (j : J) := hwbin j j₀ (hJbin j j.property j₀ j₀.property)
  have hdp (j : J) := Approximation.integrated_distance_bound
    (condDistrib id p μ w) (Hp j) (Ap j) (Hp j₀) (Ap j₀) τ
    (hHp j) (hHp j₀) (hwIp j) (hwIp j₀) (herr j).1 (herr j₀).1
    ((hd j).mono fun x hx => hx.1)
  have hdm (j : J) := Approximation.integrated_distance_bound
    (condDistrib id p μ w) (Hm j) (Am j) (Hm j₀) (Am j₀) τ
    (hHm j) (hHm j₀) (hwIm j) (hwIm j₀) (herr j).2 (herr j₀).2
    ((hd j).mono fun x hx => hx.2)
  obtain ⟨i, j, hij, hlo⟩ := EncodedCollision.collision_from_measurable_encodings
    (condDistrib id p μ w) m hm ρ hρ
    (fun x (j : J) => zp x j) (fun x (j : J) => zm x j)
    (fun j : J => ap j) (fun j : J => am j) j₀ (fun j : J => Hp j) (fun j : J => Hm j)
    (hwenc.mono fun x hx j => hx j) (fun j => hap j) (fun j => ham j)
    (fun j => (hHp j).dist (hHp j₀)) (fun j => (hHm j).dist (hHm j₀))
    (hwmem.mono fun x hx j => hx j)
    (fun j => (hdp j).1.add (hdm j).1)
    (fun j => by
      rw [integral_add (hdp j).1 (hdm j).1]
      exact (add_lt_add (hdp j).2 (hdm j).2).trans (by nlinarith [hτδ]))
    (by simpa only [Fintype.card_coe] using hJ)
  exact (not_lt_of_ge hlo) (hwup hwf i j (fun heq => hij (Subtype.ext heq)))

end EuclideanFiveColor.FiniteModule

open scoped BigOperators
namespace EuclideanFiveColor.FiniteBins

variable {A : Type*} [PseudoMetricSpace A]

theorem compact_bins {s : Set A} (hs : IsCompact s) {r : ℝ} (hr : 0 < r) :
    ∃ L : ℕ, ∃ f : s → Fin L, ∀ x y, f x = f y → dist (x : A) (y : A) < r := by
  classical
  obtain ⟨u, _, hu, hucover⟩ := hs.finite_cover_balls (half_pos hr)
  let t := hu.toFinset
  have ht : s ⊆ ⋃ a ∈ t, Metric.ball a (r/2) := by simpa only [t, hu.mem_toFinset] using hucover
  have hx (x : s) : ∃ a ∈ t, dist (x : A) a < r/2 := by
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp (ht x.property)
    obtain ⟨hat, hx⟩ := Set.mem_iUnion.mp ha
    exact ⟨a, hat, hx⟩
  let c : s → t := fun x => ⟨(hx x).choose, (hx x).choose_spec.1⟩
  let e : t ≃ Fin t.card := t.equivFin
  refine ⟨t.card, fun x => e (c x), ?_⟩
  intro x y hxy
  have hc : c x = c y := e.injective hxy
  have hdx : dist (x : A) (c x : A) < r/2 := (hx x).choose_spec.2
  have hdy : dist (y : A) (c x : A) < r/2 := by rw [hc]; exact (hx y).choose_spec.2
  calc
    _ ≤ dist (x : A) (c x : A) + dist (c x : A) (y : A) := dist_triangle _ _ _
    _ < r/2+r/2 := add_lt_add hdx (by simpa only [dist_comm] using hdy)
    _ = r := by ring

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

lemma linear_combination_dist_bound {q : ℕ} (H : Fin q → V)
    (b c : Fin q → ℂ) :
    dist (∑ i, b i • H i) (∑ i, c i • H i) ≤
      dist b c * ∑ i, ‖H i‖ := by
  rw [dist_eq_norm, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, ‖b i • H i - c i • H i‖ := norm_sum_le _ _
    _ ≤ ∑ i, dist b c * ‖H i‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [← sub_smul, norm_smul]
      exact mul_le_mul_of_nonneg_right
        (by simpa only [dist_eq_norm] using dist_le_pi_dist b c i) (norm_nonneg _)
    _ = _ := by rw [Finset.mul_sum]

theorem bounded_coefficient_bins (q : ℕ) (B D τ : ℝ) (hD : 0 ≤ D) (hτ : 0 < τ) :
    ∃ L : ℕ, ∃ f : {b : Fin 2 → Fin q → ℂ // ‖b‖ ≤ B} → Fin L,
      ∀ b c, f b = f c → ∀ H : Fin q → V, (∑ i, ‖H i‖) ≤ D →
      ∀ j : Fin 2, dist (∑ i, b.val j i • H i) (∑ i, c.val j i • H i) < τ := by
  have hden : 0 < 1+D := by linarith
  have hs : IsCompact {b : Fin 2 → Fin q → ℂ | ‖b‖ ≤ B} := by
    simpa only [Metric.closedBall, dist_zero_right] using
      (isCompact_closedBall (0 : Fin 2 → Fin q → ℂ) B)
  obtain ⟨L, f, hf⟩ := compact_bins hs (div_pos hτ hden)
  refine ⟨L, f, ?_⟩
  intro b c hbc H hH j
  have hdist : dist (b.val j) (c.val j) < τ/(1+D) :=
    (dist_le_pi_dist b.val c.val j).trans_lt (hf b c hbc)
  calc
    _ ≤ dist (b.val j) (c.val j) * ∑ i, ‖H i‖ := linear_combination_dist_bound H _ _
    _ ≤ dist (b.val j) (c.val j) * D :=
      mul_le_mul_of_nonneg_left hH dist_nonneg
    _ ≤ dist (b.val j) (c.val j) * (1+D) :=
      mul_le_mul_of_nonneg_left (by linarith) dist_nonneg
    _ < τ := (lt_div_iff₀ hden).mp hdist

end EuclideanFiveColor.FiniteBins

end

end ParishFactor
end

-- OAI.Analysis.PlaneSpectrum.ConditionalSpectrum
section
namespace ParishFactor

noncomputable section

open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators
open Polynomial
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open MeasureTheory ProbabilityTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace PlaneFiveColor.Spectral
variable [Carrier]

section
open MeasureTheory ProbabilityTheory
open EuclideanFiveColor
open scoped BigOperators ComplexConjugate

private instance dualPolishSpace : PolishSpace D := by
  have : TopologicalSpace.SeparableSpace (DiscreteE → Circle) := inferInstance
  have : TopologicalSpace.IsCompletelyMetrizableSpace (DiscreteE → Circle) := inferInstance
  exact ContinuousMonoidHom.isClosedEmbedding_coe.polishSpace

local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩

private def eval (a : E) : D →* Circle where
  toFun d := d (Multiplicative.ofAdd a)
  map_one' := rfl
  map_mul' _ _ := rfl

lemma continuous_eval (a : E) : Continuous (eval a) :=
  (continuous_apply (Multiplicative.ofAdd a)).comp
    ContinuousMonoidHom.isClosedEmbedding_coe.continuous

lemma measurable_eval (a : E) : Measurable (eval a) := (continuous_eval a).measurable
lemma measurable_eval_coe (a : E) : Measurable (fun d => (eval a d : ℂ)) :=
  ((show Continuous (fun z : Circle => (z : ℂ)) from continuous_subtype_val).comp
    (continuous_eval a)).measurable

@[simp] lemma eval_zero (d : D) : eval 0 d = 1 := map_one d
lemma eval_add (a b : E) (d : D) : eval (a+b) d = eval a d * eval b d :=
  map_mul d (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)
lemma eval_neg (a : E) (d : D) : eval (-a) d = (eval a d)⁻¹ :=
  d.map_inv (Multiplicative.ofAdd a)
lemma eval_sub (a b : E) (d : D) : eval (a-b) d = eval a d / eval b d := by
  rw [sub_eq_add_neg, eval_add, eval_neg, div_eq_mul_inv]
lemma eval_nat_mul (n : ℕ) (a : E) (d : D) : eval ((n:E)*a) d = eval a d ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul,
      eval_add, ih, pow_succ]
lemma eval_scalar (a b : E) (d : D) : eval a (scalar b d) = eval (b*a) d := rfl
lemma eval_smul_one (u : K) (d : D) : eval 1 (u • d) = eval (kCoeff u) d := by
  change eval (kCoeff u * 1) d = _
  rw [mul_one]
lemma lineFourier_eq (ν : Measure D) (a : E) (t : F) :
    lineFourier ν a t = ∫ d, (eval (a * ofF t) d : ℂ) ∂ν := rfl

variable {X W : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
  [MeasurableSpace W]

lemma predecessor_moment_sq (μ : Measure X) [IsProbabilityMeasure μ]
    (p : X → W) (b : X → D) (hp : Measurable p) (hb : Measurable b) (a : E) :
    (∫ w, ‖∫ x, (eval a (b x) : ℂ) ∂condDistrib id p μ w‖^2 ∂μ.map p) =
      (∫ d, (eval a d : ℂ) ∂DifferenceFourier.differenceLaw (μ.map p)
        (condDistrib b p μ)).re := by
  let : IsProbabilityMeasure (μ.map p) :=
    (Measure.isProbabilityMeasure_map_iff hp.aemeasurable).mpr inferInstance
  rw [DifferenceFourier.difference_coefficient (eval a) (measurable_eval_coe a),
    Complex.ofReal_re]
  apply integral_congr_ae
  filter_upwards [ConditionalFiber.map_identity_fiber μ p hp.aemeasurable b hb] with w hw
  congr 1
  rw [← hw, integral_map hb.aemeasurable (measurable_eval_coe a).aestronglyMeasurable]

lemma integrable_predecessor_moment_sq (μ : Measure X) [IsProbabilityMeasure μ]
    (p : X → W) (b : X → D) (hp : Measurable p) (hb : Measurable b) (a : E) :
    Integrable (fun w => ‖∫ x, (eval a (b x) : ℂ) ∂condDistrib id p μ w‖^2) (μ.map p) := by
  let : IsProbabilityMeasure (μ.map p) :=
    (Measure.isProbabilityMeasure_map_iff hp.aemeasurable).mpr inferInstance
  have hm := ((measurable_eval_coe a).comp hb).stronglyMeasurable.integral_kernel
    (κ := condDistrib id p μ)
  apply Integrable.of_bound (hm.norm.pow 2).aestronglyMeasurable 1
  apply Filter.Eventually.of_forall
  intro w
  have hh : ‖∫ x, (eval a (b x) : ℂ) ∂condDistrib id p μ w‖ ≤ 1 := by
    simpa using norm_integral_le_of_norm_le_const (μ := condDistrib id p μ w)
      (C := (1 : ℝ)) (Filter.Eventually.of_forall (fun x => (Circle.norm_coe _).le))
  simpa only [Real.norm_eq_abs, Pi.pow_apply, Function.comp_apply, abs_sq, one_pow] using pow_le_pow_left₀ (norm_nonneg _) hh 2

end

theorem real_algebraic_sum_two_rotations (x : F) (hx : |(x : ℝ)| < 2) :
    ∃ u v : K, ofF x = kCoeff u + kCoeff v := by
  let r : ℝ := (x : ℝ)/2
  have hr : |r| < 1 := by dsimp [r]; rw [abs_div]; norm_num; linarith
  have hnon : 0 ≤ 1-r^2 := by nlinarith [sq_abs r, abs_nonneg r]
  let s : ℝ := Real.sqrt (1-r^2)
  have hs : s^2 = 1-r^2 := Real.sq_sqrt hnon
  have hrAlg : r ∈ F := by
    change ((x / 2 : F) : ℝ) ∈ F
    exact (x / 2 : F).property
  have hsAlg : s ∈ F := Carrier.sqrt_mem (F.sub_mem F.one_mem (F.pow_mem hrAlg 2))
  have huAlg : (r : ℂ) + Complex.I * s ∈ E :=
    E.add_mem (Carrier.ofReal_mem hrAlg) (E.mul_mem Carrier.I_mem (Carrier.ofReal_mem hsAlg))
  have hvAlg : (r : ℂ) - Complex.I * s ∈ E :=
    E.sub_mem (Carrier.ofReal_mem hrAlg) (E.mul_mem Carrier.I_mem (Carrier.ofReal_mem hsAlg))
  have huNorm : ‖(r : ℂ)+Complex.I*s‖ = 1 := by
    rw [← sq_eq_sq₀ (norm_nonneg _) zero_le_one]
    rw [← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    nlinarith
  have hvNorm : ‖(r : ℂ)-Complex.I*s‖ = 1 := by
    rw [← sq_eq_sq₀ (norm_nonneg _) zero_le_one]
    rw [← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    nlinarith
  let u : K := ⟨⟨(r : ℂ)+Complex.I*s, mem_sphere_zero_iff_norm.mpr huNorm⟩, huAlg⟩
  let v : K := ⟨⟨(r : ℂ)-Complex.I*s, mem_sphere_zero_iff_norm.mpr hvNorm⟩, hvAlg⟩
  refine ⟨u, v, ?_⟩
  apply Subtype.ext
  change ((x : ℝ) : ℂ) = ((r : ℂ)+Complex.I*s)+((r : ℂ)-Complex.I*s)
  simp only [r, Complex.ofReal_div, Complex.ofReal_ofNat]
  ring

end PlaneFiveColor.Spectral

namespace EuclideanFiveColor.PhaseEncoding
open MeasureTheory ProbabilityTheory
variable {Y G : Type*} [MeasurableSpace Y] [MeasurableSpace G]

theorem kernelEncoding_covariance (ν : Measure Y) (β : Kernel Y G)
    (R : Y → Y) (T : G → G) (hT : Measurable T)
    (χ : G → ℂ) (hχ : Measurable χ) (m : ℕ)
    (hβ : ∀ᵐ y ∂ν, β (R y) = (β y).map T) :
    ∀ᵐ y ∂ν, kernelEncoding β χ m (R y) = kernelEncoding β (χ ∘ T) m y := by
  filter_upwards [hβ] with y hy
  have he (n : ℕ) : (∫ d, χ d ^ n ∂β (R y)) = ∫ d, χ (T d)^n ∂β y := by
    rw [hy, integral_map hT.aemeasurable (hχ.pow_const n).aestronglyMeasurable]
  funext i
  simp only [kernelEncoding, he, Function.comp_def]
end EuclideanFiveColor.PhaseEncoding

namespace PlaneFiveColor.Spectral
variable [Carrier]

section
open MeasureTheory ProbabilityTheory
open EuclideanFiveColor
open scoped BigOperators
local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩

private abbrev MomentTest (M N : ℕ) := Fin N × {p : Fin M × Fin M // p.1 ≠ p.2}

private def momentArgument {M N : ℕ} (z : MomentTest M N) : E :=
  (z.1.val + 1) * ((z.2.val.1.val : E) - z.2.val.2.val)

lemma momentArgument_ne_zero {M N : ℕ} (z : MomentTest M N) : momentArgument z ≠ 0 := by
  unfold momentArgument
  apply mul_ne_zero
  · exact_mod_cast Nat.succ_ne_zero z.1.val
  · apply sub_ne_zero.mpr
    intro h
    have hh : z.2.val.1.val = z.2.val.2.val := by exact_mod_cast h
    exact z.2.property (Fin.ext hh)

omit [Carrier] in
lemma momentTest_nonempty {M N : ℕ} (hM : 2 ≤ M) (hN : 0 < N) :
    Nonempty (MomentTest M N) := by
  refine ⟨⟨⟨0, hN⟩, ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), ?_⟩⟩⟩
  intro h
  have hh := congrArg Fin.val h
  norm_num at hh

theorem exists_simultaneous_moment_parameter (ν : Measure D) [IsProbabilityMeasure ν]
    (hν : IsWild ν) (hn : ∀ a : E, 0 ≤ (∫ d, (eval a d : ℂ) ∂ν).re)
    (M N : ℕ) (hM : 2 ≤ M) (hN : 0 < N) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ t : F, t ≠ 0 ∧ |(t : ℝ)| < 1/(M : ℝ) ∧
      ∀ z : MomentTest M N, (∫ d, (eval (momentArgument z * ofF t) d : ℂ) ∂ν).re < ε := by
  let : Nonempty (MomentTest M N) := momentTest_nonempty hM hN
  have hMr : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  obtain ⟨t, ht, htr, hh⟩ := exists_small_wild_parameter
    (Finset.univ : Finset (MomentTest M N)) Finset.univ_nonempty ν hν
    momentArgument momentArgument_ne_zero
    (fun z t => by simpa only [lineFourier_eq] using hn (momentArgument z * ofF t))
    (one_div_pos.mpr hMr) hε hε1
  exact ⟨t, ht, htr, fun z => hh z (Finset.mem_univ z)⟩

lemma eval_dist (a b : E) (d : D) :
    dist (eval a d : ℂ) (eval b d : ℂ) = ‖(eval (a-b) d : ℂ)-1‖ := by
  rw [eval_sub, Circle.coe_div, dist_eq_norm]
  have he : (eval a d : ℂ) / (eval b d : ℂ) - 1 =
      ((eval a d : ℂ) - (eval b d : ℂ)) / (eval b d : ℂ) := by
    field_simp
  rw [he, norm_div, Circle.norm_coe, div_one]

theorem pair_collision_upper {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (b : X → D) (hb : Measurable b)
    (a₁ a₂ : E) (m N : ℕ) (ρ c : ℝ)
    (harc : ∀ (ω : Measure Circle) [IsProbabilityMeasure ω],
      (∀ n, 0 < n → n ≤ N → ‖∫ w, (w : ℂ)^n ∂ω‖ < c) →
      ω.real {w | ‖(w : ℂ)-1‖ ≤ 4*ρ} < 1/(4*(m : ℝ)^2))
    (hMom : ∀ n, 0 < n → n ≤ N →
      ‖∫ x, (eval ((n : E)*(a₁-a₂)) (b x) : ℂ) ∂μ‖ < c) :
    μ.real {x | dist (eval a₁ (b x) : ℂ) (eval a₂ (b x) : ℂ) ≤ 4*ρ}
      < 1/(4*(m : ℝ)^2) := by
  let φ : X → Circle := fun x => eval (a₁-a₂) (b x)
  have hφ : Measurable φ := (measurable_eval _).comp hb
  let ω := μ.map φ
  let : IsProbabilityMeasure ω :=
    (Measure.isProbabilityMeasure_map_iff hφ.aemeasurable).mpr inferInstance
  have hco : Measurable (fun z : Circle => (z : ℂ)) :=
    (show Continuous (fun z : Circle => (z : ℂ)) from continuous_subtype_val).measurable
  have hmom : ∀ n, 0 < n → n ≤ N → ‖∫ z, (z : ℂ)^n ∂ω‖ < c := by
    intro n hn hnN
    rw [show ω = μ.map φ from rfl,
      integral_map hφ.aemeasurable (hco.pow_const n).aestronglyMeasurable]
    simpa only [φ, eval_nat_mul, Circle.coe_pow] using hMom n hn hnN
  have hu := harc ω hmom
  have hs : MeasurableSet {z : Circle | ‖(z : ℂ)-1‖ ≤ 4*ρ} :=
    measurableSet_le ((hco.sub_const 1).norm) measurable_const
  rw [Measure.real, show ω = μ.map φ from rfl, Measure.map_apply hφ hs] at hu
  simpa only [Measure.real, Set.preimage_ofPred_eq, φ, eval_dist] using hu

end

open MeasureTheory ProbabilityTheory EuclideanFiveColor
open scoped BigOperators
local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩

variable {X Y W : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
  [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
  [MeasurableSpace W] [StandardBorelSpace W] [Nonempty W]

private def FiniteEncodingApproximationAt (μ : Measure X) [IsProbabilityMeasure μ] (p : X → Y) (q : Y → W)
    (b : X → D) (m : ℕ) (γ : ℝ) : Prop :=
  ∃ (r : ℕ) (B C : ℝ) (H : Fin r → Y → Fin m → ℂ),
    0 ≤ B ∧ 0 ≤ C ∧ (∀ y, ∑ i, ‖H i y‖ ≤ C) ∧
    ∀ k : K, ∃ coeff : W → Fin r → ℂ,
      (∀ w, ‖coeff w‖ ≤ B) ∧
      Integrable (fun x => dist
        (PhaseEncoding.kernelEncoding (condDistrib b p μ)
          (fun d => (eval (kCoeff k) d : ℂ)) m (p x))
        (∑ i, coeff (q (p x)) i • H i (p x)) ^ 2) μ ∧
      (∫ x, dist
        (PhaseEncoding.kernelEncoding (condDistrib b p μ)
          (fun d => (eval (kCoeff k) d : ℂ)) m (p x))
        (∑ i, coeff (q (p x)) i • H i (p x)) ^ 2 ∂μ) < γ^2

private def FiniteEncodingApproximation (μ : Measure X) [IsProbabilityMeasure μ]
    (p : X → Y) (q : Y → W) (b : X → D) (m : ℕ) : Prop :=
  ∀ γ : ℝ, 0 < γ → FiniteEncodingApproximationAt μ p q b m γ

omit [Carrier] in
lemma two_array_norm_bound {r : ℕ} {a b : Fin r → ℂ} {B : ℝ}
    (ha : ‖a‖ ≤ B) (hb : ‖b‖ ≤ B) (hB : 0 ≤ B) : ‖![a,b]‖ ≤ B := by
  rw [pi_norm_le_iff_of_nonneg hB]
  intro j
  fin_cases j <;> assumption

omit [Carrier] in
lemma simultaneous_test_budget {T : Type*} [Fintype T]
    (v : T → ℝ) (c : ℝ) (hc : 0 < c)
    (hv : ∀ t, v t < min 1 (c^2 / (4*(Fintype.card T+1)))) :
    (∑ t, v t)/(c^2) < 1/4 := by
  have hs : (∑ t, v t) ≤ (Fintype.card T : ℝ) *
      (c^2 / (4*(Fintype.card T+1))) := by
    calc
      _ ≤ ∑ _t : T, c^2 / (4*(Fintype.card T+1)) :=
        Finset.sum_le_sum fun t _ => (hv t).le.trans (min_le_right _ _)
      _ = _ := by simp
  have hn : (0 : ℝ) < Fintype.card T+1 := by positivity
  rw [div_lt_iff₀ (sq_pos_of_pos hc)]
  apply hs.trans_lt
  rw [← mul_div_assoc, div_lt_iff₀ (by positivity : (0 : ℝ) < 4*(Fintype.card T+1))]
  nlinarith [sq_pos_of_pos hc]

omit [StandardBorelSpace Y] [Nonempty Y] in

theorem finite_uniform_precision_contradiction
    (μ : Measure X) [IsProbabilityMeasure μ]
    (p : X → Y) (q : Y → W) (b : X → D)
    (hp : Measurable p) (hq : Measurable q) (hb : Measurable b)
    (m : ℕ) (hm : 0 < m) (g : Y → Fin m → D)
    (hg : ∀ᵐ y ∂μ.map p, condDistrib b p μ y =
      (m : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (g y i))
    (hwild : IsWild (DifferenceFourier.differenceLaw (μ.map (q ∘ p))
      (condDistrib b (q ∘ p) μ)))
    (ρ c : ℝ) (N : ℕ) (hρ : 0 < ρ) (hc : 0 < c) (hN : 0 < N)
    (harc : ∀ (ω : Measure Circle) [IsProbabilityMeasure ω],
      (∀ n, 0 < n → n ≤ N → ‖∫ w, (w : ℂ)^n ∂ω‖ < c) →
      ω.real {w | ‖(w : ℂ)-1‖ ≤ 4*ρ} < 1/(4*(m : ℝ)^2))
    (happrox : FiniteEncodingApproximationAt μ p q b m (((ρ^m/(m : ℝ))/100)/100)) : False := by
  classical
  let P : X → W := q ∘ p
  have hP : Measurable P := hq.comp hp
  let : IsProbabilityMeasure (μ.map P) :=
    (Measure.isProbabilityMeasure_map_iff hP.aemeasurable).mpr inferInstance
  let ν := DifferenceFourier.differenceLaw (μ.map P) (condDistrib b P μ)
  let : IsProbabilityMeasure ν := inferInstance
  have hn (a : E) : 0 ≤ (∫ d, (eval a d : ℂ) ∂ν).re := by
    rw [← predecessor_moment_sq μ P b hP hb a]
    exact integral_nonneg fun _ => sq_nonneg _
  let τ := (ρ^m/(m : ℝ))/100
  let γ := τ/100
  have hmr : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτδ : 18*τ^2 < (ρ^m/(m : ℝ))^2/20 := by
    dsimp [τ]
    nlinarith [sq_pos_of_pos (div_pos (pow_pos hρ m) hmr)]
  obtain ⟨r, B, C, H, hB, hC, hH, happ⟩ := happrox
  choose coeff hcoeff hInt hErr using happ
  obtain ⟨L, bins, hbins⟩ := FiniteBins.bounded_coefficient_bins
    (V := Fin m → ℂ) r B C τ hC hτ
  let M := 20*(L+1)*m^2
  have hM : 2 ≤ M := by dsimp [M]; nlinarith [Nat.one_le_iff_ne_zero.mpr hm.ne']
  let : NeZero M := ⟨by omega⟩
  let T := MomentTest M N
  let ε := min 1 (c^2/(4*(Fintype.card T+1)))
  have hε : 0 < ε := by dsimp [ε]; apply lt_min (by norm_num); positivity
  have hε1 : ε ≤ 1 := min_le_left _ _
  obtain ⟨t, ht, htM, hTest⟩ := exists_simultaneous_moment_parameter ν hwild hn M N hM hN ε hε hε1
  let xs : Fin M → F := fun j => (j.val+1)*t
  have hxs (j : Fin M) : |(xs j : ℝ)| < 2 := by
    have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr (by omega)
    have hj : (j.val+1 : ℝ) ≤ M := by exact_mod_cast j.isLt
    have hx : |(xs j : ℝ)| = (j.val+1 : ℝ)*|(t : ℝ)| := by
      simp [xs, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ j.val+1 by positivity)]
    rw [hx]
    have hmul := mul_lt_mul_of_pos_left htM (by positivity : (0 : ℝ) < j.val+1)
    have hbound : (j.val+1 : ℝ) * (1/(M : ℝ)) ≤ 1 := by
      rw [mul_one_div, div_le_one hMr]
      exact hj
    linarith
  choose u v huv using fun j => real_algebraic_sum_two_rotations (xs j) (hxs j)
  let β := condDistrib b p μ
  let enc : K → Y → Fin m → ℂ := fun k =>
    PhaseEncoding.kernelEncoding β (fun d => (eval (kCoeff k) d : ℂ)) m
  let Hp : Fin M → X → Fin m → ℂ := fun j x => enc (u j) (p x)
  let Hm : Fin M → X → Fin m → ℂ := fun j x => enc (v j) (p x)
  let Ap : Fin M → X → Fin m → ℂ := fun j x => ∑ i, coeff (u j) (P x) i • H i (p x)
  let Am : Fin M → X → Fin m → ℂ := fun j x => ∑ i, coeff (v j) (P x) i • H i (p x)
  let ap : Fin M → X → Circle := fun j x => eval (kCoeff (u j)) (b x)
  let am : Fin M → X → Circle := fun j x => eval (kCoeff (v j)) (b x)
  let zp : X → Fin M → Fin m → Circle := fun x j i => eval (kCoeff (u j)) (g (p x) i)
  let zm : X → Fin M → Fin m → Circle := fun x j i => eval (kCoeff (v j)) (g (p x) i)
  have henc : ∀ᵐ x ∂μ, ∀ j, PhaseEncoding.encoding (zp x j) = Hp j x ∧
      PhaseEncoding.encoding (zm x j) = Hm j x := by
    filter_upwards [ae_of_ae_map hp.aemeasurable hg] with x hx
    intro j
    exact ⟨(PhaseEncoding.kernelEncoding_eq_encoding β (eval (kCoeff (u j))) m hm (p x) (g (p x)) hx).symm,
      (PhaseEncoding.kernelEncoding_eq_encoding β (eval (kCoeff (v j))) m hm (p x) (g (p x)) hx).symm⟩
  have hmem : ∀ᵐ x ∂μ, ∀ j, (∃ i, ap j x = zp x j i) ∧ (∃ i, am j x = zm x j i) := by
    filter_upwards [SampledAtoms.ae_sampled_list μ p b hp hb hm g hg] with x hx
    obtain ⟨i, hi⟩ := hx
    intro j
    exact ⟨⟨i, congrArg (eval (kCoeff (u j))) hi⟩, ⟨i, congrArg (eval (kCoeff (v j))) hi⟩⟩
  let f : T → W → ℝ := fun z w =>
    ‖∫ x, (eval (momentArgument z * ofF t) (b x) : ℂ) ∂condDistrib id P μ w‖^2
  have hf (z : T) : Integrable (f z) (μ.map P) :=
    integrable_predecessor_moment_sq μ P b hP hb _
  have hfTest (z : T) : (∫ w, f z w ∂μ.map P) < ε := by
    rw [show (∫ w, f z w ∂μ.map P) =
      (∫ d, (eval (momentArgument z * ofF t) d : ℂ) ∂ν).re from
        predecessor_moment_sq μ P b hP hb _]
    exact hTest z
  have hfBudget : (∑ z, ∫ w, f z w ∂μ.map P)/(c^2) < 1/4 :=
    simultaneous_test_budget _ c hc hfTest
  have heBudget : 10*(∑ j, ((∫ x, dist (Hp j x) (Ap j x)^2 ∂μ) +
      (∫ x, dist (Hm j x) (Am j x)^2 ∂μ)))/((M : ℝ)*τ^2) < 1/4 := by
    have hs : (∑ j, ((∫ x, dist (Hp j x) (Ap j x)^2 ∂μ) +
        (∫ x, dist (Hm j x) (Am j x)^2 ∂μ))) < (M : ℝ)*(2*γ^2) := by
      calc
        _ < ∑ _j : Fin M, 2*γ^2 := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
          (fun j _ => by
            have h1 : (∫ x, dist (Hp j x) (Ap j x)^2 ∂μ) < γ^2 := hErr (u j)
            have h2 : (∫ x, dist (Hm j x) (Am j x)^2 ∂μ) < γ^2 := hErr (v j)
            linarith)
        _ = _ := by simp
    have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr (by omega)
    rw [div_lt_iff₀ (mul_pos hMr (sq_pos_of_pos hτ))]
    dsimp [γ] at hs
    nlinarith
  let arr : W → Fin M → {a : Fin 2 → Fin r → ℂ // ‖a‖ ≤ B} := fun w j =>
    ⟨![coeff (u j) w, coeff (v j) w], two_array_norm_bound (hcoeff _ _) (hcoeff _ _) hB⟩
  let bin : W → Fin M → Fin L := fun w j => bins (arr w j)
  have hlarge : (L : ℝ)*(10*m^2 : ℕ) < (9/10 : ℝ)*Fintype.card (Fin M) := by
    simp only [Fintype.card_fin]
    dsimp [M]
    push_cast
    nlinarith [sq_pos_of_pos hmr, Nat.cast_nonneg (α := ℝ) L]
  have hbin : ∀ᵐ w ∂μ.map P, ∀ i j, bin w i = bin w j →
      ∀ᵐ x ∂condDistrib id P μ w, dist (Ap i x) (Ap j x) ≤ τ ∧
        dist (Am i x) (Am j x) ≤ τ := by
    filter_upwards [ConditionalFiber.ae_in_own_fiber μ P hP] with w hw
    intro i j hij
    filter_upwards [hw] with x hx
    have hh := hbins (arr w i) (arr w j) hij (fun k => H k (p x)) (hH (p x))
    have h0 := (hh 0).le
    have h1 := (hh 1).le
    change dist (∑ k, coeff (u i) (P x) k • H k (p x))
      (∑ k, coeff (u j) (P x) k • H k (p x)) ≤ τ ∧
      dist (∑ k, coeff (v i) (P x) k • H k (p x))
      (∑ k, coeff (v j) (P x) k • H k (p x)) ≤ τ
    rw [hx]
    exact ⟨h0, h1⟩
  have hupper : ∀ᵐ w ∂μ.map P, (∀ z, f z w < c^2) → ∀ i j, i ≠ j →
      (condDistrib id P μ w).real {x |
        dist ((ap i x : ℂ)*(am i x : ℂ)) ((ap j x : ℂ)*(am j x : ℂ)) ≤ 4*ρ}
        < 1/(4*(m : ℝ)^2) := by
    apply Filter.Eventually.of_forall
    intro w hw i j hij
    have hMom : ∀ n : ℕ, 0 < n → n ≤ N →
        ‖∫ x, (eval ((n : E)*(ofF (xs i)-ofF (xs j))) (b x) : ℂ)
          ∂condDistrib id P μ w‖ < c := by
      intro n hn hnN
      let z : T := (⟨n-1, by omega⟩, ⟨(i,j), hij⟩)
      have he : (n : E)*(ofF (xs i)-ofF (xs j)) = momentArgument z * ofF t := by
        have hnv : (n-1)+1 = n := by omega
        have hnv' : ((n-1 : ℕ) : E)+1=(n : E) := by exact_mod_cast hnv
        simp only [momentArgument, z, hnv']
        dsimp [xs]
        simp only [map_mul, map_add, map_natCast, map_one]
        ring
      have hh := hw z
      change ‖∫ x, (eval (momentArgument z * ofF t) (b x) : ℂ)
         ∂condDistrib id P μ w‖^2 < c^2 at hh
      rw [he]
      nlinarith [norm_nonneg (∫ x, (eval (momentArgument z * ofF t) (b x) : ℂ)
         ∂condDistrib id P μ w)]
    have hh := pair_collision_upper (condDistrib id P μ w) b hb
      (ofF (xs i)) (ofF (xs j)) m N ρ c harc hMom
    have he (j : Fin M) (x : X) : (ap j x : ℂ)*(am j x : ℂ) =
        (eval (ofF (xs j)) (b x) : ℂ) := by
      change (eval (kCoeff (u j)) (b x) : ℂ) * (eval (kCoeff (v j)) (b x) : ℂ) = _
      rw [huv j]
      exact congrArg (fun z : Circle => (z : ℂ)) (eval_add _ _ _).symm
    simpa only [he] using hh
  apply FiniteModule.common_fiber_contradiction μ P hP m hm ρ τ (c^2) hρ hτ
    (sq_pos_of_pos hc) hτδ Hp Hm Ap Am
    (fun j => (PhaseEncoding.measurable_kernelEncoding β _ (measurable_eval_coe _) m).comp hp)
    (fun j => (PhaseEncoding.measurable_kernelEncoding β _ (measurable_eval_coe _) m).comp hp)
    (fun j => hInt (u j)) (fun j => hInt (v j)) zp zm ap am
    (fun j => (measurable_eval _).comp hb) (fun j => (measurable_eval _).comp hb)
    henc hmem f hf (Filter.Eventually.of_forall (fun w z => sq_nonneg _))
    (by simp only [Fintype.card_fin]; linarith) L bin hlarge hbin hupper

omit [StandardBorelSpace Y] [Nonempty Y] in
theorem finite_uniform_successor_contradiction
    (μ : Measure X) [IsProbabilityMeasure μ]
    (p : X → Y) (q : Y → W) (b : X → D)
    (hp : Measurable p) (hq : Measurable q) (hb : Measurable b)
    (m : ℕ) (hm : 0 < m) (g : Y → Fin m → D)
    (hg : ∀ᵐ y ∂μ.map p, condDistrib b p μ y =
      (m : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (g y i))
    (hwild : IsWild (DifferenceFourier.differenceLaw (μ.map (q ∘ p))
      (condDistrib b (q ∘ p) μ)))
    (happrox : FiniteEncodingApproximation μ p q b m) : False := by
  obtain ⟨ρ, c, N, hρ, hc, hN, harc⟩ := SmallArc.exists_small_arc_constants m hm
  exact finite_uniform_precision_contradiction μ p q b hp hq hb m hm g hg hwild
    ρ c N hρ hc hN harc (happrox _ (by positivity))

end PlaneFiveColor.Spectral

end

end ParishFactor
end

-- OAI.MeasureTheory.CompactFactors.RelativeCenters
section
namespace ParishFactor

noncomputable section

open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators
open Polynomial
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open MeasureTheory ProbabilityTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open MeasureTheory Filter
open scoped Topology ENNReal NNReal

open MeasureTheory
open scoped ENNReal

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
namespace PlaneFiveColor.Spectral
open MeasureTheory ProbabilityTheory
variable [Carrier]

private instance dualStandardBorelSpace : StandardBorelSpace D := by
  have : TopologicalSpace.IsCompletelyMetrizableSpace (DiscreteE → Circle) := inferInstance
  have : PolishSpace D := ContinuousMonoidHom.isClosedEmbedding_coe.polishSpace
  infer_instance

private instance dualMulDistribAction : MulDistribMulAction K D where
  smul_one u := (scalarHom (kCoeff u)).map_one
  smul_mul u d e := (scalarHom (kCoeff u)).map_mul d e

private instance dualMeasurableConstSMul : MeasurableConstSMul K D where
  measurable_const_smul u := (continuous_scalar (kCoeff u)).measurable
end PlaneFiveColor.Spectral

end

end ParishFactor
end

-- OAI.MeasureTheory.CompactFactors.ConditionalLimits
section
namespace ParishFactor

noncomputable section

open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators
open Polynomial
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open MeasureTheory ProbabilityTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open MeasureTheory Filter
open scoped Topology ENNReal NNReal
open MeasureTheory
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open MeasureTheory ProbabilityTheory

namespace EuclideanFiveColor.LimitDensity
open MeasureTheory Filter
open scoped Topology BigOperators
variable {Y : Type*} [mY : MeasurableSpace Y]

private def clip (C t : ℝ) : ℝ := max (-C) (min C t)
lemma clip_bound {C : ℝ} (hC : 0 ≤ C) (t : ℝ) : |clip C t| ≤ C := by
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
lemma clip_eq {C t : ℝ} (ht : |t| ≤ C) : clip C t = t := by
  obtain ⟨hl, hu⟩ := abs_le.mp ht
  simp only [clip, min_eq_right hu, max_eq_right hl]
lemma continuous_clip (C : ℝ) : Continuous (clip C) := by
  unfold clip
  fun_prop

theorem bounded_vector_approximation
    (ν : Measure Y) [IsProbabilityMeasure ν] (ℱ : Filtration ℕ mY)
    (m : ℕ) (H : Y → Fin m → ℂ) (hH : Measurable[⨆ n, ℱ n] H)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ y, ‖H y‖ ≤ C) :
    ∃ Hn : ℕ → Y → Fin m → ℂ,
      (∀ n, Measurable[ℱ n] (Hn n)) ∧
      (∀ n y, ‖Hn n y‖ ≤ 2*C) ∧
      (∀ n, Integrable (fun y => dist (H y) (Hn n y)^2) ν) ∧
      Tendsto (fun n => ∫ y, dist (H y) (Hn n y)^2 ∂ν) atTop (𝓝 0) := by
  classical
  have hle : (⨆ n, ℱ n) ≤ mY := iSup_le fun n => ℱ.le n
  have hHm : Measurable H := hH.mono hle le_rfl
  let R : Fin m → Y → ℝ := fun j y => (H y j).re
  let I : Fin m → Y → ℝ := fun j y => (H y j).im
  have hR (j : Fin m) : Measurable[⨆ n, ℱ n] (R j) := by
    let : MeasurableSpace Y := ⨆ n, ℱ n
    exact Complex.measurable_re.comp ((measurable_pi_iff.mp hH) j)
  have hI (j : Fin m) : Measurable[⨆ n, ℱ n] (I j) := by
    let : MeasurableSpace Y := ⨆ n, ℱ n
    exact Complex.measurable_im.comp ((measurable_pi_iff.mp hH) j)
  have hRB (j : Fin m) (y : Y) : |R j y| ≤ C :=
    (Complex.abs_re_le_norm _).trans ((norm_le_pi_norm (H y) j).trans (hbound y))
  have hIB (j : Fin m) (y : Y) : |I j y| ≤ C :=
    (Complex.abs_im_le_norm _).trans ((norm_le_pi_norm (H y) j).trans (hbound y))
  have hRi (j : Fin m) : Integrable (R j) ν :=
    Integrable.of_bound ((hR j).mono hle le_rfl).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs] using hRB j y)
  have hIi (j : Fin m) : Integrable (I j) ν :=
    Integrable.of_bound ((hI j).mono hle le_rfl).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs] using hIB j y)
  let Hn : ℕ → Y → Fin m → ℂ := fun n y j =>
    (clip C ((ν[R j | ℱ n]) y) : ℂ) + Complex.I * (clip C ((ν[I j | ℱ n]) y) : ℂ)
  have hHn (n : ℕ) : Measurable[ℱ n] (Hn n) := by
    let : MeasurableSpace Y := ℱ n
    apply measurable_pi_iff.mpr
    intro j
    exact ((Complex.measurable_ofReal.comp ((continuous_clip C).measurable.comp
      stronglyMeasurable_condExp.measurable))).add
      (measurable_const.mul (Complex.measurable_ofReal.comp ((continuous_clip C).measurable.comp
        stronglyMeasurable_condExp.measurable)))
  have hBn (n : ℕ) (y : Y) : ‖Hn n y‖ ≤ 2*C := by
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro j
    calc
      ‖Hn n y j‖ ≤ ‖(clip C ((ν[R j | ℱ n]) y) : ℂ)‖ +
          ‖Complex.I * (clip C ((ν[I j | ℱ n]) y) : ℂ)‖ := norm_add_le _ _
      _ = |clip C ((ν[R j | ℱ n]) y)| + |clip C ((ν[I j | ℱ n]) y)| := by
        simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ 2*C := by linarith [clip_bound hC ((ν[R j | ℱ n]) y), clip_bound hC ((ν[I j | ℱ n]) y)]
  have hconv : ∀ᵐ y ∂ν, Tendsto (fun n => Hn n y) atTop (𝓝 (H y)) := by
    have hr (j : Fin m) := (hRi j).tendsto_ae_condExp (hR j).stronglyMeasurable
    have hi (j : Fin m) := (hIi j).tendsto_ae_condExp (hI j).stronglyMeasurable
    filter_upwards [ae_all_iff.mpr hr, ae_all_iff.mpr hi] with y hyr hyi
    apply tendsto_pi_nhds.mpr
    intro j
    have hr' := (continuous_clip C).continuousAt.tendsto.comp (hyr j)
    have hi' := (continuous_clip C).continuousAt.tendsto.comp (hyi j)
    rw [clip_eq (hRB j y)] at hr'
    rw [clip_eq (hIB j y)] at hi'
    have ht := (Complex.continuous_ofReal.continuousAt.tendsto.comp hr').add
      ((Complex.continuous_ofReal.continuousAt.tendsto.comp hi').const_mul Complex.I)
    convert ht using 1
    · rfl
    · simp only [R, I, Complex.re_add_im, mul_comm Complex.I]
  have hdist (n : ℕ) (y : Y) : dist (H y) (Hn n y)^2 ≤ (3*C)^2 := by
    have hd : dist (H y) (Hn n y) ≤ 3*C :=
      (dist_le_norm_add_norm _ _).trans (by linarith [hbound y, hBn n y])
    exact pow_le_pow_left₀ dist_nonneg hd 2
  have hint (n : ℕ) : Integrable (fun y => dist (H y) (Hn n y)^2) ν :=
    Integrable.of_bound ((hHm.dist ((hHn n).mono (ℱ.le n) le_rfl)).pow_const 2).aestronglyMeasurable
      ((3*C)^2) (Filter.Eventually.of_forall fun y => by
        simpa only [Real.norm_eq_abs, abs_sq] using hdist n y)
  refine ⟨Hn, hHn, hBn, hint, ?_⟩
  simpa only [integral_zero] using tendsto_integral_of_dominated_convergence
    (f := fun _ : Y => (0 : ℝ)) (fun _ : Y => (3*C)^2)
    (fun n => (hint n).aestronglyMeasurable) (integrable_const _) (fun n =>
      Filter.Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs, abs_sq] using hdist n y)
    (hconv.mono fun y hy => by
      have ht := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => H y) atTop (𝓝 (H y))).dist hy).pow 2
      simpa only [dist_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using ht)

theorem generated_factor_approximation
    {Z : ℕ → Type*} [∀ n, MeasurableSpace (Z n)]
    (ν : Measure Y) [IsProbabilityMeasure ν] (p : ∀ n, Y → Z n)
    (hp : ∀ n, Measurable (p n))
    (hmono : Monotone (fun n => (inferInstance : MeasurableSpace (Z n)).comap (p n)))
    (hgen : (⨆ n, (inferInstance : MeasurableSpace (Z n)).comap (p n)) = mY)
    (m : ℕ) (H : Y → Fin m → ℂ) (hH : Measurable H)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ y, ‖H y‖ ≤ C)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n, ∃ H₀ : Z n → Fin m → ℂ, Measurable H₀ ∧ (∀ z, ‖H₀ z‖ ≤ 2*C) ∧
      Integrable (fun y => dist (H y) (H₀ (p n y))^2) ν ∧
      (∫ y, dist (H y) (H₀ (p n y))^2 ∂ν) < ε^2 := by
  classical
  let ℱ : Filtration ℕ mY := ⟨fun n => (inferInstance : MeasurableSpace (Z n)).comap (p n),
    hmono, fun n => (hp n).comap_le⟩
  have hHg : Measurable[⨆ n, ℱ n] H := by
    change Measurable[⨆ n, (inferInstance : MeasurableSpace (Z n)).comap (p n)] H
    rwa [hgen]
  obtain ⟨Hn, hHn, hBn, hint, hlim⟩ := bounded_vector_approximation ν ℱ m H hHg C hC hbound
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds (sq_pos_of_pos hε))).exists
  obtain ⟨H', hH', heq⟩ := (hHn n).exists_eq_measurable_comp
  let H₀ : Z n → Fin m → ℂ := fun z => if ‖H' z‖ ≤ 2*C then H' z else 0
  have hH₀ : Measurable H₀ := hH'.piecewise (measurableSet_le hH'.norm measurable_const) measurable_const
  have hB₀ (z : Z n) : ‖H₀ z‖ ≤ 2*C := by
    by_cases hz : ‖H' z‖ ≤ 2*C
    · simpa only [H₀, if_pos hz] using hz
    · simp only [H₀, if_neg hz, norm_zero]; positivity
  have heq₀ (y : Y) : H₀ (p n y) = Hn n y := by
    have hy := congrFun heq y
    simp only [Function.comp_apply] at hy
    have hb : ‖H' (p n y)‖ ≤ 2*C := hy ▸ hBn n y
    simpa only [H₀, if_pos hb] using hy.symm
  refine ⟨n, H₀, hH₀, hB₀, ?_, ?_⟩
  · simpa only [heq₀] using hint n
  · simpa only [heq₀] using hn

end EuclideanFiveColor.LimitDensity
end

end ParishFactor
end

-- OAI.MeasureTheory.CompactFactors.Kernels
section
namespace ParishFactor

noncomputable section

open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators
open Polynomial
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open MeasureTheory ProbabilityTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open MeasureTheory Filter
open scoped Topology ENNReal NNReal
open MeasureTheory
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open MeasureTheory ProbabilityTheory

namespace EuclideanFiveColor.KernelCompact
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

lemma norm_integral_sq (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → ℂ) (hf : Integrable f μ)
    (hf₂ : Integrable (fun x => ‖f x‖^2) μ) :
    ‖∫ x, f x ∂μ‖^2 ≤ ∫ x, ‖f x‖^2 ∂μ := by
  let a := ∫ x, ‖f x‖ ∂μ
  have ha : 0 ≤ a := integral_nonneg fun _ => norm_nonneg _
  have hvar : 0 ≤ (∫ x, ‖f x‖^2 ∂μ) - a^2 := by
    have h : (0 : ℝ) ≤ ∫ x, (‖f x‖-a)^2 ∂μ :=
      integral_nonneg (fun x => sq_nonneg (‖f x‖-a))
    have he : (fun x => (‖f x‖-a)^2) = fun x => ‖f x‖^2 - (2*a)*‖f x‖ + a^2 := by
      funext x; ring
    rw [he, integral_add (f := fun x => ‖f x‖^2 - (2*a)*‖f x‖) (g := fun _ => a^2) (hf₂.sub (hf.norm.const_mul (2*a))) (integrable_const (a^2)),
      integral_sub (f := fun x => ‖f x‖^2) (g := fun x => (2*a)*‖f x‖) hf₂ (hf.norm.const_mul (2*a)), integral_const_mul] at h
    simp only [integral_const, probReal_univ, one_smul] at h
    change 0 ≤ (∫ x, ‖f x‖^2 ∂μ) - (2*a)*a + a^2 at h
    nlinarith
  have hn : ‖∫ x, f x ∂μ‖ ≤ a := norm_integral_le_integral_norm f
  nlinarith [norm_nonneg (∫ x, f x ∂μ)]
end EuclideanFiveColor.KernelCompact

namespace EuclideanFiveColor.RectangleDensity
open MeasureTheory
open scoped BigOperators
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated X] [MeasurableSpace.CountablyGenerated Y]

private abbrev Code (n : ℕ) := Fin n → Bool

private def code (X : Type*) [MeasurableSpace X] [MeasurableSpace.CountablyGenerated X]
    (n : ℕ) (x : X) : Code n := by
  classical
  exact fun i => if x ∈ MeasurableSpace.natGeneratingSequence X i then true else false

lemma measurable_code (n : ℕ) : Measurable (code X n) := by
  classical
  apply measurable_pi_iff.mpr
  intro i
  exact measurable_const.piecewise (MeasurableSpace.measurableSet_natGeneratingSequence (α := X) i) measurable_const

private def pairCode (n : ℕ) (z : X × Y) : Code n × Code n := (code X n z.1, code Y n z.2)

lemma measurable_pairCode (n : ℕ) : Measurable (pairCode (X := X) (Y := Y) n) :=
  ((measurable_code n).comp measurable_fst).prodMk ((measurable_code n).comp measurable_snd)

lemma pairCode_mono : Monotone (fun n =>
    (inferInstance : MeasurableSpace (Code n × Code n)).comap (pairCode (X := X) (Y := Y) n)) := by
  intro n m hnm
  apply MeasurableSpace.comap_le_comap_of_eq_comp
    (fun z : Code m × Code m => (fun i : Fin n => z.1 (Fin.castLE hnm i), fun i : Fin n => z.2 (Fin.castLE hnm i)))
    (measurable_of_countable _)
  rfl

lemma pairCode_generates : (⨆ n,
    (inferInstance : MeasurableSpace (Code n × Code n)).comap (pairCode (X := X) (Y := Y) n)) =
      (inferInstance : MeasurableSpace (X × Y)) := by
  classical
  apply le_antisymm (iSup_le fun n => (measurable_pairCode n).comap_le)
  let m := ⨆ n, (inferInstance : MeasurableSpace (Code n × Code n)).comap (pairCode (X := X) (Y := Y) n)
  have hp (n : ℕ) : Measurable[m] (pairCode (X := X) (Y := Y) n) :=
    (comap_measurable _).mono (by exact le_iSup (fun n =>
      (inferInstance : MeasurableSpace (Code n × Code n)).comap (pairCode (X := X) (Y := Y) n)) n) le_rfl
  have hx : @Measurable (X × Y) X m _ Prod.fst := by
    rw [← MeasurableSpace.generateFrom_natGeneratingSequence X]
    apply measurable_generateFrom
    rintro _ ⟨n, rfl⟩
    have h : Measurable[m] (fun z : X × Y => (pairCode (X := X) (Y := Y) (n+1) z).1 ⟨n, by omega⟩) :=
      (measurable_pi_apply _).comp (measurable_fst.comp (hp (n+1)))
    have hs := h (measurableSet_singleton true)
    convert hs using 1
    ext z
    simp [pairCode, code]
  have hy : @Measurable (X × Y) Y m _ Prod.snd := by
    rw [← MeasurableSpace.generateFrom_natGeneratingSequence Y]
    apply measurable_generateFrom
    rintro _ ⟨n, rfl⟩
    have h : Measurable[m] (fun z : X × Y => (pairCode (X := X) (Y := Y) (n+1) z).2 ⟨n, by omega⟩) :=
      (measurable_pi_apply _).comp (measurable_snd.comp (hp (n+1)))
    have hs := h (measurableSet_singleton true)
    convert hs using 1
    ext z
    simp [pairCode, code]
  have hi := (hx.prodMk hy).comap_le
  have hfun : (fun z : X × Y => (z.1, z.2)) = id := rfl
  rw [hfun] at hi
  simpa only [MeasurableSpace.comap_id] using hi

theorem bounded_rectangles (ν : Measure (X × Y)) [IsProbabilityMeasure ν]
    (L : X × Y → ℂ) (hL : Measurable L) (C : ℝ) (hC : 0 ≤ C)
    (hLC : ∀ z, ‖L z‖ ≤ C) (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (a : Code n × Code n → ℂ),
      (∀ z, ‖a z‖ ≤ 2*C) ∧
      Integrable (fun z => ‖L z - a (pairCode n z)‖^2) ν ∧
      (∫ z, ‖L z - a (pairCode n z)‖^2 ∂ν) < ε^2 := by
  let H : X × Y → Fin 1 → ℂ := fun z _ => L z
  have hH : Measurable H := measurable_pi_iff.mpr fun _ => hL
  have hHB (z : X × Y) : ‖H z‖ ≤ C := by
    rw [pi_norm_le_iff_of_nonneg hC]; intro i; exact hLC z
  obtain ⟨n, H₀, _, hB, hi, he⟩ := LimitDensity.generated_factor_approximation ν
    (fun n => pairCode (X := X) (Y := Y) n) measurable_pairCode
    pairCode_mono pairCode_generates 1 H hH C hC hHB ε hε
  have hd (z : X × Y) : dist (H z) (H₀ (pairCode n z)) = ‖L z - H₀ (pairCode n z) 0‖ := by
    rw [dist_eq_norm]
    have heq : H z - H₀ (pairCode n z) = fun _ : Fin 1 => L z - H₀ (pairCode n z) 0 := by
      funext i
      have : i = 0 := Subsingleton.elim _ _
      subst i
      rfl
    rw [heq, pi_norm_const]
  refine ⟨n, fun z => H₀ z 0, fun z => (norm_le_pi_norm (H₀ z) 0).trans (hB z), ?_, ?_⟩
  · simpa only [hd] using hi
  · simpa only [hd] using he

end EuclideanFiveColor.RectangleDensity
open MeasureTheory ProbabilityTheory
namespace EuclideanFiveColor.RelativeProduct
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]

private def law (μ : Measure X) [IsFiniteMeasure μ] (q : X → Y) (hq : Measurable q) : Measure (X × X) :=
  μ ⊗ₘ (condDistrib id q μ).comap q hq

lemma law_eq_mixture (μ : Measure X) [IsProbabilityMeasure μ]
    (q : X → Y) (hq : Measurable q) :
    law μ q hq = ((condDistrib id q μ).prod (condDistrib id q μ)) ∘ₘ μ.map q := by
  let κ := condDistrib id q μ
  ext s hs
  rw [law, Measure.compProd_apply hs, Measure.bind_apply hs (Kernel.measurable _).aemeasurable]
  have he := ConditionalFiber.comp_identity_fiber μ q hq
  change κ ∘ₘ μ.map q = μ at he
  have hm : Measurable (fun x => (κ (q x)) (Prod.mk x ⁻¹' s)) :=
    Kernel.measurable_kernel_prodMk_left (κ := κ.comap q hq) hs
  change (∫⁻ x, κ (q x) (Prod.mk x ⁻¹' s) ∂μ) = _
  conv_lhs => rw [← he]
  rw [Measure.lintegral_bind (Kernel.measurable κ).aemeasurable hm.aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [ConditionalFiber.ae_in_own_fiber μ q hq] with y hy
  rw [Kernel.prod_apply, Measure.prod_apply hs]
  exact lintegral_congr_ae (hy.mono fun x hx => by change κ (q x) _ = _; rw [hx])

lemma law_swap (μ : Measure X) [IsProbabilityMeasure μ]
    (q : X → Y) (hq : Measurable q) :
    (law μ q hq).map Prod.swap = law μ q hq := by
  rw [law_eq_mixture]
  rw [Measure.map_comp _ _ measurable_swap, Kernel.map_prod_swap]

end EuclideanFiveColor.RelativeProduct

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace EuclideanFiveColor.RelativeProduct
open MeasureTheory ProbabilityTheory
variable {K X Y : Type*} [Group K] [MulAction K X] [MulAction K Y]
  [MeasurableSpace X] [MeasurableSpace Y]
  [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]
  [MeasurableConstSMul K X] [MeasurableConstSMul K Y]

private instance law_probability (μ : Measure X) [IsProbabilityMeasure μ]
    (q : X → Y) (hq : Measurable q) : IsProbabilityMeasure (law μ q hq) := by
  dsimp [law]; infer_instance

omit [StandardBorelSpace Y] [Nonempty Y] in
lemma conditional_covariance (μ : Measure X) [IsProbabilityMeasure μ]
    (q : X → Y) (hq : Measurable q)
    (hpres : ∀ k : K, MeasurePreserving (fun x : X => k • x) μ μ)
    (hqcov : ∀ k : K, ∀ᵐ x ∂μ, q (k • x) = k • q x) (k : K) :
    ∀ᵐ y ∂μ.map q, condDistrib id q μ (k • y) =
      (condDistrib id q μ y).map (fun x => k • x) :=
  KernelSupport.condDistrib_equivariant μ id q measurable_id hq
    (MeasurableEquiv.smul k) (MeasurableEquiv.smul k) (fun x => k • x)
    (measurable_const_smul k) (hpres k) (hqcov k) (Filter.Eventually.of_forall fun _ => rfl)

lemma law_preserving (μ : Measure X) [IsProbabilityMeasure μ]
    (q : X → Y) (hq : Measurable q)
    (hpres : ∀ k : K, MeasurePreserving (fun x : X => k • x) μ μ)
    (hqcov : ∀ k : K, ∀ᵐ x ∂μ, q (k • x) = k • q x) (k : K) :
    MeasurePreserving (fun z : X × X => (k • z.1,k • z.2)) (law μ q hq) (law μ q hq) := by
  let κ := condDistrib id q μ
  let ν := μ.map q
  have hS := measurable_const_smul (M := K) (α := X) k
  have hR := measurable_const_smul (M := K) (α := Y) k
  have hν : ν.map (fun y => k • y) = ν := by
    dsimp [ν]
    rw [Measure.map_map hR hq]
    calc
      _ = μ.map (q ∘ (fun x => k • x)) := Measure.map_congr (Filter.EventuallyEq.symm (hqcov k))
      _ = _ := by rw [← Measure.map_map hq hS, (hpres k).map_eq]
  have hc := conditional_covariance μ q hq hpres hqcov k
  refine ⟨hS.prodMap hS, ?_⟩
  change (law μ q hq).map (Prod.map (fun x => k • x) (fun x => k • x)) = _
  rw [law_eq_mixture, Measure.map_comp _ _ (hS.prodMap hS), ← Kernel.map_prod_map _ _ hS hS]
  change ((κ.map (fun x => k • x)).prod (κ.map (fun x => k • x))) ∘ₘ ν = _
  calc
    _ = ((κ.prod κ).comap (fun y => k • y) hR) ∘ₘ ν := by
      apply Measure.comp_congr
      filter_upwards [hc] with y hy
      simp only [Kernel.prod_apply, Kernel.map_apply _ hS, Kernel.comap_apply]
      rw [hy]
    _ = (κ.prod κ) ∘ₘ ν.map (fun y => k • y) := by
      ext s hs
      rw [Measure.bind_apply hs (Kernel.measurable _).aemeasurable,
        Measure.bind_apply hs (Kernel.measurable _).aemeasurable,
        lintegral_map ((κ.prod κ).measurable_coe hs) hR]
      rfl
    _ = (κ.prod κ) ∘ₘ ν := by rw [hν]

lemma law_invariant (μ : Measure X) [IsProbabilityMeasure μ]
    (q : X → Y) (hq : Measurable q)
    (hpres : ∀ k : K, MeasurePreserving (fun x : X => k • x) μ μ)
    (hqcov : ∀ k : K, ∀ᵐ x ∂μ, q (k • x) = k • q x) :
    SMulInvariantMeasure K (X × X) (law μ q hq) := by
  constructor
  intro k s hs
  exact (law_preserving μ q hq hpres hqcov k).measure_preimage hs.nullMeasurableSet

end EuclideanFiveColor.RelativeProduct
end

end ParishFactor
end

-- OAI.MeasureTheory.CompactFactors.BoundedFunctions
section
namespace ParishFactor

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

private def l2 : Func X →ₗ[ℝ] Lp ℂ 2 μ where
  toFun := lp μ 2
  map_add' := lp_add μ 2
  map_smul' := lp_smul μ 2

lemma l2_ae (f : Func X) : l2 μ f =ᵐ[μ] f := coe_lp μ 2 f

lemma l2_eq_iff (f g : Func X) : l2 μ f = l2 μ g ↔ f =ᵐ[μ] g := by
  constructor
  · intro h
    exact (l2_ae μ f).symm.trans (h ▸ l2_ae μ g)
  · exact lp_congr μ 2

lemma integral_l2 (f : Func X) : ∫ x, l2 μ f x ∂μ = ∫ x, f x ∂μ :=
  integral_congr_ae (l2_ae μ f)

lemma inner_l2 (f g : Func X) :
    inner ℝ (l2 μ f) (l2 μ g) = ∫ x, inner ℝ (f x) (g x) ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [l2_ae μ f, l2_ae μ g] with x hx hy
  rw [hx, hy]

lemma l2_norm_mul_le (f g : Func X) {C : ℝ} (hf : ∀ x, ‖f x‖ ≤ C) :
    ‖l2 μ (f*g)‖ ≤ C * ‖l2 μ g‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [l2_ae μ (f*g), l2_ae μ g] with x hx hy
  rw [hx, hy, mul_apply, norm_mul]
  exact mul_le_mul_of_nonneg_right (hf x) (norm_nonneg _)

lemma l2_norm_le [IsProbabilityMeasure μ] (f : Func X) {C : ℝ} (hf : ∀ x, ‖f x‖ ≤ C) :
    ‖l2 μ f‖ ≤ C := by
  have hn : ∀ᵐ x ∂μ, ‖l2 μ f x‖ ≤ C := (l2_ae μ f).mono (fun x hx => by rw [hx]; exact hf x)
  have hC : 0 ≤ C := by
    obtain ⟨x, hx⟩ := hn.exists
    exact (norm_nonneg _).trans hx
  simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound hC hn

end
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

lemma integrable (μ : Measure X) [IsFiniteMeasure μ] (f : Func X) : Integrable (f : X → ℂ) μ :=
  (memLp μ f 1).integrable le_rfl

lemma integrable_norm_sq (μ : Measure X) [IsFiniteMeasure μ] (f : Func X) :
    Integrable (fun x => ‖f x‖^2) μ :=
  Integrable.of_bound ((measurable f).norm.pow_const 2).aestronglyMeasurable ((bound f : ℝ)^2)
    (.of_forall (fun x => by simpa only [Real.norm_eq_abs, abs_sq] using
      (pow_le_pow_left₀ (norm_nonneg _) (norm_le_bound f x) 2)))

lemma norm_l2_sq (μ : Measure X) [IsFiniteMeasure μ] (f : Func X) :
    ‖l2 μ f‖^2 = ∫ x, ‖f x‖^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, inner_l2]
  simp only [real_inner_self_eq_norm_sq]

private def expect (κ : Kernel Y X) [IsMarkovKernel κ] (f : Func X) : Func Y :=
  ⟨fun y => ∫ x, f x ∂κ y, (measurable f).stronglyMeasurable.integral_kernel.measurable,
    bound f, fun y => by
      simpa only [probReal_univ, mul_one] using
        norm_integral_le_of_norm_le_const (μ := κ y) (.of_forall (norm_le_bound f))⟩

@[simp] lemma expect_apply (κ : Kernel Y X) [IsMarkovKernel κ] (f : Func X) (y : Y) :
    expect κ f y = ∫ x, f x ∂κ y := rfl

lemma expect_bound (κ : Kernel Y X) [IsMarkovKernel κ] (f : Func X)
    {C : ℝ} (hf : ∀ x, ‖f x‖ ≤ C) (y : Y) : ‖expect κ f y‖ ≤ C := by
  simpa only [expect_apply, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (μ := κ y) (.of_forall hf)

lemma expect_add (κ : Kernel Y X) [IsMarkovKernel κ] (f g : Func X) :
    expect κ (f+g) = expect κ f + expect κ g := by
  ext y; exact integral_add (integrable (κ y) f) (integrable (κ y) g)

lemma expect_smul (κ : Kernel Y X) [IsMarkovKernel κ] (c : ℝ) (f : Func X) :
    expect κ (c • f) = c • expect κ f := by
  ext y; exact integral_smul c f

private def expectLinear (κ : Kernel Y X) [IsMarkovKernel κ] : Func X →ₗ[ℝ] Func Y where
  toFun := expect κ
  map_add' := expect_add κ
  map_smul' := expect_smul κ

lemma expect_conj (κ : Kernel Y X) [IsMarkovKernel κ] (f : Func X) :
    expect κ (bmConj f) = bmConj (expect κ f) := by
  ext y; exact integral_conj

variable [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]
variable (μ : Measure X) [IsProbabilityMeasure μ] (q : X → Y) (hq : Measurable q)

private abbrev conditional (f : Func X) : Func Y := expect (condDistrib id q μ) f

private def project (f : Func X) : Func X := comp (conditional μ q f) q hq

omit [StandardBorelSpace Y] [Nonempty Y] in
@[simp] lemma project_apply (f : Func X) (x : X) :
    project μ q hq f x = conditional μ q f (q x) := rfl

omit [StandardBorelSpace Y] [Nonempty Y] in
include hq in
lemma conditional_integral (f : Func X) : ∫ y, conditional μ q f y ∂μ.map q = ∫ x, f x ∂μ :=
  ConditionalFiber.integral_fiber μ q hq f (integrable μ f)

omit [StandardBorelSpace Y] [Nonempty Y] in
lemma project_integral (f : Func X) : ∫ x, project μ q hq f x ∂μ = ∫ x, f x ∂μ := by
  rw [← conditional_integral μ q hq f]
  exact (integral_map hq.aemeasurable (measurable (conditional μ q f)).aestronglyMeasurable).symm

lemma conditional_pullout (f : Func X) (b : Func Y) :
    conditional μ q (f * comp b q hq) =ᵐ[μ.map q] (conditional μ q f * b) := by
  filter_upwards [ConditionalFiber.ae_in_own_fiber μ q hq] with y hy
  change (∫ x, f x * b (q x) ∂condDistrib id q μ y) =
    (∫ x, f x ∂condDistrib id q μ y) * b y
  rw [← integral_mul_const]
  exact integral_congr_ae (hy.mono (fun x hx => by dsimp; rw [hx]))

lemma conditional_lift (b : Func Y) :
    conditional μ q (comp b q hq) =ᵐ[μ.map q] b := by
  filter_upwards [ConditionalFiber.ae_in_own_fiber μ q hq] with y hy
  change (∫ x, b (q x) ∂condDistrib id q μ y) = b y
  rw [integral_congr_ae (hy.mono (fun x hx => congrArg b hx))]
  simp

omit [StandardBorelSpace Y] [Nonempty Y] in
include hq in
lemma conditional_congr {f g : Func X} (h : f =ᵐ[μ] g) :
    conditional μ q f =ᵐ[μ.map q] conditional μ q g :=
  (ConditionalFiber.ae_fiber_of_ae μ q hq h).mono (fun _ hy => integral_congr_ae hy)

omit [StandardBorelSpace Y] [Nonempty Y] in
include hq in
lemma conditional_norm_l2_le (f : Func X) :
    ‖l2 (μ.map q) (conditional μ q f)‖ ≤ ‖l2 μ f‖ := by
  have hs : ‖l2 (μ.map q) (conditional μ q f)‖^2 ≤ ‖l2 μ f‖^2 := by
    rw [norm_l2_sq, norm_l2_sq, ← ConditionalFiber.integral_fiber μ q hq
      (fun x => ‖f x‖^2) (integrable_norm_sq μ f)]
    apply integral_mono
    · exact integrable_norm_sq _ _
    · exact ConditionalFiber.integrable_fiber_integral μ q hq _ (integrable_norm_sq μ f)
    · intro y
      exact KernelCompact.norm_integral_sq _ f (integrable _ f) (integrable_norm_sq _ f)
  nlinarith [norm_nonneg (l2 (μ.map q) (conditional μ q f)), norm_nonneg (l2 μ f)]

omit [StandardBorelSpace Y] [Nonempty Y] in
lemma project_eq_condexp (f : Func X) :
    project μ q hq f =ᵐ[μ] μ[(f : X → ℂ) | MeasurableSpace.comap q ‹MeasurableSpace Y›] :=
  (condExp_ae_eq_integral_condDistrib_id hq (integrable μ f)).symm

end EuclideanFiveColor.BoundedMeasurable

end

end ParishFactor
end

-- OAI.MeasureTheory.CompactFactors.RelativeProducts
section
namespace ParishFactor

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal
open scoped RealInnerProductSpace BoundedContinuousFunction

namespace EuclideanFiveColor.RelativeProduct
open MeasureTheory ProbabilityTheory
variable {K X Y : Type*} [AddGroup K] [AddAction K X] [AddAction K Y]
  [MeasurableSpace X] [MeasurableSpace Y]
  [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]
  [MeasurableConstVAdd K X] [MeasurableConstVAdd K Y]

private instance law_probability_add (μ : Measure X) [IsProbabilityMeasure μ]
    (q : X → Y) (hq : Measurable q) : IsProbabilityMeasure (law μ q hq) := by
  dsimp [law]; infer_instance

omit [StandardBorelSpace Y] [Nonempty Y] in
lemma conditional_covariance_add (μ : Measure X) [IsProbabilityMeasure μ]
    (q : X → Y) (hq : Measurable q)
    (hpres : ∀ k : K, MeasurePreserving (fun x : X => k +ᵥ x) μ μ)
    (hqcov : ∀ k : K, ∀ᵐ x ∂μ, q (k +ᵥ x) = k +ᵥ q x) (k : K) :
    ∀ᵐ y ∂μ.map q, condDistrib id q μ (k +ᵥ y) =
      (condDistrib id q μ y).map (fun x => k +ᵥ x) :=
  KernelSupport.condDistrib_equivariant μ id q measurable_id hq
    (MeasurableEquiv.vadd k) (MeasurableEquiv.vadd k) (fun x => k +ᵥ x)
    (measurable_const_vadd k) (hpres k) (hqcov k) (Filter.Eventually.of_forall fun _ => rfl)

lemma law_preserving_add (μ : Measure X) [IsProbabilityMeasure μ]
    (q : X → Y) (hq : Measurable q)
    (hpres : ∀ k : K, MeasurePreserving (fun x : X => k +ᵥ x) μ μ)
    (hqcov : ∀ k : K, ∀ᵐ x ∂μ, q (k +ᵥ x) = k +ᵥ q x) (k : K) :
    MeasurePreserving (fun z : X × X => (k +ᵥ z.1,k +ᵥ z.2)) (law μ q hq) (law μ q hq) := by
  let κ := condDistrib id q μ
  let ν := μ.map q
  have hS := measurable_const_vadd (M := K) (α := X) k
  have hR := measurable_const_vadd (M := K) (α := Y) k
  have hν : ν.map (fun y => k +ᵥ y) = ν := by
    dsimp [ν]
    rw [Measure.map_map hR hq]
    calc
      _ = μ.map (q ∘ (fun x => k +ᵥ x)) := Measure.map_congr (Filter.EventuallyEq.symm (hqcov k))
      _ = _ := by rw [← Measure.map_map hq hS, (hpres k).map_eq]
  have hc := conditional_covariance_add μ q hq hpres hqcov k
  refine ⟨hS.prodMap hS, ?_⟩
  change (law μ q hq).map (Prod.map (fun x => k +ᵥ x) (fun x => k +ᵥ x)) = _
  rw [law_eq_mixture, Measure.map_comp _ _ (hS.prodMap hS), ← Kernel.map_prod_map _ _ hS hS]
  change ((κ.map (fun x => k +ᵥ x)).prod (κ.map (fun x => k +ᵥ x))) ∘ₘ ν = _
  calc
    _ = ((κ.prod κ).comap (fun y => k +ᵥ y) hR) ∘ₘ ν := by
      apply Measure.comp_congr
      filter_upwards [hc] with y hy
      simp only [Kernel.prod_apply, Kernel.map_apply _ hS, Kernel.comap_apply]
      rw [hy]
    _ = (κ.prod κ) ∘ₘ ν.map (fun y => k +ᵥ y) := by
      ext s hs
      rw [Measure.bind_apply hs (Kernel.measurable _).aemeasurable,
        Measure.bind_apply hs (Kernel.measurable _).aemeasurable,
        lintegral_map ((κ.prod κ).measurable_coe hs) hR]
      rfl
    _ = (κ.prod κ) ∘ₘ ν := by rw [hν]

lemma law_invariant_add (μ : Measure X) [IsProbabilityMeasure μ]
    (q : X → Y) (hq : Measurable q)
    (hpres : ∀ k : K, MeasurePreserving (fun x : X => k +ᵥ x) μ μ)
    (hqcov : ∀ k : K, ∀ᵐ x ∂μ, q (k +ᵥ x) = k +ᵥ q x) :
    VAddInvariantMeasure K (X × X) (law μ q hq) := by
  constructor
  intro k s hs
  exact (law_preserving_add μ q hq hpres hqcov k).measure_preimage hs.nullMeasurableSet

end EuclideanFiveColor.RelativeProduct

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal RealInnerProductSpace NNReal
namespace EuclideanFiveColor.BoundedMeasurable

section
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [StandardBorelSpace X] [Nonempty X]
variable (μ : Measure X) [IsProbabilityMeasure μ] (q : X → Y) (hq : Measurable q)

private def projectCLM : Lp ℂ 2 μ →L[ℝ] Lp ℂ 2 μ :=
  (lpMeas ℂ ℝ (MeasurableSpace.comap q ‹MeasurableSpace Y›) 2 μ).subtypeL.comp
    (condExpL2 ℂ ℝ hq.comap_le)

lemma projectCLM_l2 (f : Func X) : projectCLM μ q hq (l2 μ f) = l2 μ (project μ q hq f) := by
  apply Lp.ext
  exact ((memLp μ f 2).condExpL2_ae_eq_condExp (𝕜 := ℝ) hq.comap_le).trans
    ((project_eq_condexp μ q hq f).symm.trans (l2_ae μ (project μ q hq f)).symm)

lemma norm_project_l2 (f : Func X) :
    ‖l2 μ (project μ q hq f)‖ = ‖l2 (μ.map q) (conditional μ q f)‖ := by
  have : ‖l2 μ (project μ q hq f)‖^2 = ‖l2 (μ.map q) (conditional μ q f)‖^2 := by
    rw [norm_l2_sq, norm_l2_sq]
    exact (integral_map hq.aemeasurable
      ((measurable (conditional μ q f)).norm.pow_const 2).aestronglyMeasurable).symm
  nlinarith [norm_nonneg (l2 μ (project μ q hq f)),
    norm_nonneg (l2 (μ.map q) (conditional μ q f))]

end
section
variable {G X : Type*} [AddCommGroup G] [MeasurableSpace X]
  [AddAction G X] [MeasurableConstVAdd G X]

private def act (g : G) (f : Func X) : Func X := comp f (fun x => g +ᵥ x) (measurable_const_vadd g)
@[simp] lemma act_apply (g : G) (f : Func X) (x : X) : act g f x = f (g +ᵥ x) := rfl
lemma act_add (g h : G) (f : Func X) : act (g+h) f = act g (act h f) := by
  ext x
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
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]
variable (μ : Measure X) [IsProbabilityMeasure μ] (q : X → Y) (hq : Measurable q)

omit [StandardBorelSpace Y] [Nonempty Y] in
lemma project_sub (f g : Func X) : project μ q hq (f-g) = project μ q hq f - project μ q hq g := by
  ext x
  exact integral_sub (integrable _ f) (integrable _ g)
omit [StandardBorelSpace Y] [Nonempty Y] in
lemma project_bound (f : Func X) {C : ℝ} (hf : ∀ x, ‖f x‖ ≤ C) (x : X) :
    ‖project μ q hq f x‖ ≤ C := expect_bound _ f hf (q x)
lemma project_comp (b : Func Y) : project μ q hq (comp b q hq) =ᵐ[μ] comp b q hq :=
  ae_of_ae_map hq.aemeasurable (conditional_lift μ q hq b)
lemma project_project (f : Func X) : project μ q hq (project μ q hq f) =ᵐ[μ] project μ q hq f :=
  project_comp μ q hq _
lemma center_project_l2 (f : Func X) : l2 μ (project μ q hq (f-project μ q hq f)) = 0 := by
  rw [project_sub, map_sub]
  have : l2 μ (project μ q hq (project μ q hq f)) = l2 μ (project μ q hq f) :=
    (l2_eq_iff μ _ _).mpr (project_project μ q hq f)
  rw [this, sub_self]

lemma project_pullout (f : Func X) (b : Func Y) :
    project μ q hq (f * comp b q hq) =ᵐ[μ] project μ q hq f * comp b q hq :=
  ae_of_ae_map hq.aemeasurable (conditional_pullout μ q hq f b)

lemma integral_mul_lift (f : Func X) (b : Func Y) :
    ∫ x, (f * comp b q hq) x ∂μ = ∫ x, (project μ q hq f * comp b q hq) x ∂μ := by
  rw [← project_integral μ q hq (f * comp b q hq)]
  exact integral_congr_ae (project_pullout μ q hq f b)

variable {G : Type*} [AddCommGroup G] [AddAction G X] [AddAction G Y]
  [MeasurableConstVAdd G X] [MeasurableConstVAdd G Y] [VAddInvariantMeasure G X μ]
variable (hqcov : ∀ g : G, ∀ᵐ x ∂μ, q (g +ᵥ x) = g +ᵥ q x)

omit [StandardBorelSpace Y] [Nonempty Y] in
include hq hqcov in
lemma conditional_act (g : G) (f : Func X) :
    conditional μ q (act g f) =ᵐ[μ.map q] act g (conditional μ q f) := by
  filter_upwards [RelativeProduct.conditional_covariance_add μ q hq
    (fun k => measurePreserving_vadd k μ) hqcov g] with y hy
  change (∫ x, f (g +ᵥ x) ∂condDistrib id q μ y) = ∫ x, f x ∂condDistrib id q μ (g +ᵥ y)
  rw [hy]
  exact (integral_map (measurable_const_vadd g).aemeasurable (measurable f).aestronglyMeasurable).symm

omit [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]
  [IsProbabilityMeasure μ] [VAddInvariantMeasure G X μ] in
include hqcov in
lemma act_lift (g : G) (b : Func Y) :
    act g (comp b q hq) =ᵐ[μ] comp (act g b) q hq := by
  filter_upwards [hqcov g] with x hx
  simp only [act_apply, comp_apply, hx]

omit [StandardBorelSpace Y] [Nonempty Y] in
include hqcov in
lemma project_act (g : G) (f : Func X) :
    project μ q hq (act g f) =ᵐ[μ] act g (project μ q hq f) := by
  have he : project μ q hq (act g f) =ᵐ[μ] comp (act g (conditional μ q f)) q hq :=
    ae_of_ae_map hq.aemeasurable (conditional_act μ q hq hqcov g f)
  exact he.trans (act_lift μ q hq hqcov g _).symm

end EuclideanFiveColor.BoundedMeasurable

open MeasureTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace
namespace EuclideanFiveColor.BoundedMeasurable
variable (G X : Type*) [MeasurableSpace X]
private def familyAlgebra : Subalgebra ℂ (G → Func X) where
  carrier := {F | ∃ C : ℝ≥0, ∀ g x, ‖F g x‖ ≤ C}
  zero_mem' := ⟨0, by simp⟩
  one_mem' := ⟨1, by simp⟩
  add_mem' := by
    rintro F H ⟨C,hC⟩ ⟨D,hD⟩
    exact ⟨C+D, fun g x => (norm_add_le _ _).trans (add_le_add (hC g x) (hD g x))⟩
  mul_mem' := by
    rintro F H ⟨C,hC⟩ ⟨D,hD⟩
    refine ⟨C*D, fun g x => ?_⟩
    change ‖F g x * H g x‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul (hC g x) (hD g x) (norm_nonneg _) C.coe_nonneg
  algebraMap_mem' c := ⟨‖c‖₊, fun _ _ => le_rfl⟩
private abbrev Family := ↥(familyAlgebra G X)
variable {G X}
private instance : CoeFun (Family G X) (fun _ => G → Func X) := ⟨Subtype.val⟩
private instance familyRealModule : Module ℝ (Family G X) := Module.complexToReal (Family G X)

namespace Family
private def bound (F : Family G X) : ℝ≥0 := F.property.choose
lemma norm_le_bound (F : Family G X) (g : G) (x : X) : ‖F g x‖ ≤ F.bound := F.property.choose_spec g x
lemma ext {F H : Family G X} (h : ∀ g, F g = H g) : F = H := Subtype.ext (funext h)
@[simp] lemma add_apply (F H : Family G X) (g : G) : (F+H) g = F g + H g := rfl
@[simp] lemma mul_apply (F H : Family G X) (g : G) : (F*H) g = F g * H g := rfl
@[simp] lemma sub_apply (F H : Family G X) (g : G) : (F-H) g = F g - H g := rfl
@[simp] lemma zero_apply (g : G) : (0 : Family G X) g = 0 := rfl
@[simp] lemma one_apply (g : G) : (1 : Family G X) g = 1 := rfl
@[simp] lemma real_smul_apply (c : ℝ) (F : Family G X) (g : G) : (c • F) g = c • F g := rfl
@[simp] lemma complex_smul_apply (c : ℂ) (F : Family G X) (g : G) : (c • F) g = c • F g := rfl
@[simp] lemma prod_apply {ι : Type*} (s : Finset ι) (F : ι → Family G X) (g : G) :
    (∏ i ∈ s, F i) g = ∏ i ∈ s, F i g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih]

private def const (f : Func X) : Family G X := ⟨fun _ => f, BoundedMeasurable.bound f,
  fun _ => BoundedMeasurable.norm_le_bound f⟩
@[simp] lemma const_apply (f : Func X) (g : G) : const f g = f := rfl

private def bmConj (F : Family G X) : Family G X := ⟨fun g => BoundedMeasurable.bmConj (F g), F.bound,
  fun g x => by simpa using F.norm_le_bound g x⟩
@[simp] lemma conj_apply (F : Family G X) (g : G) : bmConj F g = BoundedMeasurable.bmConj (F g) := rfl

variable [TopologicalSpace G] [DiscreteTopology G]
variable (μ : Measure X) [IsProbabilityMeasure μ]

private def toL2 (F : Family G X) : G →ᵇ Lp ℂ 2 μ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun g => l2 μ (F g))
    continuous_of_discreteTopology F.bound (fun g => l2_norm_le μ (F g) (F.norm_le_bound g))
@[simp] lemma toL2_apply (F : Family G X) (g : G) : toL2 μ F g = l2 μ (F g) := rfl

private def l2Linear : Family G X →ₗ[ℝ] (G →ᵇ Lp ℂ 2 μ) where
  toFun := toL2 μ
  map_add' F H := by
    apply BoundedContinuousFunction.ext
    intro g
    exact (l2 μ).map_add (F g) (H g)
  map_smul' c F := by
    apply BoundedContinuousFunction.ext
    intro g
    exact (l2 μ).map_smul c (F g)

lemma l2Linear_apply (F : Family G X) : l2Linear μ F = toL2 μ F := rfl

variable [AddCommGroup G] (M : Amenable.Mean G)
private def avg : Family G X →ₗ[ℝ] Lp ℂ 2 μ where
  toFun F := M.vector (toL2 μ F)
  map_add' F H := by rw [← l2Linear_apply, map_add]; exact M.vector_add _ _
  map_smul' c F := by rw [← l2Linear_apply, map_smul]; exact M.vector_smul _ _

lemma avg_pair (F : Family G X) (h : Lp ℂ 2 μ) :
    inner ℝ (avg μ M F) h = M.map (Amenable.Mean.pairing (toL2 μ F) h) := M.vector_pair _ _

lemma avg_congr_ae {F H : Family G X} (he : ∀ g, F g =ᵐ[μ] H g) : avg μ M F = avg μ M H := by
  change M.vector (toL2 μ F) = M.vector (toL2 μ H)
  congr 1
  apply BoundedContinuousFunction.ext
  intro g
  exact (l2_eq_iff μ _ _).mpr (he g)

omit [TopologicalSpace G] [DiscreteTopology G]
variable [AddAction G X] [MeasurableConstVAdd G X]
private def orbit (φ : G →+ G) (f : Func X) : Family G X :=
  ⟨fun g => act (φ g) f, BoundedMeasurable.bound f,
    fun g x => BoundedMeasurable.norm_le_bound f (φ g +ᵥ x)⟩
@[simp] lemma orbit_apply (φ : G →+ G) (f : Func X) (g : G) : orbit φ f g = act (φ g) f := rfl
lemma orbit_add (φ : G →+ G) (f h : Func X) : orbit φ (f+h) = orbit φ f + orbit φ h := rfl
lemma orbit_sub (φ : G →+ G) (f h : Func X) : orbit φ (f-h) = orbit φ f - orbit φ h := rfl

end Family
end EuclideanFiveColor.BoundedMeasurable

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal RealInnerProductSpace NNReal
namespace EuclideanFiveColor.BoundedMeasurable
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

private def tensor (f : Func X) (g : Func Y) : Func (X×Y) :=
  comp f Prod.fst measurable_fst * comp g Prod.snd measurable_snd
@[simp] lemma tensor_apply (f : Func X) (g : Func Y) (z : X×Y) : tensor f g z = f z.1 * g z.2 := rfl
lemma tensor_mul (f h : Func X) (g k : Func Y) : tensor (f*h) (g*k) = tensor f g * tensor h k := by
  ext z; simp only [tensor_apply, mul_apply]; ring
lemma tensor_conj (f : Func X) (g : Func Y) : tensor (bmConj f) (bmConj g) = bmConj (tensor f g) := by
  ext z; simp only [tensor_apply, conj_apply, star_mul']

variable [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]
variable (μ : Measure X) [IsProbabilityMeasure μ] (q : X → Y) (hq : Measurable q)

lemma integral_law (f : Func (X×X)) :
    ∫ z, f z ∂(RelativeProduct.law μ q hq) =
      ∫ y, (∫ z, f z ∂(condDistrib id q μ y).prod (condDistrib id q μ y)) ∂μ.map q := by
  have hi := integrable (RelativeProduct.law μ q hq) f
  rw [RelativeProduct.law_eq_mixture, Measure.comp_eq_comp_const_apply] at hi
  have he := Kernel.integral_comp hi
  simpa only [Kernel.const_apply, Kernel.prod_apply, ← Measure.comp_eq_comp_const_apply,
    ← RelativeProduct.law_eq_mixture μ q hq] using he

lemma integral_tensor (f g : Func X) :
    ∫ z, tensor f g z ∂(RelativeProduct.law μ q hq) =
      ∫ y, conditional μ q f y * conditional μ q g y ∂μ.map q := by
  rw [integral_law]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => integral_prod_mul f g)

lemma integral_tensor_self (f : Func X) :
    ∫ z, tensor f (bmConj f) z ∂(RelativeProduct.law μ q hq) =
      (‖l2 (μ.map q) (conditional μ q f)‖^2 : ℝ) := by
  rw [integral_tensor, norm_l2_sq]
  simp only [conditional, expect_conj, conj_apply]
  change (∫ y, conditional μ q f y * star (conditional μ q f y) ∂μ.map q) = _
  calc
    _ = ∫ y, ((‖conditional μ q f y‖^2 : ℝ) : ℂ) ∂μ.map q := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => (Complex.mul_conj _).trans
        (congrArg Complex.ofReal (Complex.normSq_eq_norm_sq _))
    _ = _ := integral_complex_ofReal

lemma inner_tensor (v w : Func X) :
    inner ℝ (l2 (RelativeProduct.law μ q hq) (tensor w (bmConj w)))
      (l2 (RelativeProduct.law μ q hq) (tensor (bmConj v) v)) =
      ‖l2 (μ.map q) (conditional μ q (v*w))‖^2 := by
  rw [real_inner_comm, inner_l2]
  have he : (fun z : X×X => inner ℝ (tensor (bmConj v) v z) (tensor w (bmConj w) z)) =
      (fun z => (tensor (v*w) (bmConj (v*w)) z).re) := by
    funext z
    simp only [Complex.inner, tensor_apply, conj_apply, mul_apply, starRingEnd_apply, star_mul', star_star]
    congr 1
    ring
  rw [he]
  change (∫ z, RCLike.re (tensor (v*w) (bmConj (v*w)) z) ∂(RelativeProduct.law μ q hq)) = _
  rw [integral_re (integrable _ (tensor (v*w) (bmConj (v*w)))), integral_tensor_self]
  rfl

end EuclideanFiveColor.BoundedMeasurable

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal RealInnerProductSpace NNReal BoundedContinuousFunction
namespace EuclideanFiveColor.Amenable.Koopman
variable {G X E : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace X] [AddAction G X] [MeasurableConstVAdd G X]
  (μ : Measure X) [IsProbabilityMeasure μ] [ErgodicVAdd G X μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace.CountablySeparated E]

lemma vector_orbit_hom_zero (M : Mean G) (φ : G →+ G) (hs : Function.Surjective φ)
    (v : Lp E 2 μ) (hv : ∫ x, v x ∂μ = 0) :
    M.vector (Mean.orbit (fun g => action (E := E) μ (φ g)) v) = 0 := by
  apply M.vector_orbit_eq_zero _ (fun g h v => by rw [map_add, action_add]) v
  intro w hw
  apply inner_fixed_zero (G := G) (E := E) μ v hv w
  intro g
  obtain ⟨h, rfl⟩ := hs g
  exact hw h
end EuclideanFiveColor.Amenable.Koopman
namespace EuclideanFiveColor.BoundedMeasurable
variable {G X Y : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace X] [Nonempty X]
  [StandardBorelSpace Y] [Nonempty Y] [AddAction G X] [MeasurableConstVAdd G X]
private instance product_measurable_vadd : MeasurableConstVAdd G (X×X) where
  measurable_const_vadd g := (measurable_const_vadd (α := X) g).prodMap (measurable_const_vadd g)
variable (μ : Measure X) [IsProbabilityMeasure μ] (q : X → Y) (hq : Measurable q)

private def pairSequence (φ : G →+ G) (v w : Func X) : G →ᵇ Lp ℂ 2 (μ.map q) :=
  letI : IsProbabilityMeasure (μ.map q) :=
    (Measure.isProbabilityMeasure_map_iff hq.aemeasurable).mpr inferInstance
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun g => l2 (μ.map q) (conditional μ q (v * act (φ g) w)))
    continuous_of_discreteTopology (bound v * bound w) (fun g => by
      apply l2_norm_le
      intro y
      apply expect_bound
      intro x
      dsimp only [mul_apply, act_apply]
      rw [norm_mul]
      exact mul_le_mul (norm_le_bound v x) (norm_le_bound w _) (norm_nonneg _) (bound v).coe_nonneg)

omit [StandardBorelSpace Y] [Nonempty Y] in
@[simp] lemma pairSequence_apply (φ : G →+ G) (v w : Func X) (g : G) :
    pairSequence μ q hq φ v w g = l2 (μ.map q) (conditional μ q (v*act (φ g) w)) := rfl

omit [TopologicalSpace G] [DiscreteTopology G] [StandardBorelSpace X] [Nonempty X] in
lemma tensor_act (g : G) (v w : Func X) :
    tensor (act g v) (act g w) = act g (tensor v w) := rfl

variable [ErgodicVAdd G (X×X) (RelativeProduct.law μ q hq)]

include hq in
lemma pair_mean_sq_zero (M : Amenable.Mean G) (φ : G →+ G) (hs : Function.Surjective φ)
    (v w : Func X) (hw : l2 (μ.map q) (conditional μ q w) = 0) :
    M.map (Amenable.Mean.squareNorm (pairSequence μ q hq φ v w)) = 0 := by
  let ρ := RelativeProduct.law μ q hq
  let t := tensor w (bmConj w)
  have iw : ∫ z, l2 ρ t z ∂ρ = 0 := by
    rw [integral_l2, integral_tensor_self, hw]
    simp
  let U := fun g : G => Amenable.Koopman.action (E := ℂ) ρ (φ g)
  have hv := Amenable.Koopman.vector_orbit_hom_zero ρ M φ hs (l2 ρ t) iw
  let a := l2 ρ (tensor (bmConj v) v)
  have he : Amenable.Mean.squareNorm (pairSequence μ q hq φ v w) =
      Amenable.Mean.pairing (Amenable.Mean.orbit U (l2 ρ t)) a := by
    ext g
    rw [Amenable.Mean.squareNorm_apply]
    change ‖l2 (μ.map q) (conditional μ q (v*act (φ g) w))‖^2 =
      inner ℝ (Amenable.Koopman.action ρ (φ g) (l2 ρ t)) a
    dsimp only [t, a]
    rw [← l2_act, ← tensor_act, act_conj]
    exact (inner_tensor μ q hq v (act (φ g) w)).symm
  rw [he, ← M.vector_pair]
  change inner ℝ (M.vector (Amenable.Mean.orbit U (l2 ρ t))) a = 0
  rw [hv, inner_zero_left]

end EuclideanFiveColor.BoundedMeasurable

namespace EuclideanFiveColor.AlgebraReplacement

section
variable {ι R A H : Type*} [DecidableEq ι] [Semiring R] [CommRing A]
  [Module R A] [AddCommMonoid H] [Module R H]

lemma mixed_prod (s t : Finset ι) (ht : t ⊆ s) (f g : ι → A) :
    (∏ i ∈ t, f i) * (∏ i ∈ s\t, g i) = ∏ i ∈ s, if i∈t then f i else g i := by
  have he : s.filter (fun i => i ∈ t) = t := by
    ext i
    simp only [Finset.mem_filter]
    exact ⟨And.right, fun h => ⟨ht h,h⟩⟩
  have hn : s.filter (fun i => ¬ i∈t) = s\t := by ext i; simp
  rw [Finset.prod_ite, he, hn]

lemma linear_prod_replace (L : A →ₗ[R] H) (s : Finset ι) (f g : ι → A)
    (h : ∀ t ∈ s.powerset, t ≠ ∅ →
      L ((∏ i ∈ t, (f i - g i)) * ∏ i ∈ s\t, g i) = 0) :
    L (∏ i ∈ s, f i) = L (∏ i ∈ s, g i) := by
  have he := Finset.prod_add (fun i => f i - g i) g s
  simp only [sub_add_cancel] at he
  rw [he, map_sum]
  rw [Finset.sum_eq_single ∅]
  · simp
  · intro t ht hn
    exact h t ht hn
  · simp
end
variable {ι A H : Type*} [DecidableEq ι] [CommRing A] [AddCommMonoid H]
lemma add_prod_replace (L : A →+ H) (s : Finset ι) (f g : ι → A)
    (h : ∀ t ∈ s.powerset, t ≠ ∅ →
      L ((∏ i ∈ t, (f i - g i)) * ∏ i ∈ s\t, g i) = 0) :
    L (∏ i ∈ s, f i) = L (∏ i ∈ s, g i) := by
  have he := Finset.prod_add (fun i => f i - g i) g s
  simp only [sub_add_cancel] at he
  rw [he, map_sum]
  rw [Finset.sum_eq_single ∅]
  · simp
  · intro t ht hn
    exact h t ht hn
  · simp
end EuclideanFiveColor.AlgebraReplacement

end

end ParishFactor
end

-- OAI.MeasureTheory.CompactFactors.Separability
section
namespace ParishFactor

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal
open scoped RealInnerProductSpace BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal RealInnerProductSpace NNReal
open MeasureTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal RealInnerProductSpace NNReal BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace
namespace EuclideanFiveColor.Amenable.Mean
variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
variable (M : EuclideanFiveColor.Amenable.Mean G)
lemma vector_real (f : G →ᵇ ℝ) : M.vector f = M.map f := by
  have h := M.vector_pair f 1
  have he : pairing f 1 = f := by ext g; simp [pairing_apply]
  simpa only [Real.inner_apply, mul_one, he] using h

lemma norm_mean_zero_of_square {H : Type*} [NormedAddCommGroup H]
    (V : G →ᵇ H) (h : M.map (squareNorm V) = 0) : M.map (normFn V) = 0 := by
  have he : squareNorm (normFn V) = squareNorm V := by
    ext g
    simp only [squareNorm_apply, normFn_apply, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  have hj := M.jensen (normFn V)
  rw [M.vector_real, he, h] at hj
  rw [Real.norm_eq_abs, sq_abs] at hj
  have : (M.map (normFn V))^2 = 0 := le_antisymm hj (sq_nonneg _)
  exact sq_eq_zero_iff.mp this
end EuclideanFiveColor.Amenable.Mean

namespace EuclideanFiveColor.BoundedMeasurable
variable {G X : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace X] [AddAction G X] [MeasurableConstVAdd G X]
variable (μ : Measure X) [IsProbabilityMeasure μ] [VAddInvariantMeasure G X μ]

lemma l2_inner (f h : Func X) : inner ℝ (l2 μ f) (l2 μ h) =
    (∫ x, (bmConj f * h) x ∂μ).re := by
  rw [inner_l2]
  simp only [Complex.inner, starRingEnd_apply, mul_comm (h _)]
  change (∫ x, RCLike.re ((bmConj f * h) x) ∂μ) = _
  exact integral_re (integrable μ (bmConj f * h))

omit [TopologicalSpace G] [DiscreteTopology G] in
lemma inner_act (g : G) (f h : Func X) :
    inner ℝ (l2 μ (act g f)) (l2 μ (act g h)) = inner ℝ (l2 μ f) (l2 μ h) := by
  rw [l2_act, l2_act]
  exact (Amenable.Koopman.action (E := ℂ) μ g).inner_map_map _ _

omit [TopologicalSpace G] [DiscreteTopology G] [IsProbabilityMeasure μ] in
lemma integral_act (g : G) (f : Func X) : ∫ x, act g f x ∂μ = ∫ x, f x ∂μ :=
  (measurePreserving_vadd g μ).integral_comp (MeasurableEquiv.vadd g).measurableEmbedding (f : X → ℂ)

lemma l2_mul_norm_le (f h : Func X) {C : ℝ} (hC : ∀ x, ‖h x‖ ≤ C) :
    ‖l2 μ (f*h)‖ ≤ C * ‖l2 μ f‖ := by
  have hC0 : 0 ≤ C := by
    have : Nonempty X := MeasureTheory.nonempty_of_isProbabilityMeasure μ
    exact (norm_nonneg (h (Classical.choice this))).trans (hC _)
  have hi : ‖l2 μ (f*h)‖^2 ≤ C^2 * ‖l2 μ f‖^2 := by
    rw [norm_l2_sq, norm_l2_sq, ← integral_const_mul]
    apply integral_mono (integrable_norm_sq μ (f*h)) ((integrable_norm_sq μ f).const_mul _)
    intro x
    change ‖f x * h x‖^2 ≤ C^2 * ‖f x‖^2
    rw [norm_mul, mul_pow]
    have hh : ‖h x‖^2 ≤ C^2 := pow_le_pow_left₀ (norm_nonneg _) (hC x) 2
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hh (sq_nonneg ‖f x‖)
  have hn := norm_nonneg (l2 μ (f*h))
  have hm := norm_nonneg (l2 μ f)
  nlinarith [mul_nonneg hC0 hm]

end EuclideanFiveColor.BoundedMeasurable

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace
namespace EuclideanFiveColor.BoundedMeasurable

section
variable {ι G X : Type*} [DecidableEq ι] [AddCommGroup G] [MeasurableSpace X]
  [AddAction G X] [MeasurableConstVAdd G X]

@[simp] lemma func_prod_apply (s : Finset ι) (f : ι → Func X) (x : X) :
    (∏ i ∈ s, f i) x = ∏ i ∈ s, f i x := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih]

@[simp] lemma conj_conj (f : Func X) : bmConj (bmConj f) = f := by ext x; simp
lemma conj_mul (f h : Func X) : bmConj (f*h) = bmConj f * bmConj h := by ext x; simp
lemma conj_prod (s : Finset ι) (f : ι → Func X) : bmConj (∏ i ∈ s, f i) = ∏ i ∈ s, bmConj (f i) := by
  ext x
  simp
lemma comp_prod {Y : Type*} [MeasurableSpace Y] (s : Finset ι) (f : ι → Func Y)
    (q : X → Y) (hq : Measurable q) : comp (∏ i ∈ s, f i) q hq = ∏ i ∈ s, comp (f i) q hq := by
  ext x
  simp
lemma act_prod (g : G) (s : Finset ι) (f : ι → Func X) :
    act g (∏ i ∈ s, f i) = ∏ i ∈ s, act g (f i) := by ext x; simp
lemma act_zero (f : Func X) : act (0 : G) f = f := by ext x; simp

lemma prod_orbit_correlation (s : Finset ι) (φ : ι → G →+ G) (f : ι → Func X) (u h : G) :
    (∏ i ∈ s, act (φ i (u+h)) (f i)) * bmConj (∏ i ∈ s, act (φ i u) (f i)) =
    ∏ i ∈ s, act (φ i u) (act (φ i h) (f i) * bmConj (f i)) := by
  rw [conj_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [map_add, act_add, act_mul, act_conj]

lemma prod_shift_erase (s : Finset ι) (j : ι) (hj : j∈s)
    (φ : ι → G →+ G) (f : ι → Func X) (u : G) :
    (∏ i ∈ s, act (φ i u) (f i)) =
    act (φ j u) (f j * ∏ i ∈ s.erase j, act ((φ i - φ j) u) (f i)) := by
  rw [act_mul, act_prod]
  rw [← Finset.mul_prod_erase s (fun i => act (φ i u) (f i)) hj]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [← act_add]
  congr 1
  simp only [AddMonoidHom.sub_apply]
  abel

variable (μ : Measure X) [IsProbabilityMeasure μ] [VAddInvariantMeasure G X μ]
omit [DecidableEq ι] in
lemma l2_inner_mul (f h : Func X) : inner ℝ (l2 μ f) (l2 μ (bmConj h)) =
    (∫ x, (f*h) x ∂μ).re := by
  rw [real_inner_comm, l2_inner, conj_conj]
  congr 1
  rw [mul_comm h f]

variable [TopologicalSpace G] [DiscreteTopology G]
lemma correlation_product (M : Amenable.Mean G) (s : Finset ι) (j : ι) (hj : j∈s)
    (φ : ι → G →+ G) (f : ι → Func X) (h : G) :
    M.correlation (Family.toL2 μ (∏ i ∈ s, Family.orbit (φ i) (f i)))
      (Family.toL2 μ (∏ i ∈ s, Family.orbit (φ i) (f i))) h =
    inner ℝ (Family.avg μ M (∏ i ∈ s.erase j,
      Family.orbit (φ i - φ j) (act (φ i h) (f i) * bmConj (f i))))
      (l2 μ (bmConj (act (φ j h) (f j) * bmConj (f j)))) := by
  rw [Family.avg_pair, Amenable.Mean.correlation_apply]
  congr 1
  apply BoundedContinuousFunction.ext
  intro u
  simp only [Amenable.Mean.cross_apply, Amenable.shift_apply, Family.toL2_apply,
    Family.prod_apply, Family.orbit_apply, Amenable.Mean.pairing_apply]
  rw [← conj_conj (∏ i ∈ s, act (φ i u) (f i)), l2_inner_mul]
  rw [prod_orbit_correlation, prod_shift_erase s j hj, integral_act, l2_inner_mul]
  congr 1
  rw [mul_comm]

end

section

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]
variable (μ : Measure X) [IsProbabilityMeasure μ] (q : X → Y) (hq : Measurable q)

omit [MeasurableSpace Y] [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y] in
lemma norm_l2_conj (f : Func X) : ‖l2 μ (bmConj f)‖ = ‖l2 μ f‖ := by
  have he : ‖l2 μ (bmConj f)‖^2 = ‖l2 μ f‖^2 := by simp only [norm_l2_sq, conj_apply, norm_star]
  nlinarith [norm_nonneg (l2 μ (bmConj f)), norm_nonneg (l2 μ f)]

lemma inner_replace_project (w h : Func X) (b : Func Y) (hw : w =ᵐ[μ] comp b q hq) :
    inner ℝ (l2 μ w) (l2 μ (bmConj h)) =
    inner ℝ (l2 μ w) (l2 μ (bmConj (project μ q hq h))) := by
  rw [l2_inner_mul, l2_inner_mul]
  congr 1
  calc
    (∫ x, (w*h) x ∂μ) = ∫ x, (h*comp b q hq) x ∂μ := by
      apply integral_congr_ae
      filter_upwards [hw] with x hx
      simp only [mul_apply, hx, mul_comm]
    _ = ∫ x, (project μ q hq h * comp b q hq) x ∂μ := integral_mul_lift μ q hq h b
    _ = ∫ x, (w * project μ q hq h) x ∂μ := by
      apply integral_congr_ae
      filter_upwards [hw] with x hx
      simp only [mul_apply, hx, mul_comm]

lemma inner_project_bound (w h : Func X) (b : Func Y) (hw : w =ᵐ[μ] comp b q hq)
    {C : ℝ} (hC : ∀ x, ‖w x‖ ≤ C) :
    |inner ℝ (l2 μ w) (l2 μ (bmConj h))| ≤ C * ‖l2 μ (project μ q hq h)‖ := by
  rw [inner_replace_project μ q hq w h b hw]
  calc
    |inner ℝ (l2 μ w) (l2 μ (bmConj (project μ q hq h)))| ≤
        ‖l2 μ w‖ * ‖l2 μ (bmConj (project μ q hq h))‖ := abs_real_inner_le_norm _ _
    _ ≤ C * ‖l2 μ (project μ q hq h)‖ := by
      rw [norm_l2_conj]
      exact mul_le_mul_of_nonneg_right (l2_norm_le μ w hC) (norm_nonneg _)

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
lemma avg_project_bound (M : Amenable.Mean G) (W : Family G X) (h : Func X) (b : G → Func Y)
    (hw : ∀ g, W g =ᵐ[μ] comp (b g) q hq) {C : ℝ} (hC : ∀ g x, ‖W g x‖ ≤ C) :
    |inner ℝ (Family.avg μ M W) (l2 μ (bmConj h))| ≤ C * ‖l2 μ (project μ q hq h)‖ := by
  rw [Family.avg_pair, ← M.map_const (C * ‖l2 μ (project μ q hq h)‖)]
  apply M.abs_le
  intro g
  exact inner_project_bound μ q hq (W g) h (b g) (hw g) (hC g)

variable [AddAction G X] [MeasurableConstVAdd G X] [VAddInvariantMeasure G X μ]
  [AddAction G Y] [MeasurableConstVAdd G Y]
variable (hqcov : ∀ g : G, (fun x => q (g +ᵥ x)) =ᵐ[μ] (fun x => g +ᵥ q x))
variable {ι : Type*} [DecidableEq ι]
omit [StandardBorelSpace Y] [Nonempty Y] [TopologicalSpace G] [DiscreteTopology G]
  [VAddInvariantMeasure G X μ] in
include hqcov in
lemma prod_act_project_lift (s : Finset ι) (ψ : ι → G →+ G) (f : ι → Func X) (u : G) :
    (∏ i ∈ s, act (ψ i u) (project μ q hq (f i))) =ᵐ[μ]
    comp (∏ i ∈ s, act (ψ i u) (conditional μ q (f i))) q hq := by
  rw [comp_prod]
  induction s using Finset.induction_on with
  | empty => exact .of_forall (fun _ => by simp)
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    filter_upwards [act_lift μ q hq hqcov (ψ i u) (conditional μ q (f i)), ih] with x hx hy
    exact congrArg₂ (·*·) hx hy

end

variable {G X Y : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace X] [Nonempty X]
  [StandardBorelSpace Y] [Nonempty Y] [AddAction G X] [MeasurableConstVAdd G X]
variable (μ : Measure X) [IsProbabilityMeasure μ] [VAddInvariantMeasure G X μ]
  (q : X → Y) (hq : Measurable q)

private def PairVanishing (M : Amenable.Mean G) : Prop :=
  ∀ (φ : G →+ G), Function.Surjective φ → ∀ v w : Func X,
    l2 μ (project μ q hq w) = 0 →
    M.map (Amenable.Mean.normFn (pairSequence μ q hq φ v w)) = 0

omit [VAddInvariantMeasure G X μ] in
lemma pairVanishing_of_ergodic [ErgodicVAdd G (X×X) (RelativeProduct.law μ q hq)]
    (M : Amenable.Mean G) : PairVanishing μ q hq M := by
  intro φ hs v w hw
  apply M.norm_mean_zero_of_square
  apply pair_mean_sq_zero μ q hq M φ hs v w
  apply norm_eq_zero.mp
  rw [← norm_project_l2 μ q hq w, hw, norm_zero]

variable {ι : Type*} [DecidableEq ι]
private def Admissible (s : Finset ι) (φ : ι → G →+ G) : Prop :=
  (∀ i∈s, Function.Surjective (φ i)) ∧
  ∀ i∈s, ∀ j∈s, i≠j → Function.Surjective (φ i - φ j)

omit [TopologicalSpace G] [DiscreteTopology G] in
lemma Admissible.erase_diff {s : Finset ι} {φ : ι → G →+ G}
    (ha : Admissible s φ) {j : ι} (hj : j∈s) :
    Admissible (s.erase j) (fun i => φ i - φ j) := by
  constructor
  · intro i hi
    exact ha.2 i (Finset.mem_of_mem_erase hi) j hj (Finset.ne_of_mem_erase hi)
  · intro i hi k hk hik
    have he : (φ i - φ j) - (φ k - φ j) = φ i - φ k := by abel
    rw [he]
    exact ha.2 i (Finset.mem_of_mem_erase hi) k (Finset.mem_of_mem_erase hk) hik

variable [AddAction G Y] [MeasurableConstVAdd G Y]
variable (hqcov : ∀ g : G, (fun x => q (g +ᵥ x)) =ᵐ[μ] (fun x => g +ᵥ q x))
include hqcov in

theorem avg_product_zero_of_pair (M : Amenable.Mean G) (hpair : PairVanishing μ q hq M)
    (s : Finset ι) (φ : ι → G →+ G) (f : ι → Func X) (ha : Admissible s φ)
    (hc : ∃ j∈s, l2 μ (project μ q hq (f j)) = 0) :
    Family.avg μ M (∏ i∈s, Family.orbit (φ i) (f i)) = 0 := by
  have main : ∀ n : ℕ, ∀ (s : Finset ι), s.card ≤ n → ∀ (φ : ι → G →+ G)
      (f : ι → Func X), Admissible s φ →
      (∃ j∈s, l2 μ (project μ q hq (f j)) = 0) →
      Family.avg μ M (∏ i∈s, Family.orbit (φ i) (f i)) = 0 := by
    intro n
    induction n with
    | zero =>
      intro s hn φ f ha hc
      have hs : s = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hn)
      obtain ⟨j,hj,_⟩ := hc
      simp [hs] at hj
    | succ n ih =>
      intro s hn φ f ha hc
      obtain ⟨j,hj,hfj⟩ := hc
      let e := s.erase j
      let ψ := fun i => φ i - φ j
      have he : e.card ≤ n := by
        have := Finset.card_erase_of_mem hj
        dsimp [e]
        omega
      have had : Admissible e ψ := ha.erase_diff hj
      let F : G → ι → Func X := fun h i => act (φ i h) (f i) * bmConj (f i)
      have replace (h : G) :
          Family.avg μ M (∏ i∈e, Family.orbit (ψ i) (F h i)) =
          Family.avg μ M (∏ i∈e, Family.orbit (ψ i) (project μ q hq (F h i))) := by
        apply EuclideanFiveColor.AlgebraReplacement.add_prod_replace
          (A := Family G X) (H := Lp ℂ 2 μ) (Family.avg μ M).toAddMonoidHom e
          (fun i => Family.orbit (ψ i) (F h i))
          (fun i => Family.orbit (ψ i) (project μ q hq (F h i)))
        intro t ht htn
        have hte := Finset.mem_powerset.mp ht
        rw [EuclideanFiveColor.AlgebraReplacement.mixed_prod e t hte]
        have heq : (∏ i∈e, if i∈t then
            Family.orbit (ψ i) (F h i) - Family.orbit (ψ i) (project μ q hq (F h i))
            else Family.orbit (ψ i) (project μ q hq (F h i))) =
            ∏ i∈e, Family.orbit (ψ i)
              (if i∈t then F h i - project μ q hq (F h i) else project μ q hq (F h i)) := by
          apply Finset.prod_congr rfl
          intro i _
          split_ifs <;> simp only [Family.orbit_sub]
        rw [heq]
        apply ih e he ψ _ had
        obtain ⟨i,hit⟩ := Finset.nonempty_iff_ne_empty.mpr htn
        refine ⟨i,hte hit, ?_⟩
        rw [if_pos hit]
        exact center_project_l2 μ q hq (F h i)
      let C : ℝ := ∏ i∈e, (bound (f i) : ℝ)^2
      have hCb (h u : G) (x : X) :
          ‖(∏ i∈e, Family.orbit (ψ i) (project μ q hq (F h i))) u x‖ ≤ C := by
        simp only [Family.prod_apply, Family.orbit_apply, func_prod_apply]
        rw [norm_prod]
        apply Finset.prod_le_prod (fun index _ => norm_nonneg _)
        intro i _
        apply project_bound μ q hq
        intro z
        dsimp only [F, mul_apply, act_apply, conj_apply]
        rw [norm_mul, norm_star, pow_two]
        exact mul_le_mul (norm_le_bound (f i) _) (norm_le_bound (f i) _) (norm_nonneg _) (bound (f i)).coe_nonneg
      let V := Family.toL2 μ (∏ i∈s, Family.orbit (φ i) (f i))
      let a := Amenable.Mean.normFn (pairSequence μ q hq (φ j) (bmConj (f j)) (f j))
      have hcorr (h : G) : M.correlation V V h ≤ C * a h := by
        dsimp only [V]
        rw [correlation_product μ M s j hj]
        change inner ℝ (Family.avg μ M (∏ i∈e, Family.orbit (ψ i) (F h i)))
          (l2 μ (bmConj (F h j))) ≤ _
        rw [replace]
        have hb := avg_project_bound μ q hq M
          (∏ i∈e, Family.orbit (ψ i) (project μ q hq (F h i))) (F h j)
          (fun u => ∏ i∈e, act (ψ i u) (conditional μ q (F h i)))
          (fun u => by
            filter_upwards [prod_act_project_lift μ q hq hqcov e ψ (F h) u] with x hx
            simpa only [Family.prod_apply, Family.orbit_apply, func_prod_apply, Finset.prod_apply] using hx) (hCb h)
        apply (le_abs_self _).trans (hb.trans_eq ?_)
        congr 1
        rw [norm_project_l2]
        change ‖l2 (μ.map q) (conditional μ q (F h j))‖ =
          ‖l2 (μ.map q) (conditional μ q (bmConj (f j) * act (φ j h) (f j)))‖
        dsimp only [F]
        rw [mul_comm]
      change M.vector V = 0
      apply M.vector_eq_zero_of_correlation_nonpos
      have hm := M.mono (M.correlation V V) (C • a) hcorr
      rw [map_smul, show M.map a = 0 from hpair (φ j) (ha.1 j hj) (bmConj (f j)) (f j) hfj,
        smul_zero] at hm
      exact hm
  exact main s.card s le_rfl φ f ha hc

end EuclideanFiveColor.BoundedMeasurable

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace
namespace EuclideanFiveColor.BoundedMeasurable.Family
variable {G X : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace X]
variable (μ : Measure X) [IsProbabilityMeasure μ] (M : Amenable.Mean G)
private def meanNorm (F : Family G X) : ℝ := M.map (Amenable.Mean.normFn (toL2 μ F))
lemma meanNorm_nonneg (F : Family G X) : 0 ≤ meanNorm μ M F :=
  M.positive _ (fun g => by
    change 0 ≤ ‖l2 μ (F g)‖
    exact norm_nonneg _)
lemma meanNorm_mono {F H : Family G X} (h : ∀ g, ‖l2 μ (F g)‖ ≤ ‖l2 μ (H g)‖) :
    meanNorm μ M F ≤ meanNorm μ M H := M.mono _ _ h
lemma meanNorm_congr {F H : Family G X} (h : ∀ g, F g =ᵐ[μ] H g) :
    meanNorm μ M F = meanNorm μ M H := by
  apply congrArg M.map
  apply BoundedContinuousFunction.ext
  intro g
  exact congrArg norm ((l2_eq_iff μ _ _).mpr (h g))
lemma meanNorm_le {F : Family G X} {C : ℝ} (h : ∀ g, ‖l2 μ (F g)‖ ≤ C) :
    meanNorm μ M F ≤ C := by
  rw [meanNorm, ← M.map_const C]
  exact M.mono _ _ h
@[simp] lemma meanNorm_zero : meanNorm μ M (0 : Family G X) = 0 := by
  apply le_antisymm _ (meanNorm_nonneg μ M 0)
  apply meanNorm_le
  intro g
  change ‖l2 μ (0 : Func X)‖ ≤ 0
  rw [map_zero, norm_zero]
lemma meanNorm_add_le (F H : Family G X) :
    meanNorm μ M (F+H) ≤ meanNorm μ M F + meanNorm μ M H := by
  unfold meanNorm
  rw [← map_add]
  apply M.mono
  intro g
  simpa only [Amenable.Mean.normFn_apply, BoundedContinuousFunction.add_apply,
    toL2_apply, add_apply, map_add] using norm_add_le (l2 μ (F g)) (l2 μ (H g))
lemma meanNorm_neg (F : Family G X) : meanNorm μ M (-F) = meanNorm μ M F := by
  apply congrArg M.map
  apply BoundedContinuousFunction.ext
  intro g
  change ‖l2 μ (-(F g))‖ = ‖l2 μ (F g)‖
  rw [map_neg, norm_neg]
lemma meanNorm_sub_le (F H : Family G X) :
    meanNorm μ M (F-H) ≤ meanNorm μ M F + meanNorm μ M H := by
  have h := meanNorm_add_le μ M F (-H)
  rw [meanNorm_neg] at h
  change meanNorm μ M (F + -H) ≤ _
  exact h
lemma meanNorm_mul_le (F H : Family G X) {C : ℝ} (hC : ∀ g x, ‖H g x‖ ≤ C) :
    meanNorm μ M (F*H) ≤ C * meanNorm μ M F := by
  unfold meanNorm
  calc
    _ ≤ M.map (C • Amenable.Mean.normFn (toL2 μ F)) := by
      apply M.mono
      intro g
      exact l2_mul_norm_le μ (F g) (H g) (hC g)
    _ = _ := by rw [map_smul]; rfl
lemma meanNorm_const (f : Func X) : meanNorm μ M (const f : Family G X) = ‖l2 μ f‖ := by
  have he : Amenable.Mean.normFn (toL2 μ (const f : Family G X)) =
      BoundedContinuousFunction.const G ‖l2 μ f‖ := by
    ext g
    rfl
  unfold meanNorm
  rw [he, M.map_const]
lemma meanNorm_add_zero {F H : Family G X} (hF : meanNorm μ M F = 0) (hH : meanNorm μ M H = 0) :
    meanNorm μ M (F+H) = 0 := by
  have h := meanNorm_add_le μ M F H
  rw [hF, hH, add_zero] at h
  exact le_antisymm h (meanNorm_nonneg μ M _)
lemma meanNorm_mul_zero {F H : Family G X} (hF : meanNorm μ M F = 0) :
    meanNorm μ M (F*H) = 0 := by
  have h := meanNorm_mul_le μ M F H H.norm_le_bound
  rw [hF, mul_zero] at h
  exact le_antisymm h (meanNorm_nonneg μ M _)
lemma meanNorm_sum_zero {ι : Type*} (s : Finset ι) (F : ι → Family G X)
    (hF : ∀ i∈s, meanNorm μ M (F i) = 0) : meanNorm μ M (∑ i∈s, F i) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact meanNorm_add_zero μ M (hF i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hF j (Finset.mem_insert_of_mem hj)))
lemma meanNorm_eq_zero_of_approx {F : Family G X}
    (h : ∀ ε : ℝ, 0 < ε → ∃ H : Family G X, meanNorm μ M H = 0 ∧
      ∀ g, ‖l2 μ (F g - H g)‖ ≤ ε) : meanNorm μ M F = 0 := by
  apply le_antisymm _ (meanNorm_nonneg μ M F)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨H,hH,hd⟩ := h ε hε
  have hb := meanNorm_add_le μ M (F-H) H
  rw [hH, add_zero] at hb
  have ht : (F-H)+H = F := sub_add_cancel F H
  rw [ht] at hb
  have hd' : meanNorm μ M (F-H) ≤ ε := meanNorm_le μ M hd
  simpa only [zero_add] using hb.trans hd'
end EuclideanFiveColor.BoundedMeasurable.Family

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace
namespace EuclideanFiveColor.BoundedMeasurable
variable {G X Y : Type*} [AddCommGroup G]
  [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace X] [Nonempty X]
  [StandardBorelSpace Y] [Nonempty Y]
variable (μ : Measure X) [IsProbabilityMeasure μ] (q : X → Y) (hq : Measurable q)
namespace Family
omit [AddCommGroup G] [StandardBorelSpace Y] [Nonempty Y] in
private def conditional (F : Family G X) : Family G Y :=
  ⟨fun g => BoundedMeasurable.conditional μ q (F g), F.bound,
    fun g y => expect_bound _ _ (F.norm_le_bound g) y⟩
omit [AddCommGroup G] [StandardBorelSpace Y] [Nonempty Y] in
@[simp] lemma conditional_apply (F : Family G X) (g : G) :
    conditional μ q F g = BoundedMeasurable.conditional μ q (F g) := rfl
omit [AddCommGroup G] [StandardBorelSpace Y] [Nonempty Y] in
lemma conditional_add (F H : Family G X) : conditional μ q (F+H) = conditional μ q F + conditional μ q H := by
  ext g y
  exact integral_add (integrable _ (F g)) (integrable _ (H g))
omit [AddCommGroup G] [StandardBorelSpace Y] [Nonempty Y] in
lemma conditional_sub (F H : Family G X) : conditional μ q (F-H) = conditional μ q F - conditional μ q H := by
  ext g y
  exact integral_sub (integrable _ (F g)) (integrable _ (H g))
end Family
variable [AddAction G X] [AddAction G Y] [MeasurableConstVAdd G X] [MeasurableConstVAdd G Y]

private def covariance (φ : G →+ G) (v w : Func X) : Family G Y :=
  Family.conditional μ q (Family.const v * Family.orbit φ w) -
    Family.const (conditional μ q v) * Family.orbit φ (conditional μ q w)
omit [StandardBorelSpace Y] [Nonempty Y] in
@[simp] lemma covariance_apply (φ : G →+ G) (v w : Func X) (g : G) :
    covariance μ q φ v w g = conditional μ q (v*act (φ g) w) -
      conditional μ q v * act (φ g) (conditional μ q w) := rfl

omit [StandardBorelSpace Y] [Nonempty Y] in
lemma covariance_add_left (φ : G →+ G) (v v' w : Func X) :
    covariance μ q φ (v+v') w = covariance μ q φ v w + covariance μ q φ v' w := by
  apply Family.ext
  intro g
  change conditional μ q ((v+v')*act (φ g) w) - conditional μ q (v+v') *
    act (φ g) (conditional μ q w) =
    (conditional μ q (v*act (φ g) w) - conditional μ q v * act (φ g) (conditional μ q w)) +
    (conditional μ q (v'*act (φ g) w) - conditional μ q v' * act (φ g) (conditional μ q w))
  unfold conditional
  rw [add_mul, expect_add, expect_add, add_mul]
  abel

omit [StandardBorelSpace Y] [Nonempty Y] in
lemma covariance_add_right (φ : G →+ G) (v w w' : Func X) :
    covariance μ q φ v (w+w') = covariance μ q φ v w + covariance μ q φ v w' := by
  have ha (g : G) (a b : Func X) : act g (a+b) = act g a + act g b := rfl
  have hb (g : G) (a b : Func Y) : act g (a+b) = act g a + act g b := rfl
  apply Family.ext
  intro g
  change conditional μ q (v*act (φ g) (w+w')) - conditional μ q v *
    act (φ g) (conditional μ q (w+w')) =
    (conditional μ q (v*act (φ g) w) - conditional μ q v * act (φ g) (conditional μ q w)) +
    (conditional μ q (v*act (φ g) w') - conditional μ q v * act (φ g) (conditional μ q w'))
  unfold conditional
  rw [ha, mul_add, expect_add, expect_add, hb, mul_add]
  abel
variable [VAddInvariantMeasure G X μ]
variable (hqcov : ∀ g : G, (fun x => q (g +ᵥ x)) =ᵐ[μ] (fun x => g +ᵥ q x))
omit [VAddInvariantMeasure G X μ] in
include hqcov in
lemma conditional_mul_project_act (g : G) (v w : Func X) :
    conditional μ q (v*act g (project μ q hq w)) =ᵐ[μ.map q]
      conditional μ q v * act g (conditional μ q w) := by
  have h := act_lift μ q hq hqcov g (conditional μ q w)
  have hc : v*act g (project μ q hq w) =ᵐ[μ] v*comp (act g (conditional μ q w)) q hq := by
    filter_upwards [h] with x hx
    exact congrArg (fun t => v x*t) hx
  exact (conditional_congr μ q hq hc).trans (conditional_pullout μ q hq v _)

omit [VAddInvariantMeasure G X μ] in
include hqcov in
lemma covariance_center (φ : G →+ G) (v w : Func X) (g : G) :
    covariance μ q φ v w g =ᵐ[μ.map q]
      conditional μ q (v*act (φ g) (w-project μ q hq w)) := by
  have he : conditional μ q (v*act (φ g) (w-project μ q hq w)) =
      conditional μ q (v*act (φ g) w) - conditional μ q (v*act (φ g) (project μ q hq w)) := by
    rw [act_sub, mul_sub]
    exact (expectLinear (condDistrib id q μ)).map_sub _ _
  rw [he]
  filter_upwards [conditional_mul_project_act μ q hq hqcov (φ g) v w] with y hy
  simp only [covariance_apply, sub_apply]
  rw [hy]
  rfl

variable [TopologicalSpace G] [DiscreteTopology G]

omit [VAddInvariantMeasure G X μ] in
include hqcov in
lemma covariance_mean_zero (M : Amenable.Mean G) (hp : PairVanishing μ q hq M)
    (φ : G →+ G) (hs : Function.Surjective φ) (v w : Func X) [IsProbabilityMeasure (μ.map q)] :
    Family.meanNorm (μ.map q) M (covariance μ q φ v w) = 0 := by
  rw [Family.meanNorm_congr (μ.map q) M (F := covariance μ q φ v w)
    (H := Family.conditional μ q (Family.const v * Family.orbit φ (w-project μ q hq w)))
    (fun g => by
      simpa only [Family.conditional_apply, Family.mul_apply, Family.const_apply, Family.orbit_apply]
        using covariance_center μ q hq hqcov φ v w g)]
  have he : Family.toL2 (μ.map q) (Family.conditional μ q
      (Family.const v * Family.orbit φ (w-project μ q hq w))) =
      pairSequence μ q hq φ v (w-project μ q hq w) := by
    ext g
    rfl
  unfold Family.meanNorm
  rw [he]
  exact hp φ hs v _ (center_project_l2 μ q hq w)
end EuclideanFiveColor.BoundedMeasurable

end

end ParishFactor
end

-- OAI.MeasureTheory.CompactFactors.AlgebraModels
section
namespace ParishFactor

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal
open scoped RealInnerProductSpace BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal RealInnerProductSpace NNReal
open MeasureTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal RealInnerProductSpace NNReal BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction
namespace EuclideanFiveColor.BoundedMeasurable
variable {G X Y : Type*} [AddCommGroup G] [MeasurableSpace X] [MeasurableSpace Y]
  [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]
  [AddAction G X] [AddAction G Y] [MeasurableConstVAdd G X] [MeasurableConstVAdd G Y]
variable (μ : Measure X) [IsProbabilityMeasure μ] (q : X → Y) (hq : Measurable q)

omit [StandardBorelSpace Y] [Nonempty Y] in
lemma covariance_sub_left (φ : G →+ G) (v v' w : Func X) :
    covariance μ q φ (v-v') w = covariance μ q φ v w - covariance μ q φ v' w := by
  have h := covariance_add_left μ q φ (v-v') v' w
  rw [sub_add_cancel] at h
  rw [h]
  ext g y
  simp only [Family.sub_apply, Family.add_apply, sub_apply, add_apply]
  ring
omit [StandardBorelSpace Y] [Nonempty Y] in
lemma covariance_sub_right (φ : G →+ G) (v w w' : Func X) :
    covariance μ q φ v (w-w') = covariance μ q φ v w - covariance μ q φ v w' := by
  have h := covariance_add_right μ q φ v (w-w') w'
  rw [sub_add_cancel] at h
  rw [h]
  ext g y
  simp only [Family.sub_apply, Family.add_apply, sub_apply, add_apply]
  ring

omit [StandardBorelSpace Y] [Nonempty Y] in
include hq in
lemma covariance_norm_left (φ : G →+ G) (v w : Func X) (g : G) :
    ‖l2 (μ.map q) (covariance μ q φ v w g)‖ ≤ (2*(bound w : ℝ))*‖l2 μ v‖ := by
  have hp := conditional_norm_l2_le μ q hq v
  have h1 : ‖l2 (μ.map q) (conditional μ q (v*act (φ g) w))‖ ≤ (bound w : ℝ)*‖l2 μ v‖ :=
    (conditional_norm_l2_le μ q hq _).trans (l2_mul_norm_le μ v (act (φ g) w)
      (fun x => norm_le_bound w _))
  have h2 : ‖l2 (μ.map q) (conditional μ q v * act (φ g) (conditional μ q w))‖ ≤
      (bound w : ℝ)*‖l2 μ v‖ := by
    have h := l2_norm_mul_le (μ.map q) (act (φ g) (conditional μ q w)) (conditional μ q v)
      (fun y => expect_bound _ w (norm_le_bound w) (φ g +ᵥ y))
    rw [mul_comm (act _ _) _] at h
    exact h.trans (mul_le_mul_of_nonneg_left hp (bound w).coe_nonneg)
  rw [covariance_apply, map_sub]
  calc
    _ ≤ ‖l2 (μ.map q) (conditional μ q (v*act (φ g) w))‖ +
        ‖l2 (μ.map q) (conditional μ q v * act (φ g) (conditional μ q w))‖ := norm_sub_le _ _
    _ ≤ _ := by linarith

variable [VAddInvariantMeasure G X μ]
variable (hqcov : ∀ g : G, (fun x => q (g +ᵥ x)) =ᵐ[μ] (fun x => g +ᵥ q x))
omit [StandardBorelSpace Y] [Nonempty Y] in
include hq hqcov in
lemma covariance_norm_right (φ : G →+ G) (v w : Func X) (g : G) :
    ‖l2 (μ.map q) (covariance μ q φ v w g)‖ ≤ (2*(bound v : ℝ))*‖l2 μ w‖ := by
  have hn : ‖l2 μ (act (φ g) w)‖ = ‖l2 μ w‖ := by
    rw [l2_act]
    exact (Amenable.Koopman.action μ (φ g)).norm_map _
  have h1 : ‖l2 (μ.map q) (conditional μ q (v*act (φ g) w))‖ ≤ (bound v : ℝ)*‖l2 μ w‖ := by
    have h := (conditional_norm_l2_le μ q hq (v*act (φ g) w)).trans
      (l2_norm_mul_le μ v _ (norm_le_bound v))
    rwa [hn] at h
  have hp : ‖l2 (μ.map q) (act (φ g) (conditional μ q w))‖ ≤ ‖l2 μ w‖ := by
    have he := (l2_eq_iff (μ.map q) _ _).mpr (conditional_act μ q hq hqcov (φ g) w)
    rw [← he, ← hn]
    exact conditional_norm_l2_le μ q hq _
  have h2 : ‖l2 (μ.map q) (conditional μ q v * act (φ g) (conditional μ q w))‖ ≤
      (bound v : ℝ)*‖l2 μ w‖ := by
    exact (l2_norm_mul_le (μ.map q) _ _ (expect_bound _ v (norm_le_bound v))).trans
      (mul_le_mul_of_nonneg_left hp (bound v).coe_nonneg)
  rw [covariance_apply, map_sub]
  calc
    _ ≤ ‖l2 (μ.map q) (conditional μ q (v*act (φ g) w))‖ +
        ‖l2 (μ.map q) (conditional μ q v * act (φ g) (conditional μ q w))‖ := norm_sub_le _ _
    _ ≤ _ := by linarith
end EuclideanFiveColor.BoundedMeasurable

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction
namespace EuclideanFiveColor.BoundedMeasurable
variable {G X Y : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace X] [MeasurableSpace Y]
variable (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Y) [IsProbabilityMeasure ν]

lemma meanNorm_zero_of_dense (M : Amenable.Mean G) (S : Set (Func X))
    (hd : ∀ f : Func X, ∀ ε : ℝ, 0<ε → ∃ h∈S, ‖l2 μ (f-h)‖ < ε)
    (T : Func X → Family G Y) {C : ℝ} (hC : 0 ≤ C)
    (hT : ∀ f h : Func X, ∀ g, ‖l2 ν (T f g-T h g)‖ ≤ C*‖l2 μ (f-h)‖)
    (hS : ∀ f∈S, Family.meanNorm ν M (T f) = 0) (f : Func X) :
    Family.meanNorm ν M (T f) = 0 := by
  apply Family.meanNorm_eq_zero_of_approx
  intro ε hε
  have hden : 0 < C+1 := by linarith
  obtain ⟨h,hh,hdist⟩ := hd f (ε/(C+1)) (div_pos hε hden)
  refine ⟨T h, hS h hh, fun g => ?_⟩
  have he : ε/(C+1)*(C+1) = ε := div_mul_cancel₀ _ (ne_of_gt hden)
  have hd0 : 0 ≤ ε/(C+1) := (div_pos hε hden).le
  calc
    _ ≤ C * ‖l2 μ (f-h)‖ := hT f h g
    _ ≤ C*(ε/(C+1)) := mul_le_mul_of_nonneg_left hdist.le hC
    _ ≤ ε := by nlinarith

variable [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]
  [AddAction G X] [AddAction G Y] [MeasurableConstVAdd G X] [MeasurableConstVAdd G Y]
  [VAddInvariantMeasure G X μ]
variable (q : X → Y) (hq : Measurable q) [IsProbabilityMeasure (μ.map q)]
variable (hqcov : ∀ g : G, (fun x => q (g +ᵥ x)) =ᵐ[μ] (fun x => g +ᵥ q x))
omit [StandardBorelSpace Y] [Nonempty Y] in
include hq hqcov in
lemma covariance_zero_of_dense (M : Amenable.Mean G) (S : Set (Func X))
    (hd : ∀ f : Func X, ∀ ε : ℝ, 0<ε → ∃ h∈S, ‖l2 μ (f-h)‖ < ε)
    (φ : G →+ G)
    (hS : ∀ v∈S, ∀ w∈S, Family.meanNorm (μ.map q) M (covariance μ q φ v w) = 0)
    (v w : Func X) : Family.meanNorm (μ.map q) M (covariance μ q φ v w) = 0 := by
  have hw (v : Func X) (hv : v∈S) (w : Func X) :
      Family.meanNorm (μ.map q) M (covariance μ q φ v w) = 0 := by
    apply meanNorm_zero_of_dense μ (μ.map q) M S hd (covariance μ q φ v)
      (C := 2*(bound v : ℝ)) (by positivity) _ (hS v hv) w
    intro w w' g
    have he : covariance μ q φ v w g - covariance μ q φ v w' g = covariance μ q φ v (w-w') g :=
      congrArg (fun F : Family G Y => F g) (covariance_sub_right μ q φ v w w').symm
    rw [he]
    exact covariance_norm_right μ q hq hqcov φ v (w-w') g
  apply meanNorm_zero_of_dense μ (μ.map q) M S hd (fun v => covariance μ q φ v w)
    (C := 2*(bound w : ℝ)) (by positivity) _ (fun v hv => hw v hv w) v
  intro v v' g
  have he : covariance μ q φ v w g - covariance μ q φ v' w g = covariance μ q φ (v-v') w g :=
    congrArg (fun F : Family G Y => F g) (covariance_sub_left μ q φ v v' w).symm
  rw [he]
  exact covariance_norm_left μ q hq φ (v-v') w g
end EuclideanFiveColor.BoundedMeasurable

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal
namespace EuclideanFiveColor.RelativeProduct
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
lemma graph_mixture (ν : Measure Y) [SFinite ν] (κ : Kernel Y X) [IsMarkovKernel κ]
    (q : X → Y) (hq : Measurable q) (hf : ∀ᵐ y ∂ν, ∀ᵐ x ∂κ y, q x = y) :
    (κ ∘ₘ ν).map (fun x => (q x,x)) = ν ⊗ₘ κ := by
  ext s hs
  rw [Measure.map_apply (show Measurable (fun x => (q x,x)) from hq.prodMk measurable_id) hs,
    Measure.bind_apply (hs.preimage (show Measurable (fun x => (q x,x)) from hq.prodMk measurable_id)) (Kernel.measurable κ).aemeasurable,
    Measure.compProd_apply hs]
  apply lintegral_congr_ae
  filter_upwards [hf] with y hy
  apply measure_congr
  filter_upwards [hy] with x hx
  change ((q x,x) ∈ s) = ((y,x) ∈ s)
  rw [hx]

lemma map_mixture (ν : Measure Y) [SFinite ν] (κ : Kernel Y X) [IsMarkovKernel κ]
    (q : X → Y) (hq : Measurable q) (hf : ∀ᵐ y ∂ν, ∀ᵐ x ∂κ y, q x = y) :
    (κ ∘ₘ ν).map q = ν := by
  have he := congrArg Measure.fst (graph_mixture ν κ q hq hf)
  change ((κ ∘ₘ ν).map (fun x => (q x,id x))).fst = (ν ⊗ₘ κ).fst at he
  simpa only [Measure.fst_map_prodMk measurable_id, Measure.fst_compProd] using he

variable [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]
variable (μ : Measure X) [IsProbabilityMeasure μ] (q : X → Y) (hq : Measurable q)

include hq in
lemma square_fiber : ∀ᵐ y ∂μ.map q,
    ∀ᵐ z ∂((condDistrib id q μ).prod (condDistrib id q μ)) y, q z.1 = y := by
  filter_upwards [ConditionalFiber.ae_in_own_fiber μ q hq] with y hy
  rw [Kernel.prod_apply]
  exact (measurePreserving_fst (μ := condDistrib id q μ y)
    (ν := condDistrib id q μ y)).quasiMeasurePreserving.ae hy

lemma law_map_base : (law μ q hq).map (q ∘ Prod.fst) = μ.map q := by
  rw [law_eq_mixture]
  exact map_mixture (μ.map q) _ _ (hq.comp measurable_fst) (square_fiber μ q hq)

lemma conditional_square :
    condDistrib id (q ∘ Prod.fst) (law μ q hq) =ᵐ[μ.map q]
      (condDistrib id q μ).prod (condDistrib id q μ) := by
  have he := graph_mixture (μ.map q) ((condDistrib id q μ).prod (condDistrib id q μ))
    (q ∘ Prod.fst) (hq.comp measurable_fst) (square_fiber μ q hq)
  rw [← law_eq_mixture μ q hq] at he
  have hc := condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    (hq.comp measurable_fst) measurable_id (he.trans (by rw [law_map_base]))
  rwa [law_map_base] at hc

end EuclideanFiveColor.RelativeProduct

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction
namespace EuclideanFiveColor.BoundedMeasurable
variable {G X Y : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace X] [Nonempty X]
  [StandardBorelSpace Y] [Nonempty Y]
variable (μ : Measure X) [IsProbabilityMeasure μ] (q : X → Y) (hq : Measurable q)

omit [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G] in
lemma conditional_tensor (v w : Func X) :
    conditional (RelativeProduct.law μ q hq) (q ∘ Prod.fst) (tensor v w) =ᵐ[μ.map q]
      conditional μ q v * conditional μ q w := by
  filter_upwards [RelativeProduct.conditional_square μ q hq] with y hy
  change (∫ z, tensor v w z ∂condDistrib id (q ∘ Prod.fst) (RelativeProduct.law μ q hq) y) = _
  rw [hy, Kernel.prod_apply]
  exact integral_prod_mul v w

variable [AddAction G X] [AddAction G Y] [MeasurableConstVAdd G X] [MeasurableConstVAdd G Y]
  [VAddInvariantMeasure G X μ]
variable (hqcov : ∀ g : G, (fun x => q (g +ᵥ x)) =ᵐ[μ] (fun x => g +ᵥ q x))
omit [TopologicalSpace G] [DiscreteTopology G] [StandardBorelSpace X] [Nonempty X]
  [StandardBorelSpace Y] [Nonempty Y] [IsProbabilityMeasure μ] in
include hq hqcov in
lemma factor_preserving (g : G) : MeasurePreserving (fun y : Y => g +ᵥ y) (μ.map q) (μ.map q) := by
  refine ⟨measurable_const_vadd g, ?_⟩
  rw [Measure.map_map (measurable_const_vadd g) hq]
  calc
    _ = μ.map (q ∘ (fun x => g +ᵥ x)) := Measure.map_congr (hqcov g).symm
    _ = _ := by rw [← Measure.map_map hq (measurable_const_vadd g), (measurePreserving_vadd g μ).map_eq]

omit [TopologicalSpace G] [DiscreteTopology G] in
include hqcov in
lemma covariance_tensor (φ : G →+ G) (a₁ a₂ b₁ b₂ : Func X) (g : G) :
    covariance (RelativeProduct.law μ q hq) (q ∘ Prod.fst) φ (tensor a₁ a₂) (tensor b₁ b₂) g =ᵐ[μ.map q]
      ((Family.conditional μ q (Family.const a₁ * Family.orbit φ b₁)) *
        (Family.conditional μ q (Family.const a₂ * Family.orbit φ b₂)) -
        (Family.const (conditional μ q a₁) * Family.orbit φ (conditional μ q b₁)) *
        (Family.const (conditional μ q a₂) * Family.orbit φ (conditional μ q b₂)) : Family G Y) g := by
  have ht : tensor a₁ a₂ * act (φ g) (tensor b₁ b₂) = tensor (a₁*act (φ g) b₁) (a₂*act (φ g) b₂) := by
    rw [← tensor_act, tensor_mul]
  have h₁ := conditional_tensor μ q hq a₁ a₂
  have h₂ := (factor_preserving μ q hq hqcov (φ g)).quasiMeasurePreserving.ae
    (conditional_tensor μ q hq b₁ b₂)
  have h₃ := conditional_tensor μ q hq (a₁*act (φ g) b₁) (a₂*act (φ g) b₂)
  filter_upwards [h₁,h₂,h₃] with y hy₁ hy₂ hy₃
  change conditional _ _ (tensor a₁ a₂ * act (φ g) (tensor b₁ b₂)) y -
    conditional _ _ (tensor a₁ a₂) y * conditional _ _ (tensor b₁ b₂) (φ g +ᵥ y) = _
  rw [ht, hy₁, hy₂, hy₃]
  dsimp only [Family.mul_apply, Family.sub_apply, Family.conditional_apply,
    Family.const_apply, Family.orbit_apply, mul_apply, sub_apply, act_apply, Pi.mul_apply]
  ring

variable [IsProbabilityMeasure (μ.map q)]
include hqcov in
lemma covariance_tensor_mean_zero (M : Amenable.Mean G) (hp : PairVanishing μ q hq M)
    (φ : G →+ G) (hs : Function.Surjective φ) (a₁ a₂ b₁ b₂ : Func X) :
    Family.meanNorm (μ.map q) M
      (covariance (RelativeProduct.law μ q hq) (q ∘ Prod.fst) φ (tensor a₁ a₂) (tensor b₁ b₂)) = 0 := by
  let A₁ := Family.conditional μ q (Family.const a₁ * Family.orbit φ b₁)
  let A₂ := Family.conditional μ q (Family.const a₂ * Family.orbit φ b₂)
  let B₁ := Family.const (conditional μ q a₁) * Family.orbit φ (conditional μ q b₁)
  let B₂ := Family.const (conditional μ q a₂) * Family.orbit φ (conditional μ q b₂)
  have h₁ : Family.meanNorm (μ.map q) M (A₁-B₁) = 0 := covariance_mean_zero μ q hq hqcov M hp φ hs a₁ b₁
  have h₂ : Family.meanNorm (μ.map q) M (A₂-B₂) = 0 := covariance_mean_zero μ q hq hqcov M hp φ hs a₂ b₂
  rw [Family.meanNorm_congr (μ.map q) M (covariance_tensor μ q hq hqcov φ a₁ a₂ b₁ b₂)]
  change Family.meanNorm (μ.map q) M (A₁*A₂-B₁*B₂) = 0
  have he : A₁*A₂-B₁*B₂ = (A₁-B₁)*A₂ + (A₂-B₂)*B₁ := by ring
  rw [he]
  exact Family.meanNorm_add_zero _ _ (Family.meanNorm_mul_zero _ _ h₁) (Family.meanNorm_mul_zero _ _ h₂)
end EuclideanFiveColor.BoundedMeasurable

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal
namespace EuclideanFiveColor.BoundedMeasurable
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
private inductive FiniteTensor : Func (X×Y) → Prop
  | tensor (f : Func X) (g : Func Y) : FiniteTensor (tensor f g)
  | add {f g : Func (X×Y)} : FiniteTensor f → FiniteTensor g → FiniteTensor (f+g)

lemma FiniteTensor.zero : FiniteTensor (0 : Func (X×Y)) := by
  have he : BoundedMeasurable.tensor (0 : Func X) (0 : Func Y) = 0 := by ext z; simp
  rw [← he]
  exact .tensor _ _

lemma FiniteTensor.sum {ι : Type*} (s : Finset ι) (f : ι → Func (X×Y))
    (hf : ∀ i∈s, FiniteTensor (f i)) : FiniteTensor (∑ i∈s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using FiniteTensor.zero (X := X) (Y := Y)
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact .add (hf i (Finset.mem_insert_self _ _)) (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

lemma func_sum_apply {ι : Type*} (s : Finset ι) (f : ι → Func X) (x : X) :
    (∑ i∈s, f i) x = ∑ i∈s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih]

variable [MeasurableSpace.CountablyGenerated X] [MeasurableSpace.CountablyGenerated Y]
open RectangleDensity

private def codeCell (n : ℕ) (c : Code n) : Func X := by
  classical
  refine ⟨fun x => if code X n x = c then (1:ℂ) else 0, ?_, 1, ?_⟩
  · exact Measurable.ite ((measurable_code n) (measurableSet_singleton c)) measurable_const measurable_const
  · intro x; dsimp only; split_ifs <;> simp

lemma tensor_code_finite (n : ℕ) (a : Code n × Code n → ℂ) (F : Func (X×Y))
    (he : ∀ z, F z = a (pairCode n z)) : FiniteTensor F := by
  classical
  let T : Code n × Code n → Func (X×Y) := fun c =>
    tensor (a c • codeCell (X := X) n c.1) (codeCell (X := Y) n c.2)
  have hsum : F = ∑ c, T c := by
    ext z
    rw [he, func_sum_apply]
    rw [Finset.sum_eq_single (pairCode n z)]
    · simp [T, tensor_apply, codeCell, pairCode]
    · intro c _ hc
      have hn : code X n z.1 ≠ c.1 ∨ code Y n z.2 ≠ c.2 := by
        contrapose! hc
        exact Prod.ext hc.1.symm hc.2.symm
      rcases hn with hn | hn <;> simp [T, tensor_apply, codeCell, hn]
    · simp
  rw [hsum]
  exact FiniteTensor.sum _ _ (fun _ _ => .tensor _ _)

lemma finiteTensor_dense (ν : Measure (X×Y)) [IsProbabilityMeasure ν]
    (f : Func (X×Y)) (ε : ℝ) (hε : 0 < ε) :
    ∃ h : Func (X×Y), FiniteTensor h ∧ ‖l2 ν (f-h)‖ < ε := by
  obtain ⟨n,a,ha,_,he⟩ := bounded_rectangles ν f (measurable f) (bound f)
    (bound f).coe_nonneg (norm_le_bound f) ε hε
  let h : Func (X×Y) := ⟨fun z => a (pairCode n z),
    (measurable_of_countable a).comp (measurable_pairCode n), 2*bound f,
    fun z => by simpa only [NNReal.coe_mul, NNReal.coe_ofNat] using ha (pairCode n z)⟩
  refine ⟨h, tensor_code_finite n a h (fun _ => rfl), ?_⟩
  have hh : ‖l2 ν (f-h)‖^2 < ε^2 := by
    rw [norm_l2_sq]
    exact he
  nlinarith [norm_nonneg (l2 ν (f-h))]
end EuclideanFiveColor.BoundedMeasurable

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction
namespace EuclideanFiveColor.BoundedMeasurable

section
variable {G X Y : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace X] [Nonempty X]
  [StandardBorelSpace Y] [Nonempty Y]
  [AddAction G X] [AddAction G Y] [MeasurableConstVAdd G X] [MeasurableConstVAdd G Y]
variable (μ : Measure X) [IsProbabilityMeasure μ] [VAddInvariantMeasure G X μ]
  (q : X → Y) (hq : Measurable q) [IsProbabilityMeasure (μ.map q)]
variable (hqcov : ∀ g : G, (fun x => q (g +ᵥ x)) =ᵐ[μ] (fun x => g +ᵥ q x))
include hqcov in
lemma pairVanishing_of_covariance (M : Amenable.Mean G)
    (hc : ∀ (φ : G →+ G), Function.Surjective φ → ∀ v w : Func X,
      Family.meanNorm (μ.map q) M (covariance μ q φ v w) = 0) : PairVanishing μ q hq M := by
  intro φ hs v w hw
  have he0 : l2 μ (project μ q hq w) = l2 μ 0 := hw.trans (map_zero _).symm
  have hp : project μ q hq w =ᵐ[μ] (0 : Func X) := (l2_eq_iff μ _ _).mp he0
  have he (g : G) : covariance μ q φ v w g =ᵐ[μ.map q] conditional μ q (v*act (φ g) w) := by
    apply (covariance_center μ q hq hqcov φ v w g).trans
    apply conditional_congr μ q hq
    filter_upwards [(measurePreserving_vadd (φ g) μ).quasiMeasurePreserving.ae hp] with x hx
    change v x * (w (φ g +ᵥ x) - project μ q hq w (φ g +ᵥ x)) = v x*w (φ g +ᵥ x)
    change project μ q hq w (φ g +ᵥ x) = 0 at hx
    rw [hx, sub_zero]
  have hmean := hc φ hs v w
  have hnorm : Family.meanNorm (μ.map q) M (covariance μ q φ v w) =
      Family.meanNorm (μ.map q) M (Family.conditional μ q (Family.const v * Family.orbit φ w)) :=
    Family.meanNorm_congr _ _ he
  rw [hnorm] at hmean
  have hseq : Family.toL2 (μ.map q) (Family.conditional μ q (Family.const v * Family.orbit φ w)) =
      pairSequence μ q hq φ v w := by ext g; rfl
  unfold Family.meanNorm at hmean
  rwa [hseq] at hmean
end

variable {G X Y : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace X] [Nonempty X]
  [StandardBorelSpace Y] [Nonempty Y]
  [AddAction G X] [AddAction G Y] [MeasurableConstVAdd G X] [MeasurableConstVAdd G Y]
variable (μ : Measure X) [IsProbabilityMeasure μ] [VAddInvariantMeasure G X μ]
  (q : X → Y) (hq : Measurable q)
variable (hqcov : ∀ g : G, (fun x => q (g +ᵥ x)) =ᵐ[μ] (fun x => g +ᵥ q x))

omit [TopologicalSpace G] [DiscreteTopology G] [VAddInvariantMeasure G X μ]
  [StandardBorelSpace Y] [Nonempty Y] [MeasurableConstVAdd G X] [MeasurableConstVAdd G Y] in
include hqcov in
lemma square_equivariant (g : G) :
    (fun z => (q ∘ Prod.fst) (g +ᵥ z)) =ᵐ[RelativeProduct.law μ q hq]
      (fun z => g +ᵥ (q ∘ Prod.fst) z) := by
  have hp : MeasurePreserving Prod.fst (RelativeProduct.law μ q hq) μ :=
    ⟨measurable_fst, Measure.fst_compProd μ ((condDistrib id q μ).comap q hq)⟩
  exact hp.quasiMeasurePreserving.ae (hqcov g)

variable [IsProbabilityMeasure (μ.map q)]
include hqcov in
lemma covariance_finiteTensor_mean_zero (M : Amenable.Mean G) (hp : PairVanishing μ q hq M)
    (φ : G →+ G) (hs : Function.Surjective φ) (v w : Func (X×X))
    (hv : FiniteTensor v) (hw : FiniteTensor w) :
    Family.meanNorm (μ.map q) M
      (covariance (RelativeProduct.law μ q hq) (q ∘ Prod.fst) φ v w) = 0 := by
  induction hv with
  | tensor a₁ a₂ =>
    induction hw with
    | tensor b₁ b₂ => exact covariance_tensor_mean_zero μ q hq hqcov M hp φ hs a₁ a₂ b₁ b₂
    | add _ _ ih₁ ih₂ =>
      rw [covariance_add_right]
      exact Family.meanNorm_add_zero _ _ ih₁ ih₂
  | add _ _ ih₁ ih₂ =>
    rw [covariance_add_left]
    exact Family.meanNorm_add_zero _ _ ih₁ ih₂

include hqcov in
lemma square_pairVanishing (M : Amenable.Mean G) (hp : PairVanishing μ q hq M) :
    PairVanishing (RelativeProduct.law μ q hq) (q ∘ Prod.fst) (hq.comp measurable_fst) M := by
  have : VAddInvariantMeasure G (X×X) (RelativeProduct.law μ q hq) :=
    RelativeProduct.law_invariant_add μ q hq (fun g => measurePreserving_vadd g μ) hqcov
  have : IsProbabilityMeasure ((RelativeProduct.law μ q hq).map (q ∘ Prod.fst)) := by
    rw [RelativeProduct.law_map_base μ q hq]
    infer_instance
  apply pairVanishing_of_covariance (RelativeProduct.law μ q hq) (q ∘ Prod.fst)
    (hq.comp measurable_fst) (square_equivariant μ q hq hqcov) M
  intro φ hs v w
  apply covariance_zero_of_dense (RelativeProduct.law μ q hq) (q ∘ Prod.fst)
    (hq.comp measurable_fst) (square_equivariant μ q hq hqcov) M
    {f | FiniteTensor f} (fun f ε hε => finiteTensor_dense _ f ε hε) φ _ v w
  intro v hv w hw
  simpa only [RelativeProduct.law_map_base μ q hq] using
    covariance_finiteTensor_mean_zero μ q hq hqcov M hp φ hs v w hv hw
end EuclideanFiveColor.BoundedMeasurable

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace
namespace EuclideanFiveColor.BoundedMeasurable
variable {G X Y : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace X] [Nonempty X]
  [StandardBorelSpace Y] [Nonempty Y]
variable (μ : Measure X) [IsProbabilityMeasure μ] (q : X → Y) (hq : Measurable q)

omit [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G] in
lemma square_tensor_centered (f : Func X) (hf : l2 μ (project μ q hq f) = 0) :
    l2 (RelativeProduct.law μ q hq)
      (project (RelativeProduct.law μ q hq) (q ∘ Prod.fst) (hq.comp measurable_fst)
        (tensor f (bmConj f))) = 0 := by
  have he : l2 (μ.map q) (conditional μ q f) = 0 := by
    apply norm_eq_zero.mp
    rw [← norm_project_l2 μ q hq, hf, norm_zero]
  have hz : conditional μ q f =ᵐ[μ.map q] (0 : Func Y) := by
    apply (l2_eq_iff _ _ _).mp
    rw [he, map_zero]
  have ht : conditional (RelativeProduct.law μ q hq) (q ∘ Prod.fst) (tensor f (bmConj f))
      =ᵐ[μ.map q] (0 : Func Y) := by
    filter_upwards [conditional_tensor μ q hq f (bmConj f), hz] with y hy hz
    rw [hy]
    change conditional μ q f y * _ = 0
    rw [hz, zero_apply, zero_mul]
  rw [← map_zero (l2 (RelativeProduct.law μ q hq))]
  apply (l2_eq_iff _ _ _).mpr
  have ht' : conditional (RelativeProduct.law μ q hq) (q ∘ Prod.fst) (tensor f (bmConj f)) =ᵐ[(RelativeProduct.law μ q hq).map (q ∘ Prod.fst)] (0 : Func Y) := by
    simpa only [RelativeProduct.law_map_base μ q hq] using ht
  exact (ae_of_ae_map (hq.comp measurable_fst).aemeasurable ht').mono (fun z hz => hz)

variable {ι : Type*} [DecidableEq ι]
omit [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G] [StandardBorelSpace X]
  [Nonempty X] [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y] in
lemma tensor_prod (s : Finset ι) (f h : ι → Func X) :
    tensor (∏ i∈s, f i) (∏ i∈s, h i) = ∏ i∈s, tensor (f i) (h i) := by
  induction s using Finset.induction_on with
  | empty => ext z; simp [tensor_apply]
  | @insert i s hi ih => simp only [Finset.prod_insert hi, tensor_mul, ih]

variable [AddAction G X] [AddAction G Y] [MeasurableConstVAdd G X] [MeasurableConstVAdd G Y]
  [VAddInvariantMeasure G X μ]
variable (hqcov : ∀ g : G, (fun x => q (g +ᵥ x)) =ᵐ[μ] (fun x => g +ᵥ q x))
variable [IsProbabilityMeasure (μ.map q)]
include hqcov in
lemma centered_conditional_mean_zero (M : Amenable.Mean G) (hp : PairVanishing μ q hq M)
    (s : Finset ι) (φ : ι → G →+ G) (θ : G →+ G) (f : ι → Func X)
    (ha : Admissible s (fun i => θ + φ i))
    (hc : ∃ j∈s, l2 μ (project μ q hq (f j)) = 0) :
    Family.meanNorm (μ.map q) M (Family.conditional μ q (∏ i∈s, Family.orbit (φ i) (f i))) = 0 := by
  let ρ := RelativeProduct.law μ q hq
  have : VAddInvariantMeasure G (X×X) ρ :=
    RelativeProduct.law_invariant_add μ q hq (fun g => measurePreserving_vadd g μ) hqcov
  let t : ι → Func (X×X) := fun i => tensor (f i) (bmConj (f i))
  let F : Family G (X×X) := ∏ i∈s, Family.orbit (θ+φ i) (t i)
  have htc : ∃ j∈s, l2 ρ (project ρ (q ∘ Prod.fst) (hq.comp measurable_fst) (t j)) = 0 := by
    obtain ⟨j,hj,hf⟩ := hc
    exact ⟨j,hj,square_tensor_centered μ q hq (f j) hf⟩
  have hv : Family.avg ρ M F = 0 := avg_product_zero_of_pair ρ (q ∘ Prod.fst)
    (hq.comp measurable_fst) (square_equivariant μ q hq hqcov) M
    (square_pairVanishing μ q hq hqcov M hp) s (fun i => θ+φ i) t ha htc
  unfold Family.meanNorm
  apply M.norm_mean_zero_of_square
  have he : Amenable.Mean.squareNorm (Family.toL2 (μ.map q)
      (Family.conditional μ q (∏ i∈s, Family.orbit (φ i) (f i)))) =
      Amenable.Mean.pairing (Family.toL2 ρ F) (l2 ρ (1 : Func (X×X))) := by
    ext g
    simp only [Amenable.Mean.squareNorm_apply, Amenable.Mean.pairing_apply,
      Family.toL2_apply, Family.conditional_apply, Family.prod_apply, Family.orbit_apply]
    change ‖l2 (μ.map q) (conditional μ q (∏ i∈s, act (φ i g) (f i)))‖^2 =
      inner ℝ (l2 ρ (F g)) (l2 ρ (1 : Func (X×X)))
    have hF : F g = act (θ g) (tensor (∏ i∈s, act (φ i g) (f i))
        (bmConj (∏ i∈s, act (φ i g) (f i)))) := by
      dsimp only [F]
      rw [Family.prod_apply, conj_prod, tensor_prod, act_prod]
      apply Finset.prod_congr rfl
      intro i hi
      rw [← act_conj, tensor_act, ← act_add]
      rfl
    have hc1 : bmConj (1 : Func (X×X)) = 1 := by ext z; simp
    rw [hF, real_inner_comm, l2_inner, hc1, one_mul, integral_act,
      integral_tensor_self μ q hq]
    rfl
  rw [he, ← Family.avg_pair, hv, inner_zero_left]
end EuclideanFiveColor.BoundedMeasurable

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace
namespace EuclideanFiveColor.AlgebraReplacement
variable {ι A : Type*} [DecidableEq ι] [CommRing A]
lemma prod_sub_prod (s : Finset ι) (f g : ι → A) :
    (∏ i∈s, f i) - (∏ i∈s, g i) = ∑ t∈s.powerset.erase ∅,
      (∏ i∈t, (f i-g i)) * ∏ i∈s\t, g i := by
  have he := Finset.prod_add (fun i => f i-g i) g s
  simp only [sub_add_cancel] at he
  rw [he]
  have hs := Finset.sum_erase_add s.powerset
    (fun t => (∏ i∈t, (f i-g i)) * ∏ i∈s\t, g i) (Finset.empty_mem_powerset s)
  simp only [Finset.prod_empty, Finset.sdiff_empty, one_mul] at hs
  exact sub_eq_iff_eq_add.mpr hs.symm
end EuclideanFiveColor.AlgebraReplacement
namespace EuclideanFiveColor.BoundedMeasurable
variable {G X Y : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace X] [Nonempty X]
  [StandardBorelSpace Y] [Nonempty Y]
variable (μ : Measure X) [IsProbabilityMeasure μ] (q : X → Y) (hq : Measurable q)
variable {ι : Type*} [DecidableEq ι]
omit [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G] [StandardBorelSpace Y] [Nonempty Y] in
lemma Family.conditional_sum (s : Finset ι) (f : ι → Family G X) :
    Family.conditional μ q (∑ i∈s, f i) = ∑ i∈s, Family.conditional μ q (f i) := by
  induction s using Finset.induction_on with
  | empty => ext g y; simp [Family.conditional, conditional, expect]
  | @insert i s hi ih => simp only [Finset.sum_insert hi, Family.conditional_add, ih]

variable [AddAction G X] [AddAction G Y] [MeasurableConstVAdd G X] [MeasurableConstVAdd G Y]
  [VAddInvariantMeasure G X μ]
variable (hqcov : ∀ g : G, (fun x => q (g +ᵥ x)) =ᵐ[μ] (fun x => g +ᵥ q x))
variable [IsProbabilityMeasure (μ.map q)]
include hqcov in
lemma conditional_multiple_mean_zero (M : Amenable.Mean G) (hp : PairVanishing μ q hq M)
    (s : Finset ι) (φ : ι → G →+ G) (θ : G →+ G) (f : ι → Func X)
    (ha : Admissible s (fun i => θ + φ i)) :
    Family.meanNorm (μ.map q) M (Family.conditional μ q (∏ i∈s, Family.orbit (φ i) (f i)) -
      ∏ i∈s, Family.orbit (φ i) (conditional μ q (f i))) = 0 := by
  let a : ι → Family G X := fun i => Family.orbit (φ i) (f i)
  let b : ι → Family G X := fun i => Family.orbit (φ i) (project μ q hq (f i))
  have hb (g : G) : conditional μ q ((∏ i∈s, b i) g) =ᵐ[μ.map q]
      (∏ i∈s, Family.orbit (φ i) (conditional μ q (f i))) g := by
    simp only [Family.prod_apply, Family.orbit_apply]
    apply (conditional_congr μ q hq (f := ∏ i∈s, act (φ i g) (project μ q hq (f i)))
      (g := comp (∏ i∈s, act (φ i g) (conditional μ q (f i))) q hq) ?_).trans
      (conditional_lift μ q hq _)
    filter_upwards [prod_act_project_lift μ q hq hqcov s φ f g] with x hx
    simpa only [func_prod_apply, Finset.prod_apply] using hx
  have hrep : Family.meanNorm (μ.map q) M (Family.conditional μ q
      ((∏ i∈s, a i) - ∏ i∈s, b i)) = 0 := by
    rw [AlgebraReplacement.prod_sub_prod s a b, Family.conditional_sum]
    apply Family.meanNorm_sum_zero
    intro t ht
    have hts : t ⊆ s := Finset.mem_powerset.mp (Finset.mem_of_mem_erase ht)
    have htn : t.Nonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.ne_of_mem_erase ht)
    rw [AlgebraReplacement.mixed_prod s t hts]
    let w : ι → Func X := fun i => if i∈t then f i-project μ q hq (f i) else project μ q hq (f i)
    have he : (∏ i∈s, if i∈t then a i-b i else b i) = ∏ i∈s, Family.orbit (φ i) (w i) := by
      apply Finset.prod_congr rfl
      intro i hi
      by_cases hit : i∈t
      · simp only [hit, ↓reduceIte, w, a, b]
        apply Family.ext
        intro g
        exact (act_sub _ _ _).symm
      · simp only [hit, ↓reduceIte, w, b]
    rw [he]
    apply centered_conditional_mean_zero μ q hq hqcov M hp s φ θ w ha
    obtain ⟨j,hj⟩ := htn
    refine ⟨j,hts hj,?_⟩
    simp only [w, hj, ↓reduceIte]
    exact center_project_l2 μ q hq (f j)
  rw [Family.conditional_sub] at hrep
  rw [Family.meanNorm_congr (μ.map q) M (F := Family.conditional μ q (∏ i∈s, a i) -
      Family.conditional μ q (∏ i∈s, b i)) (H := Family.conditional μ q (∏ i∈s, a i) -
      ∏ i∈s, Family.orbit (φ i) (conditional μ q (f i))) (fun g => by
        filter_upwards [hb g] with y hy
        simp only [Family.sub_apply, sub_apply, Family.conditional_apply]
        rw [hy])] at hrep
  exact hrep
end EuclideanFiveColor.BoundedMeasurable

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction
namespace EuclideanFiveColor.BoundedMeasurable
variable {G : Type*} [AddCommGroup G]
private def scaleHom (n : ℤ) : G →+ G := n • AddMonoidHom.id G
@[simp] lemma scaleHom_apply (n : ℤ) (g : G) : scaleHom n g = n • g := rfl
lemma scaleHom_add (n m : ℤ) : scaleHom (G := G) (n+m) = scaleHom n + scaleHom m := add_smul _ _ _
lemma scaleHom_sub (n m : ℤ) : scaleHom (G := G) (n-m) = scaleHom n - scaleHom m := sub_smul _ _ _
variable {ι : Type*} [DecidableEq ι]
omit [DecidableEq ι] in
lemma shifted_admissible (hdiv : ∀ n : ℤ, n ≠ 0 → Function.Surjective (scaleHom (G := G) n))
    (s : Finset ι) (n : ι → ℤ) (hn : Set.InjOn n s) :
    ∃ m : ℤ, Admissible s (fun i => scaleHom (G := G) m + scaleHom (n i)) := by
  obtain ⟨m,hm⟩ := Infinite.exists_notMem_finset (s.image (fun i => -n i))
  refine ⟨m, ?_, ?_⟩
  · intro i hi
    dsimp only
    rw [← scaleHom_add]
    apply hdiv
    intro hz
    have he : m = -n i := eq_neg_of_add_eq_zero_left hz
    exact hm (Finset.mem_image.mpr ⟨i,hi,he.symm⟩)
  · intro i hi j hj hij
    have he : (scaleHom m + scaleHom (n i)) - (scaleHom m + scaleHom (n j)) =
        scaleHom (G := G) (n i-n j) := by rw [scaleHom_sub]; abel
    rw [he]
    apply hdiv
    exact sub_ne_zero.mpr (fun h => hij (hn hi hj h))
variable {X Y : Type*} [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace X] [Nonempty X]
  [StandardBorelSpace Y] [Nonempty Y]
  [AddAction G X] [AddAction G Y] [MeasurableConstVAdd G X] [MeasurableConstVAdd G Y]
variable (μ : Measure X) [IsProbabilityMeasure μ] [VAddInvariantMeasure G X μ]
  (q : X → Y) (hq : Measurable q)
variable (hqcov : ∀ g : G, (fun x => q (g +ᵥ x)) =ᵐ[μ] (fun x => g +ᵥ q x))
variable [IsProbabilityMeasure (μ.map q)]
include hqcov in
lemma conditional_integer_multiple_mean_zero
    (hdiv : ∀ n : ℤ, n ≠ 0 → Function.Surjective (scaleHom (G := G) n))
    (M : Amenable.Mean G) (hp : PairVanishing μ q hq M)
    (s : Finset ι) (n : ι → ℤ) (f : ι → Func X) (hn : Set.InjOn n s) :
    Family.meanNorm (μ.map q) M (Family.conditional μ q (∏ i∈s, Family.orbit (scaleHom (n i)) (f i)) -
      ∏ i∈s, Family.orbit (scaleHom (n i)) (conditional μ q (f i))) = 0 := by
  obtain ⟨m,hm⟩ := shifted_admissible hdiv s n hn
  exact conditional_multiple_mean_zero μ q hq hqcov M hp s (fun i => scaleHom (n i)) (scaleHom m) f hm
end EuclideanFiveColor.BoundedMeasurable

end

end ParishFactor
end

-- OAI.MeasureTheory.CompactFactors.Stationary
section
namespace ParishFactor

noncomputable section

namespace PlaneFiveColor.Spectral
open MeasureTheory ProbabilityTheory EuclideanFiveColor
variable [Carrier]
private instance K_countable : Countable K := by
  let f : K → E := fun k => ⟨(k.val : ℂ), k.property⟩
  apply Function.Injective.countable (f := f)
  intro a b h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : E => (z : ℂ)) h
end PlaneFiveColor.Spectral

end

end ParishFactor
end

-- OAI.Analysis.PlaneSpectrum.Representations
section
namespace ParishFactor

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction
namespace PlaneFiveColor.Spectral
variable [Carrier]

private def Rot := Additive K deriving AddCommGroup
private instance : TopologicalSpace Rot := ⊥
private instance : DiscreteTopology Rot := ⟨rfl⟩
private def rotMul (g : Rot) : K := Additive.toMul g
private def mulRot (k : K) : Rot := Additive.ofMul k
@[simp] lemma rotMul_mulRot (k : K) : rotMul (mulRot k) = k := rfl
@[simp] lemma mulRot_rotMul (g : Rot) : mulRot (rotMul g) = g := rfl
private instance rotAction (X : Type*) [MulAction K X] : AddAction Rot X where
  vadd g x := rotMul g • x
  zero_vadd x := one_smul K x
  add_vadd g h x := mul_smul (rotMul g) (rotMul h) x
@[simp] lemma rot_vadd {X : Type*} [MulAction K X] (g : Rot) (x : X) :
    g +ᵥ x = rotMul g • x := rfl
private instance rotMeasurable {X : Type*} [MeasurableSpace X] [MulAction K X]
    [MeasurableConstSMul K X] : MeasurableConstVAdd Rot X where
  measurable_const_vadd g := measurable_const_smul (rotMul g)
private instance rotInvariant {X : Type*} [MeasurableSpace X] [MulAction K X]
    (μ : Measure X) [SMulInvariantMeasure K X μ] : VAddInvariantMeasure Rot X μ where
  measure_preimage_vadd g s _hs := measure_preimage_smul μ (rotMul g) s
private instance rotErgodic {X : Type*} [MeasurableSpace X] [MulAction K X]
    (μ : Measure X) [ErgodicSMul K X μ] : ErgodicVAdd Rot X μ where
  aeconst_of_forall_preimage_vadd_ae_eq hm he :=
    ErgodicSMul.aeconst_of_forall_preimage_smul_ae_eq hm (fun k => he (mulRot k))
lemma rot_zsmul_surjective (n : ℤ) (hn : n ≠ 0) :
    Function.Surjective (EuclideanFiveColor.BoundedMeasurable.scaleHom (G := Rot) n) := by
  intro g
  obtain ⟨k,hk⟩ := K_pow_surjective n.natAbs (Int.natAbs_ne_zero.mpr hn) (rotMul g)
  rcases n with n | n
  · refine ⟨mulRot k, ?_⟩
    change Additive.ofMul (k^n) = g
    exact congrArg mulRot hk
  · refine ⟨mulRot k⁻¹, ?_⟩
    change Additive.ofMul (k⁻¹ ^ (Int.negSucc n)) = g
    have he : k⁻¹ ^ (Int.negSucc n) = k^(n+1) := by simp
    rw [he]
    exact congrArg mulRot hk
end PlaneFiveColor.Spectral
end

end ParishFactor
end

-- OAI.Analysis.PlaneSpectrum.Energy
section
namespace ParishFactor

noncomputable section

section
open scoped BoundedContinuousFunction
open Filter Topology
namespace EuclideanFiveColor.MovingMean

section
open PlaneFiveColor.InvariantMean
variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
variable (b : Finset G × ℕ → G)
private def approxAt (i : Finset G × ℕ) (f : G →ᵇ ℝ) : ℝ := cube i.1.toList i.2 f (b i)
lemma approx_norm_le (i : Finset G × ℕ) (f : G →ᵇ ℝ) : ‖approxAt b i f‖ ≤ ‖f‖ :=
  ((cube i.1.toList i.2 f).norm_coe_le_norm (b i)).trans (cube_norm_le _ _ _)

lemma approx_has_limit (f : G →ᵇ ℝ) :
    ∃ r : ℝ, Tendsto (fun i => approxAt b i f) (averagingUF G : Filter _) (𝓝 r) := by
  have hb : (Ultrafilter.map (fun i => approxAt b i f) (averagingUF G) : Filter ℝ) ≤
      𝓟 (Set.Icc (-‖f‖) ‖f‖) := by
    rw [Ultrafilter.coe_map, Filter.le_principal_iff, Filter.mem_map]
    apply Filter.Eventually.of_forall
    intro i
    exact abs_le.mp (approx_norm_le b i f)
  obtain ⟨r, _, hr⟩ := isCompact_Icc.ultrafilter_le_nhds
    (Ultrafilter.map (fun i => approxAt b i f) (averagingUF G)) hb
  exact ⟨r, hr⟩

private def meanAt (f : G →ᵇ ℝ) : ℝ :=
  (averagingUF G : Filter _).limUnder (fun i => approxAt b i f)

lemma tendsto_approx (f : G →ᵇ ℝ) :
    Tendsto (fun i => approxAt b i f) (averagingUF G : Filter _) (𝓝 (meanAt b f)) :=
  tendsto_nhds_limUnder (approx_has_limit b f)

lemma mean_add (f h : G →ᵇ ℝ) : meanAt b (f+h) = meanAt b f + meanAt b h := by
  apply Tendsto.limUnder_eq
  convert (tendsto_approx b f).add (tendsto_approx b h) using 1
  simp only [approxAt, cube_add, BoundedContinuousFunction.add_apply]

lemma mean_smul (c : ℝ) (f : G →ᵇ ℝ) : meanAt b (c • f) = c * meanAt b f := by
  apply Tendsto.limUnder_eq
  convert (tendsto_approx b f).const_mul c using 1
  simp only [approxAt, cube_smul, BoundedContinuousFunction.smul_apply, smul_eq_mul]

lemma mean_const (c : ℝ) : meanAt b (BoundedContinuousFunction.const G c) = c := by
  apply Tendsto.limUnder_eq
  convert (tendsto_const_nhds : Tendsto (fun _ : Finset G × ℕ => c)
    (averagingUF G : Filter _) (𝓝 c)) using 1
  simp only [approxAt, cube_const, BoundedContinuousFunction.const_apply]

lemma mean_nonneg (f : G →ᵇ ℝ) (hf : ∀ x, 0 ≤ f x) : 0 ≤ meanAt b f := by
  exact ge_of_tendsto (tendsto_approx b f) (Filter.Eventually.of_forall fun i =>
    cube_nonneg i.1.toList i.2 f hf (b i))

lemma mean_norm_le (f : G →ᵇ ℝ) : ‖meanAt b f‖ ≤ ‖f‖ := by
  exact le_of_tendsto (tendsto_approx b f).norm
    (Filter.Eventually.of_forall fun i => approx_norm_le b i f)

lemma mean_shift (g : G) (f : G →ᵇ ℝ) : meanAt b (shift g f) = meanAt b f := by
  have hz : Tendsto (fun i : Finset G × ℕ => approxAt b i (shift g f) - approxAt b i f)
      (averagingUF G : Filter _) (𝓝 0) := by
    apply squeeze_zero_norm' _ (tendsto_boundary f)
    filter_upwards [eventually_mem g] with i hi
    have h := ((cube i.1.toList i.2 (shift g f-f)).norm_coe_le_norm (b i)).trans
      (cube_coboundary_norm i.1.toList g (Finset.mem_toList.mpr hi) i.2 f)
    simpa only [cube_sub, BoundedContinuousFunction.sub_apply, approxAt] using h
  exact sub_eq_zero.mp (tendsto_nhds_unique ((tendsto_approx b _).sub (tendsto_approx b _)) hz)

private def meanCLM : (G →ᵇ ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := meanAt b, map_add' := mean_add b, map_smul' := mean_smul b }
    1 (by intro f; change ‖meanAt b f‖ ≤ 1 * ‖f‖; simpa only [one_mul] using mean_norm_le b f)

@[simp] lemma meanCLM_apply (f : G →ᵇ ℝ) : meanCLM b f = meanAt b f := rfl

private def toMean : Amenable.Mean G where
  map := meanCLM b
  map_const := mean_const b
  positive := mean_nonneg b
  invariant g f := mean_shift b g f
end

open PlaneFiveColor.InvariantMean
variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
local instance : DecidableEq G := Classical.decEq _
private def cubeSupport : List G → ℕ → Finset G
  | [], _ => {0}
  | g::L, n => (Finset.range (n+1)).biUnion (fun k => (cubeSupport L n).image (fun h => k • g+h))
lemma cube_le_of_support (L : List G) (n : ℕ) (f : G →ᵇ ℝ) (v : G) (c : ℝ)
    (hf : ∀ h ∈ cubeSupport L n, f (v+h) ≤ c) : cube L n f v ≤ c := by
  induction L generalizing v with
  | nil => simpa [cubeSupport, cube] using hf 0 (by simp [cubeSupport])
  | cons g L ih =>
    rw [cube, single_apply]
    have hb : ∑ k ∈ Finset.range (n+1), cube L n f (v+k • g) ≤ (n+1 : ℕ) * c := by
      calc
        _ ≤ ∑ _k ∈ Finset.range (n+1), c := Finset.sum_le_sum fun k hk =>
          ih _ (by
            intro h hh
            have hm : k • g+h ∈ cubeSupport (g::L) n := by
              apply Finset.mem_biUnion.mpr
              exact ⟨k, hk, Finset.mem_image.mpr ⟨h,hh,rfl⟩⟩
            simpa only [add_assoc] using hf _ hm)
        _ = _ := by simp
    calc
      _ ≤ ((n+1 : ℕ) : ℝ)⁻¹ * ((n+1 : ℕ) * c) := mul_le_mul_of_nonneg_left hb (by positivity)
      _ = c := by rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

lemma syndetic_of_all_means (f : G →ᵇ ℝ) (c : ℝ)
    (hf : ∀ M : Amenable.Mean G, c < M.map f) :
    ∃ S : Finset G, ∀ v : G, ∃ s ∈ S, c < f (v+s) := by
  classical
  by_contra hn
  push Not at hn
  choose b hb using (fun i : Finset G × ℕ => hn (cubeSupport i.1.toList i.2))
  have hle : meanAt b f ≤ c := by
    apply le_of_tendsto (tendsto_approx b f)
    apply Filter.Eventually.of_forall
    intro i
    exact cube_le_of_support _ _ _ _ _ (hb i)
  exact (not_lt_of_ge hle) (hf (toMean b))
end EuclideanFiveColor.MovingMean
end

section
open MeasureTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace
namespace EuclideanFiveColor.BoundedMeasurable

section
variable {G X : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G] [MeasurableSpace X]
variable (μ : Measure X) [IsProbabilityMeasure μ]
namespace Family
private def energy (F : Family G X) : G →ᵇ ℝ := Amenable.Mean.squareNorm (toL2 μ F)
omit [AddCommGroup G] in
@[simp] lemma energy_apply (F : Family G X) (g : G) : energy μ F g = ‖l2 μ (F g)‖^2 :=
  Amenable.Mean.squareNorm_apply _ _
lemma energy_mean_eq_of_meanNorm_zero (M : Amenable.Mean G) (F H : Family G X)
    (he : meanNorm μ M (F-H) = 0) : M.map (energy μ F) = M.map (energy μ H) := by
  have hb : |M.map (energy μ F - energy μ H)| ≤
      M.map (((bound F : ℝ)+(bound H : ℝ)) • Amenable.Mean.normFn (toL2 μ (F-H))) := by
    apply M.abs_le
    intro g
    simp only [BoundedContinuousFunction.sub_apply, energy_apply,
      BoundedContinuousFunction.smul_apply, Amenable.Mean.normFn_apply, toL2_apply,
      sub_apply, smul_eq_mul]
    rw [map_sub]
    have hn := abs_norm_sub_norm_le (l2 μ (F g)) (l2 μ (H g))
    have hF := l2_norm_le μ (F g) (F.norm_le_bound g)
    have hH := l2_norm_le μ (H g) (H.norm_le_bound g)
    calc
      _ = |‖l2 μ (F g)‖-‖l2 μ (H g)‖| * (‖l2 μ (F g)‖+‖l2 μ (H g)‖) := by
        have heq : ‖l2 μ (F g)‖^2 - ‖l2 μ (H g)‖^2 =
            (‖l2 μ (F g)‖-‖l2 μ (H g)‖) * (‖l2 μ (F g)‖+‖l2 μ (H g)‖) := by ring
        rw [heq, abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
      _ ≤ ‖l2 μ (F g)-l2 μ (H g)‖ * ((bound F : ℝ)+bound H) :=
        mul_le_mul hn (add_le_add hF hH) (add_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
      _ = _ := mul_comm _ _
  rw [map_sub, map_smul] at hb
  change |M.map (energy μ F) - M.map (energy μ H)| ≤ _ * meanNorm μ M (F-H) at hb
  rw [he, mul_zero] at hb
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hb (abs_nonneg _)))
lemma avg_const (M : Amenable.Mean G) (f : Func X) :
    avg μ M (const (G := G) f) = l2 μ f := by
  apply ext_inner_right ℝ
  intro v
  rw [avg_pair]
  have he : Amenable.Mean.pairing (toL2 μ (const (G := G) f)) v =
      BoundedContinuousFunction.const G (inner ℝ (l2 μ f) v) := rfl
  rw [he, M.map_const]
end Family

private def normSquare (f : Func X) : Func X := f * bmConj f
@[simp] lemma normSquare_apply (f : Func X) (x : X) : normSquare f x = (‖f x‖^2 : ℝ) := by
  change f x * star (f x) = _
  rw [← starRingEnd_apply, Complex.mul_conj, Complex.normSq_eq_norm_sq]
lemma integral_normSquare (f : Func X) : ∫ x, normSquare f x ∂μ = (‖l2 μ f‖^2 : ℝ) := by
  simp only [normSquare_apply, norm_l2_sq, integral_complex_ofReal]
lemma inner_normSquare (f h : Func X) :
    inner ℝ (l2 μ (normSquare f)) (l2 μ (normSquare h)) = ‖l2 μ (f*h)‖^2 := by
  rw [inner_l2, norm_l2_sq]
  apply integral_congr_ae
  exact .of_forall fun x => by
    simp only [normSquare_apply, Complex.inner, Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re,
      mul_apply, norm_mul]
    ring

variable [AddAction G X] [MeasurableConstVAdd G X] [ErgodicVAdd G X μ]
lemma avg_orbit_const (M : Amenable.Mean G) (φ : G →+ G) (hs : Function.Surjective φ) (f : Func X) :
    Family.avg μ M (Family.orbit φ f) = l2 μ (algebraMap ℂ (Func X) (∫ x, f x ∂μ)) := by
  let c : Func X := algebraMap ℂ (Func X) (∫ x, f x ∂μ)
  have hc : ∫ x, l2 μ (f-c) x ∂μ = 0 := by
    rw [integral_l2]
    change ∫ x, f x-c x ∂μ = 0
    rw [integral_sub (integrable μ f) (integrable μ c)]
    change (∫ x, f x ∂μ) - (∫ _x : X, (∫ x, f x ∂μ) ∂μ) = 0
    simp
  have hv := Amenable.Koopman.vector_orbit_hom_zero μ M φ hs (l2 μ (f-c)) hc
  have he : Family.avg μ M (Family.orbit φ (f-c)) =
      M.vector (Amenable.Mean.orbit (fun g => Amenable.Koopman.action μ (φ g)) (l2 μ (f-c))) := by
    congr 1
  rw [← he] at hv
  have ho : Family.orbit φ (f-c) = Family.orbit φ f - Family.const c := by
    ext g x
    rfl
  rw [ho, (Family.avg μ M).map_sub, Family.avg_const] at hv
  exact sub_eq_zero.mp hv

lemma pair_energy_mean (M : Amenable.Mean G) (φ : G →+ G) (hs : Function.Surjective φ) (f h : Func X) :
    M.map (Family.energy μ (Family.const f * Family.orbit φ h)) = ‖l2 μ f‖^2 * ‖l2 μ h‖^2 := by
  have he : Family.energy μ (Family.const f * Family.orbit φ h) =
      Amenable.Mean.pairing (Family.toL2 μ (Family.orbit φ (normSquare h))) (l2 μ (normSquare f)) := by
    ext g
    rw [Family.energy_apply, Amenable.Mean.pairing_apply, Family.toL2_apply]
    change ‖l2 μ (f*act (φ g) h)‖^2 = inner ℝ (l2 μ (act (φ g) (normSquare h))) (l2 μ (normSquare f))
    rw [real_inner_comm]
    exact (inner_normSquare μ f (act (φ g) h)).symm
  rw [he, ← Family.avg_pair, avg_orbit_const μ M φ hs]
  rw [integral_normSquare]
  rw [inner_l2]
  calc
    _ = ∫ x, ‖l2 μ h‖^2 * ‖f x‖^2 ∂μ := by
      apply integral_congr_ae
      exact .of_forall fun x => by
        change inner ℝ ((‖l2 μ h‖^2 : ℝ) : ℂ) (normSquare f x) = _
        rw [normSquare_apply]
        simp only [Complex.inner, Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re]
        ring
    _ = _ := by rw [integral_const_mul, ← norm_l2_sq]; ring
end

variable {G X : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace X] [AddAction G X] [MeasurableConstVAdd G X]
  (μ : Measure X) [IsProbabilityMeasure μ] [VAddInvariantMeasure G X μ]
lemma energy_two_orbits (φ θ : G →+ G) (f h : Func X) :
    Family.energy μ (Family.orbit φ f * Family.orbit θ h) =
      Family.energy μ (Family.const f * Family.orbit (θ-φ) h) := by
  ext g
  rw [Family.energy_apply, Family.energy_apply]
  have he : act (φ g) f * act (θ g) h = act (φ g) (f * act ((θ-φ) g) h) := by
    ext x
    simp only [mul_apply, act_apply, AddMonoidHom.sub_apply, ← add_vadd]
    congr 2
    abel_nf
  change ‖l2 μ (act (φ g) f * act (θ g) h)‖^2 = _
  rw [he, l2_act]
  simp
omit [VAddInvariantMeasure G X μ]
variable [ErgodicVAdd G X μ]
lemma two_orbit_energy_mean (M : Amenable.Mean G) (φ θ : G →+ G)
    (hs : Function.Surjective (θ-φ)) (f h : Func X) :
    M.map (Family.energy μ (Family.orbit φ f * Family.orbit θ h)) = ‖l2 μ f‖^2 * ‖l2 μ h‖^2 := by
  rw [energy_two_orbits]
  exact pair_energy_mean μ M (θ-φ) hs f h
end EuclideanFiveColor.BoundedMeasurable
end

section
open MeasureTheory Filter
namespace EuclideanFiveColor.BoundedMeasurable
variable {G X Y : Type*} [AddCommGroup G] [MeasurableSpace X] [MeasurableSpace Y]
  [AddAction G X] [AddAction G Y] [MeasurableConstVAdd G X] [MeasurableConstVAdd G Y]
variable (μ : Measure X) [IsProbabilityMeasure μ] [ErgodicVAdd G X μ]
  (q : X → Y) (hq : Measurable q)
  (hqcov : ∀ g : G, (fun x => q (g +ᵥ x)) =ᵐ[μ] (fun x => g +ᵥ q x))
omit [IsProbabilityMeasure μ] in
include hq hqcov in
lemma factor_ergodic : ErgodicVAdd G Y (μ.map q) := by
  have hp (g : G) : MeasurePreserving (fun y : Y => g +ᵥ y) (μ.map q) (μ.map q) := by
    refine ⟨measurable_const_vadd _, ?_⟩
    rw [Measure.map_map (measurable_const_vadd _) hq]
    calc
      _ = μ.map (q ∘ (fun x => g +ᵥ x)) := Measure.map_congr (hqcov g).symm
      _ = _ := by rw [← Measure.map_map hq (measurable_const_vadd _), (measurePreserving_vadd g μ).map_eq]
  have : VAddInvariantMeasure G Y (μ.map q) := ⟨fun g s hs => (hp g).measure_preimage hs.nullMeasurableSet⟩
  constructor
  intro s hs hinv
  have hc : Filter.EventuallyConst (q ⁻¹' s) (ae μ) := by
    apply ErgodicVAdd.aeconst_of_forall_preimage_vadd_ae_eq (G := G) (hs.preimage hq)
    intro g
    filter_upwards [ae_of_ae_map hq.aemeasurable (hinv g), hqcov g] with x hx he
    change (q (g +ᵥ x) ∈ s) = (q x ∈ s)
    rw [he]
    exact hx
  rw [Filter.eventuallyConst_set] at hc ⊢
  rcases hc with hc | hc
  · exact Or.inl ((ae_map_iff hq.aemeasurable hs).mpr hc)
  · exact Or.inr ((ae_map_iff hq.aemeasurable hs.compl).mpr hc)
end EuclideanFiveColor.BoundedMeasurable

open MeasureTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace
namespace EuclideanFiveColor.BoundedMeasurable
variable {G X Y : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace X] [Nonempty X]
  [StandardBorelSpace Y] [Nonempty Y]
  [AddAction G X] [AddAction G Y] [MeasurableConstVAdd G X] [MeasurableConstVAdd G Y]
  (μ : Measure X) [IsProbabilityMeasure μ] [ErgodicVAdd G X μ]
  (q : X → Y) (hq : Measurable q)
  (hqcov : ∀ g : G, (fun x => q (g +ᵥ x)) =ᵐ[μ] (fun x => g +ᵥ q x))
variable [IsProbabilityMeasure (μ.map q)]
variable [ErgodicVAdd G (X×X) (RelativeProduct.law μ q hq)]
include hq hqcov in
lemma conditional_pair_energy (M : Amenable.Mean G) (φ : G →+ G)
    (hs : Function.Surjective φ) (f h : Func X) :
    M.map (Family.energy (μ.map q) (Family.conditional μ q (Family.const f * Family.orbit φ h))) =
      ‖l2 (μ.map q) (conditional μ q f)‖^2 * ‖l2 (μ.map q) (conditional μ q h)‖^2 := by
  have : ErgodicVAdd G Y (μ.map q) := factor_ergodic μ q hq hqcov
  have hp := pairVanishing_of_ergodic μ q hq M
  have he := covariance_mean_zero μ q hq hqcov M hp φ hs f h
  have hv := Family.energy_mean_eq_of_meanNorm_zero (μ.map q) M _ _ he
  rw [hv]
  exact pair_energy_mean (μ.map q) M φ hs (conditional μ q f) (conditional μ q h)
include hq hqcov in
lemma conditional_integer_pair_energy
    (hdiv : ∀ n : ℤ, n ≠ 0 → Function.Surjective (scaleHom (G := G) n))
    (M : Amenable.Mean G) {n m : ℤ} (hnm : n ≠ m) (f h : Func X) :
    M.map (Family.energy (μ.map q) (Family.conditional μ q
      (Family.orbit (scaleHom n) f * Family.orbit (scaleHom m) h))) =
      ‖l2 (μ.map q) (conditional μ q f)‖^2 * ‖l2 (μ.map q) (conditional μ q h)‖^2 := by
  have : ErgodicVAdd G Y (μ.map q) := factor_ergodic μ q hq hqcov
  have hp := pairVanishing_of_ergodic μ q hq M
  have hn : Set.InjOn (![n,m]) (Finset.univ : Finset (Fin 2)) := by
    intro i _ j _ he
    fin_cases i <;> fin_cases j <;> simp_all
  have he := conditional_integer_multiple_mean_zero μ q hq hqcov hdiv M hp
    Finset.univ ![n,m] ![f,h] hn
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at he
  rw [Family.energy_mean_eq_of_meanNorm_zero (μ.map q) M _ _ he]
  apply two_orbit_energy_mean
  rw [← scaleHom_sub]
  exact hdiv _ (sub_ne_zero.mpr hnm.symm)
include hq hqcov in
lemma conditional_integer_triple_energy
    (hdiv : ∀ n : ℤ, n ≠ 0 → Function.Surjective (scaleHom (G := G) n))
    (M : Amenable.Mean G) (f h k : Func X) :
    M.map (Family.energy (μ.map q) (Family.conditional μ q
      (Family.orbit (scaleHom 0) f * Family.orbit (scaleHom 1) h * Family.orbit (scaleHom 2) k))) =
    M.map (Family.energy (μ.map q)
      (Family.orbit (scaleHom 0) (conditional μ q f) * Family.orbit (scaleHom 1) (conditional μ q h) *
        Family.orbit (scaleHom 2) (conditional μ q k))) := by
  have hp := pairVanishing_of_ergodic μ q hq M
  have hn : Set.InjOn (![(0:ℤ),1,2]) (Finset.univ : Finset (Fin 3)) := by
    intro i _ j _ he
    fin_cases i <;> fin_cases j <;> simp_all
  have he := conditional_integer_multiple_mean_zero μ q hq hqcov hdiv M hp
    Finset.univ ![(0:ℤ),1,2] ![f,h,k] hn
  simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two] at he
  exact Family.energy_mean_eq_of_meanNorm_zero (μ.map q) M _ _ he
end EuclideanFiveColor.BoundedMeasurable
end

open MeasureTheory ProbabilityTheory Filter EuclideanFiveColor
open scoped ENNReal NNReal ComplexConjugate
namespace PlaneFiveColor.Spectral
open EuclideanFiveColor.BoundedMeasurable
variable [Carrier]

private def char (z : E) : Func D := ⟨fun d => (eval z d : ℂ), measurable_eval_coe z,
  1, fun d => by simp only [Circle.norm_coe, NNReal.coe_one, le_refl]⟩
@[simp] lemma char_apply (z : E) (d : D) : char z d = (eval z d : ℂ) := rfl
@[simp] lemma norm_char (z : E) (d : D) : ‖char z d‖ = 1 := Circle.norm_coe _
@[simp] lemma char_zero : char 0 = 1 := by ext d; simp
lemma char_add (z w : E) : char (z+w) = char z * char w := by
  ext d
  exact congrArg (fun a : Circle => (a : ℂ)) (eval_add z w d)
lemma char_neg (z : E) : char (-z) = bmConj (char z) := by
  ext d
  simp only [char_apply, eval_neg, conj_apply]
  exact Circle.coe_inv_eq_conj _
lemma char_act (g : Rot) (z : E) : act g (char z) = char (kCoeff (rotMul g)*z) := rfl

variable {Y : Type*} [MeasurableSpace Y]
variable (μ : Measure D) [IsProbabilityMeasure μ] (q : D → Y)
private def projectedMass (z : E) : ℝ := ‖l2 (μ.map q) (conditional μ q (char z))‖^2
lemma projectedMass_nonneg (z : E) : 0 ≤ projectedMass μ q z := sq_nonneg _
lemma projected_char_bound (z : E) (y : Y) : ‖conditional μ q (char z) y‖ ≤ 1 :=
  expect_bound _ _ (fun d => le_of_eq (norm_char _ d)) y
variable (hq : Measurable q)
include hq in
lemma projectedMass_le_one (z : E) : projectedMass μ q z ≤ 1 := by
  let : IsProbabilityMeasure (μ.map q) :=
    (Measure.isProbabilityMeasure_map_iff hq.aemeasurable).mpr inferInstance
  have hn := l2_norm_le (μ.map q) (conditional μ q (char z)) (projected_char_bound μ q z)
  unfold projectedMass
  nlinarith [norm_nonneg (l2 (μ.map q) (conditional μ q (char z)))]
include hq in
lemma projectedMass_zero : projectedMass μ q 0 = 1 := by
  let : IsProbabilityMeasure (μ.map q) :=
    (Measure.isProbabilityMeasure_map_iff hq.aemeasurable).mpr inferInstance
  have he : conditional μ q (char 0) = 1 := by
    ext y
    change (∫ d, char 0 d ∂condDistrib id q μ y) = 1
    simp
  unfold projectedMass
  rw [he, norm_l2_sq]
  simp
include hq in
lemma differenceFourier_projectedMass (z : E) :
    ∫ d, (eval z d : ℂ) ∂DifferenceFourier.differenceLaw (μ.map q) (condDistrib id q μ) =
      (projectedMass μ q z : ℂ) := by
  let : IsProbabilityMeasure (μ.map q) :=
    (Measure.isProbabilityMeasure_map_iff hq.aemeasurable).mpr inferInstance
  rw [DifferenceFourier.difference_coefficient (eval z) (measurable_eval_coe z)]
  congr 1
  exact (norm_l2_sq (μ.map q) (conditional μ q (char z))).symm

variable [MulAction K Y] [MeasurableConstSMul K Y] [SMulInvariantMeasure K D μ]
variable (hqcov : ∀ k : K, ∀ᵐ d ∂μ, q (k • d) = k • q d)
include hq hqcov in
lemma projectedMass_rotation (u : K) (z : E) :
    projectedMass μ q (kCoeff u*z) = projectedMass μ q z := by
  let : IsProbabilityMeasure (μ.map q) :=
    (Measure.isProbabilityMeasure_map_iff hq.aemeasurable).mpr inferInstance
  unfold projectedMass
  rw [← norm_project_l2 μ q hq, ← norm_project_l2 μ q hq]
  have hchar : char (kCoeff u*z) = act (mulRot u) (char z) := rfl
  rw [hchar]
  have he := (l2_eq_iff μ _ _).mpr (project_act μ q hq (fun g : Rot => hqcov (rotMul g)) (mulRot u) (char z))
  rw [he, l2_act]
  simp
include hq hqcov in
lemma projectedMass_radial {z w : E} (hn : ‖(z : ℂ)‖ = ‖(w : ℂ)‖) :
    projectedMass μ q z = projectedMass μ q w := by
  by_cases hw : w = 0
  · have hz : z = 0 := by
      apply Subtype.ext
      apply norm_eq_zero.mp
      simpa [hw] using hn
    rw [hz, hw]
  have hwc : (w : ℂ) ≠ 0 := fun h => hw (Subtype.ext h)
  let c : Circle := ⟨(z : ℂ)/(w : ℂ), mem_sphere_zero_iff_norm.mpr (by
    rw [norm_div, hn, div_self (norm_ne_zero_iff.mpr hwc)])⟩
  let u : K := ⟨c, div_mem z.property w.property⟩
  have he : kCoeff u * w = z := by
    apply Subtype.ext
    exact div_mul_cancel₀ _ hwc
  rw [← he]
  exact projectedMass_rotation μ q hq hqcov u w
end PlaneFiveColor.Spectral

end

end ParishFactor
end

-- OAI.Analysis.PlaneSpectrum.NumberFields
section
namespace ParishFactor

noncomputable section
open Polynomial
namespace EuclideanFiveColor.AlgebraicCayley
variable {L : Type*} [Field L] [Algebra ℚ L]

lemma minpoly_reverse_eval_ne_zero (b : L) (hb : IsAlgebraic ℚ b) (t : ℚ)
    (ht : 1-b*algebraMap ℚ L t ≠ 0) : (minpoly ℚ b).reverse.eval t ≠ 0 := by
  intro hz
  by_cases ht0 : t = 0
  · subst t
    rw [← coeff_zero_eq_eval_zero, coeff_zero_reverse, (minpoly.monic hb.isIntegral).leadingCoeff] at hz
    exact one_ne_zero hz
  let : Invertible (t⁻¹) := invertibleOfNonzero (inv_ne_zero ht0)
  have hp : (minpoly ℚ b).IsRoot t⁻¹ := by
    have he := (eval₂_reverse_eq_zero_iff (RingHom.id ℚ) t⁻¹ (minpoly ℚ b))
    simp only [invOf_eq_inv, inv_inv, eval₂_id] at he
    exact he.mp hz
  have he := minpoly.root hb.isIntegral hp
  apply ht
  rw [← he, ← map_mul, inv_mul_cancel₀ ht0, map_one, sub_self]

lemma reciprocal_denominator (b : L) (hb : IsAlgebraic ℚ b) :
    ∃ (P : ℚ[X]) (R : L[X]), P.coeff 0 = 1 ∧
      (1-C b*X)*R = P.map (algebraMap ℚ L) ∧
      ∀ t : ℚ, 1-b*algebraMap ℚ L t ≠ 0 → P.eval t ≠ 0 := by
  by_cases hb0 : b = 0
  · subst b
    exact ⟨1,1,by simp,by simp,by simp⟩
  let p := minpoly ℚ b
  have hm : p.Monic := minpoly.monic hb.isIntegral
  let : Invertible b := invertibleOfNonzero hb0
  have hz : (p.reverse.map (algebraMap ℚ L)).IsRoot b⁻¹ := by
    rw [IsRoot, eval_map]
    have h := (eval₂_reverse_eq_zero_iff (algebraMap ℚ L) b p).mpr (minpoly.aeval ℚ b)
    simpa only [invOf_eq_inv] using h
  obtain ⟨R,hR⟩ := (dvd_iff_isRoot.mpr hz)
  refine ⟨p.reverse,C (-b⁻¹)*R,?_,?_,minpoly_reverse_eval_ne_zero b hb⟩
  · rw [coeff_zero_reverse, hm.leadingCoeff]
  · calc
      _ = (X-C b⁻¹)*R := by
        have he : (1-C b*X)*C (-b⁻¹) = X-C b⁻¹ := by
          have hc : C b*C b⁻¹ = (1 : L[X]) := by rw [← map_mul, mul_inv_cancel₀ hb0, map_one]
          rw [map_neg]
          calc
            _ = (C b*C b⁻¹)*X-C b⁻¹ := by ring
            _ = _ := by rw [hc, one_mul]
        rw [← mul_assoc, he]
      _ = _ := hR.symm

private def polyLinear (ℓ : L →ₗ[ℚ] ℚ) (p : L[X]) : ℚ[X] :=
  Polynomial.ofFinsupp (AddMonoidAlgebra.ofCoeff (p.toFinsupp.coeff.mapRange ℓ (map_zero ℓ)))
@[simp] lemma coeff_polyLinear (ℓ : L →ₗ[ℚ] ℚ) (p : L[X]) (n : ℕ) :
    (polyLinear ℓ p).coeff n = ℓ (p.coeff n) := rfl
lemma polyLinear_add (ℓ : L →ₗ[ℚ] ℚ) (p q : L[X]) :
    polyLinear ℓ (p+q) = polyLinear ℓ p + polyLinear ℓ q := by
  ext n
  simp only [coeff_polyLinear, coeff_add, map_add]
lemma polyLinear_monomial (ℓ : L →ₗ[ℚ] ℚ) (n : ℕ) (a : L) :
    polyLinear ℓ (monomial n a) = monomial n (ℓ a) := by
  ext k
  simp only [coeff_polyLinear, coeff_monomial]
  split_ifs <;> simp
lemma eval_polyLinear (ℓ : L →ₗ[ℚ] ℚ) (p : L[X]) (t : ℚ) :
    (polyLinear ℓ p).eval t = ℓ (p.eval (algebraMap ℚ L t)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [polyLinear_add, eval_add, hp, hq, map_add]
  | monomial n a =>
    rw [polyLinear_monomial, eval_monomial, eval_monomial]
    have he : a*(algebraMap ℚ L t)^n = (t^n) • a := by
      rw [Algebra.smul_def, map_pow, mul_comm]
    rw [he, map_smul]
    exact mul_comm _ _

lemma polyLinear_eq_zero_iff (ℓ : L →ₗ[ℚ] ℚ) (p : L[X]) :
    polyLinear ℓ p = 0 ↔ ∀ t : ℚ, ℓ (p.eval (algebraMap ℚ L t)) = 0 := by
  simp_rw [← eval_polyLinear]
  exact ⟨fun he _ => by rw [he, eval_zero], fun h => Polynomial.funext fun t => by simpa using h t⟩

lemma cayley_annihilation (b : L) (hb : IsAlgebraic ℚ b) (ℓ : L →ₗ[ℚ] ℚ)
    (hd : ∀ t : ℚ, 1-b*(algebraMap ℚ L t) ≠ 0)
    (h : ∀ t : ℚ, ℓ ((1+b*(algebraMap ℚ L t))/(1-b*(algebraMap ℚ L t))) = 0) :
    ℓ 1 = 0 ∧ ℓ b = 0 ∧ ℓ (b^2) = 0 := by
  obtain ⟨P,R,hP,hR,_hPreg⟩ := reciprocal_denominator b hb
  have hR' : R-(C b*R)*X = P.map (algebraMap ℚ L) := by
    convert hR using 1
    ring
  let T := R+(C b*R)*X
  have hT : polyLinear ℓ T = 0 := by
    apply (polyLinear_eq_zero_iff ℓ T).mpr
    intro t
    have hRt := congrArg (Polynomial.eval (algebraMap ℚ L t)) hR
    simp only [eval_mul, eval_sub, eval_one, eval_C, eval_X, eval_map, eval₂_at_apply] at hRt
    have he : T.eval (algebraMap ℚ L t) =
        (P.eval t) • ((1+b*(algebraMap ℚ L t))/(1-b*(algebraMap ℚ L t))) := by
      dsimp only [T]
      simp only [eval_add, eval_mul, eval_C, eval_X, Algebra.smul_def]
      rw [← hRt]
      rw [← mul_div_assoc, eq_div_iff (hd t)]
      ring
    rw [he, map_smul, h t, smul_zero]
  have h0 : R.coeff 0 = 1 := by
    have he := congrArg (fun p : L[X] => p.coeff 0) hR'
    simpa only [coeff_sub, coeff_mul_X_zero, sub_zero, coeff_map, hP, map_one] using he
  have h1 : R.coeff 1-b = algebraMap ℚ L (P.coeff 1) := by
    have he := congrArg (fun p : L[X] => p.coeff 1) hR'
    simpa only [coeff_sub, coeff_mul_X, coeff_C_mul, h0, mul_one, coeff_map] using he
  have h2 : R.coeff 2-b*R.coeff 1 = algebraMap ℚ L (P.coeff 2) := by
    have he := congrArg (fun p : L[X] => p.coeff 2) hR'
    simpa only [coeff_sub, coeff_mul_X, coeff_C_mul, coeff_map] using he
  have ht0 : ℓ 1 = 0 := by
    have he := congrArg (fun p : ℚ[X] => p.coeff 0) hT
    simpa only [coeff_polyLinear, T, coeff_add, coeff_mul_X_zero, add_zero, h0, coeff_zero] using he
  have ht1 : ℓ (R.coeff 1) + ℓ b = 0 := by
    have he := congrArg (fun p : ℚ[X] => p.coeff 1) hT
    simpa only [coeff_polyLinear, T, coeff_add, coeff_mul_X, coeff_C_mul, h0, mul_one,
      map_add, coeff_zero] using he
  have ht2 : ℓ (R.coeff 2) + ℓ (b*R.coeff 1) = 0 := by
    have he := congrArg (fun p : ℚ[X] => p.coeff 2) hT
    simpa only [coeff_polyLinear, T, coeff_add, coeff_mul_X, coeff_C_mul,
      map_add, coeff_zero] using he
  have hlQ (c : ℚ) : ℓ (algebraMap ℚ L c) = 0 := by
    have he : algebraMap ℚ L c = c • (1:L) := by rw [Algebra.smul_def, mul_one]
    rw [he, map_smul, ht0, smul_zero]
  have hh1 := congrArg ℓ h1
  rw [map_sub, hlQ] at hh1
  have hb0 : ℓ b = 0 := by linarith
  have hh2 := congrArg ℓ h2
  rw [map_sub, hlQ] at hh2
  have hbR : ℓ (b*R.coeff 1) = 0 := by linarith
  have hR1 : R.coeff 1 = algebraMap ℚ L (P.coeff 1)+b := sub_eq_iff_eq_add.mp h1
  rw [hR1, mul_add, map_add] at hbR
  have he : b*algebraMap ℚ L (P.coeff 1) = (P.coeff 1) • b := by
    rw [Algebra.smul_def, mul_comm]
  rw [he, map_smul, hb0, smul_zero, zero_add, ← sq] at hbR
  exact ⟨ht0,hb0,hbR⟩

end EuclideanFiveColor.AlgebraicCayley

end

noncomputable section
open Polynomial
namespace EuclideanFiveColor.AlgebraicCayley
variable {L : Type*} [Field L] [Algebra ℚ L]

lemma linearFraction_polynomials (a b c d : L) (hc : c ≠ 0)
    (hb : IsAlgebraic ℚ (-d/c)) (ℓ : L →ₗ[ℚ] ℚ)
    (hd : ∀ t : ℚ, c+d*algebraMap ℚ L t ≠ 0) :
    ∃ P Q : ℚ[X], ∀ t : ℚ, Q.eval t ≠ 0 ∧
      P.eval t = Q.eval t * ℓ ((a+b*algebraMap ℚ L t)/(c+d*algebraMap ℚ L t)) := by
  obtain ⟨Q,R,hQ,hR,hQreg⟩ := reciprocal_denominator (-d/c) hb
  clear hQ
  have hdn (t : ℚ) : 1-(-d/c)*algebraMap ℚ L t ≠ 0 := by
    intro hh
    apply hd t
    have he : c+d*algebraMap ℚ L t = c*(1-(-d/c)*algebraMap ℚ L t) := by
      field_simp
      ring
    rw [he, hh, mul_zero]
  let U : L[X] := (C (a/c)+C (b/c)*X)*R
  refine ⟨polyLinear ℓ U,Q,fun t => ⟨hQreg t (hdn t),?_⟩⟩
  rw [eval_polyLinear]
  have hRt := congrArg (Polynomial.eval (algebraMap ℚ L t)) hR
  simp only [eval_mul, eval_sub, eval_one, eval_C, eval_X, eval_map, eval₂_at_apply] at hRt
  have he : U.eval (algebraMap ℚ L t) =
      (Q.eval t) • ((a+b*algebraMap ℚ L t)/(c+d*algebraMap ℚ L t)) := by
    dsimp only [U]
    simp only [eval_mul, eval_add, eval_C, eval_X, Algebra.smul_def]
    rw [← hRt, ← mul_div_assoc, eq_div_iff (hd t)]
    field_simp
    ring
  rw [he, map_smul, smul_eq_mul]

lemma rational_functions_avoid {ι : Type*} (s : Finset ι) (f : ι → ℚ → ℚ)
    (hpoly : ∀ i ∈ s, ∃ P Q : ℚ[X], ∀ t, Q.eval t ≠ 0 ∧ P.eval t = Q.eval t*f i t)
    (hn : ∀ i ∈ s, ∃ t, f i t ≠ 0) :
    ∃ t, ∀ i ∈ s, f i t ≠ 0 := by
  classical
  choose P Q hQ using fun i : s => hpoly i i.property
  have hP (i : s) : P i ≠ 0 := by
    obtain ⟨t,ht⟩ := hn i i.property
    intro he
    have hh := (hQ i t).2
    rw [he, eval_zero] at hh
    exact mul_ne_zero (hQ i t).1 ht hh.symm
  have hz : (∏ i : s, P i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun _ _ => hP _)
  obtain ⟨t,ht⟩ : ∃ t : ℚ, (∏ i : s, P i).eval t ≠ 0 := by
    by_contra! hn
    exact hz (Polynomial.funext fun t => by simpa using hn t)
  refine ⟨t,fun i hi hh => ?_⟩
  have hpt : (P ⟨i,hi⟩).eval t ≠ 0 := by
    rw [eval_prod] at ht
    exact Finset.prod_ne_zero_iff.mp ht _ (Finset.mem_univ _)
  apply hpt
  rw [(hQ ⟨i,hi⟩ t).2, hh, mul_zero]

lemma finite_hyperplanes_avoid {T : Type*} [Nonempty T]
    (f : T → L) (line : T → T → ℚ → T)
    (hzero : ∀ a b, line a b 0 = a) (hone : ∀ a b, line a b 1 = b)
    (hline : ∀ a b (ℓ : L →ₗ[ℚ] ℚ), ∃ P Q : ℚ[X], ∀ t,
      Q.eval t ≠ 0 ∧ P.eval t = Q.eval t * ℓ (f (line a b t)))
    (s : Finset (L →ₗ[ℚ] ℚ)) (hs : ∀ ℓ ∈ s, ∃ t, ℓ (f t) ≠ 0) :
    ∃ t, ∀ ℓ ∈ s, ℓ (f t) ≠ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨Classical.arbitrary T, by simp⟩
  | @insert ℓ s hℓ ih =>
    obtain ⟨a,ha⟩ := ih (fun ψ hψ => hs ψ (Finset.mem_insert_of_mem hψ))
    obtain ⟨b,hb⟩ := hs ℓ (Finset.mem_insert_self _ _)
    obtain ⟨t,ht⟩ := rational_functions_avoid (insert ℓ s)
      (fun ψ t => ψ (f (line a b t))) (fun ψ _ => hline a b ψ) (by
        intro ψ hψ
        rcases Finset.mem_insert.mp hψ with rfl | hψ
        · exact ⟨1,by simpa only [hone] using hb⟩
        · exact ⟨0,by simpa only [hzero] using ha ψ hψ⟩)
    exact ⟨line a b t,ht⟩
end EuclideanFiveColor.AlgebraicCayley
end

noncomputable section
open Polynomial
open scoped ComplexConjugate
namespace EuclideanFiveColor.AlgebraicCayley
variable (N : IntermediateField ℚ ℂ)
private def realSlice : Subfield ℝ := N.toSubfield.comap Complex.ofRealHom
private def asN : realSlice N →+* N where
  toFun a := ⟨(a : ℝ),a.property⟩
  map_zero' := by ext; simp
  map_one' := by ext; simp
  map_add' _ _ := by ext; simp
  map_mul' _ _ := by ext; simp
@[simp] lemma coe_asN (a : realSlice N) : ((asN N a : N) : ℂ) = (a : ℝ) := rfl
variable (hi : Complex.I ∈ N)
private def iN : N := ⟨Complex.I, hi⟩
@[simp] lemma coe_iN : ((iN N hi : N) : ℂ) = Complex.I := rfl
lemma iN_sq : iN N hi ^2 = -1 := by ext; exact Complex.I_sq
lemma cayley_den_ne (a : realSlice N) : 1-iN N hi*asN N a ≠ 0 := by
  intro h
  have hh := congrArg (fun z : N => (z : ℂ).re) h
  simp [iN, asN] at hh

private def realCayley (a : realSlice N) : N :=
  (1+iN N hi*asN N a)/(1-iN N hi*asN N a)
lemma cayley_real_norm (a : realSlice N) : ‖((realCayley N hi a : N) : ℂ)‖ = 1 := by
  change ‖(1+Complex.I*(a:ℝ))/(1-Complex.I*(a:ℝ))‖ = 1
  have hn : ‖(1+Complex.I*(a:ℝ))‖ = ‖(1-Complex.I*(a:ℝ))‖ := by
    have he : conj (1+Complex.I*(a:ℝ)) = 1-Complex.I*(a:ℝ) := by simp; ring
    rw [← he, Complex.norm_conj]
  rw [norm_div, hn, div_self]
  apply norm_ne_zero_iff.mpr
  intro hz
  have he := congrArg Complex.re hz
  simp at he

variable [FiniteDimensional ℚ N]
lemma cayley_functional_escape
    (hre : ∀ z : N, ((z : ℂ).re : ℂ) ∈ N)
    (him : ∀ z : N, ((z : ℂ).im : ℂ) ∈ N)
    (ℓ : N →ₗ[ℚ] ℚ) (hℓ : ℓ ≠ 0) :
    ∃ a : realSlice N, ℓ (realCayley N hi a) ≠ 0 := by
  by_contra! hh
  have hx (a : realSlice N) : ℓ 1 = 0 ∧ ℓ (iN N hi*asN N a) = 0 ∧
      ℓ ((asN N a)^2) = 0 := by
    have he (t : ℚ) : asN N (a*algebraMap ℚ (realSlice N) t) =
        asN N a*algebraMap ℚ N t := by simp
    have hd (t : ℚ) : 1-(iN N hi*asN N a)*algebraMap ℚ N t ≠ 0 := by
      simpa only [he, mul_assoc] using cayley_den_ne N hi (a*algebraMap ℚ (realSlice N) t)
    have ha (t : ℚ) : ℓ ((1+(iN N hi*asN N a)*algebraMap ℚ N t)/
        (1-(iN N hi*asN N a)*algebraMap ℚ N t)) = 0 := by
      simpa only [realCayley, he, mul_assoc] using hh (a*algebraMap ℚ (realSlice N) t)
    obtain ⟨h1,hia,hsa⟩ := cayley_annihilation (iN N hi*asN N a)
      (Algebra.IsAlgebraic.isAlgebraic _) ℓ hd ha
    rw [mul_pow, iN_sq, neg_one_mul, map_neg, neg_eq_zero] at hsa
    exact ⟨h1,hia,hsa⟩
  have hreal (a : realSlice N) : ℓ (asN N a) = 0 := by
    have h1 := (hx (a+1)).2.2
    have h2 := (hx (a-1)).2.2
    have he : (asN N (a+1))^2-(asN N (a-1))^2 = (4:ℚ) • asN N a := by
      simp only [map_add, map_one, map_sub, Algebra.smul_def, map_ofNat]
      ring
    have hh := congrArg ℓ he
    rw [map_sub, h1,h2,sub_self,map_smul,smul_eq_mul] at hh
    linarith
  apply hℓ
  ext z
  let a : realSlice N := ⟨(z:ℂ).re,hre z⟩
  let b : realSlice N := ⟨(z:ℂ).im,him z⟩
  have he : z = asN N a+iN N hi*asN N b := by
    apply Subtype.ext
    change (z:ℂ) = (z:ℂ).re+Complex.I*(z:ℂ).im
    rw [mul_comm]
    exact (Complex.re_add_im _).symm
  rw [he,map_add,hreal,(hx b).2.1,add_zero]
  rfl

private def realLine (a b : realSlice N) (t : ℚ) : realSlice N :=
  a+algebraMap ℚ (realSlice N) t*(b-a)
omit [FiniteDimensional ℚ N] in
@[simp] lemma realLine_zero (a b : realSlice N) : realLine N a b 0 = a := by simp [realLine]
omit [FiniteDimensional ℚ N] in
@[simp] lemma realLine_one (a b : realSlice N) : realLine N a b 1 = b := by simp [realLine]
lemma cayley_line_polynomials (a b : realSlice N) (ℓ : N →ₗ[ℚ] ℚ) :
    ∃ P Q : ℚ[X], ∀ t, Q.eval t ≠ 0 ∧
      P.eval t = Q.eval t*ℓ (realCayley N hi (realLine N a b t)) := by
  let A := 1+iN N hi*asN N a
  let B := iN N hi*(asN N b-asN N a)
  let C := 1-iN N hi*asN N a
  let D := -iN N hi*(asN N b-asN N a)
  have he (t : ℚ) : asN N (realLine N a b t) =
      asN N a+algebraMap ℚ N t*(asN N b-asN N a) := by simp [realLine]
  have hd (t : ℚ) : C+D*algebraMap ℚ N t = 1-iN N hi*asN N (realLine N a b t) := by
    rw [he]; dsimp [C,D]; ring
  have hn (t : ℚ) : A+B*algebraMap ℚ N t = 1+iN N hi*asN N (realLine N a b t) := by
    rw [he]; dsimp [A,B]; ring
  obtain ⟨P,Q,hPQ⟩ := linearFraction_polynomials A B C D (cayley_den_ne N hi a)
    (Algebra.IsAlgebraic.isAlgebraic _) ℓ (fun t => by rw [hd]; exact cayley_den_ne N hi _)
  refine ⟨P,Q,fun t => ?_⟩
  simpa only [hn,hd,realCayley] using hPQ t

lemma cayley_finite_avoid
    (hre : ∀ z : N, ((z : ℂ).re : ℂ) ∈ N)
    (him : ∀ z : N, ((z : ℂ).im : ℂ) ∈ N)
    (s : Finset (N →ₗ[ℚ] ℚ)) (hs : ∀ ℓ ∈ s, ℓ ≠ 0) :
    ∃ a : realSlice N, ∀ ℓ ∈ s, ℓ (realCayley N hi a) ≠ 0 :=
  finite_hyperplanes_avoid (realCayley N hi) (realLine N)
    (realLine_zero N) (realLine_one N) (cayley_line_polynomials N hi) s
    (fun ℓ hℓ => cayley_functional_escape N hi hre him ℓ (hs ℓ hℓ))
end EuclideanFiveColor.AlgebraicCayley
end

noncomputable section
open Module
namespace EuclideanFiveColor.GeneralPosition
variable {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]

private def General (s : Finset V) : Prop :=
  ∀ t ⊆ s, t.card ≤ finrank ℚ V → LinearIndepOn ℚ id (t : Set V)

omit [FiniteDimensional ℚ V] in

lemma exists_general (A : Set V) (hd : 2 ≤ finrank ℚ V)
    (ha : ∀ P : Finset (Submodule ℚ V), (∀ p ∈ P, p < ⊤) →
      ∃ x ∈ A, ∀ p ∈ P, x ∉ p) (n : ℕ) :
    ∃ s : Finset V, s.card = n ∧ (s : Set V) ⊆ A ∧ General s := by
  classical
  induction n with
  | zero =>
    refine ⟨∅,rfl,by simp,?_⟩
    intro t ht _
    have : t = ∅ := Finset.subset_empty.mp ht
    simp [this, linearIndepOn_empty]
  | succ n ih =>
    obtain ⟨s,hs,hA,hg⟩ := ih
    let B := s.powerset.filter (fun t => t.card < finrank ℚ V)
    let P := B.image (fun t : Finset V => Submodule.span ℚ (t : Set V))
    have hP : ∀ p ∈ P, p < ⊤ := by
      intro p hp
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hp
      have hc : t.card < finrank ℚ V := (Finset.mem_filter.mp ht).2
      apply Submodule.lt_top_of_finrank_lt_finrank
      exact (finrank_span_finset_le_card t).trans_lt hc
    obtain ⟨x,hx,havoid⟩ := ha P hP
    have havo (t : Finset V) (ht : t ⊆ s) (hc : t.card < finrank ℚ V) :
        x ∉ Submodule.span ℚ (t : Set V) := by
      apply havoid _
      exact Finset.mem_image.mpr ⟨t,Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ht,hc⟩,rfl⟩
    have hxs : x ∉ s := by
      intro hh
      exact havo {x} (Finset.singleton_subset_iff.mpr hh) (by simpa only [Finset.card_singleton] using (show 1 < finrank ℚ V by omega))
        (Submodule.subset_span (by simp))
    refine ⟨insert x s,by simp [hxs,hs],?_,?_⟩
    · intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hx
      · exact hA hy
    · intro t ht hc
      by_cases hxt : x ∈ t
      · have hts : t.erase x ⊆ s := by
          intro y hy
          obtain ⟨hyx,hyt⟩ := Finset.mem_erase.mp hy
          exact (Finset.mem_insert.mp (ht hyt)).resolve_left hyx
        have hct : (t.erase x).card < finrank ℚ V := by
          rw [Finset.card_erase_of_mem hxt]
          have hp := Finset.card_pos.mpr ⟨x,hxt⟩
          omega
        have hli := hg (t.erase x) hts hct.le
        have hn := havo (t.erase x) hts hct
        have hh := (linearIndepOn_id_insert (K := ℚ) (by simp : x ∉ (t.erase x : Set V))).mpr ⟨hli,hn⟩
        simpa only [← Finset.coe_insert, Finset.insert_erase hxt] using hh
      · exact hg t (by
          intro y hy
          exact (Finset.mem_insert.mp (ht hy)).resolve_left (fun he => hxt (he ▸ hy))) hc

lemma General.spans {s t : Finset V} (hs : General s) (ht : t ⊆ s)
    (hc : t.card = finrank ℚ V) : Submodule.span ℚ (t : Set V) = ⊤ := by
  have hli := hs t ht hc.le
  have hr : finrank ℚ (Submodule.span ℚ (t : Set V)) = finrank ℚ V :=
    (finrank_span_finset_eq_card hli).trans hc
  exact Submodule.eq_top_of_finrank_eq hr

end EuclideanFiveColor.GeneralPosition
end

noncomputable section
open Module
open scoped ComplexConjugate
namespace EuclideanFiveColor.AlgebraicCayley

private def generatingSet (s : Finset ℂ) : Finset ℂ :=
  {Complex.I} ∪ s.image (fun z => (z.re : ℂ)) ∪ s.image (fun z => (z.im : ℂ))
private def generatedField (s : Finset ℂ) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ (generatingSet s : Set ℂ)
lemma generatedField_I (s : Finset ℂ) : Complex.I ∈ generatedField s := by
  apply IntermediateField.subset_adjoin
  simp [generatingSet]
lemma generatedField_real (s : Finset ℂ) (z : ℂ) (hz : z ∈ s) :
    (z.re : ℂ) ∈ generatedField s := by
  apply IntermediateField.subset_adjoin
  simp only [generatingSet, Finset.mem_coe, Finset.mem_union]
  exact Or.inl (Or.inr (Finset.mem_image.mpr ⟨z,hz,rfl⟩))
lemma generatedField_imag (s : Finset ℂ) (z : ℂ) (hz : z ∈ s) :
    (z.im : ℂ) ∈ generatedField s := by
  apply IntermediateField.subset_adjoin
  simp only [generatingSet, Finset.mem_coe, Finset.mem_union]
  exact Or.inr (Finset.mem_image.mpr ⟨z,hz,rfl⟩)
lemma generatedField_contains (s : Finset ℂ) (z : ℂ) (hz : z ∈ s) : z ∈ generatedField s := by
  rw [← Complex.re_add_im z]
  exact (generatedField s).add_mem (generatedField_real s z hz)
    ((generatedField s).mul_mem (generatedField_imag s z hz) (generatedField_I s))
lemma generatedField_conj (s : Finset ℂ) {z : ℂ} (hz : z ∈ generatedField s) :
    conj z ∈ generatedField s := by
  induction hz using IntermediateField.adjoin_induction ℚ with
  | mem z hz =>
    rcases Finset.mem_union.mp hz with hz | hz
    · rcases Finset.mem_union.mp hz with hz | hz
      · have : z = Complex.I := Finset.mem_singleton.mp hz
        rw [this,Complex.conj_I]
        exact (generatedField s).neg_mem (generatedField_I s)
      · obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
        simpa using generatedField_real s w hw
    · obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
      simpa using generatedField_imag s w hw
  | algebraMap r => simp
  | add x y hx hy ihx ihy => simpa using (generatedField s).add_mem ihx ihy
  | inv x hx ihx => simpa using (generatedField s).inv_mem ihx
  | mul x y hx hy ihx ihy => simpa using (generatedField s).mul_mem ihx ihy
lemma generatedField_re_closed (s : Finset ℂ) (z : generatedField s) :
    ((z:ℂ).re : ℂ) ∈ generatedField s := by
  rw [Complex.re_eq_add_conj]
  exact (generatedField s).div_mem ((generatedField s).add_mem z.property
    (generatedField_conj s z.property)) (by norm_cast; exact (generatedField s).natCast_mem 2)
lemma generatedField_im_closed (s : Finset ℂ) (z : generatedField s) :
    ((z:ℂ).im : ℂ) ∈ generatedField s := by
  rw [Complex.im_eq_sub_conj]
  exact (generatedField s).div_mem ((generatedField s).sub_mem z.property
    (generatedField_conj s z.property)) ((generatedField s).mul_mem
      (by norm_cast; exact (generatedField s).natCast_mem 2) (generatedField_I s))

lemma generatedField_finite (s : Finset ℂ) (hs : ∀ z ∈ s, IsAlgebraic ℚ z) :
    FiniteDimensional ℚ (generatedField s) := by
  have hiAlg : IsAlgebraic ℚ Complex.I := IsAlgebraic.of_pow (n := 2) (by norm_num) (by
    rw [Complex.I_sq]; exact isAlgebraic_one.neg)
  apply IntermediateField.finiteDimensional_adjoin
  intro z hz
  rcases Finset.mem_union.mp hz with hz | hz
  · rcases Finset.mem_union.mp hz with hz | hz
    · have : z = Complex.I := Finset.mem_singleton.mp hz
      rw [this]
      exact hiAlg.isIntegral
    · obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
      rw [Complex.re_eq_add_conj, div_eq_mul_inv]
      exact ((hs w hw).add (IsAlgebraic.algHom (Complex.conjAe.restrictScalars ℚ).toAlgHom
        (hs w hw))).mul (isAlgebraic_natCast 2).inv |>.isIntegral
  · obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
    rw [Complex.im_eq_sub_conj, div_eq_mul_inv]
    exact ((hs w hw).sub (IsAlgebraic.algHom (Complex.conjAe.restrictScalars ℚ).toAlgHom
      (hs w hw))).mul ((isAlgebraic_natCast 2).mul hiAlg).inv |>.isIntegral

lemma finrank_ge_two (N : IntermediateField ℚ ℂ) [FiniteDimensional ℚ N]
    (hi : Complex.I ∈ N) : 2 ≤ finrank ℚ N := by
  have hp : 0 < finrank ℚ N := finrank_pos
  by_contra! hh
  have he : finrank ℚ N = 1 := by omega
  obtain ⟨q,hq⟩ := (finrank_eq_one_iff_of_nonzero' (1:N) one_ne_zero).mp he (iN N hi)
  have hqc := congrArg (fun z : N => (z:ℂ).im) hq
  simp [iN,Algebra.smul_def] at hqc

lemma cayley_subspaces_avoid (N : IntermediateField ℚ ℂ) [FiniteDimensional ℚ N]
    (hi : Complex.I ∈ N) (hre : ∀ z : N, ((z:ℂ).re : ℂ) ∈ N)
    (him : ∀ z : N, ((z:ℂ).im : ℂ) ∈ N)
    (P : Finset (Submodule ℚ N)) (hP : ∀ p ∈ P, p < ⊤) :
    ∃ x : N, ‖(x:ℂ)‖ = 1 ∧ ∀ p ∈ P, x ∉ p := by
  classical
  choose ℓ hn hker using fun p : P => Submodule.exists_le_ker_of_lt_top p.val (hP p p.property)
  let s : Finset (N →ₗ[ℚ] ℚ) := Finset.univ.image ℓ
  have hs : ∀ ψ ∈ s, ψ ≠ 0 := by
    intro ψ hψ
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hψ
    exact hn p
  obtain ⟨a,ha⟩ := cayley_finite_avoid N hi hre him s hs
  refine ⟨realCayley N hi a,cayley_real_norm N hi a,fun p hp hx => ?_⟩
  exact ha (ℓ ⟨p,hp⟩) (Finset.mem_image.mpr ⟨⟨p,hp⟩,Finset.mem_univ _,rfl⟩) (hker ⟨p,hp⟩ hx)

lemma numberField_general_position (N : IntermediateField ℚ ℂ) [FiniteDimensional ℚ N]
    (hi : Complex.I ∈ N) (hre : ∀ z : N, ((z:ℂ).re : ℂ) ∈ N)
    (him : ∀ z : N, ((z:ℂ).im : ℂ) ∈ N) (n : ℕ) :
    ∃ s : Finset N, s.card = n ∧ (∀ z ∈ s, ‖(z:ℂ)‖ = 1) ∧ GeneralPosition.General s := by
  obtain ⟨s,hs,hA,hg⟩ := GeneralPosition.exists_general {z : N | ‖(z:ℂ)‖ = 1}
    (finrank_ge_two N hi) (cayley_subspaces_avoid N hi hre him) n
  exact ⟨s,hs,hA,hg⟩
end EuclideanFiveColor.AlgebraicCayley
end

end ParishFactor
end

-- OAI.Analysis.PlaneSpectrum.Selections
section
namespace ParishFactor

noncomputable section
open Module
namespace EuclideanFiveColor.GeneralPosition
variable {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]

lemma spanning_selection {ι : Type*} (Q : Finset ι) (S : Finset V) (hS : General S)
    (hcard : Q.card*(finrank ℚ V-1) < S.card)
    (A : ι → V → Prop) (hA : ∀ x ∈ S, ∃ i ∈ Q, A i x) :
    ∃ i ∈ Q, ∃ T ⊆ S, T.card = finrank ℚ V ∧
      Submodule.span ℚ (T : Set V) = ⊤ ∧ ∀ x ∈ T, A i x := by
  classical
  choose f hfQ hfA using fun x : S => hA x x.property
  have hs : Fintype.card Q * (finrank ℚ V-1) < Fintype.card S := by simpa using hcard
  let g : S → Q := fun x => ⟨f x,hfQ x⟩
  obtain ⟨i,hi⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card g hs
  have hi' : finrank ℚ V ≤ (S.filter (fun x => A i x)).card := by
    have hx : (Finset.univ.filter (fun x : S => g x = i)).card ≤
        (S.filter (fun x => A i x)).card := by
      apply Finset.card_le_card_of_injOn (fun x : S => x.val)
      · intro x hx
        have hg : g x = i := (Finset.mem_filter.mp hx).2
        exact Finset.mem_filter.mpr ⟨x.property,by
          have hh := hfA x
          change A (g x).val x.val at hh
          rwa [hg] at hh⟩
      · intro x hx y hy hxy
        exact Subtype.ext hxy
    omega
  obtain ⟨T,hT,hTc⟩ := Finset.exists_subset_card_eq hi'
  have hTS : T ⊆ S := fun x hx => (Finset.mem_filter.mp (hT hx)).1
  exact ⟨i,i.property,T,hTS,hTc,hS.spans hTS hTc, fun x hx => (Finset.mem_filter.mp (hT hx)).2⟩
end EuclideanFiveColor.GeneralPosition
end

noncomputable section
namespace EuclideanFiveColor.Arithmetic

lemma common_denominator {ι : Type*} [Fintype ι] (c : ι → ℚ) :
    ∃ D : ℕ, 0 < D ∧ ∃ a : ι → ℤ, ∀ i, (D:ℚ)*c i = a i := by
  classical
  let D := ∏ i, (c i).den
  let a := fun i => ((∏ j ∈ Finset.univ.erase i, (c j).den : ℕ) : ℤ)*(c i).num
  refine ⟨D,Finset.prod_pos (fun _ _ => Rat.den_pos _),a,fun i => ?_⟩
  have hD : D = (∏ j ∈ Finset.univ.erase i, (c j).den)*(c i).den :=
    (Finset.prod_erase_mul _ _ (Finset.mem_univ i)).symm
  rw [hD, Nat.cast_mul, mul_assoc, Rat.den_mul_eq_num]
  simp only [a, Int.cast_mul, Int.cast_natCast]

lemma uniform_integral_representations {ι : Type*} [Fintype ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)]
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (v : ∀ i, κ i → V) (x y : V)
    (hx : ∀ i, ∃ c : κ i → ℚ, ∑ j, c j • v i j = x)
    (hy : ∀ i, ∃ c : κ i → ℚ, ∑ j, c j • v i j = y) :
    ∃ D M : ℕ, 0 < D ∧ 0 < M ∧ ∃ a b : ∀ i, κ i → ℤ, ∀ i : ι,
      (∑ j, a i j • v i j) = D • x ∧
      (∑ j, b i j • v i j) = D • y ∧
      (∑ j : κ i, ((a i j).natAbs+(b i j).natAbs)) ≤ M := by
  classical
  choose c hc using hx
  choose d hd using hy
  let f : (Σ i, κ i) × Bool → ℚ := fun p => if p.2 then c p.1.1 p.1.2 else d p.1.1 p.1.2
  obtain ⟨D,hD,A,hA⟩ := common_denominator f
  let a := fun (i : ι) (j : κ i) => A (⟨i,j⟩,true)
  let b := fun (i : ι) (j : κ i) => A (⟨i,j⟩,false)
  let m := fun i => ∑ j : κ i, ((a i j).natAbs+(b i j).natAbs)
  let M := (∑ i, m i)+1
  refine ⟨D,M,hD,Nat.zero_lt_succ _,a,b,fun i => ⟨?_,?_,?_⟩⟩
  · calc
      (∑ j, a i j • v i j) = ∑ j, ((D:ℚ)*c i j) • v i j := by
        apply Finset.sum_congr rfl
        intro j _
        have hh := hA (⟨i,j⟩,true)
        simp only [f,ite_true] at hh
        rw [hh,Int.cast_smul_eq_zsmul]
      _ = (D:ℚ) • ∑ j, c i j • v i j := by simp only [Finset.smul_sum,smul_smul]
      _ = D • x := by rw [hc,Nat.cast_smul_eq_nsmul]
  · calc
      (∑ j, b i j • v i j) = ∑ j, ((D:ℚ)*d i j) • v i j := by
        apply Finset.sum_congr rfl
        intro j _
        have hh := hA (⟨i,j⟩,false)
        simp only [f,Bool.false_eq_true,ite_false] at hh
        rw [hh,Int.cast_smul_eq_zsmul]
      _ = (D:ℚ) • ∑ j, d i j • v i j := by simp only [Finset.smul_sum,smul_smul]
      _ = D • y := by rw [hd,Nat.cast_smul_eq_nsmul]
  · exact (Finset.single_le_sum (fun j _ => Nat.zero_le (m j)) (Finset.mem_univ i)).trans (Nat.le_succ _)
end EuclideanFiveColor.Arithmetic
end

noncomputable section
open Module
namespace EuclideanFiveColor.Arithmetic
open AlgebraicCayley GeneralPosition

lemma span_mult_rep (N : IntermediateField ℚ ℂ) (T : Finset N)
    (hT : Submodule.span ℚ (T : Set N) = ⊤) (q : N) (hq : q ≠ 0) (x : N) :
    ∃ c : T → ℚ, ∑ j, c j • (q*j.val) = x := by
  have hs : Set.range (fun j : T => j.val) = (T : Set N) := Subtype.range_coe
  have hx : q⁻¹*x ∈ Submodule.span ℚ (Set.range (fun j : T => j.val)) := by rw [hs,hT]; trivial
  obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp hx
  refine ⟨c,?_⟩
  calc
    (∑ j, c j • (q*j.val)) = q * ∑ j, c j • j.val := by
      simp only [Finset.mul_sum, mul_smul_comm]
    _ = x := by rw [hc,← mul_assoc,mul_inv_cancel₀ hq,one_mul]

lemma uniform_selection (Q : Finset ℂ)
    (hQn : ∀ q ∈ Q, ‖q‖ = 1) (hQa : ∀ q ∈ Q, IsAlgebraic ℚ q)
    (A : ℂ → Prop)
    (hA : ∀ v : ℂ, ‖v‖ = 1 → IsAlgebraic ℚ v → ∃ q ∈ Q, A (q*v)) :
    ∃ D M : ℕ, 0 < D ∧ 0 < M ∧ ∀ v : ℂ, ‖v‖ = 1 → IsAlgebraic ℚ v →
      ∃ n : ℕ, ∃ k : Fin n → ℂ, ∃ a b : Fin n → ℤ,
        (∀ j, ‖k j‖ = 1 ∧ IsAlgebraic ℚ (k j) ∧ A (k j*v)) ∧
        (∑ j, a j • k j) = D • (1:ℂ) ∧
        (∑ j, b j • k j) = D • Complex.I ∧
        (∑ j, ((a j).natAbs+(b j).natAbs)) ≤ M := by
  classical
  let N := generatedField Q
  have : FiniteDimensional ℚ N := generatedField_finite Q hQa
  obtain ⟨S,hSc,hSn,hSg⟩ := numberField_general_position N (generatedField_I Q)
    (generatedField_re_closed Q) (generatedField_im_closed Q)
    (Q.card*(finrank ℚ N-1)+1)
  let TS : Finset (Finset N) := S.powerset.filter (fun T => Submodule.span ℚ (T:Set N) = ⊤)
  let I := Q × TS
  let κ : I → Type := fun i => i.2.val
  let qs : Q → N := fun q => ⟨q.val,generatedField_contains Q q.val q.property⟩
  have hqs (q : Q) : qs q ≠ 0 := by
    intro he
    have hec := congrArg (fun z : N => (z:ℂ)) he
    have hn := hQn q q.property
    change q.val = 0 at hec
    simp [hec] at hn
  let k : ∀ i : I, κ i → N := fun i j => qs i.1*j.val
  have hs (i : I) : Submodule.span ℚ (i.2.val:Set N) = ⊤ := (Finset.mem_filter.mp i.2.property).2
  obtain ⟨D,M,hD,hM,a,b,hab⟩ := uniform_integral_representations k (1:N) (iN N (generatedField_I Q))
    (fun i => span_mult_rep N i.2.val (hs i) _ (hqs _) _)
    (fun i => span_mult_rep N i.2.val (hs i) _ (hqs _) _)
  refine ⟨D,M,hD,hM,fun v hv hva => ?_⟩
  have hAlg (z : N) : IsAlgebraic ℚ (z:ℂ) :=
    IsAlgebraic.algHom N.val (IsAlgebraic.of_finite ℚ z)
  obtain ⟨q,hq,T,hTS,hTc,hTspan,hTA⟩ := spanning_selection Q S hSg (by omega)
    (fun q s => A (q*(s:ℂ)*v)) (by
      intro s hs
      have hn : ‖(s:ℂ)*v‖ = 1 := by rw [norm_mul,hSn s hs,hv,one_mul]
      obtain ⟨q,hq,hqA⟩ := hA ((s:ℂ)*v) hn ((hAlg s).mul hva)
      exact ⟨q,hq,by simpa only [mul_assoc] using hqA⟩)
  have hTmem : T ∈ TS := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hTS,hTspan⟩
  let i : I := (⟨q,hq⟩,⟨T,hTmem⟩)
  let e := (Fintype.equivFin (κ i)).symm
  refine ⟨Fintype.card (κ i),fun j => (k i (e j):ℂ),fun j => a i (e j),fun j => b i (e j),?_,?_,?_,?_⟩
  · intro j
    have hj : (e j).val ∈ T := (e j).property
    refine ⟨?_,hAlg (k i (e j)),?_⟩
    · change ‖q*((e j).val:ℂ)‖ = 1
      rw [norm_mul,hQn q hq,hSn _ (hTS hj),one_mul]
    · exact hTA _ hj
  · have he := congrArg (fun z : N => (z:ℂ)) (hab i).1
    push_cast at he
    rw [← he]
    exact Fintype.sum_equiv e _ _ (fun _ => by simp)
  · have he := congrArg (fun z : N => (z:ℂ)) (hab i).2.1
    push_cast at he
    change (∑ j, b i j • (k i j:ℂ)) = D • Complex.I at he
    rw [← he]
    exact Fintype.sum_equiv e _ _ (fun _ => by simp)
  · rw [Fintype.sum_equiv e _ (fun j => (a i j).natAbs+(b i j).natAbs) (fun _ => rfl)]
    exact (hab i).2.2

lemma uniform_selection_of_template (E : Set ℂ) (hE : PlaneFiveColor.Spectral.TemplateProperty E)
    (hEmul : ∀ a ∈ E, ∀ b ∈ E, a*b ∈ E) (Q : Finset ℂ)
    (hQn : ∀ q ∈ Q, ‖q‖ = 1) (hQa : ∀ q ∈ Q, q ∈ E)
    (A : ℂ → Prop)
    (hA : ∀ v : ℂ, ‖v‖ = 1 → v ∈ E → ∃ q ∈ Q, A (q*v)) :
    ∃ D M : ℕ, 0 < D ∧ 0 < M ∧ ∀ v : ℂ, ‖v‖ = 1 → v ∈ E →
      ∃ n : ℕ, ∃ k : Fin n → ℂ, ∃ a b : Fin n → ℤ,
        (∀ j, ‖k j‖ = 1 ∧ k j ∈ E ∧ A (k j*v)) ∧
        (∑ j, a j • k j) = D • (1:ℂ) ∧
        (∑ j, b j • k j) = D • Complex.I ∧
        (∑ j, ((a j).natAbs+(b j).natAbs)) ≤ M := by
  classical
  obtain ⟨S,hSa,hS⟩ := hE Q (fun q hq => ⟨hQa q hq,hQn q hq⟩)
  let k : ∀ i : S → Q, S → ℂ := fun i s => (i s:ℂ)*s
  let jf : (S → Q) → ℂ → ℂ := fun i z => if h : z ∈ S then (i ⟨z,h⟩:ℂ) else 0
  have hspan (i : S → Q) (x : ℂ)
      (hx : x ∈ Submodule.span ℚ ((fun s => jf i s*s) '' (S:Set ℂ))) :
      ∃ c : S → ℚ, ∑ s, c s • k i s = x := by
    have he : (fun s => jf i s*s) '' (S:Set ℂ) = Set.range (k i) := by
      ext z
      constructor
      · rintro ⟨s,hs,rfl⟩
        exact ⟨⟨s,hs⟩,by simp [k,jf,Finset.mem_coe.mp hs]⟩
      · rintro ⟨s,rfl⟩
        exact ⟨s,s.property,by simp [k,jf]⟩
    rw [he] at hx
    exact (Submodule.mem_span_range_iff_exists_fun ℚ).mp hx
  have hj (i : S → Q) : ∀ s ∈ S, jf i s ∈ Q := fun s hs => by simp [jf,hs]
  obtain ⟨D,M,hD,hM,a,b,hab⟩ := uniform_integral_representations (κ := fun _ : S → Q => S)
    k (1:ℂ) Complex.I
    (fun i => hspan i 1 (hS (jf i) (hj i)).1)
    (fun i => hspan i Complex.I (hS (jf i) (hj i)).2)
  refine ⟨D,M,hD,hM,fun v hv hva => ?_⟩
  have hc (s : S) : ∃ q ∈ Q, A (q*((s:ℂ)*v)) :=
    hA _ (by rw [norm_mul,(hSa s s.property).2,hv,one_mul]) (hEmul _ (hSa s s.property).1 _ hva)
  choose f hfQ hfA using hc
  let i : S → Q := fun s => ⟨f s,hfQ s⟩
  let e := (Fintype.equivFin S).symm
  refine ⟨Fintype.card S,fun j => k i (e j),fun j => a i (e j),fun j => b i (e j),?_,?_,?_,?_⟩
  · intro j
    refine ⟨?_,hEmul _ (hQa _ (hfQ _)) _ (hSa _ (e j).property).1,?_⟩
    · change ‖f (e j)*((e j:S):ℂ)‖ = 1
      rw [norm_mul,hQn _ (hfQ _),hSa _ (e j).property |>.2,one_mul]
    · change A (f (e j)*((e j:S):ℂ)*v)
      rw [mul_assoc]
      exact hfA _
  · rw [← (hab i).1]
    exact Fintype.sum_equiv e _ _ (fun _ => rfl)
  · rw [← (hab i).2.1]
    exact Fintype.sum_equiv e _ _ (fun _ => rfl)
  · rw [Fintype.sum_equiv e _ (fun j => (a i j).natAbs+(b i j).natAbs) (fun _ => rfl)]
    exact (hab i).2.2
end EuclideanFiveColor.Arithmetic
end

noncomputable section
namespace EuclideanFiveColor.Arithmetic

lemma real_sum_bound {ι : Type*} [Fintype ι] (a : ι → ℤ) (x : ι → ℝ) (B : ℝ)
    (hx : ∀ i, |x i| ≤ B) :
    |∑ i, (a i : ℝ)*x i| ≤ (∑ i, ((a i).natAbs : ℝ))*B := by
  calc
    _ ≤ ∑ i, |(a i:ℝ)*x i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ((a i).natAbs : ℝ)*B := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      have he : |(a i:ℝ)| = ((a i).natAbs : ℝ) := by simp
      rw [he]
      exact mul_le_mul_of_nonneg_left (hx i) (Nat.cast_nonneg _)
    _ = _ := (Finset.sum_mul _ _ _).symm

lemma selection_transverse {ι : Type*} [Fintype ι] (k : ι → ℂ) (a b : ι → ℤ)
    (D M : ℕ) (hD : 0 < D)
    (ha : (∑ i, a i • k i) = D • (1:ℂ))
    (hb : (∑ i, b i • k i) = D • Complex.I)
    (hM : (∑ i, ((a i).natAbs+(b i).natAbs)) ≤ M)
    (v : ℂ) (hv : ‖v‖ = 1) :
    ∃ i, ∀ j, |(k j*v).re| ≤ |(k i*v).re| ∧
      (D:ℝ) ≤ (M:ℝ)*|(k i*v).re| := by
  classical
  have hn : Nonempty ι := by
    by_contra hh
    have : IsEmpty ι := not_nonempty_iff.mp hh
    have he : (D:ℂ) = 0 := by simpa using ha.symm
    have : D = 0 := by exact_mod_cast he
    omega
  have := hn
  obtain ⟨i,_,him⟩ := Finset.exists_max_image Finset.univ (fun j => |(k j*v).re|) Finset.univ_nonempty
  have hm (j : ι) : |(k j*v).re| ≤ |(k i*v).re| := him j (Finset.mem_univ j)
  have h1 : (∑ j, (a j:ℝ)*(k j*v).re) = (D:ℝ)*v.re := by
    have he := congrArg (fun z : ℂ => (z*v).re) ha
    simpa only [Finset.sum_mul, Complex.re_sum, zsmul_eq_mul, nsmul_eq_mul,
      mul_assoc, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, zero_mul,
      sub_zero, Complex.natCast_re, Complex.natCast_im, Complex.one_re, Complex.one_im,
      mul_one] using he
  have h2 : (∑ j, (b j:ℝ)*(k j*v).re) = -(D:ℝ)*v.im := by
    have he := congrArg (fun z : ℂ => (z*v).re) hb
    simpa only [Finset.sum_mul, Complex.re_sum, zsmul_eq_mul, nsmul_eq_mul,
      mul_assoc, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, zero_mul,
      sub_zero, Complex.natCast_re, Complex.natCast_im, Complex.I_re, Complex.I_im,
      one_mul, zero_sub, mul_neg, neg_mul] using he
  have h1b := real_sum_bound a (fun j => (k j*v).re) _ hm
  have h2b := real_sum_bound b (fun j => (k j*v).re) _ hm
  rw [h1,abs_mul,abs_of_nonneg (Nat.cast_nonneg D)] at h1b
  rw [h2,abs_mul,abs_neg,abs_of_nonneg (Nat.cast_nonneg D)] at h2b
  have hcomp : 1 ≤ |v.re|+|v.im| := hv ▸ Complex.norm_le_abs_re_add_abs_im v
  have hMc : (∑ j, ((a j).natAbs:ℝ))+(∑ j, ((b j).natAbs:ℝ)) ≤ (M:ℝ) := by
    have he : ((∑ j, ((a j).natAbs+(b j).natAbs) : ℕ):ℝ) =
        (∑ j, ((a j).natAbs:ℝ))+(∑ j, ((b j).natAbs:ℝ)) := by
      simp [Finset.sum_add_distrib]
    rw [← he]
    exact_mod_cast hM
  have hexp := mul_le_mul_of_nonneg_right hMc (abs_nonneg (k i*v).re)
  have hfinal : (D:ℝ) ≤ (M:ℝ)*|(k i*v).re| := by
    nlinarith [mul_le_mul_of_nonneg_left hcomp (Nat.cast_nonneg D)]
  exact ⟨i,fun j => ⟨hm j,hfinal⟩⟩
end EuclideanFiveColor.Arithmetic
end

noncomputable section
namespace EuclideanFiveColor.CappedResidues
variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
variable (m : α → ℝ) (hm0 : m 0 = 1)
  (hd : ∀ a b : α, 0 ≤ a → 0 ≤ b → m a * m b ≤ m |a-b|)
  (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)

private def Good (n : ℕ) (x : α) : Prop := c^n ≤ m x
include hc0 hc1 in
omit [Field α] [LinearOrder α] [IsStrictOrderedRing α] in
lemma good_mono {n k : ℕ} {x : α} (h : Good m c n x) (hnk : n ≤ k) : Good m c k x :=
  (pow_le_pow_of_le_one hc0 hc1 hnk).trans h
include hm0 hc0 hc1 in
omit [LinearOrder α] [IsStrictOrderedRing α] in
lemma good_zero (n : ℕ) : Good m c n 0 := by
  unfold Good
  rw [hm0]
  exact pow_le_one₀ hc0 hc1
include hd hc0 in
omit [IsStrictOrderedRing α] in
lemma good_diff {n k : ℕ} {a b : α} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : Good m c n a) (hB : Good m c k b) : Good m c (n+k) |a-b| := by
  unfold Good at *
  rw [pow_add]
  exact (mul_le_mul hA hB (pow_nonneg hc0 k) ((pow_nonneg hc0 n).trans hA)).trans (hd a b ha hb)

variable {p : α} (hp : 0 < p) (hpG : Good m c 1 p)
include hd hc0 hc1 hp hpG in
lemma add_residues {a b : α} {n k : ℕ} (ha : a ∈ Set.Ico 0 p) (hb : b ∈ Set.Ico 0 p)
    (hA : Good m c n a) (hB : Good m c k b) :
    ∃ r : α, r ∈ Set.Ico 0 p ∧ Good m c (n+k+2) r ∧ ∃ j : ℤ, a+b = r+j•p := by
  obtain ⟨ha0, hap⟩ := ha
  obtain ⟨hb0, hbp⟩ := hb
  have ha : a ∈ Set.Ico 0 p := ⟨ha0,hap⟩
  have hb : b ∈ Set.Ico 0 p := ⟨hb0,hbp⟩
  by_cases hs : a+b < p
  · refine ⟨a+b, ⟨add_nonneg ha.1 hb.1, hs⟩, ?_, 0, by simp⟩
    have hpa : Good m c (1+n) (p-a) := by
      simpa only [abs_of_nonneg (sub_nonneg.mpr ha.2.le)] using
        good_diff m hd c hc0 hp.le ha.1 hpG hA
    have hsub : Good m c (1+n+k) ((p-a)-b) := by
      simpa only [abs_of_nonneg (show 0 ≤ (p-a)-b by linarith)] using
        good_diff m hd c hc0 (sub_nonneg.mpr ha.2.le) hb.1 hpa hB
    have hfinal := good_diff m hd c hc0 hp.le (show 0 ≤ (p-a)-b by linarith) hpG hsub
    have he : |p-((p-a)-b)| = a+b := by rw [abs_of_nonneg (by linarith)]; abel
    simpa only [he, show 1+(1+n+k) = n+k+2 by omega] using hfinal
  · refine ⟨a+b-p, ⟨by linarith, by linarith⟩, ?_, 1, by simp⟩
    have hpb : Good m c (1+k) (p-b) := by
      simpa only [abs_of_nonneg (sub_nonneg.mpr hb.2.le)] using
        good_diff m hd c hc0 hp.le hb.1 hpG hB
    have hfinal := good_diff m hd c hc0 ha.1 (sub_nonneg.mpr hb.2.le) hA hpb
    have he : |a-(p-b)| = a+b-p := by rw [abs_of_nonneg (by linarith)]; abel
    apply good_mono m c hc0 hc1 (n := n+(1+k)) (hnk := by omega)
    simpa only [he] using hfinal

include hm0 hd hc0 hc1 hp hpG in
lemma input_residue {x : α} (hx : |x| ≤ p) (hG : Good m c 1 |x|) :
    ∃ r : α, r ∈ Set.Ico 0 p ∧ Good m c 2 r ∧ ∃ j : ℤ, x = r+j•p := by
  by_cases hx0 : 0 ≤ x
  · have hxp : x ≤ p := by simpa [abs_of_nonneg hx0] using hx
    rcases lt_or_eq_of_le hxp with hlt | rfl
    · exact ⟨x, ⟨hx0,hlt⟩, good_mono m c hc0 hc1 (by simpa [abs_of_nonneg hx0] using hG) (by omega), 0, by simp⟩
    · exact ⟨0, ⟨le_rfl,hp⟩, good_zero m hm0 c hc0 hc1 2, 1, by simp⟩
  · have hn : 0 < -x := neg_pos.mpr (lt_of_not_ge hx0)
    have hnx : -x ≤ p := by simpa [abs_of_neg (lt_of_not_ge hx0)] using hx
    rcases lt_or_eq_of_le hnx with hlt | heq
    · refine ⟨p+x, ⟨by linarith, by linarith⟩, ?_, -1, by simp⟩
      have hneg : Good m c 1 (-x) := by simpa [abs_of_neg (lt_of_not_ge hx0)] using hG
      have hfinal := good_diff m hd c hc0 hp.le hn.le hpG hneg
      simpa only [show |p- -x| = p+x by rw [sub_neg_eq_add, abs_of_nonneg (by linarith)]] using hfinal
    · refine ⟨0, ⟨le_rfl,hp⟩, good_zero m hm0 c hc0 hc1 2, -1, ?_⟩
      simp only [neg_smul, one_smul, zero_add]
      linarith

include hm0 hd hc0 hc1 hp hpG in
lemma list_residue (l : List α) (hl : ∀ x∈l, |x| ≤ p ∧ Good m c 1 |x|) :
    ∃ r : α, r ∈ Set.Ico 0 p ∧ Good m c (4*l.length) r ∧ ∃ j : ℤ, l.sum = r+j•p := by
  induction l with
  | nil => exact ⟨0, ⟨le_rfl,hp⟩, good_zero m hm0 c hc0 hc1 _, 0, by simp⟩
  | cons x l ih =>
    obtain ⟨a,ha,hA,i,hi⟩ := input_residue m hm0 hd c hc0 hc1 hp hpG (hl x (List.mem_cons_self)).1 (hl x (List.mem_cons_self)).2
    obtain ⟨b,hb,hB,j,hj⟩ := ih (fun y hy => hl y (List.mem_cons_of_mem x hy))
    obtain ⟨r,hr,hR,k,hk⟩ := add_residues m hd c hc0 hc1 hp hpG ha hb hA hB
    refine ⟨r,hr,?_,i+j+k,?_⟩
    · simpa only [List.length_cons, show 2+4*l.length+2 = 4*(l.length+1) by omega] using hR
    · simp only [List.sum_cons, hi, hj, add_zsmul]
      calc
        _ = (a+b)+(i•p+j•p) := by abel
        _ = _ := by rw [hk]; abel

include hm0 hd hc0 hc1 hp hpG in
lemma list_cap (l : List α) (hl : ∀ x∈l, |x| ≤ p ∧ Good m c 1 |x|)
    (hz : l.sum ∈ Set.Ico 0 p) : Good m c (4*l.length) l.sum := by
  obtain ⟨r,hr,hR,j,hj⟩ := list_residue m hm0 hd c hc0 hc1 hp hpG l hl
  have hzero : j = 0 := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hn | hn
    · have hle : j ≤ -1 := by omega
      have hh : j•p ≤ (-1:ℤ)•p := by
        simp only [zsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hle) hp.le
      simp only [neg_smul, one_smul] at hh
      linarith [hz.1, hr.2]
    · have hge : 1 ≤ j := by omega
      have hh : (1:ℤ)•p ≤ j•p := by
        simp only [zsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hge) hp.le
      simp only [one_smul] at hh
      linarith [hz.2, hr.1]
  have he : l.sum = r := by simpa only [hzero, zero_smul, add_zero] using hj
  rw [he]
  exact hR
end EuclideanFiveColor.CappedResidues
end

noncomputable section
namespace EuclideanFiveColor.CappedResidues
variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

private def signedList (a : ℤ) (x : α) : List α :=
  match a with
  | .ofNat n => List.replicate n x
  | .negSucc n => List.replicate (n+1) (-x)
omit [LinearOrder α] [IsStrictOrderedRing α] in
@[simp] lemma signedList_length (a : ℤ) (x : α) : (signedList a x).length = a.natAbs := by
  cases a <;> simp [signedList]
omit [LinearOrder α] [IsStrictOrderedRing α] in
@[simp] lemma signedList_sum (a : ℤ) (x : α) : (signedList a x).sum = a • x := by
  cases a <;> simp [signedList]
  ring
omit [IsStrictOrderedRing α] in
lemma signedList_mem (a : ℤ) (x v : α) (hv : v ∈ signedList a x) : |v| = |x| := by
  cases a <;> simp only [signedList,List.mem_replicate] at hv
  · rw [hv.2]
  · rw [hv.2,abs_neg]

omit [IsStrictOrderedRing α] in
lemma integer_list {ι : Type*} (s : Finset ι) (a : ι → ℤ) (x : ι → α) :
    ∃ l : List α, l.length = ∑ i ∈ s, (a i).natAbs ∧ l.sum = ∑ i ∈ s, a i • x i ∧
      ∀ v ∈ l, ∃ i ∈ s, |v| = |x i| := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨[],by simp,by simp,by simp⟩
  | @insert i s hi ih =>
    obtain ⟨l,hl,hs,hv⟩ := ih
    refine ⟨signedList (a i) (x i) ++ l,?_,?_,?_⟩
    · simp [hl,hi]
    · simp [hs,hi]
    · intro v hv'
      rcases List.mem_append.mp hv' with hv' | hv'
      · exact ⟨i,Finset.mem_insert_self _ _,signedList_mem _ _ _ hv'⟩
      · obtain ⟨j,hj,he⟩ := hv v hv'
        exact ⟨j,Finset.mem_insert_of_mem hj,he⟩

variable (m : α → ℝ) (hm0 : m 0 = 1)
  (hd : ∀ a b : α, 0 ≤ a → 0 ≤ b → m a*m b ≤ m |a-b|)
  (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
  {p : α} (hp : 0 < p) (hpG : Good m c 1 p)
include hm0 hd hc0 hc1 hp hpG in
lemma integer_cap {ι : Type*} (s : Finset ι) (a : ι → ℤ) (x : ι → α)
    (hx : ∀ i ∈ s, |x i| ≤ p ∧ Good m c 1 |x i|)
    (hz : (∑ i ∈ s, a i • x i) ∈ Set.Ico 0 p) :
    Good m c (4*∑ i ∈ s, (a i).natAbs) (∑ i ∈ s, a i • x i) := by
  obtain ⟨l,hl,hs,hv⟩ := integer_list s a x
  have he := list_cap m hm0 hd c hc0 hc1 hp hpG l (by
    intro v hvl
    obtain ⟨i,hi,he⟩ := hv v hvl
    rw [he]
    exact hx i hi) (hs.symm ▸ hz)
  rwa [hl,hs] at he
include hm0 hd hc0 hc1 hp hpG in
lemma integer_abs_cap {ι : Type*} (s : Finset ι) (a : ι → ℤ) (x : ι → α)
    (hx : ∀ i ∈ s, |x i| ≤ p ∧ Good m c 1 |x i|)
    (hz : |∑ i ∈ s, a i • x i| < p) :
    Good m c (4*∑ i ∈ s, (a i).natAbs) |∑ i ∈ s, a i • x i| := by
  by_cases hn : 0 ≤ ∑ i ∈ s, a i • x i
  · rw [abs_of_nonneg hn] at hz ⊢
    exact integer_cap m hm0 hd c hc0 hc1 hp hpG s a x hx ⟨hn,hz⟩
  · have hs : (∑ i ∈ s, a i • (-x i)) = -∑ i ∈ s, a i • x i := by simp
    have hz' : (∑ i ∈ s, a i • (-x i)) ∈ Set.Ico 0 p := by
      rw [hs]
      have he : |∑ i ∈ s, a i • x i| = -∑ i ∈ s, a i • x i := abs_of_neg (lt_of_not_ge hn)
      exact ⟨by linarith,he ▸ hz⟩
    have he := integer_cap m hm0 hd c hc0 hc1 hp hpG s a (fun i => -x i)
      (fun i hi => by simpa only [abs_neg] using hx i hi) hz'
    simpa only [hs,abs_of_neg (lt_of_not_ge hn)] using he
end EuclideanFiveColor.CappedResidues
end

end ParishFactor
end

-- OAI.Analysis.PlaneSpectrum.RadialEnergy
section
namespace ParishFactor

noncomputable section
open scoped ComplexConjugate
namespace PlaneFiveColor.Spectral
lemma equal_moduli_quadratic (A B L : ℝ) (hL : L^2 = A*B) (u : Circle) :
    ‖(A : ℂ) - B*(u : ℂ)^2‖ =
      ‖-(L : ℂ) + (A-B : ℝ)*(u : ℂ) + L*(u : ℂ)^2‖ := by
  have hu : (u : ℂ) * conj (u : ℂ) = 1 := by
    rw [Complex.mul_conj, Circle.normSq_coe, Complex.ofReal_one]
  have hreal : (u : ℂ).re^2 + (u : ℂ).im^2 = 1 := by
    simpa only [Complex.normSq_apply, sq] using Circle.normSq_coe u
  have hleft : (A : ℂ) - B*(u : ℂ)^2 =
      (u : ℂ) * ((A : ℂ)*conj (u : ℂ) - B*(u : ℂ)) := by
    calc
      _ = A*((u : ℂ)*conj (u : ℂ)) - B*(u : ℂ)^2 := by rw [hu, mul_one]
      _ = _ := by ring
  have hright : -(L : ℂ) + (A-B : ℝ)*(u : ℂ) + L*(u : ℂ)^2 =
      (u : ℂ) * (((A-B : ℝ) : ℂ) + L*((u : ℂ)-conj (u : ℂ))) := by
    calc
      _ = -L*((u : ℂ)*conj (u : ℂ)) + (A-B : ℝ)*(u : ℂ) + L*(u : ℂ)^2 := by rw [hu, mul_one]
      _ = _ := by ring
  rw [hleft, hright, norm_mul, norm_mul, Circle.norm_coe, one_mul, one_mul]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.conj_re, Complex.conj_im, Complex.sub_im, Complex.mul_im,
    Complex.add_re, Complex.add_im, zero_mul, sub_zero, zero_add, add_zero]
  nlinarith [mul_self_nonneg (A-B), mul_self_nonneg (A+B),
    congrArg (fun x : ℝ => (A-B)^2*x) hreal,
    congrArg (fun x : ℝ => 4*x*(u : ℂ).im^2) hL]
end PlaneFiveColor.Spectral
end

noncomputable section
open MeasureTheory ProbabilityTheory Filter EuclideanFiveColor
open scoped ENNReal NNReal ComplexConjugate BoundedContinuousFunction
namespace PlaneFiveColor.Spectral
open EuclideanFiveColor.BoundedMeasurable
variable [Carrier]
variable {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
variable (μ : Measure D) [IsProbabilityMeasure μ] [ErgodicSMul K D μ]
  (q : D → Y) (hq : Measurable q)
  [MulAction K Y] [MeasurableConstSMul K Y]
  (hqcov : ∀ k : K, ∀ᵐ d ∂μ, q (k • d) = k • q d)
  [ErgodicVAdd Rot (D×D) (RelativeProduct.law μ q hq)]

include hq hqcov in
lemma projectedMass_pair_mean [IsProbabilityMeasure (μ.map q)] (M : Amenable.Mean Rot) (a b : E) :
    M.map (Family.energy (μ.map q) (Family.conditional μ q
      (Family.const (G := Rot) (char a) * Family.orbit (scaleHom (G := Rot) 2) (char b)))) =
      projectedMass μ q a * projectedMass μ q b := by
  exact conditional_pair_energy μ q hq (fun g : Rot => hqcov (rotMul g)) M
    (scaleHom (G := Rot) 2) (rot_zsmul_surjective 2 (by decide)) (char a) (char b)

lemma kCoeff_scale_two (g : Rot) : kCoeff (rotMul ((scaleHom (G := Rot) 2) g)) = kCoeff (rotMul g)^2 := by
  change kCoeff ((rotMul g)^2) = _
  simp only [pow_two, kCoeff_mul]
lemma kCoeff_scale_one (g : Rot) : kCoeff (rotMul ((scaleHom (G := Rot) 1) g)) = kCoeff (rotMul g) := by
  change kCoeff (rotMul ((1:ℤ) • g)) = _
  rw [one_zsmul]
lemma char_two_term (a b : E) (g : Rot) :
    (Family.const (G := Rot) (char a) * Family.orbit (scaleHom (G := Rot) 2) (char b)) g =
      char (a + kCoeff (rotMul g)^2*b) := by
  simp only [Family.mul_apply, Family.const_apply, Family.orbit_apply, char_act,
    kCoeff_scale_two, char_add]
lemma char_three_term (a b c : E) (g : Rot) :
    (Family.orbit (scaleHom (G := Rot) 0) (char a) * Family.orbit (scaleHom (G := Rot) 1) (char b) *
      Family.orbit (scaleHom (G := Rot) 2) (char c)) g =
      char (a+kCoeff (rotMul g)*b+kCoeff (rotMul g)^2*c) := by
  simp only [Family.mul_apply, Family.orbit_apply, char_act, kCoeff_scale_one, kCoeff_scale_two,
    char_add]
  congr 2
  change char (kCoeff (rotMul ((0:ℤ) • g))*a) = char a
  simp only [zero_zsmul]
  change char (1*a) = char a
  rw [one_mul]

include hq hqcov in
lemma quadratic_mass_inequality (a b l h k : E)
    (hn : ∀ u : K, ‖((a + kCoeff u^2*b : E) : ℂ)‖ =
      ‖((l+kCoeff u*h+kCoeff u^2*k : E) : ℂ)‖) :
    projectedMass μ q a * projectedMass μ q b ≤ projectedMass μ q h := by
  haveI := Measure.isProbabilityMeasure_map (μ := μ) hq.aemeasurable
  let : ErgodicVAdd Rot Y (μ.map q) := factor_ergodic μ q hq (fun g : Rot => hqcov (rotMul g))
  let M : Amenable.Mean Rot := MovingMean.toMean (fun _ => 0)
  have he : Family.energy (μ.map q) (Family.conditional μ q
      (Family.const (G := Rot) (char a) * Family.orbit (scaleHom (G := Rot) 2) (char b))) =
      Family.energy (μ.map q) (Family.conditional μ q
        (Family.orbit (scaleHom (G := Rot) 0) (char l) * Family.orbit (scaleHom (G := Rot) 1) (char h) *
          Family.orbit (scaleHom (G := Rot) 2) (char k))) := by
    ext g
    simp only [Family.energy_apply, Family.conditional_apply, char_two_term, char_three_term]
    exact projectedMass_radial μ q hq hqcov (hn (rotMul g))
  rw [← projectedMass_pair_mean μ q hq hqcov M a b, he,
    conditional_integer_triple_energy μ q hq (fun g : Rot => hqcov (rotMul g)) rot_zsmul_surjective]
  calc
    _ ≤ M.map (BoundedContinuousFunction.const Rot (projectedMass μ q h)) := by
      apply M.mono
      intro g
      simp only [Family.energy_apply, Family.mul_apply, Family.orbit_apply,
        BoundedContinuousFunction.const_apply]
      have h1 := l2_mul_norm_le (μ.map q)
        (act (scaleHom (G := Rot) 0 g) (conditional μ q (char l)) * act (scaleHom (G := Rot) 1 g) (conditional μ q (char h)))
        (act (scaleHom (G := Rot) 2 g) (conditional μ q (char k)))
        (fun y => projected_char_bound μ q k ((scaleHom (G := Rot) 2 g) +ᵥ y))
      have h2 := l2_norm_mul_le (μ.map q)
        (act (scaleHom (G := Rot) 0 g) (conditional μ q (char l))) (act (scaleHom (G := Rot) 1 g) (conditional μ q (char h)))
        (fun y => projected_char_bound μ q l ((scaleHom (G := Rot) 0 g) +ᵥ y))
      simp only [one_mul, l2_act, LinearIsometryEquiv.norm_map] at h1 h2
      exact pow_le_pow_left₀ (norm_nonneg _) (h1.trans h2) 2
    _ = _ := M.map_const _
end PlaneFiveColor.Spectral
end

noncomputable section
open MeasureTheory ProbabilityTheory Filter EuclideanFiveColor
open scoped ENNReal NNReal ComplexConjugate BoundedContinuousFunction
namespace PlaneFiveColor.Spectral
open EuclideanFiveColor.BoundedMeasurable
variable [Carrier]

private def sqrtF (a : F) : F := ⟨Real.sqrt a, Carrier.sqrt_mem a.property⟩
lemma sqrtF_sq (a : F) (ha : 0 ≤ a) : sqrtF a ^ 2 = a := by
  apply Subtype.ext
  exact Real.sq_sqrt ha
lemma norm_ofF (a : F) : ‖((ofF a : E) : ℂ)‖ = |(a : ℝ)| := by
  change ‖((a : ℝ) : ℂ)‖ = _
  rw [Complex.norm_real, Real.norm_eq_abs]

variable {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
variable (μ : Measure D) [IsProbabilityMeasure μ] [ErgodicSMul K D μ]
  (q : D → Y) (hq : Measurable q)
  [MulAction K Y] [MeasurableConstSMul K Y]
  (hqcov : ∀ k : K, ∀ᵐ d ∂μ, q (k • d) = k • q d)
  [ErgodicVAdd Rot (D×D) (RelativeProduct.law μ q hq)]
private def massReal (a : F) : ℝ := projectedMass μ q (ofF a)
include hq hqcov in
omit [StandardBorelSpace Y] [Nonempty Y] [ErgodicVAdd Rot (D×D) (RelativeProduct.law μ q hq)] in
lemma projectedMass_neg (a : E) : projectedMass μ q (-a) = projectedMass μ q a := by
  apply projectedMass_radial μ q hq hqcov
  exact norm_neg (a : ℂ)
include hq hqcov in
omit [StandardBorelSpace Y] [Nonempty Y] [ErgodicVAdd Rot (D×D) (RelativeProduct.law μ q hq)] in
lemma massReal_abs (a : F) : massReal μ q |a| = massReal μ q a := by
  apply projectedMass_radial μ q hq hqcov
  rw [norm_ofF, norm_ofF]
  change abs (abs (a : ℝ)) = abs (a : ℝ)
  exact abs_abs _
include hq hqcov in
lemma massReal_difference (A B : F) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    massReal μ q A * massReal μ q B ≤ massReal μ q |A-B| := by
  let l := sqrtF (A*B)
  have hl : (l : ℝ)^2 = (A : ℝ)*(B : ℝ) := by
    exact congrArg (fun x : F => (x : ℝ)) (sqrtF_sq (A*B) (mul_nonneg hA hB))
  have he := quadratic_mass_inequality μ q hq hqcov (ofF A) (-ofF B) (-ofF l) (ofF (A-B)) (ofF l) (fun u => by
    have hh := equal_moduli_quadratic (A : ℝ) (B : ℝ) (l : ℝ) hl u.val
    convert hh using 1 <;> congr 1 <;> simp only [map_sub, ofF, RingHom.coe_mk, MonoidHom.coe_mk,
      OneHom.coe_mk, kCoeff] <;> push_cast <;> ring)
  rw [projectedMass_neg μ q hq hqcov] at he
  rw [massReal_abs μ q hq hqcov]
  exact he
end PlaneFiveColor.Spectral
end

noncomputable section
open scoped ComplexConjugate
namespace PlaneFiveColor.Spectral
open EuclideanFiveColor EuclideanFiveColor.Arithmetic
variable [Carrier]

lemma reF_sum {ι : Type*} (s : Finset ι) (z : ι → E) : reF (∑ i ∈ s,z i) = ∑ i ∈ s,reF (z i) := by
  apply Subtype.ext
  simp [reF]
lemma reF_zsmul (a : ℤ) (z : E) : reF (a • z) = a • reF z := by
  apply Subtype.ext
  simp only [reF, zsmul_eq_mul]
  push_cast
  simp
lemma reF_nsmul (a : ℕ) (z : E) : reF (a • z) = a • reF z := by
  apply Subtype.ext
  simp only [reF,nsmul_eq_mul]
  push_cast
  simp

lemma selected_mass_bound (m : F → ℝ) (hm0 : m 0 = 1)
    (hd : ∀ a b : F, 0 ≤ a → 0 ≤ b → m a*m b ≤ m |a-b|)
    (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (r : F) (hr : 0 < r) {n : ℕ} (k : Fin n → E) (a b : Fin n → ℤ)
    (D M : ℕ) (hD : 0 < D) (hM : 0 < M)
    (ha : (∑ j, a j • k j) = D • (1:E))
    (hb : (∑ j, b j • k j) = D • imagUnit)
    (hab : (∑ j, ((a j).natAbs+(b j).natAbs)) ≤ M)
    (v : E) (hv : ‖(v:ℂ)‖ = 1) (hsmall : |reF v| < (M:F)⁻¹)
    (hgood : ∀ j, c ≤ m |2*r*reF (k j*v)|) :
    c^(4*M) ≤ m |2*r*D*reF v| := by
  classical
  have hac : (∑ j, a j • (k j:ℂ)) = D • (1:ℂ) := by
    have he := congrArg (fun z : E => (z:ℂ)) ha
    simpa using he
  have hbc : (∑ j, b j • (k j:ℂ)) = D • Complex.I := by
    have he := congrArg (fun z : E => (z:ℂ)) hb
    simpa [imagUnit] using he
  obtain ⟨i,hi⟩ := selection_transverse (fun j => (k j:ℂ)) a b D M hD hac hbc hab (v:ℂ) hv
  have hmax (j : Fin n) : |reF (k j*v)| ≤ |reF (k i*v)| := by
    exact_mod_cast (hi j).1
  have htrans : (D:F) ≤ (M:F)*|reF (k i*v)| := by exact_mod_cast (hi i).2
  have hDp : (0:F) < D := Nat.cast_pos.mpr hD
  have hMp : (0:F) < M := Nat.cast_pos.mpr hM
  have hip : 0 < |reF (k i*v)| := by nlinarith
  let x := fun j => 2*r*reF (k j*v)
  let p := |x i|
  have hx (j : Fin n) : |x j| = 2*r*|reF (k j*v)| := by
    dsimp [x]
    rw [abs_mul, abs_of_pos (by positivity : 0 < 2*r)]
  have hp : 0 < p := by dsimp [p]; rw [hx]; positivity
  have hsum : (∑ j, a j • x j) = 2*r*D*reF v := by
    have he := congrArg reF (congrArg (fun z : E => z*v) ha)
    simp only [Finset.sum_mul,reF_sum,smul_mul_assoc,reF_zsmul,one_mul,reF_nsmul] at he
    calc
      (∑ j, a j • x j) = 2*r * ∑ j, a j • reF (k j*v) := by
        simp only [x,Finset.mul_sum,zsmul_eq_mul]; congr 1; ext j; ring_nf
      _ = 2*r*D*reF v := by rw [he,nsmul_eq_mul]; ring
  have hz : |∑ j, a j • x j| < p := by
    rw [hsum,abs_mul,abs_of_pos (by positivity : (0:F) < 2*r*D)]
    dsimp only [p]
    rw [hx]
    have hvM : (M:F)*|reF v| < 1 := by
      have hh := mul_lt_mul_of_pos_left hsmall hMp
      rwa [mul_inv_cancel₀ hMp.ne'] at hh
    have ht : (D:F)*|reF v| < |reF (k i*v)| := by
      have hh := mul_le_mul_of_nonneg_right htrans (abs_nonneg (reF v))
      nlinarith
    nlinarith [mul_lt_mul_of_pos_left ht (by positivity : (0:F) < 2*r)]
  have hcap := CappedResidues.integer_abs_cap m hm0 hd c hc0 hc1 hp
    (by simpa only [CappedResidues.Good,p,pow_one] using hgood i)
    Finset.univ a x (fun j _ => ⟨by dsimp only [p]; rw [hx,hx]; exact mul_le_mul_of_nonneg_left (hmax j) (by positivity),
      by simpa only [CappedResidues.Good,pow_one] using hgood j⟩) hz
  have hlen : ∑ j, (a j).natAbs ≤ M := by
    calc
      _ ≤ ∑ j, ((a j).natAbs+(b j).natAbs) := Finset.sum_le_sum (fun j _ => Nat.le_add_right _ _)
      _ ≤ M := hab
  have hpow : c^(4*M) ≤ c^(4*∑ j,(a j).natAbs) :=
    pow_le_pow_of_le_one hc0 hc1 (Nat.mul_le_mul_left 4 hlen)
  exact hpow.trans (by simpa only [CappedResidues.Good,hsum] using hcap)
end PlaneFiveColor.Spectral
end

noncomputable section
namespace PlaneFiveColor.Spectral
open EuclideanFiveColor EuclideanFiveColor.Arithmetic
variable [Carrier]

lemma circle_realPart (t : F) (ht : |t| ≤ 1) :
    ∃ v : E, ‖(v:ℂ)‖ = 1 ∧ reF v = t := by
  let y := sqrtF (1-t^2)
  have hy : y^2 = 1-t^2 := sqrtF_sq _ (by have hh := sq_le_sq₀ (abs_nonneg t) zero_le_one |>.mpr ht; nlinarith [sq_abs t])
  let v := ofF t + imagUnit * ofF y
  have hv : (v:ℂ) = (t:ℝ) + Complex.I*(y:ℝ) := rfl
  refine ⟨v,?_,?_⟩
  · have hh : ‖(v:ℂ)‖^2 = 1 := by
      rw [← Complex.normSq_eq_norm_sq,hv]
      simp only [Complex.normSq_apply, Complex.add_re,Complex.add_im,Complex.mul_re,
        Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
        zero_mul,one_mul,mul_zero,sub_zero,add_zero,zero_add]
      have hyc : (y:ℝ)^2 = 1-(t:ℝ)^2 := by exact_mod_cast hy
      nlinarith
    nlinarith [norm_nonneg (v:ℂ)]
  · apply Subtype.ext
    change (v:ℂ).re = (t:ℝ)
    simp [hv]

lemma cover_mass_positive (m : F → ℝ) (hm0 : m 0 = 1)
    (hd : ∀ a b : F, 0 ≤ a → 0 ≤ b → m a*m b ≤ m |a-b|)
    (c : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (r : F) (hr : 0 < r) (Q : Finset E) (hQ : ∀ q ∈ Q, ‖(q:ℂ)‖ = 1)
    (hcover : ∀ v : E, ‖(v:ℂ)‖ = 1 → ∃ q ∈ Q, c ≤ m |2*r*reF (q*v)|) :
    ∃ δ : F, 0 < δ ∧ ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
      ∀ s : F, 0 < s → s < δ → ε ≤ m s := by
  classical
  let A : ℂ → Prop := fun w => ∃ z : E, (z:ℂ) = w ∧ c ≤ m |2*r*reF z|
  have hQN : ∀ q ∈ Q.image (fun z : E => (z:ℂ)), ‖q‖ = 1 := by
    intro q hq
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hq
    exact hQ z hz
  have hQA : ∀ q ∈ Q.image (fun z : E => (z:ℂ)), q ∈ (E : Set ℂ) := by
    intro q hq
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hq
    exact z.property
  have hA : ∀ v : ℂ, ‖v‖ = 1 → v ∈ (E : Set ℂ) → ∃ q ∈ Q.image (fun z : E => (z:ℂ)), A (q*v) := by
    intro v hv hva
    let v' : E := ⟨v,hva⟩
    obtain ⟨q,hq,hgood⟩ := hcover v' hv
    exact ⟨q,Finset.mem_image.mpr ⟨q,hq,rfl⟩,q*v',rfl,hgood⟩
  obtain ⟨D,M,hD,hM,hsel⟩ := uniform_selection_of_template _ Carrier.template
    (fun a ha b hb => E.mul_mem ha hb) _ hQN hQA A hA
  have hDp : (0:F) < D := Nat.cast_pos.mpr hD
  have hMp : (0:F) < M := Nat.cast_pos.mpr hM
  let δ : F := 2*r*D/(M+1)
  refine ⟨δ,by dsimp [δ]; positivity,c^(4*M),pow_pos hc0 _,pow_le_one₀ hc0.le hc1,?_⟩
  intro s hs hsδ
  let t := s/(2*r*D)
  have ht : 0 < t := div_pos hs (by positivity)
  have htM : t < ((M:F)+1)⁻¹ := by
    dsimp [t,δ] at *
    apply (div_lt_iff₀ (by positivity : (0:F) < 2*r*D)).mpr
    simpa only [div_eq_mul_inv,mul_comm] using hsδ
  have ht1 : |t| ≤ 1 := by
    rw [abs_of_pos ht]
    have hh : ((M:F)+1)⁻¹ ≤ 1 := (inv_le_one₀ (by positivity)).mpr (by linarith)
    exact htM.le.trans hh
  obtain ⟨v,hv,hvt⟩ := circle_realPart t ht1
  obtain ⟨n,k,a,b,hkg,ha,hb,hab⟩ := hsel (v:ℂ) hv v.property
  let k' : Fin n → E := fun j => ⟨k j,(hkg j).2.1⟩
  have ha' : (∑ j, a j • k' j) = D • (1:E) := by
    apply Subtype.ext
    simpa [k'] using ha
  have hb' : (∑ j, b j • k' j) = D • imagUnit := by
    apply Subtype.ext
    simpa [k',imagUnit] using hb
  have hgood (j : Fin n) : c ≤ m |2*r*reF (k' j*v)| := by
    obtain ⟨z,hz,hg⟩ := (hkg j).2.2
    have he : z = k' j*v := Subtype.ext hz
    rwa [he] at hg
  have hsmall : |reF v| < (M:F)⁻¹ := by
    rw [hvt,abs_of_pos ht]
    exact htM.trans (inv_lt_inv₀ (by positivity : (0:F) < M+1) hMp |>.mpr (by linarith))
  have hh := selected_mass_bound m hm0 hd c hc0.le hc1 r hr k' a b D M hD hM ha' hb' hab v hv hsmall hgood
  convert hh using 1
  have he : 2*r*(D:F)*reF v = s := by rw [hvt]; dsimp [t]; field_simp
  rw [he,abs_of_pos hs]
end PlaneFiveColor.Spectral
end

noncomputable section
open MeasureTheory ProbabilityTheory Filter EuclideanFiveColor
open scoped ENNReal NNReal ComplexConjugate BoundedContinuousFunction
namespace PlaneFiveColor.Spectral
open EuclideanFiveColor.BoundedMeasurable
variable [Carrier]
lemma kCoeff_scale_neg_one (g : Rot) :
    ((kCoeff (rotMul (scaleHom (G := Rot) (-1) g)) : E) : ℂ) = conj ((kCoeff (rotMul g) : E) : ℂ) := by
  change ((rotMul ((-1:ℤ) • g)).val : ℂ) = _
  rw [neg_one_zsmul]
  exact Circle.coe_inv_eq_conj _
lemma char_symmetric (r : F) (g : Rot) :
    (Family.orbit (scaleHom (G := Rot) 1) (char (ofF r)) *
      Family.orbit (scaleHom (G := Rot) (-1)) (char (ofF r))) g =
      char (ofF (2*r*reF (kCoeff (rotMul g)))) := by
  simp only [Family.mul_apply, Family.orbit_apply, char_act, kCoeff_scale_one, ← char_add]
  congr 1
  apply Subtype.ext
  change ((kCoeff (rotMul g) : E) : ℂ)*(r : ℝ) +
    ((kCoeff (rotMul (scaleHom (G := Rot) (-1) g)) : E) : ℂ)*(r : ℝ) =
    ((2*r*reF (kCoeff (rotMul g)) : F) : ℝ)
  rw [kCoeff_scale_neg_one]
  push_cast
  change _ = 2*(r : ℝ)*(((kCoeff (rotMul g) : E) : ℂ).re : ℂ)
  apply Complex.ext <;> simp
  ring

variable {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
variable (μ : Measure D) [IsProbabilityMeasure μ] [ErgodicSMul K D μ]
  (q : D → Y) (hq : Measurable q)
  [MulAction K Y] [MeasurableConstSMul K Y]
  (hqcov : ∀ k : K, ∀ᵐ d ∂μ, q (k • d) = k • q d)
  [ErgodicVAdd Rot (D×D) (RelativeProduct.law μ q hq)]
private def radiusFamily (r : F) : Rot →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun g => massReal μ q (2*r*reF (kCoeff (rotMul g)))) continuous_of_discreteTopology 1
    (fun g => by
      rw [Real.norm_eq_abs]
      change |projectedMass μ q (ofF _)| ≤ 1
      rw [abs_of_nonneg (projectedMass_nonneg _ _ _)]
      exact projectedMass_le_one μ q hq _)
omit [StandardBorelSpace Y] [Nonempty Y] [ErgodicSMul K D μ]
  [MulAction K Y] [MeasurableConstSMul K Y]
  [ErgodicVAdd Rot (D×D) (RelativeProduct.law μ q hq)] in
@[simp] lemma radiusFamily_apply (r : F) (g : Rot) :
    radiusFamily μ q hq r g = massReal μ q (2*r*reF (kCoeff (rotMul g))) := rfl
include hq hqcov in
lemma radiusFamily_mean (r : F) (M : Amenable.Mean Rot) :
    M.map (radiusFamily μ q hq r) = massReal μ q r ^2 := by
  haveI := Measure.isProbabilityMeasure_map (μ := μ) hq.aemeasurable
  have he : radiusFamily μ q hq r = Family.energy (μ.map q) (Family.conditional μ q
      (Family.orbit (scaleHom (G := Rot) 1) (char (ofF r)) *
        Family.orbit (scaleHom (G := Rot) (-1)) (char (ofF r)))) := by
    ext g
    simp only [radiusFamily_apply, Family.energy_apply, Family.conditional_apply, char_symmetric]
    rfl
  rw [he, conditional_integer_pair_energy μ q hq (fun g : Rot => hqcov (rotMul g))
    rot_zsmul_surjective M (by decide : (1:ℤ) ≠ -1)]
  exact (pow_two _).symm
include hq hqcov in
lemma radius_syndetic (r : F) (c : ℝ) (hc : c < massReal μ q r ^2) :
    ∃ S : Finset Rot, ∀ v : Rot, ∃ s ∈ S,
      c < massReal μ q (2*r*reF (kCoeff (rotMul (v+s)))) := by
  apply MovingMean.syndetic_of_all_means (radiusFamily μ q hq r) c
  intro M
  rwa [radiusFamily_mean μ q hq hqcov r M]
end PlaneFiveColor.Spectral
end

noncomputable section
open MeasureTheory ProbabilityTheory Filter EuclideanFiveColor
open scoped ENNReal NNReal ComplexConjugate BoundedContinuousFunction
namespace PlaneFiveColor.Spectral
open EuclideanFiveColor.BoundedMeasurable
variable [Carrier]
variable {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
variable (μ : Measure D) [IsProbabilityMeasure μ] [ErgodicSMul K D μ]
  (q : D → Y) (hq : Measurable q)
  [MulAction K Y] [MeasurableConstSMul K Y]
  (hqcov : ∀ k : K, ∀ᵐ d ∂μ, q (k • d) = k • q d)
  [ErgodicVAdd Rot (D×D) (RelativeProduct.law μ q hq)]

include hq hqcov in
lemma radial_positive_near_zero (r : F) (hr : 0 < r) (hm : massReal μ q r ≠ 0) :
    ∃ δ : F, 0 < δ ∧ ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
      ∀ s : F, 0 < s → s < δ → ε ≤ massReal μ q s := by
  classical
  let c := massReal μ q r ^2/2
  have hp : 0 < massReal μ q r := lt_of_le_of_ne (projectedMass_nonneg μ q _) (Ne.symm hm)
  have hc : 0 < c := div_pos (sq_pos_of_pos hp) (by norm_num)
  have hc1 : c ≤ 1 := by
    have h := projectedMass_le_one μ q hq (ofF r)
    change massReal μ q r ≤ 1 at h
    dsimp [c]; nlinarith
  obtain ⟨S,hS⟩ := radius_syndetic μ q hq hqcov r c (by dsimp [c]; nlinarith)
  let Q := S.image (fun s => kCoeff (rotMul s))
  apply cover_mass_positive (massReal μ q) (projectedMass_zero μ q hq)
    (massReal_difference μ q hq hqcov) c hc hc1 r hr Q
  · intro z hz
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hz
    exact Circle.norm_coe _
  · intro v hv
    let u : K := ⟨⟨(v:ℂ),mem_sphere_zero_iff_norm.mpr hv⟩,v.property⟩
    obtain ⟨s,hs,hsg⟩ := hS (mulRot u)
    refine ⟨kCoeff (rotMul s),Finset.mem_image.mpr ⟨s,hs,rfl⟩,?_⟩
    rw [massReal_abs μ q hq hqcov]
    have he : kCoeff (rotMul (mulRot u+s)) = kCoeff (rotMul s)*v := by
      change kCoeff (u*rotMul s) = _
      rw [kCoeff_mul,mul_comm]
      rfl
    rw [he] at hsg
    exact hsg.le

include hq hqcov in
lemma massReal_vanish (hw : IsWild (DifferenceFourier.differenceLaw (μ.map q) (condDistrib id q μ)))
    (r : F) (hr : 0 < r) : massReal μ q r = 0 := by
  haveI := Measure.isProbabilityMeasure_map (μ := μ) hq.aemeasurable
  by_contra hn
  obtain ⟨δ,hδ,ε,hε,hε1,hpos⟩ := radial_positive_near_zero μ q hq hqcov r hr hn
  let ν := DifferenceFourier.differenceLaw (μ.map q) (condDistrib id q μ)
  have he (t : F) : lineFourier ν 1 t = (massReal μ q t : ℂ) := by
    simpa only [ν,massReal,lineFourier_eq,one_mul] using differenceFourier_projectedMass μ q hq (ofF t)
  obtain ⟨t,ht,htδ,htε⟩ := exists_small_wild_parameter ({()} : Finset Unit) (by simp)
    ν hw (fun _ => (1:E)) (fun _ => one_ne_zero)
    (fun i t => by rw [he,Complex.ofReal_re]; exact projectedMass_nonneg μ q _)
    (show 0 < (δ:ℝ) from hδ) hε hε1
  have htest : massReal μ q t < ε := by
    have hh := htε () (by simp)
    rwa [he,Complex.ofReal_re] at hh
  have hgood := hpos |t| (abs_pos.mpr ht) (by exact_mod_cast htδ)
  rw [massReal_abs μ q hq hqcov] at hgood
  exact (not_lt_of_ge hgood) htest
end PlaneFiveColor.Spectral
end

end ParishFactor
end

namespace ParishFactor

noncomputable section
open MeasureTheory ProbabilityTheory Filter EuclideanFiveColor
open scoped ENNReal NNReal ComplexConjugate BoundedContinuousFunction
namespace PlaneFiveColor.Spectral
open EuclideanFiveColor.BoundedMeasurable
variable [Carrier]

private def normF (z : E) : F := ⟨‖(z:ℂ)‖,Carrier.norm_mem z.property⟩
@[simp] lemma normF_coe (z : E) : ((normF z : F):ℝ) = ‖(z:ℂ)‖ := rfl
lemma normF_pos {z : E} (hz : z ≠ 0) : 0 < normF z := by
  change 0 < ‖(z:ℂ)‖
  exact norm_pos_iff.mpr (fun h => hz (Subtype.ext h))

variable {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
variable (μ : Measure D) [IsProbabilityMeasure μ] [ErgodicSMul K D μ]
  (q : D → Y) (hq : Measurable q)
  [MulAction K Y] [MeasurableConstSMul K Y]
  (hqcov : ∀ k : K, ∀ᵐ d ∂μ, q (k • d) = k • q d)
  [ErgodicVAdd Rot (D×D) (RelativeProduct.law μ q hq)]
include hq hqcov in
lemma projectedMass_vanish (hw : IsWild (DifferenceFourier.differenceLaw (μ.map q) (condDistrib id q μ)))
    (z : E) (hz : z ≠ 0) : projectedMass μ q z = 0 := by
  have hn : ‖(z:ℂ)‖ = ‖((ofF (normF z):E):ℂ)‖ := by
    rw [norm_ofF,normF_coe,abs_of_nonneg (norm_nonneg _)]
  rw [projectedMass_radial μ q hq hqcov hn]
  exact massReal_vanish μ q hq hqcov hw (normF z) (normF_pos hz)

include hq hqcov in
private lemma conditional_vanish (hw : IsWild (DifferenceFourier.differenceLaw (μ.map q) (condDistrib id q μ)))
    (z : E) (hz : z ≠ 0) : ∀ᵐ w ∂μ.map q, ∫ d, (eval z d : ℂ) ∂condDistrib id q μ w = 0 := by
  have h := projectedMass_vanish μ q hq hqcov hw z hz
  change ‖l2 (μ.map q) (conditional μ q (char z))‖^2 = 0 at h
  have hn : ‖l2 (μ.map q) (conditional μ q (char z))‖ = 0 := by nlinarith
  have he := (l2_eq_iff (μ.map q) (conditional μ q (char z)) (0:Func Y)).mp
    (by rw [map_zero]; exact norm_eq_zero.mp hn)
  exact he
end PlaneFiveColor.Spectral
end
end ParishFactor

open MeasureTheory ProbabilityTheory ParishFactor.EuclideanFiveColor ParishFactor.PlaneFiveColor.Spectral

private theorem bridge (E : IntermediateField ℚ ℂ) (F : IntermediateField ℚ ℝ) (hc : Countable E)
    (hF : ∀ z : ℂ, z ∈ E ↔ z.re ∈ F ∧ z.im ∈ F)
    (ha : ∀ p : Polynomial ℂ, p ≠ 0 → (∀ n, p.coeff n ∈ E) → ∀ z, p.eval z = 0 → z ∈ E)
    (ht : ∀ Q : Finset ℂ, (∀ q ∈ Q, q ∈ E ∧ ‖q‖ = 1) →
      ∃ S : Finset ℂ, (∀ s ∈ S, s ∈ E ∧ ‖s‖ = 1) ∧
      ∀ j : ℂ → ℂ, (∀ s ∈ S, j s ∈ Q) →
        (1 : ℂ) ∈ Submodule.span ℚ ((fun s => j s*s) '' (S : Set ℂ)) ∧
        Complex.I ∈ Submodule.span ℚ ((fun s => j s*s) '' (S : Set ℂ))) :
    letI : Carrier := ⟨E,F,hc,hF,ha,ht⟩
    ∀ (μ : Measure D) [IsProbabilityMeasure μ] [ErgodicSMul K D μ]
      (Y : Type) [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
      [MulAction K Y] [MeasurableConstSMul K Y] (q : D → Y) (hq : Measurable q), (∀ k : K, ∀ᵐ x ∂μ, q (k • x) = k • q x) →
      ErgodicSMul K (D×D) (RelativeProduct.law μ q hq) →
      IsWild (DifferenceFourier.differenceLaw (μ.map q) (condDistrib id q μ)) →
      ∀ a : E, a ≠ 0 → ∀ᵐ w ∂μ.map q, ∫ d, (eval a d : ℂ) ∂condDistrib id q μ w = 0 := by
  letI : Carrier := ⟨E,F,hc,hF,ha,ht⟩
  intro μ _ _ Y _ _ _ _ _ q hq hcov hsq hw z hz
  exact conditional_vanish μ q hq hcov hw z hz

theorem OMA.solution : OMA.R_Erdos173_erdos_173_R1_H2_R1_H1_R1_H2_R1_H1_R1_H2_R1.H2 := by
  intro E F hc hF ha ht
  exact bridge E F hc hF ha ht
