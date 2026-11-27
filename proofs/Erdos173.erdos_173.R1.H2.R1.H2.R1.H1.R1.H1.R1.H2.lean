import OMAReductions.R_Erdos173_erdos_173_R1_H2_R1_H2_R1_H1_R1_H1_R1
import Mathlib
/-! Modified from Jacob Parish, plasma-ai/erdos-173@4a368a652753 and OpenAI, openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a, both Apache-2.0. -/
-- OAI.Analysis.PlaneSpectrum.Carrier
section
noncomputable section

namespace ParishOrth.PlaneFiveColor.Spectral

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
end ParishOrth.PlaneFiveColor.Spectral
end
end

-- OAI.Analysis.PlaneSpectrum.Basic
section
namespace ParishOrth

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

private def IsWild (ν : MeasureTheory.Measure D) : Prop :=
  (∀ u : K, MeasureTheory.MeasurePreserving (fun d : D => u • d) ν ν) ∧
    ν (C : Set D) = 0

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

@[simp] theorem kCoeff_inv (u : K) : kCoeff u⁻¹ = (kCoeff u)⁻¹ := by
  apply Subtype.ext
  change ((u.val)⁻¹ : Circle).val = (u.val : ℂ)⁻¹
  exact Circle.coe_inv u.val

@[simp] theorem kCoeff_ne_zero (u : K) : kCoeff u ≠ 0 := by
  intro h
  have hz : (u.val : ℂ) = 0 := congrArg (fun x : E => (x : ℂ)) h
  exact u.val.coe_ne_zero hz
end PlaneFiveColor.Spectral
end
end ParishOrth
end

-- OAI.Analysis.PlaneSpectrum.Representations
section
namespace ParishOrth

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction
end
noncomputable section
open Filter Topology
namespace EuclideanFiveColor.ContinuousVectors
variable {A H : Type*} [AddCommGroup A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative A →* unitary (H →L[ℂ] H))
private def op (a : A) : H →L[ℂ] H := U (Multiplicative.ofAdd a)
@[simp] lemma op_zero (v : H) : op U 0 v = v := by simp [op]
lemma op_add (a b : A) (v : H) : op U (a+b) v = op U a (op U b v) := by
  change ((U (Multiplicative.ofAdd a * Multiplicative.ofAdd b) : unitary _) : H →L[ℂ] H) v = _
  rw [map_mul]; rfl
lemma op_comm (a b : A) (v : H) : op U a (op U b v) = op U b (op U a v) := by
  rw [← op_add,← op_add,add_comm]
lemma norm_op (a : A) (v : H) : ‖op U a v‖ = ‖v‖ := Unitary.norm_map _ _
lemma dist_op (a : A) (v w : H) : dist (op U a v) (op U a w) = dist v w := by
  simp only [dist_eq_norm,← map_sub,norm_op]
variable [TopologicalSpace A]
private def space : Submodule ℂ H where
  carrier := {v | Tendsto (fun a => op U a v) (𝓝 0) (𝓝 v)}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw
    change Tendsto (fun a => op U a (v+w)) (𝓝 0) (𝓝 (v+w))
    simpa only [map_add] using hv.add hw
  smul_mem' := by
    intro c v hv
    change Tendsto (fun a => op U a (c • v)) (𝓝 0) (𝓝 (c • v))
    simpa only [map_smul] using hv.const_smul c
lemma mem_space (v : H) : v ∈ space U ↔ Tendsto (fun a => op U a v) (𝓝 0) (𝓝 v) := Iff.rfl
lemma isClosed_space : IsClosed (space U : Set H) := by
  apply isClosed_of_closure_subset
  intro v hv
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨w,hw,hd⟩ := Metric.mem_closure_iff.mp hv (ε/4) (by positivity)
  have ht := Metric.tendsto_nhds.mp hw (ε/2) (by positivity)
  filter_upwards [ht] with a ha
  have he : dist (op U a v) v ≤ 2 * dist v w + dist (op U a w) w := by
    calc
      _ ≤ dist (op U a v) (op U a w) + dist (op U a w) v := dist_triangle _ _ _
      _ ≤ dist (op U a v) (op U a w) + (dist (op U a w) w + dist w v) :=
        by linarith [dist_triangle (op U a w) w v]
      _ = _ := by rw [dist_op,dist_comm w v]; ring
  linarith
private instance : CompleteSpace (space U) := (isClosed_space U).completeSpace_coe
lemma op_mem (a : A) {v : H} (hv : v ∈ space U) : op U a v ∈ space U := by
  have ht := ((op U a).continuous.tendsto v).comp hv
  change Tendsto (fun z => op U z (op U a v)) (𝓝 0) (𝓝 (op U a v))
  simpa only [Function.comp_def,op_comm U a] using ht
variable [IsTopologicalAddGroup A]
lemma orbit_continuous {v : H} (hv : v ∈ space U) : Continuous (fun a => op U a v) := by
  rw [continuous_iff_continuousAt]
  intro a
  have ht0 : Tendsto (fun b : A => b-a) (𝓝 a) (𝓝 0) := by
    have hh := ((tendsto_id : Tendsto (fun b : A => b) (𝓝 a) (𝓝 a)).sub_const a)
    rw [sub_self] at hh
    exact hh
  have ht := (((op U a).continuous.tendsto v).comp hv).comp ht0
  change Tendsto (fun b => op U b v) (𝓝 a) (𝓝 (op U a v))
  convert ht using 1
  ext b
  change op U b v = op U a (op U (b-a) v)
  rw [← op_add]
  congr 1
  abel_nf
end EuclideanFiveColor.ContinuousVectors
end

noncomputable section
open MeasureTheory
open scoped ComplexConjugate InnerProductSpace
namespace EuclideanFiveColor.VectorMeasure
variable {X H : Type*} [TopologicalSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (Φ : C(X,ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H)
private def realCM (f : C(X,ℝ)) : C(X,ℂ) := ⟨fun x => (f x : ℂ),by fun_prop⟩
@[simp] lemma realCM_apply (f : C(X,ℝ)) (x : X) : realCM f x = (f x : ℂ) := rfl
@[simp] lemma realCM_add (f g : C(X,ℝ)) : realCM (f+g) = realCM f+realCM g := by ext; simp
@[simp] lemma realCM_sub (f g : C(X,ℝ)) : realCM (f-g) = realCM f-realCM g := by ext; simp
@[simp] lemma realCM_smul (c : ℝ) (f : C(X,ℝ)) : realCM (c • f) = (c:ℂ) • realCM f := by ext; simp
@[simp] lemma realCM_one : realCM (1:C(X,ℝ)) = 1 := by ext; simp
variable [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
omit [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] in
lemma real_nonneg (f : C(X,ℝ)) (hf : 0 ≤ f) : 0 ≤ (⟪v, Φ (realCM f) v⟫_ℂ).re := by
  let g : C(X,ℂ) := realCM ⟨fun x => Real.sqrt (f x),by fun_prop⟩
  have he : star g * g = realCM f := by
    ext x
    simp only [ContinuousMap.mul_apply,ContinuousMap.star_apply,realCM_apply,g,ContinuousMap.coe_mk,Complex.star_def,Complex.conj_ofReal]
    rw [← Complex.ofReal_mul]
    exact congrArg Complex.ofReal (Real.mul_self_sqrt (show 0 ≤ f x from hf x))
  rw [← he,map_mul,map_star]
  change 0 ≤ (⟪v, (star (Φ g)) ((Φ g) v)⟫_ℂ).re
  rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
  exact inner_self_nonneg (𝕜 := ℂ) (x := (Φ g) v)

private def functional : CompactlySupportedContinuousMap X ℝ →ₚ[ℝ] ℝ where
  toFun f := (⟪v,Φ (realCM f.toContinuousMap) v⟫_ℂ).re
  map_add' f g := by
    change (⟪v,Φ (realCM (f.toContinuousMap+g.toContinuousMap)) v⟫_ℂ).re = _
    simp
  map_smul' c f := by
    change (⟪v,Φ (realCM (c • f.toContinuousMap)) v⟫_ℂ).re = c * _
    rw [realCM_smul,map_smul]
    simp only [FunLike.coe_smul,Pi.smul_apply,inner_smul_right,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  monotone' f g hfg := by
    have he := real_nonneg Φ v (g.toContinuousMap-f.toContinuousMap) (sub_nonneg.mpr hfg)
    simpa [inner_sub_right] using he

private def measure : Measure X := RealRMK.rieszMeasure (functional Φ v)
private instance : IsFiniteMeasure (measure Φ v) := by dsimp [measure]; infer_instance
private instance : (measure Φ v).Regular := by dsimp [measure]; infer_instance
lemma integral_real (f : C(X,ℝ)) : ∫ x, f x ∂measure Φ v = (⟪v,Φ (realCM f) v⟫_ℂ).re := by
  exact RealRMK.integral_rieszMeasure (functional Φ v) (CompactlySupportedContinuousMap.continuousMapEquiv f)
lemma integral_complex (f : C(X,ℂ)) : ∫ x, f x ∂measure Φ v = ⟪v,Φ f v⟫_ℂ := by
  let fr : C(X,ℝ) := ⟨fun x => (f x).re,by fun_prop⟩
  let fi : C(X,ℝ) := ⟨fun x => (f x).im,by fun_prop⟩
  have he : f = realCM fr + Complex.I • realCM fi := by
    ext x
    simpa [fr,fi,smul_eq_mul,mul_comm] using (Complex.re_add_im (f x)).symm
  have hi_real (g : C(X,ℝ)) : (⟪v,Φ (realCM g) v⟫_ℂ).im = 0 := by
    have hs : star (Φ (realCM g)) = Φ (realCM g) := by
      rw [← map_star]; congr 1; ext x; simp
    have ht := inner_conj_symm (𝕜 := ℂ) v (Φ (realCM g) v)
    rw [← ContinuousLinearMap.adjoint_inner_right,← ContinuousLinearMap.star_eq_adjoint,hs] at ht
    have hh := congrArg Complex.im ht
    simp only [Complex.conj_im] at hh
    linarith
  have hb (g : C(X,ℝ)) : ∫ x, (g x : ℂ) ∂measure Φ v = ⟪v,Φ (realCM g) v⟫_ℂ := by
    rw [integral_complex_ofReal,integral_real]
    exact Complex.ext (by simp) (by simp [hi_real])
  rw [he,map_add,map_smul]
  simp only [ContinuousMap.add_apply,ContinuousMap.smul_apply,realCM_apply,add_apply,
    smul_apply,inner_add_right,inner_smul_right]
  have hir : Integrable (fun x => (fr x : ℂ)) (measure Φ v) :=
    (Complex.continuous_ofReal.comp fr.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hii : Integrable (fun x => (fi x : ℂ)) (measure Φ v) :=
    (Complex.continuous_ofReal.comp fi.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc
    _ = (∫ x, (fr x : ℂ) ∂measure Φ v) +
        (∫ x, Complex.I • (fi x : ℂ) ∂measure Φ v) := integral_add hir (hii.smul Complex.I)
    _ = _ := by rw [integral_smul,hb,hb]; rfl
lemma measure_univ : (measure Φ v).real Set.univ = ‖v‖^2 := by
  have he := integral_real Φ v (1:C(X,ℝ))
  simp only [ContinuousMap.one_apply,integral_const,smul_eq_mul,mul_one,realCM_one,map_one,one_apply_eq_self] at he
  exact he.trans (inner_self_eq_norm_sq (𝕜 := ℂ) v)
end EuclideanFiveColor.VectorMeasure
end

end ParishOrth
end

-- OAI.Analysis.PlaneSpectrum.SpectralMeasure
section
namespace ParishOrth

noncomputable section
open scoped ComplexConjugate IsMulCommutative
namespace EuclideanFiveColor.CommutingSpectral
variable {G H : Type*} [CommGroup G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : G →* unitary (H →L[ℂ] H))
private abbrev algebra : StarSubalgebra ℂ (H →L[ℂ] H) :=
  (StarAlgebra.adjoin ℂ (Set.range (fun g => (U g : H →L[ℂ] H)))).topologicalClosure
private instance algebra_closed : IsClosed (algebra U : Set (H →L[ℂ] H)) :=
  StarSubalgebra.isClosed_topologicalClosure _
set_option synthInstance.maxHeartbeats 80000 in
lemma adjoin_comm : IsMulCommutative (StarAlgebra.adjoin ℂ (Set.range (fun g => (U g : H →L[ℂ] H)))) := by
  apply StarAlgebra.isMulCommutative_adjoin
  · rintro _ ⟨left,rfl⟩ _ ⟨right,rfl⟩
    change ((U left * U right : unitary _) : H →L[ℂ] H) = ((U right * U left : unitary _) : H →L[ℂ] H)
    rw [← map_mul,← map_mul,mul_comm]
  · rintro _ ⟨left,rfl⟩ _ ⟨right,rfl⟩
    change ((U left * (U right)⁻¹ : unitary _) : H →L[ℂ] H) = (((U right)⁻¹ * U left : unitary _) : H →L[ℂ] H)
    rw [← map_inv,← map_mul,← map_mul,mul_comm]
open scoped IsMulCommutative in
private instance algebra_commRing : CommRing (algebra U) :=
  let := adjoin_comm U
  StarSubalgebra.commRingTopologicalClosure _ mul_comm
private instance algebra_commCStar : CommCStarAlgebra (algebra U) where

private def generator (g : G) : algebra U :=
  ⟨U g,StarSubalgebra.le_topologicalClosure _ (StarAlgebra.subset_adjoin ℂ _ (Set.mem_range_self g))⟩
@[simp] lemma generator_one : generator U 1 = 1 := by ext; simp [generator]
@[simp] lemma generator_mul (g h : G) : generator U (g*h) = generator U g * generator U h := by
  apply Subtype.ext; change (U (g*h) : H →L[ℂ] H) = (U g : H →L[ℂ] H) * U h
  rw [map_mul]; rfl
lemma generator_unitary (g : G) : generator U g ∈ unitary (algebra U) := by
  constructor <;> apply Subtype.ext
  · exact (U g).property.1
  · exact (U g).property.2
variable [TopologicalSpace G] [DiscreteTopology G]
private abbrev Spectrum := WeakDual.characterSpace ℂ (algebra U)
private def character (φ : Spectrum U) : PontryaginDual G where
  toFun g := ⟨gelfandStarTransform (algebra U) (generator U g) φ, by
    change gelfandStarTransform (algebra U) (generator U g) φ ∈ Metric.sphere (0:ℂ) 1
    rw [Metric.mem_sphere, dist_zero_right]
    apply CStarRing.norm_of_mem_unitary
    exact Unitary.map_mem ((ContinuousMap.evalStarAlgHom ℂ ℂ φ).comp
      (gelfandStarTransform (algebra U)).toStarAlgHom) (generator_unitary U g)⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' g h := by
    apply Subtype.ext
    change _ = (gelfandStarTransform (algebra U) (generator U g) φ) *
      (gelfandStarTransform (algebra U) (generator U h) φ)
    simp
  continuous_toFun := continuous_of_discreteTopology
lemma character_apply (φ : Spectrum U) (g : G) :
    (character U φ g : ℂ) = gelfandStarTransform (algebra U) (generator U g) φ := rfl
lemma character_continuous : Continuous (character U) := by
  apply ContinuousMonoidHom.isClosedEmbedding_coe.isEmbedding.isInducing.continuous_iff.mpr
  apply continuous_pi; intro g
  exact Continuous.subtype_mk (map_continuous (gelfandStarTransform (algebra U) (generator U g))) _
private def calculus : C(PontryaginDual G,ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  (algebra U).subtype.comp <| (gelfandStarTransform (algebra U)).symm.toStarAlgHom.comp
    (ContinuousMap.compStarAlgHom' ℂ ℂ ⟨character U,character_continuous U⟩)
private def evaluation (g : G) : C(PontryaginDual G,ℂ) :=
  ⟨fun d => (d g : ℂ),continuous_subtype_val.comp ((continuous_apply g).comp ContinuousMonoidHom.isClosedEmbedding_coe.continuous)⟩
lemma calculus_evaluation (g : G) : calculus U (evaluation g) = U g := by
  change ((gelfandStarTransform (algebra U)).symm ((evaluation g).comp ⟨character U,character_continuous U⟩) : H →L[ℂ] H) = U g
  have he : (evaluation g).comp ⟨character U,character_continuous U⟩ =
      gelfandStarTransform (algebra U) (generator U g) := by ext φ; rfl
  rw [he,StarAlgEquiv.symm_apply_apply]; rfl
end EuclideanFiveColor.CommutingSpectral
end

noncomputable section
open MeasureTheory
open scoped ComplexConjugate
namespace EuclideanFiveColor.CommutingSpectral
variable {G : Type*} [CommGroup G] [TopologicalSpace G] [DiscreteTopology G]
lemma evaluation_one : evaluation (1:G) = 1 := by
  ext d
  change (d 1 : ℂ) = 1
  rw [map_one]; rfl
lemma evaluation_mul (g h : G) : evaluation (g*h) = evaluation g * evaluation h := by
  ext d
  change (d (g*h) : ℂ) = (d g : ℂ)*(d h : ℂ)
  rw [map_mul]; rfl
lemma star_evaluation (g : G) : star (evaluation g) = evaluation g⁻¹ := by
  ext d
  change star (d g : ℂ) = (d g⁻¹ : ℂ)
  rw [map_inv]
  exact (Circle.coe_inv_eq_conj (d g)).symm
private def evaluationHom : G →* C(PontryaginDual G,ℂ) where
  toFun := evaluation
  map_one' := evaluation_one
  map_mul' := evaluation_mul
lemma evaluation_span_dense : Dense (Submodule.span ℂ (Set.range (evaluation (G := G))) : Set C(PontryaginDual G,ℂ)) := by
  let A := StarAlgebra.adjoin ℂ (Set.range (evaluation (G := G)))
  have hs : star (Set.range (evaluation (G := G))) = Set.range (evaluation (G := G)) := by
    ext f
    rw [Set.mem_star]
    constructor
    · rintro ⟨g,hg⟩
      refine ⟨g⁻¹,?_⟩
      rw [← star_evaluation,hg,star_star]
    · rintro ⟨g,rfl⟩
      exact ⟨g⁻¹,(star_evaluation g).symm⟩
  have he : A.toSubalgebra.toSubmodule = Submodule.span ℂ (Set.range (evaluation (G := G))) := by
    rw [StarAlgebra.adjoin_eq_span,hs,Set.union_self]
    have hc : Submonoid.closure (Set.range (evaluation (G := G))) = MonoidHom.mrange (evaluationHom (G := G)) :=
      Submonoid.closure_eq (MonoidHom.mrange (evaluationHom (G := G)))
    rw [hc]
    rfl
  have hsep : A.SeparatesPoints := by
    intro d e hde
    have hn : ∃ g, d g ≠ e g := by
      by_contra! h
      exact hde (DFunLike.ext _ _ h)
    obtain ⟨g,hg⟩ := hn
    refine ⟨evaluation g,⟨evaluation g,StarAlgebra.subset_adjoin ℂ _ (Set.mem_range_self g),rfl⟩,?_⟩
    change (d g : ℂ) ≠ (e g : ℂ)
    exact fun h => hg (Subtype.ext h)
  have ht := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints A hsep
  rw [dense_iff_closure_eq,← he]
  change closure (A:Set C(PontryaginDual G,ℂ)) = _
  rw [← StarSubalgebra.topologicalClosure_coe,ht]
  rfl
end EuclideanFiveColor.CommutingSpectral
namespace EuclideanFiveColor.CompactIntegral
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  (μ : Measure X) [IsFiniteMeasure μ]
lemma integrableCM (f : C(X,ℂ)) : Integrable (f : X → ℂ) μ :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
private def linear : C(X,ℂ) →ₗ[ℂ] ℂ where
  toFun f := ∫ x, f x ∂μ
  map_add' f g := integral_add (integrableCM μ f) (integrableCM μ g)
  map_smul' c f := integral_smul c f
lemma norm_le (f : C(X,ℂ)) : ‖linear μ f‖ ≤ μ.real Set.univ * ‖f‖ := by
  simpa only [linear,LinearMap.coe_mk,AddHom.coe_mk,mul_comm] using
    norm_integral_le_of_norm_le_const (μ := μ) (Filter.Eventually.of_forall (ContinuousMap.norm_coe_le_norm f))
private def clm : C(X,ℂ) →L[ℂ] ℂ := (linear μ).mkContinuous (μ.real Set.univ) (norm_le μ)
lemma apply_clm (f : C(X,ℂ)) : clm μ f = ∫ x, f x ∂μ := rfl
end EuclideanFiveColor.CompactIntegral
namespace EuclideanFiveColor.CommutingSpectral
variable {G : Type*} [CommGroup G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)]
lemma measure_eq_of_fourier (μ ν : Measure (PontryaginDual G)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [μ.Regular] [ν.Regular]
    (h : ∀ g, ∫ d, (d g : ℂ) ∂μ = ∫ d, (d g : ℂ) ∂ν) : μ = ν := by
  have he : CompactIntegral.clm μ = CompactIntegral.clm ν := by
    apply ContinuousLinearMap.ext_on evaluation_span_dense
    rintro _ ⟨g,rfl⟩
    exact h g
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  let fc : C(PontryaginDual G,ℂ) := ⟨fun d => (f d : ℂ),by fun_prop⟩
  have hh := congrArg (fun L : C(PontryaginDual G,ℂ) →L[ℂ] ℂ => (L fc).re) he
  simpa only [CompactIntegral.apply_clm,fc,ContinuousMap.coe_mk,integral_complex_ofReal,Complex.ofReal_re] using hh
end EuclideanFiveColor.CommutingSpectral
end

end ParishOrth
end

-- OAI.Analysis.PlaneSpectrum.ConditionalSpectrum
section
namespace ParishOrth

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
end PlaneFiveColor.Spectral
end
end ParishOrth
end

namespace ParishOrth

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

end EuclideanFiveColor.BoundedMeasurable

end

end ParishOrth
namespace ParishOrth

noncomputable section
open MeasureTheory
open scoped InnerProductSpace ComplexConjugate
namespace EuclideanFiveColor.VectorMeasure
variable {X H : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (Φ : C(X,ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H)
lemma inner_toLp (f g : C(X,ℂ)) :
    ⟪ContinuousMap.toLp 2 (measure Φ v) ℂ f, ContinuousMap.toLp 2 (measure Φ v) ℂ g⟫_ℂ =
      ⟪Φ f v,Φ g v⟫_ℂ := by
  rw [L2.inner_def]
  calc
    _ = ∫ x, (star f*g) x ∂measure Φ v := by
      apply integral_congr_ae
      filter_upwards [ContinuousMap.coeFn_toLp (μ := measure Φ v) (p := 2) (𝕜 := ℂ) f,
        ContinuousMap.coeFn_toLp (μ := measure Φ v) (p := 2) (𝕜 := ℂ) g] with x hx hy
      simp only [hx,hy,RCLike.inner_apply,ContinuousMap.mul_apply,ContinuousMap.star_apply,Complex.star_def]
      ring
    _ = ⟪v,Φ (star f*g) v⟫_ℂ := integral_complex Φ v _
    _ = _ := by
      rw [map_mul,map_star]
      change ⟪v,star (Φ f) (Φ g v)⟫_ℂ = _
      rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
private def vectorLinear : C(X,ℂ) →ₗ[ℂ] H where
  toFun f := Φ f v
  map_add' f g := by simp
  map_smul' c f := by simp
lemma norm_toLp (f : C(X,ℂ)) :
    ‖ContinuousMap.toLp 2 (measure Φ v) ℂ f‖ = ‖vectorLinear Φ v f‖ := by
  have he := congrArg Complex.re (inner_toLp Φ v f f)
  change RCLike.re (⟪ContinuousMap.toLp 2 (measure Φ v) ℂ f,ContinuousMap.toLp 2 (measure Φ v) ℂ f⟫_ℂ) =
    RCLike.re (⟪Φ f v,Φ f v⟫_ℂ) at he
  rw [inner_self_eq_norm_sq,inner_self_eq_norm_sq] at he
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp he
private def cyclicMap : Lp ℂ 2 (measure Φ v) →L[ℂ] H :=
  (vectorLinear Φ v).extendOfNorm (ContinuousMap.toLp 2 (measure Φ v) ℂ).toLinearMap
lemma cyclicMap_toLp (f : C(X,ℂ)) :
    cyclicMap Φ v (ContinuousMap.toLp 2 (measure Φ v) ℂ f) = Φ f v := by
  apply LinearMap.extendOfNorm_eq
  · exact ContinuousMap.toLp_denseRange (E := ℂ) (p := 2) (μ := measure Φ v) (𝕜 := ℂ) (by norm_num)
  · exact ⟨1,fun g => by simp only [one_mul]; exact le_of_eq (norm_toLp Φ v g).symm⟩
lemma norm_cyclicMap (f : Lp ℂ 2 (measure Φ v)) : ‖cyclicMap Φ v f‖ = ‖f‖ := by
  refine (ContinuousMap.toLp_denseRange (E := ℂ) (p := 2) (μ := measure Φ v) (𝕜 := ℂ) (by norm_num)).induction
    (fun y hy => ?_) (isClosed_eq (by fun_prop) (by fun_prop)) f
  obtain ⟨g,rfl⟩ := hy
  rw [cyclicMap_toLp]
  exact (norm_toLp Φ v g).symm
private def cyclicIsometry : Lp ℂ 2 (measure Φ v) →ₗᵢ[ℂ] H :=
  ⟨(cyclicMap Φ v).toLinearMap,norm_cyclicMap Φ v⟩
end EuclideanFiveColor.VectorMeasure
end

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace EuclideanFiveColor.BoundedMeasurable
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
private def mulLp (f : Func X) (g : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  ((Lp.memLp g).mul' (r:=2) (memLp μ f ∞)).toLp (fun point => f point * g point)
lemma mulLp_ae (f : Func X) (g : Lp ℂ 2 μ) :
    mulLp μ f g =ᵐ[μ] fun x => f x * g x := MemLp.coeFn_toLp _
private def mulLpLinear (f : Func X) : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ where
  toFun := mulLp μ f
  map_add' g h := by
    apply Lp.ext
    filter_upwards [mulLp_ae μ f (g+h),mulLp_ae μ f g,mulLp_ae μ f h,
      Lp.coeFn_add g h,Lp.coeFn_add (mulLp μ f g) (mulLp μ f h)] with x ha hb hc hd he
    simp only [ha,he,Pi.add_apply,hb,hc,hd]
    exact mul_add _ _ _
  map_smul' c g := by
    apply Lp.ext
    filter_upwards [mulLp_ae μ f (c • g),mulLp_ae μ f g,
      Lp.coeFn_smul c g,Lp.coeFn_smul c (mulLp μ f g)] with x ha hb hc hd
    simp only [RingHom.id_apply,ha,hd,Pi.smul_apply,hb,hc,smul_eq_mul]
    ring
lemma mulLp_norm_le (f : Func X) (g : Lp ℂ 2 μ) {C : ℝ} (hf : ∀ x, ‖f x‖ ≤ C) :
    ‖mulLp μ f g‖ ≤ C * ‖g‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [mulLp_ae μ f g] with x hx
  rw [hx,norm_mul]
  exact mul_le_mul_of_nonneg_right (hf x) (norm_nonneg _)
private def mulLpCLM (f : Func X) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (mulLpLinear μ f).mkContinuous (bound f) (fun g => mulLp_norm_le μ f g (norm_le_bound f))
lemma mulLpCLM_ae (f : Func X) (g : Lp ℂ 2 μ) :
    mulLpCLM μ f g =ᵐ[μ] fun x => f x * g x := mulLp_ae μ f g
lemma mulLp_l2 (f g : Func X) : mulLpCLM μ f (l2 μ g) = l2 μ (f*g) := by
  apply Lp.ext
  filter_upwards [mulLpCLM_ae μ f (l2 μ g),l2_ae μ g,l2_ae μ (f*g)] with x hx hy hz
  rw [hx,hy,hz]; rfl
end EuclideanFiveColor.BoundedMeasurable
end
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal InnerProductSpace
namespace EuclideanFiveColor.VectorMeasure
open BoundedMeasurable
variable {X H : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (Φ : C(X,ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H)
private def boundedCM (f : C(X,ℂ)) : Func X :=
  ⟨f,f.continuous.measurable,‖f‖₊,fun x => ContinuousMap.norm_coe_le_norm f x⟩
omit [T2Space X] in
@[simp] lemma boundedCM_apply (f : C(X,ℂ)) (x : X) : boundedCM f x = f x := rfl
omit [T2Space X] in
lemma boundedCM_toLp (μ : Measure X) [IsFiniteMeasure μ] (f : C(X,ℂ)) :
    l2 μ (boundedCM f) = ContinuousMap.toLp 2 μ ℂ f := by
  apply Lp.ext
  exact (l2_ae μ _).trans (ContinuousMap.coeFn_toLp (μ := μ) (p := 2) (𝕜 := ℂ) f).symm
lemma mulCM_toLp (f g : C(X,ℂ)) :
    mulLpCLM (measure Φ v) (boundedCM f) (ContinuousMap.toLp 2 (measure Φ v) ℂ g) =
      ContinuousMap.toLp 2 (measure Φ v) ℂ (f*g) := by
  rw [← boundedCM_toLp,← boundedCM_toLp,mulLp_l2]
  congr 1
lemma cyclicMap_mul (f : C(X,ℂ)) (g : Lp ℂ 2 (measure Φ v)) :
    cyclicMap Φ v (mulLpCLM (measure Φ v) (boundedCM f) g) = Φ f (cyclicMap Φ v g) := by
  refine (ContinuousMap.toLp_denseRange (E := ℂ) (p := 2) (μ := measure Φ v) (𝕜 := ℂ) (by norm_num)).induction
    (fun y hy => ?_) (isClosed_eq (by fun_prop) (by fun_prop)) g
  obtain ⟨h,rfl⟩ := hy
  rw [mulCM_toLp,cyclicMap_toLp,cyclicMap_toLp,map_mul]
  rfl
lemma cyclicMap_one : cyclicMap Φ v (l2 (measure Φ v) (1:Func X)) = v := by
  have he : (1:Func X) = boundedCM (1:C(X,ℂ)) := rfl
  rw [he,boundedCM_toLp,cyclicMap_toLp,map_one]
  rfl
lemma cyclicMap_inner (f g : Lp ℂ 2 (measure Φ v)) :
    ⟪cyclicMap Φ v f,cyclicMap Φ v g⟫_ℂ = ⟪f,g⟫_ℂ :=
  (cyclicIsometry Φ v).inner_map_map f g
lemma cyclicMap_pair_one (f : Func X) :
    ⟪v,cyclicMap Φ v (l2 (measure Φ v) f)⟫_ℂ = ∫ x, f x ∂measure Φ v := by
  nth_rw 1 [← cyclicMap_one Φ v]
  rw [cyclicMap_inner,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [l2_ae (measure Φ v) (1:Func X),l2_ae (measure Φ v) f] with x hx hy
  simp only [hx,hy,one_apply,RCLike.inner_apply,map_one,mul_one]
end EuclideanFiveColor.VectorMeasure
end

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
namespace PlaneFiveColor.Spectral
open EuclideanFiveColor EuclideanFiveColor.BoundedMeasurable
open EuclideanFiveColor.VectorMeasure EuclideanFiveColor.CommutingSpectral
variable [Carrier]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : DiscreteE →* unitary (H →L[ℂ] H)) (v : H)
private def ordinaryIndicator : Func D :=
  ⟨(C:Set D).indicator (fun _ => (1:ℂ)),measurable_const.indicator measurableSet_C,
    1,fun d => by by_cases hd : d ∈ C <;> simp [Set.indicator_of_mem,Set.indicator_of_notMem,hd]⟩
lemma ordinaryIndicator_apply (d : D) : ordinaryIndicator d = (C:Set D).indicator (fun _ => (1:ℂ)) d := rfl
lemma ordinary_eval_continuous {d : D} (hd : d ∈ C) :
    Continuous (fun z : E => (eval z d : ℂ)) := by
  obtain ⟨ξ,rfl⟩ := hd
  change Continuous (fun z : E => (Circle.exp (inner ℝ (Multiplicative.toAdd ξ) (z:ℂ)) : ℂ))
  fun_prop
lemma ordinary_difference_tendsto (μ : Measure D) [IsFiniteMeasure μ] :
    Tendsto (fun z : E => ∫ d, ‖((eval z d : ℂ)-1)*ordinaryIndicator d‖^2 ∂μ)
      (𝓝 0) (𝓝 0) := by
  have hm (z : E) : Measurable (fun d => ‖((eval z d : ℂ)-1)*ordinaryIndicator d‖^2) := by
    have he : Measurable (fun d : D => (eval z d : ℂ)) := (evaluation (G := DiscreteE) (Multiplicative.ofAdd z)).continuous.measurable
    exact ((he.sub measurable_const).mul (measurable ordinaryIndicator)).norm.pow_const 2
  have hb (z : E) (d : D) : ‖‖((eval z d : ℂ)-1)*ordinaryIndicator d‖^2‖ ≤ (4:ℝ) := by
    have hi : ‖ordinaryIndicator d‖ ≤ 1 := by
      by_cases hd : d ∈ C <;> simp [ordinaryIndicator_apply,hd]
    have he : ‖(eval z d : ℂ)-1‖ ≤ 2 := by
      calc
        _ ≤ ‖(eval z d : ℂ)‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [Circle.norm_coe, norm_one]; norm_num
    have hn : ‖((eval z d : ℂ)-1)*ordinaryIndicator d‖ ≤ 2 := by
      rw [norm_mul]
      exact (mul_le_mul he hi (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
    rw [Real.norm_eq_abs,abs_sq]
    nlinarith [norm_nonneg (((eval z d:ℂ)-1)*ordinaryIndicator d)]
  have hl (d : D) : Tendsto (fun z : E => ‖((eval z d : ℂ)-1)*ordinaryIndicator d‖^2)
      (𝓝 0) (𝓝 (0:ℝ)) := by
    by_cases hd : d ∈ C
    · have he := ((ordinary_eval_continuous hd).tendsto (0:E)).sub_const (1:ℂ)
      have ht := (he.mul_const (ordinaryIndicator d)).norm.pow 2
      have hz : (eval (0:E) d : ℂ) = 1 := by
        change (d 1 : ℂ) = 1
        rw [map_one]; rfl
      simpa only [hz,sub_self,zero_mul,norm_zero,zero_pow (by decide : 2 ≠ 0)] using ht
    · simp only [ordinaryIndicator_apply,Set.indicator_of_notMem hd,mul_zero,norm_zero,zero_pow (by decide : 2 ≠ 0)]
      exact tendsto_const_nhds
  have ht := tendsto_integral_filter_of_dominated_convergence (μ := μ) (fun _ : D => (4:ℝ))
    (Filter.Eventually.of_forall (fun z : E => (hm z).aestronglyMeasurable))
    (Filter.Eventually.of_forall (fun z : E => Filter.Eventually.of_forall (hb z)))
    (integrable_const (4:ℝ)) (Filter.Eventually.of_forall hl)
  simpa only [integral_zero] using ht

private def ordinaryVector : H := cyclicMap (calculus U) v (l2 (measure (calculus U) v) ordinaryIndicator)
lemma ordinaryVector_continuous : ordinaryVector U v ∈ ContinuousVectors.space U := by
  let μ := measure (calculus U) v
  have he (z : E) : ContinuousVectors.op U z (ordinaryVector U v) - ordinaryVector U v =
      cyclicMap (calculus U) v (l2 μ ((boundedCM (evaluation (G := DiscreteE) (Multiplicative.ofAdd z))-1)*ordinaryIndicator)) := by
    dsimp [ordinaryVector,μ]
    rw [sub_mul,map_sub,one_mul,map_sub]
    rw [← mulLp_l2,cyclicMap_mul]
    rw [calculus_evaluation U (Multiplicative.ofAdd z : DiscreteE)]
    rfl
  have hn (z : E) : ‖ContinuousVectors.op U z (ordinaryVector U v) - ordinaryVector U v‖^2 =
      ∫ d, ‖((eval z d:ℂ)-1)*ordinaryIndicator d‖^2 ∂μ := by
    rw [he]
    change ‖cyclicIsometry (calculus U) v _‖^2 = _
    rw [LinearIsometry.norm_map,norm_l2_sq]
    rfl
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht := Real.continuous_sqrt.tendsto (0:ℝ) |>.comp (ordinary_difference_tendsto μ)
  simpa only [Function.comp_def,← hn,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using ht
lemma measure_ordinary_zero_of_orthogonal (hv : v ∈ (ContinuousVectors.space U)ᗮ) :
    measure (calculus U) v (C:Set D) = 0 := by
  have ho := (Submodule.mem_orthogonal' _ _).mp hv (ordinaryVector U v) (ordinaryVector_continuous U v)
  have hp := cyclicMap_pair_one (calculus U) v ordinaryIndicator
  change ⟪v,ordinaryVector U v⟫_ℂ = _ at hp
  rw [ho] at hp
  have hz : (measure (calculus U) v).real (C:Set D) = 0 := by
    have := congrArg Complex.re hp
    simpa only [ordinaryIndicator_apply,integral_indicator measurableSet_C,integral_const,
      Measure.restrict_apply_univ,Complex.real_smul, smul_eq_mul,mul_one,Complex.zero_re,Complex.ofReal_re,Measure.real] using this.symm
  exact (ENNReal.toReal_eq_zero_iff _).mp hz |>.resolve_right (measure_ne_top _ _)
end PlaneFiveColor.Spectral
end
end ParishOrth

open MeasureTheory ParishOrth.PlaneFiveColor.Spectral ParishOrth.EuclideanFiveColor
set_option maxHeartbeats 2400000 in
theorem OMA.solution : OMA.R_Erdos173_erdos_173_R1_H2_R1_H2_R1_H1_R1_H1_R1.H2 := by
  intro E F hc hF ha ht H hN hI hC U v hv
  letI : Carrier := ⟨E,F,hc,hF,ha,ht⟩
  exact measure_ordinary_zero_of_orthogonal U v hv
