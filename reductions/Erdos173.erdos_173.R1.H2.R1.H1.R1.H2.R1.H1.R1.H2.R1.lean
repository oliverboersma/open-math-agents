import OMAReductions.R_Erdos173_erdos_173_R1_H2_R1_H1_R1_H2_R1_H1_R1
/-! Conditional Fourier coefficients on a terminal factor of an ergodic action.
Adapted from Jacob Parish, plasma-ai/erdos-173@4a368a652753, and OpenAI,
openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a, both Apache-2.0. -/
-- OAI.Analysis.PlaneSpectrum.Carrier
section
noncomputable section

namespace ParishRigid.PlaneFiveColor.Spectral

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
end ParishRigid.PlaneFiveColor.Spectral
end
end

-- OAI.Analysis.PlaneSpectrum.Basic
section
namespace ParishRigid

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
end ParishRigid
end
section
namespace ParishRigid

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
end ParishRigid
end

noncomputable section
namespace OMA.R_Erdos173_erdos_173_R1_H2_R1_H1_R1_H2_R1_H1_R1_H2_R1
open MeasureTheory ProbabilityTheory ParishRigid.PlaneFiveColor.Spectral

private instance [Carrier] : Countable K := by
  apply Function.Injective.countable (f := kCoeff)
  intro x y h
  exact Subtype.ext (Subtype.ext (congrArg (fun z : E => (z : ℂ)) h))

private def difference [Carrier] {Y : Type} [MeasurableSpace Y] (μ : Measure D) [IsProbabilityMeasure μ] (q : D → Y) : Measure D :=
  let κ := condDistrib id q μ
  ((κ ×ₖ κ) ∘ₘ μ.map q).map (fun z : D × D => z.1 / z.2)

private def square [Carrier] {Y : Type} [MeasurableSpace Y] (μ : Measure D) [IsProbabilityMeasure μ]
    (q : D → Y) (hq : Measurable q) : Measure (D×D) :=
  μ ⊗ₘ (condDistrib id q μ).comap q hq

/-- Existence of a rotation factor with an ergodic relative square and wild conditional differences. -/
def H1 : Prop := ∀ (E : IntermediateField ℚ ℂ) (F : IntermediateField ℚ ℝ), ∀ hc : Countable E,
    ∀ hF : (∀ z : ℂ, z ∈ E ↔ z.re ∈ F ∧ z.im ∈ F),
    ∀ ha : (∀ p : Polynomial ℂ, p ≠ 0 → (∀ n, p.coeff n ∈ E) → ∀ z, p.eval z = 0 → z ∈ E),
    ∀ ht : (∀ Q : Finset ℂ, (∀ q ∈ Q, q ∈ E ∧ ‖q‖ = 1) →
      ∃ S : Finset ℂ, (∀ s ∈ S, s ∈ E ∧ ‖s‖ = 1) ∧
      ∀ j : ℂ → ℂ, (∀ s ∈ S, j s ∈ Q) →
        (1 : ℂ) ∈ Submodule.span ℚ ((fun s => j s*s) '' (S : Set ℂ)) ∧
        Complex.I ∈ Submodule.span ℚ ((fun s => j s*s) '' (S : Set ℂ))),
    letI : Carrier := ⟨E,F,hc,hF,ha,ht⟩

    ∀ (μ : Measure D) [IsProbabilityMeasure μ] [ErgodicSMul K D μ], IsWild μ →
      ∃ (Y : Type) (mY : MeasurableSpace Y) (aY : MulAction K Y),
        letI := mY
        letI := aY
        StandardBorelSpace Y ∧ Nonempty Y ∧ MeasurableConstSMul K Y ∧ ∃ (q : D → Y) (hq : Measurable q),
        (∀ k : K, ∀ᵐ x ∂μ, q (k • x) = k • q x) ∧
        ErgodicSMul K (D×D) (square μ q hq) ∧ IsWild (difference μ q)

/-- Vanishing of each nontrivial conditional Fourier coefficient on such a factor. -/
def H2 : Prop := ∀ (E : IntermediateField ℚ ℂ) (F : IntermediateField ℚ ℝ), ∀ hc : Countable E,
    ∀ hF : (∀ z : ℂ, z ∈ E ↔ z.re ∈ F ∧ z.im ∈ F),
    ∀ ha : (∀ p : Polynomial ℂ, p ≠ 0 → (∀ n, p.coeff n ∈ E) → ∀ z, p.eval z = 0 → z ∈ E),
    ∀ ht : (∀ Q : Finset ℂ, (∀ q ∈ Q, q ∈ E ∧ ‖q‖ = 1) →
      ∃ S : Finset ℂ, (∀ s ∈ S, s ∈ E ∧ ‖s‖ = 1) ∧
      ∀ j : ℂ → ℂ, (∀ s ∈ S, j s ∈ Q) →
        (1 : ℂ) ∈ Submodule.span ℚ ((fun s => j s*s) '' (S : Set ℂ)) ∧
        Complex.I ∈ Submodule.span ℚ ((fun s => j s*s) '' (S : Set ℂ))),
    letI : Carrier := ⟨E,F,hc,hF,ha,ht⟩

    ∀ (μ : Measure D) [IsProbabilityMeasure μ] [ErgodicSMul K D μ]
      (Y : Type) [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
      [MulAction K Y] [MeasurableConstSMul K Y] (q : D → Y) (hq : Measurable q), (∀ k : K, ∀ᵐ x ∂μ, q (k • x) = k • q x) →
      ErgodicSMul K (D×D) (square μ q hq) → IsWild (difference μ q) →
      ∀ a : E, a ≠ 0 → ∀ᵐ w ∂μ.map q, ∫ d, (eval a d : ℂ) ∂condDistrib id q μ w = 0

theorem assemble (factor : H1) (vanish : H2) (E : IntermediateField ℚ ℂ) (F : IntermediateField ℚ ℝ) (hc : Countable E)
    (hF : ∀ z : ℂ, z ∈ E ↔ z.re ∈ F ∧ z.im ∈ F)
    (ha : ∀ p : Polynomial ℂ, p ≠ 0 → (∀ n, p.coeff n ∈ E) → ∀ z, p.eval z = 0 → z ∈ E)
    (ht : ∀ Q : Finset ℂ, (∀ q ∈ Q, q ∈ E ∧ ‖q‖ = 1) →
      ∃ S : Finset ℂ, (∀ s ∈ S, s ∈ E ∧ ‖s‖ = 1) ∧
      ∀ j : ℂ → ℂ, (∀ s ∈ S, j s ∈ Q) →
        (1 : ℂ) ∈ Submodule.span ℚ ((fun s => j s*s) '' (S : Set ℂ)) ∧
        Complex.I ∈ Submodule.span ℚ ((fun s => j s*s) '' (S : Set ℂ))) :
    letI : Carrier := ⟨E,F,hc,hF,ha,ht⟩
    ∀ (μ : Measure D) [IsProbabilityMeasure μ] [ErgodicSMul K D μ],
      IsWild μ → ∀ a : E, a ≠ 0 → ∫ d, (eval a d : ℂ) ∂μ = 0 := by
  letI : Carrier := ⟨E,F,hc,hF,ha,ht⟩
  intro μ hμ he hw a hne
  haveI := hμ
  haveI := he
  obtain ⟨Y,mY,aY,bY,nY,sY,q,hq,hcov,heq,hd⟩ := @factor E F hc hF ha ht μ hμ he hw
  letI : MeasurableSpace Y := mY
  letI : MulAction K Y := aY
  letI : StandardBorelSpace Y := bY
  letI : Nonempty Y := nY
  letI : MeasurableConstSMul K Y := sY
  have hv := @vanish E F hc hF ha ht μ hμ he Y _ _ _ _ _ q hq hcov heq hd a hne
  let f := fun d : D => (eval a d : ℂ)
  have hf : Integrable f μ := Integrable.of_bound (measurable_eval_coe a).aestronglyMeasurable 1
    (Filter.Eventually.of_forall (fun d => (Circle.norm_coe _).le))
  have hcomp : condDistrib id q μ ∘ₘ μ.map q = μ := by
    simpa using condDistrib_comp_map hq.aemeasurable (measurable_id.aemeasurable (μ:=μ))
  have hi : Integrable f (condDistrib id q μ ∘ₘ μ.map q) := by rw [hcomp]; exact hf
  rw [Measure.comp_eq_comp_const_apply] at hi
  have h := Kernel.integral_comp hi
  have hsum : ∫ d, f d ∂μ = ∫ w, (∫ d, f d ∂condDistrib id q μ w) ∂μ.map q := by
    simpa [Kernel.const_apply,← Measure.comp_eq_comp_const_apply,hcomp] using h
  exact hsum.trans (integral_eq_zero_of_ae hv)

theorem main : H1 → H2 → OMA.R_Erdos173_erdos_173_R1_H2_R1_H1_R1_H2_R1_H1_R1.H2 := by
  intro factor vanish E F hc hF ha ht
  exact assemble factor vanish E F hc hF ha ht
end OMA.R_Erdos173_erdos_173_R1_H2_R1_H1_R1_H2_R1_H1_R1_H2_R1
end
