import OMAReductions.R_Erdos173_erdos_173_R1_H2_R1_H1_R1_H2_R1_H1_R1_H2_R1
-- PORT OF A PUBLIC PROOF, NOT A NEW RESULT.
-- Source: Jacob Parish (Plasma AI), github.com/plasma-ai/erdos-173 at commit 4a368a652753,
-- licensed Apache-2.0. Its OAI modules come from OpenAI, github.com/openai/math at commit
-- adc7f1241b42e322a6451854ab7e4b4c146bf78a, licensed Apache-2.0. Used here under the Apache
-- License 2.0 (the source files carry no separate copyright lines). Changes: the modules were
-- flattened into one file, unused parts dropped, lemma names adapted to the pinned Mathlib, and
-- a bridge to this reduction step added (agents moon-4 and opus-4 for marcusbuffett).
import Mathlib

theorem Measurable.of_eval {α ι : Type*} {X : ι → Type*} {mα : MeasurableSpace α}
    [mX : ∀ i, MeasurableSpace (X i)] {f : α → ∀ i, X i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_iff.mpr h

/-! A measurable terminal factor for a wild ergodic character law. Modified
from Jacob Parish, plasma-ai/erdos-173 at 4a368a652753, and OpenAI,
openai/math at adc7f1241b42e322a6451854ab7e4b4c146bf78a, both Apache-2.0. -/

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
  apply Measurable.of_eval
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

-- OAI.MeasureTheory.CompactFactors.Centers
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

namespace EuclideanFiveColor.Location

private abbrev Ambient := WithLp 2 (ℝ × ℂ)

private def lift (z : ℂ) : Ambient := WithLp.toLp 2 (1, z)

@[simp] theorem lift_fst (z : ℂ) : (lift z).fst = 1 := rfl
@[simp] theorem lift_snd (z : ℂ) : (lift z).snd = z := rfl

theorem lift_ne_zero (z : ℂ) : lift z ≠ 0 := by
  intro h
  have := congrArg WithLp.fst h
  simp at this

theorem norm_lift (z : ℂ) : ‖lift z‖ = Real.sqrt (1 + ‖z‖ ^ 2) := by
  simp [WithLp.prod_norm_eq_of_L2]

theorem lift_sub (z w : ℂ) : lift z - lift w = WithLp.toLp 2 (0, z - w) := by
  apply WithLp.ofLp_injective 2
  simp [lift]

theorem norm_lift_sub (z w : ℂ) : ‖lift z - lift w‖ = ‖z - w‖ := by
  rw [lift_sub, WithLp.norm_toLp_snd]

theorem lift_affine (z w : ℂ) (a b : ℝ) (hab : a + b = 1) :
    lift (a • z + b • w) = a • lift z + b • lift w := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · simpa using hab.symm
  · rfl

theorem not_sameRay_smul_lift {z w : ℂ} (hzw : z ≠ w)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ¬ SameRay ℝ (a • lift z) (b • lift w) := by
  intro h
  have haz : a • lift z ≠ 0 := smul_ne_zero ha.ne' (lift_ne_zero z)
  have hbw : b • lift w ≠ 0 := smul_ne_zero hb.ne' (lift_ne_zero w)
  obtain ⟨r, hr, he⟩ := h.exists_pos_left haz hbw
  have hfst := congrArg WithLp.fst he
  have hsnd := congrArg WithLp.snd he
  simp only [WithLp.smul_fst, lift_fst, smul_eq_mul, mul_one] at hfst
  simp only [WithLp.smul_snd, lift_snd, smul_smul, hfst] at hsnd
  exact hzw ((smul_right_injective ℂ hb.ne') hsnd)

theorem strictConvex_norm_lift : StrictConvexOn ℝ Set.univ (fun z : ℂ => ‖lift z‖) := by
  refine ⟨convex_univ, ?_⟩
  intro z _ w _ hzw a b ha hb hab
  change ‖lift (a • z + b • w)‖ < a • ‖lift z‖ + b • ‖lift w‖
  rw [lift_affine z w a b hab]
  have := norm_add_lt_of_not_sameRay (not_sameRay_smul_lift hzw ha hb)
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos ha, abs_of_pos hb,
    smul_eq_mul] using this

private noncomputable def kernel (s t : ℂ) : ℝ := ‖lift (s - t)‖ - ‖lift (-t)‖

private noncomputable def objective (μ : Measure ℂ) (s : ℂ) : ℝ := ∫ t, kernel s t ∂μ

theorem kernel_formula (s t : ℂ) : kernel s t =
    Real.sqrt (1 + ‖s - t‖ ^ 2) - Real.sqrt (1 + ‖t‖ ^ 2) := by
  simp [kernel, norm_lift]

theorem continuous_kernel (s : ℂ) : Continuous (kernel s) := by
  simp only [funext (kernel_formula s)]
  fun_prop

theorem kernel_bound (s t : ℂ) : |kernel s t| ≤ ‖s‖ := by
  have h := abs_norm_sub_norm_le (lift (s - t)) (lift (-t))
  simpa [kernel, norm_lift_sub] using h

theorem kernel_diff_bound (s s' t : ℂ) : |kernel s t - kernel s' t| ≤ ‖s - s'‖ := by
  have h := abs_norm_sub_norm_le (lift (s - t)) (lift (s' - t))
  simpa [kernel, norm_lift_sub, sub_sub_sub_cancel_right] using h

theorem integrable_kernel (μ : Measure ℂ) [IsFiniteMeasure μ] (s : ℂ) :
    Integrable (kernel s) μ := by
  apply (integrable_const ‖s‖).mono' (continuous_kernel s).aestronglyMeasurable
  exact Eventually.of_forall fun t => by simpa using kernel_bound s t

theorem objective_zero (μ : Measure ℂ) : objective μ 0 = 0 := by
  simp [objective, kernel]

theorem objective_lipschitz (μ : Measure ℂ) [IsProbabilityMeasure μ] :
    LipschitzWith 1 (objective μ) := by
  apply LipschitzWith.of_dist_le_mul
  intro s s'
  rw [Real.dist_eq, objective, objective, ← integral_sub (integrable_kernel μ s)
    (integrable_kernel μ s')]
  calc
    |∫ t, kernel s t - kernel s' t ∂μ| ≤ ∫ t, |kernel s t - kernel s' t| ∂μ :=
      abs_integral_le_integral_abs
    _ ≤ ∫ _ : ℂ, ‖s - s'‖ ∂μ := by
      apply integral_mono ((integrable_kernel μ s).sub (integrable_kernel μ s')).abs
        (integrable_const _)
      exact fun t => kernel_diff_bound s s' t
    _ = (1 : ℝ≥0) * dist s s' := by simp [dist_eq_norm]

theorem continuous_objective (μ : Measure ℂ) [IsProbabilityMeasure μ] :
    Continuous (objective μ) := (objective_lipschitz μ).continuous

theorem kernel_strict_convex (t : ℂ) : StrictConvexOn ℝ Set.univ (fun s => kernel s t) := by
  refine ⟨convex_univ, ?_⟩
  intro z _ w _ hzw a b ha hb hab
  have hn : z - t ≠ w - t := sub_left_injective.ne hzw
  have h := strictConvex_norm_lift.2 (Set.mem_univ (z - t))
    (Set.mem_univ (w - t)) hn ha hb hab
  have ht : a • t + b • t = t := by rw [← add_smul, hab, one_smul]
  have he : a • (z - t) + b • (w - t) = a • z + b • w - t := by
    calc
      _ = a • z + b • w - (a • t + b • t) := by
        simp only [smul_sub]
        abel
      _ = _ := by rw [ht]
  dsimp only at h
  rw [he] at h
  dsimp only [kernel]
  simp only [smul_eq_mul] at h ⊢
  have hc : a * ‖lift (-t)‖ + b * ‖lift (-t)‖ = ‖lift (-t)‖ := by
    rw [← add_mul, hab, one_mul]
  nlinarith only [h, hc]

theorem objective_strict_convex (μ : Measure ℂ) [IsProbabilityMeasure μ] :
    StrictConvexOn ℝ Set.univ (objective μ) := by
  refine ⟨convex_univ, ?_⟩
  intro z hz w hw hzw a b ha hb hab
  have hk (t : ℂ) := (kernel_strict_convex t).2 hz hw hzw ha hb hab
  have hf := integrable_kernel μ (a • z + b • w)
  have hg := ((integrable_kernel μ z).smul a).add ((integrable_kernel μ w).smul b)
  change (∫ t, kernel (a • z + b • w) t ∂μ) <
    a • (∫ t, kernel z t ∂μ) + b • (∫ t, kernel w t ∂μ)
  rw [← integral_smul, ← integral_smul, ← integral_add]
  · refine lt_of_le_of_ne (integral_mono hf hg fun t => (hk t).le) ?_
    intro he
    have heq := (integral_eq_iff_of_ae_le hf hg
      (Eventually.of_forall fun t => (hk t).le)).mp he
    obtain ⟨t, ht⟩ := heq.exists
    exact (hk t).ne ht
  · exact (integrable_kernel μ z).smul a
  · exact (integrable_kernel μ w).smul b

theorem norm_lift_le (z : ℂ) : ‖lift z‖ ≤ ‖z‖ + 1 := by
  calc
    ‖lift z‖ ≤ ‖lift z - lift 0‖ + ‖lift 0‖ := norm_le_norm_sub_add _ _
    _ = ‖z‖ + 1 := by simp [norm_lift_sub, norm_lift]

theorem kernel_lower (s t : ℂ) : ‖s‖ - 2 * ‖t‖ - 1 ≤ kernel s t := by
  have hst : ‖s - t‖ ≤ ‖lift (s - t)‖ := WithLp.norm_snd_le ℝ (lift (s - t))
  have hs : ‖s‖ ≤ ‖s - t‖ + ‖t‖ := norm_le_norm_sub_add _ _
  have ht := norm_lift_le (-t)
  simp only [norm_neg] at ht
  dsimp only [kernel]
  linarith

theorem exists_ball_mass (μ : Measure ℂ) [IsProbabilityMeasure μ] :
    ∃ n : ℕ, (1 / 2 : ℝ) < μ.real (Metric.closedBall 0 (n : ℝ)) := by
  by_contra! h
  have hm (n : ℕ) : μ (Metric.closedBall 0 (n : ℝ)) ≤ (1 / 2 : ℝ≥0∞) := by
    apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) (by norm_num)).mp
    simpa [measureReal_def] using h n
  have hc : (⋃ n : ℕ, Metric.closedBall (0 : ℂ) (n : ℝ)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    obtain ⟨n, hn⟩ := exists_nat_gt ‖z‖
    exact Set.mem_iUnion.mpr ⟨n, by simpa [Metric.mem_closedBall] using hn.le⟩
  have hmono : Monotone (fun n : ℕ => Metric.closedBall (0 : ℂ) (n : ℝ)) := by
    intro i j hij
    exact Metric.closedBall_subset_closedBall (Nat.cast_le.mpr hij)
  have he : μ (⋃ n : ℕ, Metric.closedBall (0 : ℂ) (n : ℝ)) ≤ (1 / 2 : ℝ≥0∞) := by
    rw [hmono.measure_iUnion]
    exact iSup_le hm
  rw [hc, measure_univ] at he
  norm_num at he

theorem objective_lower (μ : Measure ℂ) [IsProbabilityMeasure μ] (R : ℝ) (s : ℂ) :
    (2 * μ.real (Metric.closedBall 0 R) - 1) * ‖s‖ -
        μ.real (Metric.closedBall 0 R) * (2 * R + 1) ≤ objective μ s := by
  classical
  let B := Metric.closedBall (0 : ℂ) R
  let v := 2 * ‖s‖ - (2 * R + 1)
  have hB : MeasurableSet B := Metric.isClosed_closedBall.measurableSet
  have hi : Integrable (B.indicator (fun _ : ℂ => v)) μ :=
    (integrable_const v).indicator hB
  have hp (t : ℂ) : -‖s‖ + B.indicator (fun _ : ℂ => v) t ≤ kernel s t := by
    by_cases ht : t ∈ B
    · rw [Set.indicator_of_mem ht]
      have ht' : ‖t‖ ≤ R := by simpa [B, Metric.mem_closedBall] using ht
      have hlo := kernel_lower s t
      dsimp only [v]
      linarith
    · rw [Set.indicator_of_notMem ht, add_zero]
      exact (abs_le.mp (kernel_bound s t)).1
  calc
    _ = ∫ t : ℂ, -‖s‖ + B.indicator (fun _ : ℂ => v) t ∂μ := by
      rw [integral_add (integrable_const _) hi, integral_const,
        integral_indicator_const v hB]
      simp only [probReal_univ, smul_eq_mul]
      dsimp only [v, B]
      ring
    _ ≤ _ := integral_mono ((integrable_const _).add hi) (integrable_kernel μ s) hp

theorem linear_norm_coercive (a b : ℝ) (ha : 0 < a) :
    Tendsto (fun z : ℂ => a * ‖z‖ + b) (cocompact ℂ) atTop := by
  have ht : Tendsto (fun z : ℂ => a * ‖z‖) (cocompact ℂ) atTop :=
    Filter.Tendsto.const_mul_atTop ha (tendsto_norm_cocompact_atTop (E := ℂ))
  exact tendsto_atTop_add_const_right (cocompact ℂ) b ht

theorem objective_coercive (μ : Measure ℂ) [IsProbabilityMeasure μ] :
    Tendsto (objective μ) (cocompact ℂ) atTop := by
  obtain ⟨n, hn⟩ := exists_ball_mass μ
  have hp : 0 < 2 * μ.real (Metric.closedBall 0 (n : ℝ)) - 1 := by linarith
  have ht := linear_norm_coercive (2 * μ.real (Metric.closedBall 0 (n : ℝ)) - 1)
    (-(μ.real (Metric.closedBall 0 (n : ℝ)) * (2 * (n : ℝ) + 1))) hp
  apply tendsto_atTop_mono (objective_lower μ (n : ℝ))
  simpa only [sub_eq_add_neg] using ht

theorem exists_unique_minimizer (μ : Measure ℂ) [IsProbabilityMeasure μ] :
    ∃! s, ∀ t, objective μ s ≤ objective μ t := by
  obtain ⟨s, hs⟩ := (continuous_objective μ).exists_forall_le (objective_coercive μ)
  refine ⟨s, hs, ?_⟩
  intro t ht
  exact (objective_strict_convex μ).eq_of_isMinOn (fun x _ => ht x)
    (fun x _ => hs x) (Set.mem_univ t) (Set.mem_univ s)

private noncomputable def center (μ : ProbabilityMeasure ℂ) : ℂ :=
  (exists_unique_minimizer (μ : Measure ℂ)).choose

theorem center_minimizes (μ : ProbabilityMeasure ℂ) (s : ℂ) :
    objective (μ : Measure ℂ) (center μ) ≤ objective (μ : Measure ℂ) s :=
  (exists_unique_minimizer (μ : Measure ℂ)).choose_spec.1 s

theorem center_unique (μ : ProbabilityMeasure ℂ) {z : ℂ}
    (hz : ∀ t, objective (μ : Measure ℂ) z ≤ objective (μ : Measure ℂ) t) :
    z = center μ := (exists_unique_minimizer (μ : Measure ℂ)).choose_spec.2 z hz

private noncomputable def universalKernel : ProbabilityTheory.Kernel (ProbabilityMeasure ℂ) ℂ :=
  ⟨fun μ => (μ : Measure ℂ), measurable_subtype_coe⟩

theorem measurable_objective (s : ℂ) :
    Measurable (fun μ : ProbabilityMeasure ℂ => objective (μ : Measure ℂ) s) :=
  ((continuous_kernel s).stronglyMeasurable.integral_kernel
    (κ := universalKernel)).measurable

theorem denseSeq_inf_eq_min {X : Type*} [TopologicalSpace X] [TopologicalSpace.SeparableSpace X]
    [Nonempty X] (f : X → ℝ) (hf : Continuous f) (x : X)
    (hx : ∀ y, f x ≤ f y) : (⨅ n, f (TopologicalSpace.denseSeq X n)) = f x := by
  have hb : BddBelow (Set.range (fun n => f (TopologicalSpace.denseSeq X n))) :=
    ⟨f x, by rintro _ ⟨n, rfl⟩; exact hx _⟩
  apply le_antisymm
  · exact (TopologicalSpace.denseRange_denseSeq X).induction_on
      (p := fun y => (⨅ n, f (TopologicalSpace.denseSeq X n)) ≤ f y) x
      (isClosed_le continuous_const hf) (fun n => ciInf_le hb n)
  · exact le_ciInf (fun n => hx _)

private noncomputable def minValue (μ : ProbabilityMeasure ℂ) : ℝ :=
  ⨅ n, objective (μ : Measure ℂ) (TopologicalSpace.denseSeq ℂ n)

theorem measurable_minValue : Measurable minValue :=
  Measurable.iInf fun _n => measurable_objective _

theorem minValue_eq (μ : ProbabilityMeasure ℂ) :
    minValue μ = objective (μ : Measure ℂ) (center μ) :=
  denseSeq_inf_eq_min _ (continuous_objective _) _ (center_minimizes μ)

theorem exists_min_on_closed (μ : ProbabilityMeasure ℂ) {C : Set ℂ}
    (hC : IsClosed C) (hCn : C.Nonempty) :
    ∃ z ∈ C, ∀ t ∈ C, objective (μ : Measure ℂ) z ≤ objective (μ : Measure ℂ) t := by
  obtain ⟨x, hx⟩ := hCn
  apply (continuous_objective (μ : Measure ℂ)).continuousOn.exists_isMinOn' hC hx
  apply Filter.Eventually.filter_mono inf_le_left
  exact (objective_coercive (μ : Measure ℂ)).eventually
    (eventually_ge_atTop (objective (μ : Measure ℂ) x))

theorem measurable_center : Measurable center := by
  classical
  apply measurable_of_isClosed
  intro C hC
  by_cases hne : C.Nonempty
  · let : Nonempty C := hne.to_subtype
    let mC (μ : ProbabilityMeasure ℂ) : ℝ :=
      ⨅ n, objective (μ : Measure ℂ) (TopologicalSpace.denseSeq C n).val
    have hmC : Measurable mC := Measurable.iInf fun _n => measurable_objective _
    have he : center ⁻¹' C = {μ | mC μ = minValue μ} := by
      ext μ
      obtain ⟨z, hzC, hz⟩ := exists_min_on_closed μ hC hne
      have hm : mC μ = objective (μ : Measure ℂ) z :=
        denseSeq_inf_eq_min (fun t : C => objective (μ : Measure ℂ) t.val)
          ((continuous_objective _).comp continuous_subtype_val) ⟨z, hzC⟩
          (fun t => hz t.val t.property)
      rw [Set.mem_preimage, Set.mem_ofPred_eq, hm, minValue_eq]
      constructor
      · intro h
        exact le_antisymm (hz _ h) (center_minimizes μ z)
      · intro h
        have hzm : ∀ t, objective (μ : Measure ℂ) z ≤ objective (μ : Measure ℂ) t :=
          fun t => h.trans_le (center_minimizes μ t)
        rwa [center_unique μ hzm] at hzC
    rw [he]
    exact measurableSet_eq_fun hmC measurable_minValue
  · have he : C = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    simp [he]

theorem kernel_translate (s t v : ℂ) :
    kernel (s + v) (t + v) = kernel s t - kernel (-v) t := by
  have h₁ : s + v - (t + v) = s - t := by abel
  have h₂ : -(t + v) = -v - t := by abel
  simp only [kernel, h₁, h₂]
  ring

theorem objective_translate (μ : ProbabilityMeasure ℂ) (s v : ℂ) :
    objective (Measure.map (fun t => t + v) (μ : Measure ℂ)) (s + v) =
      objective (μ : Measure ℂ) s - objective (μ : Measure ℂ) (-v) := by
  have hm : AEMeasurable (fun t : ℂ => t + v) (μ : Measure ℂ) :=
    (continuous_id.add_const v).aemeasurable
  rw [objective, integral_map hm (continuous_kernel _).aestronglyMeasurable]
  simp only [kernel_translate]
  exact integral_sub (integrable_kernel _ _) (integrable_kernel _ _)

theorem center_translate (μ : ProbabilityMeasure ℂ) (v : ℂ) :
    center (μ.map (f := fun point => point + v) (continuous_id.add_const v).aemeasurable) = center μ + v := by
  apply Eq.symm
  apply center_unique
  intro t
  have he : t = (t - v) + v := by abel
  change objective (Measure.map (fun t : ℂ => t + v) (μ : Measure ℂ)) (center μ + v) ≤
    objective (Measure.map (fun t : ℂ => t + v) (μ : Measure ℂ)) t
  rw [objective_translate, he, objective_translate]
  exact sub_le_sub_right (center_minimizes μ (t - v)) _

theorem kernel_orthogonal (O : ℂ ≃ₗᵢ[ℝ] ℂ) (s t : ℂ) :
    kernel (O s) (O t) = kernel s t := by
  simp only [kernel_formula, ← O.map_sub, O.norm_map]

theorem objective_orthogonal (μ : ProbabilityMeasure ℂ) (O : ℂ ≃ₗᵢ[ℝ] ℂ) (s : ℂ) :
    objective (Measure.map O (μ : Measure ℂ)) (O s) = objective (μ : Measure ℂ) s := by
  rw [objective, integral_map O.continuous.aemeasurable
    (continuous_kernel _).aestronglyMeasurable]
  simp only [kernel_orthogonal, objective]

theorem center_orthogonal (μ : ProbabilityMeasure ℂ) (O : ℂ ≃ₗᵢ[ℝ] ℂ) :
    center (μ.map (f := (O : ℂ → ℂ)) O.continuous.aemeasurable) = O (center μ) := by
  apply Eq.symm
  apply center_unique
  intro t
  obtain ⟨s, rfl⟩ := O.surjective t
  rw [ProbabilityMeasure.toMeasure_map, objective_orthogonal, objective_orthogonal]
  exact center_minimizes μ s

end EuclideanFiveColor.Location

namespace EuclideanFiveColor.CosetCenter
open ProbabilityTheory

variable {G : Type*} [CommGroup G] [MeasurableSpace G]

private structure Embedding (G : Type*) [CommGroup G] [MeasurableSpace G] where
  hom : Multiplicative ℂ →* G
  measurableEmbedding : MeasurableEmbedding (fun z : ℂ => hom (Multiplicative.ofAdd z))

namespace Embedding

variable (e : Embedding G)

private def j (z : ℂ) : G := e.hom (Multiplicative.ofAdd z)

@[simp] theorem j_zero : e.j 0 = 1 := e.hom.map_one
@[simp] theorem j_add (z w : ℂ) : e.j (z + w) = e.j z * e.j w := e.hom.map_mul _ _
@[simp] theorem j_neg (z : ℂ) : e.j (-z) = (e.j z)⁻¹ := e.hom.map_inv _
@[simp] theorem j_sub (z w : ℂ) : e.j (z - w) = e.j z / e.j w := e.hom.map_div _ _

theorem j_injective : Function.Injective e.j := e.measurableEmbedding.injective

theorem measurable_j : Measurable e.j := e.measurableEmbedding.measurable

private def ordinary : Subgroup G := e.hom.range

theorem mem_ordinary_iff (x : G) : x ∈ e.ordinary ↔ ∃ z : ℂ, e.j z = x := Iff.rfl

theorem range_j : Set.range e.j = (e.ordinary : Set G) := rfl

theorem measurableSet_ordinary : MeasurableSet (e.ordinary : Set G) :=
  e.measurableEmbedding.measurableSet_range

private noncomputable def coordinate : G → ℂ := Function.extend e.j id (fun _ => 0)

theorem measurable_coordinate : Measurable e.coordinate :=
  e.measurableEmbedding.measurable_extend measurable_id measurable_const

@[simp] theorem coordinate_j (z : ℂ) : e.coordinate (e.j z) = z :=
  e.j_injective.extend_apply id (fun _ => 0) z

theorem j_coordinate {x : G} (hx : x ∈ e.ordinary) : e.j (e.coordinate x) = x := by
  obtain ⟨z, rfl⟩ := (e.mem_ordinary_iff x).mp hx
  simp

variable [MeasurableMul₂ G] [MeasurableInv G]

private def coset (z : G) : Set G := {d | d / z ∈ e.ordinary}

theorem measurableSet_coset (z : G) : MeasurableSet (e.coset z) :=
  e.measurableSet_ordinary.preimage (measurable_id.div_const z)

private noncomputable def frequencyMeasure (μ : Measure G) (z : G) : Measure ℂ :=
  (μ.restrict (e.coset z)).map (fun d => e.coordinate (d / z))

theorem frequencyMeasure_apply (μ : Measure G) (z : G) {s : Set ℂ}
    (hs : MeasurableSet s) :
    e.frequencyMeasure μ z s = μ {d | d / z ∈ e.ordinary ∧ e.coordinate (d / z) ∈ s} := by
  rw [frequencyMeasure, Measure.map_apply
    (show Measurable (fun d : G => e.coordinate (d / z)) from
      e.measurable_coordinate.comp (measurable_id.div_const z)) hs,
    Measure.restrict_apply (show MeasurableSet ((fun d : G => e.coordinate (d / z)) ⁻¹' s) from
      (e.measurable_coordinate.comp (measurable_id.div_const z)) hs)]
  congr 1
  ext d
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, coset]
  exact and_comm

@[simp] theorem frequencyMeasure_univ (μ : Measure G) (z : G) :
    e.frequencyMeasure μ z Set.univ = μ (e.coset z) := by
  rw [e.frequencyMeasure_apply μ z MeasurableSet.univ]
  congr 1
  ext d
  simp [coset]

private noncomputable def parameterKernel : Kernel (ProbabilityMeasure G × G) G :=
  ⟨fun p => (p.1 : Measure G), measurable_subtype_coe.comp measurable_fst⟩

private instance parameterKernel_markov : IsMarkovKernel (parameterKernel (G := G)) :=
  ⟨fun p => by change IsProbabilityMeasure (p.1 : Measure G); infer_instance⟩

theorem measurable_frequencyMeasure :
    Measurable (fun p : ProbabilityMeasure G × G => e.frequencyMeasure (p.1 : Measure G) p.2) := by
  classical
  apply Measure.measurable_of_measurable_coe
  intro s hs
  have hm : Measurable (fun p : (ProbabilityMeasure G × G) × G =>
      if p.2 / p.1.2 ∈ e.ordinary ∧ e.coordinate (p.2 / p.1.2) ∈ s
      then (1 : ℝ≥0∞) else 0) := by
    apply Measurable.ite _ measurable_const measurable_const
    exact (e.measurableSet_ordinary.preimage
      (measurable_snd.div (measurable_snd.comp measurable_fst))).inter
      (hs.preimage (e.measurable_coordinate.comp
        (measurable_snd.div (measurable_snd.comp measurable_fst))))
  have h := hm.lintegral_kernel_prod_right' (κ := parameterKernel (G := G))
  convert h using 1
  ext p
  rw [e.frequencyMeasure_apply _ _ hs]
  have hset : MeasurableSet {d : G | d / p.2 ∈ e.ordinary ∧
      e.coordinate (d / p.2) ∈ s} :=
    (e.measurableSet_ordinary.preimage (measurable_id.div_const p.2)).inter
      (hs.preimage (e.measurable_coordinate.comp (measurable_id.div_const p.2)))
  rw [show parameterKernel p = (p.1 : Measure G) from rfl]
  simpa only [Set.indicator_apply, Pi.one_apply, Set.mem_ofPred_eq] using
    (lintegral_indicator_one (μ := (p.1 : Measure G)) hset).symm

theorem measurable_mass : Measurable (fun p : ProbabilityMeasure G × G =>
    (p.1 : Measure G) (e.coset p.2)) := by
  have h : Measurable (fun p : ProbabilityMeasure G × G =>
      e.frequencyMeasure (p.1 : Measure G) p.2 Set.univ) :=
    (Measure.measurable_coe MeasurableSet.univ).comp e.measurable_frequencyMeasure
  simp only [frequencyMeasure_univ] at h
  exact h

private noncomputable def frequencyLaw (μ : ProbabilityMeasure G) (z : G) : ProbabilityMeasure ℂ :=
  if h : (μ : Measure G) (e.coset z) = 0 then ⟨Measure.dirac 0, inferInstance⟩
  else
    letI : IsProbabilityMeasure ((μ : Measure G)[|e.coset z]) :=
      cond_isProbabilityMeasure h
    ⟨((μ : Measure G)[|e.coset z]).map (fun d => e.coordinate (d / z)),
      Measure.isProbabilityMeasure_map (e.measurable_coordinate.comp (measurable_id.div_const z)).aemeasurable⟩

theorem frequencyLaw_measure (μ : ProbabilityMeasure G) (z : G) :
    (e.frequencyLaw μ z : Measure ℂ) =
      if (μ : Measure G) (e.coset z) = 0 then Measure.dirac 0 else
      ((μ : Measure G) (e.coset z))⁻¹ • e.frequencyMeasure μ z := by
  split_ifs with h
  · simp [frequencyLaw, h]
  · simp [frequencyLaw, h, ProbabilityTheory.cond, frequencyMeasure]

theorem measurable_frequencyLaw :
    Measurable (fun p : ProbabilityMeasure G × G => e.frequencyLaw p.1 p.2) := by
  have hm : Measurable (fun p : ProbabilityMeasure G × G =>
      (e.frequencyLaw p.1 p.2 : Measure ℂ)) := by
    simp_rw [frequencyLaw_measure]
    apply Measurable.ite (e.measurable_mass (measurableSet_singleton 0)) measurable_const
    apply Measure.measurable_of_measurable_coe
    intro s hs
    simp only [Measure.smul_apply, smul_eq_mul]
    exact e.measurable_mass.inv.mul ((Measure.measurable_coe hs).comp e.measurable_frequencyMeasure)
  exact hm.subtype_mk

omit [MeasurableMul₂ G] [MeasurableInv G] in
theorem coset_mul_j (z : G) (v : ℂ) : e.coset (z * e.j v) = e.coset z := by
  ext d
  have hj : e.j v ∈ e.ordinary := ⟨_, rfl⟩
  constructor
  · intro h
    change d / z ∈ e.ordinary
    convert e.ordinary.mul_mem h hj using 1
    simp [div_eq_mul_inv, mul_comm, mul_left_comm]
  · intro h
    change d / (z * e.j v) ∈ e.ordinary
    convert e.ordinary.div_mem h hj using 1
    simp [div_eq_mul_inv, mul_assoc, mul_comm]

omit [MeasurableMul₂ G] [MeasurableInv G] in
theorem coordinate_div_j {d : G} (hd : d ∈ e.ordinary) (v : ℂ) :
    e.coordinate (d / e.j v) = e.coordinate d - v := by
  rw [← e.j_coordinate hd, ← e.j_sub, e.coordinate_j, e.coordinate_j]

theorem frequencyMeasure_shift (μ : Measure G) (z : G) (v : ℂ) :
    e.frequencyMeasure μ (z * e.j v) =
      (e.frequencyMeasure μ z).map (fun t => t + -v) := by
  rw [frequencyMeasure, frequencyMeasure, e.coset_mul_j,
    Measure.map_map (show Measurable (fun t : ℂ => t + -v) from
      measurable_id.add_const (-v))
      (show Measurable (fun d : G => e.coordinate (d / z)) from
        e.measurable_coordinate.comp (measurable_id.div_const z))]
  apply Measure.map_congr
  filter_upwards [ae_restrict_mem (e.measurableSet_coset z)] with d hd
  change e.coordinate (d / (z * e.j v)) = e.coordinate (d / z) + -v
  rw [div_mul_eq_div_div, e.coordinate_div_j hd, sub_eq_add_neg]

theorem frequencyLaw_shift (μ : ProbabilityMeasure G) (z : G) (v : ℂ)
    (h : (μ : Measure G) (e.coset z) ≠ 0) :
    e.frequencyLaw μ (z * e.j v) =
      (e.frequencyLaw μ z).map (f := fun point => point + -v) (continuous_id.add_const (-v)).aemeasurable := by
  apply Subtype.ext
  change (e.frequencyLaw μ (z * e.j v) : Measure ℂ) =
    Measure.map (fun t => t + -v) (e.frequencyLaw μ z : Measure ℂ)
  rw [e.frequencyLaw_measure, e.frequencyLaw_measure, e.coset_mul_j]
  simp only [if_neg h]
  rw [Measure.map_smul ((μ : Measure G) (e.coset z))⁻¹
    (f := fun point : ℂ => point + -v),
    ← e.frequencyMeasure_shift]

private noncomputable def center (μ : ProbabilityMeasure G) (z : G) : G :=
  z * e.j (Location.center (e.frequencyLaw μ z))

theorem measurable_center :
    Measurable (fun p : ProbabilityMeasure G × G => e.center p.1 p.2) :=
  measurable_snd.mul (e.measurable_j.comp
    (Location.measurable_center.comp e.measurable_frequencyLaw))

theorem center_mem_coset (μ : ProbabilityMeasure G) (z : G) :
    e.center μ z ∈ e.coset z := by
  change z * e.j _ / z ∈ e.ordinary
  rw [mul_div_cancel_left]
  exact ⟨_, rfl⟩

theorem center_mul_j (μ : ProbabilityMeasure G) (z : G) (v : ℂ)
    (h : (μ : Measure G) (e.coset z) ≠ 0) :
    e.center μ (z * e.j v) = e.center μ z := by
  rw [center, e.frequencyLaw_shift μ z v h, Location.center_translate, e.j_add,
    e.j_neg, center]
  simp [mul_assoc, mul_comm]

theorem center_eq_of_mem_coset (μ : ProbabilityMeasure G) {z z' : G}
    (hz : (μ : Measure G) (e.coset z) ≠ 0) (hz' : z' ∈ e.coset z) :
    e.center μ z' = e.center μ z := by
  obtain ⟨v, hv⟩ := (e.mem_ordinary_iff (z' / z)).mp hz'
  have he : z' = z * e.j v := by rw [hv]; simp [div_eq_mul_inv]
  rw [he]
  exact e.center_mul_j μ z v hz

theorem quotient_center (μ : ProbabilityMeasure G) (z : G) :
    (QuotientGroup.mk (e.center μ z) : G ⧸ e.ordinary) = QuotientGroup.mk z :=
  QuotientGroup.eq_iff_div_mem.mpr (e.center_mem_coset μ z)

theorem center_eq_iff (μ : ProbabilityMeasure G) {z z' : G}
    (hz : (μ : Measure G) (e.coset z) ≠ 0) :
    e.center μ z' = e.center μ z ↔ z' ∈ e.coset z := by
  constructor
  · intro h
    change z' / z ∈ e.ordinary
    apply QuotientGroup.eq_iff_div_mem.mp
    rw [← e.quotient_center μ z', ← e.quotient_center μ z, h]
  · exact e.center_eq_of_mem_coset μ hz

theorem center_mem_ordinary_iff (μ : ProbabilityMeasure G) (z : G) :
    e.center μ z ∈ e.ordinary ↔ z ∈ e.ordinary := by
  rw [← QuotientGroup.eq_one_iff, e.quotient_center, QuotientGroup.eq_one_iff]

theorem preimage_center_singleton (μ : ProbabilityMeasure G) {z : G}
    (hz : (μ : Measure G) (e.coset z) ≠ 0) :
    (e.center μ) ⁻¹' {e.center μ z} = e.coset z := by
  ext z'
  exact e.center_eq_iff μ hz

theorem measurable_center_fixed (μ : ProbabilityMeasure G) : Measurable (e.center μ) :=
  e.measurable_center.comp (measurable_const.prodMk measurable_id)

variable (T : G ≃* G) (O : ℂ ≃ₗᵢ[ℝ] ℂ)
  (hT : Measurable T) (he : ∀ t : ℂ, T (e.j t) = e.j (O t))

include he

omit [MeasurableMul₂ G] [MeasurableInv G] in
theorem equiv_mem_ordinary_iff (d : G) : T d ∈ e.ordinary ↔ d ∈ e.ordinary := by
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨Multiplicative.ofAdd (O.symm (Multiplicative.toAdd t)), ?_⟩
    change e.j (O.symm _) = d
    apply T.injective
    rw [he, O.apply_symm_apply]
    exact ht
  · rintro ⟨t, rfl⟩
    exact (e.mem_ordinary_iff _).mpr ⟨O (Multiplicative.toAdd t), (he _).symm⟩

omit [MeasurableMul₂ G] [MeasurableInv G] in
theorem preimage_coset_equiv (z : G) : T ⁻¹' e.coset (T z) = e.coset z := by
  ext d
  change T d / T z ∈ e.ordinary ↔ d / z ∈ e.ordinary
  rw [← T.map_div]
  exact e.equiv_mem_ordinary_iff T O he _

omit [MeasurableMul₂ G] [MeasurableInv G] in
theorem coordinate_equiv {d : G} (hd : d ∈ e.ordinary) :
    e.coordinate (T d) = O (e.coordinate d) := by
  obtain ⟨t, rfl⟩ := (e.mem_ordinary_iff d).mp hd
  rw [he, e.coordinate_j, e.coordinate_j]

include hT in
theorem frequencyMeasure_equiv (μ : Measure G) (z : G) :
    e.frequencyMeasure (μ.map T) (T z) = (e.frequencyMeasure μ z).map O := by
  rw [frequencyMeasure, Measure.restrict_map hT (e.measurableSet_coset _),
    e.preimage_coset_equiv T O he,
    Measure.map_map (show Measurable (fun d : G => e.coordinate (d / T z)) from
      e.measurable_coordinate.comp (measurable_id.div_const (T z))) hT,
    frequencyMeasure,
    Measure.map_map O.continuous.measurable
      (show Measurable (fun d : G => e.coordinate (d / z)) from
        e.measurable_coordinate.comp (measurable_id.div_const z))]
  apply Measure.map_congr
  filter_upwards [ae_restrict_mem (e.measurableSet_coset z)] with d hd
  change e.coordinate (T d / T z) = O (e.coordinate (d / z))
  rw [← T.map_div]
  exact e.coordinate_equiv T O he hd

include hT in
theorem frequencyLaw_equiv (μ : ProbabilityMeasure G) (z : G)
    (hz : (μ : Measure G) (e.coset z) ≠ 0) :
    e.frequencyLaw (μ.map (f := (T : G → G)) hT.aemeasurable) (T z) =
      (e.frequencyLaw μ z).map (f := (O : ℂ → ℂ)) O.continuous.aemeasurable := by
  apply Subtype.ext
  change (e.frequencyLaw (μ.map (f := (T : G → G)) hT.aemeasurable) (T z) : Measure ℂ) =
    Measure.map O (e.frequencyLaw μ z : Measure ℂ)
  rw [e.frequencyLaw_measure, e.frequencyLaw_measure, ProbabilityMeasure.toMeasure_map,
    Measure.map_apply hT (e.measurableSet_coset _), e.preimage_coset_equiv T O he,
    ]
  simp only [if_neg hz]
  rw [Measure.map_smul (f := (O : ℂ → ℂ)) _,
    e.frequencyMeasure_equiv T O hT he]

include hT in
theorem center_equivariant (μ : ProbabilityMeasure G) (z : G)
    (hz : (μ : Measure G) (e.coset z) ≠ 0) :
    e.center (μ.map (f := (T : G → G)) hT.aemeasurable) (T z) = T (e.center μ z) := by
  rw [center, e.frequencyLaw_equiv T O hT he μ z hz, Location.center_orthogonal,
    center, T.map_mul, he]

end Embedding
end EuclideanFiveColor.CosetCenter

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

namespace EuclideanFiveColor.UniformFibers

variable {X Q : Type*} [MeasurableSpace X]

 theorem finite_uniform_fibers (μ : Measure X) [IsProbabilityMeasure μ]
    (q : X → Q) (hm : ∀ y : Q, MeasurableSet (q ⁻¹' {y}))
    {a : ℝ≥0∞} (ha : 0 < a)
    (hs : ∀ᵐ x ∂μ, μ (q ⁻¹' {q x}) = a) :
    ∃ S : Finset Q, S.Nonempty ∧
      (∀ y ∈ S, μ (q ⁻¹' {y}) = a) ∧
      (∀ᵐ x ∂μ, q x ∈ S) ∧ (S.card : ℝ≥0∞) * a = 1 := by
  classical
  have hd : Pairwise (Function.onFun Disjoint (fun y : Q => q ⁻¹' {y})) := by
    intro y z hyz
    change Disjoint (q ⁻¹' {y}) (q ⁻¹' {z})
    rw [Set.disjoint_left]
    intro x hx hy
    exact hyz (hx.symm.trans hy)
  have hf := Measure.finite_const_le_meas_of_disjoint_iUnion μ ha hm hd (measure_ne_top μ _)
  have hf' : {y : Q | μ (q ⁻¹' {y}) = a}.Finite :=
    hf.subset (fun _ h => le_of_eq h.symm)
  let S := hf'.toFinset
  have hS (y : Q) : y ∈ S ↔ μ (q ⁻¹' {y}) = a := hf'.mem_toFinset
  have hsample : ∀ᵐ x ∂μ, q x ∈ S := hs.mono fun x hx => (hS _).mpr hx
  have hcover : (⋃ y ∈ S, q ⁻¹' {y}) =ᵐ[μ] Set.univ := by
    filter_upwards [hsample] with x hx
    have hmem : x ∈ ⋃ y ∈ S, q ⁻¹' {y} :=
      Set.mem_iUnion.mpr ⟨q x, Set.mem_iUnion.mpr ⟨hx, rfl⟩⟩
    exact propext (iff_of_true hmem (Set.mem_univ x))
  have hsum : (S.card : ℝ≥0∞) * a = 1 := by
    have h := measure_congr hcover
    rw [measure_biUnion_finset (fun _ _ _ _ h => hd h) (fun y _ => hm y),
      measure_univ] at h
    calc
      (S.card : ℝ≥0∞) * a = ∑ _y ∈ S, a := by simp
      _ = ∑ y ∈ S, μ (q ⁻¹' {y}) := Finset.sum_congr rfl fun y hy => ((hS y).mp hy).symm
      _ = 1 := h
  refine ⟨S, ?_, (fun y hy => (hS y).mp hy), hsample, hsum⟩
  by_contra h
  have hS0 : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
  simp [hS0] at hsum

end EuclideanFiveColor.UniformFibers

namespace EuclideanFiveColor.CosetCenter.Embedding
open MeasureTheory
open scoped ENNReal
variable {G : Type*} [CommGroup G] [MeasurableSpace G]
  [MeasurableMul₂ G] [MeasurableInv G] [MeasurableSingletonClass G]
  (e : CosetCenter.Embedding G)

theorem finite_uniform_centers (μ : ProbabilityMeasure G) {a : ℝ≥0∞}
    (ha : 0 < a) (hs : ∀ᵐ z ∂(μ : Measure G), (μ : Measure G) (e.coset z) = a) :
    ∃ S : Finset G, S.Nonempty ∧
      (∀ b ∈ S, (μ : Measure G) ((e.center μ) ⁻¹' {b}) = a) ∧
      (∀ᵐ z ∂(μ : Measure G), e.center μ z ∈ S) ∧
      (S.card : ℝ≥0∞) * a = 1 := by
  apply UniformFibers.finite_uniform_fibers (μ : Measure G) (e.center μ)
    (fun b => e.measurable_center_fixed μ (measurableSet_singleton b)) ha
  filter_upwards [hs] with z hz
  rw [e.preimage_center_singleton μ (by rw [hz]; exact ha.ne'), hz]

omit [MeasurableSingletonClass G] in

theorem center_law_ordinary (μ : ProbabilityMeasure G) :
    (μ.map (f := e.center μ) (e.measurable_center_fixed μ).aemeasurable : Measure G) e.ordinary =
      (μ : Measure G) e.ordinary := by
  rw [ProbabilityMeasure.toMeasure_map,
    Measure.map_apply (e.measurable_center_fixed μ) e.measurableSet_ordinary]
  congr 1
  ext z
  exact e.center_mem_ordinary_iff μ z

end EuclideanFiveColor.CosetCenter.Embedding

namespace EuclideanFiveColor.ErgodicSupport
open MeasureTheory Filter
variable {K X V : Type*} [SMul K X] [MeasurableSpace X]
  {μ : Measure X} [ErgodicSMul K X μ] [MeasurableSpace V]
  [MeasurableSpace.CountablySeparated V] [Nonempty V]

theorem ae_eq_const_of_invariant {f : X → V} (hf : Measurable f)
    (hi : ∀ k : K, ∀ᵐ x ∂μ, f (k • x) = f x) :
    ∃ v : V, f =ᵐ[μ] (fun _ => v) := by
  apply exists_eventuallyEq_const_of_forall_separating MeasurableSet
  intro A hA
  have h := ErgodicSMul.aeconst_of_forall_preimage_smul_ae_eq (G := K)
    (hf hA) (fun k => (hi k).mono (fun x hx => by
      exact propext (show f (k • x) ∈ A ↔ f x ∈ A by rw [hx])))
  exact Filter.eventuallyConst_set.mp h

end EuclideanFiveColor.ErgodicSupport

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

namespace EuclideanFiveColor.RelativeCenters
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {Y G : Type*} [MeasurableSpace Y] [CommGroup G] [MeasurableSpace G]
  [MeasurableMul₂ G] [MeasurableInv G]
  (e : CosetCenter.Embedding G)

private noncomputable def probabilityKernel (κ : Kernel Y G) [IsMarkovKernel κ]
    (y : Y) : ProbabilityMeasure G := ⟨κ y, inferInstance⟩

omit [CommGroup G] [MeasurableMul₂ G] [MeasurableInv G] in
lemma measurable_probabilityKernel (κ : Kernel Y G) [IsMarkovKernel κ] :
    Measurable (probabilityKernel κ) := κ.measurable.subtype_mk

private noncomputable def cosetMass (κ : Kernel Y G) [IsMarkovKernel κ] (p : Y × G) : ℝ≥0∞ :=
  κ p.1 (e.coset p.2)

lemma measurable_cosetMass (κ : Kernel Y G) [IsMarkovKernel κ] :
    Measurable (cosetMass e κ) :=
  e.measurable_mass.comp ((measurable_probabilityKernel κ).comp measurable_fst |>.prodMk
    measurable_snd)

private noncomputable def differenceLaw (ν : Measure Y) (κ : Kernel Y G) [IsMarkovKernel κ] :
    Measure G := ((κ ×ₖ κ) ∘ₘ ν).map (fun p : G × G => p.1 / p.2)

lemma differenceLaw_ordinary (ν : Measure Y) [SFinite ν]
    (κ : Kernel Y G) [IsMarkovKernel κ] :
    differenceLaw ν κ e.ordinary = ∫⁻ p : Y × G, cosetMass e κ p ∂ν ⊗ₘ κ := by
  have hdiv : Measurable (fun p : G × G => p.1 / p.2) :=
    measurable_fst.div measurable_snd
  rw [differenceLaw, Measure.map_apply hdiv
    e.measurableSet_ordinary,
    Measure.bind_apply (hdiv e.measurableSet_ordinary)
      (κ ×ₖ κ).aemeasurable,
    Measure.lintegral_compProd (measurable_cosetMass e κ)]
  apply lintegral_congr
  intro y
  rw [Kernel.prod_apply,
    Measure.prod_apply_symm (hdiv e.measurableSet_ordinary)]
  rfl

variable {X : Type*} [MeasurableSpace X]

lemma sampledMass_integral [StandardBorelSpace G]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (d : X → G) (p : X → Y) (hd : Measurable d) (hp : Measurable p) :
    differenceLaw (μ.map p) (condDistrib d p μ) e.ordinary =
      ∫⁻ x, cosetMass e (condDistrib d p μ) (p x, d x) ∂μ := by
  rw [differenceLaw_ordinary, compProd_map_condDistrib hd.aemeasurable,
    lintegral_map (measurable_cosetMass e _) (hp.prodMk hd)]

theorem positive_mass_finite_centers [StandardBorelSpace G]
    [MeasurableSingletonClass G]
    {K : Type*} [SMul K X]
    (μ : Measure X) [IsProbabilityMeasure μ] [ErgodicSMul K X μ]
    (d : X → G) (p : X → Y) (hd : Measurable d) (hp : Measurable p)
    (hi : ∀ k : K, ∀ᵐ x ∂μ,
      cosetMass e (condDistrib d p μ) (p (k • x), d (k • x)) =
        cosetMass e (condDistrib d p μ) (p x, d x))
    (hpos : 0 < differenceLaw (μ.map p) (condDistrib d p μ) e.ordinary) :
    ∃ a : ℝ≥0∞, 0 < a ∧
      (∀ᵐ x ∂μ, cosetMass e (condDistrib d p μ) (p x, d x) = a) ∧
      ∀ᵐ y ∂μ.map p, ∃ S : Finset G, S.Nonempty ∧
        (∀ b ∈ S, condDistrib d p μ y
          ((e.center (probabilityKernel (condDistrib d p μ) y)) ⁻¹' {b}) = a) ∧
        (∀ᵐ z ∂condDistrib d p μ y,
          e.center (probabilityKernel (condDistrib d p μ) y) z ∈ S) ∧
        (S.card : ℝ≥0∞) * a = 1 := by
  have hm : Measurable (fun x => cosetMass e (condDistrib d p μ) (p x, d x)) :=
    (measurable_cosetMass e (condDistrib d p μ)).comp (hp.prodMk hd)
  obtain ⟨a, ha⟩ := ErgodicSupport.ae_eq_const_of_invariant hm hi
  have hapos : 0 < a := by
    rw [sampledMass_integral e μ d p hd hp, lintegral_congr_ae ha] at hpos
    simpa using hpos
  refine ⟨a, hapos, ha, ?_⟩
  have hpair : ∀ᵐ q ∂(μ.map p) ⊗ₘ condDistrib d p μ,
      cosetMass e (condDistrib d p μ) q = a := by
    rw [compProd_map_condDistrib hd.aemeasurable]
    exact (ae_map_iff (hp.prodMk hd).aemeasurable
      (measurableSet_eq_fun (measurable_cosetMass e _) measurable_const)).mpr ha
  have hany := Measure.ae_ae_of_ae_compProd hpair
  filter_upwards [hany] with y hy
  exact e.finite_uniform_centers (probabilityKernel (condDistrib d p μ) y) hapos hy

section Actions
variable {K : Type*} [Group K] [MulAction K X] [MulAction K Y]
  [MulDistribMulAction K G]
  [MeasurableConstSMul K X] [MeasurableConstSMul K Y] [MeasurableConstSMul K G]
  [StandardBorelSpace G]

lemma sampledMass_invariant
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure K X μ]
    (d : X → G) (p : X → Y) (hd : Measurable d) (hp : Measurable p)
    (hde : ∀ k : K, ∀ᵐ x ∂μ, d (k • x) = k • d x)
    (hpe : ∀ k : K, ∀ᵐ x ∂μ, p (k • x) = k • p x)
    (hC : ∀ (k : K) (z : G), k • z ∈ e.ordinary ↔ z ∈ e.ordinary)
    (k : K) :
    ∀ᵐ x ∂μ,
      cosetMass e (condDistrib d p μ) (p (k • x), d (k • x)) =
        cosetMass e (condDistrib d p μ) (p x, d x) := by
  have heq := KernelSupport.condDistrib_equivariant μ d p hd hp
    (MeasurableEquiv.smul k) (MeasurableEquiv.smul k) (fun z : G => k • z)
    (measurable_const_smul k) (measurePreserving_smul k μ) (hpe k) (hde k)
  have hxeq := ae_of_ae_map hp.aemeasurable heq
  filter_upwards [hxeq, hde k, hpe k] with x hx hd' hp'
  change condDistrib d p μ (p (k • x)) (e.coset (d (k • x))) =
    condDistrib d p μ (p x) (e.coset (d x))
  change condDistrib d p μ (k • p x) = _ at hx
  rw [hp', hd', hx, Measure.map_apply (measurable_const_smul k) (e.measurableSet_coset _)]
  congr 1
  ext z
  change k • z / k • d x ∈ e.ordinary ↔ z / d x ∈ e.ordinary
  rw [← smul_div']
  exact hC k _

end Actions

private noncomputable def centerMap [StandardBorelSpace G]
    (μ : Measure X) [IsProbabilityMeasure μ] (d : X → G) (p : X → Y) (x : X) : G :=
  e.center (probabilityKernel (condDistrib d p μ) (p x)) (d x)

lemma measurable_centerMap [StandardBorelSpace G]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (d : X → G) (p : X → Y) (hd : Measurable d) (hp : Measurable p) :
    Measurable (centerMap e μ d p) :=
  e.measurable_center.comp (((measurable_probabilityKernel _).comp hp).prodMk hd)

lemma centerMap_mem_ordinary_iff [StandardBorelSpace G]
    (μ : Measure X) [IsProbabilityMeasure μ] (d : X → G) (p : X → Y) (x : X) :
    centerMap e μ d p x ∈ e.ordinary ↔ d x ∈ e.ordinary :=
  e.center_mem_ordinary_iff _ _

lemma centerMap_law_ordinary [StandardBorelSpace G]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (d : X → G) (p : X → Y) (hd : Measurable d) (hp : Measurable p) :
    (μ.map (centerMap e μ d p)) e.ordinary = (μ.map d) e.ordinary := by
  rw [Measure.map_apply (measurable_centerMap e μ d p hd hp) e.measurableSet_ordinary,
    Measure.map_apply hd e.measurableSet_ordinary]
  congr 1
  ext x
  exact centerMap_mem_ordinary_iff e μ d p x

section CenterActions
variable {K : Type*} [Group K] [MulAction K X] [MulAction K Y]
  [MulDistribMulAction K G]
  [MeasurableConstSMul K X] [MeasurableConstSMul K Y] [MeasurableConstSMul K G]
  [StandardBorelSpace G]

lemma centerMap_equivariant
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure K X μ]
    (d : X → G) (p : X → Y) (hd : Measurable d) (hp : Measurable p)
    (hde : ∀ k : K, ∀ᵐ x ∂μ, d (k • x) = k • d x)
    (hpe : ∀ k : K, ∀ᵐ x ∂μ, p (k • x) = k • p x)
    (O : K → ℂ ≃ₗᵢ[ℝ] ℂ)
    (he : ∀ (k : K) (t : ℂ), k • e.j t = e.j (O k t))
    (ha : ∀ᵐ x ∂μ, cosetMass e (condDistrib d p μ) (p x, d x) ≠ 0)
    (k : K) :
    ∀ᵐ x ∂μ, centerMap e μ d p (k • x) = k • centerMap e μ d p x := by
  have hk := KernelSupport.condDistrib_equivariant μ d p hd hp
    (MeasurableEquiv.smul k) (MeasurableEquiv.smul k) (fun z : G => k • z)
    (measurable_const_smul k) (measurePreserving_smul k μ) (hpe k) (hde k)
  have hxk := ae_of_ae_map hp.aemeasurable hk
  filter_upwards [hxk, hde k, hpe k, ha] with x hx hd' hp' ha'
  have hprob : probabilityKernel (condDistrib d p μ) (k • p x) =
      (probabilityKernel (condDistrib d p μ) (p x)).map
        (f := fun point : G => k • point) (measurable_const_smul k).aemeasurable := by
    apply Subtype.ext
    exact hx
  change e.center (probabilityKernel (condDistrib d p μ) (p (k • x))) (d (k • x)) = _
  rw [hp', hd', hprob]
  exact e.center_equivariant (MulDistribMulAction.toMulEquiv G k) (O k)
    (measurable_const_smul k) (he k) _ _ ha'

end CenterActions

section ConditionalLaw
variable {H : Type*} [MeasurableSpace H]

omit [CommGroup G] [MeasurableMul₂ G] [MeasurableInv G] in
lemma dependentMapKernel_apply (κ : Kernel Y G) [IsMarkovKernel κ]
    (f : Y × G → H) (hf : Measurable f) (y : Y) :
    ((Kernel.id ×ₖ κ).map f) y = (κ y).map (fun z => f (y, z)) := by
  rw [Kernel.map_apply _ hf, Kernel.prod_apply, Kernel.id_apply,
    Measure.dirac_prod, Measure.map_map hf measurable_prodMk_left]
  rfl

omit [CommGroup G] [MeasurableMul₂ G] [MeasurableInv G] in
lemma compProd_dependentMap (ν : Measure Y) [SFinite ν]
    (κ : Kernel Y G) [IsMarkovKernel κ]
    (f : Y × G → H) (hf : Measurable f) :
    ν ⊗ₘ ((Kernel.id ×ₖ κ).map f) =
      (ν ⊗ₘ κ).map (fun q : Y × G => (q.1, f q)) := by
  ext s hs
  rw [Measure.compProd_apply hs, Measure.map_apply (measurable_fst.prodMk hf) hs,
    Measure.compProd_apply ((measurable_fst.prodMk hf) hs)]
  apply lintegral_congr
  intro y
  have hfy : Measurable (fun z : G => f (y, z)) := hf.comp measurable_prodMk_left
  rw [dependentMapKernel_apply κ f hf y,
    Measure.map_apply hfy (measurable_prodMk_left hs)]
  rfl

private noncomputable def centerKernel (κ : Kernel Y G) [IsMarkovKernel κ] : Kernel Y G :=
  (Kernel.id ×ₖ κ).map (fun q : Y × G => e.center (probabilityKernel κ q.1) q.2)

lemma measurable_fiberCenter (κ : Kernel Y G) [IsMarkovKernel κ] :
    Measurable (fun q : Y × G => e.center (probabilityKernel κ q.1) q.2) :=
  e.measurable_center.comp (((measurable_probabilityKernel κ).comp measurable_fst).prodMk
    measurable_snd)

private instance centerKernel_markov (κ : Kernel Y G) [IsMarkovKernel κ] :
    IsMarkovKernel (centerKernel e κ) :=
  Kernel.IsMarkovKernel.map _ (measurable_fiberCenter e κ)

lemma centerKernel_apply (κ : Kernel Y G) [IsMarkovKernel κ] (y : Y) :
    centerKernel e κ y = (κ y).map (e.center (probabilityKernel κ y)) :=
  dependentMapKernel_apply κ _ (measurable_fiberCenter e κ) y

lemma condDistrib_centerMap [StandardBorelSpace G]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (d : X → G) (p : X → Y) (hd : Measurable d) (hp : Measurable p) :
    condDistrib (centerMap e μ d p) p μ =ᵐ[μ.map p]
      centerKernel e (condDistrib d p μ) := by
  apply condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    hp (measurable_centerMap e μ d p hd hp)
  rw [centerKernel, compProd_dependentMap (μ.map p) (condDistrib d p μ) _
    (measurable_fiberCenter e _), compProd_map_condDistrib hd.aemeasurable,
    Measure.map_map (measurable_fst.prodMk (measurable_fiberCenter e _)) (hp.prodMk hd)]
  rfl

end ConditionalLaw

lemma centerKernel_comp_map [StandardBorelSpace G]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (d : X → G) (p : X → Y) (hd : Measurable d) (hp : Measurable p) :
    centerKernel e (condDistrib d p μ) ∘ₘ (μ.map p) = μ.map (centerMap e μ d p) := by
  rw [← Measure.comp_congr (condDistrib_centerMap e μ d p hd hp)]
  exact condDistrib_comp_map hp.aemeasurable (measurable_centerMap e μ d p hd hp).aemeasurable

variable {K : Type*} [Group K] [MulAction K X] [MulAction K Y]
  [MulDistribMulAction K G]
  [MeasurableConstSMul K X] [MeasurableConstSMul K Y] [MeasurableConstSMul K G]
  [StandardBorelSpace G] [MeasurableSingletonClass G]

theorem finite_center_reduction
    (μ : Measure X) [IsProbabilityMeasure μ] [ErgodicSMul K X μ]
    (d : X → G) (p : X → Y) (hd : Measurable d) (hp : Measurable p)
    (hde : ∀ k : K, ∀ᵐ x ∂μ, d (k • x) = k • d x)
    (hpe : ∀ k : K, ∀ᵐ x ∂μ, p (k • x) = k • p x)
    (O : K → ℂ ≃ₗᵢ[ℝ] ℂ)
    (he : ∀ (k : K) (t : ℂ), k • e.j t = e.j (O k t))
    (hwild : (μ.map d) e.ordinary = 0)
    (hpos : 0 < differenceLaw (μ.map p) (condDistrib d p μ) e.ordinary) :
    Measurable (centerMap e μ d p) ∧
    (∀ k : K, ∀ᵐ x ∂μ, centerMap e μ d p (k • x) = k • centerMap e μ d p x) ∧
    (μ.map (centerMap e μ d p)) e.ordinary = 0 ∧
    ∃ a : ℝ≥0∞, 0 < a ∧
      ∀ᵐ y ∂μ.map p, ∃ S : Finset G, S.Nonempty ∧
        (∀ b ∈ S, condDistrib (centerMap e μ d p) p μ y {b} = a) ∧
        (∀ᵐ b ∂condDistrib (centerMap e μ d p) p μ y, b ∈ S) ∧
        (S.card : ℝ≥0∞) * a = 1 ∧
        (∀ b ∈ S, b ∉ e.ordinary) := by
  have hC (k : K) (z : G) : k • z ∈ e.ordinary ↔ z ∈ e.ordinary :=
    e.equiv_mem_ordinary_iff (MulDistribMulAction.toMulEquiv G k) (O k) (he k) z
  obtain ⟨a, ha, hmass, hfib⟩ := positive_mass_finite_centers e μ d p hd hp
    (sampledMass_invariant e μ d p hd hp hde hpe hC) hpos
  have ha' : ∀ᵐ x ∂μ, cosetMass e (condDistrib d p μ) (p x, d x) ≠ 0 :=
    hmass.mono fun _ h => by rw [h]; exact ha.ne'
  have hbzero : (μ.map (centerMap e μ d p)) e.ordinary = 0 := by
    rw [centerMap_law_ordinary e μ d p hd hp, hwild]
  refine ⟨measurable_centerMap e μ d p hd hp,
    centerMap_equivariant e μ d p hd hp hde hpe O he ha', hbzero, a, ha, ?_⟩
  have hz : ∀ᵐ y ∂μ.map p, centerKernel e (condDistrib d p μ) y e.ordinary = 0 := by
    rw [← centerKernel_comp_map e μ d p hd hp,
      Measure.bind_apply e.measurableSet_ordinary (centerKernel e _).aemeasurable] at hbzero
    exact (lintegral_eq_zero_iff ((centerKernel e _).measurable_coe e.measurableSet_ordinary)).mp
      hbzero
  have hcd := condDistrib_centerMap e μ d p hd hp
  filter_upwards [hfib, hz, hcd] with y hy hyzero hycd
  obtain ⟨S, hS, hSa, hSm, hSc⟩ := hy
  have hSa' (b : G) (hb : b ∈ S) : centerKernel e (condDistrib d p μ) y {b} = a := by
    rw [centerKernel_apply, Measure.map_apply (e.measurable_center_fixed _)
      (measurableSet_singleton b)]
    exact hSa b hb
  refine ⟨S, hS, ?_, ?_, hSc, ?_⟩
  · intro b hb
    rw [hycd]
    exact hSa' b hb
  · rw [hycd, centerKernel_apply]
    exact (ae_map_iff (e.measurable_center_fixed _).aemeasurable S.measurableSet).mpr hSm
  · intro b hb hbC
    have hle : centerKernel e (condDistrib d p μ) y {b} ≤
        centerKernel e (condDistrib d p μ) y e.ordinary :=
      measure_mono (Set.singleton_subset_iff.mpr hbC)
    rw [hSa' b hb, hyzero] at hle
    exact (not_le_of_gt ha) hle

end EuclideanFiveColor.RelativeCenters

namespace PlaneFiveColor.Spectral
open MeasureTheory ProbabilityTheory
open EuclideanFiveColor.RelativeCenters
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

private noncomputable def ordinaryEmbedding : EuclideanFiveColor.CosetCenter.Embedding D :=
  ⟨jHom, j_measurableEmbedding⟩

@[simp] theorem ordinaryEmbedding_j (t : ℂ) : ordinaryEmbedding.j t = j t := rfl
@[simp] theorem ordinaryEmbedding_ordinary : ordinaryEmbedding.ordinary = C := rfl

private noncomputable def frequencyIsometry (u : K) : ℂ →ₗᵢ[ℝ] ℂ where
  toFun z := conj (u.val : ℂ) * z
  map_add' _ _ := mul_add _ _ _
  map_smul' a z := by simp only [RingHom.id_apply, mul_smul_comm]
  norm_map' z := by
    change ‖conj (u.val : ℂ) * z‖ = ‖z‖
    rw [norm_mul, Complex.norm_conj, Circle.norm_coe, one_mul]

private noncomputable def frequencyRotation (u : K) : ℂ ≃ₗᵢ[ℝ] ℂ :=
  (frequencyIsometry u).toLinearIsometryEquiv rfl

@[simp] theorem frequencyRotation_apply (u : K) (z : ℂ) :
    frequencyRotation u z = conj (u.val : ℂ) * z := rfl

theorem action_ordinaryEmbedding (u : K) (t : ℂ) :
    u • ordinaryEmbedding.j t = ordinaryEmbedding.j (frequencyRotation u t) :=
  scalar_j (kCoeff u) t

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MulAction K X] [MulAction K Y]
  [MeasurableConstSMul K X] [MeasurableConstSMul K Y]

theorem wild_map_of_equivariant (μ : Measure X) [IsProbabilityMeasure μ]
    [SMulInvariantMeasure K X μ] (b : X → D) (hb : Measurable b)
    (hbe : ∀ k : K, ∀ᵐ x ∂μ, b (k • x) = k • b x)
    (hC : (μ.map b) C = 0) : IsWild (μ.map b) := by
  refine ⟨fun k => ⟨measurable_const_smul k, ?_⟩, hC⟩
  rw [Measure.map_map (measurable_const_smul k) hb]
  calc
    μ.map ((fun z : D => k • z) ∘ b) = μ.map (b ∘ (fun x : X => k • x)) :=
      Measure.map_congr ((hbe k).mono fun _ hx => hx.symm)
    _ = (μ.map (fun x : X => k • x)).map b :=
      (Measure.map_map hb (measurable_const_smul k)).symm
    _ = μ.map b := by rw [measurePreserving_smul k μ |>.map_eq]

theorem exact_finite_center_reduction
    (μ : Measure X) [IsProbabilityMeasure μ] [ErgodicSMul K X μ]
    (d : X → D) (p : X → Y) (hd : Measurable d) (hp : Measurable p)
    (hde : ∀ k : K, ∀ᵐ x ∂μ, d (k • x) = k • d x)
    (hpe : ∀ k : K, ∀ᵐ x ∂μ, p (k • x) = k • p x)
    (hwild : IsWild (μ.map d))
    (hpos : 0 < differenceLaw (μ.map p) (condDistrib d p μ) C) :
    ∃ b : X → D, Measurable b ∧
      (∀ k : K, ∀ᵐ x ∂μ, b (k • x) = k • b x) ∧
      IsWild (μ.map b) ∧
      ∃ a : ℝ≥0∞, 0 < a ∧
        ∀ᵐ y ∂μ.map p, ∃ S : Finset D, S.Nonempty ∧
          (∀ c ∈ S, condDistrib b p μ y {c} = a) ∧
          (∀ᵐ c ∂condDistrib b p μ y, c ∈ S) ∧
          (S.card : ℝ≥0∞) * a = 1 ∧
          (∀ c ∈ S, c ∉ C) := by
  obtain ⟨hbm, hbe, hbw, hfin⟩ := finite_center_reduction ordinaryEmbedding μ d p hd hp
    hde hpe frequencyRotation action_ordinaryEmbedding hwild.2 hpos
  exact ⟨centerMap ordinaryEmbedding μ d p, hbm, hbe,
    wild_map_of_equivariant μ _ hbm hbe hbw, hfin⟩

end PlaneFiveColor.Spectral

end

end ParishFactor
end

-- OAI.MeasureTheory.CompactFactors.Approximation
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

namespace EuclideanFiveColor.UniformEnumeration
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
variable {G Y : Type*} [MeasurableSpace G] [MeasurableSingletonClass G]
  [MeasurableSpace Y] [Nonempty G]

omit [Nonempty G] in
theorem list_of_uniform_atoms (κ : Measure G)
    (S : Finset G) (a : ℝ≥0∞) (hmass : ∀ d ∈ S, κ {d} = a)
    (hsupp : ∀ᵐ d ∂κ, d ∈ S) (hc : (S.card : ℝ≥0∞)*a=1) :
    ∃ g : Fin S.card → G, κ = (S.card : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (g i) := by
  classical
  let e := S.equivFin
  let g : Fin S.card → G := fun i => (e.symm i).val
  have heq := Measure.ae_mem_finset_iff.mp hsupp
  have ha : a = (S.card : ℝ≥0∞)⁻¹ := by
    have hn : (S.card : ℝ≥0∞) ≠ 0 := by intro h; rw [h, zero_mul] at hc; exact zero_ne_one hc
    calc
      a = 1*a := by simp
      _ = ((S.card : ℝ≥0∞)⁻¹ * S.card)*a := by rw [ENNReal.inv_mul_cancel hn (by simp)]
      _ = (S.card : ℝ≥0∞)⁻¹ := by rw [mul_assoc, hc, mul_one]
  refine ⟨g, ?_⟩
  calc
    κ = ∑ d ∈ S, κ {d} • Measure.dirac d := heq
    _ = ∑ d ∈ S, (S.card : ℝ≥0∞)⁻¹ • Measure.dirac d :=
      Finset.sum_congr rfl (fun d hd => by rw [hmass d hd, ha])
    _ = (S.card : ℝ≥0∞)⁻¹ • ∑ d ∈ S, Measure.dirac d := Finset.smul_sum.symm
    _ = (S.card : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (g i) := by
      congr 1
      rw [← Finset.sum_coe_sort S (fun d => Measure.dirac d)]
      exact (Equiv.sum_comp e.symm (fun d : S => Measure.dirac d.val)).symm

theorem constant_uniform_lists (ν : Measure Y) [IsProbabilityMeasure ν]
    (κ : Kernel Y G) [IsMarkovKernel κ] (a : ℝ≥0∞) (ha : 0 < a)
    (hf : ∀ᵐ y ∂ν, ∃ S : Finset G, S.Nonempty ∧
      (∀ d ∈ S, κ y {d} = a) ∧ (∀ᵐ d ∂κ y, d ∈ S) ∧ (S.card : ℝ≥0∞)*a=1) :
    ∃ m : ℕ, 0 < m ∧ ∃ g : Y → Fin m → G,
      ∀ᵐ y ∂ν, κ y = (m : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (g y i) := by
  classical
  obtain ⟨y₀, S₀, hS₀, _, _, hc₀⟩ := hf.exists
  let m := S₀.card
  have hm : 0 < m := Finset.card_pos.mpr hS₀
  have haT : a ≠ ⊤ := by
    intro h
    rw [h, ENNReal.mul_top (by exact_mod_cast hm.ne')] at hc₀
    exact ENNReal.top_ne_one hc₀
  have hlist : ∀ᵐ y ∂ν, ∃ g : Fin m → G,
      κ y = (m : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (g i) := by
    filter_upwards [hf] with y hy
    obtain ⟨S, _hS, hSa, hSupp, hc⟩ := hy
    have hcard : S.card = m := by
      have hh : (S.card : ℝ≥0∞) = (m : ℝ≥0∞) :=
        (ENNReal.mul_right_inj ha.ne' haT).mp (by simpa only [mul_comm] using hc.trans hc₀.symm)
      exact_mod_cast hh
    obtain ⟨g, hg⟩ := list_of_uniform_atoms (κ y) S a hSa hSupp hc
    have hh : (∑ j : Fin S.card, Measure.dirac (g j)) =
        ∑ i : Fin m, Measure.dirac (g (Fin.cast hcard.symm i)) :=
      (Equiv.sum_comp (finCongr hcard.symm) (fun j => Measure.dirac (g j))).symm
    refine ⟨fun i => g (Fin.cast hcard.symm i), ?_⟩
    calc
      κ y = (S.card : ℝ≥0∞)⁻¹ • ∑ i : Fin m, Measure.dirac (g (Fin.cast hcard.symm i)) := hg.trans (congrArg ((S.card : ℝ≥0∞)⁻¹ • ·) hh)
      _ = _ := by congr 2; exact_mod_cast hcard
  let g : Y → Fin m → G := fun y => if h : ∃ g : Fin m → G,
      κ y = (m : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (g i) then h.choose else fun _ => Classical.choice inferInstance
  refine ⟨m, hm, g, ?_⟩
  filter_upwards [hlist] with y hy
  simpa only [g, dif_pos hy] using hy.choose_spec

end EuclideanFiveColor.UniformEnumeration

open MeasureTheory ProbabilityTheory
namespace EuclideanFiveColor.DifferenceInvariant
variable {G Y : Type*} [CommGroup G] [MeasurableSpace G]
  [MeasurableMul₂ G] [MeasurableInv G] [MeasurableSpace Y]

private noncomputable def differenceLaw (ν : Measure Y) (κ : Kernel Y G) [IsMarkovKernel κ] : Measure G :=
  ((κ ×ₖ κ) ∘ₘ ν).map (fun p : G × G => p.1 / p.2)

lemma invariant (ν : Measure Y) [IsProbabilityMeasure ν]
    (κ : Kernel Y G) [IsMarkovKernel κ]
    (R : Y → Y) (hR : MeasurePreserving R ν ν)
    (T : G →* G) (hT : Measurable T)
    (he : ∀ᵐ y ∂ν, κ (R y) = (κ y).map T) :
    MeasurePreserving T (differenceLaw ν κ) (differenceLaw ν κ) := by
  have hprod : (((κ ×ₖ κ) ∘ₘ ν).map (Prod.map T T)) = ((κ ×ₖ κ) ∘ₘ ν) := by
    ext s hs
    rw [Measure.map_apply (hT.prodMap hT) hs,
      Measure.bind_apply ((hT.prodMap hT) hs) (κ ×ₖ κ).aemeasurable,
      Measure.bind_apply hs (κ ×ₖ κ).aemeasurable]
    calc
      (∫⁻ y, (κ ×ₖ κ) y ((Prod.map T T) ⁻¹' s) ∂ν) =
          ∫⁻ y, (κ ×ₖ κ) (R y) s ∂ν := by
        apply lintegral_congr_ae
        filter_upwards [he] with y hy
        rw [Kernel.prod_apply, Kernel.prod_apply, hy,
          Measure.map_prod_map _ _ hT hT, Measure.map_apply (hT.prodMap hT) hs]
      _ = ∫⁻ y, (κ ×ₖ κ) y s ∂ν := hR.lintegral_comp (Kernel.measurable_coe _ hs)
  have hdiv : Measurable (fun p : G × G => p.1 / p.2) := measurable_fst.div measurable_snd
  refine ⟨hT, ?_⟩
  rw [differenceLaw, Measure.map_map hT hdiv]
  calc
    (((κ ×ₖ κ) ∘ₘ ν).map (T ∘ (fun p : G × G => p.1 / p.2))) =
        ((κ ×ₖ κ) ∘ₘ ν).map ((fun p : G × G => p.1 / p.2) ∘ Prod.map T T) := by
      congr 1
      funext p
      exact map_div T p.1 p.2
    _ = (((κ ×ₖ κ) ∘ₘ ν).map (Prod.map T T)).map (fun p : G × G => p.1 / p.2) :=
      (Measure.map_map hdiv (hT.prodMap hT)).symm
    _ = _ := by rw [hprod]

end EuclideanFiveColor.DifferenceInvariant

namespace EuclideanFiveColor.CompactApproximation
open MeasureTheory
open scoped BigOperators
variable {K Y W : Type*} [SMul K Y] [MeasurableSpace Y] [MeasurableSpace W]

private def Scalar (ν : Measure Y) (q : Y → W) : Prop :=
  ∀ H : Y → ℂ, Measurable H → (∃ C : ℝ, ∀ y, ‖H y‖ ≤ C) →
  ∀ ε : ℝ, 0 < ε → ∃ (r : ℕ) (B C : ℝ) (Hf : Fin r → Y → ℂ),
    0 ≤ B ∧ 0 ≤ C ∧ (∀ i, Measurable (Hf i)) ∧ (∀ y, ∑ i, ‖Hf i y‖ ≤ C) ∧
    ∀ k : K, ∃ a : W → Fin r → ℂ, Measurable a ∧ (∀ w, ‖a w‖ ≤ B) ∧
      Integrable (fun y => dist (H (k • y)) (∑ i, a (q y) i * Hf i y)^2) ν ∧
      (∫ y, dist (H (k • y)) (∑ i, a (q y) i * Hf i y)^2 ∂ν) < ε^2

private def Vector (ν : Measure Y) (q : Y → W) : Prop :=
  ∀ (m : ℕ) (H : Y → Fin m → ℂ), Measurable H →
  (∃ C : ℝ, ∀ y, ‖H y‖ ≤ C) → ∀ ε : ℝ, 0 < ε →
  ∃ (r : ℕ) (B C : ℝ) (Hf : Fin r → Y → Fin m → ℂ),
    0 ≤ B ∧ 0 ≤ C ∧ (∀ i, Measurable (Hf i)) ∧ (∀ y, ∑ i, ‖Hf i y‖ ≤ C) ∧
    ∀ k : K, ∃ a : W → Fin r → ℂ, Measurable a ∧ (∀ w, ‖a w‖ ≤ B) ∧
      Integrable (fun y => dist (H (k • y)) (∑ i, a (q y) i • Hf i y)^2) ν ∧
      (∫ y, dist (H (k • y)) (∑ i, a (q y) i • Hf i y)^2 ∂ν) < ε^2

lemma pi_dist_sq_le_sum {I : Type*} [Fintype I] (a b : I → ℂ) :
    dist a b ^ 2 ≤ ∑ i, dist (a i) (b i)^2 := by
  have hs : 0 ≤ ∑ i, dist (a i) (b i)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hn : dist a b ≤ Real.sqrt (∑ i, dist (a i) (b i)^2) := by
    rw [dist_eq_norm, pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
    intro i
    change ‖a i - b i‖ ≤ _
    rw [← dist_eq_norm]
    apply (Real.le_sqrt (dist_nonneg) hs).mpr
    exact Finset.single_le_sum (fun j _ => sq_nonneg (dist (a j) (b j))) (Finset.mem_univ i)
  nlinarith [Real.sq_sqrt hs, Real.sqrt_nonneg (∑ i, dist (a i) (b i)^2), dist_nonneg (x := a) (y := b)]

lemma vector_of_scalar (ν : Measure Y) [IsProbabilityMeasure ν]
    (q : Y → W) (hq : Measurable q) [MeasurableConstSMul K Y]
    (hs : Scalar (K := K) ν q) : Vector (K := K) ν q := by
  classical
  intro m H hH hHb ε hε
  let δ : ℝ := ε / (m+1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hcoord (j : Fin m) : ∃ (r : ℕ) (B C : ℝ) (Hf : Fin r → Y → ℂ),
      0 ≤ B ∧ 0 ≤ C ∧ (∀ i, Measurable (Hf i)) ∧ (∀ y, ∑ i, ‖Hf i y‖ ≤ C) ∧
      ∀ k : K, ∃ a : W → Fin r → ℂ, Measurable a ∧ (∀ w, ‖a w‖ ≤ B) ∧
        Integrable (fun y => dist (H (k • y) j) (∑ i, a (q y) i * Hf i y)^2) ν ∧
        (∫ y, dist (H (k • y) j) (∑ i, a (q y) i * Hf i y)^2 ∂ν) < δ^2 := by
    apply hs (fun y => H y j) ((measurable_pi_iff.mp hH) j) _ δ hδ
    obtain ⟨C, hC⟩ := hHb
    exact ⟨C, fun y => (norm_le_pi_norm (H y) j).trans (hC y)⟩
  choose r B C Hf hB hC hHm hHb hA using hcoord
  let I := (j : Fin m) × Fin (r j)
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let V : I → Y → Fin m → ℂ := fun s y => Pi.single s.1 (Hf s.1 s.2 y)
  have hV (s : I) : Measurable (V s) := by
    apply Measurable.of_eval
    intro j
    by_cases h : s.1 = j
    · subst j
      simpa [V] using hHm s.1 s.2
    · simp only [V, Pi.single_apply, Ne.symm h, ite_false]
      exact measurable_const
  have hVnorm (s : I) (y : Y) : ‖V s y‖ ≤ ‖Hf s.1 s.2 y‖ := by
    rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro j
    by_cases h : s.1 = j
    · subst j; simp [V]
    · simp [V, h]
  refine ⟨Fintype.card I, ∑ j, B j, ∑ j, C j, fun i => V (e i),
    Finset.sum_nonneg (fun j _ => hB j), Finset.sum_nonneg (fun j _ => hC j),
    fun i => hV (e i), ?_, ?_⟩
  · intro y
    change (∑ i, (fun s : I => ‖V s y‖) (e i)) ≤ _
    rw [Equiv.sum_comp e (fun s : I => ‖V s y‖)]
    calc
      ∑ s : I, ‖V s y‖ ≤ ∑ s : I, ‖Hf s.1 s.2 y‖ := Finset.sum_le_sum (fun s _ => hVnorm s y)
      _ = ∑ j, ∑ i, ‖Hf j i y‖ := Fintype.sum_sigma _
      _ ≤ ∑ j, C j := Finset.sum_le_sum (fun j _ => hHb j y)
  · intro k
    choose a ham hab hai hae using fun j => hA j k
    let a' : W → I → ℂ := fun w s => a s.1 w s.2
    have hap (w : W) : ‖fun i => a' w (e i)‖ ≤ ∑ j, B j := by
      rw [pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun j _ => hB j))]
      intro i
      exact ((norm_le_pi_norm (a (e i).1 w) (e i).2).trans (hab (e i).1 w)).trans
        (Finset.single_le_sum (fun j _ => hB j) (Finset.mem_univ _))
    have ham' : Measurable (fun w i => a' w (e i)) := by
      apply Measurable.of_eval
      intro i
      exact (measurable_pi_iff.mp (ham (e i).1)) (e i).2
    let A : Y → Fin m → ℂ := fun y => ∑ s : I, a' (q y) s • V s y
    have hAeq (y : Y) (j : Fin m) : A y j = ∑ i, a j (q y) i * Hf j i y := by
      change (∑ s : I, a' (q y) s • V s y) j = _
      simp only [Finset.sum_apply, Pi.smul_apply]
      rw [Fintype.sum_sigma]
      simp [a', V, Pi.single_apply]
    have hAm : Measurable A := by
      apply Measurable.of_eval
      intro j
      simp_rw [hAeq]
      exact Finset.measurable_sum _ (fun i _ => ((measurable_pi_iff.mp (ham j)) i |>.comp hq).mul (hHm j i))
    have hem : AEStronglyMeasurable (fun y => dist (H (k • y)) (A y)^2) ν :=
      ((hH.comp (measurable_const_smul k)).dist hAm |>.pow_const 2).aestronglyMeasurable
    have hsint : Integrable (fun y => ∑ j, dist (H (k • y) j) (A y j)^2) ν := by
      apply integrable_finsetSum
      intro j _
      simpa only [hAeq] using hai j
    have hbound (y : Y) : dist (H (k • y)) (A y)^2 ≤ ∑ j, dist (H (k • y) j) (A y j)^2 :=
      pi_dist_sq_le_sum _ _
    have hint : Integrable (fun y => dist (H (k • y)) (A y)^2) ν :=
      hsint.mono' hem (Filter.Eventually.of_forall (fun y => by simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (dist (H (k • y)) (A y)))] using hbound y))
    have hbudget : (∫ y, dist (H (k • y)) (A y)^2 ∂ν) < ε^2 := by
      calc
        _ ≤ ∫ y, ∑ j, dist (H (k • y) j) (A y j)^2 ∂ν := integral_mono hint hsint hbound
        _ = ∑ j, ∫ y, dist (H (k • y) j) (A y j)^2 ∂ν := integral_finsetSum _ (fun j _ => by simpa only [hAeq] using hai j)
        _ ≤ ∑ _j : Fin m, δ^2 := Finset.sum_le_sum (fun j _ => by simpa only [hAeq] using (hae j).le)
        _ = (m : ℝ) * δ^2 := by simp
        _ < ε^2 := by
          dsimp [δ]
          have hm : (0 : ℝ) < m+1 := by positivity
          rw [div_pow, ← mul_div_assoc, div_lt_iff₀ (sq_pos_of_pos hm)]
          nlinarith [sq_nonneg (m : ℝ), sq_pos_of_pos hε]
    have hAe (y : Y) : (∑ i, a' (q y) (e i) • V (e i) y) = A y :=
      Equiv.sum_comp e (fun s => a' (q y) s • V s y)
    refine ⟨fun w i => a' w (e i), ham', hap, ?_, ?_⟩
    · simpa only [hAe] using hint
    · simpa only [hAe] using hbudget

end EuclideanFiveColor.CompactApproximation

namespace EuclideanFiveColor.KernelSupport
open MeasureTheory
variable {K X Y : Type*} [Group K] [MeasurableSpace X] [MeasurableSpace Y]
  [MulAction K X] [MulAction K Y] [MeasurableConstSMul K X] [MeasurableConstSMul K Y]
lemma factor_smul_preserving (μ : Measure X) [SMulInvariantMeasure K X μ]
    (p : X → Y) (hp : Measurable p)
    (hpe : ∀ k : K, ∀ᵐ x ∂μ, p (k • x) = k • p x) (k : K) :
    MeasurePreserving (fun y : Y => k • y) (μ.map p) (μ.map p) := by
  refine ⟨measurable_const_smul k, ?_⟩
  rw [Measure.map_map (measurable_const_smul k) hp]
  calc
    μ.map ((fun y : Y => k • y) ∘ p) = μ.map (p ∘ (fun x : X => k • x)) :=
      Measure.map_congr ((hpe k).mono fun _ hx => hx.symm)
    _ = (μ.map (fun x : X => k • x)).map p :=
      (Measure.map_map hp (measurable_const_smul k)).symm
    _ = μ.map p := by rw [measurePreserving_smul k μ |>.map_eq]
end EuclideanFiveColor.KernelSupport

namespace PlaneFiveColor.Spectral
open MeasureTheory ProbabilityTheory EuclideanFiveColor
open scoped BigOperators ENNReal
variable [Carrier]
variable {X Y W : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace W]
  [MulAction K X] [MulAction K Y]
  [MeasurableConstSMul K X] [MeasurableConstSMul K Y]

lemma relative_difference_invariant (μ : Measure X) [IsProbabilityMeasure μ]
    [SMulInvariantMeasure K X μ] (b : X → D) (p : X → Y)
    (hb : Measurable b) (hp : Measurable p)
    (hbe : ∀ k : K, ∀ᵐ x ∂μ, b (k • x) = k • b x)
    (hpe : ∀ k : K, ∀ᵐ x ∂μ, p (k • x) = k • p x) (k : K) :
    MeasurePreserving (fun d : D => k • d)
      (DifferenceFourier.differenceLaw (μ.map p) (condDistrib b p μ))
      (DifferenceFourier.differenceLaw (μ.map p) (condDistrib b p μ)) := by
  haveI := Measure.isProbabilityMeasure_map (μ := μ) hp.aemeasurable
  have he := KernelSupport.condDistrib_equivariant μ b p hb hp
    (MeasurableEquiv.smul k) (MeasurableEquiv.smul k) (fun d : D => k • d)
    (measurable_const_smul k) (measurePreserving_smul k μ) (hpe k) (hbe k)
  exact DifferenceInvariant.invariant (μ.map p) (condDistrib b p μ)
    (fun y : Y => k • y) (KernelSupport.factor_smul_preserving μ p hp hpe k)
    (scalarHom (kCoeff k)) (measurable_const_smul k) he

lemma finite_encoding_approximation_of_compact
    [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]
    [StandardBorelSpace W] [Nonempty W]
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure K X μ]
    (p : X → Y) (q : Y → W) (b : X → D)
    (hp : Measurable p) (hq : Measurable q) (hb : Measurable b)
    (hpe : ∀ k : K, ∀ᵐ x ∂μ, p (k • x) = k • p x)
    (hbe : ∀ k : K, ∀ᵐ x ∂μ, b (k • x) = k • b x)
    (m : ℕ) (hm : 0 < m) (g : Y → Fin m → D)
    (hg : ∀ᵐ y ∂μ.map p, condDistrib b p μ y =
      (m : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (g y i))
    (hc : CompactApproximation.Scalar (K := K) (μ.map p) q) :
    FiniteEncodingApproximation μ p q b m := by
  classical
  haveI := Measure.isProbabilityMeasure_map (μ := μ) hp.aemeasurable
  let H₀ : Y → Fin m → ℂ := PhaseEncoding.kernelEncoding (condDistrib b p μ)
    (fun d => (eval 1 d : ℂ)) m
  have hH₀ : Measurable H₀ :=
    PhaseEncoding.measurable_kernelEncoding _ _ (measurable_eval_coe 1) m
  obtain ⟨A, hA⟩ := PhaseEncoding.exists_encoding_bound m
  have hHB : ∀ᵐ y ∂μ.map p, ‖H₀ y‖ ≤ max A 0 := by
    filter_upwards [hg] with y hy
    have he := PhaseEncoding.kernelEncoding_eq_encoding (condDistrib b p μ) (eval 1) m hm y (g y) hy
    change ‖PhaseEncoding.kernelEncoding (condDistrib b p μ) (fun d => (eval 1 d : ℂ)) m y‖ ≤ max A 0
    rw [he]
    exact (hA (fun i => eval 1 (g y i))).trans (le_max_left _ _)
  let H : Y → Fin m → ℂ := fun y => if ‖H₀ y‖ ≤ max A 0 then H₀ y else 0
  have hH : Measurable H := hH₀.piecewise (measurableSet_le hH₀.norm measurable_const) measurable_const
  have hHbound : ∀ y, ‖H y‖ ≤ max A 0 := by
    intro y
    by_cases hy : ‖H₀ y‖ ≤ max A 0
    · simpa only [H, if_pos hy] using hy
    · simp only [H, if_neg hy, norm_zero]
      exact le_max_right _ _
  have hHeq : H =ᵐ[μ.map p] H₀ := hHB.mono fun y hy => if_pos hy
  have hv := CompactApproximation.vector_of_scalar (μ.map p) q hq hc
  intro γ hγ
  obtain ⟨r, B, C, Hf, hB, hC, _hHm, hHf, ha⟩ := hv m H hH ⟨max A 0, hHbound⟩ γ hγ
  refine ⟨r, B, C, Hf, hB, hC, hHf, ?_⟩
  intro k
  obtain ⟨a, _ham, hab, hai, hae⟩ := ha k
  have hker := KernelSupport.condDistrib_equivariant μ b p hb hp
    (MeasurableEquiv.smul k) (MeasurableEquiv.smul k) (fun d : D => k • d)
    (measurable_const_smul k) (measurePreserving_smul k μ) (hpe k) (hbe k)
  have hcov := PhaseEncoding.kernelEncoding_covariance (μ.map p) (condDistrib b p μ)
    (fun y : Y => k • y) (fun d : D => k • d) (measurable_const_smul k)
    (fun d => (eval 1 d : ℂ)) (measurable_eval_coe 1) m hker
  have heq : ∀ᵐ y ∂μ.map p, H (k • y) =
      PhaseEncoding.kernelEncoding (condDistrib b p μ) (fun d => (eval (kCoeff k) d : ℂ)) m y := by
    filter_upwards [(KernelSupport.factor_smul_preserving μ p hp hpe k).quasiMeasurePreserving.ae hHeq,
      hcov] with y hy hc'
    exact hy.trans (by simpa only [Function.comp_def, eval_smul_one] using hc')
  have he : (fun y => dist (H (k • y)) (∑ i, a (q y) i • Hf i y)^2) =ᵐ[μ.map p]
      (fun y => dist (PhaseEncoding.kernelEncoding (condDistrib b p μ)
        (fun d => (eval (kCoeff k) d : ℂ)) m y) (∑ i, a (q y) i • Hf i y)^2) := by
    filter_upwards [heq] with y hy
    rw [hy]
  have hai' := hai.congr he
  refine ⟨a, hab, hai'.comp_measurable hp, ?_⟩
  rw [← integral_map hp.aemeasurable hai'.aestronglyMeasurable,
    ← integral_congr_ae he]
  exact hae

theorem relative_singularity_successor
    [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]
    [StandardBorelSpace W] [Nonempty W]
    [MulAction K W] [MeasurableConstSMul K W]
    (μ : Measure X) [IsProbabilityMeasure μ] [ErgodicSMul K X μ]
    (d : X → D) (p : X → Y) (q : Y → W)
    (hd : Measurable d) (hp : Measurable p) (hq : Measurable q)
    (hde : ∀ k : K, ∀ᵐ x ∂μ, d (k • x) = k • d x)
    (hpe : ∀ k : K, ∀ᵐ x ∂μ, p (k • x) = k • p x)
    (hqe : ∀ k : K, ∀ᵐ y ∂μ.map p, q (k • y) = k • q y)
    (hwild : IsWild (μ.map d))
    (hc : CompactApproximation.Scalar (K := K) (μ.map p) q)
    (hprev : ∀ b : X → D, Measurable b →
      (∀ k : K, ∀ᵐ x ∂μ, b (k • x) = k • b x) → IsWild (μ.map b) →
      DifferenceFourier.differenceLaw (μ.map (q ∘ p)) (condDistrib b (q ∘ p) μ) C = 0) :
    DifferenceFourier.differenceLaw (μ.map p) (condDistrib d p μ) C = 0 := by
  haveI := Measure.isProbabilityMeasure_map (μ := μ) hp.aemeasurable
  by_contra hn
  have hpos : 0 < RelativeCenters.differenceLaw (μ.map p) (condDistrib d p μ) C :=
    pos_iff_ne_zero.mpr hn
  obtain ⟨b, hb, hbe, hbw, a, ha, hf⟩ := exact_finite_center_reduction μ d p hd hp hde hpe hwild hpos
  obtain ⟨m, hm, g, hg⟩ := UniformEnumeration.constant_uniform_lists (μ.map p)
    (condDistrib b p μ) a ha (hf.mono fun y ⟨S, hS, hSa, hSupp, hcS, _⟩ =>
      ⟨S, hS, hSa, hSupp, hcS⟩)
  have hcomp : ∀ k : K, ∀ᵐ x ∂μ, (q ∘ p) (k • x) = k • (q ∘ p) x := by
    intro k
    filter_upwards [hpe k, ae_of_ae_map hp.aemeasurable (hqe k)] with x hx hy
    simp only [Function.comp_def, hx, hy]
  have hpwild : IsWild (DifferenceFourier.differenceLaw (μ.map (q ∘ p)) (condDistrib b (q ∘ p) μ)) :=
    ⟨relative_difference_invariant μ b (q ∘ p) hb (hq.comp hp) hbe hcomp,
      hprev b hb hbe hbw⟩
  exact finite_uniform_successor_contradiction μ p q b hp hq hb m hm g hg hpwild
    (finite_encoding_approximation_of_compact μ p q b hp hq hb hpe hbe m hm g hg hc)

end PlaneFiveColor.Spectral

namespace EuclideanFiveColor.CompactApproximation
open MeasureTheory
open scoped BigOperators
variable {K Y Z W : Type*} [SMul K Y] [SMul K Z]
  [MeasurableSpace Y] [MeasurableSpace Z] [MeasurableSpace W]

private def At (ν : Measure Y) (q : Y → W) (m : ℕ) (H : Y → Fin m → ℂ) (ε : ℝ) : Prop :=
  ∃ (r : ℕ) (B C : ℝ) (Hf : Fin r → Y → Fin m → ℂ),
    0 ≤ B ∧ 0 ≤ C ∧ (∀ i, Measurable (Hf i)) ∧ (∀ y, ∑ i, ‖Hf i y‖ ≤ C) ∧
    ∀ k : K, ∃ a : W → Fin r → ℂ, Measurable a ∧ (∀ w, ‖a w‖ ≤ B) ∧
      Integrable (fun y => dist (H (k • y)) (∑ i, a (q y) i • Hf i y)^2) ν ∧
      (∫ y, dist (H (k • y)) (∑ i, a (q y) i • Hf i y)^2 ∂ν) < ε^2

lemma lift_at
    (ν : Measure Y) [IsProbabilityMeasure ν]
    (p : Y → Z) (q : Z → W) (hp : Measurable p) (hq : Measurable q)
    [MeasurableConstSMul K Y] [MeasurableConstSMul K Z]
    (hpres : ∀ k : K, MeasurePreserving (fun y : Y => k • y) ν ν)
    (hpe : ∀ k : K, ∀ᵐ y ∂ν, p (k • y) = k • p y)
    (m : ℕ) (H : Y → Fin m → ℂ) (H₀ : Z → Fin m → ℂ)
    (hH : Measurable H) (hH₀ : Measurable H₀)
    (hB₀ : ∃ C : ℝ, ∀ z, ‖H₀ z‖ ≤ C)
    (ε : ℝ) (hε : 0 < ε)
    (hi : Integrable (fun y => dist (H y) (H₀ (p y))^2) ν)
    (he : (∫ y, dist (H y) (H₀ (p y))^2 ∂ν) < (ε/2)^2)
    (hc : Vector (K := K) (ν.map p) q) : At (K := K) ν (q ∘ p) m H ε := by
  classical
  obtain ⟨r, B, C, Hf, hB, hC, hHm, hHf, ha⟩ := hc m H₀ hH₀ hB₀ (ε/2) (by positivity)
  refine ⟨r, B, C, fun i => Hf i ∘ p, hB, hC, fun i => (hHm i).comp hp,
    fun y => hHf (p y), ?_⟩
  intro k
  obtain ⟨a, ham, hab, hai, hae⟩ := ha k
  let F : Y → Fin m → ℂ := fun y => ∑ i, a (q (p y)) i • Hf i (p y)
  have hFm : Measurable F := by
    exact Finset.measurable_sum _ (fun i _ =>
      (((measurable_pi_iff.mp ham) i).comp (hq.comp hp)).smul ((hHm i).comp hp))
  let e₁ : Y → ℝ := fun y => dist (H (k • y)) (H₀ (k • p y))^2
  let e₂ : Y → ℝ := fun y => dist (H₀ (k • p y)) (F y)^2
  have heq : (fun y => dist (H (k • y)) (H₀ (p (k • y)))^2) =ᵐ[ν] e₁ :=
    (hpe k).mono fun y hy => by simp only [e₁, hy]
  have hi₁ : Integrable e₁ ν := ((hpres k).integrable_comp hi.aestronglyMeasurable |>.mpr hi).congr heq
  have he₁ : (∫ y, e₁ y ∂ν) < (ε/2)^2 := by
    have hm : AEStronglyMeasurable (fun y => dist (H y) (H₀ (p y))^2)
        (ν.map (fun y : Y => k • y)) := by
      rw [(hpres k).map_eq]
      exact hi.aestronglyMeasurable
    rw [← integral_congr_ae heq, ← integral_map (hpres k).measurable.aemeasurable hm,
      (hpres k).map_eq]
    exact he
  have hi₂ : Integrable e₂ ν := hai.comp_measurable hp
  have he₂ : (∫ y, e₂ y ∂ν) < (ε/2)^2 := by
    change (∫ y, dist (H₀ (k • p y)) (∑ i, a (q (p y)) i • Hf i (p y))^2 ∂ν) < _
    rw [← integral_map hp.aemeasurable hai.aestronglyMeasurable]
    exact hae
  have hmajor (y : Y) : dist (H (k • y)) (F y)^2 ≤ 2*(e₁ y + e₂ y) := by
    have ht := dist_triangle (H (k • y)) (H₀ (k • p y)) (F y)
    have hx := dist_nonneg (x := H (k • y)) (y := H₀ (k • p y))
    have hy := dist_nonneg (x := H₀ (k • p y)) (y := F y)
    have hz := dist_nonneg (x := H (k • y)) (y := F y)
    dsimp [e₁, e₂]
    nlinarith [sq_nonneg (dist (H (k • y)) (H₀ (k • p y)) - dist (H₀ (k • p y)) (F y))]
  have himaj : Integrable (fun y => 2*(e₁ y + e₂ y)) ν := (hi₁.add hi₂).const_mul 2
  have hint : Integrable (fun y => dist (H (k • y)) (F y)^2) ν :=
    himaj.mono' (((hH.comp (measurable_const_smul k)).dist hFm).pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs, abs_sq] using hmajor y)
  refine ⟨a, ham, hab, hint, ?_⟩
  calc
    (∫ y, dist (H (k • y)) (F y)^2 ∂ν) ≤ ∫ y, 2*(e₁ y + e₂ y) ∂ν :=
      integral_mono hint himaj hmajor
    _ = 2*((∫ y, e₁ y ∂ν) + ∫ y, e₂ y ∂ν) := by
      rw [integral_const_mul, integral_add hi₁ hi₂]
    _ < ε^2 := by nlinarith

end EuclideanFiveColor.CompactApproximation

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
    apply Measurable.of_eval
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

namespace PlaneFiveColor.Spectral
variable [Carrier]

section
open MeasureTheory ProbabilityTheory EuclideanFiveColor
open scoped BigOperators ENNReal
variable {X Y W : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace W]
  [MulAction K X] [MulAction K Y]
  [MeasurableConstSMul K X] [MeasurableConstSMul K Y]

omit [MulAction K X] [MulAction K Y] [MeasurableConstSMul K X] [MeasurableConstSMul K Y] in
lemma bounded_phase_encoding
    (μ : Measure X) [IsProbabilityMeasure μ] (p : X → Y) (b : X → D)
    (m : ℕ) (hm : 0 < m) (g : Y → Fin m → D)
    (hg : ∀ᵐ y ∂μ.map p, condDistrib b p μ y =
      (m : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (g y i)) :
    ∃ H : Y → Fin m → ℂ, Measurable H ∧ (∃ A : ℝ, 0 ≤ A ∧ ∀ y, ‖H y‖ ≤ A) ∧
      H =ᵐ[μ.map p] PhaseEncoding.kernelEncoding (condDistrib b p μ) (fun d => (eval 1 d : ℂ)) m := by
  classical
  let H₀ : Y → Fin m → ℂ := PhaseEncoding.kernelEncoding (condDistrib b p μ)
    (fun d => (eval 1 d : ℂ)) m
  have hH₀ : Measurable H₀ :=
    PhaseEncoding.measurable_kernelEncoding _ _ (measurable_eval_coe 1) m
  obtain ⟨A, hA⟩ := PhaseEncoding.exists_encoding_bound m
  have hHB : ∀ᵐ y ∂μ.map p, ‖H₀ y‖ ≤ max A 0 := by
    filter_upwards [hg] with y hy
    have he := PhaseEncoding.kernelEncoding_eq_encoding (condDistrib b p μ) (eval 1) m hm y (g y) hy
    change ‖PhaseEncoding.kernelEncoding (condDistrib b p μ) (fun d => (eval 1 d : ℂ)) m y‖ ≤ max A 0
    rw [he]
    exact (hA (fun i => eval 1 (g y i))).trans (le_max_left _ _)
  let H : Y → Fin m → ℂ := fun y => if ‖H₀ y‖ ≤ max A 0 then H₀ y else 0
  have hH : Measurable H := hH₀.piecewise (measurableSet_le hH₀.norm measurable_const) measurable_const
  have hHbound : ∀ y, ‖H y‖ ≤ max A 0 := by
    intro y
    by_cases hy : ‖H₀ y‖ ≤ max A 0
    · simpa only [H, if_pos hy] using hy
    · simp only [H, if_neg hy, norm_zero]
      exact le_max_right _ _
  exact ⟨H, hH, ⟨max A 0, le_max_right _ _, hHbound⟩, hHB.mono fun y hy => if_pos hy⟩

lemma finite_encoding_at_of_approximation
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure K X μ]
    (p : X → Y) (q : Y → W) (b : X → D)
    (hp : Measurable p) (hb : Measurable b)
    (hpe : ∀ k : K, ∀ᵐ x ∂μ, p (k • x) = k • p x)
    (hbe : ∀ k : K, ∀ᵐ x ∂μ, b (k • x) = k • b x)
    (m : ℕ) (H : Y → Fin m → ℂ)
    (hHeq : H =ᵐ[μ.map p] PhaseEncoding.kernelEncoding (condDistrib b p μ) (fun d => (eval 1 d : ℂ)) m)
    (γ : ℝ) (ha : CompactApproximation.At (K := K) (μ.map p) q m H γ) :
    FiniteEncodingApproximationAt μ p q b m γ := by
  classical
  let : IsProbabilityMeasure (μ.map p) := Measure.isProbabilityMeasure_map (hp).aemeasurable
  obtain ⟨r, B, C, Hf, hB, hC, _hHm, hHf, ha⟩ := ha
  refine ⟨r, B, C, Hf, hB, hC, hHf, ?_⟩
  intro k
  obtain ⟨a, _ham, hab, hai, hae⟩ := ha k
  have hker := KernelSupport.condDistrib_equivariant μ b p hb hp
    (MeasurableEquiv.smul k) (MeasurableEquiv.smul k) (fun d : D => k • d)
    (measurable_const_smul k) (measurePreserving_smul k μ) (hpe k) (hbe k)
  have hcov := PhaseEncoding.kernelEncoding_covariance (μ.map p) (condDistrib b p μ)
    (fun y : Y => k • y) (fun d : D => k • d) (measurable_const_smul k)
    (fun d => (eval 1 d : ℂ)) (measurable_eval_coe 1) m hker
  have heq : ∀ᵐ y ∂μ.map p, H (k • y) =
      PhaseEncoding.kernelEncoding (condDistrib b p μ) (fun d => (eval (kCoeff k) d : ℂ)) m y := by
    filter_upwards [(KernelSupport.factor_smul_preserving μ p hp hpe k).quasiMeasurePreserving.ae hHeq,
      hcov] with y hy hc'
    exact hy.trans (by simpa only [Function.comp_def, eval_smul_one] using hc')
  have he : (fun y => dist (H (k • y)) (∑ i, a (q y) i • Hf i y)^2) =ᵐ[μ.map p]
      (fun y => dist (PhaseEncoding.kernelEncoding (condDistrib b p μ)
        (fun d => (eval (kCoeff k) d : ℂ)) m y) (∑ i, a (q y) i • Hf i y)^2) := by
    filter_upwards [heq] with y hy
    rw [hy]
  have hai' := hai.congr he
  refine ⟨a, hab, hai'.comp_measurable hp, ?_⟩
  rw [← integral_map hp.aemeasurable hai'.aestronglyMeasurable,
    ← integral_congr_ae he]
  exact hae

end

open MeasureTheory ProbabilityTheory EuclideanFiveColor
open scoped BigOperators ENNReal
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]
  [MulAction K X] [MulAction K Y]
  [MeasurableConstSMul K X] [MeasurableConstSMul K Y]

omit [StandardBorelSpace Y] [Nonempty Y] in

theorem relative_singularity_limit
    {Z W : ℕ → Type*} [∀ n, MeasurableSpace (Z n)] [∀ n, MeasurableSpace (W n)]
    [∀ n, StandardBorelSpace (W n)] [∀ n, Nonempty (W n)]
    [∀ n, MulAction K (Z n)] [∀ n, MulAction K (W n)]
    [∀ n, MeasurableConstSMul K (Z n)] [∀ n, MeasurableConstSMul K (W n)]
    (μ : Measure X) [IsProbabilityMeasure μ] [ErgodicSMul K X μ]
    (d : X → D) (p : X → Y) (v : ∀ n, Y → Z n) (q : ∀ n, Z n → W n)
    (hd : Measurable d) (hp : Measurable p)
    (hv : ∀ n, Measurable (v n)) (hq : ∀ n, Measurable (q n))
    (hde : ∀ k : K, ∀ᵐ x ∂μ, d (k • x) = k • d x)
    (hpe : ∀ k : K, ∀ᵐ x ∂μ, p (k • x) = k • p x)
    (hve : ∀ n, ∀ k : K, ∀ᵐ y ∂μ.map p, v n (k • y) = k • v n y)
    (hqe : ∀ n, ∀ k : K, ∀ᵐ z ∂(μ.map p).map (v n), q n (k • z) = k • q n z)
    (hmono : Monotone (fun n => (inferInstance : MeasurableSpace (Z n)).comap (v n)))
    (hgen : (⨆ n, (inferInstance : MeasurableSpace (Z n)).comap (v n)) = (inferInstance : MeasurableSpace Y))
    (hwild : IsWild (μ.map d))
    (hc : ∀ n, CompactApproximation.Scalar (K := K) ((μ.map p).map (v n)) (q n))
    (hprev : ∀ n, ∀ b : X → D, Measurable b →
      (∀ k : K, ∀ᵐ x ∂μ, b (k • x) = k • b x) → IsWild (μ.map b) →
      DifferenceFourier.differenceLaw (μ.map ((q n ∘ v n) ∘ p))
        (condDistrib b ((q n ∘ v n) ∘ p) μ) C = 0) :
    DifferenceFourier.differenceLaw (μ.map p) (condDistrib d p μ) C = 0 := by
  classical
  let : IsProbabilityMeasure (μ.map p) := Measure.isProbabilityMeasure_map (hp).aemeasurable
  by_contra hn
  have hpos : 0 < RelativeCenters.differenceLaw (μ.map p) (condDistrib d p μ) C :=
    pos_iff_ne_zero.mpr hn
  obtain ⟨b, hb, hbe, hbw, a, ha, hf⟩ := exact_finite_center_reduction μ d p hd hp hde hpe hwild hpos
  obtain ⟨m, hm, g, hg⟩ := UniformEnumeration.constant_uniform_lists (μ.map p)
    (condDistrib b p μ) a ha (hf.mono fun y ⟨S, hS, hSa, hSupp, hcS, _⟩ =>
      ⟨S, hS, hSa, hSupp, hcS⟩)
  obtain ⟨ρ, c, N, hρ, hc', hN, harc⟩ := SmallArc.exists_small_arc_constants m hm
  let γ : ℝ := ((ρ^m/(m : ℝ))/100)/100
  have hγ : 0 < γ := by dsimp [γ]; positivity
  obtain ⟨H, hH, ⟨A, hA, hHB⟩, hHeq⟩ := bounded_phase_encoding μ p b m hm g hg
  obtain ⟨n, H₀, hH₀, hH₀B, hi, he⟩ := LimitDensity.generated_factor_approximation
    (μ.map p) v hv hmono hgen m H hH A hA hHB (γ/2) (by positivity)
  let : IsProbabilityMeasure ((μ.map p).map (v n)) := Measure.isProbabilityMeasure_map (hv n).aemeasurable
  have hvector := CompactApproximation.vector_of_scalar ((μ.map p).map (v n)) (q n) (hq n) (hc n)
  have happ := CompactApproximation.lift_at (μ.map p) (v n) (q n) (hv n) (hq n)
    (KernelSupport.factor_smul_preserving μ p hp hpe) (hve n) m H H₀ hH hH₀
    ⟨2*A, hH₀B⟩ γ hγ hi he hvector
  have henc := finite_encoding_at_of_approximation μ p (q n ∘ v n) b hp hb hpe hbe m H hHeq γ happ
  have heqv (k : K) : ∀ᵐ x ∂μ, ((q n ∘ v n) ∘ p) (k • x) = k • ((q n ∘ v n) ∘ p) x := by
    have hqp : ∀ᵐ y ∂μ.map p, q n (v n (k • y)) = k • q n (v n y) := by
      filter_upwards [hve n k, ae_of_ae_map (hv n).aemeasurable (hqe n k)] with y hy hz
      rw [hy, hz]
    filter_upwards [hpe k, ae_of_ae_map hp.aemeasurable hqp] with x hx hy
    simp only [Function.comp_def, hx, hy]
  have hpwild : IsWild (DifferenceFourier.differenceLaw (μ.map ((q n ∘ v n) ∘ p))
      (condDistrib b ((q n ∘ v n) ∘ p) μ)) :=
    ⟨relative_difference_invariant μ b ((q n ∘ v n) ∘ p) hb ((hq n).comp ((hv n).comp hp)) hbe heqv,
      hprev n b hb hbe hbw⟩
  exact finite_uniform_precision_contradiction μ p (q n ∘ v n) b hp ((hq n).comp (hv n)) hb m hm g hg
    hpwild ρ c N hρ hc' hN harc henc

end PlaneFiveColor.Spectral

namespace EuclideanFiveColor.ConditionalBase
open MeasureTheory ProbabilityTheory
variable {X Y G : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace G] [StandardBorelSpace G] [Nonempty G]
lemma condDistrib_given_const (μ : Measure X) [IsProbabilityMeasure μ]
    (b : X → G) (hb : Measurable b) (y₀ : Y) :
    condDistrib b (fun _ => y₀) μ y₀ = μ.map b := by
  have h := condDistrib_comp_map (μ := μ) (X := fun _ : X => y₀) measurable_const.aemeasurable hb.aemeasurable
  simpa only [Measure.map_const, measure_univ, one_smul,
    Measure.dirac_bind (condDistrib b (fun _ => y₀) μ).measurable] using h

lemma prod_given_const (μ : Measure X) [IsProbabilityMeasure μ]
    (b : X → G) (hb : Measurable b) (y₀ : Y) :
    ((condDistrib b (fun _ => y₀) μ ×ₖ condDistrib b (fun _ => y₀) μ) ∘ₘ μ.map (fun _ => y₀)) =
      (μ.map b).prod (μ.map b) := by
  rw [Measure.map_const, measure_univ, one_smul,
    Measure.dirac_bind (condDistrib b (fun _ => y₀) μ ×ₖ condDistrib b (fun _ => y₀) μ).measurable,
    Kernel.prod_apply, condDistrib_given_const μ b hb y₀]
end EuclideanFiveColor.ConditionalBase

namespace PlaneFiveColor.Spectral
variable [Carrier]

section
open MeasureTheory ProbabilityTheory EuclideanFiveColor
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
lemma relative_singularity_base (μ : Measure X) [IsProbabilityMeasure μ]
    (b : X → D) (hb : Measurable b) (y₀ : Y) (hw : IsWild (μ.map b)) :
    DifferenceFourier.differenceLaw (μ.map (fun _ : X => y₀))
      (condDistrib b (fun _ : X => y₀) μ) C = 0 := by
  let : IsProbabilityMeasure (μ.map b) := Measure.isProbabilityMeasure_map (hb).aemeasurable
  rw [DifferenceFourier.differenceLaw, ConditionalBase.prod_given_const μ b hb y₀,
    Measure.map_apply (f := fun p : D × D => p.1 / p.2) (measurable_fst.div measurable_snd) measurableSet_C]
  exact wild_independent_difference (μ.map b) hw
end
open MeasureTheory ProbabilityTheory EuclideanFiveColor
open scoped BigOperators ENNReal
local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩
variable {X Y W : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
  [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
  [MeasurableSpace W] [StandardBorelSpace W] [Nonempty W]

private def AmbientEncodingAt (μ : Measure X) [IsProbabilityMeasure μ] (p : X → Y) (q : X → W)
    (b : X → D) (m : ℕ) (γ : ℝ) : Prop :=
  ∃ (r : ℕ) (B C : ℝ) (H : Fin r → X → Fin m → ℂ),
    0 ≤ B ∧ 0 ≤ C ∧ (∀ y, ∑ i, ‖H i y‖ ≤ C) ∧
    ∀ k : K, ∃ coeff : W → Fin r → ℂ,
      (∀ w, ‖coeff w‖ ≤ B) ∧
      Integrable (fun x => dist
        (PhaseEncoding.kernelEncoding (condDistrib b p μ)
          (fun d => (eval (kCoeff k) d : ℂ)) m (p x))
        (∑ i, coeff (q x) i • H i x) ^ 2) μ ∧
      (∫ x, dist
        (PhaseEncoding.kernelEncoding (condDistrib b p μ)
          (fun d => (eval (kCoeff k) d : ℂ)) m (p x))
        (∑ i, coeff (q x) i • H i x) ^ 2 ∂μ) < γ^2

omit [StandardBorelSpace Y] [Nonempty Y] in
theorem ambient_uniform_precision_contradiction
    (μ : Measure X) [IsProbabilityMeasure μ]
    (p : X → Y) (q : X → W) (b : X → D)
    (hp : Measurable p) (hq : Measurable q) (hb : Measurable b)
    (m : ℕ) (hm : 0 < m) (g : Y → Fin m → D)
    (hg : ∀ᵐ y ∂μ.map p, condDistrib b p μ y =
      (m : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (g y i))
    (hwild : IsWild (DifferenceFourier.differenceLaw (μ.map (q))
      (condDistrib b (q) μ)))
    (ρ c : ℝ) (N : ℕ) (hρ : 0 < ρ) (hc : 0 < c) (hN : 0 < N)
    (harc : ∀ (ω : Measure Circle) [IsProbabilityMeasure ω],
      (∀ n, 0 < n → n ≤ N → ‖∫ w, (w : ℂ)^n ∂ω‖ < c) →
      ω.real {w | ‖(w : ℂ)-1‖ ≤ 4*ρ} < 1/(4*(m : ℝ)^2))
    (happrox : AmbientEncodingAt μ p q b m (((ρ^m/(m : ℝ))/100)/100)) : False := by
  classical
  let P : X → W := q
  have hP : Measurable P := hq
  let : IsProbabilityMeasure (μ.map P) := Measure.isProbabilityMeasure_map (hP).aemeasurable
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
  let Ap : Fin M → X → Fin m → ℂ := fun j x => ∑ i, coeff (u j) (P x) i • H i x
  let Am : Fin M → X → Fin m → ℂ := fun j x => ∑ i, coeff (v j) (P x) i • H i x
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
    have hh := hbins (arr w i) (arr w j) hij (fun k => H k x) (hH x)
    have h0 := (hh 0).le
    have h1 := (hh 1).le
    change dist (∑ k, coeff (u i) (P x) k • H k x)
      (∑ k, coeff (u j) (P x) k • H k x) ≤ τ ∧
      dist (∑ k, coeff (v i) (P x) k • H k x)
      (∑ k, coeff (v j) (P x) k • H k x) ≤ τ
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

end PlaneFiveColor.Spectral
namespace EuclideanFiveColor.CompactApproximation
open MeasureTheory
variable {K Y : Type*} [SMul K Y] [MeasurableSpace Y] [MeasurableConstSMul K Y]
lemma scalar_identity (ν : Measure Y) : Scalar (K := K) ν id := by
  intro H hH hB ε hε
  obtain ⟨B,hB⟩ := hB
  refine ⟨1, max 0 B, 1, fun _ _ => 1, le_max_left _ _, by norm_num,
    fun _ => measurable_const, fun _ => by simp, ?_⟩
  intro k
  refine ⟨fun y _ => H (k • y), Measurable.of_eval (fun _ => hH.comp (measurable_const_smul k)),
    fun y => ?_, ?_, ?_⟩
  · rw [pi_norm_le_iff_of_nonneg (le_max_left _ _)]
    exact fun _ => (hB _).trans (le_max_right _ _)
  · simp
  · simpa using sq_pos_of_pos hε
end EuclideanFiveColor.CompactApproximation

namespace PlaneFiveColor.Spectral
variable [Carrier]

section
open MeasureTheory ProbabilityTheory EuclideanFiveColor
open scoped BigOperators ENNReal
variable {X Y W : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace W]
  [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]
  [StandardBorelSpace W] [Nonempty W]
  [MulAction K X] [MulAction K Y] [MulAction K W]
  [MeasurableConstSMul K X] [MeasurableConstSMul K Y] [MeasurableConstSMul K W]

omit [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace W] [Nonempty W]
  [StandardBorelSpace Y] [Nonempty Y] [MulAction K W] [MeasurableConstSMul K W] in
lemma ambient_encoding_of_at (μ : Measure X) [IsProbabilityMeasure μ]
    [ErgodicSMul K X μ] (p : X → Y) (q : X → W) (b : X → D)
    (hp : Measurable p) (hb : Measurable b)
    (hpe : ∀ k : K, ∀ᵐ x ∂μ, p (k • x) = k • p x)
    (hbe : ∀ k : K, ∀ᵐ x ∂μ, b (k • x) = k • b x)
    (m : ℕ) (H : Y → Fin m → ℂ)
    (hHeq : H =ᵐ[μ.map p] PhaseEncoding.kernelEncoding (condDistrib b p μ)
      (fun d => (eval 1 d : ℂ)) m)
    (γ : ℝ) (ha : CompactApproximation.At (K := K) μ q m (H ∘ p) γ) :
    AmbientEncodingAt μ p q b m γ := by
  obtain ⟨r, B, C, Hf, hB, hC, _hHm, hHf, ha⟩ := ha
  refine ⟨r, B, C, Hf, hB, hC, hHf, ?_⟩
  intro k
  obtain ⟨a, _ham, hab, hai, hae⟩ := ha k
  have hker := KernelSupport.condDistrib_equivariant μ b p hb hp
    (MeasurableEquiv.smul k) (MeasurableEquiv.smul k) (fun d : D => k • d)
    (measurable_const_smul k) (measurePreserving_smul k μ) (hpe k) (hbe k)
  have hcov := PhaseEncoding.kernelEncoding_covariance (μ.map p) (condDistrib b p μ)
    (fun y : Y => k • y) (fun d : D => k • d) (measurable_const_smul k)
    (fun d => (eval 1 d : ℂ)) (measurable_eval_coe 1) m hker
  have heq : ∀ᵐ x ∂μ, (H ∘ p) (k • x) =
      PhaseEncoding.kernelEncoding (condDistrib b p μ)
        (fun d => (eval (kCoeff k) d : ℂ)) m (p x) := by
    have he := (measurePreserving_smul k μ).quasiMeasurePreserving.ae
      (ae_of_ae_map hp.aemeasurable hHeq)
    filter_upwards [he, hpe k, ae_of_ae_map hp.aemeasurable hcov] with x hx hp' hc'
    dsimp only [Function.comp_apply]
    rw [hx, hp']
    simpa only [Function.comp_def, eval_smul_one] using hc'
  have he : (fun x => dist ((H ∘ p) (k • x)) (∑ i, a (q x) i • Hf i x)^2) =ᵐ[μ]
      (fun x => dist (PhaseEncoding.kernelEncoding (condDistrib b p μ)
        (fun d => (eval (kCoeff k) d : ℂ)) m (p x)) (∑ i, a (q x) i • Hf i x)^2) :=
    heq.mono fun x hx => by dsimp only at hx ⊢; rw [hx]
  exact ⟨a, hab, hai.congr he, by rw [← integral_congr_ae he]; exact hae⟩

omit [StandardBorelSpace Y] [Nonempty Y] in

theorem relative_singularity_approximation
    (μ : Measure X) [IsProbabilityMeasure μ] [ErgodicSMul K X μ]
    (d : X → D) (p : X → Y) (hd : Measurable d) (hp : Measurable p)
    (hde : ∀ k : K, ∀ᵐ x ∂μ, d (k • x) = k • d x)
    (hpe : ∀ k : K, ∀ᵐ x ∂μ, p (k • x) = k • p x)
    (hwild : IsWild (μ.map d))
    (ha : ∀ (m : ℕ) (H : Y → Fin m → ℂ), Measurable H →
      (∃ A : ℝ, ∀ y, ‖H y‖ ≤ A) → ∀ ε : ℝ, 0 < ε →
      ∃ q : X → W, Measurable q ∧
        (∀ k : K, ∀ᵐ x ∂μ, q (k • x) = k • q x) ∧
        (∀ b : X → D, Measurable b →
          (∀ k : K, ∀ᵐ x ∂μ, b (k • x) = k • b x) → IsWild (μ.map b) →
          DifferenceFourier.differenceLaw (μ.map q) (condDistrib b q μ) C = 0) ∧
        ∃ H₀ : W → Fin m → ℂ, Measurable H₀ ∧ (∃ A : ℝ, ∀ w, ‖H₀ w‖ ≤ A) ∧
          Integrable (fun x => dist (H (p x)) (H₀ (q x))^2) μ ∧
          (∫ x, dist (H (p x)) (H₀ (q x))^2 ∂μ) < ε^2) :
    DifferenceFourier.differenceLaw (μ.map p) (condDistrib d p μ) C = 0 := by
  let : IsProbabilityMeasure (μ.map p) := Measure.isProbabilityMeasure_map (hp).aemeasurable
  by_contra hn
  have hpos : 0 < RelativeCenters.differenceLaw (μ.map p) (condDistrib d p μ) C :=
    pos_iff_ne_zero.mpr hn
  obtain ⟨b, hb, hbe, hbw, a, ha', hf⟩ := exact_finite_center_reduction μ d p hd hp hde hpe hwild hpos
  obtain ⟨m, hm, g, hg⟩ := UniformEnumeration.constant_uniform_lists (μ.map p)
    (condDistrib b p μ) a ha' (hf.mono fun y ⟨S, hS, hSa, hSupp, hcS, _⟩ =>
      ⟨S, hS, hSa, hSupp, hcS⟩)
  obtain ⟨ρ, c, N, hρ, hc, hN, harc⟩ := SmallArc.exists_small_arc_constants m hm
  let γ : ℝ := ((ρ^m/(m : ℝ))/100)/100
  have hγ : 0 < γ := by dsimp [γ]; positivity
  obtain ⟨H, hH, ⟨A, _hA, hHB⟩, hHeq⟩ := bounded_phase_encoding μ p b m hm g hg
  obtain ⟨q, hq, hqe, hprev, H₀, hH₀, hH₀B, hi, he⟩ := ha m H hH ⟨A,hHB⟩ (γ/2) (by positivity)
  let : IsProbabilityMeasure (μ.map q) := Measure.isProbabilityMeasure_map (hq).aemeasurable
  have happ := CompactApproximation.lift_at μ q id hq measurable_id
    (fun k => measurePreserving_smul k μ) hqe m (H ∘ p) H₀ (hH.comp hp) hH₀ hH₀B γ hγ hi he
    (CompactApproximation.vector_of_scalar (μ.map q) id measurable_id
      (CompactApproximation.scalar_identity (K := K) (μ.map q)))
  have henc := ambient_encoding_of_at μ p q b hp hb hpe hbe m H hHeq γ happ
  have hpwild : IsWild (DifferenceFourier.differenceLaw (μ.map q) (condDistrib b q μ)) :=
    ⟨relative_difference_invariant μ b q hb hq hbe hqe, hprev b hb hbe hbw⟩
  exact ambient_uniform_precision_contradiction μ p q b hp hq hb m hm g hg
    hpwild ρ c N hρ hc hN harc henc

end
open MeasureTheory ProbabilityTheory EuclideanFiveColor
variable {X Y W : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace W]
  [MulAction K X] [MulAction K Y] [MulAction K W]
  [MeasurableConstSMul K X] [MeasurableConstSMul K Y] [MeasurableConstSMul K W]

private def UniversalGood (μ : Measure X) [IsProbabilityMeasure μ] (p : X → Y) : Prop :=
  ∀ d : X → D, Measurable d → (∀ k : K, ∀ᵐ x ∂μ, d (k • x) = k • d x) →
    IsWild (μ.map d) → DifferenceFourier.differenceLaw (μ.map p) (condDistrib d p μ) C = 0

lemma universalGood_of_factor [StandardBorelSpace X] [Nonempty X]
    [StandardBorelSpace W] [Nonempty W]
    (μ : Measure X) [IsProbabilityMeasure μ] [ErgodicSMul K X μ]
    (p : X → Y) (q : X → W) (r : W → Y)
    (hp : Measurable p) (hq : Measurable q) (hr : Measurable r)
    (hpe : ∀ k : K, ∀ᵐ x ∂μ, p (k • x) = k • p x)
    (hqe : ∀ k : K, ∀ᵐ x ∂μ, q (k • x) = k • q x)
    (he : p =ᵐ[μ] r ∘ q) (hg : UniversalGood μ q) : UniversalGood μ p := by
  intro d hd hde hw
  apply relative_singularity_approximation (W := W) μ d p hd hp hde hpe hw
  intro m H hH hB ε hε
  refine ⟨q, hq, hqe, hg, H ∘ r, hH.comp hr, ?_, ?_, ?_⟩
  · obtain ⟨B,hB⟩ := hB
    exact ⟨B, fun w => hB _⟩
  · apply (integrable_zero X ℝ μ).congr
    filter_upwards [he] with x hx
    simp only [hx, Function.comp_def, dist_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), Pi.zero_apply]
  · have he0 : (fun x => dist (H (p x)) ((H ∘ r) (q x))^2) =ᵐ[μ] 0 := by
      filter_upwards [he] with x hx
      simp only [hx, Function.comp_def, dist_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), Pi.zero_apply]
    rw [integral_congr_ae he0]
    simp only [Pi.zero_apply, integral_zero]
    exact sq_pos_of_pos hε

end PlaneFiveColor.Spectral

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

private def fiberMean (κ : Kernel X Y) (F : X × Y → ℂ) (x : X) : ℂ :=
  ∫ y, F (x,y) ∂κ x

lemma measurable_fiberMean (κ : Kernel X Y) [IsSFiniteKernel κ]
    (F : X × Y → ℂ) (hF : Measurable F) : Measurable (fiberMean κ F) :=
  hF.stronglyMeasurable.integral_kernel_prod_right'.measurable

lemma fiberMean_bound (κ : Kernel X Y) [IsMarkovKernel κ]
    (F : X × Y → ℂ) (C : ℝ) (hC : ∀ z, ‖F z‖ ≤ C) (x : X) :
    ‖fiberMean κ F x‖ ≤ C := by
  simpa only [fiberMean, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (μ := κ x)
      (Filter.Eventually.of_forall fun y => hC (x,y))

lemma fiberMean_l2_bound (μ : Measure X) [IsProbabilityMeasure μ]
    (κ : Kernel X Y) [IsMarkovKernel κ] (F : X × Y → ℂ)
    (hF : Measurable F) (C : ℝ) (hFC : ∀ z, ‖F z‖ ≤ C) :
    (∫ x, ‖fiberMean κ F x‖^2 ∂μ) ≤ ∫ z, ‖F z‖^2 ∂(μ ⊗ₘ κ) := by
  have hsq (z : X × Y) : ‖F z‖^2 ≤ C^2 := pow_le_pow_left₀ (norm_nonneg _) (hFC z) 2
  have hi : Integrable (fun z => ‖F z‖^2) (μ ⊗ₘ κ) :=
    Integrable.of_bound (hF.norm.pow_const 2).aestronglyMeasurable (C^2)
      (Filter.Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs, abs_sq] using hsq z)
  rw [Measure.integral_compProd hi]
  apply integral_mono
  · exact Integrable.of_bound ((measurable_fiberMean κ F hF).norm.pow_const 2).aestronglyMeasurable
      (C^2) (Filter.Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs, abs_sq] using
          pow_le_pow_left₀ (norm_nonneg _) (fiberMean_bound κ F C hFC x) 2)
  · have hm := (hF.norm.pow_const 2).stronglyMeasurable.integral_kernel_prod_right' (κ := κ)
    exact Integrable.of_bound hm.aestronglyMeasurable (C^2) (Filter.Eventually.of_forall fun x => by
      have hb := norm_integral_le_of_norm_le_const (μ := κ x)
        (f := fun y => ‖F (x,y)‖^2) (C := C^2)
        (Filter.Eventually.of_forall fun y => by
          simpa only [Real.norm_eq_abs, abs_sq] using hsq (x,y))
      simpa only [probReal_univ, mul_one] using hb)

  · intro x
    apply norm_integral_sq
    · exact Integrable.of_bound (hF.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
        C (Filter.Eventually.of_forall fun y => hFC (x,y))
    · exact Integrable.of_bound ((hF.comp (measurable_const.prodMk measurable_id)).norm.pow_const 2).aestronglyMeasurable
        (C^2) (Filter.Eventually.of_forall fun y => by
          simpa only [Real.norm_eq_abs, abs_sq] using hsq (x,y))

lemma kernel_apply_error_bound (μ : Measure X) [IsProbabilityMeasure μ]
    (κ : Kernel X Y) [IsMarkovKernel κ] (L P : X × Y → ℂ)
    (hL : Measurable L) (hP : Measurable P) (C : ℝ)
    (hLC : ∀ z, ‖L z‖ ≤ C) (hPC : ∀ z, ‖P z‖ ≤ C)
    (f : Y → ℂ) (hf : Measurable f) (hfB : ∀ y, ‖f y‖ ≤ 1) :
    (∫ x, ‖fiberMean κ (fun z => L z * f z.2) x -
      fiberMean κ (fun z => P z * f z.2) x‖^2 ∂μ) ≤
        ∫ z, ‖L z - P z‖^2 ∂(μ ⊗ₘ κ) := by
  have hLP (z : X × Y) : ‖L z - P z‖ ≤ 2*C :=
    (norm_sub_le _ _).trans (by linarith [hLC z, hPC z])
  have hF : Measurable (fun z : X × Y => (L z - P z) * f z.2) :=
    (hL.sub hP).mul (hf.comp measurable_snd)
  have hFB (z : X × Y) : ‖(L z - P z) * f z.2‖ ≤ 2*C := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (hfB z.2) (norm_nonneg _)).trans (by simpa using hLP z)
  have he (x : X) : fiberMean κ (fun z => L z * f z.2) x -
      fiberMean κ (fun z => P z * f z.2) x =
        fiberMean κ (fun z => (L z - P z) * f z.2) x := by
    dsimp [fiberMean]
    simp_rw [sub_mul]
    rw [integral_sub]
    · exact Integrable.of_bound ((hL.comp (measurable_const.prodMk measurable_id)).mul hf).aestronglyMeasurable
        C (Filter.Eventually.of_forall fun y => by
          rw [norm_mul]; exact (mul_le_mul_of_nonneg_left (hfB y) (norm_nonneg _)).trans (by simpa using hLC (x,y)))
    · exact Integrable.of_bound ((hP.comp (measurable_const.prodMk measurable_id)).mul hf).aestronglyMeasurable
        C (Filter.Eventually.of_forall fun y => by
          rw [norm_mul]; exact (mul_le_mul_of_nonneg_left (hfB y) (norm_nonneg _)).trans (by simpa using hPC (x,y)))
  simp_rw [he]
  apply (fiberMean_l2_bound μ κ _ hF (2*C) hFB).trans
  apply integral_mono
  · exact Integrable.of_bound (hF.norm.pow_const 2).aestronglyMeasurable ((2*C)^2)
      (Filter.Eventually.of_forall fun z => by
        simpa only [Real.norm_eq_abs, abs_sq] using pow_le_pow_left₀ (norm_nonneg _) (hFB z) 2)
  · exact Integrable.of_bound ((hL.sub hP).norm.pow_const 2).aestronglyMeasurable ((2*C)^2)
      (Filter.Eventually.of_forall fun z => by
        simpa only [Real.norm_eq_abs, abs_sq] using pow_le_pow_left₀ (norm_nonneg _) (hLP z) 2)
  · intro z
    apply pow_le_pow_left₀ (norm_nonneg _)
    rw [norm_mul]
    simpa using mul_le_mul_of_nonneg_left (hfB z.2) (norm_nonneg (L z - P z))

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
  apply Measurable.of_eval
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
  have hH : Measurable H := Measurable.of_eval fun _ => hL
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

namespace EuclideanFiveColor.KernelCompact

section
open MeasureTheory ProbabilityTheory RectangleDensity
open scoped BigOperators
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated X]

theorem bounded_range_approximation (μ : Measure X) [IsProbabilityMeasure μ]
    (κ : Kernel Y X) [IsMarkovKernel κ] (q : X → Y) (hq : Measurable q)
    (L : X × X → ℂ) (hL : Measurable L) (C : ℝ) (hC : 0 ≤ C)
    (hLC : ∀ z, ‖L z‖ ≤ C) (ε : ℝ) (hε : 0 < ε) :
    ∃ (r : ℕ) (B C₀ : ℝ) (Hf : Fin r → X → ℂ),
      0 ≤ B ∧ 0 ≤ C₀ ∧ (∀ i, Measurable (Hf i)) ∧ (∀ x, ∑ i, ‖Hf i x‖ ≤ C₀) ∧
      ∀ f : X → ℂ, Measurable f → (∀ x, ‖f x‖ ≤ 1) →
        ∃ a : Y → Fin r → ℂ, Measurable a ∧ (∀ y, ‖a y‖ ≤ B) ∧
          Integrable (fun x => dist (∫ x', L (x,x') * f x' ∂κ (q x))
            (∑ i, a (q x) i * Hf i x)^2) μ ∧
          (∫ x, dist (∫ x', L (x,x') * f x' ∂κ (q x))
            (∑ i, a (q x) i * Hf i x)^2 ∂μ) < ε^2 := by
  classical
  let κ₀ := κ.comap q hq
  obtain ⟨n, c, hB, _, he⟩ := bounded_rectangles (μ ⊗ₘ κ₀) L hL C hC hLC ε hε
  let r := Fintype.card (Code n)
  let e : Fin r ≃ Code n := (Fintype.equivFin (Code n)).symm
  let Hf : Fin r → X → ℂ := fun i x => if code X n x = e i then 1 else 0
  have hHf (i : Fin r) : Measurable (Hf i) :=
    Measurable.ite ((measurable_code n) (measurableSet_singleton (e i))) measurable_const measurable_const
  have hHfB (i : Fin r) (x : X) : ‖Hf i x‖ ≤ 1 := by
    dsimp only [Hf]
    split_ifs <;> norm_num
  have hsumB (x : X) : ∑ i, ‖Hf i x‖ ≤ r := by
    calc
      ∑ i, ‖Hf i x‖ ≤ ∑ _ : Fin r, (1 : ℝ) := Finset.sum_le_sum fun i _ => hHfB i x
      _ = r := by simp
  refine ⟨r, 2*C, r, Hf, by positivity, by positivity, hHf, hsumB, ?_⟩
  intro f hf hfB
  let a : Y → Fin r → ℂ := fun y i => ∫ x', c (e i, code X n x') * f x' ∂κ y
  have hm (i : Fin r) : Measurable (fun x' => c (e i, code X n x') * f x') :=
    ((measurable_of_countable c).comp (measurable_const.prodMk (measurable_code n))).mul hf
  have hbound (i : Fin r) (x' : X) : ‖c (e i, code X n x') * f x'‖ ≤ 2*C := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (hfB x') (norm_nonneg _)).trans (by simpa using hB (e i, code X n x'))
  have ha : Measurable a := by
    apply Measurable.of_eval
    intro i
    exact (hm i).stronglyMeasurable.integral_kernel.measurable
  have haB (y : Y) : ‖a y‖ ≤ 2*C := by
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro i
    simpa only [a, probReal_univ, mul_one] using norm_integral_le_of_norm_le_const
      (μ := κ y) (Filter.Eventually.of_forall (hbound i))
  let P : X × X → ℂ := fun z => c (pairCode n z)
  have hP : Measurable P := (measurable_of_countable c).comp (measurable_pairCode n)
  have hPB (z : X × X) : ‖P z‖ ≤ 2*C := hB _
  have hs (x : X) : (∑ i, a (q x) i * Hf i x) = fiberMean κ₀ (fun z => P z * f z.2) x := by
    rw [Finset.sum_eq_single (e.symm (code X n x))]
    · simp [a, Hf, fiberMean, P, pairCode, κ₀]
    · intro b _ hb
      have hn : code X n x ≠ e b := by
        intro hz
        exact hb (e.injective (by simpa using hz.symm))
      simp [Hf, hn]
    · simp
  have hfm : Measurable (fiberMean κ₀ (fun z => L z * f z.2)) :=
    measurable_fiberMean κ₀ _ (hL.mul (hf.comp measurable_snd))
  have hgm : Measurable (fiberMean κ₀ (fun z => P z * f z.2)) :=
    measurable_fiberMean κ₀ _ (hP.mul (hf.comp measurable_snd))
  have hfb (x : X) : ‖fiberMean κ₀ (fun z => L z * f z.2) x‖ ≤ C := by
    apply fiberMean_bound
    intro z
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (hfB z.2) (norm_nonneg _)).trans (by simpa using hLC z)
  have hgb (x : X) : ‖fiberMean κ₀ (fun z => P z * f z.2) x‖ ≤ 2*C := by
    apply fiberMean_bound
    intro z
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (hfB z.2) (norm_nonneg _)).trans (by simpa using hPB z)
  have hdist : Integrable (fun x =>
      dist (fiberMean κ₀ (fun z => L z * f z.2) x) (fiberMean κ₀ (fun z => P z * f z.2) x)^2) μ :=
    Integrable.of_bound ((hfm.dist hgm).pow_const 2).aestronglyMeasurable ((3*C)^2)
      (Filter.Eventually.of_forall fun x => by
        have hd : dist (fiberMean κ₀ (fun z => L z * f z.2) x) (fiberMean κ₀ (fun z => P z * f z.2) x) ≤ 3*C :=
          (dist_le_norm_add_norm _ _).trans (by linarith [hfb x, hgb x])
        simpa only [Real.norm_eq_abs, abs_sq] using pow_le_pow_left₀ dist_nonneg hd 2)
  refine ⟨a, ha, haB, ?_, ?_⟩
  · simpa only [hs, fiberMean, κ₀, Kernel.comap_apply] using hdist
  · simp_rw [hs, dist_eq_norm]
    change (∫ x, ‖fiberMean κ₀ (fun z => L z * f z.2) x - fiberMean κ₀ (fun z => P z * f z.2) x‖^2 ∂μ) < ε^2
    exact (kernel_apply_error_bound μ κ₀ L P hL hP (2*C)
      (fun z => (hLC z).trans (by linarith)) hPB f hf hfB).trans_lt he

end
section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {K X Y : Type*} [Group K] [MulAction K X] [MulAction K Y]
  [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableConstSMul K X] [MeasurableConstSMul K Y]

private def applyKernel (κ : Kernel Y X) (q : X → Y) (L : X × X → ℂ) (f : X → ℂ) (x : X) : ℂ :=
  ∫ x', L (x,x') * f x' ∂κ (q x)

omit [MeasurableConstSMul K Y] in
lemma applyKernel_covariance (μ : Measure X) [IsProbabilityMeasure μ]
    (κ : Kernel Y X) [IsMarkovKernel κ] (q : X → Y) (hq : Measurable q)
    (L : X × X → ℂ) (hL : Measurable L)
    (hqcov : ∀ k : K, ∀ᵐ x ∂μ, q (k • x) = k • q x)
    (hκcov : ∀ k : K, ∀ᵐ y ∂μ.map q, κ (k • y) = (κ y).map (fun x => k • x))
    (hLcov : ∀ k : K, ∀ᵐ z ∂μ ⊗ₘ κ.comap q hq, L (k • z.1, k • z.2) = L z)
    (f : X → ℂ) (hfm : Measurable f) (k : K) :
    (fun x => applyKernel κ q L f (k • x)) =ᵐ[μ]
      applyKernel κ q L (fun x => f (k • x)) := by
  have hc : ∀ᵐ x ∂μ, κ (k • q x) = (κ (q x)).map (fun x => k • x) :=
    ae_of_ae_map (μ := μ) (p := fun y => κ (k • y) = (κ y).map (fun x => k • x))
      hq.aemeasurable (hκcov k)
  have hl₀ := Measure.ae_ae_of_ae_compProd (μ := μ) (κ := κ.comap q hq)
    (p := fun z => L (k • z.1, k • z.2) = L z) (hLcov k)
  have hl : ∀ᵐ x ∂μ, ∀ᵐ x' ∂κ (q x), L (k • x, k • x') = L (x,x') := by
    simpa only [Kernel.comap_apply] using hl₀
  filter_upwards [hqcov k, hc, hl] with x hqx hcx hlx
  dsimp [applyKernel]
  have hLf : Measurable (fun y => L (k • x,y) * f y) :=
    (hL.comp (measurable_const.prodMk measurable_id)).mul hfm
  rw [hqx, hcx, integral_map (measurable_const_smul k).aemeasurable hLf.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [hlx] with x' hxx
  simp only [hxx]

end
section
open MeasureTheory ProbabilityTheory RectangleDensity
open scoped BigOperators
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated X]

lemma norm_sq_le_sub (z w : ℂ) : ‖z‖^2 ≤ ‖z-w‖^2 + 2*(z*star w).re := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  nlinarith [sq_nonneg w.re, sq_nonneg w.im]

theorem exists_nonzero_image (μ : Measure X) [IsProbabilityMeasure μ]
    (κ : Kernel Y X) [IsMarkovKernel κ] (q : X → Y) (hq : Measurable q)
    (L : X × X → ℂ) (hL : Measurable L) (C : ℝ) (hC : 0 ≤ C)
    (hLC : ∀ z, ‖L z‖ ≤ C) (hne : ¬ L =ᵐ[μ ⊗ₘ κ.comap q hq] 0) :
    ∃ f : X → ℂ, Measurable f ∧ (∀ x, ‖f x‖ ≤ 1) ∧
      ¬ applyKernel κ q L f =ᵐ[μ] 0 := by
  classical
  by_contra h
  push Not at h
  let κ₀ := κ.comap q hq
  let ν := μ ⊗ₘ κ₀
  have hL₂ : Integrable (fun z => ‖L z‖^2) ν :=
    Integrable.of_bound (hL.norm.pow_const 2).aestronglyMeasurable (C^2)
      (Filter.Eventually.of_forall fun z => by
        simpa only [Real.norm_eq_abs, abs_sq] using pow_le_pow_left₀ (norm_nonneg _) (hLC z) 2)
  have hsmall : ∀ ε : ℝ, 0 < ε → (∫ z, ‖L z‖^2 ∂ν) < ε := by
    intro ε hε
    obtain ⟨n, c, hc, hi, he⟩ := bounded_rectangles ν L hL C hC hLC
      (Real.sqrt ε) (Real.sqrt_pos.mpr hε)
    rw [Real.sq_sqrt hε.le] at he
    let P : X × X → ℂ := fun z => c (pairCode n z)
    have hP : Measurable P := (measurable_of_countable c).comp (measurable_pairCode n)
    let d : ℝ := 2*C+1
    have hd : 0 < d := by dsimp [d]; positivity
    let f : Code n → X → ℂ := fun i x => star (c (i,code X n x)) / (d : ℂ)
    have hfm (i : Code n) : Measurable (f i) :=
      (Complex.continuous_conj.measurable.comp ((measurable_of_countable c).comp (measurable_const.prodMk (measurable_code n)))).div_const _
    have hfb (i : Code n) (x : X) : ‖f i x‖ ≤ 1 := by
      dsimp only [f]
      rw [norm_div, norm_star, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
      apply (div_le_one hd).mpr
      exact (hc _).trans (by dsimp [d]; linarith)
    have hzero : ∀ᵐ x ∂μ, ∀ i : Code n, applyKernel κ q L (f i) x = 0 :=
      ae_all_iff.mpr fun i => h (f i) (hfm i) (hfb i)
    have hLP : Integrable (fun z => L z * star (P z)) ν :=
      Integrable.of_bound (hL.mul (Complex.continuous_conj.measurable.comp hP)).aestronglyMeasurable (C*(2*C))
        (Filter.Eventually.of_forall fun z => by
          rw [norm_mul, norm_star]
          exact mul_le_mul (hLC z) (hc _) (norm_nonneg _) hC)
    have hz : (∫ z, L z * star (P z) ∂ν) = 0 := by
      rw [Measure.integral_compProd hLP]
      apply integral_eq_zero_of_ae
      filter_upwards [hzero] with x hx
      have heq : (fun x' => L (x,x') * star (P (x,x'))) =
          fun x' => (L (x,x') * f (code X n x) x') * (d : ℂ) := by
        funext x'
        dsimp [P,pairCode,f]
        have hdc : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
        field_simp [hdc]
      rw [heq, integral_mul_const]
      change applyKernel κ q L (f (code X n x)) x * (d : ℂ) = 0
      rw [hx, zero_mul]
    have hr : (∫ z, RCLike.re (L z * star (P z)) ∂ν) = 0 := by
      rw [integral_re hLP, hz]; rfl
    have hb := integral_mono hL₂ (hi.add (hLP.re.const_mul 2))
      (fun z => norm_sq_le_sub (L z) (P z))
    dsimp only [Pi.add_apply] at hb
    rw [integral_add hi (hLP.re.const_mul 2), integral_const_mul, hr, mul_zero, add_zero] at hb
    exact hb.trans_lt he
  have hz : (∫ z, ‖L z‖^2 ∂ν) = 0 := by
    apply le_antisymm
    · exact le_of_forall_pos_le_add fun ε hε => le_of_lt (by simpa using hsmall ε hε)
    · exact integral_nonneg fun z => sq_nonneg _
  have hae := (integral_eq_zero_iff_of_nonneg (fun z => sq_nonneg ‖L z‖) hL₂).mp hz
  apply hne
  filter_upwards [hae] with z hz
  apply norm_eq_zero.mp
  exact sq_eq_zero_iff.mp hz

end

section
open MeasureTheory ProbabilityTheory Filter
variable {K X Y : Type*} [Group K] [MulAction K X] [MulAction K Y]
  [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableConstSMul K X] [MeasurableConstSMul K Y]

omit [MeasurableConstSMul K X] [MeasurableConstSMul K Y] in
lemma measurable_applyKernel (κ : Kernel Y X) [IsMarkovKernel κ]
    (q : X → Y) (hq : Measurable q) (L : X × X → ℂ) (hL : Measurable L)
    (f : X → ℂ) (hf : Measurable f) : Measurable (applyKernel κ q L f) :=
  measurable_fiberMean (κ.comap q hq) _ (hL.mul (hf.comp measurable_snd))

omit [MeasurableConstSMul K X] [MeasurableConstSMul K Y] in
lemma applyKernel_bound (κ : Kernel Y X) [IsMarkovKernel κ]
    (q : X → Y) (L : X × X → ℂ) (C : ℝ) (hLC : ∀ z, ‖L z‖ ≤ C)
    (f : X → ℂ) (hfB : ∀ x, ‖f x‖ ≤ 1) (x : X) : ‖applyKernel κ q L f x‖ ≤ C := by
  have hb (x' : X) : ‖L (x,x') * f x'‖ ≤ C := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (hfB _) (norm_nonneg _)).trans (by simpa using hLC (x,x'))
  change ‖∫ x', L (x,x') * f x' ∂κ (q x)‖ ≤ C
  simpa only [probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (μ := κ (q x)) (C := C) (Eventually.of_forall hb)

omit [MeasurableConstSMul K X] [MeasurableConstSMul K Y] in
lemma exists_invariant_set (ν : Measure (X × X))
    [SMulInvariantMeasure K (X × X) ν] (hn : ¬ ErgodicSMul K (X × X) ν) :
    ∃ s : Set (X × X), MeasurableSet s ∧
      (∀ k : K, (fun z : X × X => k • z) ⁻¹' s =ᵐ[ν] s) ∧
      ¬ EventuallyConst s (ae ν) := by
  classical
  by_contra! h
  apply hn
  exact ⟨fun hs hi => h _ hs hi⟩

omit [MeasurableConstSMul K X] [MeasurableConstSMul K Y] in
lemma indicator_not_constant (ν : Measure (X × X)) (s : Set (X × X))
    (hn : ¬ EventuallyConst s (ae ν)) (c : ℂ) :
    ¬ s.indicator (fun _ => (1 : ℂ)) =ᵐ[ν] (fun _ => c) := by
  classical
  intro he
  apply hn
  change Filter.EventuallyConst s (ae ν)
  rw [Filter.eventuallyConst_set]
  by_cases hc : c = 0
  · right
    filter_upwards [he] with x hx
    simpa [hc] using hx
  · left
    filter_upwards [he] with x hx
    by_contra hxs
    simp only [Set.indicator_of_notMem hxs] at hx
    exact hc hx.symm

end
open MeasureTheory ProbabilityTheory Filter
variable {K X Y : Type*} [Group K] [MulAction K X] [MulAction K Y]
  [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableConstSMul K X] [MeasurableConstSMul K Y]

omit [MeasurableConstSMul K Y] in
lemma row_constant (μ : Measure X) [IsProbabilityMeasure μ] [ErgodicSMul K X μ]
    (κ : Kernel Y X) [IsMarkovKernel κ] (q : X → Y) (hq : Measurable q)
    (L : X × X → ℂ) (hL : Measurable L) (C : ℝ) (hLC : ∀ z, ‖L z‖ ≤ C)
    (hqcov : ∀ k : K, ∀ᵐ x ∂μ, q (k • x) = k • q x)
    (hκcov : ∀ k : K, ∀ᵐ y ∂μ.map q, κ (k • y) = (κ y).map (fun x => k • x))
    (hLcov : ∀ k : K, ∀ᵐ z ∂μ ⊗ₘ κ.comap q hq, L (k • z.1, k • z.2) = L z) :
    (fun x => ∫ x', L (x,x') ∂κ (q x)) =ᵐ[μ]
      (fun _ => ∫ z, L z ∂μ ⊗ₘ κ.comap q hq) := by
  have hfm := measurable_applyKernel κ q hq L hL (fun _ => 1) measurable_const
  have hi : ∀ k : K, ∀ᵐ x ∂μ,
      applyKernel κ q L (fun _ => 1) (k • x) = applyKernel κ q L (fun _ => 1) x :=
    fun k => applyKernel_covariance μ κ q hq L hL hqcov hκcov hLcov _ measurable_const k
  obtain ⟨c, hc⟩ := ErgodicSupport.ae_eq_const_of_invariant hfm hi
  have hc' : (fun x => ∫ x', L (x,x') ∂κ (q x)) =ᵐ[μ] (fun _ => c) := by
    filter_upwards [hc] with x hx
    simpa only [applyKernel, mul_one] using hx
  have hLi : Integrable L (μ ⊗ₘ κ.comap q hq) :=
    Integrable.of_bound hL.aestronglyMeasurable C (Eventually.of_forall hLC)
  have he : (∫ z, L z ∂μ ⊗ₘ κ.comap q hq) = c := by
    rw [Measure.integral_compProd hLi]
    change (∫ x, (∫ x', L (x,x') ∂κ (q x)) ∂μ) = c
    rw [integral_congr_ae hc']
    simp
  simpa only [he] using hc'

omit [MeasurableConstSMul K Y] in
lemma centered_kernel (μ : Measure X) [IsProbabilityMeasure μ] [ErgodicSMul K X μ]
    (κ : Kernel Y X) [IsMarkovKernel κ] (q : X → Y) (hq : Measurable q)
    (hswap : (μ ⊗ₘ κ.comap q hq).map Prod.swap = μ ⊗ₘ κ.comap q hq)
    (hqcov : ∀ k : K, ∀ᵐ x ∂μ, q (k • x) = k • q x)
    (hκcov : ∀ k : K, ∀ᵐ y ∂μ.map q, κ (k • y) = (κ y).map (fun x => k • x))
    [SMulInvariantMeasure K (X × X) (μ ⊗ₘ κ.comap q hq)]
    (hn : ¬ ErgodicSMul K (X × X) (μ ⊗ₘ κ.comap q hq)) :
    ∃ L : X × X → ℂ, Measurable L ∧ (∀ z, ‖L z‖ ≤ 2) ∧
      (∀ k : K, ∀ᵐ z ∂μ ⊗ₘ κ.comap q hq, L (k • z.1, k • z.2) = L z) ∧
      ¬ L =ᵐ[μ ⊗ₘ κ.comap q hq] 0 ∧
      (∀ᵐ x ∂μ, (∫ x', L (x,x') ∂κ (q x)) = 0) ∧
      (∀ᵐ x ∂μ, (∫ x', L (x',x) ∂κ (q x)) = 0) := by
  classical
  let ν := μ ⊗ₘ κ.comap q hq
  obtain ⟨s, hs, hscov, hsn⟩ := exists_invariant_set ν hn
  let F : X × X → ℂ := s.indicator (fun _ => 1)
  have hF : Measurable F := measurable_const.indicator hs
  have hFB (z : X × X) : ‖F z‖ ≤ 1 := by
    dsimp [F]; by_cases hz : z ∈ s <;> simp [hz]
  have hFi : Integrable F ν := Integrable.of_bound hF.aestronglyMeasurable 1 (Eventually.of_forall hFB)
  have hFc : ∀ k : K, ∀ᵐ z ∂ν, F (k • z.1,k • z.2) = F z := by
    intro k; filter_upwards [hscov k] with z hz
    change ((k • z.1,k • z.2) ∈ s) = (z ∈ s) at hz
    dsimp only [F]
    simp only [Set.indicator_apply, hz]
  let c : ℂ := ∫ z, F z ∂ν
  have hc : ‖c‖ ≤ 1 := by
    simpa [c] using norm_integral_le_of_norm_le_const (μ := ν) (f := F)
      (C := 1) (Eventually.of_forall hFB)
  let L : X × X → ℂ := fun z => F z - c
  have hLm : Measurable L := hF.sub measurable_const
  have hLB (z : X × X) : ‖L z‖ ≤ 2 := (norm_sub_le _ _).trans (by linarith [hFB z])
  have hLc : ∀ k : K, ∀ᵐ z ∂ν, L (k • z.1,k • z.2) = L z := by
    intro k; filter_upwards [hFc k] with z hz using congrArg (fun w => w-c) hz
  have hLn : ¬ L =ᵐ[ν] 0 := by
    intro h
    apply indicator_not_constant ν s hsn c
    filter_upwards [h] with z hz
    exact sub_eq_zero.mp hz
  have hL0 : (∫ z, L z ∂ν) = 0 := by
    rw [integral_sub hFi (integrable_const _)]
    simp only [integral_const, probReal_univ, one_smul, c, sub_self]
  have hr := row_constant μ κ q hq L hLm 2 hLB hqcov hκcov hLc
  have hswapP : MeasurePreserving Prod.swap ν ν := ⟨measurable_swap, hswap⟩
  have hLsc : ∀ k : K, ∀ᵐ z ∂ν, (L ∘ Prod.swap) (k • z.1,k • z.2) = (L ∘ Prod.swap) z := by
    intro k
    exact hswapP.quasiMeasurePreserving.ae (hLc k)
  have hc' := row_constant μ κ q hq (L ∘ Prod.swap) (hLm.comp measurable_swap) 2
    (fun z => hLB _) hqcov hκcov hLsc
  have hLs0 : (∫ z, (L ∘ Prod.swap) z ∂ν) = 0 := by
    change (∫ z, L (Prod.swap z) ∂ν) = 0
    rw [← integral_map measurable_swap.aemeasurable hLm.aestronglyMeasurable]
    exact (congrArg (fun ρ => ∫ z, L z ∂ρ) hswap).trans hL0
  refine ⟨L, hLm, hLB, hLc, hLn, ?_, ?_⟩
  · filter_upwards [hr] with x hx using hx.trans hL0
  · filter_upwards [hc'] with x hx using hx.trans hLs0

end EuclideanFiveColor.KernelCompact
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
namespace EuclideanFiveColor.KernelCompact
open MeasureTheory ProbabilityTheory Filter ConditionalFiber
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]

lemma image_conditional_mean_zero (μ : Measure X) [IsProbabilityMeasure μ]
    (q : X → Y) (hq : Measurable q)
    (L : X × X → ℂ) (hL : Measurable L) (C : ℝ) (hLC : ∀ z, ‖L z‖ ≤ C)
    (f : X → ℂ) (hfm : Measurable f) (hfB : ∀ x, ‖f x‖ ≤ 1)
    (hcol : ∀ᵐ x ∂μ, (∫ x', L (x',x) ∂condDistrib id q μ (q x)) = 0) :
    ∀ᵐ y ∂μ.map q, (∫ x, applyKernel (condDistrib id q μ) q L f x
      ∂condDistrib id q μ y) = 0 := by
  let κ := condDistrib id q μ
  filter_upwards [ae_in_own_fiber μ q hq, ae_fiber_of_ae μ q hq hcol] with y hy hcy
  have hLF : Measurable (fun z : X × X => L z * f z.2) := hL.mul (hfm.comp measurable_snd)
  have hLFB (z : X × X) : ‖L z * f z.2‖ ≤ C := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (hfB _) (norm_nonneg _)).trans (by simpa using hLC z)
  have hLFi : Integrable (fun z : X × X => L z * f z.2) ((κ y).prod (κ y)) :=
    Integrable.of_bound hLF.aestronglyMeasurable C (Eventually.of_forall hLFB)
  calc
    (∫ x, applyKernel κ q L f x ∂κ y) =
        ∫ x, (∫ x', L (x,x') * f x' ∂κ y) ∂κ y := by
      apply integral_congr_ae
      filter_upwards [hy] with x hx
      dsimp only [applyKernel]; rw [hx]
    _ = ∫ x', (∫ x, L (x,x') * f x' ∂κ y) ∂κ y := integral_integral_swap hLFi
    _ = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hy, hcy] with x' hx' hc'
      rw [integral_mul_const]
      change (∫ x, L (x,x') ∂κ (q x')) = 0 at hc'
      rw [hx'] at hc'
      change _ = 0
      rw [hc', zero_mul]

lemma nonzero_not_factorizable (μ : Measure X) [IsProbabilityMeasure μ]
    (q : X → Y) (hq : Measurable q) (H : X → ℂ)
    (hn : ¬ H =ᵐ[μ] 0)
    (hc : ∀ᵐ y ∂μ.map q, (∫ x, H x ∂condDistrib id q μ y) = 0) :
    ¬ ∃ b : Y → ℂ, Measurable b ∧ H =ᵐ[μ] b ∘ q := by
  rintro ⟨b, _hb, he⟩
  have hb0 : ∀ᵐ y ∂μ.map q, b y = 0 := by
    filter_upwards [hc, ae_in_own_fiber μ q hq, ae_fiber_of_ae μ q hq he] with y hy hqy hey
    have hh : H =ᵐ[condDistrib id q μ y] (fun _ => b y) := by
      filter_upwards [hqy, hey] with x hx hx'
      simpa only [Function.comp_apply, hx] using hx'
    rw [integral_congr_ae hh] at hy
    simpa using hy
  apply hn
  have he0 : ∀ᵐ x ∂μ, b (q x) = 0 := ae_of_ae_map (p := fun y => b y = 0) hq.aemeasurable hb0
  filter_upwards [he, he0] with x hx hx' using hx.trans hx'

end EuclideanFiveColor.KernelCompact

end

end ParishFactor
end

-- OAI.MeasureTheory.CompactFactors.Functions
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
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace EuclideanFiveColor.CompactFunctions
open MeasureTheory
open scoped BigOperators
variable {K X Y : Type*} [SMul K X] [MeasurableSpace X] [MeasurableSpace Y]

private def At (μ : Measure X) (q : X → Y) (H : X → ℂ) (ε : ℝ) : Prop :=
  ∃ (r : ℕ) (B C : ℝ) (Hf : Fin r → X → ℂ),
    0 ≤ B ∧ 0 ≤ C ∧ (∀ i, Measurable (Hf i)) ∧ (∀ x, ∑ i, ‖Hf i x‖ ≤ C) ∧
    ∀ k : K, ∃ a : Y → Fin r → ℂ, Measurable a ∧ (∀ y, ‖a y‖ ≤ B) ∧
      Integrable (fun x => dist (H (k • x)) (∑ i, a (q x) i * Hf i x)^2) μ ∧
      (∫ x, dist (H (k • x)) (∑ i, a (q x) i * Hf i x)^2 ∂μ) < ε^2

private def Compact (μ : Measure X) (q : X → Y) (H : X → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → At (K := K) μ q H ε

lemma at_of_finite {μ : Measure X} {q : X → Y} {H : X → ℂ} {ε : ℝ}
    {I : Type*} [Fintype I] (B C : ℝ) (Hf : I → X → ℂ)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hm : ∀ i, Measurable (Hf i))
    (hb : ∀ x, ∑ i, ‖Hf i x‖ ≤ C)
    (ha : ∀ k : K, ∃ a : Y → I → ℂ, Measurable a ∧ (∀ y, ‖a y‖ ≤ B) ∧
      Integrable (fun x => dist (H (k • x)) (∑ i, a (q x) i * Hf i x)^2) μ ∧
      (∫ x, dist (H (k • x)) (∑ i, a (q x) i * Hf i x)^2 ∂μ) < ε^2) :
    At (K := K) μ q H ε := by
  classical
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  refine ⟨_, B, C, fun i => Hf (e i), hB, hC, fun i => hm (e i), ?_, ?_⟩
  · intro x
    rw [e.sum_comp (fun i => ‖Hf i x‖)]
    exact hb x
  · intro k
    obtain ⟨a, ham, hab, hai, hae⟩ := ha k
    have hs (x : X) : (∑ i, a (q x) (e i) * Hf (e i) x) = ∑ i, a (q x) i * Hf i x := e.sum_comp (fun i => a (q x) i * Hf i x)
    refine ⟨fun y i => a y (e i), Measurable.of_eval (fun i => (measurable_pi_iff.mp ham) (e i)), ?_, ?_, ?_⟩
    · intro y
      rw [pi_norm_le_iff_of_nonneg hB]
      exact fun i => (norm_le_pi_norm (a y) (e i)).trans (hab y)
    · simpa only [hs] using hai
    · simpa only [hs] using hae

lemma module_bound {I : Type*} [Fintype I] (a : I → ℂ) (H : I → ℂ)
    {B C : ℝ} (hB : 0 ≤ B) (ha : ‖a‖ ≤ B) (hH : ∑ i, ‖H i‖ ≤ C) :
    ‖∑ i, a i * H i‖ ≤ B*C := by
  calc
    ‖∑ i, a i * H i‖ ≤ ∑ i, ‖a i * H i‖ := norm_sum_le _ _
    _ ≤ ∑ i, B*‖H i‖ := Finset.sum_le_sum fun i _ => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right ((norm_le_pi_norm a i).trans ha) (norm_nonneg _)
    _ = B * ∑ i, ‖H i‖ := by rw [Finset.mul_sum]
    _ ≤ B*C := mul_le_mul_of_nonneg_left hH hB

lemma dist_sq_add (a b c d : ℂ) :
    dist (a+b) (c+d)^2 ≤ 2*(dist a c^2 + dist b d^2) := by
  have h := dist_add_add_le a b c d
  nlinarith [dist_nonneg (x := a+b) (y := c+d), dist_nonneg (x := a) (y := c),
    dist_nonneg (x := b) (y := d), sq_nonneg (dist a c - dist b d)]

lemma dist_sq_chain (a b c : ℂ) :
    dist a c^2 ≤ 2*(dist a b^2 + dist b c^2) := by
  have h := dist_triangle a b c
  nlinarith [dist_nonneg (x := a) (y := c), dist_nonneg (x := a) (y := b),
    dist_nonneg (x := b) (y := c), sq_nonneg (dist a b - dist b c)]

lemma compact_const (μ : Measure X) (q : X → Y) (c : ℂ) :
    Compact (K := K) μ q (fun _ => c) := by
  intro ε hε
  apply at_of_finite (I := Unit) 1 ‖c‖ (fun _ _ => c) (by norm_num) (norm_nonneg _) (fun _ => measurable_const)
  · intro x; simp
  · intro k
    refine ⟨fun _ _ => 1, measurable_const, fun _ => by simp, ?_, ?_⟩
    · simp
    · simpa using sq_pos_of_pos hε

lemma compact_conj {μ : Measure X} {q : X → Y} {H : X → ℂ}
    (hH : Compact (K := K) μ q H) : Compact (K := K) μ q (fun x => star (H x)) := by
  intro ε hε
  obtain ⟨r, B, C, F, hB, hC, hm, hb, ha⟩ := hH ε hε
  refine ⟨r, B, C, fun i x => star (F i x), hB, hC,
    fun i => Complex.continuous_conj.measurable.comp (hm i), ?_, ?_⟩
  · intro x; simpa using hb x
  · intro k
    obtain ⟨a, ham, hab, hai, hae⟩ := ha k
    refine ⟨fun y i => star (a y i), (Measurable.of_eval (fun i => Complex.continuous_conj.measurable.comp ((measurable_pi_iff.mp ham) i))), ?_, ?_, ?_⟩
    · intro y
      rw [pi_norm_le_iff_of_nonneg hB]
      intro i
      simpa using (norm_le_pi_norm (a y) i).trans (hab y)
    · have hs (x : X) : (∑ i, star (a (q x) i) * star (F i x)) = star (∑ i, a (q x) i * F i x) := by
        simp only [star_sum, star_mul, mul_comm]
      simpa only [hs, dist_star_star] using hai
    · have hs (x : X) : (∑ i, star (a (q x) i) * star (F i x)) = star (∑ i, a (q x) i * F i x) := by
        simp only [star_sum, star_mul, mul_comm]
      simpa only [hs, dist_star_star] using hae

lemma compact_add {μ : Measure X} {q : X → Y} {H G : X → ℂ}
    [MeasurableConstSMul K X] (hq : Measurable q) (hHm : Measurable H) (hGm : Measurable G)
    (hH : Compact (K := K) μ q H) (hG : Compact (K := K) μ q G) :
    Compact (K := K) μ q (fun x => H x + G x) := by
  intro ε hε
  obtain ⟨r, B, C, F, hB, hC, hm, hb, ha⟩ := hH (ε/2) (by positivity)
  obtain ⟨s, D, E, J, hD, hE, hjm, hjb, hd⟩ := hG (ε/2) (by positivity)
  classical
  apply at_of_finite (I := Fin r ⊕ Fin s) (max B D) (C+E) (Sum.elim F J)
    (hB.trans (le_max_left _ _)) (add_nonneg hC hE)
  · intro i; cases i with
    | inl i => exact hm i
    | inr i => exact hjm i
  · intro x
    simpa only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr] using add_le_add (hb x) (hjb x)
  · intro k
    obtain ⟨a, ham, hab, hai, hae⟩ := ha k
    obtain ⟨b, hbm, hbb, hbi, hbe⟩ := hd k
    let A : Y → Fin r ⊕ Fin s → ℂ := fun y => Sum.elim (a y) (b y)
    have hAm : Measurable A := by
      apply Measurable.of_eval
      intro i
      cases i with
      | inl i => exact (measurable_pi_iff.mp ham) i
      | inr i => exact (measurable_pi_iff.mp hbm) i
    have hAb (y : Y) : ‖A y‖ ≤ max B D := by
      rw [pi_norm_le_iff_of_nonneg (hB.trans (le_max_left _ _))]
      intro i
      cases i with
      | inl i => exact ((norm_le_pi_norm (a y) i).trans (hab y)).trans (le_max_left _ _)
      | inr i => exact ((norm_le_pi_norm (b y) i).trans (hbb y)).trans (le_max_right _ _)
    let F₀ : X → ℂ := fun x => ∑ i, a (q x) i * F i x
    let G₀ : X → ℂ := fun x => ∑ i, b (q x) i * J i x
    have hFm : Measurable F₀ := Finset.measurable_sum _ (fun i _ =>
      (((measurable_pi_iff.mp ham) i).comp hq).mul (hm i))
    have hGm₀ : Measurable G₀ := Finset.measurable_sum _ (fun i _ =>
      (((measurable_pi_iff.mp hbm) i).comp hq).mul (hjm i))
    have hiM : Integrable (fun x => 2*(dist (H (k • x)) (F₀ x)^2 +
        dist (G (k • x)) (G₀ x)^2)) μ := (hai.add hbi).const_mul 2
    have hmajor (x : X) := dist_sq_add (H (k • x)) (G (k • x)) (F₀ x) (G₀ x)
    have hi : Integrable (fun x => dist (H (k • x)+G (k • x)) (F₀ x+G₀ x)^2) μ :=
      hiM.mono' ((((hHm.comp (measurable_const_smul k)).add (hGm.comp (measurable_const_smul k))).dist
        (hFm.add hGm₀)).pow_const 2).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs, abs_sq] using hmajor x)
    have he : (∫ x, dist (H (k • x)+G (k • x)) (F₀ x+G₀ x)^2 ∂μ) < ε^2 := by
      calc
        _ ≤ ∫ x, 2*(dist (H (k • x)) (F₀ x)^2 + dist (G (k • x)) (G₀ x)^2) ∂μ :=
          integral_mono hi hiM hmajor
        _ = 2*((∫ x, dist (H (k • x)) (F₀ x)^2 ∂μ) + ∫ x, dist (G (k • x)) (G₀ x)^2 ∂μ) := by
          rw [integral_const_mul, integral_add hai hbi]
        _ < ε^2 := by dsimp [F₀, G₀]; nlinarith
    refine ⟨A, hAm, hAb, ?_, ?_⟩
    · simpa only [Fintype.sum_sum_type, A, Sum.elim_inl, Sum.elim_inr] using hi
    · simpa only [Fintype.sum_sum_type, A, Sum.elim_inl, Sum.elim_inr] using he

lemma compact_mul {μ : Measure X} {q : X → Y} {H G : X → ℂ}
    [MeasurableConstSMul K X] (hq : Measurable q) (hHm : Measurable H) (hGm : Measurable G)
    (RG : ℝ) (hRG : 0 ≤ RG) (hGb : ∀ x, ‖G x‖ ≤ RG)
    (hH : Compact (K := K) μ q H) (hG : Compact (K := K) μ q G) :
    Compact (K := K) μ q (fun x => H x * G x) := by
  intro ε hε
  let δ := ε/(2*(RG+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨r, B, C, F, hB, hC, hm, hb, ha⟩ := hH δ hδ
  let γ := ε/(2*(B*C+1))
  have hγ : 0 < γ := by dsimp [γ]; positivity
  obtain ⟨s, D, E, J, hD, hE, hjm, hjb, hd⟩ := hG γ hγ
  classical
  apply at_of_finite (I := Fin r × Fin s) (B*D) (C*E) (fun i x => F i.1 x * J i.2 x)
    (mul_nonneg hB hD) (mul_nonneg hC hE) (fun i => (hm i.1).mul (hjm i.2))
  · intro x
    calc
      (∑ i : Fin r × Fin s, ‖F i.1 x * J i.2 x‖) = (∑ i, ‖F i x‖) * ∑ j, ‖J j x‖ := by
        simp only [Fintype.sum_prod_type, norm_mul, Finset.sum_mul_sum]
      _ ≤ C*E := mul_le_mul (hb x) (hjb x) (Finset.sum_nonneg fun _ _ => norm_nonneg _) hC
  · intro k
    obtain ⟨a, ham, hab, hai, hae⟩ := ha k
    obtain ⟨b, hbm, hbb, hbi, hbe⟩ := hd k
    let A : Y → Fin r × Fin s → ℂ := fun y i => a y i.1 * b y i.2
    have hAm : Measurable A := Measurable.of_eval (fun i =>
      ((measurable_pi_iff.mp ham) i.1).mul ((measurable_pi_iff.mp hbm) i.2))
    have hAb (y : Y) : ‖A y‖ ≤ B*D := by
      rw [pi_norm_le_iff_of_nonneg (mul_nonneg hB hD)]
      intro i
      change ‖a y i.1 * b y i.2‖ ≤ _
      rw [norm_mul]
      exact mul_le_mul ((norm_le_pi_norm (a y) i.1).trans (hab y))
        ((norm_le_pi_norm (b y) i.2).trans (hbb y)) (norm_nonneg _) hB
    let F₀ : X → ℂ := fun x => ∑ i, a (q x) i * F i x
    let G₀ : X → ℂ := fun x => ∑ i, b (q x) i * J i x
    have hFm : Measurable F₀ := Finset.measurable_sum _ (fun i _ =>
      (((measurable_pi_iff.mp ham) i).comp hq).mul (hm i))
    have hGm₀ : Measurable G₀ := Finset.measurable_sum _ (fun i _ =>
      (((measurable_pi_iff.mp hbm) i).comp hq).mul (hjm i))
    have hFbound (x : X) : ‖F₀ x‖ ≤ B*C := module_bound _ _ hB (hab _) (hb _)
    have hmajor (x : X) : dist (H (k • x)*G (k • x)) (F₀ x*G₀ x)^2 ≤
        2*(RG^2*dist (H (k • x)) (F₀ x)^2 + (B*C)^2*dist (G (k • x)) (G₀ x)^2) := by
      have heq : H (k • x)*G (k • x)-F₀ x*G₀ x =
          (H (k • x)-F₀ x)*G (k • x)+F₀ x*(G (k • x)-G₀ x) := by ring
      have hn : dist (H (k • x)*G (k • x)) (F₀ x*G₀ x) ≤
          RG*dist (H (k • x)) (F₀ x) + (B*C)*dist (G (k • x)) (G₀ x) := by
        rw [dist_eq_norm, heq]
        refine (norm_add_le _ _).trans ?_
        simp only [norm_mul, ← dist_eq_norm]
        exact add_le_add (by nlinarith [hGb (k • x), dist_nonneg (x := H (k • x)) (y := F₀ x)])
          (mul_le_mul_of_nonneg_right (hFbound x) dist_nonneg)
      have h₁ : 0 ≤ RG*dist (H (k • x)) (F₀ x) := mul_nonneg hRG dist_nonneg
      have h₂ : 0 ≤ (B*C)*dist (G (k • x)) (G₀ x) := mul_nonneg (mul_nonneg hB hC) dist_nonneg
      nlinarith [dist_nonneg (x := H (k • x)*G (k • x)) (y := F₀ x*G₀ x),
        sq_nonneg (RG*dist (H (k • x)) (F₀ x) - (B*C)*dist (G (k • x)) (G₀ x))]
    have hiM : Integrable (fun x => 2*(RG^2*dist (H (k • x)) (F₀ x)^2 +
        (B*C)^2*dist (G (k • x)) (G₀ x)^2)) μ :=
      ((hai.const_mul (RG^2)).add (hbi.const_mul ((B*C)^2))).const_mul 2
    have hi : Integrable (fun x => dist (H (k • x)*G (k • x)) (F₀ x*G₀ x)^2) μ :=
      hiM.mono' ((((hHm.comp (measurable_const_smul k)).mul (hGm.comp (measurable_const_smul k))).dist
        (hFm.mul hGm₀)).pow_const 2).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs, abs_sq] using hmajor x)
    have hδB : RG*δ < ε/2 := by
      dsimp [δ]
      have hh : 0 < 2*(RG+1) := by positivity
      rw [← mul_div_assoc, div_lt_iff₀ hh]
      nlinarith
    have hγB : (B*C)*γ < ε/2 := by
      dsimp [γ]
      have hh : 0 < 2*(B*C+1) := by positivity
      rw [← mul_div_assoc, div_lt_iff₀ hh]
      nlinarith
    have he : (∫ x, dist (H (k • x)*G (k • x)) (F₀ x*G₀ x)^2 ∂μ) < ε^2 := by
      calc
        _ ≤ ∫ x, 2*(RG^2*dist (H (k • x)) (F₀ x)^2 +
            (B*C)^2*dist (G (k • x)) (G₀ x)^2) ∂μ := integral_mono hi hiM hmajor
        _ = 2*(RG^2*(∫ x, dist (H (k • x)) (F₀ x)^2 ∂μ) +
            (B*C)^2*∫ x, dist (G (k • x)) (G₀ x)^2 ∂μ) := by
          rw [integral_const_mul, integral_add (hai.const_mul _) (hbi.const_mul _),
            integral_const_mul, integral_const_mul]
        _ ≤ 2*((RG*δ)^2 + ((B*C)*γ)^2) := by
          have h₁ := mul_le_mul_of_nonneg_left hae.le (sq_nonneg RG)
          have h₂ := mul_le_mul_of_nonneg_left hbe.le (sq_nonneg (B*C))
          dsimp [F₀, G₀]
          nlinarith
        _ < ε^2 := by
          have h₁ := sq_lt_sq₀ (mul_nonneg hRG hδ.le) (by positivity : 0 ≤ ε/2) |>.mpr hδB
          have h₂ := sq_lt_sq₀ (mul_nonneg (mul_nonneg hB hC) hγ.le) (by positivity : 0 ≤ ε/2) |>.mpr hγB
          nlinarith
    have hs (x : X) : (∑ i : Fin r × Fin s, A (q x) i * (F i.1 x * J i.2 x)) = F₀ x*G₀ x := by
      simp only [Fintype.sum_prod_type, A, F₀, G₀, Finset.sum_mul_sum]
      congr 1
      funext i
      congr 1
      funext j
      ring
    refine ⟨A, hAm, hAb, ?_, ?_⟩
    · simpa only [hs] using hi
    · simpa only [hs] using he

lemma compact_of_l2_approximation {μ : Measure X} {q : X → Y} {H : X → ℂ}
    [MeasurableConstSMul K X] (hq : Measurable q) (hHm : Measurable H)
    (hpres : ∀ k : K, MeasurePreserving (fun x : X => k • x) μ μ)
    (happ : ∀ δ : ℝ, 0 < δ → ∃ G : X → ℂ, Measurable G ∧ Compact (K := K) μ q G ∧
      Integrable (fun x => dist (H x) (G x)^2) μ ∧ (∫ x, dist (H x) (G x)^2 ∂μ) < δ^2) :
    Compact (K := K) μ q H := by
  intro ε hε
  obtain ⟨G, hGm, hG, hi₀, he₀⟩ := happ (ε/2) (by positivity)
  obtain ⟨r, B, C, F, hB, hC, hm, hb, ha⟩ := hG (ε/2) (by positivity)
  refine ⟨r, B, C, F, hB, hC, hm, hb, ?_⟩
  intro k
  obtain ⟨a, ham, hab, hai, hae⟩ := ha k
  let F₀ : X → ℂ := fun x => ∑ i, a (q x) i * F i x
  have hFm : Measurable F₀ := Finset.measurable_sum _ (fun i _ =>
    (((measurable_pi_iff.mp ham) i).comp hq).mul (hm i))
  have hi₁ : Integrable (fun x => dist (H (k • x)) (G (k • x))^2) μ :=
    (hpres k).integrable_comp hi₀.aestronglyMeasurable |>.mpr hi₀
  have he₁ : (∫ x, dist (H (k • x)) (G (k • x))^2 ∂μ) < (ε/2)^2 := by
    have hm₀ : AEStronglyMeasurable (fun x => dist (H x) (G x)^2) (μ.map (fun x : X => k • x)) := by
      rw [(hpres k).map_eq]
      exact hi₀.aestronglyMeasurable
    rw [← integral_map (hpres k).measurable.aemeasurable hm₀, (hpres k).map_eq]
    exact he₀
  have hiM : Integrable (fun x => 2*(dist (H (k • x)) (G (k • x))^2 +
      dist (G (k • x)) (F₀ x)^2)) μ := (hi₁.add hai).const_mul 2
  have hmajor (x : X) := dist_sq_chain (H (k • x)) (G (k • x)) (F₀ x)
  have hi : Integrable (fun x => dist (H (k • x)) (F₀ x)^2) μ :=
    hiM.mono' (((hHm.comp (measurable_const_smul k)).dist hFm).pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs, abs_sq] using hmajor x)
  refine ⟨a, ham, hab, hi, ?_⟩
  calc
    _ ≤ ∫ x, 2*(dist (H (k • x)) (G (k • x))^2 + dist (G (k • x)) (F₀ x)^2) ∂μ :=
      integral_mono hi hiM hmajor
    _ = 2*((∫ x, dist (H (k • x)) (G (k • x))^2 ∂μ) + ∫ x, dist (G (k • x)) (F₀ x)^2 ∂μ) := by
      rw [integral_const_mul, integral_add hi₁ hai]
    _ < ε^2 := by dsimp [F₀]; nlinarith

end EuclideanFiveColor.CompactFunctions

namespace EuclideanFiveColor.Quantize
open MeasureTheory
variable {A Y : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]
  [MeasurableSpace Y]

lemma finite_measurable_choice {n : ℕ} (P : Y → Fin n → Prop)
    (hm : ∀ i, MeasurableSet {y | P y i}) (he : ∀ y, ∃ i, P y i) :
    ∃ f : Y → Fin n, Measurable f ∧ ∀ y, P y (f y) := by
  classical
  let Q : Y → ℕ → Prop := fun y k => ∃ i : Fin n, i.val = k ∧ P y i
  have hQ (y : Y) : ∃ k, Q y k := by
    obtain ⟨i, hi⟩ := he y
    exact ⟨i.val, i, rfl, hi⟩
  have hmQ (k : ℕ) : MeasurableSet {y | Q y k} := by
    have heq : {y | Q y k} = ⋃ i : Fin n, {y | i.val = k} ∩ {y | P y i} := by
      ext y
      simp only [Q, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    rw [heq]
    apply MeasurableSet.iUnion
    intro i
    exact (MeasurableSet.const _).inter (hm i)
  let f₀ : Y → ℕ := fun y => Nat.find (hQ y)
  have hf₀ : Measurable f₀ := measurable_find hQ hmQ
  have hf₀B (y : Y) : f₀ y < n := by
    obtain ⟨i, hi, _⟩ := Nat.find_spec (hQ y)
    change Nat.find (hQ y) < n
    rw [← hi]
    exact i.isLt
  have hmF : Measurable (fun y => (⟨f₀ y, hf₀B y⟩ : Fin n)) := by
    apply measurable_to_countable'
    intro i
    convert hf₀ (measurableSet_singleton i.val) using 1
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Fin.ext_iff]
  refine ⟨fun y => ⟨f₀ y, hf₀B y⟩, hmF, ?_⟩
  intro y
  obtain ⟨i, hi, hp⟩ := Nat.find_spec (hQ y)
  have heq : i = ⟨f₀ y, hf₀B y⟩ := Fin.ext hi
  simpa only [heq] using hp

lemma compact_quantization {s : Set A} (hs : IsCompact s) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ (n : ℕ) (c : Fin n → A), (∀ i, c i ∈ s) ∧
      ∀ a : Y → A, Measurable a → (∀ y, a y ∈ s) →
        ∃ f : Y → Fin n, Measurable f ∧ ∀ y, dist (a y) (c (f y)) < ρ := by
  classical
  obtain ⟨u, hus, hu, hcover⟩ := hs.finite_cover_balls hρ
  let t := hu.toFinset
  let e : Fin t.card ≃ t := t.equivFin.symm
  let c : Fin t.card → A := fun i => (e i).val
  have hc (i : Fin t.card) : c i ∈ s := hus (by simpa only [t, hu.mem_toFinset] using (e i).property)
  refine ⟨t.card, c, hc, ?_⟩
  intro a ham has
  have he (y : Y) : ∃ i, dist (a y) (c i) < ρ := by
    obtain ⟨v, hv⟩ := Set.mem_iUnion.mp (hcover (has y))
    obtain ⟨hvu, hv⟩ := Set.mem_iUnion.mp hv
    have hvt : v ∈ t := by simpa only [t, hu.mem_toFinset] using hvu
    refine ⟨e.symm ⟨v, hvt⟩, ?_⟩
    simpa only [c, Equiv.apply_symm_apply, Metric.mem_ball] using hv
  exact finite_measurable_choice (fun y i => dist (a y) (c i) < ρ)
    (fun _ => measurableSet_lt (ham.dist measurable_const) measurable_const) he
end EuclideanFiveColor.Quantize

namespace EuclideanFiveColor.CompactFunctions

section
open MeasureTheory
open scoped BigOperators
variable {K X Y : Type*} [SMul K X] [MeasurableSpace X] [MeasurableSpace Y]

lemma combination_dist {r : ℕ} (F : Fin r → ℂ) (a b : Fin r → ℂ) :
    dist (∑ i, a i * F i) (∑ i, b i * F i) ≤ dist a b * ∑ i, ‖F i‖ := by
  rw [dist_eq_norm, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, ‖a i * F i - b i * F i‖ := norm_sum_le _ _
    _ ≤ ∑ i, dist a b * ‖F i‖ := Finset.sum_le_sum fun i _ => by
      rw [← sub_mul, norm_mul]
      exact mul_le_mul_of_nonneg_right (by simpa only [dist_eq_norm] using dist_le_pi_dist a b i) (norm_nonneg _)
    _ = _ := by rw [Finset.mul_sum]

lemma compact_lipschitz {μ : Measure X} [IsProbabilityMeasure μ] {q : X → Y} {H : X → ℂ}
    [MeasurableConstSMul K X] (hq : Measurable q) (hHm : Measurable H)
    (hH : Compact (K := K) μ q H) (f : ℂ → ℂ) (L : NNReal) (hLip : LipschitzWith L f) :
    Compact (K := K) μ q (fun x => f (H x)) := by
  intro ε hε
  let τ := ε/(4*((L : ℝ)+1))
  have hτ : 0 < τ := by dsimp [τ]; positivity
  obtain ⟨r, B, C, F, hB, hC, hm, hb, ha⟩ := hH τ hτ
  let η := τ/(C+1)
  have hη : 0 < η := by dsimp [η]; positivity
  have hηC : η*C ≤ τ := by
    dsimp [η]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : 0 < C+1)]
    nlinarith
  have hs : IsCompact {a : Fin r → ℂ | ‖a‖ ≤ B} := by
    simpa only [Metric.closedBall, dist_zero_right] using isCompact_closedBall (0 : Fin r → ℂ) B
  obtain ⟨n, c, hc, hquant⟩ := Quantize.compact_quantization (Y := Y) hs hη
  let J : Fin n → X → ℂ := fun i x => f (∑ j, c i j * F j x)
  have hjm (i : Fin n) : Measurable (J i) := hLip.continuous.measurable.comp
    (Finset.measurable_sum _ (fun j _ => measurable_const.mul (hm j)))
  let R := ‖f 0‖ + (L : ℝ)*(B*C)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hJb (i : Fin n) (x : X) : ‖J i x‖ ≤ R := by
    have hnorm : ‖∑ j, c i j * F j x‖ ≤ B*C := module_bound _ _ hB (hc i) (hb x)
    have hl := hLip.dist_le_mul (∑ j, c i j * F j x) 0
    rw [dist_zero_right] at hl
    have ht : ‖J i x‖ ≤ dist (J i x) (f 0) + ‖f 0‖ := by
      simpa only [dist_eq_norm, sub_add_cancel] using norm_add_le (J i x - f 0) (f 0)
    dsimp [J, R] at *
    nlinarith [mul_le_mul_of_nonneg_left hnorm L.coe_nonneg]
  refine ⟨n, 1, n*R, J, by norm_num, mul_nonneg (Nat.cast_nonneg _) hR, hjm, ?_, ?_⟩
  · intro x
    simpa using (Finset.sum_le_sum (s := Finset.univ) fun i _ => hJb i x)
  · intro k
    obtain ⟨a, ham, hab, hai, hae⟩ := ha k
    obtain ⟨b, hbm, hbd⟩ := hquant a ham hab
    let A : Y → Fin n → ℂ := fun y i => if b y = i then 1 else 0
    have hAm : Measurable A := Measurable.of_eval (fun i =>
      measurable_const.piecewise (hbm (measurableSet_singleton i)) measurable_const)
    have hAb (y : Y) : ‖A y‖ ≤ 1 := by
      rw [pi_norm_le_iff_of_nonneg (by norm_num)]
      intro i
      dsimp [A]
      split_ifs <;> norm_num
    let F₀ : X → ℂ := fun x => ∑ i, a (q x) i * F i x
    let F₁ : X → ℂ := fun x => ∑ i, c (b (q x)) i * F i x
    have hF₁ : Measurable F₁ := Finset.measurable_sum _ (fun i _ =>
      ((measurable_of_countable (fun j => c j i)).comp (hbm.comp hq)).mul (hm i))
    have hsel (x : X) : (∑ i, A (q x) i * J i x) = f (F₁ x) := by
      rw [Finset.sum_eq_single (b (q x))]
      · simp [A, J, F₁]
      · intro i _ hi
        simp [A, Ne.symm hi]
      · simp
    have hdist (x : X) : dist (F₀ x) (F₁ x) ≤ τ := by
      calc
        _ ≤ dist (a (q x)) (c (b (q x))) * ∑ i, ‖F i x‖ := combination_dist _ _ _
        _ ≤ η*C := mul_le_mul (hbd (q x)).le (hb x) (Finset.sum_nonneg fun _ _ => norm_nonneg _) hη.le
        _ ≤ τ := hηC
    have hmajor (x : X) : dist (f (H (k • x))) (f (F₁ x))^2 ≤
        2*(L : ℝ)^2*(dist (H (k • x)) (F₀ x)^2 + τ^2) := by
      have ht := (dist_triangle (H (k • x)) (F₀ x) (F₁ x)).trans
        (add_le_add le_rfl (hdist x))
      have hl := (hLip.dist_le_mul (H (k • x)) (F₁ x)).trans
        (mul_le_mul_of_nonneg_left ht L.coe_nonneg)
      have hs₀ : dist (f (H (k • x))) (f (F₁ x))^2 ≤
          ((L : ℝ)*(dist (H (k • x)) (F₀ x)+τ))^2 :=
        pow_le_pow_left₀ dist_nonneg hl 2
      have hsq : (dist (H (k • x)) (F₀ x)+τ)^2 ≤ 2*(dist (H (k • x)) (F₀ x)^2+τ^2) := by
        nlinarith [sq_nonneg (dist (H (k • x)) (F₀ x)-τ)]
      have hmul := mul_le_mul_of_nonneg_left hsq (sq_nonneg (L : ℝ))
      nlinarith
    have hiM : Integrable (fun x => 2*(L : ℝ)^2*(dist (H (k • x)) (F₀ x)^2+τ^2)) μ :=
      (hai.add (integrable_const _)).const_mul _
    have hi : Integrable (fun x => dist (f (H (k • x))) (f (F₁ x))^2) μ :=
      hiM.mono' (((hLip.continuous.measurable.comp (hHm.comp (measurable_const_smul k))).dist
        (hLip.continuous.measurable.comp hF₁)).pow_const 2).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs, abs_sq] using hmajor x)
    have hLτ : (L : ℝ)*τ < ε/4 := by
      dsimp [τ]
      rw [← mul_div_assoc, div_lt_iff₀ (by positivity : 0 < 4*((L : ℝ)+1))]
      nlinarith
    have he : (∫ x, dist (f (H (k • x))) (f (F₁ x))^2 ∂μ) < ε^2 := by
      calc
        _ ≤ ∫ x, 2*(L : ℝ)^2*(dist (H (k • x)) (F₀ x)^2+τ^2) ∂μ := integral_mono hi hiM hmajor
        _ = 2*(L : ℝ)^2*((∫ x, dist (H (k • x)) (F₀ x)^2 ∂μ)+τ^2) := by
          rw [integral_const_mul, integral_add hai (integrable_const _), integral_const,
            probReal_univ, smul_eq_mul, one_mul]
        _ ≤ 4*((L : ℝ)*τ)^2 := by
          have htt := mul_le_mul_of_nonneg_left hae.le (by positivity : 0 ≤ 2*(L : ℝ)^2)
          dsimp [F₀]
          nlinarith
        _ < ε^2 := by
          have hsq := (sq_lt_sq₀ (mul_nonneg L.coe_nonneg hτ.le) (by positivity : 0 ≤ ε/4)).mpr hLτ
          nlinarith [sq_pos_of_pos hε]
    refine ⟨A, hAm, hAb, ?_, ?_⟩
    · simpa only [hsel] using hi
    · simpa only [hsel] using he
end
section
open MeasureTheory Filter
open scoped BigOperators Topology
variable {K X Y : Type*} [SMul K X] [MeasurableSpace X] [MeasurableSpace Y]

lemma compact_of_bounded_pointwise_limit {μ : Measure X} [IsProbabilityMeasure μ]
    {q : X → Y} {H : X → ℂ} {Hn : ℕ → X → ℂ} [MeasurableConstSMul K X]
    (hq : Measurable q) (hHm : Measurable H) (hHnm : ∀ n, Measurable (Hn n))
    (hHnc : ∀ n, Compact (K := K) μ q (Hn n))
    (hpres : ∀ k : K, MeasurePreserving (fun x : X => k • x) μ μ)
    (C : ℝ) (hC : 0 ≤ C) (hHb : ∀ x, ‖H x‖ ≤ C) (hHnb : ∀ n x, ‖Hn n x‖ ≤ C)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => Hn n x) atTop (𝓝 (H x))) :
    Compact (K := K) μ q H := by
  have hdist (n : ℕ) (x : X) : dist (H x) (Hn n x)^2 ≤ (2*C)^2 :=
    (sq_le_sq₀ dist_nonneg (mul_nonneg (by norm_num) hC)).mpr
      ((dist_le_norm_add_norm _ _).trans (by linarith [hHb x, hHnb n x]))
  have hi (n : ℕ) : Integrable (fun x => dist (H x) (Hn n x)^2) μ :=
    Integrable.of_bound ((hHm.dist (hHnm n)).pow_const 2).aestronglyMeasurable ((2*C)^2)
      (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs, abs_sq] using hdist n x)
  have hl : Tendsto (fun n => ∫ x, dist (H x) (Hn n x)^2 ∂μ) atTop (𝓝 0) := by
    simpa only [integral_zero] using tendsto_integral_of_dominated_convergence
      (f := fun _ : X => (0 : ℝ)) (fun _ : X => (2*C)^2)
      (fun n => (hi n).aestronglyMeasurable) (integrable_const _) (fun n =>
        Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs, abs_sq] using hdist n x)
      (hlim.mono fun x hx => by
        have ht := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => H x) atTop (𝓝 (H x))).dist hx).pow 2
        simpa only [dist_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using ht)
  apply compact_of_l2_approximation hq hHm hpres
  intro δ hδ
  obtain ⟨n, hn⟩ := (hl.eventually (gt_mem_nhds (sq_pos_of_pos hδ))).exists
  exact ⟨Hn n, hHnm n, hHnc n, hi n, hn⟩

lemma compact_closed_preimage {μ : Measure X} [IsProbabilityMeasure μ]
    {q : X → Y} {H : X → ℂ} [MeasurableConstSMul K X]
    (hq : Measurable q) (hH : Measurable H) (hC : Compact (K := K) μ q H)
    (hpres : ∀ k : K, MeasurePreserving (fun x : X => k • x) μ μ)
    (t : Set ℂ) (ht : IsClosed t) :
    Compact (K := K) μ q ((H ⁻¹' t).indicator (fun _ => (1 : ℂ))) := by
  let δ : ℕ → ℝ := fun n => 1/((n : ℝ)+1)
  have hδ (n : ℕ) : 0 < δ n := by dsimp [δ]; positivity
  let f : ℕ → ℂ → ℂ := fun n z => ((thickenedIndicator (hδ n) t z : ℝ) : ℂ)
  have hf (n : ℕ) : LipschitzWith ((δ n).toNNReal⁻¹) (f n) := by
    have h := Complex.isometry_ofReal.lipschitz.comp
      (NNReal.isometry_coe.lipschitz.comp (lipschitzWith_thickenedIndicator (hδ n) t))
    simpa only [one_mul, Function.comp_def] using h
  have hfb (n : ℕ) (z : ℂ) : ‖f n z‖ ≤ 1 := by
    dsimp [f]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)]
    exact_mod_cast thickenedIndicator_le_one (hδ n) t z
  have hfl (z : ℂ) : Tendsto (fun n => f n z) atTop (𝓝 (t.indicator (fun _ => (1 : ℂ)) z)) := by
    have hh := (tendsto_pi_nhds.mp (thickenedIndicator_tendsto_indicator_closure hδ
      tendsto_one_div_add_atTop_nhds_zero_nat t)) z
    rw [ht.closure_eq] at hh
    have h := Complex.continuous_ofReal.continuousAt.tendsto.comp
      (NNReal.continuous_coe.continuousAt.tendsto.comp hh)
    have he : (((t.indicator (fun _ => (1 : NNReal)) z : NNReal) : ℝ) : ℂ) =
        t.indicator (fun _ => (1 : ℂ)) z := by
      by_cases hz : z ∈ t <;> simp [hz]
    change Tendsto (fun n => f n z) atTop (𝓝 _) at h
    rwa [he] at h
  have hiM : Measurable ((H ⁻¹' t).indicator (fun _ => (1 : ℂ))) :=
    measurable_const.indicator (hH ht.measurableSet)
  apply compact_of_bounded_pointwise_limit hq hiM
    (fun n => (hf n).continuous.measurable.comp hH)
    (fun n => compact_lipschitz hq hH hC (f n) _ (hf n)) hpres 1 (by norm_num)
  · intro x
    by_cases hx : H x ∈ t <;> simp [Set.indicator, hx]
  · intro n x
    exact hfb n (H x)
  · exact Filter.Eventually.of_forall fun x => by
      have he : (H ⁻¹' t).indicator (fun _ => (1 : ℂ)) x =
          t.indicator (fun _ => (1 : ℂ)) (H x) := by
        by_cases hx : H x ∈ t <;> simp [hx]
      simpa only [Function.comp_apply, he] using hfl (H x)

lemma compact_neg {μ : Measure X} [IsProbabilityMeasure μ] {q : X → Y} {H : X → ℂ}
    [MeasurableConstSMul K X]
    (hq : Measurable q) (hm : Measurable H) (hc : Compact (K := K) μ q H) :
    Compact (K := K) μ q (fun x => -H x) := by
  have h := compact_lipschitz hq hm hc (fun z : ℂ => -z) 1 (LipschitzWith.of_dist_le_mul fun x y => by simp [dist_neg_neg])
  exact h

omit [MeasurableSpace X] in
lemma indicator_one_bound (s : Set X) (x : X) : ‖s.indicator (fun _ => (1 : ℂ)) x‖ ≤ 1 := by
  by_cases hx : x ∈ s <;> simp [hx]

lemma compact_compl {μ : Measure X} [IsProbabilityMeasure μ] {q : X → Y} [MeasurableConstSMul K X]
    (hq : Measurable q) {s : Set X} (hm : MeasurableSet s)
    (hc : Compact (K := K) μ q (s.indicator (fun _ => (1 : ℂ)))) :
    Compact (K := K) μ q (sᶜ.indicator (fun _ => (1 : ℂ))) := by
  have hn := compact_neg hq (measurable_const.indicator hm) hc
  have ha := compact_add hq measurable_const (measurable_const.indicator hm).neg
    (compact_const (K := K) μ q 1) hn
  have he : (fun x => (1 : ℂ) + -(s.indicator (fun _ => 1) x)) = sᶜ.indicator (fun _ => 1) := by
    funext x; by_cases hx : x ∈ s <;> simp [hx]
  simpa only [Pi.neg_apply, he] using ha

lemma compact_union {μ : Measure X} [IsProbabilityMeasure μ] {q : X → Y} [MeasurableConstSMul K X]
    (hq : Measurable q) {s t : Set X} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hsc : Compact (K := K) μ q (s.indicator (fun _ => (1 : ℂ))))
    (htc : Compact (K := K) μ q (t.indicator (fun _ => (1 : ℂ)))) :
    Compact (K := K) μ q ((s ∪ t).indicator (fun _ => (1 : ℂ))) := by
  have hsm : Measurable (s.indicator (fun _ => (1 : ℂ))) := measurable_const.indicator hs
  have htm : Measurable (t.indicator (fun _ => (1 : ℂ))) := measurable_const.indicator ht
  have ha := compact_add hq hsm htm hsc htc
  have hp := compact_mul hq hsm htm 1 (by norm_num) (indicator_one_bound t) hsc htc
  have hn := compact_neg hq (hsm.mul htm) hp
  have hh := compact_add hq (hsm.add htm) (hsm.mul htm).neg ha hn
  have he : (fun x => s.indicator (fun _ => (1 : ℂ)) x + t.indicator (fun _ => 1) x +
      -(s.indicator (fun _ => 1) x * t.indicator (fun _ => 1) x)) =
      (s ∪ t).indicator (fun _ => 1) := by
    funext x; by_cases hxs : x ∈ s <;> by_cases hxt : x ∈ t <;> simp [hxs, hxt]
  simpa only [Pi.neg_apply, Pi.add_apply, Pi.mul_apply, he] using hh

lemma compact_iUnion {μ : Measure X} [IsProbabilityMeasure μ] {q : X → Y}
    [MeasurableConstSMul K X] (hq : Measurable q)
    (hpres : ∀ k : K, MeasurePreserving (fun x : X => k • x) μ μ)
    (s : ℕ → Set X) (hm : ∀ n, MeasurableSet (s n))
    (hc : ∀ n, Compact (K := K) μ q ((s n).indicator (fun _ => (1 : ℂ)))) :
    Compact (K := K) μ q ((⋃ n, s n).indicator (fun _ => (1 : ℂ))) := by
  let D : ℕ → Set X := fun n => ⋃ i ∈ Finset.range n, s i
  have hDm (n : ℕ) : MeasurableSet (D n) := MeasurableSet.iUnion (fun i => MeasurableSet.iUnion (fun _ => hm i))
  have hDc (n : ℕ) : Compact (K := K) μ q ((D n).indicator (fun _ => (1 : ℂ))) := by
    induction n with
    | zero => simpa [D] using compact_const (K := K) μ q 0
    | succ n ih =>
      have he : D (n+1) = s n ∪ D n := by simp only [D, Finset.range_add_one, Finset.set_biUnion_insert]
      rw [he]
      exact compact_union hq (hm n) (hDm n) (hc n) ih
  apply compact_of_bounded_pointwise_limit hq (measurable_const.indicator (MeasurableSet.iUnion hm))
    (fun n => measurable_const.indicator (hDm n)) hDc hpres 1 (by norm_num)
    (indicator_one_bound _) (fun n => indicator_one_bound (D n))
  exact Filter.Eventually.of_forall fun x => by
    apply tendsto_const_nhds.congr'
    by_cases hx : x ∈ ⋃ n, s n
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      filter_upwards [eventually_ge_atTop (i+1)] with n hn
      have hix : x ∈ D n := Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨by simpa using hn, hi⟩⟩
      simp [hx, hix]
    · have hnx (n : ℕ) : x ∉ D n := by
        intro hh
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hh
        obtain ⟨_, hi⟩ := Set.mem_iUnion.mp hi
        exact hx (Set.mem_iUnion.mpr ⟨i, hi⟩)
      exact Filter.Eventually.of_forall fun n => by simp [hx, hnx n]

private abbrev compactSigma (μ : Measure X) [IsProbabilityMeasure μ] (q : X → Y)
    [MeasurableConstSMul K X] (hq : Measurable q)
    (hpres : ∀ k : K, MeasurePreserving (fun x : X => k • x) μ μ) : MeasurableSpace X where
  MeasurableSet' s := MeasurableSet s ∧ Compact (K := K) μ q (s.indicator (fun _ => (1 : ℂ)))
  measurableSet_empty := ⟨MeasurableSet.empty, by simpa using compact_const (K := K) μ q 0⟩
  measurableSet_compl s hs := ⟨hs.1.compl, compact_compl hq hs.1 hs.2⟩
  measurableSet_iUnion s hs := ⟨MeasurableSet.iUnion (fun n => (hs n).1),
    compact_iUnion hq hpres s (fun n => (hs n).1) (fun n => (hs n).2)⟩

lemma compactSigma_le (μ : Measure X) [IsProbabilityMeasure μ] (q : X → Y)
    [MeasurableConstSMul K X] (hq : Measurable q)
    (hpres : ∀ k : K, MeasurePreserving (fun x : X => k • x) μ μ) :
    compactSigma μ q hq hpres ≤ ‹MeasurableSpace X› := fun _ hs => hs.1

lemma measurable_compactSigma {μ : Measure X} [IsProbabilityMeasure μ] {q : X → Y}
    [MeasurableConstSMul K X] (hq : Measurable q)
    (hpres : ∀ k : K, MeasurePreserving (fun x : X => k • x) μ μ)
    {H : X → ℂ} (hm : Measurable H) (hc : Compact (K := K) μ q H) :
    @Measurable X ℂ (compactSigma μ q hq hpres) inferInstance H := by
  rw [measurable_iff_comap_le]
  change MeasurableSpace.comap H (borel ℂ) ≤ compactSigma μ q hq hpres
  rw [borel_eq_generateFrom_isClosed, MeasurableSpace.comap_generateFrom]
  apply MeasurableSpace.generateFrom_le
  rintro _ ⟨t, ht, rfl⟩
  exact ⟨hm ht.measurableSet, compact_closed_preimage hq hm hc hpres t ht⟩

end
section
open MeasureTheory Filter
open scoped BigOperators Topology
variable {K X Y : Type*} [SMul K X] [MeasurableSpace X] [MeasurableSpace Y]

lemma compact_simple {μ : Measure X} [IsProbabilityMeasure μ] {q : X → Y}
    [MeasurableConstSMul K X] (hq : Measurable q)
    (hpres : ∀ k : K, MeasurePreserving (fun x : X => k • x) μ μ)
    (f : @SimpleFunc X (compactSigma μ q hq hpres) ℂ) :
    Compact (K := K) μ q f := by
  apply @SimpleFunc.induction X ℂ (compactSigma μ q hq hpres) _
    (fun f => Compact (K := K) μ q f) ?_ ?_ f
  · intro c s hs
    have hsm : MeasurableSet s := hs.1
    have hsc : Compact (K := K) μ q (s.indicator (fun _ => (1 : ℂ))) := hs.2
    have hh := compact_mul hq measurable_const (measurable_const.indicator hsm)
      1 (by norm_num) (indicator_one_bound s) (compact_const (K := K) μ q c) hsc
    convert hh using 1
    funext x
    by_cases hx : x ∈ s <;> simp [hx]
  · intro f g _ hf hg
    exact compact_add hq ((@SimpleFunc.measurable X ℂ (compactSigma μ q hq hpres) _ f).mono (compactSigma_le μ q hq hpres) le_rfl)
      ((@SimpleFunc.measurable X ℂ (compactSigma μ q hq hpres) _ g).mono (compactSigma_le μ q hq hpres) le_rfl) hf hg

lemma compact_of_measurable_compactSigma {μ : Measure X} [IsProbabilityMeasure μ] {q : X → Y}
    [MeasurableConstSMul K X] (hq : Measurable q)
    (hpres : ∀ k : K, MeasurePreserving (fun x : X => k • x) μ μ)
    {H : X → ℂ} (hm : @Measurable X ℂ (compactSigma μ q hq hpres) inferInstance H)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, ‖H x‖ ≤ C) :
    Compact (K := K) μ q H := by
  let F : ℕ → @SimpleFunc X (compactSigma μ q hq hpres) ℂ :=
    @SimpleFunc.approxOn ℂ X _ _ _ (compactSigma μ q hq hpres) H hm Set.univ 0 (Set.mem_univ 0) inferInstance
  have hHm : Measurable H := hm.mono (compactSigma_le μ q hq hpres) le_rfl
  have hFm (n : ℕ) : Measurable (F n) :=
    (@SimpleFunc.measurable X ℂ (compactSigma μ q hq hpres) _ (F n)).mono (compactSigma_le μ q hq hpres) le_rfl
  apply compact_of_bounded_pointwise_limit hq hHm hFm
    (fun n => compact_simple hq hpres (F n)) hpres (2*C) (by positivity)
  · intro x; have := hb x; linarith
  · intro n x
    exact (@SimpleFunc.norm_approxOn_zero_le X ℂ (compactSigma μ q hq hpres) _ _ _ H hm Set.univ (Set.mem_univ 0) inferInstance x n).trans (by linarith [hb x])
  · exact Filter.Eventually.of_forall fun x => @SimpleFunc.tendsto_approxOn ℂ X _ _ _ (compactSigma μ q hq hpres) H hm Set.univ 0
      (Set.mem_univ 0) inferInstance x (by simp)

lemma compact_base {μ : Measure X} {q : X → Y} [SMul K Y] [MeasurableConstSMul K Y]
    (hqcov : ∀ k : K, ∀ᵐ x ∂μ, q (k • x) = k • q x)
    (b : Y → ℂ) (hbm : Measurable b) (B : ℝ) (hB : 0 ≤ B) (hb : ∀ y, ‖b y‖ ≤ B) :
    Compact (K := K) μ q (b ∘ q) := by
  intro ε hε
  apply at_of_finite (I := Unit) B 1 (fun _ _ => 1) hB (by norm_num) (fun _ => measurable_const)
  · intro x; simp
  · intro k
    refine ⟨fun y _ => b (k • y), Measurable.of_eval (fun _ => hbm.comp (measurable_const_smul k)), ?_, ?_, ?_⟩
    · intro y; simpa using hb (k • y)
    · apply (integrable_zero X ℝ μ).congr
      filter_upwards [hqcov k] with x hx
      simp [Function.comp_apply, hx]
    · have he : (fun x => dist ((b ∘ q) (k • x)) (∑ _ : Unit, b (k • q x) * 1)^2) =ᵐ[μ]
          (fun _ => (0 : ℝ)) := by
        filter_upwards [hqcov k] with x hx
        simp [Function.comp_apply, hx]
      rw [integral_congr_ae he, integral_zero]
      exact sq_pos_of_pos hε

end
section
open MeasureTheory Filter
open scoped BigOperators Topology
variable {K X Y : Type*} [Monoid K] [MulAction K X] [MulAction K Y]
  [MeasurableSpace X] [MeasurableSpace Y]

omit [MulAction K Y] in
lemma compact_shift {μ : Measure X} {q : X → Y} {H : X → ℂ}
    (hc : Compact (K := K) μ q H) (g : K) :
    Compact (K := K) μ q (fun x => H (g • x)) := by
  intro ε hε
  obtain ⟨r, B, C, Hf, hB, hC, hm, hb, ha⟩ := hc ε hε
  refine ⟨r, B, C, Hf, hB, hC, hm, hb, ?_⟩
  intro k
  simpa only [smul_smul] using ha (g*k)

omit [MulAction K Y] in
lemma measurable_shift_compactSigma {μ : Measure X} [IsProbabilityMeasure μ] {q : X → Y}
    [MeasurableConstSMul K X] (hq : Measurable q)
    (hpres : ∀ k : K, MeasurePreserving (fun x : X => k • x) μ μ) (g : K) :
    @Measurable X X (compactSigma μ q hq hpres) (compactSigma μ q hq hpres) (fun x => g • x) := by
  intro s hs
  refine ⟨(measurable_const_smul g) hs.1, ?_⟩
  have hh := compact_shift hs.2 g
  have he : (fun x => (s.indicator (fun _ => (1 : ℂ))) (g • x)) =
      ((fun x : X => g • x) ⁻¹' s).indicator (fun _ => 1) := by
    funext x; by_cases hx : g • x ∈ s <;> simp [hx]
  rwa [he] at hh

lemma measurable_base_compactSigma {μ : Measure X} [IsProbabilityMeasure μ] {q : X → Y}
    [MeasurableConstSMul K X] [MeasurableConstSMul K Y] (hq : Measurable q)
    (hpres : ∀ k : K, MeasurePreserving (fun x : X => k • x) μ μ)
    (hqcov : ∀ k : K, ∀ᵐ x ∂μ, q (k • x) = k • q x) :
    @Measurable X Y (compactSigma μ q hq hpres) inferInstance q := by
  intro s hs
  refine ⟨hq hs, ?_⟩
  have hh := compact_base hqcov (s.indicator (fun _ => (1 : ℂ)))
    (measurable_const.indicator hs) 1 (by norm_num) (indicator_one_bound s)
  have he : (s.indicator (fun _ => (1 : ℂ))) ∘ q =
      (q ⁻¹' s).indicator (fun _ => 1) := by
    funext x; by_cases hx : q x ∈ s <;> simp [Function.comp_apply, hx]
  rwa [he] at hh

end

open MeasureTheory ProbabilityTheory ConditionalFiber
open scoped BigOperators
variable {K X Z Y : Type*} [SMul K X] [SMul K Z]
  [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace Y]
  [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Z] [Nonempty Z]
  [MeasurableConstSMul K X] [MeasurableConstSMul K Z]

lemma compact_descend (μ : Measure X) [IsProbabilityMeasure μ]
    (π : X → Z) (hπ : Measurable π) (p : Z → Y) (hp : Measurable p)
    (hπcov : ∀ k : K, ∀ᵐ x ∂μ, π (k • x) = k • π x)
    (H : Z → ℂ) (hH : Measurable H) (D : ℝ) (_hD : 0 ≤ D)
    (hHD : ∀ z, ‖H z‖ ≤ D)
    (hc : Compact (K := K) μ (p ∘ π) (H ∘ π)) :
    Compact (K := K) (μ.map π) p H := by
  let κ := condDistrib id π μ
  let ν := μ.map π
  let : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hπ.aemeasurable
  intro ε hε
  obtain ⟨r, B, C, F, hB, hC, hFm, hFb, ha⟩ := hc ε hε
  have hFC (i : Fin r) (x : X) : ‖F i x‖ ≤ C :=
    (Finset.single_le_sum (fun j _ => norm_nonneg (F j x)) (Finset.mem_univ i)).trans (hFb x)
  have hFi (z : Z) (i : Fin r) : Integrable (F i) (κ z) :=
    Integrable.of_bound (hFm i).aestronglyMeasurable C (Filter.Eventually.of_forall (hFC i))
  let G : Fin r → Z → ℂ := fun i z => ∫ x, F i x ∂κ z
  have hGm (i : Fin r) : Measurable (G i) :=
    (hFm i).stronglyMeasurable.integral_kernel.measurable
  have hGb (z : Z) : ∑ i, ‖G i z‖ ≤ C := by
    calc
      ∑ i, ‖G i z‖ ≤ ∑ i, ∫ x, ‖F i x‖ ∂κ z :=
        Finset.sum_le_sum fun i _ => norm_integral_le_integral_norm _
      _ = ∫ x, ∑ i, ‖F i x‖ ∂κ z :=
        (integral_finsetSum _ (fun i _ => (hFi z i).norm)).symm
      _ ≤ ∫ _x, C ∂κ z := integral_mono
        (integrable_finsetSum _ (fun i _ => (hFi z i).norm)) (integrable_const C) hFb
      _ = C := by simp
  refine ⟨r, B, C, G, hB, hC, hGm, hGb, ?_⟩
  intro k
  obtain ⟨a, ham, hab, hai, hae⟩ := ha k
  let E : X → ℂ := fun x => H (π (k • x)) - ∑ i, a (p (π x)) i * F i x
  have hEm : Measurable E := ((hH.comp hπ).comp (measurable_const_smul k)).sub
    (Finset.measurable_sum _ (fun i _ =>
      (((measurable_pi_iff.mp ham) i).comp (hp.comp hπ)).mul (hFm i)))
  have hEB (x : X) : ‖E x‖ ≤ D+B*C :=
    (norm_sub_le _ _).trans (add_le_add (hHD _) (module_bound _ _ hB (hab _) (hFb x)))
  have hEi (z : Z) : Integrable E (κ z) :=
    Integrable.of_bound hEm.aestronglyMeasurable (D+B*C) (Filter.Eventually.of_forall hEB)
  have hE₂i (z : Z) : Integrable (fun x => ‖E x‖^2) (κ z) :=
    Integrable.of_bound (hEm.norm.pow_const 2).aestronglyMeasurable ((D+B*C)^2)
      (Filter.Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs, abs_sq] using
          pow_le_pow_left₀ (norm_nonneg _) (hEB x) 2)
  have hE₂μ : Integrable (fun x => ‖E x‖^2) μ := by
    simpa only [E, Function.comp_apply, dist_eq_norm] using hai
  have hEeq : ∀ᵐ z ∂ν, (∫ x, E x ∂κ z) = H (k • z) - ∑ i, a (p z) i * G i z := by
    filter_upwards [ae_in_own_fiber μ π hπ, ae_fiber_of_ae μ π hπ (hπcov k)] with z hz hc'
    have he : E =ᵐ[κ z] (fun x => H (k • z) - ∑ i, a (p z) i * F i x) := by
      filter_upwards [hz, hc'] with x hx hx'
      dsimp only [E]
      rw [hx', hx]
    rw [integral_congr_ae he, integral_sub (integrable_const _) (integrable_finsetSum _
      fun i _ => (hFi z i).const_mul _), integral_finsetSum _
      (fun i _ => (hFi z i).const_mul _)]
    simp only [integral_const, probReal_univ, one_smul, integral_const_mul, G]
  have hdistm : Measurable (fun z => dist (H (k • z)) (∑ i, a (p z) i * G i z)^2) :=
    ((hH.comp (measurable_const_smul k)).dist
      (Finset.measurable_sum _ (fun i _ => (((measurable_pi_iff.mp ham) i).comp hp).mul (hGm i)))).pow_const 2
  have hdistB (z : Z) : dist (H (k • z)) (∑ i, a (p z) i * G i z)^2 ≤ (D+B*C)^2 := by
    apply pow_le_pow_left₀ dist_nonneg
    exact (dist_le_norm_add_norm _ _).trans
      (add_le_add (hHD _) (module_bound _ _ hB (hab _) (hGb z)))
  have hdisti : Integrable (fun z => dist (H (k • z)) (∑ i, a (p z) i * G i z)^2) ν :=
    Integrable.of_bound hdistm.aestronglyMeasurable ((D+B*C)^2)
      (Filter.Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs, abs_sq] using hdistB z)
  refine ⟨a, ham, hab, hdisti, ?_⟩
  have hle : (∫ z, dist (H (k • z)) (∑ i, a (p z) i * G i z)^2 ∂ν) ≤
      ∫ z, (∫ x, ‖E x‖^2 ∂κ z) ∂ν := by
    apply integral_mono_ae hdisti (integrable_fiber_integral μ π hπ _ hE₂μ)
    filter_upwards [hEeq] with z hz
    rw [dist_eq_norm, ← hz]
    exact KernelCompact.norm_integral_sq (κ z) E (hEi z) (hE₂i z)
  rw [integral_fiber μ π hπ _ hE₂μ] at hle
  apply hle.trans_lt
  simpa only [E, Function.comp_apply, dist_eq_norm] using hae

end EuclideanFiveColor.CompactFunctions

end

end ParishFactor
end

-- OAI.MeasureTheory.CompactFactors.Factors
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
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace EuclideanFiveColor
open MeasureTheory
private structure OrbitSpace (K : Type*) where
  val : K → ℂ

namespace OrbitSpace
variable {K : Type*}
private def equiv (K : Type*) : OrbitSpace K ≃ (K → ℂ) where
  toFun := val
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl

private instance : Inhabited (OrbitSpace K) := ⟨⟨fun _ => 0⟩⟩
private instance : TopologicalSpace (OrbitSpace K) := (equiv K).topologicalSpace
private instance : MeasurableSpace (OrbitSpace K) := borel _
private instance : BorelSpace (OrbitSpace K) := ⟨rfl⟩
private instance [Countable K] : PolishSpace (OrbitSpace K) := (equiv K).polishSpace_induced

lemma ext {a b : OrbitSpace K} (h : ∀ k, a.val k = b.val k) : a = b := by
  cases a; cases b; congr; funext k; exact h k

lemma continuous_val : Continuous (val : OrbitSpace K → K → ℂ) :=
  (equiv K).homeomorph.continuous
lemma continuous_mk : Continuous (mk : (K → ℂ) → OrbitSpace K) :=
  (equiv K).homeomorph.symm.continuous
lemma measurable_val [Countable K] : Measurable (val : OrbitSpace K → K → ℂ) := continuous_val.measurable
lemma measurable_mk [Countable K] : Measurable (mk : (K → ℂ) → OrbitSpace K) := continuous_mk.measurable

private instance [Monoid K] : MulAction K (OrbitSpace K) where
  smul k f := ⟨fun l => f.val (l*k)⟩
  one_smul f := by apply OrbitSpace.ext; intro l; exact congrArg f.val (mul_one l)
  mul_smul a b f := by apply OrbitSpace.ext; intro l; exact congrArg f.val (mul_assoc l a b).symm

@[simp] lemma smul_val [Monoid K] (k : K) (f : OrbitSpace K) (l : K) :
    (k • f).val l = f.val (l*k) := rfl

private instance [Monoid K] : ContinuousConstSMul K (OrbitSpace K) where
  continuous_const_smul k := continuous_mk.comp
    (continuous_pi fun l => (continuous_apply (l*k)).comp continuous_val)
private instance [Monoid K] : MeasurableConstSMul K (OrbitSpace K) where
  measurable_const_smul k := (continuous_const_smul k).measurable

end OrbitSpace

namespace OrbitFactor
variable {K X Y : Type*} [Monoid K] [MulAction K X] [MulAction K Y]
  [MeasurableSpace X] [MeasurableSpace Y]

private def orbit (H : X → ℂ) (x : X) : OrbitSpace K := ⟨fun k => H (k • x)⟩

omit [MulAction K Y] [MeasurableSpace Y] in
lemma measurable_orbit [Countable K] [MeasurableConstSMul K X]
    {H : X → ℂ} (hH : Measurable H) : Measurable (orbit (K := K) H) :=
  OrbitSpace.measurable_mk.comp (Measurable.of_eval fun k => hH.comp (measurable_const_smul k))

omit [MulAction K Y] [MeasurableSpace X] [MeasurableSpace Y] in
lemma orbit_equivariant (H : X → ℂ) (k : K) (x : X) :
    orbit (K := K) H (k • x) = k • orbit H x := by
  apply OrbitSpace.ext; intro l
  exact congrArg H (mul_smul l k x).symm

private def extend (q : X → Y) (H : X → ℂ) (x : X) : Y × OrbitSpace K := (q x, orbit H x)

omit [MulAction K Y] in
lemma measurable_extend [Countable K] [MeasurableConstSMul K X]
    {q : X → Y} (hq : Measurable q) {H : X → ℂ} (hH : Measurable H) :
    Measurable (extend (K := K) q H) := hq.prodMk (measurable_orbit hH)

omit [MeasurableSpace Y] in
lemma extend_equivariant (μ : Measure X) {q : X → Y} (H : X → ℂ)
    (hqcov : ∀ k : K, ∀ᵐ x ∂μ, q (k • x) = k • q x) (k : K) :
    ∀ᵐ x ∂μ, extend (K := K) q H (k • x) = k • extend q H x := by
  filter_upwards [hqcov k] with x hx
  exact Prod.ext hx (orbit_equivariant H k x)

omit [MeasurableSpace X] in
@[simp] lemma orbit_one (H : X → ℂ) (x : X) : (orbit (K := K) H x).val 1 = H x := by
  simp only [orbit, one_smul]

end OrbitFactor
end EuclideanFiveColor

namespace EuclideanFiveColor.OrbitFactor
open MeasureTheory ProbabilityTheory CompactFunctions
variable {K X Y : Type*} [Monoid K] [Countable K] [MulAction K X] [MulAction K Y]
  [MeasurableSpace X] [MeasurableSpace Y]
  [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]
  [MeasurableConstSMul K X] [MeasurableConstSMul K Y]

omit [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y] in
lemma measurable_extend_compactSigma (μ : Measure X) [IsProbabilityMeasure μ]
    (q : X → Y) (hq : Measurable q)
    (hpres : ∀ k : K, MeasurePreserving (fun x : X => k • x) μ μ)
    (hqcov : ∀ k : K, ∀ᵐ x ∂μ, q (k • x) = k • q x)
    (H : X → ℂ) (hH : Measurable H) (hc : Compact (K := K) μ q H) :
    @Measurable X (Y × OrbitSpace K) (compactSigma μ q hq hpres) inferInstance
      (extend (K := K) q H) := by
  have hHm := measurable_compactSigma hq hpres hH hc
  have hpm : @Measurable X (K → ℂ) (compactSigma μ q hq hpres) inferInstance
      (fun x k => H (k • x)) :=
    @Measurable.of_eval X K (fun _ => ℂ) (compactSigma μ q hq hpres) (fun _ => inferInstance) _ (fun k => hHm.comp (measurable_shift_compactSigma hq hpres k))
  exact (measurable_base_compactSigma hq hpres hqcov).prodMk
    (OrbitSpace.measurable_mk.comp hpm)

lemma compact_orbit_extension (μ : Measure X) [IsProbabilityMeasure μ]
    (q : X → Y) (hq : Measurable q)
    (hpres : ∀ k : K, MeasurePreserving (fun x : X => k • x) μ μ)
    (hqcov : ∀ k : K, ∀ᵐ x ∂μ, q (k • x) = k • q x)
    (H : X → ℂ) (hH : Measurable H) (hc : Compact (K := K) μ q H)
    (F : Y × OrbitSpace K → ℂ) (hF : Measurable F)
    (D : ℝ) (hD : 0 ≤ D) (hFD : ∀ z, ‖F z‖ ≤ D) :
    Compact (K := K) (μ.map (extend (K := K) q H)) Prod.fst F := by
  let : MeasurableConstSMul K (Y × OrbitSpace K) := ⟨fun k =>
    ((measurable_const_smul k).comp measurable_fst).prodMk
      ((measurable_const_smul k).comp measurable_snd)⟩
  apply compact_descend μ (extend (K := K) q H) (measurable_extend hq hH)
    Prod.fst measurable_fst (extend_equivariant μ H hqcov) F hF D hD hFD
  change Compact (K := K) μ q (F ∘ extend (K := K) q H)
  exact compact_of_measurable_compactSigma hq hpres
    (hF.comp (measurable_extend_compactSigma μ q hq hpres hqcov H hH hc)) D hD
    (fun x => hFD _)

end EuclideanFiveColor.OrbitFactor
namespace EuclideanFiveColor.KernelCompact
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {K X Y : Type*} [Group K] [MulAction K X] [MulAction K Y]
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace.CountablyGenerated X]
  [MeasurableConstSMul K X] [MeasurableConstSMul K Y]

omit [MeasurableConstSMul K Y] in
lemma compact_applyKernel (μ : Measure X) [IsProbabilityMeasure μ]
    (κ : Kernel Y X) [IsMarkovKernel κ] (q : X → Y) (hq : Measurable q)
    (L : X × X → ℂ) (hL : Measurable L) (C : ℝ) (hC : 0 ≤ C)
    (hLC : ∀ z, ‖L z‖ ≤ C)
    (hqcov : ∀ k : K, ∀ᵐ x ∂μ, q (k • x) = k • q x)
    (hκcov : ∀ k : K, ∀ᵐ y ∂μ.map q, κ (k • y) = (κ y).map (fun x => k • x))
    (hLcov : ∀ k : K, ∀ᵐ z ∂μ ⊗ₘ κ.comap q hq, L (k • z.1, k • z.2) = L z)
    (f : X → ℂ) (hfm : Measurable f) (hfB : ∀ x, ‖f x‖ ≤ 1) :
    CompactFunctions.Compact (K := K) μ q (applyKernel κ q L f) := by
  intro ε hε
  obtain ⟨r, B, C₀, Hf, hB, hC₀, hHm, hHb, ha⟩ :=
    bounded_range_approximation μ κ q hq L hL C hC hLC ε hε
  refine ⟨r, B, C₀, Hf, hB, hC₀, hHm, hHb, ?_⟩
  intro k
  obtain ⟨a, ham, hab, hai, hae⟩ := ha (fun x => f (k • x))
    (hfm.comp (measurable_const_smul k)) (fun x => hfB (k • x))
  have he := applyKernel_covariance μ κ q hq L hL hqcov hκcov hLcov f hfm k
  have hd : (fun x => dist (applyKernel κ q L f (k • x))
      (∑ i, a (q x) i * Hf i x)^2) =ᵐ[μ]
      (fun x => dist (applyKernel κ q L (fun x => f (k • x)) x)
        (∑ i, a (q x) i * Hf i x)^2) := he.mono fun x hx => by dsimp only at hx ⊢; rw [hx]
  exact ⟨a, ham, hab, hai.congr hd.symm, by rw [integral_congr_ae hd]; exact hae⟩

end EuclideanFiveColor.KernelCompact
namespace EuclideanFiveColor.CompactTower
open MeasureTheory ProbabilityTheory KernelCompact CompactFunctions OrbitFactor
variable {K X Y : Type*} [Group K] [Countable K] [MulAction K X] [MulAction K Y]
  [MeasurableSpace X] [MeasurableSpace Y]
  [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]
  [MeasurableConstSMul K X] [MeasurableConstSMul K Y]

theorem strict_compact_successor (μ : Measure X) [IsProbabilityMeasure μ]
    [ErgodicSMul K X μ] (q : X → Y) (hq : Measurable q)
    (hqcov : ∀ k : K, ∀ᵐ x ∂μ, q (k • x) = k • q x)
    (hn : ¬ ErgodicSMul K (X × X) (RelativeProduct.law μ q hq)) :
    ∃ H : X → ℂ, Measurable H ∧ (∀ x, ‖H x‖ ≤ 2) ∧
      (¬ ∃ b : Y → ℂ, Measurable b ∧ H =ᵐ[μ] b ∘ q) ∧
      (∀ F : Y × OrbitSpace K → ℂ, Measurable F →
        (∃ C : ℝ, ∀ z, ‖F z‖ ≤ C) →
        Compact (K := K) (μ.map (extend (K := K) q H)) Prod.fst F) := by
  have hpres (k : K) := measurePreserving_smul k μ
  let κ := condDistrib id q μ
  let : SMulInvariantMeasure K (X × X) (μ ⊗ₘ κ.comap q hq) :=
    RelativeProduct.law_invariant μ q hq hpres hqcov
  have hκcov := RelativeProduct.conditional_covariance μ q hq hpres hqcov
  obtain ⟨L, hLm, hLB, hLcov, hLn, _hrow, hcol⟩ := centered_kernel μ κ q hq
    (RelativeProduct.law_swap μ q hq) hqcov hκcov hn
  obtain ⟨f, hfm, hfB, hfn⟩ := exists_nonzero_image μ κ q hq L hLm 2 (by norm_num) hLB hLn
  let H := applyKernel κ q L f
  have hHm : Measurable H := measurable_applyKernel κ q hq L hLm f hfm
  have hHc : Compact (K := K) μ q H := compact_applyKernel μ κ q hq L hLm 2
    (by norm_num) hLB hqcov hκcov hLcov f hfm hfB
  refine ⟨H, hHm, applyKernel_bound κ q L 2 hLB f hfB, ?_, ?_⟩
  · exact nonzero_not_factorizable μ q hq H hfn
      (image_conditional_mean_zero μ q hq L hLm 2 hLB f hfm hfB hcol)
  · intro F hF hFB
    obtain ⟨C,hC⟩ := hFB
    have hC0 : 0 ≤ C := (norm_nonneg (F (Classical.choice inferInstance))).trans (hC _)
    exact compact_orbit_extension μ q hq hpres hqcov H hHm hHc F hF C hC0 hC

end EuclideanFiveColor.CompactTower

namespace EuclideanFiveColor.FactorCode
open MeasureTheory
variable {K X Y : Type*} [Group K] [Countable K]
  [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace Y]
  [MulAction K X] [MeasurableConstSMul K X]

private def scalar (Y : Type*) [MeasurableSpace Y] [StandardBorelSpace Y] (y : Y) : ℂ :=
  Real.arctan (embeddingReal Y y)

lemma scalar_measurable : Measurable (scalar Y) :=
  Complex.measurable_ofReal.comp (Real.continuous_arctan.measurable.comp (measurable_embeddingReal Y))

lemma scalar_injective : Function.Injective (scalar Y) := by
  intro x y h
  apply (measurableEmbedding_embeddingReal Y).injective
  apply Real.arctan_injective
  exact_mod_cast (show (Real.arctan (embeddingReal Y x) : ℂ) = Real.arctan (embeddingReal Y y) from h)

lemma scalar_embedding : MeasurableEmbedding (scalar Y) :=
  scalar_measurable.measurableEmbedding scalar_injective

lemma scalar_bound (y : Y) : ‖scalar Y y‖ ≤ 2 := by
  rw [scalar, Complex.norm_real, Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · have := Real.neg_pi_div_two_lt_arctan (embeddingReal Y y)
    linarith [Real.pi_lt_four]
  · have := Real.arctan_lt_pi_div_two (embeddingReal Y y)
    linarith [Real.pi_lt_four]

private def encode (p : X → Y) : X → OrbitSpace K := OrbitFactor.orbit (scalar Y ∘ p)

lemma encode_measurable {p : X → Y} (hp : Measurable p) : Measurable (encode (K := K) p) :=
  OrbitFactor.measurable_orbit (scalar_measurable.comp hp)

omit [Countable K] [MeasurableSpace X] [MeasurableConstSMul K X] in
lemma encode_equivariant (p : X → Y) (k : K) (x : X) :
    encode (K := K) p (k • x) = k • encode (K := K) p x := OrbitFactor.orbit_equivariant _ _ _

omit [Countable K] [MeasurableSpace X] [MeasurableConstSMul K X] in
lemma encode_bound (p : X → Y) (x : X) (k : K) : ‖(encode p x).val k‖ ≤ 2 := scalar_bound _

variable [Nonempty Y]
private def decode : OrbitSpace K → Y := fun z => scalar_embedding.invFun (z.val 1)

lemma decode_measurable : Measurable (decode (K := K) (Y := Y)) :=
  scalar_embedding.measurable_invFun.comp ((measurable_pi_apply 1).comp OrbitSpace.measurable_val)

omit [Countable K] [MeasurableSpace X] [MeasurableConstSMul K X] in
lemma decode_encode (p : X → Y) (x : X) : decode (encode (K := K) p x) = p x := by
  dsimp only [decode, encode]
  rw [OrbitFactor.orbit_one]
  exact scalar_embedding.leftInverse_invFun _

omit [Nonempty Y] [MeasurableConstSMul K X] in
lemma encode_as_comp [MulAction K Y] [MeasurableConstSMul K Y]
    (μ : Measure X) (p : X → Y) (hpe : ∀ k : K, ∀ᵐ x ∂μ, p (k • x) = k • p x) :
    ∀ᵐ x ∂μ, encode (K := K) p x = encode (K := K) (id : Y → Y) (p x) := by
  filter_upwards [ae_all_iff.mpr hpe] with x hx
  apply OrbitSpace.ext; intro k
  exact congrArg (scalar Y) (hx k)

end EuclideanFiveColor.FactorCode
namespace EuclideanFiveColor.FactorLp
open MeasureTheory
variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  [StandardBorelSpace Y] [Nonempty Y]

private def space (μ : Measure X) (p : X → Y) : Submodule ℂ (Lp ℂ 2 μ) :=
  lpMeas ℂ ℂ (MeasurableSpace.comap p inferInstance) 2 μ

omit [StandardBorelSpace Y] [Nonempty Y] in
lemma isClosed (μ : Measure X) {p : X → Y} (hp : Measurable p) :
    IsClosed (space μ p : Set (Lp ℂ 2 μ)) :=
  isClosed_aestronglyMeasurable hp.comap_le

omit [StandardBorelSpace Y] [Nonempty Y] in
lemma exists_rep (μ : Measure X) (p : X → Y) (f : Lp ℂ 2 μ) (hf : f ∈ space μ p) :
    ∃ g : Y → ℂ, Measurable g ∧ (f : X → ℂ) =ᵐ[μ] g ∘ p := by
  obtain ⟨h, hh, hfe⟩ := hf
  obtain ⟨g, hg, he⟩ := hh.measurable.exists_eq_measurable_comp (f := p)
  exact ⟨g, hg, by simpa only [he] using hfe⟩

omit [StandardBorelSpace Y] [Nonempty Y] in
lemma mem_of_rep (μ : Measure X) (p : X → Y) (f : Lp ℂ 2 μ)
    (g : Y → ℂ) (hg : Measurable g) (he : (f : X → ℂ) =ᵐ[μ] g ∘ p) : f ∈ space μ p := by
  exact ⟨g ∘ p, (hg.comp (Measurable.of_comap_le le_rfl)).stronglyMeasurable, he⟩

omit [StandardBorelSpace Y] [Nonempty Y] in
lemma le_of_factor (μ : Measure X) (p : X → Y) (q : X → Z)
    (r : Z → Y) (hr : Measurable r) (he : p =ᵐ[μ] r ∘ q) : space μ p ≤ space μ q := by
  intro f hf
  obtain ⟨g, hg, hfe⟩ := exists_rep μ p f hf
  apply mem_of_rep μ q f (g ∘ r) (hg.comp hr)
  filter_upwards [hfe, he] with x hx he
  simpa only [Function.comp_apply, he] using hx

lemma factor_of_le (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → Y) (q : X → Z) (hp : Measurable p) (hle : space μ p ≤ space μ q) :
    ∃ r : Z → Y, Measurable r ∧ p =ᵐ[μ] r ∘ q := by
  let f := FactorCode.scalar Y ∘ p
  have hfm : Measurable f := FactorCode.scalar_measurable.comp hp
  have hf : MemLp f 2 μ := MemLp.of_bound hfm.aestronglyMeasurable 2
    (Filter.Eventually.of_forall fun x => FactorCode.scalar_bound (p x))
  have hmem : hf.toLp f ∈ space μ p := mem_of_rep μ p _ _ FactorCode.scalar_measurable hf.coeFn_toLp
  obtain ⟨g, hg, he⟩ := exists_rep μ q _ (hle hmem)
  refine ⟨FactorCode.scalar_embedding.invFun ∘ g,
    FactorCode.scalar_embedding.measurable_invFun.comp hg, ?_⟩
  filter_upwards [hf.coeFn_toLp, he] with x hx hex
  have hh : f x = g (q x) := hx.symm.trans hex
  change p x = FactorCode.scalar_embedding.invFun (g (q x))
  rw [← hh]
  exact (FactorCode.scalar_embedding.leftInverse_invFun (p x)).symm

end EuclideanFiveColor.FactorLp
namespace EuclideanFiveColor.CountableApprox
open MeasureTheory
variable {Y : Type*} [MeasurableSpace Y]

private def truncate (n : ℕ) (y : ℕ → Y) : Fin n → Y := fun i => y i

lemma truncate_measurable (n : ℕ) : Measurable (truncate (Y := Y) n) :=
  Measurable.of_eval fun i => measurable_pi_apply (i : ℕ)

lemma truncate_mono : Monotone (fun n => (inferInstance : MeasurableSpace (Fin n → Y)).comap (truncate n)) := by
  intro n m hnm
  rw [← measurable_iff_comap_le]
  have hm : Measurable[(inferInstance : MeasurableSpace (Fin m → Y)).comap (truncate m)]
      (truncate (Y := Y) m) := Measurable.of_comap_le le_rfl
  refine @Measurable.of_eval (ℕ → Y) (Fin n) (fun _ => Y)
    (MeasurableSpace.comap (truncate m) inferInstance) (fun _ => inferInstance) (truncate n) ?_
  intro i
  exact (measurable_pi_apply (⟨i, lt_of_lt_of_le i.isLt hnm⟩ : Fin m)).comp hm

lemma truncate_generate : (⨆ n, (inferInstance : MeasurableSpace (Fin n → Y)).comap (truncate n)) =
    (inferInstance : MeasurableSpace (ℕ → Y)) := by
  apply le_antisymm (iSup_le fun n => (truncate_measurable n).comap_le)
  have hm (n : ℕ) : Measurable[⨆ n, (inferInstance : MeasurableSpace (Fin n → Y)).comap (truncate n)]
      (truncate (Y := Y) n) := Measurable.of_comap_le (le_iSup (fun n => MeasurableSpace.comap (truncate (Y := Y) n) (inferInstance : MeasurableSpace (Fin n → Y))) n)
  have hi : Measurable[⨆ n, (inferInstance : MeasurableSpace (Fin n → Y)).comap (truncate n)]
      (id : (ℕ → Y) → (ℕ → Y)) := by
    refine @Measurable.of_eval (ℕ → Y) ℕ (fun _ => Y)
      (⨆ n, MeasurableSpace.comap (truncate n) (inferInstance : MeasurableSpace (Fin n → Y)))
      (fun _ => inferInstance) id ?_
    intro n
    exact (measurable_pi_apply (⟨n, Nat.lt_succ_self n⟩ : Fin (n+1))).comp (hm (n+1))
  simpa using hi.comap_le

lemma bounded_approximation (ν : Measure (ℕ → Y)) [IsProbabilityMeasure ν]
    (m : ℕ) (H : (ℕ → Y) → Fin m → ℂ) (hH : Measurable H)
    (C : ℝ) (hC : 0 ≤ C) (hB : ∀ y, ‖H y‖ ≤ C) (ε : ℝ) (hε : 0 < ε) :
    ∃ n, ∃ H₀ : (Fin n → Y) → Fin m → ℂ, Measurable H₀ ∧ (∀ y, ‖H₀ y‖ ≤ 2*C) ∧
      Integrable (fun y => dist (H y) (H₀ (truncate n y))^2) ν ∧
      (∫ y, dist (H y) (H₀ (truncate n y))^2 ∂ν) < ε^2 :=
  LimitDensity.generated_factor_approximation ν truncate truncate_measurable truncate_mono truncate_generate
    m H hH C hC hB ε hε

end EuclideanFiveColor.CountableApprox
namespace EuclideanFiveColor.ChainJoin
open MeasureTheory
variable {K X Y : Type*} [Group K] [Countable K]
  [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
  [MulAction K X] [MulAction K Y] [MeasurableConstSMul K X] [MeasurableConstSMul K Y]

private def joint (q : ℕ → X → Y) (x : X) : ℕ → Y := fun n => q n x

private def code (q : ℕ → X → Y) : X → OrbitSpace K := FactorCode.encode (joint q)

omit [StandardBorelSpace Y] [Nonempty Y] in
lemma joint_measurable (q : ℕ → X → Y) (hq : ∀ n, Measurable (q n)) : Measurable (joint q) :=
  Measurable.of_eval hq

omit [Nonempty Y] [MulAction K Y] [MeasurableConstSMul K Y] in
lemma code_measurable (q : ℕ → X → Y) (hq : ∀ n, Measurable (q n)) : Measurable (code (K := K) q) :=
  FactorCode.encode_measurable (joint_measurable q hq)

omit [Countable K] [MeasurableSpace X] [Nonempty Y] [MulAction K Y] [MeasurableConstSMul K X] [MeasurableConstSMul K Y] in
lemma code_equivariant (q : ℕ → X → Y) (k : K) (x : X) :
    code (K := K) q (k • x) = k • code q x := FactorCode.encode_equivariant _ _ _

omit [MulAction K Y] [MeasurableConstSMul K X] [MeasurableConstSMul K Y] in
lemma le_code (μ : Measure X) (q : ℕ → X → Y) (n : ℕ) :
    FactorLp.space μ (q n) ≤ FactorLp.space μ (code (K := K) q) := by
  apply FactorLp.le_of_factor μ (q n) (code q)
    (fun z => (FactorCode.decode (K := K) (Y := ℕ → Y) z) n)
    ((measurable_pi_apply n).comp FactorCode.decode_measurable)
  exact Filter.Eventually.of_forall fun x => by
    dsimp only [Function.comp_apply, code]
    rw [FactorCode.decode_encode]
    rfl

omit [Countable K] [MeasurableSpace Y] [MeasurableConstSMul K X] [MeasurableConstSMul K Y] [Nonempty Y] [StandardBorelSpace Y] in
lemma joint_equivariant (μ : Measure X) (q : ℕ → X → Y)
    (hqe : ∀ n (k : K), ∀ᵐ x ∂μ, q n (k • x) = k • q n x) (k : K) :
    ∀ᵐ x ∂μ, joint q (k • x) = k • joint q x := by
  filter_upwards [ae_all_iff.mpr (fun n => hqe n k)] with x hx
  exact funext hx

omit [StandardBorelSpace Y] [Nonempty Y] in
lemma finite_upper (μ : Measure X) (q : ℕ → X → Y)
    (hc : ∀ i j, FactorLp.space μ (q i) ≤ FactorLp.space μ (q j) ∨
      FactorLp.space μ (q j) ≤ FactorLp.space μ (q i)) (n : ℕ) :
    ∃ j, ∀ i < n, FactorLp.space μ (q i) ≤ FactorLp.space μ (q j) := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨j, hj⟩ := ih
    obtain hij | hji := hc j n
    · refine ⟨n, fun i hi => ?_⟩
      obtain hi | rfl := Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi)
      · exact (hj i hi).trans hij
      · exact le_rfl
    · refine ⟨j, fun i hi => ?_⟩
      obtain hi | rfl := Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi)
      · exact hj i hi
      · exact hji

omit [MeasurableConstSMul K X] in
lemma approximation (μ : Measure X) [IsProbabilityMeasure μ]
    (q : ℕ → X → Y) (hq : ∀ n, Measurable (q n))
    (hqe : ∀ n (k : K), ∀ᵐ x ∂μ, q n (k • x) = k • q n x)
    (hc : ∀ i j, FactorLp.space μ (q i) ≤ FactorLp.space μ (q j) ∨
      FactorLp.space μ (q j) ≤ FactorLp.space μ (q i))
    (m : ℕ) (H : OrbitSpace K → Fin m → ℂ) (hH : Measurable H)
    (hB : ∃ C : ℝ, ∀ z, ‖H z‖ ≤ C) (ε : ℝ) (hε : 0 < ε) :
    ∃ j, ∃ H₀ : Y → Fin m → ℂ, Measurable H₀ ∧ (∃ C : ℝ, ∀ y, ‖H₀ y‖ ≤ C) ∧
      Integrable (fun x => dist (H (code q x)) (H₀ (q j x))^2) μ ∧
      (∫ x, dist (H (code q x)) (H₀ (q j x))^2 ∂μ) < ε^2 := by
  classical
  obtain ⟨C, hC⟩ := hB
  let C' := max C 0
  have hC' : 0 ≤ C' := le_max_right _ _
  let J := joint q
  have hJ := joint_measurable q hq
  let E : (ℕ → Y) → OrbitSpace K := FactorCode.encode id
  have hE : Measurable E := FactorCode.encode_measurable measurable_id
  haveI := Measure.isProbabilityMeasure_map (μ := μ) hJ.aemeasurable
  obtain ⟨n, Hn, hHn, hHnB, hi, he⟩ := CountableApprox.bounded_approximation (μ.map J)
    m (H ∘ E) (hH.comp hE) C' hC' (fun y => (hC _).trans (le_max_left _ _)) ε hε
  obtain ⟨j, hj⟩ := finite_upper μ q hc n
  have hfac (i : Fin n) : ∃ r : Y → Y, Measurable r ∧ q i =ᵐ[μ] r ∘ q j :=
    FactorLp.factor_of_le μ (q i) (q j) (hq i) (hj i i.isLt)
  choose r hr hre using hfac
  let R : Y → Fin n → Y := fun y i => r i y
  have hR : Measurable R := Measurable.of_eval hr
  have hEq := FactorCode.encode_as_comp (K := K) μ J (joint_equivariant μ q hqe)
  have hEq' : (fun x => dist ((H ∘ E) (J x)) (Hn (CountableApprox.truncate n (J x)))^2) =ᵐ[μ]
      (fun x => dist (H (code q x)) ((Hn ∘ R) (q j x))^2) := by
    filter_upwards [hEq, ae_all_iff.mpr hre] with x hx hxr
    have hp : CountableApprox.truncate n (J x) = R (q j x) := funext hxr
    change dist (H (E (J x))) _ ^ 2 = _
    change code (K := K) q x = E (J x) at hx
    rw [← hx, hp]
    rfl
  refine ⟨j, Hn ∘ R, hHn.comp hR, ⟨2*C', fun y => hHnB _⟩, ?_, ?_⟩
  · exact (hi.comp_measurable hJ).congr hEq'
  · rw [← integral_congr_ae hEq', ← integral_map hJ.aemeasurable hi.aestronglyMeasurable]
    exact he

end EuclideanFiveColor.ChainJoin
namespace EuclideanFiveColor.SeparableZorn
open TopologicalSpace
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [SecondCountableTopology E]

lemma countable_cover (S : Set (Submodule ℂ E)) (hS : S.Nonempty) :
    ∃ p : ℕ → S, ∀ V : Submodule ℂ E, IsClosed (V : Set E) →
      (∀ n, (p n).val ≤ V) → ∀ U ∈ S, U ≤ V := by
  classical
  let D : Set E := {x | ∃ U ∈ S, x ∈ U}
  have : Nonempty D := by
    obtain ⟨U, hU⟩ := hS
    exact ⟨⟨0, U, hU, U.zero_mem⟩⟩
  obtain ⟨u, hu⟩ := exists_dense_seq D
  have hU (n : ℕ) : ∃ U : S, (u n).val ∈ U.val := by
    obtain ⟨U, hU, hx⟩ := (u n).property
    exact ⟨⟨U, hU⟩, hx⟩
  choose p hp using hU
  refine ⟨p, ?_⟩
  intro V hc hV U hUS x hx
  have hcl : IsClosed ((Subtype.val : D → E) ⁻¹' (V : Set E)) := hc.preimage continuous_subtype_val
  have hsub : Set.range u ⊆ (Subtype.val : D → E) ⁻¹' (V : Set E) := by
    rintro _ ⟨n, rfl⟩
    exact hV n (hp n)
  have hwhole := closure_minimal hsub hcl
  rw [hu.closure_range] at hwhole
  exact hwhole (Set.mem_univ (⟨x, U, hUS, hx⟩ : D))

lemma exists_maximal {A : Type*} [Preorder A] [Nonempty A]
    (F : A → Submodule ℂ E) (hF : ∀ a, IsClosed (F a : Set E))
    (hord : ∀ a b, a ≤ b ↔ F a ≤ F b)
    (hseq : ∀ p : ℕ → A, (∀ i j, p i ≤ p j ∨ p j ≤ p i) →
      ∃ a, ∀ i, p i ≤ a) : ∃ a : A, IsMax a := by
  classical
  apply zorn_le_nonempty
  intro c hc hne
  obtain ⟨p, hp⟩ := countable_cover (F '' c) (hne.image F)
  have hrep (n : ℕ) : ∃ a : c, F a = (p n).val := by
    obtain ⟨a, ha, he⟩ := (p n).property
    exact ⟨⟨a, ha⟩, he⟩
  choose a ha using hrep
  have haorder (i j : ℕ) : (a i).val ≤ (a j).val ∨ (a j).val ≤ (a i).val :=
    hc.total (a i).property (a j).property
  obtain ⟨b, hb⟩ := hseq (fun n => (a n).val) haorder
  refine ⟨b, ?_⟩
  intro d hd
  apply (hord d b).mpr
  exact hp (F b) (hF b) (fun n => by rw [← ha n]; exact (hord _ _).mp (hb n))
    (F d) ⟨d, hd, rfl⟩

end EuclideanFiveColor.SeparableZorn
namespace EuclideanFiveColor.CodedMax
open MeasureTheory
variable {K X : Type*} [Group K] [Countable K] [MeasurableSpace X]
  [MulAction K X] [MeasurableConstSMul K X]

private structure Model (μ : Measure X) (Good : (X → OrbitSpace K) → Prop) where
  map : X → OrbitSpace K
  measurable : Measurable map
  equivariant : ∀ k : K, ∀ᵐ x ∂μ, map (k • x) = k • map x
  good : Good map

private instance (μ : Measure X) (Good : (X → OrbitSpace K) → Prop) : Preorder (Model μ Good) where
  le a b := FactorLp.space μ a.map ≤ FactorLp.space μ b.map
  le_refl _ := le_rfl
  le_trans _ _ _ := le_trans

lemma exists_maximal (μ : Measure X) [IsProbabilityMeasure μ] [StandardBorelSpace X]
    (Good : (X → OrbitSpace K) → Prop) (hbase : Nonempty (Model μ Good))
    (hjoin : ∀ q : ℕ → X → OrbitSpace K, (∀ n, Measurable (q n)) →
      (∀ n (k : K), ∀ᵐ x ∂μ, q n (k • x) = k • q n x) → (∀ n, Good (q n)) →
      (∀ i j, FactorLp.space μ (q i) ≤ FactorLp.space μ (q j) ∨
        FactorLp.space μ (q j) ≤ FactorLp.space μ (q i)) → Good (ChainJoin.code q)) :
    ∃ a : Model μ Good, IsMax a := by
  have := hbase
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  apply SeparableZorn.exists_maximal (fun a : Model μ Good => FactorLp.space μ a.map)
    (fun a => FactorLp.isClosed μ a.measurable) (fun _ _ => Iff.rfl)
  intro p hc
  let q := fun n => (p n).map
  have hq (n : ℕ) := (p n).measurable
  have hqe (n : ℕ) := (p n).equivariant
  have hcg : Good (ChainJoin.code q) := hjoin q hq hqe (fun n => (p n).good) hc
  let a : Model μ Good := ⟨ChainJoin.code q, ChainJoin.code_measurable q hq,
    fun k => Filter.Eventually.of_forall (ChainJoin.code_equivariant q k), hcg⟩
  exact ⟨a, fun n => ChainJoin.le_code μ q n⟩

end EuclideanFiveColor.CodedMax

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

variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
  [MulAction K X] [MeasurableConstSMul K X]

theorem exists_terminal_factor (μ : Measure X) [IsProbabilityMeasure μ] [ErgodicSMul K X μ] :
    ∃ p : X → OrbitSpace K, ∃ hp : Measurable p,
      (∀ k : K, ∀ᵐ x ∂μ, p (k • x) = k • p x) ∧ UniversalGood μ p ∧
      ErgodicSMul K (X × X) (RelativeProduct.law μ p hp) := by
  classical
  let z₀ : OrbitSpace K := ⟨fun _ => 0⟩
  have hbase : Nonempty (CodedMax.Model (K := K) μ (UniversalGood μ)) := by
    refine ⟨⟨fun _ => z₀, measurable_const, ?_, ?_⟩⟩
    · intro k
      exact Filter.Eventually.of_forall fun x => by apply OrbitSpace.ext; intro l; rfl
    · intro d hd _hw hw
      exact relative_singularity_base μ d hd z₀ hw
  have hjoin : ∀ q : ℕ → X → OrbitSpace K, (∀ n, Measurable (q n)) →
      (∀ n (k : K), ∀ᵐ x ∂μ, q n (k • x) = k • q n x) →
      (∀ n, UniversalGood μ (q n)) →
      (∀ i j, FactorLp.space μ (q i) ≤ FactorLp.space μ (q j) ∨
        FactorLp.space μ (q j) ≤ FactorLp.space μ (q i)) → UniversalGood μ (ChainJoin.code (K := K) q) := by
    intro q hq hqe hg hc d hd hde hw
    apply relative_singularity_approximation (W := OrbitSpace K) μ d (ChainJoin.code (K := K) q) hd
      (ChainJoin.code_measurable q hq) hde
      (fun k => Filter.Eventually.of_forall (ChainJoin.code_equivariant q k)) hw
    intro m H hH hB ε hε
    obtain ⟨j, H₀, hH₀, hB₀, hi, he⟩ := ChainJoin.approximation μ q hq hqe hc m H hH hB ε hε
    exact ⟨q j, hq j, hqe j, hg j, H₀, hH₀, hB₀, hi, he⟩
  obtain ⟨a, hamax⟩ := CodedMax.exists_maximal (K := K) μ (UniversalGood μ) hbase hjoin
  refine ⟨a.map, a.measurable, a.equivariant, a.good, ?_⟩
  by_contra hn
  obtain ⟨H, hH, hB, hnot, hc⟩ := CompactTower.strict_compact_successor μ a.map
    a.measurable a.equivariant hn
  let u := OrbitFactor.extend (K := K) a.map H
  have hum : Measurable u := OrbitFactor.measurable_extend a.measurable hH
  have hue (k : K) : ∀ᵐ x ∂μ, u (k • x) = k • u x :=
    OrbitFactor.extend_equivariant μ H a.equivariant k
  have hug : UniversalGood μ u := by
    intro d hd hde hw
    apply relative_singularity_successor μ d u Prod.fst hd hum measurable_fst hde hue
      (fun k => Filter.Eventually.of_forall fun y => rfl) hw hc
    exact a.good
  let v := FactorCode.encode (K := K) u
  have hvm : Measurable v := FactorCode.encode_measurable hum
  have hve (k : K) : ∀ᵐ x ∂μ, v (k • x) = k • v x :=
    Filter.Eventually.of_forall (FactorCode.encode_equivariant u k)
  have hvg : UniversalGood μ v := universalGood_of_factor μ v u
    (FactorCode.encode (K := K) (id : OrbitSpace K × OrbitSpace K → _)) hvm hum
    (FactorCode.encode_measurable measurable_id) hve hue (FactorCode.encode_as_comp μ u hue) hug
  let b : CodedMax.Model (K := K) μ (UniversalGood μ) := ⟨v, hvm, hve, hvg⟩
  have hab : a ≤ b := by
    apply FactorLp.le_of_factor μ a.map v
      (Prod.fst ∘ FactorCode.decode (K := K) (Y := OrbitSpace K × OrbitSpace K))
      (measurable_fst.comp FactorCode.decode_measurable)
    exact Filter.Eventually.of_forall fun x => by
      dsimp only [Function.comp_apply, v]
      rw [FactorCode.decode_encode]
      rfl
  have hba : FactorLp.space μ v ≤ FactorLp.space μ a.map := hamax hab
  have hHlp : MemLp H 2 μ := MemLp.of_bound hH.aestronglyMeasurable 2
    (Filter.Eventually.of_forall hB)
  let J : OrbitSpace K → ℂ := fun z => (FactorCode.decode
    (K := K) (Y := OrbitSpace K × OrbitSpace K) z).2.val 1
  have hJ : Measurable J := (measurable_pi_apply 1).comp
    (OrbitSpace.measurable_val.comp (measurable_snd.comp FactorCode.decode_measurable))
  have hHv : hHlp.toLp H ∈ FactorLp.space μ v := by
    apply FactorLp.mem_of_rep μ v _ J hJ
    filter_upwards [hHlp.coeFn_toLp] with x hx
    rw [hx]
    dsimp only [Function.comp_apply, J, v]
    rw [FactorCode.decode_encode]
    exact (OrbitFactor.orbit_one H x).symm
  obtain ⟨g, hg, hhe⟩ := FactorLp.exists_rep μ a.map _ (hba hHv)
  exact hnot ⟨g, hg, hHlp.coeFn_toLp.symm.trans hhe⟩

end PlaneFiveColor.Spectral

end

end ParishFactor
end
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open ParishFactor.EuclideanFiveColor ParishFactor.PlaneFiveColor.Spectral

private theorem terminal_existence [Carrier] (μ : Measure D) [IsProbabilityMeasure μ]
    [ErgodicSMul K D μ] (hw : IsWild μ) :
    ∃ (q : D → OrbitSpace K) (hq : Measurable q),
      (∀ k : K, ∀ᵐ x ∂μ, q (k • x) = k • q x) ∧
      ErgodicSMul K (D×D) (RelativeProduct.law μ q hq) ∧
      IsWild (DifferenceFourier.differenceLaw (μ.map q) (condDistrib id q μ)) := by
  obtain ⟨q,hq,hqc,hgood,hmix⟩ := exists_terminal_factor μ
  exact ⟨q,hq,hqc,hmix,
    fun k => relative_difference_invariant μ id q measurable_id hq (fun _ => Eventually.of_forall fun _ => rfl) hqc k,
    hgood id measurable_id (fun _ => Eventually.of_forall fun _ => rfl) (by simpa using hw)⟩
end


noncomputable section
open MeasureTheory ProbabilityTheory Filter
open ParishFactor.EuclideanFiveColor ParishFactor.PlaneFiveColor.Spectral

private theorem bridge (E : IntermediateField ℚ ℂ) (F : IntermediateField ℚ ℝ) (hc : Countable E)
    (hF : ∀ z : ℂ, z ∈ E ↔ z.re ∈ F ∧ z.im ∈ F)
    (ha : ∀ p : Polynomial ℂ, p ≠ 0 → (∀ n, p.coeff n ∈ E) → ∀ z, p.eval z = 0 → z ∈ E)
    (ht : ∀ Q : Finset ℂ, (∀ q ∈ Q, q ∈ E ∧ ‖q‖ = 1) →
      ∃ S : Finset ℂ, (∀ s ∈ S, s ∈ E ∧ ‖s‖ = 1) ∧
      ∀ j : ℂ → ℂ, (∀ s ∈ S, j s ∈ Q) →
        (1 : ℂ) ∈ Submodule.span ℚ ((fun s => j s*s) '' (S : Set ℂ)) ∧
        Complex.I ∈ Submodule.span ℚ ((fun s => j s*s) '' (S : Set ℂ))) :
    letI : Carrier := ⟨E,F,hc,hF,ha,ht⟩
    ∀ (μ : Measure D) [IsProbabilityMeasure μ] [ErgodicSMul K D μ], IsWild μ →
      ∃ (Y : Type) (mY : MeasurableSpace Y) (aY : MulAction K Y),
        letI := mY
        letI := aY
        StandardBorelSpace Y ∧ Nonempty Y ∧ MeasurableConstSMul K Y ∧ ∃ (q : D → Y) (hq : Measurable q),
        (∀ k : K, ∀ᵐ x ∂μ, q (k • x) = k • q x) ∧
        ErgodicSMul K (D×D) (RelativeProduct.law μ q hq) ∧
        IsWild (DifferenceFourier.differenceLaw (μ.map q) (condDistrib id q μ)) := by
  letI : Carrier := ⟨E,F,hc,hF,ha,ht⟩
  intro μ _ _ hw
  obtain ⟨q,hq,hcov,hsq,hd⟩ := terminal_existence μ hw
  exact ⟨OrbitSpace K,inferInstance,inferInstance,inferInstance,inferInstance,inferInstance,q,hq,hcov,hsq,hd⟩

theorem OMA.solution : OMA.R_Erdos173_erdos_173_R1_H2_R1_H1_R1_H2_R1_H1_R1_H2_R1.H1 := by
  intro E F hc hF ha ht
  exact bridge E F hc hF ha ht
end
