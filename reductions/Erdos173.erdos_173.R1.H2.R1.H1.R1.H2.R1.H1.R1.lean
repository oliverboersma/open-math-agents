import OMAReductions.R_Erdos173_erdos_173_R1_H2_R1_H1_R1_H2_R1

/-! A stationary triangle-sign model and its discrete spectral law.
Port of Jacob Parish, plasma-ai/erdos-173@4a368a652753, and OpenAI,
openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a, both Apache-2.0.
Includes modified portions of their invariant-mean, joint spectral calculus,
rotation-invariance, and ordinary-character projection arguments. -/


-- OAI.Analysis.PlaneSpectrum.Carrier
section
noncomputable section

namespace ParishLaw.PlaneFiveColor.Spectral

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
end ParishLaw.PlaneFiveColor.Spectral
end
end

-- OAI.Analysis.PlaneSpectrum.Basic
section
namespace ParishLaw

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
end ParishLaw
end

-- OAI.Analysis.PlaneSpectrum.InvariantMean
section
namespace ParishLaw

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
end PlaneFiveColor.InvariantMean
end
end
end
end ParishLaw
end

-- OAI.MeasureTheory.CompactFactors.Stationary
section
namespace ParishLaw

noncomputable section

section
open MeasureTheory
open scoped BoundedContinuousFunction
open PlaneFiveColor.InvariantMean
namespace EuclideanFiveColor.StationaryMean
variable {A B X : Type*} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
  [TopologicalSpace X] [CompactSpace X]
  (t : A → X → X) (r : B → X → X) (x₀ : X)
private def inner (f : C(X,ℝ)) (b : B) : A →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun a => f (r b (t a x₀)))
    continuous_of_discreteTopology ‖f‖ (fun _ => f.norm_coe_le_norm _)
omit [AddCommGroup A] [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B] in
lemma inner_norm (f : C(X,ℝ)) (b : B) : ‖inner t r x₀ f b‖ ≤ ‖f‖ :=
  (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr fun _ => f.norm_coe_le_norm _
private def outer (f : C(X,ℝ)) : B →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun b => mean (inner t r x₀ f b))
    continuous_of_discreteTopology ‖f‖ (fun b => (mean_norm_le _).trans (inner_norm t r x₀ f b))
private def average (f : C(X,ℝ)) : ℝ := mean (outer t r x₀ f)
omit [AddCommGroup A] [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B] in
lemma inner_add (f g : C(X,ℝ)) (b : B) : inner t r x₀ (f+g) b = inner t r x₀ f b + inner t r x₀ g b := by ext; rfl
omit [AddCommGroup A] [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B] in
lemma inner_smul (c : ℝ) (f : C(X,ℝ)) (b : B) : inner t r x₀ (c • f) b = c • inner t r x₀ f b := by ext; rfl
omit [AddCommGroup B] in
lemma outer_add (f g : C(X,ℝ)) : outer t r x₀ (f+g) = outer t r x₀ f + outer t r x₀ g := by
  ext b
  exact (congrArg mean (inner_add t r x₀ f g b)).trans (mean_add _ _)
omit [AddCommGroup B] in
lemma outer_smul (c : ℝ) (f : C(X,ℝ)) : outer t r x₀ (c • f) = c • outer t r x₀ f := by
  ext b
  exact (congrArg mean (inner_smul t r x₀ c f b)).trans (mean_smul _ _)
lemma average_add (f g : C(X,ℝ)) : average t r x₀ (f+g) = average t r x₀ f + average t r x₀ g := by
  simp only [average,outer_add,mean_add]
lemma average_smul (c : ℝ) (f : C(X,ℝ)) : average t r x₀ (c • f) = c * average t r x₀ f := by
  simp only [average,outer_smul,mean_smul]
lemma average_mono {f g : C(X,ℝ)} (h : f ≤ g) : average t r x₀ f ≤ average t r x₀ g := by
  have hp : 0 ≤ average t r x₀ (g-f) := mean_nonneg _ fun b => mean_nonneg _ fun a => sub_nonneg.mpr (h _)
  have he : average t r x₀ (g-f) = average t r x₀ g - average t r x₀ f := by
    rw [sub_eq_add_neg,average_add,← neg_one_smul ℝ f,average_smul]; ring
  linarith
lemma average_const (c : ℝ) : average t r x₀ (ContinuousMap.const X c) = c := by
  have hi (b : B) : inner t r x₀ (ContinuousMap.const X c) b = BoundedContinuousFunction.const A c := by ext; rfl
  have ho : outer t r x₀ (ContinuousMap.const X c) = BoundedContinuousFunction.const B c := by
    ext b
    change mean (inner t r x₀ _ b) = c
    rw [hi,mean_const]
  rw [average,ho,mean_const]
lemma average_translation (ht : ∀ a b x, t a (t b x) = t (a+b) x)
    (φ : B → A → A) (hc : ∀ a b x, t a (r b x) = r b (t (φ b a) x))
    (a : A) (f : C(X,ℝ)) (ha : Continuous (t a)) :
    average t r x₀ (f.comp ⟨t a,ha⟩) = average t r x₀ f := by
  unfold average
  congr 1
  ext b
  change mean (inner t r x₀ (f.comp _) b) = mean (inner t r x₀ f b)
  have he : inner t r x₀ (f.comp ⟨t a,ha⟩) b = shift (φ b a) (inner t r x₀ f b) := by
    ext z
    change f (t a (r b (t z x₀))) = f (r b (t (z+φ b a) x₀))
    rw [hc,ht,add_comm]
  rw [he,mean_shift]
lemma average_rotation (hr : ∀ a b x, r a (r b x) = r (a+b) x)
    (b : B) (f : C(X,ℝ)) (hb : Continuous (r b)) :
    average t r x₀ (f.comp ⟨r b,hb⟩) = average t r x₀ f := by
  unfold average
  have he : outer t r x₀ (f.comp ⟨r b,hb⟩) = shift b (outer t r x₀ f) := by
    ext c
    change mean (inner t r x₀ (f.comp _) c) = mean (inner t r x₀ f (c+b))
    congr 1
    ext z
    change f (r b (r c (t z x₀))) = f (r (c+b) (t z x₀))
    rw [hr,add_comm]
  rw [he,mean_shift]
variable [T2Space X] [MeasurableSpace X] [BorelSpace X]
private def functional : CompactlySupportedContinuousMap X ℝ →ₚ[ℝ] ℝ where
  toFun f := average t r x₀ f.toContinuousMap
  map_add' := fun f g => average_add t r x₀ f.toContinuousMap g.toContinuousMap
  map_smul' := fun c f => average_smul t r x₀ c f.toContinuousMap
  monotone' := fun _ _ h => average_mono t r x₀ h
private def measure : Measure X := RealRMK.rieszMeasure (functional t r x₀)
private instance : IsFiniteMeasure (measure t r x₀) := by dsimp [measure]; infer_instance
private instance : (measure t r x₀).Regular := by dsimp [measure]; infer_instance
lemma integral (f : C(X,ℝ)) : ∫ x, f x ∂measure t r x₀ = average t r x₀ f :=
  RealRMK.integral_rieszMeasure (functional t r x₀) (CompactlySupportedContinuousMap.continuousMapEquiv f)
private instance : IsProbabilityMeasure (measure t r x₀) := by
  have he := integral t r x₀ (ContinuousMap.const X 1)
  rw [average_const] at he
  change (∫ _ : X, (1:ℝ) ∂measure t r x₀) = 1 at he
  simp only [integral_const,smul_eq_mul,mul_one] at he
  constructor
  exact (ENNReal.toReal_eq_one_iff _).mp he
lemma preserving_of_average (s : X ≃ₜ X)
    (hav : ∀ f : C(X,ℝ), average t r x₀ (f.comp ⟨s,s.continuous⟩) = average t r x₀ f) :
    MeasurePreserving s (measure t r x₀) (measure t r x₀) := by
  refine ⟨s.continuous.measurable,?_⟩
  have : (Measure.map s (measure t r x₀)).Regular := Measure.Regular.map s
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  change (∫ x, f.toContinuousMap x ∂(measure t r x₀).map s) = ∫ x, f.toContinuousMap x ∂measure t r x₀
  rw [integral_map s.continuous.measurable.aemeasurable f.continuous.measurable.aestronglyMeasurable]
  exact (integral t r x₀ (f.toContinuousMap.comp ⟨s,s.continuous⟩)).trans ((hav f.toContinuousMap).trans (integral t r x₀ f.toContinuousMap).symm)
end EuclideanFiveColor.StationaryMean
end
end
end ParishLaw
end

-- OAI.Analysis.PlaneSpectrum.Representations
section
namespace ParishLaw

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
end PlaneFiveColor.Spectral
end

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace EuclideanFiveColor.Koopman
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
private def isometry (s : X ≃ᵐ X) (hs : MeasurePreserving s μ μ) : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ where
  __ := Lp.compMeasurePreservingₗᵢ ℂ s hs
  invFun := Lp.compMeasurePreserving s.symm (hs.symm s)
  left_inv v := by
    change Lp.compMeasurePreserving s.symm (hs.symm s) (Lp.compMeasurePreserving s hs v) = v
    rw [← Lp.compMeasurePreserving_comp_apply]
    have he : (s : X → X) ∘ s.symm = id := funext s.apply_symm_apply
    simp only [he,Lp.compMeasurePreserving_id_apply]
  right_inv v := by
    change Lp.compMeasurePreserving s hs (Lp.compMeasurePreserving s.symm (hs.symm s) v) = v
    rw [← Lp.compMeasurePreserving_comp_apply]
    have he : (s.symm : X → X) ∘ s = id := funext s.symm_apply_apply
    simp only [he,Lp.compMeasurePreserving_id_apply]
private def unitary (s : X ≃ᵐ X) (hs : MeasurePreserving s μ μ) : unitary (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :=
  Unitary.linearIsometryEquiv.symm (isometry μ s hs)
lemma unitary_apply (s : X ≃ᵐ X) (hs : MeasurePreserving s μ μ) (v : Lp ℂ 2 μ) :
    (unitary μ s hs : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) v = Lp.compMeasurePreserving s hs v := rfl
end EuclideanFiveColor.Koopman
end
noncomputable section
open Filter Topology
namespace EuclideanFiveColor.ContinuousVectors
variable {A H : Type*} [AddCommGroup A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative A →* unitary (H →L[ℂ] H))
private def op (a : A) : H →L[ℂ] H := U (Multiplicative.ofAdd a)
@[simp] lemma op_zero (v : H) : op U 0 v = v := by simp [op]
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

end ParishLaw
end

-- OAI.Analysis.PlaneSpectrum.SpectralMeasure
section
namespace ParishLaw

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

end ParishLaw
end

-- Erdos173.Basic
section
noncomputable section

namespace ParishPlane

open MeasureTheory

private def ζ : ℂ := ⟨1 / 2, √3 / 2⟩

lemma norm_ζ : ‖ζ‖ = 1 := by
  rw [Complex.norm_def, Real.sqrt_eq_one]
  simp [ζ, Complex.normSq]
  ring_nf
  norm_num

lemma norm_one_sub_ζ : ‖1 - ζ‖ = 1 := by
  rw [Complex.norm_def, Real.sqrt_eq_one]
  simp [ζ, Complex.normSq]
  ring_nf
  norm_num

lemma norm_ζ_sub_one : ‖ζ - 1‖ = 1 := by
  rw [norm_sub_rev, norm_one_sub_ζ]
end ParishPlane
end
end

-- Erdos173.Transfer.LabelModel
section
noncomputable section

namespace ParishPlane.Transfer

open MeasureTheory
open ParishLaw ParishLaw.PlaneFiveColor.Spectral ParishLaw.EuclideanFiveColor ParishLaw.EuclideanFiveColor.ContinuousVectors
open scoped InnerProductSpace

variable [Carrier]

lemma sqrt_three_mem : ((√3 : ℝ) : ℂ) ∈ E :=
  Carrier.ofReal_mem (Carrier.sqrt_mem (by simp))

lemma exists_kCoeff_eq (z : E) (hz : ‖(z : ℂ)‖ = 1) : ∃ b : K, kCoeff b = z :=
  ⟨⟨⟨z, mem_sphere_zero_iff_norm.mpr hz⟩, z.property⟩, rfl⟩

@[simp] lemma coe_kCoeff (u : K) : ((kCoeff u : E) : ℂ) = (u.val : ℂ) := rfl

omit [Carrier] in

lemma ζ_eq : ζ = (1 + ((√3 : ℝ) : ℂ) * Complex.I) / 2 := by
  apply Complex.ext <;> simp [ζ]

lemma ζ_mem : ζ ∈ E := by
  rw [ζ_eq]
  have h₂ : (2 : ℂ) ∈ E := by simp
  exact E.div_mem (E.add_mem E.one_mem (E.mul_mem sqrt_three_mem imagUnit.property)) h₂

private def ζE : E := ⟨ζ, ζ_mem⟩

@[simp] lemma coe_ζE : (ζE : ℂ) = ζ := rfl

private def AvoidsSide (r : E) (η : E → Fin 2) : Prop :=
  ∀ p : E, ∀ u : K, ¬ (η (p + kCoeff u * r) = η p ∧ η (p + kCoeff u * (r * ζE)) = η p)

variable (R : Set E)

private def Admissible (η : E → Fin 2) : Prop := ∀ r ∈ R, AvoidsSide r η

private abbrev Space := {η : E → Fin 2 // Admissible R η}

theorem isClosed_admissible : IsClosed {η : E → Fin 2 | Admissible R η} := by
  unfold Admissible AvoidsSide
  simp only [Set.ofPred_forall]
  refine isClosed_iInter fun r => isClosed_iInter fun _ => isClosed_iInter fun p =>
    isClosed_iInter fun u => ?_
  have hc : Continuous (fun η : E → Fin 2 =>
      (η p, η (p + kCoeff u * r), η (p + kCoeff u * (r * ζE)))) :=
    (continuous_apply p).prodMk ((continuous_apply _).prodMk (continuous_apply _))
  exact (isClosed_discrete {q : Fin 2 × Fin 2 × Fin 2 | ¬ (q.2.1 = q.1 ∧ q.2.2 = q.1)}).preimage hc

private instance : CompactSpace (Space R) := isCompact_iff_compactSpace.mp (isClosed_admissible R).isCompact

private def trans (a : E) (ω : Space R) : Space R := ⟨fun x => ω.val (x + a), by
  intro r hr p u h
  refine ω.property r hr (p + a) u ?_
  rwa [add_right_comm p a, add_right_comm p a]⟩

private def rotate (b : K) (ω : Space R) : Space R := ⟨fun x => ω.val (kCoeff b * x), by
  intro r hr p u h
  refine ω.property r hr (kCoeff b * p) (b * u) ?_
  simpa only [kCoeff_mul, mul_add, mul_assoc] using h⟩

@[simp] lemma trans_apply (a : E) (ω : Space R) (x : E) : (trans R a ω).val x = ω.val (x + a) :=
  rfl

@[simp] lemma rotate_apply (b : K) (ω : Space R) (x : E) :
    (rotate R b ω).val x = ω.val (kCoeff b * x) := rfl

lemma continuous_trans (a : E) : Continuous (trans R a) := by
  apply Continuous.subtype_mk
  exact continuous_pi fun x => (continuous_apply (x + a)).comp continuous_subtype_val

lemma continuous_rotate (b : K) : Continuous (rotate R b) := by
  apply Continuous.subtype_mk
  exact continuous_pi fun x => (continuous_apply (kCoeff b * x)).comp continuous_subtype_val

@[simp] lemma trans_zero (ω : Space R) : trans R 0 ω = ω := by
  apply Subtype.ext
  funext x
  simp

lemma trans_add (a b : E) (ω : Space R) : trans R a (trans R b ω) = trans R (a + b) ω := by
  apply Subtype.ext
  funext x
  simp [add_assoc]

@[simp] lemma rotate_one (ω : Space R) : rotate R 1 ω = ω := by
  apply Subtype.ext
  funext x
  simp

lemma rotate_mul (a b : K) (ω : Space R) : rotate R a (rotate R b ω) = rotate R (a * b) ω := by
  apply Subtype.ext
  funext x
  change ω.val (kCoeff b * (kCoeff a * x)) = ω.val (kCoeff (a * b) * x)
  rw [kCoeff_mul]
  ring_nf

lemma covariance (a : E) (b : K) (ω : Space R) :
    trans R a (rotate R b ω) = rotate R b (trans R (kCoeff b * a) ω) := by
  apply Subtype.ext
  funext x
  simp only [trans_apply, rotate_apply, mul_add]

private def transHomeo (a : E) : Space R ≃ₜ Space R where
  toFun := trans R a
  invFun := trans R (-a)
  left_inv ω := by rw [trans_add, neg_add_cancel, trans_zero]
  right_inv ω := by rw [trans_add, add_neg_cancel, trans_zero]
  continuous_toFun := continuous_trans R a
  continuous_invFun := continuous_trans R (-a)

private def rotateHomeo (b : K) : Space R ≃ₜ Space R where
  toFun := rotate R b
  invFun := rotate R b⁻¹
  left_inv ω := by rw [rotate_mul, inv_mul_cancel, rotate_one]
  right_inv ω := by rw [rotate_mul, mul_inv_cancel, rotate_one]
  continuous_toFun := continuous_rotate R b
  continuous_invFun := continuous_rotate R b⁻¹

private abbrev Trans := Additive DiscreteE

private def tr (a : Trans) : Space R → Space R := trans R (Multiplicative.toAdd (Additive.toMul a))

private def ro (b : Rot) : Space R → Space R := rotate R (rotMul b)

private def measure (ω₀ : Space R) : Measure (Space R) := StationaryMean.measure (tr R) (ro R) ω₀

private instance (ω₀ : Space R) : IsProbabilityMeasure (measure R ω₀) :=
  inferInstanceAs (IsProbabilityMeasure (StationaryMean.measure (tr R) (ro R) ω₀))

lemma trans_preserving (ω₀ : Space R) (a : E) :
    MeasurePreserving (trans R a) (measure R ω₀) (measure R ω₀) := by
  apply StationaryMean.preserving_of_average (tr R) (ro R) ω₀ (transHomeo R a)
  intro f
  apply StationaryMean.average_translation (tr R) (ro R) ω₀
    (fun a b x => trans_add R _ _ x)
    (fun b a => Additive.ofMul (Multiplicative.ofAdd
      (kCoeff (rotMul b) * Multiplicative.toAdd (Additive.toMul a))))
    (fun a b x => covariance R _ _ x) (Additive.ofMul (Multiplicative.ofAdd a)) f
    (continuous_trans R a)

lemma rotate_preserving (ω₀ : Space R) (b : K) :
    MeasurePreserving (rotate R b) (measure R ω₀) (measure R ω₀) := by
  apply StationaryMean.preserving_of_average (tr R) (ro R) ω₀ (rotateHomeo R b)
  intro f
  exact StationaryMean.average_rotation (tr R) (ro R) ω₀
    (fun a b x => rotate_mul R _ _ x) (mulRot b) f (continuous_rotate R b)

variable (ω₀ : Space R)

private abbrev Hilbert := Lp ℂ 2 (measure R ω₀)

private def translation (a : E) : unitary (Hilbert R ω₀ →L[ℂ] Hilbert R ω₀) :=
  Koopman.unitary (measure R ω₀) (transHomeo R a).toMeasurableEquiv (trans_preserving R ω₀ a)

private def rotation (b : K) : unitary (Hilbert R ω₀ →L[ℂ] Hilbert R ω₀) :=
  Koopman.unitary (measure R ω₀) (rotateHomeo R b).toMeasurableEquiv (rotate_preserving R ω₀ b)

private def representation : DiscreteE →* unitary (Hilbert R ω₀ →L[ℂ] Hilbert R ω₀) where
  toFun a := translation R ω₀ (Multiplicative.toAdd a)
  map_one' := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro v
    change Lp.compMeasurePreserving (trans R 0) (trans_preserving R ω₀ 0) v = v
    have he : trans R 0 = id := funext (trans_zero R)
    simp only [he, Lp.compMeasurePreserving_id_apply]
  map_mul' a b := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro v
    change Lp.compMeasurePreserving
        (trans R (Multiplicative.toAdd a + Multiplicative.toAdd b)) _ v =
      Lp.compMeasurePreserving (trans R (Multiplicative.toAdd a)) _
        (Lp.compMeasurePreserving (trans R (Multiplicative.toAdd b)) _ v)
    rw [← Lp.compMeasurePreserving_comp_apply]
    congr 2
    funext x
    exact (congrArg (fun c => trans R c x) (add_comm _ _)).trans (trans_add R _ _ x).symm

lemma op_apply (a : E) (v : Hilbert R ω₀) : op (representation R ω₀) a v =
    Lp.compMeasurePreserving (trans R a) (trans_preserving R ω₀ a) v := rfl

lemma rotation_apply (b : K) (v : Hilbert R ω₀) :
    (rotation R ω₀ b : Hilbert R ω₀ →L[ℂ] Hilbert R ω₀) v =
      Lp.compMeasurePreserving (rotate R b) (rotate_preserving R ω₀ b) v := rfl

lemma rotation_covariance (b : K) (a : E) (v : Hilbert R ω₀) :
    (rotation R ω₀ b : Hilbert R ω₀ →L[ℂ] Hilbert R ω₀) (op (representation R ω₀) a v) =
      op (representation R ω₀) (kCoeff b * a)
        ((rotation R ω₀ b : Hilbert R ω₀ →L[ℂ] Hilbert R ω₀) v) := by
  simp only [rotation_apply, op_apply, ← Lp.compMeasurePreserving_comp_apply]
  congr 2
  funext x
  exact covariance R a b x

private def sgnAt (z : E) (ω : Space R) : ℝ := if ω.val z = 0 then 1 else -1

lemma continuous_sgnAt (z : E) : Continuous (sgnAt R z) :=
  (continuous_of_discreteTopology (f := fun c : Fin 2 => if c = 0 then (1 : ℝ) else -1)).comp
    ((continuous_apply z).comp continuous_subtype_val)

private def corr (z : E) : ℝ := ∫ ω, sgnAt R 0 ω * sgnAt R z ω ∂measure R ω₀

lemma memLp_sign : MemLp (fun ω => (sgnAt R 0 ω : ℂ)) 2 (measure R ω₀) := by
  refine MemLp.of_bound ?_ 1 ?_
  · exact (Complex.continuous_ofReal.comp (continuous_sgnAt R 0)).aestronglyMeasurable
  · exact .of_forall fun ω => by dsimp [sgnAt]; split_ifs <;> simp

private def signVector : Hilbert R ω₀ := (memLp_sign R ω₀).toLp fun ω => (sgnAt R 0 ω : ℂ)

lemma sign_ae : signVector R ω₀ =ᵐ[measure R ω₀] fun ω => (sgnAt R 0 ω : ℂ) :=
  (memLp_sign R ω₀).coeFn_toLp

lemma inner_signVector (z : E) :
    ⟪signVector R ω₀, op (representation R ω₀) z (signVector R ω₀)⟫_ℂ = (corr R ω₀ z : ℂ) := by
  rw [op_apply, L2.inner_def, corr, ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [sign_ae R ω₀,
    Lp.coeFn_compMeasurePreserving (signVector R ω₀) (trans_preserving R ω₀ z),
    (trans_preserving R ω₀ z).quasiMeasurePreserving.ae (sign_ae R ω₀)] with ω h1 h2 h3
  simp only [h1, h2, Function.comp_apply, h3, sgnAt, trans_apply, zero_add]
  split_ifs <;> simp

lemma norm_signVector_sq : ‖signVector R ω₀‖ ^ 2 = 1 := by
  have h : ⟪signVector R ω₀, signVector R ω₀⟫_ℂ = 1 := by
    rw [L2.inner_def]
    have he : (fun ω => ⟪signVector R ω₀ ω, signVector R ω₀ ω⟫_ℂ) =ᵐ[measure R ω₀]
        fun _ => (1 : ℂ) := by
      filter_upwards [sign_ae R ω₀] with ω h1
      simp only [h1, sgnAt]
      split_ifs <;> simp
    rw [integral_congr_ae he]
    simp
  rw [inner_self_eq_norm_sq_to_K] at h
  have h' : ((‖signVector R ω₀‖ ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by push_cast; exact h
  exact Complex.ofReal_injective h'

lemma rotation_signVector (b : K) :
    (rotation R ω₀ b : Hilbert R ω₀ →L[ℂ] Hilbert R ω₀) (signVector R ω₀) = signVector R ω₀ := by
  rw [rotation_apply]
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving (signVector R ω₀) (rotate_preserving R ω₀ b),
    (rotate_preserving R ω₀ b).quasiMeasurePreserving.ae (sign_ae R ω₀), sign_ae R ω₀]
    with ω h1 h2 h3
  simp only [Function.comp_apply, h1, h2, h3, sgnAt, rotate_apply, mul_zero]

lemma integrable_of_continuous {g : Space R → ℝ} (hg : Continuous g) :
    Integrable g (measure R ω₀) :=
  hg.integrable_of_hasCompactSupport (isClosed_tsupport g).isCompact

lemma integral_trans (a : E) (g : Space R → ℝ) :
    ∫ ω, g (trans R a ω) ∂measure R ω₀ = ∫ ω, g ω ∂measure R ω₀ :=
  (trans_preserving R ω₀ a).integral_comp (transHomeo R a).measurableEmbedding g

lemma integral_rotate (b : K) (g : Space R → ℝ) :
    ∫ ω, g (rotate R b ω) ∂measure R ω₀ = ∫ ω, g ω ∂measure R ω₀ :=
  (rotate_preserving R ω₀ b).integral_comp (rotateHomeo R b).measurableEmbedding g

lemma integral_sgnAt_mul (a b : E) :
    ∫ ω, sgnAt R a ω * sgnAt R b ω ∂measure R ω₀ = corr R ω₀ (b - a) := by
  rw [corr, ← integral_trans R ω₀ a (fun ω => sgnAt R 0 ω * sgnAt R (b - a) ω)]
  simp [sgnAt]

theorem corr_radial {z w : E} (h : ‖(z : ℂ)‖ = ‖(w : ℂ)‖) : corr R ω₀ z = corr R ω₀ w := by
  rcases eq_or_ne z 0 with rfl | hz
  · have hw : w = 0 := by
      apply Subtype.ext
      simpa [eq_comm] using h
    rw [hw]
  have hz' : (z : ℂ) ≠ 0 := by simpa using hz
  obtain ⟨b, hb⟩ := exists_kCoeff_eq (w / z) (by
    rw [IntermediateField.coe_div, norm_div, ← h, div_self (norm_ne_zero_iff.mpr hz')])
  have hb' : kCoeff b * z = w := by rw [hb, div_mul_cancel₀ w hz]
  rw [← hb', corr, corr, ← integral_rotate R ω₀ b (fun ω => sgnAt R 0 ω * sgnAt R z ω)]
  simp only [sgnAt, rotate_apply, mul_zero]
  rfl

lemma sgn_triangle {r : E} (hr : r ∈ R) (ω : Space R) (p : E) (u : K) :
    sgnAt R p ω * sgnAt R (p + kCoeff u * r) ω +
      sgnAt R p ω * sgnAt R (p + kCoeff u * (r * ζE)) ω +
      sgnAt R (p + kCoeff u * r) ω * sgnAt R (p + kCoeff u * (r * ζE)) ω = -1 := by
  have h := ω.property r hr p u
  unfold sgnAt
  generalize ω.val p = A at *
  generalize ω.val (p + kCoeff u * r) = B at *
  generalize ω.val (p + kCoeff u * (r * ζE)) = C at *
  fin_cases A <;> fin_cases B <;> fin_cases C <;> simp_all

theorem corr_triangle {r : E} (hr : r ∈ R) (u : K) :
    corr R ω₀ (kCoeff u * r) + corr R ω₀ (kCoeff u * (r * ζE)) +
      corr R ω₀ (kCoeff u * (r * ζE) - kCoeff u * r) = -1 := by
  have hi {g : Space R → ℝ} (hg : Continuous g) := integrable_of_continuous R ω₀ hg
  have hc := continuous_sgnAt R
  have h := integral_congr_ae (μ := measure R ω₀)
    (Filter.Eventually.of_forall (sgn_triangle R hr · 0 u))
  rw [integral_add (hi (by fun_prop)) (hi (by fun_prop)),
    integral_add (hi (by fun_prop)) (hi (by fun_prop)), integral_sgnAt_mul, integral_sgnAt_mul,
    integral_sgnAt_mul] at h
  simpa using h

theorem corr_side {r : E} (hr : r ∈ R) : corr R ω₀ r = -1 / 3 := by
  have h := corr_triangle R ω₀ hr 1
  have h₁ : corr R ω₀ (kCoeff 1 * (r * ζE)) = corr R ω₀ r := by
    apply corr_radial
    simp [norm_ζ]
  have h₂ : corr R ω₀ (kCoeff 1 * (r * ζE) - kCoeff 1 * r) = corr R ω₀ r := by
    apply corr_radial
    have he : ((kCoeff 1 * (r * ζE) - kCoeff 1 * r : E) : ℂ) = (r : ℂ) * (ζ - 1) := by
      simp only [kCoeff_one, one_mul]
      push_cast
      rw [coe_ζE]
      ring
    rw [he, norm_mul, norm_ζ_sub_one, mul_one]
  rw [h₁, h₂, kCoeff_one, one_mul] at h
  linarith

end ParishPlane.Transfer

end
end

-- OAI.Analysis.PlaneSpectrum.ConditionalSpectrum
section
namespace ParishLaw

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
end ParishLaw
end

-- OAI.Geometry.PlaneColoring.BorelTransfer
section
namespace ParishLaw

noncomputable section
open Filter Topology
open scoped ComplexConjugate
namespace PlaneFiveColor.Spectral
variable [Carrier]
lemma dense_E : Dense (E : Set ℂ) := by
  intro z
  have hh : ∀ x y : ℝ, (x : ℂ)+(y : ℂ)*Complex.I ∈ closure (E : Set ℂ) := by
    intro x y
    refine (Rat.denseRange_cast : DenseRange ((↑) : ℚ → ℝ)).induction_on₂
      (p := fun x y : ℝ => (x : ℂ)+(y : ℂ)*Complex.I ∈ closure (E : Set ℂ)) ?_ ?_ x y
    · exact isClosed_closure.preimage ((Complex.continuous_ofReal.comp continuous_fst).add
        ((Complex.continuous_ofReal.comp continuous_snd).mul_const Complex.I))
    · intro q r
      apply subset_closure
      have hq : ((q : ℝ) : ℂ) ∈ E := Carrier.ofReal_mem (Carrier.ratCast_mem q)
      have hr : ((r : ℝ) : ℂ) ∈ E := Carrier.ofReal_mem (Carrier.ratCast_mem r)
      exact E.add_mem hq (E.mul_mem hr imagUnit.property)
  simpa only [Complex.re_add_im] using hh z.re z.im
lemma algebraic_norm (z : E) : (‖(z:ℂ)‖ : ℂ) ∈ E :=
  Carrier.ofReal_mem (Carrier.norm_mem z.property)
end PlaneFiveColor.Spectral
end
noncomputable section
open Filter Topology
namespace PlaneFiveColor.Spectral
variable [Carrier]
lemma normalized_algebraic (z : E) (hz : z ≠ 0) :
    ∃ b : K, (b.val : ℂ) = (z : ℂ) / (‖(z:ℂ)‖ : ℂ) := by
  have hn : ‖(z:ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr (Subtype.coe_ne_coe.mpr hz)
  have hb : ‖(z:ℂ) / (‖(z:ℂ)‖ : ℂ)‖ = 1 := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),div_self hn]
  exact ⟨⟨⟨_,mem_sphere_zero_iff_norm.mpr hb⟩,
    by
      change (z : ℂ)/(‖(z:ℂ)‖ : ℂ) ∈ E
      exact div_mem z.property (algebraic_norm z)⟩,rfl⟩
lemma circle_closed_induction {p : ℂ → Prop} (hp : IsClosed {z | p z})
    (halg : ∀ b : K, p (b.val : ℂ)) (u : Circle) : p (u : ℂ) := by
  obtain ⟨s,hs,ht⟩ := mem_closure_iff_seq_limit.mp (dense_E (u : ℂ))
  have hne : ∀ᶠ n in atTop, s n ≠ 0 := ht.eventually (isOpen_compl_singleton.mem_nhds (Circle.coe_ne_zero u))
  have hnorm : Tendsto (fun n => s n / (‖s n‖ : ℂ)) atTop (𝓝 (u : ℂ)) := by
    have h := ht.div (Complex.continuous_ofReal.continuousAt.tendsto.comp ht.norm)
      (show (‖(u:ℂ)‖ : ℂ) ≠ 0 by simp [Circle.norm_coe])
    have he : (u : ℂ) / (‖(u:ℂ)‖ : ℂ) = (u : ℂ) := by simp only [Circle.norm_coe,Complex.ofReal_one,div_one]
    rw [he] at h
    convert h using 1
    rfl
  apply hp.mem_of_tendsto hnorm
  filter_upwards [hne] with n hn
  obtain ⟨b,hb⟩ := normalized_algebraic ⟨s n,hs n⟩ (fun h => hn (congrArg Subtype.val h))
  rw [← hb]
  exact halg b
end PlaneFiveColor.Spectral
end
end ParishLaw
end

-- OAI.Analysis.PlaneSpectrum.Ergodicity
section
namespace ParishLaw

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal InnerProductSpace
namespace PlaneFiveColor.Spectral
open EuclideanFiveColor EuclideanFiveColor.VectorMeasure EuclideanFiveColor.CommutingSpectral
variable [Carrier]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : DiscreteE →* unitary (H →L[ℂ] H)) (W : K → unitary (H →L[ℂ] H))
  (hcov : ∀ k z w, (W k : H →L[ℂ] H) (ContinuousVectors.op U z w) =
    ContinuousVectors.op U ((kCoeff k)*z) ((W k : H →L[ℂ] H) w))
include hcov
lemma vectorMeasure_invariant (v : H) (hfix : ∀ k, (W k : H →L[ℂ] H) v = v) :
    ∀ k : K, MeasurePreserving (fun d : D => k • d) (measure (calculus U) v) (measure (calculus U) v) := by
  intro k
  have hm : Measurable (fun d : D => k • d) := (continuous_scalar (kCoeff k)).measurable
  refine ⟨hm,measure_eq_of_fourier _ _ (fun z => ?_)⟩
  change (∫ d, evaluation z d ∂(measure (calculus U) v).map (fun d : D => k • d)) = _
  rw [integral_map hm.aemeasurable ((evaluation z).continuous.measurable.aestronglyMeasurable)]
  change (∫ d, (eval (kCoeff k * Multiplicative.toAdd z) d : ℂ) ∂measure (calculus U) v) = _
  have hc (a : E) : (∫ d, (eval a d:ℂ) ∂measure (calculus U) v) =
      ⟪v,ContinuousVectors.op U a v⟫_ℂ := by
    have hh := integral_complex (calculus U) v (evaluation (G := DiscreteE) (Multiplicative.ofAdd a))
    rw [calculus_evaluation U (Multiplicative.ofAdd a : DiscreteE)] at hh
    exact hh
  change (∫ d, (eval (kCoeff k * Multiplicative.toAdd z) d : ℂ) ∂measure (calculus U) v) =
    ∫ d, (eval (Multiplicative.toAdd z) d:ℂ) ∂measure (calculus U) v
  rw [hc,hc]
  calc
    _ = ⟪(W k : H →L[ℂ] H) v,ContinuousVectors.op U (kCoeff k * Multiplicative.toAdd z) ((W k : H →L[ℂ] H) v)⟫_ℂ := by rw [hfix k]
    _ = ⟪(W k : H →L[ℂ] H) v,(W k : H →L[ℂ] H) (ContinuousVectors.op U (Multiplicative.toAdd z) v)⟫_ℂ := by rw [hcov]
    _ = _ := Unitary.inner_map_map (W k) v (ContinuousVectors.op U (Multiplicative.toAdd z) v)
end PlaneFiveColor.Spectral
end
end ParishLaw
end

-- Erdos173.Transfer.Spectral
section
noncomputable section

namespace ParishPlane.Transfer

open MeasureTheory Filter
open ParishLaw ParishLaw.PlaneFiveColor.Spectral ParishLaw.EuclideanFiveColor
open scoped ComplexConjugate

variable [Carrier]

variable (R : Set E) (ω₀ : Space R)

private abbrev spectralMeasure : Measure D :=
  VectorMeasure.measure (CommutingSpectral.calculus (representation R ω₀)) (signVector R ω₀)

lemma integral_eval_spectralMeasure (a : E) :
    ∫ d, (eval a d : ℂ) ∂spectralMeasure R ω₀ = (corr R ω₀ a : ℂ) := by
  have hh := VectorMeasure.integral_complex (CommutingSpectral.calculus (representation R ω₀))
    (signVector R ω₀) (CommutingSpectral.evaluation (G := DiscreteE) (Multiplicative.ofAdd a))
  rw [CommutingSpectral.calculus_evaluation (representation R ω₀) (Multiplicative.ofAdd a)] at hh
  exact hh.trans (inner_signVector R ω₀ a)

lemma isWild_restrict_compl : IsWild ((spectralMeasure R ω₀).restrict (C : Set D)ᶜ) := by
  refine ⟨fun u => ?_, ?_⟩
  · have hp := vectorMeasure_invariant (representation R ω₀) (rotation R ω₀)
      (rotation_covariance R ω₀) (signVector R ω₀) (rotation_signVector R ω₀) u
    have hs : (fun d : D => u • d) ⁻¹' (C : Set D)ᶜ = (C : Set D)ᶜ := by
      ext d
      exact not_congr (scalar_mem_C_iff (kCoeff_ne_zero u) d)
    simpa only [hs] using hp.restrict_preimage measurableSet_C.compl
  · rw [Measure.restrict_apply measurableSet_C, Set.inter_compl_self, measure_empty]
end ParishPlane.Transfer
end
end

noncomputable section
open MeasureTheory Real
namespace OMA.R_Erdos173_erdos_173_R1_H2_R1_H1_R1_H2_R1_H1_R1
open MeasureTheory Filter
open scoped ENNReal
open ParishLaw ParishLaw.PlaneFiveColor.Spectral ParishLaw.EuclideanFiveColor
open ParishPlane.Transfer

/-- For a countable abelian action, a bounded observable integrates to zero if
it does on every ergodic probability assigning zero mass to a fixed null set. -/
def H1 : Prop :=
  ∀ (G X : Type) [CommGroup G] [Countable G] [MeasurableSpace X] [StandardBorelSpace X]
    [Nonempty X] [MulAction G X] [MeasurableConstSMul G X],
    ∀ (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure G X μ],
    ∀ s : Set X, MeasurableSet s → μ s = 0 →
    ∀ f : X → ℂ, Measurable f → (∀ z, ‖f z‖ ≤ 1) →
    (∀ (ρ : Measure X) [IsProbabilityMeasure ρ] [ErgodicSMul G X ρ],
      ρ s = 0 → ∫ z, f z ∂ρ = 0) → ∫ z, f z ∂μ = 0

/-- On the dual of the discrete carrier, an ergodic, rotation-invariant
probability supported off the ordinary characters has zero nontrivial Fourier coefficients. -/
def H2 : Prop := ∀ (E : IntermediateField ℚ ℂ) (F : IntermediateField ℚ ℝ), ∀ hc : Countable E,
    ∀ hF : (∀ z : ℂ, z ∈ E ↔ z.re ∈ F ∧ z.im ∈ F),
    ∀ ha : (∀ p : Polynomial ℂ, p ≠ 0 → (∀ n, p.coeff n ∈ E) → ∀ z, p.eval z = 0 → z ∈ E),
    ∀ ht : (∀ Q : Finset ℂ, (∀ q ∈ Q, q ∈ E ∧ ‖q‖ = 1) →
      ∃ S : Finset ℂ, (∀ s ∈ S, s ∈ E ∧ ‖s‖ = 1) ∧
      ∀ j : ℂ → ℂ, (∀ s ∈ S, j s ∈ Q) →
        (1 : ℂ) ∈ Submodule.span ℚ ((fun s => j s*s) '' (S : Set ℂ)) ∧
        Complex.I ∈ Submodule.span ℚ ((fun s => j s*s) '' (S : Set ℂ))),
    letI : Carrier := ⟨E,F,hc,hF,ha,ht⟩

    ∀ (μ : Measure D) [IsProbabilityMeasure μ] [ErgodicSMul K D μ],
      IsWild μ → ∀ a : E, a ≠ 0 → ∫ d, (eval a d : ℂ) ∂μ = 0

section

private instance [Carrier] : Countable K := by
  apply Function.Injective.countable (f := kCoeff)
  intro x y h
  exact Subtype.ext (Subtype.ext (congrArg (fun z : E => (z : ℂ)) h))

private instance [Carrier] : MeasurableConstSMul K D :=
  ⟨fun k => (continuous_scalar (kCoeff k)).measurable⟩

private lemma vanish [car : Carrier] (mix : H1) (rigid : H2)
    (μ : Measure D) [IsFiniteMeasure μ] (hw : IsWild μ) (a : E) (ha : a ≠ 0) :
    ∫ d, (eval a d : ℂ) ∂μ = 0 := by
  by_cases hμ : μ = 0
  · simp [hμ]
  have hu : μ Set.univ ≠ 0 := Measure.measure_univ_ne_zero.mpr hμ
  let ρ := (μ Set.univ)⁻¹ • μ
  letI : IsProbabilityMeasure ρ := ⟨by
    rw [Measure.smul_apply,smul_eq_mul,ENNReal.inv_mul_cancel hu (measure_ne_top μ Set.univ)]⟩
  have hwρ : IsWild ρ := ⟨fun k => (hw.1 k).smul_measure _, by simp [ρ,Measure.smul_apply,hw.2]⟩
  letI : SMulInvariantMeasure K D ρ := ⟨fun k s hs => (hwρ.1 k).measure_preimage hs.nullMeasurableSet⟩
  have hz := mix K D ρ (C : Set D) measurableSet_C hwρ.2 (fun d => (eval a d : ℂ))
    (measurable_eval_coe a) (fun d => (Circle.norm_coe _).le) (by
      intro τ hτ he hs
      exact rigid car.E car.F car.countable car.mem_iff car.algClosed car.template τ
        ⟨fun u => measurePreserving_smul u _,hs⟩ a ha)
  rw [integral_smul_measure] at hz
  exact (smul_eq_zero.mp hz).resolve_left (by
    rw [ENNReal.toReal_inv]
    exact inv_ne_zero ((ENNReal.toReal_pos hu (measure_ne_top μ Set.univ)).ne'))

private lemma ordinary [Carrier] (mix : H1) (rigid : H2) (R : Set E) (ω : Space R) :
    ∃ ν : Measure ℂ, IsFiniteMeasure ν ∧ ν.real Set.univ ≤ 1 ∧
    ∀ z : E, z ≠ 0 → ∀ u : Circle,
      (∫ ξ, (Circle.exp (inner ℝ ξ ((u : ℂ)*(z:ℂ))) : ℂ) ∂ν) = corr R ω z := by
  let μ := spectralMeasure R ω
  let ν := μ.comap j
  have hj := j_measurableEmbedding
  have hfourier (a : E) (ha : a ≠ 0) :
      (corr R ω a : ℂ) = ∫ ξ, (Circle.exp (inner ℝ ξ (a : ℂ)) : ℂ) ∂ν := by
    have hi : Integrable (fun d => (eval a d : ℂ)) μ :=
      Integrable.of_bound (measurable_eval_coe a).aestronglyMeasurable 1
        (Eventually.of_forall fun d => (Circle.norm_coe _).le)
    rw [← integral_eval_spectralMeasure, ← integral_add_compl measurableSet_C hi,
      vanish mix rigid _ (isWild_restrict_compl R ω) a ha, add_zero]
    change ∫ d in Set.range j, (eval a d : ℂ) ∂μ = _
    rw [← hj.map_comap, hj.integral_map]
    rfl
  let φ : ℂ → ℂ := fun w => ∫ ξ, (Circle.exp (inner ℝ ξ w) : ℂ) ∂ν
  have hφ : Continuous φ := by
    refine continuous_of_dominated (bound := fun _ => 1) (fun w => ?_)
      (fun w => Eventually.of_forall fun ξ => (Circle.norm_coe _).le) (integrable_const 1)
      (Eventually.of_forall fun ξ => ?_)
    · exact (by fun_prop : Continuous fun ξ : ℂ => (Circle.exp (inner ℝ ξ w) : ℂ))
        |>.aestronglyMeasurable
    · fun_prop
  refine ⟨ν,inferInstance,?_,fun z hz u => ?_⟩
  · have hu : ν.real Set.univ = μ.real (Set.range j) := by
      rw [Measure.real, Measure.real, hj.comap_apply, Set.image_univ]
    rw [hu]
    calc
      _ ≤ μ.real Set.univ := measureReal_mono (Set.subset_univ _)
      _ = 1 := (VectorMeasure.measure_univ _ _).trans (norm_signVector_sq R ω)
  · refine circle_closed_induction (p := fun x => φ (x * z) = corr R ω z)
      (isClosed_eq (hφ.comp (continuous_id.mul continuous_const)) continuous_const)
      (fun b => ?_) u
    have hn : ‖((kCoeff b * z : E) : ℂ)‖ = ‖(z : ℂ)‖ := by
      change ‖(b.val : ℂ) * z‖ = _
      rw [norm_mul, Circle.norm_coe, one_mul]
    change φ ((kCoeff b * z : E) : ℂ) = _
    rw [← corr_radial R ω hn]
    exact (hfourier _ (mul_ne_zero (kCoeff_ne_zero b) hz)).symm

end

theorem main : H1 → H2 → OMA.R_Erdos173_erdos_173_R1_H2_R1_H1_R1_H2_R1.H1 := by
  intro mix rigid E₀ F hc hF ha ht x hx hxE c hc'
  letI : Carrier := ⟨E₀,F,hc,hF,ha,ht⟩
  let xE : E := ⟨(x : ℂ),hxE⟩
  let R : Set E := {1,xE}
  let ω : Space R := ⟨fun z => c z, by
    intro r hr p u
    rcases hr with he | he
    · subst r
      exact hc' 1 (Or.inl rfl) p p.property _ u.property (Circle.norm_coe u.val)
    · change r = xE at he
      subst r
      exact hc' x (Or.inr rfl) p p.property _ u.property (Circle.norm_coe u.val)⟩
  obtain ⟨ν,hν,hm,hh⟩ := ordinary mix rigid R ω
  refine ⟨ν,hν,hm,?_⟩
  intro r hr u
  have aux (z : E) (hz : z ≠ 0) (hR : z ∈ R) :
      (∫ ξ, (Circle.exp (inner ℝ ξ ((u:ℂ)*(z:ℂ))) : ℂ) ∂ν) = -1/3 := by
    rw [hh z hz u, corr_side R ω hR]
    push_cast
    rfl
  rcases hr with rfl | rfl
  · exact aux 1 one_ne_zero (Set.mem_insert 1 _)
  · exact aux xE (fun he => hx.ne' (Complex.ofReal_injective (congrArg (fun z : E => (z:ℂ)) he)))
      (Set.mem_insert_of_mem _ rfl)
end OMA.R_Erdos173_erdos_173_R1_H2_R1_H1_R1_H2_R1_H1_R1

end
