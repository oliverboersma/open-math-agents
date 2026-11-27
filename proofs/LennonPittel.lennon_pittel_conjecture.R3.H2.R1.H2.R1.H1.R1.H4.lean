import OMAReductions.R_LennonPittel_lennon_pittel_conjecture_R3_H2_R1_H2_R1_H1_R1
import Mathlib

/-! Port of part of the Lennon-Pittel lower-tail proof by Bo Cowgill,
https://github.com/bocowgill/lennon-pittel at commit cf950d0596591bba912b1568aa394f99986f8191,
Copyright 2026 Bo Cowgill, used under the Apache License 2.0.
Changes: modules flattened into one file, comments removed, declarations not needed here dropped,
names adapted to the pinned Mathlib, the marked model renamed and tied to the parent reduction's
definitions (after moon-4's port of the same model for the parent step).
This step is part of the abundance argument of the source. Its three recursive definitions are those of the parent reduction, used through the equations it exports. -/


-- StandardExponentialScoreLaw
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace StepA4
private theorem expMeasure_eq_withDensity (r : ℝ) :
    expMeasure r = volume.withDensity (exponentialPDF r) := rfl
private theorem measurable_exponentialPDF (r : ℝ) : Measurable (exponentialPDF r) :=
  (measurable_exponentialPDFReal r).ennreal_ofReal
private theorem lintegral_expMeasure_one (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ∂expMeasure 1) = ∫⁻ x, exponentialPDF 1 x * f x :=
  lintegral_withDensity_eq_lintegral_mul volume (measurable_exponentialPDF 1) hf
theorem ae_expMeasure_one_nonneg : ∀ᵐ x ∂expMeasure 1, 0 ≤ x := by
  rw [ae_iff, expMeasure_eq_withDensity]
  simp only [not_le]
  change volume.withDensity (exponentialPDF 1) (Iio 0) = 0
  rw [withDensity_apply _ measurableSet_Iio, lintegral_exponentialPDF_of_nonpos le_rfl]
theorem lintegral_expMeasure_one_sq :
    (∫⁻ x, ENNReal.ofReal (x ^ 2) ∂expMeasure 1) = (2 : ℝ≥0∞) := by
  rw [lintegral_expMeasure_one _ (by fun_prop)]
  have h (x : ℝ) :
      exponentialPDF 1 x * ENNReal.ofReal (x ^ 2) = 2 * gammaPDF 3 1 x := by
    by_cases hx : 0 ≤ x
    · have hGamma : Real.Gamma 3 = 2 := by
        norm_num [show (3 : ℝ) = (2 : ℕ) + 1 by norm_num, Real.Gamma_nat_eq_factorial,
          Nat.factorial]
      rw [exponentialPDF_of_nonneg hx, gammaPDF_of_nonneg hx, ← ENNReal.ofReal_ofNat,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ))]
      congr 1
      norm_num [hGamma, Real.rpow_two]
      ring
    · rw [exponentialPDF_of_neg (lt_of_not_ge hx), gammaPDF_of_neg (lt_of_not_ge hx),
        zero_mul, mul_zero]
  simp_rw [h]
  have hγ : Measurable (gammaPDF 3 1) := (measurable_gammaPDFReal 3 1).ennreal_ofReal
  rw [lintegral_const_mul _ hγ,
    lintegral_gammaPDF_eq_one (by norm_num) (by norm_num), mul_one]
end StepA4
end

-- BoundedProductChernoff
section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace StepA4
end StepA4
end

-- IidScoreRanks
section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace StepA4
variable (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]
theorem ae_injective_iid (n : ℕ) :
    ∀ᵐ x ∂(Measure.pi fun _ : Fin n ↦ μ), Function.Injective (x : Fin n → ℝ) := by
  let law : Measure (Fin n → ℝ) := Measure.pi fun _ : Fin n ↦ μ
  have hind : iIndepFun (fun i (x : Fin n → ℝ) ↦ x i) law :=
    iIndepFun_pi (fun _ ↦ aemeasurable_id)
  refine ae_all_iff.2 fun i ↦ ae_all_iff.2 fun j ↦ ?_
  by_cases hij : i = j
  · exact Filter.Eventually.of_forall fun _ _ ↦ hij
  have hi := (measurable_pi_apply i : Measurable (fun x : Fin n → ℝ ↦ x i))
  have hj := (measurable_pi_apply j : Measurable (fun x : Fin n → ℝ ↦ x j))
  
  have hpair : law.map (fun x ↦ (x i, x j)) = μ.prod μ :=
    ((indepFun_iff_map_prod_eq_prod_map_map hi.aemeasurable hj.aemeasurable).1
      (hind.indepFun hij)).trans
        (congrArg₂ Measure.prod (measurePreserving_eval (fun _ : Fin n ↦ μ) i).map_eq
          (measurePreserving_eval (fun _ : Fin n ↦ μ) j).map_eq)
  let diagonal : Set (ℝ × ℝ) := {z | z.1 = z.2}
  have hd : MeasurableSet diagonal := measurableSet_eq_fun measurable_fst measurable_snd
  have hnull : (μ.prod μ) diagonal = 0 := by
    rw [Measure.prod_apply hd]
    have hsection (u : ℝ) : Prod.mk u ⁻¹' diagonal = {u} :=
      Set.ext fun _ ↦ eq_comm
    simp [hsection]
  have hpull : law {x | x i = x j} = 0 := by
    rw [← hpair, Measure.map_apply (hi.prodMk hj) hd] at hnull
    exact hnull
  exact ae_iff.2 (by simpa [hij] using hpull)
private theorem perm_eq_of_lt_iff {n : ℕ} {p q : Equiv.Perm (Fin n)}
    (h : ∀ i j, p i < p j ↔ q i < q j) : p = q := by
  let f := fun i ↦ q (p.symm i)
  have hf : StrictMono f := fun i j hij ↦ (h (p.symm i) (p.symm j)).1
    (by simpa using hij)
  exact Equiv.ext fun i ↦ by
    simpa [f] using (hf.id_le (p i)).antisymm (hf.le_id (p i))
theorem measurePreserving_rank_of_iid {n : ℕ}
    [MeasurableSpace (Equiv.Perm (Fin n))] [MeasurableSingletonClass (Equiv.Perm (Fin n))]
    {r : (Fin n → ℝ) → Equiv.Perm (Fin n)} (hr : Measurable r)
    (hcmp : ∀ x, Function.Injective x → ∀ i j, r x i < r x j ↔ x i < x j) :
    MeasurePreserving r (Measure.pi fun _ : Fin n ↦ μ)
      (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure := by
  let law : Measure (Fin n → ℝ) := Measure.pi fun _ : Fin n ↦ μ
  let ν : Measure (Equiv.Perm (Fin n)) := law.map r
  have : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hr.aemeasurable
  
  have hequal (p q : Equiv.Perm (Fin n)) : ν {p} = ν {q} := by
    let e : Equiv.Perm (Fin n) := q.trans p.symm
    let reindex := MeasurableEquiv.piCongrLeft (fun _ : Fin n ↦ ℝ) e.symm
    have hm : MeasurePreserving reindex law law :=
      measurePreserving_piCongrLeft (fun _ : Fin n ↦ μ) e.symm
    have he (x : Fin n → ℝ) (i : Fin n) : reindex x i = x (e i) := by
      simp [reindex, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
    have hcongr : r ⁻¹' ({p} : Set (Equiv.Perm (Fin n))) =ᶠ[ae law] reindex ⁻¹' (r ⁻¹' {q}) :=
      (ae_injective_iid μ n).mono fun x hx ↦ by
        have hre : r (reindex x) = e.trans (r x) := perm_eq_of_lt_iff fun i j ↦
          (hcmp (reindex x) (by
            simpa only [Function.Injective, Function.comp_apply, he] using hx.comp e.injective) i j).trans
            (by simpa only [he, Equiv.trans_apply] using (hcmp x hx (e i) (e j)).symm)
        apply propext
        change (r x = p) ↔ r (reindex x) = q
        rw [hre]
        constructor
        · rintro rfl
          simp [e, Equiv.trans_assoc]
        · intro h
          apply Equiv.ext
          intro i
          have hi := DFunLike.congr_fun h (e.symm i)
          simpa [e] using hi
    change law.map r {p} = law.map r {q}
    rw [Measure.map_apply hr (measurableSet_singleton p),
      Measure.map_apply hr (measurableSet_singleton q)]
    exact (measure_congr hcongr).trans
      (hm.measure_preimage (hr (measurableSet_singleton q)).nullMeasurableSet)
  refine ⟨hr, Measure.ext_of_singleton fun p ↦ ?_⟩
  
  have hsum : ν {p} * (Fintype.card (Equiv.Perm (Fin n)) : ℝ≥0∞) = 1 := by
    calc
      _ = ∑' q : Equiv.Perm (Fin n), ν {q} := by
        rw [tsum_fintype, Finset.sum_congr rfl (fun q _ ↦ hequal q p), Finset.sum_const,
          Finset.card_univ, nsmul_eq_mul, mul_comm]
      _ = 1 := by simpa only [Measure.toPMF_apply] using ν.toPMF.tsum_coe
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton p), PMF.uniformOfFintype_apply]
  exact ENNReal.eq_inv_of_mul_eq_one_left hsum
end StepA4
end

-- MarkedCounting
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace StepA4
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [Fintype A] [Nonempty A]
private noncomputable def uniformMarkLaw (A : Type*) [MeasurableSpace A] [Fintype A] [Nonempty A] :
    Measure A :=
  (PMF.uniformOfFintype A).toMeasure
private instance uniformMarkLaw_isProbabilityMeasure : IsProbabilityMeasure (uniformMarkLaw A) :=
  inferInstanceAs (IsProbabilityMeasure (PMF.uniformOfFintype A).toMeasure)
private noncomputable def markedLaw (P : Measure Ω) (E : Set (Ω × A)) : Measure (Ω × A) :=
  ProbabilityTheory.cond (P.prod (uniformMarkLaw A)) E
private noncomputable def markedNormalizer (P : Measure Ω) (E : Set (Ω × A)) : ℝ≥0∞ :=
  ∫⁻ ω, ∑ a, E.indicator 1 (ω, a) ∂ P
theorem markedLaw_isProbabilityMeasure (P : Measure Ω) [IsProbabilityMeasure P]
    {E : Set (Ω × A)} (hpos : (P.prod (uniformMarkLaw A)) E ≠ 0) :
    IsProbabilityMeasure (markedLaw P E) :=
  ProbabilityTheory.cond_isProbabilityMeasure hpos
variable [MeasurableSingletonClass A]
private theorem lintegral_restrict_uniformMarkLaw (P : Measure Ω)
    {E : Set (Ω × A)} (hE : MeasurableSet E) {f : Ω × A → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ z in E, f z ∂P.prod (uniformMarkLaw A)) =
      (Fintype.card A : ℝ≥0∞)⁻¹ * (∫⁻ ω, ∑ a, E.indicator f (ω, a) ∂ P) := by
  rw [← lintegral_indicator hE, lintegral_prod _ (hf.indicator hE).aemeasurable]
  simp only [lintegral_fintype, uniformMarkLaw, PMF.toMeasure_apply_singleton _ _
    (measurableSet_singleton _), PMF.uniformOfFintype_apply, ← Finset.sum_mul]
  rw [lintegral_mul_const' _ _ (by simp [Fintype.card_ne_zero]), mul_comm]
theorem uniform_mark_event_mass (P : Measure Ω) {E : Set (Ω × A)} (hE : MeasurableSet E) :
    (P.prod (uniformMarkLaw A)) E = (Fintype.card A : ℝ≥0∞)⁻¹ * markedNormalizer P E := by
  simpa [markedNormalizer] using
    lintegral_restrict_uniformMarkLaw P hE (f := 1) measurable_const
theorem marked_counting_identity (P : Measure Ω) [IsProbabilityMeasure P]
    {E : Set (Ω × A)} (hE : MeasurableSet E)
    (hpos : (P.prod (uniformMarkLaw A)) E ≠ 0)
    {f : Ω × A → ℝ≥0∞} (hf : Measurable f) :
    markedNormalizer P E * (∫⁻ z, f z ∂markedLaw P E) =
      ∫⁻ ω, ∑ a, E.indicator f (ω, a) ∂ P := by
  have hscaled : (Fintype.card A : ℝ≥0∞) * (P.prod (uniformMarkLaw A)) E =
      markedNormalizer P E := by
    rw [uniform_mark_event_mass P hE, ← mul_assoc,
      ENNReal.mul_inv_cancel (by simp [Fintype.card_ne_zero]) (by simp), one_mul]
  rw [← hscaled, markedLaw, ProbabilityTheory.cond, lintegral_smul_measure, smul_eq_mul,
    lintegral_restrict_uniformMarkLaw P hE hf]
  rw [mul_assoc, ← mul_assoc ((P.prod (uniformMarkLaw A)) E),
    ENNReal.mul_inv_cancel hpos (measure_lt_top _ _).ne, one_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel (by simp [Fintype.card_ne_zero]) (by simp), one_mul]
section StableMarriage
open StableMarriage
scoped instance matchingMeasurableSpace (n : ℕ) : MeasurableSpace (Matching n) := ⊤
scoped instance matchingDiscreteMeasurableSpace (n : ℕ) :
    DiscreteMeasurableSpace (Matching n) :=
  ⟨fun _ ↦ trivial⟩
scoped instance profileDiscreteMeasurableSpace (n : ℕ) : DiscreteMeasurableSpace (Profile n) :=
  ⟨fun _ ↦ trivial⟩
private def stableMarkEvent (n : ℕ) : Set (Profile n × Matching n) :=
  {z | IsStable z.1 z.2}
theorem measurableSet_stableMarkEvent (n : ℕ) : MeasurableSet (stableMarkEvent n) :=
  .of_discrete
theorem sum_stableMarkEvent_indicator_one {n : ℕ} (p : Profile n) :
    (∑ a : Matching n, (stableMarkEvent n).indicator 1 (p, a)) =
      (numStableMatchings p : ℝ≥0∞) := by
  classical
  change (∑ a : Matching n, if IsStable p a then (1 : ℝ≥0∞) else 0) =
    (Fintype.card {a : Matching n // IsStable p a} : ℝ≥0∞)
  rw [Fintype.card_subtype, ← Finset.sum_filter]
  simp
theorem markedNormalizer_stableMarkEvent (n : ℕ) :
    markedNormalizer (uniformProfile n).toMeasure (stableMarkEvent n) =
      ENNReal.ofReal (expectedNumStableMatchings n) := by
  rw [expectedNumStableMatchings, ofReal_integral_eq_lintegral_ofReal
    (memLp_one_iff_integrable.mp MemLp.of_discrete)
    (Filter.Eventually.of_forall fun _ ↦ Nat.cast_nonneg _)]
  simp [markedNormalizer, sum_stableMarkEvent_indicator_one]
theorem uniform_profile_stable_mark_ne_zero (n : ℕ) :
    ((uniformProfile n).toMeasure.prod (uniformMarkLaw (Matching n))) (stableMarkEvent n) ≠ 0 := by
  let p : Profile n := ⟨fun _ ↦ Equiv.refl _, fun _ ↦ Equiv.refl _⟩
  let m : Matching n := Equiv.refl _
  have hm : IsStable p m := fun _ _ hb ↦ lt_asymm hb.2.1 hb.2.2
  exact ne_of_gt <| calc
    0 < ((uniformProfile n).toMeasure.prod (uniformMarkLaw (Matching n))) {(p, m)} := by
      rw [← Set.singleton_prod_singleton, Measure.prod_prod]
      simp only [uniformProfile, uniformMarkLaw, PMF.toMeasure_apply_singleton _ _
        (measurableSet_singleton _), PMF.uniformOfFintype_apply]
      simp [pos_iff_ne_zero]
    _ ≤ ((uniformProfile n).toMeasure.prod (uniformMarkLaw (Matching n))) (stableMarkEvent n) :=
      measure_mono (Set.singleton_subset_iff.mpr hm)
end StableMarriage
end StepA4
end

-- ScoreRanks
section
open Function MeasureTheory Set
namespace StepA4
private noncomputable def scoreImage {n : ℕ} (x : Fin n → ℝ) : Finset ℝ :=
  Finset.univ.image x
private theorem card_scoreImage {n : ℕ} {x : Fin n → ℝ} (hx : Injective x) :
    (scoreImage x).card = n := by
  rw [scoreImage, Finset.card_image_of_injective _ hx, Finset.card_univ, Fintype.card_fin]
private noncomputable def scoreEquiv {n : ℕ} (x : Fin n → ℝ) (hx : Injective x) :
    Fin n ≃ (scoreImage x : Set ℝ) :=
  Equiv.ofBijective (fun i ↦ ⟨x i, Finset.mem_image_of_mem x (Finset.mem_univ i)⟩)
    ⟨fun _ _ h ↦ hx (congrArg Subtype.val h), fun y ↦
      let ⟨i, _, hi⟩ := Finset.mem_image.mp (show y.val ∈ Finset.univ.image x from y.property)
      ⟨i, Subtype.ext hi⟩⟩
private noncomputable def rankPermutation {n : ℕ} (x : Fin n → ℝ) : Equiv.Perm (Fin n) := by
  classical
  exact if h : Injective x then
    (scoreEquiv x h).trans ((scoreImage x).orderIsoOfFin (card_scoreImage h)).symm.toEquiv
  else Equiv.refl _
theorem rankPermutation_lt_iff {n : ℕ} {x : Fin n → ℝ} (hx : Injective x) (i j : Fin n) :
    rankPermutation x i < rankPermutation x j ↔ x i < x j := by
  classical
  unfold rankPermutation
  rw [dif_pos hx]
  exact ((scoreImage x).orderIsoOfFin (card_scoreImage hx)).symm.lt_iff_lt
    (x := scoreEquiv x hx i) (y := scoreEquiv x hx j)
private def rankChamber {n : ℕ} (p : Equiv.Perm (Fin n)) : Set (Fin n → ℝ) :=
  {x | ∀ i j, p i < p j → x i < x j}
private theorem measurableSet_rankChamber {n : ℕ} (p : Equiv.Perm (Fin n)) :
    MeasurableSet (rankChamber p) := by
  unfold rankChamber
  rw [Set.ofPred_forall]
  refine MeasurableSet.iInter fun i ↦ ?_
  rw [Set.ofPred_forall]
  refine MeasurableSet.iInter fun j ↦ ?_
  by_cases h : p i < p j
  · simpa only [h, true_implies] using
      (measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply j) :
        MeasurableSet {x : Fin n → ℝ | x i < x j})
  · simp [h]
private theorem measurableSet_injective_row (n : ℕ) :
    MeasurableSet {x : Fin n → ℝ | Injective x} := by
  unfold Injective
  rw [Set.ofPred_forall]
  refine MeasurableSet.iInter fun i ↦ ?_
  rw [Set.ofPred_forall]
  refine MeasurableSet.iInter fun j ↦ ?_
  by_cases h : i = j
  · simp [h]
  · exact ((measurableSet_eq_fun (measurable_pi_apply i) (measurable_pi_apply j) :
      MeasurableSet {x : Fin n → ℝ | x i = x j}).compl).congr (by ext x; simp [h])
private theorem rankPermutation_eq_iff {n : ℕ} {x : Fin n → ℝ} (hx : Injective x)
    (p : Equiv.Perm (Fin n)) : rankPermutation x = p ↔ x ∈ rankChamber p := by
  constructor
  · rintro rfl i j hij
    exact (rankPermutation_lt_iff hx i j).mp hij
  · intro hp
    have hmono : StrictMono (rankPermutation x ∘ p.symm) := fun i j hij ↦
      (rankPermutation_lt_iff hx (p.symm i) (p.symm j)).mpr <|
        hp (p.symm i) (p.symm j) (by simpa using hij)
    apply Equiv.ext
    intro i
    simpa only [Function.comp_apply, Equiv.symm_apply_apply, id_eq] using
      le_antisymm (hmono.le_id (p i)) (hmono.id_le (p i))
theorem measurable_rankPermutation (n : ℕ) :
    @Measurable (Fin n → ℝ) (Equiv.Perm (Fin n)) inferInstance ⊤ rankPermutation := by
  classical
  let : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤
  apply measurable_to_countable'
  intro p
  have hpre : rankPermutation ⁻¹' {p} =
      ({x : Fin n → ℝ | Injective x} ∩ rankChamber p) ∪
        ({x : Fin n → ℝ | Injective x}ᶜ ∩ {x : Fin n → ℝ | Equiv.refl (Fin n) = p}) := by
    ext x
    by_cases hx : Injective x
    · simpa only [mem_preimage, mem_singleton_iff, mem_union, mem_inter_iff, mem_ofPred_eq,
        mem_compl_iff, hx, not_true_eq_false, true_and, false_and, or_false] using
          rankPermutation_eq_iff hx p
    · simp [rankPermutation, hx]
  rw [hpre]
  exact ((measurableSet_injective_row n).inter (measurableSet_rankChamber p)).union
    ((measurableSet_injective_row n).compl.inter (MeasurableSet.const _))
private abbrev ScoreProfile (n : ℕ) := (Fin n ⊕ Fin n) → Fin n → ℝ
private noncomputable def profileOfScores {n : ℕ} (x : ScoreProfile n) : StableMarriage.Profile n :=
  ⟨fun m ↦ rankPermutation (x (.inl m)), fun w ↦ rankPermutation (x (.inr w))⟩
theorem measurable_profileOfScores (n : ℕ) : Measurable (@profileOfScores n) := by
  let : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤
  let : DiscreteMeasurableSpace (Equiv.Perm (Fin n)) :=
    ⟨fun _ ↦ MeasurableSpace.measurableSet_top⟩
  have hrow (r : Fin n ⊕ Fin n) (p : Equiv.Perm (Fin n)) :
      MeasurableSet {x : ScoreProfile n | rankPermutation (x r) = p} :=
    ((measurable_rankPermutation n).comp (measurable_pi_apply r)) (measurableSet_singleton p)
  apply measurable_to_countable'
  rintro ⟨men, women⟩
  change MeasurableSet {x | profileOfScores x = ⟨men, women⟩}
  simp only [profileOfScores, StableMarriage.Profile.mk.injEq, funext_iff, Set.ofPred_and,
    Set.ofPred_forall]
  exact (MeasurableSet.iInter fun m ↦ hrow (.inl m) (men m)).inter
    (MeasurableSet.iInter fun w ↦ hrow (.inr w) (women w))
private def IsScoreBlockingPair {n : ℕ} (x : ScoreProfile n) (μ : StableMarriage.Matching n)
    (m w : Fin n) : Prop :=
  μ m ≠ w ∧ x (.inl m) w < x (.inl m) (μ m) ∧ x (.inr w) m < x (.inr w) (μ.symm w)
private def IsScoreStable {n : ℕ} (x : ScoreProfile n) (μ : StableMarriage.Matching n) : Prop :=
  ∀ m w, ¬ IsScoreBlockingPair x μ m w
theorem isBlockingPair_profileOfScores_iff {n : ℕ} {x : ScoreProfile n}
    (hx : ∀ r, Injective (x r)) (μ : StableMarriage.Matching n) (m w : Fin n) :
    StableMarriage.IsBlockingPair (profileOfScores x) μ m w ↔ IsScoreBlockingPair x μ m w := by
  simp only [StableMarriage.IsBlockingPair, profileOfScores, IsScoreBlockingPair,
    rankPermutation_lt_iff (hx (.inl m)), rankPermutation_lt_iff (hx (.inr w))]
theorem isStable_profileOfScores_iff {n : ℕ} {x : ScoreProfile n}
    (hx : ∀ r, Injective (x r)) (μ : StableMarriage.Matching n) :
    StableMarriage.IsStable (profileOfScores x) μ ↔ IsScoreStable x μ := by
  simp only [StableMarriage.IsStable, IsScoreStable, isBlockingPair_profileOfScores_iff hx]
theorem measurableSet_isScoreStable {n : ℕ} (μ : StableMarriage.Matching n) :
    MeasurableSet {x : ScoreProfile n | IsScoreStable x μ} := by
  have hcell (r : Fin n ⊕ Fin n) (a : Fin n) : Measurable (fun x : ScoreProfile n ↦ x r a) :=
    (measurable_pi_apply a).comp (measurable_pi_apply r)
  unfold IsScoreStable
  rw [Set.ofPred_forall]
  refine MeasurableSet.iInter fun m ↦ ?_
  rw [Set.ofPred_forall]
  refine MeasurableSet.iInter fun w ↦ ?_
  by_cases h : μ m = w
  · simp [IsScoreBlockingPair, h]
  · exact ((measurableSet_lt (hcell (.inl m) w) (hcell (.inl m) (μ m))).inter
      (measurableSet_lt (hcell (.inr w) m) (hcell (.inr w) (μ.symm w)))).compl.congr
        (Set.ext fun x ↦ by simp [IsScoreBlockingPair, h])
theorem measurableSet_scoreStableEvent (n : ℕ) [MeasurableSpace (StableMarriage.Matching n)]
    [MeasurableSingletonClass (StableMarriage.Matching n)] :
    MeasurableSet {z : ScoreProfile n × StableMarriage.Matching n | IsScoreStable z.1 z.2} :=
  (measurable_from_prod_countable_left fun μ ↦
    measurableSet_setOfPred.mp (measurableSet_isScoreStable μ)).setOf
end StepA4
end

-- ContinuousScoreBridge
section
open scoped BigOperators ENNReal StepA4
open MeasureTheory Set
namespace StepA4
private noncomputable def unitScoreLaw : Measure ℝ :=
  volume.restrict (Icc 0 1)
private instance : IsProbabilityMeasure unitScoreLaw :=
  ⟨by simp [unitScoreLaw, Real.volume_Icc]⟩
private instance : NullSingletonClass unitScoreLaw :=
  Measure.restrict.instNullSingletonClass _
private noncomputable def rankRowsEquiv (n : ℕ) :
    ((Fin n ⊕ Fin n) → Equiv.Perm (Fin n)) ≃ StableMarriage.Profile n where
  toFun p := ⟨p ∘ Sum.inl, p ∘ Sum.inr⟩
  invFun p := Sum.elim p.manRank p.womanRank
  left_inv _ := funext fun i ↦ Sum.rec (fun _ ↦ rfl) (fun _ ↦ rfl) i
  right_inv := fun ⟨_, _⟩ ↦ rfl
private theorem measurePreserving_rankRowsEquiv (n : ℕ) :
    MeasurePreserving (rankRowsEquiv n)
      (Measure.pi fun _ : Fin n ⊕ Fin n ↦
        (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure)
      (StableMarriage.uniformProfile n).toMeasure := by
  refine ⟨measurable_of_countable _, Measure.ext_of_singleton fun p ↦ ?_⟩
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton p)]
  rw [show (rankRowsEquiv n) ⁻¹' {p} = {(rankRowsEquiv n).symm p} by
    ext x
    simp [← Equiv.eq_symm_apply]]
  rw [StableMarriage.uniformProfile, PMF.toMeasure_apply_singleton _ p (measurableSet_singleton _)]
  simp [← Fintype.card_congr (rankRowsEquiv n), ENNReal.inv_pow]
private noncomputable def continuousScoreLaw (n : ℕ) : Measure (ScoreProfile n) :=
  Measure.pi fun _ : Fin n ⊕ Fin n ↦ Measure.pi fun _ : Fin n ↦ unitScoreLaw
private instance (n : ℕ) : IsProbabilityMeasure (continuousScoreLaw n) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : Fin n ⊕ Fin n ↦
    Measure.pi fun _ : Fin n ↦ unitScoreLaw))
theorem ae_injective_rows (n : ℕ) :
    ∀ᵐ x ∂continuousScoreLaw n, ∀ r, Function.Injective (x r) :=
  ae_all_iff.2 fun _ ↦ Measure.tendsto_eval_ae_ae.eventually (ae_injective_iid unitScoreLaw n)
theorem measurePreserving_profileOfScores (n : ℕ) :
    MeasurePreserving (@profileOfScores n) (continuousScoreLaw n)
      (StableMarriage.uniformProfile n).toMeasure :=
  (measurePreserving_rankRowsEquiv n).comp
    (measurePreserving_pi _ _ fun _ ↦
      measurePreserving_rank_of_iid unitScoreLaw (measurable_rankPermutation n)
        (fun _ hx ↦ rankPermutation_lt_iff hx))
private def scoreMarkEvent (n : ℕ) : Set (ScoreProfile n × StableMarriage.Matching n) :=
  {z | IsScoreStable z.1 z.2}
private theorem measurableSet_scoreMarkEvent (n : ℕ) :
    MeasurableSet (scoreMarkEvent n) :=
  measurableSet_scoreStableEvent n
theorem measurePreserving_scoreAndMark (n : ℕ) :
    MeasurePreserving (Prod.map (@profileOfScores n) id)
      ((continuousScoreLaw n).prod (uniformMarkLaw (StableMarriage.Matching n)))
      ((StableMarriage.uniformProfile n).toMeasure.prod
        (uniformMarkLaw (StableMarriage.Matching n))) :=
  (measurePreserving_profileOfScores n).prod (MeasurePreserving.id _)
theorem score_mark_event_ae_eq (n : ℕ) :
    scoreMarkEvent n =ᵐ[((continuousScoreLaw n).prod
      (uniformMarkLaw (StableMarriage.Matching n)))]
      (Prod.map (@profileOfScores n) id) ⁻¹' stableMarkEvent n :=
  ((Measure.quasiMeasurePreserving_fst
    (μ := continuousScoreLaw n) (ν := uniformMarkLaw (StableMarriage.Matching n))).ae
      (ae_injective_rows n)).mono fun z hz ↦
    propext (isStable_profileOfScores_iff hz z.2).symm
theorem score_mark_event_mass_eq (n : ℕ) :
    ((continuousScoreLaw n).prod (uniformMarkLaw (StableMarriage.Matching n))) (scoreMarkEvent n) =
    ((StableMarriage.uniformProfile n).toMeasure.prod
      (uniformMarkLaw (StableMarriage.Matching n))) (stableMarkEvent n) :=
  (measure_congr (score_mark_event_ae_eq n)).trans
    ((measurePreserving_scoreAndMark n).measure_preimage
      (measurableSet_stableMarkEvent n).nullMeasurableSet)
private noncomputable def scoreMarkedLaw (n : ℕ) :
    Measure (ScoreProfile n × StableMarriage.Matching n) :=
  markedLaw (continuousScoreLaw n) (scoreMarkEvent n)
private instance (n : ℕ) : IsProbabilityMeasure (scoreMarkedLaw n) :=
  markedLaw_isProbabilityMeasure (continuousScoreLaw n)
    ((score_mark_event_mass_eq n).trans_ne (uniform_profile_stable_mark_ne_zero n))
theorem markedNormalizer_scoreMarkEvent (n : ℕ) :
    markedNormalizer (continuousScoreLaw n) (scoreMarkEvent n) =
      ENNReal.ofReal (StableMarriage.expectedNumStableMatchings n) := by
  have h := congrArg ((Fintype.card (StableMarriage.Matching n) : ℝ≥0∞) * ·)
    (score_mark_event_mass_eq n)
  simpa only [uniform_mark_event_mass _ (measurableSet_scoreMarkEvent n),
    uniform_mark_event_mass _ (measurableSet_stableMarkEvent n), ← mul_assoc,
    ENNReal.mul_inv_cancel (a := (Fintype.card (StableMarriage.Matching n) : ℝ≥0∞))
      (by simp [Fintype.card_ne_zero]) (by simp), one_mul,
    markedNormalizer_stableMarkEvent] using h
theorem continuous_mark_counting_identity (n : ℕ)
    {f : ScoreProfile n × StableMarriage.Matching n → ℝ≥0∞} (hf : Measurable f) :
    ENNReal.ofReal (StableMarriage.expectedNumStableMatchings n) *
      (∫⁻ z, f z ∂scoreMarkedLaw n) =
      ∫⁻ x, ∑ m, (scoreMarkEvent n).indicator f (x, m) ∂continuousScoreLaw n := by
  simpa only [markedNormalizer_scoreMarkEvent, scoreMarkedLaw] using
    marked_counting_identity (continuousScoreLaw n) (measurableSet_scoreMarkEvent n)
      ((score_mark_event_mass_eq n).trans_ne (uniform_profile_stable_mark_ne_zero n)) hf
end StepA4
end

-- CoexposureGoodScores
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal StepA4
namespace StepA4
variable {n : ℕ}
private def maleSpouseScore (x : ScoreProfile n) (μ : Matching n) (i : Fin n) : ℝ :=
  x (.inl i) (μ i)
private def femaleSpouseScore (x : ScoreProfile n) (μ : Matching n) (j : Fin n) : ℝ :=
  x (.inr j) (μ.symm j)
private def femaleSpouseTotal (x : ScoreProfile n) (μ : Matching n) : ℝ :=
  ∑ j, femaleSpouseScore x μ j
private def GoodSpouseScores (x : ScoreProfile n) (μ : Matching n) : Prop :=
  2 ≤ femaleSpouseTotal x μ ∧
    (∀ j, femaleSpouseScore x μ j / femaleSpouseTotal x μ ≤ 12 * Real.log n / n) ∧
    (∀ i, maleSpouseScore x μ i ≤ 8 * Real.log n / (femaleSpouseTotal x μ - 1))
private theorem measurable_scoreCoordinate (r : Fin n ⊕ Fin n) (i : Fin n) :
    Measurable (fun x : ScoreProfile n ↦ x r i) :=
  (measurable_pi_apply i).comp (measurable_pi_apply r)
theorem measurable_femaleSpouseScore (μ : Matching n) (j : Fin n) :
    Measurable (fun x : ScoreProfile n ↦ femaleSpouseScore x μ j) :=
  measurable_scoreCoordinate (.inr j) (μ.symm j)
theorem ae_unitOpen_scores (n : ℕ) :
    ∀ᵐ x ∂continuousScoreLaw n, ∀ r i, x r i ∈ Ioo (0 : ℝ) 1 := by
  have hopen : ∀ᵐ t ∂unitScoreLaw, t ∈ Ioo (0 : ℝ) 1 := by
    rw [unitScoreLaw, ← Measure.restrict_congr_set Ioo_ae_eq_Icc]
    exact ae_restrict_mem measurableSet_Ioo
  exact ae_all_iff.2 fun r ↦ ae_all_iff.2 fun i ↦
    (Measure.tendsto_eval_ae_ae (i := r)
      (μ := fun _ : Fin n ⊕ Fin n ↦ Measure.pi fun _ : Fin n ↦ unitScoreLaw)).eventually
      ((Measure.tendsto_eval_ae_ae (i := i) (μ := fun _ : Fin n ↦ unitScoreLaw)).eventually hopen)
end StepA4
end

-- CoexposureScoreEstimates
section
open Filter MeasureTheory Set StableMarriage
open scoped ENNReal BigOperators Topology
namespace StepA4
private def scoreSimplex (n : ℕ) (s : ℝ) : Set (Fin n → ℝ) :=
  {y | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ s}
theorem measurableSet_scoreSimplex (n : ℕ) (s : ℝ) :
    MeasurableSet (scoreSimplex n s) := by
  unfold scoreSimplex
  rw [ofPred_and, ofPred_forall]
  exact (MeasurableSet.iInter fun i ↦ measurableSet_le measurable_const (measurable_pi_apply i)).inter
    (measurableSet_le (Finset.measurable_sum _ fun i _ ↦ measurable_pi_apply i) measurable_const)
theorem volume_scoreSimplex (n : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    volume (scoreSimplex n s) = ENNReal.ofReal (s ^ n / (n.factorial : ℝ)) := by
  induction n generalizing s with
  | zero =>
    simp [scoreSimplex, hs, volume_pi]
  | succ n ih =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0
    let S : Set (ℝ × (Fin n → ℝ)) :=
      {a | 0 ≤ a.1 ∧ a.2 ∈ scoreSimplex n (s - a.1)}
    have heq : e ⁻¹' S = scoreSimplex (n + 1) s := by
      ext y
      simp only [e, MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_symm_apply,
        Fin.removeNth, Fin.succAbove_zero, Set.mem_preimage, S, scoreSimplex, mem_ofPred_eq,
        Fin.forall_fin_succ, Fin.sum_univ_succ]
      exact ⟨fun h ↦ ⟨⟨h.1, h.2.1⟩, by linarith [h.2.2]⟩,
        fun h ↦ ⟨h.1.1, h.1.2, by linarith [h.2]⟩⟩
    have hS : MeasurableSet S :=
      e.measurableSet_preimage.mp (heq.symm ▸ measurableSet_scoreSimplex _ _)
    have he : MeasurePreserving e volume volume :=
      volume_preserving_piFinSuccAbove _ _
    rw [← heq, he.measure_preimage_emb e.measurableEmbedding]
    change ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) S = _
    rw [Measure.prod_apply hS]
    let f (t : ℝ) : ℝ := (s - t) ^ n / (n.factorial : ℝ)
    have hslice (t : ℝ) :
        volume (Prod.mk t ⁻¹' S) = (Icc 0 s).indicator (fun t ↦ ENNReal.ofReal (f t)) t := by
      by_cases ht : t ∈ Icc 0 s
      · rw [indicator_of_mem ht, ← ih (sub_nonneg.mpr ht.2)]
        congr 1
        ext y
        change (0 ≤ t ∧ y ∈ scoreSimplex n (s - t)) ↔ y ∈ scoreSimplex n (s - t)
        exact and_iff_right ht.1
      · rw [indicator_of_notMem ht]
        have hempty : Prod.mk t ⁻¹' S = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro y hy
          change 0 ≤ t ∧ (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ s - t at hy
          have hsum : 0 ≤ ∑ i, y i := Finset.sum_nonneg fun i _ ↦ hy.2.1 i
          exact ht ⟨hy.1, by linarith [hy.2.2]⟩
        rw [hempty, measure_empty]
    rw [lintegral_congr hslice, lintegral_indicator measurableSet_Icc]
    have hfi : IntegrableOn f (Icc 0 s) := (by fun_prop : Continuous f).integrableOn_Icc
    rw [← ofReal_integral_eq_lintegral_ofReal hfi
      ((ae_restrict_mem measurableSet_Icc).mono fun t ht ↦ by
        dsimp only [f]
        exact div_nonneg (pow_nonneg (sub_nonneg.mpr ht.2) _) (Nat.cast_nonneg _))]
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hs]
    congr 1
    dsimp only [f]
    rw [intervalIntegral.integral_div, intervalIntegral.integral_comp_sub_left (fun x : ℝ ↦ x ^ n) s, sub_self,
      sub_zero, integral_pow, zero_pow (by omega : n + 1 ≠ 0), sub_zero, Nat.factorial_succ,
      Nat.cast_mul, Nat.cast_succ]
    simp [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm]
end StepA4
end

-- PittelSimplexRadial
section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace StepA4
private noncomputable def spouseAngle {n : ℕ} (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  x i / (∑ j, x j)
theorem measurable_spouseAngle (n : ℕ) : Measurable (@spouseAngle n) :=
  measurable_pi_iff.2 fun i ↦ (measurable_pi_apply i).div
    (Finset.measurable_sum _ fun j _ ↦ measurable_pi_apply j)
private noncomputable def spouseAngularLaw (n : ℕ) : Measure (Fin n → ℝ) :=
  (n.factorial : ℝ≥0∞) • Measure.map spouseAngle (volume.restrict (scoreSimplex n 1))
theorem isProbabilityMeasure_spouseAngularLaw (n : ℕ) :
    IsProbabilityMeasure (spouseAngularLaw n) := by
  refine ⟨?_⟩
  rw [spouseAngularLaw, Measure.smul_apply, Measure.map_apply (measurable_spouseAngle n)
    MeasurableSet.univ, preimage_univ, Measure.restrict_apply_univ,
    volume_scoreSimplex n zero_le_one]
  have hf : (n.factorial : ℝ≥0∞) ≠ 0 := by positivity
  rw [one_pow, one_div, ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_natCast,
    smul_eq_mul, ENNReal.mul_inv_cancel hf (by simp)]
private instance (n : ℕ) : IsProbabilityMeasure (spouseAngularLaw n) :=
  isProbabilityMeasure_spouseAngularLaw n
private noncomputable def spouseRadialLaw (n : ℕ) : Measure ℝ :=
  (volume.restrict (Ioi (0 : ℝ))).withDensity
    (fun s ↦ ENNReal.ofReal (s ^ (n - 1) / ((n - 1).factorial : ℝ)))
private instance (n : ℕ) : SigmaFinite (spouseRadialLaw n) := by
  unfold spouseRadialLaw
  infer_instance
theorem ae_spouseRadialLaw_pos (n : ℕ) :
    ∀ᵐ s ∂(spouseRadialLaw n), 0 < s := by
  exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioi)
private theorem measurable_spouseTotal (n : ℕ) :
    Measurable (fun x : Fin n → ℝ ↦ ∑ i, x i) :=
  Finset.measurable_sum _ fun i _ ↦ measurable_pi_apply i
private theorem measurableSet_spouseOrthant (n : ℕ) :
    MeasurableSet {x : Fin n → ℝ | ∀ i, 0 ≤ x i} := by
  rw [ofPred_forall]
  exact MeasurableSet.iInter fun i ↦ measurableSet_le measurable_const (measurable_pi_apply i)
theorem ae_spouseAngularLaw {n : ℕ} (hn : 0 < n) :
    ∀ᵐ w ∂(spouseAngularLaw n), (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 := by
  have hs0 : volume (scoreSimplex n 0) = 0 := by
    rw [volume_scoreSimplex n le_rfl, zero_pow hn.ne', zero_div, ENNReal.ofReal_zero]
  have hu := ae_restrict_mem (μ := (volume : Measure (Fin n → ℝ)))
    (measurableSet_scoreSimplex n 1)
  have hz : ∀ᵐ x ∂((volume : Measure (Fin n → ℝ)).restrict (scoreSimplex n 1)),
      x ∉ scoreSimplex n 0 := by
    rw [ae_iff]
    change (volume.restrict (scoreSimplex n 1)) {x | ¬ x ∉ scoreSimplex n 0} = 0
    simp only [not_not, ofPred_mem_eq]
    rw [Measure.restrict_apply (measurableSet_scoreSimplex n 0)]
    exact le_antisymm ((measure_mono inter_subset_left).trans_eq hs0) zero_le
  rw [spouseAngularLaw]
  apply Measure.ae_smul_measure
  rw [ae_map_iff (measurable_spouseAngle n).aemeasurable
    (show MeasurableSet {w : Fin n → ℝ | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1} from
      (measurableSet_spouseOrthant n).inter
        (measurableSet_eq_fun (measurable_spouseTotal n) measurable_const))]
  · filter_upwards [hu, hz] with x hx hx0
    have hsum : 0 < ∑ i, x i := lt_of_not_ge fun h ↦ hx0 ⟨hx.1, h⟩
    exact ⟨fun i ↦ div_nonneg (hx.1 i) hsum.le, by
      simp only [spouseAngle, ← Finset.sum_div, div_self hsum.ne']⟩
theorem volume_preimage_spouseScale (n : ℕ) {c : ℝ} (hc : 0 < c)
    {s : Set (Fin n → ℝ)} (hs : MeasurableSet s) :
    volume ((fun (x : Fin n → ℝ) i ↦ c⁻¹ * x i) ⁻¹' s) =
      ENNReal.ofReal (c ^ n) * volume s := by
  let M := Matrix.diagonal (fun _ : Fin n ↦ c⁻¹)
  have hdet : Matrix.det M = (c⁻¹) ^ n := by simp [M]
  have hm : Matrix.det M ≠ 0 := by rw [hdet]; positivity
  have h := Real.map_matrix_volume_pi_eq_smul_volume_pi hm
  have heq : ⇑(Matrix.toLin' M) = fun x i ↦ c⁻¹ * x i := by
    funext x i
    simp [M, Matrix.diagonal_toLin', LinearMap.smul_apply]
  rw [heq, hdet, ← inv_pow, inv_inv, abs_of_nonneg (by positivity)] at h
  rw [← smul_eq_mul, ← Measure.smul_apply, ← h, Measure.map_apply (by fun_prop) hs]
theorem spouseRadialLaw_Iic {n : ℕ} (hn : 0 < n) (u : ℝ) :
    spouseRadialLaw n (Iic u) = ENNReal.ofReal ((max u 0) ^ n / (n.factorial : ℝ)) := by
  rw [spouseRadialLaw, withDensity_apply _ measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Iic]
  have heq : Iic u ∩ Ioi (0 : ℝ) = Ioc 0 u := by ext; simp [and_comm]
  rw [heq]
  by_cases hu : 0 < u
  · rw [max_eq_left hu.le]
    let f : ℝ → ℝ := fun s ↦ s ^ (n - 1) / ((n - 1).factorial : ℝ)
    have hf : Continuous f := by fun_prop
    change (∫⁻ s in Ioc 0 u, ENNReal.ofReal (f s)) = _
    rw [← ofReal_integral_eq_lintegral_ofReal (hf.integrableOn_Icc.mono_set Ioc_subset_Icc_self)]
    · rw [← intervalIntegral.integral_of_le hu.le]
      congr 1
      unfold f
      have hpred : n - 1 + 1 = n := Nat.sub_add_cancel hn
      rw [intervalIntegral.integral_div, integral_pow, hpred, zero_pow hn.ne', sub_zero]
      have hfac : n.factorial = n * (n - 1).factorial := by
        nth_rw 1 [← hpred]
        rw [Nat.factorial_succ, hpred]
      rw [hfac, Nat.cast_mul, div_div]
      have hcast : ((n - 1 : ℕ) : ℝ) + 1 = n := by exact_mod_cast hpred
      rw [hcast]
    · exact (ae_restrict_mem measurableSet_Ioc).mono fun s hs ↦ by
        exact div_nonneg (pow_nonneg hs.1.le _) (Nat.cast_nonneg _)
  · have hu' : u ≤ 0 := le_of_not_gt hu
    simp [Ioc_eq_empty_of_le hu', max_eq_right hu', zero_pow hn.ne']
private def angularSector (n : ℕ) (u : ℝ) (t : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  scoreSimplex n u ∩ spouseAngle ⁻¹' t
private theorem measurableSet_angularSector {n : ℕ} (u : ℝ) {t : Set (Fin n → ℝ)}
    (ht : MeasurableSet t) : MeasurableSet (angularSector n u t) :=
  (measurableSet_scoreSimplex n u).inter (ht.preimage (measurable_spouseAngle n))
private theorem spouseAngle_scale {n : ℕ} (x : Fin n → ℝ) {c : ℝ} (hc : c ≠ 0) :
    spouseAngle (fun i ↦ c * x i) = spouseAngle x := by
  funext i
  simp only [spouseAngle, ← Finset.mul_sum]
  exact mul_div_mul_left _ _ hc
private theorem volume_angularSector {n : ℕ} (u : ℝ) (hu : 0 < u)
    {t : Set (Fin n → ℝ)} (ht : MeasurableSet t) :
    volume (angularSector n u t) =
      ENNReal.ofReal (u ^ n) * volume (angularSector n 1 t) := by
  rw [← volume_preimage_spouseScale n hu (measurableSet_angularSector 1 ht)]
  congr 1
  ext x
  simp only [angularSector, mem_inter_iff, mem_preimage,
    spouseAngle_scale x (inv_ne_zero hu.ne')]
  have hmul : ∀ z : ℝ, u⁻¹ * z ≤ 1 ↔ z ≤ u := fun z ↦ by
    rw [inv_mul_eq_div, div_le_iff₀ hu, one_mul]
  simp only [scoreSimplex, mem_ofPred_eq, ← Finset.mul_sum, hmul]
  have hsign : ∀ z : ℝ, 0 ≤ u⁻¹ * z ↔ 0 ≤ z := fun z ↦
    (mul_nonneg_iff_of_pos_left (inv_pos.mpr hu))
  simp only [hsign]
private theorem spouseAngularLaw_apply {n : ℕ} {t : Set (Fin n → ℝ)} (ht : MeasurableSet t) :
    spouseAngularLaw n t = (n.factorial : ℝ≥0∞) * volume (angularSector n 1 t) := by
  rw [spouseAngularLaw, Measure.smul_apply, Measure.map_apply (measurable_spouseAngle n) ht,
    Measure.restrict_apply (ht.preimage (measurable_spouseAngle n))]
  simp only [smul_eq_mul, angularSector, inter_comm]
private theorem volume_angularSector_eq_mul {n : ℕ} (hn : 0 < n) (u : ℝ)
    {t : Set (Fin n → ℝ)} (ht : MeasurableSet t) :
    volume (angularSector n u t) = spouseRadialLaw n (Iic u) * spouseAngularLaw n t := by
  rw [spouseRadialLaw_Iic hn, spouseAngularLaw_apply ht]
  by_cases hu : 0 < u
  · rw [max_eq_left hu.le, volume_angularSector u hu ht, ← mul_assoc]
    congr 1
    have hnR' : (0 : ℝ) < n.factorial := by positivity
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
      div_mul_cancel₀ _ hnR'.ne']
  · have hu' : u ≤ 0 := le_of_not_gt hu
    have hsub : angularSector n u t ⊆ scoreSimplex n 0 :=
      fun _ hx ↦ ⟨hx.1.1, hx.1.2.trans hu'⟩
    have h0 : volume (scoreSimplex n 0) = 0 := by
      rw [volume_scoreSimplex n le_rfl, zero_pow hn.ne', zero_div, ENNReal.ofReal_zero]
    simp only [max_eq_right hu', zero_pow hn.ne', zero_div, ENNReal.ofReal_zero, zero_mul]
    exact le_antisymm ((measure_mono hsub).trans_eq h0) zero_le
private def angularRay {n : ℕ} (t : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {x | ∀ i, 0 ≤ x i} ∩ spouseAngle ⁻¹' t
private theorem measure_angularRay_radius {n : ℕ} (hn : 0 < n)
    {t : Set (Fin n → ℝ)} (ht : MeasurableSet t) :
    Measure.map (fun x : Fin n → ℝ ↦ ∑ i, x i) (volume.restrict (angularRay t)) =
      spouseAngularLaw n t • spouseRadialLaw n := by
  let μ := Measure.map (fun x : Fin n → ℝ ↦ ∑ i, x i) (volume.restrict (angularRay t))
  let ν := spouseAngularLaw n t • spouseRadialLaw n
  have hμ (u : ℝ) : μ (Iic u) = volume (angularSector n u t) := by
    change (Measure.map (fun x : Fin n → ℝ ↦ ∑ i, x i)
      (volume.restrict (angularRay t))) (Iic u) = _
    rw [Measure.map_apply (measurable_spouseTotal n) measurableSet_Iic,
      Measure.restrict_apply (measurableSet_Iic.preimage (measurable_spouseTotal n))]
    congr 1
    ext x
    simp only [angularRay, angularSector, scoreSimplex, mem_inter_iff, mem_preimage,
      mem_Iic, mem_ofPred_eq]
    tauto
  have hcdf (u : ℝ) : μ (Iic u) = ν (Iic u) := by
    change μ (Iic u) = (spouseAngularLaw n t • spouseRadialLaw n) (Iic u)
    rw [hμ, volume_angularSector_eq_mul hn u ht, Measure.smul_apply, smul_eq_mul, mul_comm]
  have hfin (u : ℝ) : μ (Iic u) ≠ ∞ := by
    rw [hμ]
    exact ne_top_of_le_ne_top (by rw [volume_scoreSimplex n (le_max_right u 0)]; simp)
      (measure_mono fun x hx ↦ ⟨hx.1.1, hx.1.2.trans (le_max_left u 0)⟩ :
        volume (angularSector n u t) ≤ volume (scoreSimplex n (max u 0)))
  apply Measure.ext_of_Ioc' μ ν
  · intro a b _
    exact ne_top_of_le_ne_top (hfin b) (measure_mono fun _ hx ↦ hx.2)
  · intro a b hab
    have hν (u : ℝ) : ν (Iic u) ≠ ∞ := hcdf u ▸ hfin u
    rw [← show Iic b \ Iic a = Ioc a b by ext x; simp [and_comm],
      measure_sdiff (Iic_subset_Iic.mpr hab.le)
      measurableSet_Iic.nullMeasurableSet (hfin a),
      measure_sdiff (Iic_subset_Iic.mpr hab.le) measurableSet_Iic.nullMeasurableSet (hν a),
      hcdf a, hcdf b]
private theorem measure_map_spouseRadialAngular {n : ℕ} (hn : 0 < n) :
    Measure.map (fun x : Fin n → ℝ ↦ (∑ i, x i, spouseAngle x))
      (volume.restrict {x : Fin n → ℝ | ∀ i, 0 ≤ x i}) =
      (spouseRadialLaw n).prod (spouseAngularLaw n) := by
  symm
  apply Measure.prod_eq
  intro s t hs ht
  have hmeas : Measurable (fun x : Fin n → ℝ ↦ (∑ i, x i, spouseAngle x)) :=
    (measurable_spouseTotal n).prodMk (measurable_spouseAngle n)
  rw [Measure.map_apply hmeas (hs.prod ht), Measure.restrict_apply ((hs.prod ht).preimage hmeas)]
  rw [← mul_comm, ← smul_eq_mul, ← Measure.smul_apply, ← measure_angularRay_radius hn ht,
    Measure.map_apply (measurable_spouseTotal n) hs,
    Measure.restrict_apply (hs.preimage (measurable_spouseTotal n))]
  congr 1
  ext x
  simp only [mem_inter_iff, mem_preimage, mem_prod, mem_ofPred_eq, angularRay]
  tauto
theorem lintegral_spouseRadialAngular {n : ℕ} (hn : 0 < n)
    {f : (Fin n → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x, f x ∂(volume.restrict {x | ∀ i, 0 ≤ x i})) =
      ∫⁻ s, ∫⁻ w, f (fun i ↦ s * w i) ∂(spouseAngularLaw n) ∂(spouseRadialLaw n) := by
  let decode : ℝ × (Fin n → ℝ) → (Fin n → ℝ) := fun p i ↦ p.1 * p.2 i
  have hdecode : Measurable decode := by unfold decode; fun_prop
  have hpair : Measurable (fun x : Fin n → ℝ ↦ (∑ i, x i, spouseAngle x)) :=
    (measurable_spouseTotal n).prodMk (measurable_spouseAngle n)
  rw [← lintegral_prod (fun p ↦ f (decode p)) (hf.comp hdecode).aemeasurable,
    ← measure_map_spouseRadialAngular hn]
  change _ = ∫⁻ z, (f ∘ decode) z ∂(Measure.map (fun x : Fin n → ℝ ↦
    (∑ i, x i, spouseAngle x)) (volume.restrict {x | ∀ i, 0 ≤ x i}))
  rw [lintegral_map (hf.comp hdecode) hpair]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem (μ := (volume : Measure (Fin n → ℝ)))
    (measurableSet_spouseOrthant n)] with x hx
  congr 1
  funext i
  change x i = (∑ j, x j) * (x i / ∑ j, x j)
  by_cases h : (∑ j, x j) = 0
  · have hle : x i ≤ ∑ j, x j :=
      Finset.single_le_sum (fun j _ ↦ hx j) (Finset.mem_univ i)
    rw [h, zero_mul]
    exact le_antisymm (h ▸ hle) (hx i)
  · field_simp
end StepA4
end

-- PittelSimplexMoments
section
open Filter MeasureTheory Set
open scoped ENNReal BigOperators Topology
namespace StepA4
section Moments
variable {n : ℕ} {μ : Measure (Fin n → ℝ)} [IsProbabilityMeasure μ]
variable (hμ : ∀ᵐ w ∂μ, ∀ i, w i ∈ Icc (0 : ℝ) 1)
variable (hmoment : ∀ a : Fin n → ℕ, (∫ w, ∏ i, w i ^ a i ∂μ) =
  (∏ i, ((a i).factorial : ℝ)) * ((n - 1).factorial : ℝ) /
    ((n - 1 + ∑ i, a i).factorial : ℝ))
end Moments
end StepA4
end

-- ExponentialSpouseSquareTail
section
open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal Topology
namespace StepA4
local instance : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
  isProbabilityMeasure_expMeasure (by norm_num)
private noncomputable def iidExponentialScoreLaw (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi fun _ ↦ expMeasure 1
end StepA4
end

-- ExponentialSpouseAngles
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace StepA4
private theorem pi_withDensity_product_of_sigmaFinite {ι : Type*} [Fintype ι]
    {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    (ν : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (ν i)]
    (f : ∀ i, Ω i → ℝ≥0∞) (hf : ∀ i, Measurable (f i))
    [∀ i, SigmaFinite ((ν i).withDensity (f i))] :
    (Measure.pi ν).withDensity (fun x ↦ ∏ i, f i (x i)) =
      Measure.pi (fun i ↦ (ν i).withDensity (f i)) := by
  classical
  symm
  apply Measure.pi_eq
  intro s hs
  let g (i : ι) := (s i).indicator (f i)
  have hg (i : ι) : Measurable (g i) := (hf i).indicator (hs i)
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator
    (MeasurableSet.univ_pi hs)]
  calc
    _ = ∫⁻ x, ∏ i, g i (x i) ∂Measure.pi ν := by
      apply lintegral_congr
      intro x
      by_cases hx : x ∈ univ.pi s
      · rw [indicator_of_mem hx]
        exact Finset.prod_congr rfl fun i _ ↦
          (indicator_of_mem (mem_univ_pi.mp hx i) (f i)).symm
      · obtain ⟨i, hi⟩ := not_forall.mp (mt mem_univ_pi.mpr hx)
        rw [indicator_of_notMem hx]
        exact (Finset.prod_eq_zero (Finset.mem_univ i) (indicator_of_notMem hi (f i))).symm
    _ = ∏ i, ∫⁻ x : ∀ j, Ω j, g i (x i) ∂Measure.pi ν :=
      lintegral_prod_eq_prod_lintegral_of_indepFun _ _
        (iIndepFun_pi fun i ↦ (hg i).aemeasurable)
        (fun i ↦ (hg i).comp (measurable_pi_apply i))
    _ = _ := by
      refine Finset.prod_congr rfl fun i _ ↦ ?_
      rw [(measurePreserving_eval ν i).lintegral_comp (hg i), withDensity_apply _ (hs i)]
      exact lintegral_indicator (hs i) (f i)
private theorem expMeasure_one_eq_withDensity_Ici :
    expMeasure 1 =
      (volume.restrict (Ici 0)).withDensity (fun x ↦ ENNReal.ofReal (Real.exp (-x))) := by
  rw [expMeasure, gammaMeasure, ← withDensity_indicator measurableSet_Ici]
  congr 1
  funext x
  change exponentialPDF 1 x = _
  rw [exponentialPDF_eq]
  by_cases hx : 0 ≤ x <;> simp [hx]
private theorem ofReal_exp_mul_ofReal_exp_neg (x : ℝ) :
    ENNReal.ofReal (Real.exp x) * ENNReal.ofReal (Real.exp (-x)) = 1 := by
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add, add_neg_cancel,
    Real.exp_zero, ENNReal.ofReal_one]
private theorem expMeasure_one_withDensity_exp :
    (expMeasure 1).withDensity (fun x ↦ ENNReal.ofReal (Real.exp x)) =
      volume.restrict (Ici 0) := by
  rw [expMeasure_one_eq_withDensity_Ici, ← withDensity_mul _ (by fun_prop) (by fun_prop)]
  have h : (fun x : ℝ ↦ ENNReal.ofReal (Real.exp (-x))) *
      (fun x ↦ ENNReal.ofReal (Real.exp x)) = 1 := by
    funext x
    exact (mul_comm _ _).trans (ofReal_exp_mul_ofReal_exp_neg x)
  rw [h, withDensity_one]
theorem pi_expMeasure_one_eq_withDensity_spouseOrthant (n : ℕ) :
    Measure.pi (fun _ : Fin n ↦ expMeasure 1) =
      (volume.restrict {x : Fin n → ℝ | ∀ i, 0 ≤ x i}).withDensity
        (fun x ↦ ENNReal.ofReal (Real.exp (-(∑ i, x i)))) := by
  let ν : Fin n → Measure ℝ := fun _ ↦ expMeasure 1
  let f : ℝ → ℝ≥0∞ := fun x ↦ ENNReal.ofReal (Real.exp x)
  let hν : ∀ i, IsProbabilityMeasure (ν i) := fun _ ↦
    isProbabilityMeasure_expMeasure (by norm_num)
  let hσ : ∀ i, SigmaFinite ((ν i).withDensity f) := fun _ ↦
    expMeasure_one_withDensity_exp.symm ▸ inferInstance
  have hf : Measurable f := by fun_prop
  have hsum : Measurable (fun x : Fin n → ℝ ↦ ∑ i, x i) :=
    Finset.measurable_sum _ fun i _ ↦ measurable_pi_apply i
  have hprod : (fun x : Fin n → ℝ ↦ ∏ i, f (x i)) =
      (fun x ↦ ENNReal.ofReal (Real.exp (∑ i, x i))) := by
    funext x
    rw [Real.exp_sum, ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ Real.exp_nonneg _)]
  have hbox : (univ.pi fun _ : Fin n ↦ Ici (0 : ℝ)) = {x : Fin n → ℝ | ∀ i, 0 ≤ x i} := by
    ext x
    exact Set.mem_univ_pi
  have htilt : (Measure.pi ν).withDensity (fun x ↦ ENNReal.ofReal (Real.exp (∑ i, x i))) =
      volume.restrict {x : Fin n → ℝ | ∀ i, 0 ≤ x i} := by
    have hpi := @pi_withDensity_product_of_sigmaFinite _ _ _ _ ν hν (fun _ ↦ f) (fun _ ↦ hf) hσ
    rw [← hprod, hpi, ← hbox, volume_pi, Measure.restrict_pi_pi]
    exact congrArg Measure.pi (funext fun _ ↦ expMeasure_one_withDensity_exp)
  rw [← htilt, ← withDensity_mul _ (by fun_prop) (by fun_prop)]
  have h : (fun x : Fin n → ℝ ↦ ENNReal.ofReal (Real.exp (∑ i, x i))) *
      (fun x ↦ ENNReal.ofReal (Real.exp (-(∑ i, x i)))) = 1 := by
    funext x
    exact ofReal_exp_mul_ofReal_exp_neg _
  rw [h, withDensity_one]
private theorem map_spouseAngle_pi_expMeasure_one_apply {n : ℕ} (hn : 0 < n)
    {A : Set (Fin n → ℝ)} (hA : MeasurableSet A) :
    Measure.map spouseAngle (Measure.pi (fun _ : Fin n ↦ expMeasure 1)) A =
      (∫⁻ s, ENNReal.ofReal (Real.exp (-s)) ∂spouseRadialLaw n) * spouseAngularLaw n A := by
  let E : Set (Fin n → ℝ) := spouseAngle ⁻¹' A
  let F : (Fin n → ℝ) → ℝ≥0∞ :=
    E.indicator (fun x ↦ ENNReal.ofReal (Real.exp (-(∑ i, x i))))
  have hE : MeasurableSet E := hA.preimage (measurable_spouseAngle n)
  have hsum : Measurable (fun x : Fin n → ℝ ↦ ∑ i, x i) :=
    Finset.measurable_sum _ fun i _ ↦ measurable_pi_apply i
  have hF : Measurable F :=
    (hsum.neg.exp.ennreal_ofReal).indicator hE
  calc
    _ = ∫⁻ x, F x ∂(volume.restrict {x : Fin n → ℝ | ∀ i, 0 ≤ x i}) := by
      rw [Measure.map_apply (measurable_spouseAngle n) hA,
        pi_expMeasure_one_eq_withDensity_spouseOrthant, withDensity_apply _ hE,
        ← lintegral_indicator hE]
    _ = ∫⁻ s, ∫⁻ w, F (fun i ↦ s * w i) ∂spouseAngularLaw n ∂spouseRadialLaw n :=
      lintegral_spouseRadialAngular hn hF
    _ = ∫⁻ s, ENNReal.ofReal (Real.exp (-s)) * spouseAngularLaw n A ∂spouseRadialLaw n := by
      apply lintegral_congr_ae
      filter_upwards [ae_spouseRadialLaw_pos n] with s hs
      calc
        _ = ∫⁻ w, ENNReal.ofReal (Real.exp (-s)) * A.indicator 1 w ∂spouseAngularLaw n := by
          apply lintegral_congr_ae
          filter_upwards [ae_spouseAngularLaw hn] with w hw
          have htotal : (∑ i, s * w i) = s := by
            rw [← Finset.mul_sum, hw.2, mul_one]
          have hangle : spouseAngle (fun i ↦ s * w i) = w := by
            funext i
            unfold spouseAngle
            rw [htotal, mul_div_cancel_left₀ _ hs.ne']
          by_cases hwA : w ∈ A
          · have hmem : (fun i ↦ s * w i) ∈ E := by
              change spouseAngle (fun i ↦ s * w i) ∈ A
              rwa [hangle]
            simp [F, indicator_of_mem hmem, indicator_of_mem hwA, htotal]
          · have hmem : (fun i ↦ s * w i) ∉ E := by
              change spouseAngle (fun i ↦ s * w i) ∉ A
              rwa [hangle]
            simp [F, indicator_of_notMem hmem, indicator_of_notMem hwA]
        _ = _ := by
          have hI : Measurable (A.indicator (1 : (Fin n → ℝ) → ℝ≥0∞)) :=
            measurable_const.indicator hA
          rw [lintegral_const_mul _ hI, lintegral_indicator_one hA]
    _ = _ := lintegral_mul_const _ (by fun_prop)
theorem map_spouseAngle_pi_expMeasure_one {n : ℕ} (hn : 0 < n) :
    Measure.map spouseAngle (Measure.pi (fun _ : Fin n ↦ expMeasure 1)) = spouseAngularLaw n := by
  let (_i : Fin n) : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  have htotal := map_spouseAngle_pi_expMeasure_one_apply hn (A := univ) MeasurableSet.univ
  rw [Measure.map_apply (measurable_spouseAngle n) MeasurableSet.univ, preimage_univ,
    measure_univ, measure_univ, mul_one] at htotal
  ext1 A hA
  rw [map_spouseAngle_pi_expMeasure_one_apply hn hA, ← htotal, one_mul]
end StepA4
end

-- CoexposureScoreRow
section
open Set
open scoped BigOperators
namespace StepA4
variable {ι : Type*}
private noncomputable def scoreRowKernel (J : Finset ι) (y : ι → ℝ) (x : ℝ) : ℝ :=
  ∏ j ∈ J, (1 - x * y j)
private noncomputable def scoreRowMass (J : Finset ι) (y : ι → ℝ) (a b : ℝ) : ℝ :=
  ∫ x in a..b, scoreRowKernel J y x
theorem continuous_scoreRowKernel (J : Finset ι) (y : ι → ℝ) :
    Continuous (scoreRowKernel J y) := by
  unfold scoreRowKernel
  fun_prop
private theorem scoreRowKernel_nonneg {J : Finset ι} {y : ι → ℝ}
    (hy₀ : ∀ j ∈ J, 0 ≤ y j) (hy₁ : ∀ j ∈ J, y j ≤ 1)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    0 ≤ scoreRowKernel J y x := by
  unfold scoreRowKernel
  exact Finset.prod_nonneg fun j hj ↦ sub_nonneg.mpr (calc
    x * y j ≤ 1 * y j := mul_le_mul_of_nonneg_right hx.2 (hy₀ j hj)
    _ ≤ 1 := by simpa using hy₁ j hj)
theorem scoreRowKernel_le_exp {J : Finset ι} {y : ι → ℝ}
    (hy₀ : ∀ j ∈ J, 0 ≤ y j) (hy₁ : ∀ j ∈ J, y j ≤ 1)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    scoreRowKernel J y x ≤ Real.exp (-(∑ j ∈ J, y j) * x) := by
  unfold scoreRowKernel
  rw [show -(∑ j ∈ J, y j) * x = ∑ j ∈ J, -(x * y j) by
    calc
      -(∑ j ∈ J, y j) * x = -(x * ∑ j ∈ J, y j) := by ring
      _ = _ := by rw [Finset.mul_sum, Finset.sum_neg_distrib], Real.exp_sum]
  exact Finset.prod_le_prod
    (fun j hj ↦ sub_nonneg.mpr (calc
      x * y j ≤ 1 * y j := mul_le_mul_of_nonneg_right hx.2 (hy₀ j hj)
      _ ≤ 1 := by simpa using hy₁ j hj))
    (fun j _ ↦ Real.one_sub_le_exp_neg _)
private theorem integral_exp_neg_mul {r a b : ℝ} (hr : 0 < r) :
    (∫ x in a..b, Real.exp (-r * x)) = (Real.exp (-r * a) - Real.exp (-r * b)) / r := by
  have hderiv (x : ℝ) :
      HasDerivAt (fun z ↦ -(Real.exp (-r * z)) / r) (Real.exp (-r * x)) x := by
    exact (((Real.hasDerivAt_exp (-r * x)).comp x
      (hasDerivAt_const_mul (-r))).neg.div_const r).congr_deriv (by field_simp)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ ↦ hderiv x)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  ring
theorem scoreRowMass_le_exp_tail {J : Finset ι} {y : ι → ℝ}
    (hy₀ : ∀ j ∈ J, 0 ≤ y j) (hy₁ : ∀ j ∈ J, y j ≤ 1)
    {r a b : ℝ} (hr : 0 < r) (hrsum : r ≤ ∑ j ∈ J, y j)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    scoreRowMass J y a b ≤ Real.exp (-r * a) / r := by
  calc
    scoreRowMass J y a b ≤ ∫ x in a..b, Real.exp (-r * x) := by
      unfold scoreRowMass
      refine intervalIntegral.integral_mono_on hab
        ((continuous_scoreRowKernel J y).intervalIntegrable _ _)
        (Continuous.intervalIntegrable (by fun_prop) _ _) fun x hx ↦ ?_
      have hx' : x ∈ Icc (0 : ℝ) 1 := ⟨ha.trans hx.1, hx.2.trans hb⟩
      exact (scoreRowKernel_le_exp hy₀ hy₁ hx').trans (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right (neg_le_neg hrsum) hx'.1))
    _ = (Real.exp (-r * a) - Real.exp (-r * b)) / r := integral_exp_neg_mul hr
    _ ≤ Real.exp (-r * a) / r :=
      div_le_div_of_nonneg_right (sub_le_self _ (Real.exp_pos _).le) hr.le
theorem scoreRowMass_le_finite_exp {J : Finset ι} {y : ι → ℝ}
    (hy₀ : ∀ j ∈ J, 0 ≤ y j) (hy₁ : ∀ j ∈ J, y j ≤ 1)
    {s c : ℝ} (hs : 0 < s) (hc : 0 ≤ c) (hsum : s - c ≤ ∑ j ∈ J, y j) :
    scoreRowMass J y 0 1 ≤ Real.exp c * ((1 - Real.exp (-s)) / s) := by
  calc
    scoreRowMass J y 0 1 ≤ ∫ x in (0 : ℝ)..1, Real.exp c * Real.exp (-s * x) := by
      unfold scoreRowMass
      refine intervalIntegral.integral_mono_on (by norm_num)
        ((continuous_scoreRowKernel J y).intervalIntegrable _ _)
        (Continuous.intervalIntegrable (by fun_prop) _ _) fun x hx ↦ ?_
      refine (scoreRowKernel_le_exp hy₀ hy₁ hx).trans ?_
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h₁ := mul_le_mul_of_nonneg_right (neg_le_neg hsum) hx.1
      have h₂ := mul_le_mul_of_nonneg_left hx.2 hc
      nlinarith only [h₁, h₂]
    _ = _ := by rw [intervalIntegral.integral_const_mul, integral_exp_neg_mul hs]; simp
section FiniteRows
variable [Fintype ι] [DecidableEq ι]
private theorem sum_erase_eq_total_sub (y : ι → ℝ) (i : ι) :
    ∑ j ∈ Finset.univ.erase i, y j = (∑ j, y j) - y i := by
  linarith only [Finset.sum_erase_add Finset.univ y (Finset.mem_univ i)]
theorem scoreRowMass_erase_le_inv (y : ι → ℝ) (i : ι)
    (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) (hs : 2 ≤ ∑ j, y j) :
    scoreRowMass (Finset.univ.erase i) y 0 1 ≤ 1 / ((∑ j, y j) - y i) := by
  have hr : 0 < (∑ j, y j) - y i := by linarith [(hy i).2]
  simpa using scoreRowMass_le_exp_tail
    (J := Finset.univ.erase i) (y := y)
    (fun j _ ↦ (hy j).1) (fun j _ ↦ (hy j).2) hr
    (sum_erase_eq_total_sub y i).ge le_rfl (by norm_num) le_rfl
theorem scoreRowMass_erase_le_finite_exp (y : ι → ℝ) (i : ι)
    (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) (hs : 0 < ∑ j, y j) :
    scoreRowMass (Finset.univ.erase i) y 0 1 ≤
      Real.exp (y i) * ((1 - Real.exp (-(∑ j, y j))) / (∑ j, y j)) :=
  scoreRowMass_le_finite_exp (fun j _ ↦ (hy j).1) (fun j _ ↦ (hy j).2)
    hs (hy i).1 (sum_erase_eq_total_sub y i).ge
theorem scoreRowMass_prod_le_finite_exp (y : ι → ℝ)
    (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) (hs : 0 < ∑ j, y j) :
    (∏ i, scoreRowMass (Finset.univ.erase i) y 0 1) ≤
      Real.exp (∑ j, y j) * ((1 - Real.exp (-(∑ j, y j))) / (∑ j, y j)) ^
        Fintype.card ι := by
  calc
    _ ≤ ∏ i, Real.exp (y i) * ((1 - Real.exp (-(∑ j, y j))) / (∑ j, y j)) :=
      Finset.prod_le_prod (fun _ _ ↦ intervalIntegral.integral_nonneg (by norm_num)
        fun _ hx ↦ scoreRowKernel_nonneg (fun j _ ↦ (hy j).1) (fun j _ ↦ (hy j).2) hx)
        (fun i _ ↦ scoreRowMass_erase_le_finite_exp y i hy hs)
    _ = _ := by rw [Finset.prod_mul_distrib, ← Real.exp_sum, Finset.prod_const,
      Finset.card_univ]
theorem scoreRowMass_prod_le_inv_pow (y : ι → ℝ)
    (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) (hs : 2 ≤ ∑ j, y j) :
    (∏ i, scoreRowMass (Finset.univ.erase i) y 0 1) ≤
      Real.exp 2 / (∑ j, y j) ^ Fintype.card ι := by
  let s := ∑ j, y j
  have hs₀ : 0 < s := by dsimp [s]; linarith
  have hi (i : ι) : 1 / (s - y i) ≤ Real.exp (2 * (y i / s)) / s := by
    let z := y i / s
    have hz₀ : 0 ≤ z := div_nonneg (hy i).1 hs₀.le
    have hz₁ : z ≤ 1 / 2 := by
      dsimp [z]
      rw [div_le_iff₀ hs₀]
      dsimp [s]
      linarith [(hy i).2]
    have hprod : 1 ≤ (1 + 2 * z) * (1 - z) := by
      have hmul := mul_nonneg hz₀ (show 0 ≤ 1 - 2 * z by linarith)
      nlinarith only [hmul]
    have hlinear : 1 + 2 * z ≤ Real.exp (2 * z) := by
      simpa only [add_comm] using Real.add_one_le_exp (2 * z)
    have hexp : 1 ≤ Real.exp (2 * z) * (1 - z) :=
      hprod.trans (mul_le_mul_of_nonneg_right hlinear (by linarith))
    have hsi : 0 < s - y i := by dsimp [s]; linarith [(hy i).2]
    have heq : (s - y i) / s = 1 - z := by rw [sub_div, div_self hs₀.ne']
    rw [div_le_div_iff₀ hsi hs₀, one_mul]
    calc
      s = 1 * s := (one_mul s).symm
      _ ≤ Real.exp (2 * (y i / s)) * (s - y i) := (le_div_iff₀ hs₀).mp (by
        change 1 ≤ (Real.exp (2 * z) * (s - y i)) / s
        rw [mul_div_assoc, heq]
        exact hexp)
  calc
    _ ≤ ∏ i, Real.exp (2 * (y i / s)) / s :=
      Finset.prod_le_prod (fun _ _ ↦ intervalIntegral.integral_nonneg (by norm_num)
        fun _ hx ↦ scoreRowKernel_nonneg (fun j _ ↦ (hy j).1) (fun j _ ↦ (hy j).2) hx)
        (fun i _ ↦ (scoreRowMass_erase_le_inv y i hy hs).trans (hi i))
    _ = _ := by
      rw [Finset.prod_div_distrib, ← Real.exp_sum, ← Finset.mul_sum, ← Finset.sum_div]
      simp [show (∑ j, y j) / s = 1 by dsimp [s]; exact div_self hs₀.ne']
      rfl
end FiniteRows
section SuccessorMass
open MeasureTheory
open scoped ENNReal
end SuccessorMass
end StepA4
end

-- ExposedRotations
section
open StableMarriage
namespace StepA4
variable {n : ℕ}
private def IsEligibleSuccessor (p : Profile n) (μ : Matching n) (m w : Fin n) : Prop :=
  p.manRank m (μ m) < p.manRank m w ∧ p.womanRank w m < p.womanRank w (μ.symm w)
private abbrev premiseOf {A B : Prop} (_ : A → B) := A
private abbrev IsSuccessor (p : Profile n) (μ : Matching n) (m w : Fin n) : Prop :=
  premiseOf (@MarkedLP.IsSuccessor.unique n p μ m w w)
private theorem IsSuccessor.mk {p : Profile n} {μ : Matching n} {m w : Fin n}
    (h₁ : IsEligibleSuccessor p μ m w)
    (h₂ : ∀ w', IsEligibleSuccessor p μ m w' → p.manRank m w ≤ p.manRank m w') :
    IsSuccessor p μ m w := by
  constructor
  · exact h₁
  · exact h₂
private theorem IsSuccessor.eligible {p : Profile n} {μ : Matching n} {m w : Fin n}
    (h : IsSuccessor p μ m w) : IsEligibleSuccessor p μ m w := by
  obtain ⟨h₁, _⟩ := h
  exact h₁
private theorem IsSuccessor.min_rank {p : Profile n} {μ : Matching n} {m w : Fin n}
    (h : IsSuccessor p μ m w) :
    ∀ w', IsEligibleSuccessor p μ m w' → p.manRank m w ≤ p.manRank m w' := by
  obtain ⟨_, h₂⟩ := h
  exact h₂
private abbrev IsExposedRotation (p : Profile n) (μ : Matching n) (ρ : Equiv.Perm (Fin n)) : Prop :=
  premiseOf (@MarkedLP.IsExposedRotation.womanRank_eliminate_le n p μ ρ)
private theorem IsExposedRotation.mk {p : Profile n} {μ : Matching n} {ρ : Equiv.Perm (Fin n)}
    (h₁ : ρ.IsCycle) (h₂ : ∀ m, ρ m ≠ m → IsSuccessor p μ m (μ (ρ m))) :
    IsExposedRotation p μ ρ := by
  constructor
  · exact h₁
  · exact h₂
private theorem IsExposedRotation.isCycle {p : Profile n} {μ : Matching n} {ρ : Equiv.Perm (Fin n)}
    (h : IsExposedRotation p μ ρ) : ρ.IsCycle := by
  obtain ⟨h₁, _⟩ := h
  exact h₁
private theorem IsExposedRotation.successor {p : Profile n} {μ : Matching n} {ρ : Equiv.Perm (Fin n)}
    (h : IsExposedRotation p μ ρ) : ∀ m, ρ m ≠ m → IsSuccessor p μ m (μ (ρ m)) := by
  obtain ⟨_, h₂⟩ := h
  exact h₂
private def eliminateRotation (μ : Matching n) (ρ : Equiv.Perm (Fin n)) : Matching n :=
  ρ.trans μ
@[simp] theorem eliminateRotation_apply (μ : Matching n) (ρ : Equiv.Perm (Fin n)) (m : Fin n) :
    eliminateRotation μ ρ m = μ (ρ m) := rfl
variable {p : Profile n} {μ : Matching n} {ρ : Equiv.Perm (Fin n)}
theorem IsSuccessor.unique {m w w' : Fin n}
    (h : IsSuccessor p μ m w) (h' : IsSuccessor p μ m w') : w = w' :=
  (p.manRank m).injective <| le_antisymm ((IsSuccessor.min_rank h) w' (IsSuccessor.eligible h')) ((IsSuccessor.min_rank h') w (IsSuccessor.eligible h))
theorem IsExposedRotation.manRank_lt_eliminate_of_moved (hρ : IsExposedRotation p μ ρ)
    {m : Fin n} (hm : ρ m ≠ m) :
    p.manRank m (μ m) < p.manRank m (eliminateRotation μ ρ m) :=
  (IsSuccessor.eligible ((IsExposedRotation.successor hρ) m hm)).1
theorem IsExposedRotation.womanRank_eliminate_le (hρ : IsExposedRotation p μ ρ) (w : Fin n) :
    p.womanRank w ((eliminateRotation μ ρ).symm w) ≤ p.womanRank w (μ.symm w) :=
  let ⟨m, hm⟩ := (eliminateRotation μ ρ).surjective w
  have hle : p.womanRank (μ (ρ m)) m ≤ p.womanRank (μ (ρ m)) (ρ m) :=
    if h : ρ m = m then
      (congrArg (p.womanRank (μ (ρ m))) h.symm).le
    else by
      simpa only [Equiv.symm_apply_apply] using (IsSuccessor.eligible ((IsExposedRotation.successor hρ) m h)).2.le
  have htarget : p.womanRank (eliminateRotation μ ρ m)
        ((eliminateRotation μ ρ).symm (eliminateRotation μ ρ m)) ≤
      p.womanRank (eliminateRotation μ ρ m) (μ.symm (eliminateRotation μ ρ m)) := by
    have hinv : (eliminateRotation μ ρ).symm (μ (ρ m)) = m :=
      (eliminateRotation μ ρ).symm_apply_apply m
    simpa only [eliminateRotation_apply, hinv, Equiv.symm_apply_apply] using hle
  hm ▸ htarget
theorem IsExposedRotation.isStable_eliminate (hρ : IsExposedRotation p μ ρ)
    (hμ : IsStable p μ) : IsStable p (eliminateRotation μ ρ) :=
  fun m w hb ↦
    have hwOld : p.womanRank w m < p.womanRank w (μ.symm w) :=
      hb.2.2.trans_le (hρ.womanRank_eliminate_le w)
    have hne : μ m ≠ w := fun h ↦ (ne_of_lt hwOld)
      (congrArg (p.womanRank w) ((μ.symm_apply_apply m).symm.trans (congrArg μ.symm h)))
    have hnot : ¬ p.manRank m w < p.manRank m (μ m) := fun h ↦
      hμ m w ⟨hne, h, hwOld⟩
    if hm : ρ m = m then
      hnot (by simpa only [eliminateRotation_apply, hm] using hb.2.1)
    else
      have hbelow : p.manRank m (μ m) < p.manRank m w :=
        lt_of_le_of_ne (le_of_not_gt hnot) (fun he ↦ hne ((p.manRank m).injective he))
      (not_lt_of_ge ((IsSuccessor.min_rank ((IsExposedRotation.successor hρ) m hm)) w ⟨hbelow, hwOld⟩)) hb.2.1
end StepA4
end

-- CoexposureScoreProduct
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA4
private abbrev ScorePairIndex (n : ℕ) := Fin n × Fin n
private abbrev DiagonalScorePairs (n : ℕ) := {q : ScorePairIndex n // q.1 = q.2} → ℝ × ℝ
private abbrev OffDiagonalScorePairs (n : ℕ) := {q : ScorePairIndex n // q.1 ≠ q.2} → ℝ × ℝ
private noncomputable def unitScorePairLaw : Measure (ℝ × ℝ) :=
  unitScoreLaw.prod unitScoreLaw
private instance : IsProbabilityMeasure unitScorePairLaw :=
  inferInstanceAs (IsProbabilityMeasure (unitScoreLaw.prod unitScoreLaw))
private noncomputable def diagonalScoreLaw (n : ℕ) : Measure (DiagonalScorePairs n) :=
  Measure.pi fun _ ↦ unitScorePairLaw
private noncomputable def offDiagonalScoreLaw (n : ℕ) : Measure (OffDiagonalScorePairs n) :=
  Measure.pi fun _ ↦ unitScorePairLaw
private instance (n : ℕ) : IsProbabilityMeasure (offDiagonalScoreLaw n) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : {q : ScorePairIndex n // q.1 ≠ q.2} ↦
    unitScorePairLaw))
private theorem measurePreserving_scoreUncurry (n : ℕ) :
    MeasurePreserving (MeasurableEquiv.curry (Fin n) (Fin n) ℝ).symm
      (Measure.pi fun _ : Fin n ↦ Measure.pi fun _ : Fin n ↦ unitScoreLaw)
      (Measure.pi fun _ : ScorePairIndex n ↦ unitScoreLaw) := by
  refine ⟨(MeasurableEquiv.curry (Fin n) (Fin n) ℝ).symm.measurable, ?_⟩
  refine (Measure.pi_eq fun s hs ↦ ?_).symm
  rw [MeasurableEquiv.map_apply]
  rw [show (MeasurableEquiv.curry (Fin n) (Fin n) ℝ).symm ⁻¹' (Set.univ.pi s) =
      Set.univ.pi (fun i ↦ Set.univ.pi fun j ↦ s (i,j)) by
    ext x
    simp [Set.mem_pi, Prod.forall]]
  simp_rw [Measure.pi_pi]
  rw [← Finset.prod_product']
  simp
private def manScoreIndex {n : ℕ} (μ : Matching n) : ScorePairIndex n ≃ ScorePairIndex n :=
  Equiv.prodCongr (Equiv.refl _) μ
private def womanScoreIndex {n : ℕ} (μ : Matching n) : ScorePairIndex n ≃ ScorePairIndex n :=
  (manScoreIndex μ).trans (Equiv.prodComm _ _)
private def scorePairEquiv {n : ℕ} (μ : Matching n) :
    ScoreProfile n ≃ᵐ (ScorePairIndex n → ℝ × ℝ) :=
  ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ Fin n ↦ Fin n → ℝ)).trans
    (((MeasurableEquiv.curry (Fin n) (Fin n) ℝ).symm.trans
      (MeasurableEquiv.piCongrLeft (fun _ : ScorePairIndex n ↦ ℝ) (manScoreIndex μ).symm)).prodCongr
    ((MeasurableEquiv.curry (Fin n) (Fin n) ℝ).symm.trans
      (MeasurableEquiv.piCongrLeft (fun _ : ScorePairIndex n ↦ ℝ)
        (womanScoreIndex μ).symm)))).trans
    (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (ScorePairIndex n)).symm
private theorem scorePairEquiv_apply {n : ℕ} (μ : Matching n) (x : ScoreProfile n)
    (i j : Fin n) :
    scorePairEquiv μ x (i,j) = (x (.inl i) (μ j), x (.inr (μ j)) i) := by
  change ((MeasurableEquiv.piCongrLeft (fun _ : ScorePairIndex n ↦ ℝ)
      (manScoreIndex μ).symm) (fun q ↦ x (.inl q.1) q.2) (i,j),
    (MeasurableEquiv.piCongrLeft (fun _ : ScorePairIndex n ↦ ℝ)
      (womanScoreIndex μ).symm) (fun q ↦ x (.inr q.1) q.2) (i,j)) = _
  simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast,
    manScoreIndex, womanScoreIndex]
private theorem measurePreserving_scorePairEquiv {n : ℕ} (μ : Matching n) :
    MeasurePreserving (scorePairEquiv μ) (continuousScoreLaw n)
      (Measure.pi fun _ : ScorePairIndex n ↦ unitScorePairLaw) := by
  exact ((measurePreserving_arrowProdEquivProdArrow ℝ ℝ (ScorePairIndex n)
    (fun _ ↦ unitScoreLaw) (fun _ ↦ unitScoreLaw)).symm).comp
    ((((measurePreserving_piCongrLeft (fun _ ↦ unitScoreLaw) (manScoreIndex μ).symm).comp
      (measurePreserving_scoreUncurry n)).prod
      ((measurePreserving_piCongrLeft (fun _ ↦ unitScoreLaw) (womanScoreIndex μ).symm).comp
        (measurePreserving_scoreUncurry n))).comp
      (measurePreserving_sumPiEquivProdPi (fun _ ↦ Measure.pi fun _ : Fin n ↦ unitScoreLaw)))
private def splitScorePairs {n : ℕ} (μ : Matching n) :
    ScoreProfile n ≃ᵐ DiagonalScorePairs n × OffDiagonalScorePairs n :=
  (scorePairEquiv μ).trans
    (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ScorePairIndex n ↦ ℝ × ℝ)
      fun q ↦ q.1 = q.2)
theorem measurePreserving_splitScorePairs {n : ℕ} (μ : Matching n) :
    MeasurePreserving (splitScorePairs μ) (continuousScoreLaw n)
      ((diagonalScoreLaw n).prod (offDiagonalScoreLaw n)) :=
  (measurePreserving_piEquivPiSubtypeProd (fun _ ↦ unitScorePairLaw)
    fun q : ScorePairIndex n ↦ q.1 = q.2).comp
    (measurePreserving_scorePairEquiv μ)
private def diagonalPairAt {n : ℕ} (d : DiagonalScorePairs n) (i : Fin n) : ℝ × ℝ :=
  d ⟨(i,i), rfl⟩
theorem diagonalPairAt_splitScorePairs {n : ℕ} (μ : Matching n) (x : ScoreProfile n)
    (i : Fin n) :
    diagonalPairAt (splitScorePairs μ x).1 i = (x (.inl i) (μ i), x (.inr (μ i)) i) :=
  scorePairEquiv_apply μ x i i
theorem splitScorePairs_offDiagonal_apply {n : ℕ} (μ : Matching n) (x : ScoreProfile n)
    (q : {q : ScorePairIndex n // q.1 ≠ q.2}) :
    (splitScorePairs μ x).2 q =
      (x (.inl q.val.1) (μ q.val.2), x (.inr (μ q.val.2)) q.val.1) :=
  scorePairEquiv_apply μ x q.val.1 q.val.2
theorem unitScoreLaw_Iio_of_mem_Icc {x : ℝ} (hx : x ∈ Set.Icc 0 1) :
    unitScoreLaw (Set.Iio x) = ENNReal.ofReal x := by
  rw [unitScoreLaw, Measure.restrict_apply measurableSet_Iio]
  rw [show Set.Iio x ∩ Set.Icc 0 1 = Set.Ico 0 x by
    ext t
    exact ⟨fun ⟨hlt, hlo, _⟩ ↦ ⟨hlo, hlt⟩,
      fun ⟨hlo, hlt⟩ ↦ ⟨hlt, hlo, hlt.le.trans hx.2⟩⟩]
  rw [Real.volume_Ico, sub_zero]
private def nonblockingScoreCell (x y : ℝ) : Set (ℝ × ℝ) :=
  (Set.Iio x ×ˢ Set.Iio y)ᶜ
theorem unitScorePairLaw_nonblockingScoreCell (x y : ℝ) :
    unitScorePairLaw (nonblockingScoreCell x y) =
      1 - unitScoreLaw (Set.Iio x) * unitScoreLaw (Set.Iio y) := by
  rw [nonblockingScoreCell, measure_compl (measurableSet_Iio.prod measurableSet_Iio)
    (measure_ne_top _ _), measure_univ, unitScorePairLaw, Measure.prod_prod]
theorem unitScorePairLaw_nonblockingScoreCell_of_mem_Icc {x y : ℝ}
    (hx : x ∈ Set.Icc 0 1) (hy : y ∈ Set.Icc 0 1) :
    unitScorePairLaw (nonblockingScoreCell x y) = ENNReal.ofReal (1 - x * y) := by
  rw [unitScorePairLaw_nonblockingScoreCell, unitScoreLaw_Iio_of_mem_Icc hx,
    unitScoreLaw_Iio_of_mem_Icc hy, ← ENNReal.ofReal_mul hx.1, ENNReal.ofReal_sub _]
  · rw [ENNReal.ofReal_one]
  · exact mul_nonneg hx.1 hy.1
private def offDiagonalNonblocking {n : ℕ} (d : DiagonalScorePairs n) :
    Set (OffDiagonalScorePairs n) :=
  Set.univ.pi fun q ↦
    nonblockingScoreCell (diagonalPairAt d q.val.1).1 (diagonalPairAt d q.val.2).2
theorem offDiagonalScoreLaw_nonblocking {n : ℕ} (d : DiagonalScorePairs n) :
    offDiagonalScoreLaw n (offDiagonalNonblocking d) =
      ∏ q : {q : ScorePairIndex n // q.1 ≠ q.2},
        unitScorePairLaw
          (nonblockingScoreCell (diagonalPairAt d q.val.1).1 (diagonalPairAt d q.val.2).2) :=
  Measure.pi_pi _ _
theorem offDiagonalScoreLaw_nonblocking_of_mem_Icc {n : ℕ} (d : DiagonalScorePairs n)
    (hd : ∀ i, (diagonalPairAt d i).1 ∈ Set.Icc 0 1 ∧
      (diagonalPairAt d i).2 ∈ Set.Icc 0 1) :
    offDiagonalScoreLaw n (offDiagonalNonblocking d) =
      ∏ q : {q : ScorePairIndex n // q.1 ≠ q.2},
        ENNReal.ofReal (1 - (diagonalPairAt d q.val.1).1 * (diagonalPairAt d q.val.2).2) := by
  rw [offDiagonalScoreLaw_nonblocking]
  exact Finset.prod_congr rfl fun q _ ↦
    unitScorePairLaw_nonblockingScoreCell_of_mem_Icc (hd q.val.1).1 (hd q.val.2).2
theorem isScoreStable_iff_splitScorePairs {n : ℕ} (μ : Matching n) (x : ScoreProfile n) :
    IsScoreStable x μ ↔ (splitScorePairs μ x).2 ∈
      offDiagonalNonblocking (splitScorePairs μ x).1 := by
  constructor
  · intro h q _
    simp only [nonblockingScoreCell, Set.mem_compl_iff, Set.mem_prod, Set.mem_Iio,
      splitScorePairs_offDiagonal_apply, diagonalPairAt_splitScorePairs]
    exact fun ⟨hm, hw⟩ ↦ h q.val.1 (μ q.val.2)
      ⟨μ.injective.ne q.property, hm, by simpa only [Equiv.symm_apply_apply] using hw⟩
  · intro h i w hw
    let j := μ.symm w
    have hj : μ j = w := μ.apply_symm_apply w
    have hij : i ≠ j := fun he ↦ hw.1 ((congrArg μ he).trans hj)
    have hcell := h (i := ⟨(i,j), hij⟩) (Set.mem_univ _)
    simp only [nonblockingScoreCell, Set.mem_compl_iff, Set.mem_prod, Set.mem_Iio,
      splitScorePairs_offDiagonal_apply, diagonalPairAt_splitScorePairs] at hcell
    apply hcell
    exact ⟨by simpa only [hj] using hw.2.1, by simpa only [hj] using hw.2.2⟩
private def diagonalIndexEquiv (n : ℕ) :
    {q : ScorePairIndex n // q.1 = q.2} ≃ Fin n where
  toFun q := q.val.1
  invFun i := ⟨(i,i), rfl⟩
  left_inv q := Subtype.ext (Prod.ext rfl q.property)
  right_inv _ := rfl
theorem measurePreserving_diagonalScoreVectors (n : ℕ) :
    MeasurePreserving (fun d : DiagonalScorePairs n ↦
      ((fun i ↦ (diagonalPairAt d i).1), (fun i ↦ (diagonalPairAt d i).2)))
      (diagonalScoreLaw n)
      ((Measure.pi fun _ : Fin n ↦ unitScoreLaw).prod
        (Measure.pi fun _ : Fin n ↦ unitScoreLaw)) := by
  exact (measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin n)
    (fun _ ↦ unitScoreLaw) (fun _ ↦ unitScoreLaw)).comp
    (measurePreserving_piCongrLeft (fun _ ↦ unitScorePairLaw) (diagonalIndexEquiv n))
theorem ae_diagonalPairAt_mem_Icc (n : ℕ) :
    ∀ᵐ d ∂diagonalScoreLaw n, ∀ i, (diagonalPairAt d i).1 ∈ Set.Icc 0 1 ∧
      (diagonalPairAt d i).2 ∈ Set.Icc 0 1 := by
  have hu : ∀ᵐ t ∂unitScoreLaw, t ∈ Set.Icc 0 1 := ae_restrict_mem measurableSet_Icc
  have hp : ∀ᵐ z ∂unitScorePairLaw, z.1 ∈ Set.Icc 0 1 ∧ z.2 ∈ Set.Icc 0 1 :=
    ((Measure.quasiMeasurePreserving_fst (μ := unitScoreLaw)
      (ν := unitScoreLaw)).ae hu).and
      ((Measure.quasiMeasurePreserving_snd (μ := unitScoreLaw)
        (ν := unitScoreLaw)).ae hu)
  exact ae_all_iff.2 fun i ↦ (Measure.tendsto_eval_ae_ae
    (μ := fun _ : {q : ScorePairIndex n // q.1 = q.2} ↦ unitScorePairLaw)
    (i := ⟨(i,i), rfl⟩)).eventually hp
theorem continuousScoreLaw_stable_and_diagonal {n : ℕ} (μ : Matching n)
    {C : Set (DiagonalScorePairs n)} (hC : MeasurableSet C) :
    continuousScoreLaw n {x | IsScoreStable x μ ∧ (splitScorePairs μ x).1 ∈ C} =
      ∫⁻ d, C.indicator (fun d ↦ offDiagonalScoreLaw n (offDiagonalNonblocking d)) d
        ∂diagonalScoreLaw n := by
  let E : Set (DiagonalScorePairs n × OffDiagonalScorePairs n) :=
    {z | z.1 ∈ C ∧ z.2 ∈ offDiagonalNonblocking z.1}
  have hE_pre : E = (splitScorePairs μ).symm ⁻¹'
      {x | IsScoreStable x μ ∧ (splitScorePairs μ x).1 ∈ C} := by
    ext z
    have h := isScoreStable_iff_splitScorePairs μ ((splitScorePairs μ).symm z)
    simpa [E, and_comm] using
      (and_congr_right fun _ : z.1 ∈ C ↦ h.symm)
  have hE : MeasurableSet E := hE_pre ▸
    (((measurableSet_isScoreStable μ).inter
      ((measurable_fst.comp (splitScorePairs μ).measurable) hC)).preimage
      (splitScorePairs μ).symm.measurable)
  calc
    _ = (continuousScoreLaw n) ((splitScorePairs μ) ⁻¹' E) := by
      congr 1
      ext x
      simp [E, ← isScoreStable_iff_splitScorePairs, and_comm]
    _ = (diagonalScoreLaw n).prod (offDiagonalScoreLaw n) E :=
      (measurePreserving_splitScorePairs μ).measure_preimage hE.nullMeasurableSet
    _ = _ := by
      rw [Measure.prod_apply hE]
      refine lintegral_congr fun d ↦ ?_
      by_cases hd : d ∈ C
      · rw [Set.indicator_of_mem hd]
        congr 1
        ext v
        simp [E, hd]
      · rw [Set.indicator_of_notMem hd]
        have hempty : Prod.mk d ⁻¹' E = ∅ := by
          ext v
          simp [E, hd]
        rw [hempty, measure_empty]
theorem continuousScoreLaw_stable_and_diagonal_prod {n : ℕ} (μ : Matching n)
    {C : Set (DiagonalScorePairs n)} (hC : MeasurableSet C) :
    continuousScoreLaw n {x | IsScoreStable x μ ∧ (splitScorePairs μ x).1 ∈ C} =
      ∫⁻ d, C.indicator (fun d ↦ ∏ q : {q : ScorePairIndex n // q.1 ≠ q.2},
        ENNReal.ofReal (1 - (diagonalPairAt d q.val.1).1 * (diagonalPairAt d q.val.2).2)) d
        ∂diagonalScoreLaw n := by
  rw [continuousScoreLaw_stable_and_diagonal μ hC]
  apply lintegral_congr_ae
  filter_upwards [ae_diagonalPairAt_mem_Icc n] with d hd
  by_cases hc : d ∈ C
  · simpa only [Set.indicator_of_mem hc] using offDiagonalScoreLaw_nonblocking_of_mem_Icc d hd
  · simp only [Set.indicator_of_notMem hc]
private abbrev OffDiagonalScoreRows (n : ℕ) := (i : Fin n) → {j : Fin n // i ≠ j} → ℝ × ℝ
private def offDiagonalRowsEquiv (n : ℕ) : OffDiagonalScorePairs n ≃ᵐ OffDiagonalScoreRows n where
  toFun v i j := v ⟨(i,j), j.property⟩
  invFun v q := v q.val.1 ⟨q.val.2, q.property⟩
  left_inv v := by
    funext q
    cases q
    rfl
  right_inv _ := rfl
  measurable_toFun := measurable_pi_iff.2 fun _ ↦
    measurable_pi_iff.2 fun _ ↦ measurable_pi_apply _
  measurable_invFun := measurable_pi_iff.2 fun q ↦
    (measurable_pi_apply (⟨q.val.2, q.property⟩ : {j : Fin n // q.val.1 ≠ j})).comp
      (measurable_pi_apply q.val.1)
private def offDiagonalIndexEquiv (n : ℕ) :
    {q : ScorePairIndex n // q.1 ≠ q.2} ≃ (i : Fin n) × {j : Fin n // i ≠ j} where
  toFun q := ⟨q.val.1, ⟨q.val.2, q.property⟩⟩
  invFun q := ⟨(q.1, q.2.val), q.2.property⟩
  left_inv q := by cases q; rfl
  right_inv q := by cases q; rfl
end StepA4
end

-- CoexposureSpouseMarginal
section
open Filter MeasureTheory ProbabilityTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace StepA4
private noncomputable def spouseVectorLaw (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi fun _ ↦ unitScoreLaw
private instance (n : ℕ) : IsProbabilityMeasure (spouseVectorLaw n) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : Fin n ↦ unitScoreLaw))
theorem spouseVectorLaw_eq_restrict_volume (n : ℕ) :
    spouseVectorLaw n =
      (volume : Measure (Fin n → ℝ)).restrict (univ.pi fun _ ↦ Icc (0 : ℝ) 1) := by
  rw [volume_pi, Measure.restrict_pi_pi]
  rfl
theorem spouseVectorLaw_le_volume (n : ℕ) :
    spouseVectorLaw n ≤ (volume : Measure (Fin n → ℝ)) := by
  rw [spouseVectorLaw_eq_restrict_volume]
  exact Measure.restrict_le_self
private def femaleSpouseByHusband {n : ℕ} (μ : Matching n) (x : ScoreProfile n) : Fin n → ℝ :=
  fun j ↦ femaleSpouseScore x μ (μ j)
private noncomputable def femaleSpouseStabilityDensity {n : ℕ} (y : Fin n → ℝ) : ℝ≥0∞ :=
  ∏ i : Fin n, ENNReal.ofReal (scoreRowMass (Finset.univ.erase i) y 0 1)
theorem measurable_femaleSpouseStabilityDensity (n : ℕ) :
    Measurable (@femaleSpouseStabilityDensity n) := by
  unfold femaleSpouseStabilityDensity
  refine Finset.measurable_prod _ fun i _ ↦ Measurable.ennreal_ofReal ?_
  have h : Measurable (fun z : (Fin n → ℝ) × ℝ ↦
      scoreRowKernel (Finset.univ.erase i) z.1 z.2) := by
    unfold scoreRowKernel
    refine Finset.measurable_prod _ fun j _ ↦ measurable_const.sub ?_
    exact measurable_snd.mul ((measurable_pi_apply j).comp measurable_fst)
  convert (h.stronglyMeasurable.integral_prod_right' (ν := unitScoreLaw)).measurable using 1
  funext y
  rw [unitScoreLaw, scoreRowMass, intervalIntegral.integral_of_le (by norm_num)]
  exact integral_Icc_eq_integral_Ioc.symm
private def spouseVectors {n : ℕ} (d : DiagonalScorePairs n) :
    (Fin n → ℝ) × (Fin n → ℝ) :=
  (fun i ↦ (diagonalPairAt d i).1, fun i ↦ (diagonalPairAt d i).2)
private noncomputable def spouseStabilityKernel {n : ℕ}
    (x y : Fin n → ℝ) : ℝ≥0∞ :=
  ∏ i : Fin n, ENNReal.ofReal (scoreRowKernel (Finset.univ.erase i) y (x i))
private theorem measurable_spouseStabilityKernel (n : ℕ) :
    Measurable (fun z : (Fin n → ℝ) × (Fin n → ℝ) ↦ spouseStabilityKernel z.1 z.2) := by
  unfold spouseStabilityKernel scoreRowKernel
  refine Finset.measurable_prod _ fun i _ ↦ Measurable.ennreal_ofReal ?_
  refine Finset.measurable_prod _ fun j _ ↦ measurable_const.sub ?_
  exact ((measurable_pi_apply i).comp measurable_fst).mul
    ((measurable_pi_apply j).comp measurable_snd)
private theorem ae_spouseVectorLaw_mem_Icc (n : ℕ) :
    ∀ᵐ y ∂spouseVectorLaw n, ∀ j, y j ∈ Icc (0 : ℝ) 1 :=
  ae_all_iff.2 fun j ↦
    let h := measurePreserving_eval (fun _ : Fin n ↦ unitScoreLaw) j
    h.quasiMeasurePreserving.ae (ae_restrict_mem measurableSet_Icc)
private def offDiagonalSigmaEquiv (n : ℕ) :
    {q : ScorePairIndex n // q.1 ≠ q.2} ≃ (i : Fin n) × {j : Fin n // i ≠ j} where
  toFun q := ⟨q.val.1, ⟨q.val.2, q.property⟩⟩
  invFun q := ⟨(q.1,q.2.val),q.2.property⟩
  left_inv q := by cases q; rfl
  right_inv q := by cases q; rfl
private theorem spouseStabilityKernel_eq {n : ℕ} {x y : Fin n → ℝ}
    (hx : ∀ i, x i ∈ Icc (0 : ℝ) 1) (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) :
    spouseStabilityKernel x y = ∏ q : {q : ScorePairIndex n // q.1 ≠ q.2},
      ENNReal.ofReal (1 - x q.val.1 * y q.val.2) := by
  classical
  unfold spouseStabilityKernel scoreRowKernel
  trans ∏ i : Fin n, ∏ j : {j : Fin n // i ≠ j}, ENNReal.ofReal (1 - x i * y j.val)
  · refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [ENNReal.ofReal_prod_of_nonneg]
    · exact Finset.prod_subtype _ (by simp [ne_comm])
        (fun j ↦ ENNReal.ofReal (1 - x i * y j))
    · intro j _
      exact sub_nonneg.mpr
        ((mul_le_mul_of_nonneg_right (hx i).2 (hy j).1).trans (by simpa using (hy j).2))
  · rw [← Fintype.prod_sigma']
    exact Fintype.prod_equiv (offDiagonalSigmaEquiv n).symm _ _ fun _ ↦ rfl
theorem lintegral_scoreRowKernel_unitScoreLaw {n : ℕ} (J : Finset (Fin n))
    (y : Fin n → ℝ) (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) :
    (∫⁻ x, ENNReal.ofReal (scoreRowKernel J y x) ∂unitScoreLaw) =
      ENNReal.ofReal (scoreRowMass J y 0 1) := by
  have hint : Integrable (scoreRowKernel J y) unitScoreLaw :=
    (continuous_scoreRowKernel J y).integrableOn_Icc
  have hnn : 0 ≤ᵐ[unitScoreLaw] scoreRowKernel J y := by
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Icc :
      MeasurableSet (Icc (0 : ℝ) 1))] with x hx
    unfold scoreRowKernel
    exact Finset.prod_nonneg fun j _ ↦ sub_nonneg.mpr
      ((mul_le_mul_of_nonneg_right hx.2 (hy j).1).trans (by simpa using (hy j).2))
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
  congr 1
  rw [unitScoreLaw, scoreRowMass, intervalIntegral.integral_of_le (by norm_num)]
  exact integral_Icc_eq_integral_Ioc
private theorem lintegral_spouseStabilityKernel {n : ℕ} (y : Fin n → ℝ)
    (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) :
    (∫⁻ x, spouseStabilityKernel x y ∂spouseVectorLaw n) = femaleSpouseStabilityDensity y := by
  let f (i : Fin n) (x : ℝ) := ENNReal.ofReal (scoreRowKernel (Finset.univ.erase i) y x)
  have hf (i : Fin n) : Measurable (f i) :=
    (continuous_scoreRowKernel _ _).measurable.ennreal_ofReal
  have hi := iIndepFun_pi (μ := fun _ : Fin n ↦ unitScoreLaw)
    (X := f) (fun i ↦ (hf i).aemeasurable)
  calc
    _ = ∏ i : Fin n, ∫⁻ x, f i (x i) ∂spouseVectorLaw n :=
      lintegral_prod_eq_prod_lintegral_of_indepFun _ _ hi
        (fun i ↦ (hf i).comp (measurable_pi_apply i))
    _ = _ := by
      refine Finset.prod_congr rfl fun i _ ↦ ?_
      exact ((measurePreserving_eval (fun _ : Fin n ↦ unitScoreLaw) i).lintegral_comp
        (hf i)).trans (lintegral_scoreRowKernel_unitScoreLaw _ y hy)
theorem femaleSpouseStabilityDensity_le_one {n : ℕ} (y : Fin n → ℝ)
    (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) :
    femaleSpouseStabilityDensity y ≤ 1 := by
  rw [← lintegral_spouseStabilityKernel y hy]
  have hone : (∫⁻ _x, 1 ∂spouseVectorLaw n) = 1 := by simp
  rw [← hone]
  apply lintegral_mono_ae
  filter_upwards [ae_spouseVectorLaw_mem_Icc n] with x hx
  rw [spouseStabilityKernel_eq hx hy]
  calc
    _ ≤ ∏ _q : {q : ScorePairIndex n // q.1 ≠ q.2}, (1 : ℝ≥0∞) := by
      refine Finset.prod_le_prod' fun q _ ↦ ?_
      rw [ENNReal.ofReal_le_one]
      exact sub_le_self _ (mul_nonneg (hx q.val.1).1 (hy q.val.2).1)
    _ = _ := Finset.prod_const_one
theorem continuousScoreLaw_stable_and_spouseVectors {n : ℕ} (μ : Matching n)
    {B : Set ((Fin n → ℝ) × (Fin n → ℝ))} (hB : MeasurableSet B) :
    continuousScoreLaw n
        {x | IsScoreStable x μ ∧
          ((fun i ↦ maleSpouseScore x μ i), femaleSpouseByHusband μ x) ∈ B} =
      ∫⁻ z, B.indicator (fun z ↦ spouseStabilityKernel z.1 z.2) z
        ∂((spouseVectorLaw n).prod (spouseVectorLaw n)) := by
  have hv : MeasurePreserving (@spouseVectors n) (diagonalScoreLaw n)
      ((spouseVectorLaw n).prod (spouseVectorLaw n)) :=
    measurePreserving_diagonalScoreVectors n
  have hvec (x : ScoreProfile n) : spouseVectors (splitScorePairs μ x).1 =
      ((fun i ↦ maleSpouseScore x μ i), femaleSpouseByHusband μ x) := by
    apply Prod.ext <;> funext i
    · simp only [spouseVectors, diagonalPairAt_splitScorePairs, maleSpouseScore]
    · simp only [spouseVectors, diagonalPairAt_splitScorePairs, femaleSpouseByHusband,
        femaleSpouseScore, Equiv.symm_apply_apply]
  have hcut : MeasurableSet (spouseVectors ⁻¹' B) := hB.preimage hv.measurable
  have he : {x | IsScoreStable x μ ∧
      ((fun i ↦ maleSpouseScore x μ i), femaleSpouseByHusband μ x) ∈ B} =
      {x | IsScoreStable x μ ∧ (splitScorePairs μ x).1 ∈ spouseVectors ⁻¹' B} := by
    ext x
    simp [hvec]
  rw [he, continuousScoreLaw_stable_and_diagonal_prod μ hcut,
    ← hv.lintegral_comp ((measurable_spouseStabilityKernel n).indicator hB)]
  apply lintegral_congr_ae
  filter_upwards [ae_diagonalPairAt_mem_Icc n] with d hd
  by_cases h : spouseVectors d ∈ B
  · rw [indicator_of_mem (show d ∈ spouseVectors ⁻¹' B from h), indicator_of_mem h]
    exact (spouseStabilityKernel_eq (fun i ↦ (hd i).1) (fun i ↦ (hd i).2)).symm
  · rw [indicator_of_notMem (show d ∉ spouseVectors ⁻¹' B from h), indicator_of_notMem h]
theorem continuousScoreLaw_stable_and_femaleSpouse {n : ℕ} (μ : Matching n)
    {B : Set (Fin n → ℝ)} (hB : MeasurableSet B) :
    continuousScoreLaw n {x | IsScoreStable x μ ∧ femaleSpouseByHusband μ x ∈ B} =
      ∫⁻ y in B, femaleSpouseStabilityDensity y ∂spouseVectorLaw n := by
  rw [show {x | IsScoreStable x μ ∧ femaleSpouseByHusband μ x ∈ B} =
    {x | IsScoreStable x μ ∧
      ((fun i ↦ maleSpouseScore x μ i), femaleSpouseByHusband μ x) ∈ Prod.snd ⁻¹' B} from rfl,
    continuousScoreLaw_stable_and_spouseVectors μ (hB.preimage measurable_snd),
    lintegral_prod_symm' _ ((measurable_spouseStabilityKernel n).indicator
      (hB.preimage measurable_snd)), ← lintegral_indicator hB]
  apply lintegral_congr_ae
  filter_upwards [ae_spouseVectorLaw_mem_Icc n] with y hy
  by_cases h : y ∈ B
  · rw [indicator_of_mem h, ← lintegral_spouseStabilityKernel y hy]
    exact lintegral_congr fun x ↦ indicator_of_mem h _
  · rw [indicator_of_notMem h, ← lintegral_zero]
    exact lintegral_congr fun x ↦ indicator_of_notMem h _
theorem femaleSpouseTotal_eq_sum_byHusband {n : ℕ} (μ : Matching n) (x : ScoreProfile n) :
    femaleSpouseTotal x μ = ∑ j, femaleSpouseByHusband μ x j :=
  (Equiv.sum_comp μ (femaleSpouseScore x μ)).symm
theorem sum_measure_scoreStable_eq_expected (n : ℕ) :
    (∑ μ : Matching n, continuousScoreLaw n {x | IsScoreStable x μ}) =
      ENNReal.ofReal (expectedNumStableMatchings n) := by
  have hf (μ : Matching n) :
      Measurable ({x | IsScoreStable x μ}.indicator (1 : ScoreProfile n → ℝ≥0∞)) :=
    measurable_const.indicator (measurableSet_isScoreStable μ)
  calc
    _ = ∑ μ : Matching n, ∫⁻ x, {x | IsScoreStable x μ}.indicator 1 x ∂continuousScoreLaw n := by
      refine Finset.sum_congr rfl fun μ _ ↦ ?_
      rw [lintegral_indicator_one (measurableSet_isScoreStable μ)]
    _ = ∫⁻ x, ∑ μ : Matching n, {x | IsScoreStable x μ}.indicator 1 x ∂continuousScoreLaw n :=
      (lintegral_finsetSum _ fun μ _ ↦ hf μ).symm
    _ = ∫⁻ x, ∑ μ : Matching n, (scoreMarkEvent n).indicator 1 (x, μ)
        ∂continuousScoreLaw n := by
      refine lintegral_congr fun x ↦ Finset.sum_congr rfl fun μ _ ↦ ?_
      by_cases h : IsScoreStable x μ <;> simp [scoreMarkEvent, h]
    _ = _ := by
      have hm : Measurable (1 : ScoreProfile n × Matching n → ℝ≥0∞) :=
        measurable_const
      simpa using (continuous_mark_counting_identity n hm).symm
end StepA4
end

-- CoexposureSpouseShells
section
open Filter MeasureTheory Set StableMarriage
open scoped ENNReal BigOperators Topology
namespace StepA4
private def spouseVectorTotal {n : ℕ} (y : Fin n → ℝ) : ℝ :=
  ∑ i, y i
end StepA4
end

-- PittelMeanTail
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace StepA4
private def pittelScoreCube (n : ℕ) : Set (Fin n → ℝ) :=
  univ.pi fun _ ↦ Icc (0 : ℝ) 1
theorem measurableSet_pittelScoreCube (n : ℕ) : MeasurableSet (pittelScoreCube n) :=
  (measurableSet_pi countable_univ).2 (Or.inl fun _ _ ↦ measurableSet_Icc)
private noncomputable def pittelDensity (n : ℕ) : (Fin n → ℝ) → ℝ≥0∞ :=
  (pittelScoreCube n).indicator femaleSpouseStabilityDensity
theorem measurable_pittelDensity (n : ℕ) : Measurable (pittelDensity n) :=
  (measurable_femaleSpouseStabilityDensity n).indicator (measurableSet_pittelScoreCube n)
theorem pittelDensity_eq_ofReal_prod {n : ℕ} {y : Fin n → ℝ}
    (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) :
    pittelDensity n y =
      ENNReal.ofReal (∏ i, scoreRowMass (Finset.univ.erase i) y 0 1) := by
  rw [pittelDensity, indicator_of_mem (show y ∈ pittelScoreCube n from fun j _ ↦ hy j)]
  unfold femaleSpouseStabilityDensity
  symm
  apply ENNReal.ofReal_prod_of_nonneg
  intro i _
  unfold scoreRowMass
  refine intervalIntegral.integral_nonneg (by norm_num) fun x hx ↦ ?_
  unfold scoreRowKernel
  exact Finset.prod_nonneg fun j _ ↦ sub_nonneg.mpr (calc
    x * y j ≤ 1 * y j := mul_le_mul_of_nonneg_right hx.2 (hy j).1
    _ ≤ 1 := by simpa only [one_mul] using (hy j).2)
theorem pittelDensity_le_inv_pow {n : ℕ} {y : Fin n → ℝ} (hs : 2 ≤ spouseVectorTotal y) :
    pittelDensity n y ≤ ENNReal.ofReal (Real.exp 2 / spouseVectorTotal y ^ n) := by
  by_cases hy : y ∈ pittelScoreCube n
  · have hcube (i : Fin n) : y i ∈ Icc (0 : ℝ) 1 := hy i (mem_univ i)
    rw [pittelDensity_eq_ofReal_prod hcube]
    apply ENNReal.ofReal_le_ofReal
    simpa only [spouseVectorTotal, Fintype.card_fin] using
      scoreRowMass_prod_le_inv_pow y hcube hs
  · simp [pittelDensity, indicator_of_notMem hy]
theorem pittelDensity_eq_zero_of_size_lt {n : ℕ} {y : Fin n → ℝ}
    (hy : (n : ℝ) < spouseVectorTotal y) : pittelDensity n y = 0 := by
  refine indicator_of_notMem (fun h ↦ hy.not_ge ?_) _
  calc
    spouseVectorTotal y ≤ ∑ _ : Fin n, (1 : ℝ) :=
      Finset.sum_le_sum fun i _ ↦ (h i (mem_univ i)).2
    _ = (n : ℝ) := by simp
theorem sum_measure_scoreStable_and_femaleSpouse_eq_pittelDensity {n : ℕ}
    {B : Set (Fin n → ℝ)} (hB : MeasurableSet B) :
    (∑ μ : Matching n, continuousScoreLaw n
      {x | IsScoreStable x μ ∧ femaleSpouseByHusband μ x ∈ B}) =
      (n.factorial : ℝ≥0∞) * (∫⁻ y in B, pittelDensity n y) := by
  simp_rw [continuousScoreLaw_stable_and_femaleSpouse _ hB]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  rw [spouseVectorLaw_eq_restrict_volume, Measure.restrict_restrict hB]
  change (n.factorial : ℝ≥0∞) *
    (∫⁻ y in B ∩ pittelScoreCube n, femaleSpouseStabilityDensity y) = _
  unfold pittelDensity
  rw [setLIntegral_indicator (measurableSet_pittelScoreCube n),
    inter_comm B (pittelScoreCube n)]
theorem lintegral_Ioc_inv_of_pos {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫⁻ s in Ioc a b, ENNReal.ofReal s⁻¹) = ENNReal.ofReal (Real.log (b / a)) := by
  have hi : IntervalIntegrable (fun s : ℝ ↦ s⁻¹) volume a b :=
    (continuousOn_id.inv₀ fun _ hs ↦
      (ha.trans_le ((uIcc_of_le hab ▸ hs).1)).ne').intervalIntegrable
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hi),
    ← intervalIntegral.integral_of_le hab, integral_inv_of_pos ha (ha.trans_le hab)]
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs using
    inv_nonneg.mpr (ha.trans hs.1).le
end StepA4
end

-- MarkedSpouseAngleComparison
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA4
private theorem factorial_mul_radial_inv_power {n : ℕ} (hn : 0 < n)
    {l u C : ℝ} (hl : 0 < l) (hlu : l ≤ u) (hC : 0 ≤ C) :
    (n.factorial : ℝ≥0∞) *
        (∫⁻ s in Icc l u, ENNReal.ofReal (C / s ^ n) ∂spouseRadialLaw n) =
      ENNReal.ofReal ((n : ℝ) * C * Real.log (u / l)) := by
  have hd : Measurable (fun s : ℝ ↦
      ENNReal.ofReal (s ^ (n - 1) / ((n - 1).factorial : ℝ))) := by fun_prop
  have hg : Measurable (fun s : ℝ ↦ ENNReal.ofReal (C / s ^ n)) := by fun_prop
  rw [spouseRadialLaw, setLIntegral_withDensity_eq_setLIntegral_mul _ hd hg measurableSet_Icc,
    Measure.restrict_restrict measurableSet_Icc,
    inter_eq_left.mpr (show Icc l u ⊆ Ioi 0 from fun _ hs ↦ hl.trans_le hs.1),
    ← restrict_Ioc_eq_restrict_Icc,
    ← lintegral_const_mul' _ _ (ENNReal.natCast_ne_top n.factorial)]
  calc
    _ = ∫⁻ s in Ioc l u, ENNReal.ofReal ((n : ℝ) * C) * ENNReal.ofReal s⁻¹ := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioc : MeasurableSet (Ioc l u))]
        with s hs
      have hs' : 0 < s := hl.trans hs.1
      have hnat := Nat.factorial_succ (n - 1)
      rw [show n - 1 + 1 = n by omega] at hnat
      have hnfac : (n.factorial : ℝ) = (n : ℝ) * ((n - 1).factorial : ℝ) := by
        exact_mod_cast hnat
      change (n.factorial : ℝ≥0∞) *
          (ENNReal.ofReal (s ^ (n - 1) / ((n - 1).factorial : ℝ)) *
            ENNReal.ofReal (C / s ^ n)) =
        ENNReal.ofReal ((n : ℝ) * C) * ENNReal.ofReal s⁻¹
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), hnfac]
      congr 1
      rw [← show n - 1 + 1 = n by omega, pow_succ s (n - 1)]
      field_simp
      simp [mul_comm]
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_Ioc_inv_of_pos hl hlu,
        ← ENNReal.ofReal_mul (by positivity)]
theorem sum_measure_scoreStable_and_femaleSpouseAngle_le {n : ℕ} (hn : 2 ≤ n)
    {A : Set (Fin n → ℝ)} (hA : MeasurableSet A) :
    (∑ μ : Matching n, continuousScoreLaw n
      {x | IsScoreStable x μ ∧ 2 ≤ femaleSpouseTotal x μ ∧
        spouseAngle (femaleSpouseByHusband μ x) ∈ A}) ≤
      ENNReal.ofReal (Real.exp 2 * (n : ℝ) * Real.log n) * spouseAngularLaw n A := by
  let B : Set (Fin n → ℝ) := {y | 2 ≤ spouseVectorTotal y ∧ spouseAngle y ∈ A}
  let Q : Set (Fin n → ℝ) := {y | ∀ i, 0 ≤ y i}
  let R : Set ℝ := Icc 2 (n : ℝ)
  let f := B.indicator (pittelDensity n)
  let g (s : ℝ) := ENNReal.ofReal (Real.exp 2 / s ^ n)
  have hn' : 0 < n := by omega
  have h2n : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hB : MeasurableSet B := (measurableSet_le measurable_const
    (Finset.measurable_sum _ fun i _ ↦ measurable_pi_apply i)).inter
      (hA.preimage (measurable_spouseAngle n))
  have hQ : MeasurableSet Q := by
    change MeasurableSet {y : Fin n → ℝ | ∀ i, 0 ≤ y i}
    rw [ofPred_forall]
    exact MeasurableSet.iInter fun i ↦
      measurableSet_le measurable_const (measurable_pi_apply i)
  have hf : Measurable f := (measurable_pittelDensity n).indicator hB
  have he (μ : Matching n) :
      {x | IsScoreStable x μ ∧ 2 ≤ femaleSpouseTotal x μ ∧
        spouseAngle (femaleSpouseByHusband μ x) ∈ A} =
      {x | IsScoreStable x μ ∧ femaleSpouseByHusband μ x ∈ B} := by
    ext x
    change (IsScoreStable x μ ∧ 2 ≤ femaleSpouseTotal x μ ∧
        spouseAngle (femaleSpouseByHusband μ x) ∈ A) ↔
      (IsScoreStable x μ ∧ 2 ≤ spouseVectorTotal (femaleSpouseByHusband μ x) ∧
        spouseAngle (femaleSpouseByHusband μ x) ∈ A)
    rw [femaleSpouseTotal_eq_sum_byHusband, spouseVectorTotal]
  have horthant : (∫⁻ y, f y) = ∫⁻ y, f y ∂(volume.restrict Q) := by
    rw [← lintegral_indicator hQ]
    apply lintegral_congr
    intro y
    by_cases hy : y ∈ Q
    · rw [indicator_of_mem hy]
    · rw [indicator_of_notMem hy]
      have hcube : y ∉ pittelScoreCube n := fun hy' ↦ hy fun i ↦ (hy' i (mem_univ i)).1
      have hz : pittelDensity n y = 0 := indicator_of_notMem hcube _
      by_cases hy' : y ∈ B
      · simp only [f, indicator_of_mem hy', hz]
      · exact indicator_of_notMem hy' _
  have hinner (s : ℝ) : (∫⁻ w, f (fun i ↦ s * w i) ∂spouseAngularLaw n) ≤
      R.indicator g s * spouseAngularLaw n A := by
    by_cases hs : s ∈ R
    · rw [indicator_of_mem hs, ← setLIntegral_const, ← lintegral_indicator hA]
      apply lintegral_mono_ae
      filter_upwards [ae_spouseAngularLaw hn'] with w hw
      have hs0 : 0 < s := (by norm_num : (0 : ℝ) < 2).trans_le hs.1
      have hsum : spouseVectorTotal (fun i ↦ s * w i) = s := by
        simp only [spouseVectorTotal, ← Finset.mul_sum, hw.2, mul_one]
      have hangle : spouseAngle (fun i ↦ s * w i) = w := by
        funext i
        change s * w i / spouseVectorTotal (fun j ↦ s * w j) = w i
        rw [hsum, mul_comm s, mul_div_cancel_right₀ _ hs0.ne']
      by_cases hwA : w ∈ A
      · have hmem : (fun i ↦ s * w i) ∈ B := by
          change 2 ≤ spouseVectorTotal (fun i ↦ s * w i) ∧
            spouseAngle (fun i ↦ s * w i) ∈ A
          rw [hsum, hangle]
          exact ⟨hs.1, hwA⟩
        simp only [f, indicator_of_mem hmem, indicator_of_mem hwA]
        simpa only [g, hsum] using
          (pittelDensity_le_inv_pow (y := fun i ↦ s * w i) (hsum.symm ▸ hs.1))
      · have hmem : (fun i ↦ s * w i) ∉ B := fun h ↦ hwA (hangle ▸ h.2)
        simp only [f, indicator_of_notMem hmem, indicator_of_notMem hwA, le_refl]
    · rw [indicator_of_notMem hs, zero_mul, ← lintegral_zero]
      apply lintegral_mono_ae
      filter_upwards [ae_spouseAngularLaw hn'] with w hw
      have hsum : spouseVectorTotal (fun i ↦ s * w i) = s := by
        simp only [spouseVectorTotal, ← Finset.mul_sum, hw.2, mul_one]
      by_cases hmem : (fun i ↦ s * w i) ∈ B
      · have hs2 : 2 ≤ s := hsum ▸ hmem.1
        have hsn : (n : ℝ) < s := lt_of_not_ge fun h ↦ hs ⟨hs2, h⟩
        simp only [f, indicator_of_mem hmem,
          pittelDensity_eq_zero_of_size_lt (hsum.symm ▸ hsn), le_refl]
      · simp only [f, indicator_of_notMem hmem, le_refl]
  simp_rw [he]
  rw [sum_measure_scoreStable_and_femaleSpouse_eq_pittelDensity hB, ← lintegral_indicator hB,
    show B.indicator (pittelDensity n) = f from rfl, horthant,
    lintegral_spouseRadialAngular hn' hf]
  calc
    _ ≤ (n.factorial : ℝ≥0∞) *
        (∫⁻ s, R.indicator g s * spouseAngularLaw n A ∂spouseRadialLaw n) :=
      mul_le_mul_right (lintegral_mono hinner) _
    _ = ENNReal.ofReal ((n : ℝ) * Real.exp 2 * Real.log ((n : ℝ) / 2)) *
        spouseAngularLaw n A := by
      rw [lintegral_mul_const' _ _ (measure_ne_top _ _), lintegral_indicator measurableSet_Icc,
        ← mul_assoc]
      rw [factorial_mul_radial_inv_power hn' (by norm_num) h2n (Real.exp_nonneg _)]
    _ ≤ _ := by
      apply mul_le_mul_left
      apply ENNReal.ofReal_le_ofReal
      rw [mul_comm (n : ℝ) (Real.exp 2)]
      exact mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) (by linarith))
        (by positivity)
end StepA4
end

-- ScoreSideSwap
section
open MeasureTheory Set StableMarriage
open scoped BigOperators
namespace StepA4
private def swapScoreSides {n : ℕ} (x : ScoreProfile n) : ScoreProfile n :=
  fun row ↦ x row.swap
theorem measurePreserving_swapScoreSides (n : ℕ) :
    MeasurePreserving (@swapScoreSides n) (continuousScoreLaw n) (continuousScoreLaw n) := by
  let e := Equiv.sumComm (Fin n) (Fin n)
  have h := measurePreserving_piCongrLeft
    (fun _ : Fin n ⊕ Fin n ↦ Measure.pi fun _ : Fin n ↦ unitScoreLaw) e
  have hfun : ⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin n ⊕ Fin n ↦ Fin n → ℝ) e) =
      @swapScoreSides n := by
    funext x row
    cases row <;> rfl
  simpa only [hfun, continuousScoreLaw] using h
end StepA4
end

-- StableMaleSpouseRowLaw
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace StepA4
end StepA4
end

-- IndependentFlagLowerTail
section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace StepA4
open scoped Classical in
private theorem lintegral_exp_neg_flag_le {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] {A : Set Ω} (hA : MeasurableSet A)
    {p : ℝ} (hp₀ : 0 ≤ p) (hp : ENNReal.ofReal p ≤ ν A) :
    (∫⁻ x, if x ∈ A then ENNReal.ofReal (Real.exp (-1)) else 1 ∂ν) ≤
      ENNReal.ofReal (Real.exp (-(1 - Real.exp (-1)) * p)) := by
  let q := (ν A).toReal
  have hfin := measure_ne_top ν A
  have hfin' := measure_ne_top ν Aᶜ
  have hpq : p ≤ q := by
    simpa only [ENNReal.toReal_ofReal hp₀] using ENNReal.toReal_mono hfin hp
  have hcomp : (ν Aᶜ).toReal = 1 - q := by
    rw [measure_compl hA hfin, measure_univ,
      ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one]
  have hd : 0 ≤ 1 - Real.exp (-1) :=
    sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by norm_num))
  calc
    _ = ENNReal.ofReal (Real.exp (-1)) * ν A + ν Aᶜ := by
      change (∫⁻ x, A.piecewise (fun _ ↦ ENNReal.ofReal (Real.exp (-1)))
        (fun _ ↦ 1) x ∂ν) = _
      rw [← lintegral_add_compl _ hA]
      have h1 : ∫⁻ x in A, A.piecewise (fun _ ↦ ENNReal.ofReal (Real.exp (-1))) (fun _ ↦ 1) x ∂ν =
          ∫⁻ _ in A, ENNReal.ofReal (Real.exp (-1)) ∂ν :=
        setLIntegral_congr_fun hA (fun x hx ↦ by simp [hx])
      have h2 : ∫⁻ x in Aᶜ, A.piecewise (fun _ ↦ ENNReal.ofReal (Real.exp (-1))) (fun _ ↦ 1) x ∂ν =
          ∫⁻ _ in Aᶜ, (1 : ENNReal) ∂ν :=
        setLIntegral_congr_fun hA.compl (fun x hx ↦ by simp [show x ∉ A from hx])
      rw [h1, h2]
      simp only [lintegral_const, Measure.restrict_apply_univ, one_mul]
    _ = ENNReal.ofReal (-(1 - Real.exp (-1)) * q + 1) := by
      rw [← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_toReal hfin',
        ← ENNReal.ofReal_mul (Real.exp_pos _).le,
        ← ENNReal.ofReal_add (by positivity) ENNReal.toReal_nonneg, hcomp]
      congr 1
      ring
    _ ≤ ENNReal.ofReal (Real.exp (-(1 - Real.exp (-1)) * q)) :=
      ENNReal.ofReal_le_ofReal (Real.add_one_le_exp _)
    _ ≤ _ := ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonpos_left hpq (neg_nonpos.mpr hd)))
open scoped Classical in
theorem measure_pi_flagCount_lt_le_exp {ι : Type*} [Fintype ι]
    {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    (ν : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (ν i)]
    (A : ∀ i, Set (Ω i)) (hA : ∀ i, MeasurableSet (A i)) (p t : ℝ)
    (hp₀ : 0 ≤ p) (hp : ∀ i, ENNReal.ofReal p ≤ ν i (A i)) :
    (Measure.pi ν) {x | (∑ i, if x i ∈ A i then (1 : ℝ) else 0) < t} ≤
      ENNReal.ofReal (Real.exp (t - (1 - Real.exp (-1)) * p * (Fintype.card ι : ℝ))) := by
  let X (i : ι) (x : Ω i) := if x ∈ A i then ENNReal.ofReal (Real.exp (-1)) else 1
  let F (x : ∀ i, Ω i) := ENNReal.ofReal (Real.exp (t - ∑ i, if x i ∈ A i then (1 : ℝ) else 0))
  have hX (i : ι) : Measurable (X i) := Measurable.ite (hA i) measurable_const measurable_const
  have hXpi (i : ι) : Measurable (fun x : ∀ j, Ω j ↦ X i (x i)) :=
    (hX i).comp (measurable_pi_apply i)
  have hfactor (x : ∀ i, Ω i) :
      F x = ENNReal.ofReal (Real.exp t) * ∏ i, X i (x i) := by
    unfold F X
    rw [sub_eq_add_neg, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← Finset.sum_neg_distrib, Real.exp_sum,
      ENNReal.ofReal_prod_of_nonneg (fun _ _ ↦ (Real.exp_pos _).le)]
    congr 1
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    split <;> simp
  have hF : Measurable F := by
    rw [show F = (fun x ↦ ENNReal.ofReal (Real.exp t) * ∏ i, X i (x i)) from funext hfactor]
    exact measurable_const.mul (Finset.univ.measurable_prod fun i _ ↦ hXpi i)
  have hmgf (i : ι) : (∫⁻ x : ∀ j, Ω j, X i (x i) ∂Measure.pi ν) ≤
      ENNReal.ofReal (Real.exp (-(1 - Real.exp (-1)) * p)) := by
    rw [(measurePreserving_eval ν i).lintegral_comp (hX i)]
    exact lintegral_exp_neg_flag_le (ν i) (hA i) hp₀ (hp i)
  calc
    _ ≤ ∫⁻ x, F x ∂Measure.pi ν := by
      refine meas_le_lintegral₀ hF.aemeasurable fun x hx ↦ ?_
      have h : 0 ≤ t - ∑ i, if x i ∈ A i then (1 : ℝ) else 0 := sub_nonneg.mpr hx.le
      simpa only [F, Real.exp_zero, ENNReal.ofReal_one] using
        ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr h)
    _ = ENNReal.ofReal (Real.exp t) * ∏ i, ∫⁻ x : ∀ j, Ω j, X i (x i) ∂Measure.pi ν := by
      simp_rw [hfactor]
      rw [lintegral_const_mul _ (Finset.univ.measurable_prod fun i _ ↦ hXpi i),
        lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ _
          (iIndepFun_pi (fun i ↦ (hX i).aemeasurable)) hXpi]
    _ ≤ ENNReal.ofReal (Real.exp t) * ∏ _i : ι,
        ENNReal.ofReal (Real.exp (-(1 - Real.exp (-1)) * p)) :=
      mul_le_mul_right (Finset.prod_le_prod' fun i _ ↦ hmgf i) _
    _ = _ := by
      rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ ↦ (Real.exp_pos _).le),
        ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_sum, ← Real.exp_add,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      congr 2
      ring
end StepA4
end

-- FiniteProductDensity
section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace StepA4
variable {ι : Type*} [Fintype ι] {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
theorem pi_smul_coordinates (ν : ∀ i, Measure (Ω i)) [∀ i, IsFiniteMeasure (ν i)]
    (c : ι → ℝ≥0∞) (hc : ∀ i, c i ≠ ⊤) :
    Measure.pi (fun i ↦ c i • ν i) = (∏ i, c i) • Measure.pi ν := by
  let (i : ι) : IsFiniteMeasure (c i • ν i) := ⟨by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr (hc i)) (measure_lt_top _ _)⟩
  apply Measure.pi_eq
  intro s _
  simp only [Measure.smul_apply, Measure.pi_pi, smul_eq_mul, Finset.prod_mul_distrib]
end StepA4
end

-- SmallSpouseTotalLog
section
open Filter MeasureTheory Set StableMarriage
open scoped ENNReal BigOperators Topology
namespace StepA4
private theorem femaleSpouseStabilityDensity_le_smallCutoff {n : ℕ} {y : Fin n → ℝ}
    (hy : ∀ i, y i ∈ Icc (0 : ℝ) 1) {L : ℝ}
    (hY : 0 < spouseVectorTotal y) (hL : spouseVectorTotal y ≤ L) :
    femaleSpouseStabilityDensity y ≤ ENNReal.ofReal
      (Real.exp L * Real.exp (-(n : ℝ) * Real.exp (-L)) / spouseVectorTotal y ^ n) := by
  have hrow (i : Fin n) : 0 ≤ scoreRowMass (Finset.univ.erase i) y 0 1 := by
    unfold scoreRowMass
    refine intervalIntegral.integral_nonneg (by norm_num) fun t ht ↦ ?_
    unfold scoreRowKernel
    exact Finset.prod_nonneg fun j _ ↦ sub_nonneg.mpr
      ((mul_le_mul_of_nonneg_right ht.2 (hy j).1).trans (by simpa using (hy j).2))
  rw [femaleSpouseStabilityDensity, ← ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ hrow i)]
  apply ENNReal.ofReal_le_ofReal
  let Y := spouseVectorTotal y
  have hq : 0 ≤ 1 - Real.exp (-Y) := sub_nonneg.mpr
    (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hY.le))
  have hpow : (1 - Real.exp (-Y)) ^ n ≤ Real.exp (-(n : ℝ) * Real.exp (-L)) := calc
    _ ≤ (Real.exp (-(Real.exp (-Y)))) ^ n :=
      pow_le_pow_left₀ hq (Real.one_sub_le_exp_neg _) _
    _ = Real.exp (-(n : ℝ) * Real.exp (-Y)) := by rw [← Real.exp_nat_mul]; ring_nf
    _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left
      (Real.exp_le_exp.mpr (neg_le_neg hL)) (neg_nonpos.mpr (Nat.cast_nonneg _)))
  calc
    _ ≤ Real.exp Y * ((1 - Real.exp (-Y)) / Y) ^ n := by
      simpa only [Y, spouseVectorTotal, Fintype.card_fin] using
        scoreRowMass_prod_le_finite_exp y hy hY
    _ = Real.exp Y * (1 - Real.exp (-Y)) ^ n / Y ^ n := by rw [div_pow, mul_div_assoc]
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul (Real.exp_le_exp.mpr hL) hpow (pow_nonneg hq _) (Real.exp_pos _).le)
      (pow_nonneg hY.le _)
private theorem factorial_mul_radial_mid_le {n : ℕ} (hn : 0 < n) {C L : ℝ}
    (hC : 0 ≤ C) :
    (n.factorial : ℝ≥0∞) *
        (∫⁻ s in Ioc (1 / 2 : ℝ) L, ENNReal.ofReal (C / s ^ n) ∂spouseRadialLaw n) ≤
      ENNReal.ofReal (2 * (n : ℝ) * C * L) := by
  let A := Ioc (1 / 2 : ℝ) L
  let g (s : ℝ) := ENNReal.ofReal (C / s ^ n)
  let f (s : ℝ) := ENNReal.ofReal (s ^ (n - 1) / ((n - 1).factorial : ℝ))
  have hA : MeasurableSet A := measurableSet_Ioc
  have hf : Measurable f := by unfold f; fun_prop
  have hg : Measurable g := by unfold g; fun_prop
  have hAZ : A ∩ Ioi (0 : ℝ) = A := inter_eq_left.mpr fun _ hs ↦
    (by norm_num : (0 : ℝ) < 1 / 2).trans hs.1
  have hrewrite :
      (∫⁻ s in A, g s ∂spouseRadialLaw n) =
        ∫⁻ s in A, f s * g s := by
    rw [← lintegral_indicator hA, spouseRadialLaw,
      lintegral_withDensity_eq_lintegral_mul _ hf (hg.indicator hA)]
    simp_rw [Pi.mul_apply, ← indicator_mul_right, lintegral_indicator hA,
      Measure.restrict_restrict hA, hAZ]
  have hfac : n.factorial = n * (n - 1).factorial := calc
    _ = (n - 1 + 1).factorial := by rw [Nat.sub_add_cancel hn]
    _ = _ := by rw [Nat.factorial_succ, Nat.sub_add_cancel hn]
  change (n.factorial : ℝ≥0∞) * (∫⁻ s in A, g s ∂spouseRadialLaw n) ≤ _
  rw [hrewrite, ← lintegral_const_mul' _ _ (by simp)]
  calc
    _ ≤ ∫⁻ _ in A, ENNReal.ofReal (2 * (n : ℝ) * C) := by
      apply setLIntegral_mono' hA
      intro s hs
      have hs₀ : 0 < s := (by norm_num : (0 : ℝ) < 1 / 2).trans hs.1
      have hpow : s ^ n = s ^ (n - 1) * s := by rw [← pow_succ, Nat.sub_add_cancel hn]
      unfold f g
      rw [← ENNReal.ofReal_mul (div_nonneg (pow_nonneg hs₀.le _) (Nat.cast_nonneg _)),
        ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      have he : (n.factorial : ℝ) * (s ^ (n - 1) / ((n - 1).factorial : ℝ) *
          (C / s ^ n)) = (n : ℝ) * C / s := by
        rw [hfac, Nat.cast_mul, hpow]
        field_simp
      rw [he, div_le_iff₀ hs₀]
      nlinarith [mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hC) (sub_nonneg.mpr hs.1.le)]
    _ = ENNReal.ofReal (2 * (n : ℝ) * C) * ENNReal.ofReal (L - 1 / 2) := by
      rw [setLIntegral_const]
      change _ * volume (Ioc (1 / 2 : ℝ) L) = _
      rw [Real.volume_Ioc]
    _ ≤ _ := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
private theorem measurable_spouseVectorTotal' (n : ℕ) :
    Measurable (@spouseVectorTotal n) :=
  Finset.measurable_sum _ fun i _ ↦ measurable_pi_apply i
private theorem ae_spouseVectorLaw_mem_unit (n : ℕ) :
    ∀ᵐ y ∂spouseVectorLaw n, ∀ i, y i ∈ Icc (0 : ℝ) 1 := by
  rw [spouseVectorLaw_eq_restrict_volume]
  have hC : MeasurableSet (univ.pi fun _ : Fin n ↦ Icc (0 : ℝ) 1) :=
    (measurableSet_pi countable_univ).2 (Or.inl fun _ _ ↦ measurableSet_Icc)
  filter_upwards [ae_restrict_mem (μ := (volume : Measure (Fin n → ℝ))) hC] with y hy
  exact fun i ↦ hy i (mem_univ i)
private theorem factorial_mul_femaleSpouse_near_le (n : ℕ) :
    (n.factorial : ℝ≥0∞) *
      (∫⁻ y in {y : Fin n → ℝ | spouseVectorTotal y ≤ 1 / 2},
        femaleSpouseStabilityDensity y ∂spouseVectorLaw n) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ n) := by
  let A := {y : Fin n → ℝ | spouseVectorTotal y ≤ 1 / 2}
  let S := scoreSimplex n (1 / 2)
  have hA : MeasurableSet A :=
    measurableSet_le (measurable_spouseVectorTotal' n) measurable_const
  have hS : MeasurableSet S := measurableSet_scoreSimplex n _
  have hbound : (∫⁻ y in A, femaleSpouseStabilityDensity y ∂spouseVectorLaw n) ≤ volume S := calc
    _ = ∫⁻ y, A.indicator femaleSpouseStabilityDensity y ∂spouseVectorLaw n :=
      (lintegral_indicator hA _).symm
    _ ≤ ∫⁻ y, S.indicator (fun _ ↦ 1) y ∂spouseVectorLaw n := by
      apply lintegral_mono_ae
      filter_upwards [ae_spouseVectorLaw_mem_unit n] with y hy
      by_cases h : y ∈ A
      · have hs : y ∈ S := ⟨fun i ↦ (hy i).1, h⟩
        rw [indicator_of_mem h, indicator_of_mem hs]
        exact femaleSpouseStabilityDensity_le_one y hy
      · rw [indicator_of_notMem h]
        exact zero_le
    _ ≤ ∫⁻ y, S.indicator (fun _ ↦ 1) y := lintegral_mono' (spouseVectorLaw_le_volume n) le_rfl
    _ = _ := lintegral_indicator_one hS
  refine (mul_le_mul_right hbound _).trans_eq ?_
  change (n.factorial : ℝ≥0∞) * volume (scoreSimplex n (1 / 2)) = _
  rw [volume_scoreSimplex n (by norm_num), ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  congr 1
  field_simp [show (n.factorial : ℝ) ≠ 0 by positivity]
private theorem factorial_mul_femaleSpouse_mid_le {n : ℕ} (hn : 0 < n)
    (L : ℝ) :
    (n.factorial : ℝ≥0∞) *
      (∫⁻ y in {y : Fin n → ℝ | spouseVectorTotal y ∈ Ioc (1 / 2) L},
        femaleSpouseStabilityDensity y ∂spouseVectorLaw n) ≤
      ENNReal.ofReal (2 * (n : ℝ) * (Real.exp L * Real.exp (-(n : ℝ) * Real.exp (-L))) * L) := by
  let A := Ioc (1 / 2 : ℝ) L
  let R : Set (Fin n → ℝ) := spouseVectorTotal ⁻¹' A
  let C := Real.exp L * Real.exp (-(n : ℝ) * Real.exp (-L))
  let g (s : ℝ) := ENNReal.ofReal (C / s ^ n)
  let G (y : Fin n → ℝ) := A.indicator g (spouseVectorTotal y)
  have hA : MeasurableSet A := measurableSet_Ioc
  have hR : MeasurableSet R := hA.preimage (measurable_spouseVectorTotal' n)
  have hg : Measurable g := by unfold g; fun_prop
  have hG : Measurable G := (hg.indicator hA).comp (measurable_spouseVectorTotal' n)
  have hsub : spouseVectorLaw n ≤ (volume : Measure (Fin n → ℝ)).restrict
      {y | ∀ i, 0 ≤ y i} := by
    have hsubset : (univ.pi fun _ : Fin n ↦ Icc (0 : ℝ) 1) ⊆
        {y : Fin n → ℝ | ∀ i, 0 ≤ y i} := by
      intro y hy i
      exact (hy i (mem_univ i)).1
    rw [spouseVectorLaw_eq_restrict_volume]
    exact Measure.restrict_mono hsubset le_rfl
  have hbound :
      (∫⁻ y in R, femaleSpouseStabilityDensity y ∂spouseVectorLaw n) ≤
        ∫⁻ s in A, g s ∂spouseRadialLaw n := calc
    _ = ∫⁻ y, R.indicator femaleSpouseStabilityDensity y ∂spouseVectorLaw n :=
      (lintegral_indicator hR _).symm
    _ ≤ ∫⁻ y, G y ∂spouseVectorLaw n := by
      apply lintegral_mono_ae
      filter_upwards [ae_spouseVectorLaw_mem_unit n] with y hy
      by_cases h : spouseVectorTotal y ∈ A
      · change R.indicator femaleSpouseStabilityDensity y ≤ A.indicator g (spouseVectorTotal y)
        rw [indicator_of_mem (show y ∈ R from h), indicator_of_mem h]
        exact femaleSpouseStabilityDensity_le_smallCutoff hy
          ((by norm_num : (0 : ℝ) < 1 / 2).trans h.1) h.2
      · rw [indicator_of_notMem (show y ∉ R from h)]
        exact zero_le
    _ ≤ ∫⁻ y, G y ∂(volume.restrict {y | ∀ i, 0 ≤ y i}) := lintegral_mono' hsub le_rfl
    _ = _ := by
      rw [lintegral_spouseRadialAngular hn hG, ← lintegral_indicator hA]
      apply lintegral_congr
      intro s
      have h_inner : (∫⁻ w, G (fun i ↦ s * w i) ∂spouseAngularLaw n) =
          ∫⁻ _w, A.indicator g s ∂spouseAngularLaw n := by
        apply lintegral_congr_ae
        filter_upwards [ae_spouseAngularLaw hn] with w hw
        have hsum : spouseVectorTotal (fun i ↦ s * w i) = s := by
          rw [spouseVectorTotal, ← Finset.mul_sum, hw.2, mul_one]
        change A.indicator g (spouseVectorTotal (fun i ↦ s * w i)) = A.indicator g s
        rw [hsum]
      rw [h_inner, lintegral_const, measure_univ, mul_one]
  exact (mul_le_mul_right hbound _).trans (factorial_mul_radial_mid_le hn (by positivity))
theorem sum_stable_smallSpouseTotal_le {n : ℕ} (hn : 0 < n) (L : ℝ) :
    (∑ μ : Matching n, continuousScoreLaw n
      {x | IsScoreStable x μ ∧ femaleSpouseTotal x μ < L}) ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ n) +
        ENNReal.ofReal (2 * (n : ℝ) * (Real.exp L * Real.exp (-(n : ℝ) * Real.exp (-L))) * L) := by
  let S := {y : Fin n → ℝ | spouseVectorTotal y < L}
  let A := {y : Fin n → ℝ | spouseVectorTotal y ≤ 1 / 2}
  let B := {y : Fin n → ℝ | spouseVectorTotal y ∈ Ioc (1 / 2) L}
  have hS : MeasurableSet S := measurableSet_lt (measurable_spouseVectorTotal' n) measurable_const
  have hsub : S ⊆ A ∪ B := by
    intro y hy
    rcases le_or_gt (spouseVectorTotal y) (1 / 2) with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, (show spouseVectorTotal y < L from hy).le⟩
  have he (μ : Matching n) :
      {x | IsScoreStable x μ ∧ femaleSpouseTotal x μ < L} =
        {x | IsScoreStable x μ ∧ femaleSpouseByHusband μ x ∈ S} := by
    ext x
    change (IsScoreStable x μ ∧ femaleSpouseTotal x μ < L) ↔
      IsScoreStable x μ ∧ spouseVectorTotal (femaleSpouseByHusband μ x) < L
    rw [femaleSpouseTotal_eq_sum_byHusband, spouseVectorTotal]
  simp_rw [he, continuousScoreLaw_stable_and_femaleSpouse _ hS]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  calc
    _ ≤ (n.factorial : ℝ≥0∞) *
        ((∫⁻ y in A, femaleSpouseStabilityDensity y ∂spouseVectorLaw n) +
          (∫⁻ y in B, femaleSpouseStabilityDensity y ∂spouseVectorLaw n)) :=
      mul_le_mul_right ((lintegral_mono_set hsub).trans
        (lintegral_union_le femaleSpouseStabilityDensity A B)) _
    _ ≤ _ := by
      rw [mul_add]
      exact add_le_add (factorial_mul_femaleSpouse_near_le n)
        (factorial_mul_femaleSpouse_mid_le hn L)
theorem eventually_sum_stable_smallSpouseTotalLog_le (p : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      (∑ μ : Matching n, continuousScoreLaw n
        {x | IsScoreStable x μ ∧ femaleSpouseTotal x μ < (9 / 10 : ℝ) * Real.log n}) ≤
        ENNReal.ofReal ((n : ℝ) ^ (-p)) := by
  have hcast : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hnear : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ p * Real.exp (-(n : ℝ) / 2))
      atTop (𝓝 0) := by
    refine ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero p (1 / 2) (by norm_num)).comp
      hcast).congr fun n ↦ ?_
    simp only [Function.comp_apply]
    congr 2
    ring
  have hmidReal : Tendsto (fun x : ℝ ↦ x ^ (p + 3) * Real.exp (-(x ^ (1 / 10 : ℝ))))
      atTop (𝓝 0) := by
    refine ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (10 * (p + 3)) 1
      (by norm_num)).comp (tendsto_rpow_atTop (by norm_num : 0 < (1 / 10 : ℝ)))).congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    simp only [Function.comp_apply, neg_one_mul, ← Real.rpow_mul hx]
    rw [show (1 / 10 : ℝ) * (10 * (p + 3)) = p + 3 by ring]
  have hmid := hmidReal.comp hcast
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    hnear.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2),
    hmid.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 4)] with n hn hnearN hmidN
  have hn₀ : 0 < n := Nat.zero_lt_of_lt hn
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn₀
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  let L := (9 / 10 : ℝ) * Real.log n
  have hlog := Real.log_nonneg hn1
  have hL : 0 ≤ L := mul_nonneg (by norm_num) hlog
  have hLlog : L ≤ Real.log n := mul_le_of_le_one_left hlog (by norm_num)
  have hexp : Real.exp L ≤ n := (Real.exp_le_exp.mpr hLlog).trans_eq (Real.exp_log hnR)
  have hLn : L ≤ n := hLlog.trans (by linarith [Real.log_le_sub_one_of_pos hnR])
  have hsmall : (1 / 2 : ℝ) ^ n ≤ Real.exp (-(n : ℝ) / 2) := calc
    _ ≤ Real.exp (-(1 / 2 : ℝ)) ^ n := pow_le_pow_left₀ (by norm_num)
      (by simpa only [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] using
        Real.one_sub_le_exp_neg (1 / 2 : ℝ)) _
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hcut : (n : ℝ) * Real.exp (-L) = (n : ℝ) ^ (1 / 10 : ℝ) := by
    have he : Real.exp (-L) = (n : ℝ) ^ (-(9 / 10) : ℝ) := by
      rw [Real.rpow_def_of_pos hnR]
      congr 1
      dsimp only [L]
      ring
    calc
      _ = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-(9 / 10) : ℝ) := by rw [Real.rpow_one, he]
      _ = _ := by rw [← Real.rpow_add hnR]; norm_num
  let E := Real.exp (-(n : ℝ) * Real.exp (-L))
  have hE : E = Real.exp (-((n : ℝ) ^ (1 / 10 : ℝ))) := by
    rw [show E = Real.exp (-((n : ℝ) * Real.exp (-L))) by simp only [E, neg_mul], hcut]
  have hmiddle : 2 * (n : ℝ) * (Real.exp L * E) * L ≤ 2 * (n : ℝ) ^ 3 * E := calc
    _ = 2 * (n : ℝ) * Real.exp L * L * E := by ring
    _ ≤ 2 * (n : ℝ) * n * n * E := by gcongr
    _ = _ := by ring
  have hnearFinal : (n : ℝ) ^ p * ((1 / 2 : ℝ) ^ n) ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left hsmall (Real.rpow_nonneg hnR.le _)).trans hnearN.le
  have hmidFinal : (n : ℝ) ^ p * (2 * (n : ℝ) * (Real.exp L * E) * L) ≤ 1 / 2 := calc
    _ ≤ (n : ℝ) ^ p * (2 * (n : ℝ) ^ 3 * E) :=
      mul_le_mul_of_nonneg_left hmiddle (Real.rpow_nonneg hnR.le _)
    _ = 2 * ((n : ℝ) ^ p * (n : ℝ) ^ 3 * E) := by ring
    _ = 2 * ((n : ℝ) ^ (p + 3) * Real.exp (-((n : ℝ) ^ (1 / 10 : ℝ)))) := by
      rw [hE, ← Real.rpow_natCast (n : ℝ) 3, ← Real.rpow_add hnR]
      norm_num
    _ ≤ _ := by linarith [show (n : ℝ) ^ (p + 3) *
        Real.exp (-((n : ℝ) ^ (1 / 10 : ℝ))) < 1 / 4 from hmidN]
  refine (sum_stable_smallSpouseTotal_le hn₀ L).trans ?_
  change ENNReal.ofReal ((1 / 2 : ℝ) ^ n) +
    ENNReal.ofReal (2 * (n : ℝ) * (Real.exp L * E) * L) ≤ _
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [Real.rpow_neg hnR.le, ← one_div]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hnR _)).2
  rw [mul_comm, mul_add]
  exact (add_le_add hnearFinal hmidFinal).trans_eq (by norm_num)
end StepA4
end

-- MeanUpperBound
section
open Filter MeasureTheory Set StableMarriage
open scoped ENNReal BigOperators Topology
namespace StepA4
private noncomputable def meanUpperConstant : ℝ := Real.exp 2 + 1
theorem meanUpperConstant_nonneg : 0 ≤ meanUpperConstant := by
  unfold meanUpperConstant
  positivity
theorem eventually_expectedNumStableMatchings_le_meanUpper :
    ∀ᶠ n : ℕ in atTop, expectedNumStableMatchings n ≤
      meanUpperConstant * ((n : ℝ) * Real.log n) := by
  filter_upwards [eventually_sum_stable_smallSpouseTotalLog_le 0,
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 3,
    eventually_ge_atTop (2 : ℕ)] with n hsmall hlog hn
  change 3 ≤ Real.log (n : ℝ) at hlog
  have hnR : 2 ≤ (n : ℝ) := by exact_mod_cast hn
  have hscale : 1 ≤ (n : ℝ) * Real.log n :=
    one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)
  let A (μ : Matching n) : Set (ScoreProfile n) :=
    {x | IsScoreStable x μ ∧ femaleSpouseTotal x μ < (9 / 10 : ℝ) * Real.log n}
  let B (μ : Matching n) : Set (ScoreProfile n) :=
    {x | IsScoreStable x μ ∧ 2 ≤ femaleSpouseTotal x μ}
  have hcover (μ : Matching n) : {x | IsScoreStable x μ} ⊆ A μ ∪ B μ := by
    intro x hx
    rcases le_or_gt 2 (femaleSpouseTotal x μ) with h | h
    · exact Or.inr ⟨hx, h⟩
    · exact Or.inl ⟨hx, by linarith⟩
  have hbulk : (∑ μ : Matching n, continuousScoreLaw n (B μ)) ≤
      ENNReal.ofReal (Real.exp 2 * n * Real.log n) := by
    simpa [B] using sum_measure_scoreStable_and_femaleSpouseAngle_le hn
      (A := Set.univ) MeasurableSet.univ
  apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg meanUpperConstant_nonneg
    (zero_le_one.trans hscale))).mp
  rw [← sum_measure_scoreStable_eq_expected]
  calc
    _ ≤ ∑ μ : Matching n, (continuousScoreLaw n (A μ) + continuousScoreLaw n (B μ)) :=
      Finset.sum_le_sum fun μ _ ↦ (measure_mono (hcover μ)).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal 1 + ENNReal.ofReal (Real.exp 2 * n * Real.log n) := by
      rw [Finset.sum_add_distrib]
      exact add_le_add (by simpa [A] using hsmall) hbulk
    _ ≤ _ := by
      rw [← ENNReal.ofReal_add (by norm_num) (by positivity)]
      exact ENNReal.ofReal_le_ofReal (by unfold meanUpperConstant; linarith only [hscale])
end StepA4
end

-- PivotSpouseProductLower
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace StepA4
private def maleSpouseTotal {n : ℕ} (x : ScoreProfile n) (μ : Matching n) : ℝ :=
  ∑ i, maleSpouseScore x μ i
private def lowSpouseProductVectorSet (n : ℕ) : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  {z | 2 ≤ spouseVectorTotal z.2 ∧
    spouseVectorTotal z.1 * spouseVectorTotal z.2 < (n : ℝ) / 128}
end StepA4
end

-- PivotForwardRevealCell
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace StepA4
private def forwardEligibleScoreCell (x y : ℝ) : Set (ℝ × ℝ) :=
  Ioi x ×ˢ Iio y
private abbrev OffDiagonalCellIndex (n : ℕ) := {q : ScorePairIndex n // q.1 ≠ q.2}
private abbrev ForwardActiveCellIndex {n : ℕ} (flag : OffDiagonalCellIndex n → Bool) :=
  {q : OffDiagonalCellIndex n // flag q = true}
private abbrev ForwardInactiveCellIndex {n : ℕ} (flag : OffDiagonalCellIndex n → Bool) :=
  {q : OffDiagonalCellIndex n // flag q ≠ true}
private def forwardScoreMaskRevealAndInactive {n : ℕ} (flag : OffDiagonalCellIndex n → Bool)
    (z : OffDiagonalScorePairs n) :
    (ForwardActiveCellIndex flag → ℝ) × (ForwardInactiveCellIndex flag → ℝ × ℝ) :=
  (fun q ↦ (z q.val).1, fun q ↦ z q.val)
private abbrev ForwardInactiveColumnIndex {n : ℕ} (flag : OffDiagonalCellIndex n → Bool)
    (j : Fin n) := {q : ForwardInactiveCellIndex flag // q.val.val.2 = j}
private def forwardInactiveColumnsEquiv {n : ℕ} (flag : OffDiagonalCellIndex n → Bool) :
    (ForwardInactiveCellIndex flag → ℝ × ℝ) ≃ᵐ
      ((j : Fin n) → ForwardInactiveColumnIndex flag j → ℝ × ℝ) where
  toFun z _ q := z q.val
  invFun z q := z q.val.val.2 ⟨q, rfl⟩
  left_inv _ := rfl
  right_inv z := by
    funext j q
    obtain ⟨q, rfl⟩ := q
    rfl
  measurable_toFun := measurable_pi_iff.2 fun _ ↦
    measurable_pi_iff.2 fun _ ↦ measurable_pi_apply _
  measurable_invFun := measurable_pi_iff.2 fun q ↦
    (measurable_pi_apply (⟨q, rfl⟩ : ForwardInactiveColumnIndex flag q.val.val.2)).comp
      (measurable_pi_apply q.val.val.2)
end StepA4
end

-- PivotReverseEligibility
section
open MeasureTheory Set
open scoped ENNReal
namespace StepA4
end StepA4
end

-- PivotReverseRowLaw
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace StepA4
variable {ι : Type*}
end StepA4
end

-- ReverseSuccessorIncrement
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace StepA4
variable {ι : Type*}
end StepA4
end

-- ReverseCompatibilityRectangle
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace StepA4
end StepA4
end

-- PivotReverseRelaxedColumn
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace StepA4
end StepA4
end

-- ReverseSuccessorRotation
section
open StableMarriage
namespace StepA4
variable {n : ℕ} {p : Profile n} {μ : Matching n} {ρ : Equiv.Perm (Fin n)}
private def swapProfile (p : Profile n) : Profile n :=
  ⟨p.womanRank, p.manRank⟩
@[simp] theorem swapProfile_swapProfile (p : Profile n) : swapProfile (swapProfile p) = p := rfl
theorem isStable_swapProfile_iff : IsStable (swapProfile p) μ.symm ↔ IsStable p μ := by
  constructor
  · intro h m w hb
    exact h w m
      ⟨fun he ↦ hb.1 ((congrArg μ he).symm.trans (μ.apply_symm_apply w)), hb.2.2, hb.2.1⟩
  · intro h w m hb
    refine h m w ⟨fun he ↦ hb.1 ?_, hb.2.2, hb.2.1⟩
    simpa only [Equiv.symm_apply_apply] using (congrArg μ.symm he).symm
private def reverseRotationCycle (μ : Matching n) (ρ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) :=
  μ.symm.trans (ρ.trans μ)
theorem IsExposedRotation.isExposedRotation_swap_eliminate
    (hρ : IsExposedRotation p μ ρ) (hμ : IsStable p μ) :
    IsExposedRotation (swapProfile p) (eliminateRotation μ ρ).symm
      (reverseRotationCycle μ ρ) := by
  refine (IsExposedRotation.mk (?_) (?_))
  · change (μ * ρ * μ⁻¹).IsCycle
    exact (IsExposedRotation.isCycle hρ).conj
  · intro w hw
    obtain ⟨m, rfl⟩ := μ.surjective w
    have hm : ρ m ≠ m := by
      intro he
      apply hw
      simp [reverseRotationCycle, he]
    have hback : ρ (ρ.symm m) ≠ ρ.symm m := by
      intro he
      have he' : m = ρ.symm m := by simpa only [Equiv.apply_symm_apply] using he
      exact hm ((congrArg ρ he').trans (ρ.apply_symm_apply m))
    have hnew : (eliminateRotation μ ρ).symm (reverseRotationCycle μ ρ (μ m)) = m := by
      simp [reverseRotationCycle, eliminateRotation]
    have hcurrent : (eliminateRotation μ ρ).symm (μ m) = ρ.symm m := by
      simp [eliminateRotation]
    refine IsSuccessor.mk ?_ ?_
    · have hprev := (IsSuccessor.eligible ((IsExposedRotation.successor hρ) (ρ.symm m) hback)).2
      have hwlt : p.womanRank (μ m) (ρ.symm m) < p.womanRank (μ m) m := by
        simpa only [Equiv.apply_symm_apply, Equiv.symm_apply_apply] using hprev
      simp only [IsEligibleSuccessor, swapProfile, hnew, hcurrent, Equiv.symm_symm,
        eliminateRotation_apply]
      exact ⟨hwlt, (IsSuccessor.eligible ((IsExposedRotation.successor hρ) m hm)).1⟩
    · intro t ht
      simp only [IsEligibleSuccessor, swapProfile, hcurrent, Equiv.symm_symm,
        eliminateRotation_apply] at ht
      change p.womanRank (μ m) ((eliminateRotation μ ρ).symm
        (reverseRotationCycle μ ρ (μ m))) ≤ p.womanRank (μ m) t
      rw [hnew]
      by_contra hbad
      
      have hwbad := lt_of_not_ge hbad
      have hne : μ t ≠ μ m := fun he ↦
        (ne_of_lt hwbad) (congrArg (p.womanRank (μ m)) (μ.injective he))
      have hnot : ¬ p.manRank t (μ m) < p.manRank t (μ t) := fun ht' ↦
        hμ t (μ m) ⟨hne, ht', by simpa only [Equiv.symm_apply_apply] using hwbad⟩
      have hf : IsEligibleSuccessor p μ t (μ m) :=
        ⟨lt_of_le_of_ne (le_of_not_gt hnot) (fun he ↦ hne ((p.manRank t).injective he)),
          by simpa only [Equiv.symm_apply_apply] using hwbad⟩
      by_cases htfix : ρ t = t
      · exact (not_lt_of_ge hf.1.le) (by simpa only [htfix] using ht.2)
      · exact (not_lt_of_ge ((IsSuccessor.min_rank ((IsExposedRotation.successor hρ) t htfix)) _ hf)) ht.2
end StepA4
end

-- PivotReverseScoreSuccessor
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA4
end StepA4
end

-- PivotRelaxedArcEvents
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace StepA4
end StepA4
end

-- FinitePrerequisites
section
namespace StepA4
theorem mem_family_of_downward_closed {α : Type*} [Finite α] {F : Set (Set α)}
    (hempty : ∅ ∈ F)
    (hinter : ∀ ⦃A B⦄, A ∈ F → B ∈ F → A ∩ B ∈ F)
    (hunion : ∀ ⦃A B⦄, A ∈ F → B ∈ F → A ∪ B ∈ F)
    (hcover : ∀ a : α, ∃ A ∈ F, a ∈ A) {I : Set α}
    (hdown : ∀ ⦃a b : α⦄, (∀ A ∈ F, b ∈ A → a ∈ A) → b ∈ I → a ∈ I) :
    I ∈ F := by
  
  let P (b : α) : Set α := ⋂₀ {A : Set α | A ∈ F ∧ b ∈ A}
  have hInf : InfClosed F := fun _ hA _ hB ↦ hinter hA hB
  have hP (b : α) : P b ∈ F := by
    obtain ⟨A, hA, hbA⟩ := hcover b
    change sInf {A : Set α | A ∈ F ∧ b ∈ A} ∈ F
    exact hInf.sInf_mem_of_nonempty (Set.toFinite _) ⟨A, hA, hbA⟩ fun _ h ↦ h.1
  
  have hEq : I = ⋃ b : I, P b := by
    ext a
    constructor
    · intro ha
      exact Set.mem_iUnion_of_mem ⟨a, ha⟩ (Set.mem_sInter.mpr fun _ h ↦ h.2)
    · intro ha
      obtain ⟨b, hab⟩ := Set.mem_iUnion.mp ha
      exact hdown (fun A hA hb ↦ Set.mem_sInter.mp hab A ⟨hA, hb⟩) b.property
  have hSup : SupClosed F := fun _ hA _ hB ↦ hunion hA hB
  rw [hEq]
  exact hSup.iSup_mem hempty fun b : I ↦ hP b
end StepA4
end

-- RotationDiamond
section
open StableMarriage
namespace StepA4
variable {n : ℕ} {p : Profile n} {μ : Matching n} {ρ σ : Equiv.Perm (Fin n)}
private theorem moved_image {f : Equiv.Perm (Fin n)} {i : Fin n} (hi : f i ≠ i) :
    f (f i) ≠ f i :=
  f.injective.ne hi
private theorem eq_of_common_moved (hρ : IsExposedRotation p μ ρ) (hσ : IsExposedRotation p μ σ)
    {m : Fin n} (hmρ : ρ m ≠ m) (hmσ : σ m ≠ m) : ρ = σ := by
  have hagree (i : Fin n) (hiρ : ρ i ≠ i) (hiσ : σ i ≠ i) : ρ i = σ i :=
    μ.injective (((IsExposedRotation.successor hρ) i hiρ).unique ((IsExposedRotation.successor hσ) i hiσ))
  have horbit (k : ℕ) :
      (ρ ^ k) m = (σ ^ k) m ∧ ρ ((ρ ^ k) m) ≠ (ρ ^ k) m ∧ σ ((σ ^ k) m) ≠ (σ ^ k) m := by
    induction k with
    | zero => simpa using And.intro (rfl : m = m) (And.intro hmρ hmσ)
    | succ k ih =>
      obtain ⟨heq, hmoveρ, hmoveσ⟩ := ih
      have hmoveσ' : σ ((ρ ^ k) m) ≠ (ρ ^ k) m := heq ▸ hmoveσ
      simp only [pow_succ', Equiv.Perm.mul_apply]
      exact ⟨(hagree _ hmoveρ hmoveσ').trans (congrArg σ heq),
        moved_image hmoveρ, moved_image hmoveσ⟩
  apply Equiv.ext
  intro i
  by_cases hi : ρ i ≠ i
  · obtain ⟨k, hk⟩ := (IsExposedRotation.isCycle hρ).exists_pow_eq hmρ hi
    have his : σ i ≠ i := by
      rw [← hk, (horbit k).1]
      exact (horbit k).2.2
    exact hagree i hi his
  · have his : σ i = i := by
      by_contra hsi
      obtain ⟨k, hk⟩ := (IsExposedRotation.isCycle hσ).exists_pow_eq hmσ hsi
      apply hi
      rw [← hk, ← (horbit k).1]
      exact (horbit k).2.1
    exact (not_ne_iff.mp hi).trans his.symm
theorem IsExposedRotation.disjoint_moved (hρ : IsExposedRotation p μ ρ)
    (hσ : IsExposedRotation p μ σ) (hne : ρ ≠ σ) (m : Fin n) (hm : ρ m ≠ m) : σ m = m := by
  by_contra hs
  exact hne (eq_of_common_moved hρ hσ hm hs)
theorem IsExposedRotation.persist_eliminate (hρ : IsExposedRotation p μ ρ)
    (hσ : IsExposedRotation p μ σ) (hne : ρ ≠ σ) :
    IsExposedRotation p (eliminateRotation μ σ) ρ := by
  refine (IsExposedRotation.mk ((IsExposedRotation.isCycle hρ)) (fun m hm ↦ ?_))
  let μ' := eliminateRotation μ σ
  have hold : μ' m = μ m := congrArg μ (hρ.disjoint_moved hσ hne m hm)
  have hnext : μ' (ρ m) = μ (ρ m) :=
    congrArg μ (hρ.disjoint_moved hσ hne (ρ m) (moved_image hm))
  have hs := (IsExposedRotation.successor hρ) m hm
  have helig : IsEligibleSuccessor p μ' m (μ' (ρ m)) := by
    refine ⟨?_, ?_⟩
    · simpa only [hold, hnext] using (IsSuccessor.eligible hs).1
    · rw [Equiv.symm_apply_apply, hnext]
      simpa only [Equiv.symm_apply_apply] using (IsSuccessor.eligible hs).2
  refine (IsSuccessor.mk (helig) (fun w hw ↦ ?_))
  have hman : p.manRank m (μ' m) < p.manRank m w := hw.1
  rw [hold] at hman
  have hbefore : IsEligibleSuccessor p μ m w :=
    ⟨hman, hw.2.trans_le (hσ.womanRank_eliminate_le w)⟩
  change p.manRank m (μ' (ρ m)) ≤ p.manRank m w
  rw [hnext]
  exact (IsSuccessor.min_rank hs) w hbefore
theorem IsExposedRotation.eliminate_comm (hρ : IsExposedRotation p μ ρ)
    (hσ : IsExposedRotation p μ σ) (hne : ρ ≠ σ) :
    eliminateRotation (eliminateRotation μ ρ) σ = eliminateRotation (eliminateRotation μ σ) ρ := by
  apply Equiv.ext
  intro m
  simp only [eliminateRotation_apply]
  by_cases hr : ρ m = m
  · by_cases hs : σ m = m
    · simp only [hr, hs]
    · have hfix := hσ.disjoint_moved hρ hne.symm (σ m) (moved_image hs)
      simp only [hr, hfix]
  · have hfix := hρ.disjoint_moved hσ hne m hr
    have hfix' := hρ.disjoint_moved hσ hne (ρ m) (moved_image hr)
    simp only [hfix, hfix']
end StepA4
end

-- ManOptimal
section
open StableMarriage
open scoped BigOperators
namespace StepA4
variable {n : ℕ}
private def MenWeaklyPrefer (p : Profile n) (μ ν : Matching n) : Prop :=
  ∀ m, p.manRank m (μ m) ≤ p.manRank m (ν m)
private def IsManOptimal (p : Profile n) (μ : Matching n) : Prop :=
  IsStable p μ ∧ ∀ ν, IsStable p ν → MenWeaklyPrefer p μ ν
private def betterPartner (p : Profile n) (μ ν : Matching n) (m : Fin n) : Fin n :=
  if p.manRank m (μ m) ≤ p.manRank m (ν m) then μ m else ν m
private theorem betterPartner_spec (p : Profile n) (μ ν : Matching n) (m : Fin n) :
    (betterPartner p μ ν m = μ m ∨ betterPartner p μ ν m = ν m) ∧
      p.manRank m (betterPartner p μ ν m) ≤ p.manRank m (μ m) ∧
      p.manRank m (betterPartner p μ ν m) ≤ p.manRank m (ν m) := by
  unfold betterPartner
  split
  · rename_i h
    exact ⟨Or.inl rfl, le_rfl, h⟩
  · rename_i h
    exact ⟨Or.inr rfl, le_of_not_ge h, le_rfl⟩
private theorem woman_prefers_husband {p : Profile n} {μ : Matching n}
    (hμ : IsStable p μ) {m w : Fin n}
    (hm : p.manRank m w < p.manRank m (μ m)) :
    p.womanRank w (μ.symm w) < p.womanRank w m := by
  have hneq : μ m ≠ w := fun h ↦ hm.ne (congrArg (p.manRank m) h.symm)
  have hn : ¬ p.womanRank w m < p.womanRank w (μ.symm w) :=
    fun h ↦ hμ m w ⟨hneq, hm, h⟩
  exact lt_of_le_of_ne (le_of_not_gt hn) fun h ↦
    hneq ((Equiv.symm_apply_eq μ).mp ((p.womanRank w).injective h)).symm
private theorem betterPartner_injective {p : Profile n} {μ ν : Matching n}
    (hμ : IsStable p μ) (hν : IsStable p ν) :
    Function.Injective (betterPartner p μ ν) := by
  let f := betterPartner p μ ν
  have hcross (a b : Fin n) (ha : f a = μ a) (hb : f b = ν b) (h : f a = f b) :
      a = b := by
    by_contra hab
    have haw : μ a = f a := ha.symm
    have hbw : ν b = f a := hb.symm.trans h.symm
    have haν : p.manRank a (f a) < p.manRank a (ν a) :=
      lt_of_le_of_ne (betterPartner_spec p μ ν a).2.2 fun e ↦
        hab (ν.injective (((p.manRank a).injective e).symm.trans hbw.symm))
    have hbμ : p.manRank b (f a) < p.manRank b (μ b) :=
      lt_of_le_of_ne (h.symm ▸ (betterPartner_spec p μ ν b).2.1) fun e ↦
        hab (μ.injective (haw.trans ((p.manRank b).injective e)))
    have hμhusband : μ.symm (f a) = a := (Equiv.symm_apply_eq μ).2 ha
    have hνhusband : ν.symm (f a) = b := (Equiv.symm_apply_eq ν).2 hbw.symm
    have hfab : p.womanRank (f a) a < p.womanRank (f a) b :=
      by simpa only [hμhusband] using woman_prefers_husband hμ hbμ
    have hfba : p.womanRank (f a) b < p.womanRank (f a) a :=
      by simpa only [hνhusband] using woman_prefers_husband hν haν
    exact lt_asymm hfab hfba
  intro a b h
  rcases (betterPartner_spec p μ ν a).1 with ha | ha <;>
    rcases (betterPartner_spec p μ ν b).1 with hb | hb
  · exact μ.injective (ha.symm.trans (h.trans hb))
  · exact hcross a b ha hb h
  · exact (hcross b a hb ha h.symm).symm
  · exact ν.injective (ha.symm.trans (h.trans hb))
theorem exists_stable_manRank_min {p : Profile n} {μ ν : Matching n}
    (hμ : IsStable p μ) (hν : IsStable p ν) :
    ∃ τ, IsStable p τ ∧
      ∀ m, p.manRank m (τ m) = min (p.manRank m (μ m)) (p.manRank m (ν m)) := by
  have hinj := betterPartner_injective hμ hν
  let τ : Matching n := Equiv.ofBijective (betterPartner p μ ν)
    ⟨hinj, Finite.surjective_of_injective hinj⟩
  have hleft : MenWeaklyPrefer p τ μ := fun m ↦ (betterPartner_spec p μ ν m).2.1
  have hright : MenWeaklyPrefer p τ ν := fun m ↦ (betterPartner_spec p μ ν m).2.2
  refine ⟨τ, ?_, fun m ↦ ?_⟩
  · intro m w hb
    have conflict (σ : Matching n) (hσ : IsStable p σ) (hpref : MenWeaklyPrefer p τ σ)
        (hsource : τ (τ.symm w) = σ (τ.symm w)) : False := by
      have hhusband : σ.symm w = τ.symm w :=
        (Equiv.symm_apply_eq σ).2 ((τ.apply_symm_apply w).symm.trans hsource)
      have hm : p.manRank m w < p.manRank m (σ m) := hb.2.1.trans_le (hpref m)
      exact hσ m w ⟨fun he ↦ hm.ne (congrArg (p.manRank m) he.symm), hm,
        hhusband.symm ▸ hb.2.2⟩
    exact ((betterPartner_spec p μ ν (τ.symm w)).1).elim (conflict μ hμ hleft)
      (conflict ν hν hright)
  · have hsource : τ m = μ m ∨ τ m = ν m := (betterPartner_spec p μ ν m).1
    rcases hsource with h | h
    · have hle := hright m
      rw [h] at hle ⊢
      exact (min_eq_left hle).symm
    · have hle := hleft m
      rw [h] at hle ⊢
      exact (min_eq_right hle).symm
private def manOptimal_swapProfile (p : Profile n) : Profile n :=
  ⟨p.womanRank, p.manRank⟩
private theorem isStable_swap {p : Profile n} {μ : Matching n}
    (hμ : IsStable p μ) : IsStable (manOptimal_swapProfile p) μ.symm := by
  intro w m hb
  exact hμ m w ⟨fun h ↦ hb.1 ((Equiv.symm_apply_eq μ).2 h.symm), hb.2.2, hb.2.1⟩
theorem exists_stable_manRank_max {p : Profile n} {μ ν : Matching n}
    (hμ : IsStable p μ) (hν : IsStable p ν) :
    ∃ τ, IsStable p τ ∧
      ∀ m, p.manRank m (τ m) = max (p.manRank m (μ m)) (p.manRank m (ν m)) := by
  obtain ⟨σ, hσ, hmin⟩ := exists_stable_manRank_min (isStable_swap hμ) (isStable_swap hν)
  let τ := σ.symm
  have hw (w : Fin n) : p.womanRank w (τ.symm w) =
      min (p.womanRank w (μ.symm w)) (p.womanRank w (ν.symm w)) := hmin w
  
  have hworse (δ : Matching n) (hδ : IsStable p δ)
      (hδrank : ∀ w, p.womanRank w (τ.symm w) ≤ p.womanRank w (δ.symm w)) (m : Fin n) :
      p.manRank m (δ m) ≤ p.manRank m (τ m) := by
    by_contra h
    have hh := woman_prefers_husband hδ (lt_of_not_ge h)
    exact (not_lt_of_ge (hδrank (τ m))) (by simpa only [Equiv.symm_apply_apply] using hh)
  refine ⟨τ, isStable_swap hσ, fun m ↦ ?_⟩
  have hchoice : τ m = μ m ∨ τ m = ν m := by
    let w := τ m
    rcases le_total (p.womanRank w (μ.symm w)) (p.womanRank w (ν.symm w)) with h | h
    · have hhusband := (p.womanRank w).injective ((hw w).trans (min_eq_left h))
      exact Or.inl ((Equiv.symm_apply_eq μ).mp (hhusband.symm.trans (τ.symm_apply_apply m)))
    · have hhusband := (p.womanRank w).injective ((hw w).trans (min_eq_right h))
      exact Or.inr ((Equiv.symm_apply_eq ν).mp (hhusband.symm.trans (τ.symm_apply_apply m)))
  rcases hchoice with h | h
  · have hle := hworse ν hν (fun w ↦ (hw w).le.trans (min_le_right _ _)) m
    rw [h] at hle ⊢
    exact (max_eq_left hle).symm
  · have hle := hworse μ hμ (fun w ↦ (hw w).le.trans (min_le_left _ _)) m
    rw [h] at hle ⊢
    exact (max_eq_right hle).symm
end StepA4
end

-- RotationCycle
section
namespace StepA4
open Function
private theorem periodicPt_of_repeat {α : Type*} {f : α → α} {x : α} {i j : ℕ}
    (hij : i < j) (heq : f^[i] x = f^[j] x) :
    f^[i] x ∈ periodicPts f :=
  mk_mem_periodicPts (Nat.sub_pos_of_lt hij)
    (show f^[j - i] (f^[i] x) = f^[i] x by
      rw [← iterate_add_apply, Nat.sub_add_cancel hij.le, ← heq])
private theorem nonempty_periodicPts {α : Type*} [Finite α] [Nonempty α] (f : α → α) :
    (periodicPts f).Nonempty :=
  let x := Classical.choice (inferInstance : Nonempty α)
  have hrepeat : ∃ i j, f^[i] x = f^[j] x ∧ i ≠ j := by
    simpa [Injective] using not_injective_infinite_finite (f^[·] x)
  let ⟨i, j, heq, hne⟩ := hrepeat
  (lt_or_gt_of_ne hne).elim
    (fun h ↦ ⟨_, periodicPt_of_repeat h heq⟩)
    (fun h ↦ ⟨_, periodicPt_of_repeat h heq.symm⟩)
theorem exists_cycle_permutation {α : Type*} [Finite α] {s : Set α} [Nonempty s]
    (f : s → s) (hnf : ∀ x, f x ≠ x) :
    ∃ ρ : Equiv.Perm α, ρ.IsCycle ∧
      ∀ a, ρ a ≠ a → ∃ ha : a ∈ s, ρ a = (f ⟨a, ha⟩).1 := by
  classical
  let ⟨a, ha⟩ := nonempty_periodicPts f
  let hbij := bijOn_periodicPts f
  let e : Equiv.Perm (periodicPts f) := Equiv.ofBijective _ hbij.bijective
  let τ : Equiv.Perm s := Equiv.Perm.ofSubtype e
  let σ : Equiv.Perm α := Equiv.Perm.ofSubtype τ
  have hτ (x : s) (hx : x ∈ periodicPts f) : τ x = f x :=
    Equiv.Perm.ofSubtype_apply_of_mem e hx
  have hσ (x : s) (hx : x ∈ periodicPts f) : σ x.1 = (f x).1 :=
    (Equiv.Perm.ofSubtype_apply_coe τ x).trans (congrArg Subtype.val (hτ x hx))
  have hmove : σ a.1 ≠ a.1 := fun h ↦ hnf a (Subtype.ext ((hσ a ha).symm.trans h))
  exact ⟨σ.cycleOf a.1, σ.isCycle_cycleOf hmove, fun x hne ↦
    have hsame : σ.SameCycle a.1 x := Classical.byContradiction fun h ↦
      hne (Equiv.Perm.cycleOf_apply_of_not_sameCycle h)
    have heq := hsame.cycleOf_apply
    have hσne : σ x ≠ x := fun h ↦ hne (heq.trans h)
    have hx : x ∈ s := Classical.byContradiction fun h ↦
      hσne (Equiv.Perm.ofSubtype_apply_of_not_mem τ h)
    have hper : (⟨x, hx⟩ : s) ∈ periodicPts f := Classical.byContradiction fun h ↦
      hσne <| (Equiv.Perm.ofSubtype_apply_of_mem τ hx).trans <|
        congrArg Subtype.val (Equiv.Perm.ofSubtype_apply_of_not_mem e h)
    ⟨hx, heq.trans (hσ ⟨x, hx⟩ hper)⟩⟩
end StepA4
end

-- TargetSuccessor
section
open StableMarriage
namespace StepA4
variable {n : ℕ} {p : Profile n} {μ ν : Matching n}
private theorem target_partner_eligible (hν : IsStable p ν)
    (hle : ∀ i, p.manRank i (μ i) ≤ p.manRank i (ν i))
    {m : Fin n} (hm : μ m ≠ ν m) : IsEligibleSuccessor p μ m (ν m) :=
  let j := μ.symm (ν m)
  have hjμ : μ j = ν m := μ.apply_symm_apply _
  have hjm : j ≠ m := fun h ↦ hm ((congrArg μ h).symm.trans hjμ)
  have hjν : ν j ≠ ν m := ν.injective.ne hjm
  have hjmove : μ j ≠ ν j := fun h ↦ hjν (h.symm.trans hjμ)
  have hjrank : p.manRank j (μ j) < p.manRank j (ν j) :=
    lt_of_le_of_ne (hle j) ((p.manRank j).injective.ne hjmove)
  have hw : ¬ p.womanRank (ν m) j < p.womanRank (ν m) m := fun h ↦
    hν j (ν m) ⟨hjν, by simpa only [hjμ] using hjrank,
      by simpa only [Equiv.symm_apply_apply] using h⟩
  ⟨lt_of_le_of_ne (hle m) ((p.manRank m).injective.ne hm),
    lt_of_le_of_ne (le_of_not_gt hw) ((p.womanRank (ν m)).injective.ne hjm.symm)⟩
private theorem successor_husband_moves (hν : IsStable p ν) {m w : Fin n}
    (hw : IsEligibleSuccessor p μ m w) (hbound : p.manRank m w ≤ p.manRank m (ν m)) :
    μ (μ.symm w) ≠ ν (μ.symm w) :=
  let j := μ.symm w
  have hjμ : μ j = w := μ.apply_symm_apply w
  have hjm : j ≠ m := fun h ↦
    (ne_of_lt hw.1) (congrArg (p.manRank m) ((congrArg μ h).symm.trans hjμ))
  fun heq ↦
    have hjν : ν j = w := heq.symm.trans hjμ
    have hwm : w ≠ ν m := fun h ↦ hjm (ν.injective (hjν.trans h))
    have hlt : p.manRank m w < p.manRank m (ν m) :=
      lt_of_le_of_ne hbound ((p.manRank m).injective.ne hwm)
    have hjνsymm : ν.symm w = j := by
      simpa only [Equiv.symm_apply_apply] using (congrArg ν.symm hjν).symm
    hν m w ⟨hwm.symm, hlt, by simpa only [hjνsymm] using hw.2⟩
theorem exists_successor_towards_target (_hμ : IsStable p μ) (hν : IsStable p ν)
    (hle : ∀ i, p.manRank i (μ i) ≤ p.manRank i (ν i)) {m : Fin n} (hm : μ m ≠ ν m) :
    ∃ j : Fin n, IsSuccessor p μ m (μ j) ∧ μ j ≠ ν j ∧
      p.manRank m (μ j) ≤ p.manRank m (ν m) := by
  classical
  let candidates := Finset.univ.filter (IsEligibleSuccessor p μ m)
  have htarget : ν m ∈ candidates :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, target_partner_eligible hν hle hm⟩
  obtain ⟨w, hw, hmin⟩ := candidates.exists_min_image (p.manRank m) ⟨ν m, htarget⟩
  have heligible : IsEligibleSuccessor p μ m w := (Finset.mem_filter.mp hw).2
  have hsuccessor : IsSuccessor p μ m w :=
    (IsSuccessor.mk (heligible) (fun v hv ↦ hmin v (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩)))
  have hbound : p.manRank m w ≤ p.manRank m (ν m) := hmin (ν m) htarget
  have hj : μ (μ.symm w) = w := μ.apply_symm_apply w
  exact ⟨μ.symm w, by simpa only [hj] using hsuccessor,
    successor_husband_moves hν heligible hbound,
    by simpa only [hj] using hbound⟩
end StepA4
end

-- RotationReachability
section
open scoped BigOperators
open StableMarriage
namespace StepA4
variable {n : ℕ} {p : Profile n}
private inductive RotationSequence (p : Profile n) :
    Matching n → List (Equiv.Perm (Fin n)) → Matching n → Prop where
  | nil {μ : Matching n} (hμ : IsStable p μ) : RotationSequence p μ [] μ
  | cons {μ ν : Matching n} {ρ : Equiv.Perm (Fin n)} {rs : List (Equiv.Perm (Fin n))}
      (hμ : IsStable p μ) (hρ : IsExposedRotation p μ ρ)
      (rest : RotationSequence p (eliminateRotation μ ρ) rs ν) :
      RotationSequence p μ (ρ :: rs) ν
private def totalManRank (p : Profile n) (μ : Matching n) : ℕ :=
  ∑ m : Fin n, (p.manRank m (μ m) : ℕ)
private theorem totalManRank_le {μ ν : Matching n}
    (hle : ∀ m, p.manRank m (μ m) ≤ p.manRank m (ν m)) :
    totalManRank p μ ≤ totalManRank p ν :=
  Finset.sum_le_sum fun m _ ↦ hle m
private theorem totalManRank_lt_eliminate {μ : Matching n} {ρ : Equiv.Perm (Fin n)}
    (hρ : IsExposedRotation p μ ρ) :
    totalManRank p μ < totalManRank p (eliminateRotation μ ρ) :=
  have hle (m : Fin n) : p.manRank m (μ m) ≤ p.manRank m (eliminateRotation μ ρ m) :=
    if hm : ρ m = m then
      le_of_eq (by simp only [eliminateRotation_apply, hm])
    else (hρ.manRank_lt_eliminate_of_moved hm).le
  let ⟨m, hm, _⟩ := (IsExposedRotation.isCycle hρ)
  Finset.sum_lt_sum (fun i _ ↦ hle i)
    ⟨m, Finset.mem_univ m, hρ.manRank_lt_eliminate_of_moved hm⟩
theorem exists_exposedRotation_towards_target {μ ν : Matching n}
    (hμ : IsStable p μ) (hν : IsStable p ν) (hle : MenWeaklyPrefer p μ ν) (hne : μ ≠ ν) :
    ∃ ρ, IsExposedRotation p μ ρ ∧ MenWeaklyPrefer p (eliminateRotation μ ρ) ν := by
  classical
  obtain ⟨m, hm⟩ : ∃ m, μ m ≠ ν m := by
    simpa only [not_forall] using mt (fun h : ∀ i, μ i = ν i ↦ Equiv.ext h) hne
  let changed : Set (Fin n) := {i | μ i ≠ ν i}
  let : Nonempty changed := ⟨⟨m, hm⟩⟩
  
  choose next hsucc hchanged hbound using fun i : changed ↦
    exists_successor_towards_target hμ hν hle i.property
  let f : changed → changed := fun i ↦ ⟨next i, hchanged i⟩
  have hnf (i : changed) : f i ≠ i := fun h ↦
    have he : next i = i.val := congrArg Subtype.val h
    (lt_irrefl _) (by simpa only [he] using (IsSuccessor.eligible (hsucc i)).1)
  obtain ⟨ρ, hcycle, hedge⟩ := exists_cycle_permutation f hnf
  refine ⟨ρ, (IsExposedRotation.mk (hcycle) (?_)), ?_⟩
  · intro i hi
    obtain ⟨ha, hρ⟩ := hedge i hi
    simpa only [hρ] using hsucc ⟨i, ha⟩
  · intro i
    by_cases hi : ρ i = i
    · simpa only [eliminateRotation_apply, hi] using hle i
    · obtain ⟨ha, hρ⟩ := hedge i hi
      simpa only [eliminateRotation_apply, hρ] using hbound ⟨i, ha⟩
theorem exists_rotationSequence_of_menWeaklyPrefer {μ ν : Matching n}
    (hμ : IsStable p μ) (hν : IsStable p ν) (hle : MenWeaklyPrefer p μ ν) :
    ∃ rs, RotationSequence p μ rs ν := by
  classical
  let gap := fun σ : Matching n ↦ totalManRank p ν - totalManRank p σ
  refine (measure gap).wf.induction
    (C := fun σ ↦ IsStable p σ →
      MenWeaklyPrefer p σ ν →
      ∃ rs, RotationSequence p σ rs ν) μ ?_ hμ hle
  intro σ ih hσ hσν
  by_cases h : σ = ν
  · exact ⟨[], h ▸ RotationSequence.nil hσ⟩
  · obtain ⟨ρ, hρ, hnext⟩ := exists_exposedRotation_towards_target hσ hν hσν h
    have hinc := totalManRank_lt_eliminate hρ
    have hbound := totalManRank_le hnext
    have hdrop : gap (eliminateRotation σ ρ) < gap σ := by
      dsimp only [gap]
      omega
    obtain ⟨rs, hrs⟩ := ih _ hdrop (hρ.isStable_eliminate hσ) hnext
    exact ⟨ρ :: rs, .cons hσ hρ hrs⟩
theorem exists_rotationSequence_of_manOptimal {μ ν : Matching n}
    (hopt : IsManOptimal p μ) (hν : IsStable p ν) :
    ∃ rs, RotationSequence p μ rs ν :=
  exists_rotationSequence_of_menWeaklyPrefer hopt.1 hν (hopt.2 ν hν)
end StepA4
end

-- RotationLabels
section
open StableMarriage
namespace StepA4
variable {n : ℕ} {p : Profile n}
private structure RotationLabel (n : ℕ) where
  cycle : Equiv.Perm (Fin n)
  oldPartner : Fin n → Option (Fin n)
private def rotationLabel (μ : Matching n) (ρ : Equiv.Perm (Fin n)) : RotationLabel n :=
  ⟨ρ, fun m ↦ if ρ m = m then none else some (μ m)⟩
private def rotationLabels : Matching n → List (Equiv.Perm (Fin n)) → List (RotationLabel n)
  | _, [] => []
  | μ, ρ :: rs => rotationLabel μ ρ :: rotationLabels (eliminateRotation μ ρ) rs
theorem rotationLabel_eliminate_of_fixes {μ : Matching n} {ρ σ : Equiv.Perm (Fin n)}
    (hfix : ∀ m, ρ m ≠ m → σ m = m) :
    rotationLabel (eliminateRotation μ σ) ρ = rotationLabel μ ρ := by
  unfold rotationLabel
  congr 1
  funext m
  by_cases hm : ρ m = m
  · simp [hm]
  · simp [hm, hfix m hm]
theorem RotationSequence.menWeaklyPrefer {μ ν : Matching n} {rs : List (Equiv.Perm (Fin n))}
    (h : RotationSequence p μ rs ν) : MenWeaklyPrefer p μ ν := by
  induction h with
  | nil => exact fun _ ↦ le_rfl
  | @cons μ ν ρ rs hμ hρ rest ih =>
    intro m
    by_cases hm : ρ m = m
    · simpa only [eliminateRotation_apply, hm] using ih m
    · exact (hρ.manRank_lt_eliminate_of_moved hm).le.trans (ih m)
theorem IsExposedRotation.partner_ne_of_moved_of_rotationSequence {μ ν : Matching n}
    {ρ : Equiv.Perm (Fin n)} {rs : List (Equiv.Perm (Fin n))}
    (hρ : IsExposedRotation p μ ρ) (hpath : RotationSequence p (eliminateRotation μ ρ) rs ν)
    {m : Fin n} (hm : ρ m ≠ m) : μ m ≠ ν m :=
  fun he ↦ ((hρ.manRank_lt_eliminate_of_moved hm).trans_le
    (hpath.menWeaklyPrefer m)).ne (congrArg (p.manRank m) he)
end StepA4
end

-- RotationPathIndependence
section
open StableMarriage
namespace StepA4
variable {n : ℕ} {p : Profile n}
theorem RotationSequence.pull_rotation_to_front {μ ν : Matching n}
    {rs : List (Equiv.Perm (Fin n))} (hpath : RotationSequence p μ rs ν)
    {ρ : Equiv.Perm (Fin n)} (hρ : IsExposedRotation p μ ρ)
    {m : Fin n} (hm : ρ m ≠ m) (hend : μ m ≠ ν m) :
    ∃ ts, RotationSequence p (eliminateRotation μ ρ) ts ν ∧
      (rotationLabels μ rs).Perm
        (rotationLabel μ ρ :: rotationLabels (eliminateRotation μ ρ) ts) := by
  classical
  induction hpath generalizing ρ with
  | nil _ => exact (hend rfl).elim
  | @cons μ ν σ rs hμ hσ htail ih =>
    by_cases h : ρ = σ
    · subst σ
      exact ⟨rs, htail, List.Perm.refl _⟩
    · have hend' : eliminateRotation μ σ m ≠ ν m := by
        simpa only [eliminateRotation_apply, hρ.disjoint_moved hσ h m hm] using hend
      obtain ⟨ts, hts, hp⟩ := ih (hρ.persist_eliminate hσ h) hm hend'
      have hc := hρ.eliminate_comm hσ h
      have hts' : RotationSequence p (eliminateRotation (eliminateRotation μ ρ) σ) ts ν :=
        hc.symm ▸ hts
      have hlρ := rotationLabel_eliminate_of_fixes (μ := μ) (hρ.disjoint_moved hσ h)
      have hrev : σ ≠ ρ := Ne.symm h
      have hlσ := rotationLabel_eliminate_of_fixes (μ := μ) (hσ.disjoint_moved hρ hrev)
      refine ⟨σ :: ts, .cons (hρ.isStable_eliminate hμ) (hσ.persist_eliminate hρ hrev) hts', ?_⟩
      simp only [rotationLabels, hlσ, hc]
      rw [hlρ] at hp
      exact (List.Perm.cons _ hp).trans (List.Perm.swap _ _ _)
theorem RotationSequence.rotationLabels_perm {μ ν : Matching n}
    {rs ss : List (Equiv.Perm (Fin n))}
    (h : RotationSequence p μ rs ν) (h' : RotationSequence p μ ss ν) :
    (rotationLabels μ rs).Perm (rotationLabels μ ss) := by
  induction h generalizing ss with
  | nil _ =>
    cases h' with
    | nil _ => exact List.Perm.refl _
    | cons _ hσ htail =>
      obtain ⟨m, hm, _⟩ := (IsExposedRotation.isCycle hσ)
      exact ((hσ.partner_ne_of_moved_of_rotationSequence htail hm) rfl).elim
  | cons _ hρ htail ih =>
    obtain ⟨m, hm, _⟩ := (IsExposedRotation.isCycle hρ)
    have hend := hρ.partner_ne_of_moved_of_rotationSequence htail hm
    obtain ⟨ts, hts, hp⟩ := h'.pull_rotation_to_front hρ hm hend
    exact (List.Perm.cons _ (ih hts)).trans hp.symm
end StepA4
end

-- RotationTrace
section
open StableMarriage
namespace StepA4
variable {n : ℕ} {p : Profile n}
private def rotationLabelNewPartner (r : RotationLabel n) (m : Fin n) : Option (Fin n) :=
  r.oldPartner (r.cycle m)
theorem rotationLabelNewPartner_eq {μ : Matching n} {ρ : Equiv.Perm (Fin n)}
    {m : Fin n} (hm : ρ m ≠ m) :
    rotationLabelNewPartner (rotationLabel μ ρ) m = some (eliminateRotation μ ρ m) := by
  have hnext : ρ (ρ m) ≠ ρ m := fun h ↦ hm (ρ.injective h)
  simp [rotationLabelNewPartner, rotationLabel, eliminateRotation_apply, hnext]
namespace RotationSequence
variable {μ ν τ : Matching n} {rs ss : List (Equiv.Perm (Fin n))}
theorem isStable_end (h : RotationSequence p μ rs ν) : IsStable p ν := by
  induction h with
  | nil hμ => exact hμ
  | cons _ _ _ ih => exact ih
theorem append (h : RotationSequence p μ rs ν) (k : RotationSequence p ν ss τ) :
    RotationSequence p μ (rs ++ ss) τ := by
  induction h with
  | nil _ => exact k
  | cons hμ hρ _ ih => exact .cons hμ hρ (ih k)
theorem rotationLabels_append (h : RotationSequence p μ rs ν) :
    rotationLabels μ (rs ++ ss) = rotationLabels μ rs ++ rotationLabels ν ss := by
  induction h with
  | nil _ => rfl
  | cons _ _ _ ih => simp only [List.cons_append, rotationLabels, ih]
theorem label_moves_someone (h : RotationSequence p μ rs ν)
    {r : RotationLabel n} (hr : r ∈ rotationLabels μ rs) : ∃ m, r.cycle m ≠ m := by
  induction h with
  | nil _ => exact (List.not_mem_nil hr).elim
  | cons _ hρ _ ih =>
    rcases List.mem_cons.mp hr with rfl | hr
    · obtain ⟨m, hm, _⟩ := (IsExposedRotation.isCycle hρ)
      exact ⟨m, hm⟩
    · exact ih hr
theorem label_rank_bounds (h : RotationSequence p μ rs ν)
    {r : RotationLabel n} (hr : r ∈ rotationLabels μ rs)
    {m : Fin n} (hm : r.cycle m ≠ m) :
    ∃ old new, r.oldPartner m = some old ∧ rotationLabelNewPartner r m = some new ∧
      p.manRank m (μ m) ≤ p.manRank m old ∧ p.manRank m old < p.manRank m new ∧
      p.manRank m new ≤ p.manRank m (ν m) := by
  induction h with
  | nil _ => exact (List.not_mem_nil hr).elim
  | @cons μ ν ρ rs hμ hρ rest ih =>
    rcases List.mem_cons.mp hr with rfl | hr
    · refine ⟨μ m, eliminateRotation μ ρ m, ?_, rotationLabelNewPartner_eq hm,
        le_rfl, hρ.manRank_lt_eliminate_of_moved hm, rest.menWeaklyPrefer m⟩
      simp [rotationLabel, show ρ m ≠ m from hm]
    · obtain ⟨old, new, hold, hnew, hle, hlt, hend⟩ := ih hr
      have hstep : RotationSequence p μ [ρ] (eliminateRotation μ ρ) :=
        .cons hμ hρ (.nil (hρ.isStable_eliminate hμ))
      exact ⟨old, new, hold, hnew, (hstep.menWeaklyPrefer m).trans hle, hlt, hend⟩
theorem partner_eq_or_label_newPartner (h : RotationSequence p μ rs ν) (m : Fin n) :
    μ m = ν m ∨ ∃ r, r ∈ rotationLabels μ rs ∧ r.cycle m ≠ m ∧
      rotationLabelNewPartner r m = some (ν m) := by
  induction h with
  | nil _ => exact Or.inl rfl
  | @cons μ ν ρ rs _ _ _ ih =>
    rcases ih with he | ⟨r, hr, hm, hnew⟩
    · by_cases hm : ρ m = m
      · exact Or.inl (by simpa only [eliminateRotation_apply, hm] using he)
      · exact Or.inr ⟨rotationLabel μ ρ, List.mem_cons_self, hm,
          (rotationLabelNewPartner_eq hm).trans (congrArg some he)⟩
    · exact Or.inr ⟨r, List.mem_cons_of_mem _ hr, hm, hnew⟩
theorem separating_prefix (h : RotationSequence p μ rs ν) {a b : RotationLabel n}
    (hne : a ≠ b) (hmem : a ∈ rotationLabels μ rs ∨ b ∈ rotationLabels μ rs) :
    ∃ τ ts, RotationSequence p μ ts τ ∧
      ((a ∈ rotationLabels μ ts ∧ b ∉ rotationLabels μ ts) ∨
        (b ∈ rotationLabels μ ts ∧ a ∉ rotationLabels μ ts)) := by
  classical
  induction h with
  | nil _ => exact (hmem.elim (List.not_mem_nil ·) (List.not_mem_nil ·)).elim
  | @cons μ _ ρ _ hμ hρ _ ih =>
    have hstep : RotationSequence p μ [ρ] (eliminateRotation μ ρ) :=
      .cons hμ hρ (.nil (hρ.isStable_eliminate hμ))
    by_cases ha : rotationLabel μ ρ = a
    · exact ⟨_, _, hstep, Or.inl (by simp [rotationLabels, ha, Ne.symm hne])⟩
    · by_cases hb : rotationLabel μ ρ = b
      · exact ⟨_, _, hstep, Or.inr (by simp [rotationLabels, hb, hne])⟩
      · simp only [rotationLabels, List.mem_cons, Ne.symm ha, Ne.symm hb, false_or] at hmem
        obtain ⟨τ, ts, hts, hsep⟩ := ih hmem
        exact ⟨τ, ρ :: ts, .cons hμ hρ hts, by
          simpa only [rotationLabels, List.mem_cons, Ne.symm ha, Ne.symm hb, false_or]⟩
end RotationSequence
end StepA4
end

-- RotationIdeals
section
open StableMarriage
namespace StepA4
variable {n : ℕ} {p : Profile n} {μ₀ : Matching n}
private def Rotation (p : Profile n) (μ₀ : Matching n) :=
  {r : RotationLabel n // ∃ ν rs, RotationSequence p μ₀ rs ν ∧ r ∈ rotationLabels μ₀ rs}
private instance : Finite (RotationLabel n) :=
  Finite.of_injective (fun r : RotationLabel n ↦ (r.cycle, r.oldPartner)) (by
    intro a b h
    cases a
    cases b
    cases h
    rfl)
private instance : Finite (Rotation p μ₀) :=
  Finite.of_injective Subtype.val Subtype.val_injective
private def eliminatedRotations (p : Profile n) (μ₀ ν : Matching n) : Set (Rotation p μ₀) :=
  {r | ∃ rs, RotationSequence p μ₀ rs ν ∧ r.val ∈ rotationLabels μ₀ rs}
theorem RotationSequence.mem_eliminatedRotations_iff {ν : Matching n}
    {rs : List (Equiv.Perm (Fin n))} (h : RotationSequence p μ₀ rs ν)
    {r : Rotation p μ₀} :
    r ∈ eliminatedRotations p μ₀ ν ↔ r.val ∈ rotationLabels μ₀ rs :=
  ⟨fun ⟨_, hs, hr⟩ ↦ (hs.rotationLabels_perm h).mem_iff.mp hr, fun hr ↦ ⟨rs, h, hr⟩⟩
theorem eliminatedRotations_start (h : IsStable p μ₀) :
    eliminatedRotations p μ₀ μ₀ = ∅ := by
  ext r
  simp only [(RotationSequence.nil h).mem_eliminatedRotations_iff, rotationLabels,
    List.not_mem_nil, Set.notMem_empty]
private def Rotation.IsPrerequisite (r s : Rotation p μ₀) : Prop :=
  ∀ ν, s ∈ eliminatedRotations p μ₀ ν → r ∈ eliminatedRotations p μ₀ ν
private instance : PartialOrder (Rotation p μ₀) where
  le := Rotation.IsPrerequisite
  le_refl _ _ hr := hr
  le_trans _ _ _ hrs hst ν ht := hrs ν (hst ν ht)
  le_antisymm r s hrs hsr := by
    classical
    apply Subtype.ext
    by_contra hne
    obtain ⟨ν, rs, h, hr⟩ := r.property
    obtain ⟨τ, ts, ht, hsep⟩ := h.separating_prefix hne (Or.inl hr)
    rcases hsep with ⟨hr', hs'⟩ | ⟨hs', hr'⟩
    · exact hs' (ht.mem_eliminatedRotations_iff.mp
        (hsr τ (ht.mem_eliminatedRotations_iff.mpr hr')))
    · exact hr' (ht.mem_eliminatedRotations_iff.mp
        (hrs τ (ht.mem_eliminatedRotations_iff.mpr hs')))
theorem mem_eliminatedRotations_iff_newRank_le {ν : Matching n} (hopt : IsManOptimal p μ₀)
    (hν : IsStable p ν) {r : Rotation p μ₀} {m w : Fin n} (hm : r.val.cycle m ≠ m)
    (hw : rotationLabelNewPartner r.val m = some w) :
    r ∈ eliminatedRotations p μ₀ ν ↔ p.manRank m w ≤ p.manRank m (ν m) := by
  constructor
  · rintro ⟨rs, h, hr⟩
    obtain ⟨_, w', _, hw', _, _, hle⟩ := h.label_rank_bounds hr hm
    exact (Option.some.inj (hw'.symm.trans hw)) ▸ hle
  · intro hle
    obtain ⟨σ, rs, hσ, hr⟩ := r.property
    
    obtain ⟨τ, hτ, hmax⟩ := exists_stable_manRank_max hν hσ.isStable_end
    obtain ⟨as, ha⟩ := exists_rotationSequence_of_manOptimal hopt hν
    obtain ⟨bs, hb⟩ := exists_rotationSequence_of_menWeaklyPrefer hν hτ (fun i ↦ by
      rw [hmax i]
      exact le_max_left _ _)
    obtain ⟨cs, hc⟩ := exists_rotationSequence_of_menWeaklyPrefer hσ.isStable_end hτ (fun i ↦ by
      rw [hmax i]
      exact le_max_right _ _)
    have hrc : r.val ∈ rotationLabels μ₀ (rs ++ cs) := by
      rw [hσ.rotationLabels_append]
      exact List.mem_append_left _ hr
    have hra := ((hσ.append hc).rotationLabels_perm (ha.append hb)).mem_iff.mp hrc
    rw [ha.rotationLabels_append, List.mem_append] at hra
    rcases hra with hr' | hr'
    · exact ⟨as, ha, hr'⟩
    · 
      obtain ⟨_, w', _, hw', hstart, hstep, _⟩ := hb.label_rank_bounds hr' hm
      have heq := Option.some.inj (hw'.symm.trans hw)
      subst w'
      exact ((hstep.trans_le (hle.trans hstart)).false).elim
private theorem Rotation.exists_newPartner (r : Rotation p μ₀) :
    ∃ m w, r.val.cycle m ≠ m ∧ rotationLabelNewPartner r.val m = some w := by
  obtain ⟨ν, rs, h, hr⟩ := r.property
  obtain ⟨m, hm⟩ := h.label_moves_someone hr
  obtain ⟨_, w, _, hw, _, _, _⟩ := h.label_rank_bounds hr hm
  exact ⟨m, w, hm, hw⟩
theorem exists_eliminatedRotations_inter {μ ν : Matching n} (hopt : IsManOptimal p μ₀)
    (hμ : IsStable p μ) (hν : IsStable p ν) :
    ∃ τ, IsStable p τ ∧
      eliminatedRotations p μ₀ τ = eliminatedRotations p μ₀ μ ∩ eliminatedRotations p μ₀ ν := by
  obtain ⟨τ, hτ, hmin⟩ := exists_stable_manRank_min hμ hν
  refine ⟨τ, hτ, Set.ext fun r ↦ ?_⟩
  obtain ⟨m, w, hm, hw⟩ := r.exists_newPartner
  rw [Set.mem_inter_iff, mem_eliminatedRotations_iff_newRank_le hopt hτ hm hw,
    mem_eliminatedRotations_iff_newRank_le hopt hμ hm hw,
    mem_eliminatedRotations_iff_newRank_le hopt hν hm hw, hmin m, le_min_iff]
theorem exists_eliminatedRotations_union {μ ν : Matching n} (hopt : IsManOptimal p μ₀)
    (hμ : IsStable p μ) (hν : IsStable p ν) :
    ∃ τ, IsStable p τ ∧
      eliminatedRotations p μ₀ τ = eliminatedRotations p μ₀ μ ∪ eliminatedRotations p μ₀ ν := by
  obtain ⟨τ, hτ, hmax⟩ := exists_stable_manRank_max hμ hν
  refine ⟨τ, hτ, Set.ext fun r ↦ ?_⟩
  obtain ⟨m, w, hm, hw⟩ := r.exists_newPartner
  rw [Set.mem_union, mem_eliminatedRotations_iff_newRank_le hopt hτ hm hw,
    mem_eliminatedRotations_iff_newRank_le hopt hμ hm hw,
    mem_eliminatedRotations_iff_newRank_le hopt hν hm hw, hmax m, le_max_iff]
theorem eliminatedRotations_subset_iff {μ ν : Matching n} (hopt : IsManOptimal p μ₀)
    (hμ : IsStable p μ) (hν : IsStable p ν) :
    eliminatedRotations p μ₀ μ ⊆ eliminatedRotations p μ₀ ν ↔ MenWeaklyPrefer p μ ν := by
  constructor
  · intro hsub m
    obtain ⟨rs, h⟩ := exists_rotationSequence_of_manOptimal hopt hμ
    rcases h.partner_eq_or_label_newPartner m with he | ⟨r, hr, hm, hw⟩
    · rw [← he]
      exact hopt.2 ν hν m
    · let r' : Rotation p μ₀ := ⟨r, μ, rs, h, hr⟩
      have hmem : r' ∈ eliminatedRotations p μ₀ μ := ⟨rs, h, hr⟩
      exact (mem_eliminatedRotations_iff_newRank_le hopt hν hm hw).mp (hsub hmem)
  · intro hle r hr
    obtain ⟨m, w, hm, hw⟩ := r.exists_newPartner
    exact (mem_eliminatedRotations_iff_newRank_le hopt hν hm hw).mpr
      (((mem_eliminatedRotations_iff_newRank_le hopt hμ hm hw).mp hr).trans (hle m))
private def stableMatchingToRotationIdeal (ν : {ν : Matching n // IsStable p ν}) :
    LowerSet (Rotation p μ₀) :=
  ⟨eliminatedRotations p μ₀ ν.val, fun _ _ hrs hs ↦ hrs ν.val hs⟩
theorem stableMatchingToRotationIdeal_bijective (hopt : IsManOptimal p μ₀) :
    Function.Bijective (stableMatchingToRotationIdeal (p := p) (μ₀ := μ₀)) := by
  constructor
  · intro μ ν h
    have he : eliminatedRotations p μ₀ μ.val = eliminatedRotations p μ₀ ν.val :=
      congrArg (fun I : LowerSet (Rotation p μ₀) ↦ I.carrier) h
    have hμν := (eliminatedRotations_subset_iff hopt μ.property ν.property).mp he.le
    have hνμ := (eliminatedRotations_subset_iff hopt ν.property μ.property).mp he.ge
    exact Subtype.ext (Equiv.ext fun m ↦ (p.manRank m).injective ((hμν m).antisymm (hνμ m)))
  · intro I
    let F := Set.range fun ν : {ν : Matching n // IsStable p ν} ↦
      eliminatedRotations p μ₀ ν.val
    have hempty : ∅ ∈ F := ⟨⟨μ₀, hopt.1⟩, eliminatedRotations_start hopt.1⟩
    have hinter : ∀ ⦃A B⦄, A ∈ F → B ∈ F → A ∩ B ∈ F := by
      rintro _ _ ⟨μ, rfl⟩ ⟨ν, rfl⟩
      obtain ⟨τ, hτ, he⟩ := exists_eliminatedRotations_inter hopt μ.property ν.property
      exact ⟨⟨τ, hτ⟩, he⟩
    have hunion : ∀ ⦃A B⦄, A ∈ F → B ∈ F → A ∪ B ∈ F := by
      rintro _ _ ⟨μ, rfl⟩ ⟨ν, rfl⟩
      obtain ⟨τ, hτ, he⟩ := exists_eliminatedRotations_union hopt μ.property ν.property
      exact ⟨⟨τ, hτ⟩, he⟩
    have hcover (r : Rotation p μ₀) : ∃ A ∈ F, r ∈ A := by
      obtain ⟨ν, rs, h, hr⟩ := r.property
      exact ⟨_, ⟨⟨ν, h.isStable_end⟩, rfl⟩, ⟨rs, h, hr⟩⟩
    have hdown : ∀ ⦃r s : Rotation p μ₀⦄, (∀ A ∈ F, s ∈ A → r ∈ A) → s ∈ I → r ∈ I := by
      intro r s hrs hs
      refine I.lower (show r ≤ s from fun ν hν ↦ ?_) hs
      obtain ⟨rs, h, hmem⟩ := hν
      exact hrs _ ⟨⟨ν, h.isStable_end⟩, rfl⟩ ⟨rs, h, hmem⟩
    have hI : (I : Set (Rotation p μ₀)) ∈ F :=
      mem_family_of_downward_closed hempty hinter hunion hcover hdown
    obtain ⟨ν, hν⟩ := hI
    exact ⟨ν, LowerSet.ext hν⟩
private noncomputable def stableMatchingEquivRotationIdeals (hopt : IsManOptimal p μ₀) :
    {ν : Matching n // IsStable p ν} ≃ LowerSet (Rotation p μ₀) :=
  Equiv.ofBijective stableMatchingToRotationIdeal (stableMatchingToRotationIdeal_bijective hopt)
end StepA4
end

-- CoexposedRotations
section
open StableMarriage
namespace StepA4
variable {n : ℕ} {p : Profile n} {μ₀ μ : Matching n}
private def rotationOfExposed (hopt : IsManOptimal p μ₀) (hμ : IsStable p μ)
    {ρ : Equiv.Perm (Fin n)} (hρ : IsExposedRotation p μ ρ) : Rotation p μ₀ :=
  ⟨rotationLabel μ ρ, by
    obtain ⟨rs, hrs⟩ := exists_rotationSequence_of_manOptimal hopt hμ
    have hstep : RotationSequence p μ [ρ] (eliminateRotation μ ρ) :=
      .cons hμ hρ (.nil (hρ.isStable_eliminate hμ))
    refine ⟨_, rs ++ [ρ], hrs.append hstep, ?_⟩
    simp [hrs.rotationLabels_append, rotationLabels]⟩
end StepA4
end

-- CoexposedRotationMultiplicity
section
open StableMarriage
open scoped BigOperators
namespace StepA4
variable {n : ℕ} {p : Profile n} {μ : Matching n}
end StepA4
end

-- CoexposureCycleMoment
section
open StableMarriage MeasureTheory
open scoped BigOperators ENNReal
namespace StepA4
private def RealizesSuccessorPermutation {n : ℕ} (p : Profile n) (M σ : Matching n) : Prop :=
  ∀ i ∈ σ.support, IsSuccessor p M i (M (σ i))
end StepA4
end

-- PivotReverseMaskJointLaw
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA4
end StepA4
end

-- RowCompetition
section
open Set
open scoped BigOperators
namespace StepA4
variable {ι : Type*} {J : Finset ι} {a : ι → ℝ} {A b : ℝ}
end StepA4
end

-- ReverseArcRelativeLower
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace StepA4
end StepA4
end

-- ReverseIIDLabelGood
section
open MeasureTheory Set ProbabilityTheory
open scoped BigOperators ENNReal
namespace StepA4
section Measures
variable {ι α : Type*} [Fintype ι] [MeasurableSpace α]
variable [Fintype α] [DiscreteMeasurableSpace α]
end Measures
end StepA4
end

-- ReverseCycleLabelMultiplicity
section
open scoped BigOperators ENNReal
namespace StepA4
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {k : ℕ} {A : Finset α} {F : α → Finset α}
end StepA4
end

-- ReverseDerangementFraction
section
open scoped ENNReal
namespace StepA4
end StepA4
end

-- PivotReverseMaskLowerMoment
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA4
open scoped Classical in
private noncomputable def goodReverseSupportPermutations {n : ℕ} (k : ℕ)
    (A : Finset (Fin n)) (F : Fin n → Finset (Fin n)) : Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter fun σ ↦ σ.support.card = k ∧
    ∀ i ∈ σ.support, i ∉ A ∧ σ i ∉ F i
private noncomputable def forwardMaskForbiddenTargets {n : ℕ} (μ : Matching n)
    (flag : OffDiagonalCellIndex n → Bool) (i : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun j ↦ ¬ ∃ q : ForwardInactiveColumnIndex flag (μ.symm i),
    q.val.val.val.1 = μ.symm j
private noncomputable def reverseSpouseWeights {n : ℕ} (μ : Matching n) (d : DiagonalScorePairs n) :
    Fin n → ℝ≥0∞ := fun j ↦
  ENNReal.ofReal ((diagonalPairAt d (μ.symm j)).1 / ∑ i, (diagonalPairAt d i).1)
end StepA4
end

-- PivotReverseCompetitorMass
section
open StableMarriage
open scoped BigOperators ENNReal
namespace StepA4
private noncomputable def forwardMaskOmittedMass {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) (j : Fin n) : ℝ :=
  ∑ i : {i : Fin n // i ≠ j}, if flag ⟨(i.val, j), i.property⟩ then
    (diagonalPairAt d i.val).1 else 0
end StepA4
end

-- PivotForwardMaskProbability
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace StepA4
private noncomputable def forwardCellFlag (x y : ℝ) (z : ℝ × ℝ) : Bool := by
  classical
  exact decide (z ∈ forwardEligibleScoreCell x y)
private noncomputable def forwardMaskOfScores {n : ℕ} (d : DiagonalScorePairs n)
    (z : OffDiagonalScorePairs n) (q : OffDiagonalCellIndex n) : Bool :=
  forwardCellFlag (diagonalPairAt d q.val.1).1 (diagonalPairAt d q.val.2).2 (z q)
end StepA4
end

-- WeightedBoolProductTail
section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace StepA4
end StepA4
end

-- PivotEligibleMask
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA4
end StepA4
end

-- PivotForwardRevealRectangle
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace StepA4
private abbrev ForwardRevealedMaleScores {n : ℕ} (flag : OffDiagonalCellIndex n → Bool) :=
  ForwardActiveCellIndex flag → ℝ
private abbrev ForwardInactiveColumns {n : ℕ} (flag : OffDiagonalCellIndex n → Bool) :=
  (i : Fin n) → ForwardInactiveColumnIndex flag i → ℝ × ℝ
private def forwardRevealWithColumns {n : ℕ} (flag : OffDiagonalCellIndex n → Bool) :
    OffDiagonalScorePairs n → ForwardRevealedMaleScores flag × ForwardInactiveColumns flag :=
  Prod.map id (forwardInactiveColumnsEquiv flag) ∘ forwardScoreMaskRevealAndInactive flag
end StepA4
end

-- PivotForwardPivotReadout
section
open MeasureTheory Set StableMarriage
namespace StepA4
private noncomputable def forwardPivotIncrement {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) (ρ : Matching n)
    (a : ForwardRevealedMaleScores flag) (m : Fin n) : ℝ :=
  if hm : ρ m ≠ m then
    let q : OffDiagonalCellIndex n := ⟨(m, ρ m), hm.symm⟩
    if hq : flag q = true then a ⟨q, hq⟩ - (diagonalPairAt d m).1 else 0
  else 0
end StepA4
end

-- SingletonIdealAnchor
section
namespace StepA4
variable {α : Type*} [PartialOrder α]
private def singletonAnchorIdeal (r : α) : LowerSet α :=
  ⟨(Set.Ici r)ᶜ, fun _ _ hst ht hrs ↦ ht (hrs.trans hst)⟩
end StepA4
end

-- SingletonRotationAnchor
section
open StableMarriage
namespace StepA4
variable {n : ℕ} {p : Profile n} {μ₀ μ : Matching n}
private def Rotation.IsExposedAt (r : Rotation p μ₀) (μ : Matching n) : Prop :=
  IsExposedRotation p μ r.val.cycle ∧ rotationLabel μ r.val.cycle = r.val
private noncomputable def singletonRotationAnchor (hopt : IsManOptimal p μ₀) (r : Rotation p μ₀) :
    {ν : Matching n // IsStable p ν} :=
  (stableMatchingEquivRotationIdeals hopt).symm (singletonAnchorIdeal r)
end StepA4
end

-- ReverseRotationIdeals
section
open StableMarriage
namespace StepA4
variable {n : ℕ} {p : Profile n} {μ₀ ν : Matching n} {σ : Equiv.Perm (Fin n)}
private def IsReverseExposedRotation (p : Profile n) (ν : Matching n) (σ : Equiv.Perm (Fin n)) : Prop :=
  IsExposedRotation (swapProfile p) ν.symm σ
private def undoReverseRotation (ν : Matching n) (σ : Equiv.Perm (Fin n)) : Matching n :=
  (eliminateRotation ν.symm σ).symm
theorem IsReverseExposedRotation.undo_stable
    (hσ : IsReverseExposedRotation p ν σ) (hν : IsStable p ν) :
    IsStable p (undoReverseRotation ν σ) := by
  apply isStable_swapProfile_iff.mp
  simpa only [undoReverseRotation, Equiv.symm_symm] using
    (show IsExposedRotation (swapProfile p) ν.symm σ from hσ).isStable_eliminate
      (isStable_swapProfile_iff.mpr hν)
theorem IsReverseExposedRotation.forward_exposed
    (hσ : IsReverseExposedRotation p ν σ) (hν : IsStable p ν) :
    IsExposedRotation p (undoReverseRotation ν σ) (reverseRotationCycle ν.symm σ) := by
  simpa only [undoReverseRotation, swapProfile_swapProfile] using
    (show IsExposedRotation (swapProfile p) ν.symm σ from hσ).isExposedRotation_swap_eliminate
      (isStable_swapProfile_iff.mpr hν)
private def reverseExposedRotationLabel (hopt : IsManOptimal p μ₀) (hν : IsStable p ν)
    (σ : {σ : Equiv.Perm (Fin n) // IsReverseExposedRotation p ν σ}) : Rotation p μ₀ :=
  rotationOfExposed hopt (σ.property.undo_stable hν) (σ.property.forward_exposed hν)
end StepA4
end

-- PivotCrossBlocker
section
open StableMarriage
namespace StepA4
variable {n : ℕ} {p : Profile n} {A N : Matching n} {ρ : Equiv.Perm (Fin n)}
end StepA4
end

-- PivotReversePermutationCompatibility
section
open StableMarriage
namespace StepA4
variable {n : ℕ} {p : Profile n} {μ ρ σ : Matching n}
theorem RealizesSuccessorPermutation.womanRank_eliminate_le
    (hσ : RealizesSuccessorPermutation p μ σ) (w : Fin n) :
    p.womanRank w ((eliminateRotation μ σ).symm w) ≤ p.womanRank w (μ.symm w) :=
  let ⟨m, hm⟩ := (eliminateRotation μ σ).surjective w
  have hle : p.womanRank (μ (σ m)) m ≤ p.womanRank (μ (σ m)) (σ m) :=
    if he : σ m = m then (congrArg (p.womanRank (μ (σ m))) he.symm).le
    else by simpa only [Equiv.symm_apply_apply] using
      (IsSuccessor.eligible (hσ m (Equiv.Perm.mem_support.mpr he))).2.le
  have htarget : p.womanRank (eliminateRotation μ σ m)
      ((eliminateRotation μ σ).symm (eliminateRotation μ σ m)) ≤
        p.womanRank (eliminateRotation μ σ m) (μ.symm (eliminateRotation μ σ m)) := by
    have hinv : (eliminateRotation μ σ).symm (μ (σ m)) = m :=
      (eliminateRotation μ σ).symm_apply_apply m
    simpa only [eliminateRotation_apply, hinv, Equiv.symm_apply_apply] using hle
  hm ▸ htarget
theorem RealizesSuccessorPermutation.isStable_eliminate
    (hσ : RealizesSuccessorPermutation p μ σ) (hμ : IsStable p μ) :
    IsStable p (eliminateRotation μ σ) :=
  fun m w hb ↦
    have hwOld : p.womanRank w m < p.womanRank w (μ.symm w) :=
      hb.2.2.trans_le (hσ.womanRank_eliminate_le w)
    have hne : μ m ≠ w := fun h ↦ (ne_of_lt hwOld)
      (congrArg (p.womanRank w) ((μ.symm_apply_apply m).symm.trans (congrArg μ.symm h)))
    have hnot : ¬ p.manRank m w < p.manRank m (μ m) := fun h ↦
      hμ m w ⟨hne, h, hwOld⟩
    if hm : σ m = m then
      hnot (by simpa only [eliminateRotation_apply, hm] using hb.2.1)
    else
      have hbelow : p.manRank m (μ m) < p.manRank m w :=
        lt_of_le_of_ne (le_of_not_gt hnot) (fun he ↦ hne ((p.manRank m).injective he))
      (not_lt_of_ge ((IsSuccessor.min_rank (hσ m (Equiv.Perm.mem_support.mpr hm))) w ⟨hbelow, hwOld⟩)) hb.2.1
theorem RealizesSuccessorPermutation.undo_stable
    (hσ : RealizesSuccessorPermutation (swapProfile p) μ.symm σ) (hμ : IsStable p μ) :
    IsStable p (undoReverseRotation μ σ) :=
  isStable_swapProfile_iff.mp (hσ.isStable_eliminate (isStable_swapProfile_iff.mpr hμ))
end StepA4
end

-- ReverseSupportWeightUpper
section
open scoped BigOperators ENNReal
namespace StepA4
end StepA4
end

-- PivotCompatibilityLoss
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA4
end StepA4
end

-- UndoMaximalSubset
section
open StableMarriage
namespace StepA4
variable {n : ℕ} {p : Profile n} {μ₀ ν : Matching n}
private abbrev MaximalEliminatedRotation (p : Profile n) (μ₀ ν : Matching n) :=
  {r : Rotation p μ₀ // Maximal (fun s ↦ s ∈ eliminatedRotations p μ₀ ν) r}
private def undoMaximalSubsetIdeal (hν : IsStable p ν)
    (D : Set (MaximalEliminatedRotation p μ₀ ν)) : LowerSet (Rotation p μ₀) :=
  ⟨eliminatedRotations p μ₀ ν \ (Subtype.val '' D), by
    let I := stableMatchingToRotationIdeal (μ₀ := μ₀) ⟨ν, hν⟩
    intro b a hab hb
    refine ⟨I.lower hab hb.1, ?_⟩
    rintro ⟨r, hr, rfl⟩
    exact hb.2 ⟨r, hr, hab.antisymm (r.property.2 hb.1 hab)⟩⟩
private theorem mem_undoMaximalSubsetIdeal_iff (hν : IsStable p ν)
    (D : Set (MaximalEliminatedRotation p μ₀ ν)) (r : MaximalEliminatedRotation p μ₀ ν) :
    r.val ∈ undoMaximalSubsetIdeal hν D ↔ r ∉ D := by
  change (r.val ∈ eliminatedRotations p μ₀ ν ∧ r.val ∉ Subtype.val '' D) ↔ r ∉ D
  rw [and_iff_right r.property.1, Subtype.val_injective.mem_set_image]
private def undoMaximalSubsetIdealEmbedding (hν : IsStable p ν) :
    Set (MaximalEliminatedRotation p μ₀ ν) ↪ LowerSet (Rotation p μ₀) :=
  ⟨undoMaximalSubsetIdeal hν, by
    intro D E h
    ext r
    apply not_iff_not.mp
    rw [← mem_undoMaximalSubsetIdeal_iff hν D r,
      ← mem_undoMaximalSubsetIdeal_iff hν E r, h]⟩
private noncomputable def undoMaximalSubsetEmbedding (hopt : IsManOptimal p μ₀) (hν : IsStable p ν) :
    Set (MaximalEliminatedRotation p μ₀ ν) ↪ {μ : Matching n // IsStable p μ} :=
  (undoMaximalSubsetIdealEmbedding hν).trans
    (stableMatchingEquivRotationIdeals hopt).symm.toEmbedding
end StepA4
end

-- RotationUndoSequences
section
open StableMarriage
namespace StepA4
variable {n : ℕ} {p : Profile n} {μ₀ μ ν : Matching n} {hopt : IsManOptimal p μ₀}
private inductive RotationUndoSequence (hopt : IsManOptimal p μ₀) :
    Matching n → List (Rotation p μ₀) → Matching n → Prop where
  | nil {ν : Matching n} (hν : IsStable p ν) : RotationUndoSequence hopt ν [] ν
  | cons {ν τ : Matching n} {r : Rotation p μ₀} {rs : List (Rotation p μ₀)}
      (hν : IsStable p ν)
      (σ : {σ : Equiv.Perm (Fin n) // IsReverseExposedRotation p ν σ})
      (hlabel : reverseExposedRotationLabel hopt hν σ = r)
      (rest : RotationUndoSequence hopt (undoReverseRotation ν σ.val) rs τ) :
      RotationUndoSequence hopt ν (r :: rs) τ
theorem RotationUndoSequence.isStable_end {rs : List (Rotation p μ₀)}
    (h : RotationUndoSequence hopt ν rs μ) : IsStable p μ := by
  induction h with
  | nil hν => exact hν
  | cons _ _ _ _ ih => exact ih
end StepA4
end

-- PivotIncidenceCounting
section
open StableMarriage
open scoped BigOperators
namespace StepA4
variable {n : ℕ} {p : Profile n} {μ₀ ν μ : Matching n} {hopt : IsManOptimal p μ₀}
private def rotationLength (r : Rotation p μ₀) : ℕ :=
  r.val.cycle.support.card
private structure PivotDecoration (hopt : IsManOptimal p μ₀) (K : ℕ) (r : Rotation p μ₀) where
  removed : Finset (MaximalEliminatedRotation p μ₀ (singletonRotationAnchor hopt r).val)
  totalLength_le : (∑ s ∈ removed, rotationLength s.val) ≤ K
  pivot_exposed : r.IsExposedAt
    (undoMaximalSubsetEmbedding hopt (singletonRotationAnchor hopt r).property removed).val
namespace PivotDecoration
variable {K : ℕ} {r : Rotation p μ₀}
private noncomputable def matching (D : PivotDecoration hopt K r) : {M : Matching n // IsStable p M} :=
  undoMaximalSubsetEmbedding hopt (singletonRotationAnchor hopt r).property D.removed
end PivotDecoration
end StepA4
end

-- PivotCompatibleLowerMoment
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA4
private def memFinset {α : Type} {S : Finset α} {Q : α → Prop} (_ : ∀ {σ}, σ ∈ S ↔ Q σ) := S
private noncomputable def compatibleReversePermutations {n : ℕ} (S : Finset (Matching n))
    (p : Profile n) (μ ρ : Matching n) : Finset (Matching n) :=
  memFinset (@MarkedLP.mem_compatibleReversePermutations n S p μ ρ)
private def premise {A B : Prop} (_ : A → B) := A
private abbrev SourceSuccessor {n} (p : Profile n) (μ : Matching n) (m w : Fin n) : Prop :=
  premise (@MarkedLP.IsSuccessor.unique n p μ m w w)
private lemma sourceSuccessor_iff {n} (p : Profile n) (μ : Matching n) (m w : Fin n) :
    SourceSuccessor p μ m w ↔ IsSuccessor p μ m w := by
  constructor
  · rintro ⟨he,hm⟩
    exact (IsSuccessor.mk (he) (hm))
  · rintro ⟨he,hm⟩
    constructor <;> assumption
private abbrev SourceExposed {n} (p : Profile n) (μ ρ : Matching n) : Prop :=
  premise (@MarkedLP.IsExposedRotation.womanRank_eliminate_le n p μ ρ)
private lemma sourceExposed_iff {n} (p : Profile n) (μ ρ : Matching n) :
    SourceExposed p μ ρ ↔ IsExposedRotation p μ ρ := by
  constructor
  · rintro ⟨hc,hs⟩
    exact (IsExposedRotation.mk (hc) (fun m hm => (sourceSuccessor_iff ..).mp (hs m hm)))
  · rintro ⟨hc,hs⟩
    constructor
    · exact hc
    · exact fun m hm => (sourceSuccessor_iff ..).mpr (hs m hm)
theorem mem_compatibleReversePermutations {n : ℕ} {S : Finset (Matching n)}
    {p : Profile n} {μ ρ σ : Matching n} : σ ∈ compatibleReversePermutations S p μ ρ ↔
    σ ∈ S ∧ RealizesSuccessorPermutation (swapProfile p) μ.symm σ ∧
      IsExposedRotation p (undoReverseRotation μ σ) ρ := by
  apply (MarkedLP.mem_compatibleReversePermutations (S:=S) (p:=p) (μ:=μ) (ρ:=ρ) (σ:=σ)).trans
  apply and_congr_right
  intro _
  refine and_congr ?_ (sourceExposed_iff ..)
  exact forall_congr' fun i => forall_congr' fun _ => sourceSuccessor_iff ..
private noncomputable def compatibleReverseSupportFamily {n : ℕ} (μ ρ : Matching n)
    (flag : OffDiagonalCellIndex n → Bool) (k : ℕ) (p : Profile n) : Finset (Matching n) :=
  compatibleReversePermutations
    (goodReverseSupportPermutations k (ρ.support.map μ.toEmbedding)
      (forwardMaskForbiddenTargets μ flag)) p μ ρ
end StepA4
end

-- ReverseIncrementColumnTail
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace StepA4
variable {ι : Type*}
end StepA4
end

-- PivotReverseIncrementFilter
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA4
private def reverseScoreIncrement {n : ℕ} (x : ScoreProfile n) (μ : Matching n)
    (w j : Fin n) : ℝ := x (.inr w) j - x (.inr w) (μ.symm w)
private noncomputable def reverseIncrementCutoff (n : ℕ) (X : ℝ) : ℝ := 16 * Real.log (n : ℝ) / X
end StepA4
end

-- PivotReverseFilteredCount
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA4
private def shortCycleCapBad (L : ℕ) (T : Multiset ℕ) : Prop :=
  (3 / 2 : ℝ) * Real.log (L : ℝ) < ((T.filter (· ≤ L)).card : ℝ)
private def reverseCollectionIncrementGood {n : ℕ} (x : ScoreProfile n) (μ σ : Matching n)
    (t : ℝ) : Prop :=
  ∀ w ∈ σ.support, reverseScoreIncrement x μ w (μ.symm (σ w)) ≤ t
private noncomputable def filteredReverseSupportFamily {n : ℕ} (μ ρ : Matching n)
    (flag : OffDiagonalCellIndex n → Bool) (k L : ℕ) (t : ℝ) (x : ScoreProfile n) :
    Finset (Matching n) := by
  classical
  exact (compatibleReverseSupportFamily μ ρ flag k (profileOfScores x)).filter fun σ ↦
    (¬ shortCycleCapBad L σ.cycleType) ∧ reverseCollectionIncrementGood x μ σ t
end StepA4
end

-- ReverseColoredPermutations
section
open scoped BigOperators
namespace StepA4
end StepA4
end

-- CoexposureGaussianSum
section
open scoped BigOperators ENNReal
open Finset Filter
namespace StepA4
end StepA4
end

-- ReverseQuadraticGaussian
section
open Finset
open scoped BigOperators ENNReal
namespace StepA4
end StepA4
end

-- ReverseCycleCollectionMoment
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA4
end StepA4
end

-- PivotReverseMaskMoment
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA4
end StepA4
end

-- MeasureCountFilterLoss
section
open MeasureTheory
open scoped ENNReal
namespace StepA4
variable {Ω : Type*} [MeasurableSpace Ω]
end StepA4
end

-- ReverseCycleTypeWeightTransfer
section
open scoped BigOperators ENNReal
namespace StepA4
end StepA4
end

-- ShortCycleChebyshev
section
open scoped BigOperators ENNReal
namespace StepA4
end StepA4
end

-- UniformShortCycleMoments
section
open Equiv Equiv.Perm
open scoped BigOperators
namespace StepA4
variable {α : Type*} [Fintype α] [DecidableEq α]
end StepA4
end

-- PivotReverseFilterMoment
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA4
end StepA4
end

-- PivotScoreLock
section
open StableMarriage
namespace StepA4
variable {n : ℕ} {p : Profile n} {μ₀ μ ν : Matching n} {r : Rotation p μ₀}
end StepA4
end

-- PivotForwardExposureReveal
section
open MeasureTheory Set StableMarriage
namespace StepA4
private def forwardRevealExposureEvent {n : ℕ} (ρ : Matching n)
    (flag : OffDiagonalCellIndex n → Bool) : Set (ForwardRevealedMaleScores flag) :=
  {v | ρ.IsCycle ∧ ∀ m, ρ m ≠ m →
    ∃ q : ForwardActiveCellIndex flag, q.val.val = (m, ρ m) ∧
      ∀ t : ForwardActiveCellIndex flag, t.val.val.1 = m → v q ≤ v t}
end StepA4
end

-- PivotEligibilityScale
section
open Filter Real
open scoped BigOperators ENNReal Topology
namespace StepA4
end StepA4
end

-- PivotEligibleRevealControls
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA4
private def reverseDiagonalMaleTotal {n : ℕ} (d : DiagonalScorePairs n) : ℝ :=
  ∑ i, (diagonalPairAt d i).1
private def eligiblePivotRevealSet {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) (ρ : Matching n) (D : ℝ) :
    Set (ForwardRevealedMaleScores flag) :=
  {v | (∀ τ : Matching n, v ∈ forwardRevealExposureEvent τ flag ↔ τ = ρ) ∧
    (∀ m ∈ ρ.support, 0 ≤ forwardPivotIncrement d flag ρ v m) ∧
    (∑ m ∈ ρ.support, forwardPivotIncrement d flag ρ v m) ≤ D}
namespace ReverseMaskGeometry
variable {n : ℕ} {d : DiagonalScorePairs n} {flag : OffDiagonalCellIndex n → Bool}
  {μ ρ : Matching n} {s u p : ℝ}
end ReverseMaskGeometry
end StepA4
end

-- PivotSpouseBandMask
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA4
private def pivotDiagonalFemaleTotal {n : ℕ} (d : DiagonalScorePairs n) : ℝ :=
  ∑ i, (diagonalPairAt d i).2
private def pivotBaseDiagonalBand (n : ℕ) : Set (DiagonalScorePairs n) :=
  {d | let X := reverseDiagonalMaleTotal d
       let Y := pivotDiagonalFemaleTotal d
       (∀ i, (diagonalPairAt d i).1 ∈ Ico 0 1 ∧ (diagonalPairAt d i).2 ∈ Ico 0 1) ∧
       2 ≤ Y ∧ Y ≤ (n : ℝ) ^ (2 / 5 : ℝ) ∧ (n : ℝ) / 128 ≤ X * Y ∧
       (∀ i, (diagonalPairAt d i).2 / Y ≤ 12 * Real.log n / n) ∧
       ∀ i, (diagonalPairAt d i).1 ≤ 8 * Real.log n / (Y - 1)}
end StepA4
end

-- CoexposureScoreMomentBound
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace StepA4
end StepA4
end

-- CoexposureScoreRefutation
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace StepA4
end StepA4
end

-- PivotSpouseBandRegularity
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace StepA4
end StepA4
end

-- PivotSpouseSquareRegularity
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace StepA4
end StepA4
end

-- ForestDeterministic
section
open scoped BigOperators Classical
namespace StepA4
private def RealizesDirectedCycle {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → Option ι) (σ : Equiv.Perm ι) : Prop :=
  σ.IsCycle ∧ ∀ i ∈ σ.support, f i = some (σ i)
private def IsAcyclicSuccessor {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → Option ι) : Prop :=
  ∀ σ : Equiv.Perm ι, ¬ RealizesDirectedCycle f σ
end StepA4
end

-- ForestProductProbability
section
open scoped BigOperators Classical
namespace StepA4
end StepA4
end

-- ForestRankOne
section
namespace StepA4
end StepA4
end

-- ForestRowThinning
section
open scoped BigOperators Classical
namespace StepA4
end StepA4
end

-- ForwardSuccessorRowLaw
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA4
end StepA4
end

-- ForwardSuccessorOutcome
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA4
end StepA4
end

-- PivotForwardRowDeficit
section
open Filter MeasureTheory Set
open scoped BigOperators ENNReal
namespace StepA4
private noncomputable def forwardSpouseWeight {n : ℕ} (d : DiagonalScorePairs n) (i : Fin n) : ℝ :=
  (diagonalPairAt d i).2 / ∑ j, (diagonalPairAt d j).2
end StepA4
end

-- PivotForwardForest
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA4
end StepA4
end

-- PivotLocalEligibility
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace StepA4
private def certifiedSet {α : Type} [MeasurableSpace α] {t : Set α} (_ : MeasurableSet t) := t
private def LocalPivotGeometry {n : ℕ} (b A B : ℝ) (μ ρ : Matching n)
    (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool) : Prop :=
  d ∈ certifiedSet (MarkedLP.measurableSet_localPivotGeometry b A B μ ρ flag)
private theorem LocalPivotGeometry.mk {n : ℕ} {b A B : ℝ} {μ ρ : Matching n}
    {d : DiagonalScorePairs n} {flag : OffDiagonalCellIndex n → Bool}
    (h0 : d ∈ pivotBaseDiagonalBand n) (h1 : (n : ℝ) ^ (1 / 10 : ℝ) ≤ pivotDiagonalFemaleTotal d) (h2 : b * Real.sqrt (n : ℝ) ≤ (ρ.support.card : ℝ)) (h3 : (ρ.support.card : ℝ) ≤ A * Real.sqrt (n : ℝ)) (h4 : (∑ j, (reverseSpouseWeights μ d j) ^ 2) ≤ ENNReal.ofReal (24 / (n : ℝ))) (h5 : (∑ i, (forwardSpouseWeight d i) ^ 2) ≤ 24 / (n : ℝ)) (h6 : ∀ j, forwardMaskOmittedMass d flag j ≤ (n : ℝ) ^ (-11 / 20 : ℝ) * reverseDiagonalMaleTotal d) (h7 : (∑ i ∈ ρ.support, (diagonalPairAt d i).1) ≤ (B / Real.sqrt (n : ℝ)) * reverseDiagonalMaleTotal d) :
    LocalPivotGeometry b A B μ ρ d flag := by
  constructor
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
private noncomputable def localPivotIncrementCap {n : ℕ} (B : ℝ) (d : DiagonalScorePairs n) : ℝ :=
  B * Real.sqrt (n : ℝ) / pivotDiagonalFemaleTotal d
private def IsLocallyEligiblePivot {n : ℕ} (b A B : ℝ) (x : ScoreProfile n)
    (μ ρ : Matching n) : Prop :=
  let z := splitScorePairs μ x
  let flag := forwardMaskOfScores z.1 z.2
  LocalPivotGeometry b A B μ ρ z.1 flag ∧
    (forwardRevealWithColumns flag z.2).1 ∈
      eligiblePivotRevealSet z.1 flag ρ (localPivotIncrementCap B z.1)
theorem measurableSet_localPivotGeometry {n : ℕ} (b A B : ℝ) (μ ρ : Matching n)
    (flag : OffDiagonalCellIndex n → Bool) :
    MeasurableSet {d : DiagonalScorePairs n | LocalPivotGeometry b A B μ ρ d flag} := MarkedLP.measurableSet_localPivotGeometry b A B μ ρ flag

end StepA4
end

-- PivotMarkedDecorationCount
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA4
variable {n : ℕ}
private noncomputable def markedFilteredChoices (μ ρ : Matching n)
    (flag : OffDiagonalCellIndex n → Bool) (K L : ℕ) (t : ℝ) (x : ScoreProfile n) :
    Finset (Matching n) := by
  classical
  exact Finset.univ.filter fun σ ↦ σ.support.card ≤ K ∧
    σ ∈ filteredReverseSupportFamily μ ρ flag σ.support.card L t x
private noncomputable def localFilteredDecorationCount (b A B : ℝ) (K L : ℕ) (μ ρ : Matching n)
    (x : ScoreProfile n) : ℝ := by
  classical
  exact if IsLocallyEligiblePivot b A B x μ ρ then
    ((markedFilteredChoices μ ρ (forwardMaskOfScores (splitScorePairs μ x).1
      (splitScorePairs μ x).2) K L (reverseIncrementCutoff n (maleSpouseTotal x μ)) x).card : ℝ)
    else 0
section MatchingEndpoints
variable {x : ScoreProfile n} {μ₀ μ ρ σ : Matching n}
  {flag : OffDiagonalCellIndex n → Bool} {K L : ℕ} {t : ℝ}
end MatchingEndpoints
end StepA4
end

-- PivotRestrictedMoment
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA4
section ConditionalOrder
variable {Ω : Type*} {m m₀ : MeasurableSpace Ω}
end ConditionalOrder
end StepA4
end

-- PivotFullRevealLaw
section
open MeasureTheory Set StableMarriage
open scoped ENNReal
namespace StepA4
variable {n : ℕ}
end StepA4
end

-- PivotConditionalMean
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace StepA4
variable {n : ℕ}
end StepA4
end

-- DeferredAcceptanceTranscript
section
open StableMarriage
open scoped BigOperators
namespace StepA4
private abbrev DAState (n : ℕ) := (Fin n → ℕ) × (Fin n → Option (Fin n))
@[simp] private abbrev DAState.count {n : ℕ} (s : DAState n) : Fin n → ℕ := s.1
@[simp] private abbrev DAState.held {n : ℕ} (s : DAState n) : Fin n → Option (Fin n) := s.2
namespace DAState
variable {n : ℕ}
private def Free (s : DAState n) (m : Fin n) : Prop := ∀ w, s.held w ≠ some m
private def initial (n : ℕ) : DAState n := ⟨fun _ ↦ 0, fun _ ↦ none⟩
private def proposalTarget (rank : Fin n → Equiv.Perm (Fin n)) (s : DAState n)
    (m : Fin n) (h : s.count m < n) : Fin n := (rank m).symm ⟨s.count m, h⟩
private def chosenHolder (s : DAState n) (m w : Fin n) (accept : Bool) : Fin n :=
  if accept then m else (s.held w).getD m
private def applyDecision (s : DAState n) (m w : Fin n) (accept : Bool) : DAState n :=
  ⟨Function.update s.count m (s.count m + 1),
    Function.update s.held w (some (s.chosenHolder m w accept))⟩
private def proposalAccepted (p : Profile n) (s : DAState n) (m w : Fin n) : Bool :=
  (s.held w).elim true fun a ↦ decide (p.womanRank w m < p.womanRank w a)
private structure Valid (p : Profile n) (s : DAState n) : Prop where
  count_le : ∀ m, s.count m ≤ n
  held_unique : ∀ {u v m}, s.held u = some m → s.held v = some m → u = v
  held_last : ∀ {w m}, s.held w = some m → (p.manRank m w).val + 1 = s.count m
  preferred_holder : ∀ {m w}, (p.manRank m w).val < s.count m →
    ∃ a, s.held w = some a ∧ p.womanRank w a ≤ p.womanRank w m
  not_rejected : ∀ (ν : Matching n), IsStable p ν → ∀ m,
    (p.manRank m (ν m)).val < s.count m → s.held (ν m) = some m
theorem initial_valid (p : Profile n) : Valid p (initial n) := by
  constructor
  · simp [initial]
  · simp [initial]
  · simp [initial]
  · simp [initial]
  · simp [initial]
private theorem chosenHolder_spec (p : Profile n) (s : DAState n) (m w : Fin n) :
    let b := s.chosenHolder m w (proposalAccepted p s m w)
    (b = m ∨ s.held w = some b) ∧ p.womanRank w b ≤ p.womanRank w m ∧
      ∀ a, s.held w = some a → p.womanRank w b ≤ p.womanRank w a := by
  cases h : s.held w with
  | none => simp [chosenHolder, proposalAccepted, h]
  | some a =>
    by_cases ha : p.womanRank w m < p.womanRank w a
    · simp [chosenHolder, proposalAccepted, h, ha, ha.le]
    · simp [chosenHolder, proposalAccepted, h, ha, le_of_not_gt ha]
theorem Valid.apply_proposal {p : Profile n} {s : DAState n}
    (hs : Valid p s) {m w : Fin n} (hm : s.Free m)
    (hnew : (p.manRank m w).val = s.count m) :
    Valid p (s.applyDecision m w (proposalAccepted p s m w)) := by
  let b := s.chosenHolder m w (proposalAccepted p s m w)
  let t := s.applyDecision m w (proposalAccepted p s m w)
  have hspec : (b = m ∨ s.held w = some b) ∧
      p.womanRank w b ≤ p.womanRank w m ∧
      ∀ a, s.held w = some a → p.womanRank w b ≤ p.womanRank w a :=
    chosenHolder_spec p s m w
  have htCount : t.count m = s.count m + 1 := by simp [t, applyDecision]
  have htCount' {i : Fin n} (hi : i ≠ m) : t.count i = s.count i := by
    simp [t, applyDecision, hi]
  have htHeld : t.held w = some b := by simp [t, b, applyDecision]
  have htHeld' {v : Fin n} (hv : v ≠ w) : t.held v = s.held v := by
    simp [t, applyDecision, hv]
  have hsHeld_ne {v i : Fin n} (hi : s.held v = some i) : i ≠ m := by
    rintro rfl
    exact hm v hi
  have no_other_hold {v : Fin n} (hv : v ≠ w) (h : s.held v = some b) : False := by
    rcases hspec.1 with hbm | hbw
    · exact hm v (hbm ▸ h)
    · exact hv (hs.held_unique h hbw)
  have old_proposal {i v : Fin n} (hv : v ≠ w)
      (hi : (p.manRank i v).val < t.count i) : (p.manRank i v).val < s.count i := by
    by_cases him : i = m
    · subst i
      rw [htCount, ← hnew] at hi
      have hne : (p.manRank m v).val ≠ (p.manRank m w).val :=
        fun h ↦ hv ((p.manRank m).injective (Fin.ext h))
      rw [← hnew]
      omega
    · exact htCount' him ▸ hi
  have winner_prefers {ν : Matching n} (hν : IsStable p ν) :
      p.manRank b w ≤ p.manRank b (ν b) := by
    by_contra! hlt
    have hlt' : (p.manRank b (ν b)).val < (p.manRank b w).val := hlt
    rcases hspec.1 with hbm | hbw
    · rw [hbm, hnew] at hlt'
      exact hm (ν m) (hs.not_rejected ν hν m hlt')
    · have hp : (p.manRank b (ν b)).val < s.count b := by
        have := hs.held_last hbw
        omega
      have heq := hs.held_unique (hs.not_rejected ν hν b hp) hbw
      exact (not_lt_of_ge (le_of_eq (congrArg (p.manRank b) heq.symm))) hlt
  have proposed_dominance {i : Fin n} (hi : (p.manRank i w).val < t.count i) :
      p.womanRank w b ≤ p.womanRank w i := by
    by_cases him : i = m
    · exact him ▸ hspec.2.1
    · have hprop : (p.manRank i w).val < s.count i := htCount' him ▸ hi
      obtain ⟨a, ha, hpref⟩ := hs.preferred_holder hprop
      exact (hspec.2.2 a ha).trans hpref
  change Valid p t
  constructor
  · intro i
    by_cases h : i = m
    · subst i
      rw [htCount, ← hnew]
      exact Nat.succ_le_of_lt (p.manRank m w).isLt
    · exact (htCount' h).trans_le (hs.count_le i)
  · intro u v i hu hv
    by_cases huw : u = w
    · subst u
      have hbi : b = i := Option.some.inj (htHeld.symm.trans hu)
      subst i
      by_contra hvw
      exact no_other_hold (Ne.symm hvw) ((htHeld' (Ne.symm hvw)).symm.trans hv)
    · by_cases hvw : v = w
      · subst v
        have hbi : b = i := Option.some.inj (htHeld.symm.trans hv)
        subst i
        exact False.elim (no_other_hold huw ((htHeld' huw).symm.trans hu))
      · exact hs.held_unique ((htHeld' huw).symm.trans hu) ((htHeld' hvw).symm.trans hv)
  · intro v i hvi
    by_cases hv : v = w
    · subst v
      have hbi : b = i := Option.some.inj (htHeld.symm.trans hvi)
      subst i
      rcases hspec.1 with hbm | hbw
      · rw [hbm, htCount, hnew]
      · exact (hs.held_last hbw).trans (htCount' (hsHeld_ne hbw)).symm
    · have h := (htHeld' hv).symm.trans hvi
      exact (hs.held_last h).trans (htCount' (hsHeld_ne h)).symm
  · intro i v hi
    by_cases hv : v = w
    · subst v
      exact ⟨b, htHeld, proposed_dominance hi⟩
    · obtain ⟨a, ha, hle⟩ := hs.preferred_holder (old_proposal hv hi)
      exact ⟨a, (htHeld' hv).trans ha, hle⟩
  · intro ν hν i hi
    by_cases hw : ν i = w
    · rw [hw] at hi ⊢
      by_contra h
      have hbi : b ≠ i := fun e ↦ h (e ▸ htHeld)
      have hbν : ν b ≠ w := fun e ↦ hbi (ν.injective (e.trans hw.symm))
      have hbPref : p.manRank b w < p.manRank b (ν b) :=
        lt_of_le_of_ne (winner_prefers hν) fun e ↦ hbν ((p.manRank b).injective e).symm
      have hwPref : p.womanRank w b < p.womanRank w (ν.symm w) := by
        rw [← hw, ν.symm_apply_apply, hw]
        exact lt_of_le_of_ne (proposed_dominance hi) fun e ↦ hbi ((p.womanRank w).injective e)
      exact hν b w ⟨hbν, hbPref, hwPref⟩
    · exact (htHeld' hw).trans (hs.not_rejected ν hν i (old_proposal hw hi))
theorem Valid.free_count_lt {p : Profile n} {s : DAState n} (hs : Valid p s)
    {m : Fin n} (hm : s.Free m) : s.count m < n := by
  classical
  by_contra! h
  have hheld (w : Fin n) : ∃ a, s.held w = some a := by
    obtain ⟨a, ha, _⟩ := hs.preferred_holder ((p.manRank m w).isLt.trans_le h)
    exact ⟨a, ha⟩
  let holder (w : Fin n) := Classical.choose (hheld w)
  have hholder (w : Fin n) : s.held w = some (holder w) := Classical.choose_spec (hheld w)
  have hi : Function.Injective holder := fun u v huv ↦
    hs.held_unique (hholder u) (by rw [huv]; exact hholder v)
  obtain ⟨w, hw⟩ := Finite.surjective_of_injective hi m
  exact hm w (hw ▸ hholder w)
private def Complete (s : DAState n) : Prop := ∀ m, ∃ w, s.held w = some m
private noncomputable def toMatching (s : DAState n) (hc : s.Complete) : Matching n := by
  let wife (m : Fin n) := Classical.choose (hc m)
  have hw (m : Fin n) : s.held (wife m) = some m := Classical.choose_spec (hc m)
  have hi : Function.Injective wife := by
    intro m a h
    exact Option.some.inj ((hw m).symm.trans (h ▸ hw a))
  exact Equiv.ofBijective wife ⟨hi, Finite.surjective_of_injective hi⟩
theorem held_toMatching (s : DAState n) (hc : s.Complete) (m : Fin n) :
    s.held (s.toMatching hc m) = some m :=
  Classical.choose_spec (hc m)
theorem Valid.isManOptimal_toMatching {p : Profile n} {s : DAState n} (hs : Valid p s)
    (hc : s.Complete) : IsManOptimal p (s.toMatching hc) := by
  let μ := s.toMatching hc
  have hh := s.held_toMatching hc
  change IsManOptimal p μ
  constructor
  · intro m w hb
    have hl := hs.held_last (hh m)
    have hrank : (p.manRank m w).val < s.count m := by
      exact (show (p.manRank m w).val < (p.manRank m (μ m)).val from hb.2.1).trans
        (hl ▸ Nat.lt_succ_self _)
    obtain ⟨a, ha, hpref⟩ := hs.preferred_holder hrank
    have ha' := hh (μ.symm w)
    change s.held (μ (μ.symm w)) = _ at ha'
    rw [μ.apply_symm_apply] at ha'
    have heq := Option.some.inj (ha.symm.trans ha')
    exact hb.2.2.not_ge (heq ▸ hpref)
  · intro ν hν m
    by_contra! h
    have hrank : (p.manRank m (ν m)).val < s.count m := by
      exact (show (p.manRank m (ν m)).val < (p.manRank m (μ m)).val from h).trans
        (hs.held_last (hh m) ▸ Nat.lt_succ_self _)
    have hmate := hs.held_unique (hs.not_rejected ν hν m hrank) (hh m)
    exact h.ne (congrArg (p.manRank m) hmate)
private def readyMen (s : DAState n) : Finset (Fin n) :=
  Finset.univ.filter fun m ↦ (∀ w, s.held w ≠ some m) ∧ s.count m < n
theorem mem_readyMen {s : DAState n} {m : Fin n} :
    m ∈ s.readyMen ↔ s.Free m ∧ s.count m < n := by
  simp [readyMen, Free]
private def nextProposal (rank : Fin n → Equiv.Perm (Fin n)) (s : DAState n) :
    Option (Fin n × Fin n) :=
  if h : s.readyMen.Nonempty then
    let m := s.readyMen.min' h
    let hm := mem_readyMen.mp (Finset.min'_mem _ h)
    some (m, s.proposalTarget rank m hm.2)
  else none
theorem nextProposal_some {rank : Fin n → Equiv.Perm (Fin n)} {s : DAState n}
    {m w : Fin n} (h : s.nextProposal rank = some (m, w)) :
    s.Free m ∧ (rank m w).val = s.count m := by
  unfold nextProposal at h
  split at h
  · rename_i hne
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact ⟨(mem_readyMen.mp (Finset.min'_mem _ hne)).1, by simp [proposalTarget]⟩
  · contradiction
theorem Valid.complete_of_nextProposal_none {p : Profile n} {s : DAState n}
    (hs : Valid p s) (hd : s.nextProposal p.manRank = none) : s.Complete := by
  classical
  intro m
  by_contra! hm
  have hfree : s.Free m := hm
  have hne : s.readyMen.Nonempty := ⟨m, mem_readyMen.mpr ⟨hfree, hs.free_count_lt hfree⟩⟩
  simp [nextProposal, hne] at hd
private def advance (p : Profile n) (s : DAState n) : DAState n :=
  match s.nextProposal p.manRank with
  | none => s
  | some (m, w) => s.applyDecision m w (proposalAccepted p s m w)
theorem Valid.advance {p : Profile n} {s : DAState n} (hs : Valid p s) :
    Valid p (advance p s) := by
  cases h : s.nextProposal p.manRank with
  | none => simpa only [DAState.advance, h] using hs
  | some a =>
    obtain ⟨m, w⟩ := a
    have hp := nextProposal_some h
    simpa only [DAState.advance, h] using hs.apply_proposal hp.1 hp.2
private def proposalCount (s : DAState n) : ℕ := ∑ m, s.count m
private theorem proposalCount_applyDecision (s : DAState n) (m w : Fin n) (accept : Bool) :
    (s.applyDecision m w accept).proposalCount = s.proposalCount + 1 := by
  let t := s.applyDecision m w accept
  have hm : m ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
  have he :
      ∑ i ∈ Finset.univ.erase m, t.count i = ∑ i ∈ Finset.univ.erase m, s.count i := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [t, applyDecision, (Finset.mem_erase.mp hi).1]
  change t.proposalCount = _
  unfold proposalCount
  rw [← Finset.sum_erase_add _ t.count hm, ← Finset.sum_erase_add _ s.count hm, he]
  simp [t, applyDecision, add_assoc]
theorem proposalCount_advance_of_some {p : Profile n} {s : DAState n} {a : Fin n × Fin n}
    (h : s.nextProposal p.manRank = some a) :
    (advance p s).proposalCount = s.proposalCount + 1 := by
  obtain ⟨m, w⟩ := a
  rw [advance, h]
  exact proposalCount_applyDecision s m w _
theorem Valid.proposalCount_le {p : Profile n} {s : DAState n} (hs : Valid p s) :
    s.proposalCount ≤ n * n := by
  calc
    _ ≤ ∑ _ : Fin n, n := Finset.sum_le_sum fun m _ ↦ hs.count_le m
    _ = _ := by simp
private abbrev lhsOfEq {α : Sort _} {a b : α} (_ : a = b) : α := a
private abbrev run (p : Profile n) : ℕ → DAState n :=
  lhsOfEq (@AbunLP.DAState.run_alias) p
private theorem run_zero (p : Profile n) : run p 0 = initial n := AbunLP.DAState.run_zero p
private theorem run_succ (p : Profile n) (k : ℕ) : run p (k + 1) = advance p (run p k) :=
  AbunLP.DAState.run_succ p k
theorem valid_run (p : Profile n) (k : ℕ) : Valid p (run p k) := by
  induction k with
  | zero => exact initial_valid p
  | succ k ih => exact ih.advance
private theorem le_proposalCount_run_of_next {p : Profile n} {k : ℕ}
    (h : (run p k).nextProposal p.manRank ≠ none) : k ≤ (run p k).proposalCount := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    cases hprev : (run p k).nextProposal p.manRank with
    | none =>
      have he : run p (k + 1) = run p k := by simp only [DAState.run_zero, DAState.run_succ, advance, hprev]
      exact False.elim (h (he ▸ hprev))
    | some a =>
      have hcount := proposalCount_advance_of_some hprev
      change k + 1 ≤ (advance p (run p k)).proposalCount
      rw [hcount]
      exact Nat.succ_le_succ (ih (by rw [hprev]; exact Option.some_ne_none _))
theorem nextProposal_run_sq_eq_none (p : Profile n) :
    (run p (n * n)).nextProposal p.manRank = none := by
  cases h : (run p (n * n)).nextProposal p.manRank with
  | none => rfl
  | some a =>
    have hl := le_proposalCount_run_of_next (p := p) (k := n * n)
      (by rw [h]; exact Option.some_ne_none _)
    have hu := (valid_run p (n * n + 1)).proposalCount_le
    change (advance p (run p (n * n))).proposalCount ≤ n * n at hu
    rw [proposalCount_advance_of_some h] at hu
    omega
theorem complete_run_sq (p : Profile n) : (run p (n * n)).Complete :=
  (valid_run p (n * n)).complete_of_nextProposal_none (nextProposal_run_sq_eq_none p)
private noncomputable def matching (p : Profile n) : Matching n :=
  (run p (n * n)).toMatching (complete_run_sq p)
theorem isManOptimal_matching (p : Profile n) : IsManOptimal p (matching p) :=
  (valid_run p (n * n)).isManOptimal_toMatching (complete_run_sq p)
theorem proposed_run_sq_iff (p : Profile n) (m w : Fin n) :
    (p.manRank m w).val < (run p (n * n)).count m ↔
      p.manRank m w ≤ p.manRank m (matching p m) := by
  have hlast : (p.manRank m (matching p m)).val + 1 = (run p (n * n)).count m :=
    (valid_run p (n * n)).held_last
      ((run p (n * n)).held_toMatching (complete_run_sq p) m)
  rw [← hlast]
  exact Nat.lt_succ_iff
theorem count_le_advance (p : Profile n) (s : DAState n) (m : Fin n) :
    s.count m ≤ (advance p s).count m := by
  cases h : s.nextProposal p.manRank with
  | none => simp only [advance, h, le_rfl]
  | some a =>
    obtain ⟨i, w⟩ := a
    rw [advance, h]
    by_cases hm : m = i
    · subst m
      simp [applyDecision]
    · simp [applyDecision, hm]
theorem count_mono_run (p : Profile n) (m : Fin n) :
    Monotone fun k ↦ (run p k).count m :=
  monotone_nat_of_le_succ fun k ↦ count_le_advance p (run p k) m
theorem run_eq_of_agree_on_proposed {p q : Profile n} (k : ℕ)
    (hmen : p.manRank = q.manRank)
    (hwomen : ∀ w a b,
      (p.manRank a w).val < (run p k).count a →
      (p.manRank b w).val < (run p k).count b →
      (p.womanRank w a < p.womanRank w b ↔ q.womanRank w a < q.womanRank w b)) :
    run q k = run p k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hprev := ih fun w a b ha hb ↦ hwomen w a b
      (ha.trans_le (count_le_advance p (run p k) a))
      (hb.trans_le (count_le_advance p (run p k) b))
    change advance q (run q k) = advance p (run p k)
    rw [hprev]
    unfold advance
    rw [← hmen]
    cases hn : (run p k).nextProposal p.manRank with
    | none => rfl
    | some pair =>
      obtain ⟨m, w⟩ := pair
      cases ha : (run p k).held w with
      | none => simp [proposalAccepted, ha]
      | some a =>
        have hnew : (p.manRank m w).val < (run p (k + 1)).count m := by
          change _ < (advance p (run p k)).count m
          rw [advance, hn, (nextProposal_some hn).2]
          simp [applyDecision]
        have hold : (p.manRank a w).val < (run p (k + 1)).count a := by
          have hlast := (valid_run p k).held_last ha
          have hpast : (p.manRank a w).val < (run p k).count a := by
            rw [← hlast]
            exact Nat.lt_succ_self _
          exact hpast.trans_le (count_le_advance p (run p k) a)
        simp only [proposalAccepted, ha, Option.elim_some]
        exact congrArg ((run p k).applyDecision m w)
          (decide_eq_decide.mpr (hwomen w m a hnew hold).symm)
theorem run_eq_of_agree_on_proposed_scores {x y : ScoreProfile n} (k : ℕ)
    (hx : ∀ w, Function.Injective (x (.inr w)))
    (hy : ∀ w, Function.Injective (y (.inr w)))
    (hmen : (profileOfScores x).manRank = (profileOfScores y).manRank)
    (hwomen : ∀ w a, ((profileOfScores x).manRank a w).val <
      (run (profileOfScores x) k).count a → x (.inr w) a = y (.inr w) a) :
    run (profileOfScores y) k = run (profileOfScores x) k := by
  apply run_eq_of_agree_on_proposed k hmen
  intro w a b ha hb
  change rankPermutation (x (.inr w)) a < rankPermutation (x (.inr w)) b ↔
    rankPermutation (y (.inr w)) a < rankPermutation (y (.inr w)) b
  rw [rankPermutation_lt_iff (hx w), rankPermutation_lt_iff (hy w),
    hwomen w a ha, hwomen w b hb]
private def proposedCells (rank : Fin n → Equiv.Perm (Fin n)) (s : DAState n) :
    Set (Fin n × Fin n) := {c | (rank c.2 c.1).val < s.count c.2}
theorem matching_symm_mem_proposedCells (p : Profile n) (w : Fin n) :
    (w, (matching p).symm w) ∈ proposedCells p.manRank (run p (n * n)) := by
  apply (proposed_run_sq_iff p ((matching p).symm w) w).mpr
  rw [(matching p).apply_symm_apply]
end DAState
end StepA4
end

-- UniformStreamRanks
section
open Function MeasureTheory
open scoped ENNReal StepA4
namespace StepA4
variable {n T : ℕ}
private def IsStreamHit (raw : Fin T → Fin n) (w : Fin n) (k : ℕ) : Prop :=
  k = T ∨ ∃ i : Fin T, i.val = k ∧ raw i = w
private theorem exists_streamHit (raw : Fin T → Fin n) (w : Fin n) :
    ∃ k, IsStreamHit raw w k :=
  ⟨T, Or.inl rfl⟩
private noncomputable def streamFirstHit (raw : Fin T → Fin n) (w : Fin n) : ℕ := by
  classical
  exact Nat.find (exists_streamHit raw w)
private theorem streamFirstHit_spec (raw : Fin T → Fin n) (w : Fin n) :
    IsStreamHit raw w (streamFirstHit raw w) := by
  classical
  exact Nat.find_spec (exists_streamHit raw w)
private theorem streamFirstHit_le (raw : Fin T → Fin n) (w : Fin n) {k : ℕ}
    (hk : IsStreamHit raw w k) : streamFirstHit raw w ≤ k := by
  classical
  exact Nat.find_min' (exists_streamHit raw w) hk
theorem streamFirstHit_lt_iff (raw : Fin T → Fin n) (w : Fin n) {k : ℕ} (hk : k ≤ T) :
    streamFirstHit raw w < k ↔ ∃ j : Fin T, j.val < k ∧ raw j = w := by
  constructor
  · intro h
    rcases streamFirstHit_spec raw w with hT | ⟨j, hj, hw⟩
    · omega
    · exact ⟨j, hj ▸ h, hw⟩
  · rintro ⟨j, hj, hw⟩
    exact (streamFirstHit_le raw w (Or.inr ⟨j, rfl, hw⟩)).trans_lt hj
theorem streamFirstHit_fresh (raw : Fin T → Fin n) (i : Fin T)
    (hfresh : ∀ j : Fin T, j < i → raw j ≠ raw i) :
    streamFirstHit raw (raw i) = i.val := by
  apply le_antisymm (streamFirstHit_le raw (raw i) (Or.inr ⟨i, rfl, rfl⟩))
  by_contra! h
  obtain ⟨j, hj, heq⟩ := (streamFirstHit_lt_iff raw (raw i) i.isLt.le).1 h
  exact hfresh j hj heq
private noncomputable def streamKey (raw : Fin T → Fin n) (fallback : Equiv.Perm (Fin n))
    (w : Fin n) : ℕ :=
  streamFirstHit raw w * (n + 1) + (fallback w).val
private theorem streamKey_lt_of_firstHit_lt (raw : Fin T → Fin n)
    (fallback : Equiv.Perm (Fin n)) {w u : Fin n}
    (h : streamFirstHit raw w < streamFirstHit raw u) :
    streamKey raw fallback w < streamKey raw fallback u := by
  have hmul := Nat.mul_le_mul_right (n + 1) (Nat.succ_le_of_lt h)
  rw [Nat.succ_mul] at hmul
  have hw := (fallback w).isLt
  unfold streamKey
  omega
private theorem streamKey_injective (raw : Fin T → Fin n)
    (fallback : Equiv.Perm (Fin n)) : Injective (streamKey raw fallback) := by
  intro w u h
  have hfirst : streamFirstHit raw w = streamFirstHit raw u :=
    le_antisymm (le_of_not_gt fun h' ↦
      (streamKey_lt_of_firstHit_lt raw fallback h').ne h.symm)
      (le_of_not_gt fun h' ↦ (streamKey_lt_of_firstHit_lt raw fallback h').ne h)
  apply fallback.injective
  apply Fin.ext
  simpa only [streamKey, hfirst, Nat.add_left_cancel_iff] using h
private noncomputable def streamRank (raw : Fin T → Fin n) (fallback : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin n) :=
  rankPermutation fun w ↦ (streamKey raw fallback w : ℝ)
private theorem streamRank_lt_iff (raw : Fin T → Fin n) (fallback : Equiv.Perm (Fin n))
    (w u : Fin n) :
    streamRank raw fallback w < streamRank raw fallback u ↔
      streamKey raw fallback w < streamKey raw fallback u := by
  have hinj : Injective (fun w ↦ (streamKey raw fallback w : ℝ)) :=
    (Nat.cast_injective (R := ℝ)).comp (streamKey_injective raw fallback)
  exact (rankPermutation_lt_iff hinj w u).trans Nat.cast_lt
theorem streamRank_lt_fresh_iff (raw : Fin T → Fin n) (fallback : Equiv.Perm (Fin n))
    (i : Fin T) (hfresh : ∀ j : Fin T, j < i → raw j ≠ raw i) (w : Fin n) :
    streamRank raw fallback w < streamRank raw fallback (raw i) ↔
      ∃ j : Fin T, j < i ∧ raw j = w := by
  have hi := streamFirstHit_fresh raw i hfresh
  change streamRank raw fallback w < streamRank raw fallback (raw i) ↔
    ∃ j : Fin T, j.val < i.val ∧ raw j = w
  rw [streamRank_lt_iff, ← streamFirstHit_lt_iff raw w i.isLt.le]
  constructor
  · intro h
    rcases lt_trichotomy (streamFirstHit raw w) i.val with hlt | heq | hgt
    · exact hlt
    · rcases streamFirstHit_spec raw w with hT | ⟨j, hj, hw⟩
      · omega
      · have hji : j = i := Fin.ext (hj.trans heq)
        exact (h.ne (by rw [← hw, hji])).elim
    · exact (lt_asymm h (streamKey_lt_of_firstHit_lt raw fallback (hi ▸ hgt))).elim
  · intro h
    exact streamKey_lt_of_firstHit_lt raw fallback (hi.symm ▸ h)
private theorem streamFirstHit_relabel (raw : Fin T → Fin n) (e : Equiv.Perm (Fin n))
    (w : Fin n) :
    streamFirstHit (fun i ↦ e.symm (raw i)) w = streamFirstHit raw (e w) := by
  have h (k : ℕ) : IsStreamHit (fun i ↦ e.symm (raw i)) w k ↔
      IsStreamHit raw (e w) k := by
    simp [IsStreamHit, Equiv.symm_apply_eq]
  exact le_antisymm
    (streamFirstHit_le _ _ ((h _).mpr (streamFirstHit_spec raw (e w))))
    (streamFirstHit_le _ _ ((h _).mp (streamFirstHit_spec _ w)))
theorem streamRank_relabel (raw : Fin T → Fin n) (fallback e : Equiv.Perm (Fin n)) :
    streamRank (fun i ↦ e.symm (raw i)) (e.trans fallback) =
      e.trans (streamRank raw fallback) := by
  let p := streamRank (fun i ↦ e.symm (raw i)) (e.trans fallback)
  let q := e.trans (streamRank raw fallback)
  have hcmp (i j : Fin n) : p i < p j ↔ q i < q j := by
    change streamRank _ _ i < streamRank _ _ j ↔
      streamRank raw fallback (e i) < streamRank raw fallback (e j)
    simp only [streamRank_lt_iff, streamKey, streamFirstHit_relabel, Equiv.trans_apply]
  have hmono : StrictMono (q ∘ p.symm) := fun i j hij ↦
    (hcmp (p.symm i) (p.symm j)).mp (by simpa using hij)
  apply Equiv.ext
  intro i
  change p i = q i
  simpa only [id_eq, Function.comp_apply, Equiv.symm_apply_apply] using
    (hmono.id_le (p i)).antisymm (hmono.le_id (p i))
private theorem uniformOfFintype_equiv_preserving {α : Type*}
    [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (e : Equiv.Perm α) :
    MeasurePreserving e (PMF.uniformOfFintype α).toMeasure (PMF.uniformOfFintype α).toMeasure := by
  have hm : Measurable e := measurable_of_countable _
  refine ⟨hm, Measure.ext_of_singleton fun a ↦ ?_⟩
  have he : e ⁻¹' ({a} : Set α) = {e.symm a} := by
    ext x
    change e x = a ↔ x = e.symm a
    exact e.eq_symm_apply.symm
  rw [Measure.map_apply hm (measurableSet_singleton a), he,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton (e.symm a)),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton a)]
  simp
theorem measurePreserving_streamRank [Nonempty (Fin n)]
    [MeasurableSpace (Equiv.Perm (Fin n))] [MeasurableSingletonClass (Equiv.Perm (Fin n))] :
    MeasurePreserving (fun z : (Fin T → Fin n) × Equiv.Perm (Fin n) ↦ streamRank z.1 z.2)
      ((Measure.pi fun _ : Fin T ↦ (PMF.uniformOfFintype (Fin n)).toMeasure).prod
        (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure)
      (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure := by
  let law := (Measure.pi fun _ : Fin T ↦ (PMF.uniformOfFintype (Fin n)).toMeasure).prod
    (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure
  let rank := fun z : (Fin T → Fin n) × Equiv.Perm (Fin n) ↦ streamRank z.1 z.2
  have hr : Measurable rank := measurable_of_countable _
  let ν := law.map rank
  have : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hr.aemeasurable
  have hequal (p q : Equiv.Perm (Fin n)) : ν {p} = ν {q} := by
    let e : Equiv.Perm (Fin n) := q.trans p.symm
    let precompose : Equiv.Perm (Equiv.Perm (Fin n)) :=
      ⟨e.trans, e.symm.trans, fun u ↦ Equiv.ext fun i ↦ by
        change u (e (e.symm i)) = u i
        rw [e.apply_symm_apply], fun u ↦ Equiv.ext fun i ↦ by
        change u (e.symm (e i)) = u i
        rw [e.symm_apply_apply]⟩
    let reindex := Prod.map (fun raw : Fin T → Fin n ↦ fun i ↦ e.symm (raw i)) precompose
    have hm : MeasurePreserving reindex law law :=
      (measurePreserving_pi _ _ (fun _ : Fin T ↦ uniformOfFintype_equiv_preserving e.symm)).prod
        (uniformOfFintype_equiv_preserving precompose)
    have hcongr : rank ⁻¹' ({p} : Set (Equiv.Perm (Fin n))) =
        reindex ⁻¹' (rank ⁻¹' {q}) := by
      ext z
      change (rank z = p) ↔ rank (reindex z) = q
      change (streamRank z.1 z.2 = p) ↔
        streamRank (fun i ↦ e.symm (z.1 i)) (e.trans z.2) = q
      rw [streamRank_relabel]
      constructor
      · rintro rfl
        simp [e, Equiv.trans_assoc]
      · intro h
        apply Equiv.ext
        intro i
        have hi := DFunLike.congr_fun h (e.symm i)
        simpa [e] using hi
    change law.map rank {p} = law.map rank {q}
    rw [Measure.map_apply hr (measurableSet_singleton p),
      Measure.map_apply hr (measurableSet_singleton q), hcongr]
    exact hm.measure_preimage (hr (measurableSet_singleton q)).nullMeasurableSet
  refine ⟨hr, Measure.ext_of_singleton fun p ↦ ?_⟩
  have hsum : ν {p} * (Fintype.card (Equiv.Perm (Fin n)) : ℝ≥0∞) = 1 := by
    calc
      _ = ∑' q : Equiv.Perm (Fin n), ν {q} := by
        rw [tsum_fintype, Finset.sum_congr rfl (fun q _ ↦ hequal q p), Finset.sum_const,
          Finset.card_univ, nsmul_eq_mul, mul_comm]
      _ = 1 := by simpa only [Measure.toPMF_apply] using ν.toPMF.tsum_coe
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton p), PMF.uniformOfFintype_apply]
  exact ENNReal.eq_inv_of_mul_eq_one_left hsum
private theorem measurePreserving_pairRows {ι α β : Type*} [Fintype ι] [Finite α] [Finite β]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass α]
    [MeasurableSingletonClass β] (μ : Measure α) (ν : Measure β)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    MeasurePreserving (fun z : (ι → α) × (ι → β) ↦ fun i ↦ (z.1 i, z.2 i))
      ((Measure.pi fun _ : ι ↦ μ).prod (Measure.pi fun _ : ι ↦ ν))
      (Measure.pi fun _ : ι ↦ μ.prod ν) := by
  let f := fun z : (ι → α) × (ι → β) ↦ fun i ↦ (z.1 i, z.2 i)
  have hf : Measurable f := measurable_of_countable _
  refine ⟨hf, Measure.ext_of_singleton fun a ↦ ?_⟩
  have hpre : f ⁻¹' ({a} : Set (ι → α × β)) =
      {fun i ↦ (a i).1} ×ˢ {fun i ↦ (a i).2} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_prod, funext_iff,
      Prod.ext_iff, f, forall_and]
  rw [Measure.map_apply hf (measurableSet_singleton a), hpre, Measure.prod_prod,
    Measure.pi_singleton, Measure.pi_singleton, Measure.pi_singleton, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ ↦ by
    rw [← Measure.prod_prod, Set.singleton_prod_singleton]
theorem measurePreserving_curry_iid {ι κ α : Type*} [Fintype ι] [Fintype κ] [Finite α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (μ : Measure α) [IsProbabilityMeasure μ] :
    MeasurePreserving (Equiv.curry ι κ α)
      (Measure.pi fun _ : ι × κ ↦ μ)
      (Measure.pi fun _ : ι ↦ Measure.pi fun _ : κ ↦ μ) := by
  let e := Equiv.curry ι κ α
  have he : Measurable e := measurable_of_countable _
  refine ⟨he, Measure.ext_of_singleton fun a ↦ ?_⟩
  have hpre : e ⁻¹' ({a} : Set (ι → κ → α)) = {e.symm a} := by
    ext x
    change e x = a ↔ x = e.symm a
    exact e.eq_symm_apply.symm
  rw [Measure.map_apply he (measurableSet_singleton a), hpre, Measure.pi_singleton,
    Measure.pi_singleton]
  simp only [Measure.pi_singleton, e, Equiv.curry_symm_apply, Function.uncurry,
    ← Finset.univ_product_univ, Finset.prod_product]
theorem measurePreserving_streamRankRows {ι : Type*} [Fintype ι] [Nonempty (Fin n)]
    [MeasurableSpace (Equiv.Perm (Fin n))] [MeasurableSingletonClass (Equiv.Perm (Fin n))] :
    MeasurePreserving
      (fun z : (ι → Fin T → Fin n) × (ι → Equiv.Perm (Fin n)) ↦
        fun i ↦ streamRank (z.1 i) (z.2 i))
      ((Measure.pi fun _ : ι ↦ Measure.pi fun _ : Fin T ↦
        (PMF.uniformOfFintype (Fin n)).toMeasure).prod
          (Measure.pi fun _ : ι ↦ (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure))
      (Measure.pi fun _ : ι ↦ (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure) := by
  let rawLaw : Measure (Fin T → Fin n) :=
    Measure.pi fun _ : Fin T ↦ (PMF.uniformOfFintype (Fin n)).toMeasure
  let permLaw : Measure (Equiv.Perm (Fin n)) :=
    (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure
  have : IsProbabilityMeasure rawLaw := inferInstanceAs (IsProbabilityMeasure (Measure.pi _))
  have : IsProbabilityMeasure permLaw :=
    inferInstanceAs (IsProbabilityMeasure (PMF.uniformOfFintype _).toMeasure)
  have h := measurePreserving_pi (fun _ : ι ↦ rawLaw.prod permLaw) (fun _ ↦ permLaw)
    (fun _ ↦ measurePreserving_streamRank (n := n) (T := T))
  have hpair := measurePreserving_pairRows (ι := ι) rawLaw permLaw
  have hc := h.comp hpair
  change MeasurePreserving _ ((Measure.pi fun _ : ι ↦ rawLaw).prod
    (Measure.pi fun _ : ι ↦ permLaw)) (Measure.pi fun _ : ι ↦ permLaw)
  exact hc
private theorem measurePreserving_profileOfRankPairs (n : ℕ) :
    MeasurePreserving
      (fun z : (Fin n → Equiv.Perm (Fin n)) × (Fin n → Equiv.Perm (Fin n)) ↦
        (⟨z.1, z.2⟩ : StableMarriage.Profile n))
      ((Measure.pi fun _ : Fin n ↦ (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure).prod
        (Measure.pi fun _ : Fin n ↦ (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure))
      (StableMarriage.uniformProfile n).toMeasure := by
  let e : ((Fin n → Equiv.Perm (Fin n)) × (Fin n → Equiv.Perm (Fin n))) ≃
      StableMarriage.Profile n :=
    ⟨fun z ↦ ⟨z.1, z.2⟩, fun p ↦ (p.manRank, p.womanRank), fun _ ↦ rfl, fun _ ↦ rfl⟩
  have hm : Measurable e := measurable_of_countable _
  refine ⟨hm, Measure.ext_of_singleton fun p ↦ ?_⟩
  have hpre : e ⁻¹' ({p} : Set (StableMarriage.Profile n)) = {p.manRank} ×ˢ {p.womanRank} := by
    rw [Set.singleton_prod_singleton]
    ext z
    change e z = p ↔ z = e.symm p
    exact e.eq_symm_apply.symm
  change Measure.map e _ {p} = _
  rw [Measure.map_apply hm (measurableSet_singleton p), hpre, Measure.prod_prod,
    Measure.pi_singleton, Measure.pi_singleton, StableMarriage.uniformProfile,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton p), PMF.uniformOfFintype_apply]
  simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← Fintype.card_congr e]
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    Nat.cast_pow, ← pow_add, ENNReal.inv_pow]
theorem measurePreserving_streamProfile [Nonempty (Fin n)] :
    MeasurePreserving
      (fun z : (Fin n × Fin T → Fin n) × (Fin n → Equiv.Perm (Fin n)) ×
          (Fin n → Equiv.Perm (Fin n)) ↦
        (⟨fun m ↦ streamRank (fun j ↦ z.1 (m, j)) (z.2.1 m), z.2.2⟩ :
          StableMarriage.Profile n))
      ((Measure.pi fun _ : Fin n × Fin T ↦ (PMF.uniformOfFintype (Fin n)).toMeasure).prod
        ((Measure.pi fun _ : Fin n ↦ (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure).prod
          (Measure.pi fun _ : Fin n ↦ (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure)))
      (StableMarriage.uniformProfile n).toMeasure := by
  let rawLaw : Measure (Fin n × Fin T → Fin n) :=
    Measure.pi fun _ : Fin n × Fin T ↦ (PMF.uniformOfFintype (Fin n)).toMeasure
  let permRows : Measure (Fin n → Equiv.Perm (Fin n)) :=
    Measure.pi fun _ : Fin n ↦ (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure
  have : IsProbabilityMeasure permRows := inferInstanceAs (IsProbabilityMeasure (Measure.pi _))
  have hcur := measurePreserving_curry_iid (ι := Fin n) (κ := Fin T)
    (PMF.uniformOfFintype (Fin n)).toMeasure
  have hman := (measurePreserving_streamRankRows (ι := Fin n) (n := n) (T := T)).comp
    (hcur.prod (MeasurePreserving.id permRows))
  exact (measurePreserving_profileOfRankPairs n).comp
    ((hman.prod (MeasurePreserving.id permRows)).comp
      (measurePreserving_prodAssoc rawLaw permRows permRows).symm)
end StepA4
end

-- AdaptiveFiniteQueries
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace StepA4
variable {I A : Type*}
private def adaptiveTranscript (next : List A → I) (table : I → A) : ℕ → List A
  | 0 => []
  | t + 1 =>
      let history := adaptiveTranscript next table t
      history ++ [table (next history)]
@[simp] theorem length_adaptiveTranscript (next : List A → I) (table : I → A) (T : ℕ) :
    (adaptiveTranscript next table T).length = T := by
  induction T with
  | zero => rfl
  | succ T ih => simp [adaptiveTranscript, ih]
private def adaptiveTranscriptFn (next : List A → I) (table : I → A) (T : ℕ) (t : Fin T) : A :=
  (adaptiveTranscript next table T)[t.val]'(by simp [t.isLt])
@[simp] theorem ofFn_adaptiveTranscriptFn (next : List A → I) (table : I → A) (T : ℕ) :
    List.ofFn (adaptiveTranscriptFn next table T) = adaptiveTranscript next table T := by
  apply List.ext_getElem (by simp)
  intro i _ _
  simp [adaptiveTranscriptFn]
theorem take_adaptiveTranscript (next : List A → I) (table : I → A) {t T : ℕ} (h : t ≤ T) :
    (adaptiveTranscript next table T).take t = adaptiveTranscript next table t := by
  induction T with
  | zero => simp [adaptiveTranscript, Nat.eq_zero_of_le_zero h]
  | succ T ih =>
    by_cases ht : t ≤ T
    · rw [adaptiveTranscript, List.take_append_of_le_length (by simpa using ht), ih ht]
    · have hEq : t = T + 1 := by omega
      subst t
      exact List.take_of_length_le (by simp)
private def adaptiveQueryIndex (next : List A → I) {T : ℕ} (y : Fin T → A) (t : Fin T) : I :=
  next ((List.ofFn y).take t.val)
theorem adaptiveTranscriptFn_apply (next : List A → I) (table : I → A)
    (T : ℕ) (t : Fin T) :
    adaptiveTranscriptFn next table T t = table (next (adaptiveTranscript next table t.val)) := by
  have ht : t.val < (adaptiveTranscript next table T).length := by simp [t.isLt]
  have heq := List.take_succ_eq_append_getElem ht
  rw [take_adaptiveTranscript next table (Nat.succ_le_of_lt t.isLt),
    take_adaptiveTranscript next table (Nat.le_of_lt t.isLt), adaptiveTranscript] at heq
  exact (List.singleton_inj.mp (List.append_cancel_left heq)).symm
theorem adaptiveTranscriptFn_eq_iff (next : List A → I) (table : I → A) {T : ℕ} (y : Fin T → A) :
    adaptiveTranscriptFn next table T = y ↔ ∀ t, table (adaptiveQueryIndex next y t) = y t := by
  constructor
  · rintro rfl t
    simp only [adaptiveQueryIndex, ofFn_adaptiveTranscriptFn,
      take_adaptiveTranscript next table (Nat.le_of_lt t.isLt)]
    exact (adaptiveTranscriptFn_apply next table T t).symm
  · intro hy
    apply List.ofFn_injective
    rw [ofFn_adaptiveTranscriptFn]
    suffices h : ∀ k ≤ T, adaptiveTranscript next table k = (List.ofFn y).take k by
      rw [h T le_rfl, List.take_of_length_le (by simp)]
    intro k hk
    induction k with
    | zero => rfl
    | succ k ih =>
      have hk' : k < T := hk
      rw [adaptiveTranscript, ih (Nat.le_of_lt hk'),
        List.take_succ_eq_append_getElem (show k < (List.ofFn y).length by simpa)]
      simpa only [List.getElem_ofFn, adaptiveQueryIndex] using
        congrArg ((List.ofFn y).take k ++ [·]) (hy ⟨k, hk'⟩)
variable [Fintype I] [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
theorem map_adaptiveTranscriptFn_eq_pi (μ : Measure A) [IsProbabilityMeasure μ]
    (next : List A → I) (T : ℕ)
    (fresh : ∀ y : Fin T → A, Function.Injective (adaptiveQueryIndex next y)) :
    Measure.map (fun table ↦ adaptiveTranscriptFn next table T)
      (Measure.pi (fun _ : I ↦ μ)) = Measure.pi (fun _ : Fin T ↦ μ) := by
  classical
  refine Measure.ext_of_singleton fun y ↦ ?_
  let q := adaptiveQueryIndex next y
  let B (i : I) : Set A := {a | ∀ t, q t = i → a = y t}
  have hbox : (fun table ↦ adaptiveTranscriptFn next table T) ⁻¹' {y} = univ.pi B := by
    ext table
    change adaptiveTranscriptFn next table T = y ↔ _
    rw [adaptiveTranscriptFn_eq_iff, Set.mem_univ_pi]
    exact ⟨fun h _ t ht ↦ ht ▸ h t, fun h t ↦ h (q t) t rfl⟩
  have hsingle (t : Fin T) : B (q t) = {y t} := by
    ext a
    change (∀ s, q s = q t → a = y s) ↔ a = y t
    exact ⟨fun h ↦ h t rfl, fun ha s hs ↦ (fresh y hs).symm ▸ ha⟩
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton y), hbox,
    Measure.pi_pi, Measure.pi_singleton]
  calc
    (∏ i, μ (B i)) = ∏ i ∈ Finset.univ.image q, μ (B i) := by
      symm
      refine Finset.prod_subset (Finset.subset_univ _) fun i _ hi ↦ ?_
      have hBi : B i = univ := by
        ext a
        simp only [B, mem_ofPred_eq, mem_univ, iff_true]
        exact fun t ht ↦ (hi (Finset.mem_image.mpr ⟨t, Finset.mem_univ _, ht⟩)).elim
      rw [hBi, measure_univ]
    _ = ∏ t, μ (B (q t)) := Finset.prod_image (fresh y).injOn
    _ = ∏ t, μ {y t} := by simp only [hsingle]
end StepA4
end

-- DAStreamSimulation
section
open StableMarriage
namespace StepA4
private structure DAStreamState (n : ℕ) where
  da : DAState n
  observed : Fin n → List (Fin n)
namespace DAStreamState
variable {n T : ℕ}
private def initial (n : ℕ) : DAStreamState n := ⟨DAState.initial n, fun _ ↦ []⟩
private def proposer (seed : Fin n) (s : DAStreamState n) : Fin n :=
  if h : s.da.readyMen.Nonempty then s.da.readyMen.min' h else seed
private def step (seed : Fin n) (women : Fin n → Equiv.Perm (Fin n))
    (s : DAStreamState n) (w : Fin n) : DAStreamState n :=
  let m := proposer seed s
  let q : Profile n := ⟨fun _ ↦ Equiv.refl _, women⟩
  ⟨if s.da.readyMen.Nonempty ∧ w ∉ s.observed m then
      s.da.applyDecision m w (DAState.proposalAccepted q s.da m w)
    else s.da,
    Function.update s.observed m (s.observed m ++ [w])⟩
private def replay (seed : Fin n) (women : Fin n → Equiv.Perm (Fin n))
    (ys : List (Fin n)) : DAStreamState n :=
  ys.foldl (step seed women) (initial n)
@[simp] theorem replay_append_singleton (seed : Fin n) (women : Fin n → Equiv.Perm (Fin n))
    (ys : List (Fin n)) (w : Fin n) :
    replay seed women (ys ++ [w]) = step seed women (replay seed women ys) w := by
  simp [replay]
theorem length_observed_step (seed : Fin n) (women : Fin n → Equiv.Perm (Fin n))
    (s : DAStreamState n) (w i : Fin n) :
    ((step seed women s w).observed i).length =
      (s.observed i).length + if i = s.proposer seed then 1 else 0 := by
  by_cases hi : i = s.proposer seed
  · subst i
    simp [step]
  · simp [step, hi]
theorem length_observed_replay_le (seed : Fin n) (women : Fin n → Equiv.Perm (Fin n))
    (ys : List (Fin n)) (i : Fin n) :
    ((replay seed women ys).observed i).length ≤ ys.length := by
  induction ys using List.reverseRecOn with
  | nil => simp [replay, initial]
  | append_singleton ys w ih =>
    simp only [replay_append_singleton, length_observed_step, List.length_append,
      List.length_singleton]
    split <;> omega
private def query (seed : Fin n) (women : Fin n → Equiv.Perm (Fin n)) (hT : 0 < T)
    (ys : List (Fin n)) : Fin n × Fin T :=
  let s := replay seed women ys
  let m := s.proposer seed
  (m, if h : (s.observed m).length < T then ⟨(s.observed m).length, h⟩ else ⟨0, hT⟩)
theorem query_index_val (seed : Fin n) (women : Fin n → Equiv.Perm (Fin n))
    (hT : 0 < T) {ys : List (Fin n)} (hy : ys.length < T) :
    (query seed women hT ys).2.val =
      ((replay seed women ys).observed ((replay seed women ys).proposer seed)).length := by
  simp [query, (length_observed_replay_le seed women ys _).trans_lt hy]
private theorem observed_take_mono (seed : Fin n) (women : Fin n → Equiv.Perm (Fin n))
    (ys : List (Fin n)) (m : Fin n) :
    Monotone fun k ↦ ((replay seed women (ys.take k)).observed m).length := by
  apply monotone_nat_of_le_succ
  intro k
  by_cases hk : k < ys.length
  · rw [List.take_succ_eq_append_getElem hk, replay_append_singleton, length_observed_step]
    exact Nat.le_add_right _ _
  · rw [List.take_of_length_le (Nat.le_of_not_lt hk),
      List.take_of_length_le (by omega : ys.length ≤ k + 1)]
theorem query_injective (seed : Fin n) (women : Fin n → Equiv.Perm (Fin n)) (hT : 0 < T)
    (ys : Fin T → Fin n) :
    Function.Injective (fun t : Fin T ↦ query seed women hT ((List.ofFn ys).take t.val)) := by
  let l := List.ofFn ys
  let S := fun t : ℕ ↦ replay seed women (l.take t)
  have hlen (t : Fin T) : (l.take t.val).length < T :=
    (List.length_take_le _ _).trans_lt t.isLt
  have hne (i j : Fin T) (hij : i < j) :
      query seed women hT (l.take i.val) ≠ query seed women hT (l.take j.val) := by
    intro h
    let m := (S i.val).proposer seed
    have hm : m = (S j.val).proposer seed := congrArg Prod.fst h
    have hcount : ((S i.val).observed m).length = ((S j.val).observed m).length := by
      have he := congrArg (fun a : Fin n × Fin T ↦ a.2.val) h
      change (query seed women hT (l.take i.val)).2.val =
        (query seed women hT (l.take j.val)).2.val at he
      rw [query_index_val seed women hT (hlen i), query_index_val seed women hT (hlen j)] at he
      exact he.trans (congrArg (fun a ↦ ((S j.val).observed a).length) hm.symm)
    have hi : i.val < l.length := by simp [l]
    have hstep : ((S (i.val + 1)).observed m).length = ((S i.val).observed m).length + 1 := by
      change ((replay seed women (l.take (i.val + 1))).observed m).length = _
      rw [List.take_succ_eq_append_getElem hi, replay_append_singleton, length_observed_step,
        if_pos (show m = (S i.val).proposer seed from rfl)]
    have hle := observed_take_mono seed women l m (show i.val + 1 ≤ j.val from hij)
    change ((S (i.val + 1)).observed m).length ≤ ((S j.val).observed m).length at hle
    omega
  intro i j h
  exact le_antisymm (le_of_not_gt (fun hji ↦ hne j i hji h.symm))
    (le_of_not_gt (fun hij ↦ hne i j hij h))
private noncomputable def streamProfile (raw : Fin n × Fin T → Fin n)
    (fallback women : Fin n → Equiv.Perm (Fin n)) : Profile n :=
  ⟨fun m ↦ streamRank (fun j ↦ raw (m, j)) (fallback m), women⟩
private def ObservationsMatch (s : DAStreamState n) (raw : Fin n × Fin T → Fin n) : Prop :=
  ∀ m, s.observed m = (List.ofFn fun j : Fin T ↦ raw (m, j)).take (s.observed m).length
private def Agrees (s : DAStreamState n) (p : Profile n) : Prop :=
  s.da.Valid p ∧ (s.da.readyMen.Nonempty → ∀ m w,
    w ∈ s.observed m ↔ (p.manRank m w).val < s.da.count m)
theorem initial_agrees (p : Profile n) : (initial n).Agrees p := by
  refine ⟨DAState.initial_valid p, ?_⟩
  simp [initial, DAState.initial]
theorem initial_observationsMatch (raw : Fin n × Fin T → Fin n) :
    (initial n).ObservationsMatch raw := by
  intro m
  simp [initial]
theorem observationsMatch_step (seed : Fin n) (women : Fin n → Equiv.Perm (Fin n))
    {s : DAStreamState n} {raw : Fin n × Fin T → Fin n} (hs : s.ObservationsMatch raw)
    (h : (s.observed (s.proposer seed)).length < T) :
    (s.step seed women (raw (s.proposer seed, ⟨_, h⟩))).ObservationsMatch raw := by
  intro m
  by_cases hm : m = s.proposer seed
  · subst m
    simp only [step, Function.update_self, List.length_append, List.length_singleton]
    rw [List.take_succ_eq_append_getElem (by simpa only [List.length_ofFn] using h),
      List.getElem_ofFn, ← hs]
  · simpa only [step, Function.update_of_ne hm] using hs m
private theorem rank_eq_count_of_lower_iff {rank : Equiv.Perm (Fin n)} {w : Fin n} {k : ℕ}
    (hk : k < n) (h : ∀ v, rank v < rank w ↔ (rank v).val < k) : (rank w).val = k := by
  apply le_antisymm
  · by_contra! hlt
    let v := rank.symm ⟨k, hk⟩
    have hv : rank v = ⟨k, hk⟩ := rank.apply_symm_apply _
    have hvlt : rank v < rank w := by
      rw [hv]
      exact hlt
    have hvk := (h v).mp hvlt
    rw [hv] at hvk
    exact (lt_irrefl k) hvk
  · by_contra! hlt
    exact (lt_irrefl (rank w)) ((h w).mpr hlt)
private theorem fresh_ordinal_rank (seed : Fin n) {s : DAStreamState n}
    {raw : Fin n × Fin T → Fin n} {fallback women : Fin n → Equiv.Perm (Fin n)}
    (hs : s.Agrees (streamProfile raw fallback women)) (hObs : s.ObservationsMatch raw)
    (hready : s.da.readyMen.Nonempty) (hidx : (s.observed (s.proposer seed)).length < T)
    (hfresh : raw (s.proposer seed, ⟨_, hidx⟩) ∉ s.observed (s.proposer seed)) :
    ((streamProfile raw fallback women).manRank (s.proposer seed)
      (raw (s.proposer seed, ⟨_, hidx⟩))).val = s.da.count (s.proposer seed) := by
  let m := s.proposer seed
  let i : Fin T := ⟨(s.observed m).length, hidx⟩
  let row := fun j : Fin T ↦ raw (m, j)
  have hmem (w : Fin n) : w ∈ s.observed m ↔ ∃ j : Fin T, j < i ∧ row j = w := by
    rw [hObs m]
    constructor
    · intro hw
      obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp hw
      have hj' : j < i.val := hj.trans_le (List.length_take_le _ _)
      exact ⟨⟨j, hj'.trans i.isLt⟩, hj', by simpa only [List.getElem_take,
        List.getElem_ofFn] using he⟩
    · rintro ⟨j, hj, rfl⟩
      apply List.mem_iff_getElem.mpr
      have hj' : j.val < ((List.ofFn row).take i.val).length := by
        simp only [List.length_take, List.length_ofFn, lt_min_iff]
        exact ⟨hj, j.isLt⟩
      exact ⟨j.val, hj', by rw [List.getElem_take, List.getElem_ofFn]⟩
  have hf : ∀ j : Fin T, j < i → row j ≠ row i :=
    fun j hj he ↦ hfresh ((hmem _).mpr ⟨j, hj, he⟩)
  have hm : m ∈ s.da.readyMen := by
    simpa only [m, proposer, dif_pos hready] using Finset.min'_mem _ hready
  change (streamRank row (fallback m) (row i)).val = s.da.count m
  apply rank_eq_count_of_lower_iff (DAState.mem_readyMen.mp hm).2
  intro w
  exact (streamRank_lt_fresh_iff row (fallback m) i hf w).trans
    ((hmem w).symm.trans (hs.2 hready m w))
private theorem nextProposal_eq_of_fresh (seed : Fin n) {s : DAStreamState n}
    {p : Profile n} {w : Fin n} (hready : s.da.readyMen.Nonempty)
    (hrank : (p.manRank (s.proposer seed) w).val = s.da.count (s.proposer seed)) :
    s.da.nextProposal p.manRank = some (s.proposer seed, w) := by
  have hw : s.da.proposalTarget p.manRank (s.proposer seed)
      ((DAState.mem_readyMen.mp (by
        simpa only [proposer, dif_pos hready] using Finset.min'_mem _ hready)).2) = w := by
    unfold DAState.proposalTarget
    apply (p.manRank (s.proposer seed)).symm_apply_eq.mpr
    exact Fin.ext hrank.symm
  simpa only [DAState.nextProposal, proposer, dif_pos hready, Option.some.injEq,
    Prod.mk.injEq, true_and] using hw
private theorem fresh_step (seed : Fin n) {s : DAStreamState n}
    {p : Profile n} {w : Fin n} (hready : s.da.readyMen.Nonempty)
    (hf : w ∉ s.observed (s.proposer seed))
    (hrank : (p.manRank (s.proposer seed) w).val = s.da.count (s.proposer seed)) :
    (s.step seed p.womanRank w).da = s.da.advance p := by
  rw [DAState.advance, nextProposal_eq_of_fresh seed hready hrank]
  simp only [step, if_pos (And.intro hready hf)]
  rfl
theorem agrees_step (seed : Fin n) {s : DAStreamState n}
    {raw : Fin n × Fin T → Fin n} {fallback women : Fin n → Equiv.Perm (Fin n)}
    (hs : s.Agrees (streamProfile raw fallback women)) (hObs : s.ObservationsMatch raw)
    (hidx : (s.observed (s.proposer seed)).length < T) :
    let w := raw (s.proposer seed, ⟨_, hidx⟩)
    (s.step seed women w).Agrees (streamProfile raw fallback women) ∧
    (s.step seed women w).da.proposalCount ≤ s.da.proposalCount + 1 := by
  let p := streamProfile raw fallback women
  let m := s.proposer seed
  let w := raw (m, ⟨_, hidx⟩)
  let t := s.step seed women w
  change t.Agrees p ∧ t.da.proposalCount ≤ s.da.proposalCount + 1
  have hobs : t.observed = Function.update s.observed m (s.observed m ++ [w]) := rfl
  by_cases hready : s.da.readyMen.Nonempty
  · by_cases hseen : w ∈ s.observed m
    · have hda : t.da = s.da := by simp [t, step, m, hseen]
      refine ⟨⟨hda ▸ hs.1, ?_⟩, by rw [hda]; exact Nat.le_succ _⟩
      intro _ i v
      rw [hda, hobs]
      by_cases hi : i = m
      · subst i
        rw [Function.update_self, List.mem_append, List.mem_singleton, ← hs.2 hready m v]
        exact ⟨fun hv ↦ hv.elim id (fun h ↦ h ▸ hseen), Or.inl⟩
      · simpa only [Function.update_of_ne hi] using hs.2 hready i v
    · have hrank := fresh_ordinal_rank seed hs hObs hready hidx hseen
      have hda : t.da = s.da.advance p := fresh_step seed hready hseen hrank
      have hnext : s.da.nextProposal p.manRank = some (m, w) :=
        nextProposal_eq_of_fresh seed hready hrank
      refine ⟨⟨hda ▸ hs.1.advance, ?_⟩, ?_⟩
      · intro _ i v
        rw [hda, DAState.advance, hnext, hobs]
        by_cases hi : i = m
        · subst i
          have he : v = w ↔ (p.manRank m v).val = s.da.count m :=
            ⟨fun h ↦ h ▸ hrank, fun h ↦ (p.manRank m).injective
              (Fin.ext (h.trans hrank.symm))⟩
          simp only [DAState.count, DAState.held, DAState.applyDecision, Function.update_self, List.mem_append,
            List.mem_singleton]
          have hprev : v ∈ s.observed m ↔ (p.manRank m v).val < s.da.count m :=
            hs.2 hready m v
          rw [hprev, he]
          dsimp only [DAState.count, DAState.held] at *
          omega
        · simpa only [DAState.count, DAState.held, DAState.applyDecision, Function.update_of_ne hi] using
            hs.2 hready i v
      · rw [hda, DAState.proposalCount_advance_of_some hnext]
  · have hda : t.da = s.da := by simp [t, step, hready]
    exact ⟨⟨hda ▸ hs.1, fun h ↦ (hready (hda ▸ h)).elim⟩,
      by rw [hda]; exact Nat.le_succ _⟩
private theorem step_preserves_observed (seed : Fin n)
    (women : Fin n → Equiv.Perm (Fin n)) (s : DAStreamState n) (v : Fin n)
    {m w : Fin n} (hw : w ∈ s.observed m) : w ∈ (s.step seed women v).observed m := by
  by_cases hm : m = s.proposer seed
  · subst m
    simpa only [step, Function.update_self, List.mem_append] using Or.inl hw
  · simpa only [step, Function.update_of_ne hm] using hw
theorem exists_mem_observed_of_mem (seed : Fin n) (women : Fin n → Equiv.Perm (Fin n))
    {ys : List (Fin n)} {w : Fin n} (hw : w ∈ ys) :
    ∃ m, w ∈ (replay seed women ys).observed m := by
  induction ys using List.reverseRecOn with
  | nil => simp at hw
  | append_singleton ys v ih =>
    rw [replay_append_singleton]
    rcases List.mem_append.mp hw with h | h
    · obtain ⟨m, hm⟩ := ih h
      exact ⟨m, step_preserves_observed seed women _ v hm⟩
    · obtain rfl := List.mem_singleton.mp h
      exact ⟨(replay seed women ys).proposer seed, by simp [step]⟩
theorem complete_of_covers (seed : Fin n) {p : Profile n} {ys : List (Fin n)}
    (hs : (replay seed p.womanRank ys).Agrees p) (hcover : ∀ w : Fin n, w ∈ ys) :
    (replay seed p.womanRank ys).da.Complete := by
  classical
  let s := replay seed p.womanRank ys
  have hnone : s.da.nextProposal p.manRank = none := by
    by_contra hnext
    have hr : s.da.readyMen.Nonempty := by
      by_contra h
      exact hnext (by simp [DAState.nextProposal, h])
    have hheld (w : Fin n) : ∃ a, s.da.held w = some a := by
      obtain ⟨m, hm⟩ := exists_mem_observed_of_mem seed p.womanRank (hcover w)
      obtain ⟨a, ha, _⟩ := hs.1.preferred_holder ((hs.2 hr m w).mp hm)
      exact ⟨a, ha⟩
    let holder (w : Fin n) := Classical.choose (hheld w)
    have hholder (w : Fin n) : s.da.held w = some (holder w) := Classical.choose_spec (hheld w)
    have hi : Function.Injective holder := fun u v huv ↦
      hs.1.held_unique (hholder u) (by rw [huv]; exact hholder v)
    obtain ⟨w, hw⟩ := Finite.surjective_of_injective hi (s.da.readyMen.min' hr)
    exact (DAState.mem_readyMen.mp (Finset.min'_mem _ hr)).1 w (hw ▸ hholder w)
  exact hs.1.complete_of_nextProposal_none hnone
private theorem proposalCount_eq_run_sq_of_complete {p : Profile n} {s : DAState n}
    (hs : s.Valid p) (hc : s.Complete) :
    s.proposalCount = (DAState.run p (n * n)).proposalCount := by
  let μ := s.toMatching hc
  let ν := DAState.matching p
  have hμ := hs.isManOptimal_toMatching hc
  have hν := DAState.isManOptimal_matching p
  have he (m : Fin n) : p.manRank m (μ m) = p.manRank m (ν m) :=
    le_antisymm (hμ.2 ν hν.1 m) (hν.2 μ hμ.1 m)
  unfold DAState.proposalCount
  apply Finset.sum_congr rfl
  intro m _
  rw [← hs.held_last (s.held_toMatching hc m),
    ← (DAState.valid_run p _).held_last ((DAState.run p _).held_toMatching
      (DAState.complete_run_sq p) m)]
  change (p.manRank m (μ m)).val + 1 = (p.manRank m (ν m)).val + 1
  rw [he]
theorem replay_adaptiveTranscript (seed : Fin n) (hT : 0 < T)
    (raw : Fin n × Fin T → Fin n) (fallback women : Fin n → Equiv.Perm (Fin n))
    (t : ℕ) (ht : t ≤ T) :
    let s := replay seed women (adaptiveTranscript (query seed women hT) raw t)
    s.ObservationsMatch raw ∧ s.Agrees (streamProfile raw fallback women) ∧
      s.da.proposalCount ≤ t := by
  induction t with
  | zero =>
    exact ⟨initial_observationsMatch raw, initial_agrees _, by
      simp [adaptiveTranscript, DAState.proposalCount, replay, initial, DAState.initial]⟩
  | succ t ih =>
    let ys := adaptiveTranscript (query seed women hT) raw t
    let s := replay seed women ys
    let m := s.proposer seed
    have hy : ys.length = t := length_adaptiveTranscript _ _ _
    have hi : (s.observed m).length < T :=
      (length_observed_replay_le seed women ys m).trans_lt (hy ▸ Nat.lt_of_succ_le ht)
    have hq : query seed women hT ys = (m, ⟨(s.observed m).length, hi⟩) := by
      change (m, (if h : (s.observed m).length < T then
        (⟨(s.observed m).length, h⟩ : Fin T) else ⟨0, hT⟩)) = _
      rw [dif_pos hi]
    obtain ⟨ho, hv, hp⟩ := ih (Nat.le_of_succ_le ht)
    have hy' : adaptiveTranscript (query seed women hT) raw (t + 1) =
        ys ++ [raw (query seed women hT ys)] := rfl
    dsimp only
    rw [hy', hq, replay_append_singleton]
    obtain ⟨hv', hp'⟩ := agrees_step seed hv ho hi
    exact ⟨observationsMatch_step seed women ho hi, hv', hp'.trans (Nat.succ_le_succ hp)⟩
theorem proposalCount_le_of_adaptiveTranscript_covers (seed : Fin n) (hT : 0 < T)
    (raw : Fin n × Fin T → Fin n) (fallback women : Fin n → Equiv.Perm (Fin n))
    (hcover : ∀ w : Fin n, ∃ t : Fin T, adaptiveTranscriptFn (query seed women hT) raw T t = w) :
    (DAState.run (streamProfile raw fallback women) (n * n)).proposalCount ≤ T := by
  let ys := adaptiveTranscript (query seed women hT) raw T
  let s := replay seed women ys
  let p := streamProfile raw fallback women
  obtain ⟨_, hv, hcount⟩ := replay_adaptiveTranscript seed hT raw fallback women T le_rfl
  change s.Agrees p at hv
  change s.da.proposalCount ≤ T at hcount
  change (DAState.run p (n * n)).proposalCount ≤ T
  have hlist (w : Fin n) : w ∈ ys := by
    change w ∈ adaptiveTranscript (query seed women hT) raw T
    rw [← ofFn_adaptiveTranscriptFn (query seed women hT) raw T]
    exact List.mem_ofFn.mpr (hcover w)
  have hc : s.da.Complete := complete_of_covers (p := p) seed hv hlist
  rw [← proposalCount_eq_run_sq_of_complete hv.1 hc]
  exact hcount
end DAStreamState
end StepA4
end

-- DAProposalCoupon
section
open Filter MeasureTheory Set StableMarriage
open scoped ENNReal Topology StepA4
namespace StepA4
variable {n T : ℕ}
private def missesReceiver (w : Fin n) : Set (Fin T → Fin n) :=
  {y | ∀ t, y t ≠ w}
private def notCovered (n T : ℕ) : Set (Fin T → Fin n) :=
  {y | ¬ ∀ w, ∃ t, y t = w}
private theorem measure_missesReceiver_le [Nonempty (Fin n)] (hn : 0 < n)
    (w : Fin n) :
    (Measure.pi fun _ : Fin T ↦ (PMF.uniformOfFintype (Fin n)).toMeasure)
      (missesReceiver w) ≤ ENNReal.ofReal (Real.exp (-(T : ℝ) / n)) := by
  classical
  let μ := (PMF.uniformOfFintype (Fin n)).toMeasure
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hw : μ ({w} : Set (Fin n)) = (n : ℝ≥0∞)⁻¹ := by
    simp [μ, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton w)]
  have hwc : μ ({w}ᶜ : Set (Fin n)) = 1 - (n : ℝ≥0∞)⁻¹ := by
    rw [measure_compl (measurableSet_singleton w) (measure_ne_top _ _), measure_univ, hw]
  have hbase : 1 - (n : ℝ≥0∞)⁻¹ ≤ ENNReal.ofReal (Real.exp (-(n : ℝ)⁻¹)) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_inv_of_pos hnR, ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_sub _ (inv_nonneg.mpr hnR.le)]
    apply ENNReal.ofReal_le_ofReal
    simpa only [sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-(n : ℝ)⁻¹)
  have he : missesReceiver (T := T) w = Set.pi univ (fun _ ↦ ({w}ᶜ : Set (Fin n))) := by
    ext y
    simp [missesReceiver]
  rw [he, Measure.pi_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  change μ ({w}ᶜ : Set (Fin n)) ^ T ≤ _
  rw [hwc]
  calc
    _ ≤ ENNReal.ofReal (Real.exp (-(n : ℝ)⁻¹)) ^ T := pow_le_pow_left' hbase T
    _ = _ := by
      rw [← ENNReal.ofReal_pow (Real.exp_nonneg _) _, ← Real.exp_nat_mul]
      congr 2
      rw [div_eq_mul_inv, mul_neg, neg_mul]
private theorem measure_notCovered_le [Nonempty (Fin n)] (hn : 0 < n) :
    (Measure.pi fun _ : Fin T ↦ (PMF.uniformOfFintype (Fin n)).toMeasure)
      (notCovered n T) ≤ ENNReal.ofReal ((n : ℝ) * Real.exp (-(T : ℝ) / n)) := by
  classical
  let μ := Measure.pi fun _ : Fin T ↦ (PMF.uniformOfFintype (Fin n)).toMeasure
  have he : notCovered n T = ⋃ w : Fin n, missesReceiver w := by
    ext y
    simp [notCovered, missesReceiver]
  rw [he]
  calc
    μ (⋃ w : Fin n, missesReceiver w) ≤ ∑ w : Fin n, μ (missesReceiver w) :=
      measure_iUnion_fintype_le _ _
    _ ≤ ∑ _ : Fin n, ENNReal.ofReal (Real.exp (-(T : ℝ) / n)) :=
      Finset.sum_le_sum fun w _ ↦ measure_missesReceiver_le hn w
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
theorem measure_daProposalCount_gt_le (hn : 0 < n) (hT : 0 < T) :
    (uniformProfile n).toMeasure {p | T < (DAState.run p (n * n)).proposalCount} ≤
      ENNReal.ofReal ((n : ℝ) * Real.exp (-(T : ℝ) / n)) := by
  classical
  let seed : Fin n := ⟨0, hn⟩
  have : Nonempty (Fin n) := ⟨seed⟩
  let rawLaw : Measure (Fin n × Fin T → Fin n) :=
    Measure.pi fun _ ↦ (PMF.uniformOfFintype (Fin n)).toMeasure
  let rankLaw : Measure (Fin n → Equiv.Perm (Fin n)) :=
    Measure.pi fun _ ↦ (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure
  have : IsProbabilityMeasure rankLaw := inferInstanceAs (IsProbabilityMeasure (Measure.pi _))
  let f := fun z : (Fin n × Fin T → Fin n) × (Fin n → Equiv.Perm (Fin n)) ×
      (Fin n → Equiv.Perm (Fin n)) ↦ DAStreamState.streamProfile z.1 z.2.1 z.2.2
  let E : Set (Profile n) := {p | T < (DAState.run p (n * n)).proposalCount}
  have hf : MeasurePreserving f (rawLaw.prod (rankLaw.prod rankLaw))
      (uniformProfile n).toMeasure := measurePreserving_streamProfile
  have hE : MeasurableSet E := MeasurableSet.of_discrete
  change (uniformProfile n).toMeasure E ≤ _
  rw [← hf.map_eq, Measure.map_apply hf.measurable hE,
    Measure.prod_apply_symm (hf.measurable hE)]
  calc
    _ ≤ (∫⁻ _, ENNReal.ofReal ((n : ℝ) * Real.exp (-(T : ℝ) / n))
        ∂(rankLaw.prod rankLaw)) := by
      apply lintegral_mono
      intro z
      let next := DAStreamState.query seed z.2 hT
      let draw := fun raw ↦ adaptiveTranscriptFn next raw T
      have hfiber : (fun raw ↦ (raw, z)) ⁻¹' (f ⁻¹' E) ⊆ draw ⁻¹' notCovered n T := by
        intro raw hbad
        change T < (DAState.run (DAStreamState.streamProfile raw z.1 z.2)
          (n * n)).proposalCount at hbad
        exact fun hc ↦ (Nat.not_lt_of_ge
          (DAStreamState.proposalCount_le_of_adaptiveTranscript_covers
            seed hT raw z.1 z.2 hc)) hbad
      refine (measure_mono hfiber).trans ?_
      rw [← Measure.map_apply (f := draw) Measurable.of_discrete MeasurableSet.of_discrete,
        show Measure.map draw rawLaw = _ from
          map_adaptiveTranscriptFn_eq_pi (PMF.uniformOfFintype (Fin n)).toMeasure next T
            (DAStreamState.query_injective seed z.2 hT)]
      exact measure_notCovered_le hn
    _ = _ := by simp
private noncomputable def daProposalCap (n : ℕ) : ℕ := ⌈(3 : ℝ) * n * Real.log n⌉₊
theorem eventually_daProposalCap_le :
    ∀ᶠ n : ℕ in atTop, (daProposalCap n : ℝ) ≤ 4 * n * Real.log n := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually_ge_atTop 1, eventually_ge_atTop (1 : ℕ)] with n hl hn
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hprod : 1 ≤ (n : ℝ) * Real.log n := by nlinarith
  have hp : 0 ≤ (3 : ℝ) * n * Real.log n := by positivity
  exact (Nat.ceil_lt_add_one hp).le.trans (by linarith)
theorem tendsto_measure_daProposalCount_gt_daProposalCap :
    Tendsto (fun n ↦ (uniformProfile n).toMeasure
      {p | daProposalCap n < (DAState.run p (n * n)).proposalCount}) atTop (𝓝 0) := by
  have hzero : Tendsto (fun n : ℕ ↦ ENNReal.ofReal ((n : ℝ) ^ (-2 : ℝ))) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero, Function.comp_apply] using ENNReal.tendsto_ofReal
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2)).comp
        tendsto_natCast_atTop_atTop)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hzero
    (Eventually.of_forall fun _ ↦ zero_le)
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  have hn' : 0 < n := by omega
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn'
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hc : (3 : ℝ) * n * Real.log n ≤ daProposalCap n := Nat.le_ceil _
  have hT : 0 < daProposalCap n := by
    exact_mod_cast (show 0 < (daProposalCap n : ℝ) from (by positivity : 0 < (3 : ℝ) * n *
      Real.log n).trans_le hc)
  refine (measure_daProposalCount_gt_le hn' hT).trans (ENNReal.ofReal_le_ofReal ?_)
  have he : -(daProposalCap n : ℝ) / n ≤ Real.log n * (-3) := by
    apply (div_le_iff₀ hnR).mpr
    linarith [show Real.log n * (-3) * n = -((3 : ℝ) * n * Real.log n) by ring]
  calc
    _ ≤ (n : ℝ) * Real.exp (Real.log n * (-3)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) hnR.le
    _ = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-3 : ℝ) := by
      rw [Real.rpow_one, Real.rpow_def_of_pos hnR]
    _ = (n : ℝ) ^ (-2 : ℝ) := by
      rw [← Real.rpow_add hnR]
      norm_num
end StepA4
end

-- AdaptiveScoreRectangles
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace StepA4
variable {ι : Type*}
variable [DecidableEq ι]
variable [Fintype ι]
private noncomputable def cachedUniformScoreLaw (u : ℝ) : Measure ℝ :=
  (ENNReal.ofReal u)⁻¹ • volume.restrict (Ioo 0 u)
theorem isProbabilityMeasure_cachedUniformScoreLaw {u : ℝ} (hu : 0 < u) :
    IsProbabilityMeasure (cachedUniformScoreLaw u) := by
  constructor
  rw [cachedUniformScoreLaw, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ,
    Real.volume_Ioo, sub_zero, ENNReal.inv_mul_cancel (by simpa using hu) ENNReal.ofReal_ne_top]
theorem map_cachedUniformScoreLaw_div {v : ℝ} (hv : 0 < v) :
    Measure.map (fun x ↦ x / v) (cachedUniformScoreLaw v) = unitScoreLaw := by
  have hmeas : Measurable (fun x : ℝ ↦ x / v) := measurable_id.div_const v
  have hpre : (fun x : ℝ ↦ x / v) ⁻¹' Ioo (0 : ℝ) 1 = Ioo 0 v := by
    ext x
    simp only [mem_preimage, mem_Ioo, div_pos_iff_of_pos_right hv, div_lt_iff₀ hv, one_mul]
  have hmap : Measure.map (fun x ↦ x / v) volume = ENNReal.ofReal v • volume := by
    simp only [div_eq_mul_inv]
    rw [Real.map_volume_mul_right (inv_ne_zero hv.ne'), inv_inv, abs_of_pos hv]
  rw [cachedUniformScoreLaw, Measure.map_smul _ _ _, ← hpre,
    ← Measure.restrict_map hmeas measurableSet_Ioo, hmap, Measure.restrict_smul, smul_smul,
    ENNReal.inv_mul_cancel (by simpa using hv) ENNReal.ofReal_ne_top, one_smul, unitScoreLaw,
    Measure.restrict_congr_set Ioo_ae_eq_Icc]
omit [DecidableEq ι] in
theorem measurePreserving_normalize_cachedUniformScoreLaw (upper : ι → ℝ)
    (hupper : ∀ i, 0 < upper i) :
    MeasurePreserving (fun (x : ι → ℝ) i ↦ x i / upper i)
      (Measure.pi fun i ↦ cachedUniformScoreLaw (upper i))
      (Measure.pi fun _ : ι ↦ unitScoreLaw) := by
  have hmeas (i : ι) : Measurable (fun x : ℝ ↦ x / upper i) := measurable_id.div_const _
  have (i : ι) : SigmaFinite
      (Measure.map (fun x : ℝ ↦ x / upper i) (cachedUniformScoreLaw (upper i))) := by
    rw [map_cachedUniformScoreLaw_div (hupper i)]
    infer_instance
  refine ⟨measurable_pi_iff.2 (fun i ↦ (hmeas i).comp (measurable_pi_apply i)), ?_⟩
  rw [Measure.pi_map_pi (fun i ↦ (hmeas i).aemeasurable)]
  simp only [map_cachedUniformScoreLaw_div (hupper _)]
end StepA4
end

-- UniformLogScoreMoments
section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace StepA4
private theorem ae_unitScoreLaw_mem_Icc : ∀ᵐ u ∂unitScoreLaw, u ∈ Icc (0 : ℝ) 1 :=
  ae_restrict_mem measurableSet_Icc
private theorem ae_unitScoreLaw_pos : ∀ᵐ u ∂unitScoreLaw, 0 < u := by
  filter_upwards [ae_unitScoreLaw_mem_Icc, unitScoreLaw.ae_ne 0] with u hu hu0
  exact lt_of_le_of_ne hu.1 hu0.symm
private theorem ae_negLog_unitScoreLaw_nonneg :
    0 ≤ᵐ[unitScoreLaw] fun u ↦ -Real.log u := by
  filter_upwards [ae_unitScoreLaw_mem_Icc] with u hu
  exact neg_nonneg.mpr (Real.log_nonpos hu.1 hu.2)
theorem measurePreserving_negLog_unitScoreLaw :
    MeasurePreserving (fun u : ℝ ↦ -Real.log u) unitScoreLaw (expMeasure 1) := by
  have hm : Measurable (fun u : ℝ ↦ -Real.log u) := Real.measurable_log.neg
  refine ⟨hm, Measure.ext_of_Iic _ _ (fun a ↦ ?_)⟩
  rw [Measure.map_apply hm measurableSet_Iic]
  have hCDF : expMeasure 1 (Iic a) =
      ENNReal.ofReal (if 0 ≤ a then 1 - Real.exp (-a) else 0) := by
    change volume.withDensity (exponentialPDF 1) (Iic a) = _
    rw [withDensity_apply _ measurableSet_Iic,
      lintegral_exponentialPDF_eq_antiDeriv (by norm_num), one_mul]
  rw [hCDF]
  by_cases ha : 0 ≤ a
  · have hpre : (fun u : ℝ ↦ -Real.log u) ⁻¹' Iic a =ᵐ[unitScoreLaw]
        ((Iio (Real.exp (-a)))ᶜ : Set ℝ) := by
      filter_upwards [ae_unitScoreLaw_pos] with u hu
      change (-Real.log u ≤ a) = (¬ u < Real.exp (-a))
      have hneg : -Real.log u ≤ a ↔ -a ≤ Real.log u := by
        constructor <;> intro h <;> linarith
      exact propext (hneg.trans ((Real.le_log_iff_exp_le hu).trans not_lt.symm))
    rw [measure_congr hpre, prob_compl_eq_one_sub measurableSet_Iio,
      unitScoreLaw_Iio_of_mem_Icc ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (neg_nonpos.mpr ha)⟩,
      if_pos ha, ENNReal.ofReal_sub _ (Real.exp_pos _).le, ENNReal.ofReal_one]
  · have hpre : (fun u : ℝ ↦ -Real.log u) ⁻¹' Iic a =ᵐ[unitScoreLaw] (∅ : Set ℝ) := by
      filter_upwards [ae_negLog_unitScoreLaw_nonneg] with u hu
      change (-Real.log u ≤ a) = False
      exact eq_false fun h ↦ ha (hu.trans h)
    rw [measure_congr hpre, measure_empty, if_neg ha, ENNReal.ofReal_zero]
private theorem lintegral_expMeasure_one_id :
    (∫⁻ x, ENNReal.ofReal x ∂expMeasure 1) = 1 := by
  have hPDF : Measurable (exponentialPDF 1) :=
    (measurable_exponentialPDFReal 1).ennreal_ofReal
  rw [show expMeasure (1 : ℝ) = volume.withDensity (exponentialPDF 1) from rfl,
    lintegral_withDensity_eq_lintegral_mul volume hPDF ENNReal.measurable_ofReal]
  have h (x : ℝ) : exponentialPDF 1 x * ENNReal.ofReal x = gammaPDF 2 1 x := by
    by_cases hx : 0 ≤ x
    · rw [exponentialPDF_of_nonneg hx, gammaPDF_of_nonneg hx, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      norm_num [mul_comm]
    · rw [exponentialPDF_of_neg (lt_of_not_ge hx), gammaPDF_of_neg (lt_of_not_ge hx), zero_mul]
  exact (lintegral_congr h).trans (lintegral_gammaPDF_eq_one (by norm_num) (by norm_num))
private theorem lintegral_negLog_unitScoreLaw :
    (∫⁻ u, ENNReal.ofReal (-Real.log u) ∂unitScoreLaw) = 1 :=
  (measurePreserving_negLog_unitScoreLaw.lintegral_comp ENNReal.measurable_ofReal).trans
    lintegral_expMeasure_one_id
private theorem lintegral_sq_negLog_unitScoreLaw :
    (∫⁻ u, ENNReal.ofReal ((-Real.log u) ^ 2) ∂unitScoreLaw) = 2 :=
  (measurePreserving_negLog_unitScoreLaw.lintegral_comp
    (show Measurable (fun x : ℝ ↦ ENNReal.ofReal (x ^ 2)) by fun_prop)).trans
      lintegral_expMeasure_one_sq
theorem integrable_negLog_unitScoreLaw :
    Integrable (fun u ↦ -Real.log u) unitScoreLaw := by
  refine ⟨Real.measurable_log.neg.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal ae_negLog_unitScoreLaw_nonneg, lintegral_negLog_unitScoreLaw]
  exact ENNReal.one_lt_top
theorem integrable_sq_negLog_unitScoreLaw :
    Integrable (fun u ↦ (-Real.log u) ^ 2) unitScoreLaw := by
  refine ⟨(Real.measurable_log.neg.pow_const 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun u ↦ sq_nonneg (-Real.log u)),
    lintegral_sq_negLog_unitScoreLaw]
  exact ENNReal.ofNat_lt_top
theorem memLp_two_negLog_unitScoreLaw :
    MemLp (fun u ↦ -Real.log u) 2 unitScoreLaw :=
  (memLp_two_iff_integrable_sq Real.measurable_log.neg.aestronglyMeasurable).mpr
    integrable_sq_negLog_unitScoreLaw
theorem integral_negLog_unitScoreLaw :
    (∫ u, -Real.log u ∂unitScoreLaw) = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae ae_negLog_unitScoreLaw_nonneg
    integrable_negLog_unitScoreLaw.aestronglyMeasurable, lintegral_negLog_unitScoreLaw,
    ENNReal.toReal_one]
theorem integral_sq_negLog_unitScoreLaw :
    (∫ u, (-Real.log u) ^ 2 ∂unitScoreLaw) = 2 := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun u ↦ sq_nonneg (-Real.log u))
    integrable_sq_negLog_unitScoreLaw.aestronglyMeasurable, lintegral_sq_negLog_unitScoreLaw]
  norm_num
theorem memLp_two_centeredNegLog_unitScoreLaw :
    MemLp (fun u ↦ -Real.log u - 1) 2 unitScoreLaw :=
  memLp_two_negLog_unitScoreLaw.sub (memLp_const 1)
theorem integral_centeredNegLog_unitScoreLaw :
    (∫ u, -Real.log u - 1 ∂unitScoreLaw) = 0 := by
  rw [integral_sub integrable_negLog_unitScoreLaw (integrable_const 1),
    integral_negLog_unitScoreLaw, integral_const, probReal_univ, one_smul, sub_self]
theorem integral_sq_centeredNegLog_unitScoreLaw :
    (∫ u, (-Real.log u - 1) ^ 2 ∂unitScoreLaw) = 1 := by
  have hpoly (u : ℝ) : (-Real.log u - 1) ^ 2 =
      (-Real.log u) ^ 2 - 2 * (-Real.log u) + 1 := by ring
  have hmul : Integrable (fun u ↦ 2 * (-Real.log u)) unitScoreLaw :=
    integrable_negLog_unitScoreLaw.const_mul 2
  have hsub : Integrable (fun u ↦ (-Real.log u) ^ 2 - 2 * (-Real.log u)) unitScoreLaw :=
    integrable_sq_negLog_unitScoreLaw.sub hmul
  simp_rw [hpoly]
  rw [integral_add hsub (integrable_const 1), integral_sub integrable_sq_negLog_unitScoreLaw hmul,
    integral_sq_negLog_unitScoreLaw, integral_const_mul, integral_negLog_unitScoreLaw,
    integral_const, probReal_univ, one_smul]
  norm_num
section FiniteProduct
variable {ι : Type*}
theorem sum_negLog_sub_card_eq_sum_centeredNegLog (s : Finset ι) (u : ι → ℝ) :
    (∑ i ∈ s, -Real.log (u i)) - (s.card : ℝ) =
      ∑ i ∈ s, (-Real.log (u i) - 1) := by
  simp [Finset.sum_sub_distrib, nsmul_eq_mul]
variable [Fintype ι]


private theorem memLp_two_centeredNegLog_eval (i : ι) :
    MemLp ((fun (i : ι) (u : ι → ℝ) ↦ -Real.log (u i) - 1) i) 2 (Measure.pi (fun _ : ι ↦ unitScoreLaw)) :=
  memLp_two_centeredNegLog_unitScoreLaw.comp_measurePreserving (measurePreserving_eval _ i)
private theorem integral_centeredNegLog_eval (i : ι) :
    (∫ u, (fun (i : ι) (u : ι → ℝ) ↦ -Real.log (u i) - 1) i u ∂(Measure.pi (fun _ : ι ↦ unitScoreLaw))) = 0 :=
  (integral_comp_eval (μ := fun _ : ι ↦ unitScoreLaw) (i := i)
    memLp_two_centeredNegLog_unitScoreLaw.aestronglyMeasurable).trans
    integral_centeredNegLog_unitScoreLaw
private theorem variance_centeredNegLog_eval (i : ι) :
    variance ((fun (i : ι) (u : ι → ℝ) ↦ -Real.log (u i) - 1) i) (Measure.pi (fun _ : ι ↦ unitScoreLaw)) = 1 := by
  rw [variance_of_integral_eq_zero (memLp_two_centeredNegLog_eval i).aemeasurable
    (integral_centeredNegLog_eval i)]
  exact (integral_comp_eval (μ := fun _ : ι ↦ unitScoreLaw) (i := i)
    (show AEStronglyMeasurable (fun u : ℝ ↦ (-Real.log u - 1) ^ 2)
      unitScoreLaw from by fun_prop)).trans integral_sq_centeredNegLog_unitScoreLaw
theorem memLp_two_sum_centeredNegLog_unitScoreLaw_pi (s : Finset ι) :
    MemLp (fun u ↦ ∑ i ∈ s, (-Real.log (u i) - 1)) 2 (Measure.pi (fun _ : ι ↦ unitScoreLaw)) :=
  memLp_finsetSum s fun i _ ↦ memLp_two_centeredNegLog_eval i
theorem integral_sum_centeredNegLog_unitScoreLaw_pi (s : Finset ι) :
    (∫ u, ∑ i ∈ s, (-Real.log (u i) - 1) ∂(Measure.pi (fun _ : ι ↦ unitScoreLaw))) = 0 := by
  rw [integral_finsetSum s (fun i _ ↦ (memLp_two_centeredNegLog_eval i).integrable (by norm_num))]
  exact Finset.sum_eq_zero fun i _ ↦ integral_centeredNegLog_eval i
theorem integral_sq_sum_centeredNegLog_unitScoreLaw_pi (s : Finset ι) :
    (∫ u, (∑ i ∈ s, (-Real.log (u i) - 1)) ^ 2 ∂(Measure.pi (fun _ : ι ↦ unitScoreLaw))) = (s.card : ℝ) := by
  have hind : iIndepFun (fun (i : ι) (u : ι → ℝ) ↦ -Real.log (u i) - 1) (Measure.pi (fun _ : ι ↦ unitScoreLaw)) :=
    iIndepFun_pi (X := fun _ : ι ↦ fun u : ℝ ↦ -Real.log u - 1) (fun _ ↦ by fun_prop)
  have hvar := IndepFun.variance_sum (s := s) (fun i _ ↦ memLp_two_centeredNegLog_eval i)
    (by intro _ _ _ _ hij; exact hind.indepFun hij)
  simp only [variance_centeredNegLog_eval, Finset.sum_const, nsmul_eq_mul, mul_one] at hvar
  have hsum : (∑ i ∈ s, (fun (i : ι) (u : ι → ℝ) ↦ -Real.log (u i) - 1) i) = fun u ↦ ∑ i ∈ s, (-Real.log (u i) - 1) := by
    funext u
    simp only [Finset.sum_apply]
  rw [hsum, variance_of_integral_eq_zero
    (memLp_two_sum_centeredNegLog_unitScoreLaw_pi s).aemeasurable
    (integral_sum_centeredNegLog_unitScoreLaw_pi s)] at hvar
  exact hvar
end FiniteProduct
end StepA4
end

-- AdaptiveScoreFiberMoments
section
open MeasureTheory Set
open scoped BigOperators ENNReal MeasureTheory
namespace StepA4
section Fiber
variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
theorem measurePreserving_prod_restrict_of_map_fiber (μ : Measure α) [IsFiniteMeasure μ]
    (ν : Measure β) [IsFiniteMeasure ν] (η : Measure γ) [IsProbabilityMeasure η]
    (E : Set (α × β)) (hE : MeasurableSet E) (g : α × β → γ) (hg : Measurable g)
    (hfiber : ∀ a, Measure.map (fun b ↦ g (a, b)) (ν.restrict (Prod.mk a ⁻¹' E)) =
      ν (Prod.mk a ⁻¹' E) • η) :
    MeasurePreserving (fun z ↦ (z.1, g z)) ((μ.prod ν).restrict E)
      ((Measure.map Prod.fst ((μ.prod ν).restrict E)).prod η) := by
  have hmap := measurable_fst.prodMk hg
  refine ⟨hmap, ?_⟩
  symm
  apply Measure.prod_eq
  intro s t hs ht
  rw [Measure.map_apply hmap (hs.prod ht),
    Measure.restrict_apply (hmap (hs.prod ht)),
    Measure.map_apply measurable_fst hs, Measure.restrict_apply (measurable_fst hs),
    Measure.prod_apply ((hmap (hs.prod ht)).inter hE),
    Measure.prod_apply ((measurable_fst hs).inter hE),
    ← lintegral_mul_const' (η t) _ (measure_ne_top η t)]
  apply lintegral_congr
  intro a
  by_cases ha : a ∈ s
  · have hmeas : Measurable (fun b ↦ g (a, b)) := hg.comp measurable_prodMk_left
    have ht' : (Prod.mk a ⁻¹' ((fun z : α × β ↦ (z.1, g z)) ⁻¹' (s ×ˢ t) ∩ E)) =
        (fun b ↦ g (a, b)) ⁻¹' t ∩ (Prod.mk a ⁻¹' E) := by
      ext b
      simp [ha]
    have hs' : (Prod.mk a ⁻¹' (Prod.fst ⁻¹' s ∩ E)) = Prod.mk a ⁻¹' E := by
      ext b
      simp [ha]
    rw [ht', hs', ← Measure.restrict_apply (hmeas ht), ← Measure.map_apply hmeas ht,
      hfiber a, Measure.smul_apply, smul_eq_mul]
  · have ht' : (Prod.mk a ⁻¹' ((fun z : α × β ↦ (z.1, g z)) ⁻¹' (s ×ˢ t) ∩ E)) = ∅ := by
      ext b
      simp [ha]
    have hs' : (Prod.mk a ⁻¹' (Prod.fst ⁻¹' s ∩ E)) = ∅ := by
      ext b
      simp [ha]
    simp [ht', hs']
end Fiber
section Cache
variable {α ι : Type*} [MeasurableSpace α] [Fintype ι]

private def scoreCacheFiberEvent (A : Set α) (upper : α → ι → ℝ) : Set (α × (ι → ℝ)) :=
  {z | z.1 ∈ A ∧ ∀ i, z.2 i ∈ Ioo 0 (upper z.1 i)}
theorem measurableSet_scoreCacheFiberEvent (A : Set α) (hA : MeasurableSet A)
    (upper : α → ι → ℝ) (hu : ∀ i, Measurable (fun a ↦ upper a i)) :
    MeasurableSet (scoreCacheFiberEvent A upper) := by
  have he (i : ι) : Measurable (fun z : α × (ι → ℝ) ↦ z.2 i) :=
    (measurable_pi_apply i).comp measurable_snd
  have heq : scoreCacheFiberEvent A upper = Prod.fst ⁻¹' A ∩ ⋂ i,
      {z : α × (ι → ℝ) | z.2 i ∈ Ioo 0 (upper z.1 i)} := by
    ext z
    simp [scoreCacheFiberEvent]
  rw [heq]
  exact (measurable_fst hA).inter (MeasurableSet.iInter fun i ↦
    (measurableSet_lt measurable_const (he i)).inter
      (measurableSet_lt (he i) ((hu i).comp measurable_fst)))
private theorem unitScoreLaw_restrict_Ioo {u : ℝ} (hu : 0 < u) (hu₁ : u ≤ 1) :
    unitScoreLaw.restrict (Ioo 0 u) = ENNReal.ofReal u • cachedUniformScoreLaw u := by
  have hsub : Ioo (0 : ℝ) u ⊆ Icc 0 1 :=
    fun _ hx ↦ ⟨hx.1.le, hx.2.le.trans hu₁⟩
  rw [unitScoreLaw, Measure.restrict_restrict measurableSet_Ioo,
    inter_eq_left.mpr hsub, cachedUniformScoreLaw, smul_smul,
    ENNReal.mul_inv_cancel (by simpa using hu) ENNReal.ofReal_ne_top, one_smul]
theorem measurePreserving_normalize_scoreCacheFiber (μ : Measure α) [IsFiniteMeasure μ]
    (A : Set α) (hA : MeasurableSet A) (upper : α → ι → ℝ)
    (hu : ∀ i, Measurable (fun a ↦ upper a i))
    (hcut : ∀ a ∈ A, ∀ i, 0 < upper a i ∧ upper a i ≤ 1) :
    MeasurePreserving (fun z : α × (ι → ℝ) ↦ (z.1, fun i ↦ z.2 i / upper z.1 i))
      ((μ.prod (Measure.pi (fun _ : ι ↦ unitScoreLaw))).restrict (scoreCacheFiberEvent A upper))
      ((Measure.map Prod.fst ((μ.prod (Measure.pi (fun _ : ι ↦ unitScoreLaw))).restrict
        (scoreCacheFiberEvent A upper))).prod (Measure.pi (fun _ : ι ↦ unitScoreLaw))) := by
  have hg : Measurable (fun (z : α × (ι → ℝ)) i ↦ z.2 i / upper z.1 i) :=
    measurable_pi_iff.2 fun i ↦
      ((measurable_pi_apply i).comp measurable_snd).div ((hu i).comp measurable_fst)
  apply measurePreserving_prod_restrict_of_map_fiber _ _ _ _
    (measurableSet_scoreCacheFiberEvent A hA upper hu) _ hg
  intro a
  by_cases ha : a ∈ A
  · have hbox : Prod.mk a ⁻¹' scoreCacheFiberEvent A upper =
        univ.pi (fun i ↦ Ioo 0 (upper a i)) := by
      ext z
      simp [scoreCacheFiberEvent, ha]
    have hpos (i : ι) := (hcut a ha i).1
    have hscale (i : ι) : unitScoreLaw (Ioo 0 (upper a i)) = ENNReal.ofReal (upper a i) := by
      rw [← Measure.restrict_apply_univ, unitScoreLaw_restrict_Ioo (hpos i) (hcut a ha i).2,
        Measure.smul_apply, smul_eq_mul]
      have := isProbabilityMeasure_cachedUniformScoreLaw (hpos i)
      simp
    rw [hbox, Measure.restrict_pi_pi, Measure.pi_pi]
    simp_rw [unitScoreLaw_restrict_Ioo (hpos _) (hcut a ha _).2, hscale]
    have (i : ι) := isProbabilityMeasure_cachedUniformScoreLaw (hpos i)
    have hnormalize := measurePreserving_normalize_cachedUniformScoreLaw (upper a) hpos
    rw [pi_smul_coordinates _ _ (fun _ ↦ ENNReal.ofReal_ne_top),
      Measure.map_smul _ _ _, hnormalize.map_eq]
  · have hempty : Prod.mk a ⁻¹' scoreCacheFiberEvent A upper = ∅ := by
      ext z
      simp [scoreCacheFiberEvent, ha]
    simp [hempty]
private noncomputable def centeredCacheLogIncrement (upper : α → ι → ℝ)
    (z : α × (ι → ℝ)) : ℝ :=
  ∑ i, (-Real.log (z.2 i / upper z.1 i) - 1)
set_option maxHeartbeats 450000 in
theorem scoreCacheFiber_logMoments (μ : Measure α) [IsFiniteMeasure μ]
    (A : Set α) (hA : MeasurableSet A) (upper : α → ι → ℝ)
    (hu : ∀ i, Measurable (fun a ↦ upper a i))
    (hcut : ∀ a ∈ A, ∀ i, 0 < upper a i ∧ upper a i ≤ 1) :
    let E := scoreCacheFiberEvent A upper
    let L := centeredCacheLogIncrement upper
    MemLp L 2 ((μ.prod (Measure.pi (fun _ : ι ↦ unitScoreLaw))).restrict E) ∧
      (∫ z in E, L z ∂(μ.prod (Measure.pi (fun _ : ι ↦ unitScoreLaw)))) = 0 ∧
      (∫ z in E, (L z) ^ 2 ∂(μ.prod (Measure.pi (fun _ : ι ↦ unitScoreLaw)))) =
        (Fintype.card ι : ℝ) * (μ.prod (Measure.pi (fun _ : ι ↦ unitScoreLaw))).real E := by
  let E := scoreCacheFiberEvent A upper
  let ν := (μ.prod (Measure.pi (fun _ : ι ↦ unitScoreLaw))).restrict E
  let ρ := Measure.map Prod.fst ν
  let T (z : α × (ι → ℝ)) := (z.1, fun i ↦ z.2 i / upper z.1 i)
  let L₀ (z : ι → ℝ) := ∑ i, (-Real.log (z i) - 1)
  have hT : MeasurePreserving T ν (ρ.prod (Measure.pi (fun _ : ι ↦ unitScoreLaw))) :=
    measurePreserving_normalize_scoreCacheFiber μ A hA upper hu hcut
  have hL₀ : MemLp L₀ 2 (Measure.pi (fun _ : ι ↦ unitScoreLaw)) :=
    memLp_two_sum_centeredNegLog_unitScoreLaw_pi Finset.univ
  have h₁ : (∫ z, L₀ z ∂(Measure.pi (fun _ : ι ↦ unitScoreLaw))) = 0 :=
    integral_sum_centeredNegLog_unitScoreLaw_pi Finset.univ
  have h₂ : (∫ z, (L₀ z) ^ 2 ∂(Measure.pi (fun _ : ι ↦ unitScoreLaw))) = (Fintype.card ι : ℝ) := by
    simpa only [Finset.card_univ] using integral_sq_sum_centeredNegLog_unitScoreLaw_pi
      (Finset.univ : Finset ι)
  have hρ : ρ.real univ = (μ.prod (Measure.pi (fun _ : ι ↦ unitScoreLaw))).real E := by
    simp [ρ, ν, measureReal_def, Measure.map_apply measurable_fst]
  have hL : MemLp (fun z : α × (ι → ℝ) ↦ L₀ z.2) 2 (ρ.prod (Measure.pi (fun _ : ι ↦ unitScoreLaw))) :=
    hL₀.comp_snd ρ
  have hint (f : (ι → ℝ) → ℝ) (hf : Integrable f (Measure.pi (fun _ : ι ↦ unitScoreLaw))) :
      (∫ z, f (T z).2 ∂ν) = ρ.real univ * (∫ z, f z ∂(Measure.pi (fun _ : ι ↦ unitScoreLaw))) := by
    have hprod := hf.comp_snd ρ
    have hmap : (∫ z, f z.2 ∂Measure.map T ν) = (∫ z, f (T z).2 ∂ν) :=
      integral_map hT.measurable.aemeasurable (hT.map_eq ▸ hprod.aestronglyMeasurable)
    rw [← hmap, hT.map_eq, integral_prod _ hprod]
    change (∫ _ : α, ∫ y, f y ∂(Measure.pi (fun _ : ι ↦ unitScoreLaw)) ∂ρ) = _
    rw [integral_const, smul_eq_mul]
  change MemLp (centeredCacheLogIncrement upper) 2 ν ∧
    (∫ z, centeredCacheLogIncrement upper z ∂ν) = 0 ∧
    (∫ z, (centeredCacheLogIncrement upper z) ^ 2 ∂ν) =
      (Fintype.card ι : ℝ) * (μ.prod (Measure.pi (fun _ : ι ↦ unitScoreLaw))).real E
  have hLT := hL.comp_measurePreserving hT
  refine ⟨hLT, ?_, ?_⟩
  · change (∫ z, L₀ (T z).2 ∂ν) = 0
    rw [hint _ (hL₀.integrable (by norm_num)), h₁, mul_zero]
  · change (∫ z, (L₀ (T z).2) ^ 2 ∂ν) = _
    rw [hint _ hL₀.integrable_sq, h₂, hρ, mul_comm]
theorem scoreCacheFiber_condExp_logMoments (μ : Measure α) [IsFiniteMeasure μ]
    (A : Set α) (hA : MeasurableSet A) (upper : α → ι → ℝ)
    (hu : ∀ i, Measurable (fun a ↦ upper a i))
    (hcut : ∀ a ∈ A, ∀ i, 0 < upper a i ∧ upper a i ≤ 1) :
    let ν := (μ.prod (Measure.pi (fun _ : ι ↦ unitScoreLaw))).restrict (scoreCacheFiberEvent A upper)
    let L := centeredCacheLogIncrement upper
    let m := MeasurableSpace.comap (Prod.fst : α × (ι → ℝ) → α) ‹MeasurableSpace α›
    ν[L | m] =ᵐ[ν] (fun _ ↦ 0) ∧
      ν[(fun z ↦ (L z) ^ 2) | m] =ᵐ[ν] (fun _ ↦ (Fintype.card ι : ℝ)) := by
  let ν := (μ.prod (Measure.pi (fun _ : ι ↦ unitScoreLaw))).restrict (scoreCacheFiberEvent A upper)
  let L := centeredCacheLogIncrement upper
  let m := MeasurableSpace.comap (Prod.fst : α × (ι → ℝ) → α) ‹MeasurableSpace α›
  have hm : m ≤ MeasurableSpace.prod ‹MeasurableSpace α› (inferInstance :
      MeasurableSpace (ι → ℝ)) := measurable_fst.comap_le
  have hl : MemLp L 2 ν := (scoreCacheFiber_logMoments μ A hA upper hu hcut).1
  have hrefine (B : Set α) (hB : MeasurableSet B) :
      ν.restrict (Prod.fst ⁻¹' B) =
        (μ.prod (Measure.pi (fun _ : ι ↦ unitScoreLaw))).restrict (scoreCacheFiberEvent (B ∩ A) upper) := by
    dsimp only [ν]
    rw [Measure.restrict_restrict (measurable_fst hB)]
    congr 1
    ext z
    simp only [scoreCacheFiberEvent, mem_inter_iff, mem_preimage, mem_ofPred_eq, and_assoc]
  have hmass (B : Set α) (hB : MeasurableSet B) :
      ν.real (Prod.fst ⁻¹' B) = (μ.prod (Measure.pi (fun _ : ι ↦ unitScoreLaw))).real (scoreCacheFiberEvent (B ∩ A) upper) := by
    rw [measureReal_def, measureReal_def,
      ← Measure.restrict_apply_univ (μ := ν) (Prod.fst ⁻¹' B), hrefine B hB,
      Measure.restrict_apply_univ]
  change ν[L | m] =ᵐ[ν] (fun _ ↦ 0) ∧
    ν[(fun z ↦ (L z) ^ 2) | m] =ᵐ[ν] (fun _ ↦ (Fintype.card ι : ℝ))
  constructor
  · symm
    refine ae_eq_condExp_of_forall_setIntegral_eq hm (hl.integrable (by norm_num))
      (fun _ _ _ ↦ (integrable_const _).integrableOn) ?_
      stronglyMeasurable_const.aestronglyMeasurable
    rintro s ⟨B, hB, rfl⟩ _
    rw [integral_zero, hrefine B hB]
    exact (scoreCacheFiber_logMoments μ (B ∩ A) (hB.inter hA) upper hu
      (fun a ha ↦ hcut a ha.2)).2.1.symm
  · symm
    refine ae_eq_condExp_of_forall_setIntegral_eq hm hl.integrable_sq
      (fun _ _ _ ↦ (integrable_const _).integrableOn) ?_
      stronglyMeasurable_const.aestronglyMeasurable
    rintro s ⟨B, hB, rfl⟩ _
    rw [setIntegral_const, smul_eq_mul, hmass B hB, mul_comm]
    change _ = ∫ z, (L z) ^ 2 ∂ν.restrict (Prod.fst ⁻¹' B)
    rw [hrefine B hB]
    exact (scoreCacheFiber_logMoments μ (B ∩ A) (hB.inter hA) upper hu
      (fun a ha ↦ hcut a ha.2)).2.2.symm
end Cache
end StepA4
end

-- AdaptiveScoreFiberAssembly
section
open MeasureTheory Set
namespace StepA4
variable {α ι : Type*} [MeasurableSpace α] [Fintype ι]

private def scoreBranchBase (E : Set (α × (ι → ℝ))) : Set α :=
  {a | 0 < (Measure.pi (fun _ : ι ↦ unitScoreLaw)) (Prod.mk a ⁻¹' E)}
theorem measurableSet_scoreBranchBase {E : Set (α × (ι → ℝ))} (hE : MeasurableSet E) :
    MeasurableSet (scoreBranchBase E) :=
  measurableSet_lt measurable_const (measurable_measure_prodMk_left hE)
omit [MeasurableSpace α] in
private theorem nonempty_fiber_of_mem_scoreBranchBase {E : Set (α × (ι → ℝ))} {a : α}
    (ha : a ∈ scoreBranchBase E) : (Prod.mk a ⁻¹' E).Nonempty := by
  by_contra! hnone
  have hpos : 0 < (Measure.pi (fun _ : ι ↦ unitScoreLaw)) (Prod.mk a ⁻¹' E) := ha
  rw [hnone, measure_empty] at hpos
  exact lt_irrefl _ hpos
theorem ae_eq_scoreCacheFiberEvent_of_replay (μ : Measure α) [IsFiniteMeasure μ]
    {E G : Set (α × (ι → ℝ))} (hE : MeasurableSet E) (hG : MeasurableSet G)
    (hgood : ∀ᵐ z ∂μ.prod (Measure.pi (fun _ : ι ↦ unitScoreLaw)), z ∈ G)
    (upper : α → ι → ℝ) (hu : ∀ i, Measurable (fun a ↦ upper a i))
    (hreplay : ∀ a u, (a, u) ∈ E → ∀ v, (a, v) ∈ G →
      ((a, v) ∈ E ↔ ∀ i, v i ∈ Ioo 0 (upper a i))) :
    E =ᵐ[μ.prod (Measure.pi (fun _ : ι ↦ unitScoreLaw))] scoreCacheFiberEvent (scoreBranchBase E) upper := by
  have hbox := measurableSet_scoreCacheFiberEvent _ (measurableSet_scoreBranchBase hE) upper hu
  have heq :
      MeasurableSet {z | z ∈ E ↔ z ∈ scoreCacheFiberEvent (scoreBranchBase E) upper} := by
    rw [show {z | z ∈ E ↔ z ∈ scoreCacheFiberEvent (scoreBranchBase E) upper} =
      (E ∩ scoreCacheFiberEvent (scoreBranchBase E) upper) ∪
        (Eᶜ ∩ (scoreCacheFiberEvent (scoreBranchBase E) upper)ᶜ) by
      ext z
      simp only [mem_ofPred_eq, mem_union, mem_inter_iff, mem_compl_iff]
      tauto]
    exact (hE.inter hbox).union (hE.compl.inter hbox.compl)
  have hg := (Measure.ae_prod_iff_ae_ae hG).mp hgood
  apply Filter.Eventually.set_eq
  apply (Measure.ae_prod_iff_ae_ae heq).mpr
  filter_upwards [hg] with a ha
  by_cases hb : a ∈ scoreBranchBase E
  · obtain ⟨u, huE⟩ := nonempty_fiber_of_mem_scoreBranchBase hb
    filter_upwards [ha] with v hv
    simpa only [scoreCacheFiberEvent, mem_ofPred_eq, hb, true_and] using hreplay a u huE v hv
  · have hzero : (Measure.pi (fun _ : ι ↦ unitScoreLaw)) (Prod.mk a ⁻¹' E) = 0 := nonpos_iff_eq_zero.mp (le_of_not_gt hb)
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hzero] with v hv
    simp only [scoreCacheFiberEvent, mem_ofPred_eq, hb, false_and, iff_false]
    exact hv
theorem scoreBranch_condExp_logMoments_of_replay (μ : Measure α) [IsFiniteMeasure μ]
    {E G : Set (α × (ι → ℝ))} (hE : MeasurableSet E) (hG : MeasurableSet G)
    (hgood : ∀ᵐ z ∂μ.prod (Measure.pi (fun _ : ι ↦ unitScoreLaw)), z ∈ G)
    (upper : α → ι → ℝ) (hu : ∀ i, Measurable (fun a ↦ upper a i))
    (hcut : ∀ a v, (a, v) ∈ E → ∀ i, 0 < upper a i ∧ upper a i ≤ 1)
    (hreplay : ∀ a u, (a, u) ∈ E → ∀ v, (a, v) ∈ G →
      ((a, v) ∈ E ↔ ∀ i, v i ∈ Ioo 0 (upper a i))) :
    let ν := (μ.prod (Measure.pi (fun _ : ι ↦ unitScoreLaw))).restrict E
    let L := centeredCacheLogIncrement upper
    let m := MeasurableSpace.comap (Prod.fst : α × (ι → ℝ) → α) ‹MeasurableSpace α›
    MemLp L 2 ν ∧ ν[L | m] =ᵐ[ν] (fun _ ↦ 0) ∧
      ν[(fun z ↦ (L z) ^ 2) | m] =ᵐ[ν] (fun _ ↦ (Fintype.card ι : ℝ)) := by
  have he := ae_eq_scoreCacheFiberEvent_of_replay μ hE hG hgood upper hu hreplay
  have hb : ∀ a ∈ scoreBranchBase E, ∀ i, 0 < upper a i ∧ upper a i ≤ 1 := by
    intro a ha
    obtain ⟨v, hv⟩ := nonempty_fiber_of_mem_scoreBranchBase ha
    exact hcut a v hv
  dsimp only
  rw [Measure.restrict_congr_set he]
  exact ⟨(scoreCacheFiber_logMoments μ _ (measurableSet_scoreBranchBase hE) upper hu hb).1,
    scoreCacheFiber_condExp_logMoments μ _ (measurableSet_scoreBranchBase hE) upper hu hb⟩
end StepA4
end

-- RotationParticipationClock
section
open StableMarriage
open scoped BigOperators
namespace StepA4
private def rotationParticipation {n : ℕ} (rs : List (Equiv.Perm (Fin n))) : ℕ :=
  (rs.map fun σ ↦ σ.support.card).sum
private noncomputable def femaleLogPotential {n : ℕ} (x : ScoreProfile n) (μ : Matching n) : ℝ :=
  ∑ j, -Real.log (femaleSpouseScore x μ j)
private noncomputable def femaleRotationRatio {n : ℕ} (x : ScoreProfile n) (μ : Matching n)
    (ρ : Equiv.Perm (Fin n)) (i : Fin n) : ℝ :=
  femaleSpouseScore x (eliminateRotation μ ρ) (μ i) / femaleSpouseScore x μ (μ i)
theorem femaleSpouseScore_eliminate_eq_of_not_mem_support {n : ℕ} (x : ScoreProfile n)
    (μ : Matching n) (ρ : Equiv.Perm (Fin n)) {i : Fin n} (hi : i ∉ ρ.support) :
    femaleSpouseScore x (eliminateRotation μ ρ) (μ i) = femaleSpouseScore x μ (μ i) := by
  have hfix : ρ i = i := by simpa only [Equiv.Perm.mem_support, not_not] using hi
  have hpartner : eliminateRotation μ ρ i = μ i := by rw [eliminateRotation_apply, hfix]
  unfold femaleSpouseScore
  rw [(Equiv.symm_apply_eq (eliminateRotation μ ρ)).mpr hpartner.symm, μ.symm_apply_apply]
open scoped Classical in
theorem femaleLogPotential_eliminate_sub {n : ℕ} (x : ScoreProfile n) (μ : Matching n)
    (ρ : Equiv.Perm (Fin n)) (hx : ∀ j i, 0 < x (.inr j) i) :
    femaleLogPotential x (eliminateRotation μ ρ) - femaleLogPotential x μ =
      ∑ i ∈ ρ.support, -Real.log (femaleRotationRatio x μ ρ i) := by
  let ν := eliminateRotation μ ρ
  have he (M : Matching n) : femaleLogPotential x M =
      ∑ i, -Real.log (femaleSpouseScore x M (μ i)) :=
    (Equiv.sum_comp μ fun j ↦ -Real.log (femaleSpouseScore x M j)).symm
  rw [he ν, he μ, ← Finset.sum_sub_distrib]
  have hsupport : Finset.univ.filter (· ∈ ρ.support) = ρ.support := by ext; simp
  rw [← hsupport, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ ρ.support
  · rw [if_pos hi]
    unfold femaleRotationRatio
    have ho : 0 < femaleSpouseScore x μ (μ i) := hx _ _
    have hn : 0 < femaleSpouseScore x ν (μ i) := hx _ _
    rw [Real.log_div hn.ne' ho.ne']
    ring
  · rw [if_neg hi, femaleSpouseScore_eliminate_eq_of_not_mem_support x μ ρ hi, sub_self]
private def rankPotential {n : ℕ} (p : Profile n) (μ : Matching n) : ℕ :=
  ∑ m, (p.manRank m (μ m)).val
open scoped Classical in
private theorem rankPotential_add_support_le {n : ℕ} {p : Profile n} {μ : Matching n}
    {ρ : Equiv.Perm (Fin n)} (hρ : IsExposedRotation p μ ρ) :
    rankPotential p μ + ρ.support.card ≤ rankPotential p (eliminateRotation μ ρ) := by
  have hc : ρ.support.card = ∑ i : Fin n, if i ∈ ρ.support then 1 else 0 := by
    have hsupport : Finset.univ.filter (· ∈ ρ.support) = ρ.support := by ext; simp
    rw [← Finset.sum_filter, hsupport]
    simp
  rw [hc, rankPotential, rankPotential, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i ∈ ρ.support
  · rw [if_pos hi]
    exact hρ.manRank_lt_eliminate_of_moved (Equiv.Perm.mem_support.mp hi)
  · have he : ρ i = i := by simpa only [Equiv.Perm.mem_support, not_not] using hi
    simp only [if_neg hi, add_zero, eliminateRotation_apply, he, le_refl]
private theorem RotationSequence.participation_add_rankPotential_le {n : ℕ} {p : Profile n}
    {μ ν : Matching n} {rs : List (Equiv.Perm (Fin n))} (h : RotationSequence p μ rs ν) :
    rankPotential p μ + rotationParticipation rs ≤ rankPotential p ν := by
  induction h with
  | nil => simp [rotationParticipation]
  | @cons μ ν ρ rs _ hρ _ ih =>
    simp only [rotationParticipation, List.map_cons, List.sum_cons] at ih ⊢
    rw [← add_assoc]
    exact (Nat.add_le_add_right (rankPotential_add_support_le hρ) _).trans ih
theorem RotationSequence.participation_le {n : ℕ} {p : Profile n} {μ ν : Matching n}
    {rs : List (Equiv.Perm (Fin n))} (h : RotationSequence p μ rs ν) :
    rotationParticipation rs ≤ n * (n - 1) := by
  refine (Nat.le_add_left _ _).trans (h.participation_add_rankPotential_le.trans ?_)
  calc
    rankPotential p ν ≤ ∑ _m : Fin n, (n - 1) :=
      Finset.sum_le_sum fun m _ ↦ Nat.le_pred_of_lt (p.manRank m (ν m)).isLt
    _ = _ := by simp
theorem femaleSpouseScore_eliminate_le {n : ℕ} (x : ScoreProfile n) {μ : Matching n}
    {ρ : Equiv.Perm (Fin n)} (hρ : IsExposedRotation (profileOfScores x) μ ρ)
    (ht : ∀ j, Function.Injective (x (.inr j))) (j : Fin n) :
    femaleSpouseScore x (eliminateRotation μ ρ) j ≤ femaleSpouseScore x μ j := by
  apply le_of_not_gt
  intro h
  exact (not_lt_of_ge (hρ.womanRank_eliminate_le j))
    ((rankPermutation_lt_iff (ht j) _ _).mpr h)
end StepA4
end

-- RotationClockCells
section
open StableMarriage
namespace StepA4
variable {n : ℕ} {p : Profile n} {μ ν : Matching n}
variable {ρ : Equiv.Perm (Fin n)}
private def rotationClockCell (μ : Matching n) (ρ : Equiv.Perm (Fin n)) (m : Fin n) :
    (Fin n ⊕ Fin n) × Fin n :=
  (.inr (eliminateRotation μ ρ m), m)
theorem rotationClockCell_injective (μ : Matching n) (ρ : Equiv.Perm (Fin n)) :
    Function.Injective (rotationClockCell μ ρ) :=
  fun _ _ h ↦ congrArg Prod.snd h
theorem femaleSpouseScore_eliminate_apply (x : ScoreProfile n) (μ : Matching n)
    (ρ : Equiv.Perm (Fin n)) (m : Fin n) :
    femaleSpouseScore x (eliminateRotation μ ρ) (eliminateRotation μ ρ m) =
      x (rotationClockCell μ ρ m).1 (rotationClockCell μ ρ m).2 := by
  simp only [femaleSpouseScore, Equiv.symm_apply_apply, rotationClockCell]
theorem IsExposedRotation.new_partner_ne_of_rank_le (hρ : IsExposedRotation p μ ρ)
    {m w : Fin n} (hm : m ∈ ρ.support)
    (hw : p.manRank m w ≤ p.manRank m (μ m)) :
    eliminateRotation μ ρ m ≠ w :=
  fun h ↦ (not_lt_of_ge hw)
    (h ▸ hρ.manRank_lt_eliminate_of_moved (Equiv.Perm.mem_support.mp hm))
theorem RotationSequence.rotationClockCell_ne_old_spouse {rs : List (Equiv.Perm (Fin n))}
    (h : RotationSequence p ν rs μ) (hρ : IsExposedRotation p μ ρ)
    {m : Fin n} (hm : m ∈ ρ.support) (a : Fin n) :
    rotationClockCell μ ρ m ≠ (.inr (ν a), a) := by
  intro heq
  have ha : m = a := congrArg Prod.snd heq
  subst a
  exact hρ.new_partner_ne_of_rank_le hm (h.menWeaklyPrefer m)
    (Sum.inr.inj (congrArg Prod.fst heq))
theorem RotationSequence.femaleSpouseScore_end_le_start
    {x : ScoreProfile n} {rs : List (Equiv.Perm (Fin n))}
    (h : RotationSequence (profileOfScores x) ν rs μ)
    (ht : ∀ j, Function.Injective (x (.inr j))) (j : Fin n) :
    femaleSpouseScore x μ j ≤ femaleSpouseScore x ν j := by
  induction h with
  | nil => exact le_rfl
  | cons _ hρ _ ih => exact ih.trans (femaleSpouseScore_eliminate_le x hρ ht j)
theorem IsExposedRotation.rotationClockCell_score_lt {x : ScoreProfile n}
    (hρ : IsExposedRotation (profileOfScores x) μ ρ)
    (ht : ∀ j, Function.Injective (x (.inr j))) {m : Fin n} (hm : m ∈ ρ.support) :
    x (rotationClockCell μ ρ m).1 (rotationClockCell μ ρ m).2 <
      femaleSpouseScore x μ (eliminateRotation μ ρ m) := by
  have h := (IsSuccessor.eligible ((IsExposedRotation.successor hρ) m (Equiv.Perm.mem_support.mp hm))).2
  exact (rankPermutation_lt_iff (ht _) _ _).mp h
theorem RotationSequence.rotationClockCell_score_lt_old_threshold
    {x : ScoreProfile n} {rs : List (Equiv.Perm (Fin n))}
    (h : RotationSequence (profileOfScores x) ν rs μ)
    (hρ : IsExposedRotation (profileOfScores x) μ ρ)
    (ht : ∀ j, Function.Injective (x (.inr j))) {m : Fin n} (hm : m ∈ ρ.support) :
    x (rotationClockCell μ ρ m).1 (rotationClockCell μ ρ m).2 <
      femaleSpouseScore x ν (eliminateRotation μ ρ m) :=
  (hρ.rotationClockCell_score_lt ht hm).trans_le
    (h.femaleSpouseScore_end_le_start ht (eliminateRotation μ ρ m))
end StepA4
end

-- RotationSuccessorQueries
section
open StableMarriage
namespace StepA4
private abbrev runSuccessorQuery {α : Type*} (passes : α → Bool) :
    List α → Option α × List (α × Bool) :=
  DAState.lhsOfEq (@AbunLP.runSuccessorQuery_alias) passes
private theorem runSuccessorQuery_nil {α : Type*} (passes : α → Bool) :
    runSuccessorQuery passes [] = (none, []) := AbunLP.runSuccessorQuery_nil passes
private theorem runSuccessorQuery_cons {α : Type*} (passes : α → Bool) (w : α) (ws : List α) :
    runSuccessorQuery passes (w :: ws) =
      (match passes w with
      | true => (some w, [(w, true)])
      | false =>
        let rest := runSuccessorQuery passes ws
        (rest.1, (w, false) :: rest.2)) := AbunLP.runSuccessorQuery_cons passes w ws
theorem runSuccessorQuery_fst {α : Type*} (passes : α → Bool) (candidates : List α) :
    (runSuccessorQuery passes candidates).1 = candidates.find? passes := by
  induction candidates with
  | nil => rfl
  | cons w ws ih =>
    cases h : passes w <;> simp [runSuccessorQuery_nil, runSuccessorQuery_cons, h, ih]
variable {n : ℕ}
private def successorQueryCandidates (rank : Equiv.Perm (Fin n)) (wife : Fin n) : List (Fin n) :=
  ((List.finRange n).filter fun i ↦ decide (rank wife < i)).map rank.symm
theorem mem_successorQueryCandidates {rank : Equiv.Perm (Fin n)} {wife w : Fin n} :
    w ∈ successorQueryCandidates rank wife ↔ rank wife < rank w := by
  simp only [successorQueryCandidates, List.mem_map, List.mem_filter, List.mem_finRange,
    true_and, decide_eq_true_eq, Equiv.symm_apply_eq]
  exact ⟨fun ⟨i, hi, h⟩ ↦ h ▸ hi, fun h ↦ ⟨rank w, h, rfl⟩⟩
theorem successorQueryCandidates_pairwise (rank : Equiv.Perm (Fin n)) (wife : Fin n) :
    (successorQueryCandidates rank wife).Pairwise (fun a b ↦ rank a < rank b) := by
  have hs : (List.finRange n).Pairwise (fun a b : Fin n ↦ a < b) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simpa using hij
  simpa [successorQueryCandidates, List.pairwise_map] using
    hs.filter (fun i ↦ decide (rank wife < i))
private def querySuccessorRow (rank : Equiv.Perm (Fin n)) (wife : Fin n) (passes : Fin n → Bool) :
    Option (Fin n) × List (Fin n × Bool) :=
  runSuccessorQuery passes (successorQueryCandidates rank wife)
variable {p : Profile n} {μ : Matching n} {m w : Fin n}
private theorem isSuccessor_of_querySuccessorRow (passes : Fin n → Bool)
    (hpasses : ∀ v, passes v = true ↔ p.womanRank v m < p.womanRank v (μ.symm v))
    (h : (querySuccessorRow (p.manRank m) (μ m) passes).1 = some w) :
    IsSuccessor p μ m w := by
  rw [querySuccessorRow, runSuccessorQuery_fst] at h
  have hw := List.mem_of_find?_eq_some h
  obtain ⟨hpass, before, after, heq, hfail⟩ := List.find?_eq_some_iff_append.mp h
  refine (IsSuccessor.mk (⟨mem_successorQueryCandidates.mp hw, (hpasses w).mp hpass⟩) (?_))
  intro v hv
  have hs := successorQueryCandidates_pairwise (p.manRank m) (μ m)
  have hmem := mem_successorQueryCandidates.mpr hv.1
  rw [heq, List.mem_append, List.mem_cons] at hmem
  rw [heq, List.pairwise_append, List.pairwise_cons] at hs
  rcases hmem with hbefore | rfl | hafter
  · have hfalse := hfail v hbefore
    simp [(hpasses v).mpr hv.2] at hfalse
  · exact le_rfl
  · exact (hs.2.1.1 v hafter).le
theorem querySuccessorRow_eq_some_iff (passes : Fin n → Bool)
    (hpasses : ∀ v, passes v = true ↔ p.womanRank v m < p.womanRank v (μ.symm v)) :
    (querySuccessorRow (p.manRank m) (μ m) passes).1 = some w ↔ IsSuccessor p μ m w := by
  refine ⟨isSuccessor_of_querySuccessorRow passes hpasses, ?_⟩
  intro hw
  cases h : (querySuccessorRow (p.manRank m) (μ m) passes).1 with
  | none =>
    rw [querySuccessorRow, runSuccessorQuery_fst, List.find?_eq_none] at h
    exact (h w (mem_successorQueryCandidates.mpr (IsSuccessor.eligible hw).1)
      ((hpasses w).mpr (IsSuccessor.eligible hw).2)).elim
  | some v =>
    rw [(isSuccessor_of_querySuccessorRow passes hpasses h).unique hw]
private def queriedSuccessorGraph (menRank : Fin n → Equiv.Perm (Fin n)) (μ : Matching n)
    (passes : Fin n → Fin n → Bool) (m : Fin n) : Option (Fin n) :=
  ((querySuccessorRow (menRank m) (μ m) (passes m)).1).map μ.symm
private noncomputable def chooseQueriedRotation (f : Fin n → Option (Fin n)) :
    Option (Equiv.Perm (Fin n)) := by
  classical
  exact if h : ∃ ρ, RealizesDirectedCycle f ρ then some (Classical.choose h) else none
theorem realizesDirectedCycle_of_chooseQueriedRotation {f : Fin n → Option (Fin n)}
    {ρ : Equiv.Perm (Fin n)} (h : chooseQueriedRotation f = some ρ) :
    RealizesDirectedCycle f ρ := by
  unfold chooseQueriedRotation at h
  split at h
  · rename_i hcycle
    exact (Option.some.inj h) ▸ Classical.choose_spec hcycle
  · cases h
theorem chooseQueriedRotation_eq_none_iff (f : Fin n → Option (Fin n)) :
    chooseQueriedRotation f = none ↔ IsAcyclicSuccessor f := by
  classical
  unfold chooseQueriedRotation IsAcyclicSuccessor
  split <;> simp_all [← not_exists]
theorem queriedSuccessorGraph_eq_some_iff (passes : Fin n → Fin n → Bool)
    (hpasses : ∀ i v, passes i v = true ↔ p.womanRank v i < p.womanRank v (μ.symm v))
    (m j : Fin n) :
    queriedSuccessorGraph p.manRank μ passes m = some j ↔ IsSuccessor p μ m (μ j) := by
  simp only [queriedSuccessorGraph, Option.map_eq_some_iff, Equiv.symm_apply_eq]
  exact ⟨fun ⟨v, hv, h⟩ ↦ h ▸ (querySuccessorRow_eq_some_iff _ (hpasses m)).mp hv,
    fun hs ↦ ⟨μ j, (querySuccessorRow_eq_some_iff _ (hpasses m)).mpr hs, rfl⟩⟩
theorem realizesDirectedCycle_queriedSuccessorGraph_iff (passes : Fin n → Fin n → Bool)
    (hpasses : ∀ i v, passes i v = true ↔ p.womanRank v i < p.womanRank v (μ.symm v))
    (ρ : Equiv.Perm (Fin n)) :
    RealizesDirectedCycle (queriedSuccessorGraph p.manRank μ passes) ρ ↔
      IsExposedRotation p μ ρ :=
  ⟨fun h ↦ (IsExposedRotation.mk (h.1) (fun m hm ↦ (queriedSuccessorGraph_eq_some_iff passes hpasses m _).mp
      (h.2 m (Equiv.Perm.mem_support.mpr hm)))),
    fun h ↦ ⟨(IsExposedRotation.isCycle h), fun m hm ↦ (queriedSuccessorGraph_eq_some_iff passes hpasses m _).mpr
      ((IsExposedRotation.successor h) m (Equiv.Perm.mem_support.mp hm))⟩⟩
private noncomputable def successorScoreOracle (threshold : Fin n → ℝ)
    (score : Fin n → Fin n → ℝ) (m w : Fin n) : Bool :=
  decide (score w m < threshold w)
theorem realizesDirectedCycle_queriedSuccessorGraph_scores_iff (x : ScoreProfile n)
    (hx : ∀ w, Function.Injective (x (.inr w))) (μ : Matching n)
    (ρ : Equiv.Perm (Fin n)) :
    RealizesDirectedCycle (queriedSuccessorGraph (profileOfScores x).manRank μ
      (successorScoreOracle (fun w ↦ x (.inr w) (μ.symm w)) (fun w ↦ x (.inr w)))) ρ ↔
      IsExposedRotation (profileOfScores x) μ ρ :=
  realizesDirectedCycle_queriedSuccessorGraph_iff _ (fun m w ↦ by
    simp only [successorScoreOracle, decide_eq_true_eq, profileOfScores,
      rankPermutation_lt_iff (hx w)]) ρ
theorem isWomanOptimal_of_no_exposedRotation (hμ : IsStable p μ)
    (hnone : ∀ ρ, ¬ IsExposedRotation p μ ρ) : IsManOptimal (swapProfile p) μ.symm := by
  refine ⟨isStable_swapProfile_iff.mpr hμ, ?_⟩
  intro η hη w
  let ν := η.symm
  have hν : IsStable p ν :=
    isStable_swapProfile_iff.mp (by simpa only [ν, Equiv.symm_symm] using hη)
  obtain ⟨ξ, hξ, hmax⟩ := exists_stable_manRank_max hμ hν
  have hμξ : MenWeaklyPrefer p μ ξ := fun i ↦ (le_max_left _ _).trans_eq (hmax i).symm
  have heq : ξ = μ := by
    by_contra h
    obtain ⟨ρ, hρ, -⟩ := exists_exposedRotation_towards_target hμ hξ hμξ (Ne.symm h)
    exact hnone ρ hρ
  let m := η w
  have hmν : ν m = w := η.symm_apply_apply w
  change p.womanRank w (μ.symm w) ≤ p.womanRank w m
  by_contra hw
  have hwoman := lt_of_not_ge hw
  have hm : μ m ≠ w := fun h ↦ (ne_of_lt hwoman)
    (congrArg (p.womanRank w) ((Equiv.symm_apply_eq μ).mpr h.symm).symm)
  have hman : p.manRank m w ≤ p.manRank m (μ m) := by
    rw [← hmν, ← heq, hmax]
    exact le_max_right _ _
  exact hμ m w ⟨hm, lt_of_le_of_ne hman ((p.manRank m).injective.ne hm.symm), hwoman⟩
theorem isWomanOptimal_of_acyclic_queriedSuccessorGraph_scores (x : ScoreProfile n)
    (hx : ∀ w, Function.Injective (x (.inr w))) (μ : Matching n)
    (hμ : IsStable (profileOfScores x) μ)
    (hgraph : IsAcyclicSuccessor (queriedSuccessorGraph (profileOfScores x).manRank μ
      (successorScoreOracle (fun w ↦ x (.inr w) (μ.symm w)) (fun w ↦ x (.inr w))))) :
    IsManOptimal (swapProfile (profileOfScores x)) μ.symm :=
  isWomanOptimal_of_no_exposedRotation hμ fun ρ hρ ↦ hgraph ρ
    ((realizesDirectedCycle_queriedSuccessorGraph_scores_iff x hx μ ρ).mpr hρ)
end StepA4
end

-- ScoreRotationWalk
section
open StableMarriage
namespace StepA4
variable {n : ℕ}
private noncomputable def scoreRotationGraph (x : ScoreProfile n) (μ : Matching n) :
    Fin n → Option (Fin n) :=
  queriedSuccessorGraph (profileOfScores x).manRank μ
    (successorScoreOracle (femaleSpouseScore x μ) (fun w ↦ x (.inr w)))
private noncomputable abbrev scoreRotationWalk (x : ScoreProfile n) :
    ℕ → Matching n → List (Equiv.Perm (Fin n)) × Matching n :=
  DAState.lhsOfEq (@AbunLP.scoreRotationWalk_alias) x
private theorem scoreRotationWalk_zero (x : ScoreProfile n) (μ : Matching n) :
    scoreRotationWalk x 0 μ = ([], μ) := AbunLP.scoreRotationWalk_zero x μ
private theorem scoreRotationWalk_succ (x : ScoreProfile n) (k : ℕ) (μ : Matching n) :
    scoreRotationWalk x (k + 1) μ =
      (match chooseQueriedRotation (scoreRotationGraph x μ) with
      | none => ([], μ)
      | some ρ =>
        let out := scoreRotationWalk x k (eliminateRotation μ ρ)
        (ρ :: out.1, out.2)) := AbunLP.scoreRotationWalk_succ x k μ
theorem scoreRotationWalk_legal (x : ScoreProfile n)
    (ht : ∀ j, Function.Injective (x (.inr j))) (k : ℕ)
    {μ : Matching n} (hμ : IsStable (profileOfScores x) μ) :
    RotationSequence (profileOfScores x) μ (scoreRotationWalk x k μ).1
      (scoreRotationWalk x k μ).2 := by
  induction k generalizing μ with
  | zero => exact .nil hμ
  | succ k ih =>
    rw [scoreRotationWalk_succ]
    split
    · exact .nil hμ
    · rename_i ρ hselect
      have hρ : IsExposedRotation (profileOfScores x) μ ρ :=
        (realizesDirectedCycle_queriedSuccessorGraph_scores_iff x ht μ ρ).mp
          (realizesDirectedCycle_of_chooseQueriedRotation hselect)
      exact .cons hμ hρ (ih (hρ.isStable_eliminate hμ))
private theorem scoreRotationWalk_length_of_endpoint_cycle (x : ScoreProfile n)
    (k : ℕ) (μ : Matching n)
    (h : chooseQueriedRotation (scoreRotationGraph x (scoreRotationWalk x k μ).2) ≠ none) :
    (scoreRotationWalk x k μ).1.length = k := by
  induction k generalizing μ with
  | zero => rfl
  | succ k ih =>
    cases hc : chooseQueriedRotation (scoreRotationGraph x μ) with
    | none =>
      rw [scoreRotationWalk_succ, hc] at h
      exact (h hc).elim
    | some ρ =>
      rw [scoreRotationWalk_succ, hc] at h ⊢
      exact congrArg Nat.succ (ih _ h)
theorem RotationSequence.length_le_participation {p : Profile n} {μ ν : Matching n}
    {rs : List (Equiv.Perm (Fin n))} (h : RotationSequence p μ rs ν) :
    rs.length ≤ rotationParticipation rs := by
  induction h with
  | nil => simp [rotationParticipation]
  | @cons μ ν ρ rs _ hρ _ ih =>
    obtain ⟨m, hm, _⟩ := (IsExposedRotation.isCycle hρ)
    have hpos := Finset.card_pos.mpr ⟨m, Equiv.Perm.mem_support.mpr hm⟩
    simp only [List.length_cons, rotationParticipation, List.map_cons, List.sum_cons] at ih ⊢
    omega
theorem scoreRotationWalk_horizon_acyclic (x : ScoreProfile n)
    (ht : ∀ j, Function.Injective (x (.inr j))) {μ : Matching n}
    (hμ : IsStable (profileOfScores x) μ) :
    IsAcyclicSuccessor (scoreRotationGraph x (scoreRotationWalk x (n * (n - 1)) μ).2) := by
  let N := n * (n - 1)
  let out := scoreRotationWalk x N μ
  have hp := scoreRotationWalk_legal x ht N hμ
  apply (chooseQueriedRotation_eq_none_iff _).mp
  change chooseQueriedRotation (scoreRotationGraph x out.2) = none
  cases hchoose : chooseQueriedRotation (scoreRotationGraph x out.2) with
  | none => rfl
  | some ρ =>
    have hρ : IsExposedRotation (profileOfScores x) out.2 ρ :=
      (realizesDirectedCycle_queriedSuccessorGraph_scores_iff x ht _ ρ).mp
        (realizesDirectedCycle_of_chooseQueriedRotation hchoose)
    have hstep : RotationSequence (profileOfScores x) out.2 [ρ] (eliminateRotation out.2 ρ) :=
      .cons hp.isStable_end hρ (.nil (hρ.isStable_eliminate hp.isStable_end))
    have hext := hp.append hstep
    have hl := scoreRotationWalk_length_of_endpoint_cycle x N μ (by
      change chooseQueriedRotation (scoreRotationGraph x out.2) ≠ none
      rw [hchoose]
      exact Option.some_ne_none _)
    have hbad := hext.length_le_participation.trans hext.participation_le
    change (out.1 ++ [ρ]).length ≤ N at hbad
    change out.1.length = N at hl
    simp only [List.length_append, List.length_singleton, hl] at hbad
    omega
theorem scoreRotationWalk_da_optimal_endpoints (x : ScoreProfile n)
    (ht : ∀ j, Function.Injective (x (.inr j))) :
    let p := profileOfScores x
    let μ := DAState.matching p
    let out := scoreRotationWalk x (n * (n - 1)) μ
    IsManOptimal p μ ∧ RotationSequence p μ out.1 out.2 ∧
      IsManOptimal (swapProfile p) out.2.symm := by
  dsimp only
  have hs := DAState.isManOptimal_matching (profileOfScores x)
  have hp := scoreRotationWalk_legal x ht (n * (n - 1)) hs.1
  exact ⟨hs, hp, isWomanOptimal_of_acyclic_queriedSuccessorGraph_scores x ht _
    hp.isStable_end (scoreRotationWalk_horizon_acyclic x ht hs.1)⟩
private def IsRotationClockCell (μ : Matching n) (ρ : Equiv.Perm (Fin n))
    (c : (Fin n ⊕ Fin n) × Fin n) : Prop :=
  ∃ m ∈ ρ.support, rotationClockCell μ ρ m = c
private theorem manRank_eq_of_fix_rotationClockCells {x y : ScoreProfile n}
    {μ : Matching n} {ρ : Equiv.Perm (Fin n)}
    (hfixed : ∀ r i, ¬IsRotationClockCell μ ρ (r, i) → y r i = x r i) :
    (profileOfScores y).manRank = (profileOfScores x).manRank := by
  have hrow (m : Fin n) : y (.inl m) = x (.inl m) := funext fun i ↦
    hfixed (.inl m) i fun ⟨a, _, ha⟩ ↦ Sum.inr_ne_inl (congrArg Prod.fst ha)
  funext m
  simp only [profileOfScores, hrow m]
theorem scoreRotationGraph_eq_of_replace_selected {x y : ScoreProfile n} {ν μ : Matching n}
    {rs : List (Equiv.Perm (Fin n))} (hp : RotationSequence (profileOfScores x) ν rs μ)
    {ρ : Equiv.Perm (Fin n)} (hρ : IsExposedRotation (profileOfScores x) μ ρ)
    (ht : ∀ j, Function.Injective (x (.inr j)))
    (hfixed : ∀ r i, ¬IsRotationClockCell μ ρ (r, i) → y r i = x r i)
    (hbelow : ∀ m ∈ ρ.support, y (rotationClockCell μ ρ m).1 (rotationClockCell μ ρ m).2 <
      femaleSpouseScore x μ (eliminateRotation μ ρ m)) :
    scoreRotationGraph y ν = scoreRotationGraph x ν := by
  have hmen := manRank_eq_of_fix_rotationClockCells hfixed
  have hspouse (j : Fin n) : femaleSpouseScore y ν j = femaleSpouseScore x ν j := by
    apply hfixed
    intro ⟨a, ha, h⟩
    apply hp.rotationClockCell_ne_old_spouse hρ ha (ν.symm j)
    simpa only [Equiv.apply_symm_apply] using h
  have horacle : successorScoreOracle (femaleSpouseScore y ν) (fun w ↦ y (.inr w)) =
      successorScoreOracle (femaleSpouseScore x ν) (fun w ↦ x (.inr w)) := by
    funext m w
    unfold successorScoreOracle
    rw [hspouse]
    change decide (y (.inr w) m < _) = decide (x (.inr w) m < _)
    by_cases hc : IsRotationClockCell μ ρ (.inr w, m)
    · obtain ⟨a, ha, heq⟩ := hc
      have hy := (hbelow a ha).trans_le
        (hp.femaleSpouseScore_end_le_start ht (eliminateRotation μ ρ a))
      have hx := hp.rotationClockCell_score_lt_old_threshold hρ ht ha
      have hw : eliminateRotation μ ρ a = w := Sum.inr.inj (congrArg Prod.fst heq)
      rw [hw, heq] at hy hx
      simp only [hy, hx, decide_true]
    · rw [hfixed _ _ hc]
  rw [scoreRotationGraph, scoreRotationGraph, hmen, horacle]
theorem da_matching_eq_of_replace_selected {x y : ScoreProfile n} {μ : Matching n}
    {rs : List (Equiv.Perm (Fin n))}
    (hp : RotationSequence (profileOfScores x) (DAState.matching (profileOfScores x)) rs μ)
    {ρ : Equiv.Perm (Fin n)} (hρ : IsExposedRotation (profileOfScores x) μ ρ)
    (hx : ∀ j, Function.Injective (x (.inr j))) (hy : ∀ j, Function.Injective (y (.inr j)))
    (hfixed : ∀ r i, ¬IsRotationClockCell μ ρ (r, i) → y r i = x r i) :
    DAState.matching (profileOfScores y) = DAState.matching (profileOfScores x) := by
  let p := profileOfScores x
  let q := profileOfScores y
  have hrun := DAState.run_eq_of_agree_on_proposed_scores (n * n) hx hy
    (manRank_eq_of_fix_rotationClockCells hfixed).symm fun w a ha ↦ by
      apply Eq.symm
      apply hfixed
      intro ⟨m, hm, heq⟩
      have hma : m = a := congrArg Prod.snd heq
      subst a
      exact hρ.new_partner_ne_of_rank_le hm
        (((DAState.proposed_run_sq_iff p m w).mp ha).trans (hp.menWeaklyPrefer m))
        (Sum.inr.inj (congrArg Prod.fst heq))
  apply Equiv.ext
  intro m
  have hm (a : Profile n) :
      (DAState.run a (n * n)).held (DAState.matching a m) = some m :=
    DAState.held_toMatching _ (DAState.complete_run_sq a) m
  exact (DAState.valid_run p (n * n)).held_unique (hrun ▸ hm q) (hm p)
theorem scoreRotationWalk_eq_at_every_prefix {x y : ScoreProfile n} (k : ℕ)
    (ht : ∀ j, Function.Injective (x (.inr j))) {ν : Matching n}
    (hν : IsStable (profileOfScores x) ν) {ρ : Equiv.Perm (Fin n)}
    (hρ : IsExposedRotation (profileOfScores x) (scoreRotationWalk x k ν).2 ρ)
    (hfixed : ∀ r i, ¬IsRotationClockCell (scoreRotationWalk x k ν).2 ρ (r, i) →
      y r i = x r i)
    (hbelow : ∀ m ∈ ρ.support,
      let μ := (scoreRotationWalk x k ν).2
      y (rotationClockCell μ ρ m).1 (rotationClockCell μ ρ m).2 <
        femaleSpouseScore x μ (eliminateRotation μ ρ m)) :
    ∀ j ≤ k, scoreRotationWalk y j ν = scoreRotationWalk x j ν := by
  induction k generalizing ν with
  | zero =>
    intro j hj
    obtain rfl := Nat.eq_zero_of_le_zero hj
    rfl
  | succ k ih =>
    intro j hj
    cases j with
    | zero => rfl
    | succ j =>
      have hgraph := scoreRotationGraph_eq_of_replace_selected
        (scoreRotationWalk_legal x ht (k + 1) hν) hρ ht hfixed hbelow
      rw [scoreRotationWalk_succ, scoreRotationWalk_succ, hgraph]
      cases h : chooseQueriedRotation (scoreRotationGraph x ν) with
      | none => rfl
      | some σ =>
        have hσ : IsExposedRotation (profileOfScores x) ν σ :=
          (realizesDirectedCycle_queriedSuccessorGraph_scores_iff x ht ν σ).mp
            (realizesDirectedCycle_of_chooseQueriedRotation h)
        rw [scoreRotationWalk_succ, h] at hρ hfixed hbelow
        exact congrArg (fun z ↦ (σ :: z.1, z.2))
          (ih (hσ.isStable_eliminate hν) hρ hfixed hbelow j (Nat.le_of_succ_le_succ hj))
theorem scoreRotationWalk_eq_of_replace_selected {x y : ScoreProfile n} (k : ℕ)
    (ht : ∀ j, Function.Injective (x (.inr j))) {ν : Matching n}
    (hν : IsStable (profileOfScores x) ν) {ρ : Equiv.Perm (Fin n)}
    (hρ : IsExposedRotation (profileOfScores x) (scoreRotationWalk x k ν).2 ρ)
    (hfixed : ∀ r i, ¬IsRotationClockCell (scoreRotationWalk x k ν).2 ρ (r, i) →
      y r i = x r i)
    (hbelow : ∀ m ∈ ρ.support,
      let μ := (scoreRotationWalk x k ν).2
      y (rotationClockCell μ ρ m).1 (rotationClockCell μ ρ m).2 <
        femaleSpouseScore x μ (eliminateRotation μ ρ m)) :
    scoreRotationWalk y k ν = scoreRotationWalk x k ν :=
  scoreRotationWalk_eq_at_every_prefix k ht hν hρ hfixed hbelow k le_rfl
theorem scoreRotationWalk_same_prefix_and_choice_iff {x y : ScoreProfile n} (k : ℕ)
    (hx : ∀ j, Function.Injective (x (.inr j))) (hy : ∀ j, Function.Injective (y (.inr j)))
    {ρ : Equiv.Perm (Fin n)}
    (hchoose : chooseQueriedRotation (scoreRotationGraph x
      (scoreRotationWalk x k (DAState.matching (profileOfScores x))).2) = some ρ)
    (hfixed : ∀ r i, ¬IsRotationClockCell
      (scoreRotationWalk x k (DAState.matching (profileOfScores x))).2 ρ (r, i) →
      y r i = x r i) :
    let start := DAState.matching (profileOfScores x)
    let out := scoreRotationWalk x k start
    let out' := scoreRotationWalk y k (DAState.matching (profileOfScores y))
    (out' = out ∧ chooseQueriedRotation (scoreRotationGraph y out'.2) = some ρ) ↔
      ∀ m ∈ ρ.support,
        y (rotationClockCell out.2 ρ m).1 (rotationClockCell out.2 ρ m).2 <
          femaleSpouseScore x out.2 (eliminateRotation out.2 ρ m) := by
  let start := DAState.matching (profileOfScores x)
  let out := scoreRotationWalk x k start
  let out' := scoreRotationWalk y k (DAState.matching (profileOfScores y))
  change (out' = out ∧ chooseQueriedRotation (scoreRotationGraph y out'.2) = some ρ) ↔ _
  have hstart := (DAState.isManOptimal_matching (profileOfScores x)).1
  have hp := scoreRotationWalk_legal x hx k hstart
  have hρ := (realizesDirectedCycle_queriedSuccessorGraph_scores_iff x hx out.2 ρ).mp
    (realizesDirectedCycle_of_chooseQueriedRotation hchoose)
  have hspouse (j : Fin n) : femaleSpouseScore y out.2 j = femaleSpouseScore x out.2 j := by
    apply hfixed
    intro ⟨a, ha, heq⟩
    apply (RotationSequence.nil hp.isStable_end).rotationClockCell_ne_old_spouse hρ ha
      (out.2.symm j)
    change rotationClockCell out.2 ρ a = (.inr (out.2 (out.2.symm j)), out.2.symm j)
    rw [Equiv.apply_symm_apply]
    exact heq
  constructor
  · rintro ⟨heq, hc⟩ m hm
    rw [heq] at hc
    have hρ' := (realizesDirectedCycle_queriedSuccessorGraph_scores_iff y hy out.2 ρ).mp
      (realizesDirectedCycle_of_chooseQueriedRotation hc)
    rw [← hspouse]
    exact hρ'.rotationClockCell_score_lt hy hm
  · intro hbelow
    have hda := da_matching_eq_of_replace_selected hp hρ hx hy hfixed
    have heq : out' = out := by
      unfold out' out
      rw [hda]
      exact scoreRotationWalk_eq_of_replace_selected k hx hstart hρ hfixed hbelow
    have hgraph := scoreRotationGraph_eq_of_replace_selected
      (RotationSequence.nil hp.isStable_end) hρ hx hfixed hbelow
    exact ⟨heq, by rw [heq, hgraph]; exact hchoose⟩
end StepA4
end

-- ScoreRotationBranchLaw
section
open MeasureTheory Set StableMarriage
open scoped BigOperators Classical
namespace StepA4
variable {n : ℕ}
private abbrev ClockCell (n : ℕ) := (Fin n ⊕ Fin n) × Fin n
private abbrev ClockSelected (μ : Matching n) (ρ : Equiv.Perm (Fin n)) :=
  {c : ClockCell n // IsRotationClockCell μ ρ c}
private abbrev ClockComplement (μ : Matching n) (ρ : Equiv.Perm (Fin n)) :=
  {c : ClockCell n // ¬IsRotationClockCell μ ρ c}
private noncomputable def splitRotationClockCells (μ : Matching n) (ρ : Equiv.Perm (Fin n)) :
    ScoreProfile n ≃ᵐ (ClockComplement μ ρ → ℝ) × (ClockSelected μ ρ → ℝ) :=
  (MeasurableEquiv.curry (Fin n ⊕ Fin n) (Fin n) ℝ).symm.trans
    ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ClockCell n ↦ ℝ)
      (IsRotationClockCell μ ρ)).trans MeasurableEquiv.prodComm)
private theorem measurePreserving_clockUncurry (n : ℕ) :
    MeasurePreserving (MeasurableEquiv.curry (Fin n ⊕ Fin n) (Fin n) ℝ).symm
      (continuousScoreLaw n) (Measure.pi fun _ : ClockCell n ↦ unitScoreLaw) := by
  refine ⟨(MeasurableEquiv.curry (Fin n ⊕ Fin n) (Fin n) ℝ).symm.measurable, ?_⟩
  refine (Measure.pi_eq fun s _ ↦ ?_).symm
  rw [MeasurableEquiv.map_apply]
  rw [show (MeasurableEquiv.curry (Fin n ⊕ Fin n) (Fin n) ℝ).symm ⁻¹' (univ.pi s) =
      univ.pi (fun i ↦ univ.pi fun j ↦ s (i, j)) by
    ext x
    simp [mem_pi, Prod.forall]]
  simp_rw [continuousScoreLaw, Measure.pi_pi]
  rw [← Finset.prod_product']
  simp
theorem measurePreserving_splitRotationClockCells (μ : Matching n) (ρ : Equiv.Perm (Fin n)) :
    MeasurePreserving (splitRotationClockCells μ ρ) (continuousScoreLaw n)
      ((Measure.pi fun _ : ClockComplement μ ρ ↦ unitScoreLaw).prod
        (Measure.pi fun _ : ClockSelected μ ρ ↦ unitScoreLaw)) :=
  (Measure.measurePreserving_swap.comp
    (measurePreserving_piEquivPiSubtypeProd (fun _ : ClockCell n ↦ unitScoreLaw)
      (IsRotationClockCell μ ρ))).comp (measurePreserving_clockUncurry n)
private theorem split_snd_apply (μ : Matching n) (ρ : Equiv.Perm (Fin n))
    (x : ScoreProfile n) (c : ClockSelected μ ρ) :
    (splitRotationClockCells μ ρ x).2 c = x c.val.1 c.val.2 := rfl
theorem old_spouse_not_selected (μ : Matching n) (ρ : Equiv.Perm (Fin n))
    (w : Fin n) : ¬IsRotationClockCell μ ρ (.inr w, μ.symm w) := by
  rintro ⟨m, hm, heq⟩
  have ha : m = μ.symm w := congrArg Prod.snd heq
  have hw : μ (ρ m) = w := Sum.inr.inj (congrArg Prod.fst heq)
  have hm' : μ m = w := (congrArg μ ha).trans (μ.apply_symm_apply w)
  have hr : ρ m = m := μ.injective (hw.trans hm'.symm)
  exact (Equiv.Perm.mem_support.mp hm) hr
theorem femaleSpouseScore_eq_of_splitRotationClockCells_fst_eq (μ : Matching n)
    (ρ : Equiv.Perm (Fin n)) {x y : ScoreProfile n}
    (h : (splitRotationClockCells μ ρ x).1 = (splitRotationClockCells μ ρ y).1) (w : Fin n) :
    femaleSpouseScore x μ w = femaleSpouseScore y μ w :=
  congrFun h ⟨(.inr w, μ.symm w), old_spouse_not_selected μ ρ w⟩
private def rotationClockUpper (μ : Matching n) (ρ : Equiv.Perm (Fin n))
    (a : ClockComplement μ ρ → ℝ) (c : ClockSelected μ ρ) : ℝ :=
  let w := eliminateRotation μ ρ c.val.2
  a ⟨(.inr w, μ.symm w), old_spouse_not_selected μ ρ w⟩
private theorem rotationClockUpper_split (μ : Matching n) (ρ : Equiv.Perm (Fin n))
    (x : ScoreProfile n) (c : ClockSelected μ ρ) :
    rotationClockUpper μ ρ (splitRotationClockCells μ ρ x).1 c =
      femaleSpouseScore x μ (eliminateRotation μ ρ c.val.2) := rfl
private theorem symm_mem_support {ρ : Equiv.Perm (Fin n)} {i : Fin n} (hi : i ∈ ρ.support) :
    ρ.symm i ∈ ρ.support :=
  Equiv.Perm.apply_mem_support.mp (by simpa only [Equiv.apply_symm_apply] using hi)
private noncomputable def oldHusbandEquivSelected (μ : Matching n) (ρ : Equiv.Perm (Fin n)) :
    {i : Fin n // i ∈ ρ.support} ≃ ClockSelected μ ρ := by
  let f (i : {i : Fin n // i ∈ ρ.support}) : ClockSelected μ ρ :=
    ⟨rotationClockCell μ ρ (ρ.symm i.val), ⟨_, symm_mem_support i.property, rfl⟩⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro i j h
    exact Subtype.ext (ρ.symm.injective
      (rotationClockCell_injective μ ρ (congrArg Subtype.val h)))
  · intro c
    obtain ⟨m, hm, heq⟩ := c.property
    refine ⟨⟨ρ m, Equiv.Perm.apply_mem_support.mpr hm⟩, Subtype.ext ?_⟩
    exact (congrArg (rotationClockCell μ ρ) (ρ.symm_apply_apply m)).trans heq
theorem card_clockSelected (μ : Matching n) (ρ : Equiv.Perm (Fin n)) :
    Fintype.card (ClockSelected μ ρ) = ρ.support.card :=
  (Fintype.card_congr (oldHusbandEquivSelected μ ρ).symm).trans (Fintype.card_coe _)
theorem centeredCacheLogIncrement_splitRotationClockCells (x : ScoreProfile n)
    (μ : Matching n) (ρ : Equiv.Perm (Fin n)) (hx : ∀ j i, 0 < x (.inr j) i) :
    centeredCacheLogIncrement (rotationClockUpper μ ρ) (splitRotationClockCells μ ρ x) =
      femaleLogPotential x (eliminateRotation μ ρ) - femaleLogPotential x μ -
        (ρ.support.card : ℝ) := by
  rw [femaleLogPotential_eliminate_sub x μ ρ hx, sum_negLog_sub_card_eq_sum_centeredNegLog]
  unfold centeredCacheLogIncrement
  let e := oldHusbandEquivSelected μ ρ
  rw [← Equiv.sum_comp e]
  rw [← Finset.sum_coe_sort ρ.support]
  apply Finset.sum_congr rfl
  intro i _
  have he : (e i).val = rotationClockCell μ ρ (ρ.symm i.val) := rfl
  have hnew : eliminateRotation μ ρ (ρ.symm i.val) = μ i.val := by
    rw [eliminateRotation_apply, Equiv.apply_symm_apply]
  have hval := femaleSpouseScore_eliminate_apply x μ ρ (ρ.symm i.val)
  rw [hnew] at hval
  rw [split_snd_apply, rotationClockUpper_split]
  simp only [he, rotationClockCell, hnew, femaleRotationRatio] at hval ⊢
  rw [hval]
private def ordinalClockGraph (p : Profile n) (μ : Matching n) : Fin n → Option (Fin n) :=
  queriedSuccessorGraph p.manRank μ
    (fun m w ↦ decide (p.womanRank w m < p.womanRank w (μ.symm w)))
private noncomputable def ordinalClockEnd (p : Profile n) : ℕ → Matching n → Matching n
  | 0, μ => μ
  | k + 1, μ =>
    match chooseQueriedRotation (ordinalClockGraph p μ) with
    | none => μ
    | some ρ => ordinalClockEnd p k (eliminateRotation μ ρ)
private theorem ordinalClockGraph_eq_score (x : ScoreProfile n)
    (hx : ∀ w, Function.Injective (x (.inr w))) (μ : Matching n) :
    ordinalClockGraph (profileOfScores x) μ = scoreRotationGraph x μ := by
  unfold ordinalClockGraph scoreRotationGraph
  congr 1
  funext m w
  simp only [profileOfScores, successorScoreOracle, femaleSpouseScore]
  exact decide_eq_decide.mpr (rankPermutation_lt_iff (hx w) m (μ.symm w))
private theorem ordinalClockEnd_eq_score (x : ScoreProfile n)
    (hx : ∀ w, Function.Injective (x (.inr w))) (k : ℕ) (μ : Matching n) :
    ordinalClockEnd (profileOfScores x) k μ = (scoreRotationWalk x k μ).2 := by
  induction k generalizing μ with
  | zero => rfl
  | succ k ih =>
    rw [ordinalClockEnd, scoreRotationWalk_succ, ordinalClockGraph_eq_score x hx]
    cases chooseQueriedRotation (scoreRotationGraph x μ) with
    | none => rfl
    | some ρ => exact ih _
private def goodClockInput (n : ℕ) : Set (ScoreProfile n) :=
  {x | (∀ w, Function.Injective (x (.inr w))) ∧ ∀ r i, x r i ∈ Ioo (0 : ℝ) 1}
theorem measurableSet_goodClockInput (n : ℕ) : MeasurableSet (goodClockInput n) := by
  have hc (r : Fin n ⊕ Fin n) (i : Fin n) :
      Measurable fun x : ScoreProfile n ↦ x r i :=
    (measurable_pi_apply i).comp (measurable_pi_apply r)
  unfold goodClockInput
  simp only [ofPred_and, Function.Injective, ofPred_forall]
  refine (MeasurableSet.iInter fun w ↦ MeasurableSet.iInter fun i ↦
    MeasurableSet.iInter fun j ↦ ?_).inter
    (MeasurableSet.iInter fun r ↦ MeasurableSet.iInter fun i ↦
      (measurableSet_Ioo : MeasurableSet (Ioo (0 : ℝ) 1)).preimage (hc r i))
  by_cases hij : i = j
  · simp [hij]
  · simp only [hij, imp_false]
    exact (measurableSet_eq_fun (hc (.inr w) i) (hc (.inr w) j)).compl
theorem ae_goodClockInput (n : ℕ) : ∀ᵐ x ∂continuousScoreLaw n, x ∈ goodClockInput n := by
  filter_upwards [ae_injective_rows n, ae_unitOpen_scores n] with x ht hu
  exact ⟨fun w ↦ ht (.inr w), hu⟩
private def scoreRotationBranch (k : ℕ) (μ : Matching n) (ρ : Equiv.Perm (Fin n)) :
    Set (ScoreProfile n) :=
  {x | x ∈ goodClockInput n ∧
    (scoreRotationWalk x k (DAState.matching (profileOfScores x))).2 = μ ∧
    chooseQueriedRotation (scoreRotationGraph x μ) = some ρ}
theorem measurableSet_scoreRotationBranch (k : ℕ) (μ : Matching n) (ρ : Equiv.Perm (Fin n)) :
    MeasurableSet (scoreRotationBranch k μ ρ) := by
  let B : Set (Profile n) := {p | ordinalClockEnd p k (DAState.matching p) = μ ∧
    chooseQueriedRotation (ordinalClockGraph p μ) = some ρ}
  have hB : MeasurableSet B := MeasurableSet.of_discrete
  have h : scoreRotationBranch k μ ρ = goodClockInput n ∩ profileOfScores ⁻¹' B := by
    ext x
    change (x ∈ goodClockInput n ∧ _) ↔ (x ∈ goodClockInput n ∧ _)
    refine and_congr_right fun hx ↦ ?_
    change (_ = μ ∧ _) ↔ (ordinalClockEnd _ k _ = μ ∧ _)
    rw [ordinalClockEnd_eq_score x hx.1, ordinalClockGraph_eq_score x hx.1]
  rw [h]
  exact (measurableSet_goodClockInput n).inter ((measurable_profileOfScores n) hB)
theorem scoreRotationBranch_inter_condExp_logMoments
    (k : ℕ) (μ : Matching n) (ρ : Equiv.Perm (Fin n)) {A : Set (ScoreProfile n)}
    (hA : MeasurableSet A)
    (hconst : ∀ {x y}, x ∈ scoreRotationBranch k μ ρ → y ∈ scoreRotationBranch k μ ρ →
      (splitRotationClockCells μ ρ x).1 = (splitRotationClockCells μ ρ y).1 →
      (x ∈ A ↔ y ∈ A)) :
    let e := splitRotationClockCells μ ρ
    let P := (Measure.pi fun _ : ClockComplement μ ρ ↦ unitScoreLaw).prod
      (Measure.pi fun _ : ClockSelected μ ρ ↦ unitScoreLaw)
    let ν := P.restrict (e.symm ⁻¹' (scoreRotationBranch k μ ρ ∩ A))
    let L := centeredCacheLogIncrement (rotationClockUpper μ ρ)
    let m := MeasurableSpace.comap Prod.fst (inferInstance :
      MeasurableSpace (ClockComplement μ ρ → ℝ))
    MemLp L 2 ν ∧ ν[L | m] =ᵐ[ν] (fun _ ↦ 0) ∧
      ν[(fun z ↦ (L z) ^ 2) | m] =ᵐ[ν] (fun _ ↦ (ρ.support.card : ℝ)) := by
  let e := splitRotationClockCells μ ρ
  let E := e.symm ⁻¹' (scoreRotationBranch k μ ρ ∩ A)
  let G := e.symm ⁻¹' goodClockInput n
  have hE := e.symm.measurable ((measurableSet_scoreRotationBranch k μ ρ).inter hA)
  have hG := e.symm.measurable (measurableSet_goodClockInput n)
  have hgood := (measurePreserving_splitRotationClockCells μ ρ).symm.quasiMeasurePreserving.ae
    (ae_goodClockInput n)
  have hupper (i : ClockSelected μ ρ) :
      Measurable (fun a ↦ rotationClockUpper μ ρ a i) := measurable_pi_apply _
  rw [← card_clockSelected μ ρ]
  refine scoreBranch_condExp_logMoments_of_replay
    (Measure.pi fun _ : ClockComplement μ ρ ↦ unitScoreLaw)
    (E := E) (G := G) hE hG hgood (rotationClockUpper μ ρ) hupper ?_ ?_
  · intro a v hv i
    let x := e.symm (a, v)
    have hg : x ∈ goodClockInput n := hv.1.1
    have hs := hg.2 (.inr (eliminateRotation μ ρ i.val.2))
      (μ.symm (eliminateRotation μ ρ i.val.2))
    have he : e x = (a, v) := e.apply_symm_apply _
    have hc := rotationClockUpper_split μ ρ x i
    change rotationClockUpper μ ρ (e x).1 i = _ at hc
    rw [he] at hc
    exact ⟨hc ▸ hs.1, hc ▸ hs.2.le⟩
  · intro a u hu v hv
    let x := e.symm (a, u)
    let y := e.symm (a, v)
    have ex : e x = (a, u) := e.apply_symm_apply _
    have ey : e y = (a, v) := e.apply_symm_apply _
    have hx : x ∈ scoreRotationBranch k μ ρ := hu.1
    have hy : y ∈ goodClockInput n := hv
    have hfixed (r : Fin n ⊕ Fin n) (i : Fin n) (hc : ¬ IsRotationClockCell μ ρ (r, i)) :
        y r i = x r i := by
      let c : ClockComplement μ ρ := ⟨(r, i), hc⟩
      change (e y).1 c = (e x).1 c
      rw [ey, ex]
    have hchoose := hx.2.2
    rw [← hx.2.1] at hchoose
    have hpass := scoreRotationWalk_same_prefix_and_choice_iff k hx.1.1 hy.1 hchoose
      (by rw [hx.2.1]; exact hfixed)
    constructor
    · intro hbranch i
      have hb : y ∈ scoreRotationBranch k μ ρ := hbranch.1
      have hρ := (realizesDirectedCycle_queriedSuccessorGraph_scores_iff y hy.1 μ ρ).mp
        (realizesDirectedCycle_of_chooseQueriedRotation hb.2.2)
      obtain ⟨m, hm, heq⟩ := i.property
      have ha : m = i.val.2 := congrArg Prod.snd heq
      subst m
      have hlt := hρ.rotationClockCell_score_lt hy.1 hm
      rw [heq, femaleSpouseScore, hfixed _ _ (old_spouse_not_selected μ ρ _)] at hlt
      have hc := rotationClockUpper_split μ ρ x i
      change rotationClockUpper μ ρ (e x).1 i = _ at hc
      rw [ex] at hc
      have hval := split_snd_apply μ ρ y i
      change (e y).2 i = _ at hval
      rw [ey] at hval
      change v i = _ at hval
      change rotationClockUpper μ ρ a i = _ at hc
      refine ⟨?_, ?_⟩
      · rw [hval]
        exact (hy.2 i.val.1 i.val.2).1
      · rw [hval, hc]
        exact hlt
    · intro hall
      have hbelow (m : Fin n) (hm : m ∈ ρ.support) :
          y (rotationClockCell μ ρ m).1 (rotationClockCell μ ρ m).2 <
            femaleSpouseScore x μ (eliminateRotation μ ρ m) := by
        let c : ClockSelected μ ρ := ⟨rotationClockCell μ ρ m, ⟨m, hm, rfl⟩⟩
        have hval := split_snd_apply μ ρ y c
        change (e y).2 c = _ at hval
        rw [ey] at hval
        have hc := rotationClockUpper_split μ ρ x c
        change rotationClockUpper μ ρ (e x).1 c = _ at hc
        rw [ex] at hc
        exact hval ▸ hc ▸ (hall c).2
      have hp := hpass.mpr (by rw [hx.2.1]; exact hbelow)
      have hyμ := (congrArg Prod.snd hp.1).trans hx.2.1
      have hsame := congrArg
        (fun τ : Matching n ↦ chooseQueriedRotation (scoreRotationGraph y τ)) hyμ
      have hb : y ∈ scoreRotationBranch k μ ρ := ⟨hy, hyμ, hsame.symm.trans hp.2⟩
      refine ⟨hb, (hconst hx hb ?_).mp hu.2⟩
      exact (congrArg Prod.fst ex).trans (congrArg Prod.fst ey).symm
end StepA4
end

-- DALowerEndpoint
section
open Filter MeasureTheory Set StableMarriage
open scoped Classical ENNReal Topology
namespace StepA4
variable {n : ℕ}
private def daProposalEvent (k : ℕ) (c : Fin n × Fin n) : Set (ScoreProfile n) :=
  {x | (DAState.run (profileOfScores x) k).nextProposal (profileOfScores x).manRank = some c}
theorem measurableSet_daProposalEvent (k : ℕ) (c : Fin n × Fin n) :
    MeasurableSet (daProposalEvent k c) := by
  change MeasurableSet (profileOfScores ⁻¹'
    {p : Profile n | (DAState.run p k).nextProposal p.manRank = some c})
  exact (measurable_profileOfScores n) MeasurableSet.of_discrete
private abbrev daFemaleCell (c : Fin n × Fin n) : ClockCell n :=
  (.inr c.2, c.1)
theorem mem_daProposalEvent_of_agree_off_cell (k : ℕ) (c : Fin n × Fin n)
    {x y : ScoreProfile n} (hx : x ∈ daProposalEvent k c)
    (hxt : ∀ w, Function.Injective (x (.inr w)))
    (hyt : ∀ w, Function.Injective (y (.inr w)))
    (hoff : ∀ d : ClockCell n, d ≠ daFemaleCell c → x d.1 d.2 = y d.1 d.2) :
    y ∈ daProposalEvent k c := by
  have hmen : (profileOfScores x).manRank = (profileOfScores y).manRank := by
    funext m
    change rankPermutation (x (.inl m)) = rankPermutation (y (.inl m))
    congr 1
    funext w
    exact hoff (.inl m, w) (by simp)
  have hp := DAState.nextProposal_some hx
  have hrun := DAState.run_eq_of_agree_on_proposed_scores k hxt hyt hmen ?_
  · change (DAState.run (profileOfScores y) k).nextProposal (profileOfScores y).manRank =
      some c
    rw [hrun, ← hmen]
    exact hx
  · intro w m hread
    apply hoff (.inr w, m)
    intro h
    have hw : w = c.2 := Sum.inr.inj (congrArg Prod.fst h)
    have hm : m = c.1 := congrArg Prod.snd h
    subst w
    subst m
    exact (Nat.ne_of_lt hread) hp.2
private abbrev DAOtherCells (c : Fin n × Fin n) := {d : ClockCell n // d ≠ daFemaleCell c}
private abbrev DAChosenCell (c : Fin n × Fin n) := {d : ClockCell n // d = daFemaleCell c}
private noncomputable def splitDAFemaleCell (c : Fin n × Fin n) :
    ScoreProfile n ≃ᵐ (DAOtherCells c → ℝ) × (DAChosenCell c → ℝ) :=
  (MeasurableEquiv.curry (Fin n ⊕ Fin n) (Fin n) ℝ).symm.trans
    ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ClockCell n ↦ ℝ)
      (fun d ↦ d = daFemaleCell c)).trans MeasurableEquiv.prodComm)
private theorem measurePreserving_daUncurry (n : ℕ) :
    MeasurePreserving (MeasurableEquiv.curry (Fin n ⊕ Fin n) (Fin n) ℝ).symm
      (continuousScoreLaw n) (Measure.pi fun _ : ClockCell n ↦ unitScoreLaw) := by
  refine ⟨(MeasurableEquiv.curry (Fin n ⊕ Fin n) (Fin n) ℝ).symm.measurable, ?_⟩
  refine (Measure.pi_eq fun s _ ↦ ?_).symm
  rw [MeasurableEquiv.map_apply]
  rw [show (MeasurableEquiv.curry (Fin n ⊕ Fin n) (Fin n) ℝ).symm ⁻¹' (univ.pi s) =
      univ.pi (fun i ↦ univ.pi fun j ↦ s (i, j)) by
    ext x
    simp [Set.mem_pi, Prod.forall]]
  simp_rw [continuousScoreLaw, Measure.pi_pi]
  rw [← Finset.prod_product']
  simp
private theorem measurePreserving_splitDAFemaleCell (c : Fin n × Fin n) :
    MeasurePreserving (splitDAFemaleCell c) (continuousScoreLaw n)
      ((Measure.pi fun _ : DAOtherCells c ↦ unitScoreLaw).prod
        (Measure.pi fun _ : DAChosenCell c ↦ unitScoreLaw)) := by
  convert (Measure.measurePreserving_swap.comp
    (measurePreserving_piEquivPiSubtypeProd (fun _ : ClockCell n ↦ unitScoreLaw)
      (fun d ↦ d = daFemaleCell c))).comp (measurePreserving_daUncurry n) using 3
  rfl
theorem measure_daProposalEvent_inter_score (k : ℕ) (c : Fin n × Fin n)
    {S : Set ℝ} (hS : MeasurableSet S) :
    continuousScoreLaw n (daProposalEvent k c ∩ {x | x (.inr c.2) c.1 ∈ S}) =
      continuousScoreLaw n (daProposalEvent k c) * unitScoreLaw S := by
  let e := splitDAFemaleCell c
  let Q := Measure.pi (fun _ : DAOtherCells c ↦ unitScoreLaw)
  let R := Measure.pi (fun _ : DAChosenCell c ↦ unitScoreLaw)
  let E := e.symm ⁻¹' (daProposalEvent k c ∩ goodClockInput n)
  let G := e.symm ⁻¹' goodClockInput n
  let Z : Set (DAChosenCell c → ℝ) := Function.eval ⟨daFemaleCell c, rfl⟩ ⁻¹' S
  have he : MeasurePreserving e (continuousScoreLaw n) (Q.prod R) :=
    measurePreserving_splitDAFemaleCell c
  have hE := e.symm.measurable ((measurableSet_daProposalEvent k c).inter
    (measurableSet_goodClockInput n))
  have hG := e.symm.measurable (measurableSet_goodClockInput n)
  have hgood := he.symm.quasiMeasurePreserving.ae (ae_goodClockInput n)
  have hZ : MeasurableSet Z := (measurable_pi_apply _) hS
  have hZR : R Z = unitScoreLaw S :=
    (measurePreserving_eval (μ := fun _ : DAChosenCell c ↦ unitScoreLaw) _).measure_preimage
      hS.nullMeasurableSet
  have hreplay : ∀ a u, (a, u) ∈ E → ∀ v, (a, v) ∈ G →
      ((a, v) ∈ E ↔ ∀ i : DAChosenCell c, v i ∈ Ioo (0 : ℝ) 1) := by
    intro a u hu v hv
    let x := e.symm (a, u)
    let y := e.symm (a, v)
    have hx : x ∈ daProposalEvent k c ∩ goodClockInput n := hu
    have hy : y ∈ goodClockInput n := hv
    have ex : e x = (a, u) := e.apply_symm_apply _
    have ey : e y = (a, v) := e.apply_symm_apply _
    have hfixed (d : ClockCell n) (hd : d ≠ daFemaleCell c) : x d.1 d.2 = y d.1 d.2 := by
      change (e x).1 ⟨d, hd⟩ = (e y).1 ⟨d, hd⟩
      rw [ex, ey]
    have hsel := mem_daProposalEvent_of_agree_off_cell k c hx.1 hx.2.1 hy.1 hfixed
    have hvunit (i : DAChosenCell c) : v i ∈ Ioo (0 : ℝ) 1 := by
      have h := hy.2 i.val.1 i.val.2
      change (e y).2 i ∈ Ioo (0 : ℝ) 1 at h
      simpa only [ey] using h
    exact ⟨fun _ ↦ hvunit, fun _ ↦ ⟨hsel, hy⟩⟩
  have hrep := ae_eq_scoreCacheFiberEvent_of_replay Q hE hG hgood (fun _ _ ↦ 1)
    (fun _ ↦ measurable_const) hreplay
  have hrect : E =ᵐ[Q.prod R] scoreBranchBase E ×ˢ (univ : Set (DAChosenCell c → ℝ)) := by
    apply hrep.trans
    apply Filter.Eventually.set_eq
    filter_upwards [hgood] with z hz
    change z.1 ∈ scoreBranchBase E ∧ (∀ i : DAChosenCell c, z.2 i ∈ Ioo (0 : ℝ) 1) ↔
      z.1 ∈ scoreBranchBase E ∧ z.2 ∈ univ
    have hunit (i : DAChosenCell c) : z.2 i ∈ Ioo (0 : ℝ) 1 := by
      have h : (e (e.symm z)).2 i ∈ Ioo (0 : ℝ) 1 := hz.2 i.val.1 i.val.2
      simpa only [e.apply_symm_apply] using h
    simp [hunit]
  have hE0 : (Q.prod R) E = Q (scoreBranchBase E) := by
    rw [measure_congr hrect, Measure.prod_prod, measure_univ, mul_one]
  have hEZ : (Q.prod R) (E ∩ Prod.snd ⁻¹' Z) = Q (scoreBranchBase E) * unitScoreLaw S := by
    have hrectZ : (E ∩ Prod.snd ⁻¹' Z : Set _) =ᵐ[Q.prod R] (scoreBranchBase E ×ˢ Z) := by
      apply Filter.Eventually.set_eq
      filter_upwards [hrect.mem_iff] with z hz
      change (z ∈ E ∧ z.2 ∈ Z) ↔ _
      rw [hz]
      simp
    rw [measure_congr hrectZ, Measure.prod_prod, hZR]
  have hpre : e ⁻¹' E = daProposalEvent k c ∩ goodClockInput n := by
    ext x
    simp [E]
  have hpreZ : e ⁻¹' (E ∩ Prod.snd ⁻¹' Z) =
      (daProposalEvent k c ∩ goodClockInput n) ∩ {x | x (.inr c.2) c.1 ∈ S} := by
    rw [preimage_inter, hpre]
    rfl
  have h0 := he.measure_preimage hE.nullMeasurableSet
  have h1 := he.measure_preimage (hE.inter (measurable_snd hZ)).nullMeasurableSet
  rw [hpre, hE0] at h0
  rw [hpreZ, hEZ, ← h0] at h1
  have hg (A : Set (ScoreProfile n)) :
      (A ∩ goodClockInput n : Set _) =ᵐ[continuousScoreLaw n] A := by
    apply Filter.Eventually.set_eq
    filter_upwards [ae_goodClockInput n] with x hx
    simp [hx]
  rw [measure_congr (hg (daProposalEvent k c))] at h1
  refine (measure_congr ?_).trans h1
  apply Filter.Eventually.set_eq
  filter_upwards [ae_goodClockInput n] with x hx
  simp [hx]
private theorem DAState.proposalCount_run_eq_of_active (p : Profile n) (k : ℕ)
    (h : (DAState.run p k).nextProposal p.manRank ≠ none) :
    (DAState.run p k).proposalCount = k := by
  induction k with
  | zero => simp [DAState.run_zero, DAState.run_succ, DAState.initial, DAState.proposalCount]
  | succ k ih =>
    cases hp : (DAState.run p k).nextProposal p.manRank with
    | none => exact False.elim (h (by simp only [DAState.run_zero, DAState.run_succ, DAState.advance, hp]))
    | some c =>
      change (DAState.advance p (DAState.run p k)).proposalCount = k + 1
      rw [DAState.proposalCount_advance_of_some hp, ih (by simp [hp])]
private theorem DAState.exists_proposal_before_of_rank_lt_count (p : Profile n) (K : ℕ)
    (m w : Fin n) (h : (p.manRank m w).val < (DAState.run p K).count m) :
    ∃ k < K, (DAState.run p k).nextProposal p.manRank = some (m, w) := by
  induction K with
  | zero => simp [DAState.run_zero, DAState.run_succ, DAState.initial] at h
  | succ K ih =>
    by_cases hprev : (p.manRank m w).val < (DAState.run p K).count m
    · obtain ⟨k, hk, hp⟩ := ih hprev
      exact ⟨k, hk.trans (Nat.lt_succ_self _), hp⟩
    · change _ < (DAState.advance p (DAState.run p K)).count m at h
      cases hp : (DAState.run p K).nextProposal p.manRank with
      | none => exact False.elim (hprev (by simpa only [DAState.advance, hp] using h))
      | some c =>
        obtain ⟨a, b⟩ := c
        rw [DAState.advance, hp] at h
        have ham : m = a := by
          by_contra hne
          exact hprev (by simpa [DAState.applyDecision, hne] using h)
        subst a
        have hcount : (p.manRank m w).val = (DAState.run p K).count m := by
          simp only [DAState.count, DAState.held, DAState.applyDecision, Function.update_self] at h
          dsimp only [DAState.count, DAState.held] at *
          omega
        have hwb := (p.manRank m).injective (Fin.ext (hcount.trans
          (DAState.nextProposal_some hp).2.symm))
        exact ⟨K, Nat.lt_succ_self _, hwb ▸ hp⟩
private theorem DAState.proposalCount_run_mono (p : Profile n) :
    Monotone fun k ↦ (DAState.run p k).proposalCount :=
  fun _ _ h ↦ Finset.sum_le_sum fun m _ ↦ DAState.count_mono_run p m h
theorem DAState.exists_nextProposal_final_pair (p : Profile n) (w : Fin n) :
    ∃ k < (DAState.run p (n * n)).proposalCount,
      (DAState.run p k).nextProposal p.manRank = some ((DAState.matching p).symm w, w) := by
  obtain ⟨k, hk, hp⟩ := DAState.exists_proposal_before_of_rank_lt_count p (n * n) _ _
    (DAState.matching_symm_mem_proposedCells p w)
  have hc := DAState.proposalCount_run_eq_of_active p k (by simp [hp])
  have hm := DAState.proposalCount_run_mono p (Nat.succ_le_of_lt hk)
  change (DAState.advance p (DAState.run p k)).proposalCount ≤ _ at hm
  rw [DAState.proposalCount_advance_of_some hp, hc] at hm
  exact ⟨k, Nat.lt_of_succ_le hm, hp⟩
private def daLowProposalEvent (k : ℕ) (u : ℝ) (c : Fin n × Fin n) : Set (ScoreProfile n) :=
  daProposalEvent k c ∩ {x | x (.inr c.2) c.1 ≤ u}
private theorem measurableSet_daLowProposalEvent (k : ℕ) (u : ℝ) (c : Fin n × Fin n) :
    MeasurableSet (daLowProposalEvent k u c) :=
  (measurableSet_daProposalEvent k c).inter
    (measurableSet_le ((measurable_pi_apply c.1).comp
      (measurable_pi_apply (Sum.inr c.2 : Fin n ⊕ Fin n)))
      measurable_const)
private theorem unitScoreLaw_Iic_le_ofReal (u : ℝ) :
    unitScoreLaw (Iic u) ≤ ENNReal.ofReal u := by
  rw [unitScoreLaw, Measure.restrict_apply measurableSet_Iic]
  have hsub : Iic u ∩ Icc (0 : ℝ) 1 ⊆ Icc 0 u := fun _ hx ↦ ⟨hx.2.1, hx.1⟩
  simpa only [Real.volume_Icc, sub_zero] using (measure_mono (μ := volume) hsub)
private theorem sum_measure_daProposalEvent_le_one (k : ℕ) :
    ∑ c : Fin n × Fin n, continuousScoreLaw n (daProposalEvent k c) ≤ 1 := by
  have hd : Pairwise (fun c d : Fin n × Fin n ↦
      Disjoint (daProposalEvent k c) (daProposalEvent k d)) := by
    intro c d hne
    refine Set.disjoint_left.mpr fun x hc hd ↦ hne ?_
    exact Option.some.inj (hc.symm.trans hd)
  rw [← tsum_fintype (L := SummationFilter.unconditional (Fin n × Fin n)),
    ← measure_iUnion hd (measurableSet_daProposalEvent k)]
  exact (measure_mono (subset_univ _)).trans_eq measure_univ
private theorem sum_measure_daLowProposalEvent_le (k : ℕ) (u : ℝ) :
    ∑ c : Fin n × Fin n, continuousScoreLaw n (daLowProposalEvent k u c) ≤
      ENNReal.ofReal u := by
  have h c : continuousScoreLaw n (daLowProposalEvent k u c) =
      continuousScoreLaw n (daProposalEvent k c) * unitScoreLaw (Iic u) :=
    measure_daProposalEvent_inter_score k c measurableSet_Iic
  simp_rw [h, ← Finset.sum_mul]
  exact (mul_le_mul' (sum_measure_daProposalEvent_le_one k) (unitScoreLaw_Iic_le_ofReal u)).trans
    (one_mul _).le
private noncomputable def daLowProposalCount (T : ℕ) (u : ℝ) (x : ScoreProfile n) : ℝ≥0∞ :=
  (Finset.univ.filter fun a : Fin T × (Fin n × Fin n) ↦
    x ∈ daLowProposalEvent a.1.val u a.2).card
private theorem daLowProposalCount_eq_sum (T : ℕ) (u : ℝ) (x : ScoreProfile n) :
    daLowProposalCount T u x = ∑ a : Fin T × (Fin n × Fin n),
      (daLowProposalEvent a.1.val u a.2).indicator 1 x := by
  simp [daLowProposalCount, Set.indicator]
theorem measurable_daLowProposalCount (T : ℕ) (u : ℝ) :
    Measurable (daLowProposalCount (n := n) T u) := by
  simp_rw [show daLowProposalCount (n := n) T u = _ from funext (daLowProposalCount_eq_sum T u)]
  exact Finset.measurable_sum _ fun a _ ↦ measurable_const.indicator
    (measurableSet_daLowProposalEvent a.1.val u a.2)
theorem lintegral_daLowProposalCount_le (T : ℕ) (u : ℝ) :
    (∫⁻ x, daLowProposalCount T u x ∂continuousScoreLaw n) ≤
      (T : ℝ≥0∞) * ENNReal.ofReal u := by
  simp_rw [daLowProposalCount_eq_sum]
  rw [lintegral_finsetSum _ (f := fun a : Fin T × (Fin n × Fin n) ↦
    (daLowProposalEvent a.1.val u a.2).indicator 1) (fun a _ ↦ measurable_const.indicator
    (measurableSet_daLowProposalEvent a.1.val u a.2))]
  simp_rw [lintegral_indicator_one (measurableSet_daLowProposalEvent _ _ _)]
  rw [Fintype.sum_prod_type]
  calc
    _ ≤ ∑ _ : Fin T, ENNReal.ofReal u :=
      Finset.sum_le_sum fun a _ ↦ sum_measure_daLowProposalEvent_le a.val u
    _ = _ := by simp [nsmul_eq_mul]
private theorem card_low_spouse_le_daLowProposalCount (T : ℕ) (u : ℝ) (x : ScoreProfile n)
    (hcap : (DAState.run (profileOfScores x) (n * n)).proposalCount ≤ T) :
    ((Finset.univ.filter fun w : Fin n ↦
      femaleSpouseScore x (DAState.matching (profileOfScores x)) w ≤ u).card : ℝ≥0∞) ≤
      daLowProposalCount T u x := by
  let p := profileOfScores x
  have hex (w : Fin n) : ∃ k : Fin T,
      (DAState.run p k.val).nextProposal p.manRank = some ((DAState.matching p).symm w, w) := by
    obtain ⟨k, hk, hp⟩ := DAState.exists_nextProposal_final_pair p w
    exact ⟨⟨k, hk.trans_le hcap⟩, hp⟩
  choose f hf using hex
  unfold daLowProposalCount
  apply Nat.cast_le.mpr
  apply Finset.card_le_card_of_injOn (fun w ↦ (f w, (DAState.matching p).symm w, w))
  · intro w hw
    change w ∈ Finset.univ.filter (fun w ↦ femaleSpouseScore x (DAState.matching p) w ≤ u) at hw
    have hs := (Finset.mem_filter.mp hw).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf w, hs⟩
  · intro a _ b _ hab
    exact congrArg (fun v : Fin T × (Fin n × Fin n) ↦ v.2.2) hab
private theorem half_le_card_low_of_sum_le (a : Fin n → ℝ) (ha : ∀ j, 0 ≤ a j)
    (u : ℝ) (hu : 0 < u) (hsmall : ∑ j, a j ≤ u * ((n : ℝ) / 2)) :
    (n : ℝ) / 2 ≤ ((Finset.univ.filter fun w ↦ a w ≤ u).card : ℝ) := by
  let lo := Finset.univ.filter fun w ↦ a w ≤ u
  let hi := Finset.univ.filter fun w ↦ ¬ a w ≤ u
  have hcard : lo.card + hi.card = n := by
    simpa only [lo, hi, Finset.card_univ, Fintype.card_fin] using
      Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun w ↦ a w ≤ u)
  have hsum : (hi.card : ℝ) * u ≤ ∑ j, a j := by
    calc
      _ = ∑ _ ∈ hi, u := by simp [nsmul_eq_mul]
      _ ≤ ∑ j ∈ hi, a j := Finset.sum_le_sum fun j hj ↦
        le_of_lt (lt_of_not_ge (Finset.mem_filter.mp hj).2)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ hi)
        (fun j _ _ ↦ ha j)
  have hhi : (hi.card : ℝ) ≤ (n : ℝ) / 2 :=
    (mul_le_mul_iff_left₀ hu).mp (by simpa only [mul_comm u ((n : ℝ) / 2)] using hsum.trans hsmall)
  have hcast : (lo.card : ℝ) + (hi.card : ℝ) = n := by exact_mod_cast hcard
  change (n : ℝ) / 2 ≤ (lo.card : ℝ)
  linarith
theorem measure_badManOptimalScore_inter_proposalCap_le {T : ℕ} {u : ℝ}
    (hn : 0 < n) (hu : 0 < u) :
    continuousScoreLaw n {x |
      femaleSpouseTotal x (DAState.matching (profileOfScores x)) ≤ u * ((n : ℝ) / 2) ∧
      (DAState.run (profileOfScores x) (n * n)).proposalCount ≤ T} ≤
      (T : ℝ≥0∞) * ENNReal.ofReal u / ENNReal.ofReal ((n : ℝ) / 2) := by
  have hpos : 0 < (n : ℝ) / 2 := by positivity
  have hsub : ∀ᵐ x ∂continuousScoreLaw n,
      (femaleSpouseTotal x (DAState.matching (profileOfScores x)) ≤ u * ((n : ℝ) / 2) ∧
      (DAState.run (profileOfScores x) (n * n)).proposalCount ≤ T) →
      ENNReal.ofReal ((n : ℝ) / 2) ≤ daLowProposalCount T u x := by
    filter_upwards [ae_unitOpen_scores n] with x hx hh
    have hhalf := half_le_card_low_of_sum_le
      (femaleSpouseScore x (DAState.matching (profileOfScores x)))
      (fun j ↦ (hx (.inr j) ((DAState.matching (profileOfScores x)).symm j)).1.le) u hu hh.1
    have hcast := ENNReal.ofReal_le_ofReal hhalf
    rw [ENNReal.ofReal_natCast] at hcast
    exact hcast.trans (card_low_spouse_le_daLowProposalCount T u x hh.2)
  refine (measure_mono_ae hsub).trans
    ((meas_ge_le_lintegral_div (measurable_daLowProposalCount T u).aemeasurable
      (ENNReal.ofReal_pos.mpr hpos).ne' ENNReal.ofReal_ne_top).trans ?_)
  exact ENNReal.div_le_div_right (lintegral_daLowProposalCount_le T u) _
theorem tendsto_measure_badManOptimalScore_of_proposalCap {C : ℝ} (T : ℕ → ℕ)
    (hT : ∀ᶠ n : ℕ in atTop, (T n : ℝ) ≤ C * n * Real.log n)
    (hcap : Tendsto (fun n ↦ continuousScoreLaw n {x |
      T n < (DAState.run (profileOfScores x) (n * n)).proposalCount}) atTop (𝓝 0)) :
    Tendsto (fun n ↦ continuousScoreLaw n {x |
      femaleSpouseTotal x (DAState.matching (profileOfScores x)) ≤ (n : ℝ) ^ (2 / 5 : ℝ)})
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log n / (n : ℝ) ^ (3 / 5 : ℝ)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 5)).tendsto_div_nhds_zero.comp
      tendsto_natCast_atTop_atTop
  have hdecay : Tendsto (fun n : ℕ ↦ ENNReal.ofReal
      (4 * C * (Real.log n / (n : ℝ) ^ (3 / 5 : ℝ)))) atTop (𝓝 0) := by
    simpa only [mul_zero, ENNReal.ofReal_zero, Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp (tendsto_const_nhds.mul hlog)
  have hsum : Tendsto (fun n ↦ continuousScoreLaw n {x |
      T n < (DAState.run (profileOfScores x) (n * n)).proposalCount} +
      ENNReal.ofReal (4 * C * (Real.log n / (n : ℝ) ^ (3 / 5 : ℝ)))) atTop (𝓝 0) := by
    simpa only [add_zero] using hcap.add hdecay
  refine tendsto_const_nhds.squeeze' hsum (Eventually.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [hT, eventually_gt_atTop (0 : ℕ)] with n hTn hn
  let u : ℝ := 2 * (n : ℝ) ^ (2 / 5 : ℝ) / n
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hu : 0 < u := by dsimp [u]; positivity
  have hscale : u * ((n : ℝ) / 2) = (n : ℝ) ^ (2 / 5 : ℝ) := by
    dsimp [u]
    field_simp
  have hmark := measure_badManOptimalScore_inter_proposalCap_le (T := T n) hn hu
  rw [hscale] at hmark
  let B : Set (ScoreProfile n) := {x |
    femaleSpouseTotal x (DAState.matching (profileOfScores x)) ≤ (n : ℝ) ^ (2 / 5 : ℝ)}
  let E : Set (ScoreProfile n) :=
    {x | T n < (DAState.run (profileOfScores x) (n * n)).proposalCount}
  let G : Set (ScoreProfile n) := {x |
    femaleSpouseTotal x (DAState.matching (profileOfScores x)) ≤ (n : ℝ) ^ (2 / 5 : ℝ) ∧
    (DAState.run (profileOfScores x) (n * n)).proposalCount ≤ T n}
  have hsub : B ⊆ E ∪ G := by
    intro x hx
    by_cases h : x ∈ E
    · exact Or.inl h
    · exact Or.inr ⟨hx, le_of_not_gt h⟩
  change continuousScoreLaw n B ≤ continuousScoreLaw n E + _
  calc
    _ ≤ continuousScoreLaw n (E ∪ G) := measure_mono hsub
    _ ≤ continuousScoreLaw n E + continuousScoreLaw n G := measure_union_le E G
    _ ≤ continuousScoreLaw n E + ((T n : ℝ≥0∞) * ENNReal.ofReal u /
        ENNReal.ofReal ((n : ℝ) / 2)) := add_le_add_right hmark _
    _ ≤ _ := by
      apply add_le_add_right
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg (T n)),
        ← ENNReal.ofReal_div_of_pos (by positivity : 0 < (n : ℝ) / 2)]
      apply ENNReal.ofReal_le_ofReal
      apply (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hTn hu.le) (by positivity)).trans
      apply le_of_eq
      have hpow : (n : ℝ) ^ (3 / 5 : ℝ) = (n : ℝ) / (n : ℝ) ^ (2 / 5 : ℝ) := by
        rw [show (3 / 5 : ℝ) = 1 - 2 / 5 by norm_num, Real.rpow_sub hn', Real.rpow_one]
      rw [hpow]
      dsimp [u]
      field_simp
      norm_num
end StepA4
end

-- ExponentialSpouseLogTail
section
open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal Topology
namespace StepA4
local instance : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
  isProbabilityMeasure_expMeasure (by norm_num)
private noncomputable def spouseAngularLogExcess {n : ℕ} (p : Fin n → ℝ) : ℝ :=
  ∑ i, -Real.log ((n : ℝ) * p i)
theorem measurable_spouseAngularLogExcess (n : ℕ) :
    Measurable (@spouseAngularLogExcess n) := by
  unfold spouseAngularLogExcess
  fun_prop
theorem spouseAngularLogExcess_spouseAngle {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) (hx : ∀ i, 0 < x i) :
    spouseAngularLogExcess (spouseAngle x) =
      (n : ℝ) * Real.log ((∑ i, x i) / n) - ∑ i, Real.log (x i) := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hT : 0 < ∑ i, x i := by
    have i : Fin n := ⟨0, hn⟩
    exact Finset.sum_pos (fun j _ ↦ hx j) ⟨i, Finset.mem_univ i⟩
  unfold spouseAngularLogExcess
  calc
    _ = ∑ i, (Real.log ((∑ j, x j) / n) - Real.log (x i)) := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [spouseAngle, Real.log_mul hn'.ne' (div_pos (hx i) hT).ne',
        Real.log_div (hx i).ne' hT.ne', Real.log_div hT.ne' hn'.ne']
      ring
    _ = _ := by
      rw [Finset.sum_sub_distrib]
      simp
private theorem ae_expMeasure_one_pos : ∀ᵐ x ∂expMeasure 1, 0 < x := by
  have hvol : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by simp [ae_iff]
  have hne : ∀ᵐ x ∂expMeasure 1, x ≠ 0 :=
    (withDensity_absolutelyContinuous volume (exponentialPDF 1)).ae_le hvol
  filter_upwards [ae_expMeasure_one_nonneg, hne] with x hx hnx
  exact lt_of_le_of_ne hx (Ne.symm hnx)
private theorem lintegral_expMeasure_one_density (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ∂expMeasure 1) = ∫⁻ x, exponentialPDF 1 x * f x :=
  lintegral_withDensity_eq_lintegral_mul volume
    (measurable_exponentialPDFReal 1).ennreal_ofReal hf
private theorem lintegral_expMeasure_one_exp_half :
    (∫⁻ x, ENNReal.ofReal (Real.exp (x / 2)) ∂expMeasure 1) = ENNReal.ofReal 2 := by
  rw [lintegral_expMeasure_one_density _ (by fun_prop)]
  have h (x : ℝ) :
      exponentialPDF 1 x * ENNReal.ofReal (Real.exp (x / 2)) =
        ENNReal.ofReal 2 * exponentialPDF (1 / 2) x := by
    by_cases hx : 0 ≤ x
    · rw [exponentialPDF_of_nonneg hx, exponentialPDF_of_nonneg hx,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ))]
      congr 1
      simp only [one_mul, ← Real.exp_add]
      rw [show -x + x / 2 = -(1 / 2 * x) by ring]
      ring
    · rw [exponentialPDF_of_neg (lt_of_not_ge hx), exponentialPDF_of_neg (lt_of_not_ge hx),
        zero_mul, mul_zero]
  simp_rw [h]
  have he : Measurable (exponentialPDF (1 / 2)) :=
    (measurable_exponentialPDFReal _).ennreal_ofReal
  rw [lintegral_const_mul _ he,
    lintegral_exponentialPDF_eq_one (by norm_num), mul_one]
private theorem lintegral_expMeasure_one_neg_half_rpow :
    (∫⁻ x, ENNReal.ofReal (x ^ (-1 / 2 : ℝ)) ∂expMeasure 1) =
      ENNReal.ofReal (Real.Gamma (1 / 2)) := by
  rw [lintegral_expMeasure_one_density _ (by fun_prop)]
  have hΓ := Real.Gamma_pos_of_pos (by norm_num : 0 < (1 / 2 : ℝ))
  have h (x : ℝ) :
      exponentialPDF 1 x * ENNReal.ofReal (x ^ (-1 / 2 : ℝ)) =
        ENNReal.ofReal (Real.Gamma (1 / 2)) * gammaPDF (1 / 2) 1 x := by
    by_cases hx : 0 ≤ x
    · rw [exponentialPDF_of_nonneg hx, gammaPDF_of_nonneg hx,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hΓ.le]
      congr 1
      rw [show (1 / 2 : ℝ) - 1 = -1 / 2 by norm_num]
      simp only [Real.one_rpow, one_mul]
      field_simp
    · rw [exponentialPDF_of_neg (lt_of_not_ge hx), gammaPDF_of_neg (lt_of_not_ge hx),
        zero_mul, mul_zero]
  simp_rw [h]
  have hγ : Measurable (gammaPDF (1 / 2) 1) :=
    (measurable_gammaPDFReal _ _).ennreal_ofReal
  rw [lintegral_const_mul _ hγ,
    lintegral_gammaPDF_eq_one (by norm_num) (by norm_num), mul_one]
private theorem lintegral_expMeasure_one_exp_neg_log_half_le :
    (∫⁻ x, ENNReal.ofReal (Real.exp (-Real.log x / 2)) ∂expMeasure 1) ≤ ENNReal.ofReal 2 := by
  have h : (fun x : ℝ ↦ ENNReal.ofReal (Real.exp (-Real.log x / 2))) =ᵐ[expMeasure 1]
      (fun x ↦ ENNReal.ofReal (x ^ (-1 / 2 : ℝ))) := by
    filter_upwards [ae_expMeasure_one_pos] with x hx
    rw [Real.rpow_def_of_pos hx]
    congr 2
    ring
  rw [lintegral_congr_ae h, lintegral_expMeasure_one_neg_half_rpow, Real.Gamma_one_half_eq]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ Real.sqrt 4 := Real.sqrt_le_sqrt Real.pi_lt_four.le
    _ = _ := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
private theorem measure_iidExponential_sum_gt_le (n : ℕ)
    {g : ℝ → ℝ} (hg : Measurable g) (a : ℝ) {m : ℝ} (hm : 0 ≤ m)
    (hmg : (∫⁻ x, ENNReal.ofReal (Real.exp (g x)) ∂expMeasure 1) ≤ ENNReal.ofReal m) :
    iidExponentialScoreLaw n {x | a * (n : ℝ) < ∑ i, g (x i)} ≤
      ENNReal.ofReal ((Real.exp (-a) * m) ^ n) := by
  let ν (i : Fin n) := expMeasure (1 : ℝ)
  let f (t : ℝ) := ENNReal.ofReal (Real.exp (g t))
  let F (x : Fin n → ℝ) := ENNReal.ofReal (Real.exp (-a * (n : ℝ) + ∑ i, g (x i)))
  have hf : Measurable f := by unfold f; fun_prop
  have hF : Measurable F := by unfold F; fun_prop
  have hcoord (i : Fin n) : Measurable (fun x : Fin n → ℝ ↦ f (x i)) :=
    hf.comp (measurable_pi_apply i)
  have hfactor (x : Fin n → ℝ) :
      F x = ENNReal.ofReal (Real.exp (-a * (n : ℝ))) * ∏ i, f (x i) := by
    unfold F f
    rw [Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le, Real.exp_sum,
      ENNReal.ofReal_prod_of_nonneg (fun _ _ ↦ (Real.exp_pos _).le)]
  have hrow (i : Fin n) : (∫⁻ x : Fin n → ℝ, f (x i) ∂Measure.pi ν) ≤ ENNReal.ofReal m := by
    rw [(measurePreserving_eval ν i).lintegral_comp hf]
    exact hmg
  change (Measure.pi ν) _ ≤ _
  calc
    _ ≤ ∫⁻ x, F x ∂Measure.pi ν := by
      apply meas_le_lintegral₀ hF.aemeasurable
      intro x hx
      change a * (n : ℝ) < ∑ i, g (x i) at hx
      have h : 0 ≤ -a * (n : ℝ) + ∑ i, g (x i) := by linarith only [hx]
      simpa only [F, Real.exp_zero, ENNReal.ofReal_one] using
        ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr h)
    _ ≤ ENNReal.ofReal (Real.exp (-a * (n : ℝ))) * ENNReal.ofReal m ^ n := by
      simp_rw [hfactor]
      rw [lintegral_const_mul _ (Finset.univ.measurable_prod fun i _ ↦ hcoord i),
        lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ _
          (iIndepFun_pi fun _ ↦ hf.aemeasurable) hcoord]
      apply mul_le_mul_right
      exact (Finset.prod_le_prod' fun i _ ↦ hrow i).trans_eq (by simp)
    _ = _ := by
      rw [← ENNReal.ofReal_pow hm, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
      congr 1
      rw [mul_comm (-a), Real.exp_nat_mul, mul_pow]
private noncomputable def logTailFactor : ℝ := Real.exp (-1) * 2
private theorem logTailFactor_pos : 0 < logTailFactor := by
  unfold logTailFactor
  positivity
private theorem logTailFactor_lt_one : logTailFactor < 1 := by
  unfold logTailFactor
  rw [Real.exp_neg, inv_mul_lt_iff₀ (Real.exp_pos _), mul_one]
  exact Real.exp_one_gt_two
private theorem measure_iidExponential_radius_gt_le (n : ℕ) :
    iidExponentialScoreLaw n {x | 2 * (n : ℝ) < ∑ i, x i} ≤
      ENNReal.ofReal (logTailFactor ^ n) := by
  have h (x : Fin n → ℝ) : 2 * (n : ℝ) < ∑ i, x i ↔
      1 * (n : ℝ) < ∑ i, x i / 2 := by
    rw [← Finset.sum_div, one_mul]
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 2), mul_comm (n : ℝ) (2 : ℝ)]
  simp_rw [h]
  exact measure_iidExponential_sum_gt_le n (g := fun x ↦ x / 2) (by fun_prop) 1
    (by norm_num) lintegral_expMeasure_one_exp_half.le
private theorem measure_iidExponential_neg_log_sum_gt_le (n : ℕ) :
    iidExponentialScoreLaw n {x | 4 * (n : ℝ) < ∑ i, -Real.log (x i)} ≤
      ENNReal.ofReal (logTailFactor ^ n) := by
  have h (x : Fin n → ℝ) : 4 * (n : ℝ) < ∑ i, -Real.log (x i) ↔
      2 * (n : ℝ) < ∑ i, -Real.log (x i) / 2 := by
    rw [← Finset.sum_div]
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    rw [show 2 * (n : ℝ) * 2 = 4 * (n : ℝ) by ring]
  simp_rw [h]
  refine (measure_iidExponential_sum_gt_le n (g := fun x ↦ -Real.log x / 2) (by fun_prop) 2
    (by norm_num) lintegral_expMeasure_one_exp_neg_log_half_le).trans ?_
  apply ENNReal.ofReal_le_ofReal
  apply pow_le_pow_left₀ (by positivity) _ n
  unfold logTailFactor
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by norm_num)) (by norm_num)
private theorem measure_iidExponential_spouseAngularLogExcess_gt_le {n : ℕ} (hn : 0 < n) :
    iidExponentialScoreLaw n {x | 6 * (n : ℝ) < spouseAngularLogExcess (spouseAngle x)} ≤
      ENNReal.ofReal (logTailFactor ^ n) + ENNReal.ofReal (logTailFactor ^ n) := by
  let ν (_ : Fin n) := expMeasure (1 : ℝ)
  have hae : ∀ᵐ x ∂iidExponentialScoreLaw n, ∀ i, 0 < x i :=
    ae_all_iff.2 fun i ↦
      (measurePreserving_eval ν i).quasiMeasurePreserving.ae ae_expMeasure_one_pos
  let A : Set (Fin n → ℝ) := {x | 2 * (n : ℝ) < ∑ i, x i}
  let B : Set (Fin n → ℝ) := {x | 4 * (n : ℝ) < ∑ i, -Real.log (x i)}
  let U : Set (Fin n → ℝ) := A ∪ B
  have hsub : {x | 6 * (n : ℝ) < spouseAngularLogExcess (spouseAngle x)}
      ≤ᵐ[iidExponentialScoreLaw n] U := by
    filter_upwards [hae] with x hx hbad
    by_cases hA : x ∈ A
    · exact Or.inl hA
    by_cases hB : x ∈ B
    · exact Or.inr hB
    exfalso
    have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
    have hT : 0 < ∑ i, x i :=
      Finset.sum_pos (fun j _ ↦ hx j) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    have hdiv : (∑ i, x i) / (n : ℝ) ≤ 2 :=
      (div_le_iff₀ hn').mpr (le_of_not_gt hA)
    have hlog : Real.log ((∑ i, x i) / (n : ℝ)) ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (div_pos hT hn')
      linarith only [h, hdiv]
    have hsum : -(∑ i, Real.log (x i)) ≤ 4 * (n : ℝ) := by
      rw [← Finset.sum_neg_distrib]
      exact le_of_not_gt hB
    change 6 * (n : ℝ) < spouseAngularLogExcess (spouseAngle x) at hbad
    rw [spouseAngularLogExcess_spouseAngle hn x hx] at hbad
    linarith only [hbad, hn', hsum, mul_le_mul_of_nonneg_left hlog hn'.le]
  exact (measure_mono_ae hsub).trans ((measure_union_le A B).trans
    (add_le_add (measure_iidExponential_radius_gt_le n)
      (measure_iidExponential_neg_log_sum_gt_le n)))
private theorem eventually_logTailFactor_le_neg_rpow (p : ℝ) :
    ∀ᶠ n : ℕ in atTop, logTailFactor ^ n ≤ (n : ℝ) ^ (-p) := by
  have hq : 0 < -Real.log logTailFactor :=
    neg_pos.mpr (Real.log_neg logTailFactor_pos logTailFactor_lt_one)
  have h := (((isLittleO_log_rpow_atTop (r := (1 : ℝ)) (by norm_num)).const_mul_left
    (p / -Real.log logTailFactor)).comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))).eventuallyLE
  filter_upwards [eventually_gt_atTop (0 : ℕ), h] with n hn hnlog
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have habs : |p / -Real.log logTailFactor * Real.log (n : ℝ)| ≤ |(n : ℝ) ^ (1 : ℝ)| := hnlog
  rw [Real.rpow_one, abs_of_nonneg hn'.le] at habs
  have hle : p * Real.log (n : ℝ) ≤ (n : ℝ) * -Real.log logTailFactor := by
    apply (div_le_iff₀ hq).mp
    rw [mul_div_right_comm]
    exact (le_abs_self _).trans habs
  rw [Real.rpow_def_of_pos hn', ← Real.exp_log logTailFactor_pos, ← Real.exp_nat_mul]
  exact Real.exp_le_exp.mpr (by linarith only [hle])
theorem eventually_measure_iidExponential_spouseAngularLogExcess_gt_le (p : ℝ) :
    ∀ᶠ n : ℕ in atTop, iidExponentialScoreLaw n
      {x | 6 * (n : ℝ) < spouseAngularLogExcess (spouseAngle x)} ≤
        ENNReal.ofReal ((n : ℝ) ^ (-p)) := by
  filter_upwards [eventually_ge_atTop (2 : ℕ),
    eventually_logTailFactor_le_neg_rpow (p + 1)] with n hn hq
  have hn' : 0 < n := by omega
  have hn₀ : 0 < (n : ℝ) := by exact_mod_cast hn'
  have hn₂ : 2 ≤ (n : ℝ) := by exact_mod_cast hn
  let a := (n : ℝ) ^ (-(p + 1))
  have ha : 0 ≤ a := Real.rpow_nonneg hn₀.le _
  refine (measure_iidExponential_spouseAngularLogExcess_gt_le hn').trans ?_
  refine (add_le_add (ENNReal.ofReal_le_ofReal hq) (ENNReal.ofReal_le_ofReal hq)).trans ?_
  rw [← ENNReal.ofReal_add ha ha]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ = 2 * a := by ring
    _ ≤ (n : ℝ) * a := mul_le_mul_of_nonneg_right hn₂ ha
    _ = _ := calc
      _ = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-(p + 1)) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hn₀, show (1 : ℝ) + -(p + 1) = -p by ring]
end StepA4
end

-- MarkedSpouseLogGeometry
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace StepA4
theorem spouseAngularLogExcess_nonneg_of_sum_eq_one {n : ℕ} (hn : 0 < n) {p : Fin n → ℝ}
    (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1) : 0 ≤ spouseAngularLogExcess p := by
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  unfold spouseAngularLogExcess
  calc
    _ = ∑ i : Fin n, (1 - (n : ℝ) * p i) := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsum]
      simp
    _ ≤ _ := Finset.sum_le_sum fun i _ ↦ by
      linarith only [Real.log_le_sub_one_of_pos (mul_pos hn' (hp i))]
theorem femaleLogPotential_eq_total_add_angular {n : ℕ} (hn : 0 < n)
    (x : ScoreProfile n) (μ : Matching n) (hx : ∀ j i, 0 < x (.inr j) i) :
    femaleLogPotential x μ =
      (n : ℝ) * Real.log ((n : ℝ) / femaleSpouseTotal x μ) +
        spouseAngularLogExcess (spouseAngle (femaleSpouseByHusband μ x)) := by
  let y := femaleSpouseByHusband μ x
  let Y := femaleSpouseTotal x μ
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hy (i : Fin n) : 0 < y i := hx _ _
  have hYsum : Y = ∑ i, y i := femaleSpouseTotal_eq_sum_byHusband μ x
  have hY : 0 < Y := by
    rw [hYsum]
    exact Finset.sum_pos (fun i _ ↦ hy i) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have ha (i : Fin n) : spouseAngle y i = y i / Y := by
    unfold spouseAngle
    rw [← hYsum]
  have heq (i : Fin n) : -Real.log (y i) =
      Real.log ((n : ℝ) / Y) - Real.log ((n : ℝ) * spouseAngle y i) := by
    rw [ha, Real.log_mul hn'.ne' (div_pos (hy i) hY).ne',
      Real.log_div hn'.ne' hY.ne', Real.log_div (hy i).ne' hY.ne']
    ring
  calc
    _ = ∑ i, -Real.log (y i) :=
      (Equiv.sum_comp μ fun j ↦ -Real.log (femaleSpouseScore x μ j)).symm
    _ = ∑ i, (Real.log ((n : ℝ) / Y) - Real.log ((n : ℝ) * spouseAngle y i)) :=
      Finset.sum_congr rfl fun i _ ↦ heq i
    _ = _ := by
      simp only [spouseAngularLogExcess, Y, y, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      exact sub_eq_add_neg _ _
theorem femaleLogPotential_lower {n : ℕ} (hn : 0 < n)
    (x : ScoreProfile n) (μ : Matching n) (hx : ∀ j i, 0 < x (.inr j) i) :
    (n : ℝ) * Real.log ((n : ℝ) / femaleSpouseTotal x μ) ≤ femaleLogPotential x μ := by
  let y := femaleSpouseByHusband μ x
  have hy (i : Fin n) : 0 < y i := hx _ _
  have hY : 0 < ∑ i, y i :=
    Finset.sum_pos (fun i _ ↦ hy i) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hp (i : Fin n) : 0 < spouseAngle y i := div_pos (hy i) hY
  have hsum : ∑ i, spouseAngle y i = 1 := by
    unfold spouseAngle
    rw [← Finset.sum_div, div_self hY.ne']
  rw [femaleLogPotential_eq_total_add_angular hn x μ hx]
  exact le_add_of_nonneg_right (spouseAngularLogExcess_nonneg_of_sum_eq_one hn hp hsum)
theorem eventually_sum_measure_scoreStable_femaleAngularException_le
    (A : (n : ℕ) → Set (Fin n → ℝ)) (hA : ∀ n, MeasurableSet (A n))
    (htail : ∀ q : ℝ, ∀ᶠ n : ℕ in atTop, spouseAngularLaw n (A n) ≤
      ENNReal.ofReal ((n : ℝ) ^ (-q))) (q : ℝ) :
    ∀ᶠ n : ℕ in atTop, (∑ μ : Matching n, continuousScoreLaw n
      {x | IsScoreStable x μ ∧ spouseAngle (femaleSpouseByHusband μ x) ∈ A n}) ≤
        ENNReal.ofReal ((n : ℝ) ^ (-q)) := by
  have hL : ∀ᶠ n : ℕ in atTop, 2 ≤ (9 / 10 : ℝ) * Real.log n :=
    ((Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop
      (20 / 9)).mono fun n h ↦ by
        change (20 / 9 : ℝ) ≤ Real.log (n : ℝ) at h
        linarith only [h]
  have hC : ∀ᶠ n : ℕ in atTop, Real.exp 2 ≤ (n : ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop _
  filter_upwards [htail (q + 4), eventually_sum_stable_smallSpouseTotalLog_le (q + 1),
    hL, hC, eventually_ge_atTop (2 : ℕ)] with n ha hsmall hlogcut hC hn
  let E (μ : Matching n) : Set (ScoreProfile n) :=
    {x | IsScoreStable x μ ∧ femaleSpouseTotal x μ < (9 / 10 : ℝ) * Real.log n}
  let F (μ : Matching n) : Set (ScoreProfile n) :=
    {x | IsScoreStable x μ ∧ 2 ≤ femaleSpouseTotal x μ ∧
      spouseAngle (femaleSpouseByHusband μ x) ∈ A n}
  have hn₀ : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hn₂ : 2 ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog₀ : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith only [hn₂])
  have hlog : Real.log (n : ℝ) ≤ n :=
    (Real.log_le_sub_one_of_pos hn₀).trans (by linarith)
  have hcoef : Real.exp 2 * (n : ℝ) * Real.log n ≤ (n : ℝ) ^ (3 : ℕ) := by
    calc
      _ ≤ (n : ℝ) * n * Real.log n :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hn₀.le) hlog₀
      _ ≤ (n : ℝ) * n * n := mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = _ := by ring
  let a := (n : ℝ) ^ (-(q + 1))
  have ha₀ : 0 ≤ a := by unfold a; positivity
  have hF : (∑ μ : Matching n, continuousScoreLaw n (F μ)) ≤ ENNReal.ofReal a := by
    refine (sum_measure_scoreStable_and_femaleSpouseAngle_le hn (hA n)).trans ?_
    calc
      _ ≤ ENNReal.ofReal ((n : ℝ) ^ (3 : ℕ)) * ENNReal.ofReal ((n : ℝ) ^ (-(q + 4))) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal hcoef) ha
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity), ← Real.rpow_ofNat, ← Real.rpow_add hn₀]
        congr 2
        ring
  calc
    _ ≤ ∑ μ : Matching n, (continuousScoreLaw n (E μ) + continuousScoreLaw n (F μ)) := by
      apply Finset.sum_le_sum
      intro μ _
      refine (measure_mono ?_).trans (measure_union_le _ _)
      intro x hx
      by_cases hY : 2 ≤ femaleSpouseTotal x μ
      · exact Or.inr ⟨hx.1, hY, hx.2⟩
      · exact Or.inl ⟨hx.1, (lt_of_not_ge hY).trans_le hlogcut⟩
    _ ≤ ENNReal.ofReal a + ENNReal.ofReal a := by
      rw [Finset.sum_add_distrib]
      exact add_le_add hsmall hF
    _ ≤ _ := by
      rw [← ENNReal.ofReal_add ha₀ ha₀]
      apply ENNReal.ofReal_le_ofReal
      calc
        _ = 2 * a := (two_mul _).symm
        _ ≤ (n : ℝ) * a := mul_le_mul_of_nonneg_right hn₂ ha₀
        _ = _ := by
          unfold a
          calc
            _ = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-(q + 1)) := by rw [Real.rpow_one]
            _ = _ := by rw [← Real.rpow_add hn₀]; congr 1; ring
private def largeSpouseAngularLogSet (n : ℕ) : Set (Fin n → ℝ) :=
  {p | 6 * (n : ℝ) < spouseAngularLogExcess p}
theorem measurableSet_largeSpouseAngularLogSet (n : ℕ) :
    MeasurableSet (largeSpouseAngularLogSet n) :=
  measurableSet_lt measurable_const (measurable_spouseAngularLogExcess n)
theorem eventually_measure_spouseAngularLogExcess_gt_le (q : ℝ) :
    ∀ᶠ n : ℕ in atTop, spouseAngularLaw n (largeSpouseAngularLogSet n) ≤
      ENNReal.ofReal ((n : ℝ) ^ (-q)) := by
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    eventually_measure_iidExponential_spouseAngularLogExcess_gt_le q] with n hn h
  rw [← map_spouseAngle_pi_expMeasure_one hn,
    Measure.map_apply (measurable_spouseAngle n) (measurableSet_largeSpouseAngularLogSet n)]
  exact h
private def HasFemaleLogGeometry {n : ℕ} (x : ScoreProfile n) (μ : Matching n) : Prop :=
  (n : ℝ) * Real.log ((n : ℝ) / femaleSpouseTotal x μ) ≤ femaleLogPotential x μ ∧
    femaleLogPotential x μ ≤
      (n : ℝ) * Real.log ((n : ℝ) / femaleSpouseTotal x μ) + 6 * n
private def goodFemaleLogGeometry (n : ℕ) : Set (ScoreProfile n) :=
  {x | ∀ μ : Matching n, IsStable (profileOfScores x) μ → HasFemaleLogGeometry x μ}
theorem eventually_measure_badFemaleLogGeometry_le (q : ℝ) :
    ∀ᶠ n : ℕ in atTop, continuousScoreLaw n (goodFemaleLogGeometry n)ᶜ ≤
      ENNReal.ofReal ((n : ℝ) ^ (-q)) := by
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    eventually_sum_measure_scoreStable_femaleAngularException_le largeSpouseAngularLogSet
      measurableSet_largeSpouseAngularLogSet eventually_measure_spouseAngularLogExcess_gt_le q]
    with n hn he
  let B (μ : Matching n) : Set (ScoreProfile n) :=
    {x | IsScoreStable x μ ∧
      spouseAngle (femaleSpouseByHusband μ x) ∈ largeSpouseAngularLogSet n}
  have hsub : (goodFemaleLogGeometry n)ᶜ ≤ᵐ[continuousScoreLaw n] ⋃ μ, B μ := by
    filter_upwards [ae_injective_rows n, ae_unitOpen_scores n] with x hties hu hbad
    by_contra hnB
    apply hbad
    intro μ hμ
    have hμ' := (isStable_profileOfScores_iff hties μ).mp hμ
    have hx (j i : Fin n) : 0 < x (.inr j) i := (hu (.inr j) i).1
    have hupper : spouseAngularLogExcess (spouseAngle (femaleSpouseByHusband μ x)) ≤
        6 * (n : ℝ) :=
      le_of_not_gt fun h ↦ hnB (mem_iUnion.mpr ⟨μ, hμ', h⟩)
    exact ⟨femaleLogPotential_lower hn x μ hx, by
      rw [femaleLogPotential_eq_total_add_angular hn x μ hx]
      exact add_le_add_right hupper _⟩
  refine (measure_mono_ae hsub).trans ((measure_iUnion_le _).trans ?_)
  rwa [tsum_fintype]
end StepA4
end

-- CycleSupportCount
section
open Equiv.Perm Finset
open scoped BigOperators Classical
namespace StepA4
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
end StepA4
end

-- PointedSymmetricSums
section
open Finset
open scoped BigOperators
namespace StepA4
end StepA4
end

-- SingletonGaussianLength
section
open scoped BigOperators
open Finset
namespace StepA4
end StepA4
end

-- PivotSingletonLength
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA4
end StepA4
end

-- SingletonAnchorCounting
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal StepA4
namespace StepA4
variable {n : ℕ} {p : Profile n} {μ₀ : Matching n}
end StepA4
end

-- ForwardRowDeficitConcentration
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace StepA4
end StepA4
end

-- MarkedForwardRowDeficit
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace StepA4
end StepA4
end

-- SingletonDiagonalExceptions
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace StepA4
end StepA4
end

-- PivotSingletonMarkedLength
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA4
end StepA4
end

-- RotationLengthCutoff
section
open Filter MeasureTheory Set StableMarriage
open scoped ENNReal StepA4 Topology
namespace StepA4
end StepA4
end

-- RotationClockBand
section
open Filter MeasureTheory StableMarriage
open scoped ENNReal Topology
namespace StepA4
end StepA4
end

-- ScoreRotationHistory
section
open StableMarriage
open scoped Classical
namespace StepA4
variable {n : ℕ}
private theorem scoreRotationWalk_eq_nil_of_acyclic (x : ScoreProfile n) (μ : Matching n)
    (h : chooseQueriedRotation (scoreRotationGraph x μ) = none) (k : ℕ) :
    scoreRotationWalk x k μ = ([], μ) := by
  cases k with
  | zero => rfl
  | succ k => rw [scoreRotationWalk_succ, h]
theorem scoreRotationWalk_add (x : ScoreProfile n) (j k : ℕ) (ν : Matching n) :
    scoreRotationWalk x (j + k) ν =
      let a := scoreRotationWalk x j ν
      let b := scoreRotationWalk x k a.2
      (a.1 ++ b.1, b.2) := by
  induction j generalizing ν with
  | zero => simp only [Nat.zero_add, scoreRotationWalk_zero, scoreRotationWalk_succ, List.nil_append, Prod.eta]
  | succ j ih =>
    rw [Nat.succ_add, scoreRotationWalk_succ, scoreRotationWalk_succ]
    cases hc : chooseQueriedRotation (scoreRotationGraph x ν) with
    | none => simp only [scoreRotationWalk_eq_nil_of_acyclic x ν hc, List.nil_append]
    | some ρ =>
      change (ρ :: (scoreRotationWalk x (j + k) (eliminateRotation ν ρ)).1,
        (scoreRotationWalk x (j + k) (eliminateRotation ν ρ)).2) = _
      rw [ih]
      rfl
private noncomputable def scoreWalkClock (x : ScoreProfile n) (k : ℕ) : ℝ :=
  let start := DAState.matching (profileOfScores x)
  let out := scoreRotationWalk x k start
  femaleLogPotential x out.2 - femaleLogPotential x start - (rotationParticipation out.1 : ℝ)
theorem scoreWalkClock_succ_sub (x : ScoreProfile n) (k : ℕ)
    (hx : ∀ j i, 0 < x (.inr j) i) :
    let μ := (scoreRotationWalk x k (DAState.matching (profileOfScores x))).2
    scoreWalkClock x (k + 1) - scoreWalkClock x k =
      match chooseQueriedRotation (scoreRotationGraph x μ) with
      | none => 0
      | some ρ => centeredCacheLogIncrement (rotationClockUpper μ ρ)
          (splitRotationClockCells μ ρ x) := by
  let start := DAState.matching (profileOfScores x)
  let out := scoreRotationWalk x k start
  let μ := out.2
  change scoreWalkClock x (k + 1) - scoreWalkClock x k = _
  unfold scoreWalkClock
  change femaleLogPotential x (scoreRotationWalk x (k + 1) start).2 -
      femaleLogPotential x start - (rotationParticipation (scoreRotationWalk x (k + 1) start).1 :
      ℝ) - (femaleLogPotential x μ - femaleLogPotential x start -
      (rotationParticipation out.1 : ℝ)) = _
  rw [scoreRotationWalk_add x k 1 start]
  change (let b := scoreRotationWalk x 1 μ
    femaleLogPotential x b.2 - femaleLogPotential x start -
      (rotationParticipation (out.1 ++ b.1) : ℝ)) -
      (femaleLogPotential x μ - femaleLogPotential x start -
        (rotationParticipation out.1 : ℝ)) =
    match chooseQueriedRotation (scoreRotationGraph x μ) with
    | none => 0
    | some ρ => centeredCacheLogIncrement (rotationClockUpper μ ρ)
        (splitRotationClockCells μ ρ x)
  rw [scoreRotationWalk_succ]
  cases h : chooseQueriedRotation (scoreRotationGraph x μ) with
  | none => simp only [List.append_nil, sub_self]
  | some ρ =>
    have hpart : rotationParticipation (out.1 ++ [ρ]) =
        rotationParticipation out.1 + ρ.support.card := by
      simp [rotationParticipation]
    change femaleLogPotential x (eliminateRotation μ ρ) - femaleLogPotential x start -
      (rotationParticipation (out.1 ++ [ρ]) : ℝ) -
        (femaleLogPotential x μ - femaleLogPotential x start -
          (rotationParticipation out.1 : ℝ)) =
      centeredCacheLogIncrement (rotationClockUpper μ ρ) (splitRotationClockCells μ ρ x)
    rw [hpart, Nat.cast_add, centeredCacheLogIncrement_splitRotationClockCells x μ ρ hx]
    ring
theorem scoreWalkClock_history_eq_of_replace_selected {x y : ScoreProfile n} (k : ℕ)
    (hx : ∀ j, Function.Injective (x (.inr j))) (hy : ∀ j, Function.Injective (y (.inr j)))
    {ρ : Equiv.Perm (Fin n)}
    (hρ : IsExposedRotation (profileOfScores x)
      (scoreRotationWalk x k (DAState.matching (profileOfScores x))).2 ρ)
    (hfixed : ∀ r i, ¬IsRotationClockCell
      (scoreRotationWalk x k (DAState.matching (profileOfScores x))).2 ρ (r, i) →
      y r i = x r i)
    (hbelow : ∀ m ∈ ρ.support,
      let μ := (scoreRotationWalk x k (DAState.matching (profileOfScores x))).2
      y (rotationClockCell μ ρ m).1 (rotationClockCell μ ρ m).2 <
        femaleSpouseScore x μ (eliminateRotation μ ρ m)) :
    ∀ j ≤ k, scoreWalkClock y j = scoreWalkClock x j := by
  let start := DAState.matching (profileOfScores x)
  have hstart : IsStable (profileOfScores x) start :=
    (DAState.isManOptimal_matching (profileOfScores x)).1
  have hp := scoreRotationWalk_legal x hx k hstart
  have hda := da_matching_eq_of_replace_selected hp hρ hx hy hfixed
  have hpaths := scoreRotationWalk_eq_at_every_prefix k hx hstart hρ hfixed hbelow
  have hpotential (j : ℕ) (hj : j ≤ k) :
      femaleLogPotential y (scoreRotationWalk x j start).2 =
        femaleLogPotential x (scoreRotationWalk x j start).2 := by
    let prev := (scoreRotationWalk x j start).2
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hj
    have heq : (scoreRotationWalk x k start).2 = (scoreRotationWalk x d prev).2 := by
      rw [hd, scoreRotationWalk_add]
    have hseg : RotationSequence (profileOfScores x) prev (scoreRotationWalk x d prev).1
        (scoreRotationWalk x k start).2 :=
      heq ▸ scoreRotationWalk_legal x hx d (scoreRotationWalk_legal x hx j hstart).isStable_end
    unfold femaleLogPotential
    apply Finset.sum_congr rfl
    intro w _
    apply congrArg (fun z : ℝ ↦ -Real.log z)
    apply hfixed
    intro ⟨m, hm, he⟩
    apply hseg.rotationClockCell_ne_old_spouse hρ hm (prev.symm w)
    rw [Equiv.apply_symm_apply]
    exact he
  intro j hj
  unfold scoreWalkClock
  rw [hda]
  change femaleLogPotential y (scoreRotationWalk y j start).2 - femaleLogPotential y start -
      (rotationParticipation (scoreRotationWalk y j start).1 : ℝ) =
    femaleLogPotential x (scoreRotationWalk x j start).2 - femaleLogPotential x start -
      (rotationParticipation (scoreRotationWalk x j start).1 : ℝ)
  have hzero := hpotential 0 (Nat.zero_le k)
  change femaleLogPotential y start = femaleLogPotential x start at hzero
  rw [hpaths j hj, hpotential j hj, hzero]
end StepA4
end

-- ScoreRotationBandCrossing
section
open StableMarriage
open scoped BigOperators
namespace StepA4
variable {n : ℕ}
private noncomputable def scoreWalkMatching (x : ScoreProfile n) (k : ℕ) : Matching n :=
  (scoreRotationWalk x k (DAState.matching (profileOfScores x))).2
private noncomputable def scoreWalkFemaleTotal (x : ScoreProfile n) (k : ℕ) : ℝ :=
  femaleSpouseTotal x (scoreWalkMatching x k)
end StepA4
end

-- DAUpperEndpoint
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace StepA4
private noncomputable def daRankScoreThreshold (n k : ℕ) : ℝ :=
  16 * ((k : ℝ) + Real.log n) / n
private def badRankThresholdRow (n : ℕ) (k : Fin n) : Set (Fin n → ℝ) :=
  {y | (∑ j, if y j ≤ daRankScoreThreshold n (k.val + 1) then (1 : ℝ) else 0) < k.val + 1}
private theorem measurableSet_badRankThresholdRow (n : ℕ) (k : Fin n) :
    MeasurableSet (badRankThresholdRow n k) :=
  measurableSet_lt (Finset.measurable_sum _ fun j _ ↦
    Measurable.ite (measurableSet_le (measurable_pi_apply j) measurable_const)
      measurable_const measurable_const) measurable_const
private theorem unitScoreLaw_Iic {a : ℝ} (ha' : a ≤ 1) :
    unitScoreLaw (Iic a) = ENNReal.ofReal a := by
  rw [unitScoreLaw, Measure.restrict_apply measurableSet_Iic,
    show Iic a ∩ Icc 0 1 = Icc 0 a by
      ext x
      simp only [mem_inter_iff, mem_Iic, mem_Icc]
      exact ⟨fun h ↦ ⟨h.2.1, h.1⟩, fun h ↦ ⟨h.2, h.1, h.2.trans ha'⟩⟩,
    Real.volume_Icc, sub_zero]
private theorem measure_badRankThresholdRow_le {n : ℕ} (hn : 0 < n) (k : Fin n) :
    (Measure.pi fun _ : Fin n ↦ unitScoreLaw) (badRankThresholdRow n k) ≤
      ENNReal.ofReal (Real.exp (-4 * Real.log n)) := by
  let q := daRankScoreThreshold n (k.val + 1)
  let ν := Measure.pi fun _ : Fin n ↦ unitScoreLaw
  have hn₀ : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hq : 0 ≤ q := by
    unfold q daRankScoreThreshold
    positivity
  by_cases hq₁ : q ≤ 1
  · have hmass : ∀ _ : Fin n, ENNReal.ofReal q ≤ unitScoreLaw (Iic q) :=
      fun _ ↦ (unitScoreLaw_Iic hq₁).ge
    have htail := measure_pi_flagCount_lt_le_exp
      (fun _ : Fin n ↦ unitScoreLaw) (fun _ ↦ Iic q)
      (fun _ ↦ measurableSet_Iic) q ((k.val : ℝ) + 1) hq hmass
    refine htail.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_))
    rw [Fintype.card_fin]
    have hhalf : (1 / 2 : ℝ) ≤ 1 - Real.exp (-1) := by
      rw [Real.exp_neg, inv_eq_one_div]
      have h := Real.exp_one_gt_d9
      have h' : 1 / Real.exp 1 ≤ (1 / 2 : ℝ) :=
        one_div_le_one_div_of_le (by norm_num) (by linarith)
      linarith
    have hmul := mul_le_mul_of_nonneg_right hhalf (show 0 ≤ q * n by positivity)
    have hqmul : q * (n : ℝ) = 16 * ((k.val : ℝ) + 1 + Real.log n) := by
      simp only [q, daRankScoreThreshold, Nat.cast_add, Nat.cast_one]
      exact div_mul_cancel₀ _ hn₀.ne'
    rw [hqmul] at hmul
    rw [mul_assoc, hqmul]
    linarith only [hmul, hlog, Nat.cast_nonneg (α := ℝ) k.val]
  · have hae : ∀ᵐ y ∂ν, ∀ i, y i ∈ Icc (0 : ℝ) 1 :=
      ae_all_iff.2 fun i ↦
        (measurePreserving_eval (fun _ : Fin n ↦ unitScoreLaw) i).quasiMeasurePreserving.ae
          (ae_restrict_mem measurableSet_Icc)
    have hz : ν (badRankThresholdRow n k) = 0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [hae] with y hy
      change ¬ (∑ j, if y j ≤ q then (1 : ℝ) else 0) < _
      have hh (j : Fin n) : y j ≤ q := (hy j).2.trans (le_of_not_ge hq₁)
      simp only [hh, ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one, not_lt]
      exact_mod_cast Nat.succ_le_of_lt k.isLt
    change ν (badRankThresholdRow n k) ≤ _
    rw [hz]
    exact zero_le
private def daBadFemaleRankThreshold (n : ℕ) : Set (ScoreProfile n) :=
  ⋃ w : Fin n, ⋃ k : Fin n, (fun x : ScoreProfile n ↦ x (.inr w)) ⁻¹' badRankThresholdRow n k
theorem measure_daBadFemaleRankThreshold_le {n : ℕ} (hn : 0 < n) :
    continuousScoreLaw n (daBadFemaleRankThreshold n) ≤ ENNReal.ofReal ((n : ℝ) ^ (-2 : ℝ)) := by
  have hrow (w k : Fin n) :
      continuousScoreLaw n ((fun x : ScoreProfile n ↦ x (.inr w)) ⁻¹'
        badRankThresholdRow n k) ≤ ENNReal.ofReal (Real.exp (-4 * Real.log n)) := by
    rw [continuousScoreLaw, (measurePreserving_eval (fun _ : Fin n ⊕ Fin n ↦ Measure.pi
      fun _ : Fin n ↦ unitScoreLaw) (.inr w)).measure_preimage
      (measurableSet_badRankThresholdRow n k).nullMeasurableSet]
    exact measure_badRankThresholdRow_le hn k
  unfold daBadFemaleRankThreshold
  refine (measure_iUnion_le _).trans ?_
  rw [tsum_fintype]
  calc
    _ ≤ ∑ _w : Fin n, ∑ _k : Fin n, ENNReal.ofReal (Real.exp (-4 * Real.log n)) := by
      gcongr with w _
      exact (measure_iUnion_le _).trans (by
        rw [tsum_fintype]
        exact Finset.sum_le_sum fun k _ ↦ hrow w k)
    _ = _ := by
      have hn₀ : (0 : ℝ) < n := Nat.cast_pos.mpr hn
      rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [mul_comm (-4) (Real.log n), ← Real.rpow_def_of_pos hn₀,
        Real.rpow_neg hn₀.le, Real.rpow_neg hn₀.le,
        show (4 : ℝ) = (4 : ℕ) by norm_num, show (2 : ℝ) = (2 : ℕ) by norm_num,
        Real.rpow_natCast, Real.rpow_natCast]
      field_simp
theorem femaleScore_le_daRankScoreThreshold {n : ℕ} {x : ScoreProfile n}
    (hx : ∀ w, Function.Injective (x (.inr w))) (hgood : x ∉ daBadFemaleRankThreshold n)
    (w m : Fin n) :
    x (.inr w) m ≤ daRankScoreThreshold n ((rankPermutation (x (.inr w)) m).val + 1) := by
  let y := x (.inr w)
  let e := rankPermutation y
  let k := e m
  let q := daRankScoreThreshold n (k.val + 1)
  have hcount : (k.val : ℝ) + 1 ≤ ∑ j, if y j ≤ q then (1 : ℝ) else 0 := by
    apply le_of_not_gt
    intro h
    exact hgood (mem_iUnion.mpr ⟨w, mem_iUnion.mpr ⟨k, h⟩⟩)
  change y m ≤ q
  by_contra! h
  have hbound : (∑ j, if y j ≤ q then (1 : ℝ) else 0) ≤
      ∑ j, if e j < k then (1 : ℝ) else 0 := by
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : y j ≤ q
    · have hlt : e j < k := (rankPermutation_lt_iff (hx w) j m).mpr (hj.trans_lt h)
      simp only [hj, hlt, ite_true, le_refl]
    · simp only [hj, ite_false]
      split <;> norm_num
  have hcard : (∑ j, if e j < k then (1 : ℝ) else 0) = k.val := by
    rw [Equiv.sum_comp e (fun j ↦ if j < k then (1 : ℝ) else 0), ← Finset.sum_filter,
      show Finset.univ.filter (fun j ↦ j < k) = Finset.Iio k by ext j; simp,
      Finset.sum_const, nsmul_eq_mul, mul_one, Fin.card_Iio]
  rw [hcard] at hbound
  linarith
private theorem scoreWalkMatching_horizon_symm_eq_swap_da {n : ℕ} (x : ScoreProfile n)
    (hx : ∀ w, Function.Injective (x (.inr w))) :
    (scoreWalkMatching x (n * (n - 1))).symm =
      DAState.matching (swapProfile (profileOfScores x)) := by
  let p := swapProfile (profileOfScores x)
  let μ := (scoreWalkMatching x (n * (n - 1))).symm
  let ν := DAState.matching p
  have hμ : IsManOptimal p μ := (scoreRotationWalk_da_optimal_endpoints x hx).2.2
  have hν : IsManOptimal p ν := DAState.isManOptimal_matching p
  change μ = ν
  apply Equiv.ext
  intro w
  exact (p.manRank w).injective (le_antisymm (hμ.2 ν hν.1 w) (hν.2 μ hμ.1 w))
theorem scoreWalkFemaleTotal_horizon_le_of_proposalCount {n : ℕ} (hn : 0 < n)
    {x : ScoreProfile n} (hx : ∀ w, Function.Injective (x (.inr w)))
    (hgood : x ∉ daBadFemaleRankThreshold n) {T : ℕ}
    (hT : (DAState.run (swapProfile (profileOfScores x)) (n * n)).proposalCount ≤ T) :
    scoreWalkFemaleTotal x (n * (n - 1)) ≤ 16 * ((T : ℝ) / n + Real.log n) := by
  let p := swapProfile (profileOfScores x)
  let s := DAState.run p (n * n)
  let μ := DAState.matching p
  have hn₀ : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hrank (w : Fin n) : (rankPermutation (x (.inr w)) (μ w)).val + 1 = s.count w :=
    (DAState.valid_run p _).held_last (s.held_toMatching (DAState.complete_run_sq p) w)
  have hsum : (∑ w, (s.count w : ℝ)) ≤ T := by
    exact_mod_cast hT
  change (∑ w, x (.inr w) ((scoreWalkMatching x (n * (n - 1))).symm w)) ≤ _
  rw [scoreWalkMatching_horizon_symm_eq_swap_da x hx]
  calc
    _ ≤ ∑ w, daRankScoreThreshold n (s.count w) := by
      refine Finset.sum_le_sum fun w _ ↦ ?_
      simpa only [hrank w] using femaleScore_le_daRankScoreThreshold hx hgood w (μ w)
    _ = 16 * ((∑ w, (s.count w : ℝ)) / n + Real.log n) := by
      simp only [daRankScoreThreshold, ← Finset.sum_div, ← Finset.mul_sum,
        Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    _ ≤ _ := by gcongr
private theorem measure_swapDAProposalCount_gt (n T : ℕ) :
    continuousScoreLaw n
        {x | T < (DAState.run (swapProfile (profileOfScores x)) (n * n)).proposalCount} =
      (uniformProfile n).toMeasure {p | T < (DAState.run p (n * n)).proposalCount} := by
  let E : Set (Profile n) := {p | T < (DAState.run p (n * n)).proposalCount}
  have hp : MeasurePreserving (profileOfScores ∘ @swapScoreSides n) (continuousScoreLaw n)
      (uniformProfile n).toMeasure :=
    (measurePreserving_profileOfScores n).comp (measurePreserving_swapScoreSides n)
  change continuousScoreLaw n ((profileOfScores ∘ @swapScoreSides n) ⁻¹' E) = _
  exact hp.measure_preimage (MeasurableSet.of_discrete (s := E)).nullMeasurableSet
private theorem eventually_proposalCountScoreBound_le_rpow {T : ℕ → ℕ} {C : ℝ}
    (hT : ∀ᶠ n : ℕ in atTop, (T n : ℝ) ≤ C * n * Real.log n) :
    ∀ᶠ n : ℕ in atTop, 16 * ((T n : ℝ) / n + Real.log n) ≤ (n : ℝ) ^ (1 / 5 : ℝ) := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log n / (n : ℝ) ^ (1 / 5 : ℝ)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 5)).tendsto_div_nhds_zero.comp
      tendsto_natCast_atTop_atTop
  have hscaled : Tendsto (fun n : ℕ ↦ (16 * (C + 1)) *
      (Real.log n / (n : ℝ) ^ (1 / 5 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using hlog.const_mul (16 * (C + 1))
  filter_upwards [hT, eventually_gt_atTop (0 : ℕ), hscaled.eventually_lt_const zero_lt_one]
    with n hTn hn hsmall
  have hn₀ : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hdiv : (T n : ℝ) / n ≤ C * Real.log n :=
    (div_le_iff₀ hn₀).mpr (by simpa only [mul_right_comm C] using hTn)
  calc
    16 * ((T n : ℝ) / n + Real.log n) ≤ 16 * (C * Real.log n + Real.log n) := by
      gcongr
    _ = 16 * (C + 1) * Real.log n := by ring
    _ ≤ (n : ℝ) ^ (1 / 5 : ℝ) := by
      rw [← mul_div_assoc] at hsmall
      exact ((div_lt_iff₀ (Real.rpow_pos_of_pos hn₀ _)).mp hsmall).le.trans_eq (one_mul _)
theorem tendsto_measure_badScoreWalkUpperEndpoint {T : ℕ → ℕ} {C : ℝ}
    (hT : ∀ᶠ n : ℕ in atTop, (T n : ℝ) ≤ C * n * Real.log n)
    (hcap : Tendsto (fun n ↦ (uniformProfile n).toMeasure
      {p | T n < (DAState.run p (n * n)).proposalCount}) atTop (𝓝 0)) :
    Tendsto (fun n ↦ continuousScoreLaw n
      {x | (n : ℝ) ^ (1 / 5 : ℝ) < scoreWalkFemaleTotal x (n * (n - 1))}) atTop (𝓝 0) := by
  have hrare : Tendsto (fun n : ℕ ↦ ENNReal.ofReal ((n : ℝ) ^ (-2 : ℝ))) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero, Function.comp_def] using ENNReal.tendsto_ofReal
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2)).comp
        tendsto_natCast_atTop_atTop)
  have hsum := hrare.add hcap
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ), eventually_proposalCountScoreBound_le_rpow hT]
    with n hn hsmall
  let E : Set (ScoreProfile n) :=
    {x | T n < (DAState.run (swapProfile (profileOfScores x)) (n * n)).proposalCount}
  let B : Set (ScoreProfile n) := daBadFemaleRankThreshold n ∪ E
  have hsub : {x | (n : ℝ) ^ (1 / 5 : ℝ) < scoreWalkFemaleTotal x (n * (n - 1))} ≤ᵐ[
      continuousScoreLaw n] B := by
    filter_upwards [ae_injective_rows n] with x hx hbad
    by_contra hgood
    have hx₁ : x ∉ daBadFemaleRankThreshold n := fun h ↦ hgood (Or.inl h)
    have hx₂ : (DAState.run (swapProfile (profileOfScores x)) (n * n)).proposalCount ≤ T n :=
      le_of_not_gt fun h ↦ hgood (Or.inr h)
    exact not_lt_of_ge
      ((scoreWalkFemaleTotal_horizon_le_of_proposalCount hn (fun w ↦ hx (.inr w)) hx₁ hx₂).trans
        hsmall) hbad
  refine (measure_mono_ae hsub).trans ((measure_union_le _ _).trans ?_)
  exact add_le_add (measure_daBadFemaleRankThreshold_le hn) (measure_swapDAProposalCount_gt n _).le
end StepA4
end

-- ParticipationClockMartingale
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal
namespace StepA4
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {ℱ : Filtration ℕ mΩ} {M : ℕ → Ω → ℝ}
theorem condExp_martingale_increment_sq [IsFiniteMeasure μ]
    (hM : Martingale M ℱ μ) (hL2 : ∀ t, MemLp (M t) 2 μ) {i j : ℕ} (hij : i ≤ j) :
    μ[fun ω ↦ (M j ω - M i ω)^2 | ℱ i] =ᵐ[μ]
      fun ω ↦ μ[fun ω ↦ M j ω ^ 2 | ℱ i] ω - M i ω ^ 2 := by
  have hmean := hM.condExp_ae_eq hij
  have hvar : Var[M j; μ | ℱ i] =ᵐ[μ] μ[fun ω ↦ (M j ω - M i ω)^2 | ℱ i] := by
    apply condExp_congr_ae
    filter_upwards [hmean] with ω hω
    change (M j ω - μ[M j | ℱ i] ω)^2 = _
    rw [hω]
  refine hvar.symm.trans ((condVar_ae_eq_condExp_sq_sub_sq_condExp (ℱ.le i) (hL2 j)).trans ?_)
  filter_upwards [hmean] with ω hω
  change μ[fun ω ↦ M j ω ^ 2 | ℱ i] ω - (μ[M j | ℱ i] ω)^2 = _
  rw [hω]
theorem martingale_sq_submartingale [IsFiniteMeasure μ]
    (hM : Martingale M ℱ μ) (hL2 : ∀ t, MemLp (M t) 2 μ) :
    Submartingale (fun t ω ↦ M t ω ^ 2) ℱ μ := by
  refine ⟨fun t ↦ (hM.stronglyMeasurable t).pow 2, fun i j hij ↦ ?_, fun t ↦
    (hL2 t).integrable_sq⟩
  have hnonneg : 0 ≤ᵐ[μ] μ[fun ω ↦ (M j ω - M i ω)^2 | ℱ i] :=
    condExp_nonneg (.of_forall fun ω ↦ sq_nonneg (M j ω - M i ω))
  filter_upwards [hnonneg, condExp_martingale_increment_sq hM hL2 hij] with ω hω heq
  rw [heq] at hω
  exact sub_nonneg.mp hω
theorem integral_martingale_sq_eq_sum_increment_sq [IsFiniteMeasure μ]
    (hM : Martingale M ℱ μ) (hL2 : ∀ t, MemLp (M t) 2 μ) (h0 : M 0 =ᵐ[μ] 0) (N : ℕ) :
    (∫ ω, M N ω ^ 2 ∂μ) = ∑ t ∈ Finset.range N, ∫ ω, (M (t + 1) ω - M t ω)^2 ∂μ := by
  induction N with
  | zero =>
    rw [Finset.range_zero, Finset.sum_empty, ← integral_zero Ω ℝ]
    apply integral_congr_ae
    filter_upwards [h0] with ω hω
    change M 0 ω ^ 2 = 0
    rw [hω]
    norm_num
  | succ N ih =>
    have hstep :
        (∫ ω, (M (N + 1) ω - M N ω)^2 ∂μ) =
          (∫ ω, M (N + 1) ω ^ 2 ∂μ) - ∫ ω, M N ω ^ 2 ∂μ := by
      rw [← integral_condExp (ℱ.le N) (f := fun ω ↦ (M (N + 1) ω - M N ω)^2)]
      calc
        _ = ∫ ω, μ[fun ω ↦ M (N + 1) ω ^ 2 | ℱ N] ω - M N ω ^ 2 ∂μ :=
          integral_congr_ae (condExp_martingale_increment_sq hM hL2 (Nat.le_succ N))
        _ = _ := by rw [integral_sub integrable_condExp (hL2 N).integrable_sq,
          integral_condExp (ℱ.le N)]
    rw [Finset.sum_range_succ, ← ih, hstep]
    ring
theorem measure_clock_maximal_le_of_integral_sq [IsFiniteMeasure μ]
    (hM : Martingale M ℱ μ) (hL2 : ∀ t, MemLp (M t) 2 μ) {N : ℕ} {B a : ℝ}
    (hB : (∫ ω, M N ω ^ 2 ∂μ) ≤ B) (ha : 0 < a) :
    μ {ω | ∃ t ≤ N, a ≤ |M t ω|} ≤ ENNReal.ofReal (B / a^2) := by
  let ε : ℝ≥0 := ⟨a^2, sq_nonneg a⟩
  have hnonneg : 0 ≤ (fun t ω ↦ M t ω ^ 2) := fun t ω ↦ sq_nonneg (M t ω)
  have h := maximal_ineq (martingale_sq_submartingale hM hL2) hnonneg (ε := ε) N
  have hevent :
      {ω | (ε : ℝ) ≤ (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
        fun t ↦ M t ω ^ 2} = {ω | ∃ t ≤ N, a ≤ |M t ω|} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Finset.le_sup'_iff, Finset.mem_range, Nat.lt_succ_iff]
    apply exists_congr
    intro t
    change (t ≤ N ∧ a^2 ≤ M t ω ^ 2) ↔ (t ≤ N ∧ a ≤ |M t ω|)
    rw [← sq_abs (M t ω), sq_le_sq₀ ha.le (abs_nonneg _)]
  rw [hevent] at h
  have hterminal : 0 ≤ (∫ ω, M N ω ^ 2 ∂μ) :=
    integral_nonneg fun ω ↦ sq_nonneg (M N ω)
  have hscaled : ε • μ {ω | ∃ t ≤ N, a ≤ |M t ω|} ≤ ENNReal.ofReal B :=
    h.trans (ENNReal.ofReal_le_ofReal ((setIntegral_le_integral (hL2 N).integrable_sq
      (.of_forall fun ω ↦ sq_nonneg (M N ω))).trans hB))
  have hreal := (ENNReal.le_ofReal_iff_toReal_le
    (ENNReal.mul_ne_top (by simp) (measure_ne_top μ _)) (hterminal.trans hB)).mp hscaled
  rw [ENNReal.toReal_mul] at hreal
  change a^2 * (μ {ω | ∃ t ≤ N, a ≤ |M t ω|}).toReal ≤ B at hreal
  rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ _)
    (div_nonneg (hterminal.trans hB) (sq_nonneg a)), le_div_iff₀ (sq_pos_of_pos ha), mul_comm]
  exact hreal
theorem measure_clock_maximal_le_of_increment_sq [IsFiniteMeasure μ]
    (hM : Martingale M ℱ μ) (hL2 : ∀ t, MemLp (M t) 2 μ) (h0 : M 0 =ᵐ[μ] 0)
    {N : ℕ} {B a : ℝ}
    (hB : (∑ t ∈ Finset.range N, ∫ ω, (M (t + 1) ω - M t ω)^2 ∂μ) ≤ B)
    (ha : 0 < a) :
    μ {ω | ∃ t ≤ N, a ≤ |M t ω|} ≤ ENNReal.ofReal (B / a^2) :=
  measure_clock_maximal_le_of_integral_sq hM hL2
    ((integral_martingale_sq_eq_sum_increment_sq hM hL2 h0 N).le.trans hB) ha
theorem measure_clock_maximal_le_of_step_energy [IsFiniteMeasure μ]
    (hM : StronglyAdapted ℱ M) {N : ℕ} (hL2 : ∀ t ≤ N, MemLp (M t) 2 μ)
    (h0 : M 0 =ᵐ[μ] 0) {B a : ℝ}
    (hmean : ∀ t < N, μ[fun ω ↦ M (t + 1) ω - M t ω | ℱ t] =ᵐ[μ] 0)
    (hB : (∑ t ∈ Finset.range N, ∫ ω, (M (t + 1) ω - M t ω)^2 ∂μ) ≤ B)
    (ha : 0 < a) :
    μ {ω | ∃ t ≤ N, a ≤ |M t ω|} ≤ ENNReal.ofReal (B / a^2) := by
  let M' : ℕ → Ω → ℝ := fun t ↦ M (min t N)
  have hM'L2 (t : ℕ) : MemLp (M' t) 2 μ := hL2 _ (min_le_right t N)
  have hM' : Martingale M' ℱ μ := by
    refine martingale_of_condExp_sub_eq_zero_nat
      (fun t ↦ (hM _).mono (ℱ.mono (min_le_left t N)))
      (fun t ↦ (hM'L2 t).integrable (by simp)) fun t ↦ ?_
    change μ[fun ω ↦ M (min (t + 1) N) ω - M (min t N) ω | ℱ t] =ᵐ[μ] 0
    by_cases ht : t < N
    · rw [min_eq_left ht.le, min_eq_left (Nat.succ_le_of_lt ht)]
      exact hmean t ht
    · have hle := Nat.le_of_not_gt ht
      rw [min_eq_right hle, min_eq_right (hle.trans (Nat.le_succ t))]
      simp only [sub_self, ← Pi.zero_def, condExp_zero, EventuallyEq.rfl]
  have hM'0 : M' 0 =ᵐ[μ] 0 := by simpa only [M', Nat.zero_min] using h0
  have hM'B : (∑ t ∈ Finset.range N, ∫ ω, (M' (t + 1) ω - M' t ω)^2 ∂μ) ≤ B := by
    convert hB using 1
    apply Finset.sum_congr rfl
    intro t ht
    have hlt := Finset.mem_range.mp ht
    simp only [M', min_eq_left hlt.le, min_eq_left (Nat.succ_le_of_lt hlt)]
  have h := measure_clock_maximal_le_of_increment_sq hM' hM'L2 hM'0 hM'B ha
  have hevent : {ω | ∃ t ≤ N, a ≤ |M' t ω|} = {ω | ∃ t ≤ N, a ≤ |M t ω|} := by
    ext ω
    constructor
    · rintro ⟨t, ht, hω⟩
      exact ⟨t, ht, by simpa only [M', min_eq_left ht] using hω⟩
    · rintro ⟨t, ht, hω⟩
      exact ⟨t, ht, by simpa only [M', min_eq_left ht] using hω⟩
  rwa [hevent] at h
end StepA4
end

-- FinitePartitionClock
section
open MeasureTheory Set
open scoped Function
namespace StepA4
variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι]
theorem clock_moments_of_fintype_partition (μ : Measure Ω) [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {d l : Ω → ℝ}
    (hd : Measurable[mΩ] d) (hl : Integrable l μ) {B : ι → Set Ω}
    (hB : ∀ i, MeasurableSet[mΩ] (B i)) (hdisj : Pairwise (Disjoint on B))
    (hcover : (⋃ i, B i) = univ) (hLp : ∀ i, MemLp d 2 (μ.restrict (B i)))
    (hmean : ∀ i A, MeasurableSet[m] A → (∫ x in B i ∩ A, d x ∂μ) = 0)
    (henergy : ∀ i, (∫ x in B i, (d x)^2 ∂μ) = ∫ x in B i, l x ∂μ) :
    MemLp d 2 μ ∧ μ[d | m] =ᵐ[μ] 0 ∧
      (∫ x, (d x)^2 ∂μ) = ∫ x, l x ∂μ := by
  have hsq (i : ι) : IntegrableOn (fun x ↦ (d x)^2) (B i) μ := (hLp i).integrable_sq
  have hwholeSq : Integrable (fun x ↦ (d x)^2) μ := by
    rw [← integrableOn_univ, ← hcover, integrableOn_finite_iUnion]
    exact hsq
  have hdm : AEStronglyMeasurable[mΩ] d μ := hd.aestronglyMeasurable
  have hL : MemLp d 2 μ := (memLp_two_iff_integrable_sq hdm).mpr hwholeSq
  refine ⟨hL, ?_, ?_⟩
  · refine (ae_eq_condExp_of_forall_setIntegral_eq hm (hL.integrable (by norm_num))
      (fun _ _ _ ↦ (integrable_zero Ω ℝ μ).integrableOn) ?_
      stronglyMeasurable_zero.aestronglyMeasurable).symm
    intro A hA _
    have hA₀ : MeasurableSet[mΩ] A := hm A hA
    have hsplit : (⋃ i, B i ∩ A) = A := by rw [← iUnion_inter, hcover, univ_inter]
    have hdisj' : Pairwise (Disjoint on fun i ↦ B i ∩ A) :=
      fun _ _ hij ↦ (hdisj hij).mono inter_subset_left inter_subset_left
    rw [← hsplit,
      integral_iUnion_fintype (fun i ↦ (hB i).inter hA₀) hdisj'
        (fun _ ↦ (hL.integrable (by norm_num)).integrableOn)]
    simp only [hmean _ A hA, Finset.sum_const_zero, integral_zero']
  · calc
      (∫ x, (d x)^2 ∂μ) = ∑ i, ∫ x in B i, (d x)^2 ∂μ := by
        rw [← integral_iUnion_fintype hB hdisj hsq, hcover, setIntegral_univ]
      _ = ∑ i, ∫ x in B i, l x ∂μ := Finset.sum_congr rfl fun i _ ↦ henergy i
      _ = ∫ x, l x ∂μ := by
        rw [← integral_iUnion_fintype hB hdisj (fun _ ↦ hl.integrableOn),
          hcover, setIntegral_univ]
end StepA4
end

-- ScoreClockFiltration
section
open MeasureTheory Set StableMarriage
open scoped BigOperators
namespace StepA4
private abbrev DMeasurable {α β : Type*} [MeasurableSpace α] (f : α → β) : Prop :=
  @Measurable α β inferInstance ⊤ f
private theorem dmeasurable_postcomp {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace γ]
    {f : α → β} (hf : DMeasurable f) (g : β → γ) : Measurable (g ∘ f) :=
  fun s _ ↦ hf (t := g ⁻¹' s) MeasurableSpace.measurableSet_top
private theorem dmeasurable_postcomp_discrete {α β γ : Type*} [MeasurableSpace α]
    {f : α → β} (hf : DMeasurable f) (g : β → γ) : DMeasurable (g ∘ f) :=
  @dmeasurable_postcomp _ _ _ _ ⊤ _ hf g
private theorem dmeasurable_pi {α ι β : Type*} [MeasurableSpace α] [Countable ι]
    [Countable (ι → β)] {f : α → ι → β}
    (h : ∀ i, DMeasurable fun x ↦ f x i) : DMeasurable f := by
  let : MeasurableSpace (ι → β) := ⊤
  apply measurable_to_countable'
  intro b
  have heq : f ⁻¹' {b} = ⋂ i, (fun x ↦ f x i) ⁻¹' {b i} := by
    ext x
    simp only [mem_preimage, mem_singleton_iff, mem_iInter, funext_iff]
  rw [heq]
  exact MeasurableSet.iInter fun i ↦ h i MeasurableSpace.measurableSet_top
private theorem dmeasurable_prod {α β γ : Type*} [MeasurableSpace α]
    [Countable β] [Countable γ] {f : α → β} {g : α → γ}
    (hf : DMeasurable f) (hg : DMeasurable g) :
    DMeasurable fun x ↦ (f x, g x) := by
  let : MeasurableSpace (β × γ) := ⊤
  apply measurable_to_countable'
  rintro ⟨b, c⟩
  rw [show (fun x ↦ (f x, g x)) ⁻¹' {(b, c)} = f ⁻¹' {b} ∩ g ⁻¹' {c} by
    ext x
    simp]
  exact (hf (t := {b}) MeasurableSpace.measurableSet_top).inter
    (hg (t := {c}) MeasurableSpace.measurableSet_top)
private theorem measurable_discrete_cases {α β γ : Type*} [MeasurableSpace α] [Countable β]
    [MeasurableSpace γ] {f : α → β} (hf : DMeasurable f) (g : β → α → γ)
    (hg : ∀ b, Measurable (g b)) : Measurable fun x ↦ g (f x) x := by
  intro s hs
  have heq : (fun x ↦ g (f x) x) ⁻¹' s = ⋃ b, (f ⁻¹' {b}) ∩ (g b ⁻¹' s) := by
    ext x
    simp
  rw [heq]
  exact MeasurableSet.iUnion fun b ↦ (hf MeasurableSpace.measurableSet_top).inter (hg b hs)
private theorem dmeasurable_discrete_cases {α β γ : Type*} [MeasurableSpace α] [Countable β]
    {f : α → β} (hf : DMeasurable f) (g : β → α → γ)
    (hg : ∀ b, DMeasurable (g b)) : DMeasurable fun x ↦ g (f x) x :=
  @measurable_discrete_cases _ _ _ _ _ ⊤ _ hf g hg
variable {n : ℕ}
private theorem measurable_scoreComparison (μ : Matching n) (m w : Fin n) :
    DMeasurable fun x : ScoreProfile n ↦
      successorScoreOracle (femaleSpouseScore x μ) (fun v ↦ x (.inr v)) m w := by
  let E : Set (ScoreProfile n) := {x | x (.inr w) m < femaleSpouseScore x μ w}
  have hE : MeasurableSet E := measurableSet_lt
    ((measurable_pi_apply m).comp (measurable_pi_apply (Sum.inr w : Fin n ⊕ Fin n)))
    (measurable_femaleSpouseScore μ w)
  let : MeasurableSpace Bool := ⊤
  apply measurable_to_countable'
  intro b
  cases b
  · convert hE.compl using 1
    ext x
    simp [successorScoreOracle, E]
  · convert hE using 1
    ext x
    simp [successorScoreOracle, E]
theorem measurable_scoreRotationGraph (μ : Matching n) :
    @Measurable (ScoreProfile n) (Fin n → Option (Fin n)) inferInstance ⊤
      (fun x ↦ scoreRotationGraph x μ) := by
  have hp : DMeasurable (@profileOfScores n) := measurable_profileOfScores n
  have hor : DMeasurable fun x : ScoreProfile n ↦
      successorScoreOracle (femaleSpouseScore x μ) (fun w ↦ x (.inr w)) :=
    dmeasurable_pi fun m ↦ dmeasurable_pi fun w ↦ measurable_scoreComparison μ m w
  exact dmeasurable_postcomp_discrete (dmeasurable_prod hp hor) fun z ↦
    queriedSuccessorGraph z.1.manRank μ z.2
theorem measurable_scoreRotationWalk (k : ℕ) (μ : Matching n) :
    @Measurable (ScoreProfile n) (List (Equiv.Perm (Fin n)) × Matching n) inferInstance ⊤
      (fun x ↦ scoreRotationWalk x k μ) := by
  induction k generalizing μ with
  | zero => exact measurable_const
  | succ k ih =>
    have hnext : DMeasurable fun x : ScoreProfile n ↦
        chooseQueriedRotation (scoreRotationGraph x μ) :=
      dmeasurable_postcomp_discrete (measurable_scoreRotationGraph μ) chooseQueriedRotation
    simp only [scoreRotationWalk_zero, scoreRotationWalk_succ]
    refine dmeasurable_discrete_cases hnext (fun b x ↦ match b with
      | none => ([], μ)
      | some ρ =>
        let z := scoreRotationWalk x k (eliminateRotation μ ρ)
        (ρ :: z.1, z.2)) ?_
    intro b
    cases b with
    | none => exact measurable_const
    | some ρ => exact dmeasurable_postcomp_discrete (ih _) fun z ↦ (ρ :: z.1, z.2)
theorem measurable_scoreWalkStart (n : ℕ) :
    @Measurable (ScoreProfile n) (Matching n) inferInstance ⊤
      (fun x ↦ DAState.matching (profileOfScores x)) := by
  have hp : DMeasurable (@profileOfScores n) := measurable_profileOfScores n
  exact dmeasurable_postcomp_discrete hp DAState.matching
theorem measurable_scoreWalkRecord (n k : ℕ) :
    @Measurable (ScoreProfile n) (List (Equiv.Perm (Fin n)) × Matching n) inferInstance ⊤
      (fun x ↦ scoreRotationWalk x k (DAState.matching (profileOfScores x))) :=
  dmeasurable_discrete_cases (measurable_scoreWalkStart n) (fun μ x ↦ scoreRotationWalk x k μ)
    (fun μ ↦ measurable_scoreRotationWalk k μ)
theorem measurable_scoreWalkClock (n k : ℕ) :
    Measurable (fun x : ScoreProfile n ↦ scoreWalkClock x k) := by
  have hpot (μ : Matching n) : Measurable fun x : ScoreProfile n ↦ femaleLogPotential x μ :=
    Finset.measurable_sum _ fun i _ ↦ (measurable_femaleSpouseScore μ i).log.neg
  exact ((measurable_discrete_cases (measurable_scoreWalkRecord n k)
      (fun z x ↦ femaleLogPotential x z.2) (fun z ↦ hpot z.2)).sub
    (measurable_discrete_cases (measurable_scoreWalkStart n)
      (fun μ x ↦ femaleLogPotential x μ) hpot)).sub
    (dmeasurable_postcomp (measurable_scoreWalkRecord n k) fun z ↦
      (rotationParticipation z.1 : ℝ))
private noncomputable def scoreWalkClockHistory (x : ScoreProfile n) (k : ℕ) : Fin (k + 1) → ℝ :=
  fun i ↦ scoreWalkClock x i
theorem measurable_scoreWalkClockHistory (n k : ℕ) :
    Measurable (fun x : ScoreProfile n ↦ scoreWalkClockHistory x k) :=
  measurable_pi_iff.2 fun i ↦ measurable_scoreWalkClock n i
private noncomputable def scoreWalkClockFiltration (n : ℕ) :
    Filtration ℕ (inferInstance : MeasurableSpace (ScoreProfile n)) where
  seq k :=
    MeasurableSpace.comap (fun x : ScoreProfile n ↦ scoreWalkClockHistory x k) inferInstance
  mono' i j hij := by
    let trim : (Fin (j + 1) → ℝ) → Fin (i + 1) → ℝ :=
      fun z k ↦ z (k.castLE (Nat.succ_le_succ hij))
    have ht : Measurable trim := measurable_pi_iff.2 fun k ↦ measurable_pi_apply _
    rintro _ ⟨A, hA, rfl⟩
    exact ⟨trim ⁻¹' A, ht hA, rfl⟩
  le' k := (measurable_scoreWalkClockHistory n k).comap_le
theorem stronglyAdapted_scoreWalkClock (n : ℕ) :
    StronglyAdapted (scoreWalkClockFiltration n) (fun k x ↦ scoreWalkClock x k) := by
  intro k
  exact ((measurable_pi_apply (Fin.last k)).comp
    (comap_measurable (fun x : ScoreProfile n ↦ scoreWalkClockHistory x k))).stronglyMeasurable
theorem mem_iff_of_scoreWalkClock_history_eq {A : Set (ScoreProfile n)} {x y : ScoreProfile n}
    {k : ℕ} (hA : MeasurableSet[scoreWalkClockFiltration n k] A)
    (hxy : ∀ j ≤ k, scoreWalkClock x j = scoreWalkClock y j) : x ∈ A ↔ y ∈ A := by
  obtain ⟨B, _, rfl⟩ := hA
  change scoreWalkClockHistory x k ∈ B ↔ scoreWalkClockHistory y k ∈ B
  rw [show scoreWalkClockHistory x k = scoreWalkClockHistory y k from
    funext fun j ↦ hxy j (Nat.le_of_lt_succ j.isLt)]
end StepA4
end

-- ScoreRotationBranchTest
section
open MeasureTheory Set StableMarriage
open scoped Classical
namespace StepA4
variable {n : ℕ}
theorem scoreWalkClock_increment_eq_on_branch (k : ℕ) (μ : Matching n)
    (ρ : Equiv.Perm (Fin n)) {x : ScoreProfile n} (hx : x ∈ scoreRotationBranch k μ ρ) :
    scoreWalkClock x (k + 1) - scoreWalkClock x k =
      centeredCacheLogIncrement (rotationClockUpper μ ρ) (splitRotationClockCells μ ρ x) := by
  have h := scoreWalkClock_succ_sub x k (fun j i ↦ (hx.1.2 (.inr j) i).1)
  dsimp only at h
  rw [hx.2.1, hx.2.2] at h
  exact h
theorem scoreWalkClock_history_eq_on_branch_fst_eq (k : ℕ) (μ : Matching n)
    (ρ : Equiv.Perm (Fin n)) {x y : ScoreProfile n}
    (hx : x ∈ scoreRotationBranch k μ ρ) (hy : y ∈ scoreRotationBranch k μ ρ)
    (hfst : (splitRotationClockCells μ ρ x).1 = (splitRotationClockCells μ ρ y).1) :
    ∀ j ≤ k, scoreWalkClock x j = scoreWalkClock y j := by
  have hxrot : IsExposedRotation (profileOfScores x) μ ρ :=
    (realizesDirectedCycle_queriedSuccessorGraph_scores_iff x hx.1.1 μ ρ).mp
      (realizesDirectedCycle_of_chooseQueriedRotation hx.2.2)
  have hyrot : IsExposedRotation (profileOfScores y) μ ρ :=
    (realizesDirectedCycle_queriedSuccessorGraph_scores_iff y hy.1.1 μ ρ).mp
      (realizesDirectedCycle_of_chooseQueriedRotation hy.2.2)
  have hfixed (r i) (hr : ¬ IsRotationClockCell μ ρ (r, i)) : y r i = x r i :=
    (congrFun hfst ⟨(r, i), hr⟩).symm
  have hbelow (i : Fin n) (hi : i ∈ ρ.support) :
      y (rotationClockCell μ ρ i).1 (rotationClockCell μ ρ i).2 <
        femaleSpouseScore x μ (eliminateRotation μ ρ i) := by
    rw [femaleSpouseScore_eq_of_splitRotationClockCells_fst_eq μ ρ hfst]
    exact hyrot.rotationClockCell_score_lt hy.1.1 hi
  intro j hj
  refine (scoreWalkClock_history_eq_of_replace_selected k hx.1.1 hy.1.1
    (ρ := ρ) ?_ ?_ ?_ j hj).symm
  · rw [hx.2.1]
    exact hxrot
  · rw [hx.2.1]
    exact hfixed
  · simpa only [hx.2.1] using hbelow
private theorem scoreWalkClock_moments_on_branch_inter (k : ℕ) (μ : Matching n)
    (ρ : Equiv.Perm (Fin n)) {A : Set (ScoreProfile n)} (hA : MeasurableSet A)
    (hInv : ∀ {x y}, x ∈ scoreRotationBranch k μ ρ → y ∈ scoreRotationBranch k μ ρ →
      (∀ j ≤ k, scoreWalkClock x j = scoreWalkClock y j) → (x ∈ A ↔ y ∈ A)) :
    let D := scoreRotationBranch k μ ρ ∩ A
    let Δ := fun x ↦ scoreWalkClock x (k + 1) - scoreWalkClock x k
    MemLp Δ 2 ((continuousScoreLaw n).restrict D) ∧
      (∫ x in D, Δ x ∂continuousScoreLaw n) = 0 ∧
      (∫ x in D, (Δ x)^2 ∂continuousScoreLaw n) =
        (ρ.support.card : ℝ) * (continuousScoreLaw n).real D := by
  let D := scoreRotationBranch k μ ρ ∩ A
  let Δ := fun x : ScoreProfile n ↦ scoreWalkClock x (k + 1) - scoreWalkClock x k
  let e := splitRotationClockCells μ ρ
  let P := (Measure.pi fun _ : ClockComplement μ ρ ↦ unitScoreLaw).prod
    (Measure.pi fun _ : ClockSelected μ ρ ↦ unitScoreLaw)
  let E := e.symm ⁻¹' D
  let ν := P.restrict E
  let L := centeredCacheLogIncrement (rotationClockUpper μ ρ)
  have hm : MeasurableSpace.comap (Prod.fst :
      (ClockComplement μ ρ → ℝ) × (ClockSelected μ ρ → ℝ) →
        (ClockComplement μ ρ → ℝ))
      inferInstance ≤ MeasurableSpace.prod
      (inferInstance : MeasurableSpace (ClockComplement μ ρ → ℝ))
      (inferInstance : MeasurableSpace (ClockSelected μ ρ → ℝ)) :=
    measurable_fst.comap_le
  have hD : MeasurableSet D := (measurableSet_scoreRotationBranch k μ ρ).inter hA
  have hE : MeasurableSet E := e.symm.measurable hD
  have hsplit : MeasurePreserving e ((continuousScoreLaw n).restrict D) ν := by
    have hpre : e ⁻¹' E = D := by
      ext x
      simp [E]
    have hp : MeasurePreserving e (continuousScoreLaw n) P :=
      measurePreserving_splitRotationClockCells μ ρ
    rw [← hpre]
    exact hp.restrict_preimage hE
  have hΔ : (fun x ↦ L (e x)) =ᵐ[(continuousScoreLaw n).restrict D] Δ := by
    filter_upwards [ae_restrict_mem hD] with x hx
    exact (scoreWalkClock_increment_eq_on_branch k μ ρ hx.1).symm
  have h := scoreRotationBranch_inter_condExp_logMoments k μ ρ hA
    (fun hx hy hfst ↦ hInv hx hy (scoreWalkClock_history_eq_on_branch_fst_eq k μ ρ hx hy hfst))
  have hmean : (∫ z, L z ∂ν) = 0 := by
    rw [← integral_condExp hm, integral_congr_ae h.2.1, integral_zero]
  have henergy : (∫ z, (L z)^2 ∂ν) = ∫ _ : ScoreProfile n,
      (ρ.support.card : ℝ) ∂(continuousScoreLaw n).restrict D := by
    rw [← integral_condExp hm, integral_congr_ae h.2.2]
    exact (hsplit.integral_comp' (fun _ ↦ (ρ.support.card : ℝ))).symm
  refine ⟨(memLp_congr_ae hΔ).mp (h.1.comp_measurePreserving hsplit), ?_, ?_⟩
  · exact (integral_congr_ae hΔ).symm.trans ((hsplit.integral_comp' L).trans hmean)
  · calc
      _ = ∫ x in D, (L (e x))^2 ∂continuousScoreLaw n :=
        integral_congr_ae (hΔ.symm.mono fun _ hx ↦ congrArg (fun r : ℝ ↦ r^2) hx)
      _ = ∫ z, (L z)^2 ∂ν := hsplit.integral_comp' (fun z ↦ (L z)^2)
      _ = (ρ.support.card : ℝ) * (continuousScoreLaw n).real D := by
        rw [henergy, integral_const, smul_eq_mul, mul_comm]
        simp only [measureReal_def, Measure.restrict_apply_univ]
theorem memLp_scoreWalkClock_increment_on_branch
    (k : ℕ) (μ : Matching n) (ρ : Equiv.Perm (Fin n)) :
    MemLp (fun x ↦ scoreWalkClock x (k + 1) - scoreWalkClock x k) 2
      ((continuousScoreLaw n).restrict (scoreRotationBranch k μ ρ)) := by
  simpa only [inter_univ] using
    (scoreWalkClock_moments_on_branch_inter k μ ρ MeasurableSet.univ (fun _ _ _ ↦ Iff.rfl)).1
theorem setIntegral_sq_scoreWalkClock_increment_on_branch
    (k : ℕ) (μ : Matching n) (ρ : Equiv.Perm (Fin n)) :
    (∫ x in scoreRotationBranch k μ ρ, (scoreWalkClock x (k + 1) - scoreWalkClock x k)^2
      ∂continuousScoreLaw n) = (ρ.support.card : ℝ) *
        (continuousScoreLaw n).real (scoreRotationBranch k μ ρ) := by
  simpa only [inter_univ] using
    (scoreWalkClock_moments_on_branch_inter k μ ρ MeasurableSet.univ
      (fun _ _ _ ↦ Iff.rfl)).2.2
theorem setIntegral_scoreWalkClock_increment_on_branch_inter
    (k : ℕ) (μ : Matching n) (ρ : Equiv.Perm (Fin n))
    {A : Set (ScoreProfile n)} (hA : MeasurableSet A)
    (hInv : ∀ {x y}, x ∈ scoreRotationBranch k μ ρ → y ∈ scoreRotationBranch k μ ρ →
      (∀ j ≤ k, scoreWalkClock x j = scoreWalkClock y j) → (x ∈ A ↔ y ∈ A)) :
    (∫ x in scoreRotationBranch k μ ρ ∩ A, (scoreWalkClock x (k + 1) - scoreWalkClock x k)
      ∂continuousScoreLaw n) = 0 :=
  (scoreWalkClock_moments_on_branch_inter k μ ρ hA hInv).2.1
end StepA4
end

-- ScoreRotationClockBudget
section
open MeasureTheory Set StableMarriage
open scoped BigOperators Classical Function
namespace StepA4
variable {n : ℕ}
private noncomputable def scoreWalkNextCycle (x : ScoreProfile n) (k : ℕ) :
    Option (Equiv.Perm (Fin n)) :=
  let start := DAState.matching (profileOfScores x)
  chooseQueriedRotation (scoreRotationGraph x (scoreRotationWalk x k start).2)
private noncomputable def scoreWalkStepLength (x : ScoreProfile n) (k : ℕ) : ℕ :=
  (scoreWalkNextCycle x k).elim 0 fun ρ ↦ ρ.support.card
private noncomputable def scoreWalkIncrement (x : ScoreProfile n) (k : ℕ) : ℝ :=
  scoreWalkClock x (k + 1) - scoreWalkClock x k
private def scoreWalkSelectionPartition (k : ℕ) :
    Option (Matching n × Equiv.Perm (Fin n)) → Set (ScoreProfile n)
  | none => (⋃ b : Matching n × Equiv.Perm (Fin n), scoreRotationBranch k b.1 b.2)ᶜ
  | some b => scoreRotationBranch k b.1 b.2
theorem measurableSet_scoreWalkSelectionPartition (k : ℕ)
    (b : Option (Matching n × Equiv.Perm (Fin n))) :
    MeasurableSet (scoreWalkSelectionPartition k b) := by
  cases b with
  | none => exact (MeasurableSet.iUnion fun b : Matching n × Equiv.Perm (Fin n) ↦
      measurableSet_scoreRotationBranch k b.1 b.2).compl
  | some b => exact measurableSet_scoreRotationBranch k b.1 b.2
theorem pairwise_disjoint_scoreWalkSelectionPartition (k : ℕ) :
    Pairwise (Disjoint on (@scoreWalkSelectionPartition n k)) := by
  intro a b hab
  change Disjoint (scoreWalkSelectionPartition k a) (scoreWalkSelectionPartition k b)
  rw [Set.disjoint_left]
  intro x ha hb
  cases a with
  | none =>
    cases b with
    | none => exact hab rfl
    | some b => exact ha (Set.mem_iUnion.mpr ⟨b, hb⟩)
  | some a =>
    cases b with
    | none => exact hb (Set.mem_iUnion.mpr ⟨a, ha⟩)
    | some b =>
      have ha' : x ∈ scoreRotationBranch k a.1 a.2 := ha
      have hb' : x ∈ scoreRotationBranch k b.1 b.2 := hb
      have he : a.1 = b.1 := ha'.2.1.symm.trans hb'.2.1
      have hsecond : a.2 = b.2 := Option.some.inj (ha'.2.2.symm.trans
        ((congrArg (fun ν ↦ chooseQueriedRotation (scoreRotationGraph x ν)) he).trans hb'.2.2))
      exact hab (congrArg some (Prod.ext he hsecond))
theorem iUnion_scoreWalkSelectionPartition (k : ℕ) :
    (⋃ b, @scoreWalkSelectionPartition n k b) = univ := by
  ext x
  simp only [mem_iUnion, mem_univ, iff_true]
  by_cases h : x ∈ ⋃ b : Matching n × Equiv.Perm (Fin n), scoreRotationBranch k b.1 b.2
  · obtain ⟨b, hb⟩ := mem_iUnion.mp h
    exact ⟨some b, hb⟩
  · exact ⟨none, h⟩
theorem scoreWalkNextCycle_of_mem_branch {x : ScoreProfile n} {k : ℕ} {μ : Matching n}
    {ρ : Equiv.Perm (Fin n)} (hx : x ∈ scoreRotationBranch k μ ρ) :
    scoreWalkNextCycle x k = some ρ := by
  unfold scoreWalkNextCycle
  dsimp only
  rw [hx.2.1]
  exact hx.2.2
theorem scoreWalkNextCycle_eq_none_of_mem_stopped {x : ScoreProfile n} {k : ℕ}
    (hg : x ∈ goodClockInput n) (hx : x ∈ scoreWalkSelectionPartition k none) :
    scoreWalkNextCycle x k = none := by
  cases h : scoreWalkNextCycle x k with
  | none => rfl
  | some ρ =>
    exfalso
    apply hx
    let μ := (scoreRotationWalk x k (DAState.matching (profileOfScores x))).2
    exact mem_iUnion.mpr ⟨(μ, ρ), hg, rfl, h⟩
theorem scoreWalkIncrement_ae_eq_zero_on_stopped (k : ℕ) :
    (fun x ↦ scoreWalkIncrement x k) =ᵐ[(continuousScoreLaw n).restrict
      (scoreWalkSelectionPartition k none)] 0 := by
  filter_upwards [ae_restrict_mem (measurableSet_scoreWalkSelectionPartition (n := n) k none),
    ae_restrict_of_ae (ae_goodClockInput n)] with x hx hg
  have h := scoreWalkNextCycle_eq_none_of_mem_stopped hg hx
  have hs := scoreWalkClock_succ_sub x k (fun j i ↦ (hg.2 (.inr j) i).1)
  change scoreWalkIncrement x k = (match scoreWalkNextCycle x k with
    | none => 0
    | some ρ => _) at hs
  simpa only [h, Pi.zero_apply] using hs
private noncomputable def scoreWalkMeasurableLength (x : ScoreProfile n) (k : ℕ) : ℝ :=
  ∑ b : Matching n × Equiv.Perm (Fin n),
    (scoreRotationBranch k b.1 b.2).indicator (fun _ ↦ (b.2.support.card : ℝ)) x
theorem scoreWalkMeasurableLength_of_mem_branch {x : ScoreProfile n} {k : ℕ} {μ : Matching n}
    {ρ : Equiv.Perm (Fin n)} (hx : x ∈ scoreRotationBranch k μ ρ) :
    scoreWalkMeasurableLength x k = (ρ.support.card : ℝ) := by
  unfold scoreWalkMeasurableLength
  rw [Finset.sum_eq_single (μ, ρ)]
  · exact indicator_of_mem hx _
  · intro b _ hb
    apply indicator_of_notMem
    intro h
    exact Set.disjoint_left.mp
      (pairwise_disjoint_scoreWalkSelectionPartition (n := n) k
        (show some b ≠ some (μ, ρ) from fun e ↦ hb (Option.some.inj e))) h hx
  · simp
theorem scoreWalkMeasurableLength_of_mem_stopped {x : ScoreProfile n} {k : ℕ}
    (hx : x ∈ scoreWalkSelectionPartition k none) : scoreWalkMeasurableLength x k = 0 := by
  apply Finset.sum_eq_zero
  intro b _
  exact indicator_of_notMem (fun hb ↦ hx (mem_iUnion.mpr ⟨b, hb⟩)) _
theorem scoreWalkMeasurableLength_eq_stepLength {x : ScoreProfile n} {k : ℕ}
    (hg : x ∈ goodClockInput n) :
    scoreWalkMeasurableLength x k = (scoreWalkStepLength x k : ℝ) := by
  obtain ⟨b, hb⟩ := mem_iUnion.mp
    (show x ∈ ⋃ b, @scoreWalkSelectionPartition n k b from by
      rw [iUnion_scoreWalkSelectionPartition]; exact mem_univ _)
  cases b with
  | none =>
    rw [scoreWalkMeasurableLength_of_mem_stopped hb, scoreWalkStepLength,
      scoreWalkNextCycle_eq_none_of_mem_stopped hg hb]
    exact Nat.cast_zero.symm
  | some b =>
    obtain ⟨μ, ρ⟩ := b
    have hb' : x ∈ scoreRotationBranch k μ ρ := hb
    rw [scoreWalkMeasurableLength_of_mem_branch hb', scoreWalkStepLength,
      scoreWalkNextCycle_of_mem_branch hb']
    rfl
theorem sum_scoreWalkStepLength_eq_rotationParticipation (x : ScoreProfile n) (N : ℕ) :
    (∑ k ∈ Finset.range N, scoreWalkStepLength x k) =
      rotationParticipation (scoreRotationWalk x N (DAState.matching (profileOfScores x))).1 := by
  let start := DAState.matching (profileOfScores x)
  induction N with
  | zero => simp [scoreRotationWalk_zero, scoreRotationWalk_succ, rotationParticipation]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, scoreRotationWalk_add x k 1 start]
    let out := scoreRotationWalk x k start
    change rotationParticipation out.1 + scoreWalkStepLength x k =
      rotationParticipation (out.1 ++ (scoreRotationWalk x 1 out.2).1)
    rw [scoreRotationWalk_succ]
    cases h : scoreWalkNextCycle x k with
    | none =>
      have h' : chooseQueriedRotation (scoreRotationGraph x out.2) = none := h
      simp [scoreWalkStepLength, h, h']
    | some ρ =>
      have h' : chooseQueriedRotation (scoreRotationGraph x out.2) = some ρ := h
      simp [scoreWalkStepLength, h, h', scoreRotationWalk_zero, scoreRotationWalk_succ, rotationParticipation]
theorem ae_sum_scoreWalkMeasurableLength_le (n N : ℕ) :
    ∀ᵐ x ∂continuousScoreLaw n, ∑ k ∈ Finset.range N, scoreWalkMeasurableLength x k ≤
      (n * (n - 1) : ℕ) := by
  filter_upwards [ae_goodClockInput n] with x hg
  have h := (scoreRotationWalk_legal x hg.1 N
    (DAState.isManOptimal_matching (profileOfScores x)).1).participation_le
  simp_rw [scoreWalkMeasurableLength_eq_stepLength hg]
  rw [← Nat.cast_sum, sum_scoreWalkStepLength_eq_rotationParticipation]
  exact_mod_cast h
end StepA4
end

-- ScoreRotationClockMaximal
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators Classical ENNReal Topology
namespace StepA4
variable {n : ℕ}
private theorem integrable_scoreWalkMeasurableLength (n k : ℕ) :
    Integrable (fun x : ScoreProfile n ↦ scoreWalkMeasurableLength x k)
      (continuousScoreLaw n) :=
  integrable_finsetSum _ fun b _ ↦ (integrable_const _).indicator
    (measurableSet_scoreRotationBranch k b.1 b.2)
theorem scoreWalkIncrement_moments (n k : ℕ) :
    let P := continuousScoreLaw n
    let d := fun x : ScoreProfile n ↦ scoreWalkIncrement x k
    MemLp d 2 P ∧ P[d | scoreWalkClockFiltration n k] =ᵐ[P] 0 ∧
      (∫ x, (d x)^2 ∂ P) = ∫ x, scoreWalkMeasurableLength x k ∂ P := by
  let P := continuousScoreLaw n
  let d := fun x : ScoreProfile n ↦ scoreWalkIncrement x k
  let B := @scoreWalkSelectionPartition n k
  have hB := measurableSet_scoreWalkSelectionPartition (n := n) k
  have hm := (scoreWalkClockFiltration n).le k
  have h0 := scoreWalkIncrement_ae_eq_zero_on_stopped (n := n) k
  refine clock_moments_of_fintype_partition P hm
    ((measurable_scoreWalkClock n (k + 1)).sub (measurable_scoreWalkClock n k))
    (integrable_scoreWalkMeasurableLength n k) hB
    (pairwise_disjoint_scoreWalkSelectionPartition k) (iUnion_scoreWalkSelectionPartition k)
    ?_ ?_ ?_
  · intro b
    cases b with
    | none =>
      exact (memLp_congr_ae h0).mpr (memLp_const (0 : ℝ))
    | some b => exact memLp_scoreWalkClock_increment_on_branch k b.1 b.2
  · intro b A hA
    cases b with
    | none =>
      have h : d =ᵐ[P.restrict (B none ∩ A)] 0 :=
        h0.filter_mono (ae_mono (Measure.restrict_mono inter_subset_left le_rfl))
      rw [integral_congr_ae h]
      simp
    | some b =>
      exact setIntegral_scoreWalkClock_increment_on_branch_inter k b.1 b.2 (hm A hA)
        (fun _ _ hxy ↦ mem_iff_of_scoreWalkClock_history_eq hA hxy)
  · intro b
    cases b with
    | none =>
      have hs : (fun x ↦ (d x)^2) =ᵐ[P.restrict (B none)] fun _ ↦ (0 : ℝ) :=
        h0.mono fun x hx ↦ by simp [d, hx]
      calc
        (∫ x in B none, (d x)^2 ∂ P) = 0 := by
          rw [integral_congr_ae hs, integral_zero]
        _ = ∫ x in B none, scoreWalkMeasurableLength x k ∂ P := by
          rw [integral_congr_ae ((ae_restrict_mem (hB none)).mono fun _ hx ↦
            scoreWalkMeasurableLength_of_mem_stopped hx), integral_zero]
    | some b =>
      have hlen : (fun x ↦ scoreWalkMeasurableLength x k) =ᵐ[P.restrict (B (some b))]
          fun _ ↦ (b.2.support.card : ℝ) :=
        (ae_restrict_mem (hB (some b))).mono fun _ hx ↦
          scoreWalkMeasurableLength_of_mem_branch hx
      rw [integral_congr_ae hlen, setIntegral_const, smul_eq_mul, mul_comm]
      exact setIntegral_sq_scoreWalkClock_increment_on_branch k b.1 b.2
theorem scoreWalkClock_zero (x : ScoreProfile n) : scoreWalkClock x 0 = 0 := by
  simp [scoreWalkClock, scoreRotationWalk_zero, scoreRotationWalk_succ, rotationParticipation]
theorem memLp_scoreWalkClock (n k : ℕ) :
    MemLp (fun x : ScoreProfile n ↦ scoreWalkClock x k) 2 (continuousScoreLaw n) := by
  induction k with
  | zero =>
    simpa only [scoreWalkClock_zero] using
      (memLp_const (0 : ℝ) :
        MemLp (fun _ : ScoreProfile n ↦ (0 : ℝ)) 2 (continuousScoreLaw n))
  | succ k ih =>
    have he : ((fun x : ScoreProfile n ↦ scoreWalkClock x k) +
        (fun x ↦ scoreWalkIncrement x k)) =ᵐ[continuousScoreLaw n]
        fun x ↦ scoreWalkClock x (k + 1) :=
      Eventually.of_forall fun x ↦ by simp [scoreWalkIncrement]
    exact (memLp_congr_ae he).mp (ih.add (scoreWalkIncrement_moments n k).1)
theorem sum_integral_scoreWalkIncrement_sq_le (n N : ℕ) :
    (∑ k ∈ Finset.range N, ∫ x, (scoreWalkIncrement x k)^2 ∂continuousScoreLaw n) ≤
      (n * (n - 1) : ℕ) := by
  let P := continuousScoreLaw n
  let f (k : ℕ) (x : ScoreProfile n) := scoreWalkMeasurableLength x k
  have hi (k : ℕ) : Integrable (f k) P := integrable_scoreWalkMeasurableLength n k
  change (∑ k ∈ Finset.range N, ∫ x, (scoreWalkIncrement x k)^2 ∂ P) ≤ _
  calc
    _ = ∑ k ∈ Finset.range N, ∫ x, f k x ∂ P :=
      Finset.sum_congr rfl fun k _ ↦ (scoreWalkIncrement_moments n k).2.2
    _ = ∫ x, ∑ k ∈ Finset.range N, f k x ∂ P :=
      (integral_finsetSum _ (fun k _ ↦ hi k)).symm
    _ ≤ ∫ _ : ScoreProfile n, ((n * (n - 1) : ℕ) : ℝ) ∂ P :=
      integral_mono_ae (integrable_finsetSum _ (fun k _ ↦ hi k)) (integrable_const _)
        (ae_sum_scoreWalkMeasurableLength_le n N)
    _ = _ := by simp [P]
theorem measure_scoreWalkClock_maximal_le (n N : ℕ) {a : ℝ} (ha : 0 < a) :
    continuousScoreLaw n {x | ∃ k ≤ N, a ≤ |scoreWalkClock x k|} ≤
      ENNReal.ofReal (((n * (n - 1) : ℕ) : ℝ) / a^2) :=
  measure_clock_maximal_le_of_step_energy (stronglyAdapted_scoreWalkClock n)
    (fun k _ ↦ memLp_scoreWalkClock n k) (Eventually.of_forall scoreWalkClock_zero)
    (fun k _ ↦ (scoreWalkIncrement_moments n k).2.1)
    (sum_integral_scoreWalkIncrement_sq_le n N) ha
theorem tendsto_measure_scoreWalkClock_large {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ ↦ continuousScoreLaw n
      {x | ∃ k ≤ n * (n - 1), ε * (n * Real.log n) ≤ |scoreWalkClock x k|})
      atTop (𝓝 0) := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hdiv := tendsto_inv_atTop_zero.comp (hlog.const_mul_atTop hε)
  have htop :
      Tendsto (fun n : ℕ ↦ ENNReal.ofReal ((ε * Real.log n)⁻¹ ^ 2)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, zero_pow (by decide : (2 : ℕ) ≠ 0), ENNReal.ofReal_zero]
      using ENNReal.tendsto_ofReal (hdiv.pow 2)
  refine tendsto_const_nhds.squeeze' htop (Eventually.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
  have hn₁ : (1 : ℝ) < n := by exact_mod_cast hn
  have hn₀ : (0 : ℝ) < n := zero_lt_one.trans hn₁
  have hlog₀ := Real.log_pos hn₁
  have ha : 0 < ε * ((n : ℝ) * Real.log n) := by positivity
  have hB : ((n * (n - 1) : ℕ) : ℝ) ≤ (n : ℝ)^2 := by
    exact_mod_cast (show n * (n - 1) ≤ n^2 by
      simpa only [pow_two] using Nat.mul_le_mul_left n (Nat.sub_le n 1))
  refine (measure_scoreWalkClock_maximal_le n (n * (n - 1)) ha).trans
    (ENNReal.ofReal_le_ofReal ?_)
  calc
    _ ≤ (n : ℝ)^2 / (ε * ((n : ℝ) * Real.log n))^2 :=
      div_le_div_of_nonneg_right hB (sq_nonneg _)
    _ = _ := by
      field_simp [hε.ne', hn₀.ne', hlog₀.ne']
end StepA4
end

-- ScoreRotationLengthBudgets
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators Classical ENNReal Topology
namespace StepA4
end StepA4
end

-- ScoreRotationBandAbundance
section
open Filter MeasureTheory Set StableMarriage
open scoped ENNReal Topology
namespace StepA4
private def scoreWalkBandEndpoints (n : ℕ) : Set (ScoreProfile n) :=
  {x | (n : ℝ) ^ (2 / 5 : ℝ) < scoreWalkFemaleTotal x 0 ∧
    scoreWalkFemaleTotal x (n * (n - 1)) ≤ (n : ℝ) ^ (1 / 5 : ℝ)}
private theorem tendsto_measure_badFemaleLogGeometry_zero :
    Tendsto (fun n ↦ continuousScoreLaw n (goodFemaleLogGeometry n)ᶜ) atTop (𝓝 0) := by
  have hrate :
      Tendsto (fun n : ℕ ↦ ENNReal.ofReal ((n : ℝ) ^ (-(1 : ℝ)))) atTop (𝓝 0) := by
    simp only [Real.rpow_neg_one]
    simpa only [ENNReal.ofReal_zero, one_div] using
      ENNReal.tendsto_ofReal (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
  exact tendsto_const_nhds.squeeze' hrate (Eventually.of_forall fun _ ↦ zero_le)
    (eventually_measure_badFemaleLogGeometry_le 1)
end StepA4
end

-- ScoreRotationAnchorAbundance
section
open Filter MeasureTheory Set StableMarriage
open scoped ENNReal Topology
namespace StepA4
end StepA4
end

-- ScoreRotationNonTiny
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators Classical ENNReal Topology
namespace StepA4
end StepA4
end

-- ScoreRotationAnchorProbability
section
open Filter MeasureTheory Set
open scoped ENNReal Topology
namespace StepA4
end StepA4
end

-- DAEndpointAsymptotics
section
open Filter MeasureTheory Set StableMarriage
open scoped ENNReal Topology StepA4
namespace StepA4
theorem measure_scoreDAProposalCount_gt (n T : ℕ) :
    continuousScoreLaw n {x | T < (DAState.run (profileOfScores x) (n * n)).proposalCount} =
      (uniformProfile n).toMeasure {p | T < (DAState.run p (n * n)).proposalCount} := by
  let E : Set (Profile n) := {p | T < (DAState.run p (n * n)).proposalCount}
  have hm := measurePreserving_profileOfScores n
  change continuousScoreLaw n (profileOfScores ⁻¹' E) = (uniformProfile n).toMeasure E
  rw [← Measure.map_apply hm.measurable MeasurableSet.of_discrete, hm.map_eq]
theorem tendsto_measure_badScoreWalkBandEndpoints :
    Tendsto (fun n ↦ continuousScoreLaw n (scoreWalkBandEndpoints n)ᶜ) atTop (𝓝 0) := by
  have hcap : Tendsto (fun n ↦ continuousScoreLaw n {x |
      daProposalCap n < (DAState.run (profileOfScores x) (n * n)).proposalCount}) atTop (𝓝 0) := by
    simpa only [measure_scoreDAProposalCount_gt] using
      tendsto_measure_daProposalCount_gt_daProposalCap
  have hstart : Tendsto (fun n ↦ continuousScoreLaw n {x |
      scoreWalkFemaleTotal x 0 ≤ (n : ℝ) ^ (2 / 5 : ℝ)}) atTop (𝓝 0) :=
    tendsto_measure_badManOptimalScore_of_proposalCap daProposalCap
      eventually_daProposalCap_le hcap
  have hend := tendsto_measure_badScoreWalkUpperEndpoint eventually_daProposalCap_le
    tendsto_measure_daProposalCount_gt_daProposalCap
  have hsum := hstart.add hend
  rw [add_zero] at hsum
  refine tendsto_const_nhds.squeeze' hsum (Eventually.of_forall fun _ ↦ zero_le) ?_
  apply Eventually.of_forall
  intro n
  have he : (scoreWalkBandEndpoints n)ᶜ =
      {x | scoreWalkFemaleTotal x 0 ≤ (n : ℝ) ^ (2 / 5 : ℝ)} ∪
      {x | (n : ℝ) ^ (1 / 5 : ℝ) < scoreWalkFemaleTotal x (n * (n - 1))} := by
    ext x
    simp only [scoreWalkBandEndpoints, Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_union,
      not_and_or, not_lt, not_le]
  rw [he]
  exact measure_union_le _ _
end StepA4
end

-- PivotMarkedCutoffBridge
section
open Filter MeasureTheory ProbabilityTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace StepA4
section IndependentRows
variable {n : ℕ} {Ω : Fin n → Type*} [∀ i, MeasurableSpace (Ω i)]
  (ν : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (ν i)]
  (out : ∀ i, Ω i → Option (Fin n)) (g : ∀ i, Fin n → Ω i → ℝ)
  [MeasurableSpace (Option (Fin n))] [MeasurableSingletonClass (Option (Fin n))]
end IndependentRows
end StepA4
end

-- PivotSupportMassTail
section
open Filter MeasureTheory Set StableMarriage
open scoped ENNReal Topology
namespace StepA4
end StepA4
end

-- PivotForwardIncrementTail
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace StepA4
end StepA4
end

-- PivotEligibleAbundance
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace StepA4
end StepA4
end

-- PivotAggregateMean
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace StepA4
variable {n : ℕ}
end StepA4
end

-- PivotDecorationRevealInvariance
section
open MeasureTheory Set StableMarriage
namespace StepA4
variable {n : ℕ} {μ ρ σ : Matching n} {x y : ScoreProfile n}
  {flag : OffDiagonalCellIndex n → Bool}
private structure SameReverseReveal (μ : Matching n) (flag : OffDiagonalCellIndex n → Bool)
    (x y : ScoreProfile n) : Prop where
  diagonal : (splitScorePairs μ x).1 = (splitScorePairs μ y).1
  observed : forwardRevealWithColumns flag (splitScorePairs μ x).2 =
    forwardRevealWithColumns flag (splitScorePairs μ y).2
theorem SameReverseReveal.symm (h : SameReverseReveal μ flag x y) :
    SameReverseReveal μ flag y x := ⟨h.diagonal.symm, h.observed.symm⟩
end StepA4
end

-- PivotLaterRevealReplay
section
open MeasureTheory Set StableMarriage
namespace StepA4
variable {n : ℕ}
private def ScoreForwardEligible (x : ScoreProfile n) (A : Matching n) (m w : Fin n) : Prop :=
  x (.inl m) (A m) < x (.inl m) w ∧ x (.inr w) m < x (.inr w) (A.symm w)
private def ScorePairAgrees (x y : ScoreProfile n) (m w : Fin n) : Prop :=
  x (.inl m) w = y (.inl m) w ∧ x (.inr w) m = y (.inr w) m
private structure FullForwardRevealAgrees (x y : ScoreProfile n) (A : Matching n) : Prop where
  spouse : ∀ m, ScorePairAgrees x y m (A m)
  eligible_iff : ∀ m w, ScoreForwardEligible x A m w ↔ ScoreForwardEligible y A m w
  cell : ∀ m w, ScoreForwardEligible x A m w → ScorePairAgrees x y m w
variable {x y : ScoreProfile n} {A B : Matching n}
theorem FullForwardRevealAgrees.symm (h : FullForwardRevealAgrees x y A) :
    FullForwardRevealAgrees y x A where
  spouse m := ⟨(h.spouse m).1.symm, (h.spouse m).2.symm⟩
  eligible_iff m w := (h.eligible_iff m w).symm
  cell m w hw :=
    let hc := h.cell m w ((h.eligible_iff m w).mpr hw)
    ⟨hc.1.symm, hc.2.symm⟩
end StepA4
end

-- PivotComparableCentered
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA4
private structure PivotCountParameters where
  lowerLength : ℝ
  upperLength : ℝ
  geometryBudget : ℝ
  supportCap : ℕ
  shortCutoff : ℕ
private abbrev PivotMark (n : ℕ) := Matching n × Matching n
namespace PivotCountParameters
variable {n : ℕ}
private noncomputable def localCount (q : PivotCountParameters) (i : PivotMark n) :
    ScoreProfile n → ℝ :=
  localFilteredDecorationCount q.lowerLength q.upperLength q.geometryBudget
    q.supportCap q.shortCutoff i.1 i.2
private noncomputable def onStableMark (i : PivotMark n) (f : ScoreProfile n → ℝ) :
    ScoreProfile n → ℝ :=
  {x | IsScoreStable x i.1}.indicator f
private noncomputable def count (q : PivotCountParameters) (i : PivotMark n) :
    ScoreProfile n → ℝ :=
  onStableMark i (q.localCount i)
end PivotCountParameters
end StepA4
end

-- PivotTwoCycleForest
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace StepA4
end StepA4
end

-- LogarithmicCutoffs
section
open Filter
open scoped Topology BigOperators
namespace StepA4
end StepA4
end

-- PivotVarianceClosure
section
open Filter MeasureTheory Set StableMarriage Asymptotics
open scoped BigOperators ENNReal Topology
namespace StepA4
namespace PivotCountParameters
variable {n : ℕ}
end PivotCountParameters
variable {n : ℕ}
namespace PivotCountParameters
end PivotCountParameters
end StepA4
end

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 30000 in
theorem OMA.solution : OMA.R_LennonPittel_lennon_pittel_conjecture_R3_H2_R1_H2_R1_H1_R1.H4 :=
  ⟨@StepA4.tendsto_measure_scoreWalkClock_large, @StepA4.tendsto_measure_badScoreWalkBandEndpoints, @StepA4.tendsto_measure_badFemaleLogGeometry_zero, @StepA4.eventually_expectedNumStableMatchings_le_meanUpper⟩
