import OMAReductions.R_LennonPittel_lennon_pittel_conjecture_R3_H2_R1_H2_R1
import Mathlib

/-! Port of part of the Lennon-Pittel lower-tail proof by Bo Cowgill,
https://github.com/bocowgill/lennon-pittel at commit cf950d0596591bba912b1568aa394f99986f8191,
Copyright 2026 Bo Cowgill, used under the Apache License 2.0.
Changes: modules flattened into one file, comments removed, declarations not needed here dropped,
names adapted to the pinned Mathlib, the marked model renamed and tied to the parent reduction's
definitions (after moon-4's port of the same model for the parent step).
This reduction proves the abundance of the conditional means from eight lemmas of the source, grouped
into four hypotheses. -/


-- StandardExponentialScoreLaw
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace AbunLP
end AbunLP
end

-- BoundedProductChernoff
section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace AbunLP
end AbunLP
end

-- IidScoreRanks
section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace AbunLP
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
end AbunLP
end

-- MarkedCounting
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace AbunLP
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
end AbunLP
end

-- ScoreRanks
section
open Function MeasureTheory Set
namespace AbunLP
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
end AbunLP
end

-- ContinuousScoreBridge
section
open scoped BigOperators ENNReal AbunLP
open MeasureTheory Set
namespace AbunLP
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
end AbunLP
end

-- CoexposureGoodScores
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal AbunLP
namespace AbunLP
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
private def goodCoexposureScores (n : ℕ) : Set (ScoreProfile n) :=
  {x | (∀ r, Function.Injective (x r)) ∧ (∀ r i, x r i ∈ Ioo (0 : ℝ) 1) ∧
    ∀ μ, IsStable (profileOfScores x) μ → GoodSpouseScores x μ}
private theorem measurable_scoreCoordinate (r : Fin n ⊕ Fin n) (i : Fin n) :
    Measurable (fun x : ScoreProfile n ↦ x r i) :=
  (measurable_pi_apply i).comp (measurable_pi_apply r)
theorem measurable_femaleSpouseScore (μ : Matching n) (j : Fin n) :
    Measurable (fun x : ScoreProfile n ↦ femaleSpouseScore x μ j) :=
  measurable_scoreCoordinate (.inr j) (μ.symm j)
theorem measurable_femaleSpouseTotal (μ : Matching n) :
    Measurable (fun x : ScoreProfile n ↦ femaleSpouseTotal x μ) :=
  Finset.measurable_sum _ (fun j _ ↦ measurable_femaleSpouseScore μ j)
end AbunLP
end

-- CoexposureScoreEstimates
section
open Filter MeasureTheory Set StableMarriage
open scoped ENNReal BigOperators Topology
namespace AbunLP
private def scoreSimplex (n : ℕ) (s : ℝ) : Set (Fin n → ℝ) :=
  {y | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ s}
end AbunLP
end

-- PittelSimplexRadial
section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace AbunLP
private noncomputable def spouseAngle {n : ℕ} (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  x i / (∑ j, x j)
private noncomputable def spouseAngularLaw (n : ℕ) : Measure (Fin n → ℝ) :=
  (n.factorial : ℝ≥0∞) • Measure.map spouseAngle (volume.restrict (scoreSimplex n 1))
end AbunLP
end

-- PittelSimplexMoments
section
open Filter MeasureTheory Set
open scoped ENNReal BigOperators Topology
namespace AbunLP
private noncomputable def pittelAngularSquareScore {n : ℕ} (w : Fin n → ℝ) : ℝ :=
  (n : ℝ) * ∑ i, w i ^ 2
section Moments
variable {n : ℕ} {μ : Measure (Fin n → ℝ)} [IsProbabilityMeasure μ]
variable (hμ : ∀ᵐ w ∂μ, ∀ i, w i ∈ Icc (0 : ℝ) 1)
variable (hmoment : ∀ a : Fin n → ℕ, (∫ w, ∏ i, w i ^ a i ∂μ) =
  (∏ i, ((a i).factorial : ℝ)) * ((n - 1).factorial : ℝ) /
    ((n - 1 + ∑ i, a i).factorial : ℝ))
end Moments
end AbunLP
end

-- ExponentialSpouseSquareTail
section
open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal Topology
namespace AbunLP
local instance : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
  isProbabilityMeasure_expMeasure (by norm_num)
end AbunLP
end

-- ExponentialSpouseAngles
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace AbunLP
end AbunLP
end

-- CoexposureScoreRow
section
open Set
open scoped BigOperators
namespace AbunLP
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
private noncomputable def rowEligibilityProbability (x y : ℝ) : ℝ :=
  (1 - x) * y / (1 - x * y)
theorem rowEligibilityProbability_nonneg {x y : ℝ} (hx : x ∈ Ico (0 : ℝ) 1)
    (hy : y ∈ Icc (0 : ℝ) 1) : 0 ≤ rowEligibilityProbability x y := by
  unfold rowEligibilityProbability
  have hxy : x * y ≤ x := by simpa using mul_le_mul_of_nonneg_left hy.2 hx.1
  exact div_nonneg (mul_nonneg (sub_nonneg.mpr hx.2.le) hy.1) (by linarith [hx.2])
theorem rowEligibilityProbability_le_one {x y : ℝ} (hx : x ∈ Ico (0 : ℝ) 1)
    (hy : y ∈ Icc (0 : ℝ) 1) : rowEligibilityProbability x y ≤ 1 := by
  unfold rowEligibilityProbability
  have hxy : x * y ≤ x := by simpa using mul_le_mul_of_nonneg_left hy.2 hx.1
  rw [div_le_iff₀ (by linarith [hx.2])]
  nlinarith [hy.2]
theorem mul_le_rowEligibilityProbability {x y : ℝ} (hx : x ∈ Ico (0 : ℝ) 1)
    (hy : y ∈ Icc (0 : ℝ) 1) : (1 - x) * y ≤ rowEligibilityProbability x y := by
  unfold rowEligibilityProbability
  have hxy : x * y ≤ x := by simpa using mul_le_mul_of_nonneg_left hy.2 hx.1
  rw [le_div_iff₀ (by linarith [hx.2])]
  exact mul_le_of_le_one_right (mul_nonneg (sub_nonneg.mpr hx.2.le) hy.1)
    (by nlinarith [mul_nonneg hx.1 hy.1])
theorem scoreRowSuccessor_le {J : Finset ι} {y : ι → ℝ} {x v : ℝ}
    (hx : x ∈ Ico (0 : ℝ) 1) (hy : ∀ j ∈ J, y j ∈ Icc (0 : ℝ) 1)
    (hv : v ∈ Icc (0 : ℝ) 1) (hsum : 0 < ∑ j ∈ J, y j) :
    rowEligibilityProbability x v *
        scoreRowMass J (fun j ↦ rowEligibilityProbability x (y j)) 0 1 ≤
      v / ((1 - x * v) * (∑ j ∈ J, y j)) := by
  let r := (1 - x) * (∑ j ∈ J, y j)
  have hx₁ : 0 < 1 - x := sub_pos.mpr hx.2
  have hr : 0 < r := mul_pos hx₁ hsum
  have hr' : r ≤ ∑ j ∈ J, rowEligibilityProbability x (y j) := by
    dsimp [r]
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j hj ↦ mul_le_rowEligibilityProbability hx (hy j hj)
  have hmass :
      scoreRowMass J (fun j ↦ rowEligibilityProbability x (y j)) 0 1 ≤ 1 / r := by
    simpa using scoreRowMass_le_exp_tail
      (fun j hj ↦ rowEligibilityProbability_nonneg hx (hy j hj))
      (fun j hj ↦ rowEligibilityProbability_le_one hx (hy j hj))
      hr hr' le_rfl (by norm_num) le_rfl
  have hden : 0 < 1 - x * v := by
    have h := mul_le_mul_of_nonneg_left hv.2 hx.1
    nlinarith [hx.2]
  refine (mul_le_mul_of_nonneg_left hmass (rowEligibilityProbability_nonneg hx hv)).trans_eq ?_
  dsimp [r, rowEligibilityProbability]
  field_simp
section FiniteRows
variable [Fintype ι] [DecidableEq ι]
end FiniteRows
theorem scoreRowMass_affine_eq {J : Finset ι} {y : ι → ℝ} {x : ℝ}
    (hx : x ∈ Ico (0 : ℝ) 1) (hy : ∀ j ∈ J, y j ∈ Icc (0 : ℝ) 1) :
    scoreRowMass J y x 1 =
      (1 - x) * scoreRowKernel J y x *
        scoreRowMass J (fun j ↦ rowEligibilityProbability x (y j)) 0 1 := by
  have hpoint (t : ℝ) :
      scoreRowKernel J y (x + (1 - x) * t) =
        scoreRowKernel J y x *
          scoreRowKernel J (fun j ↦ rowEligibilityProbability x (y j)) t := by
    unfold scoreRowKernel
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j hj
    unfold rowEligibilityProbability
    have hxy : x * y j ≤ x := by simpa using mul_le_mul_of_nonneg_left (hy j hj).2 hx.1
    have hd : 1 - x * y j ≠ 0 := by linarith [hx.2]
    field_simp
    ring
  have haff :
      (1 - x) * (∫ t in (0 : ℝ)..1, scoreRowKernel J y (x + (1 - x) * t)) =
        scoreRowMass J y x 1 := by
    unfold scoreRowMass
    have h := intervalIntegral.smul_integral_comp_add_mul (a := (0 : ℝ)) (b := 1)
      (scoreRowKernel J y) (1 - x) x
    simp only [smul_eq_mul, mul_zero, add_zero, mul_one] at h
    rw [show x + (1 - x) = 1 by ring] at h
    exact h
  rw [← haff]
  simp_rw [hpoint, intervalIntegral.integral_const_mul, scoreRowMass]
  ring
theorem scoreRowSuccessor_unnormalized_le {J : Finset ι} {y : ι → ℝ} {x v : ℝ}
    (hx : x ∈ Ico (0 : ℝ) 1) (hy : ∀ j ∈ J, y j ∈ Icc (0 : ℝ) 1)
    (hv : v ∈ Icc (0 : ℝ) 1) (hsum : 0 < ∑ j ∈ J, y j) :
    v * scoreRowMass J y x 1 ≤ ((1 - x * v) * scoreRowKernel J y x) *
      (v / ((1 - x * v) * (∑ j ∈ J, y j))) := by
  have hxv : x * v ≤ x := by simpa using mul_le_mul_of_nonneg_left hv.2 hx.1
  have hden : 0 < 1 - x * v := by linarith [hx.2]
  have hK := scoreRowKernel_nonneg (fun j hj ↦ (hy j hj).1)
    (fun j hj ↦ (hy j hj).2) ⟨hx.1, hx.2.le⟩
  calc
    _ = ((1 - x * v) * scoreRowKernel J y x) *
        (rowEligibilityProbability x v *
          scoreRowMass J (fun j ↦ rowEligibilityProbability x (y j)) 0 1) := by
      rw [scoreRowMass_affine_eq hx hy, rowEligibilityProbability]
      have hden' : 1 - v * x ≠ 0 := by simpa only [mul_comm] using hden.ne'
      field_simp [hden.ne', hden']
    _ ≤ _ := mul_le_mul_of_nonneg_left (scoreRowSuccessor_le hx hy hv hsum)
      (mul_nonneg hden.le hK)
section SuccessorMass
open MeasureTheory
open scoped ENNReal
private noncomputable def rowNonblockingLaw (x y : ℝ) : Measure (ℝ × ℝ) :=
  (unitScoreLaw.prod unitScoreLaw).restrict (Iio x ×ˢ Iio y)ᶜ
private instance (x y : ℝ) : IsFiniteMeasure (rowNonblockingLaw x y) := by
  unfold rowNonblockingLaw
  infer_instance
theorem unitScoreLaw_apply_Iio {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) :
    unitScoreLaw (Iio a) = ENNReal.ofReal a := by
  rw [unitScoreLaw, Measure.restrict_apply measurableSet_Iio]
  have heq : Iio a ∩ Icc (0 : ℝ) 1 = Ico 0 a := by
    ext t
    change (t < a ∧ 0 ≤ t ∧ t ≤ 1) ↔ (0 ≤ t ∧ t < a)
    exact ⟨fun h ↦ ⟨h.2.1, h.1⟩, fun h ↦ ⟨h.2, h.1, h.2.le.trans ha.2⟩⟩
  rw [heq, Real.volume_Ico, sub_zero]
theorem rowNonblockingLaw_apply_avoiding {x a y : ℝ} (hxa : x ≤ a)
    (ha : a ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    rowNonblockingLaw x y (Iio a ×ˢ Iio y)ᶜ = ENNReal.ofReal (1 - a * y) := by
  have hs : MeasurableSet (Iio a ×ˢ Iio y) := measurableSet_Iio.prod measurableSet_Iio
  have hsub : (Iio x ×ˢ Iio y : Set (ℝ × ℝ)) ⊆ Iio a ×ˢ Iio y :=
    fun _ h ↦ ⟨h.1.trans_le hxa, h.2⟩
  rw [rowNonblockingLaw, Measure.restrict_apply hs.compl,
    inter_eq_left.mpr (compl_subset_compl.mpr hsub), measure_compl hs (measure_ne_top _ _),
    measure_univ, Measure.prod_prod, unitScoreLaw_apply_Iio ha, unitScoreLaw_apply_Iio hy,
    ← ENNReal.ofReal_mul ha.1, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (mul_nonneg ha.1 hy.1)]
private def scoreSuccessorPairEvent (x v : ℝ) (y : ι → ℝ) :
    Set ((ℝ × ℝ) × (ι → ℝ × ℝ)) :=
  {z | x < z.1.1 ∧ z.1.2 < v ∧ ∀ h, ¬((z.2 h).1 < z.1.1 ∧ (z.2 h).2 < y h)}
theorem measurableSet_scoreSuccessorPairEvent [Fintype ι] (x v : ℝ) (y : ι → ℝ) :
    MeasurableSet (scoreSuccessorPairEvent x v y) := by
  unfold scoreSuccessorPairEvent
  simp only [ofPred_and, ofPred_forall]
  refine (measurableSet_lt measurable_const measurable_fst.fst).inter
    ((measurableSet_lt measurable_fst.snd measurable_const).inter
      (MeasurableSet.iInter fun h ↦ ?_))
  have hmeas : Measurable (fun z : (ℝ × ℝ) × (ι → ℝ × ℝ) ↦ z.2 h) :=
    (measurable_pi_apply h).comp measurable_snd
  exact ((measurableSet_lt hmeas.fst measurable_fst.fst).inter
    (measurableSet_lt hmeas.snd measurable_const)).compl
private theorem scoreSuccessorPairEvent_section {x v : ℝ} (y : ι → ℝ) (uv : ℝ × ℝ)
    (h : uv ∈ Ioi x ×ˢ Iio v) :
    Prod.mk uv ⁻¹' scoreSuccessorPairEvent x v y =
      Set.pi univ (fun j ↦ (Iio uv.1 ×ˢ Iio (y j))ᶜ) := by
  ext z
  simp only [mem_preimage, scoreSuccessorPairEvent, mem_ofPred_eq, mem_pi, mem_univ,
    true_implies, mem_compl_iff, mem_prod, mem_Iio]
  exact ⟨fun h' ↦ h'.2.2, fun h' ↦ ⟨h.1, h.2, h'⟩⟩
private theorem scoreSuccessorPairEvent_section_empty {x v : ℝ} (y : ι → ℝ) (uv : ℝ × ℝ)
    (h : uv ∉ Ioi x ×ˢ Iio v) :
    Prod.mk uv ⁻¹' scoreSuccessorPairEvent x v y = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro z hz
  exact h ⟨hz.1, hz.2.1⟩
theorem scoreSuccessorPairEvent_mass [Fintype ι] {x v : ℝ} {y : ι → ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1)
    (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) :
    ((rowNonblockingLaw x v).prod (Measure.pi fun j ↦ rowNonblockingLaw x (y j)))
        (scoreSuccessorPairEvent x v y) =
      ENNReal.ofReal (v * scoreRowMass Finset.univ y x 1) := by
  let T : Set (ℝ × ℝ) := Ioi x ×ˢ Iio v
  let F : ℝ × ℝ → ℝ≥0∞ := fun uv ↦ ENNReal.ofReal (scoreRowKernel Finset.univ y uv.1)
  have hT : MeasurableSet T := measurableSet_Ioi.prod measurableSet_Iio
  have hsupp : ∀ᵐ uv ∂rowNonblockingLaw x v, uv ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := by
    unfold rowNonblockingLaw unitScoreLaw
    rw [Measure.prod_restrict]
    exact ae_restrict_of_ae (ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc))
  rw [Measure.prod_apply (measurableSet_scoreSuccessorPairEvent x v y)]
  have hsection :
      (fun uv ↦ (Measure.pi fun j ↦ rowNonblockingLaw x (y j))
        (Prod.mk uv ⁻¹' scoreSuccessorPairEvent x v y)) =ᵐ[rowNonblockingLaw x v]
          T.indicator F := by
    filter_upwards [hsupp] with uv hu
    by_cases ht : uv ∈ T
    · rw [scoreSuccessorPairEvent_section y uv ht, Measure.pi_pi, Set.indicator_of_mem ht]
      simp only [rowNonblockingLaw_apply_avoiding ht.1.le hu.1 (hy _)]
      unfold F scoreRowKernel
      exact (ENNReal.ofReal_prod_of_nonneg fun j _ ↦ sub_nonneg.mpr (by
        nlinarith [(hy j).1, (hy j).2, hu.1.2,
          mul_nonneg (sub_nonneg.mpr hu.1.2) (hy j).1])).symm
    · rw [scoreSuccessorPairEvent_section_empty y uv ht, measure_empty, Set.indicator_of_notMem ht]
  rw [lintegral_congr_ae hsection, lintegral_indicator hT]
  have hsub : T ⊆ (Iio x ×ˢ Iio v : Set (ℝ × ℝ))ᶜ := by
    intro uv h h'
    exact (not_lt_of_ge (show x < uv.1 from h.1).le) (show uv.1 < x from h'.1)
  have hrestrict : (rowNonblockingLaw x v).restrict T =
      (unitScoreLaw.restrict (Ioi x)).prod (unitScoreLaw.restrict (Iio v)) := by
    rw [rowNonblockingLaw, Measure.restrict_restrict_of_subset hsub]
    exact (Measure.prod_restrict _ _).symm
  rw [hrestrict]
  have hf : Measurable fun u ↦ ENNReal.ofReal (scoreRowKernel Finset.univ y u) :=
    (continuous_scoreRowKernel Finset.univ y).measurable.ennreal_ofReal
  unfold F
  rw [show (fun uv : ℝ × ℝ ↦ ENNReal.ofReal (scoreRowKernel Finset.univ y uv.1)) =
    (fun uv : ℝ × ℝ ↦ ENNReal.ofReal (scoreRowKernel Finset.univ y uv.1) * (1 : ℝ≥0∞)) by
      funext uv; rw [mul_one]]
  rw [lintegral_prod_mul hf.aemeasurable measurable_const.aemeasurable, lintegral_const, one_mul,
    Measure.restrict_apply_univ, unitScoreLaw_apply_Iio hv]
  have hleft : unitScoreLaw.restrict (Ioi x) = volume.restrict (Ioc x 1) := by
    rw [unitScoreLaw, Measure.restrict_restrict measurableSet_Ioi]
    congr 1
    ext u
    change (x < u ∧ 0 ≤ u ∧ u ≤ 1) ↔ (x < u ∧ u ≤ 1)
    exact ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun h ↦ ⟨h.1, hx.1.trans h.1.le, h.2⟩⟩
  rw [hleft, scoreRowMass, intervalIntegral.integral_of_le hx.2,
    ENNReal.ofReal_mul hv.1, mul_comm (ENNReal.ofReal v)]
  congr 1
  rw [ofReal_integral_eq_lintegral_ofReal]
  · exact ((continuous_scoreRowKernel Finset.univ y).intervalIntegrable x 1).1
  · filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioc : MeasurableSet (Ioc x 1))]
      with u hu
    exact scoreRowKernel_nonneg (fun j _ ↦ (hy j).1) (fun j _ ↦ (hy j).2)
      ⟨hx.1.trans hu.1.le, hu.2⟩
theorem rowNonblockingLaw_apply_univ {x y : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    rowNonblockingLaw x y univ = ENNReal.ofReal (1 - x * y) := by
  rw [← rowNonblockingLaw_apply_avoiding le_rfl hx hy]
  unfold rowNonblockingLaw
  rw [Measure.restrict_apply_univ,
    Measure.restrict_apply (measurableSet_Iio.prod measurableSet_Iio).compl, inter_self]
theorem scoreSuccessorPairEvent_mass_le [Fintype ι] {x v : ℝ} {y : ι → ℝ}
    (hx : x ∈ Ico (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1)
    (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) (hsum : 0 < ∑ j, y j) :
    ((rowNonblockingLaw x v).prod (Measure.pi fun j ↦ rowNonblockingLaw x (y j)))
        (scoreSuccessorPairEvent x v y) ≤
      (rowNonblockingLaw x v univ * ∏ j, rowNonblockingLaw x (y j) univ) *
        ENNReal.ofReal (v / ((1 - x * v) * (∑ j, y j))) := by
  have hxy (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1) : 0 < 1 - x * z := by
    have h := mul_le_mul_of_nonneg_left hz.2 hx.1
    linarith [hx.2]
  have hK := scoreRowKernel_nonneg (J := (Finset.univ : Finset ι))
    (fun j _ ↦ (hy j).1) (fun j _ ↦ (hy j).2) ⟨hx.1, hx.2.le⟩
  rw [scoreSuccessorPairEvent_mass ⟨hx.1, hx.2.le⟩ hv hy,
    rowNonblockingLaw_apply_univ ⟨hx.1, hx.2.le⟩ hv]
  simp only [rowNonblockingLaw_apply_univ (show x ∈ Icc (0 : ℝ) 1 from ⟨hx.1, hx.2.le⟩) (hy _)]
  unfold scoreRowKernel at hK
  rw [← ENNReal.ofReal_prod_of_nonneg (fun j _ ↦ (hxy (y j) (hy j)).le),
    ← ENNReal.ofReal_mul (hxy v hv).le, ← ENNReal.ofReal_mul
      (mul_nonneg (hxy v hv).le hK)]
  exact ENNReal.ofReal_le_ofReal (scoreRowSuccessor_unnormalized_le hx
    (fun j _ ↦ hy j) hv hsum)
end SuccessorMass
end AbunLP
end

-- ExposedRotations
section
open StableMarriage
namespace AbunLP
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
end AbunLP
end

-- CoexposureScoreProduct
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace AbunLP
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
private def nonblockingScoreCell (x y : ℝ) : Set (ℝ × ℝ) :=
  (Set.Iio x ×ˢ Set.Iio y)ᶜ
private def offDiagonalNonblocking {n : ℕ} (d : DiagonalScorePairs n) :
    Set (OffDiagonalScorePairs n) :=
  Set.univ.pi fun q ↦
    nonblockingScoreCell (diagonalPairAt d q.val.1).1 (diagonalPairAt d q.val.2).2
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
theorem measurePreserving_offDiagonalRowsEquiv {n : ℕ}
    (m : {q : ScorePairIndex n // q.1 ≠ q.2} → Measure (ℝ × ℝ))
    [∀ q, SigmaFinite (m q)] :
    MeasurePreserving (offDiagonalRowsEquiv n) (Measure.pi m)
      (Measure.pi fun i : Fin n ↦ Measure.pi fun j : {j : Fin n // i ≠ j} ↦
        m ⟨(i,j), j.property⟩) := by
  refine MeasurePreserving.symm (offDiagonalRowsEquiv n).symm ?_
  refine ⟨(offDiagonalRowsEquiv n).symm.measurable, (Measure.pi_eq fun s _ ↦ ?_).symm⟩
  rw [MeasurableEquiv.map_apply]
  rw [show (offDiagonalRowsEquiv n).symm ⁻¹' (Set.univ.pi s) =
      Set.univ.pi (fun i ↦ Set.univ.pi fun j : {j : Fin n // i ≠ j} ↦ s ⟨(i,j), j.property⟩) by
    ext v
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left]
    refine ⟨fun h i j ↦ ?_, fun h q ↦ ?_⟩
    · simpa [offDiagonalRowsEquiv] using h ⟨(i,j), j.property⟩
    · simpa [offDiagonalRowsEquiv] using h q.val.1 ⟨q.val.2, q.property⟩]
  simp_rw [Measure.pi_pi]
  rw [← Fintype.prod_sigma']
  exact Fintype.prod_equiv (offDiagonalIndexEquiv n).symm _ _ fun _ ↦ rfl
private noncomputable def stableScoreRowLaw {n : ℕ} (d : DiagonalScorePairs n) (i : Fin n) :
    Measure ({j : Fin n // i ≠ j} → ℝ × ℝ) :=
  Measure.pi fun j ↦ unitScorePairLaw.restrict
    (nonblockingScoreCell (diagonalPairAt d i).1 (diagonalPairAt d j.val).2)
private instance {n : ℕ} (d : DiagonalScorePairs n) (i : Fin n) :
    IsFiniteMeasure (stableScoreRowLaw d i) :=
  inferInstanceAs (IsFiniteMeasure (Measure.pi fun j : {j : Fin n // i ≠ j} ↦
    unitScorePairLaw.restrict
      (nonblockingScoreCell (diagonalPairAt d i).1 (diagonalPairAt d j.val).2)))
theorem offDiagonalScoreLaw_restrict_nonblocking {n : ℕ} (d : DiagonalScorePairs n) :
    (offDiagonalScoreLaw n).restrict (offDiagonalNonblocking d) =
      Measure.pi fun q : {q : ScorePairIndex n // q.1 ≠ q.2} ↦ unitScorePairLaw.restrict
        (nonblockingScoreCell (diagonalPairAt d q.val.1).1 (diagonalPairAt d q.val.2).2) :=
  Measure.restrict_pi_pi _ _
theorem measurePreserving_offDiagonalRowsEquiv_stable {n : ℕ} (d : DiagonalScorePairs n) :
    MeasurePreserving (offDiagonalRowsEquiv n)
      ((offDiagonalScoreLaw n).restrict (offDiagonalNonblocking d))
      (Measure.pi (stableScoreRowLaw d)) := by
  rw [offDiagonalScoreLaw_restrict_nonblocking]
  exact measurePreserving_offDiagonalRowsEquiv _
theorem continuousScoreLaw_lintegral_stable_and_diagonal {n : ℕ} (μ : Matching n)
    {C : Set (DiagonalScorePairs n)} (hC : MeasurableSet C)
    {f : ScoreProfile n → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x in {x | IsScoreStable x μ ∧ (splitScorePairs μ x).1 ∈ C}, f x
      ∂continuousScoreLaw n) =
      ∫⁻ d in C, ∫⁻ v, f ((splitScorePairs μ).symm (d,v))
        ∂((offDiagonalScoreLaw n).restrict (offDiagonalNonblocking d)) ∂diagonalScoreLaw n := by
  let S : Set (ScoreProfile n) := {x | IsScoreStable x μ ∧ (splitScorePairs μ x).1 ∈ C}
  let E : Set (DiagonalScorePairs n × OffDiagonalScorePairs n) :=
    {z | z.1 ∈ C ∧ z.2 ∈ offDiagonalNonblocking z.1}
  let f' := f ∘ (splitScorePairs μ).symm
  have hS : MeasurableSet S := (measurableSet_isScoreStable μ).inter
    ((measurable_fst.comp (splitScorePairs μ).measurable) hC)
  have hE_pre : E = (splitScorePairs μ).symm ⁻¹' S := by
    ext z
    have h := isScoreStable_iff_splitScorePairs μ ((splitScorePairs μ).symm z)
    simpa [E, S, and_comm] using (and_congr_right fun _ : z.1 ∈ C ↦ h.symm)
  have hE : MeasurableSet E := hE_pre ▸ hS.preimage (splitScorePairs μ).symm.measurable
  have hpre : (splitScorePairs μ) ⁻¹' E = S := by
    ext x
    simp [E, S, ← isScoreStable_iff_splitScorePairs, and_comm]
  have hf' : Measurable f' := hf.comp (splitScorePairs μ).symm.measurable
  calc
    _ = ∫⁻ z in E, f' z ∂((diagonalScoreLaw n).prod (offDiagonalScoreLaw n)) := by
      rw [← (measurePreserving_splitScorePairs μ).setLIntegral_comp_preimage hE hf', hpre]
      simp [f', S]
    _ = _ := by
      rw [← lintegral_indicator hE,
        lintegral_prod _ (hf'.indicator hE).aemeasurable, ← lintegral_indicator hC]
      refine lintegral_congr fun d ↦ ?_
      by_cases hd : d ∈ C
      · have hnon : MeasurableSet (offDiagonalNonblocking d) :=
          MeasurableSet.univ_pi fun _ ↦ (measurableSet_Iio.prod measurableSet_Iio).compl
        rw [Set.indicator_of_mem hd, ← lintegral_indicator hnon]
        refine lintegral_congr fun v ↦ ?_
        by_cases hv : v ∈ offDiagonalNonblocking d <;> simp [E, f', hd, hv]
      · rw [Set.indicator_of_notMem hd]
        simp [E, hd]
theorem continuousScoreLaw_lintegral_stable_and_diagonal_rows {n : ℕ} (μ : Matching n)
    {C : Set (DiagonalScorePairs n)} (hC : MeasurableSet C)
    {f : ScoreProfile n → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x in {x | IsScoreStable x μ ∧ (splitScorePairs μ x).1 ∈ C}, f x
      ∂continuousScoreLaw n) =
      ∫⁻ d in C, ∫⁻ r, f ((splitScorePairs μ).symm (d,(offDiagonalRowsEquiv n).symm r))
        ∂(Measure.pi (stableScoreRowLaw d)) ∂diagonalScoreLaw n := by
  rw [continuousScoreLaw_lintegral_stable_and_diagonal μ hC hf]
  refine lintegral_congr fun d ↦ ?_
  rw [(measurePreserving_offDiagonalRowsEquiv_stable d).lintegral_map_equiv _
    (offDiagonalRowsEquiv n)]
  simp only [MeasurableEquiv.symm_apply_apply]
theorem measurePreserving_rowTargetAndCompetitors {ι X : Type*}
    [Fintype ι] [DecidableEq ι] [MeasurableSpace X] (m : ι → Measure X)
    [∀ i, SigmaFinite (m i)] (j : ι) :
    MeasurePreserving (fun r : ι → X ↦ (r j, fun k : {k : ι // k ≠ j} ↦ r k.val))
      (Measure.pi m) ((m j).prod (Measure.pi fun k : {k : ι // k ≠ j} ↦ m k.val)) := by
  let : Unique {k : ι // k = j} :=
    ⟨⟨⟨j, rfl⟩⟩, fun k ↦ Subtype.ext k.property⟩
  let : Fintype {k : ι // k = j} := Subtype.fintype (fun k ↦ k = j)
  exact ((measurePreserving_piUnique (fun k : {k : ι // k = j} ↦ m k.val)).prod
    (MeasurePreserving.id _)).comp (measurePreserving_piEquivPiSubtypeProd m fun k ↦ k = j)
theorem ae_diagonal_ae_stableRows {n : ℕ} (μ : Matching n) :
    ∀ᵐ d ∂diagonalScoreLaw n, ∀ᵐ r ∂Measure.pi (stableScoreRowLaw d),
      let x := (splitScorePairs μ).symm (d, (offDiagonalRowsEquiv n).symm r)
      (∀ row, Function.Injective (x row)) ∧ IsScoreStable x μ := by
  have ht : ∀ᵐ z ∂((diagonalScoreLaw n).prod (offDiagonalScoreLaw n)),
      ∀ row, Function.Injective ((splitScorePairs μ).symm z row) :=
    ((measurePreserving_splitScorePairs μ).symm).quasiMeasurePreserving.ae (ae_injective_rows n)
  filter_upwards [Measure.ae_ae_of_ae_prod ht] with d hd
  have hnon : MeasurableSet (offDiagonalNonblocking d) :=
    MeasurableSet.univ_pi fun _ ↦ (measurableSet_Iio.prod measurableSet_Iio).compl
  have hv : ∀ᵐ v ∂(offDiagonalScoreLaw n).restrict (offDiagonalNonblocking d),
      (∀ row, Function.Injective ((splitScorePairs μ).symm (d,v) row)) ∧
        v ∈ offDiagonalNonblocking d :=
    (ae_restrict_of_ae hd).and (ae_restrict_mem hnon)
  have he := (measurePreserving_offDiagonalRowsEquiv_stable d).symm
  filter_upwards [he.quasiMeasurePreserving.ae hv] with r hr
  refine ⟨hr.1, (isScoreStable_iff_splitScorePairs μ _).2 ?_⟩
  simpa only [MeasurableEquiv.apply_symm_apply] using hr.2
private def scoreRowSuccessorEvent {n : ℕ} (d : DiagonalScorePairs n) (i : Fin n)
    (j : {j : Fin n // i ≠ j}) : Set ({j : Fin n // i ≠ j} → ℝ × ℝ) :=
  {r | (diagonalPairAt d i).1 < (r j).1 ∧ (r j).2 < (diagonalPairAt d j.val).2 ∧
    ∀ k : {k : {k : Fin n // i ≠ k} // k ≠ j},
      ¬ ((r k.val).1 < (r j).1 ∧ (r k.val).2 < (diagonalPairAt d k.val.val).2)}
theorem scoreRowSuccessorEvent_of_isSuccessor {n : ℕ} (μ : Matching n) (x : ScoreProfile n)
    (hs : IsScoreStable x μ) (ht : ∀ row, Function.Injective (x row))
    (i : Fin n) (j : {j : Fin n // i ≠ j}) (hj : IsSuccessor (profileOfScores x) μ i (μ j.val)) :
    offDiagonalRowsEquiv n (splitScorePairs μ x).2 i ∈
      scoreRowSuccessorEvent (splitScorePairs μ x).1 i j := by
  have hcell (a : {a : Fin n // i ≠ a}) :
      offDiagonalRowsEquiv n (splitScorePairs μ x).2 i a =
        (x (.inl i) (μ a.val), x (.inr (μ a.val)) i) := by
    simpa [offDiagonalRowsEquiv] using
      splitScorePairs_offDiagonal_apply μ x ⟨(i,a.val),a.property⟩
  simp only [scoreRowSuccessorEvent, Set.mem_ofPred_eq, hcell, diagonalPairAt_splitScorePairs]
  have hman (w w' : Fin n) : (profileOfScores x).manRank i w < (profileOfScores x).manRank i w'
      ↔ x (.inl i) w < x (.inl i) w' :=
    rankPermutation_lt_iff (ht (.inl i)) w w'
  have hwoman (w m m' : Fin n) :
      (profileOfScores x).womanRank w m < (profileOfScores x).womanRank w m'
        ↔ x (.inr w) m < x (.inr w) m' :=
    rankPermutation_lt_iff (ht (.inr w)) m m'
  refine ⟨(hman _ _).1 (IsSuccessor.eligible hj).1, ?_, ?_⟩
  · simpa only [Equiv.symm_apply_apply] using (hwoman _ _ _).1 (IsSuccessor.eligible hj).2
  · intro k hk
    have hwk : x (.inr (μ k.val.val)) i <
        x (.inr (μ k.val.val)) (μ.symm (μ k.val.val)) := by
      simpa only [Equiv.symm_apply_apply] using hk.2
    have hmle : x (.inl i) (μ i) ≤ x (.inl i) (μ k.val.val) :=
      le_of_not_gt fun h ↦ hs i (μ k.val.val) ⟨μ.injective.ne k.val.property, h, hwk⟩
    have hmne := (ht (.inl i)).ne (μ.injective.ne k.val.property)
    have hel : IsEligibleSuccessor (profileOfScores x) μ i (μ k.val.val) :=
      ⟨(hman _ _).2 (lt_of_le_of_ne hmle hmne), (hwoman _ _ _).2 hwk⟩
    exact (not_lt_of_ge ((IsSuccessor.min_rank hj) _ hel)) ((hman _ _).2 hk.1)
theorem scoreRowSuccessorEvent_of_isSuccessor_reconstructed {n : ℕ} (μ : Matching n)
    (d : DiagonalScorePairs n) (r : OffDiagonalScoreRows n)
    (i : Fin n) (j : {j : Fin n // i ≠ j})
    (hs : IsScoreStable ((splitScorePairs μ).symm (d,(offDiagonalRowsEquiv n).symm r)) μ)
    (ht : ∀ row, Function.Injective
      ((splitScorePairs μ).symm (d,(offDiagonalRowsEquiv n).symm r) row))
    (hj : IsSuccessor (profileOfScores ((splitScorePairs μ).symm
      (d,(offDiagonalRowsEquiv n).symm r))) μ i (μ j.val)) :
    r i ∈ scoreRowSuccessorEvent d i j := by
  simpa only [MeasurableEquiv.apply_symm_apply] using
    scoreRowSuccessorEvent_of_isSuccessor μ _ hs ht i j hj
theorem prod_stableScoreRowLaw_univ {n : ℕ} (d : DiagonalScorePairs n) :
    (∏ i, stableScoreRowLaw d i univ) =
      offDiagonalScoreLaw n (offDiagonalNonblocking d) := by
  have h := (measurePreserving_offDiagonalRowsEquiv_stable d).measure_preimage
    (s := Set.univ) MeasurableSet.univ.nullMeasurableSet
  simpa only [Set.preimage_univ, Measure.restrict_apply_univ, Measure.pi_univ] using h.symm
theorem measurableSet_scoreRowSuccessorEvent {n : ℕ} (d : DiagonalScorePairs n)
    (i : Fin n) (j : {j : Fin n // i ≠ j}) :
    MeasurableSet (scoreRowSuccessorEvent d i j) :=
  (measurableSet_scoreSuccessorPairEvent (diagonalPairAt d i).1 (diagonalPairAt d j.val).2
    (fun k : {k : {k : Fin n // i ≠ k} // k ≠ j} ↦ (diagonalPairAt d k.val.val).2)).preimage
    (measurePreserving_rowTargetAndCompetitors
      (fun _ : {k : Fin n // i ≠ k} ↦ unitScorePairLaw) j).measurable
theorem stableScoreRowLaw_successor_le {n : ℕ} (d : DiagonalScorePairs n)
    (i : Fin n) (j : {j : Fin n // i ≠ j})
    (hx : (diagonalPairAt d i).1 ∈ Ico (0 : ℝ) 1)
    (hy : ∀ k, (diagonalPairAt d k).2 ∈ Icc (0 : ℝ) 1)
    (hsum : 0 < ∑ k : {k : {k : Fin n // i ≠ k} // k ≠ j}, (diagonalPairAt d k.val.val).2) :
    stableScoreRowLaw d i (scoreRowSuccessorEvent d i j) ≤
      stableScoreRowLaw d i univ *
        ENNReal.ofReal ((diagonalPairAt d j.val).2 /
          ((1 - (diagonalPairAt d i).1 * (diagonalPairAt d j.val).2) *
            (∑ k : {k : {k : Fin n // i ≠ k} // k ≠ j}, (diagonalPairAt d k.val.val).2))) := by
  let x := (diagonalPairAt d i).1
  let y (k : {k : Fin n // i ≠ k}) := (diagonalPairAt d k.val).2
  let m (k : {k : Fin n // i ≠ k}) := rowNonblockingLaw x (y k)
  let E := scoreSuccessorPairEvent x (y j) (fun k : {k // k ≠ j} ↦ y k.val)
  have hpres := measurePreserving_rowTargetAndCompetitors m j
  have hE : MeasurableSet E := measurableSet_scoreSuccessorPairEvent _ _ _
  have heq : stableScoreRowLaw d i (scoreRowSuccessorEvent d i j) =
      ((m j).prod (Measure.pi fun k : {k // k ≠ j} ↦ m k.val)) E :=
    hpres.measure_preimage hE.nullMeasurableSet
  have ht : stableScoreRowLaw d i univ =
      m j univ * ∏ k : {k // k ≠ j}, m k.val univ := by
    have h := hpres.measure_preimage (s := Set.univ) MeasurableSet.univ.nullMeasurableSet
    calc
      _ = ((m j).prod (Measure.pi fun k : {k // k ≠ j} ↦ m k.val)) univ :=
        by simpa only [Set.preimage_univ, stableScoreRowLaw, m, x, y, unitScorePairLaw,
          rowNonblockingLaw, nonblockingScoreCell] using h
      _ = ((m j).prod (Measure.pi fun k : {k // k ≠ j} ↦ m k.val)) (univ ×ˢ univ) :=
        by rw [Set.univ_prod_univ]
      _ = _ := by rw [Measure.prod_prod, Measure.pi_univ]
  rw [heq, ht]
  exact scoreSuccessorPairEvent_mass_le hx (hy j.val) (fun k ↦ hy k.val.val) hsum
end AbunLP
end

-- CoexposureSpouseMarginal
section
open Filter MeasureTheory ProbabilityTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace AbunLP
private def femaleSpouseByHusband {n : ℕ} (μ : Matching n) (x : ScoreProfile n) : Fin n → ℝ :=
  fun j ↦ femaleSpouseScore x μ (μ j)
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
end AbunLP
end

-- CoexposureSpouseShells
section
open Filter MeasureTheory Set StableMarriage
open scoped ENNReal BigOperators Topology
namespace AbunLP
private def spouseVectorTotal {n : ℕ} (y : Fin n → ℝ) : ℝ :=
  ∑ i, y i
end AbunLP
end

-- PittelMeanTail
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace AbunLP
end AbunLP
end

-- MarkedSpouseAngleComparison
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace AbunLP
end AbunLP
end

-- ScoreSideSwap
section
open MeasureTheory Set StableMarriage
open scoped BigOperators
namespace AbunLP
end AbunLP
end

-- StableMaleSpouseRowLaw
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace AbunLP
end AbunLP
end

-- IndependentFlagLowerTail
section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace AbunLP
end AbunLP
end

-- FiniteProductDensity
section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace AbunLP
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
end AbunLP
end

-- SmallSpouseTotalLog
section
open Filter MeasureTheory Set StableMarriage
open scoped ENNReal BigOperators Topology
namespace AbunLP
end AbunLP
end

-- MeanUpperBound
section
open Filter MeasureTheory Set StableMarriage
open scoped ENNReal BigOperators Topology
namespace AbunLP
private noncomputable def meanUpperConstant : ℝ := Real.exp 2 + 1
theorem meanUpperConstant_nonneg : 0 ≤ meanUpperConstant := by
  unfold meanUpperConstant
  positivity
private class LPHyp3_3 : Prop where
  bound : ∀ᶠ n : ℕ in atTop, expectedNumStableMatchings n ≤
      meanUpperConstant * ((n : ℝ) * Real.log n)
theorem eventually_expectedNumStableMatchings_le_meanUpper [h : LPHyp3_3] :
    ∀ᶠ n : ℕ in atTop, expectedNumStableMatchings n ≤
      meanUpperConstant * ((n : ℝ) * Real.log n) :=
  h.bound
theorem eventually_expectedNumStableMatchings_le_sizeSq [LPHyp3_3] :
    ∀ᶠ n : ℕ in atTop, expectedNumStableMatchings n ≤ (n : ℝ) ^ 2 := by
  have h := (((isLittleO_log_rpow_atTop (r := (1 : ℝ)) (by norm_num)).const_mul_left
    meanUpperConstant).comp_tendsto (tendsto_natCast_atTop_atTop (R := ℝ))).eventuallyLE
  filter_upwards [eventually_expectedNumStableMatchings_le_meanUpper, h] with n hmean hlog
  have hnorm : |meanUpperConstant * Real.log (n : ℝ)| ≤ |(n : ℝ) ^ (1 : ℝ)| := hlog
  rw [Real.rpow_one, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)] at hnorm
  calc
    _ ≤ meanUpperConstant * ((n : ℝ) * Real.log n) := hmean
    _ = (n : ℝ) * (meanUpperConstant * Real.log n) := by ring
    _ ≤ (n : ℝ) * n := mul_le_mul_of_nonneg_left ((le_abs_self _).trans hnorm) (Nat.cast_nonneg n)
    _ = _ := (sq _).symm
end AbunLP
end

-- PivotSpouseProductLower
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace AbunLP
private def maleSpouseTotal {n : ℕ} (x : ScoreProfile n) (μ : Matching n) : ℝ :=
  ∑ i, maleSpouseScore x μ i
private def lowSpouseProductVectorSet (n : ℕ) : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  {z | 2 ≤ spouseVectorTotal z.2 ∧
    spouseVectorTotal z.1 * spouseVectorTotal z.2 < (n : ℝ) / 128}
end AbunLP
end

-- PivotForwardRevealCell
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace AbunLP
private def forwardEligibleScoreCell (x y : ℝ) : Set (ℝ × ℝ) :=
  Ioi x ×ˢ Iio y
private def forwardScoreCellFlagEvent (x y : ℝ) (b : Bool) : Set (ℝ × ℝ) :=
  if b then forwardEligibleScoreCell x y else (forwardEligibleScoreCell x y)ᶜ
private abbrev OffDiagonalCellIndex (n : ℕ) := {q : ScorePairIndex n // q.1 ≠ q.2}
private def forwardScoreMaskEvent {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) : Set (OffDiagonalScorePairs n) :=
  univ.pi fun q ↦ forwardScoreCellFlagEvent
    (diagonalPairAt d q.val.1).1 (diagonalPairAt d q.val.2).2 (flag q)
private abbrev ForwardActiveCellIndex {n : ℕ} (flag : OffDiagonalCellIndex n → Bool) :=
  {q : OffDiagonalCellIndex n // flag q = true}
private abbrev ForwardInactiveCellIndex {n : ℕ} (flag : OffDiagonalCellIndex n → Bool) :=
  {q : OffDiagonalCellIndex n // flag q ≠ true}
private def forwardScoreMaskRevealAndInactive {n : ℕ} (flag : OffDiagonalCellIndex n → Bool)
    (z : OffDiagonalScorePairs n) :
    (ForwardActiveCellIndex flag → ℝ) × (ForwardInactiveCellIndex flag → ℝ × ℝ) :=
  (fun q ↦ (z q.val).1, fun q ↦ z q.val)
theorem measurable_forwardScoreMaskRevealAndInactive {n : ℕ}
    (flag : OffDiagonalCellIndex n → Bool) :
    Measurable (forwardScoreMaskRevealAndInactive flag) :=
  (measurable_pi_iff.2 fun q ↦ measurable_fst.comp (measurable_pi_apply q.val)).prodMk
    (measurable_pi_iff.2 fun q ↦ measurable_pi_apply q.val)
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
end AbunLP
end

-- PivotReverseEligibility
section
open MeasureTheory Set
open scoped ENNReal
namespace AbunLP
end AbunLP
end

-- PivotReverseRowLaw
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace AbunLP
variable {ι : Type*}
end AbunLP
end

-- ReverseSuccessorIncrement
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace AbunLP
variable {ι : Type*}
end AbunLP
end

-- ReverseCompatibilityRectangle
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace AbunLP
end AbunLP
end

-- PivotReverseRelaxedColumn
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace AbunLP
end AbunLP
end

-- ReverseSuccessorRotation
section
open StableMarriage
namespace AbunLP
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
end AbunLP
end

-- PivotReverseScoreSuccessor
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace AbunLP
end AbunLP
end

-- PivotRelaxedArcEvents
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace AbunLP
end AbunLP
end

-- FinitePrerequisites
section
namespace AbunLP
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
end AbunLP
end

-- RotationDiamond
section
open StableMarriage
namespace AbunLP
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
end AbunLP
end

-- ManOptimal
section
open StableMarriage
open scoped BigOperators
namespace AbunLP
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
theorem exists_stable_menWeaklyPrefer {p : Profile n} {μ ν : Matching n}
    (hμ : IsStable p μ) (hν : IsStable p ν) :
    ∃ τ, IsStable p τ ∧ MenWeaklyPrefer p τ μ ∧ MenWeaklyPrefer p τ ν := by
  obtain ⟨τ, hτ, hmin⟩ := exists_stable_manRank_min hμ hν
  exact ⟨τ, hτ, fun m ↦ (hmin m).le.trans (min_le_left _ _),
    fun m ↦ (hmin m).le.trans (min_le_right _ _)⟩
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
private def manOptimal_totalManRank (p : Profile n) (μ : Matching n) : ℕ :=
  ∑ m : Fin n, (p.manRank m (μ m)).val
theorem exists_manOptimal_of_exists_stable {p : Profile n}
    (h : ∃ μ, IsStable p μ) : ∃ μ, IsManOptimal p μ := by
  classical
  let st : Finset (Matching n) := Finset.univ.filter (IsStable p)
  obtain ⟨s, hs⟩ := h
  obtain ⟨μ, hμ, hmin⟩ := st.exists_min_image (manOptimal_totalManRank p)
    ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩⟩
  have hμStable : IsStable p μ := (Finset.mem_filter.mp hμ).2
  refine ⟨μ, hμStable, ?_⟩
  intro ν hν m
  by_contra hbad
  obtain ⟨τ, hτ, hτμ, hτν⟩ := exists_stable_menWeaklyPrefer hμStable hν
  have hlt : manOptimal_totalManRank p τ < manOptimal_totalManRank p μ :=
    Finset.sum_lt_sum (fun i _ ↦ hτμ i)
      ⟨m, Finset.mem_univ _, (hτν m).trans_lt (lt_of_not_ge hbad)⟩
  exact (not_lt_of_ge (hmin τ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hτ⟩))) hlt
end AbunLP
end

-- RotationCycle
section
namespace AbunLP
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
end AbunLP
end

-- TargetSuccessor
section
open StableMarriage
namespace AbunLP
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
end AbunLP
end

-- RotationReachability
section
open scoped BigOperators
open StableMarriage
namespace AbunLP
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
end AbunLP
end

-- RotationLabels
section
open StableMarriage
namespace AbunLP
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
end AbunLP
end

-- RotationPathIndependence
section
open StableMarriage
namespace AbunLP
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
end AbunLP
end

-- RotationTrace
section
open StableMarriage
namespace AbunLP
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
end AbunLP
end

-- RotationIdeals
section
open StableMarriage
namespace AbunLP
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
private theorem RotationSequence.exists_exposed_prefix_of_mem {μ ν : Matching n}
    {rs : List (Equiv.Perm (Fin n))} (h : RotationSequence p μ rs ν)
    {r : RotationLabel n} (hr : r ∈ rotationLabels μ rs) :
    ∃ τ ts us, RotationSequence p μ ts τ ∧ IsExposedRotation p τ r.cycle ∧
      rotationLabel τ r.cycle = r ∧ rs = ts ++ r.cycle :: us := by
  induction h with
  | nil => exact (List.not_mem_nil hr).elim
  | @cons μ ν ρ rs hμ hρ htail ih =>
    rw [rotationLabels, List.mem_cons] at hr
    rcases hr with he | hr
    · subst r
      exact ⟨μ, [], rs, .nil hμ, hρ, rfl, rfl⟩
    · obtain ⟨τ, ts, us, ht, he, hl, hs⟩ := ih hr
      exact ⟨τ, ρ :: ts, us, .cons hμ hρ ht, he, hl, congrArg (ρ :: ·) hs⟩
theorem Rotation.lt_iff_before_exposure (hopt : IsManOptimal p μ₀)
    {r s : Rotation p μ₀} (hne : r ≠ s) :
    r < s ↔ ∀ ν, IsStable p ν → IsExposedRotation p ν s.val.cycle →
      rotationLabel ν s.val.cycle = s.val → r ∈ eliminatedRotations p μ₀ ν := by
  rw [lt_iff_le_and_ne]
  constructor
  · rintro ⟨hrs, _⟩ ν hν he hl
    obtain ⟨ts, ht⟩ := exists_rotationSequence_of_manOptimal hopt hν
    have hstep : RotationSequence p ν [s.val.cycle] (eliminateRotation ν s.val.cycle) :=
      .cons hν he (.nil (he.isStable_eliminate hν))
    have hnext := ht.append hstep
    have hs : s ∈ eliminatedRotations p μ₀ (eliminateRotation ν s.val.cycle) := by
      apply hnext.mem_eliminatedRotations_iff.mpr
      simp [ht.rotationLabels_append, rotationLabels, hl]
    have hr := hnext.mem_eliminatedRotations_iff.mp (hrs _ hs)
    rw [ht.rotationLabels_append, List.mem_append, rotationLabels, rotationLabels, hl,
      List.mem_singleton] at hr
    exact ht.mem_eliminatedRotations_iff.mpr (hr.resolve_right (fun h ↦ hne (Subtype.ext h)))
  · intro hbefore
    refine ⟨fun ν hν ↦ ?_, hne⟩
    obtain ⟨rs, h, hs⟩ := hν
    obtain ⟨τ, ts, us, ht, he, hl, hsplit⟩ := h.exists_exposed_prefix_of_mem hs
    have hr := ht.mem_eliminatedRotations_iff.mp (hbefore τ ht.isStable_end he hl)
    refine h.mem_eliminatedRotations_iff.mpr ?_
    rw [hsplit, ht.rotationLabels_append]
    exact List.mem_append_left _ hr
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
end AbunLP
end

-- CoexposedRotations
section
open StableMarriage
namespace AbunLP
variable {n : ℕ} {p : Profile n} {μ₀ μ : Matching n}
private def rotationOfExposed (hopt : IsManOptimal p μ₀) (hμ : IsStable p μ)
    {ρ : Equiv.Perm (Fin n)} (hρ : IsExposedRotation p μ ρ) : Rotation p μ₀ :=
  ⟨rotationLabel μ ρ, by
    obtain ⟨rs, hrs⟩ := exists_rotationSequence_of_manOptimal hopt hμ
    have hstep : RotationSequence p μ [ρ] (eliminateRotation μ ρ) :=
      .cons hμ hρ (.nil (hρ.isStable_eliminate hμ))
    refine ⟨_, rs ++ [ρ], hrs.append hstep, ?_⟩
    simp [hrs.rotationLabels_append, rotationLabels]⟩
theorem rotationOfExposed_not_mem_eliminatedRotations (hopt : IsManOptimal p μ₀)
    (hμ : IsStable p μ) {ρ : Equiv.Perm (Fin n)} (hρ : IsExposedRotation p μ ρ) :
    rotationOfExposed hopt hμ hρ ∉ eliminatedRotations p μ₀ μ := by
  obtain ⟨m, hm, _⟩ := (IsExposedRotation.isCycle hρ)
  exact fun hr ↦ (not_le_of_gt (hρ.manRank_lt_eliminate_of_moved hm))
    ((mem_eliminatedRotations_iff_newRank_le hopt hμ (m := m) hm
      (rotationLabelNewPartner_eq hm)).mp hr)
end AbunLP
end

-- CoexposedRotationMultiplicity
section
open StableMarriage
open scoped BigOperators
namespace AbunLP
variable {n : ℕ} {p : Profile n} {μ : Matching n}
end AbunLP
end

-- CoexposureCycleMoment
section
open StableMarriage MeasureTheory
open scoped BigOperators ENNReal
namespace AbunLP
private def RealizesSuccessorPermutation {n : ℕ} (p : Profile n) (M σ : Matching n) : Prop :=
  ∀ i ∈ σ.support, IsSuccessor p M i (M (σ i))
end AbunLP
end

-- PivotReverseMaskJointLaw
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace AbunLP
end AbunLP
end

-- RowCompetition
section
open Set
open scoped BigOperators
namespace AbunLP
variable {ι : Type*} {J : Finset ι} {a : ι → ℝ} {A b : ℝ}
end AbunLP
end

-- ReverseArcRelativeLower
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace AbunLP
end AbunLP
end

-- ReverseIIDLabelGood
section
open MeasureTheory Set ProbabilityTheory
open scoped BigOperators ENNReal
namespace AbunLP
section Measures
variable {ι α : Type*} [Fintype ι] [MeasurableSpace α]
variable [Fintype α] [DiscreteMeasurableSpace α]
private def iidLabelGood (A : Set α) (F : α → Set α) (e : ι → ι) : Set (ι → α) :=
  {x | Function.Injective x ∧ (∀ i, x i ∉ A) ∧ ∀ i, x (e i) ∉ F (x i)}
end Measures
end AbunLP
end

-- ReverseCycleLabelMultiplicity
section
open scoped BigOperators ENNReal
namespace AbunLP
variable {α : Type*} [Fintype α] [DecidableEq α]
private abbrev GoodLabeling (k : ℕ) (A : Finset α) (F : α → Finset α) :=
  Σ e : derangements (Fin k),
    {x : Fin k → α // x ∈ iidLabelGood (A : Set α) (fun a ↦ ↑(F a)) e.val}
private abbrev GoodSupport (k : ℕ) (A : Finset α) (F : α → Finset α) :=
  {σ : Equiv.Perm α // σ.support.card = k ∧ ∀ i ∈ σ.support, i ∉ A ∧ σ i ∉ F i}
variable {k : ℕ} {A : Finset α} {F : α → Finset α}
private def labelingEmbedding (l : GoodLabeling k A F) : Fin k ↪ α :=
  ⟨l.2.val, l.2.property.1⟩
private def labelingPerm (l : GoodLabeling k A F) : Equiv.Perm α :=
  l.1.val.viaFintypeEmbedding (labelingEmbedding l)
omit [Fintype α] in
private theorem labelingPerm_apply (l : GoodLabeling k A F) (i : Fin k) :
    labelingPerm l (l.2.val i) = l.2.val (l.1.val i) :=
  l.1.val.viaFintypeEmbedding_apply_image (labelingEmbedding l) i
private theorem mem_labelingPerm_support (l : GoodLabeling k A F) (a : α) :
    a ∈ (labelingPerm l).support ↔ ∃ i, l.2.val i = a := by
  rw [Equiv.Perm.mem_support]
  constructor
  · intro h
    by_contra h'
    exact h (l.1.val.viaFintypeEmbedding_apply_notMem_range (labelingEmbedding l) h')
  · rintro ⟨i, rfl⟩
    rw [labelingPerm_apply]
    exact (labelingEmbedding l).injective.ne (l.1.property i)
private noncomputable def labelingOrder (l : GoodLabeling k A F) :
    Fin k ≃ (labelingPerm l).support :=
  Equiv.ofBijective (fun i ↦ ⟨l.2.val i, (mem_labelingPerm_support l _).mpr ⟨i, rfl⟩⟩)
    ⟨fun _ _ h ↦ l.2.property.1 (congrArg Subtype.val h), fun a ↦ by
      obtain ⟨i, hi⟩ := (mem_labelingPerm_support l _).mp a.property
      exact ⟨i, Subtype.ext hi⟩⟩
private noncomputable def labelingSupport (l : GoodLabeling k A F) : GoodSupport k A F :=
  ⟨labelingPerm l, by
    constructor
    · simpa only [Fintype.card_coe, Fintype.card_fin] using
        (Fintype.card_congr (labelingOrder l)).symm
    · intro a ha
      obtain ⟨i, rfl⟩ := (mem_labelingPerm_support l a).mp ha
      rw [labelingPerm_apply]
      exact ⟨l.2.property.2.1 i, l.2.property.2.2 i⟩⟩
private def supportPositionPerm (s : GoodSupport k A F) (t : Fin k ≃ s.val.support) :
    Equiv.Perm (Fin k) :=
  t.symm.permCongr s.val.subtypePermOfSupport
private theorem supportPositionPerm_label (s : GoodSupport k A F) (t : Fin k ≃ s.val.support)
    (i : Fin k) : (t (supportPositionPerm s t i)).val = s.val (t i).val := by
  simp only [supportPositionPerm, Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
  rfl
private def supportLabeling (s : GoodSupport k A F) (t : Fin k ≃ s.val.support) :
    GoodLabeling k A F :=
  ⟨⟨supportPositionPerm s t, fun i hi ↦
      Equiv.Perm.mem_support.mp (t i).property
        ((supportPositionPerm_label s t i).symm.trans (congrArg (fun j ↦ (t j).val) hi))⟩,
    ⟨fun i ↦ (t i).val, Subtype.val_injective.comp t.injective,
      fun i ↦ (s.property.2 _ (t i).property).1, fun i ↦ by
        change (t (supportPositionPerm s t i)).val ∉ F (t i).val
        rw [supportPositionPerm_label]
        exact (s.property.2 _ (t i).property).2⟩⟩
private theorem labelingSupport_supportLabeling (s : GoodSupport k A F)
    (t : Fin k ≃ s.val.support) :
    labelingSupport (supportLabeling s t) = s := by
  apply Subtype.ext
  ext a
  change labelingPerm (supportLabeling s t) a = s.val a
  by_cases ha : a ∈ s.val.support
  · obtain ⟨i, hi⟩ := t.surjective ⟨a, ha⟩
    have hi' : (t i).val = a := congrArg Subtype.val hi
    rw [← hi']
    exact (labelingPerm_apply (supportLabeling s t) i).trans (supportPositionPerm_label s t i)
  · have hnot : a ∉ Set.range (labelingEmbedding (supportLabeling s t)) :=
      fun ⟨i, hi⟩ ↦ ha (hi ▸ (t i).property)
    exact ((supportLabeling s t).1.val.viaFintypeEmbedding_apply_notMem_range
      (labelingEmbedding (supportLabeling s t)) hnot).trans ((Equiv.Perm.notMem_support.mp ha).symm)
private noncomputable def supportOrderEquivFiber (s : GoodSupport k A F) :
    (Fin k ≃ s.val.support) ≃ {l : GoodLabeling k A F // labelingSupport l = s} := by
  let f (t : Fin k ≃ s.val.support) :
      {l : GoodLabeling k A F // labelingSupport l = s} :=
    ⟨supportLabeling s t, labelingSupport_supportLabeling s t⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro t u h
    exact Equiv.ext fun i ↦ Subtype.ext (congrArg (fun z ↦ z.val.2.val i) h)
  · rintro ⟨l, rfl⟩
    refine ⟨labelingOrder l, Subtype.ext (Sigma.subtype_ext ?_ rfl)⟩
    apply Subtype.ext
    apply Equiv.ext
    intro i
    apply (labelingEmbedding l).injective
    exact (supportPositionPerm_label (labelingSupport l) (labelingOrder l) i).trans
      (labelingPerm_apply l i)
private theorem card_supportFiber (s : GoodSupport k A F) :
    Nat.card {l : GoodLabeling k A F // labelingSupport l = s} = k.factorial := by
  classical
  let t : Fin k ≃ s.val.support := Fintype.equivOfCardEq (by
    rw [Fintype.card_fin, Fintype.card_coe, s.property.1])
  rw [← Nat.card_congr (supportOrderEquivFiber s), Nat.card_eq_fintype_card,
    ← Fintype.card_congr (Equiv.equivCongr (Equiv.refl (Fin k)) t), Fintype.card_perm,
    Fintype.card_fin]
open scoped Classical in
theorem sum_iidLabelGood_eq_factorial_mul_sum_support
    (k : ℕ) (r : α → ℝ≥0∞) (A : Finset α) (F : α → Finset α) :
    (∑ e : derangements (Fin k),
      ∑ x ∈ Finset.univ.filter
        (fun x ↦ x ∈ iidLabelGood (A : Set α) (fun a ↦ ↑(F a)) e.val),
          ∏ i, r (x i)) =
      (k.factorial : ℝ≥0∞) * ∑ σ ∈ Finset.univ.filter
        (fun σ : Equiv.Perm α ↦ σ.support.card = k ∧ ∀ i ∈ σ.support, i ∉ A ∧ σ i ∉ F i),
          ∏ i ∈ σ.support, r i := by
  let W (s : GoodSupport k A F) : ℝ≥0∞ := ∏ i ∈ s.val.support, r i
  have hw (l : GoodLabeling k A F) : (∏ i, r (l.2.val i)) = W (labelingSupport l) := by
    calc
      _ = ∏ j : (labelingPerm l).support, r j.val :=
        Fintype.prod_equiv (labelingOrder l) (fun i ↦ r (l.2.val i))
          (fun j ↦ r j.val) (fun _ ↦ rfl)
      _ = _ := Finset.prod_coe_sort _ r
  calc
    _ = ∑ l : GoodLabeling k A F, ∏ i, r (l.2.val i) := by
      rw [Fintype.sum_sigma]
      refine Finset.sum_congr rfl fun e _ ↦ ?_
      exact Finset.sum_subtype _ (fun _ ↦ by simp) _
    _ = ∑ l : GoodLabeling k A F, W (labelingSupport l) :=
      Finset.sum_congr rfl (fun l _ ↦ hw l)
    _ = ∑ s : GoodSupport k A F, ∑ l : {l // labelingSupport l = s}, W (labelingSupport l.val) :=
      (Fintype.sum_fiberwise labelingSupport (fun l ↦ W (labelingSupport l))).symm
    _ = ∑ s : GoodSupport k A F, (k.factorial : ℝ≥0∞) * W s := by
      refine Finset.sum_congr rfl fun s _ ↦ ?_
      have hc : Fintype.card {l // labelingSupport l = s} = k.factorial :=
        (Nat.card_eq_fintype_card.symm.trans (card_supportFiber s))
      calc
        _ = ∑ _l : {l // labelingSupport l = s}, W s :=
          Finset.sum_congr rfl (fun l _ ↦ congrArg W l.property)
        _ = _ := by simp only [Finset.sum_const, Finset.card_univ, hc, nsmul_eq_mul]
    _ = _ := by
      have h : (∑ s : GoodSupport k A F, W s) = ∑ σ ∈ Finset.univ.filter
          (fun σ : Equiv.Perm α ↦ σ.support.card = k ∧ ∀ i ∈ σ.support, i ∉ A ∧ σ i ∉ F i),
            ∏ i ∈ σ.support, r i := (Finset.sum_subtype
        (Finset.univ.filter (fun σ : Equiv.Perm α ↦
          σ.support.card = k ∧ ∀ i ∈ σ.support, i ∉ A ∧ σ i ∉ F i))
        (fun σ ↦ Finset.mem_filter_univ σ) (fun σ ↦ ∏ i ∈ σ.support, r i)).symm
      rw [← Finset.mul_sum, h]
end AbunLP
end

-- ReverseDerangementFraction
section
open scoped ENNReal
namespace AbunLP
end AbunLP
end

-- PivotReverseMaskLowerMoment
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace AbunLP
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
end AbunLP
end

-- PivotReverseCompetitorMass
section
open StableMarriage
open scoped BigOperators ENNReal
namespace AbunLP
private noncomputable def forwardMaskOmittedMass {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) (j : Fin n) : ℝ :=
  ∑ i : {i : Fin n // i ≠ j}, if flag ⟨(i.val, j), i.property⟩ then
    (diagonalPairAt d i.val).1 else 0
end AbunLP
end

-- PivotForwardMaskProbability
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace AbunLP
private noncomputable def forwardCellFlag (x y : ℝ) (z : ℝ × ℝ) : Bool := by
  classical
  exact decide (z ∈ forwardEligibleScoreCell x y)
@[simp] theorem forwardCellFlag_eq_true {x y : ℝ} {z : ℝ × ℝ} :
    forwardCellFlag x y z = true ↔ z ∈ forwardEligibleScoreCell x y := by
  classical
  simp [forwardCellFlag]
private noncomputable def forwardMaskOfScores {n : ℕ} (d : DiagonalScorePairs n)
    (z : OffDiagonalScorePairs n) (q : OffDiagonalCellIndex n) : Bool :=
  forwardCellFlag (diagonalPairAt d q.val.1).1 (diagonalPairAt d q.val.2).2 (z q)
theorem forwardMaskOfScores_eq_iff {n : ℕ} (d : DiagonalScorePairs n)
    (z : OffDiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool) :
    forwardMaskOfScores d z = flag ↔ z ∈ forwardScoreMaskEvent d flag := by
  rw [funext_iff, forwardScoreMaskEvent, mem_univ_pi]
  apply forall_congr'
  intro q
  cases flag q with
  | false =>
    simp [forwardScoreCellFlagEvent, forwardMaskOfScores, ← Bool.not_eq_true]
  | true =>
    simp [forwardScoreCellFlagEvent, forwardMaskOfScores]
end AbunLP
end

-- WeightedBoolProductTail
section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace AbunLP
end AbunLP
end

-- PivotEligibleMask
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace AbunLP
private def badForwardMask {n : ℕ} (d : DiagonalScorePairs n) (u : ℝ) : Set (OffDiagonalScorePairs n) :=
  ⋃ j : Fin n, {z | u * (∑ i, (diagonalPairAt d i).1) <
    forwardMaskOmittedMass d (forwardMaskOfScores d z) j}
theorem forwardMaskOmittedMass_le_of_notMem_badForwardMask {n : ℕ}
    (d : DiagonalScorePairs n) {u : ℝ} {z : OffDiagonalScorePairs n}
    (h : z ∉ badForwardMask d u) (j : Fin n) :
    forwardMaskOmittedMass d (forwardMaskOfScores d z) j ≤
      u * (∑ i, (diagonalPairAt d i).1) :=
  le_of_not_gt fun hj ↦ h (Set.mem_iUnion.mpr ⟨j, hj⟩)
end AbunLP
end

-- PivotForwardRevealRectangle
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace AbunLP
private abbrev ForwardRevealedMaleScores {n : ℕ} (flag : OffDiagonalCellIndex n → Bool) :=
  ForwardActiveCellIndex flag → ℝ
private abbrev ForwardInactiveColumns {n : ℕ} (flag : OffDiagonalCellIndex n → Bool) :=
  (i : Fin n) → ForwardInactiveColumnIndex flag i → ℝ × ℝ
private def forwardRevealWithColumns {n : ℕ} (flag : OffDiagonalCellIndex n → Bool) :
    OffDiagonalScorePairs n → ForwardRevealedMaleScores flag × ForwardInactiveColumns flag :=
  Prod.map id (forwardInactiveColumnsEquiv flag) ∘ forwardScoreMaskRevealAndInactive flag
theorem measurable_forwardRevealWithColumns {n : ℕ} (flag : OffDiagonalCellIndex n → Bool) :
    Measurable (forwardRevealWithColumns flag) :=
  (measurable_id.prodMap (forwardInactiveColumnsEquiv flag).measurable).comp
    (measurable_forwardScoreMaskRevealAndInactive flag)
end AbunLP
end

-- PivotForwardPivotReadout
section
open MeasureTheory Set StableMarriage
namespace AbunLP
private noncomputable def forwardPivotIncrement {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) (ρ : Matching n)
    (a : ForwardRevealedMaleScores flag) (m : Fin n) : ℝ :=
  if hm : ρ m ≠ m then
    let q : OffDiagonalCellIndex n := ⟨(m, ρ m), hm.symm⟩
    if hq : flag q = true then a ⟨q, hq⟩ - (diagonalPairAt d m).1 else 0
  else 0
theorem forwardPivotIncrement_eq_of_exposed {n : ℕ} (μ ρ : Matching n)
    (x : ScoreProfile n) (flag : OffDiagonalCellIndex n → Bool)
    (ht : ∀ r, Function.Injective (x r))
    (hmask : (splitScorePairs μ x).2 ∈ forwardScoreMaskEvent (splitScorePairs μ x).1 flag)
    (hρ : IsExposedRotation (profileOfScores x) μ ρ) {m : Fin n} (hm : ρ m ≠ m) :
    forwardPivotIncrement (splitScorePairs μ x).1 flag ρ
      (forwardRevealWithColumns flag (splitScorePairs μ x).2).1 m =
      x (.inl m) (μ (ρ m)) - x (.inl m) (μ m) := by
  let q : OffDiagonalCellIndex n := ⟨(m, ρ m), hm.symm⟩
  have hmale : x (.inl m) (μ m) < x (.inl m) (μ (ρ m)) :=
    (rankPermutation_lt_iff (ht (.inl m)) _ _).mp (IsSuccessor.eligible ((IsExposedRotation.successor hρ) m hm)).1
  have hfemale : x (.inr (μ (ρ m))) m < x (.inr (μ (ρ m))) (ρ m) :=
    (rankPermutation_lt_iff (ht (.inr (μ (ρ m)))) _ _).mp
      (by simpa only [profileOfScores, Equiv.symm_apply_apply] using (IsSuccessor.eligible ((IsExposedRotation.successor hρ) m hm)).2)
  have hq : flag q = true := by
    by_contra h
    have hh := mem_pi.mp hmask q (mem_univ _)
    change (splitScorePairs μ x).2 q ∈ forwardScoreCellFlagEvent
      (diagonalPairAt (splitScorePairs μ x).1 m).1
      (diagonalPairAt (splitScorePairs μ x).1 (ρ m)).2 (flag q) at hh
    rw [forwardScoreCellFlagEvent, if_neg h, mem_compl_iff, forwardEligibleScoreCell,
      splitScorePairs_offDiagonal_apply, diagonalPairAt_splitScorePairs,
      diagonalPairAt_splitScorePairs] at hh
    exact hh ⟨hmale, hfemale⟩
  have hq' : flag (⟨(m, ρ m), hm.symm⟩ : OffDiagonalCellIndex n) = true := hq
  simp only [forwardPivotIncrement, dif_pos hm, dif_pos hq']
  change ((splitScorePairs μ x).2 q).1 - (diagonalPairAt (splitScorePairs μ x).1 m).1 = _
  rw [splitScorePairs_offDiagonal_apply, diagonalPairAt_splitScorePairs]
end AbunLP
end

-- SingletonIdealAnchor
section
namespace AbunLP
variable {α : Type*} [PartialOrder α]
private def singletonAnchorIdeal (r : α) : LowerSet α :=
  ⟨(Set.Ici r)ᶜ, fun _ _ hst ht hrs ↦ ht (hrs.trans hst)⟩
@[simp] theorem mem_singletonAnchorIdeal {r s : α} :
    s ∈ singletonAnchorIdeal r ↔ ¬ r ≤ s :=
  Iff.rfl
theorem lowerSet_eq_singletonAnchorIdeal_iff [Finite α] (I : LowerSet α) (r : α) :
    I = singletonAnchorIdeal r ↔ ∀ s : α, Minimal (fun t : α ↦ t ∉ I) s ↔ s = r :=
  ⟨fun h s ↦ h.symm ▸
    minimal_iff_eq (fun hr ↦ (mem_singletonAnchorIdeal.mp hr) le_rfl)
      (fun _ ht ↦ not_not.mp fun hrt ↦ ht (mem_singletonAnchorIdeal.mpr hrt)),
    fun h ↦ LowerSet.ext (Set.ext fun s ↦
      show s ∈ I ↔ ¬ r ≤ s from
      ⟨fun hs hrs ↦ ((h r).mpr rfl).prop (I.lower hrs hs),
        fun hrs ↦ Classical.byContradiction fun hs ↦
          
          let ⟨t, hts, ht⟩ := Finite.exists_le_minimal (p := fun t : α ↦ t ∉ I) hs
          hrs (by simpa only [(h t).mp ht] using hts)⟩)⟩
end AbunLP
end

-- SingletonRotationAnchor
section
open StableMarriage
namespace AbunLP
variable {n : ℕ} {p : Profile n} {μ₀ μ : Matching n}
private def Rotation.IsExposedAt (r : Rotation p μ₀) (μ : Matching n) : Prop :=
  IsExposedRotation p μ r.val.cycle ∧ rotationLabel μ r.val.cycle = r.val
theorem Rotation.isExposedAt_iff_minimal (hopt : IsManOptimal p μ₀) (hμ : IsStable p μ)
    (r : Rotation p μ₀) :
    r.IsExposedAt μ ↔ Minimal (fun s ↦ s ∉ eliminatedRotations p μ₀ μ) r := by
  rw [minimal_iff_forall_lt]
  constructor
  · rintro ⟨he, hl⟩
    have hr : rotationOfExposed hopt hμ he = r := Subtype.ext hl
    refine ⟨hr ▸ rotationOfExposed_not_mem_eliminatedRotations hopt hμ he, ?_⟩
    intro s hsr
    exact not_not_intro
      ((Rotation.lt_iff_before_exposure hopt hsr.ne).mp hsr μ hμ he hl)
  · classical
    rintro ⟨hr, hbefore⟩
    let I := stableMatchingToRotationIdeal (μ₀ := μ₀) ⟨μ, hμ⟩
    let J : LowerSet (Rotation p μ₀) :=
      ⟨insert r (I : Set (Rotation p μ₀)), by
        intro s t hst ht
        rcases Set.mem_insert_iff.mp ht with rfl | ht
        · rcases eq_or_lt_of_le hst with rfl | hsr
          · exact Set.mem_insert _ _
          · exact Set.mem_insert_of_mem _ (not_not.mp (hbefore hsr))
        · exact Set.mem_insert_of_mem _ (I.lower hst ht)⟩
    let e := stableMatchingEquivRotationIdeals hopt
    let ν := e.symm J
    have hν : eliminatedRotations p μ₀ ν.val = (J : Set (Rotation p μ₀)) :=
      congrArg (fun K : LowerSet (Rotation p μ₀) ↦ (K : Set (Rotation p μ₀)))
        (e.apply_symm_apply J)
    have hle : eliminatedRotations p μ₀ μ ⊆ eliminatedRotations p μ₀ ν.val := by
      rw [hν]
      exact fun s hs ↦ Set.mem_insert_of_mem _ hs
    have hne : μ ≠ ν.val := by
      intro h
      apply hr
      rw [h, hν]
      exact Set.mem_insert r _
    obtain ⟨ρ, hρ, hnext⟩ := exists_exposedRotation_towards_target hμ ν.property
      ((eliminatedRotations_subset_iff hopt hμ ν.property).mp hle) hne
    let q := rotationOfExposed hopt hμ hρ
    obtain ⟨rs, hrs⟩ := exists_rotationSequence_of_manOptimal hopt hμ
    have hstable := hρ.isStable_eliminate hμ
    have hstep : RotationSequence p μ [ρ] (eliminateRotation μ ρ) :=
      .cons hμ hρ (.nil hstable)
    have hq : q ∈ eliminatedRotations p μ₀ (eliminateRotation μ ρ) := by
      apply (hrs.append hstep).mem_eliminatedRotations_iff.mpr
      simp [hrs.rotationLabels_append, rotationLabels, q, rotationOfExposed]
    have hq' := (eliminatedRotations_subset_iff hopt hstable ν.property).mpr hnext hq
    rw [hν] at hq'
    have hqr : q = r := (Set.mem_insert_iff.mp hq').resolve_right
      (rotationOfExposed_not_mem_eliminatedRotations hopt hμ hρ)
    rw [← hqr]
    exact ⟨hρ, rfl⟩
private noncomputable def singletonRotationAnchor (hopt : IsManOptimal p μ₀) (r : Rotation p μ₀) :
    {ν : Matching n // IsStable p ν} :=
  (stableMatchingEquivRotationIdeals hopt).symm (singletonAnchorIdeal r)
theorem eliminatedRotations_singletonRotationAnchor
    (hopt : IsManOptimal p μ₀) (r : Rotation p μ₀) :
    eliminatedRotations p μ₀ (singletonRotationAnchor hopt r).val = (Set.Ici r)ᶜ :=
  congrArg (fun I : LowerSet (Rotation p μ₀) ↦ (I : Set (Rotation p μ₀)))
    ((stableMatchingEquivRotationIdeals hopt).apply_symm_apply (singletonAnchorIdeal r))
theorem eq_singletonRotationAnchor_iff (hopt : IsManOptimal p μ₀) (r : Rotation p μ₀)
    (ν : {ν : Matching n // IsStable p ν}) :
    ν = singletonRotationAnchor hopt r ↔
      ∀ s : Rotation p μ₀, s.IsExposedAt ν.val ↔ s = r := by
  let e := stableMatchingEquivRotationIdeals hopt
  change ν = e.symm (singletonAnchorIdeal r) ↔ _
  rw [← e.apply_eq_iff_eq, e.apply_symm_apply, lowerSet_eq_singletonAnchorIdeal_iff]
  simp only [Rotation.isExposedAt_iff_minimal hopt ν.property]
  rfl
theorem isExposedRotation_singletonRotationAnchor_iff
    (hopt : IsManOptimal p μ₀) (r : Rotation p μ₀) (ρ : Equiv.Perm (Fin n)) :
    IsExposedRotation p (singletonRotationAnchor hopt r).val ρ ↔ ρ = r.val.cycle := by
  let ν := singletonRotationAnchor hopt r
  have h := (eq_singletonRotationAnchor_iff hopt r ν).mp rfl
  constructor
  · intro hρ
    let q := rotationOfExposed hopt ν.property hρ
    exact congrArg (fun s : Rotation p μ₀ ↦ s.val.cycle) ((h q).mp ⟨hρ, rfl⟩)
  · rintro rfl
    exact ((h r).mpr rfl).1
end AbunLP
end

-- ReverseRotationIdeals
section
open StableMarriage
namespace AbunLP
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
end AbunLP
end

-- PivotCrossBlocker
section
open StableMarriage
namespace AbunLP
variable {n : ℕ} {p : Profile n} {A N : Matching n} {ρ : Equiv.Perm (Fin n)}
end AbunLP
end

-- PivotReversePermutationCompatibility
section
open StableMarriage
namespace AbunLP
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
end AbunLP
end

-- ReverseSupportWeightUpper
section
open scoped BigOperators ENNReal
namespace AbunLP
theorem sum_supportPermutation_weights_le_one {α : Type*} [Fintype α] [DecidableEq α]
    (k : ℕ) (r : α → ℝ≥0∞) (hr : ∑ i, r i = 1) :
    (∑ σ ∈ (Finset.univ : Finset (Equiv.Perm α)).filter (fun σ ↦ σ.support.card = k),
      ∏ i ∈ σ.support, r i) ≤ 1 := by
  classical
  have hfac : (k.factorial : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero k
  apply (ENNReal.mul_le_mul_iff_right hfac (ENNReal.natCast_ne_top _)).mp
  rw [mul_one]
  calc
    _ = ∑ e : derangements (Fin k),
        ∑ x ∈ Finset.univ.filter
          (fun x ↦ x ∈ iidLabelGood (∅ : Set α) (fun _ ↦ ∅) e.val), ∏ i, r (x i) := by
      simpa using (sum_iidLabelGood_eq_factorial_mul_sum_support k r ∅ (fun _ ↦ ∅)).symm
    _ ≤ ∑ _e : derangements (Fin k), (1 : ℝ≥0∞) :=
      Finset.sum_le_sum fun e _ ↦ calc
        _ ≤ ∑ x : Fin k → α, ∏ i, r (x i) :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
        _ = 1 := by rw [← Fintype.prod_sum]; simp [hr]
    _ = (Fintype.card (derangements (Fin k)) : ℝ≥0∞) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    _ ≤ _ := by
      have h := Fintype.card_subtype_le (fun e : Equiv.Perm (Fin k) ↦ e ∈ derangements (Fin k))
      rw [Fintype.card_perm, Fintype.card_fin] at h
      exact_mod_cast h
end AbunLP
end

-- PivotCompatibilityLoss
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace AbunLP
end AbunLP
end

-- UndoMaximalSubset
section
open StableMarriage
namespace AbunLP
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
end AbunLP
end

-- RotationUndoSequences
section
open StableMarriage
namespace AbunLP
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
end AbunLP
end

-- PivotIncidenceCounting
section
open StableMarriage
open scoped BigOperators
namespace AbunLP
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
end AbunLP
end

-- PivotCompatibleLowerMoment
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace AbunLP
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
end AbunLP
end

-- ReverseIncrementColumnTail
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace AbunLP
variable {ι : Type*}
end AbunLP
end

-- PivotReverseIncrementFilter
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace AbunLP
private def reverseScoreIncrement {n : ℕ} (x : ScoreProfile n) (μ : Matching n)
    (w j : Fin n) : ℝ := x (.inr w) j - x (.inr w) (μ.symm w)
private noncomputable def reverseIncrementCutoff (n : ℕ) (X : ℝ) : ℝ := 16 * Real.log (n : ℝ) / X
end AbunLP
end

-- PivotReverseFilteredCount
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace AbunLP
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
end AbunLP
end

-- ReverseColoredPermutations
section
open scoped BigOperators
namespace AbunLP
end AbunLP
end

-- CoexposureGaussianSum
section
open scoped BigOperators ENNReal
open Finset Filter
namespace AbunLP
private theorem inv_one_sub_mul_le {a b : ℝ} (ha₀ : 0 ≤ a) (hb₀ : 0 ≤ b)
    (ha : a ≤ 1 / 2) (hb : b ≤ 1 / 2) :
    (1 - a)⁻¹ * (1 - b)⁻¹ ≤ 1 + 4 * (a + b) := by
  have hinv (x : ℝ) (hx₀ : 0 ≤ x) (hx : x ≤ 1 / 2) : (1 - x)⁻¹ ≤ 1 + 2 * x := by
    rw [inv_eq_one_div, div_le_iff₀ (by linarith : 0 < 1 - x)]
    nlinarith [mul_nonneg hx₀ (show 0 ≤ 1 - 2 * x by linarith)]
  calc
    _ ≤ (1 + 2 * a) * (1 + 2 * b) :=
      mul_le_mul (hinv a ha₀ ha) (hinv b hb₀ hb)
        (inv_nonneg.mpr (by linarith)) (by positivity)
    _ ≤ _ := by nlinarith [mul_nonneg hb₀ (show 0 ≤ 2 - 4 * a by linarith)]
private noncomputable def coexposureSuccessorPerturbation (n : ℕ) : ℝ :=
  1000 * (Real.log (n : ℝ)) ^ 2 / (n : ℝ)
theorem eventually_coexposureSuccessorPerturbation_bounds :
    ∀ᶠ n : ℕ in atTop,
      0 < n ∧
      0 ≤ coexposureSuccessorPerturbation n ∧
      coexposureSuccessorPerturbation n ≤ 1 / Real.sqrt (n : ℝ) ∧
      0 < 1 - 192 * (Real.log (n : ℝ)) ^ 2 / (n : ℝ) ∧
      0 < 1 - 24 * Real.log (n : ℝ) / (n : ℝ) ∧
      (1 - 192 * (Real.log (n : ℝ)) ^ 2 / (n : ℝ))⁻¹ *
        (1 - 24 * Real.log (n : ℝ) / (n : ℝ))⁻¹ ≤
          1 + coexposureSuccessorPerturbation n := by
  have hcast : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog := (Real.tendsto_log_atTop.comp hcast).eventually_ge_atTop 1
  have hbound := ((isLittleO_log_rpow_rpow_atTop (2 : ℝ)
    (show 0 < (1 / 2 : ℝ) by norm_num)).comp_tendsto hcast).bound
      (show 0 < (1 / 1000 : ℝ) by norm_num)
  filter_upwards [hlog, hbound, eventually_ge_atTop (4 : ℕ)] with n hlogn hnorm hn4
  let x := (n : ℝ)
  let l := Real.log x
  let s := Real.sqrt x
  have hn : 0 < n := by omega
  have hx : 0 < x := by positivity
  have hl : 1 ≤ l := hlogn
  have hs₂ : s ^ 2 = x := Real.sq_sqrt hx.le
  have hs : 0 < s := Real.sqrt_pos.mpr hx
  have hs_ge : 2 ≤ s := by
    change 2 ≤ Real.sqrt x
    have h := Real.sqrt_le_sqrt (show (4 : ℝ) ≤ (n : ℝ) by exact_mod_cast hn4)
    rwa [show Real.sqrt (4 : ℝ) = 2 by norm_num] at h
  have hnorm' : l ^ 2 ≤ (1 / 1000 : ℝ) * s := by
    change ‖l ^ (2 : ℝ)‖ ≤ (1 / 1000 : ℝ) * ‖x ^ (1 / 2 : ℝ)‖ at hnorm
    rw [← Real.sqrt_eq_rpow, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), Real.norm_eq_abs, abs_of_nonneg hs.le] at hnorm
    exact hnorm
  let d := coexposureSuccessorPerturbation n
  have hd : d = 1000 * l ^ 2 / x := rfl
  have hd₀ : 0 ≤ d := by rw [hd]; positivity
  have hd_s : d ≤ 1 / s := by
    calc
      d ≤ s / x := by rw [hd]; exact div_le_div_of_nonneg_right (by linarith) hx.le
      _ = s / s ^ 2 := by rw [hs₂]
      _ = 1 / s := by field_simp
  have hd_half : d ≤ 1 / 2 :=
    hd_s.trans (one_div_le_one_div_of_le (by norm_num) hs_ge)
  let a := 192 * l ^ 2 / x
  let b := 24 * l / x
  have ha₀ : 0 ≤ a := by dsimp [a]; positivity
  have hb₀ : 0 ≤ b := by dsimp [b]; positivity
  have hsum : 4 * (a + b) ≤ d := by
    rw [hd]
    dsimp [a, b]
    rw [← add_div, ← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ hx.le
    nlinarith [mul_nonneg (show 0 ≤ l - 1 by linarith) (show 0 ≤ l by linarith)]
  have ha : a ≤ 1 / 2 := (show a ≤ 4 * (a + b) by linarith).trans (hsum.trans hd_half)
  have hb : b ≤ 1 / 2 := (show b ≤ 4 * (a + b) by linarith).trans (hsum.trans hd_half)
  exact ⟨hn, hd₀, hd_s, by change 0 < 1 - a; linarith, by change 0 < 1 - b; linarith,
    (inv_one_sub_mul_le ha₀ hb₀ ha hb).trans (add_le_add_right hsum _)⟩
end AbunLP
end

-- ReverseQuadraticGaussian
section
open Finset
open scoped BigOperators ENNReal
namespace AbunLP
end AbunLP
end

-- ReverseCycleCollectionMoment
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace AbunLP
end AbunLP
end

-- PivotReverseMaskMoment
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace AbunLP
end AbunLP
end

-- MeasureCountFilterLoss
section
open MeasureTheory
open scoped ENNReal
namespace AbunLP
variable {Ω : Type*} [MeasurableSpace Ω]
end AbunLP
end

-- ReverseCycleTypeWeightTransfer
section
open scoped BigOperators ENNReal
namespace AbunLP
end AbunLP
end

-- ShortCycleChebyshev
section
open scoped BigOperators ENNReal
namespace AbunLP
end AbunLP
end

-- UniformShortCycleMoments
section
open Equiv Equiv.Perm
open scoped BigOperators
namespace AbunLP
variable {α : Type*} [Fintype α] [DecidableEq α]
end AbunLP
end

-- PivotReverseFilterMoment
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace AbunLP
private noncomputable def reverseFilterSecondMomentConstant (C : ℝ) : ℝ :=
  2 * Real.exp ((4 * C + 3 + 3 / 2) ^ 2 / 2)
end AbunLP
end

-- PivotScoreLock
section
open StableMarriage
namespace AbunLP
variable {n : ℕ} {p : Profile n} {μ₀ μ ν : Matching n} {r : Rotation p μ₀}
theorem Rotation.IsExposedAt.eliminatedRotations_subset_singletonAnchor
    (he : r.IsExposedAt μ) (hopt : IsManOptimal p μ₀) (hμ : IsStable p μ) :
    eliminatedRotations p μ₀ μ ⊆
      eliminatedRotations p μ₀ (singletonRotationAnchor hopt r).val := by
  rw [eliminatedRotations_singletonRotationAnchor]
  intro s hs hrs
  exact ((r.isExposedAt_iff_minimal hopt hμ).mp he).prop (hrs μ hs)
theorem Rotation.IsExposedAt.partner_eq_of_moved
    (hμ : r.IsExposedAt μ) (hν : r.IsExposedAt ν) {m : Fin n} (hm : r.val.cycle m ≠ m) :
    μ m = ν m := by
  have he := congrArg (fun l : RotationLabel n ↦ l.oldPartner m) (hμ.2.trans hν.2.symm)
  simpa only [rotationLabel, if_neg hm, Option.some.injEq] using he
theorem Rotation.IsExposedAt.husband_eq_of_moved
    (hμ : r.IsExposedAt μ) (hν : r.IsExposedAt ν) {m : Fin n} (hm : r.val.cycle m ≠ m) :
    ν.symm (μ m) = m :=
  (Equiv.symm_apply_eq ν).2 (hμ.partner_eq_of_moved hν hm)
theorem Rotation.IsExposedAt.singletonAnchor_spouseScores_eq
    (he : r.IsExposedAt μ) (hopt : IsManOptimal p μ₀) (x : ScoreProfile n)
    {m : Fin n} (hm : r.val.cycle m ≠ m) :
    maleSpouseScore x μ m = maleSpouseScore x (singletonRotationAnchor hopt r).val m ∧
      femaleSpouseScore x μ (μ m) =
        femaleSpouseScore x (singletonRotationAnchor hopt r).val (μ m) := by
  have ha : r.IsExposedAt (singletonRotationAnchor hopt r).val :=
    ((eq_singletonRotationAnchor_iff hopt r _).mp rfl r).mpr rfl
  exact ⟨congrArg (x (.inl m)) (he.partner_eq_of_moved ha hm),
    congrArg (x (.inr (μ m))) ((μ.symm_apply_apply m).trans
      (he.husband_eq_of_moved ha hm).symm)⟩
theorem RotationSequence.womanRank_end_le {rs : List (Equiv.Perm (Fin n))}
    (hpath : RotationSequence p μ rs ν) (j : Fin n) :
    p.womanRank j (ν.symm j) ≤ p.womanRank j (μ.symm j) := by
  induction hpath with
  | nil => exact le_rfl
  | cons _ hρ _ ih => exact ih.trans (hρ.womanRank_eliminate_le j)
theorem femaleSpouseTotal_le_of_eliminatedRotations_subset {x : ScoreProfile n}
    {μ₀ μ ν : Matching n} (ht : ∀ row, Function.Injective (x row))
    (hopt : IsManOptimal (profileOfScores x) μ₀)
    (hμ : IsStable (profileOfScores x) μ) (hν : IsStable (profileOfScores x) ν)
    (hsub : eliminatedRotations (profileOfScores x) μ₀ μ ⊆
      eliminatedRotations (profileOfScores x) μ₀ ν) :
    femaleSpouseTotal x ν ≤ femaleSpouseTotal x μ := by
  obtain ⟨_, hpath⟩ := exists_rotationSequence_of_menWeaklyPrefer hμ hν
    ((eliminatedRotations_subset_iff hopt hμ hν).mp hsub)
  refine Finset.sum_le_sum fun j _ ↦ le_of_not_gt fun hgt ↦ ?_
  exact (not_lt_of_ge (hpath.womanRank_end_le j))
    ((rankPermutation_lt_iff (ht (.inr j)) (μ.symm j) (ν.symm j)).mpr hgt)
theorem Rotation.IsExposedAt.singletonAnchor_femaleSpouseTotal_bounds {x : ScoreProfile n}
    {μ₀ μ : Matching n} {r : Rotation (profileOfScores x) μ₀}
    (he : r.IsExposedAt μ) (ht : ∀ row, Function.Injective (x row))
    (hopt : IsManOptimal (profileOfScores x) μ₀) (hμ : IsStable (profileOfScores x) μ)
    {m : Fin n} (hm : r.val.cycle m ≠ m) {a b : ℝ} (hb : 0 < b)
    (hlo : femaleSpouseTotal x μ * a ≤ femaleSpouseScore x μ (μ m))
    (hhi : femaleSpouseScore x (singletonRotationAnchor hopt r).val (μ m) ≤
      femaleSpouseTotal x (singletonRotationAnchor hopt r).val * b) :
    femaleSpouseTotal x μ * a / b ≤ femaleSpouseTotal x (singletonRotationAnchor hopt r).val ∧
      femaleSpouseTotal x (singletonRotationAnchor hopt r).val ≤ femaleSpouseTotal x μ := by
  refine ⟨(div_le_iff₀ hb).2 ?_, femaleSpouseTotal_le_of_eliminatedRotations_subset ht hopt hμ
    (singletonRotationAnchor hopt r).property (he.eliminatedRotations_subset_singletonAnchor
      hopt hμ)⟩
  calc
    femaleSpouseTotal x μ * a ≤ femaleSpouseScore x μ (μ m) := hlo
    _ = femaleSpouseScore x (singletonRotationAnchor hopt r).val (μ m) :=
      (he.singletonAnchor_spouseScores_eq hopt x hm).2
    _ ≤ femaleSpouseTotal x (singletonRotationAnchor hopt r).val * b := hhi
theorem Rotation.IsExposedAt.singletonAnchor_femaleSpouseTotal_bounds_of_shares
    {x : ScoreProfile n} {μ₀ μ : Matching n} {r : Rotation (profileOfScores x) μ₀}
    (he : r.IsExposedAt μ) (ht : ∀ row, Function.Injective (x row))
    (hopt : IsManOptimal (profileOfScores x) μ₀) (hμ : IsStable (profileOfScores x) μ)
    {m : Fin n} (hm : r.val.cycle m ≠ m) {a b : ℝ} (hb : 0 < b)
    (hμpos : 0 < femaleSpouseTotal x μ)
    (hApos : 0 < femaleSpouseTotal x (singletonRotationAnchor hopt r).val)
    (hlo : a ≤ femaleSpouseScore x μ (μ m) / femaleSpouseTotal x μ)
    (hhi : femaleSpouseScore x (singletonRotationAnchor hopt r).val (μ m) /
      femaleSpouseTotal x (singletonRotationAnchor hopt r).val ≤ b) :
    femaleSpouseTotal x μ * a / b ≤ femaleSpouseTotal x (singletonRotationAnchor hopt r).val ∧
      femaleSpouseTotal x (singletonRotationAnchor hopt r).val ≤ femaleSpouseTotal x μ :=
  he.singletonAnchor_femaleSpouseTotal_bounds ht hopt hμ hm hb
    (by simpa only [mul_comm] using (le_div_iff₀ hμpos).mp hlo)
    (by simpa only [mul_comm] using (div_le_iff₀ hApos).mp hhi)
end AbunLP
end

-- PivotForwardExposureReveal
section
open MeasureTheory Set StableMarriage
namespace AbunLP
private theorem forwardEligible_iff_flag {n : ℕ} (μ : Matching n) (x : ScoreProfile n)
    (flag : OffDiagonalCellIndex n → Bool) (ht : ∀ r, Function.Injective (x r))
    (hmask : (splitScorePairs μ x).2 ∈ forwardScoreMaskEvent (splitScorePairs μ x).1 flag)
    (i j : Fin n) (hij : i ≠ j) :
    IsEligibleSuccessor (profileOfScores x) μ i (μ j) ↔ flag ⟨(i, j), hij⟩ = true := by
  let q : OffDiagonalCellIndex n := ⟨(i, j), hij⟩
  let d := (splitScorePairs μ x).1
  let z := (splitScorePairs μ x).2
  have he : IsEligibleSuccessor (profileOfScores x) μ i (μ j) ↔
      z q ∈ forwardEligibleScoreCell (diagonalPairAt d i).1 (diagonalPairAt d j).2 := by
    dsimp only [z, d]
    rw [splitScorePairs_offDiagonal_apply, diagonalPairAt_splitScorePairs,
      diagonalPairAt_splitScorePairs]
    simp only [IsEligibleSuccessor, forwardEligibleScoreCell, mem_prod, mem_Ioi, mem_Iio,
      Equiv.symm_apply_apply, profileOfScores, rankPermutation_lt_iff (ht (.inl i)),
      rankPermutation_lt_iff (ht (.inr (μ j))), q]
  have hh : z q ∈ forwardScoreCellFlagEvent (diagonalPairAt d i).1 (diagonalPairAt d j).2
      (flag q) := mem_pi.mp hmask q (mem_univ _)
  change _ ↔ flag q = true
  rw [he]
  by_cases hq : flag q = true
  · simp only [hq, forwardScoreCellFlagEvent] at hh
    simp only [hq, iff_true]
    exact hh
  · simp only [forwardScoreCellFlagEvent, if_neg hq, mem_compl_iff] at hh
    exact ⟨fun h ↦ (hh h).elim, fun h ↦ (hq h).elim⟩
private def forwardRevealExposureEvent {n : ℕ} (ρ : Matching n)
    (flag : OffDiagonalCellIndex n → Bool) : Set (ForwardRevealedMaleScores flag) :=
  {v | ρ.IsCycle ∧ ∀ m, ρ m ≠ m →
    ∃ q : ForwardActiveCellIndex flag, q.val.val = (m, ρ m) ∧
      ∀ t : ForwardActiveCellIndex flag, t.val.val.1 = m → v q ≤ v t}
theorem isExposedRotation_iff_forwardRevealExposureEvent {n : ℕ} (μ ρ : Matching n)
    (x : ScoreProfile n) (flag : OffDiagonalCellIndex n → Bool)
    (ht : ∀ r, Function.Injective (x r))
    (hmask : (splitScorePairs μ x).2 ∈ forwardScoreMaskEvent (splitScorePairs μ x).1 flag) :
    IsExposedRotation (profileOfScores x) μ ρ ↔
      (forwardRevealWithColumns flag (splitScorePairs μ x).2).1 ∈
        forwardRevealExposureEvent ρ flag := by
  let v := (forwardRevealWithColumns flag (splitScorePairs μ x).2).1
  let p := profileOfScores x
  have hscore (q : ForwardActiveCellIndex flag) :
      v q = x (.inl q.val.val.1) (μ q.val.val.2) :=
    congrArg Prod.fst (splitScorePairs_offDiagonal_apply μ x q.val)
  have hle (m j k : Fin n) :
      p.manRank m (μ j) ≤ p.manRank m (μ k) ↔ x (.inl m) (μ j) ≤ x (.inl m) (μ k) := by
    rw [← not_lt, ← not_lt]
    exact not_congr (rankPermutation_lt_iff (ht (.inl m)) _ _)
  constructor
  · intro h
    refine ⟨(IsExposedRotation.isCycle h), fun m hm ↦ ?_⟩
    let q₀ : OffDiagonalCellIndex n := ⟨(m, ρ m), hm.symm⟩
    let q : ForwardActiveCellIndex flag := ⟨q₀,
      (forwardEligible_iff_flag μ x flag ht hmask m (ρ m) hm.symm).mp (IsSuccessor.eligible ((IsExposedRotation.successor h) m hm))⟩
    refine ⟨q, rfl, fun t htm ↦ ?_⟩
    have htne : m ≠ t.val.val.2 := htm.symm ▸ t.val.property
    have hteq : (⟨(m, t.val.val.2), htne⟩ : OffDiagonalCellIndex n) = t.val :=
      Subtype.ext (Prod.ext htm.symm rfl)
    have hflag : flag ⟨(m, t.val.val.2), htne⟩ = true := by rw [hteq]; exact t.property
    have htel := (forwardEligible_iff_flag μ x flag ht hmask m t.val.val.2 htne).mpr hflag
    change v q ≤ v t
    rw [hscore q, hscore t, htm]
    exact (hle m (ρ m) t.val.val.2).mp ((IsSuccessor.min_rank ((IsExposedRotation.successor h) m hm)) _ htel)
  · rintro ⟨hcyc, htest⟩
    refine (IsExposedRotation.mk (hcyc) (fun m hm ↦ ?_))
    obtain ⟨q, hq, hmin⟩ := htest m hm
    have hq' : (⟨(m, ρ m), hm.symm⟩ : OffDiagonalCellIndex n) = q.val := Subtype.ext hq.symm
    refine (IsSuccessor.mk ((forwardEligible_iff_flag μ x flag ht hmask m (ρ m) hm.symm).mpr
      (hq' ▸ q.property)) (?_))
    intro w hwel
    let j := μ.symm w
    have hjw : μ j = w := μ.apply_symm_apply w
    have hj : m ≠ j := fun h ↦ (lt_irrefl _ (by simpa only [← hjw, ← h] using hwel.1))
    let t : ForwardActiveCellIndex flag := ⟨⟨(m, j), hj⟩,
      (forwardEligible_iff_flag μ x flag ht hmask m j hj).mp (hjw.symm ▸ hwel)⟩
    have h := hmin t rfl
    change v q ≤ v t at h
    rw [hscore q, hscore t, hq] at h
    exact hjw ▸ (hle m (ρ m) j).mpr h
theorem measurableSet_forwardRevealExposureEvent {n : ℕ} (ρ : Matching n)
    (flag : OffDiagonalCellIndex n → Bool) : MeasurableSet (forwardRevealExposureEvent ρ flag) := by
  unfold forwardRevealExposureEvent
  simp only [ofPred_and, ofPred_forall, ofPred_exists]
  refine (MeasurableSet.const _).inter (MeasurableSet.iInter fun (m : Fin n) ↦
    MeasurableSet.iInter fun (_ : ρ m ≠ m) ↦ MeasurableSet.iUnion
      fun (q : ForwardActiveCellIndex flag) ↦ (MeasurableSet.const _).inter
        (MeasurableSet.iInter fun (t : ForwardActiveCellIndex flag) ↦
          MeasurableSet.iInter fun (_ : t.val.val.1 = m) ↦ ?_))
  exact measurableSet_le (measurable_pi_apply q) (measurable_pi_apply t)
end AbunLP
end

-- PivotEligibilityScale
section
open Filter Real
open scoped BigOperators ENNReal Topology
namespace AbunLP
theorem exists_squareRootLabelBudget {b C B E : ℝ} (hb : 0 < b)
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hE : 0 ≤ E) :
    ∃ a : ℝ, 0 < a ∧ a < b ∧ C * a ^ 2 / 2 + (B + E) * a ≤ 1 / 4 := by
  let S := C + B + E + 1
  have hS : 1 ≤ S := by dsimp [S]; linarith
  have hS₀ : 0 < S := zero_lt_one.trans_le hS
  let a := min (b / 2) (1 / (4 * S))
  have ha₀ : 0 < a := lt_min (by positivity) (by positivity)
  have ha₁ : a ≤ 1 := (min_le_right ..).trans (by
    apply (div_le_iff₀ (by positivity : 0 < 4 * S)).2
    linarith)
  have ha₂ : a * S ≤ 1 / 4 := by
    have h := (le_div_iff₀ (by positivity : 0 < 4 * S)).1 (min_le_right (b / 2) (1 / (4 * S)))
    linarith only [h, show a * (4 * S) = 4 * (a * S) by ring]
  have ha_sq : a ^ 2 ≤ a := by
    simpa only [pow_two, mul_one] using mul_le_mul_of_nonneg_left ha₁ ha₀.le
  refine ⟨a, ha₀, (min_le_left ..).trans_lt (by linarith), ?_⟩
  have hCa := mul_le_mul_of_nonneg_left ha_sq hC
  dsimp only [S] at ha₂
  nlinarith only [hCa, ha₂, mul_nonneg hC ha₀.le, ha₀.le]
end AbunLP
end

-- PivotEligibleRevealControls
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace AbunLP
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
theorem exists_eligibleSupportCoefficient {b H B V : ℝ} (hb : 0 < b)
    (hH : 0 ≤ H) (hB : 0 ≤ B) (hV : 0 ≤ V) :
    ∃ κ, 0 < κ ∧ κ < b ∧ H * κ ^ 2 / 2 + (B + 1) * κ ≤ 1 / 4 ∧
      Real.exp (κ * (2 * (1 + B))) * (2 * κ * V) ≤ 3 / 32 := by
  let Q := 2 * (1 + B)
  let d₁ := 1 / (Q + 1)
  let d₂ := 3 / (64 * (V + 1) * Real.exp 1)
  have hQ : 0 ≤ Q := by dsimp [Q]; linarith
  have h₁ : 0 < d₁ := by dsimp [d₁]; positivity
  have h₂ : 0 < d₂ := by dsimp [d₂]; positivity
  obtain ⟨κ, hκ, hκ', hbudget⟩ := exists_squareRootLabelBudget
    (lt_min hb (lt_min h₁ h₂)) hH hB (by norm_num : 0 ≤ (1 : ℝ))
  have hκQ : κ * Q ≤ 1 := calc
    _ ≤ κ * (Q + 1) := mul_le_mul_of_nonneg_left (by linarith) hκ.le
    _ ≤ _ := (le_div_iff₀ (by positivity : 0 < Q + 1)).mp
      (hκ'.le.trans (min_le_right ..) |>.trans (min_le_left ..))
  have hκV : κ * (64 * (V + 1) * Real.exp 1) ≤ 3 :=
    (le_div_iff₀ (by positivity : 0 < 64 * (V + 1) * Real.exp 1)).mp
      (hκ'.le.trans (min_le_right ..) |>.trans (min_le_right ..))
  refine ⟨κ, hκ, hκ'.trans_le (min_le_left ..), hbudget, ?_⟩
  calc
    _ ≤ Real.exp 1 * (2 * κ * V) :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hκQ) (by positivity)
    _ ≤ Real.exp 1 * (2 * κ * (V + 1)) := by gcongr; linarith
    _ ≤ _ := by linarith only [hκV]
end AbunLP
end

-- PivotSpouseBandMask
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace AbunLP
private def pivotDiagonalFemaleTotal {n : ℕ} (d : DiagonalScorePairs n) : ℝ :=
  ∑ i, (diagonalPairAt d i).2
private def pivotBaseDiagonalBand (n : ℕ) : Set (DiagonalScorePairs n) :=
  {d | let X := reverseDiagonalMaleTotal d
       let Y := pivotDiagonalFemaleTotal d
       (∀ i, (diagonalPairAt d i).1 ∈ Ico 0 1 ∧ (diagonalPairAt d i).2 ∈ Ico 0 1) ∧
       2 ≤ Y ∧ Y ≤ (n : ℝ) ^ (2 / 5 : ℝ) ∧ (n : ℝ) / 128 ≤ X * Y ∧
       (∀ i, (diagonalPairAt d i).2 / Y ≤ 12 * Real.log n / n) ∧
       ∀ i, (diagonalPairAt d i).1 ≤ 8 * Real.log n / (Y - 1)}
theorem measurableSet_pivotBaseDiagonalBand (n : ℕ) :
    MeasurableSet (pivotBaseDiagonalBand n) := by
  have hx (i : Fin n) : Measurable (fun d : DiagonalScorePairs n ↦ (diagonalPairAt d i).1) :=
    measurable_fst.comp (measurable_pi_apply _)
  have hy (i : Fin n) : Measurable (fun d : DiagonalScorePairs n ↦ (diagonalPairAt d i).2) :=
    measurable_snd.comp (measurable_pi_apply _)
  have hX : Measurable (@reverseDiagonalMaleTotal n) :=
    Finset.measurable_sum _ fun i _ ↦ hx i
  have hY : Measurable (@pivotDiagonalFemaleTotal n) :=
    Finset.measurable_sum _ fun i _ ↦ hy i
  unfold pivotBaseDiagonalBand
  simp only [ofPred_and, ofPred_forall]
  refine (MeasurableSet.iInter fun i ↦
    (measurableSet_Ico.preimage (hx i)).inter (measurableSet_Ico.preimage (hy i))).inter ?_
  exact (measurableSet_le measurable_const hY).inter
    ((measurableSet_le hY measurable_const).inter
      ((measurableSet_le measurable_const (hX.mul hY)).inter
        ((MeasurableSet.iInter fun i ↦ measurableSet_le ((hy i).div hY) measurable_const).inter
          (MeasurableSet.iInter fun i ↦ measurableSet_le (hx i)
            (measurable_const.div (hY.sub measurable_const))))))
theorem normalizedMaleScore_le_of_spouseProduct {n : ℕ} {X Y x : ℝ}
    (hn : 0 < n) (hY : 2 ≤ Y) (hXY : (n : ℝ) / 128 ≤ X * Y)
    (hx : x ≤ 8 * Real.log n / (Y - 1)) :
    x / X ≤ 2048 * Real.log n / n := by
  have hn₀ : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hlog := Real.log_nonneg (show 1 ≤ (n : ℝ) by exact_mod_cast hn)
  have hY₀ : 0 < Y := by linarith
  have hY₁ : 0 < Y - 1 := by linarith
  have hXY₀ : 0 < X * Y := (div_pos hn₀ (by norm_num)).trans_le hXY
  have hX₀ : 0 < X := pos_of_mul_pos_left hXY₀ hY₀.le
  have hquot : Y / (Y - 1) ≤ 2 := (div_le_iff₀ hY₁).2 (by linarith)
  calc
    x / X ≤ (8 * Real.log n / (Y - 1)) / X := div_le_div_of_nonneg_right hx hX₀.le
    _ = (8 * Real.log n * (Y / (Y - 1))) / (X * Y) := by
      field_simp
    _ ≤ (8 * Real.log n * 2) / (X * Y) := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hquot (mul_nonneg (by norm_num) hlog)) hXY₀.le
    _ ≤ (8 * Real.log n * 2) / ((n : ℝ) / 128) := div_le_div_of_nonneg_left
      (by positivity) (div_pos hn₀ (by norm_num)) hXY
    _ = _ := by ring
end AbunLP
end

-- CoexposureScoreMomentBound
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace AbunLP
private def diagonalMale {n : ℕ} (d : DiagonalScorePairs n) (i : Fin n) : ℝ :=
  (diagonalPairAt d i).1
private def diagonalFemale {n : ℕ} (d : DiagonalScorePairs n) (i : Fin n) : ℝ :=
  (diagonalPairAt d i).2
private def diagonalFemaleTotal {n : ℕ} (d : DiagonalScorePairs n) : ℝ :=
  ∑ j, diagonalFemale d j
private def goodDiagonalScores (n : ℕ) : Set (DiagonalScorePairs n) :=
  {d | 2 ≤ diagonalFemaleTotal d ∧
    (∀ j, diagonalFemale d j / diagonalFemaleTotal d ≤ 12 * Real.log n / n) ∧
    (∀ i, diagonalMale d i ≤ 8 * Real.log n / (diagonalFemaleTotal d - 1))}
theorem mem_goodDiagonalScores_iff {n : ℕ} (x : ScoreProfile n) (μ : Matching n) :
    (splitScorePairs μ x).1 ∈ goodDiagonalScores n ↔ GoodSpouseScores x μ := by
  have hy (j : Fin n) : diagonalFemale (splitScorePairs μ x).1 j =
      femaleSpouseScore x μ (μ j) := by
    simp [diagonalFemale, diagonalPairAt_splitScorePairs, femaleSpouseScore]
  have hs : diagonalFemaleTotal (splitScorePairs μ x).1 = femaleSpouseTotal x μ := by
    simp only [diagonalFemaleTotal, hy, femaleSpouseTotal]
    exact Equiv.sum_comp μ (fun j ↦ x (.inr j) (μ.symm j))
  have hall : (∀ j, femaleSpouseScore x μ (μ j) / femaleSpouseTotal x μ ≤
      12 * Real.log n / n) ↔
      ∀ j, femaleSpouseScore x μ j / femaleSpouseTotal x μ ≤ 12 * Real.log n / n :=
    ⟨fun h j ↦ by simpa only [Equiv.apply_symm_apply] using h (μ.symm j),
      fun h j ↦ h (μ j)⟩
  simp only [goodDiagonalScores, mem_ofPred_eq, GoodSpouseScores, hs, hy, diagonalMale,
    diagonalPairAt_splitScorePairs, maleSpouseScore, hall]
theorem measurableSet_goodDiagonalScores (n : ℕ) : MeasurableSet (goodDiagonalScores n) := by
  have hm (i : Fin n) : Measurable (fun d : DiagonalScorePairs n ↦ diagonalMale d i) :=
    measurable_fst.comp (measurable_pi_apply _)
  have hf (i : Fin n) : Measurable (fun d : DiagonalScorePairs n ↦ diagonalFemale d i) :=
    measurable_snd.comp (measurable_pi_apply _)
  have hs : Measurable (fun d : DiagonalScorePairs n ↦ diagonalFemaleTotal d) :=
    Finset.measurable_sum _ fun i _ ↦ hf i
  unfold goodDiagonalScores
  simp only [ofPred_and, ofPred_forall]
  exact (measurableSet_le measurable_const hs).inter
    ((MeasurableSet.iInter fun j ↦ measurableSet_le ((hf j).div hs) measurable_const).inter
      (MeasurableSet.iInter fun i ↦ measurableSet_le (hm i)
        (measurable_const.div (hs.sub measurable_const))))
private theorem diagonal_good_product_le {n : ℕ} {d : DiagonalScorePairs n}
    (hg : d ∈ goodDiagonalScores n) (hx : ∀ i, 0 ≤ diagonalMale d i)
    (hy : ∀ j, 0 ≤ diagonalFemale d j) (i j : Fin n) :
    diagonalMale d i * diagonalFemale d j ≤ 192 * (Real.log n) ^ 2 / n := by
  let s := diagonalFemaleTotal d
  have hs : 2 ≤ s := hg.1
  have hspos : 0 < s := by linarith
  have hsone : 0 < s - 1 := by linarith
  have hscale : s / (s - 1) ≤ 2 := (div_le_iff₀ hsone).2 (by linarith)
  calc
    diagonalMale d i * diagonalFemale d j =
        (diagonalMale d i * (diagonalFemale d j / s)) * s := by
          rw [mul_assoc, div_mul_cancel₀ _ hspos.ne']
    _ ≤ (8 * Real.log n / (s - 1) * (12 * Real.log n / n)) * s :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul (hg.2.2 i) (hg.2.1 j) (div_nonneg (hy j) hspos.le)
          ((hx i).trans (hg.2.2 i))) hspos.le
    _ = (96 * (Real.log n) ^ 2 / n) * (s / (s - 1)) := by ring
    _ ≤ (96 * (Real.log n) ^ 2 / n) * 2 := mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = _ := by ring
private theorem diagonal_competitor_sum {n : ℕ} (y : Fin n → ℝ)
    (i : Fin n) (j : {j : Fin n // i ≠ j}) :
    (∑ k : {k : {k : Fin n // i ≠ k} // k ≠ j}, y k.val.val) =
      (∑ k, y k) - y i - y j.val := by
  classical
  have houter : (∑ k : {k : Fin n // i ≠ k}, y k.val) = (∑ k, y k) - y i := by
    rw [← Finset.sum_subtype (Finset.univ.erase i) (by simp [ne_comm]) y]
    linarith [Finset.sum_erase_add Finset.univ y (Finset.mem_univ i)]
  let f := fun k : {k : Fin n // i ≠ k} ↦ y k.val
  change (∑ k : {k : {k : Fin n // i ≠ k} // k ≠ j}, f k.val) =
    (∑ k, y k) - y i - f j
  rw [← Finset.sum_subtype (Finset.univ.erase j) (by simp) f]
  linarith [Finset.sum_erase_add Finset.univ f (Finset.mem_univ j)]
private theorem diagonal_arc_bound {n : ℕ} {d : DiagonalScorePairs n}
    (hg : d ∈ goodDiagonalScores n) (hx : ∀ i, 0 ≤ diagonalMale d i)
    (hy : ∀ j, 0 ≤ diagonalFemale d j)
    (hA : 0 < 1 - 192 * (Real.log n) ^ 2 / n)
    (hB : 0 < 1 - 24 * Real.log n / n)
    (hδ : (1 - 192 * (Real.log n) ^ 2 / n)⁻¹ * (1 - 24 * Real.log n / n)⁻¹ ≤
      1 + coexposureSuccessorPerturbation n) (i j : Fin n) :
    0 < diagonalFemaleTotal d - diagonalFemale d i - diagonalFemale d j ∧
      diagonalFemale d j / ((1 - diagonalMale d i * diagonalFemale d j) *
        (diagonalFemaleTotal d - diagonalFemale d i - diagonalFemale d j)) ≤
      (1 + coexposureSuccessorPerturbation n) * (diagonalFemale d j / diagonalFemaleTotal d) := by
  let s := diagonalFemaleTotal d
  let v := diagonalFemale d j
  let a := 1 - diagonalMale d i * v
  let b := s - diagonalFemale d i - v
  have hs : 0 < s := by linarith [show 2 ≤ s from hg.1]
  have ha : 1 - 192 * (Real.log n) ^ 2 / n ≤ a := by
    linarith only [diagonal_good_product_le hg hx hy i j]
  have hapos := hA.trans_le ha
  have hb : 1 - 24 * Real.log n / n ≤ b / s := by
    dsimp only [b, v]
    rw [sub_div, sub_div, div_self hs.ne']
    have hi := hg.2.1 i
    have hj := hg.2.1 j
    change diagonalFemale d i / s ≤ 12 * Real.log n / n at hi
    change diagonalFemale d j / s ≤ 12 * Real.log n / n at hj
    linarith only [hi, hj, show (24 : ℝ) * Real.log n / n =
      12 * Real.log n / n + 12 * Real.log n / n by ring]
  have hbpos : 0 < b := (div_pos_iff_of_pos_right hs).mp (hB.trans_le hb)
  refine ⟨hbpos, ?_⟩
  change v / (a * b) ≤ (1 + coexposureSuccessorPerturbation n) * (v / s)
  calc
    _ = (a⁻¹ * (b / s)⁻¹) * (v / s) := by
      field_simp [hapos.ne', hbpos.ne', hs.ne']
    _ ≤ ((1 - 192 * (Real.log n) ^ 2 / n)⁻¹ * (1 - 24 * Real.log n / n)⁻¹) * (v / s) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul (inv_anti₀ hA ha) (inv_anti₀ hB hb)
          (inv_nonneg.mpr (div_nonneg hbpos.le hs.le)) (inv_nonneg.mpr hA.le))
        (div_nonneg (hy j) hs.le)
    _ ≤ _ := mul_le_mul_of_nonneg_right hδ (div_nonneg (hy j) hs.le)
theorem stableScoreRowLaw_successor_le_of_goodDiagonalScores {n : ℕ} {d : DiagonalScorePairs n}
    (hg : d ∈ goodDiagonalScores n)
    (hx : ∀ i, (diagonalPairAt d i).1 ∈ Ico 0 1)
    (hy : ∀ j, (diagonalPairAt d j).2 ∈ Icc 0 1)
    (hA : 0 < 1 - 192 * (Real.log n) ^ 2 / n)
    (hB : 0 < 1 - 24 * Real.log n / n)
    (hδ : (1 - 192 * (Real.log n) ^ 2 / n)⁻¹ * (1 - 24 * Real.log n / n)⁻¹ ≤
      1 + coexposureSuccessorPerturbation n) (i : Fin n) (j : {j : Fin n // i ≠ j}) :
    stableScoreRowLaw d i (scoreRowSuccessorEvent d i j) ≤ stableScoreRowLaw d i univ *
      ENNReal.ofReal ((1 + coexposureSuccessorPerturbation n) *
        ((diagonalPairAt d j.val).2 / ∑ k, (diagonalPairAt d k).2)) := by
  have hsum := diagonal_competitor_sum (diagonalFemale d) i j
  have harc := diagonal_arc_bound hg (fun k ↦ (hx k).1) (fun k ↦ (hy k).1) hA hB hδ i j.val
  have hsum_pos : 0 < ∑ k : {k : {k : Fin n // i ≠ k} // k ≠ j},
      (diagonalPairAt d k.val.val).2 := by
    change 0 < ∑ k : {k : {k : Fin n // i ≠ k} // k ≠ j}, diagonalFemale d k.val.val
    rw [hsum]
    exact harc.1
  refine (stableScoreRowLaw_successor_le d i j (hx i) hy hsum_pos).trans ?_
  gcongr
  change diagonalFemale d j.val / ((1 - diagonalMale d i * diagonalFemale d j.val) *
    (∑ k : {k : {k : Fin n // i ≠ k} // k ≠ j}, diagonalFemale d k.val.val)) ≤ _
  rw [hsum]
  exact harc.2
end AbunLP
end

-- CoexposureScoreRefutation
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace AbunLP
private class LPHyp2_1 : Prop where
  bound : ∀ {C : ℝ} (hC : 0 ≤ C)
    (hmean : ∀ᶠ n : ℕ in atTop,
      expectedNumStableMatchings n ≤ C * ((n : ℝ) * Real.log n)),
    Tendsto (fun n ↦ continuousScoreLaw n (goodCoexposureScores n)ᶜ) atTop (𝓝 0)
theorem tendsto_measure_badCoexposureScores_zero_of_mean_upper [h : LPHyp2_1] {C : ℝ} (hC : 0 ≤ C)
    (hmean : ∀ᶠ n : ℕ in atTop,
      expectedNumStableMatchings n ≤ C * ((n : ℝ) * Real.log n)) :
    Tendsto (fun n ↦ continuousScoreLaw n (goodCoexposureScores n)ᶜ) atTop (𝓝 0) :=
  h.bound hC hmean
end AbunLP
end

-- PivotSpouseBandRegularity
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace AbunLP
private def rankStableSmallFemaleTotalEvent (n : ℕ) : Set (ScoreProfile n) :=
  {x | ∃ μ : Matching n, IsStable (profileOfScores x) μ ∧
    femaleSpouseTotal x μ < (9 / 10 : ℝ) * Real.log n}
private def rankStableBadPivotMaskEvent (n : ℕ) : Set (ScoreProfile n) :=
  {x | ∃ μ : Matching n, IsStable (profileOfScores x) μ ∧
    let z := splitScorePairs μ x
    z.1 ∈ pivotBaseDiagonalBand n ∧ z.2 ∈ badForwardMask z.1 ((n : ℝ) ^ (-11 / 20 : ℝ))}
private def goodPivotBaseGeometry (n : ℕ) : Set (ScoreProfile n) :=
  {x | x ∈ goodCoexposureScores n ∧
    (∀ μ : Matching n, IsStable (profileOfScores x) μ →
      (9 / 10 : ℝ) * Real.log n ≤ femaleSpouseTotal x μ ∧
      (n : ℝ) / 128 ≤ maleSpouseTotal x μ * femaleSpouseTotal x μ) ∧
    ∀ μ : Matching n, IsStable (profileOfScores x) μ →
      femaleSpouseTotal x μ ≤ (n : ℝ) ^ (2 / 5 : ℝ) →
      let z := splitScorePairs μ x
      z.1 ∈ pivotBaseDiagonalBand n ∧ z.2 ∉ badForwardMask z.1 ((n : ℝ) ^ (-11 / 20 : ℝ))}
end AbunLP
end

-- PivotSpouseSquareRegularity
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace AbunLP
private def largeSpouseAngularSquareSet (n : ℕ) : Set (Fin n → ℝ) :=
  {w | 24 < pittelAngularSquareScore w}
private def goodSpouseSquareWeights (n : ℕ) : Set (ScoreProfile n) :=
  {x | ∀ μ : Matching n, IsStable (profileOfScores x) μ →
    pittelAngularSquareScore (spouseAngle (fun i ↦ maleSpouseScore x μ i)) ≤ 24 ∧
    pittelAngularSquareScore (spouseAngle (femaleSpouseByHusband μ x)) ≤ 24}
theorem sum_reverseSpouseWeights_sq_le_of_angularSquare {n : ℕ} (hn : 0 < n)
    {x : ScoreProfile n} (μ : Matching n)
    (hscore : ∀ i, 0 ≤ maleSpouseScore x μ i)
    (h : pittelAngularSquareScore (spouseAngle (fun i ↦ maleSpouseScore x μ i)) ≤ 24) :
    (∑ j, (reverseSpouseWeights μ (splitScorePairs μ x).1 j) ^ 2) ≤
      ENNReal.ofReal (24 / (n : ℝ)) := by
  let d := (splitScorePairs μ x).1
  let v (i : Fin n) := maleSpouseScore x μ i
  let w := spouseAngle v
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hweight (i : Fin n) : reverseSpouseWeights μ d (μ i) = ENNReal.ofReal (w i) := by
    have he (j : Fin n) : (diagonalPairAt d j).1 = v j :=
      congrArg Prod.fst (diagonalPairAt_splitScorePairs μ x j)
    simp only [reverseSpouseWeights, Equiv.symm_apply_apply, he, w, spouseAngle]
  have hw (i : Fin n) : 0 ≤ w i :=
    div_nonneg (hscore i) (Finset.sum_nonneg fun j _ ↦ hscore j)
  have hreal : (∑ i, (w i) ^ 2) ≤ 24 / (n : ℝ) := by
    apply (le_div_iff₀ hn').mpr
    simpa only [pittelAngularSquareScore, mul_comm] using h
  calc
    _ = ∑ i, (reverseSpouseWeights μ d (μ i)) ^ 2 :=
      (Equiv.sum_comp μ (fun j ↦ (reverseSpouseWeights μ d j) ^ 2)).symm
    _ = ∑ i, ENNReal.ofReal ((w i) ^ 2) := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [hweight, ENNReal.ofReal_pow (hw i)]
    _ = ENNReal.ofReal (∑ i, (w i) ^ 2) :=
      (ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ sq_nonneg _).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hreal
theorem sum_femaleSpouseShares_sq_le_of_angularSquare {n : ℕ} (hn : 0 < n)
    {x : ScoreProfile n} (μ : Matching n)
    (h : pittelAngularSquareScore (spouseAngle (femaleSpouseByHusband μ x)) ≤ 24) :
    (∑ j, (femaleSpouseScore x μ j / femaleSpouseTotal x μ) ^ 2) ≤ 24 / (n : ℝ) := by
  let w := spouseAngle (femaleSpouseByHusband μ x)
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have he (i : Fin n) : w i = femaleSpouseScore x μ (μ i) / femaleSpouseTotal x μ := by
    change (femaleSpouseByHusband μ x i / ∑ j, femaleSpouseByHusband μ x j) = _
    rw [← femaleSpouseTotal_eq_sum_byHusband]
    rfl
  calc
    _ = ∑ i, (femaleSpouseScore x μ (μ i) / femaleSpouseTotal x μ) ^ 2 :=
      (Equiv.sum_comp μ (fun j ↦ (femaleSpouseScore x μ j / femaleSpouseTotal x μ) ^ 2)).symm
    _ = ∑ i, (w i) ^ 2 := Finset.sum_congr rfl fun i _ ↦ congrArg (· ^ (2 : ℕ)) (he i).symm
    _ ≤ _ := by
      apply (le_div_iff₀ hn').mpr
      simpa only [pittelAngularSquareScore, mul_comm] using h
private def goodPivotScoreGeometry (n : ℕ) : Set (ScoreProfile n) :=
  goodPivotBaseGeometry n ∩ goodSpouseSquareWeights n
theorem spouseSquareWeights_of_goodPivotScoreGeometry {n : ℕ} (hn : 0 < n)
    {x : ScoreProfile n} (hx : x ∈ goodPivotScoreGeometry n) (μ : Matching n)
    (hμ : IsStable (profileOfScores x) μ) :
    (∑ j, (reverseSpouseWeights μ (splitScorePairs μ x).1 j) ^ 2) ≤
      ENNReal.ofReal (24 / (n : ℝ)) ∧
    (∑ j, (femaleSpouseScore x μ j / femaleSpouseTotal x μ) ^ 2) ≤ 24 / (n : ℝ) := by
  have hsq := hx.2 μ hμ
  have hunit := hx.1.1.2.1
  exact ⟨sum_reverseSpouseWeights_sq_le_of_angularSquare hn μ
    (fun i ↦ (hunit (.inl i) (μ i)).1.le) hsq.1,
    sum_femaleSpouseShares_sq_le_of_angularSquare hn μ hsq.2⟩
theorem sum_spouseShares_mul_le_of_goodPivotScoreGeometry {n : ℕ} (hn : 0 < n)
    {x : ScoreProfile n} (hx : x ∈ goodPivotScoreGeometry n) (μ : Matching n)
    (hμ : IsStable (profileOfScores x) μ) :
    (∑ i, (femaleSpouseScore x μ (μ i) / femaleSpouseTotal x μ) *
      (maleSpouseScore x μ i / maleSpouseTotal x μ)) ≤ 24 / (n : ℝ) := by
  let p (i : Fin n) := femaleSpouseScore x μ (μ i) / femaleSpouseTotal x μ
  let r (i : Fin n) := maleSpouseScore x μ i / maleSpouseTotal x μ
  have hp : (∑ i, (p i) ^ 2) ≤ 24 / (n : ℝ) :=
    (Equiv.sum_comp μ (fun j ↦ (femaleSpouseScore x μ j / femaleSpouseTotal x μ) ^ 2)).le.trans
      (spouseSquareWeights_of_goodPivotScoreGeometry hn hx μ hμ).2
  have hr : (∑ i, (r i) ^ 2) ≤ 24 / (n : ℝ) := by
    have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
    apply (le_div_iff₀ hn').mpr
    simpa only [pittelAngularSquareScore, spouseAngle, r, maleSpouseTotal, mul_comm] using
      (hx.2 μ hμ).1
  change (∑ i, p i * r i) ≤ _
  calc
    _ ≤ ∑ i, ((p i) ^ 2 + (r i) ^ 2) / 2 :=
      Finset.sum_le_sum fun i _ ↦ by nlinarith only [sq_nonneg (p i - r i)]
    _ = ((∑ i, (p i) ^ 2) + (∑ i, (r i) ^ 2)) / 2 := by
      rw [← Finset.sum_div, Finset.sum_add_distrib]
    _ ≤ _ := by linarith only [hp, hr]
private class LPHyp2_0 : Prop where
  bound : Tendsto (fun n ↦ continuousScoreLaw n (goodPivotScoreGeometry n)ᶜ) atTop (𝓝 0)
theorem tendsto_measure_badPivotScoreGeometry_zero [h : LPHyp2_0] :
    Tendsto (fun n ↦ continuousScoreLaw n (goodPivotScoreGeometry n)ᶜ) atTop (𝓝 0) :=
  h.bound
end AbunLP
end

-- ForestDeterministic
section
open scoped BigOperators Classical
namespace AbunLP
private def RealizesDirectedCycle {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → Option ι) (σ : Equiv.Perm ι) : Prop :=
  σ.IsCycle ∧ ∀ i ∈ σ.support, f i = some (σ i)
end AbunLP
end

-- ForestProductProbability
section
open scoped BigOperators Classical
namespace AbunLP
end AbunLP
end

-- ForestRankOne
section
namespace AbunLP
end AbunLP
end

-- ForestRowThinning
section
open scoped BigOperators Classical
namespace AbunLP
end AbunLP
end

-- ForwardSuccessorRowLaw
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace AbunLP
private noncomputable def normalizedStableScoreRowLaw {n : ℕ}
    (d : DiagonalScorePairs n) (i : Fin n) :
    Measure ({j : Fin n // i ≠ j} → ℝ × ℝ) :=
  (stableScoreRowLaw d i univ)⁻¹ • stableScoreRowLaw d i
private theorem stableScoreRowLaw_univ_ne_zero {n : ℕ}
    (d : DiagonalScorePairs n) (i : Fin n)
    (hx : (diagonalPairAt d i).1 ∈ Ico 0 1)
    (hy : ∀ k, (diagonalPairAt d k).2 ∈ Icc 0 1) :
    stableScoreRowLaw d i univ ≠ 0 := by
  rw [stableScoreRowLaw, Measure.pi_univ]
  refine Finset.prod_ne_zero_iff.mpr fun j _ ↦ ?_
  change rowNonblockingLaw (diagonalPairAt d i).1 (diagonalPairAt d j.val).2 univ ≠ 0
  rw [rowNonblockingLaw_apply_univ ⟨hx.1, hx.2.le⟩ (hy j.val)]
  apply ENNReal.ofReal_ne_zero_iff.mpr
  have h := mul_le_mul_of_nonneg_left (hy j.val).2 hx.1
  linarith only [h, hx.2]
theorem normalizedStableScoreRowLaw_isProbabilityMeasure {n : ℕ}
    (d : DiagonalScorePairs n) (i : Fin n)
    (hx : (diagonalPairAt d i).1 ∈ Ico 0 1)
    (hy : ∀ k, (diagonalPairAt d k).2 ∈ Icc 0 1) :
    IsProbabilityMeasure (normalizedStableScoreRowLaw d i) := by
  constructor
  rw [normalizedStableScoreRowLaw, Measure.smul_apply, smul_eq_mul,
    ENNReal.inv_mul_cancel (stableScoreRowLaw_univ_ne_zero d i hx hy) (measure_ne_top _ _)]
theorem stableScoreRowLaw_eq_smul_normalized {n : ℕ} (d : DiagonalScorePairs n) (i : Fin n)
    (hx : (diagonalPairAt d i).1 ∈ Ico 0 1)
    (hy : ∀ k, (diagonalPairAt d k).2 ∈ Icc 0 1) :
    stableScoreRowLaw d i = stableScoreRowLaw d i univ • normalizedStableScoreRowLaw d i := by
  rw [normalizedStableScoreRowLaw, smul_smul,
    ENNReal.mul_inv_cancel (stableScoreRowLaw_univ_ne_zero d i hx hy) (measure_ne_top _ _),
    one_smul]
theorem isSuccessor_of_scoreRowSuccessorEvent {n : ℕ} (μ : Matching n) (x : ScoreProfile n)
    (ht : ∀ row, Function.Injective (x row))
    (i : Fin n) (j : {j : Fin n // i ≠ j})
    (h : offDiagonalRowsEquiv n (splitScorePairs μ x).2 i ∈
      scoreRowSuccessorEvent (splitScorePairs μ x).1 i j) :
    IsSuccessor (profileOfScores x) μ i (μ j.val) := by
  have hcell (a : {a : Fin n // i ≠ a}) :
      offDiagonalRowsEquiv n (splitScorePairs μ x).2 i a =
        (x (.inl i) (μ a.val), x (.inr (μ a.val)) i) :=
    splitScorePairs_offDiagonal_apply μ x ⟨(i, a.val), a.property⟩
  simp only [scoreRowSuccessorEvent, Set.mem_ofPred_eq, hcell, diagonalPairAt_splitScorePairs] at h
  have hman (w w' : Fin n) : (profileOfScores x).manRank i w < (profileOfScores x).manRank i w'
      ↔ x (.inl i) w < x (.inl i) w' :=
    rankPermutation_lt_iff (ht (.inl i)) w w'
  have hwoman (w m m' : Fin n) :
      (profileOfScores x).womanRank w m < (profileOfScores x).womanRank w m'
        ↔ x (.inr w) m < x (.inr w) m' :=
    rankPermutation_lt_iff (ht (.inr w)) m m'
  refine (IsSuccessor.mk (⟨(hman _ _).2 h.1, ?_⟩) (?_))
  · simpa only [Equiv.symm_apply_apply] using (hwoman (μ j.val) i j.val).2 h.2.1
  · intro w hw
    apply le_of_not_gt
    intro hlt
    have hi : i ≠ μ.symm w := by
      intro hi
      have heq : μ i = w := by rw [hi, Equiv.apply_symm_apply]
      exact (ne_of_lt hw.1) (congrArg ((profileOfScores x).manRank i) heq)
    let k : {k : Fin n // i ≠ k} := ⟨μ.symm w, hi⟩
    have hk : k ≠ j := by
      intro heq
      have hwj : w = μ j.val := by
        have hval := congrArg (fun k : {k : Fin n // i ≠ k} ↦ μ k.val) heq
        simpa only [k, Equiv.apply_symm_apply] using hval
      exact (ne_of_lt hlt) (congrArg ((profileOfScores x).manRank i) hwj)
    have hlt' : x (.inl i) w < x (.inl i) (μ j.val) := (hman _ _).1 hlt
    have hel' : x (.inr w) i < x (.inr w) (μ.symm w) := (hwoman _ _ _).1 hw.2
    exact h.2.2 ⟨k, hk⟩ (by simpa only [k, Equiv.apply_symm_apply] using And.intro hlt' hel')
theorem scoreRowSuccessorEvent_iff_isSuccessor_reconstructed {n : ℕ} (μ : Matching n)
    (d : DiagonalScorePairs n) (r : OffDiagonalScoreRows n)
    (i : Fin n) (j : {j : Fin n // i ≠ j})
    (hs : IsScoreStable ((splitScorePairs μ).symm (d, (offDiagonalRowsEquiv n).symm r)) μ)
    (ht : ∀ row, Function.Injective
      ((splitScorePairs μ).symm (d, (offDiagonalRowsEquiv n).symm r) row)) :
    r i ∈ scoreRowSuccessorEvent d i j ↔
      IsSuccessor
        (profileOfScores ((splitScorePairs μ).symm (d, (offDiagonalRowsEquiv n).symm r)))
        μ i (μ j.val) := by
  refine ⟨fun h ↦ isSuccessor_of_scoreRowSuccessorEvent μ _ ht i j ?_, ?_⟩
  · simpa only [MeasurableEquiv.apply_symm_apply] using h
  · exact scoreRowSuccessorEvent_of_isSuccessor_reconstructed μ d r i j hs ht
end AbunLP
end

-- ForwardSuccessorOutcome
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace AbunLP
private def uniqueScoreRowSuccessorEvent {n : ℕ} (d : DiagonalScorePairs n) (i : Fin n)
    (j : {j : Fin n // i ≠ j}) : Set ({j : Fin n // i ≠ j} → ℝ × ℝ) :=
  scoreRowSuccessorEvent d i j ∩ ⋂ k : {k : {k : Fin n // i ≠ k} // k ≠ j},
    (scoreRowSuccessorEvent d i k.val)ᶜ
private theorem measurableSet_uniqueScoreRowSuccessorEvent {n : ℕ} (d : DiagonalScorePairs n)
    (i : Fin n) (j : {j : Fin n // i ≠ j}) :
    MeasurableSet (uniqueScoreRowSuccessorEvent d i j) :=
  (measurableSet_scoreRowSuccessorEvent d i j).inter
    (MeasurableSet.iInter fun k ↦ (measurableSet_scoreRowSuccessorEvent d i k.val).compl)
private theorem uniqueScoreRowSuccessorEvent_of_unique {n : ℕ} {d : DiagonalScorePairs n}
    {i : Fin n} {r : {j : Fin n // i ≠ j} → ℝ × ℝ} {j : {j : Fin n // i ≠ j}}
    (hj : r ∈ scoreRowSuccessorEvent d i j)
    (huniq : ∀ k, r ∈ scoreRowSuccessorEvent d i k → k = j) :
    r ∈ uniqueScoreRowSuccessorEvent d i j :=
  ⟨hj, Set.mem_iInter.mpr fun k hk ↦ k.property (huniq k.val hk)⟩
private theorem uniqueScoreRowSuccessorEvent_unique {n : ℕ} {d : DiagonalScorePairs n}
    {i : Fin n} {r : {j : Fin n // i ≠ j} → ℝ × ℝ} {j k : {j : Fin n // i ≠ j}}
    (hj : r ∈ uniqueScoreRowSuccessorEvent d i j)
    (hk : r ∈ scoreRowSuccessorEvent d i k) : k = j := by
  by_contra hne
  exact (Set.mem_iInter.mp hj.2 ⟨k, hne⟩) hk
private noncomputable def forwardSuccessorOutcome {n : ℕ} (d : DiagonalScorePairs n) (i : Fin n)
    (r : {j : Fin n // i ≠ j} → ℝ × ℝ) : Option (Fin n) := by
  classical
  exact if h : ∃ j, r ∈ uniqueScoreRowSuccessorEvent d i j then some h.choose.val else none
private theorem forwardSuccessorOutcome_eq_some_iff_unique {n : ℕ} (d : DiagonalScorePairs n)
    (i : Fin n) (r : {j : Fin n // i ≠ j} → ℝ × ℝ) (j : {j : Fin n // i ≠ j}) :
    forwardSuccessorOutcome d i r = some j.val ↔ r ∈ uniqueScoreRowSuccessorEvent d i j := by
  classical
  unfold forwardSuccessorOutcome
  split
  · rename_i h
    constructor
    · intro he
      have hej : h.choose = j := Subtype.ext (Option.some.inj he)
      simpa only [hej] using h.choose_spec
    · intro hj
      rw [uniqueScoreRowSuccessorEvent_unique hj h.choose_spec.1]
  · rename_i h
    constructor
    · intro he
      cases he
    · exact fun hj ↦ (h ⟨j, hj⟩).elim
theorem forwardSuccessorOutcome_ne_some_self {n : ℕ} (d : DiagonalScorePairs n) (i : Fin n)
    (r : {j : Fin n // i ≠ j} → ℝ × ℝ) : forwardSuccessorOutcome d i r ≠ some i := by
  classical
  unfold forwardSuccessorOutcome
  split
  · rename_i h
    exact fun he ↦ h.choose.property (Option.some.inj he).symm
  · intro he
    cases he
theorem measurable_forwardSuccessorOutcome {n : ℕ} [MeasurableSpace (Option (Fin n))]
    (d : DiagonalScorePairs n) (i : Fin n) : Measurable (forwardSuccessorOutcome d i) := by
  apply measurable_to_countable'
  intro o
  cases o with
  | none =>
    have hset : forwardSuccessorOutcome d i ⁻¹' {none} =
        (⋃ j, uniqueScoreRowSuccessorEvent d i j)ᶜ := by
      classical
      ext r
      simp only [mem_preimage, mem_singleton_iff, mem_compl_iff, mem_iUnion]
      unfold forwardSuccessorOutcome
      split <;> simp_all
    rw [hset]
    exact (MeasurableSet.iUnion (measurableSet_uniqueScoreRowSuccessorEvent d i)).compl
  | some j =>
    by_cases hj : i = j
    · subst j
      have hset : forwardSuccessorOutcome d i ⁻¹' {some i} = ∅ :=
        eq_empty_iff_forall_notMem.mpr fun r ↦ forwardSuccessorOutcome_ne_some_self d i r
      rw [hset]
      exact MeasurableSet.empty
    · have hset : forwardSuccessorOutcome d i ⁻¹' {some j} =
          uniqueScoreRowSuccessorEvent d i ⟨j, hj⟩ :=
        Set.ext fun r ↦ forwardSuccessorOutcome_eq_some_iff_unique d i r ⟨j, hj⟩
      rw [hset]
      exact measurableSet_uniqueScoreRowSuccessorEvent d i ⟨j, hj⟩
private theorem scoreRowSuccessorEvent_unique_of_injective {n : ℕ} {d : DiagonalScorePairs n}
    {i : Fin n} {r : {j : Fin n // i ≠ j} → ℝ × ℝ}
    (hinj : Function.Injective (fun k ↦ (r k).1))
    {j k : {j : Fin n // i ≠ j}} (hj : r ∈ scoreRowSuccessorEvent d i j)
    (hk : r ∈ scoreRowSuccessorEvent d i k) : k = j := by
  by_contra hne
  have hle : (r j).1 ≤ (r k).1 :=
    le_of_not_gt fun h ↦ hj.2.2 ⟨k, hne⟩ ⟨h, hk.2.1⟩
  have hge : (r k).1 ≤ (r j).1 :=
    le_of_not_gt fun h ↦ hk.2.2 ⟨j, fun e ↦ hne e.symm⟩ ⟨h, hj.2.1⟩
  exact hne (hinj (le_antisymm hge hle))
theorem forwardSuccessorOutcome_eq_some_iff {n : ℕ} (d : DiagonalScorePairs n)
    (i : Fin n) (r : {j : Fin n // i ≠ j} → ℝ × ℝ) (j : {j : Fin n // i ≠ j})
    (hinj : Function.Injective (fun k ↦ (r k).1)) :
    forwardSuccessorOutcome d i r = some j.val ↔ r ∈ scoreRowSuccessorEvent d i j :=
  (forwardSuccessorOutcome_eq_some_iff_unique d i r j).trans
    ⟨fun h ↦ h.1, fun hj ↦ uniqueScoreRowSuccessorEvent_of_unique hj fun _ hk ↦
      scoreRowSuccessorEvent_unique_of_injective hinj hj hk⟩
theorem forwardSuccessorOutcome_eq_some_iff_isSuccessor {n : ℕ} (μ : Matching n)
    (d : DiagonalScorePairs n) (r : OffDiagonalScoreRows n)
    (i : Fin n) (j : {j : Fin n // i ≠ j})
    (hs : IsScoreStable ((splitScorePairs μ).symm (d, (offDiagonalRowsEquiv n).symm r)) μ)
    (ht : ∀ row, Function.Injective
      ((splitScorePairs μ).symm (d, (offDiagonalRowsEquiv n).symm r) row)) :
    forwardSuccessorOutcome d i (r i) = some j.val ↔
      IsSuccessor
        (profileOfScores ((splitScorePairs μ).symm (d, (offDiagonalRowsEquiv n).symm r)))
        μ i (μ j.val) := by
  have hiff (k : {k : Fin n // i ≠ k}) :=
    scoreRowSuccessorEvent_iff_isSuccessor_reconstructed μ d r i k hs ht
  apply (forwardSuccessorOutcome_eq_some_iff_unique d i (r i) j).trans
  exact ⟨fun hj ↦ (hiff j).mp hj.1, fun hj ↦
    uniqueScoreRowSuccessorEvent_of_unique ((hiff j).mpr hj) fun k hk ↦
      Subtype.ext (μ.injective (((hiff k).mp hk).unique hj))⟩
private theorem ae_injective_unitScoreLaw_pi (ι : Type*) [Fintype ι] :
    ∀ᵐ x ∂(Measure.pi fun _ : ι ↦ unitScoreLaw), Function.Injective (x : ι → ℝ) := by
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  have hpres := measurePreserving_piCongrLeft (fun _ : Fin (Fintype.card ι) ↦ unitScoreLaw) e
  filter_upwards [hpres.quasiMeasurePreserving.ae
    (ae_injective_iid unitScoreLaw (Fintype.card ι))] with x hx
  intro i j hij
  apply e.injective
  apply hx
  simpa only [MeasurableEquiv.piCongrLeft_apply_apply] using hij
theorem ae_injective_fst_normalizedStableScoreRowLaw {n : ℕ}
    (d : DiagonalScorePairs n) (i : Fin n) :
    ∀ᵐ r ∂normalizedStableScoreRowLaw d i,
      Function.Injective (fun k ↦ (r k).1) := by
  let ι := {j : Fin n // i ≠ j}
  let ν := Measure.pi fun _ : ι ↦ unitScorePairLaw
  have hm : Measure.map Prod.fst unitScorePairLaw = unitScoreLaw := by
    simp [unitScorePairLaw]
  have hmap : ν.map (fun (r : ι → ℝ × ℝ) k ↦ (r k).1) =
      Measure.pi fun _ : ι ↦ unitScoreLaw := by
    unfold ν
    rw [Measure.pi_map_pi (fun _ ↦ measurable_fst.aemeasurable)]
    simp only [hm]
  have hpres : MeasurePreserving (fun (r : ι → ℝ × ℝ) k ↦ (r k).1) ν
      (Measure.pi fun _ : ι ↦ unitScoreLaw) :=
    ⟨measurable_pi_iff.2 fun k ↦ measurable_fst.comp (measurable_pi_apply k), hmap⟩
  have hν : ∀ᵐ r ∂ν, Function.Injective (fun k ↦ (r k).1) :=
    hpres.quasiMeasurePreserving.ae (ae_injective_unitScoreLaw_pi ι)
  have hsub : stableScoreRowLaw d i ≤ ν := by
    rw [stableScoreRowLaw, ← Measure.restrict_pi_pi]
    exact Measure.restrict_le_self
  exact (Measure.smul_absolutelyContinuous.trans
    (Measure.absolutelyContinuous_of_le hsub)).ae_le hν
private noncomputable def forwardSuccessorOutcomeLaw {n : ℕ} [MeasurableSpace (Option (Fin n))]
    (d : DiagonalScorePairs n) (i : Fin n) : Measure (Option (Fin n)) :=
  Measure.map (forwardSuccessorOutcome d i) (normalizedStableScoreRowLaw d i)
theorem forwardSuccessorOutcomeLaw_some {n : ℕ} [MeasurableSpace (Option (Fin n))]
    [MeasurableSingletonClass (Option (Fin n))]
    (d : DiagonalScorePairs n) (i : Fin n) (j : {j : Fin n // i ≠ j}) :
    forwardSuccessorOutcomeLaw d i {some j.val} =
      normalizedStableScoreRowLaw d i (scoreRowSuccessorEvent d i j) := by
  rw [forwardSuccessorOutcomeLaw, Measure.map_apply (measurable_forwardSuccessorOutcome d i)
    (measurableSet_singleton _)]
  apply measure_congr
  filter_upwards [ae_injective_fst_normalizedStableScoreRowLaw d i] with r hr
  exact propext (forwardSuccessorOutcome_eq_some_iff d i r j hr)
theorem pi_stableScoreRowLaw_eq_smul_normalized {n : ℕ} (d : DiagonalScorePairs n)
    (hx : ∀ i, (diagonalPairAt d i).1 ∈ Ico 0 1)
    (hy : ∀ i, (diagonalPairAt d i).2 ∈ Icc 0 1) :
    Measure.pi (stableScoreRowLaw d) =
      (offDiagonalScoreLaw n (offDiagonalNonblocking d)) •
        Measure.pi (normalizedStableScoreRowLaw d) := by
  have (i : Fin n) := normalizedStableScoreRowLaw_isProbabilityMeasure d i (hx i) hy
  rw [← prod_stableScoreRowLaw_univ]
  calc
    _ = Measure.pi (fun i ↦ stableScoreRowLaw d i univ • normalizedStableScoreRowLaw d i) :=
      congrArg Measure.pi (funext fun i ↦ stableScoreRowLaw_eq_smul_normalized d i (hx i) hy)
    _ = _ := pi_smul_coordinates (normalizedStableScoreRowLaw d)
      (fun i ↦ stableScoreRowLaw d i univ) fun i ↦ measure_ne_top _ _
theorem offDiagonalScoreLaw_nonblocking_ne_zero_of_valid {n : ℕ} (d : DiagonalScorePairs n)
    (hx : ∀ i, (diagonalPairAt d i).1 ∈ Ico 0 1)
    (hy : ∀ i, (diagonalPairAt d i).2 ∈ Icc 0 1) :
    offDiagonalScoreLaw n (offDiagonalNonblocking d) ≠ 0 := by
  rw [← prod_stableScoreRowLaw_univ]
  refine Finset.prod_ne_zero_iff.mpr fun i _ h ↦ ?_
  have := normalizedStableScoreRowLaw_isProbabilityMeasure d i (hx i) hy
  have h1 : normalizedStableScoreRowLaw d i univ = 1 := measure_univ
  rw [normalizedStableScoreRowLaw, Measure.smul_apply, smul_eq_mul, h, mul_zero] at h1
  exact zero_ne_one h1
theorem ae_diagonal_ae_normalizedStableRows {n : ℕ} (μ : Matching n) :
    ∀ᵐ d ∂diagonalScoreLaw n,
      (∀ i, (diagonalPairAt d i).1 ∈ Ico 0 1) →
      (∀ i, (diagonalPairAt d i).2 ∈ Icc 0 1) →
      ∀ᵐ r ∂Measure.pi (normalizedStableScoreRowLaw d),
        let x := (splitScorePairs μ).symm (d, (offDiagonalRowsEquiv n).symm r)
        (∀ row, Function.Injective (x row)) ∧ IsScoreStable x μ := by
  filter_upwards [ae_diagonal_ae_stableRows μ] with d hd
  intro hx hy
  rw [pi_stableScoreRowLaw_eq_smul_normalized d hx hy,
    Measure.ae_ennreal_smul_measure_iff
      (offDiagonalScoreLaw_nonblocking_ne_zero_of_valid d hx hy)] at hd
  exact hd
end AbunLP
end

-- PivotForwardRowDeficit
section
open Filter MeasureTheory Set
open scoped BigOperators ENNReal
namespace AbunLP
private noncomputable def forwardSpouseWeight {n : ℕ} (d : DiagonalScorePairs n) (i : Fin n) : ℝ :=
  (diagonalPairAt d i).2 / ∑ j, (diagonalPairAt d j).2
end AbunLP
end

-- PivotForwardForest
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace AbunLP
private noncomputable def forwardOutcomeWeight {n : ℕ} [MeasurableSpace (Option (Fin n))]
    (d : DiagonalScorePairs n) (i : Fin n) (o : Option (Fin n)) : ℝ :=
  (forwardSuccessorOutcomeLaw d i).real {o}
theorem forwardOutcomeWeight_some {n : ℕ} [MeasurableSpace (Option (Fin n))]
    [MeasurableSingletonClass (Option (Fin n))] (d : DiagonalScorePairs n)
    (i : Fin n) (j : {j : Fin n // i ≠ j}) :
    forwardOutcomeWeight d i (some j.val) =
      (normalizedStableScoreRowLaw d i).real (scoreRowSuccessorEvent d i j) := by
  simp only [forwardOutcomeWeight, measureReal_def, forwardSuccessorOutcomeLaw_some]
theorem forwardOutcomeWeight_some_le_of_goodDiagonalScores {n : ℕ}
    [MeasurableSpace (Option (Fin n))] [MeasurableSingletonClass (Option (Fin n))]
    {d : DiagonalScorePairs n} (hg : d ∈ goodDiagonalScores n)
    (hx : ∀ i, (diagonalPairAt d i).1 ∈ Ico 0 1)
    (hy : ∀ j, (diagonalPairAt d j).2 ∈ Icc 0 1)
    (hA : 0 < 1 - 192 * (Real.log n) ^ 2 / n)
    (hB : 0 < 1 - 24 * Real.log n / n)
    (hδ : (1 - 192 * (Real.log n) ^ 2 / n)⁻¹ * (1 - 24 * Real.log n / n)⁻¹ ≤
      1 + coexposureSuccessorPerturbation n) (i : Fin n) (j : {j : Fin n // i ≠ j}) :
    forwardOutcomeWeight d i (some j.val) ≤
      (1 + coexposureSuccessorPerturbation n) * forwardSpouseWeight d j.val := by
  rw [forwardOutcomeWeight_some]
  let ν := stableScoreRowLaw d i
  let E := scoreRowSuccessorEvent d i j
  let C := (1 + coexposureSuccessorPerturbation n) * forwardSpouseWeight d j.val
  have hC : 0 ≤ C :=
    mul_nonneg ((mul_nonneg (inv_nonneg.mpr hA.le) (inv_nonneg.mpr hB.le)).trans hδ)
      (div_nonneg (hy j.val).1 ((by norm_num : (0 : ℝ) ≤ 2).trans hg.1))
  have h := stableScoreRowLaw_successor_le_of_goodDiagonalScores hg hx hy hA hB hδ i j
  change ν E ≤ ν univ * ENNReal.ofReal C at h
  have hn : normalizedStableScoreRowLaw d i E ≤ ENNReal.ofReal C := by
    rw [normalizedStableScoreRowLaw, Measure.smul_apply, smul_eq_mul]
    change (ν univ)⁻¹ * ν E ≤ _
    calc
      _ ≤ (ν univ)⁻¹ * (ν univ * ENNReal.ofReal C) := mul_le_mul_right h _
      _ = ((ν univ)⁻¹ * ν univ) * ENNReal.ofReal C := (mul_assoc _ _ _).symm
      _ ≤ ENNReal.ofReal C := by
        simpa only [one_mul] using
          (mul_le_mul' (ν univ).inv_mul_le_one (le_refl (ENNReal.ofReal C)))
  simpa only [measureReal_def, ENNReal.toReal_ofReal hC] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top hn
private def IsSoleForwardExposedRotation {n : ℕ} (p : Profile n) (μ σ : Matching n) : Prop :=
  IsExposedRotation p μ σ ∧ ∀ τ, IsExposedRotation p μ τ → τ = σ
theorem realizesDirectedCycle_forwardOutcome_iff {n : ℕ} (μ : Matching n)
    (d : DiagonalScorePairs n) (r : OffDiagonalScoreRows n) (σ : Matching n)
    (hs : IsScoreStable ((splitScorePairs μ).symm (d, (offDiagonalRowsEquiv n).symm r)) μ)
    (ht : ∀ row, Function.Injective
      ((splitScorePairs μ).symm (d, (offDiagonalRowsEquiv n).symm r) row)) :
    RealizesDirectedCycle (fun i ↦ forwardSuccessorOutcome d i (r i)) σ ↔
      IsExposedRotation
        (profileOfScores ((splitScorePairs μ).symm (d, (offDiagonalRowsEquiv n).symm r))) μ σ := by
  refine ⟨fun h ↦ (IsExposedRotation.mk (h.1) (?_)), fun h ↦ ⟨(IsExposedRotation.isCycle h), ?_⟩⟩
  · intro i hi
    exact (forwardSuccessorOutcome_eq_some_iff_isSuccessor μ d r i ⟨σ i, hi.symm⟩ hs ht).mp
      (h.2 i (Equiv.Perm.mem_support.mpr hi))
  · intro i hi
    have hne := Equiv.Perm.mem_support.mp hi
    exact (forwardSuccessorOutcome_eq_some_iff_isSuccessor μ d r i ⟨σ i, hne.symm⟩ hs ht).mpr
      ((IsExposedRotation.successor h) i hne)
end AbunLP
end

-- PivotLocalEligibility
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace AbunLP
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
theorem reverseDiagonalMaleTotal_splitScorePairs {n : ℕ}
    (μ : Matching n) (x : ScoreProfile n) :
    reverseDiagonalMaleTotal (splitScorePairs μ x).1 = maleSpouseTotal x μ :=
  Finset.sum_congr rfl fun i _ ↦ congrArg Prod.fst (diagonalPairAt_splitScorePairs μ x i)
theorem pivotDiagonalFemaleTotal_splitScorePairs {n : ℕ}
    (μ : Matching n) (x : ScoreProfile n) :
    pivotDiagonalFemaleTotal (splitScorePairs μ x).1 = femaleSpouseTotal x μ := by
  rw [femaleSpouseTotal_eq_sum_byHusband]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [diagonalPairAt_splitScorePairs, femaleSpouseByHusband, femaleSpouseScore,
    Equiv.symm_apply_apply]
private noncomputable def pivotMaleSupportMass {n : ℕ} (x : ScoreProfile n) (μ ρ : Matching n) : ℝ :=
  ∑ i ∈ ρ.support, maleSpouseScore x μ i / maleSpouseTotal x μ
private noncomputable def pivotNormalizedForwardIncrement {n : ℕ}
    (x : ScoreProfile n) (μ ρ : Matching n) : ℝ :=
  femaleSpouseTotal x μ *
    ∑ i ∈ ρ.support, (x (.inl i) (μ (ρ i)) - x (.inl i) (μ i))
theorem isLocallyEligiblePivot_of_good {n : ℕ} (hn : 0 < n) {b A B : ℝ}
    {x : ScoreProfile n} {μ ρ : Matching n}
    (ht : ∀ row, Function.Injective (x row))
    (hx : x ∈ goodPivotScoreGeometry n) (hμ : IsStable (profileOfScores x) μ)
    (hρ : IsSoleForwardExposedRotation (profileOfScores x) μ ρ)
    (hband : femaleSpouseTotal x μ ∈
      Icc ((n : ℝ) ^ (1 / 10 : ℝ)) ((n : ℝ) ^ (2 / 5 : ℝ)))
    (hlen : (ρ.support.card : ℝ) ∈ Icc (b * Real.sqrt (n : ℝ)) (A * Real.sqrt (n : ℝ)))
    (hmass : pivotMaleSupportMass x μ ρ ≤ B / Real.sqrt (n : ℝ))
    (hinc : pivotNormalizedForwardIncrement x μ ρ ≤ B * Real.sqrt (n : ℝ)) :
    IsLocallyEligiblePivot b A B x μ ρ := by
  let z := splitScorePairs μ x
  let flag := forwardMaskOfScores z.1 z.2
  let v := (forwardRevealWithColumns flag z.2).1
  have hmask : z.2 ∈ forwardScoreMaskEvent z.1 flag :=
    (forwardMaskOfScores_eq_iff _ _ _).mp rfl
  obtain ⟨hd, hmaskBound⟩ := hx.1.2.2 μ hμ hband.2
  obtain ⟨hmale, hfemale⟩ := spouseSquareWeights_of_goodPivotScoreGeometry hn hx μ hμ
  have hY : 0 < pivotDiagonalFemaleTotal z.1 := lt_of_lt_of_le (by norm_num) hd.2.1
  have hX : 0 < reverseDiagonalMaleTotal z.1 :=
    pos_of_mul_pos_left ((div_pos (Nat.cast_pos.mpr hn) (by norm_num)).trans_le hd.2.2.2.1) hY.le
  have hXeq := reverseDiagonalMaleTotal_splitScorePairs μ x
  have hYeq := pivotDiagonalFemaleTotal_splitScorePairs μ x
  have hshare (i : Fin n) : forwardSpouseWeight z.1 i =
      femaleSpouseScore x μ (μ i) / femaleSpouseTotal x μ := by
    rw [forwardSpouseWeight, diagonalPairAt_splitScorePairs]
    change x (.inr (μ i)) i / pivotDiagonalFemaleTotal z.1 = _
    rw [hYeq, femaleSpouseScore, Equiv.symm_apply_apply]
  have hfemale' : (∑ i, (forwardSpouseWeight z.1 i) ^ 2) ≤ 24 / (n : ℝ) := by
    simp_rw [hshare]
    rwa [Equiv.sum_comp μ (fun j ↦ (femaleSpouseScore x μ j / femaleSpouseTotal x μ) ^ 2)]
  have hpivot : (∑ i ∈ ρ.support, (diagonalPairAt z.1 i).1) ≤
      (B / Real.sqrt (n : ℝ)) * reverseDiagonalMaleTotal z.1 := by
    have hm : (∑ i ∈ ρ.support, (diagonalPairAt z.1 i).1) /
        reverseDiagonalMaleTotal z.1 ≤ B / Real.sqrt (n : ℝ) := by
      rw [Finset.sum_div, hXeq]
      simpa only [z, pivotMaleSupportMass, diagonalPairAt_splitScorePairs, maleSpouseScore]
        using hmass
    exact (div_le_iff₀ hX).mp hm
  refine ⟨(LocalPivotGeometry.mk hd (by rw [hYeq]; exact hband.1) (hlen.1) (hlen.2) (hmale) (hfemale') (fun j ↦ forwardMaskOmittedMass_le_of_notMem_badForwardMask z.1 hmaskBound j) (hpivot)),
    ?_, ?_, ?_⟩
  · intro τ
    rw [← isExposedRotation_iff_forwardRevealExposureEvent μ τ x flag ht hmask]
    exact ⟨hρ.2 τ, fun h ↦ h.symm ▸ hρ.1⟩
  · intro i hi
    have hne := Equiv.Perm.mem_support.mp hi
    rw [forwardPivotIncrement_eq_of_exposed μ ρ x flag ht hmask hρ.1 hne]
    exact sub_nonneg.mpr ((rankPermutation_lt_iff (ht (.inl i)) _ _).mp
      (IsSuccessor.eligible ((IsExposedRotation.successor hρ.1) i hne)).1).le
  · have he : (∑ i ∈ ρ.support, forwardPivotIncrement z.1 flag ρ v i) =
        ∑ i ∈ ρ.support, (x (.inl i) (μ (ρ i)) - x (.inl i) (μ i)) :=
      Finset.sum_congr rfl fun i hi ↦ forwardPivotIncrement_eq_of_exposed μ ρ x flag ht hmask
        hρ.1 (Equiv.Perm.mem_support.mp hi)
    change (∑ i ∈ ρ.support, forwardPivotIncrement z.1 flag ρ v i) ≤
      B * Real.sqrt (n : ℝ) / pivotDiagonalFemaleTotal z.1
    rw [he]
    apply (le_div_iff₀ hY).mpr
    rw [mul_comm, hYeq]
    exact hinc
theorem exists_localPivotSupportCoefficient {b B : ℝ} (hb : 0 < b) (hB : 0 ≤ B) :
    ∃ κ, 0 < κ ∧ κ < b ∧ 24 * κ ^ 2 / 2 + (B + 1) * κ ≤ 1 / 4 ∧
      Real.exp (κ * (2 * (1 + B))) * (2 * κ * (B / (1 / 128))) ≤ 3 / 32 :=
  exists_eligibleSupportCoefficient hb (by norm_num) hB (by positivity)
private theorem measurable_diagonalMaleScore {n : ℕ} (i : Fin n) :
    Measurable (fun d : DiagonalScorePairs n ↦ (diagonalPairAt d i).1) :=
  (measurable_pi_apply _).fst
private theorem measurable_diagonalFemaleScore {n : ℕ} (i : Fin n) :
    Measurable (fun d : DiagonalScorePairs n ↦ (diagonalPairAt d i).2) :=
  (measurable_pi_apply _).snd
private theorem measurable_pivotDiagonalFemaleTotal (n : ℕ) :
    Measurable (@pivotDiagonalFemaleTotal n) :=
  Finset.measurable_sum _ fun i _ ↦ measurable_diagonalFemaleScore i
theorem measurableSet_localPivotGeometry {n : ℕ} (b A B : ℝ) (μ ρ : Matching n)
    (flag : OffDiagonalCellIndex n → Bool) :
    MeasurableSet {d : DiagonalScorePairs n | LocalPivotGeometry b A B μ ρ d flag} := MarkedLP.measurableSet_localPivotGeometry b A B μ ρ flag

private theorem measurable_jointForwardPivotIncrement {n : ℕ}
    (flag : OffDiagonalCellIndex n → Bool) (ρ : Matching n) (m : Fin n) :
    Measurable (fun z : DiagonalScorePairs n × ForwardRevealedMaleScores flag ↦
      forwardPivotIncrement z.1 flag ρ z.2 m) := by
  by_cases hm : ρ m ≠ m
  · let q : OffDiagonalCellIndex n := ⟨(m, ρ m), hm.symm⟩
    by_cases hq : flag q = true
    · have hq' : flag (⟨(m, ρ m), hm.symm⟩ : OffDiagonalCellIndex n) = true := hq
      simp only [forwardPivotIncrement, dif_pos hm, dif_pos hq']
      exact (((measurable_pi_apply (⟨q, hq⟩ : ForwardActiveCellIndex flag)).comp
          (measurable_snd : Measurable (@Prod.snd (DiagonalScorePairs n) _))).sub
          ((measurable_diagonalMaleScore m).comp measurable_fst))
    · have hq' : flag (⟨(m, ρ m), hm.symm⟩ : OffDiagonalCellIndex n) ≠ true := hq
      simp only [forwardPivotIncrement, dif_pos hm, dif_neg hq']
      exact measurable_const
  · simp only [forwardPivotIncrement, dif_neg hm]
    exact measurable_const
theorem measurableSet_jointEligiblePivotReveal {n : ℕ}
    (B : ℝ) (flag : OffDiagonalCellIndex n → Bool) (ρ : Matching n) :
    MeasurableSet {z : DiagonalScorePairs n × ForwardRevealedMaleScores flag |
      z.2 ∈ eligiblePivotRevealSet z.1 flag ρ (localPivotIncrementCap B z.1)} := by
  have hs : MeasurableSet {v : ForwardRevealedMaleScores flag |
      ∀ τ : Matching n, v ∈ forwardRevealExposureEvent τ flag ↔ τ = ρ} := by
    rw [ofPred_forall]
    refine MeasurableSet.iInter fun τ ↦ ?_
    by_cases ht : τ = ρ
    · simpa only [ht, iff_true, ofPred_mem_eq] using
        measurableSet_forwardRevealExposureEvent ρ flag
    · simpa only [ht, iff_false, ← mem_compl_iff, ofPred_mem_eq] using
        (measurableSet_forwardRevealExposureEvent τ flag).compl
  have hcap : Measurable (fun z : DiagonalScorePairs n × ForwardRevealedMaleScores flag ↦
      localPivotIncrementCap B z.1) :=
    measurable_const.div ((measurable_pivotDiagonalFemaleTotal n).comp measurable_fst)
  have hnonneg : MeasurableSet {z : DiagonalScorePairs n × ForwardRevealedMaleScores flag |
      ∀ m ∈ ρ.support, 0 ≤ forwardPivotIncrement z.1 flag ρ z.2 m} := by
    simp only [ofPred_forall]
    exact MeasurableSet.iInter fun m ↦ MeasurableSet.iInter fun _ ↦
      measurableSet_le measurable_const (measurable_jointForwardPivotIncrement flag ρ m)
  have hsum : MeasurableSet {z : DiagonalScorePairs n × ForwardRevealedMaleScores flag |
      (∑ m ∈ ρ.support, forwardPivotIncrement z.1 flag ρ z.2 m) ≤
        localPivotIncrementCap B z.1} :=
    measurableSet_le (Finset.measurable_sum _ fun m _ ↦
      measurable_jointForwardPivotIncrement flag ρ m) hcap
  exact (measurable_snd hs).inter (hnonneg.inter hsum)
theorem measurable_jointForwardMaskOfScores (n : ℕ) :
    Measurable (fun z : DiagonalScorePairs n × OffDiagonalScorePairs n ↦
      forwardMaskOfScores z.1 z.2) := by
  apply measurable_pi_iff.2
  intro q
  apply measurable_to_bool
  have hz : Measurable (fun z : DiagonalScorePairs n × OffDiagonalScorePairs n ↦ z.2 q) :=
    (measurable_pi_apply q).comp measurable_snd
  have he : (fun z : DiagonalScorePairs n × OffDiagonalScorePairs n ↦
      forwardMaskOfScores z.1 z.2 q) ⁻¹' {true} =
      {z | (diagonalPairAt z.1 q.val.1).1 < (z.2 q).1} ∩
      {z | (z.2 q).2 < (diagonalPairAt z.1 q.val.2).2} := by
    ext z
    exact forwardCellFlag_eq_true.trans Set.mem_prod
  rw [he]
  exact (measurableSet_lt ((measurable_diagonalMaleScore _).comp measurable_fst) hz.fst).inter
    (measurableSet_lt hz.snd ((measurable_diagonalFemaleScore _).comp measurable_fst))
theorem measurableSet_isLocallyEligiblePivot {n : ℕ} (b A B : ℝ) (μ ρ : Matching n) :
    MeasurableSet {x : ScoreProfile n | IsLocallyEligiblePivot b A B x μ ρ} := by
  let Z := splitScorePairs μ
  let mask (x : ScoreProfile n) := forwardMaskOfScores (Z x).1 (Z x).2
  let E (flag : OffDiagonalCellIndex n → Bool) := {x : ScoreProfile n | mask x = flag ∧
    LocalPivotGeometry b A B μ ρ (Z x).1 flag ∧
    (forwardRevealWithColumns flag (Z x).2).1 ∈
      eligiblePivotRevealSet (Z x).1 flag ρ (localPivotIncrementCap B (Z x).1)}
  have hmask : Measurable mask := (measurable_jointForwardMaskOfScores n).comp Z.measurable
  have hE : {x : ScoreProfile n | IsLocallyEligiblePivot b A B x μ ρ} = ⋃ flag, E flag := by
    ext x
    refine ⟨fun h ↦ mem_iUnion.mpr ⟨mask x, rfl, h.1, h.2⟩, fun h ↦ ?_⟩
    obtain ⟨f, hf, hg, hv⟩ := mem_iUnion.mp h
    subst f
    exact ⟨hg, hv⟩
  rw [hE]
  refine MeasurableSet.iUnion fun flag ↦ (hmask (measurableSet_singleton flag)).inter
    ((((measurable_fst.comp Z.measurable) (measurableSet_localPivotGeometry b A B μ ρ flag))).inter ?_)
  exact (measurableSet_jointEligiblePivotReveal B flag ρ).preimage
    ((measurable_fst.comp Z.measurable).prodMk
      (measurable_fst.comp ((measurable_forwardRevealWithColumns flag).comp
        (measurable_snd.comp Z.measurable))))
end AbunLP
end

-- PivotMarkedDecorationCount
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace AbunLP
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
end AbunLP
end

-- PivotRestrictedMoment
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace AbunLP
section ConditionalOrder
variable {Ω : Type*} {m m₀ : MeasurableSpace Ω}
end ConditionalOrder
private noncomputable def stableMarkScoreLaw {n : ℕ} (μ : Matching n) : Measure (ScoreProfile n) :=
  (continuousScoreLaw n).restrict {x | IsScoreStable x μ}
end AbunLP
end

-- PivotFullRevealLaw
section
open MeasureTheory Set StableMarriage
open scoped ENNReal
namespace AbunLP
private abbrev PivotMaleRevealData (n : ℕ) :=
  DiagonalScorePairs n × (OffDiagonalCellIndex n → Bool) × (OffDiagonalCellIndex n → ℝ)
variable {n : ℕ}
private noncomputable def pivotMaleRevealFromScores (z : DiagonalScorePairs n × OffDiagonalScorePairs n) :
    PivotMaleRevealData n :=
  let flag := forwardMaskOfScores z.1 z.2
  (z.1, flag, fun q ↦ if flag q = true then (z.2 q).1 else 0)
private noncomputable def pivotMaleReveal (μ : Matching n) (x : ScoreProfile n) : PivotMaleRevealData n :=
  pivotMaleRevealFromScores (splitScorePairs μ x)
private noncomputable def pivotMaleRevealSpace (μ : Matching n) : MeasurableSpace (ScoreProfile n) :=
  MeasurableSpace.comap (pivotMaleReveal μ) inferInstance
end AbunLP
end

-- PivotConditionalMean
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace AbunLP
variable {n : ℕ}
private noncomputable def localPivotMeanFloor (b A B : ℝ) (K : ℕ) (μ ρ : Matching n)
    (x : ScoreProfile n) : ℝ :=
  {x | IsLocallyEligiblePivot b A B x μ ρ}.indicator
    (fun _ ↦ (3 / 64 : ℝ) * ((K - 1 : ℕ) : ℝ)) x
theorem localPivotMeanFloor_nonneg (b A B : ℝ) (K : ℕ) (μ ρ : Matching n)
    (x : ScoreProfile n) : 0 ≤ localPivotMeanFloor b A B K μ ρ x :=
  Set.indicator_nonneg (fun _ _ ↦ by positivity) _
private noncomputable def localPivotConditionalMean (b A B : ℝ) (K L : ℕ) (μ ρ : Matching n) :
    ScoreProfile n → ℝ :=
  (stableMarkScoreLaw μ)[localFilteredDecorationCount b A B K L μ ρ|pivotMaleRevealSpace μ]
private class LPHyp0_0 : Prop where
  bound : ∀ (K L : ℕ → ℕ)
    {B κ : ℝ} (hB : 0 ≤ B) (hκ : 0 ≤ κ)
    (hK : ∀ᶠ n in atTop, 2 ≤ K n ∧ (K n : ℝ) ≤ κ * Real.sqrt (n : ℝ))
    (hL : Tendsto L atTop atTop)
    (hsmallLabel : 24 * κ ^ 2 / 2 + (B + 1) * κ ≤ 1 / 4)
    (hsmallCompat : Real.exp (κ * (2 * (1 + B))) * (2 * κ * (B / (1 / 128))) ≤ 3 / 32),
    ∀ᶠ n : ℕ in atTop, ∀ (μ ρ : Matching n) (b A : ℝ),
      localPivotMeanFloor b A B (K n) μ ρ ≤ᵐ[stableMarkScoreLaw μ]
        localPivotConditionalMean b A B (K n) (L n) μ ρ
theorem eventually_localPivotMeanFloor_le_conditionalMean_ae [h : LPHyp0_0] (K L : ℕ → ℕ)
    {B κ : ℝ} (hB : 0 ≤ B) (hκ : 0 ≤ κ)
    (hK : ∀ᶠ n in atTop, 2 ≤ K n ∧ (K n : ℝ) ≤ κ * Real.sqrt (n : ℝ))
    (hL : Tendsto L atTop atTop)
    (hsmallLabel : 24 * κ ^ 2 / 2 + (B + 1) * κ ≤ 1 / 4)
    (hsmallCompat : Real.exp (κ * (2 * (1 + B))) * (2 * κ * (B / (1 / 128))) ≤ 3 / 32) :
    ∀ᶠ n : ℕ in atTop, ∀ (μ ρ : Matching n) (b A : ℝ),
      localPivotMeanFloor b A B (K n) μ ρ ≤ᵐ[stableMarkScoreLaw μ]
        localPivotConditionalMean b A B (K n) (L n) μ ρ :=
  h.bound K L hB hκ hK hL hsmallLabel hsmallCompat
end AbunLP
end

-- DeferredAcceptanceTranscript
section
open StableMarriage
open scoped BigOperators
namespace AbunLP
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
private def run (p : Profile n) : ℕ → DAState n
  | 0 => initial n
  | k + 1 => advance p (run p k)
theorem run_alias : @run = @run := rfl
theorem run_zero (p : Profile n) : run p 0 = initial n := rfl
theorem run_succ (p : Profile n) (k : ℕ) : run p (k + 1) = advance p (run p k) := rfl
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
      have he : run p (k + 1) = run p k := by simp only [run, advance, hprev]
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
end DAState
end AbunLP
end

-- UniformStreamRanks
section
open Function MeasureTheory
open scoped ENNReal AbunLP
namespace AbunLP
variable {n T : ℕ}
end AbunLP
end

-- AdaptiveFiniteQueries
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace AbunLP
variable {I A : Type*}
variable [Fintype I] [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
end AbunLP
end

-- DAStreamSimulation
section
open StableMarriage
namespace AbunLP
private structure DAStreamState (n : ℕ) where
  da : DAState n
  observed : Fin n → List (Fin n)
namespace DAStreamState
variable {n T : ℕ}
private def initial (n : ℕ) : DAStreamState n := ⟨DAState.initial n, fun _ ↦ []⟩
end DAStreamState
end AbunLP
end

-- DAProposalCoupon
section
open Filter MeasureTheory Set StableMarriage
open scoped ENNReal Topology AbunLP
namespace AbunLP
variable {n T : ℕ}
end AbunLP
end

-- AdaptiveScoreRectangles
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace AbunLP
variable {ι : Type*}
variable [DecidableEq ι]
variable [Fintype ι]
end AbunLP
end

-- UniformLogScoreMoments
section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace AbunLP
section FiniteProduct
variable {ι : Type*}
variable [Fintype ι]


end FiniteProduct
end AbunLP
end

-- AdaptiveScoreFiberMoments
section
open MeasureTheory Set
open scoped BigOperators ENNReal MeasureTheory
namespace AbunLP
section Fiber
variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
end Fiber
section Cache
variable {α ι : Type*} [MeasurableSpace α] [Fintype ι]

end Cache
end AbunLP
end

-- AdaptiveScoreFiberAssembly
section
open MeasureTheory Set
namespace AbunLP
variable {α ι : Type*} [MeasurableSpace α] [Fintype ι]

end AbunLP
end

-- RotationParticipationClock
section
open StableMarriage
open scoped BigOperators
namespace AbunLP
private def rotationParticipation {n : ℕ} (rs : List (Equiv.Perm (Fin n))) : ℕ :=
  (rs.map fun σ ↦ σ.support.card).sum
private noncomputable def femaleLogPotential {n : ℕ} (x : ScoreProfile n) (μ : Matching n) : ℝ :=
  ∑ j, -Real.log (femaleSpouseScore x μ j)
theorem femaleSpouseScore_eliminate_eq_of_not_mem_support {n : ℕ} (x : ScoreProfile n)
    (μ : Matching n) (ρ : Equiv.Perm (Fin n)) {i : Fin n} (hi : i ∉ ρ.support) :
    femaleSpouseScore x (eliminateRotation μ ρ) (μ i) = femaleSpouseScore x μ (μ i) := by
  have hfix : ρ i = i := by simpa only [Equiv.Perm.mem_support, not_not] using hi
  have hpartner : eliminateRotation μ ρ i = μ i := by rw [eliminateRotation_apply, hfix]
  unfold femaleSpouseScore
  rw [(Equiv.symm_apply_eq (eliminateRotation μ ρ)).mpr hpartner.symm, μ.symm_apply_apply]
theorem femaleSpouseScore_eliminate_le {n : ℕ} (x : ScoreProfile n) {μ : Matching n}
    {ρ : Equiv.Perm (Fin n)} (hρ : IsExposedRotation (profileOfScores x) μ ρ)
    (ht : ∀ j, Function.Injective (x (.inr j))) (j : Fin n) :
    femaleSpouseScore x (eliminateRotation μ ρ) j ≤ femaleSpouseScore x μ j := by
  apply le_of_not_gt
  intro h
  exact (not_lt_of_ge (hρ.womanRank_eliminate_le j))
    ((rankPermutation_lt_iff (ht j) _ _).mpr h)
theorem femaleSpouseTotal_eliminate_le {n : ℕ} (x : ScoreProfile n) {μ : Matching n}
    {ρ : Equiv.Perm (Fin n)} (hρ : IsExposedRotation (profileOfScores x) μ ρ)
    (ht : ∀ j, Function.Injective (x (.inr j))) :
    femaleSpouseTotal x (eliminateRotation μ ρ) ≤ femaleSpouseTotal x μ :=
  Finset.sum_le_sum fun j _ ↦ femaleSpouseScore_eliminate_le x hρ ht j
open scoped Classical in
theorem femaleSpouseTotal_drop_le_support_mul {n : ℕ} (x : ScoreProfile n) (μ : Matching n)
    (ρ : Equiv.Perm (Fin n)) {B : ℝ} (hB : ∀ j, femaleSpouseScore x μ j ≤ B)
    (hx : ∀ j, 0 ≤ femaleSpouseScore x (eliminateRotation μ ρ) j) :
    femaleSpouseTotal x μ - femaleSpouseTotal x (eliminateRotation μ ρ) ≤
      (ρ.support.card : ℝ) * B := by
  have he (M : Matching n) : femaleSpouseTotal x M = ∑ i, femaleSpouseScore x M (μ i) :=
    (Equiv.sum_comp μ (femaleSpouseScore x M)).symm
  have hsupport : Finset.univ.filter (· ∈ ρ.support) = ρ.support := by ext; simp
  rw [he μ, he (eliminateRotation μ ρ), ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i : Fin n, if i ∈ ρ.support then B else 0 := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : i ∈ ρ.support
      · rw [if_pos hi]
        exact (sub_le_self _ (hx (μ i))).trans (hB (μ i))
      · rw [if_neg hi, femaleSpouseScore_eliminate_eq_of_not_mem_support x μ ρ hi, sub_self]
    _ = _ := by rw [← Finset.sum_filter, hsupport]; simp [nsmul_eq_mul]
theorem femaleSpouseTotal_drop_le_support_mul_share {n : ℕ} (x : ScoreProfile n) (μ : Matching n)
    (ρ : Equiv.Perm (Fin n)) {B : ℝ} (hY : 0 < femaleSpouseTotal x μ)
    (hB : ∀ j, femaleSpouseScore x μ j / femaleSpouseTotal x μ ≤ B)
    (hx : ∀ j, 0 ≤ femaleSpouseScore x (eliminateRotation μ ρ) j) :
    femaleSpouseTotal x μ - femaleSpouseTotal x (eliminateRotation μ ρ) ≤
      ((ρ.support.card : ℝ) * B) * femaleSpouseTotal x μ := by
  rw [mul_assoc]
  exact femaleSpouseTotal_drop_le_support_mul x μ ρ (fun j ↦ (div_le_iff₀ hY).mp (hB j)) hx
end AbunLP
end

-- RotationClockCells
section
open StableMarriage
namespace AbunLP
variable {n : ℕ} {p : Profile n} {μ ν : Matching n}
variable {ρ : Equiv.Perm (Fin n)}
end AbunLP
end

-- RotationSuccessorQueries
section
open StableMarriage
namespace AbunLP
private def runSuccessorQuery {α : Type*} (passes : α → Bool) :
    List α → Option α × List (α × Bool)
  | [] => (none, [])
  | w :: ws =>
    match passes w with
    | true => (some w, [(w, true)])
    | false =>
      let rest := runSuccessorQuery passes ws
      (rest.1, (w, false) :: rest.2)
theorem runSuccessorQuery_alias : @runSuccessorQuery = @runSuccessorQuery := rfl
theorem runSuccessorQuery_nil {α : Type*} (passes : α → Bool) :
    runSuccessorQuery passes [] = (none, []) := rfl
theorem runSuccessorQuery_cons {α : Type*} (passes : α → Bool) (w : α) (ws : List α) :
    runSuccessorQuery passes (w :: ws) =
      (match passes w with
      | true => (some w, [(w, true)])
      | false =>
        let rest := runSuccessorQuery passes ws
        (rest.1, (w, false) :: rest.2)) := by
  rw [runSuccessorQuery]
theorem runSuccessorQuery_fst {α : Type*} (passes : α → Bool) (candidates : List α) :
    (runSuccessorQuery passes candidates).1 = candidates.find? passes := by
  induction candidates with
  | nil => rfl
  | cons w ws ih =>
    cases h : passes w <;> simp [runSuccessorQuery, h, ih]
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
end AbunLP
end

-- ScoreRotationWalk
section
open StableMarriage
namespace AbunLP
variable {n : ℕ}
private noncomputable def scoreRotationGraph (x : ScoreProfile n) (μ : Matching n) :
    Fin n → Option (Fin n) :=
  queriedSuccessorGraph (profileOfScores x).manRank μ
    (successorScoreOracle (femaleSpouseScore x μ) (fun w ↦ x (.inr w)))
private noncomputable def scoreRotationWalk (x : ScoreProfile n) :
    ℕ → Matching n → List (Equiv.Perm (Fin n)) × Matching n
  | 0, μ => ([], μ)
  | k + 1, μ =>
    match chooseQueriedRotation (scoreRotationGraph x μ) with
    | none => ([], μ)
    | some ρ =>
      let out := scoreRotationWalk x k (eliminateRotation μ ρ)
      (ρ :: out.1, out.2)
theorem scoreRotationWalk_alias : @scoreRotationWalk = @scoreRotationWalk := rfl
theorem scoreRotationWalk_zero (x : ScoreProfile n) (μ : Matching n) :
    scoreRotationWalk x 0 μ = ([], μ) := by
  rw [scoreRotationWalk]
theorem scoreRotationWalk_succ (x : ScoreProfile n) (k : ℕ) (μ : Matching n) :
    scoreRotationWalk x (k + 1) μ =
      (match chooseQueriedRotation (scoreRotationGraph x μ) with
      | none => ([], μ)
      | some ρ =>
        let out := scoreRotationWalk x k (eliminateRotation μ ρ)
        (ρ :: out.1, out.2)) := by
  rw [scoreRotationWalk]
theorem scoreRotationWalk_legal (x : ScoreProfile n)
    (ht : ∀ j, Function.Injective (x (.inr j))) (k : ℕ)
    {μ : Matching n} (hμ : IsStable (profileOfScores x) μ) :
    RotationSequence (profileOfScores x) μ (scoreRotationWalk x k μ).1
      (scoreRotationWalk x k μ).2 := by
  induction k generalizing μ with
  | zero => exact .nil hμ
  | succ k ih =>
    rw [scoreRotationWalk]
    split
    · exact .nil hμ
    · rename_i ρ hselect
      have hρ : IsExposedRotation (profileOfScores x) μ ρ :=
        (realizesDirectedCycle_queriedSuccessorGraph_scores_iff x ht μ ρ).mp
          (realizesDirectedCycle_of_chooseQueriedRotation hselect)
      exact .cons hμ hρ (ih (hρ.isStable_eliminate hμ))
end AbunLP
end

-- ScoreRotationBranchLaw
section
open MeasureTheory Set StableMarriage
open scoped BigOperators Classical
namespace AbunLP
variable {n : ℕ}
end AbunLP
end

-- DALowerEndpoint
section
open Filter MeasureTheory Set StableMarriage
open scoped Classical ENNReal Topology
namespace AbunLP
variable {n : ℕ}
end AbunLP
end

-- ExponentialSpouseLogTail
section
open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal Topology
namespace AbunLP
local instance : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
  isProbabilityMeasure_expMeasure (by norm_num)
private noncomputable def spouseAngularLogExcess {n : ℕ} (p : Fin n → ℝ) : ℝ :=
  ∑ i, -Real.log ((n : ℝ) * p i)
end AbunLP
end

-- MarkedSpouseLogGeometry
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace AbunLP
private def largeSpouseAngularLogSet (n : ℕ) : Set (Fin n → ℝ) :=
  {p | 6 * (n : ℝ) < spouseAngularLogExcess p}
private def HasFemaleLogGeometry {n : ℕ} (x : ScoreProfile n) (μ : Matching n) : Prop :=
  (n : ℝ) * Real.log ((n : ℝ) / femaleSpouseTotal x μ) ≤ femaleLogPotential x μ ∧
    femaleLogPotential x μ ≤
      (n : ℝ) * Real.log ((n : ℝ) / femaleSpouseTotal x μ) + 6 * n
private def goodFemaleLogGeometry (n : ℕ) : Set (ScoreProfile n) :=
  {x | ∀ μ : Matching n, IsStable (profileOfScores x) μ → HasFemaleLogGeometry x μ}
theorem rotationParticipation_ge_log_drop {n : ℕ} (x : ScoreProfile n) (μ ν : Matching n)
    (rs : List (Equiv.Perm (Fin n))) (hμ : HasFemaleLogGeometry x μ)
    (hν : HasFemaleLogGeometry x ν) (hYμ : 0 < femaleSpouseTotal x μ)
    (hYν : 0 < femaleSpouseTotal x ν) {E : ℝ}
    (hclock : |femaleLogPotential x ν - femaleLogPotential x μ -
      (rotationParticipation rs : ℝ)| ≤ E) :
    (n : ℝ) * Real.log (femaleSpouseTotal x μ / femaleSpouseTotal x ν) - 6 * n - E ≤
      (rotationParticipation rs : ℝ) := by
  have hn : (0 : ℝ) < n := by
    cases n with
    | zero => simp [femaleSpouseTotal] at hYμ
    | succ n => positivity
  have hlog : Real.log (femaleSpouseTotal x μ / femaleSpouseTotal x ν) =
      Real.log ((n : ℝ) / femaleSpouseTotal x ν) -
        Real.log ((n : ℝ) / femaleSpouseTotal x μ) := by
    rw [Real.log_div hYμ.ne' hYν.ne', Real.log_div hn.ne' hYν.ne',
      Real.log_div hn.ne' hYμ.ne']
    ring
  rw [hlog, mul_sub]
  linarith only [hμ.2, hν.1, (le_abs_self _).trans hclock]
end AbunLP
end

-- CycleSupportCount
section
open Equiv.Perm Finset
open scoped BigOperators Classical
namespace AbunLP
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
end AbunLP
end

-- PointedSymmetricSums
section
open Finset
open scoped BigOperators
namespace AbunLP
end AbunLP
end

-- SingletonGaussianLength
section
open scoped BigOperators
open Finset
namespace AbunLP
private noncomputable def singletonLengthGaussian (n k : ℕ) : ℝ :=
  Real.exp (-(k : ℝ) ^ 2 / (16 * (n : ℝ)))
private theorem singletonLengthGaussian_eq (n k : ℕ) :
    singletonLengthGaussian n k = Real.exp (-((k : ℝ) / Real.sqrt n) ^ 2 / 16) := by
  unfold singletonLengthGaussian
  rw [div_pow, Real.sq_sqrt (by positivity : 0 ≤ (n : ℝ))]
  congr 1
  ring
private theorem singletonLengthGaussian_le_one (n k : ℕ) : singletonLengthGaussian n k ≤ 1 := by
  unfold singletonLengthGaussian
  exact Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _))
    (by positivity))
private theorem expGeometric_sum_le (s : Finset ℕ) {r : ℝ} (hr : 0 < r) :
    (∑ k ∈ s, Real.exp (-(k : ℝ) / r)) ≤ 1 + r := by
  let q := Real.exp (-(1 / r))
  have hq₀ : 0 ≤ q := Real.exp_nonneg _
  have hq₁ : q < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (one_div_pos.mpr hr))
  have hq : q ≤ r / (1 + r) := calc
    _ = (Real.exp (1 / r))⁻¹ := Real.exp_neg _
    _ ≤ (1 / r + 1)⁻¹ := inv_anti₀ (by positivity) (Real.add_one_le_exp (1 / r))
    _ = _ := by field_simp
  have hmul : 1 ≤ (1 + r) * (1 - q) := by
    have h := (le_div_iff₀ (by positivity : 0 < 1 + r)).mp hq
    nlinarith only [h]
  calc
    _ = ∑ k ∈ s, q ^ k := by
      refine sum_congr rfl fun k _ ↦ ?_
      dsimp [q]
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ ∑' k : ℕ, q ^ k :=
      (summable_geometric_of_lt_one hq₀ hq₁).sum_le_tsum s (fun _ _ ↦ by positivity)
    _ = (1 - q)⁻¹ := tsum_geometric_of_lt_one hq₀ hq₁
    _ ≤ 1 + r := by
      rw [← one_div]
      exact (div_le_iff₀ (sub_pos.mpr hq₁)).mpr hmul
theorem singletonLengthGaussian_sum_le {n : ℕ} (hn : 0 < n) (K : Finset ℕ) :
    (∑ k ∈ K, singletonLengthGaussian n k) ≤ 2 * Real.exp 4 * Real.sqrt n := by
  let r := Real.sqrt (n : ℝ)
  have hr : 0 < r := Real.sqrt_pos.mpr (by positivity)
  have hr₁ : 1 ≤ r := by
    change 1 ≤ Real.sqrt (n : ℝ)
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hn)
  calc
    _ ≤ ∑ k ∈ K, Real.exp 4 * Real.exp (-(k : ℝ) / r) := by
      refine sum_le_sum fun k _ ↦ ?_
      rw [singletonLengthGaussian_eq, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      change -((k : ℝ) / r) ^ 2 / 16 ≤ 4 + -(k : ℝ) / r
      rw [show -(k : ℝ) / r = -((k : ℝ) / r) by ring]
      generalize (k : ℝ) / r = t
      nlinarith only [sq_nonneg (t - 8)]
    _ = Real.exp 4 * ∑ k ∈ K, Real.exp (-(k : ℝ) / r) := (mul_sum ..).symm
    _ ≤ Real.exp 4 * (1 + r) :=
      mul_le_mul_of_nonneg_left (expGeometric_sum_le K hr) (Real.exp_nonneg _)
    _ ≤ 2 * Real.exp 4 * r := by
      have h := mul_nonneg (Real.exp_nonneg 4) (sub_nonneg.mpr hr₁)
      nlinarith only [h]
theorem singletonLengthGaussian_countSum_le {n : ℕ} (hn : 0 < n)
    {τ s : ℝ} (hτ : 0 ≤ τ) (hs : 0 ≤ s) :
    (∑ k ∈ Icc 2 n, singletonLengthGaussian n k * (τ / (k : ℝ) + s)) ≤
      τ * (1 + Real.log n) + 2 * Real.exp 4 * Real.sqrt n * s := by
  have hH : (∑ k ∈ Icc 2 n, (k : ℝ)⁻¹) ≤ 1 + Real.log n := calc
    _ ≤ ∑ k ∈ Icc 1 n, (k : ℝ)⁻¹ := sum_le_sum_of_subset_of_nonneg
      (by intro k hk; simp only [mem_Icc] at hk ⊢; omega) (fun _ _ _ ↦ by positivity)
    _ = (harmonic n : ℝ) := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    _ ≤ _ := harmonic_le_one_add_log n
  have hweighted :
      (∑ k ∈ Icc 2 n, singletonLengthGaussian n k * (τ / (k : ℝ))) ≤
        τ * (1 + Real.log n) := calc
    _ ≤ ∑ k ∈ Icc 2 n, τ / (k : ℝ) :=
      sum_le_sum fun k _ ↦ mul_le_of_le_one_left (by positivity)
        (singletonLengthGaussian_le_one n k)
    _ = τ * ∑ k ∈ Icc 2 n, (k : ℝ)⁻¹ := by simp only [mul_sum, div_eq_mul_inv]
    _ ≤ _ := mul_le_mul_of_nonneg_left hH hτ
  calc
    _ = (∑ k ∈ Icc 2 n, singletonLengthGaussian n k * (τ / (k : ℝ))) +
        (∑ k ∈ Icc 2 n, singletonLengthGaussian n k) * s := by
      simp_rw [sum_mul, ← sum_add_distrib, mul_add]
    _ ≤ _ := add_le_add hweighted
      (mul_le_mul_of_nonneg_right (singletonLengthGaussian_sum_le hn (Icc 2 n)) hs)
open scoped Classical in
theorem singletonLengthGaussian_longSum_le {n : ℕ} (hn : 0 < n) (a : ℝ)
    {τ s : ℝ} (hτ : 0 ≤ τ) (hs : 0 ≤ s) :
    (∑ k ∈ (Icc 2 n).filter (fun k : ℕ ↦ a * Real.sqrt n < (k : ℝ)),
      (k : ℝ) * singletonLengthGaussian n k * (τ / (k : ℝ) + s)) ≤
      2 * Real.exp 4 * τ * Real.sqrt n + 6 * Real.exp 16 * Real.exp (-a) * s * (n : ℝ) := by
  let r := Real.sqrt (n : ℝ)
  let K := (Icc 2 n).filter (fun k : ℕ ↦ a * r < (k : ℝ))
  have hr : 0 < r := Real.sqrt_pos.mpr (by positivity)
  have hr₂ : r ^ 2 = (n : ℝ) := Real.sq_sqrt (by positivity)
  have hr₁ : 1 ≤ r := by
    change 1 ≤ Real.sqrt (n : ℝ)
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hn)
  have hfirst : (∑ k ∈ K, (k : ℝ) * singletonLengthGaussian n k * (τ / (k : ℝ))) ≤
      2 * Real.exp 4 * τ * r := calc
    _ = (∑ k ∈ K, singletonLengthGaussian n k) * τ := by
      rw [sum_mul]
      refine sum_congr rfl fun k hk ↦ ?_
      have hk₀ : (k : ℝ) ≠ 0 := by
        have hk₂ := (mem_Icc.mp (mem_filter.mp hk).1).1
        exact_mod_cast (show k ≠ 0 by omega)
      field_simp
    _ ≤ (2 * Real.exp 4 * r) * τ :=
      mul_le_mul_of_nonneg_right (singletonLengthGaussian_sum_le hn K) hτ
    _ = _ := by ring
  have hsecond : (∑ k ∈ K, (k : ℝ) * singletonLengthGaussian n k) ≤
      6 * Real.exp 16 * Real.exp (-a) * (n : ℝ) := by
    let B := Real.exp 16 * Real.exp (-a)
    have hB : 0 ≤ B := by dsimp [B]; positivity
    have hterm (k : ℕ) (hk : k ∈ K) :
        (k : ℝ) * singletonLengthGaussian n k ≤
          (2 * r * B) * Real.exp (-(k : ℝ) / (2 * r)) := by
      let t := (k : ℝ) / r
      have ht : 0 ≤ t := by dsimp [t]; positivity
      have hat : a < t := (lt_div_iff₀ hr).mpr (mem_filter.mp hk).2
      have ht_exp : t ≤ 2 * Real.exp (t / 2) := by linarith only [Real.add_one_le_exp (t / 2)]
      have hG : singletonLengthGaussian n k ≤ B * Real.exp (-t) := by
        rw [singletonLengthGaussian_eq]
        dsimp only [B]
        rw [← Real.exp_add, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        change -t ^ 2 / 16 ≤ 16 + -a + -t
        nlinarith only [sq_nonneg (t - 16), hat]
      have hkr : (k : ℝ) = r * t := by dsimp [t]; field_simp
      calc
        _ ≤ (k : ℝ) * (B * Real.exp (-t)) := mul_le_mul_of_nonneg_left hG (by positivity)
        _ = (r * B * Real.exp (-t)) * t := by rw [hkr]; ring
        _ ≤ (r * B * Real.exp (-t)) * (2 * Real.exp (t / 2)) :=
          mul_le_mul_of_nonneg_left ht_exp (by positivity)
        _ = _ := by
          rw [show (r * B * Real.exp (-t)) * (2 * Real.exp (t / 2)) =
            (2 * r * B) * (Real.exp (-t) * Real.exp (t / 2)) by ring, ← Real.exp_add]
          congr 2
          dsimp [t]
          ring
    calc
      _ ≤ ∑ k ∈ K, (2 * r * B) * Real.exp (-(k : ℝ) / (2 * r)) :=
        sum_le_sum hterm
      _ = (2 * r * B) * ∑ k ∈ K, Real.exp (-(k : ℝ) / (2 * r)) := (mul_sum ..).symm
      _ ≤ (2 * r * B) * (1 + 2 * r) :=
        mul_le_mul_of_nonneg_left (expGeometric_sum_le K (by positivity : 0 < 2 * r))
          (by positivity)
      _ ≤ (2 * r * B) * (3 * r) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := by rw [← hr₂]; dsimp [B]; ring
  change (∑ k ∈ K, (k : ℝ) * singletonLengthGaussian n k * (τ / (k : ℝ) + s)) ≤ _
  simp_rw [mul_add]
  rw [sum_add_distrib, ← sum_mul]
  refine add_le_add hfirst ((mul_le_mul_of_nonneg_right hsecond hs).trans_eq ?_)
  ring
private theorem sqrt_mul_sqrt_sqrt_eq_rpow {n : ℕ} (hn : 0 < n) :
    Real.sqrt n * Real.sqrt (Real.sqrt n) = (n : ℝ) ^ (3 / 4 : ℝ) := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [Real.sqrt_eq_rpow (n : ℝ), Real.sqrt_eq_rpow ((n : ℝ) ^ (1 / (2 : ℝ))),
    ← Real.rpow_mul hn'.le, ← Real.rpow_add hn']
  norm_num
theorem singletonLengthGaussian_countSum_le_inv_sqrt {n : ℕ} (hn : 0 < n)
    {τ s T S : ℝ} (hτ : 0 ≤ τ) (hs : 0 ≤ s)
    (hτn : τ ≤ T / (n : ℝ) ^ (3 / 4 : ℝ)) (hsn : s ≤ S / (n : ℝ)) :
    (∑ k ∈ Icc 2 n, singletonLengthGaussian n k * (τ / (k : ℝ) + s)) ≤
      (4 * T + 2 * Real.exp 4 * S) / Real.sqrt n := by
  let r := Real.sqrt (n : ℝ)
  let q := Real.sqrt r
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hr : 0 < r := Real.sqrt_pos.mpr hn'
  have hq : 0 < q := Real.sqrt_pos.mpr hr
  have hr₂ : r ^ 2 = (n : ℝ) := Real.sq_sqrt hn'.le
  have hq₂ : q ^ 2 = r := Real.sq_sqrt hr.le
  have hq₄ : q ^ 4 = (n : ℝ) := by rw [show q ^ 4 = (q ^ 2) ^ 2 by ring, hq₂, hr₂]
  have hlog : 1 + Real.log n ≤ 4 * q := by
    rw [← hq₄, Real.log_pow]
    norm_num
    linarith only [Real.log_le_sub_one_of_pos hq]
  have hτT : τ * (r * q) ≤ T := by
    rw [show r * q = (n : ℝ) ^ (3 / 4 : ℝ) from sqrt_mul_sqrt_sqrt_eq_rpow hn]
    exact (le_div_iff₀ (Real.rpow_pos_of_pos hn' _)).mp hτn
  have hsS : s * (n : ℝ) ≤ S := (le_div_iff₀ hn').mp hsn
  have hfirst : (τ * (1 + Real.log n)) * r ≤ 4 * T := calc
    _ ≤ (τ * (4 * q)) * r :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog hτ) hr.le
    _ = 4 * (τ * (r * q)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hτT (by norm_num)
  have hsecond : (2 * Real.exp 4 * r * s) * r ≤ 2 * Real.exp 4 * S := calc
    _ = (2 * Real.exp 4) * (s * r ^ 2) := by ring
    _ ≤ _ := by
      rw [hr₂]
      exact mul_le_mul_of_nonneg_left hsS (by positivity)
  refine (singletonLengthGaussian_countSum_le hn hτ hs).trans ((le_div_iff₀ hr).mpr ?_)
  change (τ * (1 + Real.log n) + 2 * Real.exp 4 * r * s) * r ≤ _
  rw [add_mul]
  exact add_le_add hfirst hsecond
open scoped Classical in
theorem singletonLengthGaussian_longSum_le_of_budgets {n : ℕ} (hn : 0 < n) (a : ℝ)
    {τ s T S : ℝ} (hτ : 0 ≤ τ) (hs : 0 ≤ s)
    (hτn : τ ≤ T / (n : ℝ) ^ (3 / 4 : ℝ)) (hsn : s ≤ S / (n : ℝ)) :
    (∑ k ∈ (Icc 2 n).filter (fun k : ℕ ↦ a * Real.sqrt n < (k : ℝ)),
      (k : ℝ) * singletonLengthGaussian n k * (τ / (k : ℝ) + s)) ≤
      (2 * Real.exp 4 * T) / Real.sqrt (Real.sqrt n) + 6 * Real.exp 16 * Real.exp (-a) * S := by
  let r := Real.sqrt (n : ℝ)
  let q := Real.sqrt r
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hr : 0 < r := Real.sqrt_pos.mpr hn'
  have hq : 0 < q := Real.sqrt_pos.mpr hr
  have hτT : τ * r ≤ T / q := by
    rw [← (show r * q = (n : ℝ) ^ (3 / 4 : ℝ) from sqrt_mul_sqrt_sqrt_eq_rpow hn)] at hτn
    exact (le_div_iff₀ hq).mpr (by
      rw [mul_assoc]
      exact (le_div_iff₀ (mul_pos hr hq)).mp hτn)
  have hsS : s * (n : ℝ) ≤ S := (le_div_iff₀ hn').mp hsn
  refine (singletonLengthGaussian_longSum_le hn a hτ hs).trans ?_
  change 2 * Real.exp 4 * τ * r + 6 * Real.exp 16 * Real.exp (-a) * s * (n : ℝ) ≤
    (2 * Real.exp 4 * T) / q + 6 * Real.exp 16 * Real.exp (-a) * S
  rw [mul_assoc (2 * Real.exp 4) τ r, mul_div_assoc,
    mul_assoc (6 * Real.exp 16 * Real.exp (-a)) s (n : ℝ)]
  exact add_le_add (mul_le_mul_of_nonneg_left hτT (by positivity))
    (mul_le_mul_of_nonneg_left hsS (by positivity))
end AbunLP
end

-- PivotSingletonLength
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace AbunLP
end AbunLP
end

-- SingletonAnchorCounting
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal AbunLP
namespace AbunLP
variable {n : ℕ} {p : Profile n} {μ₀ : Matching n}
private abbrev SingletonAnchorPair (p : Profile n) :=
  {a : Matching n × Matching n // IsStable p a.1 ∧ IsSoleForwardExposedRotation p a.1 a.2}
private noncomputable def rotationEquivSingletonAnchorPair (hopt : IsManOptimal p μ₀) :
    Rotation p μ₀ ≃ SingletonAnchorPair p where
  toFun r :=
    ⟨((singletonRotationAnchor hopt r).val, r.val.cycle),
      (singletonRotationAnchor hopt r).property,
      (isExposedRotation_singletonRotationAnchor_iff hopt r _).mpr rfl,
      fun σ hσ ↦ (isExposedRotation_singletonRotationAnchor_iff hopt r σ).mp hσ⟩
  invFun a := rotationOfExposed hopt a.property.1 a.property.2.1
  left_inv r := by
    apply Subtype.ext
    exact (((eq_singletonRotationAnchor_iff hopt r _).mp rfl r).mpr rfl).2
  right_inv a := by
    let ν : {ν : Matching n // IsStable p ν} := ⟨a.val.1, a.property.1⟩
    let r := rotationOfExposed hopt ν.property a.property.2.1
    have hs (s : Rotation p μ₀) : s.IsExposedAt ν.val ↔ s = r := by
      constructor
      · intro he
        have hcycle := a.property.2.2 s.val.cycle he.1
        apply Subtype.ext
        change s.val = rotationLabel ν.val a.val.2
        rw [← he.2, hcycle]
      · rintro rfl
        exact ⟨a.property.2.1, rfl⟩
    have hν := (eq_singletonRotationAnchor_iff hopt r ν).mpr hs
    exact Subtype.ext (Prod.ext (congrArg Subtype.val hν.symm) rfl)
theorem rotationEquivSingletonAnchorPair_length (hopt : IsManOptimal p μ₀)
    (r : Rotation p μ₀) :
    ((rotationEquivSingletonAnchorPair hopt r).val.2.support.card) =
      r.val.cycle.support.card :=
  rfl
open scoped Classical in
theorem sum_rotation_lengthWeight_eq_sum_singletonAnchors {W : Type*} [AddCommMonoid W]
    [Fintype (Rotation p μ₀)] (hopt : IsManOptimal p μ₀) (g : ℕ → W) :
    (∑ r : Rotation p μ₀, g r.val.cycle.support.card) =
      ∑ ν : Matching n, ∑ σ : Matching n,
        if IsStable p ν ∧ IsSoleForwardExposedRotation p ν σ then g σ.support.card else 0 := by
  let f (a : Matching n × Matching n) := g a.2.support.card
  let q (a : Matching n × Matching n) :=
    IsStable p a.1 ∧ IsSoleForwardExposedRotation p a.1 a.2
  calc
    _ = ∑ a : SingletonAnchorPair p, f a.val :=
      Fintype.sum_equiv (rotationEquivSingletonAnchorPair hopt) _ _ fun _ ↦ rfl
    _ = ∑ a ∈ Finset.univ.filter q, f a :=
      (Finset.sum_subtype _ (by simp [q]) f).symm
    _ = ∑ a : Matching n × Matching n, if q a then f a else 0 :=
      Finset.sum_filter ..
    _ = _ := Fintype.sum_prod_type _
open scoped Classical in
private noncomputable def singletonAnchorLengthWeight {W : Type*} [AddCommMonoid W]
    (p : Profile n) (μ : Matching n) (g : ℕ → W) : W :=
  ∑ σ : Matching n, if IsSoleForwardExposedRotation p μ σ then g σ.support.card else 0
open scoped Classical in
private noncomputable def profileSingletonAnchorLengthWeight {W : Type*} [AddCommMonoid W]
    (p : Profile n) (g : ℕ → W) : W :=
  ∑ μ : Matching n, if IsStable p μ then singletonAnchorLengthWeight p μ g else 0
theorem sum_rotation_lengthWeight_eq_profileSingletonAnchorLengthWeight {W : Type*}
    [AddCommMonoid W] [Fintype (Rotation p μ₀)] (hopt : IsManOptimal p μ₀) (g : ℕ → W) :
    (∑ r : Rotation p μ₀, g r.val.cycle.support.card) =
      profileSingletonAnchorLengthWeight p g := by
  classical
  rw [sum_rotation_lengthWeight_eq_sum_singletonAnchors hopt]
  unfold profileSingletonAnchorLengthWeight singletonAnchorLengthWeight
  exact Finset.sum_congr rfl fun μ _ ↦ by
    by_cases hμ : IsStable p μ <;> simp [hμ]
end AbunLP
end

-- ForwardRowDeficitConcentration
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace AbunLP
end AbunLP
end

-- MarkedForwardRowDeficit
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace AbunLP
end AbunLP
end

-- SingletonDiagonalExceptions
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace AbunLP
end AbunLP
end

-- PivotSingletonMarkedLength
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace AbunLP
private noncomputable def singletonLengthBudget (n : ℕ) : ℝ :=
  3 * (n : ℝ) ^ (-3 / 4 : ℝ) + 24 / (n : ℝ)
private noncomputable def singletonLengthEnvelope (n k : ℕ) : ℝ :=
  Real.exp 5 * singletonLengthGaussian n k * (singletonLengthBudget n / (k : ℝ) + 24 / (n : ℝ))
private class LPHyp1_0 : Prop where
  bound : ∀ᶠ n : ℕ in atTop, ∀ (g : ℕ → ℝ) (B : ℝ),
      (∀ k, 0 ≤ g k) → (∀ k ∈ Finset.Icc 2 n, g k ≤ B) →
      (∫⁻ p, profileSingletonAnchorLengthWeight p (fun k ↦ ENNReal.ofReal (g k))
        ∂(uniformProfile n).toMeasure) ≤
        ENNReal.ofReal (expectedNumStableMatchings n) *
          ENNReal.ofReal (∑ k ∈ Finset.Icc 2 n, g k * singletonLengthEnvelope n k) +
          ENNReal.ofReal B * ENNReal.ofReal ((n : ℝ) ^ (-3 : ℝ))
theorem eventually_lintegral_profileSingletonAnchorLengthWeight_le_gaussian [h : LPHyp1_0] :
    ∀ᶠ n : ℕ in atTop, ∀ (g : ℕ → ℝ) (B : ℝ),
      (∀ k, 0 ≤ g k) → (∀ k ∈ Finset.Icc 2 n, g k ≤ B) →
      (∫⁻ p, profileSingletonAnchorLengthWeight p (fun k ↦ ENNReal.ofReal (g k))
        ∂(uniformProfile n).toMeasure) ≤
        ENNReal.ofReal (expectedNumStableMatchings n) *
          ENNReal.ofReal (∑ k ∈ Finset.Icc 2 n, g k * singletonLengthEnvelope n k) +
          ENNReal.ofReal B * ENNReal.ofReal ((n : ℝ) ^ (-3 : ℝ)) :=
  h.bound
theorem singletonLengthBudget_le {n : ℕ} (hn : 0 < n) :
    singletonLengthBudget n ≤ 27 / (n : ℝ) ^ (3 / 4 : ℝ) := by
  have hn₀ : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hn₁ : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hp : (n : ℝ) ^ (3 / 4 : ℝ) ≤ n := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hn₁ (show (3 / 4 : ℝ) ≤ 1 by norm_num)
  calc
    _ = 3 / (n : ℝ) ^ (3 / 4 : ℝ) + 24 / (n : ℝ) := by
      unfold singletonLengthBudget
      rw [show (-3 / 4 : ℝ) = -(3 / 4) by ring, Real.rpow_neg hn₀.le]
      simp only [div_eq_mul_inv]
    _ ≤ 3 / (n : ℝ) ^ (3 / 4 : ℝ) + 24 / (n : ℝ) ^ (3 / 4 : ℝ) :=
      add_le_add le_rfl (div_le_div_of_nonneg_left (by norm_num) (by positivity) hp)
    _ = _ := by ring
private noncomputable def singletonMomentScale : ℝ := meanUpperConstant * Real.exp 5
theorem singletonMomentScale_pos : 0 < singletonMomentScale := by
  unfold singletonMomentScale meanUpperConstant
  positivity
theorem eventually_lintegral_profileSingletonAnchorCount_le [LPHyp1_0] [LPHyp3_3] :
    ∀ᶠ n : ℕ in atTop,
      (∫⁻ p, profileSingletonAnchorLengthWeight p (fun _ ↦ (1 : ℝ≥0∞))
        ∂(uniformProfile n).toMeasure) ≤
        ENNReal.ofReal ((singletonMomentScale * (108 + 48 * Real.exp 4)) *
          Real.sqrt n * Real.log n + (n : ℝ) ^ (-3 : ℝ)) := by
  filter_upwards [eventually_lintegral_profileSingletonAnchorLengthWeight_le_gaussian,
    eventually_expectedNumStableMatchings_le_meanUpper, eventually_gt_atTop (0 : ℕ)]
    with n h hmean hn
  have hn₀ : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hl : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  let C := Real.exp 5 * (108 + 48 * Real.exp 4)
  have hsum : (∑ k ∈ Finset.Icc 2 n, singletonLengthEnvelope n k) ≤ C / Real.sqrt n := by
    have h₀ : 0 ≤ singletonLengthBudget n := by unfold singletonLengthBudget; positivity
    calc
      _ = Real.exp 5 * ∑ k ∈ Finset.Icc 2 n, singletonLengthGaussian n k *
          (singletonLengthBudget n / (k : ℝ) + 24 / (n : ℝ)) := by
        rw [Finset.mul_sum]
        simp only [singletonLengthEnvelope, mul_assoc]
      _ ≤ Real.exp 5 * ((4 * 27 + 2 * Real.exp 4 * 24) / Real.sqrt n) :=
        mul_le_mul_of_nonneg_left
          (singletonLengthGaussian_countSum_le_inv_sqrt hn h₀ (by positivity)
            (singletonLengthBudget_le hn) le_rfl) (Real.exp_pos _).le
      _ = _ := by unfold C; ring
  have h' := h (fun _ ↦ 1) 1 (fun _ ↦ zero_le_one) (fun _ _ ↦ le_rfl)
  simp only [ENNReal.ofReal_one, one_mul] at h'
  refine h'.trans ?_
  have hm₀ := mul_nonneg meanUpperConstant_nonneg (mul_nonneg hn₀.le hl)
  calc
    _ ≤ ENNReal.ofReal (meanUpperConstant * ((n : ℝ) * Real.log n)) * ENNReal.ofReal (C / Real.sqrt n) +
        ENNReal.ofReal ((n : ℝ) ^ (-3 : ℝ)) :=
      add_le_add
        (mul_le_mul' (ENNReal.ofReal_le_ofReal hmean) (ENNReal.ofReal_le_ofReal hsum)) le_rfl
    _ = _ := by
      rw [← ENNReal.ofReal_mul hm₀,
        ← ENNReal.ofReal_add (mul_nonneg hm₀ (by dsimp [C]; positivity)) (by positivity)]
      congr 1
      have hs : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt hn₀.le
      have hquot : (n : ℝ) / Real.sqrt n = Real.sqrt n :=
        (div_eq_iff (Real.sqrt_pos.mpr hn₀).ne').mpr (by simpa only [pow_two] using hs.symm)
      calc
        _ = meanUpperConstant * C * ((n : ℝ) / Real.sqrt n) * Real.log n +
            (n : ℝ) ^ (-3 : ℝ) := by ring
        _ = _ := by rw [hquot]; unfold C singletonMomentScale; ring
open scoped Classical in
theorem eventually_lintegral_profileSingletonAnchorLongLength_le [LPHyp1_0] [LPHyp3_3] :
    ∀ᶠ n : ℕ in atTop, ∀ a : ℝ,
      (∫⁻ p, profileSingletonAnchorLengthWeight p (fun k ↦
        ENNReal.ofReal (if a * Real.sqrt (n : ℝ) < (k : ℝ) then k else 0))
        ∂(uniformProfile n).toMeasure) ≤
        ENNReal.ofReal ((n : ℝ) * Real.log n) *
          ENNReal.ofReal (singletonMomentScale *
            ((54 * Real.exp 4) / Real.sqrt (Real.sqrt (n : ℝ)) +
              144 * Real.exp 16 * Real.exp (-a))) +
          ENNReal.ofReal ((n : ℝ) ^ (-2 : ℝ)) := by
  filter_upwards [eventually_lintegral_profileSingletonAnchorLengthWeight_le_gaussian,
    eventually_expectedNumStableMatchings_le_meanUpper, eventually_gt_atTop (0 : ℕ)]
    with n h hmean hn
  intro a
  let g (k : ℕ) : ℝ := if a * Real.sqrt (n : ℝ) < (k : ℝ) then k else 0
  have hg (k : ℕ) : 0 ≤ g k := by unfold g; split <;> positivity
  have hcap (k : ℕ) (hk : k ∈ Finset.Icc 2 n) : g k ≤ (n : ℝ) := by
    unfold g
    split
    · exact_mod_cast (Finset.mem_Icc.mp hk).2
    · positivity
  have h₀ : 0 ≤ singletonLengthBudget n := by unfold singletonLengthBudget; positivity
  have hsum : (∑ k ∈ Finset.Icc 2 n, g k * singletonLengthEnvelope n k) ≤
      Real.exp 5 * ((54 * Real.exp 4) / Real.sqrt (Real.sqrt (n : ℝ)) +
        144 * Real.exp 16 * Real.exp (-a)) := by
    calc
      _ = Real.exp 5 * ∑ k ∈ (Finset.Icc 2 n).filter (fun k : ℕ ↦
          a * Real.sqrt (n : ℝ) < (k : ℝ)), (k : ℝ) * singletonLengthGaussian n k *
            (singletonLengthBudget n / (k : ℝ) + 24 / (n : ℝ)) := by
        rw [Finset.sum_filter, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        by_cases hk : a * Real.sqrt (n : ℝ) < (k : ℝ)
        · simp only [g, singletonLengthEnvelope, if_pos hk]
          ring
        · simp [g, hk]
      _ ≤ Real.exp 5 * ((2 * Real.exp 4 * 27) / Real.sqrt (Real.sqrt (n : ℝ)) +
          6 * Real.exp 16 * Real.exp (-a) * 24) :=
        mul_le_mul_of_nonneg_left
          (singletonLengthGaussian_longSum_le_of_budgets hn a h₀ (by positivity)
            (singletonLengthBudget_le hn) le_rfl) (Real.exp_pos _).le
      _ = _ := by ring
  have he : ENNReal.ofReal (n : ℝ) * ENNReal.ofReal ((n : ℝ) ^ (-3 : ℝ)) =
      ENNReal.ofReal ((n : ℝ) ^ (-2 : ℝ)) := by
    rw [← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    congr 1
    calc
      _ = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-3 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add (Nat.cast_pos.mpr hn)]; norm_num
  refine (h g n hg hcap).trans ?_
  rw [he]
  refine add_le_add ((mul_le_mul' (ENNReal.ofReal_le_ofReal hmean)
    (ENNReal.ofReal_le_ofReal hsum)).trans_eq ?_) le_rfl
  simp only [singletonMomentScale, ENNReal.ofReal_mul meanUpperConstant_nonneg,
    ENNReal.ofReal_mul (Real.exp_pos 5).le,
    ENNReal.ofReal_mul (mul_nonneg meanUpperConstant_nonneg (Real.exp_pos 5).le)]
  ac_rfl
end AbunLP
end

-- RotationLengthCutoff
section
open Filter MeasureTheory Set StableMarriage
open scoped ENNReal AbunLP Topology
namespace AbunLP
private def longSingletonRotationEvent (n : ℕ) (c : ℝ) : Set (Profile n) :=
  {p | ∃ μ σ : Matching n, IsStable p μ ∧ IsSoleForwardExposedRotation p μ σ ∧
    c < (σ.support.card : ℝ)}
private def longStableExposedRotationEvent (n : ℕ) (c : ℝ) : Set (Profile n) :=
  {p | ∃ μ σ : Matching n, IsStable p μ ∧ IsExposedRotation p μ σ ∧
    c < (σ.support.card : ℝ)}
theorem measurableSet_longStableExposedRotationEvent (n : ℕ) (c : ℝ) :
    MeasurableSet (longStableExposedRotationEvent n c) :=
  MeasurableSet.of_discrete
theorem longStableExposedRotationEvent_eq_longSingletonRotationEvent (n : ℕ) (c : ℝ) :
    longStableExposedRotationEvent n c = longSingletonRotationEvent n c := by
  ext p
  constructor
  · rintro ⟨μ, σ, hμ, hσ, hc⟩
    obtain ⟨μ₀, hopt⟩ := exists_manOptimal_of_exists_stable ⟨μ, hμ⟩
    let r := rotationOfExposed hopt hμ hσ
    let a := rotationEquivSingletonAnchorPair hopt r
    refine ⟨a.val.1, a.val.2, a.property.1, a.property.2, ?_⟩
    rw [rotationEquivSingletonAnchorPair_length hopt r]
    exact hc
  · rintro ⟨μ, σ, hμ, hσ, hc⟩
    exact ⟨μ, σ, hμ, hσ.1, hc⟩
private theorem cutoff_mul_measure_longSingletonRotationEvent_le {n : ℕ} (c : ℝ) :
    ENNReal.ofReal c * (uniformProfile n).toMeasure (longSingletonRotationEvent n c) ≤
      ∫⁻ p, profileSingletonAnchorLengthWeight p
        (fun k ↦ ENNReal.ofReal (if c < (k : ℝ) then k else 0))
        ∂(uniformProfile n).toMeasure := by
  classical
  let E := longSingletonRotationEvent n c
  let g (k : ℕ) := ENNReal.ofReal (if c < (k : ℝ) then k else 0)
  have hE : MeasurableSet E := MeasurableSet.of_discrete
  change ENNReal.ofReal c * (uniformProfile n).toMeasure E ≤
    ∫⁻ p, profileSingletonAnchorLengthWeight p g ∂(uniformProfile n).toMeasure
  rw [← lintegral_indicator_const hE]
  apply lintegral_mono
  intro p
  by_cases hp : p ∈ E
  · rw [indicator_of_mem hp]
    obtain ⟨μ, σ, hμ, hσ, hc⟩ := hp
    calc
      ENNReal.ofReal c ≤ g σ.support.card := by
        simpa only [g, if_pos hc] using ENNReal.ofReal_le_ofReal hc.le
      _ ≤ singletonAnchorLengthWeight p μ g := by
        simpa only [singletonAnchorLengthWeight, if_pos hσ] using
          (Finset.single_le_sum
            (f := fun τ : Matching n ↦
              if IsSoleForwardExposedRotation p μ τ then g τ.support.card else 0)
            (fun _ _ ↦ zero_le) (Finset.mem_univ σ))
      _ ≤ profileSingletonAnchorLengthWeight p g := by
        simpa only [profileSingletonAnchorLengthWeight, if_pos hμ] using
          (Finset.single_le_sum
            (f := fun ν : Matching n ↦ if IsStable p ν then singletonAnchorLengthWeight p ν g else 0)
            (fun _ _ ↦ zero_le) (Finset.mem_univ μ))
  · rw [indicator_of_notMem hp]
    exact zero_le
private noncomputable def rotationLengthCutoff (n : ℕ) : ℝ := (n : ℝ) ^ (7 / 8 : ℝ)
private theorem real_longRotationBound_le {x D : ℝ} (hx : 1 ≤ x) (hD : 0 ≤ D) :
    (x * Real.log x * (D *
      ((54 * Real.exp 4) / Real.sqrt (Real.sqrt x) +
        144 * Real.exp 16 * Real.exp (-(x ^ (3 / 8 : ℝ))))) + x ^ (-2 : ℝ)) /
      (x ^ (7 / 8 : ℝ)) ≤
    (D * (54 * Real.exp 4 + 144 * Real.exp 16)) *
      (Real.log x / x ^ (1 / 8 : ℝ)) + x ^ (-2 : ℝ) := by
  have hx' : 0 < x := zero_lt_one.trans_le hx
  have hsqrt : Real.sqrt (Real.sqrt x) = x ^ (1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx'.le]
    norm_num
  have hexp : Real.exp (-(x ^ (3 / 8 : ℝ))) ≤ 1 / x ^ (1 / 4 : ℝ) := by
    have hxpow : x ^ (1 / 4 : ℝ) ≤ x ^ (3 / 8 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
    have hle : x ^ (1 / 4 : ℝ) ≤ Real.exp (x ^ (3 / 8 : ℝ)) :=
      hxpow.trans ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _))
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by positivity) hle
  have hpowers : x ^ (1 / 4 : ℝ) * x ^ (7 / 8 : ℝ) = x * x ^ (1 / 8 : ℝ) := by
    calc
      _ = x ^ (1 / 4 + 7 / 8 : ℝ) := (Real.rpow_add hx' _ _).symm
      _ = x ^ (1 + 1 / 8 : ℝ) := by norm_num
      _ = _ := by rw [Real.rpow_add hx', Real.rpow_one]
  have hden : 1 ≤ x ^ (7 / 8 : ℝ) := Real.one_le_rpow hx (by norm_num)
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  rw [add_div]
  refine add_le_add ?_ ?_
  · calc
      _ ≤ (x * Real.log x * (D *
          ((54 * Real.exp 4) / x ^ (1 / 4 : ℝ) +
            144 * Real.exp 16 * (1 / x ^ (1 / 4 : ℝ))))) /
          x ^ (7 / 8 : ℝ) := by
        rw [hsqrt]
        gcongr
      _ = _ := by
        have heq :
            54 * Real.exp 4 / x ^ (1 / 4 : ℝ) +
                144 * Real.exp 16 * (1 / x ^ (1 / 4 : ℝ)) =
              (54 * Real.exp 4 + 144 * Real.exp 16) / x ^ (1 / 4 : ℝ) := by ring
        rw [heq, ← mul_div_assoc, ← mul_div_assoc, div_div, hpowers]
        field_simp
  · exact (div_le_iff₀ (by positivity)).mpr
      (le_mul_of_one_le_right (by positivity) hden)
theorem tendsto_measure_longStableExposedRotationEvent [LPHyp1_0] [LPHyp3_3] :
    Tendsto (fun n ↦ (uniformProfile n).toMeasure
      (longStableExposedRotationEvent n (rotationLengthCutoff n))) atTop (𝓝 0) := by
  let C := singletonMomentScale * (54 * Real.exp 4 + 144 * Real.exp 16)
  have hlog : Tendsto (fun n : ℕ ↦ Real.log n / (n : ℝ) ^ (1 / 8 : ℝ)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8)).tendsto_div_nhds_zero.comp
      tendsto_natCast_atTop_atTop
  have hsmall : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (-2 : ℝ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2)).comp tendsto_natCast_atTop_atTop
  have hupper : Tendsto (fun n : ℕ ↦ ENNReal.ofReal
      (C * (Real.log n / (n : ℝ) ^ (1 / 8 : ℝ)) + (n : ℝ) ^ (-2 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero, ENNReal.ofReal_zero, Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        ((tendsto_const_nhds.mul hlog).add hsmall)
  refine tendsto_const_nhds.squeeze' hupper (Eventually.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [eventually_lintegral_profileSingletonAnchorLongLength_le,
    eventually_ge_atTop (1 : ℕ)] with n hn hn₁
  have hn₁' : (1 : ℝ) ≤ n := by exact_mod_cast hn₁
  have hnpos : 0 < (n : ℝ) := zero_lt_one.trans_le hn₁'
  let a := (n : ℝ) ^ (3 / 8 : ℝ)
  let c := rotationLengthCutoff n
  have hc : 0 < c := Real.rpow_pos_of_pos hnpos _
  have heq : a * Real.sqrt (n : ℝ) = c := by
    dsimp [a, c, rotationLengthCutoff]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hnpos]
    norm_num
  have hweighted := hn a
  rw [heq] at hweighted
  have hm := (cutoff_mul_measure_longSingletonRotationEvent_le (n := n) c).trans hweighted
  rw [mul_comm] at hm
  have hnl : 0 ≤ (n : ℝ) * Real.log n := mul_nonneg (by positivity) (Real.log_nonneg hn₁')
  rw [longStableExposedRotationEvent_eq_longSingletonRotationEvent]
  refine (ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_ne_zero_iff.mpr hc))
    (Or.inl ENNReal.ofReal_ne_top)).mpr hm |>.trans ?_
  rw [← ENNReal.ofReal_mul hnl, ← ENNReal.ofReal_add
    (mul_nonneg hnl (mul_nonneg singletonMomentScale_pos.le (by positivity))) (by positivity),
    ← ENNReal.ofReal_div_of_pos hc]
  exact ENNReal.ofReal_le_ofReal (real_longRotationBound_le hn₁' singletonMomentScale_pos.le)
theorem tendsto_measure_score_longStableExposedRotationEvent [LPHyp1_0] [LPHyp3_3] :
    Tendsto (fun n ↦ continuousScoreLaw n
      (profileOfScores ⁻¹' longStableExposedRotationEvent n (rotationLengthCutoff n)))
      atTop (𝓝 0) := by
  convert tendsto_measure_longStableExposedRotationEvent using 1
  funext n
  rw [← (measurePreserving_profileOfScores n).map_eq,
    Measure.map_apply (measurePreserving_profileOfScores n).measurable
      (measurableSet_longStableExposedRotationEvent n _)]
end AbunLP
end

-- RotationClockBand
section
open Filter MeasureTheory StableMarriage
open scoped ENNReal Topology
namespace AbunLP
private noncomputable def rotationStepRelativeCap (n : ℕ) : ℝ :=
  rotationLengthCutoff n * (12 * Real.log n / n)
theorem tendsto_rotationStepRelativeCap :
    Tendsto rotationStepRelativeCap atTop (𝓝 0) := by
  have ho := isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8)
  have h := (ho.tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul 12
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  change 12 * (Real.log (n : ℝ) / (n : ℝ) ^ (1 / 8 : ℝ)) =
    (n : ℝ) ^ (7 / 8 : ℝ) * (12 * Real.log (n : ℝ) / (n : ℝ))
  rw [show (7 / 8 : ℝ) = 1 - 1 / 8 by norm_num, Real.rpow_sub hn', Real.rpow_one]
  field_simp
theorem tendsto_measure_badRotationStepGeometry_zero [LPHyp1_0] [LPHyp2_1] [LPHyp3_3] :
    Tendsto (fun n ↦ continuousScoreLaw n
      ((goodCoexposureScores n)ᶜ ∪
        profileOfScores ⁻¹' longStableExposedRotationEvent n (rotationLengthCutoff n)))
      atTop (𝓝 0) := by
  have hgood := tendsto_measure_badCoexposureScores_zero_of_mean_upper
    meanUpperConstant_nonneg eventually_expectedNumStableMatchings_le_meanUpper
  have h := hgood.add tendsto_measure_score_longStableExposedRotationEvent
  rw [add_zero] at h
  exact tendsto_const_nhds.squeeze' h (Eventually.of_forall fun _ ↦ zero_le)
    (Eventually.of_forall fun _ ↦ measure_union_le _ _)
theorem femaleSpouseTotal_drop_le_rotationStepRelativeCap {n : ℕ} {x : ScoreProfile n}
    (hx : x ∈ goodCoexposureScores n)
    (hlen : profileOfScores x ∉ longStableExposedRotationEvent n (rotationLengthCutoff n))
    {μ : Matching n} (hμ : IsStable (profileOfScores x) μ)
    {ρ : Equiv.Perm (Fin n)} (hρ : IsExposedRotation (profileOfScores x) μ ρ) :
    femaleSpouseTotal x μ - femaleSpouseTotal x (eliminateRotation μ ρ) ≤
      rotationStepRelativeCap n * femaleSpouseTotal x μ := by
  have hs := hx.2.2 μ hμ
  have hY : 0 < femaleSpouseTotal x μ := by linarith only [hs.1]
  have hn : 0 < n := by
    by_contra! hn
    obtain rfl := Nat.eq_zero_of_le_zero hn
    simp [femaleSpouseTotal] at hY
  have hcap : (ρ.support.card : ℝ) ≤ rotationLengthCutoff n :=
    le_of_not_gt fun h ↦ hlen ⟨μ, ρ, hμ, hρ, h⟩
  have hshare : 0 ≤ 12 * Real.log (n : ℝ) / (n : ℝ) := by
    have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    positivity
  exact (femaleSpouseTotal_drop_le_support_mul_share x μ ρ hY hs.2.1
    (fun _ ↦ (hx.2.1 _ _).1.le)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcap hshare) hY.le)
theorem lower_of_relative_drop_at_crossing {old new threshold cap : ℝ}
    (hbefore : threshold ≤ old) (hcap : cap ≤ 1) (hdrop : old - new ≤ cap * old) :
    (1 - cap) * threshold ≤ new := by
  calc
    _ ≤ (1 - cap) * old := mul_le_mul_of_nonneg_left hbefore (sub_nonneg.mpr hcap)
    _ = old - cap * old := by ring
    _ ≤ new := by linarith only [hdrop]
theorem rotationParticipation_ge_of_pivot_band {n : ℕ} (hn : 0 < n)
    (x : ScoreProfile n) (μ ν : Matching n) (rs : List (Equiv.Perm (Fin n)))
    (hμ : HasFemaleLogGeometry x μ) (hν : HasFemaleLogGeometry x ν)
    (hstart : (n : ℝ) ^ (2 / 5 : ℝ) / 2 ≤ femaleSpouseTotal x μ)
    (hfinish : femaleSpouseTotal x ν ≤ (n : ℝ) ^ (1 / 5 : ℝ))
    (hYν : 0 < femaleSpouseTotal x ν) {E : ℝ}
    (hclock : |femaleLogPotential x ν - femaleLogPotential x μ -
      (rotationParticipation rs : ℝ)| ≤ E) :
    (n : ℝ) * (Real.log n / 5 - Real.log 2 - 6) - E ≤ (rotationParticipation rs : ℝ) := by
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hstart' : 0 < (n : ℝ) ^ (2 / 5 : ℝ) / 2 := by positivity
  have hYμ : 0 < femaleSpouseTotal x μ := hstart'.trans_le hstart
  have hlog : Real.log n / 5 - Real.log 2 ≤
      Real.log (femaleSpouseTotal x μ / femaleSpouseTotal x ν) := by
    have hstartLog := Real.strictMonoOn_log.monotoneOn hstart' hYμ hstart
    have hfinishLog :=
      Real.strictMonoOn_log.monotoneOn hYν (Real.rpow_pos_of_pos hn' _) hfinish
    rw [Real.log_div (Real.rpow_pos_of_pos hn' _).ne' (by norm_num),
      Real.log_rpow hn'] at hstartLog
    rw [Real.log_rpow hn'] at hfinishLog
    rw [Real.log_div hYμ.ne' hYν.ne']
    linarith only [hstartLog, hfinishLog]
  calc
    _ = (n : ℝ) * (Real.log n / 5 - Real.log 2) - 6 * n - E := by ring
    _ ≤ (n : ℝ) * Real.log (femaleSpouseTotal x μ / femaleSpouseTotal x ν) - 6 * n - E :=
      sub_le_sub_right (sub_le_sub_right (mul_le_mul_of_nonneg_left hlog hn'.le) _) _
    _ ≤ _ := rotationParticipation_ge_log_drop x μ ν rs hμ hν hYμ hYν hclock
end AbunLP
end

-- ScoreRotationHistory
section
open StableMarriage
open scoped Classical
namespace AbunLP
variable {n : ℕ}
private theorem scoreRotationWalk_eq_nil_of_acyclic (x : ScoreProfile n) (μ : Matching n)
    (h : chooseQueriedRotation (scoreRotationGraph x μ) = none) (k : ℕ) :
    scoreRotationWalk x k μ = ([], μ) := by
  cases k with
  | zero => rfl
  | succ k => rw [scoreRotationWalk, h]
theorem scoreRotationWalk_add (x : ScoreProfile n) (j k : ℕ) (ν : Matching n) :
    scoreRotationWalk x (j + k) ν =
      let a := scoreRotationWalk x j ν
      let b := scoreRotationWalk x k a.2
      (a.1 ++ b.1, b.2) := by
  induction j generalizing ν with
  | zero => simp only [Nat.zero_add, scoreRotationWalk, List.nil_append, Prod.eta]
  | succ j ih =>
    rw [Nat.succ_add, scoreRotationWalk, scoreRotationWalk]
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
end AbunLP
end

-- ScoreRotationBandCrossing
section
open StableMarriage
open scoped BigOperators
namespace AbunLP
variable {n : ℕ}
private noncomputable def scoreWalkMatching (x : ScoreProfile n) (k : ℕ) : Matching n :=
  (scoreRotationWalk x k (DAState.matching (profileOfScores x))).2
private noncomputable def scoreWalkFemaleTotal (x : ScoreProfile n) (k : ℕ) : ℝ :=
  femaleSpouseTotal x (scoreWalkMatching x k)
private noncomputable def scoreWalkSegmentRotations (x : ScoreProfile n) (a b : ℕ) :
    List (Equiv.Perm (Fin n)) :=
  (scoreRotationWalk x (b - a) (scoreWalkMatching x a)).1
theorem scoreWalkMatching_stable {x : ScoreProfile n}
    (hx : ∀ j, Function.Injective (x (.inr j))) (k : ℕ) :
    IsStable (profileOfScores x) (scoreWalkMatching x k) := by
  have hstart := (DAState.isManOptimal_matching (profileOfScores x)).1
  exact (scoreRotationWalk_legal x hx k hstart).isStable_end
theorem scoreWalkSegmentRotations_legal {x : ScoreProfile n}
    (hx : ∀ j, Function.Injective (x (.inr j))) {a b : ℕ} (hab : a ≤ b) :
    RotationSequence (profileOfScores x) (scoreWalkMatching x a)
      (scoreWalkSegmentRotations x a b) (scoreWalkMatching x b) := by
  have h := congrArg Prod.snd
    (scoreRotationWalk_add x a (b - a) (DAState.matching (profileOfScores x)))
  rw [Nat.add_sub_of_le hab] at h
  change scoreWalkMatching x b = (scoreRotationWalk x (b - a) (scoreWalkMatching x a)).2 at h
  rw [h]
  exact scoreRotationWalk_legal x hx _ (scoreWalkMatching_stable hx a)
theorem scoreWalkMatching_succ (x : ScoreProfile n) (k : ℕ) :
    scoreWalkMatching x (k + 1) =
      match chooseQueriedRotation (scoreRotationGraph x (scoreWalkMatching x k)) with
      | none => scoreWalkMatching x k
      | some ρ => eliminateRotation (scoreWalkMatching x k) ρ := by
  have h := congrArg Prod.snd
    (scoreRotationWalk_add x k 1 (DAState.matching (profileOfScores x)))
  change scoreWalkMatching x (k + 1) = (scoreRotationWalk x 1 (scoreWalkMatching x k)).2 at h
  rw [h, scoreRotationWalk]
  cases chooseQueriedRotation (scoreRotationGraph x (scoreWalkMatching x k)) <;> rfl
theorem antitone_scoreWalkFemaleTotal {x : ScoreProfile n}
    (hx : ∀ j, Function.Injective (x (.inr j))) :
    Antitone (scoreWalkFemaleTotal x) := by
  apply antitone_nat_of_succ_le
  intro k
  unfold scoreWalkFemaleTotal
  rw [scoreWalkMatching_succ]
  cases h : chooseQueriedRotation (scoreRotationGraph x (scoreWalkMatching x k)) with
  | none => rfl
  | some ρ =>
    have hρ :=
      (realizesDirectedCycle_queriedSuccessorGraph_scores_iff x hx (scoreWalkMatching x k) ρ).mp
        (realizesDirectedCycle_of_chooseQueriedRotation h)
    exact femaleSpouseTotal_eliminate_le x hρ hx
theorem scoreWalkFemaleTotal_step_drop {x : ScoreProfile n} (hn : 0 < n)
    (hx : x ∈ goodCoexposureScores n)
    (hlen : profileOfScores x ∉ longStableExposedRotationEvent n (rotationLengthCutoff n))
    (k : ℕ) :
    scoreWalkFemaleTotal x k - scoreWalkFemaleTotal x (k + 1) ≤
      rotationStepRelativeCap n * scoreWalkFemaleTotal x k := by
  have ht : ∀ j, Function.Injective (x (.inr j)) := fun j ↦ hx.1 (.inr j)
  have hs := scoreWalkMatching_stable ht k
  unfold scoreWalkFemaleTotal
  rw [scoreWalkMatching_succ]
  cases h : chooseQueriedRotation (scoreRotationGraph x (scoreWalkMatching x k)) with
  | none =>
    change femaleSpouseTotal x (scoreWalkMatching x k) -
        femaleSpouseTotal x (scoreWalkMatching x k) ≤ _
    rw [sub_self]
    apply mul_nonneg _ (zero_le_two.trans (hx.2.2 _ hs).1)
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    unfold rotationStepRelativeCap rotationLengthCutoff
    positivity
  | some ρ =>
    have hρ :=
      (realizesDirectedCycle_queriedSuccessorGraph_scores_iff x ht (scoreWalkMatching x k) ρ).mp
        (realizesDirectedCycle_of_chooseQueriedRotation h)
    exact femaleSpouseTotal_drop_le_rotationStepRelativeCap hx hlen hs hρ
theorem scoreWalkClock_sub (x : ScoreProfile n) {a b : ℕ} (hab : a ≤ b) :
    scoreWalkClock x b - scoreWalkClock x a =
      femaleLogPotential x (scoreWalkMatching x b) - femaleLogPotential x (scoreWalkMatching x a) -
        (rotationParticipation (scoreWalkSegmentRotations x a b) : ℝ) := by
  let μ := DAState.matching (profileOfScores x)
  have h := scoreRotationWalk_add x a (b - a) μ
  rw [Nat.add_sub_of_le hab] at h
  have hp : (rotationParticipation (scoreRotationWalk x b μ).1 : ℝ) =
      (rotationParticipation (scoreRotationWalk x a μ).1 : ℝ) +
        (rotationParticipation (scoreWalkSegmentRotations x a b) : ℝ) := by
    rw [h]
    simp [rotationParticipation, scoreWalkSegmentRotations, scoreWalkMatching, μ]
  change (femaleLogPotential x (scoreWalkMatching x b) - femaleLogPotential x μ -
      (rotationParticipation (scoreRotationWalk x b μ).1 : ℝ)) -
      (femaleLogPotential x (scoreWalkMatching x a) - femaleLogPotential x μ -
        (rotationParticipation (scoreRotationWalk x a μ).1 : ℝ)) = _
  rw [hp]
  ring
private theorem first_score_crossing {Y : ℕ → ℝ} {N : ℕ} {u c : ℝ}
    (hstart : u < Y 0) (hfinish : Y N ≤ u) (hcap : c ≤ 1)
    (hstep : ∀ t, Y t - Y (t + 1) ≤ c * Y t) :
    ∃ t ≤ N, (∀ j < t, u < Y j) ∧ (1 - c) * u ≤ Y t ∧ Y t ≤ u := by
  have hex : ∃ t, Y t ≤ u := ⟨N, hfinish⟩
  let t := Nat.find hex
  have hsmall : ∀ j < t, u < Y j := fun j hj ↦ lt_of_not_ge (Nat.find_min hex hj)
  have ht : t ≤ N := Nat.find_min' hex hfinish
  have htop : Y t ≤ u := Nat.find_spec hex
  have ht' : t ≠ 0 := fun he ↦ (not_le_of_gt hstart) (he ▸ htop)
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero ht'
  have hk' : k < t := by omega
  refine ⟨t, ht, hsmall, ?_, htop⟩
  rw [hk]
  exact lower_of_relative_drop_at_crossing (hsmall k hk').le hcap (hstep k)
theorem exists_scoreWalk_pivot_band_segment {x : ScoreProfile n} {N : ℕ} {E : ℝ}
    (hn : 0 < n) (hx : x ∈ goodCoexposureScores n) (hgeom : x ∈ goodFemaleLogGeometry n)
    (hlen : profileOfScores x ∉ longStableExposedRotationEvent n (rotationLengthCutoff n))
    (hcap : rotationStepRelativeCap n ≤ 1 / 2)
    (hsep : (n : ℝ) ^ (1 / 5 : ℝ) < (n : ℝ) ^ (2 / 5 : ℝ) / 2)
    (hstart : (n : ℝ) ^ (2 / 5 : ℝ) < scoreWalkFemaleTotal x 0)
    (hfinish : scoreWalkFemaleTotal x N ≤ (n : ℝ) ^ (1 / 5 : ℝ))
    (hclock : ∀ t ≤ N, |scoreWalkClock x t| ≤ E) :
    ∃ a b, a < b ∧ b ≤ N ∧
      (∀ t, a ≤ t → t < b → scoreWalkFemaleTotal x t ∈
        Set.Ioc ((n : ℝ) ^ (1 / 5 : ℝ)) ((n : ℝ) ^ (2 / 5 : ℝ))) ∧
      (1 - rotationStepRelativeCap n) * (n : ℝ) ^ (2 / 5 : ℝ) ≤ scoreWalkFemaleTotal x a ∧
      (1 - rotationStepRelativeCap n) * (n : ℝ) ^ (1 / 5 : ℝ) ≤ scoreWalkFemaleTotal x b ∧
      scoreWalkFemaleTotal x b ≤ (n : ℝ) ^ (1 / 5 : ℝ) ∧
      RotationSequence (profileOfScores x) (scoreWalkMatching x a)
        (scoreWalkSegmentRotations x a b) (scoreWalkMatching x b) ∧
      (n : ℝ) * (Real.log n / 5 - Real.log 2 - 6) - 2 * E ≤
        (rotationParticipation (scoreWalkSegmentRotations x a b) : ℝ) := by
  let Y := scoreWalkFemaleTotal x
  let U := (n : ℝ) ^ (2 / 5 : ℝ)
  let L := (n : ℝ) ^ (1 / 5 : ℝ)
  let c := rotationStepRelativeCap n
  have ht : ∀ j, Function.Injective (x (.inr j)) := fun j ↦ hx.1 (.inr j)
  have hY : Antitone Y := antitone_scoreWalkFemaleTotal ht
  have hc : c ≤ 1 := hcap.trans (by norm_num)
  have hU : 0 ≤ U := by unfold U; positivity
  have hLU : L < U := hsep.trans_le (by change U / 2 ≤ U; linarith)
  have hstep := scoreWalkFemaleTotal_step_drop hn hx hlen
  obtain ⟨a, haN, _, ha, hau⟩ := first_score_crossing hstart
    (hfinish.trans hLU.le) hc hstep
  obtain ⟨b, hbN, hbefore, hb, hbl⟩ := first_score_crossing (hLU.trans hstart) hfinish hc hstep
  have ha' : U / 2 ≤ Y a := calc
    U / 2 = (1 / 2) * U := by ring
    _ ≤ (1 - c) * U := mul_le_mul_of_nonneg_right (by
      change (1 / 2 : ℝ) ≤ 1 - rotationStepRelativeCap n
      linarith only [hcap]) hU
    _ ≤ Y a := ha
  have hab : a < b := by
    by_contra! hba
    exact (not_le_of_gt (hsep.trans_le ha')) ((hY hba).trans hbl)
  have hsa := scoreWalkMatching_stable ht a
  have hsb := scoreWalkMatching_stable ht b
  have hseg := scoreWalkSegmentRotations_legal ht hab.le
  refine ⟨a, b, hab, hbN, fun t hat htb ↦ ⟨hbefore t htb, (hY hat).trans hau⟩,
    ha, hb, hbl, hseg, ?_⟩
  have herr : |scoreWalkClock x b - scoreWalkClock x a| ≤ 2 * E := calc
    _ ≤ |scoreWalkClock x b| + |scoreWalkClock x a| := abs_sub _ _
    _ ≤ 2 * E := by linarith only [hclock a haN, hclock b hbN]
  rw [scoreWalkClock_sub x hab.le] at herr
  exact rotationParticipation_ge_of_pivot_band hn x _ _ _ (hgeom _ hsa) (hgeom _ hsb)
    ha' hbl (lt_of_lt_of_le (by norm_num) (hx.2.2 _ hsb).1) herr
theorem RotationSequence.rotationLabels_nodup {p : Profile n} {μ ν : Matching n}
    {rs : List (Equiv.Perm (Fin n))} (h : RotationSequence p μ rs ν) :
    (rotationLabels μ rs).Nodup := by
  induction h with
  | nil => exact List.nodup_nil
  | @cons μ ν ρ rs _ hρ htail ih =>
    rw [rotationLabels, List.nodup_cons]
    refine ⟨?_, ih⟩
    intro hmem
    obtain ⟨m, hm, _⟩ := (IsExposedRotation.isCycle hρ)
    obtain ⟨old, _, hold, _, hstart, _, _⟩ := htail.label_rank_bounds hmem
      (show (rotationLabel μ ρ).cycle m ≠ m from hm)
    have hold' : μ m = old := by simpa [rotationLabel, hm] using hold
    rw [← hold'] at hstart
    exact (not_le_of_gt (hρ.manRank_lt_eliminate_of_moved hm)) hstart
private theorem rotationLabels_map_lengthWeight {W : Type*} (g : ℕ → W)
    (μ : Matching n) (rs : List (Equiv.Perm (Fin n))) :
    (rotationLabels μ rs).map (fun r ↦ g r.cycle.support.card) =
      rs.map (fun σ ↦ g σ.support.card) := by
  induction rs generalizing μ with
  | nil => rfl
  | cons σ rs ih =>
    simp only [rotationLabels, List.map_cons, rotationLabel, ih]
theorem RotationSequence.lengthWeight_le_profileSingletonAnchorLengthWeight
    {p : Profile n} {μ₀ μ ν : Matching n} {rs ss : List (Equiv.Perm (Fin n))}
    (hopt : IsManOptimal p μ₀) (hprefix : RotationSequence p μ₀ ss μ)
    (hseg : RotationSequence p μ rs ν) (g : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k) :
    (rs.map (fun σ ↦ g σ.support.card)).sum ≤ profileSingletonAnchorLengthWeight p g := by
  classical
  let : Fintype (RotationLabel n) := Fintype.ofFinite _
  let : Fintype (Rotation p μ₀) := Fintype.ofFinite _
  let f (r : RotationLabel n) : ℝ := g r.cycle.support.card
  let P (r : RotationLabel n) : Prop :=
    ∃ ν' rs', RotationSequence p μ₀ rs' ν' ∧ r ∈ rotationLabels μ₀ rs'
  let V := Finset.univ.filter P
  have hsub : (rotationLabels μ rs).toFinset ⊆ V := by
    intro r hr
    have hr' := List.mem_toFinset.mp hr
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ν, ss ++ rs, hprefix.append hseg,
      by rw [hprefix.rotationLabels_append]; exact List.mem_append_right _ hr'⟩
  calc
    _ = ((rotationLabels μ rs).map f).sum := by rw [rotationLabels_map_lengthWeight]
    _ = ∑ r ∈ (rotationLabels μ rs).toFinset, f r :=
      (List.sum_toFinset f hseg.rotationLabels_nodup).symm
    _ ≤ ∑ r ∈ V, f r := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun r _ _ ↦ hg _)
    _ = ∑ r : Rotation p μ₀, g r.val.cycle.support.card :=
      Finset.sum_subtype (p := P) V (by intro r; simp [V]) f
    _ = _ := sum_rotation_lengthWeight_eq_profileSingletonAnchorLengthWeight hopt g
private noncomputable def shortRotationLengthWeight (K : ℝ) (k : ℕ) : ℝ :=
  if (k : ℝ) < K then k else 0
private noncomputable def longRotationLengthWeight (A : ℝ) (k : ℕ) : ℝ :=
  if A < (k : ℝ) then k else 0
open scoped Classical in
private noncomputable def middleRotationCount (K A : ℝ) (rs : List (Equiv.Perm (Fin n))) : ℕ :=
  rs.countP (fun ρ ↦ decide (K ≤ (ρ.support.card : ℝ) ∧ (ρ.support.card : ℝ) ≤ A))
theorem rotationParticipation_le_lengthWeights_add_middleCount (K A : ℝ)
    (rs : List (Equiv.Perm (Fin n))) :
    (rotationParticipation rs : ℝ) ≤
      (rs.map (fun ρ ↦ shortRotationLengthWeight K ρ.support.card)).sum +
        (rs.map (fun ρ ↦ longRotationLengthWeight A ρ.support.card)).sum +
        A * (middleRotationCount K A rs : ℝ) := by
  classical
  induction rs with
  | nil => simp [rotationParticipation, middleRotationCount]
  | cons ρ rs ih =>
    let l : ℝ := ρ.support.card
    have h₁ : 0 ≤ shortRotationLengthWeight K ρ.support.card := by
      unfold shortRotationLengthWeight
      split <;> positivity
    have h₂ : 0 ≤ longRotationLengthWeight A ρ.support.card := by
      unfold longRotationLengthWeight
      split <;> positivity
    have hhead : l ≤ shortRotationLengthWeight K ρ.support.card +
        longRotationLengthWeight A ρ.support.card + (if K ≤ l ∧ l ≤ A then A else 0) := by
      by_cases hK : l < K
      · rw [if_neg (fun h ↦ hK.not_ge h.1)]
        have hs : shortRotationLengthWeight K ρ.support.card = l := if_pos hK
        linarith only [h₂, hs]
      · by_cases hA : A < l
        · rw [if_neg (fun h ↦ hA.not_ge h.2)]
          have hl : longRotationLengthWeight A ρ.support.card = l := if_pos hA
          linarith only [h₁, hl]
        · rw [if_pos ⟨le_of_not_gt hK, le_of_not_gt hA⟩]
          linarith only [h₁, h₂, le_of_not_gt hA]
    have hpart : (rotationParticipation (ρ :: rs) : ℝ) =
        l + (rotationParticipation rs : ℝ) := by
      simp [l, rotationParticipation]
    rw [hpart]
    simp [middleRotationCount] at ih
    by_cases hm : K ≤ l ∧ l ≤ A
    · simp [middleRotationCount, l, hm, Nat.cast_add, mul_add] at hhead ⊢
      linarith only [ih, hhead]
    · simp [middleRotationCount, l, hm] at hhead ⊢
      linarith only [ih, hhead]
theorem exists_scoreWalk_pivot_band_middle_count {x : ScoreProfile n} {N : ℕ} {E : ℝ}
    (hn : 0 < n) (hx : x ∈ goodCoexposureScores n) (hgeom : x ∈ goodFemaleLogGeometry n)
    (hlen : profileOfScores x ∉ longStableExposedRotationEvent n (rotationLengthCutoff n))
    (hcap : rotationStepRelativeCap n ≤ 1 / 2)
    (hsep : (n : ℝ) ^ (1 / 5 : ℝ) < (n : ℝ) ^ (2 / 5 : ℝ) / 2)
    (hstart : (n : ℝ) ^ (2 / 5 : ℝ) < scoreWalkFemaleTotal x 0)
    (hfinish : scoreWalkFemaleTotal x N ≤ (n : ℝ) ^ (1 / 5 : ℝ))
    (hclock : ∀ t ≤ N, |scoreWalkClock x t| ≤ E) (K A : ℝ) :
    ∃ a b, a < b ∧ b ≤ N ∧
      (∀ t, a ≤ t → t < b → scoreWalkFemaleTotal x t ∈
        Set.Ioc ((n : ℝ) ^ (1 / 5 : ℝ)) ((n : ℝ) ^ (2 / 5 : ℝ))) ∧
      RotationSequence (profileOfScores x) (scoreWalkMatching x a)
        (scoreWalkSegmentRotations x a b) (scoreWalkMatching x b) ∧
      (n : ℝ) * (Real.log n / 5 - Real.log 2 - 6) - 2 * E -
        profileSingletonAnchorLengthWeight (profileOfScores x) (shortRotationLengthWeight K) -
        profileSingletonAnchorLengthWeight (profileOfScores x) (longRotationLengthWeight A) ≤
        A * (middleRotationCount K A (scoreWalkSegmentRotations x a b) : ℝ) := by
  obtain ⟨a, b, hab, hbN, hband, _, _, _, hseg, hpart⟩ :=
    exists_scoreWalk_pivot_band_segment hn hx hgeom hlen hcap hsep hstart hfinish hclock
  let p := profileOfScores x
  have hopt := DAState.isManOptimal_matching p
  have hprefix := scoreRotationWalk_legal x (fun j ↦ hx.1 (.inr j)) a hopt.1
  have hs := RotationSequence.lengthWeight_le_profileSingletonAnchorLengthWeight hopt hprefix hseg
    (shortRotationLengthWeight K) (fun k ↦ by
      unfold shortRotationLengthWeight
      split <;> positivity)
  have hl := RotationSequence.lengthWeight_le_profileSingletonAnchorLengthWeight hopt hprefix hseg
    (longRotationLengthWeight A) (fun k ↦ by
      unfold longRotationLengthWeight
      split <;> positivity)
  have hmid := rotationParticipation_le_lengthWeights_add_middleCount K A
    (scoreWalkSegmentRotations x a b)
  exact ⟨a, b, hab, hbN, hband, hseg, by linarith only [hpart, hmid, hs, hl]⟩
private theorem rotationLabels_scoreRotationWalk_checkpoint (x : ScoreProfile n) (k : ℕ)
    {μ : Matching n} {r : RotationLabel n}
    (hr : r ∈ rotationLabels μ (scoreRotationWalk x k μ).1) :
    ∃ t < k, let ν := (scoreRotationWalk x t μ).2
      chooseQueriedRotation (scoreRotationGraph x ν) = some r.cycle ∧
        rotationLabel ν r.cycle = r := by
  induction k generalizing μ with
  | zero => simp [scoreRotationWalk, rotationLabels] at hr
  | succ k ih =>
    cases hρ : chooseQueriedRotation (scoreRotationGraph x μ) with
    | none => simp [scoreRotationWalk, hρ, rotationLabels] at hr
    | some ρ =>
      simp only [scoreRotationWalk, hρ, rotationLabels, List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact ⟨0, Nat.zero_lt_succ k, hρ, rfl⟩
      · obtain ⟨t, ht, hw⟩ := ih hr
        exact ⟨t + 1, Nat.succ_lt_succ ht, by simpa only [scoreRotationWalk, hρ] using hw⟩
theorem exists_scoreWalkSegment_middle_realizedRotations {x : ScoreProfile n}
    (hx : ∀ j, Function.Injective (x (.inr j))) {a b : ℕ} (hab : a ≤ b) (K A : ℝ) :
    ∃ S : Finset (Rotation (profileOfScores x) (DAState.matching (profileOfScores x))),
      S.card = middleRotationCount K A (scoreWalkSegmentRotations x a b) ∧
      ∀ r ∈ S, K ≤ (r.val.cycle.support.card : ℝ) ∧
        (r.val.cycle.support.card : ℝ) ≤ A ∧
          ∃ t, a ≤ t ∧ t < b ∧ r.IsExposedAt (scoreWalkMatching x t) := by
  classical
  let p := profileOfScores x
  let μ₀ := DAState.matching p
  let rs := scoreWalkSegmentRotations x a b
  let ss := (scoreRotationWalk x a μ₀).1
  let labels := rotationLabels (scoreWalkMatching x a) rs
  let middle (r : RotationLabel n) : Bool := decide
    (K ≤ (r.cycle.support.card : ℝ) ∧ (r.cycle.support.card : ℝ) ≤ A)
  let T := (labels.filter middle).toFinset
  let P (r : RotationLabel n) : Prop :=
    ∃ ν rs', RotationSequence p μ₀ rs' ν ∧ r ∈ rotationLabels μ₀ rs'
  have hprefix := scoreRotationWalk_legal x hx a (DAState.isManOptimal_matching p).1
  have hseg := scoreWalkSegmentRotations_legal hx hab
  have hsub : ∀ r ∈ T, P r := by
    intro r hr
    have hr' := (List.mem_filter.mp (List.mem_toFinset.mp hr)).1
    refine ⟨scoreWalkMatching x b, ss ++ rs, hprefix.append hseg, ?_⟩
    rw [hprefix.rotationLabels_append]
    exact List.mem_append_right _ hr'
  let S : Finset (Rotation p μ₀) := T.subtype P
  have hmap := rotationLabels_map_lengthWeight (fun k : ℕ ↦ k) (scoreWalkMatching x a) rs
  have hcnt : labels.countP middle = middleRotationCount K A rs := by
    let goodLength (k : ℕ) : Bool := decide (K ≤ (k : ℝ) ∧ (k : ℝ) ≤ A)
    have h := congrArg (List.countP goodLength) hmap
    simpa only [List.countP_map, Function.comp_def, labels, middle, middleRotationCount,
      goodLength] using h
  have hc : S.card = middleRotationCount K A rs := by
    change (T.subtype P).card = _
    rw [Finset.card_subtype, Finset.filter_eq_self.mpr hsub]
    change (labels.filter middle).toFinset.card = _
    rw [List.toFinset_card_of_nodup (hseg.rotationLabels_nodup.filter _)]
    rw [← List.countP_eq_length_filter]
    exact hcnt
  refine ⟨S, hc, ?_⟩
  intro r hr
  have hr' : r.val ∈ T := Finset.mem_subtype.mp hr
  have hr'' := List.mem_filter.mp (List.mem_toFinset.mp hr')
  have hlength : K ≤ (r.val.cycle.support.card : ℝ) ∧
      (r.val.cycle.support.card : ℝ) ≤ A := decide_eq_true_eq.mp hr''.2
  obtain ⟨t, ht, hchoose, hlabel⟩ := rotationLabels_scoreRotationWalk_checkpoint
    x (b - a) (μ := scoreWalkMatching x a) hr''.1
  have heq := congrArg Prod.snd (scoreRotationWalk_add x a t μ₀)
  change scoreWalkMatching x (a + t) = (scoreRotationWalk x t (scoreWalkMatching x a)).2 at heq
  rw [← heq] at hchoose hlabel
  have hρ := (realizesDirectedCycle_queriedSuccessorGraph_scores_iff x hx
    (scoreWalkMatching x (a + t)) r.val.cycle).mp
      (realizesDirectedCycle_of_chooseQueriedRotation hchoose)
  exact ⟨hlength.1, hlength.2, a + t, by omega, by omega, hρ, hlabel⟩
end AbunLP
end

-- DAUpperEndpoint
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace AbunLP
end AbunLP
end

-- ParticipationClockMartingale
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal
namespace AbunLP
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {ℱ : Filtration ℕ mΩ} {M : ℕ → Ω → ℝ}
end AbunLP
end

-- FinitePartitionClock
section
open MeasureTheory Set
open scoped Function
namespace AbunLP
variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι]
end AbunLP
end

-- ScoreClockFiltration
section
open MeasureTheory Set StableMarriage
open scoped BigOperators
namespace AbunLP
variable {n : ℕ}
end AbunLP
end

-- ScoreRotationBranchTest
section
open MeasureTheory Set StableMarriage
open scoped Classical
namespace AbunLP
variable {n : ℕ}
end AbunLP
end

-- ScoreRotationClockBudget
section
open MeasureTheory Set StableMarriage
open scoped BigOperators Classical Function
namespace AbunLP
variable {n : ℕ}
end AbunLP
end

-- ScoreRotationClockMaximal
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators Classical ENNReal Topology
namespace AbunLP
variable {n : ℕ}
private class LPHyp3_0 : Prop where
  bound : ∀ {ε : ℝ} (hε : 0 < ε),
    Tendsto (fun n : ℕ ↦ continuousScoreLaw n
      {x | ∃ k ≤ n * (n - 1), ε * (n * Real.log n) ≤ |scoreWalkClock x k|})
      atTop (𝓝 0)
theorem tendsto_measure_scoreWalkClock_large [h : LPHyp3_0] {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ ↦ continuousScoreLaw n
      {x | ∃ k ≤ n * (n - 1), ε * (n * Real.log n) ≤ |scoreWalkClock x k|})
      atTop (𝓝 0) :=
  h.bound hε
end AbunLP
end

-- ScoreRotationLengthBudgets
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators Classical ENNReal Topology
namespace AbunLP
private theorem ofReal_profileSingletonAnchorLengthWeight {n : ℕ} (p : Profile n)
    (g : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k) :
    ENNReal.ofReal (profileSingletonAnchorLengthWeight p g) =
      profileSingletonAnchorLengthWeight p (fun k ↦ ENNReal.ofReal (g k)) := by
  unfold profileSingletonAnchorLengthWeight singletonAnchorLengthWeight
  rw [ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro μ _
    by_cases hμ : IsStable p μ
    · simp only [hμ, ite_true]
      rw [ENNReal.ofReal_sum_of_nonneg]
      · apply Finset.sum_congr rfl
        intro σ _
        split <;> simp
      · intro σ _
        split
        · exact hg _
        · exact le_rfl
    · simp [hμ]
  · intro μ _
    split
    · exact Finset.sum_nonneg fun σ _ ↦ by
        split
        · exact hg _
        · exact le_rfl
    · exact le_rfl
private theorem measure_score_lengthWeight_tail_le {n : ℕ} (g : ℕ → ℝ)
    (hg : ∀ k, 0 ≤ g k) {t b : ℝ} (ht : 0 < t)
    (hm : (∫⁻ p, profileSingletonAnchorLengthWeight p (fun k ↦ ENNReal.ofReal (g k))
      ∂(uniformProfile n).toMeasure) ≤ ENNReal.ofReal b) :
    continuousScoreLaw n {x | t < profileSingletonAnchorLengthWeight (profileOfScores x) g}
      ≤ ENNReal.ofReal (b / t) := by
  let E : Set (Profile n) := {p | t < profileSingletonAnchorLengthWeight p g}
  let f (p : Profile n) := profileSingletonAnchorLengthWeight p (fun k ↦ ENNReal.ofReal (g k))
  let μ := (uniformProfile n).toMeasure
  change continuousScoreLaw n (profileOfScores ⁻¹' E) ≤ _
  rw [← Measure.map_apply (measurePreserving_profileOfScores n).measurable
    (show MeasurableSet E from MeasurableSet.of_discrete),
    (measurePreserving_profileOfScores n).map_eq]
  change μ E ≤ _
  have hsub : E ⊆ {p | ENNReal.ofReal t ≤ f p} := by
    intro p hp
    change ENNReal.ofReal t ≤ f p
    exact (ENNReal.ofReal_le_ofReal (le_of_lt hp)).trans_eq
      (ofReal_profileSingletonAnchorLengthWeight p g hg)
  have hmarkov : ENNReal.ofReal t * μ E ≤ ENNReal.ofReal b :=
    (mul_le_mul_right (measure_mono hsub) (ENNReal.ofReal t)).trans
      ((mul_meas_ge_le_lintegral (μ := μ) (f := f) Measurable.of_discrete _).trans hm)
  rw [ENNReal.ofReal_div_of_pos ht]
  exact (ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_ne_zero_iff.mpr ht))
    (Or.inl ENNReal.ofReal_ne_top)).mpr (by simpa only [mul_comm] using hmarkov)
private theorem eventually_log_size_ge_one :
    ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (n : ℝ) :=
  (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 1
private theorem tendsto_size_quarter_neg :
    Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (-(1 / 4) : ℝ)) atTop (𝓝 0) :=
  (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp tendsto_natCast_atTop_atTop
theorem exists_eventually_measure_longRotationLengthBudget_bad [LPHyp1_0] [LPHyp3_3] {ε η : ℝ}
    (hε : 0 < ε) (hη : 0 < η) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ᶠ n : ℕ in atTop,
      continuousScoreLaw n {x | ε * ((n : ℝ) * Real.log n) <
        profileSingletonAnchorLengthWeight (profileOfScores x)
          (longRotationLengthWeight (A * Real.sqrt n))} ≤ ENNReal.ofReal η := by
  let C₁ := singletonMomentScale * (54 * Real.exp 4)
  let C₂ := singletonMomentScale * (144 * Real.exp 16)
  let δ := ε * η / 3
  have hδ : 0 < δ := by positivity
  have hA_lim : Tendsto (fun A : ℝ ↦ C₂ * Real.exp (-A)) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul Real.tendsto_exp_neg_atTop_nhds_zero
  have hA_ev : ∀ᶠ A : ℝ in atTop, 1 ≤ A ∧ C₂ * Real.exp (-A) ≤ δ :=
    (eventually_ge_atTop (1 : ℝ)).and (hA_lim.eventually_le_const hδ)
  obtain ⟨A, hA, hA_tail⟩ := hA_ev.exists
  refine ⟨A, hA, ?_⟩
  have hsize_lim :
      Tendsto (fun n : ℕ ↦ C₁ * (n : ℝ) ^ (-(1 / 4) : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul tendsto_size_quarter_neg
  have hrem_lim : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (-2 : ℝ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_lintegral_profileSingletonAnchorLongLength_le,
    hsize_lim.eventually_le_const hδ, hrem_lim.eventually_le_const hδ,
    eventually_ge_atTop (1 : ℕ), eventually_log_size_ge_one]
    with n hm hs hr hn hlog
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn₀ : 0 < (n : ℝ) := zero_lt_one.trans_le hn₁
  let b := (n : ℝ) * Real.log n
  have hb₁ : 1 ≤ b := by dsimp [b]; nlinarith
  have hb : 0 < b := zero_lt_one.trans_le hb₁
  have hsqrt : Real.sqrt (Real.sqrt (n : ℝ)) = (n : ℝ) ^ (1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hn₀.le]
    norm_num
  have hc : singletonMomentScale * ((54 * Real.exp 4) / Real.sqrt (Real.sqrt (n : ℝ)) +
        144 * Real.exp 16 * Real.exp (-A)) ≤ 2 * δ := by
    rw [hsqrt]
    have hsplit : singletonMomentScale * ((54 * Real.exp 4) / ((n : ℝ) ^ (1 / 4 : ℝ)) +
        144 * Real.exp 16 * Real.exp (-A)) =
        C₁ * (n : ℝ) ^ (-(1 / 4) : ℝ) + C₂ * Real.exp (-A) := by
      rw [Real.rpow_neg hn₀.le]
      dsimp [C₁, C₂]
      ring
    rw [hsplit]
    linarith
  let g := longRotationLengthWeight (A * Real.sqrt (n : ℝ))
  have hg (k : ℕ) : 0 ≤ g k := by dsimp [g, longRotationLengthWeight]; split <;> positivity
  apply (measure_score_lengthWeight_tail_le g hg (b := b * (ε * η)) (mul_pos hε hb) ?_).trans
  · apply ENNReal.ofReal_le_ofReal
    exact (div_le_iff₀ (mul_pos hε hb)).mpr (by ring_nf; exact le_rfl)
  · refine (hm A).trans ?_
    have hscale := singletonMomentScale_pos
    rw [← ENNReal.ofReal_mul hb.le, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ b * (2 * δ) + δ := add_le_add (mul_le_mul_of_nonneg_left hc hb.le) hr
      _ ≤ b * (2 * δ) + b * δ :=
        add_le_add le_rfl (le_mul_of_one_le_left hδ.le hb₁)
      _ = _ := by dsimp [δ]; ring
private theorem profileSingletonAnchorLengthWeight_le_mul_count {n : ℕ} (p : Profile n)
    (g : ℕ → ℝ≥0∞) (K : ℝ≥0∞) (hg : ∀ k, g k ≤ K) :
    profileSingletonAnchorLengthWeight p g ≤
      K * profileSingletonAnchorLengthWeight p (fun _ ↦ (1 : ℝ≥0∞)) := by
  unfold profileSingletonAnchorLengthWeight singletonAnchorLengthWeight
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro μ _
  by_cases hμ : IsStable p μ
  · simp only [hμ, ite_true, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro σ _
    by_cases hσ : IsSoleForwardExposedRotation p μ σ
    · simpa only [hσ, ite_true, mul_one] using hg σ.support.card
    · simp [hσ]
  · simp [hμ]
theorem exists_eventually_measure_shortRotationLengthBudget_bad [LPHyp1_0] [LPHyp3_3] {ε η : ℝ}
    (hε : 0 < ε) (hη : 0 < η) :
    ∃ b : ℝ, 0 < b ∧ b ≤ 1 ∧ ∀ᶠ n : ℕ in atTop,
      continuousScoreLaw n {x | ε * ((n : ℝ) * Real.log n) <
        profileSingletonAnchorLengthWeight (profileOfScores x)
          (shortRotationLengthWeight (b * Real.sqrt n))} ≤ ENNReal.ofReal η := by
  let C := singletonMomentScale * (108 + 48 * Real.exp 4)
  have hC : 0 < C + 1 := by
    have hscale := singletonMomentScale_pos
    dsimp [C]
    positivity
  let b := min 1 (ε * η / (C + 1))
  have hb : 0 < b := lt_min zero_lt_one (div_pos (mul_pos hε hη) hC)
  have hbudget : b * (C + 1) ≤ ε * η := (le_div_iff₀ hC).mp (min_le_right _ _)
  refine ⟨b, hb, min_le_left _ _, ?_⟩
  filter_upwards [eventually_lintegral_profileSingletonAnchorCount_le,
    eventually_ge_atTop (1 : ℕ), eventually_log_size_ge_one] with n hm hn hlog
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn₀ : 0 < (n : ℝ) := zero_lt_one.trans_le hn₁
  let L := (n : ℝ) * Real.log n
  have hL : 0 < L := mul_pos hn₀ (zero_lt_one.trans_le hlog)
  let K := b * Real.sqrt (n : ℝ)
  let g := shortRotationLengthWeight K
  have hK : 0 < K := mul_pos hb (Real.sqrt_pos_of_pos hn₀)
  have hg (k : ℕ) : 0 ≤ g k := by dsimp [g, shortRotationLengthWeight]; split <;> positivity
  have hle (k : ℕ) : ENNReal.ofReal (g k) ≤ ENNReal.ofReal K := by
    apply ENNReal.ofReal_le_ofReal
    dsimp [g, shortRotationLengthWeight]
    split
    · exact le_of_lt ‹_›
    · exact hK.le
  let f (p : Profile n) := profileSingletonAnchorLengthWeight p (fun _ ↦ (1 : ℝ≥0∞))
  have hcount : (∫⁻ p, f p ∂(uniformProfile n).toMeasure) ≤
      ENNReal.ofReal ((C + 1) * Real.sqrt n * Real.log n) := by
    refine hm.trans (ENNReal.ofReal_le_ofReal ?_)
    have hsmall : (n : ℝ) ^ (-3 : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hn₁ (by norm_num)
    have hbase : 1 ≤ Real.sqrt (n : ℝ) * Real.log n :=
      one_le_mul_of_one_le_of_one_le (Real.one_le_sqrt.mpr hn₁) hlog
    change C * Real.sqrt n * Real.log n + _ ≤ _
    nlinarith only [hsmall, hbase]
  have hmoment : (∫⁻ p, profileSingletonAnchorLengthWeight p (fun k ↦ ENNReal.ofReal (g k))
        ∂(uniformProfile n).toMeasure) ≤ ENNReal.ofReal (L * (ε * η)) := by
    calc
      _ ≤ ∫⁻ p, ENNReal.ofReal K * f p ∂(uniformProfile n).toMeasure :=
        lintegral_mono fun p ↦ profileSingletonAnchorLengthWeight_le_mul_count p _ _ hle
      _ = ENNReal.ofReal K * (∫⁻ p, f p ∂(uniformProfile n).toMeasure) :=
        lintegral_const_mul _ Measurable.of_discrete
      _ ≤ ENNReal.ofReal K * ENNReal.ofReal ((C + 1) * Real.sqrt n * Real.log n) :=
        mul_le_mul_right hcount _
      _ = ENNReal.ofReal (L * (b * (C + 1))) := by
        rw [← ENNReal.ofReal_mul hK.le]
        congr 1
        have hs := Real.sq_sqrt hn₀.le
        dsimp [K, L]
        calc
          _ = b * (C + 1) * (Real.sqrt n)^2 * Real.log n := by ring
          _ = _ := by rw [hs]; ring
      _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hbudget hL.le)
  apply (measure_score_lengthWeight_tail_le g hg (mul_pos hε hL) hmoment).trans
  apply ENNReal.ofReal_le_ofReal
  exact (div_le_iff₀ (mul_pos hε hL)).mpr (by ring_nf; exact le_rfl)
end AbunLP
end

-- ScoreRotationBandAbundance
section
open Filter MeasureTheory Set StableMarriage
open scoped ENNReal Topology
namespace AbunLP
private def scoreWalkBandEndpoints (n : ℕ) : Set (ScoreProfile n) :=
  {x | (n : ℝ) ^ (2 / 5 : ℝ) < scoreWalkFemaleTotal x 0 ∧
    scoreWalkFemaleTotal x (n * (n - 1)) ≤ (n : ℝ) ^ (1 / 5 : ℝ)}
private def scoreWalkBandAbundanceAtCutoffs (n : ℕ) (K A : ℝ) : Set (ScoreProfile n) :=
  {x | ∃ S : Finset (Rotation (profileOfScores x) (DAState.matching (profileOfScores x))),
    Real.sqrt n * Real.log n / (10 * A) ≤ (S.card : ℝ) ∧
    ∀ r ∈ S, K ≤ (r.val.cycle.support.card : ℝ) ∧
      (r.val.cycle.support.card : ℝ) ≤ A * Real.sqrt n ∧
      ∃ t < n * (n - 1), r.IsExposedAt (scoreWalkMatching x t) ∧
        scoreWalkFemaleTotal x t ∈ Ioc ((n : ℝ) ^ (1 / 5 : ℝ)) ((n : ℝ) ^ (2 / 5 : ℝ))}
private theorem scoreWalkBandAbundanceAtCutoffs_of_budgets {n : ℕ} (hn : 0 < n)
    {x : ScoreProfile n} {K A : ℝ} (hA : 1 ≤ A) (hx : x ∈ goodCoexposureScores n)
    (hgeom : x ∈ goodFemaleLogGeometry n)
    (hlen : profileOfScores x ∉ longStableExposedRotationEvent n (rotationLengthCutoff n))
    (hcap : rotationStepRelativeCap n ≤ 1 / 2)
    (hsep : (n : ℝ) ^ (1 / 5 : ℝ) < (n : ℝ) ^ (2 / 5 : ℝ) / 2)
    (hlog : Real.log 2 + 6 ≤ Real.log n / 25)
    (hend : x ∈ scoreWalkBandEndpoints n)
    (hclock : ∀ t ≤ n * (n - 1), |scoreWalkClock x t| ≤ (1 / 100 : ℝ) * (n * Real.log n))
    (hshort : profileSingletonAnchorLengthWeight (profileOfScores x)
      (shortRotationLengthWeight K) ≤ (1 / 50 : ℝ) * (n * Real.log n))
    (hlong : profileSingletonAnchorLengthWeight (profileOfScores x)
      (longRotationLengthWeight (A * Real.sqrt n)) ≤ (1 / 50 : ℝ) * (n * Real.log n)) :
    x ∈ scoreWalkBandAbundanceAtCutoffs n K A := by
  let L := A * Real.sqrt n
  obtain ⟨a, b, hab, hbN, hband, -, hmid⟩ :=
    exists_scoreWalk_pivot_band_middle_count hn hx hgeom hlen hcap hsep hend.1 hend.2 hclock K L
  obtain ⟨S, hScard, hS⟩ := exists_scoreWalkSegment_middle_realizedRotations
    (fun j ↦ hx.1 (.inr j)) hab.le K L
  rw [← hScard] at hmid
  have hn₀ : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hA₀ : 0 < A := zero_lt_one.trans_le hA
  have hL : 0 < L := mul_pos hA₀ (Real.sqrt_pos.mpr hn₀)
  have h10 : (n : ℝ) * Real.log n / 10 ≤ L * (S.card : ℝ) := by
    have hlog' := mul_le_mul_of_nonneg_left hlog hn₀.le
    linarith only [hlog', hshort, hlong, hmid]
  refine ⟨S, (mul_le_mul_iff_right₀ hL).mp ?_, ?_⟩
  · calc
      L * (Real.sqrt n * Real.log n / (10 * A)) =
          (Real.sqrt n)^2 * Real.log n / 10 := by
        dsimp [L]
        field_simp [hA₀.ne']
      _ = _ := by rw [Real.sq_sqrt hn₀.le]
      _ ≤ _ := h10
  · intro r hr
    obtain ⟨hrlo, hrhi, t, hat, htb, hex⟩ := hS r hr
    exact ⟨hrlo, hrhi, t, htb.trans_le hbN, hex, hband t hat htb⟩
private class LPHyp3_2 : Prop where
  bound : Tendsto (fun n ↦ continuousScoreLaw n (goodFemaleLogGeometry n)ᶜ) atTop (𝓝 0)
private theorem tendsto_measure_badFemaleLogGeometry_zero [h : LPHyp3_2] :
    Tendsto (fun n ↦ continuousScoreLaw n (goodFemaleLogGeometry n)ᶜ) atTop (𝓝 0) :=
  h.bound
private theorem eventually_pivotBand_separated :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (1 / 5 : ℝ) < (n : ℝ) ^ (2 / 5 : ℝ) / 2 := by
  have hpow := (tendsto_rpow_atTop (by norm_num : 0 < (1 / 5 : ℝ))).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hpow.eventually_gt_atTop 2, eventually_gt_atTop (0 : ℕ)] with n hn hn₀
  have hnr : 0 < (n : ℝ) := Nat.cast_pos.mpr hn₀
  have hsq : ((n : ℝ) ^ (1 / 5 : ℝ))^2 = (n : ℝ) ^ (2 / 5 : ℝ) := by
    rw [pow_two, ← Real.rpow_add hnr]
    norm_num
  rw [← hsq]
  change 2 < (n : ℝ) ^ (1 / 5 : ℝ) at hn
  nlinarith
theorem eventually_measure_scoreWalkBandEndpoints_diff_abundanceAtCutoffs_le [LPHyp1_0] [LPHyp2_1] [LPHyp3_0] [LPHyp3_2] [LPHyp3_3]
    (K : ℕ → ℝ) {A : ℝ} (hA : 1 ≤ A) {δ ηs ηl : ℝ}
    (hδ : 0 < δ) (hηs : 0 ≤ ηs) (hηl : 0 ≤ ηl)
    (hshort : ∀ᶠ n : ℕ in atTop, continuousScoreLaw n
      {x | (1 / 50 : ℝ) * (n * Real.log n) < profileSingletonAnchorLengthWeight
        (profileOfScores x) (shortRotationLengthWeight (K n))} ≤ ENNReal.ofReal ηs)
    (hlong : ∀ᶠ n : ℕ in atTop, continuousScoreLaw n
      {x | (1 / 50 : ℝ) * (n * Real.log n) < profileSingletonAnchorLengthWeight
        (profileOfScores x) (longRotationLengthWeight (A * Real.sqrt n))} ≤ ENNReal.ofReal ηl) :
    ∀ᶠ n : ℕ in atTop, continuousScoreLaw n
      (scoreWalkBandEndpoints n \ scoreWalkBandAbundanceAtCutoffs n (K n) A) ≤
      ENNReal.ofReal (δ + ηs + ηl) := by
  let B₁ (n : ℕ) := (goodCoexposureScores n)ᶜ ∪
    profileOfScores ⁻¹' longStableExposedRotationEvent n (rotationLengthCutoff n)
  let B₂ (n : ℕ) := (goodFemaleLogGeometry n)ᶜ
  let B₃ (n : ℕ) : Set (ScoreProfile n) :=
    {x | ∃ k ≤ n * (n - 1), (1 / 100 : ℝ) * (n * Real.log n) ≤ |scoreWalkClock x k|}
  let B₄ (n : ℕ) : Set (ScoreProfile n) :=
    {x | (1 / 50 : ℝ) * (n * Real.log n) < profileSingletonAnchorLengthWeight (profileOfScores x)
      (shortRotationLengthWeight (K n))}
  let B₅ (n : ℕ) : Set (ScoreProfile n) :=
    {x | (1 / 50 : ℝ) * (n * Real.log n) < profileSingletonAnchorLengthWeight (profileOfScores x)
      (longRotationLengthWeight (A * Real.sqrt n))}
  let small (n : ℕ) := (continuousScoreLaw n (B₁ n) + continuousScoreLaw n (B₂ n)) +
    continuousScoreLaw n (B₃ n)
  have hs : Tendsto small atTop (𝓝 0) := by
    simpa only [add_zero] using
      (tendsto_measure_badRotationStepGeometry_zero.add
        tendsto_measure_badFemaleLogGeometry_zero).add
        (tendsto_measure_scoreWalkClock_large (ε := 1 / 100) (by norm_num))
  have hcap := tendsto_rotationStepRelativeCap.eventually_lt_const
    (by norm_num : (0 : ℝ) < 1 / 2)
  have hlog := (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop (25 * (Real.log 2 + 6))
  have hδ₀ : 0 < ENNReal.ofReal δ := ENNReal.ofReal_pos.mpr hδ
  filter_upwards [hs.eventually_lt_const hδ₀, hshort, hlong, hcap, hlog,
    eventually_pivotBand_separated, eventually_gt_atTop (0 : ℕ)]
    with n hsmall hshort hlong hcap hlog hsep hn
  change 25 * (Real.log 2 + 6) ≤ Real.log (n : ℝ) at hlog
  have hsub : scoreWalkBandEndpoints n \ scoreWalkBandAbundanceAtCutoffs n (K n) A ⊆
      (((B₁ n ∪ B₂ n) ∪ B₃ n) ∪ B₄ n) ∪ B₅ n := by
    intro x hx
    by_contra! h
    have hnone :
        (x ∉ B₁ n ∧ x ∉ B₂ n) ∧ x ∉ B₃ n ∧ x ∉ B₄ n ∧ x ∉ B₅ n := by
      simp only [mem_union, not_or] at h
      tauto
    have hgood : x ∈ goodCoexposureScores n := by
      by_contra! hbad
      exact hnone.1.1 (Or.inl hbad)
    have hlen : profileOfScores x ∉ longStableExposedRotationEvent n (rotationLengthCutoff n) :=
      fun hbad ↦ hnone.1.1 (Or.inr hbad)
    have hgeom : x ∈ goodFemaleLogGeometry n := by
      by_contra! hbad
      exact hnone.1.2 hbad
    apply hx.2
    exact scoreWalkBandAbundanceAtCutoffs_of_budgets hn hA hgood hgeom hlen hcap.le hsep
      (by linarith only [hlog]) hx.1
      (fun t ht ↦ (lt_of_not_ge (fun hb ↦ hnone.2.1 ⟨t, ht, hb⟩)).le)
      (le_of_not_gt hnone.2.2.1) (le_of_not_gt hnone.2.2.2)
  calc
    _ ≤ continuousScoreLaw n ((((B₁ n ∪ B₂ n) ∪ B₃ n) ∪ B₄ n) ∪ B₅ n) :=
      measure_mono hsub
    _ ≤ small n + continuousScoreLaw n (B₄ n) + continuousScoreLaw n (B₅ n) :=
      (measure_union_le _ _).trans (add_le_add
        ((measure_union_le _ _).trans (add_le_add
          ((measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)) le_rfl))
        le_rfl)
    _ ≤ ENNReal.ofReal δ + ENNReal.ofReal ηs + ENNReal.ofReal ηl :=
      add_le_add (add_le_add hsmall.le hshort) hlong
    _ = _ := by
      rw [← ENNReal.ofReal_add hδ.le hηs, ← ENNReal.ofReal_add (by positivity) hηl]
theorem exists_eventually_measure_scoreWalkBandEndpoints_diff_sqrtAbundance_le [LPHyp1_0] [LPHyp2_1] [LPHyp3_0] [LPHyp3_2] [LPHyp3_3] {η : ℝ}
    (hη : 0 < η) :
    ∃ b A : ℝ, 0 < b ∧ b ≤ 1 ∧ 1 ≤ A ∧ ∀ᶠ n : ℕ in atTop,
      continuousScoreLaw n
        (scoreWalkBandEndpoints n \ scoreWalkBandAbundanceAtCutoffs n (b * Real.sqrt n) A) ≤
        ENNReal.ofReal η := by
  obtain ⟨b, hb, hb₁, hshort⟩ := exists_eventually_measure_shortRotationLengthBudget_bad
    (ε := 1 / 50) (η := η / 3) (by norm_num) (by positivity)
  obtain ⟨A, hA, hlong⟩ := exists_eventually_measure_longRotationLengthBudget_bad
    (ε := 1 / 50) (η := η / 3) (by norm_num) (by positivity)
  have hh := eventually_measure_scoreWalkBandEndpoints_diff_abundanceAtCutoffs_le
    (fun n ↦ b * Real.sqrt n) hA
    (δ := η / 3) (ηs := η / 3) (ηl := η / 3) (by positivity) (by positivity) (by positivity)
    hshort hlong
  rw [show η / 3 + η / 3 + η / 3 = η by ring] at hh
  exact ⟨b, A, hb, hb₁, hA, hh⟩
end AbunLP
end

-- ScoreRotationAnchorAbundance
section
open Filter MeasureTheory Set StableMarriage
open scoped ENNReal Topology
namespace AbunLP
theorem singletonRotationAnchor_injective {n : ℕ} {p : Profile n} {μ₀ : Matching n}
    (hopt : IsManOptimal p μ₀) : Function.Injective (singletonRotationAnchor hopt) := by
  intro r s he
  have hr := ((eq_singletonRotationAnchor_iff hopt r _).mp rfl r).mpr rfl
  have hs : r.IsExposedAt (singletonRotationAnchor hopt s).val :=
    (congrArg Subtype.val he) ▸ hr
  exact ((eq_singletonRotationAnchor_iff hopt s _).mp rfl r).mp hs
private def scoreWalkAnchorAbundanceAtCutoffs (n : ℕ) (K A : ℝ) : Set (ScoreProfile n) :=
  {x | ∃ S : Finset (Rotation (profileOfScores x) (DAState.matching (profileOfScores x))),
    Real.sqrt n * Real.log n / (10 * A) ≤ (S.card : ℝ) ∧
    ∀ r ∈ S, K ≤ (r.val.cycle.support.card : ℝ) ∧
      (r.val.cycle.support.card : ℝ) ≤ A * Real.sqrt n ∧
      femaleSpouseTotal x (singletonRotationAnchor
        (DAState.isManOptimal_matching (profileOfScores x)) r).val ∈
        Icc ((n : ℝ) ^ (1 / 10 : ℝ)) ((n : ℝ) ^ (2 / 5 : ℝ))}
private theorem eventually_anchorShareScale :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (1 / 10 : ℝ) ≤
      ((n : ℝ) ^ (1 / 5 : ℝ) * (n : ℝ) ^ (-21 / 20 : ℝ)) /
        (12 * Real.log (n : ℝ) / n) := by
  have ho := isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 20)
  have ht := (ho.tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul 12
  rw [mul_zero] at ht
  filter_upwards [ht.eventually_lt_const zero_lt_one, eventually_gt_atTop (1 : ℕ)] with n h hn
  have hn₁ : (1 : ℝ) < n := by exact_mod_cast hn
  have hn₀ : 0 < (n : ℝ) := zero_lt_one.trans hn₁
  have hlog := Real.log_pos hn₁
  have hb : 0 < 12 * Real.log (n : ℝ) / n := by positivity
  change 12 * (Real.log (n : ℝ) / (n : ℝ) ^ (1 / 20 : ℝ)) < 1 at h
  rw [← mul_div_assoc] at h
  have hle : 12 * Real.log (n : ℝ) ≤ (n : ℝ) ^ (1 / 20 : ℝ) := by
    simpa only [one_mul] using
      ((div_lt_iff₀ (Real.rpow_pos_of_pos hn₀ (1 / 20))).mp h).le
  apply (le_div_iff₀ hb).mpr
  calc
    _ ≤ (n : ℝ) ^ (1 / 10 : ℝ) * ((n : ℝ) ^ (1 / 20 : ℝ) / n) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hle hn₀.le) (by positivity)
    _ = (n : ℝ) ^ (-17 / 20 : ℝ) := by
      have hf := Real.rpow_sub hn₀ (1 / 10 + 1 / 20) 1
      rw [Real.rpow_one] at hf
      rw [← mul_div_assoc, ← Real.rpow_add hn₀, ← hf]
      norm_num
    _ = _ := by rw [← Real.rpow_add hn₀]; norm_num
theorem eventually_scoreWalkAnchorAbundance_of_bandAbundance
    (K : ℕ → ℝ) (hK : ∀ᶠ n in atTop, 81 ≤ K n) :
    ∀ᶠ n : ℕ in atTop, ∀ {x : ScoreProfile n} {A : ℝ},
      x ∈ goodCoexposureScores n → x ∈ scoreWalkBandAbundanceAtCutoffs n (K n) A →
      (∀ μ : Matching n, IsStable (profileOfScores x) μ → ∀ ρ : Equiv.Perm (Fin n),
        IsExposedRotation (profileOfScores x) μ ρ → 81 ≤ ρ.support.card →
        ∃ m ∈ ρ.support, (n : ℝ) ^ (-21 / 20 : ℝ) ≤
          femaleSpouseScore x μ (μ m) / femaleSpouseTotal x μ) →
      x ∈ scoreWalkAnchorAbundanceAtCutoffs n (K n) A := by
  filter_upwards [eventually_anchorShareScale, hK, eventually_gt_atTop (1 : ℕ)]
    with n hscale hK hn
  intro x A hgood hband hnon
  let p := profileOfScores x
  let hopt := DAState.isManOptimal_matching p
  obtain ⟨S, hS, hcuts⟩ := hband
  refine ⟨S, hS, ?_⟩
  intro r hr
  obtain ⟨hk, hmax, t, -, hex, hY⟩ := hcuts r hr
  let μ := scoreWalkMatching x t
  let ν := (singletonRotationAnchor hopt r).val
  have hμ := scoreWalkMatching_stable (fun j ↦ hgood.1 (.inr j)) t
  have hν := (singletonRotationAnchor hopt r).property
  have hlarge : 81 ≤ r.val.cycle.support.card := by exact_mod_cast (hK.trans hk)
  obtain ⟨m, hm, hlo⟩ := hnon μ hμ r.val.cycle hex.1 hlarge
  have hgoodμ := hgood.2.2 μ hμ
  have hgoodν := hgood.2.2 ν hν
  have hμ₀ : 0 < femaleSpouseTotal x μ := by linarith only [hgoodμ.1]
  have hν₀ : 0 < femaleSpouseTotal x ν := by linarith only [hgoodν.1]
  have hn₁ : (1 : ℝ) < n := by exact_mod_cast hn
  have hb : 0 < 12 * Real.log (n : ℝ) / n := by
    have h := Real.log_pos hn₁
    positivity
  have hbound := hex.singletonAnchor_femaleSpouseTotal_bounds_of_shares
    hgood.1 hopt hμ (Equiv.Perm.mem_support.mp hm) hb hμ₀ hν₀ hlo (hgoodν.2.1 (μ m))
  have hYlo : (n : ℝ) ^ (1 / 5 : ℝ) ≤ femaleSpouseTotal x μ := hY.1.le
  have hYhi : femaleSpouseTotal x μ ≤ (n : ℝ) ^ (2 / 5 : ℝ) := hY.2
  exact ⟨hk, hmax, hscale.trans ((div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hYlo (by positivity)) hb.le).trans hbound.1),
    hbound.2.trans hYhi⟩
end AbunLP
end

-- ScoreRotationNonTiny
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators Classical ENNReal Topology
namespace AbunLP
private noncomputable def nonTinyRotationShare (n : ℕ) : ℝ := (n : ℝ) ^ (-(21 / 20) : ℝ)
private theorem cycle_has_injective_segment {n k : ℕ} {σ : Equiv.Perm (Fin n)}
    (hσ : σ.IsCycle) (hk : k + 1 ≤ σ.support.card) :
    ∃ a : Fin (k + 1) → Fin n, Function.Injective a ∧
      (∀ i, a i ∈ σ.support) ∧ ∀ t : Fin k, σ (a t.castSucc) = a t.succ := by
  have hc : σ.IsCycleOn (↑σ.support : Set (Fin n)) := by
    simpa only [Equiv.Perm.coe_support_eq_set_support] using hσ.isCycleOn
  obtain ⟨i, hi, -⟩ := hσ
  have hi' := Equiv.Perm.mem_support.mpr hi
  let a (t : Fin (k + 1)) := (σ ^ t.val) i
  refine ⟨a, ?_, fun j ↦ Equiv.Perm.pow_apply_mem_support.mpr hi', ?_⟩
  · intro s t hst
    have hh := (hc.pow_apply_eq_pow_apply hi').mp hst
    unfold Nat.ModEq at hh
    rw [Nat.mod_eq_of_lt (s.isLt.trans_le hk), Nat.mod_eq_of_lt (t.isLt.trans_le hk)] at hh
    exact Fin.ext hh
  · intro t
    change σ ((σ ^ t.val) i) = (σ ^ (t.val + 1)) i
    rw [pow_succ', Equiv.Perm.mul_apply]
private theorem measure_segment_le_of_pi {n k : ℕ} {β : Fin n → Type*}
    [∀ i, MeasurableSpace (β i)] (ν : ∀ i, Measure (β i)) [∀ i, SigmaFinite (ν i)]
    (T : (i : Fin n) → Fin n → Set (β i)) (a : Fin (k + 1) → Fin n)
    (ha : Function.Injective a) (c : ℝ≥0∞)
    (hm : ∀ t : Fin k, ν (a t.castSucc) (T (a t.castSucc) (a t.succ)) ≤
      ν (a t.castSucc) univ * c) :
    (Measure.pi ν) {x | ∀ t : Fin k, x (a t.castSucc) ∈ T (a t.castSucc) (a t.succ)} ≤
      (∏ i, ν i univ) * c ^ k := by
  let f : Fin k → Fin n := a ∘ Fin.castSucc
  have hf : Function.Injective f := ha.comp (Fin.castSucc_injective _)
  let s := Finset.univ.image f
  have hfind (i : Fin n) (hi : i ∈ s) : ∃ t, f t = i := by
    obtain ⟨t, -, ht⟩ := Finset.mem_image.mp hi
    exact ⟨t, ht⟩
  let B (i : Fin n) : Set (β i) :=
    if hi : i ∈ s then T i (a (Classical.choose (hfind i hi)).succ) else univ
  have hcard : s.card = k := by simp [s, Finset.card_image_of_injective _ hf]
  have hsub : {x | ∀ t : Fin k, x (a t.castSucc) ∈ T (a t.castSucc) (a t.succ)} ⊆
      univ.pi B := by
    intro x hx
    have hx' (t : Fin k) (i : Fin n) (hi : a t.castSucc = i) :
        x i ∈ T i (a t.succ) := hi ▸ hx t
    refine Set.mem_pi.mpr fun i _ ↦ ?_
    by_cases hi : i ∈ s
    · rw [show B i = T i (a (Classical.choose (hfind i hi)).succ) by simp only [B, dif_pos hi]]
      let t := Classical.choose (hfind i hi)
      have ht : a t.castSucc = i := Classical.choose_spec (hfind i hi)
      exact hx' t i ht
    · simp only [B, dif_neg hi, mem_univ]
  calc
    _ ≤ (Measure.pi ν) (univ.pi B) := measure_mono hsub
    _ = ∏ i, ν i (B i) := Measure.pi_pi ν B
    _ ≤ ∏ i, ν i univ * (if i ∈ s then c else 1) := by
      apply Finset.prod_le_prod'
      intro i _
      by_cases hi : i ∈ s
      · let t := Classical.choose (hfind i hi)
        have ht : a t.castSucc = i := Classical.choose_spec (hfind i hi)
        rw [show B i = T i (a t.succ) by simp only [B, dif_pos hi, t], if_pos hi]
        exact ht ▸ hm t
      · simp only [B, dif_neg hi, if_neg hi, mul_one, le_rfl]
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.univ_inter,
        Finset.prod_const, hcard]
private def hasAllTinyLongRotation {n : ℕ} (x : ScoreProfile n) (μ : Matching n) : Prop :=
  ∃ σ : Matching n, 81 ≤ σ.support.card ∧ IsExposedRotation (profileOfScores x) μ σ ∧
    ∀ i : {j : Fin n // j ∈ σ.support},
      femaleSpouseScore x μ (μ i.val) / femaleSpouseTotal x μ < nonTinyRotationShare n
private theorem measurableSet_hasAllTinyLongRotation {n : ℕ} (μ : Matching n) :
    MeasurableSet {x | hasAllTinyLongRotation x μ} := by
  classical
  unfold hasAllTinyLongRotation
  simp only [ofPred_exists, ofPred_and, ofPred_forall]
  refine MeasurableSet.iUnion fun σ : Matching n ↦ ?_
  have hs : MeasurableSet {a : ScoreProfile n |
      IsExposedRotation (profileOfScores a) μ σ} :=
    measurable_profileOfScores n (MeasurableSet.of_discrete :
      MeasurableSet {p : Profile n | IsExposedRotation p μ σ})
  exact (MeasurableSet.const _).inter (hs.inter (MeasurableSet.iInter fun i ↦
    measurableSet_lt ((measurable_femaleSpouseScore μ (μ i.val)).div
      (measurable_femaleSpouseTotal μ)) measurable_const))
private theorem diagonalFemaleShare_reconstruct {n : ℕ} (μ : Matching n)
    (d : DiagonalScorePairs n) (r : OffDiagonalScoreRows n) (i : Fin n) :
    let x := (splitScorePairs μ).symm (d, (offDiagonalRowsEquiv n).symm r)
    femaleSpouseScore x μ (μ i) / femaleSpouseTotal x μ =
      (diagonalPairAt d i).2 / ∑ j, (diagonalPairAt d j).2 := by
  let x := (splitScorePairs μ).symm (d, (offDiagonalRowsEquiv n).symm r)
  have he : (splitScorePairs μ x).1 = d := by simp [x]
  have hj (j : Fin n) : (diagonalPairAt d j).2 = femaleSpouseScore x μ (μ j) := by
    rw [← he, diagonalPairAt_splitScorePairs, femaleSpouseScore, Equiv.symm_apply_apply]
  change femaleSpouseScore x μ (μ i) / femaleSpouseTotal x μ = _
  rw [show femaleSpouseTotal x μ = ∑ j, femaleSpouseScore x μ (μ j) by
      exact (Equiv.sum_comp μ (femaleSpouseScore x μ)).symm]
  simp_rw [hj]
private theorem measure_diagonal_allTiny_le {n : ℕ} (μ : Matching n)
    {d : DiagonalScorePairs n} (hg : d ∈ goodDiagonalScores n)
    (hx : ∀ i, (diagonalPairAt d i).1 ∈ Ico (0 : ℝ) 1)
    (hy : ∀ i, (diagonalPairAt d i).2 ∈ Icc (0 : ℝ) 1)
    (hδsmall : coexposureSuccessorPerturbation n ≤ 1)
    (hA : 0 < 1 - 192 * (Real.log n) ^ 2 / n) (hB : 0 < 1 - 24 * Real.log n / n)
    (hδ : (1 - 192 * (Real.log n) ^ 2 / n)⁻¹ * (1 - 24 * Real.log n / n)⁻¹ ≤
      1 + coexposureSuccessorPerturbation n)
    (hrow : ∀ᵐ r ∂Measure.pi (stableScoreRowLaw d),
      let x := (splitScorePairs μ).symm (d, (offDiagonalRowsEquiv n).symm r)
      (∀ row, Function.Injective (x row)) ∧ IsScoreStable x μ) :
    (Measure.pi (stableScoreRowLaw d))
      {r | hasAllTinyLongRotation
        ((splitScorePairs μ).symm (d, (offDiagonalRowsEquiv n).symm r)) μ} ≤
      (∏ i, stableScoreRowLaw d i univ) *
        ((n : ℝ≥0∞) ^ 81 * ENNReal.ofReal (2 * nonTinyRotationShare n) ^ 80) := by
  classical
  let T (i j : Fin n) := if hij : i ≠ j then scoreRowSuccessorEvent d i ⟨j, hij⟩ else ∅
  let w (j : Fin n) := (diagonalPairAt d j).2 / ∑ l, (diagonalPairAt d l).2
  let Q (a : Fin 81 → Fin n) := Function.Injective a ∧
    ∀ t : Fin 80, w (a t.succ) < nonTinyRotationShare n
  let E (a : Fin 81 → Fin n) : Set (OffDiagonalScoreRows n) :=
    if Q a then {r | ∀ t : Fin 80, r (a t.castSucc) ∈ T (a t.castSucc) (a t.succ)} else ∅
  have hs : 0 ≤ ∑ l, (diagonalPairAt d l).2 :=
    Finset.sum_nonneg fun j _ ↦ (hy j).1
  have hw (j : Fin n) : 0 ≤ w j := div_nonneg (hy j).1 hs
  have hsub : {r | hasAllTinyLongRotation
      ((splitScorePairs μ).symm (d, (offDiagonalRowsEquiv n).symm r)) μ} ≤ᵐ[
        Measure.pi (stableScoreRowLaw d)] ⋃ a, E a := by
    filter_upwards [hrow] with r hr hbad
    obtain ⟨σ, hlen, hσ, htiny⟩ := hbad
    obtain ⟨a, hinj, hmem, hnext⟩ := cycle_has_injective_segment (IsExposedRotation.isCycle hσ)
      (k := 80) hlen
    have hQ : Q a := ⟨hinj, fun t ↦ by
      dsimp only [w]
      rw [← diagonalFemaleShare_reconstruct μ d r (a t.succ)]
      exact htiny ⟨a t.succ, hmem t.succ⟩⟩
    refine mem_iUnion.mpr ⟨a, ?_⟩
    simp only [E, if_pos hQ, mem_ofPred_eq]
    intro t
    have hmove := Equiv.Perm.mem_support.mp (hmem t.castSucc)
    have hsucc := (IsExposedRotation.successor hσ) _ hmove
    rw [hnext t] at hsucc
    have ht : a t.castSucc ≠ a t.succ :=
      fun hh ↦ (ne_of_lt t.castSucc_lt_succ) (hinj hh)
    simpa only [T, dif_pos ht] using
      scoreRowSuccessorEvent_of_isSuccessor_reconstructed μ d r _ ⟨_, ht⟩ hr.2 hr.1 hsucc
  have hE (a : Fin 81 → Fin n) :
      (Measure.pi (stableScoreRowLaw d)) (E a) ≤
        (∏ i, stableScoreRowLaw d i univ) * ENNReal.ofReal (2 * nonTinyRotationShare n) ^ 80 := by
    by_cases ha : Q a
    · simp only [E, if_pos ha]
      refine measure_segment_le_of_pi (stableScoreRowLaw d) T a ha.1 _ fun t ↦ ?_
      have ht : a t.castSucc ≠ a t.succ :=
        fun hh ↦ (ne_of_lt t.castSucc_lt_succ) (ha.1 hh)
      simp only [T, dif_pos ht]
      refine (stableScoreRowLaw_successor_le_of_goodDiagonalScores hg hx hy hA hB hδ
        _ ⟨_, ht⟩).trans (mul_le_mul_right (ENNReal.ofReal_le_ofReal ?_) _)
      change (1 + coexposureSuccessorPerturbation n) * w (a t.succ) ≤ _
      exact mul_le_mul (by linarith) (ha.2 t).le (hw _) (by norm_num)
    · simp [E, ha]
  calc
    _ ≤ (Measure.pi (stableScoreRowLaw d)) (⋃ a, E a) := measure_mono_ae hsub
    _ ≤ ∑' a, (Measure.pi (stableScoreRowLaw d)) (E a) := measure_iUnion_le E
    _ ≤ ∑ _a : Fin 81 → Fin n,
          (∏ i, stableScoreRowLaw d i univ) * ENNReal.ofReal (2 * nonTinyRotationShare n)^80 := by
        rw [tsum_fintype]
        exact Finset.sum_le_sum fun a _ ↦ hE a
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_pow]
      ac_rfl
private theorem ae_diagonalMale_openUpper (n : ℕ) :
    ∀ᵐ d ∂diagonalScoreLaw n, ∀ i, (diagonalPairAt d i).1 ∈ Ico (0 : ℝ) 1 := by
  have hne : ∀ᵐ t ∂unitScoreLaw, t ≠ (1 : ℝ) := by rw [ae_iff]; simp
  have hu : ∀ᵐ t ∂unitScoreLaw, t ∈ Ico (0 : ℝ) 1 := by
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Icc :
      MeasurableSet (Icc (0 : ℝ) 1)), hne] with t ht hnt
    exact ⟨ht.1, lt_of_le_of_ne ht.2 hnt⟩
  have hp : ∀ᵐ z ∂unitScorePairLaw, z.1 ∈ Ico (0 : ℝ) 1 :=
    (Measure.quasiMeasurePreserving_fst (μ := unitScoreLaw)
      (ν := unitScoreLaw)).ae hu
  exact ae_all_iff.2 fun i ↦ (Measure.tendsto_eval_ae_ae
    (μ := fun _ : {q : ScorePairIndex n // q.1 = q.2} ↦ unitScorePairLaw)
    (i := ⟨(i,i), rfl⟩)).eventually hp
private theorem stableMass_eq_lintegral_nonTinyRows {n : ℕ} (μ : Matching n) :
    continuousScoreLaw n {x | IsScoreStable x μ} =
      ∫⁻ d, (∏ i, stableScoreRowLaw d i univ) ∂diagonalScoreLaw n := by
  have h := continuousScoreLaw_lintegral_stable_and_diagonal_rows μ
    (C := univ) MeasurableSet.univ (f := fun _ ↦ 1) measurable_const
  simpa only [mem_univ, and_true, Measure.restrict_univ, lintegral_one,
    Measure.restrict_apply_univ, Measure.pi_univ] using h
private theorem nonTiny_path_coefficient {n : ℕ} (hn : 0 < n) :
    (n : ℝ≥0∞) ^ 81 * ENNReal.ofReal (2 * nonTinyRotationShare n) ^ 80 =
      ENNReal.ofReal (2 ^ 80 * (n : ℝ) ^ (-3 : ℝ)) := by
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  rw [← ENNReal.ofReal_natCast n, ← ENNReal.ofReal_pow (Nat.cast_nonneg _) 81,
    ← ENNReal.ofReal_pow (by unfold nonTinyRotationShare; positivity) 80,
    ← ENNReal.ofReal_mul (by positivity)]
  apply congrArg ENNReal.ofReal
  unfold nonTinyRotationShare
  rw [mul_pow]
  calc
    _ = (2 : ℝ) ^ 80 * ((n : ℝ) ^ 81 * ((n : ℝ) ^ (-(21 / 20) : ℝ)) ^ 80) := by ac_rfl
    _ = _ := by
      rw [← Real.rpow_natCast (n : ℝ) 81, ← Real.rpow_mul_natCast hn'.le,
        ← Real.rpow_add hn']
      norm_num
theorem eventually_measure_stable_allTinyLongRotation_le :
    ∀ᶠ n : ℕ in atTop, ∀ μ : Matching n,
      continuousScoreLaw n {x | IsScoreStable x μ ∧ GoodSpouseScores x μ ∧
        hasAllTinyLongRotation x μ} ≤
        continuousScoreLaw n {x | IsScoreStable x μ} *
          ENNReal.ofReal (2 ^ 80 * (n : ℝ) ^ (-3 : ℝ)) := by
  filter_upwards [eventually_coexposureSuccessorPerturbation_bounds] with n h
  rcases h with ⟨hn, -, hδsmall, hA, hB, hδ⟩
  intro μ
  let F : Set (ScoreProfile n) := {x | hasAllTinyLongRotation x μ}
  let C := goodDiagonalScores n
  let S : Set (ScoreProfile n) := {x | IsScoreStable x μ ∧ (splitScorePairs μ x).1 ∈ C}
  let c := ENNReal.ofReal (2 ^ 80 * (n : ℝ) ^ (-3 : ℝ))
  have hF : MeasurableSet F := measurableSet_hasAllTinyLongRotation μ
  have hC : MeasurableSet C := measurableSet_goodDiagonalScores n
  have hδ₁ : coexposureSuccessorPerturbation n ≤ 1 := by
    refine hδsmall.trans ((div_le_one (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn))).mpr ?_)
    exact Real.one_le_sqrt.mpr (by exact_mod_cast hn)
  have hpre (d : DiagonalScorePairs n) :
      MeasurableSet {r | hasAllTinyLongRotation
        ((splitScorePairs μ).symm (d, (offDiagonalRowsEquiv n).symm r)) μ} :=
    hF.preimage ((splitScorePairs μ).symm.measurable.comp
      (measurable_const.prodMk (offDiagonalRowsEquiv n).symm.measurable))
  calc
    _ = ∫⁻ x in S, F.indicator 1 x ∂continuousScoreLaw n := by
      rw [lintegral_indicator_one hF, Measure.restrict_apply hF]
      congr 1
      ext x
      simp only [F, S, C, mem_inter_iff, mem_ofPred_eq, mem_goodDiagonalScores_iff]
      tauto
    _ = ∫⁻ d in C, Measure.pi (stableScoreRowLaw d)
          {r | hasAllTinyLongRotation
            ((splitScorePairs μ).symm (d, (offDiagonalRowsEquiv n).symm r)) μ}
          ∂diagonalScoreLaw n := by
      unfold S
      rw [continuousScoreLaw_lintegral_stable_and_diagonal_rows μ (f := F.indicator 1) hC
        (measurable_const.indicator hF)]
      apply lintegral_congr
      intro d
      rw [← lintegral_indicator_one (hpre d)]
      apply lintegral_congr
      intro r
      rfl
    _ ≤ ∫⁻ d in C, (∏ i, stableScoreRowLaw d i univ) * c ∂diagonalScoreLaw n := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hC, ae_restrict_of_ae (ae_diagonalMale_openUpper n),
        ae_restrict_of_ae (ae_diagonalPairAt_mem_Icc n),
        ae_restrict_of_ae (ae_diagonal_ae_stableRows μ)] with d hd hx hy hr
      dsimp only [c]
      rw [← nonTiny_path_coefficient hn]
      exact measure_diagonal_allTiny_le μ hd hx (fun j ↦ (hy j).2) hδ₁ hA hB hδ hr
    _ = (∫⁻ d in C, (∏ i, stableScoreRowLaw d i univ) ∂diagonalScoreLaw n) * c :=
      lintegral_mul_const' c _ ENNReal.ofReal_ne_top
    _ ≤ _ := by
      rw [stableMass_eq_lintegral_nonTinyRows μ]
      gcongr
      exact Measure.restrict_le_self
private def badNonTinyRotation (n : ℕ) : Set (ScoreProfile n) :=
  {x | ∃ μ : Matching n, IsStable (profileOfScores x) μ ∧ hasAllTinyLongRotation x μ}
theorem exists_nonTiny_participant_of_not_mem_badNonTinyRotation {n : ℕ}
    {x : ScoreProfile n} (hx : x ∉ badNonTinyRotation n) {μ σ : Matching n}
    (hμ : IsStable (profileOfScores x) μ) (hσ : IsExposedRotation (profileOfScores x) μ σ)
    (hlen : 81 ≤ σ.support.card) :
    ∃ i ∈ σ.support,
      nonTinyRotationShare n ≤ femaleSpouseScore x μ (μ i) / femaleSpouseTotal x μ := by
  by_contra! h
  exact hx ⟨μ, hμ, σ, hlen, hσ, fun i ↦ h i.val i.property⟩
private theorem eventually_measure_badNonTinyRotation_le [LPHyp3_3] :
    ∀ᶠ n : ℕ in atTop, continuousScoreLaw n (badNonTinyRotation n) ≤
      continuousScoreLaw n (goodCoexposureScores n)ᶜ + ENNReal.ofReal (2 ^ 80 / (n : ℝ)) := by
  filter_upwards [eventually_measure_stable_allTinyLongRotation_le,
    eventually_expectedNumStableMatchings_le_sizeSq, eventually_gt_atTop (0 : ℕ)]
    with n hfixed hmean hn
  let G (μ : Matching n) : Set (ScoreProfile n) :=
    {x | IsScoreStable x μ ∧ GoodSpouseScores x μ ∧ hasAllTinyLongRotation x μ}
  have hsub : badNonTinyRotation n ⊆ (goodCoexposureScores n)ᶜ ∪ ⋃ μ, G μ := by
    rintro x ⟨μ, hμ, hrot⟩
    by_cases hx : x ∈ goodCoexposureScores n
    · exact Or.inr (mem_iUnion.mpr ⟨μ, (isStable_profileOfScores_iff hx.1 μ).mp hμ,
        hx.2.2 μ hμ, hrot⟩)
    · exact Or.inl hx
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add_right ?_ _))
  calc
    _ ≤ ∑' μ, continuousScoreLaw n (G μ) := measure_iUnion_le G
    _ ≤ ∑ μ : Matching n, continuousScoreLaw n {x | IsScoreStable x μ} *
        ENNReal.ofReal (2 ^ 80 * (n : ℝ) ^ (-3 : ℝ)) := by
      rw [tsum_fintype]
      exact Finset.sum_le_sum fun μ _ ↦ hfixed μ
    _ = ENNReal.ofReal (expectedNumStableMatchings n) *
        ENNReal.ofReal (2 ^ 80 * (n : ℝ) ^ (-3 : ℝ)) := by
      rw [← Finset.sum_mul, sum_measure_scoreStable_eq_expected]
    _ ≤ ENNReal.ofReal ((n : ℝ)^2) * ENNReal.ofReal (2 ^ 80 * (n : ℝ) ^ (-3 : ℝ)) :=
      mul_le_mul' (ENNReal.ofReal_le_ofReal hmean) le_rfl
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      apply congrArg ENNReal.ofReal
      have hp : (n : ℝ) ^ (-3 : ℝ) = ((n : ℝ)^3)⁻¹ := by
        rw [show (-3 : ℝ) = -(3 : ℝ) by norm_num, Real.rpow_neg hn'.le,
          show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rw [hp]
      field_simp
theorem tendsto_measure_badNonTinyRotation_zero [LPHyp2_1] [LPHyp3_3] :
    Tendsto (fun n ↦ continuousScoreLaw n (badNonTinyRotation n)) atTop (𝓝 0) := by
  have h₁ := tendsto_measure_badCoexposureScores_zero_of_mean_upper
    meanUpperConstant_nonneg eventually_expectedNumStableMatchings_le_meanUpper
  have h₂ := ENNReal.tendsto_ofReal (tendsto_const_div_atTop_nhds_zero_nat (2 ^ 80 : ℝ))
  rw [ENNReal.ofReal_zero] at h₂
  have h := h₁.add h₂
  simp only [add_zero] at h
  exact tendsto_const_nhds.squeeze' h (Eventually.of_forall fun _ ↦ zero_le)
    eventually_measure_badNonTinyRotation_le
end AbunLP
end

-- ScoreRotationAnchorProbability
section
open Filter MeasureTheory Set
open scoped ENNReal Topology
namespace AbunLP
theorem exists_eventually_measure_scoreWalkBandEndpoints_diff_anchorAbundance_le [LPHyp1_0] [LPHyp2_1] [LPHyp3_0] [LPHyp3_2] [LPHyp3_3]
    {η : ℝ} (hη : 0 < η) :
    ∃ b A : ℝ, 0 < b ∧ b ≤ 1 ∧ 1 ≤ A ∧ ∀ᶠ n : ℕ in atTop,
      continuousScoreLaw n
        (scoreWalkBandEndpoints n \ scoreWalkAnchorAbundanceAtCutoffs n (b * Real.sqrt n) A) ≤
        ENNReal.ofReal η := by
  obtain ⟨b, A, hb, hb₁, hA, hband⟩ :=
    exists_eventually_measure_scoreWalkBandEndpoints_diff_sqrtAbundance_le
      (η := η / 3) (by positivity)
  refine ⟨b, A, hb, hb₁, hA, ?_⟩
  let K (n : ℕ) := b * Real.sqrt (n : ℝ)
  have hK : ∀ᶠ n : ℕ in atTop, 81 ≤ K n :=
    ((Real.tendsto_sqrt_atTop.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul_atTop hb).eventually_ge_atTop 81
  have himp := eventually_scoreWalkAnchorAbundance_of_bandAbundance K hK
  have hg := tendsto_measure_badCoexposureScores_zero_of_mean_upper
    meanUpperConstant_nonneg eventually_expectedNumStableMatchings_le_meanUpper
  have hη₀ := ENNReal.ofReal_pos.mpr (show 0 < η / 3 by positivity)
  filter_upwards [himp, hband, hg.eventually_lt_const hη₀,
    tendsto_measure_badNonTinyRotation_zero.eventually_lt_const hη₀]
    with n himp hband hg hnon
  let E := scoreWalkBandEndpoints n
  let B := scoreWalkBandAbundanceAtCutoffs n (K n) A
  let Q := scoreWalkAnchorAbundanceAtCutoffs n (K n) A
  have hsub : E \ Q ⊆ ((E \ B) ∪ (goodCoexposureScores n)ᶜ) ∪ badNonTinyRotation n := by
    intro x hx
    by_cases hB : x ∈ B
    · by_cases hG : x ∈ goodCoexposureScores n
      · by_cases hN : x ∈ badNonTinyRotation n
        · exact Or.inr hN
        · exfalso
          apply hx.2
          refine himp hG hB fun μ hμ σ hσ hlen ↦ ?_
          simpa only [nonTinyRotationShare, neg_div] using
            exists_nonTiny_participant_of_not_mem_badNonTinyRotation hN hμ hσ hlen
      · exact Or.inl (Or.inr hG)
    · exact Or.inl (Or.inl ⟨hx.1, hB⟩)
  change continuousScoreLaw n (E \ Q) ≤ _
  calc
    _ ≤ continuousScoreLaw n
        (((E \ B) ∪ (goodCoexposureScores n)ᶜ) ∪ badNonTinyRotation n) := measure_mono hsub
    _ ≤ continuousScoreLaw n (E \ B) + continuousScoreLaw n (goodCoexposureScores n)ᶜ +
        continuousScoreLaw n (badNonTinyRotation n) :=
      (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ ENNReal.ofReal (η / 3) + ENNReal.ofReal (η / 3) + ENNReal.ofReal (η / 3) :=
      add_le_add (add_le_add hband hg.le) hnon.le
    _ = _ := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
theorem exists_eventually_measure_badScoreWalkAnchorAbundance_le_of_endpoints [LPHyp1_0] [LPHyp2_1] [LPHyp3_0] [LPHyp3_2] [LPHyp3_3]
    (hend : Tendsto (fun n ↦ continuousScoreLaw n (scoreWalkBandEndpoints n)ᶜ) atTop (𝓝 0))
    {η : ℝ} (hη : 0 < η) :
    ∃ b A : ℝ, 0 < b ∧ b ≤ 1 ∧ 1 ≤ A ∧ ∀ᶠ n : ℕ in atTop,
      continuousScoreLaw n (scoreWalkAnchorAbundanceAtCutoffs n (b * Real.sqrt n) A)ᶜ ≤
        ENNReal.ofReal η := by
  obtain ⟨b, A, hb, hb₁, hA, ha⟩ :=
    exists_eventually_measure_scoreWalkBandEndpoints_diff_anchorAbundance_le
      (η := η / 2) (by positivity)
  refine ⟨b, A, hb, hb₁, hA, ?_⟩
  have hη₀ := ENNReal.ofReal_pos.mpr (show 0 < η / 2 by positivity)
  filter_upwards [hend.eventually_lt_const hη₀, ha] with n he ha
  let E := scoreWalkBandEndpoints n
  let Q := scoreWalkAnchorAbundanceAtCutoffs n (b * Real.sqrt n) A
  have hsub : Qᶜ ⊆ Eᶜ ∪ (E \ Q) := by
    intro x hx
    by_cases h : x ∈ E
    · exact Or.inr ⟨h, hx⟩
    · exact Or.inl h
  calc
    _ ≤ continuousScoreLaw n (Eᶜ ∪ (E \ Q)) := measure_mono hsub
    _ ≤ continuousScoreLaw n Eᶜ + continuousScoreLaw n (E \ Q) := measure_union_le _ _
    _ ≤ ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) := add_le_add he.le ha
    _ = _ := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
end AbunLP
end

-- DAEndpointAsymptotics
section
open Filter MeasureTheory Set StableMarriage
open scoped ENNReal Topology AbunLP
namespace AbunLP
private class LPHyp3_1 : Prop where
  bound : Tendsto (fun n ↦ continuousScoreLaw n (scoreWalkBandEndpoints n)ᶜ) atTop (𝓝 0)
theorem tendsto_measure_badScoreWalkBandEndpoints [h : LPHyp3_1] :
    Tendsto (fun n ↦ continuousScoreLaw n (scoreWalkBandEndpoints n)ᶜ) atTop (𝓝 0) :=
  h.bound
theorem exists_eventually_measure_badScoreWalkAnchorAbundance_le [LPHyp1_0] [LPHyp2_1] [LPHyp3_0] [LPHyp3_1] [LPHyp3_2] [LPHyp3_3]
    {η : ℝ} (hη : 0 < η) :
    ∃ b A : ℝ, 0 < b ∧ b ≤ 1 ∧ 1 ≤ A ∧ ∀ᶠ n : ℕ in atTop,
      continuousScoreLaw n (scoreWalkAnchorAbundanceAtCutoffs n (b * Real.sqrt n) A)ᶜ ≤
        ENNReal.ofReal η :=
  exists_eventually_measure_badScoreWalkAnchorAbundance_le_of_endpoints
    tendsto_measure_badScoreWalkBandEndpoints hη
end AbunLP
end

-- PivotMarkedCutoffBridge
section
open Filter MeasureTheory ProbabilityTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace AbunLP
private theorem sum_supportPermutation_weights_le_pow {n k : ℕ} (q : Fin n → ℝ≥0∞)
    (hzero : (∑ j, q j) ≠ 0) (htop : (∑ j, q j) ≠ ∞) :
    (∑ σ ∈ Finset.univ.filter (fun σ : Matching n ↦ σ.support.card = k),
      ∏ i ∈ σ.support, q i) ≤ (∑ j, q j) ^ k := by
  classical
  let Q := ∑ j, q j
  let p (j : Fin n) := Q⁻¹ * q j
  have hp : ∑ j, p j = 1 := by
    simp only [p, ← Finset.mul_sum]
    exact ENNReal.inv_mul_cancel hzero htop
  have hq (j : Fin n) : q j = Q * p j := by
    change q j = Q * (Q⁻¹ * q j)
    rw [← mul_assoc, ENNReal.mul_inv_cancel hzero htop, one_mul]
  have he :
      (∑ σ ∈ Finset.univ.filter (fun σ : Matching n ↦ σ.support.card = k),
        ∏ i ∈ σ.support, q i) =
      Q ^ k * ∑ σ ∈ Finset.univ.filter (fun σ : Matching n ↦ σ.support.card = k),
        ∏ i ∈ σ.support, p i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ hσ
    conv_lhs => simp only [hq, Finset.prod_mul_distrib, Finset.prod_const,
      (Finset.mem_filter.mp hσ).2]
  rw [he]
  exact (mul_le_mul_right (sum_supportPermutation_weights_le_one k p hp) (Q ^ k)).trans_eq
    (mul_one _)
section IndependentRows
variable {n : ℕ} {Ω : Fin n → Type*} [∀ i, MeasurableSpace (Ω i)]
  (ν : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (ν i)]
  (out : ∀ i, Ω i → Option (Fin n)) (g : ∀ i, Fin n → Ω i → ℝ)
  [MeasurableSpace (Option (Fin n))] [MeasurableSingletonClass (Option (Fin n))]
private noncomputable def tiltedForwardArc (i j : Fin n) : Ω i → ℝ≥0∞ :=
  {x | out i x = some j}.indicator fun x ↦ ENNReal.ofReal (Real.exp (g i j x))
theorem measure_pi_cycle_sum_gt_le (hout : ∀ i, Measurable (out i))
    (hg : ∀ i j, Measurable (g i j)) (σ : Matching n) (t : ℝ) :
    Measure.pi ν {y | RealizesDirectedCycle (fun i ↦ out i (y i)) σ ∧
      t < ∑ i ∈ σ.support, g i (σ i) (y i)} ≤
      ENNReal.ofReal (Real.exp (-t)) *
        ∏ i ∈ σ.support, ∫⁻ x, tiltedForwardArc out g i (σ i) x ∂ν i := by
  classical
  let F (i : Fin n) := tiltedForwardArc out g i (σ i)
  have hF (i : Fin n) : Measurable (F i) :=
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hg i _))).indicator
      (measurableSet_eq_fun (hout i) measurable_const)
  have hFπ (i : Fin n) : Measurable (fun y : ∀ j, Ω j ↦ F i (y i)) :=
    (hF i).comp (measurable_pi_apply i)
  let G (y : ∀ i, Ω i) := ENNReal.ofReal (Real.exp (-t)) * ∏ i ∈ σ.support, F i (y i)
  have hG : Measurable G := measurable_const.mul (σ.support.measurable_prod fun i _ ↦ hFπ i)
  calc
    _ ≤ ∫⁻ y, G y ∂Measure.pi ν := by
      apply meas_le_lintegral₀ hG.aemeasurable
      intro y hy
      have he : (∏ i ∈ σ.support, F i (y i)) =
          ∏ i ∈ σ.support, ENNReal.ofReal (Real.exp (g i (σ i) (y i))) := by
        apply Finset.prod_congr rfl
        intro i hi
        exact indicator_of_mem (s := {x | out i x = some (σ i)}) (hy.1.2 i hi)
          (fun x ↦ ENNReal.ofReal (Real.exp (g i (σ i) x)))
      unfold G
      rw [he, ← ENNReal.ofReal_prod_of_nonneg (fun _ _ ↦ Real.exp_nonneg _),
        ← Real.exp_sum, ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
      exact ENNReal.one_le_ofReal.mpr (Real.one_le_exp (by linarith [hy.2]))
    _ = _ := by
      unfold G
      rw [lintegral_const_mul _ (σ.support.measurable_prod fun i _ ↦ hFπ i),
        lintegral_prod_eq_prod_lintegral_of_indepFun σ.support _
          (iIndepFun_pi fun i ↦ (hF i).aemeasurable) hFπ]
      congr 1
      exact Finset.prod_congr rfl fun i _ ↦
        (measurePreserving_eval ν i).lintegral_comp (hF i)
theorem measure_pi_exists_cycle_length_sum_gt_le
    (hout : ∀ i, Measurable (out i)) (hg : ∀ i j, Measurable (g i j))
    (q : Fin n → ℝ≥0∞) (hzero : (∑ j, q j) ≠ 0) (htop : (∑ j, q j) ≠ ∞)
    (harc : ∀ i j, i ≠ j → (∫⁻ x, tiltedForwardArc out g i j x ∂ν i) ≤ q j)
    (k : ℕ) (t : ℝ) :
    Measure.pi ν {y | ∃ σ : Matching n, RealizesDirectedCycle (fun i ↦ out i (y i)) σ ∧
      σ.support.card = k ∧ t < ∑ i ∈ σ.support, g i (σ i) (y i)} ≤
      ENNReal.ofReal (Real.exp (-t)) * (∑ j, q j) ^ k := by
  classical
  let S := Finset.univ.filter (fun σ : Matching n ↦ σ.support.card = k)
  let E (σ : Matching n) := {y : ∀ i, Ω i | RealizesDirectedCycle (fun i ↦ out i (y i)) σ ∧
    t < ∑ i ∈ σ.support, g i (σ i) (y i)}
  have he :
      {y | ∃ σ : Matching n, RealizesDirectedCycle (fun i ↦ out i (y i)) σ ∧
        σ.support.card = k ∧ t < ∑ i ∈ σ.support, g i (σ i) (y i)} =
        ⋃ σ ∈ S, E σ := by
    ext y
    simp only [mem_ofPred_eq, mem_iUnion, S, E, Finset.mem_filter_univ]
    constructor
    · rintro ⟨σ, hσ, hk, ht⟩
      exact ⟨σ, hk, hσ, ht⟩
    · rintro ⟨σ, hk, hσ, ht⟩
      exact ⟨σ, hσ, hk, ht⟩
  rw [he]
  calc
    _ ≤ ∑ σ ∈ S, Measure.pi ν (E σ) := measure_biUnion_finset_le _ _
    _ ≤ ∑ σ ∈ S, ENNReal.ofReal (Real.exp (-t)) * ∏ i ∈ σ.support, q i :=
      Finset.sum_le_sum fun σ _ ↦ (measure_pi_cycle_sum_gt_le ν out g hout hg σ t).trans <|
        mul_le_mul_right (calc
          _ ≤ ∏ i ∈ σ.support, q (σ i) :=
            Finset.prod_le_prod' fun i hi ↦ harc i (σ i) (Equiv.Perm.mem_support.mp hi).symm
          _ = _ := σ.prod_comp σ.support q (fun _ hi ↦ Equiv.Perm.mem_support.mpr hi)) _
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_right (sum_supportPermutation_weights_le_pow q hzero htop) _
end IndependentRows
theorem measure_scoreStable_diagonal_scoreEvent_le {n : ℕ} (μ : Matching n)
    {C : Set (DiagonalScorePairs n)} (hC : MeasurableSet C)
    (hvalid : ∀ d ∈ C, (∀ i, (diagonalPairAt d i).1 ∈ Ico 0 1) ∧
      ∀ i, (diagonalPairAt d i).2 ∈ Icc 0 1)
    {E : Set (ScoreProfile n)} (hE : MeasurableSet E) {a : ℝ≥0∞} (ha : a ≠ ∞)
    (hrow : ∀ᵐ d ∂diagonalScoreLaw n, d ∈ C →
      (Measure.pi (normalizedStableScoreRowLaw d))
        {r | (splitScorePairs μ).symm (d, (offDiagonalRowsEquiv n).symm r) ∈ E} ≤ a) :
    continuousScoreLaw n {x | IsScoreStable x μ ∧ (splitScorePairs μ x).1 ∈ C ∧ x ∈ E} ≤
      continuousScoreLaw n {x | IsScoreStable x μ} * a := by
  let D : Set (ScoreProfile n) := {x | IsScoreStable x μ ∧ (splitScorePairs μ x).1 ∈ C}
  let f : ScoreProfile n → ℝ≥0∞ := E.indicator 1
  have hf : Measurable f := measurable_const.indicator hE
  have hleft : continuousScoreLaw n
      {x | IsScoreStable x μ ∧ (splitScorePairs μ x).1 ∈ C ∧ x ∈ E} =
      ∫⁻ x in D, f x ∂continuousScoreLaw n := by
    rw [show f = E.indicator 1 from rfl, lintegral_indicator_one hE, Measure.restrict_apply hE]
    congr 1
    ext x
    change (IsScoreStable x μ ∧ (splitScorePairs μ x).1 ∈ C ∧ x ∈ E) ↔
      (x ∈ E ∧ IsScoreStable x μ ∧ (splitScorePairs μ x).1 ∈ C)
    tauto
  rw [hleft, continuousScoreLaw_lintegral_stable_and_diagonal_rows μ hC hf]
  let m (d : DiagonalScorePairs n) := offDiagonalScoreLaw n (offDiagonalNonblocking d)
  have hM : (∫⁻ d, m d ∂diagonalScoreLaw n) = continuousScoreLaw n {x | IsScoreStable x μ} := by
    simpa only [mem_univ, and_true, indicator_univ, m] using
      (continuousScoreLaw_stable_and_diagonal μ (C := univ) MeasurableSet.univ).symm
  calc
    _ ≤ ∫⁻ d in C, m d * a ∂diagonalScoreLaw n := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hC, ae_restrict_of_ae hrow] with d hd hr
      obtain ⟨hx, hy⟩ := hvalid d hd
      let R := (splitScorePairs μ).symm ∘ fun r : OffDiagonalScoreRows n ↦
        (d, (offDiagonalRowsEquiv n).symm r)
      let B := R ⁻¹' E
      have hB : MeasurableSet B := hE.preimage
        ((splitScorePairs μ).symm.measurable.comp
          (measurable_const.prodMk (offDiagonalRowsEquiv n).symm.measurable))
      have hfun : (fun r ↦ f ((splitScorePairs μ).symm (d, (offDiagonalRowsEquiv n).symm r))) =
          B.indicator 1 := by
        funext r
        change E.indicator 1 (R r) = _
        by_cases hb : r ∈ B
        · rw [indicator_of_mem (show R r ∈ E from hb), indicator_of_mem hb]
          rfl
        · rw [indicator_of_notMem (show R r ∉ E from hb), indicator_of_notMem hb]
      rw [pi_stableScoreRowLaw_eq_smul_normalized d hx hy, hfun, lintegral_smul_measure,
        lintegral_indicator_one hB, smul_eq_mul]
      exact mul_le_mul_right (hr hd) _
    _ ≤ ∫⁻ d, m d * a ∂diagonalScoreLaw n :=
      lintegral_mono' Measure.restrict_le_self le_rfl
    _ = _ := by rw [lintegral_mul_const' _ _ ha, hM]
theorem measure_exists_scoreStable_diagonal_event_le {n : ℕ}
    (C : Set (DiagonalScorePairs n)) (E : Matching n → Set (ScoreProfile n)) (a : ℝ≥0∞)
    (h : ∀ μ : Matching n,
      continuousScoreLaw n {x | IsScoreStable x μ ∧ (splitScorePairs μ x).1 ∈ C ∧ x ∈ E μ} ≤
        continuousScoreLaw n {x | IsScoreStable x μ} * a) :
    continuousScoreLaw n {x | ∃ μ : Matching n, IsScoreStable x μ ∧
      (splitScorePairs μ x).1 ∈ C ∧ x ∈ E μ} ≤ ENNReal.ofReal (expectedNumStableMatchings n) * a := by
  let F (μ : Matching n) :=
    {x | IsScoreStable x μ ∧ (splitScorePairs μ x).1 ∈ C ∧ x ∈ E μ}
  have he : {x | ∃ μ : Matching n, IsScoreStable x μ ∧
      (splitScorePairs μ x).1 ∈ C ∧ x ∈ E μ} = ⋃ μ, F μ := by
    ext x
    change (∃ μ : Matching n, x ∈ F μ) ↔ x ∈ ⋃ μ, F μ
    exact mem_iUnion.symm
  rw [he]
  calc
    _ ≤ ∑ μ : Matching n, continuousScoreLaw n (F μ) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ μ : Matching n, continuousScoreLaw n {x | IsScoreStable x μ} * a :=
      Finset.sum_le_sum fun μ _ ↦ h μ
    _ = _ := by rw [← Finset.sum_mul, sum_measure_scoreStable_eq_expected]
end AbunLP
end

-- PivotSupportMassTail
section
open Filter MeasureTheory Set StableMarriage
open scoped ENNReal Topology
namespace AbunLP
private theorem exp_le_one_add_two_mul {t : ℝ} (ht : 0 ≤ t) (ht₁ : t ≤ 1) :
    Real.exp t ≤ 1 + 2 * t := by
  have h := convexOn_exp.2 (mem_univ (0 : ℝ)) (mem_univ (1 : ℝ))
    (show 0 ≤ 1 - t by linarith) ht (show 1 - t + t = 1 by ring)
  simp only [smul_eq_mul, mul_zero, mul_one, zero_add, Real.exp_zero] at h
  nlinarith only [h, mul_nonneg ht (sub_nonneg.mpr Real.exp_one_lt_three.le)]
theorem sum_expTilt_le {ι : Type*} [Fintype ι] {p r : ι → ℝ} {θ : ℝ}
    (hp : ∀ i, 0 ≤ p i) (hp₁ : ∑ i, p i = 1)
    (ht : ∀ i, 0 ≤ θ * r i ∧ θ * r i ≤ 1) :
    (∑ i, p i * Real.exp (θ * r i)) ≤ 1 + 2 * θ * ∑ i, p i * r i := by
  calc
    _ ≤ ∑ i, p i * (1 + 2 * (θ * r i)) := Finset.sum_le_sum fun i _ ↦
      mul_le_mul_of_nonneg_left (exp_le_one_add_two_mul (ht i).1 (ht i).2) (hp i)
    _ = _ := by
      simp only [mul_add, mul_one, Finset.sum_add_distrib, hp₁]
      rw [Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun i _ ↦ by ring
theorem eventually_exp_neg_size_rpow_le (a q : ℝ) (ha : 0 < a) :
    ∀ᶠ n : ℕ in atTop, Real.exp (-((n : ℝ) ^ a)) ≤ (n : ℝ) ^ (-q) := by
  have hlog := (((isLittleO_log_rpow_atTop ha).const_mul_left q).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventuallyLE
  filter_upwards [eventually_gt_atTop (0 : ℕ), hlog] with n hn h
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have habs : |q * Real.log n| ≤ |(n : ℝ) ^ a| := h
  rw [abs_of_nonneg (Real.rpow_nonneg hnR.le _)] at habs
  rw [show (n : ℝ) ^ (-q) = Real.exp (Real.log n * -q) from Real.rpow_def_of_pos hnR _]
  apply Real.exp_le_exp.mpr
  linarith only [(le_abs_self (q * Real.log n)).trans habs]
theorem eventually_supportMassTilt_pow_mul_le {A H R : ℝ}
    (hH : 0 ≤ H) (q : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ k : ℕ, (k : ℝ) ≤ A * Real.sqrt n →
      ∀ (p r : Fin n → ℝ), (∀ i, 0 ≤ p i) → (∑ i, p i = 1) →
        (∀ i, 0 ≤ r i ∧ r i ≤ R * Real.log n / n) → (∑ i, p i * r i) ≤ H / n →
      Real.exp (-((n : ℝ) ^ (3 / 4 : ℝ)) *
          (((1 + 2 * H) * A + 1) / Real.sqrt n)) *
        ((1 + coexposureSuccessorPerturbation n) *
          ∑ i, p i * Real.exp ((n : ℝ) ^ (3 / 4 : ℝ) * r i)) ^ k ≤ (n : ℝ) ^ (-q) := by
  have hlog := (((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).const_mul_left
    R).comp_tendsto (tendsto_natCast_atTop_atTop (R := ℝ))).eventuallyLE
  filter_upwards [eventually_coexposureSuccessorPerturbation_bounds, hlog,
    eventually_exp_neg_size_rpow_le (1 / 4) q (by norm_num)] with n hn hl hdecay
  intro k hk p r hp hp₁ hr hpr
  let x : ℝ := n
  let t : ℝ := x ^ (1 / 4 : ℝ)
  let θ : ℝ := x ^ (3 / 4 : ℝ)
  let s : ℝ := Real.sqrt x
  let B : ℝ := (1 + 2 * H) * A + 1
  let δ := coexposureSuccessorPerturbation n
  have hx : 0 < x := Nat.cast_pos.mpr hn.1
  have ht : 0 < t := Real.rpow_pos_of_pos hx _
  have hθ : 0 < θ := Real.rpow_pos_of_pos hx _
  have hs : 0 < s := Real.sqrt_pos.mpr hx
  have ht₁ : 1 ≤ t := Real.one_le_rpow (Nat.one_le_cast.mpr hn.1) (by norm_num)
  have hθt : θ * t = x := by
    dsimp [θ, t]
    rw [← Real.rpow_add hx, show (3 / 4 : ℝ) + 1 / 4 = 1 by norm_num, Real.rpow_one]
  have htt : t * t = s := by
    dsimp [t, s]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx]
    norm_num
  have hst : s * t = θ := by
    dsimp [s, t, θ]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx]
    norm_num
  have hlog' : R * Real.log x ≤ t := by
    have ha : |R * Real.log x| ≤ |t| := hl
    rw [abs_of_pos ht] at ha
    exact (le_abs_self _).trans ha
  have hscale : θ / x = 1 / t := by
    rw [← hθt]
    field_simp
  have hδ : δ ≤ 1 / t := by
    refine hn.2.2.1.trans (one_div_le_one_div_of_le ht ?_)
    change t ≤ s
    rw [← htt]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right ht₁ ht.le
  have htilt : ∀ i, 0 ≤ θ * r i ∧ θ * r i ≤ 1 := by
    intro i
    refine ⟨mul_nonneg hθ.le (hr i).1, ?_⟩
    calc
      _ ≤ θ * (R * Real.log x / x) := mul_le_mul_of_nonneg_left (hr i).2 hθ.le
      _ ≤ θ * (t / x) := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hlog' hx.le) hθ.le
      _ = 1 := by rw [← mul_div_assoc, hθt, div_self hx.ne']
  have hsum : (∑ i, p i * Real.exp (θ * r i)) ≤ 1 + 2 * H / t := by
    refine (sum_expTilt_le hp hp₁ htilt).trans ?_
    calc
      _ ≤ 1 + 2 * θ * (H / x) :=
        add_le_add_right (mul_le_mul_of_nonneg_left hpr (mul_nonneg (by norm_num) hθ.le)) _
      _ = _ := by rw [show 2 * θ * (H / x) = (2 * H) * (θ / x) by ring, hscale]; ring
  have hsumExp : (∑ i, p i * Real.exp (θ * r i)) ≤ Real.exp (2 * H / t) :=
    hsum.trans (by simpa only [add_comm] using Real.add_one_le_exp (2 * H / t))
  have hdExp : 1 + δ ≤ Real.exp (1 / t) :=
    (add_le_add_right hδ 1).trans (by simpa only [add_comm] using Real.add_one_le_exp (1 / t))
  have hbase : (1 + δ) * (∑ i, p i * Real.exp (θ * r i)) ≤
      Real.exp ((1 + 2 * H) / t) := by
    rw [add_div, Real.exp_add]
    exact mul_le_mul hdExp hsumExp
      (Finset.sum_nonneg fun i _ ↦ mul_nonneg (hp i) (Real.exp_pos _).le)
      (Real.exp_pos _).le
  have hbase₀ : 0 ≤ (1 + δ) * (∑ i, p i * Real.exp (θ * r i)) :=
    mul_nonneg (by linarith only [hn.2.1])
      (Finset.sum_nonneg fun i _ ↦ mul_nonneg (hp i) (Real.exp_pos _).le)
  change Real.exp (-θ * (B / s)) *
    ((1 + δ) * ∑ i, p i * Real.exp (θ * r i)) ^ k ≤ _
  calc
    _ ≤ Real.exp (-θ * (B / s)) * Real.exp ((1 + 2 * H) / t) ^ k :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hbase₀ hbase _) (Real.exp_pos _).le
    _ ≤ Real.exp (-t) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hsDiv : s / t = t := by rw [← htt, mul_div_cancel_right₀ _ ht.ne']
      have hθDiv : θ / s = t := by rw [← hst, mul_comm, mul_div_cancel_right₀ _ hs.ne']
      have hK : (k : ℝ) * ((1 + 2 * H) / t) ≤ ((1 + 2 * H) * A) * t := by
        calc
          _ ≤ (A * s) * ((1 + 2 * H) / t) :=
            mul_le_mul_of_nonneg_right hk (div_nonneg (by positivity) ht.le)
          _ = _ := by
            rw [show A * s * ((1 + 2 * H) / t) = ((1 + 2 * H) * A) * (s / t) by ring, hsDiv]
      rw [show -θ * (B / s) = -B * (θ / s) by ring, hθDiv]
      dsimp [B]
      linarith only [hK]
    _ ≤ _ := hdecay
private noncomputable def pivotSupportMaleWeight {n : ℕ} (d : DiagonalScorePairs n) (i : Fin n) : ℝ :=
  (diagonalPairAt d i).1 / reverseDiagonalMaleTotal d
theorem measurable_pivotSupportMaleWeight {n : ℕ} (i : Fin n) :
    Measurable fun d : DiagonalScorePairs n ↦ pivotSupportMaleWeight d i := by
  have hcoord (j : Fin n) : Measurable fun d : DiagonalScorePairs n ↦ (diagonalPairAt d j).1 :=
    measurable_fst.comp (measurable_pi_apply _)
  exact (hcoord i).div (Finset.measurable_sum _ fun j _ ↦ hcoord j)
theorem pivotSupportMaleWeight_splitScorePairs {n : ℕ}
    (x : ScoreProfile n) (μ : Matching n) (i : Fin n) :
    pivotSupportMaleWeight (splitScorePairs μ x).1 i =
      maleSpouseScore x μ i / maleSpouseTotal x μ := by
  simp only [pivotSupportMaleWeight, reverseDiagonalMaleTotal, diagonalPairAt_splitScorePairs,
    maleSpouseScore, maleSpouseTotal]
theorem forwardSpouseWeight_splitScorePairs {n : ℕ}
    (x : ScoreProfile n) (μ : Matching n) (i : Fin n) :
    forwardSpouseWeight (splitScorePairs μ x).1 i =
      femaleSpouseScore x μ (μ i) / femaleSpouseTotal x μ := by
  rw [femaleSpouseTotal_eq_sum_byHusband μ x]
  simp only [forwardSpouseWeight, diagonalPairAt_splitScorePairs, femaleSpouseByHusband,
    femaleSpouseScore, Equiv.symm_apply_apply]
theorem sum_diagonalSpouseWeights_mul_le_of_goodPivotScoreGeometry {n : ℕ} (hn : 0 < n)
    {x : ScoreProfile n} (hx : x ∈ goodPivotScoreGeometry n) (μ : Matching n)
    (hμ : IsStable (profileOfScores x) μ) :
    (∑ i, forwardSpouseWeight (splitScorePairs μ x).1 i *
      pivotSupportMaleWeight (splitScorePairs μ x).1 i) ≤ 24 / (n : ℝ) := by
  simpa only [pivotSupportMaleWeight_splitScorePairs, forwardSpouseWeight_splitScorePairs] using
    sum_spouseShares_mul_le_of_goodPivotScoreGeometry hn hx μ hμ
theorem eventually_diagonalSupportMassTilt_pow_mul_le (A q : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ k : ℕ, (k : ℝ) ≤ A * Real.sqrt n →
      ∀ d ∈ pivotBaseDiagonalBand n,
        (∑ i, forwardSpouseWeight d i * pivotSupportMaleWeight d i) ≤ 24 / (n : ℝ) →
      Real.exp (-((n : ℝ) ^ (3 / 4 : ℝ)) * ((49 * A + 1) / Real.sqrt n)) *
        ((1 + coexposureSuccessorPerturbation n) * ∑ i,
          forwardSpouseWeight d i *
            Real.exp ((n : ℝ) ^ (3 / 4 : ℝ) * pivotSupportMaleWeight d i)) ^ k ≤
        (n : ℝ) ^ (-q) := by
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    eventually_supportMassTilt_pow_mul_le (A := A) (H := 24) (R := 2048) (by norm_num) q]
    with n hn h
  intro k hk d hd hmix
  have hY : 0 < pivotDiagonalFemaleTotal d :=
    (by norm_num : (0 : ℝ) < 2).trans_le hd.2.1
  have hXY := hd.2.2.2.1
  have hXY₀ : 0 < reverseDiagonalMaleTotal d * pivotDiagonalFemaleTotal d :=
    (div_pos (Nat.cast_pos.mpr hn) (by norm_num : (0 : ℝ) < 128)).trans_le hXY
  have hX : 0 < reverseDiagonalMaleTotal d := pos_of_mul_pos_left hXY₀ hY.le
  have hp (i : Fin n) : 0 ≤ forwardSpouseWeight d i := div_nonneg (hd.1 i).2.1 hY.le
  have hp₁ : ∑ i, forwardSpouseWeight d i = 1 := by
    simp only [forwardSpouseWeight, ← Finset.sum_div]
    exact div_self hY.ne'
  have hr (i : Fin n) :
      0 ≤ pivotSupportMaleWeight d i ∧ pivotSupportMaleWeight d i ≤ 2048 * Real.log n / n :=
    ⟨div_nonneg (hd.1 i).1.1 hX.le,
      normalizedMaleScore_le_of_spouseProduct hn hd.2.1 hXY (hd.2.2.2.2.2 i)⟩
  simpa only [show (1 + 2 * 24 : ℝ) = 49 by norm_num] using h k hk _ _ hp hp₁ hr hmix
theorem eventually_measure_pi_heavyForwardSupport_length_le (A q : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ k : ℕ, (k : ℝ) ≤ A * Real.sqrt n →
      ∀ d ∈ pivotBaseDiagonalBand n,
        (∑ i, forwardSpouseWeight d i * pivotSupportMaleWeight d i) ≤ 24 / (n : ℝ) →
      Measure.pi (normalizedStableScoreRowLaw d)
        {y : OffDiagonalScoreRows n |
          ∃ σ : Matching n,
            RealizesDirectedCycle (fun i ↦ forwardSuccessorOutcome d i (y i)) σ ∧
            σ.support.card = k ∧
            (49 * A + 1) / Real.sqrt n < ∑ i ∈ σ.support, pivotSupportMaleWeight d i} ≤
        ENNReal.ofReal ((n : ℝ) ^ (-q)) := by
  filter_upwards [eventually_coexposureSuccessorPerturbation_bounds,
    eventually_diagonalSupportMassTilt_pow_mul_le A q] with n hn htilt
  intro k hk d hd hmix
  let θ := (n : ℝ) ^ (3 / 4 : ℝ)
  let B := (49 * A + 1) / Real.sqrt (n : ℝ)
  let c := 1 + coexposureSuccessorPerturbation n
  let p := forwardSpouseWeight d
  let r := pivotSupportMaleWeight d
  have hθ : 0 < θ := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn.1) _
  have hc : 0 < c := by dsimp [c]; linarith only [hn.2.1]
  have hY : 0 < pivotDiagonalFemaleTotal d := (by norm_num : (0 : ℝ) < 2).trans_le hd.2.1
  have hX : 0 < reverseDiagonalMaleTotal d :=
    pos_of_mul_pos_left (lt_of_lt_of_le (div_pos (Nat.cast_pos.mpr hn.1)
      (by norm_num : (0 : ℝ) < 128)) hd.2.2.2.1) hY.le
  have hp (i : Fin n) : 0 ≤ p i := div_nonneg (hd.1 i).2.1 hY.le
  have hr (i : Fin n) : 0 ≤ r i := div_nonneg (hd.1 i).1.1 hX.le
  have hp₁ : ∑ i, p i = 1 := by
    simp only [p, forwardSpouseWeight, ← Finset.sum_div]
    exact div_self hY.ne'
  let w (j : Fin n) := ENNReal.ofReal (c * (p j * Real.exp (θ * r j)))
  have hw : ∑ j, w j = ENNReal.ofReal (c * ∑ j, p j * Real.exp (θ * r j)) := by
    rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg]
    exact fun j _ ↦ mul_nonneg hc.le (mul_nonneg (hp j) (Real.exp_nonneg _))
  have hw₀ : (∑ j, w j) ≠ 0 := by
    have hh : 1 ≤ ∑ j, p j * Real.exp (θ * r j) := by
      rw [← hp₁]
      exact Finset.sum_le_sum fun j _ ↦ le_mul_of_one_le_right (hp j)
        (Real.one_le_exp (mul_nonneg hθ.le (hr j)))
    rw [hw]
    exact ENNReal.ofReal_ne_zero_iff.mpr (mul_pos hc (zero_lt_one.trans_le hh))
  have hwt : (∑ j, w j) ≠ ∞ := by rw [hw]; exact ENNReal.ofReal_ne_top
  let : MeasurableSpace (Option (Fin n)) := ⊤
  let : DiscreteMeasurableSpace (Option (Fin n)) := ⟨fun _ ↦ trivial⟩
  let ν := normalizedStableScoreRowLaw d
  let out := forwardSuccessorOutcome d
  let g (i j : Fin n) (_ : {l : Fin n // i ≠ l} → ℝ × ℝ) := θ * r j
  have hx (i : Fin n) := (hd.1 i).1
  have hy (i : Fin n) : (diagonalPairAt d i).2 ∈ Icc 0 1 :=
    ⟨(hd.1 i).2.1, (hd.1 i).2.2.le⟩
  have hg : d ∈ goodDiagonalScores n := ⟨hd.2.1, hd.2.2.2.2.1, hd.2.2.2.2.2⟩
  let (i : Fin n) : IsProbabilityMeasure (ν i) :=
    normalizedStableScoreRowLaw_isProbabilityMeasure d i (hx i) hy
  have hout (i : Fin n) : Measurable (out i) := measurable_forwardSuccessorOutcome d i
  have harc (i j : Fin n) (hij : i ≠ j) :
      (∫⁻ x, tiltedForwardArc out g i j x ∂ν i) ≤ w j := by
    let E := {x | out i x = some j}
    have hE : MeasurableSet E := measurableSet_eq_fun (hout i) measurable_const
    have hM : ν i E ≤ ENNReal.ofReal (c * p j) := by
      have hmap : forwardSuccessorOutcomeLaw d i {some j} = ν i E :=
        Measure.map_apply (hout i) (measurableSet_singleton _)
      have hR : (ν i E).toReal ≤ c * p j := by
        rw [← hmap]
        exact forwardOutcomeWeight_some_le_of_goodDiagonalScores hg hx hy hn.2.2.2.1
          hn.2.2.2.2.1 hn.2.2.2.2.2 i ⟨j, hij⟩
      simpa only [ENNReal.ofReal_toReal (measure_ne_top (ν i) E)] using
        ENNReal.ofReal_le_ofReal hR
    change (∫⁻ x, E.indicator (fun _ ↦ ENNReal.ofReal (Real.exp (θ * r j))) x ∂ν i) ≤
      w j
    rw [lintegral_indicator hE, lintegral_const, Measure.restrict_apply_univ]
    calc
      _ ≤ ENNReal.ofReal (Real.exp (θ * r j)) * ENNReal.ofReal (c * p j) := by gcongr
      _ = _ := by
        rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
        congr 1
        ring
  have hsub :
      {y : OffDiagonalScoreRows n |
        ∃ σ : Matching n, RealizesDirectedCycle (fun i ↦ out i (y i)) σ ∧
          σ.support.card = k ∧ B < ∑ i ∈ σ.support, r i} ⊆
      {y : OffDiagonalScoreRows n |
        ∃ σ : Matching n, RealizesDirectedCycle (fun i ↦ out i (y i)) σ ∧
          σ.support.card = k ∧ θ * B < ∑ i ∈ σ.support, g i (σ i) (y i)} := by
    rintro y ⟨σ, hσ, hk', hmass⟩
    refine ⟨σ, hσ, hk', ?_⟩
    change θ * B < ∑ i ∈ σ.support, θ * r (σ i)
    rw [← Finset.mul_sum, σ.sum_comp σ.support r (fun _ hi ↦ Equiv.Perm.mem_support.mpr hi)]
    exact mul_lt_mul_of_pos_left hmass hθ
  refine (measure_mono hsub).trans ((measure_pi_exists_cycle_length_sum_gt_le ν out g hout
    (fun _ _ ↦ measurable_const) w hw₀ hwt harc k (θ * B)).trans ?_)
  rw [hw, ← ENNReal.ofReal_pow (mul_nonneg hc.le
    (Finset.sum_nonneg fun i _ ↦ mul_nonneg (hp i) (Real.exp_nonneg _))),
    ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← neg_mul]
  exact ENNReal.ofReal_le_ofReal (htilt k hk d hd hmix)
end AbunLP
end

-- PivotForwardIncrementTail
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace AbunLP
private theorem lintegral_scoreSuccessorPairEvent {ι : Type*} [Fintype ι] {x v : ℝ} {y : ι → ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1)
    (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ z in scoreSuccessorPairEvent x v y, f z.1.1
      ∂((rowNonblockingLaw x v).prod (Measure.pi fun j ↦ rowNonblockingLaw x (y j)))) =
      (∫⁻ u in Ioc x 1, f u * ENNReal.ofReal (scoreRowKernel Finset.univ y u)) *
        ENNReal.ofReal v := by
  let ν := rowNonblockingLaw x v
  let Q := Measure.pi fun j ↦ rowNonblockingLaw x (y j)
  let E := scoreSuccessorPairEvent x v y
  let T : Set (ℝ × ℝ) := Ioi x ×ˢ Iio v
  let G : ℝ → ℝ≥0∞ := fun u ↦ f u * ENNReal.ofReal (scoreRowKernel Finset.univ y u)
  have hE : MeasurableSet E := measurableSet_scoreSuccessorPairEvent _ _ _
  have hT : MeasurableSet T := measurableSet_Ioi.prod measurableSet_Iio
  have hG : Measurable G := hf.mul (continuous_scoreRowKernel _ _).measurable.ennreal_ofReal
  have hsupp : ∀ᵐ uv ∂ν, uv ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := by
    unfold ν rowNonblockingLaw unitScoreLaw
    rw [Measure.prod_restrict]
    exact ae_restrict_of_ae (ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc))
  change (∫⁻ z in E, f z.1.1 ∂(ν.prod Q)) = _
  rw [← lintegral_indicator hE, lintegral_prod (E.indicator (fun z ↦ f z.1.1))
    ((hf.comp measurable_fst.fst).indicator hE).aemeasurable]
  have hsection :
      (fun uv ↦ ∫⁻ z, E.indicator (fun z ↦ f z.1.1) (uv, z) ∂ Q) =ᵐ[ν]
        T.indicator (fun uv ↦ G uv.1) := by
    filter_upwards [hsupp] with uv hu
    simp_rw [← Set.indicator_comp_right (Prod.mk uv), Function.comp_def,
      lintegral_indicator_const (measurable_prodMk_left hE)]
    by_cases ht : uv ∈ T
    · have hsec : Prod.mk uv ⁻¹' E = Set.pi univ (fun j ↦ (Iio uv.1 ×ˢ Iio (y j))ᶜ) := by
        ext z
        simp only [mem_preimage, E, scoreSuccessorPairEvent, mem_ofPred_eq, Set.mem_pi, mem_univ,
          true_implies, mem_compl_iff, mem_prod, mem_Iio]
        exact ⟨fun h ↦ h.2.2, fun h ↦ ⟨ht.1, ht.2, h⟩⟩
      rw [hsec, Set.indicator_of_mem ht]
      change f uv.1 * Q _ = f uv.1 * ENNReal.ofReal (scoreRowKernel Finset.univ y uv.1)
      have hnonneg (j : ι) : 0 ≤ 1 - uv.1 * y j := sub_nonneg.mpr (calc
        uv.1 * y j ≤ 1 * y j := mul_le_mul_of_nonneg_right hu.1.2 (hy j).1
        _ ≤ 1 := by simpa using (hy j).2)
      dsimp only [Q]
      rw [Measure.pi_pi]
      simp only [rowNonblockingLaw_apply_avoiding ht.1.le hu.1 (hy _), scoreRowKernel,
        ENNReal.ofReal_prod_of_nonneg (fun j _ ↦ hnonneg j)]
    · have hsec : Prod.mk uv ⁻¹' E = ∅ :=
        eq_empty_iff_forall_notMem.mpr fun _ h ↦ ht ⟨h.1, h.2.1⟩
      rw [hsec, measure_empty, mul_zero, Set.indicator_of_notMem ht]
  rw [lintegral_congr_ae hsection, lintegral_indicator hT]
  have hsub : T ⊆ (Iio x ×ˢ Iio v : Set (ℝ × ℝ))ᶜ := by
    intro uv h h'
    exact (not_lt_of_ge (show x < uv.1 from h.1).le) (show uv.1 < x from h'.1)
  have hrestrict : ν.restrict T =
      (unitScoreLaw.restrict (Ioi x)).prod (unitScoreLaw.restrict (Iio v)) := by
    dsimp only [ν]
    rw [rowNonblockingLaw, Measure.restrict_restrict_of_subset hsub]
    exact (Measure.prod_restrict _ _).symm
  have hleft : unitScoreLaw.restrict (Ioi x) = volume.restrict (Ioc x 1) := by
    rw [unitScoreLaw, Measure.restrict_restrict measurableSet_Ioi]
    congr 1
    ext u
    change (x < u ∧ 0 ≤ u ∧ u ≤ 1) ↔ (x < u ∧ u ≤ 1)
    exact ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun h ↦ ⟨h.1, hx.1.trans h.1.le, h.2⟩⟩
  rw [hrestrict, hleft]
  rw [show (fun uv : ℝ × ℝ ↦ G uv.1) = (fun uv : ℝ × ℝ ↦ G uv.1 * 1) by simp]
  rw [lintegral_prod_mul hG.aemeasurable measurable_const.aemeasurable, lintegral_const,
    one_mul, Measure.restrict_apply_univ, unitScoreLaw_apply_Iio hv]
private theorem scoreRowKernel_le_at_mul_exp {ι : Type*} {J : Finset ι} {y : ι → ℝ} {x u : ℝ}
    (hy : ∀ j ∈ J, y j ∈ Icc (0 : ℝ) 1) (hx : 0 ≤ x) (hxu : x ≤ u) (hu : u ≤ 1) :
    scoreRowKernel J y u ≤
      scoreRowKernel J y x * Real.exp (-(u - x) * ∑ j ∈ J, y j) := by
  unfold scoreRowKernel
  have hnonneg (j : ι) (hj : j ∈ J) : 0 ≤ 1 - u * y j := by
    exact sub_nonneg.mpr ((mul_le_mul_of_nonneg_right hu (hy j hj).1).trans
      (by simpa only [one_mul] using (hy j hj).2))
  calc
    _ ≤ ∏ j ∈ J, (1 - x * y j) * Real.exp (-((u - x) * y j)) := by
      apply Finset.prod_le_prod hnonneg
      intro j hj
      have hden : 0 ≤ 1 - x * y j :=
        (hnonneg j hj).trans (sub_le_sub_left (mul_le_mul_of_nonneg_right hxu (hy j hj).1) 1)
      refine (show 1 - u * y j ≤ (1 - x * y j) * (1 - (u - x) * y j) by
        nlinarith only [mul_nonneg (mul_nonneg hx (hy j hj).1)
          (mul_nonneg (sub_nonneg.mpr hxu) (hy j hj).1)]).trans ?_
      exact mul_le_mul_of_nonneg_left (Real.one_sub_le_exp_neg _) hden
    _ = _ := by
      rw [Finset.prod_mul_distrib, ← Real.exp_sum]
      congr 2
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ ↦ (neg_mul (u - x) (y j)).symm
private theorem lintegral_exp_neg_increment_le {x a : ℝ} (ha : 0 < a) :
    (∫⁻ u in Ioc x 1, ENNReal.ofReal (Real.exp (-a * (u - x)))) ≤
      ENNReal.ofReal (1 / a) := by
  refine (lintegral_mono_set (μ := volume) Ioc_subset_Ioi_self).trans_eq ?_
  have he (u : ℝ) : Real.exp (-a * (u - x)) = Real.exp (a * x) * Real.exp (-a * u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hf : IntegrableOn (fun u : ℝ ↦ Real.exp (-a * (u - x))) (Ioi x) := by
    rw [show (fun u : ℝ ↦ Real.exp (-a * (u - x))) =
      (fun u : ℝ ↦ Real.exp (a * x) * Real.exp (-a * u)) from funext he]
    exact (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr ha) x).const_mul (Real.exp (a * x))
  rw [← ofReal_integral_eq_lintegral_ofReal hf (Eventually.of_forall fun _ ↦ Real.exp_nonneg _)]
  congr 1
  rw [show (fun u : ℝ ↦ Real.exp (-a * (u - x))) =
      (fun u : ℝ ↦ Real.exp (a * x) * Real.exp (-a * u)) from funext he,
    integral_const_mul, integral_exp_mul_Ioi (neg_lt_zero.mpr ha), neg_div_neg_eq,
    ← mul_div_assoc, ← Real.exp_add]
  rw [show a * x + -a * x = 0 by ring, Real.exp_zero]
private theorem sum_forwardCompetitors {n : ℕ} (y : Fin n → ℝ)
    (i : Fin n) (j : {j : Fin n // i ≠ j}) :
    (∑ k : {k : {k : Fin n // i ≠ k} // k ≠ j}, y k.val.val) =
      (∑ k, y k) - y i - y j.val := by
  classical
  have houter : (∑ k : {k : Fin n // i ≠ k}, y k.val) = (∑ k, y k) - y i := by
    rw [← Finset.sum_subtype (Finset.univ.erase i) (by simp [ne_comm]) y]
    linarith [Finset.sum_erase_add Finset.univ y (Finset.mem_univ i)]
  let f := fun k : {k : Fin n // i ≠ k} ↦ y k.val
  change (∑ k : {k : {k : Fin n // i ≠ k} // k ≠ j}, f k.val) =
    (∑ k, y k) - y i - f j
  rw [← Finset.sum_subtype (Finset.univ.erase j) (by simp) f]
  linarith [Finset.sum_erase_add Finset.univ f (Finset.mem_univ j)]
theorem lintegral_forwardSuccessor_exp_le {n : ℕ}
    (d : DiagonalScorePairs n) (i : Fin n) (j : {j : Fin n // i ≠ j})
    (hx : (diagonalPairAt d i).1 ∈ Icc (0 : ℝ) (1 / 2))
    (hy : ∀ k, (diagonalPairAt d k).2 ∈ Icc (0 : ℝ) 1)
    (hY : 4 ≤ ∑ k, (diagonalPairAt d k).2) :
    (∫⁻ r in scoreRowSuccessorEvent d i j,
      ENNReal.ofReal (Real.exp (((∑ k, (diagonalPairAt d k).2) / 4) *
        ((r j).1 - (diagonalPairAt d i).1))) ∂normalizedStableScoreRowLaw d i) ≤
      ENNReal.ofReal (8 * forwardSpouseWeight d j.val) := by
  classical
  let x := (diagonalPairAt d i).1
  let y (k : Fin n) := (diagonalPairAt d k).2
  let Y := ∑ k, y k
  let z (k : {k : {k : Fin n // i ≠ k} // k ≠ j}) := y k.val.val
  let K := scoreRowKernel Finset.univ z
  let m (k : {k : Fin n // i ≠ k}) := rowNonblockingLaw x (y k.val)
  let f (u : ℝ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp ((Y / 4) * (u - x)))
  let E := scoreSuccessorPairEvent x (y j.val) z
  let Erow := scoreRowSuccessorEvent d i j
  let ν := stableScoreRowLaw d i
  let νsplit := (m j).prod (Measure.pi fun k : {k // k ≠ j} ↦ m k.val)
  let split := fun r : {k : Fin n // i ≠ k} → ℝ × ℝ ↦
    (r j, fun k : {k // k ≠ j} ↦ r k.val)
  have hx' : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1, hx.2.trans (by norm_num)⟩
  have hY₀ : 0 < Y := (by norm_num : (0 : ℝ) < 4).trans_le hY
  have hf : Measurable f := by
    dsimp only [f]
    fun_prop
  have hK : 0 ≤ K x := by
    unfold K scoreRowKernel
    exact Finset.prod_nonneg fun k _ ↦ sub_nonneg.mpr
      ((mul_le_mul_of_nonneg_right hx'.2 (hy k.val.val).1).trans
        (by simpa only [one_mul] using (hy k.val.val).2))
  have hpres : MeasurePreserving split ν νsplit := measurePreserving_rowTargetAndCompetitors m j
  have hE : MeasurableSet E := measurableSet_scoreSuccessorPairEvent _ _ _
  have hErow : MeasurableSet Erow := measurableSet_scoreRowSuccessorEvent _ _ _
  have hsplit :
      (∫⁻ r in Erow, f (r j).1 ∂ν) = ∫⁻ u in E, f u.1.1 ∂νsplit := by
    rw [← lintegral_indicator hErow, ← lintegral_indicator hE]
    exact hpres.lintegral_comp ((hf.comp measurable_fst.fst).indicator hE)
  have hden (k : Fin n) : 1 / 2 ≤ 1 - x * y k := by
    have hxy : x * y k ≤ x := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (hy k).2 hx.1
    linarith only [hxy, hx.2]
  have hmass : ν univ = ENNReal.ofReal ((1 - x * y j.val) * K x) := by
    have hh := hpres.measure_preimage (s := univ) MeasurableSet.univ.nullMeasurableSet
    rw [preimage_univ] at hh
    rw [hh, ← univ_prod_univ]
    change (m j).prod (Measure.pi fun k : {k // k ≠ j} ↦ m k.val) (univ ×ˢ univ) = _
    rw [Measure.prod_prod, Measure.pi_univ]
    have hm (k : {k : Fin n // i ≠ k}) : m k univ = ENNReal.ofReal (1 - x * y k.val) :=
      rowNonblockingLaw_apply_univ hx' (hy k.val)
    have hden₀ (k : Fin n) : 0 ≤ 1 - x * y k :=
      (by norm_num : (0 : ℝ) ≤ 1 / 2).trans (hden k)
    simp_rw [hm]
    rw [← ENNReal.ofReal_prod_of_nonneg
        (fun (k : {k : {k : Fin n // i ≠ k} // k ≠ j}) _ ↦ hden₀ k.val.val),
      ← ENNReal.ofReal_mul (hden₀ j.val)]
    rfl
  have hS : Y / 2 ≤ ∑ k, z k := by
    change Y / 2 ≤ ∑ k : {k : {k : Fin n // i ≠ k} // k ≠ j}, y k.val.val
    rw [sum_forwardCompetitors y i j]
    linarith only [hY, (hy i).2, (hy j.val).2]
  have hI : (∫⁻ u in Ioc x 1, f u * ENNReal.ofReal (K u)) ≤
      ENNReal.ofReal (K x) * ENNReal.ofReal (4 / Y) := by
    let g (u : ℝ) := ENNReal.ofReal (Real.exp (-(Y / 4) * (u - x)))
    have hg : Measurable g := by
      dsimp only [g]
      fun_prop
    calc
      _ ≤ ∫⁻ u in Ioc x 1, ENNReal.ofReal (K x) * g u := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioc (a := x) (b := 1))]
          with u hu
        have hker := scoreRowKernel_le_at_mul_exp (J := Finset.univ) (y := z)
          (fun k _ ↦ hy k.val.val) hx.1 hu.1.le hu.2
        change K u ≤ K x * _ at hker
        have hexp : (Y / 4) * (u - x) + -(u - x) * ∑ k, z k ≤ -(Y / 4) * (u - x) := by
          nlinarith only [mul_nonneg (sub_nonneg.mpr hS) (sub_nonneg.mpr hu.1.le)]
        calc
          _ ≤ f u * ENNReal.ofReal (K x * Real.exp (-(u - x) * ∑ k, z k)) :=
            mul_le_mul_right (ENNReal.ofReal_le_ofReal hker) _
          _ ≤ _ := by
            rw [ENNReal.ofReal_mul hK, ← mul_assoc, mul_comm (f u), mul_assoc]
            apply mul_le_mul_right
            change ENNReal.ofReal (Real.exp _) * ENNReal.ofReal (Real.exp _) ≤ ENNReal.ofReal _
            rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
            exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hexp)
      _ = ENNReal.ofReal (K x) * (∫⁻ u in Ioc x 1, g u) := lintegral_const_mul _ hg
      _ ≤ _ := mul_le_mul_right
        ((lintegral_exp_neg_increment_le (x := x) (by positivity : 0 < Y / 4)).trans_eq
          (congrArg ENNReal.ofReal (by ring))) _
  have hun : (∫⁻ r in Erow, f (r j).1 ∂ν) ≤
      ν univ * ENNReal.ofReal (8 * forwardSpouseWeight d j.val) := by
    have he :
        (∫⁻ u in E, f u.1.1 ∂νsplit) =
          (∫⁻ u in Ioc x 1, f u * ENNReal.ofReal (K u)) * ENNReal.ofReal (y j.val) :=
      lintegral_scoreSuccessorPairEvent (y := z) hx' (hy j.val) (fun k ↦ hy k.val.val) hf
    rw [hsplit, he]
    refine (mul_le_mul_left hI _).trans ?_
    rw [hmass, ← ENNReal.ofReal_mul hK,
      ← ENNReal.ofReal_mul (mul_nonneg hK (by positivity)),
      ← ENNReal.ofReal_mul (mul_nonneg (by linarith [hden j.val]) hK)]
    apply ENNReal.ofReal_le_ofReal
    change K x * (4 / Y) * y j.val ≤ (1 - x * y j.val) * K x * (8 * (y j.val / Y))
    calc
      _ = (1 / 2) * (K x * (8 * (y j.val / Y))) := by ring
      _ ≤ (1 - x * y j.val) * (K x * (8 * (y j.val / Y))) :=
        mul_le_mul_of_nonneg_right (hden j.val)
          (mul_nonneg hK (mul_nonneg (by norm_num) (div_nonneg (hy j.val).1 hY₀.le)))
      _ = _ := by ring
  change (∫⁻ r in Erow, f (r j).1 ∂normalizedStableScoreRowLaw d i) ≤ _
  rw [normalizedStableScoreRowLaw, setLIntegral_smul_measure, smul_eq_mul]
  refine (mul_le_mul_right hun _).trans ?_
  rw [← mul_assoc]
  simpa only [one_mul] using mul_le_mul_left (ENNReal.inv_mul_le_one (ν univ))
    (ENNReal.ofReal (8 * forwardSpouseWeight d j.val))
private def forwardRowScoreIncrement {n : ℕ} (d : DiagonalScorePairs n) (i j : Fin n)
    (r : {k : Fin n // i ≠ k} → ℝ × ℝ) : ℝ :=
  if h : i ≠ j then (r ⟨j, h⟩).1 - (diagonalPairAt d i).1 else 0
theorem measurable_forwardRowScoreIncrement {n : ℕ} (d : DiagonalScorePairs n) (i j : Fin n) :
    Measurable (forwardRowScoreIncrement d i j) := by
  unfold forwardRowScoreIncrement
  by_cases h : i ≠ j
  · have hm : Measurable (fun r : {k : Fin n // i ≠ k} → ℝ × ℝ ↦ r ⟨j, h⟩) :=
      measurable_pi_apply _
    simpa only [dif_pos h] using hm.fst.sub_const (diagonalPairAt d i).1
  · simp only [dif_neg h]
    exact measurable_const
theorem forwardRowScoreIncrement_splitScorePairs {n : ℕ} (μ : Matching n)
    (x : ScoreProfile n) {i j : Fin n} (hij : i ≠ j) :
    forwardRowScoreIncrement (splitScorePairs μ x).1 i j
      (offDiagonalRowsEquiv n (splitScorePairs μ x).2 i) =
      x (.inl i) (μ j) - x (.inl i) (μ i) := by
  simp only [forwardRowScoreIncrement, dif_pos hij]
  change ((splitScorePairs μ x).2 ⟨(i, j), hij⟩).1 -
      (diagonalPairAt (splitScorePairs μ x).1 i).1 = _
  rw [splitScorePairs_offDiagonal_apply, diagonalPairAt_splitScorePairs]
theorem lintegral_tiltedForwardArc_increment_le {n : ℕ}
    (d : DiagonalScorePairs n) (i j : Fin n) (hij : i ≠ j)
    (hx : (diagonalPairAt d i).1 ∈ Icc (0 : ℝ) (1 / 2))
    (hy : ∀ k, (diagonalPairAt d k).2 ∈ Icc (0 : ℝ) 1)
    (hY : 4 ≤ pivotDiagonalFemaleTotal d) :
    (∫⁻ r, tiltedForwardArc (forwardSuccessorOutcome d)
      (fun i j r ↦ (pivotDiagonalFemaleTotal d / 4) * forwardRowScoreIncrement d i j r)
      i j r ∂normalizedStableScoreRowLaw d i) ≤
      ENNReal.ofReal (8 * forwardSpouseWeight d j) := by
  let a : {k : Fin n // i ≠ k} := ⟨j, hij⟩
  let f : ({k : Fin n // i ≠ k} → ℝ × ℝ) → ℝ≥0∞ := fun r ↦
    ENNReal.ofReal (Real.exp (((∑ k, (diagonalPairAt d k).2) / 4) *
      ((r a).1 - (diagonalPairAt d i).1)))
  have he :
      tiltedForwardArc (forwardSuccessorOutcome d)
          (fun i j r ↦ (pivotDiagonalFemaleTotal d / 4) * forwardRowScoreIncrement d i j r)
          i j =ᵐ[normalizedStableScoreRowLaw d i] (scoreRowSuccessorEvent d i a).indicator f := by
    filter_upwards [ae_injective_fst_normalizedStableScoreRowLaw d i] with r hr
    have hiff := forwardSuccessorOutcome_eq_some_iff d i r a hr
    by_cases h : r ∈ scoreRowSuccessorEvent d i a
    · have h' : forwardSuccessorOutcome d i r = some j := hiff.mpr h
      simp only [tiltedForwardArc, indicator_of_mem, mem_ofPred_eq, h', h,
        forwardRowScoreIncrement, dif_pos hij, f, a, pivotDiagonalFemaleTotal]
    · have h' : forwardSuccessorOutcome d i r ≠ some j := fun h' ↦ h (hiff.mp h')
      rw [tiltedForwardArc, indicator_of_notMem (show
        r ∉ {x | forwardSuccessorOutcome d i x = some j} from h'), indicator_of_notMem h]
  rw [lintegral_congr_ae he, lintegral_indicator (measurableSet_scoreRowSuccessorEvent _ _ _)]
  exact lintegral_forwardSuccessor_exp_le d i a hx hy hY
private def forwardIncrementOverflowRowEvent {n : ℕ}
    (d : DiagonalScorePairs n) (k : ℕ) (t : ℝ) : Set (OffDiagonalScoreRows n) :=
  {r | ∃ σ : Matching n,
    RealizesDirectedCycle (fun i ↦ forwardSuccessorOutcome d i (r i)) σ ∧
      σ.support.card = k ∧ t < pivotDiagonalFemaleTotal d *
        ∑ i ∈ σ.support, forwardRowScoreIncrement d i (σ i) (r i)}
theorem measure_forwardIncrementOverflowRowEvent_le {n : ℕ} (d : DiagonalScorePairs n)
    (hx : ∀ i, (diagonalPairAt d i).1 ∈ Icc (0 : ℝ) (1 / 2))
    (hy : ∀ i, (diagonalPairAt d i).2 ∈ Icc (0 : ℝ) 1)
    (hY : 4 ≤ pivotDiagonalFemaleTotal d) (k : ℕ) (t : ℝ) :
    Measure.pi (normalizedStableScoreRowLaw d) (forwardIncrementOverflowRowEvent d k t) ≤
      ENNReal.ofReal (Real.exp (-(t / 4))) * (8 : ℝ≥0∞) ^ k := by
  let : MeasurableSpace (Option (Fin n)) := ⊤
  have : DiscreteMeasurableSpace (Option (Fin n)) := ⟨fun _ ↦ trivial⟩
  have (i : Fin n) := normalizedStableScoreRowLaw_isProbabilityMeasure d i
    ⟨(hx i).1, (hx i).2.trans_lt (by norm_num)⟩ hy
  let Y := pivotDiagonalFemaleTotal d
  let q (j : Fin n) := ENNReal.ofReal (8 * forwardSpouseWeight d j)
  let g (i j : Fin n) := fun r ↦ (Y / 4) * forwardRowScoreIncrement d i j r
  have hY₀ : 0 < Y := (by norm_num : (0 : ℝ) < 4).trans_le hY
  have hq₀ (j : Fin n) : 0 ≤ 8 * forwardSpouseWeight d j :=
    mul_nonneg (by norm_num) (div_nonneg (hy j).1 hY₀.le)
  have hq : (∑ j, q j) = 8 := by
    unfold q
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ ↦ hq₀ j), ← Finset.mul_sum]
    have h : (∑ j, forwardSpouseWeight d j) = 1 := by
      unfold forwardSpouseWeight
      rw [← Finset.sum_div]
      exact div_self hY₀.ne'
    rw [h, mul_one]
    norm_num
  have he : forwardIncrementOverflowRowEvent d k t = {r | ∃ σ : Matching n,
      RealizesDirectedCycle (fun i ↦ forwardSuccessorOutcome d i (r i)) σ ∧
      σ.support.card = k ∧ t / 4 < ∑ i ∈ σ.support, g i (σ i) (r i)} := by
    ext r
    unfold forwardIncrementOverflowRowEvent
    simp only [mem_ofPred_eq, g, ← Finset.mul_sum]
    refine exists_congr fun _ ↦ and_congr_right fun _ ↦ and_congr_right fun _ ↦ ?_
    change t < Y * _ ↔ t / 4 < (Y / 4) * _
    rw [show ∀ z : ℝ, (Y / 4) * z = Y * z / 4 from fun z ↦ by ring]
    exact (div_lt_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 4)).symm
  rw [he, ← hq]
  exact measure_pi_exists_cycle_length_sum_gt_le (normalizedStableScoreRowLaw d)
    (forwardSuccessorOutcome d) g (measurable_forwardSuccessorOutcome d)
    (fun i j ↦ (measurable_forwardRowScoreIncrement d i j).const_mul _)
    q (by rw [hq]; norm_num) (by rw [hq]; norm_num)
    (fun i j hij ↦ lintegral_tiltedForwardArc_increment_le d i j hij (hx i) hy hY) k (t / 4)
theorem eventually_measure_forwardIncrementOverflowRowEvent_le {A p : ℝ} :
    ∀ᶠ n : ℕ in atTop, ∀ d : DiagonalScorePairs n, d ∈ pivotBaseDiagonalBand n →
      (n : ℝ) ^ (1 / 10 : ℝ) ≤ pivotDiagonalFemaleTotal d →
      ∀ k : ℕ, (k : ℝ) ≤ A * Real.sqrt (n : ℝ) →
        Measure.pi (normalizedStableScoreRowLaw d)
          (forwardIncrementOverflowRowEvent d k ((4 * (8 * A + 1)) * Real.sqrt (n : ℝ))) ≤
          ENNReal.ofReal ((n : ℝ) ^ (-p)) := by
  let hcast : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog (a C : ℝ) (ha : 0 < a) :
      Tendsto (fun n : ℕ ↦ C * (Real.log n / (n : ℝ) ^ a)) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_apply] using tendsto_const_nhds.mul
      ((isLittleO_log_rpow_atTop ha).tendsto_div_nhds_zero.comp hcast)
  have h4 := Tendsto.eventually_ge_atTop
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp hcast) 4
  filter_upwards [eventually_ge_atTop (1 : ℕ), h4,
    (hlog (1 / 10) 16 (by norm_num)).eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2),
    (hlog (1 / 2) p (by norm_num)).eventually_lt_const (by norm_num : (0 : ℝ) < 1)]
    with n hn h4 hsmall hpow
  intro d hd hband k hk
  have hn₀ : 0 < (n : ℝ) := by exact_mod_cast (zero_lt_one.trans_le hn)
  have hlog₀ : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hY : 4 ≤ pivotDiagonalFemaleTotal d := h4.trans hband
  have hX (i : Fin n) : (diagonalPairAt d i).1 ∈ Icc (0 : ℝ) (1 / 2) := by
    refine ⟨(hd.1 i).1.1, (hd.2.2.2.2.2 i).trans ?_⟩
    calc
      _ ≤ 8 * Real.log n / ((n : ℝ) ^ (1 / 10 : ℝ) / 2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
      _ = 16 * (Real.log n / (n : ℝ) ^ (1 / 10 : ℝ)) := by ring
      _ ≤ _ := hsmall.le
  have hy (i : Fin n) : (diagonalPairAt d i).2 ∈ Icc (0 : ℝ) 1 :=
    ⟨(hd.1 i).2.1, (hd.1 i).2.2.le⟩
  have hpow' : p * Real.log n ≤ Real.sqrt (n : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    have h := (div_lt_iff₀ (Real.rpow_pos_of_pos hn₀ (1 / 2))).mp
      (show p * Real.log n / (n : ℝ) ^ (1 / 2 : ℝ) < 1 from
        by simpa only [mul_div_assoc] using hpow)
    simpa only [one_mul] using h.le
  have hexp : (8 : ℝ) ≤ Real.exp 8 := by
    linarith only [Real.add_one_le_exp (8 : ℝ)]
  refine (measure_forwardIncrementOverflowRowEvent_le d hX hy hY k _).trans ?_
  calc
    _ ≤ ENNReal.ofReal (Real.exp (-((4 * (8 * A + 1) * Real.sqrt (n : ℝ)) / 4))) *
        (ENNReal.ofReal (Real.exp 8)) ^ k := by
      apply mul_le_mul_right
      apply pow_le_pow_left'
      exact (show (8 : ℝ≥0∞) = ENNReal.ofReal (8 : ℝ) by norm_num) ▸
        ENNReal.ofReal_le_ofReal hexp
    _ ≤ _ := by
      rw [← ENNReal.ofReal_pow (Real.exp_nonneg _), ← Real.exp_nat_mul,
        ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add, Real.rpow_def_of_pos hn₀]
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      nlinarith only [hk, hpow']
end AbunLP
end

-- PivotEligibleAbundance
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace AbunLP
private def pivotCutoffDiagonal (n : ℕ) : Set (DiagonalScorePairs n) :=
  {d | d ∈ pivotBaseDiagonalBand n ∧
    (n : ℝ) ^ (1 / 10 : ℝ) ≤ pivotDiagonalFemaleTotal d ∧
    (∑ i, forwardSpouseWeight d i * pivotSupportMaleWeight d i) ≤ 24 / (n : ℝ)}
theorem measurableSet_pivotCutoffDiagonal (n : ℕ) :
    MeasurableSet (pivotCutoffDiagonal n) := by
  have hy (i : Fin n) : Measurable (fun d : DiagonalScorePairs n ↦ (diagonalPairAt d i).2) :=
    measurable_snd.comp (measurable_pi_apply _)
  have hY : Measurable (@pivotDiagonalFemaleTotal n) :=
    Finset.measurable_sum _ fun i _ ↦ hy i
  have hmix : Measurable (fun d : DiagonalScorePairs n ↦ ∑ i,
      forwardSpouseWeight d i * pivotSupportMaleWeight d i) :=
    Finset.measurable_sum _ fun i _ ↦ ((hy i).div hY).mul (measurable_pivotSupportMaleWeight i)
  refine (measurableSet_pivotBaseDiagonalBand n).inter
    ((measurableSet_le measurable_const hY).inter (measurableSet_le hmix measurable_const))
theorem splitScorePairs_mem_pivotCutoffDiagonal {n : ℕ} (hn : 0 < n) {x : ScoreProfile n}
    (hg : x ∈ goodPivotScoreGeometry n) (μ : Matching n) (hμ : IsStable (profileOfScores x) μ)
    (hband : femaleSpouseTotal x μ ∈ Icc ((n : ℝ) ^ (1 / 10 : ℝ)) ((n : ℝ) ^ (2 / 5 : ℝ))) :
    (splitScorePairs μ x).1 ∈ pivotCutoffDiagonal n := by
  refine ⟨(hg.1.2.2 μ hμ hband.2).1, ?_, ?_⟩
  · rw [pivotDiagonalFemaleTotal_splitScorePairs]
    exact hband.1
  · exact sum_diagonalSpouseWeights_mul_le_of_goodPivotScoreGeometry hn hg μ hμ
private def badShortPivotAt {n : ℕ} (V : ScoreProfile n → Matching n → Matching n → ℝ)
    (A t : ℝ) (μ : Matching n) : Set (ScoreProfile n) :=
  {x | ∃ σ : Matching n, IsExposedRotation (profileOfScores x) μ σ ∧
    (σ.support.card : ℝ) ≤ A * Real.sqrt (n : ℝ) ∧ t < V x μ σ}
theorem measurableSet_badShortPivotAt {n : ℕ}
    {V : ScoreProfile n → Matching n → Matching n → ℝ} (μ : Matching n)
    (hV : ∀ σ, Measurable (fun x ↦ V x μ σ)) (A t : ℝ) :
    MeasurableSet (badShortPivotAt V A t μ) := by
  unfold badShortPivotAt
  simp only [ofPred_exists, ofPred_and]
  refine MeasurableSet.iUnion fun σ ↦ (measurable_profileOfScores n
    (MeasurableSet.of_discrete : MeasurableSet {p : Profile n | IsExposedRotation p μ σ})).inter
    ((MeasurableSet.const _).inter (measurableSet_lt measurable_const (hV σ)))
private def badShortStablePivot {n : ℕ} (V : ScoreProfile n → Matching n → Matching n → ℝ)
    (A t : ℝ) : Set (ScoreProfile n) :=
  {x | ∃ μ : Matching n, IsScoreStable x μ ∧ (splitScorePairs μ x).1 ∈ pivotCutoffDiagonal n ∧
    x ∈ badShortPivotAt V A t μ}
theorem measure_badShortStablePivot_le {n : ℕ}
    {V : ScoreProfile n → Matching n → Matching n → ℝ} {A t : ℝ}
    (hV : ∀ μ σ, Measurable (fun x ↦ V x μ σ)) {e : ℝ≥0∞} (he : e ≠ ∞)
    (hrow : ∀ μ : Matching n, ∀ᵐ d ∂diagonalScoreLaw n, d ∈ pivotCutoffDiagonal n →
      ∀ k ∈ Finset.Icc 2 n, (k : ℝ) ≤ A * Real.sqrt (n : ℝ) →
        (Measure.pi (normalizedStableScoreRowLaw d))
          {r | let x := (splitScorePairs μ).symm (d, (offDiagonalRowsEquiv n).symm r)
               ∃ σ : Matching n, IsExposedRotation (profileOfScores x) μ σ ∧
                 σ.support.card = k ∧ t < V x μ σ} ≤ e) :
    continuousScoreLaw n (badShortStablePivot V A t) ≤
      ENNReal.ofReal (expectedNumStableMatchings n) * ((n : ℝ≥0∞) * e) := by
  classical
  refine measure_exists_scoreStable_diagonal_event_le _ _ _ fun μ ↦ ?_
  apply measure_scoreStable_diagonal_scoreEvent_le μ (measurableSet_pivotCutoffDiagonal n)
    (fun _ hd ↦ ⟨fun i ↦ (hd.1.1 i).1, fun i ↦ Ico_subset_Icc_self (hd.1.1 i).2⟩)
    (measurableSet_badShortPivotAt μ (hV μ) A t)
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) he)
  filter_upwards [hrow μ] with d hd hD
  let S := (Finset.Icc 2 n).filter (fun k : ℕ ↦ (k : ℝ) ≤ A * Real.sqrt (n : ℝ))
  let R := fun r : OffDiagonalScoreRows n ↦ (splitScorePairs μ).symm (d, (offDiagonalRowsEquiv n).symm r)
  let E (k : ℕ) := {r | ∃ σ : Matching n, IsExposedRotation (profileOfScores (R r)) μ σ ∧
    σ.support.card = k ∧ t < V (R r) μ σ}
  have hsub : {r | R r ∈ badShortPivotAt V A t μ} ⊆ ⋃ k ∈ S, E k := by
    rintro r ⟨σ, hσ, hA, ht⟩
    have hk : σ.support.card ∈ Finset.Icc 2 n := Finset.mem_Icc.mpr
      ⟨(IsExposedRotation.isCycle hσ).two_le_card_support, (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)⟩
    exact mem_iUnion.mpr ⟨_, mem_iUnion.mpr ⟨Finset.mem_filter.mpr ⟨hk, hA⟩, σ, hσ, rfl, ht⟩⟩
  have hcard : S.card ≤ n := by
    calc
      _ ≤ (Finset.Icc 2 n).card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = n + 1 - 2 := Nat.card_Icc 2 n
      _ ≤ n := by omega
  calc
    _ ≤ (Measure.pi (normalizedStableScoreRowLaw d)) (⋃ k ∈ S, E k) := measure_mono hsub
    _ ≤ ∑ k ∈ S, (Measure.pi (normalizedStableScoreRowLaw d)) (E k) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _k ∈ S, e := Finset.sum_le_sum fun k hk ↦
      hd hD k (Finset.mem_filter.mp hk).1 (Finset.mem_filter.mp hk).2
    _ ≤ _ := by
      rw [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_left (Nat.cast_le.mpr hcard) _
theorem tendsto_measure_badShortStablePivot_of_perLength [LPHyp3_3] {E : ∀ n, Set (ScoreProfile n)}
    (hE : ∀ᶠ n : ℕ in atTop, continuousScoreLaw n (E n) ≤
      ENNReal.ofReal (expectedNumStableMatchings n) *
        ((n : ℝ≥0∞) * ENNReal.ofReal ((n : ℝ) ^ (-5 : ℝ)))) :
    Tendsto (fun n ↦ continuousScoreLaw n (E n)) atTop (𝓝 0) := by
  have hzero : Tendsto (fun n : ℕ ↦ ENNReal.ofReal ((n : ℝ) ^ (-2 : ℝ))) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero, Function.comp_def] using ENNReal.tendsto_ofReal
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2)).comp
        tendsto_natCast_atTop_atTop)
  refine tendsto_const_nhds.squeeze' hzero (Eventually.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [hE, eventually_expectedNumStableMatchings_le_sizeSq,
    eventually_gt_atTop (0 : ℕ)] with n h hmean hnpos
  have hpos : 0 < (n : ℝ) := Nat.cast_pos.mpr hnpos
  refine h.trans ((mul_le_mul_left (ENNReal.ofReal_le_ofReal hmean) _).trans_eq ?_)
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hpos.le,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  calc
    _ = (n : ℝ) ^ (2 : ℝ) * ((n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-5 : ℝ)) := by
      rw [Real.rpow_two, Real.rpow_one]
    _ = _ := by rw [← Real.rpow_add hpos, ← Real.rpow_add hpos]; norm_num
theorem measurable_pivotMaleSupportMass {n : ℕ} (μ σ : Matching n) :
    Measurable (fun x : ScoreProfile n ↦ pivotMaleSupportMass x μ σ) := by
  unfold pivotMaleSupportMass
  exact Finset.measurable_sum _ fun i _ ↦ by
    have hi : Measurable (fun x : ScoreProfile n ↦
        pivotSupportMaleWeight (splitScorePairs μ x).1 i) :=
      (measurable_pivotSupportMaleWeight i).comp (measurable_fst.comp (splitScorePairs μ).measurable)
    simpa only [pivotSupportMaleWeight_splitScorePairs] using hi
theorem measurable_pivotNormalizedForwardIncrement {n : ℕ} (μ σ : Matching n) :
    Measurable (fun x : ScoreProfile n ↦ pivotNormalizedForwardIncrement x μ σ) := by
  unfold pivotNormalizedForwardIncrement
  refine (measurable_femaleSpouseTotal μ).mul (Finset.measurable_sum _ fun i _ ↦ ?_)
  have hi : Measurable (fun x : ScoreProfile n ↦ x (.inl i)) := measurable_pi_apply _
  exact ((measurable_pi_apply (μ (σ i))).comp hi).sub ((measurable_pi_apply (μ i)).comp hi)
theorem tendsto_measure_badShortStablePivotMaleMass [LPHyp3_3] (A : ℝ) :
    Tendsto (fun n ↦ continuousScoreLaw n
      (badShortStablePivot pivotMaleSupportMass A ((49 * A + 1) / Real.sqrt (n : ℝ))))
      atTop (𝓝 0) := by
  apply tendsto_measure_badShortStablePivot_of_perLength
  filter_upwards [eventually_measure_pi_heavyForwardSupport_length_le A 5] with n hmass
  refine measure_badShortStablePivot_le measurable_pivotMaleSupportMass ENNReal.ofReal_ne_top
    fun μ ↦ ?_
  filter_upwards [ae_diagonal_ae_normalizedStableRows μ] with d hrows hd k _ hk
  refine (measure_mono_ae ?_).trans (hmass k hk d hd.1 hd.2.2)
  filter_upwards [hrows (fun i ↦ (hd.1.1 i).1) (fun i ↦ Ico_subset_Icc_self (hd.1.1 i).2)]
    with r hr hbad
  obtain ⟨σ, hσ, hk', hcut⟩ := hbad
  let x := (splitScorePairs μ).symm (d, (offDiagonalRowsEquiv n).symm r)
  have hsplit : (splitScorePairs μ x).1 = d := by simp [x]
  have hmass' : pivotMaleSupportMass x μ σ = ∑ i ∈ σ.support, pivotSupportMaleWeight d i := by
    simp_rw [pivotMaleSupportMass, ← pivotSupportMaleWeight_splitScorePairs, hsplit]
  exact ⟨σ, (realizesDirectedCycle_forwardOutcome_iff μ d r σ hr.2 hr.1).mpr hσ,
    hk', hmass' ▸ hcut⟩
theorem tendsto_measure_badShortStablePivotForwardIncrement [LPHyp3_3] (A : ℝ) :
    Tendsto (fun n ↦ continuousScoreLaw n
      (badShortStablePivot pivotNormalizedForwardIncrement A
        ((4 * (8 * A + 1)) * Real.sqrt (n : ℝ)))) atTop (𝓝 0) := by
  apply tendsto_measure_badShortStablePivot_of_perLength
  filter_upwards [eventually_measure_forwardIncrementOverflowRowEvent_le (A := A) (p := 5)]
    with n hinc
  refine measure_badShortStablePivot_le measurable_pivotNormalizedForwardIncrement
    ENNReal.ofReal_ne_top fun μ ↦ ?_
  filter_upwards [ae_diagonal_ae_normalizedStableRows μ] with d hrows hd k _ hk
  refine (measure_mono_ae ?_).trans (hinc d hd.1 hd.2.1 k hk)
  filter_upwards [hrows (fun i ↦ (hd.1.1 i).1) (fun i ↦ Ico_subset_Icc_self (hd.1.1 i).2)]
    with r hr hbad
  obtain ⟨σ, hσ, hk', hcut⟩ := hbad
  let x := (splitScorePairs μ).symm (d, (offDiagonalRowsEquiv n).symm r)
  have hsplit : splitScorePairs μ x = (d, (offDiagonalRowsEquiv n).symm r) :=
    (splitScorePairs μ).apply_symm_apply _
  have hd' : (splitScorePairs μ x).1 = d := congrArg Prod.fst hsplit
  have hr' : offDiagonalRowsEquiv n (splitScorePairs μ x).2 = r := by
    rw [congrArg Prod.snd hsplit, MeasurableEquiv.apply_symm_apply]
  have hval : pivotNormalizedForwardIncrement x μ σ =
      pivotDiagonalFemaleTotal d *
        ∑ i ∈ σ.support, forwardRowScoreIncrement d i (σ i) (r i) := by
    unfold pivotNormalizedForwardIncrement
    rw [← pivotDiagonalFemaleTotal_splitScorePairs μ x, hd']
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have he := forwardRowScoreIncrement_splitScorePairs μ x
      (Equiv.Perm.mem_support.mp hi).symm
    rw [hd', hr'] at he
    exact he.symm
  exact ⟨σ, (realizesDirectedCycle_forwardOutcome_iff μ d r σ hr.2 hr.1).mpr hσ,
    hk', hval ▸ hcut⟩
private def locallyEligiblePivotAbundance (n : ℕ) (b A B : ℝ) : Set (ScoreProfile n) :=
  {x | ∃ S : Finset (Rotation (profileOfScores x) (DAState.matching (profileOfScores x))),
    Real.sqrt n * Real.log n / (10 * A) ≤ (S.card : ℝ) ∧
    ∀ r ∈ S, IsLocallyEligiblePivot b A B x
      (singletonRotationAnchor (DAState.isManOptimal_matching (profileOfScores x)) r).val
      r.val.cycle}
theorem measurableSet_locallyEligiblePivotAbundance (n : ℕ) (b A B : ℝ) :
    MeasurableSet (locallyEligiblePivotAbundance n b A B) := by
  let F (p : Profile n) : Set (ScoreProfile n) :=
    {x | ∃ S : Finset (Rotation p (DAState.matching p)),
      Real.sqrt n * Real.log n / (10 * A) ≤ (S.card : ℝ) ∧
      ∀ r ∈ S, IsLocallyEligiblePivot b A B x
        (singletonRotationAnchor (DAState.isManOptimal_matching p) r).val r.val.cycle}
  have hF (p : Profile n) : MeasurableSet (F p) := by
    unfold F
    simp only [ofPred_exists, ofPred_and, ofPred_forall]
    refine MeasurableSet.iUnion fun S ↦ (MeasurableSet.const _).inter
      (MeasurableSet.iInter fun r ↦ MeasurableSet.iInter fun _ ↦ ?_)
    exact measurableSet_isLocallyEligiblePivot b A B _ _
  have he : locallyEligiblePivotAbundance n b A B =
      ⋃ p, profileOfScores ⁻¹' {p} ∩ F p := by
    ext x
    constructor
    · intro hx
      exact mem_iUnion.mpr ⟨profileOfScores x, rfl, hx⟩
    · intro hx
      obtain ⟨p, hp, h⟩ := mem_iUnion.mp hx
      have hp' : profileOfScores x = p := hp
      subst p
      exact h
  rw [he]
  exact MeasurableSet.iUnion fun p ↦
    ((measurable_profileOfScores n) (measurableSet_singleton p)).inter (hF p)
theorem locallyEligiblePivotAbundance_of_good {n : ℕ} (hn : 0 < n) {b A B : ℝ}
    {x : ScoreProfile n} (ht : ∀ row, Function.Injective (x row))
    (hG : x ∈ goodPivotScoreGeometry n)
    (hE : x ∈ scoreWalkAnchorAbundanceAtCutoffs n (b * Real.sqrt n) A)
    (hBm : 49 * A + 1 ≤ B) (hBi : 4 * (8 * A + 1) ≤ B)
    (hM : x ∉ badShortStablePivot pivotMaleSupportMass A ((49 * A + 1) / Real.sqrt n))
    (hI : x ∉ badShortStablePivot pivotNormalizedForwardIncrement A
      ((4 * (8 * A + 1)) * Real.sqrt n)) :
    x ∈ locallyEligiblePivotAbundance n b A B := by
  obtain ⟨S, hcard, hS⟩ := hE
  refine ⟨S, hcard, fun r hr ↦ ?_⟩
  let hopt := DAState.isManOptimal_matching (profileOfScores x)
  let m := singletonRotationAnchor hopt r
  let σ := r.val.cycle
  have hσ : IsSoleForwardExposedRotation (profileOfScores x) m.val σ :=
    ⟨(isExposedRotation_singletonRotationAnchor_iff hopt r σ).mpr rfl,
      fun τ hτ ↦ (isExposedRotation_singletonRotationAnchor_iff hopt r τ).mp hτ⟩
  obtain ⟨hlo, hhi, hband⟩ := hS r hr
  have hd := splitScorePairs_mem_pivotCutoffDiagonal hn hG m.val m.property hband
  have hstable := (isStable_profileOfScores_iff ht m.val).mp m.property
  have hm : pivotMaleSupportMass x m.val σ ≤ (49 * A + 1) / Real.sqrt n :=
    le_of_not_gt fun h ↦ hM ⟨m.val, hstable, hd, σ, hσ.1, hhi, h⟩
  have hi : pivotNormalizedForwardIncrement x m.val σ ≤ (4 * (8 * A + 1)) * Real.sqrt n :=
    le_of_not_gt fun h ↦ hI ⟨m.val, hstable, hd, σ, hσ.1, hhi, h⟩
  exact isLocallyEligiblePivot_of_good hn ht hG m.property hσ hband ⟨hlo, hhi⟩
    (hm.trans (div_le_div_of_nonneg_right hBm (Real.sqrt_nonneg _)))
    (hi.trans (mul_le_mul_of_nonneg_right hBi (Real.sqrt_nonneg _)))
theorem exists_eventually_measure_badLocallyEligiblePivotAbundance_le [LPHyp1_0] [LPHyp2_0] [LPHyp2_1] [LPHyp3_0] [LPHyp3_1] [LPHyp3_2] [LPHyp3_3] {η : ℝ}
    (hη : 0 < η) :
    ∃ b A B : ℝ, 0 < b ∧ b ≤ 1 ∧ 1 ≤ A ∧ 0 < B ∧ ∀ᶠ n : ℕ in atTop,
      continuousScoreLaw n (locallyEligiblePivotAbundance n b A B)ᶜ ≤ ENNReal.ofReal η := by
  obtain ⟨b, A, hb, hb₁, hA, hband⟩ :=
    exists_eventually_measure_badScoreWalkAnchorAbundance_le (η := η / 2) (by positivity)
  let B := max (49 * A + 1) (4 * (8 * A + 1))
  have hB : 0 < B := lt_of_lt_of_le (by linarith : 0 < 49 * A + 1) (le_max_left _ _)
  refine ⟨b, A, B, hb, hb₁, hA, hB, ?_⟩
  have hrare := tendsto_measure_badPivotScoreGeometry_zero.add
    ((tendsto_measure_badShortStablePivotMaleMass A).add
      (tendsto_measure_badShortStablePivotForwardIncrement A))
  simp only [add_zero] at hrare
  filter_upwards [hband, hrare.eventually_lt_const (ENNReal.ofReal_pos.mpr
    (show 0 < η / 2 by positivity)), eventually_gt_atTop (0 : ℕ)] with n hn hsmall hnpos
  let E := scoreWalkAnchorAbundanceAtCutoffs n (b * Real.sqrt n) A
  let G := goodPivotScoreGeometry n
  let M : Set (ScoreProfile n) :=
    badShortStablePivot pivotMaleSupportMass A ((49 * A + 1) / Real.sqrt (n : ℝ))
  let I : Set (ScoreProfile n) := badShortStablePivot pivotNormalizedForwardIncrement A
    ((4 * (8 * A + 1)) * Real.sqrt (n : ℝ))
  let U : Set (ScoreProfile n) := Eᶜ ∪ (Gᶜ ∪ (M ∪ I))
  have hsub : (locallyEligiblePivotAbundance n b A B)ᶜ ≤ᵐ[continuousScoreLaw n] U := by
    filter_upwards [ae_injective_rows n] with x ht hbad
    by_contra hx
    have hE : x ∈ E := by
      by_contra h
      exact hx (Or.inl h)
    have hG : x ∈ G := by
      by_contra h
      exact hx (Or.inr (Or.inl h))
    have hM : x ∉ M := fun h ↦ hx (Or.inr (Or.inr (Or.inl h)))
    have hI : x ∉ I := fun h ↦ hx (Or.inr (Or.inr (Or.inr h)))
    exact hbad (locallyEligiblePivotAbundance_of_good hnpos ht hG hE
      (le_max_left _ _) (le_max_right _ _) hM hI)
  calc
    _ ≤ continuousScoreLaw n (Eᶜ ∪ (Gᶜ ∪ (M ∪ I))) := measure_mono_ae hsub
    _ ≤ continuousScoreLaw n Eᶜ +
        (continuousScoreLaw n Gᶜ + (continuousScoreLaw n M + continuousScoreLaw n I)) := by
      exact (measure_union_le Eᶜ _).trans (add_le_add le_rfl
        ((measure_union_le Gᶜ _).trans (add_le_add le_rfl (measure_union_le M I))))
    _ ≤ ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) := add_le_add hn hsmall.le
    _ = _ := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
theorem exists_eligiblePivotAbundance_and_supportCoefficient [LPHyp1_0] [LPHyp2_0] [LPHyp2_1] [LPHyp3_0] [LPHyp3_1] [LPHyp3_2] [LPHyp3_3] {η : ℝ} (hη : 0 < η) :
    ∃ b A B κ : ℝ, 0 < b ∧ b ≤ 1 ∧ 1 ≤ A ∧ 0 < B ∧ 0 < κ ∧ κ < b ∧
      24 * κ ^ 2 / 2 + (B + 1) * κ ≤ 1 / 4 ∧
      Real.exp (κ * (2 * (1 + B))) * (2 * κ * (B / (1 / 128))) ≤ 3 / 32 ∧
      ∀ᶠ n : ℕ in atTop,
        continuousScoreLaw n (locallyEligiblePivotAbundance n b A B)ᶜ ≤ ENNReal.ofReal η := by
  obtain ⟨b, A, B, hb, hb₁, hA, hB, hab⟩ :=
    exists_eventually_measure_badLocallyEligiblePivotAbundance_le hη
  obtain ⟨κ, hκ, hκb, hlabel, hcompat⟩ := exists_localPivotSupportCoefficient hb hB.le
  exact ⟨b, A, B, κ, hb, hb₁, hA, hB, hκ, hκb, hlabel, hcompat, hab⟩
end AbunLP
end

-- PivotAggregateMean
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace AbunLP
variable {n : ℕ}
private noncomputable def stablePivotMeanTerm (b A B : ℝ) (K L : ℕ)
    (x : ScoreProfile n) (i : Matching n × Matching n) : ℝ :=
  {y | IsScoreStable y i.1}.indicator (localPivotConditionalMean b A B K L i.1 i.2) x
private noncomputable def totalLocalPivotConditionalMean (b A B : ℝ) (K L : ℕ)
    (x : ScoreProfile n) : ℝ :=
  ∑ i : Matching n × Matching n, stablePivotMeanTerm b A B K L x i
theorem totalLocalPivotConditionalMean_ge_of_abundance {b A B : ℝ} {K L : ℕ}
    {x : ScoreProfile n} (ht : ∀ row, Function.Injective (x row))
    (h : ∀ μ ρ : Matching n, IsScoreStable x μ →
      localPivotMeanFloor b A B K μ ρ x ≤ localPivotConditionalMean b A B K L μ ρ x)
    (hE : x ∈ locallyEligiblePivotAbundance n b A B) :
    (3 / 64 : ℝ) * ((K - 1 : ℕ) : ℝ) * (Real.sqrt n * Real.log n / (10 * A)) ≤
      totalLocalPivotConditionalMean b A B K L x := by
  classical
  obtain ⟨S, hS, hE⟩ := hE
  let p := profileOfScores x
  let hopt := DAState.isManOptimal_matching p
  let f (r : Rotation p (DAState.matching p)) : Matching n × Matching n :=
    ((singletonRotationAnchor hopt r).val, r.val.cycle)
  let c : ℝ := (3 / 64 : ℝ) * ((K - 1 : ℕ) : ℝ)
  let term := stablePivotMeanTerm b A B K L x
  have hf : Function.Injective f := by
    intro r s he
    exact singletonRotationAnchor_injective hopt (Subtype.ext (congrArg Prod.fst he))
  have hnonneg (i : Matching n × Matching n) : 0 ≤ term i := by
    by_cases hi : x ∈ {y | IsScoreStable y i.1}
    · unfold term stablePivotMeanTerm
      rw [indicator_of_mem hi]
      exact (localPivotMeanFloor_nonneg b A B K i.1 i.2 x).trans (h i.1 i.2 hi)
    · unfold term stablePivotMeanTerm
      rw [indicator_of_notMem hi]
  have hterm (r : Rotation p (DAState.matching p)) (hr : r ∈ S) : c ≤ term (f r) := by
    have hs := (isStable_profileOfScores_iff ht (f r).1).mp (singletonRotationAnchor hopt r).property
    have he : IsLocallyEligiblePivot b A B x (f r).1 (f r).2 := hE r hr
    have hh := h (f r).1 (f r).2 hs
    unfold localPivotMeanFloor at hh
    rw [indicator_of_mem (show x ∈ {y | IsLocallyEligiblePivot b A B y (f r).1 (f r).2}
      from he)] at hh
    unfold term stablePivotMeanTerm
    rw [indicator_of_mem (show x ∈ {y | IsScoreStable y (f r).1} from hs)]
    exact hh
  change c * _ ≤ ∑ i, term i
  calc
    _ ≤ c * (S.card : ℝ) := mul_le_mul_of_nonneg_left hS (by positivity)
    _ = ∑ _r ∈ S, c := by simp only [Finset.sum_const, nsmul_eq_mul]; exact mul_comm _ _
    _ ≤ ∑ r ∈ S, term (f r) := Finset.sum_le_sum hterm
    _ = ∑ i ∈ S.image f, term i := (Finset.sum_image fun _ _ _ _ he ↦ hf he).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ ↦ hnonneg i)
private noncomputable def pivotDecorationSupportCap (κ : ℝ) (n : ℕ) : ℕ :=
  ⌊κ * Real.sqrt (n : ℝ)⌋₊
theorem eventually_pivotDecorationSupportCap_bounds {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ n : ℕ in atTop, 2 ≤ pivotDecorationSupportCap κ n ∧
      (pivotDecorationSupportCap κ n : ℝ) ≤ κ * Real.sqrt (n : ℝ) ∧
      κ * Real.sqrt (n : ℝ) / 2 ≤ ((pivotDecorationSupportCap κ n - 1 : ℕ) : ℝ) := by
  have ht : Tendsto (fun n : ℕ ↦ κ * Real.sqrt (n : ℝ)) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hκ
  filter_upwards [ht.eventually_ge_atTop 4] with n hn
  let t := κ * Real.sqrt (n : ℝ)
  let K := pivotDecorationSupportCap κ n
  change 4 ≤ t at hn
  have hK : t < (K : ℝ) + 1 := Nat.lt_floor_add_one t
  have hK' : (K : ℝ) ≤ t := Nat.floor_le (by positivity)
  have h₂ : 2 ≤ K := by
    exact_mod_cast (show (2 : ℝ) ≤ K by linarith)
  refine ⟨h₂, hK', ?_⟩
  rw [Nat.cast_sub (by omega : 1 ≤ K)]
  push_cast
  linarith
end AbunLP
end

-- PivotDecorationRevealInvariance
section
open MeasureTheory Set StableMarriage
namespace AbunLP
variable {n : ℕ} {μ ρ σ : Matching n} {x y : ScoreProfile n}
  {flag : OffDiagonalCellIndex n → Bool}
private structure SameReverseReveal (μ : Matching n) (flag : OffDiagonalCellIndex n → Bool)
    (x y : ScoreProfile n) : Prop where
  diagonal : (splitScorePairs μ x).1 = (splitScorePairs μ y).1
  observed : forwardRevealWithColumns flag (splitScorePairs μ x).2 =
    forwardRevealWithColumns flag (splitScorePairs μ y).2
theorem SameReverseReveal.symm (h : SameReverseReveal μ flag x y) :
    SameReverseReveal μ flag y x := ⟨h.diagonal.symm, h.observed.symm⟩
end AbunLP
end

-- PivotLaterRevealReplay
section
open MeasureTheory Set StableMarriage
namespace AbunLP
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
end AbunLP
end

-- PivotComparableCentered
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace AbunLP
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
end AbunLP
end

-- PivotTwoCycleForest
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace AbunLP
end AbunLP
end

-- LogarithmicCutoffs
section
open Filter
open scoped Topology BigOperators
namespace AbunLP
private noncomputable def logarithmicCycleCutoff (n : ℕ) : ℕ := ⌊Real.log (n : ℝ)⌋₊
theorem tendsto_logarithmicCycleCutoff : Tendsto logarithmicCycleCutoff atTop atTop :=
  tendsto_nat_floor_atTop.comp
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
end AbunLP
end

-- PivotVarianceClosure
section
open Filter MeasureTheory Set StableMarriage Asymptotics
open scoped BigOperators ENNReal Topology
namespace AbunLP
namespace PivotCountParameters
variable {n : ℕ}
end PivotCountParameters
variable {n : ℕ}
namespace PivotCountParameters
private noncomputable def aggregateMean (q : PivotCountParameters) (n : ℕ) : ScoreProfile n → ℝ :=
  totalLocalPivotConditionalMean q.lowerLength q.upperLength q.geometryBudget
    q.supportCap q.shortCutoff
end PivotCountParameters
private theorem eventually_pivotMean_large_of_abundance [LPHyp0_0] {b A B κ η : ℝ} (L : ℕ → ℕ)
    (hη : 0 ≤ η) (hA : 0 < A) (hB : 0 ≤ B) (hκ : 0 < κ)
    (hL : Tendsto L atTop atTop)
    (hsmallLabel : 24 * κ ^ 2 / 2 + (B + 1) * κ ≤ 1 / 4)
    (hsmallCompat : Real.exp (κ * (2 * (1 + B))) * (2 * κ * (B / (1 / 128))) ≤ 3 / 32)
    (hab : ∀ᶠ n : ℕ in atTop,
      continuousScoreLaw n (locallyEligiblePivotAbundance n b A B)ᶜ ≤ ENNReal.ofReal η) :
    ∀ᶠ n : ℕ in atTop, ENNReal.ofReal (1 - η) ≤ (continuousScoreLaw n)
      {x | (3 * κ / (1280 * A)) * ((n : ℝ) * Real.log n) ≤
        (PivotCountParameters.mk b A B (pivotDecorationSupportCap κ n) (L n)).aggregateMean n x} := by
  let K := pivotDecorationSupportCap κ
  let d := 3 * κ / (1280 * A)
  have hK := eventually_pivotDecorationSupportCap_bounds hκ
  have hmean := eventually_localPivotMeanFloor_le_conditionalMean_ae K L hB hκ.le
    (hK.mono fun _ h ↦ ⟨h.1, h.2.1⟩) hL hsmallLabel hsmallCompat
  filter_upwards [hK, hmean, hab] with n hnK hnMean hnAb
  have hAll : ∀ᵐ x ∂continuousScoreLaw n, ∀ μ ρ : Matching n, IsScoreStable x μ →
      localPivotMeanFloor b A B (K n) μ ρ x ≤
        localPivotConditionalMean b A B (K n) (L n) μ ρ x := by
    rw [ae_all_iff]
    intro μ
    rw [ae_all_iff]
    intro ρ
    exact (ae_restrict_iff' (measurableSet_isScoreStable μ)).mp (hnMean μ ρ b A)
  have hnum : d * ((n : ℝ) * Real.log n) ≤ (3 / 64 : ℝ) * ((K n - 1 : ℕ) : ℝ) *
      (Real.sqrt n * Real.log n / (10 * A)) := by
    calc
      _ = (3 / 64 : ℝ) * (κ * Real.sqrt n / 2) * (Real.sqrt n * Real.log n / (10 * A)) := by
        calc
          _ = (3 * κ / (1280 * A)) * ((Real.sqrt n) ^ 2 * Real.log n) := by
            rw [Real.sq_sqrt (Nat.cast_nonneg n)]
          _ = _ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hnK.2.2 (by norm_num)) (by positivity)
  let E := locallyEligiblePivotAbundance n b A B
  have hE : ENNReal.ofReal (1 - η) ≤ continuousScoreLaw n E := by
    have he := measure_compl (μ := continuousScoreLaw n)
      (measurableSet_locallyEligiblePivotAbundance n b A B).compl
      (measure_ne_top (continuousScoreLaw n) Eᶜ)
    rw [show (locallyEligiblePivotAbundance n b A B)ᶜᶜ = E by simp [E], measure_univ] at he
    rw [ENNReal.ofReal_sub _ hη, ENNReal.ofReal_one, he]
    exact tsub_le_tsub_left hnAb _
  refine hE.trans (measure_mono_ae ?_)
  filter_upwards [ae_injective_rows n, hAll] with x ht hall hx
  exact hnum.trans (totalLocalPivotConditionalMean_ge_of_abundance ht hall hx)
end AbunLP
end

noncomputable section
open MeasureTheory Filter AbunLP Asymptotics
open scoped Topology AbunLP
private def params (b A B κ : ℝ) (n : ℕ) : PivotCountParameters :=
  ⟨b,A,B,pivotDecorationSupportCap κ n,logarithmicCycleCutoff n⟩

private def admissible (b A B κ : ℝ) : Prop :=
  0 < b ∧ b ≤ 1 ∧ 1 ≤ A ∧ 0 < B ∧ 0 < κ ∧ κ < b ∧
    24*κ^2/2 + (B+1)*κ ≤ 1/4 ∧
    Real.exp (κ*(2*(1+B))) * (2*κ*(B/(1/128))) ≤ 3/32

private theorem abundance_estimate [LPHyp0_0] [LPHyp1_0] [LPHyp2_0] [LPHyp2_1] [LPHyp3_0] [LPHyp3_1] [LPHyp3_2] [LPHyp3_3] : ∀ η : ℝ, 0 < η → ∃ b A B κ d : ℝ,
  admissible b A B κ ∧ 0 < d ∧ ∀ᶠ n : ℕ in atTop,
    ENNReal.ofReal (1-η) ≤ continuousScoreLaw n
      {x | d*((n:ℝ)*Real.log n) ≤ (params b A B κ n).aggregateMean n x} := by
  intro η hη
  obtain ⟨b, A, B, κ, hb, hb₁, hA, hB, hκ, hκb, hlabel, hcompat, hab⟩ :=
    exists_eligiblePivotAbundance_and_supportCoefficient hη
  have hA' : 0 < A := zero_lt_one.trans_le hA
  refine ⟨b, A, B, κ, 3 * κ / (1280 * A), ⟨hb, hb₁, hA, hB, hκ, hκb, hlabel, hcompat⟩,
    by positivity, ?_⟩
  exact eventually_pivotMean_large_of_abundance logarithmicCycleCutoff hη.le hA' hB.le hκ
    tendsto_logarithmicCycleCutoff hlabel hcompat hab
end


noncomputable section
namespace OMA.R_LennonPittel_lennon_pittel_conjecture_R3_H2_R1_H2_R1_H1_R1
open MeasureTheory Filter AbunLP Asymptotics StableMarriage
open scoped Topology ENNReal AbunLP

/-- Cowgill's almost sure lower bound of the local pivot conditional mean by its floor. -/
def H1 : Prop :=
  ∀ (K L : ℕ → ℕ)
    {B κ : ℝ} (hB : 0 ≤ B) (hκ : 0 ≤ κ)
    (hK : ∀ᶠ n in atTop, 2 ≤ K n ∧ (K n : ℝ) ≤ κ * Real.sqrt (n : ℝ))
    (hL : Tendsto L atTop atTop)
    (hsmallLabel : 24 * κ ^ 2 / 2 + (B + 1) * κ ≤ 1 / 4)
    (hsmallCompat : Real.exp (κ * (2 * (1 + B))) * (2 * κ * (B / (1 / 128))) ≤ 3 / 32),
    ∀ᶠ n : ℕ in atTop, ∀ (μ ρ : Matching n) (b A : ℝ),
      localPivotMeanFloor b A B (K n) μ ρ ≤ᵐ[stableMarkScoreLaw μ]
        localPivotConditionalMean b A B (K n) (L n) μ ρ

/-- Cowgill's Gaussian bound for the weighted singleton anchor count. -/
def H2 : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ (g : ℕ → ℝ) (B : ℝ),
      (∀ k, 0 ≤ g k) → (∀ k ∈ Finset.Icc 2 n, g k ≤ B) →
      (∫⁻ p, profileSingletonAnchorLengthWeight p (fun k ↦ ENNReal.ofReal (g k))
        ∂(uniformProfile n).toMeasure) ≤
        ENNReal.ofReal (expectedNumStableMatchings n) *
          ENNReal.ofReal (∑ k ∈ Finset.Icc 2 n, g k * singletonLengthEnvelope n k) +
          ENNReal.ofReal B * ENNReal.ofReal ((n : ℝ) ^ (-3 : ℝ))

/-- Bad pivot score geometry and bad coexposure scores have vanishing probability. -/
def H3 : Prop :=
  (Tendsto (fun n ↦ continuousScoreLaw n (goodPivotScoreGeometry n)ᶜ) atTop (𝓝 0)) ∧
  (∀ {C : ℝ} (hC : 0 ≤ C)
    (hmean : ∀ᶠ n : ℕ in atTop,
      expectedNumStableMatchings n ≤ C * ((n : ℝ) * Real.log n)),
    Tendsto (fun n ↦ continuousScoreLaw n (goodCoexposureScores n)ᶜ) atTop (𝓝 0))

/-- Score walk, band endpoint and female log geometry estimates, and Pittel's first-moment upper bound. -/
def H4 : Prop :=
  (∀ {ε : ℝ} (hε : 0 < ε),
    Tendsto (fun n : ℕ ↦ continuousScoreLaw n
      {x | ∃ k ≤ n * (n - 1), ε * (n * Real.log n) ≤ |scoreWalkClock x k|})
      atTop (𝓝 0)) ∧
  (Tendsto (fun n ↦ continuousScoreLaw n (scoreWalkBandEndpoints n)ᶜ) atTop (𝓝 0)) ∧
  (Tendsto (fun n ↦ continuousScoreLaw n (goodFemaleLogGeometry n)ᶜ) atTop (𝓝 0)) ∧
  (∀ᶠ n : ℕ in atTop, expectedNumStableMatchings n ≤
      meanUpperConstant * ((n : ℝ) * Real.log n))

theorem main : H1 → H2 → H3 → H4 → OMA.R_LennonPittel_lennon_pittel_conjecture_R3_H2_R1_H2_R1.H1 := by
  intro h1 h2 h3 h4
  haveI : LPHyp0_0 := ⟨h1⟩
  haveI : LPHyp1_0 := ⟨h2⟩
  haveI : LPHyp2_0 := ⟨h3.1⟩
  haveI : LPHyp2_1 := ⟨h3.2⟩
  haveI : LPHyp3_0 := ⟨h4.1⟩
  haveI : LPHyp3_1 := ⟨h4.2.1⟩
  haveI : LPHyp3_2 := ⟨h4.2.2.1⟩
  haveI : LPHyp3_3 := ⟨h4.2.2.2⟩
  exact abundance_estimate

end OMA.R_LennonPittel_lennon_pittel_conjecture_R3_H2_R1_H2_R1_H1_R1
end
