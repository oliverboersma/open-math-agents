import OMAReductions.R_LennonPittel_lennon_pittel_conjecture_R3_H2_R1_H2_R1
import Mathlib

/-! The marked score model of Bo Cowgill, bocowgill/lennon-pittel at
cf950d059659, Apache-2.0. The probability of two long stable matchings with incomparable anchors bounds
the expected product of their reverse decoration counts. -/
-- Credit: @marcusbuffett


-- IidScoreRanks
section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace IncomparableLP
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
end IncomparableLP
end

-- MarkedCounting
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace IncomparableLP
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [Fintype A] [Nonempty A]
private noncomputable def uniformMarkLaw (A : Type*) [MeasurableSpace A] [Fintype A] [Nonempty A] :
    Measure A :=
  (PMF.uniformOfFintype A).toMeasure
private instance uniformMarkLaw_isProbabilityMeasure : IsProbabilityMeasure (uniformMarkLaw A) :=
  inferInstanceAs (IsProbabilityMeasure (PMF.uniformOfFintype A).toMeasure)
private noncomputable def markedLaw (P : Measure Ω) (E : Set (Ω × A)) : Measure (Ω × A) :=
  ProbabilityTheory.cond (P.prod (uniformMarkLaw A)) E
theorem markedLaw_isProbabilityMeasure (P : Measure Ω) [IsProbabilityMeasure P]
    {E : Set (Ω × A)} (hpos : (P.prod (uniformMarkLaw A)) E ≠ 0) :
    IsProbabilityMeasure (markedLaw P E) :=
  ProbabilityTheory.cond_isProbabilityMeasure hpos
variable [MeasurableSingletonClass A]
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
end IncomparableLP
end

-- ScoreRanks
section
open Function MeasureTheory Set
namespace IncomparableLP
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
end IncomparableLP
end

-- ContinuousScoreBridge
section
open scoped BigOperators ENNReal IncomparableLP
open MeasureTheory Set
namespace IncomparableLP
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
end IncomparableLP
end

-- CoexposureGoodScores
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal IncomparableLP
namespace IncomparableLP
variable {n : ℕ}
private def maleSpouseScore (x : ScoreProfile n) (μ : Matching n) (i : Fin n) : ℝ :=
  x (.inl i) (μ i)
private def femaleSpouseScore (x : ScoreProfile n) (μ : Matching n) (j : Fin n) : ℝ :=
  x (.inr j) (μ.symm j)
private theorem measurable_scoreCoordinate (r : Fin n ⊕ Fin n) (i : Fin n) :
    Measurable (fun x : ScoreProfile n ↦ x r i) :=
  (measurable_pi_apply i).comp (measurable_pi_apply r)
theorem measurable_maleSpouseScore (μ : Matching n) (i : Fin n) :
    Measurable (fun x : ScoreProfile n ↦ maleSpouseScore x μ i) :=
  measurable_scoreCoordinate (.inl i) (μ i)
theorem ae_unitOpen_scores (n : ℕ) :
    ∀ᵐ x ∂continuousScoreLaw n, ∀ r i, x r i ∈ Ioo (0 : ℝ) 1 := by
  have hopen : ∀ᵐ t ∂unitScoreLaw, t ∈ Ioo (0 : ℝ) 1 := by
    rw [unitScoreLaw, ← Measure.restrict_congr_set Ioo_ae_eq_Icc]
    exact ae_restrict_mem measurableSet_Ioo
  exact ae_all_iff.2 fun r ↦ ae_all_iff.2 fun i ↦
    (Measure.tendsto_eval_ae_ae (i := r)
      (μ := fun _ : Fin n ⊕ Fin n ↦ Measure.pi fun _ : Fin n ↦ unitScoreLaw)).eventually
      ((Measure.tendsto_eval_ae_ae (i := i) (μ := fun _ : Fin n ↦ unitScoreLaw)).eventually hopen)
end IncomparableLP
end

-- CoexposureScoreEstimates
section
open Filter MeasureTheory Set StableMarriage
open scoped ENNReal BigOperators Topology
namespace IncomparableLP
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
end IncomparableLP
end

-- PittelSimplexRadial
section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace IncomparableLP
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
end IncomparableLP
end

-- CoexposureScoreRow
section
open Set
open scoped BigOperators
namespace IncomparableLP
variable {ι : Type*}
section FiniteRows
variable [Fintype ι] [DecidableEq ι]
end FiniteRows
section SuccessorMass
open MeasureTheory
open scoped ENNReal
private noncomputable def rowNonblockingLaw (x y : ℝ) : Measure (ℝ × ℝ) :=
  (unitScoreLaw.prod unitScoreLaw).restrict (Iio x ×ˢ Iio y)ᶜ
private instance (x y : ℝ) : IsFiniteMeasure (rowNonblockingLaw x y) := by
  unfold rowNonblockingLaw
  infer_instance
end SuccessorMass
end IncomparableLP
end

-- ExposedRotations
section
open StableMarriage
namespace IncomparableLP
variable {n : ℕ}
private def IsEligibleSuccessor (p : Profile n) (μ : Matching n) (m w : Fin n) : Prop :=
  p.manRank m (μ m) < p.manRank m w ∧ p.womanRank w m < p.womanRank w (μ.symm w)
private structure IsSuccessor (p : Profile n) (μ : Matching n) (m w : Fin n) : Prop where
  eligible : IsEligibleSuccessor p μ m w
  min_rank : ∀ w', IsEligibleSuccessor p μ m w' → p.manRank m w ≤ p.manRank m w'
private structure IsExposedRotation (p : Profile n) (μ : Matching n) (ρ : Equiv.Perm (Fin n)) : Prop where
  isCycle : ρ.IsCycle
  successor : ∀ m, ρ m ≠ m → IsSuccessor p μ m (μ (ρ m))
private def eliminateRotation (μ : Matching n) (ρ : Equiv.Perm (Fin n)) : Matching n :=
  ρ.trans μ
@[simp] theorem eliminateRotation_apply (μ : Matching n) (ρ : Equiv.Perm (Fin n)) (m : Fin n) :
    eliminateRotation μ ρ m = μ (ρ m) := rfl
variable {p : Profile n} {μ : Matching n} {ρ : Equiv.Perm (Fin n)}
theorem IsSuccessor.unique {m w w' : Fin n}
    (h : IsSuccessor p μ m w) (h' : IsSuccessor p μ m w') : w = w' :=
  (p.manRank m).injective <| le_antisymm (h.min_rank w' h'.eligible) (h'.min_rank w h.eligible)
theorem IsExposedRotation.manRank_lt_eliminate_of_moved (hρ : IsExposedRotation p μ ρ)
    {m : Fin n} (hm : ρ m ≠ m) :
    p.manRank m (μ m) < p.manRank m (eliminateRotation μ ρ m) :=
  (hρ.successor m hm).eligible.1
theorem IsExposedRotation.womanRank_eliminate_le (hρ : IsExposedRotation p μ ρ) (w : Fin n) :
    p.womanRank w ((eliminateRotation μ ρ).symm w) ≤ p.womanRank w (μ.symm w) :=
  let ⟨m, hm⟩ := (eliminateRotation μ ρ).surjective w
  have hle : p.womanRank (μ (ρ m)) m ≤ p.womanRank (μ (ρ m)) (ρ m) :=
    if h : ρ m = m then
      (congrArg (p.womanRank (μ (ρ m))) h.symm).le
    else by
      simpa only [Equiv.symm_apply_apply] using (hρ.successor m h).eligible.2.le
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
      (not_lt_of_ge ((hρ.successor m hm).min_rank w ⟨hbelow, hwOld⟩)) hb.2.1
end IncomparableLP
end

-- CoexposureScoreProduct
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace IncomparableLP
private abbrev ScorePairIndex (n : ℕ) := Fin n × Fin n
private abbrev DiagonalScorePairs (n : ℕ) := {q : ScorePairIndex n // q.1 = q.2} → ℝ × ℝ
private abbrev OffDiagonalScorePairs (n : ℕ) := {q : ScorePairIndex n // q.1 ≠ q.2} → ℝ × ℝ
private noncomputable def unitScorePairLaw : Measure (ℝ × ℝ) :=
  unitScoreLaw.prod unitScoreLaw
private instance : IsProbabilityMeasure unitScorePairLaw :=
  inferInstanceAs (IsProbabilityMeasure (unitScoreLaw.prod unitScoreLaw))
private noncomputable def diagonalScoreLaw (n : ℕ) : Measure (DiagonalScorePairs n) :=
  Measure.pi fun _ ↦ unitScorePairLaw
private instance (n : ℕ) : IsProbabilityMeasure (diagonalScoreLaw n) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : {q : ScorePairIndex n // q.1 = q.2} ↦
    unitScorePairLaw))
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
private noncomputable def stableScoreRowLaw {n : ℕ} (d : DiagonalScorePairs n) (i : Fin n) :
    Measure ({j : Fin n // i ≠ j} → ℝ × ℝ) :=
  Measure.pi fun j ↦ unitScorePairLaw.restrict
    (nonblockingScoreCell (diagonalPairAt d i).1 (diagonalPairAt d j.val).2)
private instance {n : ℕ} (d : DiagonalScorePairs n) (i : Fin n) :
    IsFiniteMeasure (stableScoreRowLaw d i) :=
  inferInstanceAs (IsFiniteMeasure (Measure.pi fun j : {j : Fin n // i ≠ j} ↦
    unitScorePairLaw.restrict
      (nonblockingScoreCell (diagonalPairAt d i).1 (diagonalPairAt d j.val).2)))
end IncomparableLP
end

-- PivotSpouseProductLower
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace IncomparableLP
private def maleSpouseTotal {n : ℕ} (x : ScoreProfile n) (μ : Matching n) : ℝ :=
  ∑ i, maleSpouseScore x μ i
theorem measurable_maleSpouseTotal {n : ℕ} (μ : Matching n) :
    Measurable (fun x : ScoreProfile n ↦ maleSpouseTotal x μ) :=
  Finset.measurable_sum _ fun i _ ↦ measurable_maleSpouseScore μ i
end IncomparableLP
end

-- PivotForwardRevealCell
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace IncomparableLP
private def forwardEligibleScoreCell (x y : ℝ) : Set (ℝ × ℝ) :=
  Ioi x ×ˢ Iio y
private noncomputable def stableScoreCellLaw (x y : ℝ) : Measure (ℝ × ℝ) :=
  unitScorePairLaw.restrict (nonblockingScoreCell x y)
private instance (x y : ℝ) : IsFiniteMeasure (stableScoreCellLaw x y) :=
  inferInstanceAs (IsFiniteMeasure (unitScorePairLaw.restrict _))
private def forwardScoreCellFlagEvent (x y : ℝ) (b : Bool) : Set (ℝ × ℝ) :=
  if b then forwardEligibleScoreCell x y else (forwardEligibleScoreCell x y)ᶜ
private noncomputable def forwardScoreCellFlagLaw (x y : ℝ) (b : Bool) : Measure (ℝ × ℝ) :=
  if b then (unitScoreLaw.restrict (Ioi x)).prod (unitScoreLaw.restrict (Iio y))
  else unitScoreLaw.prod (unitScoreLaw.restrict (Ici y))
private instance (x y : ℝ) (b : Bool) : IsFiniteMeasure (forwardScoreCellFlagLaw x y b) := by
  cases b
  · exact inferInstanceAs
      (IsFiniteMeasure (unitScoreLaw.prod (unitScoreLaw.restrict (Ici y))))
  · exact inferInstanceAs
      (IsFiniteMeasure ((unitScoreLaw.restrict (Ioi x)).prod (unitScoreLaw.restrict (Iio y))))
private abbrev OffDiagonalCellIndex (n : ℕ) := {q : ScorePairIndex n // q.1 ≠ q.2}
private def forwardScoreMaskEvent {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) : Set (OffDiagonalScorePairs n) :=
  univ.pi fun q ↦ forwardScoreCellFlagEvent
    (diagonalPairAt d q.val.1).1 (diagonalPairAt d q.val.2).2 (flag q)
private abbrev ForwardActiveCellIndex {n : ℕ} (flag : OffDiagonalCellIndex n → Bool) :=
  {q : OffDiagonalCellIndex n // flag q = true}
private abbrev ForwardInactiveCellIndex {n : ℕ} (flag : OffDiagonalCellIndex n → Bool) :=
  {q : OffDiagonalCellIndex n // flag q ≠ true}
private noncomputable def forwardScoreMaskInactiveLaw {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) :
    Measure (ForwardInactiveCellIndex flag → ℝ × ℝ) :=
  Measure.pi fun q ↦
    unitScoreLaw.prod (unitScoreLaw.restrict (Ici (diagonalPairAt d q.val.val.2).2))
private instance {n : ℕ} (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool) :
    IsFiniteMeasure (forwardScoreMaskInactiveLaw d flag) := by
  unfold forwardScoreMaskInactiveLaw
  infer_instance
private def forwardScoreMaskRevealAndInactive {n : ℕ} (flag : OffDiagonalCellIndex n → Bool)
    (z : OffDiagonalScorePairs n) :
    (ForwardActiveCellIndex flag → ℝ) × (ForwardInactiveCellIndex flag → ℝ × ℝ) :=
  (fun q ↦ (z q.val).1, fun q ↦ z q.val)
theorem measurable_forwardScoreMaskRevealAndInactive {n : ℕ}
    (flag : OffDiagonalCellIndex n → Bool) :
    Measurable (forwardScoreMaskRevealAndInactive flag) :=
  (measurable_pi_iff.2 fun q ↦ measurable_fst.comp (measurable_pi_apply q.val)).prodMk
    (measurable_pi_iff.2 fun q ↦ measurable_pi_apply q.val)
private noncomputable def forwardScoreMaskActiveMaleLaw {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) : Measure (ForwardActiveCellIndex flag → ℝ) :=
  Measure.pi fun q ↦
    unitScoreLaw (Iio (diagonalPairAt d q.val.val.2).2) •
      unitScoreLaw.restrict (Ioi (diagonalPairAt d q.val.val.1).1)
private instance {n : ℕ} (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool) :
    IsFiniteMeasure (forwardScoreMaskActiveMaleLaw d flag) := by
  have (q : ForwardActiveCellIndex flag) : IsFiniteMeasure
      (unitScoreLaw (Iio (diagonalPairAt d q.val.val.2).2) •
        unitScoreLaw.restrict (Ioi (diagonalPairAt d q.val.val.1).1)) :=
    Measure.smul_finite _ (measure_ne_top _ _)
  unfold forwardScoreMaskActiveMaleLaw
  infer_instance
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
private noncomputable def forwardScoreMaskInactiveColumnLaw {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) :
    Measure ((j : Fin n) → ForwardInactiveColumnIndex flag j → ℝ × ℝ) :=
  Measure.pi fun j : Fin n ↦ Measure.pi fun _ : ForwardInactiveColumnIndex flag j ↦
    unitScoreLaw.prod (unitScoreLaw.restrict (Ici (diagonalPairAt d j).2))
private instance {n : ℕ} (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool) :
    IsFiniteMeasure (forwardScoreMaskInactiveColumnLaw d flag) := by
  unfold forwardScoreMaskInactiveColumnLaw
  infer_instance
end IncomparableLP
end

-- ReverseSuccessorRotation
section
open StableMarriage
namespace IncomparableLP
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
theorem eliminateRotation_swap_reverseCycle (μ : Matching n) (ρ : Equiv.Perm (Fin n)) :
    eliminateRotation (eliminateRotation μ ρ).symm (reverseRotationCycle μ ρ) = μ.symm := by
  ext w
  simp [reverseRotationCycle, eliminateRotation]
theorem reverseRotationCycle_swap_reverseCycle (μ : Matching n) (ρ : Equiv.Perm (Fin n)) :
    reverseRotationCycle (eliminateRotation μ ρ).symm (reverseRotationCycle μ ρ) = ρ := by
  ext m
  simp [reverseRotationCycle, eliminateRotation]
theorem IsExposedRotation.isExposedRotation_swap_eliminate
    (hρ : IsExposedRotation p μ ρ) (hμ : IsStable p μ) :
    IsExposedRotation (swapProfile p) (eliminateRotation μ ρ).symm
      (reverseRotationCycle μ ρ) := by
  refine ⟨?_, ?_⟩
  · change (μ * ρ * μ⁻¹).IsCycle
    exact hρ.isCycle.conj
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
    constructor
    · have hprev := (hρ.successor (ρ.symm m) hback).eligible.2
      have hwlt : p.womanRank (μ m) (ρ.symm m) < p.womanRank (μ m) m := by
        simpa only [Equiv.apply_symm_apply, Equiv.symm_apply_apply] using hprev
      simp only [IsEligibleSuccessor, swapProfile, hnew, hcurrent, Equiv.symm_symm,
        eliminateRotation_apply]
      exact ⟨hwlt, (hρ.successor m hm).eligible.1⟩
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
      · exact (not_lt_of_ge ((hρ.successor t htfix).min_rank _ hf)) ht.2
end IncomparableLP
end

-- FinitePrerequisites
section
namespace IncomparableLP
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
end IncomparableLP
end

-- RotationDiamond
section
open StableMarriage
namespace IncomparableLP
variable {n : ℕ} {p : Profile n} {μ : Matching n} {ρ σ : Equiv.Perm (Fin n)}
private theorem moved_image {f : Equiv.Perm (Fin n)} {i : Fin n} (hi : f i ≠ i) :
    f (f i) ≠ f i :=
  f.injective.ne hi
private theorem eq_of_common_moved (hρ : IsExposedRotation p μ ρ) (hσ : IsExposedRotation p μ σ)
    {m : Fin n} (hmρ : ρ m ≠ m) (hmσ : σ m ≠ m) : ρ = σ := by
  have hagree (i : Fin n) (hiρ : ρ i ≠ i) (hiσ : σ i ≠ i) : ρ i = σ i :=
    μ.injective ((hρ.successor i hiρ).unique (hσ.successor i hiσ))
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
  · obtain ⟨k, hk⟩ := hρ.isCycle.exists_pow_eq hmρ hi
    have his : σ i ≠ i := by
      rw [← hk, (horbit k).1]
      exact (horbit k).2.2
    exact hagree i hi his
  · have his : σ i = i := by
      by_contra hsi
      obtain ⟨k, hk⟩ := hσ.isCycle.exists_pow_eq hmσ hsi
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
  refine ⟨hρ.isCycle, fun m hm ↦ ?_⟩
  let μ' := eliminateRotation μ σ
  have hold : μ' m = μ m := congrArg μ (hρ.disjoint_moved hσ hne m hm)
  have hnext : μ' (ρ m) = μ (ρ m) :=
    congrArg μ (hρ.disjoint_moved hσ hne (ρ m) (moved_image hm))
  have hs := hρ.successor m hm
  have helig : IsEligibleSuccessor p μ' m (μ' (ρ m)) := by
    refine ⟨?_, ?_⟩
    · simpa only [hold, hnext] using hs.eligible.1
    · rw [Equiv.symm_apply_apply, hnext]
      simpa only [Equiv.symm_apply_apply] using hs.eligible.2
  refine ⟨helig, fun w hw ↦ ?_⟩
  have hman : p.manRank m (μ' m) < p.manRank m w := hw.1
  rw [hold] at hman
  have hbefore : IsEligibleSuccessor p μ m w :=
    ⟨hman, hw.2.trans_le (hσ.womanRank_eliminate_le w)⟩
  change p.manRank m (μ' (ρ m)) ≤ p.manRank m w
  rw [hnext]
  exact hs.min_rank w hbefore
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
end IncomparableLP
end

-- ManOptimal
section
open StableMarriage
open scoped BigOperators
namespace IncomparableLP
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
end IncomparableLP
end

-- RotationCycle
section
namespace IncomparableLP
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
end IncomparableLP
end

-- TargetSuccessor
section
open StableMarriage
namespace IncomparableLP
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
    ⟨heligible, fun v hv ↦ hmin v (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩)⟩
  have hbound : p.manRank m w ≤ p.manRank m (ν m) := hmin (ν m) htarget
  have hj : μ (μ.symm w) = w := μ.apply_symm_apply w
  exact ⟨μ.symm w, by simpa only [hj] using hsuccessor,
    successor_husband_moves hν heligible hbound,
    by simpa only [hj] using hbound⟩
end IncomparableLP
end

-- RotationReachability
section
open scoped BigOperators
open StableMarriage
namespace IncomparableLP
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
  let ⟨m, hm, _⟩ := hρ.isCycle
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
    (lt_irrefl _) (by simpa only [he] using (hsucc i).eligible.1)
  obtain ⟨ρ, hcycle, hedge⟩ := exists_cycle_permutation f hnf
  refine ⟨ρ, ⟨hcycle, ?_⟩, ?_⟩
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
end IncomparableLP
end

-- RotationLabels
section
open StableMarriage
namespace IncomparableLP
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
end IncomparableLP
end

-- RotationPathIndependence
section
open StableMarriage
namespace IncomparableLP
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
      obtain ⟨m, hm, _⟩ := hσ.isCycle
      exact ((hσ.partner_ne_of_moved_of_rotationSequence htail hm) rfl).elim
  | cons _ hρ htail ih =>
    obtain ⟨m, hm, _⟩ := hρ.isCycle
    have hend := hρ.partner_ne_of_moved_of_rotationSequence htail hm
    obtain ⟨ts, hts, hp⟩ := h'.pull_rotation_to_front hρ hm hend
    exact (List.Perm.cons _ (ih hts)).trans hp.symm
end IncomparableLP
end

-- RotationTrace
section
open StableMarriage
namespace IncomparableLP
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
    · obtain ⟨m, hm, _⟩ := hρ.isCycle
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
end IncomparableLP
end

-- RotationIdeals
section
open StableMarriage
namespace IncomparableLP
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
end IncomparableLP
end

-- CoexposedRotations
section
open StableMarriage
namespace IncomparableLP
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
  obtain ⟨m, hm, _⟩ := hρ.isCycle
  exact fun hr ↦ (not_le_of_gt (hρ.manRank_lt_eliminate_of_moved hm))
    ((mem_eliminatedRotations_iff_newRank_le hopt hμ (m := m) hm
      (rotationLabelNewPartner_eq hm)).mp hr)
end IncomparableLP
end

-- CoexposureCycleMoment
section
open StableMarriage MeasureTheory
open scoped BigOperators ENNReal
namespace IncomparableLP
private def RealizesSuccessorPermutation {n : ℕ} (p : Profile n) (M σ : Matching n) : Prop :=
  ∀ i ∈ σ.support, IsSuccessor p M i (M (σ i))
theorem realizesSuccessorPermutation_iff_factors {n : ℕ}
    {p : Profile n} {M σ : Matching n} :
    RealizesSuccessorPermutation p M σ ↔
      ∀ ρ ∈ σ.cycleFactorsFinset, IsExposedRotation p M ρ := by
  constructor
  · intro h ρ hρ
    obtain ⟨hc, heq⟩ := Equiv.Perm.mem_cycleFactorsFinset_iff.mp hρ
    refine ⟨hc, fun i hi ↦ ?_⟩
    have hmem := Equiv.Perm.mem_support.mpr hi
    rw [heq i hmem]
    exact h i (Equiv.Perm.mem_cycleFactorsFinset_support_le hρ hmem)
  · intro h i hi
    obtain ⟨ρ, hρ, hmem⟩ :=
      Equiv.Perm.mem_support_iff_mem_support_of_mem_cycleFactorsFinset.mp hi
    rw [← (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hρ).2 i hmem]
    exact (h ρ hρ).successor i (Equiv.Perm.mem_support.mp hmem)
theorem card_support_eq_sum_cycleFactors_support {n : ℕ} (σ : Matching n) :
    σ.support.card = ∑ ρ ∈ σ.cycleFactorsFinset, ρ.support.card := by
  have hs : σ.cycleFactorsFinset.biUnion (fun ρ ↦ ρ.support) = σ.support := by
    ext i
    rw [Finset.mem_biUnion]
    exact Equiv.Perm.mem_support_iff_mem_support_of_mem_cycleFactorsFinset.symm
  refine (congrArg Finset.card hs.symm).trans (Finset.card_biUnion ?_)
  intro ρ hρ τ hτ hne
  exact Equiv.Perm.disjoint_iff_disjoint_support.mp
    (σ.cycleFactorsFinset_pairwise_disjoint hρ hτ hne)
end IncomparableLP
end

-- PivotReverseMaskLowerMoment
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace IncomparableLP
open scoped Classical in
private noncomputable def goodReverseSupportPermutations {n : ℕ} (k : ℕ)
    (A : Finset (Fin n)) (F : Fin n → Finset (Fin n)) : Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter fun σ ↦ σ.support.card = k ∧
    ∀ i ∈ σ.support, i ∉ A ∧ σ i ∉ F i
theorem mem_goodReverseSupportPermutations {n k : ℕ} {A : Finset (Fin n)}
    {F : Fin n → Finset (Fin n)} {σ : Matching n} :
    σ ∈ goodReverseSupportPermutations k A F ↔ σ.support.card = k ∧
      ∀ i ∈ σ.support, i ∉ A ∧ σ i ∉ F i := by
  classical
  simp [goodReverseSupportPermutations]
private noncomputable def forwardMaskForbiddenTargets {n : ℕ} (μ : Matching n)
    (flag : OffDiagonalCellIndex n → Bool) (i : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun j ↦ ¬ ∃ q : ForwardInactiveColumnIndex flag (μ.symm i),
    q.val.val.val.1 = μ.symm j
private noncomputable def reverseSpouseWeights {n : ℕ} (μ : Matching n) (d : DiagonalScorePairs n) :
    Fin n → ℝ≥0∞ := fun j ↦
  ENNReal.ofReal ((diagonalPairAt d (μ.symm j)).1 / ∑ i, (diagonalPairAt d i).1)
end IncomparableLP
end

-- PivotReverseCompetitorMass
section
open StableMarriage
open scoped BigOperators ENNReal
namespace IncomparableLP
private noncomputable def forwardMaskOmittedMass {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) (j : Fin n) : ℝ :=
  ∑ i : {i : Fin n // i ≠ j}, if flag ⟨(i.val, j), i.property⟩ then
    (diagonalPairAt d i.val).1 else 0
end IncomparableLP
end

-- PivotForwardMaskProbability
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace IncomparableLP
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
private noncomputable def normalizedStableScoreCellLaw (x y : ℝ) : Measure (ℝ × ℝ) :=
  ((stableScoreCellLaw x y) univ)⁻¹ • stableScoreCellLaw x y
private instance (x y : ℝ) : IsFiniteMeasure (normalizedStableScoreCellLaw x y) := by
  constructor
  rw [normalizedStableScoreCellLaw, Measure.smul_apply, smul_eq_mul, mul_comm]
  exact (ENNReal.mul_inv_ne_top _).lt_top
end IncomparableLP
end

-- PivotForwardRevealRectangle
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace IncomparableLP
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
end IncomparableLP
end

-- PivotForwardPivotReadout
section
open MeasureTheory Set StableMarriage
namespace IncomparableLP
private noncomputable def forwardPivotIncrement {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) (ρ : Matching n)
    (a : ForwardRevealedMaleScores flag) (m : Fin n) : ℝ :=
  if hm : ρ m ≠ m then
    let q : OffDiagonalCellIndex n := ⟨(m, ρ m), hm.symm⟩
    if hq : flag q = true then a ⟨q, hq⟩ - (diagonalPairAt d m).1 else 0
  else 0
end IncomparableLP
end

-- SingletonIdealAnchor
section
namespace IncomparableLP
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
end IncomparableLP
end

-- SingletonRotationAnchor
section
open StableMarriage
namespace IncomparableLP
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
end IncomparableLP
end

-- UndoableRotations
section
open StableMarriage
namespace IncomparableLP
variable {n : ℕ} {p : Profile n} {μ₀ μ ν : Matching n} {r : Rotation p μ₀}
private def Rotation.IsUndoableAt (r : Rotation p μ₀) (ν : Matching n) : Prop :=
  ∃ μ, IsStable p μ ∧ r.IsExposedAt μ ∧ eliminateRotation μ r.val.cycle = ν
theorem Rotation.IsExposedAt.eliminatedRotations_eliminate
    (he : r.IsExposedAt μ) (hopt : IsManOptimal p μ₀) (hμ : IsStable p μ) :
    eliminatedRotations p μ₀ (eliminateRotation μ r.val.cycle) =
      insert r (eliminatedRotations p μ₀ μ) := by
  obtain ⟨rs, hrs⟩ := exists_rotationSequence_of_manOptimal hopt hμ
  have hstep : RotationSequence p μ [r.val.cycle] (eliminateRotation μ r.val.cycle) :=
    .cons hμ he.1 (.nil (he.1.isStable_eliminate hμ))
  ext s
  rw [(hrs.append hstep).mem_eliminatedRotations_iff, hrs.rotationLabels_append,
    List.mem_append, ← hrs.mem_eliminatedRotations_iff]
  simp only [rotationLabels, List.mem_singleton, he.2, Set.mem_insert_iff]
  constructor
  · rintro (hs | hs)
    · exact Or.inr hs
    · exact Or.inl (Subtype.ext hs)
  · rintro (hs | hs)
    · exact Or.inr (congrArg (fun x : Rotation p μ₀ ↦ x.val) hs)
    · exact Or.inl hs
theorem Rotation.IsExposedAt.eliminatedRotations_eq_diff
    (he : r.IsExposedAt μ) (hopt : IsManOptimal p μ₀) (hμ : IsStable p μ)
    (hstep : eliminateRotation μ r.val.cycle = ν) :
    eliminatedRotations p μ₀ μ = eliminatedRotations p μ₀ ν \ {r} := by
  have hnot := ((r.isExposedAt_iff_minimal hopt hμ).mp he).prop
  rw [← hstep, he.eliminatedRotations_eliminate hopt hμ]
  ext s
  simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff]
  exact ⟨fun hs ↦ ⟨Or.inr hs, fun h ↦ hnot (h ▸ hs)⟩,
    fun ⟨hs, hne⟩ ↦ hs.resolve_left hne⟩
theorem Rotation.isUndoableAt_iff_maximal (hopt : IsManOptimal p μ₀) (hν : IsStable p ν)
    (r : Rotation p μ₀) :
    r.IsUndoableAt ν ↔ Maximal (fun s ↦ s ∈ eliminatedRotations p μ₀ ν) r := by
  constructor
  · rintro ⟨μ, hμ, he, rfl⟩
    rw [he.eliminatedRotations_eliminate hopt hμ, maximal_iff_forall_gt]
    refine ⟨Set.mem_insert _ _, fun s hrs hs ↦ ?_⟩
    have hold := (Set.mem_insert_iff.mp hs).resolve_left hrs.ne.symm
    exact ((r.isExposedAt_iff_minimal hopt hμ).mp he).prop (hrs.le _ hold)
  · intro hmax
    let I := stableMatchingToRotationIdeal (μ₀ := μ₀) ⟨ν, hν⟩
    let J : LowerSet (Rotation p μ₀) :=
      ⟨(I : Set (Rotation p μ₀)) \ {r}, by
        intro b a hab hb
        refine ⟨I.lower hab hb.1, ?_⟩
        intro ha
        have har : a = r := Set.mem_singleton_iff.mp ha
        subst a
        exact hb.2 (Set.mem_singleton_iff.mpr ((hmax.2 hb.1 hab).antisymm hab))⟩
    let e := stableMatchingEquivRotationIdeals hopt
    let μ := e.symm J
    have hμI : eliminatedRotations p μ₀ μ.val = (J : Set (Rotation p μ₀)) :=
      congrArg (fun K : LowerSet (Rotation p μ₀) ↦ (K : Set (Rotation p μ₀)))
        (e.apply_symm_apply J)
    have he : r.IsExposedAt μ.val := by
      rw [Rotation.isExposedAt_iff_minimal hopt μ.property, minimal_iff_forall_lt, hμI]
      refine ⟨fun h ↦ h.2 (Set.mem_singleton r), fun s hsr hn ↦ hn ?_⟩
      exact ⟨I.lower hsr.le hmax.prop, fun h ↦ hsr.ne (Set.mem_singleton_iff.mp h)⟩
    have hsets : eliminatedRotations p μ₀ (eliminateRotation μ.val r.val.cycle) =
        eliminatedRotations p μ₀ ν := by
      rw [he.eliminatedRotations_eliminate hopt μ.property, hμI]
      change insert r ((I : Set (Rotation p μ₀)) \ {r}) = (I : Set (Rotation p μ₀))
      rw [Set.insert_sdiff_singleton]
      exact Set.insert_eq_of_mem (show r ∈ I from hmax.prop)
    have hstable := he.1.isStable_eliminate μ.property
    have hmatching : (⟨eliminateRotation μ.val r.val.cycle, hstable⟩ :
        {τ : Matching n // IsStable p τ}) = ⟨ν, hν⟩ :=
      (stableMatchingToRotationIdeal_bijective hopt).1 (LowerSet.ext hsets)
    exact ⟨μ.val, μ.property, he, congrArg Subtype.val hmatching⟩
end IncomparableLP
end

-- ReverseRotationIdeals
section
open StableMarriage
namespace IncomparableLP
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
theorem eliminateRotation_undoReverseRotation (ν : Matching n) (σ : Equiv.Perm (Fin n)) :
    eliminateRotation (undoReverseRotation ν σ) (reverseRotationCycle ν.symm σ) = ν := by
  simpa only [undoReverseRotation, Equiv.symm_symm] using
    eliminateRotation_swap_reverseCycle ν.symm σ
private def reverseExposedRotationLabel (hopt : IsManOptimal p μ₀) (hν : IsStable p ν)
    (σ : {σ : Equiv.Perm (Fin n) // IsReverseExposedRotation p ν σ}) : Rotation p μ₀ :=
  rotationOfExposed hopt (σ.property.undo_stable hν) (σ.property.forward_exposed hν)
theorem eliminatedRotations_undoReverseRotation (hopt : IsManOptimal p μ₀) (hν : IsStable p ν)
    (σ : {σ : Equiv.Perm (Fin n) // IsReverseExposedRotation p ν σ}) :
    eliminatedRotations p μ₀ (undoReverseRotation ν σ.val) =
      eliminatedRotations p μ₀ ν \ {reverseExposedRotationLabel hopt hν σ} :=
  (show (reverseExposedRotationLabel hopt hν σ).IsExposedAt (undoReverseRotation ν σ.val)
    from ⟨σ.property.forward_exposed hν, rfl⟩).eliminatedRotations_eq_diff
      hopt (σ.property.undo_stable hν) (eliminateRotation_undoReverseRotation ν σ.val)
theorem reverseExposedRotationLabel_maximal (hopt : IsManOptimal p μ₀) (hν : IsStable p ν)
    (σ : {σ : Equiv.Perm (Fin n) // IsReverseExposedRotation p ν σ}) :
    Maximal (fun s ↦ s ∈ eliminatedRotations p μ₀ ν)
      (reverseExposedRotationLabel hopt hν σ) :=
  (Rotation.isUndoableAt_iff_maximal hopt hν _).mp
    ⟨undoReverseRotation ν σ.val, σ.property.undo_stable hν,
      ⟨σ.property.forward_exposed hν, rfl⟩, eliminateRotation_undoReverseRotation ν σ.val⟩
private noncomputable def reverseExposedRotationEquivMaximal (hopt : IsManOptimal p μ₀)
    (hν : IsStable p ν) :
    {σ : Equiv.Perm (Fin n) // IsReverseExposedRotation p ν σ} ≃
      {r : Rotation p μ₀ // Maximal (fun s ↦ s ∈ eliminatedRotations p μ₀ ν) r} := by
  let f (σ : {σ : Equiv.Perm (Fin n) // IsReverseExposedRotation p ν σ}) :
      {r : Rotation p μ₀ // Maximal (fun s ↦ s ∈ eliminatedRotations p μ₀ ν) r} :=
    ⟨reverseExposedRotationLabel hopt hν σ, reverseExposedRotationLabel_maximal hopt hν σ⟩
  apply Equiv.ofBijective f
  constructor
  · intro σ τ h
    apply Subtype.ext
    apply Equiv.ext
    intro w
    have he := congrArg
      (fun r : {r : Rotation p μ₀ //
          Maximal (fun s ↦ s ∈ eliminatedRotations p μ₀ ν) r} ↦
        r.val.val.cycle (ν.symm w)) h
    change reverseRotationCycle ν.symm σ.val (ν.symm w) =
      reverseRotationCycle ν.symm τ.val (ν.symm w) at he
    exact ν.symm.injective (by simpa [reverseRotationCycle] using he)
  · rintro ⟨r, hr⟩
    obtain ⟨μ, hμ, he, hstep⟩ := (r.isUndoableAt_iff_maximal hopt hν).mpr hr
    let σ := reverseRotationCycle μ r.val.cycle
    have hσ : IsReverseExposedRotation p ν σ := by
      rw [← hstep]
      exact he.1.isExposedRotation_swap_eliminate hμ
    have hund : undoReverseRotation ν σ = μ := by
      rw [← hstep, undoReverseRotation, eliminateRotation_swap_reverseCycle, Equiv.symm_symm]
    have hcycle : reverseRotationCycle ν.symm σ = r.val.cycle := by
      rw [← hstep]
      exact reverseRotationCycle_swap_reverseCycle μ r.val.cycle
    refine ⟨⟨σ, hσ⟩, Subtype.ext (Subtype.ext ?_)⟩
    change rotationLabel (undoReverseRotation ν σ) (reverseRotationCycle ν.symm σ) = r.val
    rw [hund, hcycle]
    exact he.2
end IncomparableLP
end

-- PivotCrossBlocker
section
open StableMarriage
namespace IncomparableLP
variable {n : ℕ} {p : Profile n} {A N : Matching n} {ρ : Equiv.Perm (Fin n)}
theorem rotationLabel_eq_of_fixed_on_cycle
    (hfixed : ∀ m, ρ m ≠ m → N m = A m) :
    rotationLabel N ρ = rotationLabel A ρ := by
  unfold rotationLabel
  congr 1
  funext m
  by_cases hm : ρ m = m
  · simp [hm]
  · simp [hm, hfixed m hm]
end IncomparableLP
end

-- PivotReversePermutationCompatibility
section
open StableMarriage
namespace IncomparableLP
variable {n : ℕ} {p : Profile n} {μ ρ σ : Matching n}
theorem RealizesSuccessorPermutation.womanRank_eliminate_le
    (hσ : RealizesSuccessorPermutation p μ σ) (w : Fin n) :
    p.womanRank w ((eliminateRotation μ σ).symm w) ≤ p.womanRank w (μ.symm w) :=
  let ⟨m, hm⟩ := (eliminateRotation μ σ).surjective w
  have hle : p.womanRank (μ (σ m)) m ≤ p.womanRank (μ (σ m)) (σ m) :=
    if he : σ m = m then (congrArg (p.womanRank (μ (σ m))) he.symm).le
    else by simpa only [Equiv.symm_apply_apply] using
      (hσ m (Equiv.Perm.mem_support.mpr he)).eligible.2.le
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
      (not_lt_of_ge ((hσ m (Equiv.Perm.mem_support.mpr hm)).min_rank w ⟨hbelow, hwOld⟩)) hb.2.1
theorem RealizesSuccessorPermutation.undo_stable
    (hσ : RealizesSuccessorPermutation (swapProfile p) μ.symm σ) (hμ : IsStable p μ) :
    IsStable p (undoReverseRotation μ σ) :=
  isStable_swapProfile_iff.mp (hσ.isStable_eliminate (isStable_swapProfile_iff.mpr hμ))
theorem undoReverseRotation_symm_apply (μ σ : Matching n) (w : Fin n) :
    (undoReverseRotation μ σ).symm w = μ.symm (σ w) :=
  rfl
end IncomparableLP
end

-- UndoMaximalSubset
section
open StableMarriage
namespace IncomparableLP
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
theorem eliminatedRotations_undoMaximalSubsetEmbedding (hopt : IsManOptimal p μ₀)
    (hν : IsStable p ν) (D : Set (MaximalEliminatedRotation p μ₀ ν)) :
    eliminatedRotations p μ₀ (undoMaximalSubsetEmbedding hopt hν D).val =
      eliminatedRotations p μ₀ ν \ (Subtype.val '' D) :=
  congrArg (fun I : LowerSet (Rotation p μ₀) ↦ (I : Set (Rotation p μ₀)))
    ((stableMatchingEquivRotationIdeals hopt).apply_symm_apply (undoMaximalSubsetIdeal hν D))
end IncomparableLP
end

-- PivotIdealExposure
section
open StableMarriage
namespace IncomparableLP
theorem minimal_compl_diff_maximal_iff {α : Type*} [PartialOrder α]
    (I : LowerSet α) (D : Set α) (hD : ∀ t ∈ D, Maximal (· ∈ I) t) (s : α) :
    Minimal (· ∉ (I : Set α) \ D) s ↔
      s ∈ D ∨ (Minimal (· ∉ I) s ∧ ∀ t ∈ D, ¬ t < s) := by
  simp only [minimal_iff_forall_lt, not_not]
  constructor
  · rintro ⟨hs, hpred⟩
    by_cases hsD : s ∈ D
    · exact Or.inl hsD
    · exact Or.inr ⟨⟨fun hsI ↦ hs ⟨hsI, hsD⟩, fun _ hts ↦ (hpred hts).1⟩,
        fun _ htD hts ↦ (hpred hts).2 htD⟩
  · rintro (hsD | ⟨⟨hsI, hpred⟩, hcompat⟩)
    · have hsI := (hD s hsD).prop
      refine ⟨fun h ↦ h.2 hsD, fun t hts ↦ ⟨I.lower hts.le hsI, ?_⟩⟩
      exact fun htD ↦ hts.not_ge ((hD t htD).2 hsI hts.le)
    · exact ⟨fun h ↦ hsI h.1, fun t hts ↦ ⟨hpred hts, fun htD ↦ hcompat t htD hts⟩⟩
variable {n : ℕ} {p : Profile n} {μ₀ μ : Matching n}
theorem isExposedAt_undoMaximalSubsetEmbedding_iff
    (hopt : IsManOptimal p μ₀) (hμ : IsStable p μ)
    (D : Set (MaximalEliminatedRotation p μ₀ μ)) (s : Rotation p μ₀) :
    s.IsExposedAt (undoMaximalSubsetEmbedding hopt hμ D).val ↔
      s ∈ Subtype.val '' D ∨ (s.IsExposedAt μ ∧ ∀ t ∈ Subtype.val '' D, ¬ t < s) := by
  rw [Rotation.isExposedAt_iff_minimal hopt (undoMaximalSubsetEmbedding hopt hμ D).property,
    Rotation.isExposedAt_iff_minimal hopt hμ,
    eliminatedRotations_undoMaximalSubsetEmbedding]
  let I := stableMatchingToRotationIdeal (μ₀ := μ₀) ⟨μ, hμ⟩
  apply minimal_compl_diff_maximal_iff I
  rintro _ ⟨t, _, rfl⟩
  exact t.property
theorem pivot_isExposedAt_undo_iff (hopt : IsManOptimal p μ₀) (r : Rotation p μ₀)
    (D : Set (MaximalEliminatedRotation p μ₀ (singletonRotationAnchor hopt r).val)) :
    r.IsExposedAt
      (undoMaximalSubsetEmbedding hopt (singletonRotationAnchor hopt r).property D).val ↔
      ∀ s ∈ Subtype.val '' D, ¬ s < r := by
  let A := singletonRotationAnchor hopt r
  have hA : r.IsExposedAt A.val := ((eq_singletonRotationAnchor_iff hopt r A).mp rfl r).mpr rfl
  have hrI : r ∉ eliminatedRotations p μ₀ A.val :=
    ((Rotation.isExposedAt_iff_minimal hopt A.property r).mp hA).prop
  have hrD : r ∉ Subtype.val '' D := by
    rintro ⟨s, _, hs⟩
    exact hrI (hs ▸ s.property.prop)
  rw [isExposedAt_undoMaximalSubsetEmbedding_iff hopt A.property D r]
  exact ⟨fun h ↦ (h.resolve_left hrD).2, fun h ↦ Or.inr ⟨hA, h⟩⟩
theorem isExposedAt_undo_pivot_iff (hopt : IsManOptimal p μ₀) (r : Rotation p μ₀)
    (D : Set (MaximalEliminatedRotation p μ₀ (singletonRotationAnchor hopt r).val))
    (hr : r.IsExposedAt
      (undoMaximalSubsetEmbedding hopt (singletonRotationAnchor hopt r).property D).val)
    (s : Rotation p μ₀) :
    s.IsExposedAt
      (undoMaximalSubsetEmbedding hopt (singletonRotationAnchor hopt r).property D).val ↔
      s = r ∨ s ∈ Subtype.val '' D := by
  let A := singletonRotationAnchor hopt r
  have hcompat := (pivot_isExposedAt_undo_iff hopt r D).mp hr
  rw [isExposedAt_undoMaximalSubsetEmbedding_iff hopt A.property D s,
    (eq_singletonRotationAnchor_iff hopt r A).mp rfl s]
  constructor
  · rintro (hsD | ⟨hsr, _⟩)
    · exact Or.inr hsD
    · exact Or.inl hsr
  · rintro (rfl | hsD)
    · exact Or.inr ⟨rfl, hcompat⟩
    · exact Or.inl hsD
end IncomparableLP
end

-- ReverseRotationPersistence
section
open StableMarriage
namespace IncomparableLP
variable {n : ℕ} {p : Profile n} {μ₀ ν : Matching n} {σ τ : Equiv.Perm (Fin n)}
theorem IsReverseExposedRotation.persist_undo (hτ : IsReverseExposedRotation p ν τ)
    (hσ : IsReverseExposedRotation p ν σ) (hne : τ ≠ σ) :
    IsReverseExposedRotation p (undoReverseRotation ν σ) τ := by
  simpa only [IsReverseExposedRotation, undoReverseRotation, Equiv.symm_symm] using
    (show IsExposedRotation (swapProfile p) ν.symm τ from hτ).persist_eliminate hσ hne
theorem IsReverseExposedRotation.undo_comm (hσ : IsReverseExposedRotation p ν σ)
    (hτ : IsReverseExposedRotation p ν τ) (hne : σ ≠ τ) :
    undoReverseRotation (undoReverseRotation ν σ) τ =
      undoReverseRotation (undoReverseRotation ν τ) σ := by
  simpa only [undoReverseRotation, Equiv.symm_symm] using
    congrArg (fun μ : Matching n ↦ μ.symm)
      ((show IsExposedRotation (swapProfile p) ν.symm σ from hσ).eliminate_comm hτ hne)
theorem reverseExposedRotationLabel_persist_undo (hopt : IsManOptimal p μ₀)
    (hν : IsStable p ν) (hτ : IsReverseExposedRotation p ν τ)
    (hσ : IsReverseExposedRotation p ν σ) (hne : τ ≠ σ) :
    reverseExposedRotationLabel hopt (hσ.undo_stable hν) ⟨τ, hτ.persist_undo hσ hne⟩ =
      reverseExposedRotationLabel hopt hν ⟨τ, hτ⟩ := by
  let a := reverseExposedRotationLabel hopt hν ⟨σ, hσ⟩
  let b := reverseExposedRotationLabel hopt hν ⟨τ, hτ⟩
  let b' := reverseExposedRotationLabel hopt (hσ.undo_stable hν)
    ⟨τ, hτ.persist_undo hσ hne⟩
  have hba : b ≠ a := fun he ↦ hne
    (congrArg Subtype.val ((reverseExposedRotationEquivMaximal hopt hν).injective
      (Subtype.ext he)))
  have hb := (reverseExposedRotationLabel_maximal hopt hν ⟨τ, hτ⟩).prop
  change b' = b
  by_contra hne'
  
  have hbmem :
      b ∈ eliminatedRotations p μ₀ (undoReverseRotation (undoReverseRotation ν σ) τ) := by
    rw [eliminatedRotations_undoReverseRotation hopt (hσ.undo_stable hν)
      ⟨τ, hτ.persist_undo hσ hne⟩,
      eliminatedRotations_undoReverseRotation hopt hν ⟨σ, hσ⟩]
    exact ⟨⟨hb, fun he ↦ hba (Set.mem_singleton_iff.mp he)⟩,
      fun he ↦ hne' (Set.mem_singleton_iff.mp he).symm⟩
  rw [hσ.undo_comm hτ hne.symm,
    eliminatedRotations_undoReverseRotation hopt (hτ.undo_stable hν)
      ⟨σ, hσ.persist_undo hτ hne.symm⟩,
    eliminatedRotations_undoReverseRotation hopt hν ⟨τ, hτ⟩] at hbmem
  exact hbmem.1.2 (Set.mem_singleton _)
end IncomparableLP
end

-- RotationUndoSequences
section
open StableMarriage
namespace IncomparableLP
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
theorem RotationUndoSequence.eliminatedRotations_end {rs : List (Rotation p μ₀)}
    (h : RotationUndoSequence hopt ν rs μ) :
    eliminatedRotations p μ₀ μ = eliminatedRotations p μ₀ ν \ {r | r ∈ rs} := by
  induction h with
  | nil => simp
  | cons hν σ hlabel _ ih =>
    rw [ih, eliminatedRotations_undoReverseRotation hopt hν σ, hlabel, Set.sdiff_sdiff]
    congr 1
    ext r
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_ofPred_eq, List.mem_cons]
private theorem exists_aligned_undo_sequences {α : Type*} (hopt : IsManOptimal p μ₀)
    (hν : IsStable p ν) (rs : List α)
    (cycle : α → Equiv.Perm (Fin n)) (label : α → Rotation p μ₀)
    (hnd : (rs.map cycle).Nodup)
    (he : ∀ x ∈ rs, IsReverseExposedRotation p ν (cycle x))
    (hl : ∀ x (hx : x ∈ rs), reverseExposedRotationLabel hopt hν
      ⟨cycle x, he x hx⟩ = label x) :
    ∃ μ, RotationSequence (swapProfile p) ν.symm (rs.map cycle) μ.symm ∧
      RotationUndoSequence hopt ν (rs.map label) μ := by
  induction rs generalizing ν with
  | nil => exact ⟨ν, .nil (isStable_swapProfile_iff.mpr hν), .nil hν⟩
  | cons a rs ih =>
    have hσ := he a List.mem_cons_self
    have hν' := hσ.undo_stable hν
    have hdistinct (x : α) (hx : x ∈ rs) : cycle x ≠ cycle a := fun heq ↦
      (List.nodup_cons.mp hnd).1 (List.mem_map.mpr ⟨x, hx, heq⟩)
    have hnext (x : α) (hx : x ∈ rs) :
        IsReverseExposedRotation p (undoReverseRotation ν (cycle a)) (cycle x) :=
      (he x (List.mem_cons_of_mem a hx)).persist_undo hσ (hdistinct x hx)
    have hnextLabel (x : α) (hx : x ∈ rs) : reverseExposedRotationLabel hopt hν'
        ⟨cycle x, hnext x hx⟩ = label x :=
      (reverseExposedRotationLabel_persist_undo hopt hν (he x (List.mem_cons_of_mem a hx))
        hσ (hdistinct x hx)).trans (hl x (List.mem_cons_of_mem a hx))
    obtain ⟨μ, hcycles, hlabels⟩ :=
      ih hν' (List.nodup_cons.mp hnd).2 hnext hnextLabel
    refine ⟨μ, .cons (isStable_swapProfile_iff.mpr hν) hσ ?_,
      .cons hν ⟨cycle a, hσ⟩ (hl a List.mem_cons_self) hlabels⟩
    simpa only [undoReverseRotation, Equiv.symm_symm] using hcycles
theorem exists_rotationUndoSequence_of_reverse_cycles
    (hopt : IsManOptimal p μ₀) (hν : IsStable p ν)
    (rs : List {σ : Equiv.Perm (Fin n) // IsReverseExposedRotation p ν σ}) (hnd : rs.Nodup) :
    ∃ μ, RotationSequence (swapProfile p) ν.symm (rs.map Subtype.val) μ.symm ∧
      RotationUndoSequence hopt ν (rs.map (reverseExposedRotationLabel hopt hν)) μ :=
  exists_aligned_undo_sequences hopt hν rs Subtype.val (reverseExposedRotationLabel hopt hν)
    (hnd.map Subtype.val_injective) (fun σ _ ↦ σ.property) (fun _ _ ↦ rfl)
end IncomparableLP
end

-- PivotIncidenceCounting
section
open StableMarriage
open scoped BigOperators
namespace IncomparableLP
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
private theorem ext_removed {D E : PivotDecoration hopt K r} (h : D.removed = E.removed) :
    D = E := by
  cases D
  cases E
  cases h
  rfl
private instance : Finite (PivotDecoration hopt K r) := by
  classical
  let := Fintype.ofFinite (MaximalEliminatedRotation p μ₀ (singletonRotationAnchor hopt r).val)
  exact Finite.of_injective (fun D ↦ D.removed) fun _ _ ↦ ext_removed
private noncomputable def matching (D : PivotDecoration hopt K r) : {M : Matching n // IsStable p M} :=
  undoMaximalSubsetEmbedding hopt (singletonRotationAnchor hopt r).property D.removed
theorem isExposedAt_matching_iff (D : PivotDecoration hopt K r) (s : Rotation p μ₀) :
    s.IsExposedAt D.matching.val ↔ s = r ∨ s ∈ Subtype.val ''
      (↑D.removed :
        Set (MaximalEliminatedRotation p μ₀ (singletonRotationAnchor hopt r).val)) :=
  isExposedAt_undo_pivot_iff hopt r D.removed D.pivot_exposed s
theorem long_exposed_iff (D : PivotDecoration hopt K r) (hr : K < rotationLength r)
    (s : Rotation p μ₀) :
    (s.IsExposedAt D.matching.val ∧ K < rotationLength s) ↔ s = r := by
  constructor
  · rintro ⟨he, hl⟩
    rcases (D.isExposedAt_matching_iff s).mp he with hs | ⟨t, ht, rfl⟩
    · exact hs
    · have ht' : t ∈ D.removed := ht
      exact (not_lt_of_ge ((Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) ht').trans
        D.totalLength_le) hl).elim
  · rintro rfl
    exact ⟨D.pivot_exposed, hr⟩
end PivotDecoration
private abbrev LongPivot (p : Profile n) (μ₀ : Matching n) (K : ℕ) :=
  {r : Rotation p μ₀ // K < rotationLength r}
private noncomputable def pivotDecorationEmbedding (hopt : IsManOptimal p μ₀) (K : ℕ) :
    (Σ r : LongPivot p μ₀ K, PivotDecoration hopt K r.val) ↪
      {M : Matching n // IsStable p M} :=
  ⟨fun a ↦ a.2.matching, by
    rintro ⟨r, D⟩ ⟨s, E⟩ h
    change D.matching = E.matching at h
    have he : r.val.IsExposedAt E.matching.val := by
      rw [← h]
      exact D.pivot_exposed
    have hrs : r = s := Subtype.ext ((E.long_exposed_iff s.property r.val).mp ⟨he, r.property⟩)
    subst s
    let e := undoMaximalSubsetEmbedding hopt (singletonRotationAnchor hopt r.val).property
    have hsets : (↑D.removed : Set _) = ↑E.removed := e.injective h
    have hDE : D = E := PivotDecoration.ext_removed (Finset.coe_injective hsets)
    cases hDE
    rfl⟩
end IncomparableLP
end

-- PivotReversePermutationDecoration
section
open StableMarriage
open scoped BigOperators
namespace IncomparableLP
variable {n : ℕ} {p : Profile n} {μ₀ μ ν : Matching n}
private theorem RotationSequence.eq_mul_listProd {rs : List (Equiv.Perm (Fin n))}
    (h : RotationSequence p μ rs ν) : ν = μ * rs.prod := by
  induction h with
  | nil => simp
  | cons _ _ _ ih =>
    rw [List.prod_cons, ← mul_assoc]
    simpa only [eliminateRotation, Equiv.Perm.mul_def] using ih
theorem reverseExposedRotationLabel_length (hopt : IsManOptimal p μ₀) (hμ : IsStable p μ)
    (σ : {σ : Equiv.Perm (Fin n) // IsReverseExposedRotation p μ σ}) :
    rotationLength (reverseExposedRotationLabel hopt hμ σ) = σ.val.support.card := by
  change (μ⁻¹ * σ.val * (μ⁻¹)⁻¹).support.card = _
  exact Equiv.Perm.card_support_conj
private def reverseFactorEmbedding {σ : Matching n}
    (hσ : RealizesSuccessorPermutation (swapProfile p) μ.symm σ) :
    (↥σ.cycleFactorsFinset) ↪ {τ : Equiv.Perm (Fin n) // IsReverseExposedRotation p μ τ} :=
  ⟨fun τ ↦ ⟨τ.val, realizesSuccessorPermutation_iff_factors.mp hσ τ.val τ.property⟩,
    fun _ _ h ↦ Subtype.ext (congrArg
      (fun t : {τ : Equiv.Perm (Fin n) // IsReverseExposedRotation p μ τ} ↦ t.val) h)⟩
private noncomputable def realizedReverseRemovedLabels (hopt : IsManOptimal p μ₀) (hμ : IsStable p μ)
    {σ : Matching n} (hσ : RealizesSuccessorPermutation (swapProfile p) μ.symm σ) :
    Finset (MaximalEliminatedRotation p μ₀ μ) :=
  σ.cycleFactorsFinset.attach.map
    ((reverseFactorEmbedding hσ).trans (reverseExposedRotationEquivMaximal hopt hμ).toEmbedding)
theorem realizedReverseRemovedLabels_totalLength (hopt : IsManOptimal p μ₀)
    (hμ : IsStable p μ) {σ : Matching n}
    (hσ : RealizesSuccessorPermutation (swapProfile p) μ.symm σ) :
    (∑ t ∈ realizedReverseRemovedLabels hopt hμ hσ, rotationLength t.val) =
      σ.support.card := by
  rw [realizedReverseRemovedLabels, Finset.sum_map, card_support_eq_sum_cycleFactors_support]
  calc
    _ = ∑ t ∈ σ.cycleFactorsFinset.attach, t.val.support.card :=
      Finset.sum_congr rfl fun t _ ↦ reverseExposedRotationLabel_length hopt hμ
        (reverseFactorEmbedding hσ t)
    _ = _ := Finset.sum_attach σ.cycleFactorsFinset
      (fun t : Equiv.Perm (Fin n) ↦ t.support.card)
theorem realizedReverseRemovedLabels_short_card (hopt : IsManOptimal p μ₀) (hμ : IsStable p μ)
    {σ : Matching n} (hσ : RealizesSuccessorPermutation (swapProfile p) μ.symm σ) (L : ℕ) :
    ((realizedReverseRemovedLabels hopt hμ hσ).filter
      (fun r ↦ rotationLength r.val ≤ L)).card = (σ.cycleType.filter (· ≤ L)).card := by
  rw [realizedReverseRemovedLabels, Finset.filter_map, Finset.card_map]
  have hlen (t : σ.cycleFactorsFinset) :
      rotationLength (((reverseFactorEmbedding hσ).trans
        (reverseExposedRotationEquivMaximal hopt hμ).toEmbedding) t).val = t.val.support.card :=
    reverseExposedRotationLabel_length hopt hμ (reverseFactorEmbedding hσ t)
  simp only [Function.comp_def, hlen, Equiv.Perm.cycleType_def, Multiset.filter_map, Multiset.card_map]
  rw [Finset.filter_attach (fun t : Matching n ↦ t.support.card ≤ L), Finset.card_map,
    Finset.card_attach]
  rfl
theorem undoMaximalSubsetEmbedding_realizedReverseRemovedLabels (hopt : IsManOptimal p μ₀)
    (hμ : IsStable p μ) {σ : Matching n}
    (hσ : RealizesSuccessorPermutation (swapProfile p) μ.symm σ) :
    (undoMaximalSubsetEmbedding hopt hμ (realizedReverseRemovedLabels hopt hμ hσ)).val =
      undoReverseRotation μ σ := by
  classical
  let S := σ.cycleFactorsFinset
  let f := reverseFactorEmbedding hσ
  let rs := S.attach.toList.map f
  have hnd : rs.Nodup := S.attach.nodup_toList.map f.injective
  have hset : (rs.map Subtype.val).toFinset = S := by
    ext τ
    simp only [List.mem_toFinset, List.mem_map, rs, Finset.mem_toList]
    constructor
    · rintro ⟨_, ⟨t, _, rfl⟩, rfl⟩
      exact t.property
    · intro ht
      exact ⟨f ⟨τ, ht⟩, ⟨⟨τ, ht⟩, Finset.mem_attach S _, rfl⟩, rfl⟩
  have hprod : (rs.map Subtype.val).prod = σ := by
    let L := rs.map Subtype.val
    have hc : (↑L.toFinset : Set (Matching n)).Pairwise (Function.onFun Commute id) := by
      rw [show L.toFinset = S from hset]
      exact σ.cycleFactorsFinset_mem_commute
    calc
      _ = L.toFinset.noncommProd id hc := by
        simpa only [List.map_id] using
          (Finset.noncommProd_toFinset L id hc (hnd.map Subtype.val_injective)).symm
      _ = S.noncommProd id σ.cycleFactorsFinset_mem_commute :=
        Finset.noncommProd_congr hset (fun _ _ ↦ rfl) hc
      _ = σ := σ.cycleFactorsFinset_noncommProd
  obtain ⟨M, hseq, hpath⟩ := exists_rotationUndoSequence_of_reverse_cycles hopt hμ rs hnd
  have hM : M = undoReverseRotation μ σ := by
    have he := hseq.eq_mul_listProd
    rw [hprod] at he
    change M.symm = eliminateRotation μ.symm σ at he
    exact congrArg Equiv.symm he
  let D := realizedReverseRemovedLabels hopt hμ hσ
  let N := undoMaximalSubsetEmbedding hopt hμ D
  let e := f.trans (reverseExposedRotationEquivMaximal hopt hμ).toEmbedding
  have hD : D = S.attach.map e := rfl
  have hlabels : {q | q ∈ rs.map (reverseExposedRotationLabel hopt hμ)} =
      Subtype.val '' (D : Set (MaximalEliminatedRotation p μ₀ μ)) := by
    ext q
    constructor
    · intro hq
      obtain ⟨t, ht, he⟩ := List.mem_map.mp hq
      obtain ⟨s, _, rfl⟩ := List.mem_map.mp ht
      refine ⟨e s, ?_, he⟩
      change e s ∈ D
      rw [hD]
      exact Finset.mem_map.mpr ⟨s, Finset.mem_attach S _, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      change t ∈ D at ht
      rw [hD] at ht
      obtain ⟨s, hs, rfl⟩ := Finset.mem_map.mp ht
      exact List.mem_map.mpr ⟨f s, List.mem_map.mpr ⟨s, Finset.mem_toList.mpr hs, rfl⟩, rfl⟩
  have hMI : eliminatedRotations p μ₀ M = eliminatedRotations p μ₀ N.val := by
    rw [hpath.eliminatedRotations_end, hlabels, eliminatedRotations_undoMaximalSubsetEmbedding]
  have hMN : M = N.val :=
    congrArg Subtype.val ((stableMatchingToRotationIdeal_bijective hopt).1
      (LowerSet.ext hMI : stableMatchingToRotationIdeal ⟨M, hpath.isStable_end⟩ =
        stableMatchingToRotationIdeal N))
  exact hMN.symm.trans hM
private abbrev IsCompatibleReversePermutation (hopt : IsManOptimal p μ₀) (K : ℕ)
    (r : Rotation p μ₀) (σ : Matching n) : Prop :=
  let A := singletonRotationAnchor hopt r
  RealizesSuccessorPermutation (swapProfile p) A.val.symm σ ∧
    σ.support.card ≤ K ∧
    (∀ m ∈ r.val.cycle.support, A.val m ∉ σ.support) ∧
    IsExposedRotation p (undoReverseRotation A.val σ) r.val.cycle
private abbrev CompatibleReversePermutation (hopt : IsManOptimal p μ₀) (K : ℕ)
    (r : Rotation p μ₀) :=
  {σ : Matching n // IsCompatibleReversePermutation hopt K r σ}
private noncomputable def compatibleReversePermutationToDecoration (hopt : IsManOptimal p μ₀)
    (K : ℕ) (r : Rotation p μ₀) (σ : CompatibleReversePermutation hopt K r) :
    PivotDecoration hopt K r := by
  let A := singletonRotationAnchor hopt r
  let D := realizedReverseRemovedLabels hopt A.property σ.property.1
  have hN : (undoMaximalSubsetEmbedding hopt A.property D).val =
      undoReverseRotation A.val σ.val :=
    undoMaximalSubsetEmbedding_realizedReverseRemovedLabels hopt A.property σ.property.1
  have hfix (m : Fin n) (hm : r.val.cycle m ≠ m) :
      undoReverseRotation A.val σ.val m = A.val m := by
    have hsm : σ.val (A.val m) = A.val m := by
      by_contra hn
      exact σ.property.2.2.1 m (Equiv.Perm.mem_support.mpr hm) (Equiv.Perm.mem_support.mpr hn)
    apply (undoReverseRotation A.val σ.val).symm.injective
    rw [Equiv.symm_apply_apply]
    change m = A.val.symm (σ.val (A.val m))
    rw [hsm, Equiv.symm_apply_apply]
  have hpivot := ((eq_singletonRotationAnchor_iff hopt r A).mp rfl r).mpr rfl
  refine ⟨D, (realizedReverseRemovedLabels_totalLength hopt A.property σ.property.1).le.trans
    σ.property.2.1, ?_⟩
  change r.IsExposedAt (undoMaximalSubsetEmbedding hopt A.property D).val
  rw [hN]
  exact ⟨σ.property.2.2.2, (rotationLabel_eq_of_fixed_on_cycle hfix).trans hpivot.2⟩
theorem compatibleReversePermutationToDecoration_removed (hopt : IsManOptimal p μ₀)
    (K : ℕ) (r : Rotation p μ₀) (σ : CompatibleReversePermutation hopt K r) :
    (compatibleReversePermutationToDecoration hopt K r σ).removed =
      realizedReverseRemovedLabels hopt (singletonRotationAnchor hopt r).property σ.property.1 :=
  rfl
theorem compatibleReversePermutationToDecoration_matching (hopt : IsManOptimal p μ₀)
    (K : ℕ) (r : Rotation p μ₀) (σ : CompatibleReversePermutation hopt K r) :
    (compatibleReversePermutationToDecoration hopt K r σ).matching.val =
      undoReverseRotation (singletonRotationAnchor hopt r).val σ.val :=
  undoMaximalSubsetEmbedding_realizedReverseRemovedLabels hopt
    (singletonRotationAnchor hopt r).property σ.property.1
private noncomputable def compatibleReversePermutationEmbedding (hopt : IsManOptimal p μ₀)
    (K : ℕ) (r : Rotation p μ₀) :
    CompatibleReversePermutation hopt K r ↪ PivotDecoration hopt K r :=
  ⟨compatibleReversePermutationToDecoration hopt K r, by
    intro σ τ h
    have he := congrArg (fun D : PivotDecoration hopt K r ↦ D.matching.val) h
    change (compatibleReversePermutationToDecoration hopt K r σ).matching.val =
      (compatibleReversePermutationToDecoration hopt K r τ).matching.val at he
    rw [compatibleReversePermutationToDecoration_matching,
      compatibleReversePermutationToDecoration_matching] at he
    apply Subtype.ext
    apply Equiv.ext
    intro w
    exact (singletonRotationAnchor hopt r).val.symm.injective
      (congrArg (fun ν : Matching n ↦ ν.symm w) he)⟩
end IncomparableLP
end

-- PivotCompatibleLowerMoment
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace IncomparableLP
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
    exact ⟨he,hm⟩
  · rintro ⟨he,hm⟩
    constructor <;> assumption
private abbrev SourceExposed {n} (p : Profile n) (μ ρ : Matching n) : Prop :=
  premise (@MarkedLP.IsExposedRotation.womanRank_eliminate_le n p μ ρ)
private lemma sourceExposed_iff {n} (p : Profile n) (μ ρ : Matching n) :
    SourceExposed p μ ρ ↔ IsExposedRotation p μ ρ := by
  constructor
  · rintro ⟨hc,hs⟩
    exact ⟨hc,fun m hm => (sourceSuccessor_iff ..).mp (hs m hm)⟩
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
end IncomparableLP
end

-- PivotReverseIncrementFilter
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace IncomparableLP
private def reverseScoreIncrement {n : ℕ} (x : ScoreProfile n) (μ : Matching n)
    (w j : Fin n) : ℝ := x (.inr w) j - x (.inr w) (μ.symm w)
theorem measurable_reverseScoreIncrement {n : ℕ} (μ : Matching n) (w j : Fin n) :
    Measurable (fun x : ScoreProfile n ↦ reverseScoreIncrement x μ w j) := by
  have hrow : Measurable (fun x : ScoreProfile n ↦ x (.inr w)) := measurable_pi_apply _
  exact ((measurable_pi_apply j).comp hrow).sub ((measurable_pi_apply (μ.symm w)).comp hrow)
private noncomputable def reverseIncrementCutoff (n : ℕ) (X : ℝ) : ℝ := 16 * Real.log (n : ℝ) / X
end IncomparableLP
end

-- PivotReverseFilteredCount
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace IncomparableLP
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
theorem measurable_finsetCard_of_mem {Ω α : Type*} [MeasurableSpace Ω] [Fintype α]
    (F : Ω → Finset α) (hF : ∀ a, MeasurableSet {z | a ∈ F z}) :
    Measurable (fun z ↦ ((F z).card : ℝ≥0∞)) := by
  classical
  let G (a : α) := ({z | a ∈ F z} : Set Ω).indicator (fun _ ↦ (1 : ℝ≥0∞))
  have hG (a : α) : Measurable (G a) := measurable_const.indicator (hF a)
  have he : (fun z ↦ ((F z).card : ℝ≥0∞)) = fun z ↦ ∑ a, G a z := by
    funext z
    have hs : Finset.univ.filter (fun a ↦ a ∈ F z) = F z := by ext a; simp
    simp only [G, indicator_apply, mem_ofPred_eq, ← Finset.sum_filter, hs]
    simp
  rw [he]
  exact Finset.measurable_sum _ fun a _ ↦ hG a
end IncomparableLP
end

-- PivotForwardExposureReveal
section
open MeasureTheory Set StableMarriage
namespace IncomparableLP
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
    refine ⟨h.isCycle, fun m hm ↦ ?_⟩
    let q₀ : OffDiagonalCellIndex n := ⟨(m, ρ m), hm.symm⟩
    let q : ForwardActiveCellIndex flag := ⟨q₀,
      (forwardEligible_iff_flag μ x flag ht hmask m (ρ m) hm.symm).mp (h.successor m hm).eligible⟩
    refine ⟨q, rfl, fun t htm ↦ ?_⟩
    have htne : m ≠ t.val.val.2 := htm.symm ▸ t.val.property
    have hteq : (⟨(m, t.val.val.2), htne⟩ : OffDiagonalCellIndex n) = t.val :=
      Subtype.ext (Prod.ext htm.symm rfl)
    have hflag : flag ⟨(m, t.val.val.2), htne⟩ = true := by rw [hteq]; exact t.property
    have htel := (forwardEligible_iff_flag μ x flag ht hmask m t.val.val.2 htne).mpr hflag
    change v q ≤ v t
    rw [hscore q, hscore t, htm]
    exact (hle m (ρ m) t.val.val.2).mp ((h.successor m hm).min_rank _ htel)
  · rintro ⟨hcyc, htest⟩
    refine ⟨hcyc, fun m hm ↦ ?_⟩
    obtain ⟨q, hq, hmin⟩ := htest m hm
    have hq' : (⟨(m, ρ m), hm.symm⟩ : OffDiagonalCellIndex n) = q.val := Subtype.ext hq.symm
    refine ⟨(forwardEligible_iff_flag μ x flag ht hmask m (ρ m) hm.symm).mpr
      (hq' ▸ q.property), ?_⟩
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
end IncomparableLP
end

-- PivotPairToggle
section
open StableMarriage
open scoped BigOperators
namespace IncomparableLP
variable {n : ℕ} {p : Profile n} {μ₀ : Matching n} {hopt : IsManOptimal p μ₀}
  {K : ℕ} {r : Rotation p μ₀}
namespace PivotDecoration
private def removedLabels (D : PivotDecoration hopt K r) : Set (Rotation p μ₀) :=
  Subtype.val '' (↑D.removed :
    Set (MaximalEliminatedRotation p μ₀ (singletonRotationAnchor hopt r).val))
theorem matching_eliminated (D : PivotDecoration hopt K r) :
    eliminatedRotations p μ₀ D.matching.val =
      eliminatedRotations p μ₀ (singletonRotationAnchor hopt r).val \ D.removedLabels :=
  eliminatedRotations_undoMaximalSubsetEmbedding hopt
    (singletonRotationAnchor hopt r).property D.removed
private noncomputable def eraseRemovedLabel (D : PivotDecoration hopt K r) (γ : Rotation p μ₀) :
    PivotDecoration hopt K r := by
  classical
  let E := D.removed.filter (fun s ↦ s.val ≠ γ)
  have hE : E ⊆ D.removed := Finset.filter_subset _ _
  refine ⟨E, ?_, ?_⟩
  · exact (Finset.sum_le_sum_of_subset_of_nonneg hE
      (fun _ _ _ ↦ Nat.zero_le _)).trans D.totalLength_le
  · apply (pivot_isExposedAt_undo_iff hopt r E).mpr
    rintro _ ⟨s, hs, rfl⟩
    exact (pivot_isExposedAt_undo_iff hopt r D.removed).mp D.pivot_exposed _
      ⟨s, hE hs, rfl⟩
@[simp] theorem mem_eraseRemovedLabel (D : PivotDecoration hopt K r) (γ : Rotation p μ₀)
    (s : MaximalEliminatedRotation p μ₀ (singletonRotationAnchor hopt r).val) :
    s ∈ (D.eraseRemovedLabel γ).removed ↔ s ∈ D.removed ∧ s.val ≠ γ := by
  classical
  exact Finset.mem_filter
theorem notMem_removedLabels_eraseRemovedLabel (D : PivotDecoration hopt K r)
    (γ : Rotation p μ₀) : γ ∉ (D.eraseRemovedLabel γ).removedLabels := by
  rintro ⟨s, hs, hsg⟩
  exact ((mem_eraseRemovedLabel D γ s).mp hs).2 hsg
private theorem mem_removedLabels_iff (D : PivotDecoration hopt K r)
    (s : MaximalEliminatedRotation p μ₀ (singletonRotationAnchor hopt r).val) :
    s.val ∈ D.removedLabels ↔ s ∈ D.removed := by
  constructor
  · rintro ⟨t, ht, hts⟩
    exact Subtype.ext hts ▸ ht
  · intro hs
    exact ⟨s, hs, rfl⟩
theorem eq_of_eraseRemovedLabel_eq {D E : PivotDecoration hopt K r} (γ : Rotation p μ₀)
    (h : D.eraseRemovedLabel γ = E.eraseRemovedLabel γ)
    (hbit : γ ∈ D.removedLabels ↔ γ ∈ E.removedLabels) : D = E := by
  have hsets : D.removed = E.removed := by
    ext s
    by_cases hs : s.val = γ
    · rw [← mem_removedLabels_iff, ← mem_removedLabels_iff, hs]
      exact hbit
    · have he : s ∈ (D.eraseRemovedLabel γ).removed ↔
          s ∈ (E.eraseRemovedLabel γ).removed := by rw [h]
      simpa only [mem_eraseRemovedLabel, and_iff_left hs] using he
  cases D
  cases E
  cases hsets
  rfl
end PivotDecoration
private abbrev PivotCode (hopt : IsManOptimal p μ₀) (K : ℕ) :=
  Σ r : LongPivot p μ₀ K, PivotDecoration hopt K r.val
private structure ResidualPivotPair (hopt : IsManOptimal p μ₀) (K : ℕ) where
  early : PivotCode hopt K
  late : PivotCode hopt K
  pivot_lt : early.1.val < late.1.val
  shared : ∃ γ ∈ late.2.removedLabels,
    γ ∈ eliminatedRotations p μ₀ (singletonRotationAnchor hopt early.1.val).val
private abbrev IncomparableStableMatchingPair (p : Profile n) (μ₀ : Matching n) :=
  {MN : {M : Matching n // IsStable p M} × {N : Matching n // IsStable p N} //
    (¬ eliminatedRotations p μ₀ MN.1.val ⊆ eliminatedRotations p μ₀ MN.2.val) ∧
    (¬ eliminatedRotations p μ₀ MN.2.val ⊆ eliminatedRotations p μ₀ MN.1.val)}
namespace ResidualPivotPair
private noncomputable def sharedLabel (R : ResidualPivotPair hopt K) : Rotation p μ₀ :=
  Classical.choose R.shared
theorem sharedLabel_mem_late (R : ResidualPivotPair hopt K) :
    R.sharedLabel ∈ R.late.2.removedLabels :=
  (Classical.choose_spec R.shared).1
theorem sharedLabel_mem_early_anchor (R : ResidualPivotPair hopt K) :
    R.sharedLabel ∈
      eliminatedRotations p μ₀ (singletonRotationAnchor hopt R.early.1.val).val :=
  (Classical.choose_spec R.shared).2
private noncomputable def toggledEarly (R : ResidualPivotPair hopt K) : PivotCode hopt K :=
  ⟨R.early.1, R.early.2.eraseRemovedLabel R.sharedLabel⟩
private noncomputable def toggleImage (R : ResidualPivotPair hopt K) :
    IncomparableStableMatchingPair p μ₀ := by
  refine ⟨(R.toggledEarly.2.matching, R.late.2.matching), ?_, ?_⟩
  · intro h
    have he : R.sharedLabel ∈ eliminatedRotations p μ₀ R.toggledEarly.2.matching.val := by
      rw [PivotDecoration.matching_eliminated]
      exact ⟨R.sharedLabel_mem_early_anchor,
        R.early.2.notMem_removedLabels_eraseRemovedLabel R.sharedLabel⟩
    have hl := h he
    rw [PivotDecoration.matching_eliminated] at hl
    exact hl.2 R.sharedLabel_mem_late
  · intro h
    have hl : R.early.1.val ∈ eliminatedRotations p μ₀ R.late.2.matching.val :=
      (Rotation.lt_iff_before_exposure hopt R.pivot_lt.ne).mp R.pivot_lt
        _ R.late.2.matching.property R.late.2.pivot_exposed.1 R.late.2.pivot_exposed.2
    have he := h hl
    rw [PivotDecoration.matching_eliminated, eliminatedRotations_singletonRotationAnchor] at he
    apply he.1
    change R.toggledEarly.1.val ≤ R.early.1.val
    exact le_rfl
private noncomputable def toggleBit (R : ResidualPivotPair hopt K) : Bool := by
  classical
  exact decide (R.sharedLabel ∈ R.early.2.removedLabels)
private theorem eq_of_toggled_codes_and_bit {R S : ResidualPivotPair hopt K}
    (hA : R.toggledEarly = S.toggledEarly) (hB : R.late = S.late)
    (hbit : R.toggleBit = S.toggleBit) : R = S := by
  classical
  rcases R with ⟨⟨a, D⟩, L, hlt, hshared⟩
  rcases S with ⟨⟨b, E⟩, L', hlt', hshared'⟩
  have hab : a = b := congrArg Sigma.fst hA
  subst b
  change L = L' at hB
  subst L'
  let γ := Classical.choose hshared
  change (⟨a, D.eraseRemovedLabel γ⟩ : PivotCode hopt K) =
    ⟨a, E.eraseRemovedLabel γ⟩ at hA
  change decide (γ ∈ D.removedLabels) = decide (γ ∈ E.removedLabels) at hbit
  have hdec : γ ∈ D.removedLabels ↔ γ ∈ E.removedLabels := by
    simpa using hbit
  have hDE : D = E := PivotDecoration.eq_of_eraseRemovedLabel_eq γ
    (eq_of_heq (Sigma.mk.inj_iff.mp hA).2) hdec
  subst E
  rfl
private noncomputable def toggleEmbedding (hopt : IsManOptimal p μ₀) (K : ℕ) :
    ResidualPivotPair hopt K ↪ IncomparableStableMatchingPair p μ₀ × Bool :=
  ⟨fun R ↦ (R.toggleImage, R.toggleBit), by
    intro R S h
    have hpair := congrArg (fun z : IncomparableStableMatchingPair p μ₀ × Bool ↦ z.1.val) h
    have hA : R.toggledEarly = S.toggledEarly :=
      (pivotDecorationEmbedding hopt K).injective (congrArg Prod.fst hpair)
    have hB : R.late = S.late :=
      (pivotDecorationEmbedding hopt K).injective (congrArg Prod.snd hpair)
    exact eq_of_toggled_codes_and_bit hA hB (congrArg Prod.snd h)⟩
private instance (hopt : IsManOptimal p μ₀) (K : ℕ) : Finite (ResidualPivotPair hopt K) :=
  Finite.of_injective (toggleEmbedding hopt K) (toggleEmbedding hopt K).injective
end ResidualPivotPair
end IncomparableLP
end

-- PivotFilteredDecoration
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace IncomparableLP
variable {n : ℕ} {x : ScoreProfile n} {μ₀ : Matching n}
  {hopt : IsManOptimal (profileOfScores x) μ₀} {K : ℕ}
  {r : Rotation (profileOfScores x) μ₀}
open scoped Classical in
private def PivotDecoration.PassesReverseFilters (D : PivotDecoration hopt K r) (L : ℕ) (t : ℝ) : Prop :=
  ((D.removed.filter (fun s ↦ rotationLength s.val ≤ L)).card : ℝ) ≤
    (3 / 2 : ℝ) * Real.log (L : ℝ) ∧
  ∀ w, femaleSpouseScore x D.matching.val w -
    femaleSpouseScore x (singletonRotationAnchor hopt r).val w ≤ t
private abbrev FilteredPivotDecoration (hopt : IsManOptimal (profileOfScores x) μ₀) (K : ℕ)
    (r : Rotation (profileOfScores x) μ₀) (L : ℕ) (t : ℝ) :=
  {D : PivotDecoration hopt K r // D.PassesReverseFilters L t}
theorem compatibleReversePermutationToDecoration_passesReverseFilters
    (σ : CompatibleReversePermutation hopt K r) {L : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (hcap : ¬ shortCycleCapBad L σ.val.cycleType)
    (hinc : reverseCollectionIncrementGood x (singletonRotationAnchor hopt r).val σ.val t) :
    (compatibleReversePermutationToDecoration hopt K r σ).PassesReverseFilters L t := by
  classical
  let A := singletonRotationAnchor hopt r
  constructor
  · rw [compatibleReversePermutationToDecoration_removed, realizedReverseRemovedLabels_short_card]
    exact not_lt.mp hcap
  · intro w
    rw [compatibleReversePermutationToDecoration_matching]
    change x (.inr w) ((undoReverseRotation A.val σ.val).symm w) -
      x (.inr w) (A.val.symm w) ≤ t
    rw [undoReverseRotation_symm_apply]
    by_cases hw : w ∈ σ.val.support
    · exact hinc w hw
    · rw [Equiv.Perm.notMem_support.mp hw, sub_self]
      exact ht
end IncomparableLP
end

-- PivotEligibleRevealControls
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace IncomparableLP
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
end IncomparableLP
end

-- PivotSpouseBandMask
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace IncomparableLP
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
end IncomparableLP
end

-- PivotForwardRowDeficit
section
open Filter MeasureTheory Set
open scoped BigOperators ENNReal
namespace IncomparableLP
private noncomputable def forwardSpouseWeight {n : ℕ} (d : DiagonalScorePairs n) (i : Fin n) : ℝ :=
  (diagonalPairAt d i).2 / ∑ j, (diagonalPairAt d j).2
end IncomparableLP
end

-- PivotForwardForest
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace IncomparableLP
private def IsSoleForwardExposedRotation {n : ℕ} (p : Profile n) (μ σ : Matching n) : Prop :=
  IsExposedRotation p μ σ ∧ ∀ τ, IsExposedRotation p μ τ → τ = σ
end IncomparableLP
end

-- PivotLocalEligibility
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace IncomparableLP
private def certifiedSet {α : Type} [MeasurableSpace α] {t : Set α} (_ : MeasurableSet t) := t
private def LocalPivotGeometry {n : ℕ} (b A B : ℝ) (μ ρ : Matching n)
    (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool) : Prop :=
  d ∈ certifiedSet (MarkedLP.measurableSet_localPivotGeometry b A B μ ρ flag)
private theorem LocalPivotGeometry.length_lower {n : ℕ} {b A B : ℝ} {μ ρ : Matching n}
    {d : DiagonalScorePairs n} {flag : OffDiagonalCellIndex n → Bool}
    (h : LocalPivotGeometry b A B μ ρ d flag) : b * Real.sqrt (n : ℝ) ≤ (ρ.support.card : ℝ) := by
  obtain ⟨_,_,he,_,_,_,_,_⟩ := h
  exact he
private noncomputable def localPivotIncrementCap {n : ℕ} (B : ℝ) (d : DiagonalScorePairs n) : ℝ :=
  B * Real.sqrt (n : ℝ) / pivotDiagonalFemaleTotal d
private def IsLocallyEligiblePivot {n : ℕ} (b A B : ℝ) (x : ScoreProfile n)
    (μ ρ : Matching n) : Prop :=
  let z := splitScorePairs μ x
  let flag := forwardMaskOfScores z.1 z.2
  LocalPivotGeometry b A B μ ρ z.1 flag ∧
    (forwardRevealWithColumns flag z.2).1 ∈
      eligiblePivotRevealSet z.1 flag ρ (localPivotIncrementCap B z.1)
theorem IsLocallyEligiblePivot.isSoleForwardExposed {n : ℕ} {b A B : ℝ}
    {x : ScoreProfile n} {μ ρ : Matching n}
    (h : IsLocallyEligiblePivot b A B x μ ρ)
    (ht : ∀ row, Function.Injective (x row)) :
    IsSoleForwardExposedRotation (profileOfScores x) μ ρ := by
  let z := splitScorePairs μ x
  let flag := forwardMaskOfScores z.1 z.2
  have hmask : z.2 ∈ forwardScoreMaskEvent z.1 flag :=
    (forwardMaskOfScores_eq_iff _ _ _).mp rfl
  have he (τ : Matching n) := (isExposedRotation_iff_forwardRevealExposureEvent μ τ x flag ht
    hmask).trans (h.2.1 τ)
  exact ⟨(he ρ).mpr rfl, fun τ hτ ↦ (he τ).mp hτ⟩
private theorem measurable_diagonalMaleScore {n : ℕ} (i : Fin n) :
    Measurable (fun d : DiagonalScorePairs n ↦ (diagonalPairAt d i).1) :=
  (measurable_pi_apply _).fst
private theorem measurable_diagonalFemaleScore {n : ℕ} (i : Fin n) :
    Measurable (fun d : DiagonalScorePairs n ↦ (diagonalPairAt d i).2) :=
  (measurable_pi_apply _).snd
private theorem measurable_reverseDiagonalMaleTotal (n : ℕ) :
    Measurable (@reverseDiagonalMaleTotal n) :=
  Finset.measurable_sum _ fun i _ ↦ measurable_diagonalMaleScore i
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
end IncomparableLP
end

-- PivotMarkedDecorationCount
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace IncomparableLP
variable {n : ℕ}
private noncomputable def markedFilteredChoices (μ ρ : Matching n)
    (flag : OffDiagonalCellIndex n → Bool) (K L : ℕ) (t : ℝ) (x : ScoreProfile n) :
    Finset (Matching n) := by
  classical
  exact Finset.univ.filter fun σ ↦ σ.support.card ≤ K ∧
    σ ∈ filteredReverseSupportFamily μ ρ flag σ.support.card L t x
theorem mem_markedFilteredChoices {μ ρ σ : Matching n} {flag : OffDiagonalCellIndex n → Bool}
    {K L : ℕ} {t : ℝ} {x : ScoreProfile n} :
    σ ∈ markedFilteredChoices μ ρ flag K L t x ↔ σ.support.card ≤ K ∧
      σ ∈ filteredReverseSupportFamily μ ρ flag σ.support.card L t x := by
  classical
  simp [markedFilteredChoices]
theorem measurableSet_mem_markedFilteredChoices (μ ρ σ : Matching n)
    (flag : OffDiagonalCellIndex n → Bool) (K L : ℕ)
    {t : ScoreProfile n → ℝ} (ht : Measurable t) :
    MeasurableSet {x : ScoreProfile n | σ ∈ markedFilteredChoices μ ρ flag K L (t x) x} := by
  classical
  have hinc :
      MeasurableSet {x : ScoreProfile n | reverseCollectionIncrementGood x μ σ (t x)} := by
    have he : {x : ScoreProfile n | reverseCollectionIncrementGood x μ σ (t x)} =
        ⋂ w : σ.support, {x : ScoreProfile n |
          reverseScoreIncrement x μ w.val (μ.symm (σ w.val)) ≤ t x} := by
      ext x
      exact ⟨fun h ↦ mem_iInter.mpr fun w ↦ h w.val w.property,
        fun h w hw ↦ mem_iInter.mp h ⟨w, hw⟩⟩
    rw [he]
    exact MeasurableSet.iInter fun w ↦
      measurableSet_le (measurable_reverseScoreIncrement μ w.val (μ.symm (σ w.val))) ht
  have hcomp : MeasurableSet {x : ScoreProfile n |
      σ ∈ compatibleReverseSupportFamily μ ρ flag σ.support.card (profileOfScores x)} :=
    measurable_profileOfScores n (MeasurableSet.of_discrete : MeasurableSet
      {p : Profile n | σ ∈ compatibleReverseSupportFamily μ ρ flag σ.support.card p})
  simp only [mem_markedFilteredChoices, filteredReverseSupportFamily, Finset.mem_filter,
    ofPred_and]
  exact (MeasurableSet.const _).inter (hcomp.inter ((MeasurableSet.const _).inter hinc))
theorem measurable_card_markedFilteredChoices (μ ρ : Matching n)
    (flag : OffDiagonalCellIndex n → Bool) (K L : ℕ)
    {t : ScoreProfile n → ℝ} (ht : Measurable t) :
    Measurable (fun x ↦ ((markedFilteredChoices μ ρ flag K L (t x) x).card : ℝ)) := by
  have h := measurable_finsetCard_of_mem (fun x ↦ markedFilteredChoices μ ρ flag K L (t x) x)
    (fun σ ↦ measurableSet_mem_markedFilteredChoices μ ρ σ flag K L ht)
  simpa only [Function.comp_def, ENNReal.toReal_natCast] using
    ENNReal.measurable_toReal.comp h
private noncomputable def localFilteredDecorationCount (b A B : ℝ) (K L : ℕ) (μ ρ : Matching n)
    (x : ScoreProfile n) : ℝ := by
  classical
  exact if IsLocallyEligiblePivot b A B x μ ρ then
    ((markedFilteredChoices μ ρ (forwardMaskOfScores (splitScorePairs μ x).1
      (splitScorePairs μ x).2) K L (reverseIncrementCutoff n (maleSpouseTotal x μ)) x).card : ℝ)
    else 0
private theorem measurable_mask_switch {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [Countable β] [MeasurableSingletonClass β] {M : α → β}
    (hM : Measurable M) {f : β → α → γ} (hf : ∀ j, Measurable (f j)) :
    Measurable (fun x ↦ f (M x) x) := by
  intro s hs
  let E (j : β) := {x : α | M x = j ∧ f j x ∈ s}
  have he : (fun x ↦ f (M x) x) ⁻¹' s = ⋃ j, E j := by
    ext x
    change f (M x) x ∈ s ↔ x ∈ ⋃ j, E j
    simp only [mem_iUnion, E, mem_ofPred_eq]
    exact ⟨fun hx ↦ ⟨M x, rfl, hx⟩, fun ⟨j, hj, hx⟩ ↦ hj.symm ▸ hx⟩
  rw [he]
  exact MeasurableSet.iUnion fun j ↦ (hM (measurableSet_singleton j)).inter (hf j hs)
theorem measurable_localFilteredDecorationCount (b A B : ℝ) (K L : ℕ) (μ ρ : Matching n) :
    Measurable (localFilteredDecorationCount b A B K L μ ρ) := by
  classical
  let M (x : ScoreProfile n) :=
    forwardMaskOfScores (splitScorePairs μ x).1 (splitScorePairs μ x).2
  let t (x : ScoreProfile n) := reverseIncrementCutoff n (maleSpouseTotal x μ)
  let f (flag : OffDiagonalCellIndex n → Bool) (x : ScoreProfile n) :=
    ((markedFilteredChoices μ ρ flag K L (t x) x).card : ℝ)
  have hM : Measurable M :=
    (measurable_jointForwardMaskOfScores n).comp (splitScorePairs μ).measurable
  have ht : Measurable t := measurable_const.div (measurable_maleSpouseTotal μ)
  have hf (flag : OffDiagonalCellIndex n → Bool) : Measurable (f flag) :=
    measurable_card_markedFilteredChoices μ ρ flag K L ht
  exact (measurable_mask_switch hM hf).ite (measurableSet_isLocallyEligiblePivot b A B μ ρ)
    measurable_const
theorem localFilteredDecorationCount_nonneg (b A B : ℝ) (K L : ℕ)
    (μ ρ : Matching n) (x : ScoreProfile n) :
    0 ≤ localFilteredDecorationCount b A B K L μ ρ x := by
  classical
  unfold localFilteredDecorationCount
  split <;> positivity
theorem localFilteredDecorationCount_le_factorial (b A B : ℝ) (K L : ℕ)
    (μ ρ : Matching n) (x : ScoreProfile n) :
    localFilteredDecorationCount b A B K L μ ρ x ≤ (n.factorial : ℝ) := by
  classical
  unfold localFilteredDecorationCount
  split
  · apply Nat.cast_le.mpr
    simpa only [Fintype.card_perm, Fintype.card_fin] using
      Finset.card_le_univ (markedFilteredChoices μ ρ
        (forwardMaskOfScores (splitScorePairs μ x).1 (splitScorePairs μ x).2)
        K L (reverseIncrementCutoff n (maleSpouseTotal x μ)) x)
  · positivity
section MatchingEndpoints
variable {x : ScoreProfile n} {μ₀ μ ρ σ : Matching n}
  {flag : OffDiagonalCellIndex n → Bool} {K L : ℕ} {t : ℝ}
theorem isCompatibleReversePermutation_of_mem_markedFilteredChoices
    (hopt : IsManOptimal (profileOfScores x) μ₀) (r : Rotation (profileOfScores x) μ₀)
    (hμ : (singletonRotationAnchor hopt r).val = μ) (hρ : r.val.cycle = ρ)
    (hσ : σ ∈ markedFilteredChoices μ ρ flag K L t x) :
    IsCompatibleReversePermutation hopt K r σ := by
  classical
  obtain ⟨hcap, hm⟩ := mem_markedFilteredChoices.mp hσ
  have hc := mem_compatibleReversePermutations.mp (Finset.mem_filter.mp hm).1
  have hg := (mem_goodReverseSupportPermutations.mp hc.1).2
  change RealizesSuccessorPermutation (swapProfile (profileOfScores x))
    (singletonRotationAnchor hopt r).val.symm σ ∧ σ.support.card ≤ K ∧
    (∀ m ∈ r.val.cycle.support, (singletonRotationAnchor hopt r).val m ∉ σ.support) ∧
    IsExposedRotation (profileOfScores x)
      (undoReverseRotation (singletonRotationAnchor hopt r).val σ) r.val.cycle
  rw [hμ, hρ]
  exact ⟨hc.2.1, hcap, fun m hm hmem ↦ (hg _ hmem).1
    (Finset.mem_map.mpr ⟨m, hm, rfl⟩), hc.2.2⟩
private noncomputable def markedFilteredChoicesEmbedding
    (hopt : IsManOptimal (profileOfScores x) μ₀) (r : Rotation (profileOfScores x) μ₀)
    (hμ : (singletonRotationAnchor hopt r).val = μ) (hρ : r.val.cycle = ρ)
    (ht : 0 ≤ t) :
    (↥(markedFilteredChoices μ ρ flag K L t x)) ↪ FilteredPivotDecoration hopt K r L t := by
  classical
  let f (σ : ↥(markedFilteredChoices μ ρ flag K L t x)) :
      CompatibleReversePermutation hopt K r :=
    ⟨σ.val, isCompatibleReversePermutation_of_mem_markedFilteredChoices hopt r hμ hρ
      σ.property⟩
  let e := compatibleReversePermutationEmbedding hopt K r
  refine ⟨fun σ ↦ ⟨e (f σ), ?_⟩, ?_⟩
  · have hf := (Finset.mem_filter.mp (mem_markedFilteredChoices.mp σ.property).2).2
    exact compatibleReversePermutationToDecoration_passesReverseFilters (f σ) ht hf.1
      (by rw [hμ]; exact hf.2)
  · intro σ τ he
    exact Subtype.ext (congrArg (fun a : CompatibleReversePermutation hopt K r ↦ a.val)
      (e.injective (congrArg Subtype.val he)))
end MatchingEndpoints
theorem exists_singletonRotationAnchor_of_soleForwardExposed {p : Profile n}
    {μ₀ μ ρ : Matching n} (hopt : IsManOptimal p μ₀) (hμ : IsStable p μ)
    (hsole : IsSoleForwardExposedRotation p μ ρ) :
    ∃ r : Rotation p μ₀, (singletonRotationAnchor hopt r).val = μ ∧ r.val.cycle = ρ := by
  let r := rotationOfExposed hopt hμ hsole.1
  refine ⟨r, ?_, rfl⟩
  have hanchor := (eq_singletonRotationAnchor_iff hopt r ⟨μ, hμ⟩).mpr fun s ↦ by
    constructor
    · intro hs
      exact Subtype.ext (hs.2.symm.trans (congrArg (rotationLabel μ) (hsole.2 _ hs.1)))
    · rintro rfl
      exact ⟨hsole.1, rfl⟩
  exact (congrArg Subtype.val hanchor).symm
theorem isStable_undoReverseRotation_of_mem_markedFilteredChoices {x : ScoreProfile n}
    {μ ρ σ : Matching n} {flag : OffDiagonalCellIndex n → Bool} {K L : ℕ} {t : ℝ}
    (hμ : IsStable (profileOfScores x) μ)
    (hσ : σ ∈ markedFilteredChoices μ ρ flag K L t x) :
    IsStable (profileOfScores x) (undoReverseRotation μ σ) := by
  classical
  have h := mem_compatibleReversePermutations.mp
    (Finset.mem_filter.mp (mem_markedFilteredChoices.mp hσ).2).1
  exact h.2.1.undo_stable hμ
theorem markedFilteredChoices_endpoint_injective {x : ScoreProfile n}
    {μ₀ μ μ' ρ ρ' σ σ' : Matching n}
    {flag flag' : OffDiagonalCellIndex n → Bool} {K L L' : ℕ} {t t' : ℝ}
    (hopt : IsManOptimal (profileOfScores x) μ₀)
    (hμ : IsStable (profileOfScores x) μ) (hμ' : IsStable (profileOfScores x) μ')
    (hs : IsSoleForwardExposedRotation (profileOfScores x) μ ρ)
    (hs' : IsSoleForwardExposedRotation (profileOfScores x) μ' ρ')
    (hl : K < ρ.support.card) (hl' : K < ρ'.support.card)
    (hσ : σ ∈ markedFilteredChoices μ ρ flag K L t x)
    (hσ' : σ' ∈ markedFilteredChoices μ' ρ' flag' K L' t' x)
    (he : undoReverseRotation μ σ = undoReverseRotation μ' σ') :
    μ = μ' ∧ ρ = ρ' ∧ σ = σ' := by
  obtain ⟨r, hrμ, hrρ⟩ := exists_singletonRotationAnchor_of_soleForwardExposed hopt hμ hs
  obtain ⟨r', hrμ', hrρ'⟩ :=
    exists_singletonRotationAnchor_of_soleForwardExposed hopt hμ' hs'
  let a : CompatibleReversePermutation hopt K r :=
    ⟨σ, isCompatibleReversePermutation_of_mem_markedFilteredChoices hopt r hrμ hrρ hσ⟩
  let a' : CompatibleReversePermutation hopt K r' :=
    ⟨σ', isCompatibleReversePermutation_of_mem_markedFilteredChoices hopt r' hrμ' hrρ' hσ'⟩
  let q : LongPivot (profileOfScores x) μ₀ K :=
    ⟨r, by simpa only [rotationLength, hrρ] using hl⟩
  let q' : LongPivot (profileOfScores x) μ₀ K :=
    ⟨r', by simpa only [rotationLength, hrρ'] using hl'⟩
  let f := pivotDecorationEmbedding hopt K
  have hf : f ⟨q, compatibleReversePermutationToDecoration hopt K r a⟩ =
      f ⟨q', compatibleReversePermutationToDecoration hopt K r' a'⟩ := by
    apply Subtype.ext
    change (compatibleReversePermutationToDecoration hopt K r a).matching.val =
      (compatibleReversePermutationToDecoration hopt K r' a').matching.val
    rw [compatibleReversePermutationToDecoration_matching,
      compatibleReversePermutationToDecoration_matching, hrμ, hrμ']
    exact he
  have hr : r = r' :=
    congrArg (fun z : Σ s : LongPivot (profileOfScores x) μ₀ K, PivotDecoration hopt K s.val ↦
      z.1.val) (f.injective hf)
  have hm : μ = μ' :=
    hrμ.symm.trans ((congrArg (fun s ↦ (singletonRotationAnchor hopt s).val) hr).trans hrμ')
  refine ⟨hm, hrρ.symm.trans ((congrArg (fun s : Rotation (profileOfScores x) μ₀ ↦
    s.val.cycle) hr).trans hrρ'), ?_⟩
  rw [← hm] at he
  apply Equiv.ext
  intro w
  exact μ.symm.injective (by
    simpa only [undoReverseRotation_symm_apply] using
      congrArg (fun ν : Matching n ↦ ν.symm w) he)
theorem IsLocallyEligiblePivot.supportCap_lt {b A B κ : ℝ} {K : ℕ} {x : ScoreProfile n}
    {μ ρ : Matching n} (h : IsLocallyEligiblePivot b A B x μ ρ)
    (hn : 0 < n) (hκ : κ < b) (hK : (K : ℝ) ≤ κ * Real.sqrt (n : ℝ)) :
    K < ρ.support.card := by
  have hr : (K : ℝ) < (ρ.support.card : ℝ) :=
    hK.trans_lt ((mul_lt_mul_of_pos_right hκ (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn))).trans_le
      (LocalPivotGeometry.length_lower h.1))
  exact_mod_cast hr
end IncomparableLP
end

-- PivotSharedReverse
section
open StableMarriage
namespace IncomparableLP
variable {n : ℕ} {p : Profile n} {μ₀ μ ν : Matching n}
theorem menWeaklyPrefer_singletonRotationAnchor_iff
    (hopt : IsManOptimal p μ₀) (r s : Rotation p μ₀) :
    MenWeaklyPrefer p (singletonRotationAnchor hopt r).val (singletonRotationAnchor hopt s).val
      ↔ r ≤ s := by
  rw [← eliminatedRotations_subset_iff hopt (singletonRotationAnchor hopt r).property
      (singletonRotationAnchor hopt s).property,
    eliminatedRotations_singletonRotationAnchor, eliminatedRotations_singletonRotationAnchor]
  constructor
  · intro h
    by_contra hrs
    exact (h (show s ∈ (Set.Ici r)ᶜ from hrs)) (Set.mem_Ici.mpr le_rfl)
  · exact fun h _ ha hb ↦ ha (h.trans hb)
section MarkedChoices
variable {x : ScoreProfile n} {hopt : IsManOptimal (profileOfScores x) μ₀}
  {K L : ℕ} {t₁ t₂ : ℝ} {ρ η : Matching n}
  {flag₁ flag₂ : OffDiagonalCellIndex n → Bool}
theorem markedFilteredChoicesEmbedding_matching
    (r : Rotation (profileOfScores x) μ₀) (hμ : (singletonRotationAnchor hopt r).val = μ)
    (hρ : r.val.cycle = ρ) (ht₁ : 0 ≤ t₁)
    (σ : ↥(markedFilteredChoices μ ρ flag₁ K L t₁ x)) :
    (markedFilteredChoicesEmbedding hopt r hμ hρ ht₁ σ).val.matching.val =
      undoReverseRotation μ σ.val := by
  let a : CompatibleReversePermutation hopt K r :=
    ⟨σ.val,
      isCompatibleReversePermutation_of_mem_markedFilteredChoices hopt r hμ hρ σ.property⟩
  change (compatibleReversePermutationToDecoration hopt K r a).matching.val = _
  rw [compatibleReversePermutationToDecoration_matching, hμ]
end MarkedChoices
section GlobalMarkedPairs
variable {x : ScoreProfile n} {K L : ℕ}
  {flag : Matching n → Matching n → OffDiagonalCellIndex n → Bool}
  {t : Matching n → Matching n → ℝ}
private structure LongMarkedChoice (x : ScoreProfile n) (K L : ℕ)
    (flag : Matching n → Matching n → OffDiagonalCellIndex n → Bool)
    (t : Matching n → Matching n → ℝ) where
  anchor : Matching n
  cycle : Matching n
  reverse : Matching n
  stable : IsStable (profileOfScores x) anchor
  sole : IsSoleForwardExposedRotation (profileOfScores x) anchor cycle
  long : K < cycle.support.card
  cutoff_nonneg : 0 ≤ t anchor cycle
  mem_choices : reverse ∈
    markedFilteredChoices anchor cycle (flag anchor cycle) K L (t anchor cycle) x
namespace LongMarkedChoice
variable (a : LongMarkedChoice x K L flag t) (hopt : IsManOptimal (profileOfScores x) μ₀)
private noncomputable def pivot : LongPivot (profileOfScores x) μ₀ K := by
  let h := exists_singletonRotationAnchor_of_soleForwardExposed hopt a.stable a.sole
  exact ⟨Classical.choose h,
    by simpa only [rotationLength, (Classical.choose_spec h).2] using a.long⟩
theorem pivot_anchor : (singletonRotationAnchor hopt (a.pivot hopt).val).val = a.anchor :=
  (Classical.choose_spec
    (exists_singletonRotationAnchor_of_soleForwardExposed hopt a.stable a.sole)).1
theorem pivot_cycle : (a.pivot hopt).val.val.cycle = a.cycle :=
  (Classical.choose_spec
    (exists_singletonRotationAnchor_of_soleForwardExposed hopt a.stable a.sole)).2
theorem eq_of_endpoint_eq (hopt : IsManOptimal (profileOfScores x) μ₀)
    {a' : LongMarkedChoice x K L flag t}
    (h : undoReverseRotation a.anchor a.reverse = undoReverseRotation a'.anchor a'.reverse) :
    a = a' := by
  obtain ⟨ha, hc, hr⟩ := markedFilteredChoices_endpoint_injective hopt a.stable a'.stable
    a.sole a'.sole a.long a'.long a.mem_choices a'.mem_choices h
  cases a
  cases a'
  cases ha
  cases hc
  cases hr
  rfl
end LongMarkedChoice
private structure ResidualMarkedPair (x : ScoreProfile n) (K L : ℕ)
    (flag : Matching n → Matching n → OffDiagonalCellIndex n → Bool)
    (t : Matching n → Matching n → ℝ) where
  early : LongMarkedChoice x K L flag t
  late : LongMarkedChoice x K L flag t
  prefer : MenWeaklyPrefer (profileOfScores x) early.anchor late.anchor
  ne : early.anchor ≠ late.anchor
  shared : ∃ w ∈ late.reverse.support, early.anchor.symm w = late.anchor.symm w
namespace ResidualMarkedPair
variable (a : ResidualMarkedPair x K L flag t) (hopt : IsManOptimal (profileOfScores x) μ₀)
private theorem pivot_lt : (a.early.pivot hopt).val < (a.late.pivot hopt).val := by
  apply lt_of_le_of_ne
  · apply (menWeaklyPrefer_singletonRotationAnchor_iff hopt _ _).mp
    rw [a.early.pivot_anchor hopt, a.late.pivot_anchor hopt]
    exact a.prefer
  · intro h
    have heq := congrArg (fun s ↦ (singletonRotationAnchor hopt s).val) h
    exact a.ne ((a.early.pivot_anchor hopt).symm.trans (heq.trans (a.late.pivot_anchor hopt)))
end ResidualMarkedPair
end GlobalMarkedPairs
end IncomparableLP
end

-- PivotResidualImageGeometry
section
open Filter MeasureTheory Set StableMarriage
open scoped Topology
namespace IncomparableLP
variable {n : ℕ}
private def worsePartnerMen (p : Profile n) (μ ν : Matching n) : Finset (Fin n) :=
  Finset.univ.filter fun m ↦ p.manRank m (ν m) < p.manRank m (μ m)
theorem mem_worsePartnerMen_iff_score_lt {x : ScoreProfile n}
    (hties : ∀ row, Function.Injective (x row)) (μ ν : Matching n) (m : Fin n) :
    m ∈ worsePartnerMen (profileOfScores x) μ ν ↔
      maleSpouseScore x ν m < maleSpouseScore x μ m := by
  rw [worsePartnerMen, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, profileOfScores, maleSpouseScore,
    rankPermutation_lt_iff (hties (.inl m))]
private def relativeMenPermutation (μ ν : Matching n) : Matching n := μ.trans ν.symm
theorem disjoint_worsePartnerMen (p : Profile n) (μ ν : Matching n) :
    Disjoint (worsePartnerMen p μ ν) (worsePartnerMen p ν μ) := by
  refine Finset.disjoint_left.mpr fun m hm hm' ↦ ?_
  exact (Finset.mem_filter.mp hm).2.not_gt (Finset.mem_filter.mp hm').2
theorem union_worsePartnerMen_eq_support (p : Profile n) (μ ν : Matching n) :
    worsePartnerMen p μ ν ∪ worsePartnerMen p ν μ = (relativeMenPermutation μ ν).support := by
  ext m
  simp only [worsePartnerMen, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
    Equiv.Perm.mem_support, relativeMenPermutation, Equiv.trans_apply, ← ne_iff_lt_or_gt]
  rw [(p.manRank m).injective.ne_iff]
  exact ne_comm.trans (not_congr ν.symm_apply_eq).symm
namespace IsResidualPairRankGeometry
variable {b : ℝ} {K L : ℕ} {p : Profile n} {μ ν : Matching n}
end IsResidualPairRankGeometry
namespace ResidualPivotPair
variable {p : Profile n} {μ₀ : Matching n} {K : ℕ} {hopt : IsManOptimal p μ₀}
end ResidualPivotPair
namespace ResidualMarkedPair
variable {x : ScoreProfile n} {μ₀ : Matching n} {K L : ℕ}
  {flag : Matching n → Matching n → OffDiagonalCellIndex n → Bool}
  {t : Matching n → Matching n → ℝ}
end ResidualMarkedPair
end IncomparableLP
end

-- DeferredAcceptanceTranscript
section
open StableMarriage
open scoped BigOperators
namespace IncomparableLP
private structure DAState (n : ℕ) where
  
  count : Fin n → ℕ
  
  held : Fin n → Option (Fin n)
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
end DAState
end IncomparableLP
end

-- DAStreamSimulation
section
open StableMarriage
namespace IncomparableLP
private structure DAStreamState (n : ℕ) where
  da : DAState n
  observed : Fin n → List (Fin n)
namespace DAStreamState
variable {n T : ℕ}
private def initial (n : ℕ) : DAStreamState n := ⟨DAState.initial n, fun _ ↦ []⟩
end DAStreamState
end IncomparableLP
end

-- PivotAggregateMean
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace IncomparableLP
variable {n : ℕ}
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
end IncomparableLP
end

-- PivotDecorationRevealInvariance
section
open MeasureTheory Set StableMarriage
namespace IncomparableLP
variable {n : ℕ} {μ ρ σ : Matching n} {x y : ScoreProfile n}
  {flag : OffDiagonalCellIndex n → Bool}
private structure SameReverseReveal (μ : Matching n) (flag : OffDiagonalCellIndex n → Bool)
    (x y : ScoreProfile n) : Prop where
  diagonal : (splitScorePairs μ x).1 = (splitScorePairs μ y).1
  observed : forwardRevealWithColumns flag (splitScorePairs μ x).2 =
    forwardRevealWithColumns flag (splitScorePairs μ y).2
theorem SameReverseReveal.symm (h : SameReverseReveal μ flag x y) :
    SameReverseReveal μ flag y x := ⟨h.diagonal.symm, h.observed.symm⟩
end IncomparableLP
end

-- PivotLaterRevealReplay
section
open MeasureTheory Set StableMarriage
namespace IncomparableLP
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
end IncomparableLP
end

-- PivotComparableCentered
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace IncomparableLP
private structure PivotCountParameters where
  lowerLength : ℝ
  upperLength : ℝ
  geometryBudget : ℝ
  supportCap : ℕ
  shortCutoff : ℕ
private abbrev PivotMark (n : ℕ) := Matching n × Matching n
theorem integrable_of_ae_abs_le_real {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} [IsFiniteMeasure ν] {f : Ω → ℝ}
    (hf : Measurable f) {C : ℝ} (hC : ∀ᵐ x ∂ν, |f x| ≤ C) : Integrable f ν :=
  (integrable_const C).mono' hf.aestronglyMeasurable <|
    hC.mono fun x hx ↦ by simpa only [Real.norm_eq_abs] using hx
theorem integrable_mul_of_ae_abs_le_real {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} [IsFiniteMeasure ν] {f g : Ω → ℝ} (hf : Measurable f) (hg : Measurable g)
    {C D : ℝ} (hC : 0 ≤ C) (hf' : ∀ᵐ x ∂ν, |f x| ≤ C) (hg' : ∀ᵐ x ∂ν, |g x| ≤ D) :
    Integrable (f * g) ν := by
  apply integrable_of_ae_abs_le_real (hf.mul hg) (C := C * D)
  filter_upwards [hf', hg'] with x hx hy
  rw [Pi.mul_apply, abs_mul]
  exact mul_le_mul hx hy (abs_nonneg _) hC
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
theorem measurable_localCount (q : PivotCountParameters) (i : PivotMark n) :
    Measurable (q.localCount i) :=
  measurable_localFilteredDecorationCount _ _ _ _ _ _ _
theorem measurable_onStableMark (i : PivotMark n) {f : ScoreProfile n → ℝ} (hf : Measurable f) :
    Measurable (onStableMark i f) := hf.indicator (measurableSet_isScoreStable i.1)
theorem measurable_count (q : PivotCountParameters) (i : PivotMark n) : Measurable (q.count i) :=
  measurable_onStableMark i (q.measurable_localCount i)
theorem localCount_mem_Icc (q : PivotCountParameters) (i : PivotMark n) (x : ScoreProfile n) :
    q.localCount i x ∈ Icc (0 : ℝ) (n.factorial : ℝ) :=
  ⟨localFilteredDecorationCount_nonneg _ _ _ _ _ _ _ _,
    localFilteredDecorationCount_le_factorial _ _ _ _ _ _ _ _⟩
theorem count_mem_Icc (q : PivotCountParameters) (i : PivotMark n) (x : ScoreProfile n) :
    q.count i x ∈ Icc (0 : ℝ) (n.factorial : ℝ) := by
  by_cases h : x ∈ {y | IsScoreStable y i.1}
  · simpa only [count, onStableMark, indicator_of_mem h] using q.localCount_mem_Icc i x
  · simp [count, onStableMark, h]
end PivotCountParameters
end IncomparableLP
end

-- PivotCenteredReduction
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators
namespace IncomparableLP
variable {n : ℕ}
private def IncomparableAnchors (p : Profile n) (μ ν : Matching n) : Prop :=
  ¬ MenWeaklyPrefer p μ ν ∧ ¬ MenWeaklyPrefer p ν μ
theorem measurableSet_incomparableAnchors (μ ν : Matching n) :
    MeasurableSet {x : ScoreProfile n | IncomparableAnchors (profileOfScores x) μ ν} :=
  measurable_profileOfScores n (MeasurableSet.of_discrete :
    MeasurableSet {p : Profile n | IncomparableAnchors p μ ν})
namespace PivotCountParameters
end PivotCountParameters
end IncomparableLP
end

-- PivotResidualCountBridge
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators
namespace IncomparableLP
namespace PivotCountParameters
variable {n : ℕ}
private noncomputable def residualChoiceFlag (x : ScoreProfile n) (μ _ : Matching n) :
    OffDiagonalCellIndex n → Bool :=
  forwardMaskOfScores (splitScorePairs μ x).1 (splitScorePairs μ x).2
private noncomputable def residualChoiceCutoff (x : ScoreProfile n) (μ _ : Matching n) : ℝ :=
  reverseIncrementCutoff n (maleSpouseTotal x μ)
private noncomputable def choices (q : PivotCountParameters) (x : ScoreProfile n)
    (i : PivotMark n) : Finset (Matching n) :=
  markedFilteredChoices i.1 i.2 (residualChoiceFlag x i.1 i.2)
    q.supportCap q.shortCutoff (residualChoiceCutoff x i.1 i.2) x
private noncomputable def eligibleChoices (q : PivotCountParameters) (x : ScoreProfile n)
    (i : PivotMark n) : Finset (Matching n) := by
  classical
  exact if IsScoreStable x i.1 ∧
    IsLocallyEligiblePivot q.lowerLength q.upperLength q.geometryBudget x i.1 i.2
    then q.choices x i else ∅
theorem count_eq_card_eligibleChoices (q : PivotCountParameters) (x : ScoreProfile n)
    (i : PivotMark n) : q.count i x = (q.eligibleChoices x i).card := by
  classical
  by_cases hs : IsScoreStable x i.1 <;>
    by_cases he : IsLocallyEligiblePivot q.lowerLength q.upperLength q.geometryBudget x i.1 i.2 <;>
    simp [count, onStableMark, localCount, localFilteredDecorationCount,
      eligibleChoices, choices, residualChoiceFlag, residualChoiceCutoff, hs, he]
private theorem data_of_eligibleChoices {q : PivotCountParameters} {x : ScoreProfile n}
    {i : PivotMark n} {a : Matching n} (h : a ∈ q.eligibleChoices x i) :
    IsScoreStable x i.1 ∧
      IsLocallyEligiblePivot q.lowerLength q.upperLength q.geometryBudget x i.1 i.2 ∧
      a ∈ q.choices x i := by
  classical
  unfold eligibleChoices at h
  split at h
  · rename_i hi
    exact ⟨hi.1, hi.2, h⟩
  · exact (Finset.notMem_empty _ h).elim
theorem eligibleChoices_data {q : PivotCountParameters} {x : ScoreProfile n}
    {i : PivotMark n} {a : Matching n} (h : a ∈ q.eligibleChoices x i) :
    IsScoreStable x i.1 ∧
      IsLocallyEligiblePivot q.lowerLength q.upperLength q.geometryBudget x i.1 i.2 ∧
      a ∈ markedFilteredChoices i.1 i.2 (residualChoiceFlag x i.1 i.2)
        q.supportCap q.shortCutoff (residualChoiceCutoff x i.1 i.2) x :=
  data_of_eligibleChoices h
end PivotCountParameters
end IncomparableLP
end

-- PivotIncomparableScoreCount
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators
namespace IncomparableLP
variable {n : ℕ}
private def scoreIncomparablePairEvent (Q : ScoreProfile n → Matching n → Matching n → Prop)
    (μ ν : Matching n) : Set (ScoreProfile n) :=
  {x | IsScoreStable x μ ∧ IsScoreStable x ν ∧
    IncomparableAnchors (profileOfScores x) μ ν ∧ Q x μ ν}
theorem measurableSet_scoreIncomparablePairEvent
    {Q : ScoreProfile n → Matching n → Matching n → Prop}
    (hQ : ∀ μ ν, MeasurableSet {x | Q x μ ν}) (μ ν : Matching n) :
    MeasurableSet (scoreIncomparablePairEvent Q μ ν) :=
  (measurableSet_isScoreStable μ).inter ((measurableSet_isScoreStable ν).inter
    ((measurableSet_incomparableAnchors μ ν).inter (hQ μ ν)))
private noncomputable def incomparableScorePairs
    (Q : ScoreProfile n → Matching n → Matching n → Prop)
    (x : ScoreProfile n) : Finset (Matching n × Matching n) := by
  classical
  exact Finset.univ.filter (fun mn ↦ x ∈ scoreIncomparablePairEvent Q mn.1 mn.2)
theorem mem_incomparableScorePairs {Q : ScoreProfile n → Matching n → Matching n → Prop}
    {x : ScoreProfile n} {mn : Matching n × Matching n} :
    mn ∈ incomparableScorePairs Q x ↔ x ∈ scoreIncomparablePairEvent Q mn.1 mn.2 := by
  classical
  simp [incomparableScorePairs]
private noncomputable def incomparableScorePairCount
    (Q : ScoreProfile n → Matching n → Matching n → Prop) (x : ScoreProfile n) : ℝ :=
  (incomparableScorePairs Q x).card
theorem incomparableScorePairCount_eq_sum
    (Q : ScoreProfile n → Matching n → Matching n → Prop) (x : ScoreProfile n) :
    incomparableScorePairCount Q x =
      ∑ mn : Matching n × Matching n,
        (scoreIncomparablePairEvent Q mn.1 mn.2).indicator (fun _ ↦ (1 : ℝ)) x := by
  classical
  simp only [incomparableScorePairCount, incomparableScorePairs, indicator_apply]
  rw [← Finset.sum_filter]
  simp
theorem integrable_incomparableScorePairCount
    {Q : ScoreProfile n → Matching n → Matching n → Prop}
    (hQ : ∀ μ ν, MeasurableSet {x | Q x μ ν}) :
    Integrable (incomparableScorePairCount Q) (continuousScoreLaw n) := by
  have h (mn : Matching n × Matching n) :
      Integrable ((scoreIncomparablePairEvent Q mn.1 mn.2).indicator (fun _ ↦ (1 : ℝ)))
        (continuousScoreLaw n) :=
    (integrable_const _).indicator (measurableSet_scoreIncomparablePairEvent hQ mn.1 mn.2)
  exact (integrable_finsetSum _ fun mn _ ↦ h mn).congr
    (Eventually.of_forall fun x ↦ (incomparableScorePairCount_eq_sum Q x).symm)
theorem integral_incomparableScorePairCount
    {Q : ScoreProfile n → Matching n → Matching n → Prop}
    (hQ : ∀ μ ν, MeasurableSet {x | Q x μ ν}) :
    (∫ x, incomparableScorePairCount Q x ∂continuousScoreLaw n) =
      ∑ μ : Matching n, ∑ ν : Matching n,
        (continuousScoreLaw n).real (scoreIncomparablePairEvent Q μ ν) := by
  simp_rw [incomparableScorePairCount_eq_sum]
  rw [integral_finsetSum _ (fun mn _ ↦ (integrable_const _).indicator
    (measurableSet_scoreIncomparablePairEvent hQ mn.1 mn.2)), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun μ _ ↦ Finset.sum_congr rfl fun ν _ ↦ ?_
  rw [integral_indicator_const _ (measurableSet_scoreIncomparablePairEvent hQ μ ν), smul_eq_mul,
    mul_one]
namespace PivotCountParameters
theorem residualChoiceCutoff_nonneg {x : ScoreProfile n}
    (hx : ∀ r i, 0 ≤ x r i) (i : PivotMark n) :
    0 ≤ residualChoiceCutoff x i.1 i.2 := by
  unfold residualChoiceCutoff reverseIncrementCutoff
  exact div_nonneg (mul_nonneg (by norm_num) (Real.log_natCast_nonneg _))
    (Finset.sum_nonneg fun m _ ↦ hx (.inl m) (i.1 m))
end PivotCountParameters
end IncomparableLP
end

-- PivotIncomparableDecorations
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators
namespace IncomparableLP
variable {n : ℕ} {p : Profile n} {μ₀ A B : Matching n} {hopt : IsManOptimal p μ₀}
  {K : ℕ} {r s : Rotation p μ₀}
theorem PivotDecoration.mem_matching_eliminated_of_long
    (D : PivotDecoration hopt K r) (hs : K < rotationLength s) (hrs : ¬ r ≤ s) :
    s ∈ eliminatedRotations p μ₀ D.matching.val := by
  rw [D.matching_eliminated, eliminatedRotations_singletonRotationAnchor]
  refine ⟨hrs, ?_⟩
  rintro ⟨t, ht, rfl⟩
  have hlen := (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
    (show t ∈ D.removed from ht)).trans D.totalLength_le
  exact (not_lt_of_ge hlen) hs
theorem Rotation.IsExposedAt.support_subset_worsePartnerMen_of_eliminated
    (hopt : IsManOptimal p μ₀) (hex : r.IsExposedAt A) (hB : IsStable p B)
    (hmem : r ∈ eliminatedRotations p μ₀ B) :
    r.val.cycle.support ⊆ worsePartnerMen p B A := by
  intro m hm
  have hmove := Equiv.Perm.mem_support.mp hm
  have hnew := rotationLabelNewPartner_eq (μ := A) hmove
  rw [hex.2] at hnew
  have hle := (mem_eliminatedRotations_iff_newRank_le hopt hB hmove hnew).mp hmem
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, (hex.1.manRank_lt_eliminate_of_moved hmove).trans_le hle⟩
theorem PivotDecoration.supports_subset_worsePartnerMen_of_incomparable
    (D : PivotDecoration hopt K r) (E : PivotDecoration hopt K s)
    (hr : K < rotationLength r) (hs : K < rotationLength s)
    (hrs : ¬ r ≤ s) (hsr : ¬ s ≤ r) :
    r.val.cycle.support ⊆ worsePartnerMen p E.matching.val D.matching.val ∧
      s.val.cycle.support ⊆ worsePartnerMen p D.matching.val E.matching.val :=
  ⟨D.pivot_exposed.support_subset_worsePartnerMen_of_eliminated hopt E.matching.property
      (E.mem_matching_eliminated_of_long hr hsr),
    E.pivot_exposed.support_subset_worsePartnerMen_of_eliminated hopt D.matching.property
      (D.mem_matching_eliminated_of_long hs hrs)⟩
theorem PivotDecoration.incomparable_of_incomparable_pivots
    (D : PivotDecoration hopt K r) (E : PivotDecoration hopt K s)
    (hr : K < rotationLength r) (hs : K < rotationLength s)
    (hrs : ¬ r ≤ s) (hsr : ¬ s ≤ r) :
    (¬ MenWeaklyPrefer p D.matching.val E.matching.val) ∧
      (¬ MenWeaklyPrefer p E.matching.val D.matching.val) := by
  obtain ⟨hrsub, hssub⟩ := D.supports_subset_worsePartnerMen_of_incomparable E hr hs hrs hsr
  obtain ⟨m, hm⟩ := Finset.card_pos.mp ((Nat.zero_le K).trans_lt hr)
  obtain ⟨m', hm'⟩ := Finset.card_pos.mp ((Nat.zero_le K).trans_lt hs)
  exact ⟨fun h ↦ (Finset.mem_filter.mp (hssub hm')).2.not_ge (h m'),
    fun h ↦ (Finset.mem_filter.mp (hrsub hm)).2.not_ge (h m)⟩
theorem PivotDecoration.rotationLength_le_card_worsePartnerMen_of_incomparable
    (D : PivotDecoration hopt K r) (E : PivotDecoration hopt K s)
    (hr : K < rotationLength r) (hs : K < rotationLength s)
    (hrs : ¬ r ≤ s) (hsr : ¬ s ≤ r) :
    rotationLength r ≤ (worsePartnerMen p E.matching.val D.matching.val).card ∧
      rotationLength s ≤ (worsePartnerMen p D.matching.val E.matching.val).card := by
  obtain ⟨hrsub, hssub⟩ := D.supports_subset_worsePartnerMen_of_incomparable E hr hs hrs hsr
  exact ⟨Finset.card_le_card hrsub, Finset.card_le_card hssub⟩
private def ScoreTwoLongOrientations (b : ℝ) (x : ScoreProfile n) (μ ν : Matching n) : Prop :=
  b * Real.sqrt (n : ℝ) ≤ ((worsePartnerMen (profileOfScores x) μ ν).card : ℝ) ∧
    b * Real.sqrt (n : ℝ) ≤ ((worsePartnerMen (profileOfScores x) ν μ).card : ℝ)
theorem measurableSet_scoreTwoLongOrientations (b : ℝ) (μ ν : Matching n) :
    MeasurableSet {x | ScoreTwoLongOrientations b x μ ν} :=
  measurable_profileOfScores n (MeasurableSet.of_discrete :
    MeasurableSet {p : Profile n |
      b * Real.sqrt (n : ℝ) ≤ ((worsePartnerMen p μ ν).card : ℝ) ∧
        b * Real.sqrt (n : ℝ) ≤ ((worsePartnerMen p ν μ).card : ℝ)})
namespace LongMarkedChoice
variable {x : ScoreProfile n} {L : ℕ}
  {flag : Matching n → Matching n → OffDiagonalCellIndex n → Bool}
  {t : Matching n → Matching n → ℝ}
  (a d : LongMarkedChoice x K L flag t) (hopt : IsManOptimal (profileOfScores x) μ₀)
private noncomputable def asDecoration : PivotDecoration hopt K (a.pivot hopt).val :=
  (markedFilteredChoicesEmbedding hopt (a.pivot hopt).val (a.pivot_anchor hopt)
    (a.pivot_cycle hopt) a.cutoff_nonneg ⟨a.reverse, a.mem_choices⟩).val
private theorem asDecoration_matching :
    (a.asDecoration hopt).matching.val = undoReverseRotation a.anchor a.reverse :=
  markedFilteredChoicesEmbedding_matching (a.pivot hopt).val (a.pivot_anchor hopt)
    (a.pivot_cycle hopt) a.cutoff_nonneg ⟨a.reverse, a.mem_choices⟩
theorem incomparableEndpoints_of_incomparableAnchors {b : ℝ}
    (hoptimal : IsManOptimal (profileOfScores x) μ₀)
    (hinc : IncomparableAnchors (profileOfScores x) a.anchor d.anchor)
    (ha : b * Real.sqrt (n : ℝ) ≤ (a.cycle.support.card : ℝ))
    (hd : b * Real.sqrt (n : ℝ) ≤ (d.cycle.support.card : ℝ)) :
    IncomparableAnchors (profileOfScores x) (undoReverseRotation a.anchor a.reverse)
      (undoReverseRotation d.anchor d.reverse) ∧
    ScoreTwoLongOrientations b x (undoReverseRotation a.anchor a.reverse)
      (undoReverseRotation d.anchor d.reverse) := by
  let r := (a.pivot hoptimal).val
  let s := (d.pivot hoptimal).val
  have hle : MenWeaklyPrefer (profileOfScores x) a.anchor d.anchor ↔ r ≤ s := by
    rw [← a.pivot_anchor hoptimal, ← d.pivot_anchor hoptimal]
    exact menWeaklyPrefer_singletonRotationAnchor_iff hoptimal r s
  have hge : MenWeaklyPrefer (profileOfScores x) d.anchor a.anchor ↔ s ≤ r := by
    rw [← d.pivot_anchor hoptimal, ← a.pivot_anchor hoptimal]
    exact menWeaklyPrefer_singletonRotationAnchor_iff hoptimal s r
  have hrs : ¬ r ≤ s := fun h ↦ hinc.1 (hle.mpr h)
  have hsr : ¬ s ≤ r := fun h ↦ hinc.2 (hge.mpr h)
  rw [← a.asDecoration_matching hoptimal, ← d.asDecoration_matching hoptimal]
  have hl := (a.asDecoration hoptimal).rotationLength_le_card_worsePartnerMen_of_incomparable
    (d.asDecoration hoptimal) (a.pivot hoptimal).property (d.pivot hoptimal).property hrs hsr
  have hra : b * Real.sqrt (n : ℝ) ≤ (rotationLength r : ℝ) := by
    simpa only [r, rotationLength, a.pivot_cycle hoptimal] using ha
  have hsd : b * Real.sqrt (n : ℝ) ≤ (rotationLength s : ℝ) := by
    simpa only [s, rotationLength, d.pivot_cycle hoptimal] using hd
  exact ⟨(a.asDecoration hoptimal).incomparable_of_incomparable_pivots
      (d.asDecoration hoptimal) (a.pivot hoptimal).property (d.pivot hoptimal).property hrs hsr,
    hsd.trans (Nat.cast_le.mpr hl.2), hra.trans (Nat.cast_le.mpr hl.1)⟩
end LongMarkedChoice
namespace PivotCountParameters
private noncomputable def incomparableChoicePairs (q : PivotCountParameters) (x : ScoreProfile n) :
    Finset (Σ _ : PivotMark n × PivotMark n, Matching n × Matching n) := by
  classical
  exact Finset.univ.sigma fun ij ↦
    if IncomparableAnchors (profileOfScores x) ij.1.1 ij.2.1 then
      (q.eligibleChoices x ij.1).product (q.eligibleChoices x ij.2)
    else ∅
private theorem card_incomparableChoicePairs (q : PivotCountParameters) (x : ScoreProfile n) :
    ((q.incomparableChoicePairs x).card : ℝ) =
      ∑ i : PivotMark n, ∑ j : PivotMark n,
        {x | IncomparableAnchors (profileOfScores x) i.1 j.1}.indicator
          (q.count i * q.count j) x := by
  classical
  rw [incomparableChoicePairs, Finset.card_sigma, Nat.cast_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  by_cases h : IncomparableAnchors (profileOfScores x) i.1 j.1 <;>
    simp [h, Pi.mul_apply, q.count_eq_card_eligibleChoices,
      Finset.product_eq_sprod, Finset.card_product, Nat.cast_mul]
private theorem incomparableChoicePairs_data (q : PivotCountParameters) (x : ScoreProfile n)
    (a : ↥(q.incomparableChoicePairs x)) :
    IncomparableAnchors (profileOfScores x) a.val.1.1.1 a.val.1.2.1 ∧
      a.val.2.1 ∈ q.eligibleChoices x a.val.1.1 ∧
      a.val.2.2 ∈ q.eligibleChoices x a.val.1.2 := by
  classical
  have hm := (Finset.mem_sigma.mp a.property).2
  split at hm
  · rename_i h
    exact ⟨h, Finset.mem_product.mp hm⟩
  · exact (Finset.notMem_empty _ hm).elim
private noncomputable def longChoiceOfEligible (q : PivotCountParameters) {x : ScoreProfile n}
    (hties : ∀ row, Function.Injective (x row))
    (hlong : ∀ i : PivotMark n,
      IsLocallyEligiblePivot q.lowerLength q.upperLength q.geometryBudget x i.1 i.2 →
        q.supportCap < i.2.support.card)
    (hcut : ∀ i : PivotMark n, 0 ≤ residualChoiceCutoff x i.1 i.2)
    (i : PivotMark n) (τ : Matching n) (hτ : τ ∈ q.eligibleChoices x i) :
    LongMarkedChoice x q.supportCap q.shortCutoff (residualChoiceFlag x) (residualChoiceCutoff x) :=
  let h := eligibleChoices_data hτ
  ⟨i.1, i.2, τ, (isStable_profileOfScores_iff hties _).mpr h.1, h.2.1.isSoleForwardExposed hties,
    hlong i h.2.1, hcut i, h.2.2⟩
theorem incomparableCountProducts_le_scorePairCount (q : PivotCountParameters)
    {x : ScoreProfile n} (hties : ∀ row, Function.Injective (x row))
    (hlong : ∀ i : PivotMark n,
      IsLocallyEligiblePivot q.lowerLength q.upperLength q.geometryBudget x i.1 i.2 →
        q.supportCap < i.2.support.card)
    (hcut : ∀ i : PivotMark n, 0 ≤ residualChoiceCutoff x i.1 i.2) :
    (∑ i : PivotMark n, ∑ j : PivotMark n,
      {x | IncomparableAnchors (profileOfScores x) i.1 j.1}.indicator
        (q.count i * q.count j) x) ≤ incomparableScorePairCount
          (ScoreTwoLongOrientations q.lowerLength) x := by
  classical
  rw [← q.card_incomparableChoicePairs x]
  let S := q.incomparableChoicePairs x
  let C := incomparableScorePairs (ScoreTwoLongOrientations q.lowerLength) x
  change (S.card : ℝ) ≤ (C.card : ℝ)
  apply Nat.cast_le.mpr
  by_cases hS : Nonempty ↥S
  · let data (a : ↥S) := q.incomparableChoicePairs_data x a
    let first (a : ↥S) := q.longChoiceOfEligible hties hlong hcut _ _ (data a).2.1
    let second (a : ↥S) := q.longChoiceOfEligible hties hlong hcut _ _ (data a).2.2
    let a₀ := first (Classical.choice hS)
    obtain ⟨m₀, hm₀⟩ := exists_manOptimal_of_exists_stable ⟨a₀.anchor, a₀.stable⟩
    let e (a : ↥S) : ↥C := by
      let A := first a
      let B := second a
      refine ⟨(undoReverseRotation A.anchor A.reverse, undoReverseRotation B.anchor B.reverse),
        mem_incomparableScorePairs.mpr ?_⟩
      exact ⟨(isStable_profileOfScores_iff hties _).mp
          (isStable_undoReverseRotation_of_mem_markedFilteredChoices A.stable A.mem_choices),
        (isStable_profileOfScores_iff hties _).mp
          (isStable_undoReverseRotation_of_mem_markedFilteredChoices B.stable B.mem_choices),
        A.incomparableEndpoints_of_incomparableAnchors B hm₀ (data a).1
          (LocalPivotGeometry.length_lower (eligibleChoices_data (data a).2.1).2.1.1)
          (LocalPivotGeometry.length_lower (eligibleChoices_data (data a).2.2).2.1.1)⟩
    have he : Function.Injective e := by
      intro a a' haa'
      have hpair := congrArg Subtype.val haa'
      have hf : first a = first a' :=
        (first a).eq_of_endpoint_eq hm₀ (congrArg Prod.fst hpair)
      have hs : second a = second a' :=
        (second a).eq_of_endpoint_eq hm₀ (congrArg Prod.snd hpair)
      exact Subtype.ext (Sigma.ext
        (Prod.ext (congrArg (fun c ↦ (c.anchor, c.cycle)) hf)
          (congrArg (fun c ↦ (c.anchor, c.cycle)) hs))
        (heq_of_eq (Prod.ext (congrArg (fun c ↦ c.reverse) hf)
          (congrArg (fun c ↦ c.reverse) hs))))
    simpa only [Nat.card_eq_finsetCard] using Nat.card_le_card_of_injective e he
  · have hz : S.card = 0 := Finset.card_eq_zero.mpr
      (Finset.eq_empty_iff_forall_notMem.mpr fun a ha ↦ hS ⟨⟨a, ha⟩⟩)
    rw [hz]
    exact Nat.zero_le _
theorem ae_incomparableCountProducts_le_scorePairCount (q : PivotCountParameters)
    (hn : 0 < n) {κ : ℝ} (hκ : κ < q.lowerLength)
    (hcap : (q.supportCap : ℝ) ≤ κ * Real.sqrt (n : ℝ)) :
    ∀ᵐ x ∂continuousScoreLaw n,
      (∑ i : PivotMark n, ∑ j : PivotMark n,
        {x | IncomparableAnchors (profileOfScores x) i.1 j.1}.indicator
          (q.count i * q.count j) x) ≤ incomparableScorePairCount
            (ScoreTwoLongOrientations q.lowerLength) x := by
  filter_upwards [ae_injective_rows n, ae_unitOpen_scores n] with x ht hx
  exact q.incomparableCountProducts_le_scorePairCount ht
    (fun _ he ↦ he.supportCap_lt hn hκ hcap)
    (residualChoiceCutoff_nonneg fun r i ↦ (hx r i).1.le)
theorem integral_incomparableCountProducts_le_sum (q : PivotCountParameters)
    (hn : 0 < n) {κ : ℝ} (hκ : κ < q.lowerLength)
    (hcap : (q.supportCap : ℝ) ≤ κ * Real.sqrt (n : ℝ)) :
    (∫ x, (∑ i : PivotMark n, ∑ j : PivotMark n,
      {x | IncomparableAnchors (profileOfScores x) i.1 j.1}.indicator
        (q.count i * q.count j) x) ∂continuousScoreLaw n) ≤
      ∑ μ : Matching n, ∑ ν : Matching n,
        (continuousScoreLaw n).real
          (scoreIncomparablePairEvent (ScoreTwoLongOrientations q.lowerLength) μ ν) := by
  let Q := ScoreTwoLongOrientations (n := n) q.lowerLength
  have hQ (μ ν : Matching n) : MeasurableSet {x | Q x μ ν} :=
    measurableSet_scoreTwoLongOrientations _ _ _
  rw [← integral_incomparableScorePairCount hQ]
  have habs (i : PivotMark n) :
      ∀ᵐ x ∂continuousScoreLaw n, |q.count i x| ≤ (n.factorial : ℝ) :=
    Eventually.of_forall fun x ↦ by
      rw [abs_of_nonneg (q.count_mem_Icc i x).1]
      exact (q.count_mem_Icc i x).2
  refine integral_mono_ae ?_ (integrable_incomparableScorePairCount hQ)
    (q.ae_incomparableCountProducts_le_scorePairCount hn hκ hcap)
  refine integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ ?_
  exact (integrable_mul_of_ae_abs_le_real (q.measurable_count i) (q.measurable_count j)
    (Nat.cast_nonneg _) (habs i) (habs j)).indicator (measurableSet_incomparableAnchors i.1 j.1)
end PivotCountParameters
end IncomparableLP
end

-- TwoStablePairSizeSums
section
open Finset
namespace IncomparableLP
private def ValidPairSizes (n : ℕ) (p : ℕ × ℕ) : Prop :=
  2 ≤ p.1 ∧ 2 ≤ p.2 ∧ p.1 + p.2 ≤ n
private noncomputable def twoStablePairSizeKernel (n : ℕ) (p : ℕ × ℕ) : ℝ :=
  (n : ℝ) ^ 3 / ((↑(n - p.1) : ℝ) * ↑(n - p.2)) *
    ((↑((n - p.1).descFactorial p.2) : ℝ) / ↑(n.descFactorial p.2))
theorem twoStablePairSizeKernel_nonneg (n : ℕ) (p : ℕ × ℕ) :
    0 ≤ twoStablePairSizeKernel n p := by
  unfold twoStablePairSizeKernel
  positivity
private theorem cast_descFactorial_eq_div {n k : ℕ} (hk : k ≤ n) :
    (n.descFactorial k : ℝ) = (↑n.factorial : ℝ) / ↑(n - k).factorial := by
  apply (eq_div_iff (by positivity)).2
  rw [mul_comm]
  exact_mod_cast Nat.factorial_mul_descFactorial hk
private noncomputable def pairSizeBetaFactor (n k : ℕ) : ℝ :=
  (↑(k - 1).factorial : ℝ) * ↑(n - k - 1).factorial / ↑(n - 1).factorial
private theorem cast_factorial_pred {k : ℕ} (hk : 0 < k) :
    (k.factorial : ℝ) = (k : ℝ) * ↑(k - 1).factorial := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  simp [Nat.factorial_succ]
theorem twoStablePairSizeKernel_eq_beta_factors {n u v : ℕ} (h : ValidPairSizes n (u, v)) :
    twoStablePairSizeKernel n (u, v) =
      ((n.factorial : ℝ) ^ 2 / ↑(n - u - v).factorial) *
        (pairSizeBetaFactor n u * pairSizeBetaFactor n v /
          ((↑(n - 1).factorial : ℝ) * ↑(u - 1).factorial * ↑(v - 1).factorial)) := by
  obtain ⟨hu, hv, huv⟩ := h
  have hvn : v ≤ n := by omega
  have hvu : v ≤ n - u := by omega
  have hnu : 0 < n - u := by omega
  have hnv : 0 < n - v := by omega
  have hn : 0 < n := by omega
  calc
    _ = (n : ℝ) ^ 3 * ↑(n - u - 1).factorial * ↑(n - v - 1).factorial /
        (↑(n - u - v).factorial * ↑n.factorial) := by
      change (n : ℝ) ^ 3 / (↑(n - u) * ↑(n - v)) *
        (↑((n - u).descFactorial v) / ↑(n.descFactorial v)) = _
      rw [cast_descFactorial_eq_div hvu, cast_descFactorial_eq_div hvn,
        cast_factorial_pred hnu, cast_factorial_pred hnv]
      field_simp
    _ = _ := by
      unfold pairSizeBetaFactor
      rw [cast_factorial_pred hn]
      field_simp
private theorem cast_choose_eq_factorial_div {a b : ℕ} (h : b ≤ a) :
    (a.choose b : ℝ) = (a.factorial : ℝ) / (b.factorial * ((a - b).factorial : ℝ)) := by
  apply (eq_div_iff (by positivity)).2
  rw [← mul_assoc]
  exact_mod_cast Nat.choose_mul_factorial_mul_factorial h
theorem twoStablePairSizeKernel_eq_choose {n u v : ℕ} (hu : 1 ≤ u) (hv : 1 ≤ v)
    (hs : u + v ≤ n) :
    twoStablePairSizeKernel n (u, v) =
      (n : ℝ) ^ 2 / (u : ℝ) / ((n - 1).choose u : ℝ) *
        ((n - v - 1).choose (u - 1) : ℝ) := by
  change (n : ℝ) ^ 3 / ((n - u : ℕ) * ((n - v : ℕ) : ℝ)) *
    (((n - u).descFactorial v : ℝ) / (n.descFactorial v : ℝ)) = _
  rw [cast_descFactorial_eq_div (show v ≤ n - u by omega),
    cast_descFactorial_eq_div (show v ≤ n by omega),
    cast_choose_eq_factorial_div (show u ≤ n - 1 by omega),
    cast_choose_eq_factorial_div (show u - 1 ≤ n - v - 1 by omega),
    show n - 1 - u = n - u - 1 by omega,
    show n - v - 1 - (u - 1) = n - u - v by omega,
    cast_factorial_pred (show 0 < n - u by omega),
    cast_factorial_pred (show 0 < n - v by omega),
    cast_factorial_pred (show 0 < n by omega),
    cast_factorial_pred hu]
  have hnu : 0 < n - u := by omega
  have hnv : 0 < n - v := by omega
  field_simp
private theorem sum_row_choose_from {n u a : ℕ} (hu : 1 ≤ u) (ha : a ≤ n - u)
    (hun : u ≤ n) :
    (∑ v ∈ Icc a (n - u), (n - v - 1).choose (u - 1)) = (n - a).choose u := by
  calc
    _ = ∑ j ∈ Icc (u - 1) (n - a - 1), j.choose (u - 1) := by
      refine sum_nbij' (fun v ↦ n - v - 1) (fun j ↦ n - j - 1) ?_ ?_ ?_ ?_ (fun _ _ ↦ rfl)
        <;> intro i hi <;> simp only [mem_Icc] at * <;> omega
    _ = _ := by rw [Nat.sum_Icc_choose]; congr 1 <;> omega
private theorem sum_row_choose {n u : ℕ} (hu : 1 ≤ u) (hun : u < n) :
    (∑ v ∈ Icc 1 (n - u), (n - v - 1).choose (u - 1)) = (n - 1).choose u :=
  sum_row_choose_from hu (by omega) hun.le
private theorem sum_mul_row_choose {n u : ℕ} (hu : 1 ≤ u) (hun : u < n) :
    (∑ v ∈ Icc 1 (n - u), v * (n - v - 1).choose (u - 1)) = n.choose (u + 1) := by
  have h := sum_Ico_Ico_comm 1 (n - u + 1) (fun _ v ↦ (n - v - 1).choose (u - 1))
  simp only [Ico_add_one_right_eq_Icc, sum_const, Nat.card_Icc, nsmul_eq_mul,
    Nat.add_sub_cancel, Nat.cast_id] at h
  rw [← h]
  calc
    _ = ∑ i ∈ Icc 1 (n - u), (n - i).choose u := by
      exact sum_congr rfl fun i hi ↦ sum_row_choose_from hu (mem_Icc.mp hi).2 hun.le
    _ = n.choose (u + 1) := by
      have h' := sum_row_choose (n := n + 1) (u := u + 1) (by omega) (by omega)
      simpa only [Nat.add_sub_add_right, Nat.add_sub_cancel, Nat.sub_sub] using h'
theorem sum_mul_twoStablePairSizeKernel_row {n u : ℕ} (hu : 1 ≤ u) (hun : u < n) :
    (∑ v ∈ Icc 1 (n-u), (v : ℝ) * twoStablePairSizeKernel n (u,v)) =
      (n : ℝ)^3 / ((u : ℝ) * (u+1)) := by
  have hpos : 0 < ((n - 1).choose u : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : u ≤ n - 1)
  have hchoose : (n:ℝ) * ((n-1).choose u : ℝ) = (n.choose (u+1) : ℝ) * (u+1) := by
    exact_mod_cast (show n * (n-1).choose u = n.choose (u+1) * (u+1) by
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using Nat.add_one_mul_choose_eq (n-1) u)
  calc
    _ = ((n : ℝ)^2 / u / ((n-1).choose u : ℝ)) *
        ∑ v ∈ Icc 1 (n-u), ((v * (n-v-1).choose (u-1) : ℕ) : ℝ) := by
      rw [mul_sum]
      refine sum_congr rfl fun v hv ↦ ?_
      rw [twoStablePairSizeKernel_eq_choose hu (mem_Icc.mp hv).1
        (by have := (mem_Icc.mp hv).2; omega : u+v ≤ n), Nat.cast_mul]
      ring
    _ = _ := by
      rw [← Nat.cast_sum, sum_mul_row_choose hu hun]
      have hu' : (0:ℝ) < u := by exact_mod_cast hu
      field_simp
      linear_combination (n:ℝ)^2 * hchoose.symm
private theorem sum_by_row_le {n : ℕ} (s : Finset (ℕ × ℕ))
    (hs : ∀ p ∈ s, ValidPairSizes n p) (t : Finset ℕ) (ht : ∀ p ∈ s, p.1 ∈ t)
    (g : ℕ → ℝ) (hg : ∀ u ∈ t, 0 ≤ g u)
    (hrow : ∀ u ∈ t, 2 ≤ u → u + 2 ≤ n →
      (∑ p ∈ s.filter (fun p ↦ p.1 = u), twoStablePairSizeKernel n p) ≤ g u) :
    (∑ p ∈ s, twoStablePairSizeKernel n p) ≤ ∑ u ∈ t, g u := by
  rw [← sum_fiberwise_of_maps_to ht]
  refine sum_le_sum fun u hu ↦ ?_
  by_cases he : s.filter (fun p ↦ p.1 = u) = ∅
  · simpa [he] using hg u hu
  obtain ⟨p, hp⟩ := nonempty_iff_ne_empty.mpr he
  obtain ⟨hps, hpu⟩ := mem_filter.mp hp
  obtain ⟨h₁,h₂,h₃⟩ := hs p hps
  subst u
  exact hrow _ hu h₁ (by omega)
private theorem sum_fiber_le_of_row {n u : ℕ} (s : Finset (ℕ × ℕ))
    (hs : ∀ p ∈ s, ValidPairSizes n p) (f : ℕ → ℝ) (hf : ∀ v, 0 ≤ f v)
    (h : ∀ p ∈ s, p.1 = u → twoStablePairSizeKernel n p ≤ f p.2) :
    (∑ p ∈ s.filter (fun p ↦ p.1 = u), twoStablePairSizeKernel n p) ≤
      ∑ v ∈ Icc 1 (n-u), f v := by
  let row := s.filter (fun p ↦ p.1 = u)
  have hbox : row ⊆ {u} ×ˢ Icc 1 (n-u) := by
    intro p hp
    obtain ⟨hps, hu⟩ := mem_filter.mp hp
    obtain ⟨_, hv, hn⟩ := hs p hps
    exact mem_product.mpr ⟨mem_singleton.mpr hu, mem_Icc.mpr ⟨by omega, by omega⟩⟩
  calc
    _ ≤ ∑ p ∈ row, f p.2 := sum_le_sum fun p hp ↦ h p (mem_filter.mp hp).1 (mem_filter.mp hp).2
    _ ≤ ∑ p ∈ {u} ×ˢ Icc 1 (n-u), f p.2 := sum_le_sum_of_subset_of_nonneg hbox (fun p _ _ ↦ hf p.2)
    _ = _ := by rw [sum_product, sum_singleton]
private theorem sum_row_reciprocals {k n : ℕ} (hk : 0 < k) :
    (∑ u ∈ Icc k n, 1 / ((u : ℝ) * (u + 1))) ≤ 1 / (k : ℝ) := by
  by_cases hkn : k ≤ n
  · let f (j : ℕ) : ℝ := -(1 / (j : ℝ))
    calc
      _ = ∑ u ∈ Icc k n, (f (u + 1) - f u) := by
        refine sum_congr rfl fun u hu ↦ ?_
        have hu' : 0 < (u : ℝ) := Nat.cast_pos.mpr (lt_of_lt_of_le hk (mem_Icc.mp hu).1)
        dsimp [f]
        push_cast
        field_simp
        ring
      _ = f (n + 1) - f k := sum_Icc_sub hkn f
      _ ≤ _ := by dsimp [f]; linarith [show 0 ≤ 1 / ((n + 1 : ℕ) : ℝ) by positivity]
  · rw [Icc_eq_empty_of_lt (lt_of_not_ge hkn), sum_empty]
    positivity
theorem sum_twoStablePairSizeKernel_le_both_long {n : ℕ} (hn : 0 < n)
    (s : Finset (ℕ × ℕ)) (hs : ∀ p ∈ s, ValidPairSizes n p) {b : ℝ} (hb : 0 < b)
    (hl : ∀ p ∈ s, b * Real.sqrt n ≤ (p.1 : ℝ) ∧ b * Real.sqrt n ≤ (p.2 : ℝ)) :
    (∑ p ∈ s, twoStablePairSizeKernel n p) ≤ (n : ℝ) ^ 2 / b ^ 2 := by
  let k := ⌈b * Real.sqrt n⌉₊
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hcut : 0 < b * Real.sqrt n := mul_pos hb (Real.sqrt_pos.mpr hn')
  have hle : b * Real.sqrt n ≤ (k : ℝ) := Nat.le_ceil _
  have hk : (0 : ℝ) < k := hcut.trans_le hle
  have hrow (u : ℕ) (hu : 2 ≤ u) (hun : u+2 ≤ n) :
      (∑ p ∈ s.filter (fun p ↦ p.1 = u), twoStablePairSizeKernel n p) ≤
        (n : ℝ)^3 / k * (1 / ((u : ℝ) * (u + 1))) := by
    calc
      _ ≤ ∑ v ∈ Icc 1 (n-u), ((v : ℝ) * twoStablePairSizeKernel n (u,v)) / k := by
        apply sum_fiber_le_of_row s hs _ (fun v ↦ div_nonneg
          (mul_nonneg (Nat.cast_nonneg _) (twoStablePairSizeKernel_nonneg _ _)) hk.le)
        rintro ⟨u',v⟩ hp rfl
        apply (le_div_iff₀ hk).2
        have hv : k ≤ v := Nat.ceil_le.mpr (hl _ hp).2
        simpa only [mul_comm] using mul_le_mul_of_nonneg_right
          (Nat.cast_le.mpr hv : (k : ℝ) ≤ v) (twoStablePairSizeKernel_nonneg n (u',v))
      _ = _ := by rw [← sum_div, sum_mul_twoStablePairSizeKernel_row (by omega : 1 ≤ u) (by omega : u < n)]; ring
  calc
    _ ≤ ∑ u ∈ Icc k n, (n : ℝ)^3 / k * (1 / ((u : ℝ) * (u + 1))) := by
      apply sum_by_row_le s hs (Icc k n) _ _ (fun _ _ ↦ by positivity)
        (fun u _ ↦ hrow u)
      intro p hp
      exact mem_Icc.mpr ⟨Nat.ceil_le.mpr (hl p hp).1,
        (Nat.le_add_right _ _).trans (hs p hp).2.2⟩
    _ ≤ (n : ℝ)^3 / k * (1 / (k : ℝ)) := by
      rw [← mul_sum]
      exact mul_le_mul_of_nonneg_left (sum_row_reciprocals (Nat.cast_pos.mp hk)) (by positivity)
    _ = (n : ℝ)^3 / (k : ℝ)^2 := by ring
    _ ≤ (n : ℝ)^3 / (b * Real.sqrt n)^2 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_left₀ hcut.le hle _)
    _ = _ := by rw [mul_pow, Real.sq_sqrt hn'.le]; field_simp
theorem sum_twoStablePairSizeWeights_le {n : ℕ} (hn : 0 < n)
    (s : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℝ) {C B : ℝ} (hC : 0 ≤ C)
    (hw : ∀ p ∈ s, w p ≤ C * (1 + Real.log n) * twoStablePairSizeKernel n p)
    (hB : (∑ p ∈ s, twoStablePairSizeKernel n p) ≤ B) :
    (∑ p ∈ s, w p) ≤ C * (1 + Real.log n) * B := by
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (Nat.one_le_cast.mpr hn)
  calc
    _ ≤ ∑ p ∈ s, (C * (1 + Real.log n)) * twoStablePairSizeKernel n p := sum_le_sum hw
    _ = (C * (1 + Real.log n)) * ∑ p ∈ s, twoStablePairSizeKernel n p := (mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hB (by positivity)
end IncomparableLP
end

-- LogarithmicCutoffs
section
open Filter
open scoped Topology BigOperators
namespace IncomparableLP
private noncomputable def logarithmicCycleCutoff (n : ℕ) : ℕ := ⌊Real.log (n : ℝ)⌋₊
end IncomparableLP
end

-- PivotPairEnvelopeScale
section
open Filter
open scoped Topology
namespace IncomparableLP
private noncomputable def longPairEnvelope (C b : ℝ) (n : ℕ) : ℝ :=
  C * (1 + Real.log n) * ((n : ℝ) ^ 2 / b ^ 2)
private theorem tendsto_log_marketSize : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
theorem eventually_longPairEnvelope_le {C b e : ℝ} (hC : 0 < C) (hb : 0 < b)
    (he : 0 < e) :
    ∀ᶠ n : ℕ in atTop, longPairEnvelope C b n ≤ e * ((n : ℝ) * Real.log n) ^ 2 := by
  filter_upwards [tendsto_log_marketSize.eventually_ge_atTop 1,
    tendsto_log_marketSize.eventually_ge_atTop (2 * C / b ^ 2 / e)] with n ht hscale
  let t := Real.log (n : ℝ)
  have htn : 0 ≤ t := zero_le_one.trans ht
  have htwo : 1 + t ≤ 2 * t := by change 1 ≤ t at ht; linarith only [ht]
  have hmul : 2 * C / b ^ 2 ≤ e * t := by
    simpa only [mul_comm e] using (div_le_iff₀ he).1 hscale
  calc
    longPairEnvelope C b n ≤ C * (2 * t) * ((n : ℝ) ^ 2 / b ^ 2) := by
      unfold longPairEnvelope
      gcongr
    _ = ((n : ℝ) ^ 2 * t) * (2 * C / b ^ 2) := by ring
    _ ≤ ((n : ℝ) ^ 2 * t) * (e * t) := mul_le_mul_of_nonneg_left hmul (by positivity)
    _ = _ := by ring
end IncomparableLP
end

-- PivotVarianceClosure
section
open Filter MeasureTheory Set StableMarriage Asymptotics
open scoped BigOperators ENNReal Topology
namespace IncomparableLP
namespace PivotCountParameters
variable {n : ℕ}
private noncomputable def incomparableCountProductMass (q : PivotCountParameters) (x : ScoreProfile n) : ℝ :=
  ∑ i : PivotMark n, ∑ j : PivotMark n,
    {x | IncomparableAnchors (profileOfScores x) i.1 j.1}.indicator (q.count i * q.count j) x
end PivotCountParameters
variable {n : ℕ}
namespace PivotCountParameters
end PivotCountParameters
end IncomparableLP
end

-- TwoStableScoreProduct
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace IncomparableLP
variable {n : ℕ}
private def JointSpouseCell (μ ν : Matching n) (q : ScorePairIndex n) : Prop :=
  μ q.1 = q.2 ∨ ν q.1 = q.2
private instance (μ ν : Matching n) (q : ScorePairIndex n) : Decidable (JointSpouseCell μ ν q) :=
  inferInstanceAs (Decidable (_ ∨ _))
private abbrev JointSpouseIndex (μ ν : Matching n) := {q : ScorePairIndex n // JointSpouseCell μ ν q}
private abbrev JointOffSpouseIndex (μ ν : Matching n) := {q : ScorePairIndex n // ¬ JointSpouseCell μ ν q}
private abbrev JointSpouseScores (μ ν : Matching n) := JointSpouseIndex μ ν → ℝ × ℝ
private abbrev JointOffSpouseScores (μ ν : Matching n) := JointOffSpouseIndex μ ν → ℝ × ℝ
private noncomputable def jointSpouseScoreLaw (μ ν : Matching n) : Measure (JointSpouseScores μ ν) :=
  Measure.pi fun _ ↦ unitScorePairLaw
private instance (μ ν : Matching n) : IsProbabilityMeasure (jointSpouseScoreLaw μ ν) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : JointSpouseIndex μ ν ↦
    unitScorePairLaw))
private noncomputable def jointOffSpouseScoreLaw (μ ν : Matching n) :
    Measure (JointOffSpouseScores μ ν) :=
  Measure.pi fun _ ↦ unitScorePairLaw
private instance (μ ν : Matching n) : IsProbabilityMeasure (jointOffSpouseScoreLaw μ ν) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : JointOffSpouseIndex μ ν ↦
    unitScorePairLaw))
private def scoresByCell (n : ℕ) : ScoreProfile n ≃ᵐ (ScorePairIndex n → ℝ × ℝ) :=
  (splitScorePairs (Equiv.refl (Fin n))).trans
    (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ScorePairIndex n ↦ ℝ × ℝ)
      fun q ↦ q.1 = q.2).symm
private theorem measurePreserving_scoresByCell (n : ℕ) :
    MeasurePreserving (scoresByCell n) (continuousScoreLaw n)
      (Measure.pi fun _ : ScorePairIndex n ↦ unitScorePairLaw) :=
  ((measurePreserving_piEquivPiSubtypeProd (fun _ ↦ unitScorePairLaw)
    fun q : ScorePairIndex n ↦ q.1 = q.2).symm _).comp
    (measurePreserving_splitScorePairs (Equiv.refl (Fin n)))
private theorem scoresByCell_apply (x : ScoreProfile n) (q : ScorePairIndex n) :
    scoresByCell n x q = (x (.inl q.1) q.2, x (.inr q.2) q.1) := by
  classical
  by_cases h : q.1 = q.2
  · obtain ⟨i, j⟩ := q
    change i = j at h
    subst j
    simpa [scoresByCell, MeasurableEquiv.piEquivPiSubtypeProd,
      Equiv.piEquivPiSubtypeProd, diagonalPairAt] using
      diagonalPairAt_splitScorePairs (Equiv.refl (Fin n)) x i
  · simpa [scoresByCell, MeasurableEquiv.piEquivPiSubtypeProd,
      Equiv.piEquivPiSubtypeProd, h] using
      splitScorePairs_offDiagonal_apply (Equiv.refl (Fin n)) x ⟨q, h⟩
private def splitTwoMatchingScores (μ ν : Matching n) :
    ScoreProfile n ≃ᵐ JointSpouseScores μ ν × JointOffSpouseScores μ ν :=
  (scoresByCell n).trans
    (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ScorePairIndex n ↦ ℝ × ℝ)
      (JointSpouseCell μ ν))
theorem measurePreserving_splitTwoMatchingScores (μ ν : Matching n) :
    MeasurePreserving (splitTwoMatchingScores μ ν) (continuousScoreLaw n)
      ((jointSpouseScoreLaw μ ν).prod (jointOffSpouseScoreLaw μ ν)) :=
  (measurePreserving_piEquivPiSubtypeProd (fun _ ↦ unitScorePairLaw)
    (JointSpouseCell μ ν)).comp (measurePreserving_scoresByCell n)
theorem splitTwoMatchingScores_spouse_apply (μ ν : Matching n) (x : ScoreProfile n)
    (q : JointSpouseIndex μ ν) :
    (splitTwoMatchingScores μ ν x).1 q = (x (.inl q.val.1) q.val.2, x (.inr q.val.2) q.val.1) :=
  scoresByCell_apply x q.val
theorem splitTwoMatchingScores_offSpouse_apply (μ ν : Matching n) (x : ScoreProfile n)
    (q : JointOffSpouseIndex μ ν) :
    (splitTwoMatchingScores μ ν x).2 q = (x (.inl q.val.1) q.val.2, x (.inr q.val.2) q.val.1) :=
  scoresByCell_apply x q.val
private def jointManSpouseScoreLeft {μ ν : Matching n} (d : JointSpouseScores μ ν) (m : Fin n) : ℝ :=
  (d ⟨(m, μ m), Or.inl rfl⟩).1
private def jointManSpouseScoreRight {μ ν : Matching n} (d : JointSpouseScores μ ν) (m : Fin n) : ℝ :=
  (d ⟨(m, ν m), Or.inr rfl⟩).1
private def jointWomanSpouseScoreLeft {μ ν : Matching n} (d : JointSpouseScores μ ν) (w : Fin n) : ℝ :=
  (d ⟨(μ.symm w, w), Or.inl (μ.apply_symm_apply w)⟩).2
private def jointWomanSpouseScoreRight {μ ν : Matching n} (d : JointSpouseScores μ ν) (w : Fin n) : ℝ :=
  (d ⟨(ν.symm w, w), Or.inr (ν.apply_symm_apply w)⟩).2
@[simp] theorem jointManSpouseScoreLeft_split (μ ν : Matching n) (x : ScoreProfile n) (m : Fin n) :
    jointManSpouseScoreLeft (splitTwoMatchingScores μ ν x).1 m = x (.inl m) (μ m) := by
  rw [jointManSpouseScoreLeft, splitTwoMatchingScores_spouse_apply]
@[simp] theorem jointManSpouseScoreRight_split (μ ν : Matching n) (x : ScoreProfile n) (m : Fin n) :
    jointManSpouseScoreRight (splitTwoMatchingScores μ ν x).1 m = x (.inl m) (ν m) := by
  rw [jointManSpouseScoreRight, splitTwoMatchingScores_spouse_apply]
@[simp] theorem jointWomanSpouseScoreLeft_split (μ ν : Matching n) (x : ScoreProfile n) (w : Fin n) :
    jointWomanSpouseScoreLeft (splitTwoMatchingScores μ ν x).1 w = x (.inr w) (μ.symm w) := by
  rw [jointWomanSpouseScoreLeft, splitTwoMatchingScores_spouse_apply]
@[simp] theorem jointWomanSpouseScoreRight_split (μ ν : Matching n) (x : ScoreProfile n) (w : Fin n) :
    jointWomanSpouseScoreRight (splitTwoMatchingScores μ ν x).1 w = x (.inr w) (ν.symm w) := by
  rw [jointWomanSpouseScoreRight, splitTwoMatchingScores_spouse_apply]
private def jointNonblockingScoreCell (x₁ y₁ x₂ y₂ : ℝ) : Set (ℝ × ℝ) :=
  nonblockingScoreCell x₁ y₁ ∩ nonblockingScoreCell x₂ y₂
theorem measurableSet_jointNonblockingScoreCell (x₁ y₁ x₂ y₂ : ℝ) :
    MeasurableSet (jointNonblockingScoreCell x₁ y₁ x₂ y₂) :=
  (measurableSet_Iio.prod measurableSet_Iio).compl.inter
    (measurableSet_Iio.prod measurableSet_Iio).compl
private def jointNonblockingCellAt {μ ν : Matching n} (d : JointSpouseScores μ ν)
    (q : ScorePairIndex n) : Set (ℝ × ℝ) :=
  jointNonblockingScoreCell (jointManSpouseScoreLeft d q.1) (jointWomanSpouseScoreLeft d q.2)
    (jointManSpouseScoreRight d q.1) (jointWomanSpouseScoreRight d q.2)
private def jointMarkedNonblocking (μ ν : Matching n) : Set (JointSpouseScores μ ν) :=
  {d | ∀ q : JointSpouseIndex μ ν, d q ∈ jointNonblockingCellAt d q.val}
private def jointOffSpouseNonblocking {μ ν : Matching n} (d : JointSpouseScores μ ν) :
    Set (JointOffSpouseScores μ ν) :=
  univ.pi fun q ↦ jointNonblockingCellAt d q.val
theorem measurableSet_jointMarkedNonblocking (μ ν : Matching n) :
    MeasurableSet (jointMarkedNonblocking μ ν) := by
  unfold jointMarkedNonblocking
  rw [Set.ofPred_forall]
  refine MeasurableSet.iInter fun q ↦ ?_
  have hfst (i : JointSpouseIndex μ ν) : Measurable (fun d : JointSpouseScores μ ν ↦ (d i).1) :=
    measurable_fst.comp (measurable_pi_apply i)
  have hsnd (i : JointSpouseIndex μ ν) : Measurable (fun d : JointSpouseScores μ ν ↦ (d i).2) :=
    measurable_snd.comp (measurable_pi_apply i)
  simpa only [jointNonblockingCellAt, jointNonblockingScoreCell, nonblockingScoreCell,
    jointManSpouseScoreLeft, jointWomanSpouseScoreLeft, jointManSpouseScoreRight,
    jointWomanSpouseScoreRight, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_prod, Set.mem_Iio,
    ← Set.ofPred_and, Set.compl_ofPred] using
      (((measurableSet_lt (hfst q) (hfst ⟨(q.val.1, μ q.val.1), Or.inl rfl⟩)).inter
        (measurableSet_lt (hsnd q) (hsnd ⟨(μ.symm q.val.2, q.val.2),
          Or.inl (μ.apply_symm_apply q.val.2)⟩))).compl.inter
      ((measurableSet_lt (hfst q) (hfst ⟨(q.val.1, ν q.val.1), Or.inr rfl⟩)).inter
        (measurableSet_lt (hsnd q) (hsnd ⟨(ν.symm q.val.2, q.val.2),
          Or.inr (ν.apply_symm_apply q.val.2)⟩))).compl)
theorem measurableSet_jointOffSpouseNonblocking {μ ν : Matching n} (d : JointSpouseScores μ ν) :
    MeasurableSet (jointOffSpouseNonblocking d) :=
  MeasurableSet.univ_pi fun _ ↦ measurableSet_jointNonblockingScoreCell _ _ _ _
private theorem isScoreStable_iff_forall_nonblockingScoreCell (μ : Matching n)
    (x : ScoreProfile n) :
    IsScoreStable x μ ↔ ∀ q : ScorePairIndex n,
      (x (.inl q.1) q.2, x (.inr q.2) q.1) ∈
        nonblockingScoreCell (x (.inl q.1) (μ q.1)) (x (.inr q.2) (μ.symm q.2)) := by
  simp only [nonblockingScoreCell, Set.mem_compl_iff, Set.mem_prod, Set.mem_Iio]
  constructor
  · intro h q hlt
    have hne : μ q.1 ≠ q.2 := fun heq ↦ (lt_irrefl _) (heq ▸ hlt.1)
    exact h q.1 q.2 ⟨hne, hlt.1, hlt.2⟩
  · intro h m w hblock
    exact h (m, w) ⟨hblock.2.1, hblock.2.2⟩
theorem twoStable_iff_splitTwoMatchingScores (μ ν : Matching n) (x : ScoreProfile n) :
    IsScoreStable x μ ∧ IsScoreStable x ν ↔
      (splitTwoMatchingScores μ ν x).1 ∈ jointMarkedNonblocking μ ν ∧
      (splitTwoMatchingScores μ ν x).2 ∈
        jointOffSpouseNonblocking (splitTwoMatchingScores μ ν x).1 := by
  let d := (splitTwoMatchingScores μ ν x).1
  let v := (splitTwoMatchingScores μ ν x).2
  have hleft := isScoreStable_iff_forall_nonblockingScoreCell μ x
  have hright := isScoreStable_iff_forall_nonblockingScoreCell ν x
  have hall : IsScoreStable x μ ∧ IsScoreStable x ν ↔ ∀ q : ScorePairIndex n,
      (x (.inl q.1) q.2, x (.inr q.2) q.1) ∈ jointNonblockingCellAt d q := by
    simp only [d, jointNonblockingCellAt, jointNonblockingScoreCell, Set.mem_inter_iff,
      jointManSpouseScoreLeft_split, jointManSpouseScoreRight_split,
      jointWomanSpouseScoreLeft_split, jointWomanSpouseScoreRight_split, hleft, hright, forall_and]
  rw [hall]
  change _ ↔ d ∈ jointMarkedNonblocking μ ν ∧ v ∈ jointOffSpouseNonblocking d
  constructor
  · intro h
    constructor
    · intro q
      rw [show d q = _ from splitTwoMatchingScores_spouse_apply μ ν x q]
      exact h q.val
    · refine Set.mem_pi.mpr fun q _ ↦ ?_
      rw [show v q = _ from splitTwoMatchingScores_offSpouse_apply μ ν x q]
      exact h q.val
  · rintro ⟨hd, hv⟩ q
    by_cases hq : JointSpouseCell μ ν q
    · simpa only [d, splitTwoMatchingScores_spouse_apply] using hd ⟨q, hq⟩
    · have h := Set.mem_pi.mp hv ⟨q, hq⟩ (Set.mem_univ _)
      simpa only [v, splitTwoMatchingScores_offSpouse_apply] using h
private noncomputable def jointOffSpouseCellLaw {μ ν : Matching n} (d : JointSpouseScores μ ν)
    (q : JointOffSpouseIndex μ ν) : Measure (ℝ × ℝ) :=
  unitScorePairLaw.restrict (jointNonblockingCellAt d q.val)
private instance {μ ν : Matching n} (d : JointSpouseScores μ ν) (q : JointOffSpouseIndex μ ν) :
    IsFiniteMeasure (jointOffSpouseCellLaw d q) :=
  inferInstanceAs (IsFiniteMeasure (unitScorePairLaw.restrict (jointNonblockingCellAt d q.val)))
theorem jointOffSpouseScoreLaw_restrict_nonblocking {μ ν : Matching n} (d : JointSpouseScores μ ν) :
    (jointOffSpouseScoreLaw μ ν).restrict (jointOffSpouseNonblocking d) =
      Measure.pi (jointOffSpouseCellLaw d) :=
  Measure.restrict_pi_pi _ _
theorem jointOffSpouseScoreLaw_nonblocking {μ ν : Matching n} (d : JointSpouseScores μ ν) :
    jointOffSpouseScoreLaw μ ν (jointOffSpouseNonblocking d) =
      ∏ q : JointOffSpouseIndex μ ν, unitScorePairLaw (jointNonblockingCellAt d q.val) :=
  Measure.pi_pi _ _
private noncomputable def normalizedJointOffSpouseCellLaw {μ ν : Matching n}
    (d : JointSpouseScores μ ν) (q : JointOffSpouseIndex μ ν) : Measure (ℝ × ℝ) :=
  (jointOffSpouseCellLaw d q univ)⁻¹ • jointOffSpouseCellLaw d q
private instance {μ ν : Matching n} (d : JointSpouseScores μ ν) (q : JointOffSpouseIndex μ ν) :
    IsFiniteMeasure (normalizedJointOffSpouseCellLaw d q) := by
  constructor
  rw [normalizedJointOffSpouseCellLaw, Measure.smul_apply, smul_eq_mul, mul_comm]
  exact (ENNReal.mul_inv_ne_top _).lt_top
theorem jointManSpouseScoreLeft_eq_right {μ ν : Matching n} (d : JointSpouseScores μ ν)
    {m : Fin n} (hm : μ m = ν m) :
    jointManSpouseScoreLeft d m = jointManSpouseScoreRight d m := by
  unfold jointManSpouseScoreLeft jointManSpouseScoreRight
  exact congrArg (fun q : JointSpouseIndex μ ν ↦ (d q).1)
    (Subtype.ext (Prod.ext rfl hm))
theorem continuousScoreLaw_lintegral_twoStable (μ ν : Matching n)
    {C : Set (JointSpouseScores μ ν)} (hC : MeasurableSet C)
    {f : ScoreProfile n → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x in {x | IsScoreStable x μ ∧ IsScoreStable x ν ∧ (splitTwoMatchingScores μ ν x).1 ∈ C},
      f x ∂continuousScoreLaw n) =
      ∫⁻ d in C ∩ jointMarkedNonblocking μ ν, ∫⁻ v, f ((splitTwoMatchingScores μ ν).symm (d, v))
        ∂(Measure.pi (jointOffSpouseCellLaw d)) ∂jointSpouseScoreLaw μ ν := by
  let e := splitTwoMatchingScores μ ν
  let S : Set (ScoreProfile n) := {x | IsScoreStable x μ ∧ IsScoreStable x ν ∧ (e x).1 ∈ C}
  let T := C ∩ jointMarkedNonblocking μ ν
  let E : Set (JointSpouseScores μ ν × JointOffSpouseScores μ ν) :=
    {z | z.1 ∈ T ∧ z.2 ∈ jointOffSpouseNonblocking z.1}
  let f' := f ∘ e.symm
  have hS : MeasurableSet S := (measurableSet_isScoreStable μ).inter
    ((measurableSet_isScoreStable ν).inter ((measurable_fst.comp e.measurable) hC))
  have hT : MeasurableSet T := hC.inter (measurableSet_jointMarkedNonblocking μ ν)
  have hpre : e ⁻¹' E = S := by
    ext x
    simp only [Set.mem_preimage, E, S, T, Set.mem_ofPred_eq, Set.mem_inter_iff, e]
    have h := twoStable_iff_splitTwoMatchingScores μ ν x
    tauto
  have hE_pre : E = e.symm ⁻¹' S := by
    ext z
    have h := Set.ext_iff.mp hpre (e.symm z)
    simpa only [Set.mem_preimage, MeasurableEquiv.apply_symm_apply] using h
  have hE : MeasurableSet E := hE_pre ▸ hS.preimage e.symm.measurable
  have hf' : Measurable f' := hf.comp e.symm.measurable
  calc
    _ = ∫⁻ z in E, f' z ∂((jointSpouseScoreLaw μ ν).prod (jointOffSpouseScoreLaw μ ν)) := by
      rw [← (measurePreserving_splitTwoMatchingScores μ ν).setLIntegral_comp_preimage hE hf', hpre]
      simp [f', S, e]
    _ = _ := by
      rw [← lintegral_indicator hE, lintegral_prod _ (hf'.indicator hE).aemeasurable,
        ← lintegral_indicator hT]
      refine lintegral_congr fun d ↦ ?_
      by_cases hd : d ∈ T
      · rw [Set.indicator_of_mem hd, ← jointOffSpouseScoreLaw_restrict_nonblocking,
          ← lintegral_indicator (measurableSet_jointOffSpouseNonblocking d)]
        refine lintegral_congr fun v ↦ ?_
        by_cases hv : v ∈ jointOffSpouseNonblocking d <;> simp [E, f', hd, hv, e]
      · rw [Set.indicator_of_notMem hd]
        simp [E, hd]
end IncomparableLP
end

-- TwoStableCommonRows
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace IncomparableLP
private noncomputable def commonRowCellLaw (x b : ℝ) : Measure (ℝ × ℝ) :=
  (rowNonblockingLaw x b univ)⁻¹ • rowNonblockingLaw x b
private instance (x b : ℝ) : IsFiniteMeasure (commonRowCellLaw x b) := by
  constructor
  rw [commonRowCellLaw, Measure.smul_apply, smul_eq_mul, mul_comm]
  exact (ENNReal.mul_inv_ne_top _).lt_top
private theorem base_unitScoreLaw_Ico_of_mem_Icc {x u : ℝ} (hx : 0 ≤ x) (hu : u ≤ 1) :
    unitScoreLaw (Ico x u) = ENNReal.ofReal (u - x) := by
  have hsub : Ico x u ⊆ Icc 0 1 := fun _ h ↦ ⟨hx.trans h.1, h.2.le.trans hu⟩
  rw [unitScoreLaw, Measure.restrict_apply measurableSet_Ico,
    inter_eq_left.mpr hsub, Real.volume_Ico]
section FiniteOutcomes
variable {n : ℕ} {μ ν : Matching n} [MeasurableSpace (Option (Fin n))]
variable [MeasurableSingletonClass (Option (Fin n))]
end FiniteOutcomes
end IncomparableLP
end

-- TwoStablePairDensity
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace IncomparableLP
private noncomputable def pairLaplace (s : ℝ) : ℝ :=
  ∫ t, Real.exp (-s * t) ∂unitScoreLaw
private theorem pairLaplace_integrable (s : ℝ) :
    Integrable (fun t ↦ Real.exp (-s * t)) unitScoreLaw :=
  (show Continuous (fun t : ℝ ↦ Real.exp (-s * t)) by fun_prop).integrableOn_Icc
theorem pairLaplace_nonneg (s : ℝ) : 0 ≤ pairLaplace s :=
  integral_nonneg fun _ ↦ (Real.exp_pos _).le
private theorem pairLaplace_of_ne_zero {s : ℝ} (hs : s ≠ 0) :
    pairLaplace s = (1 - Real.exp (-s)) / s := by
  have hderiv (t : ℝ) :
      HasDerivAt (fun x ↦ -(Real.exp (-s * x)) / s) (Real.exp (-s * t)) t := by
    have H := (((Real.hasDerivAt_exp (-s * t)).comp t
      (hasDerivAt_const_mul (-s))).neg.div_const s)
    have he : -(Real.exp (-s*t)* -s)/s=Real.exp (-s*t) := by field_simp
    rw [←he]
    exact H
  unfold pairLaplace unitScoreLaw
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ ↦ hderiv x)
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp only [mul_one, mul_zero, Real.exp_zero]
  ring
theorem pairLaplace_of_pos {s : ℝ} (hs : 0 < s) :
    pairLaplace s = (1 - Real.exp (-s)) / s :=
  pairLaplace_of_ne_zero hs.ne'
private theorem measurable_pairLaplace : Measurable pairLaplace := by
  have heq : pairLaplace = ({0} : Set ℝ).piecewise (fun _ ↦ 1)
      (fun s ↦ (1 - Real.exp (-s)) / s) := by
    funext s
    by_cases h : s = 0
    · subst s
      simp [pairLaplace]
    · simpa [h] using pairLaplace_of_ne_zero h
  rw [heq]
  exact measurable_const.piecewise (measurableSet_singleton _) (by fun_prop)
theorem pairLaplace_le_exp_mul {s a : ℝ} (ha : 0 ≤ a) :
    pairLaplace (s - a) ≤ Real.exp a * pairLaplace s := by
  unfold pairLaplace
  rw [← integral_const_mul]
  refine integral_mono_ae (pairLaplace_integrable _) ((pairLaplace_integrable _).const_mul _) ?_
  have ht : ∀ᵐ t ∂unitScoreLaw, t ∈ Icc 0 1 := ae_restrict_mem measurableSet_Icc
  filter_upwards [ht] with t ht
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith only [mul_le_mul_of_nonneg_left ht.2 ha]
private theorem pairLaplace_le_exp_relative {s a : ℝ} (hs : 0 < s)
    (ha : 0 ≤ a) (hle : 2 * a ≤ s) :
    pairLaplace (s - a) ≤ Real.exp (2 * a / s) * pairLaplace s := by
  have hsa : 0 < s - a := by linarith
  have hnum : 1 - Real.exp (-(s - a)) ≤ 1 - Real.exp (-s) := by
    gcongr
    linarith
  have hrat : s / (s - a) ≤ 1 + 2 * a / s := by
    apply (div_le_iff₀ hsa).mpr
    rw [add_mul, one_mul, div_mul_eq_mul_div]
    have haux : a ≤ (2 * a * (s - a)) / s := by
      apply (le_div_iff₀ hs).mpr
      nlinarith only [mul_nonneg ha (sub_nonneg.mpr hle)]
    linarith
  rw [pairLaplace_of_pos hsa, pairLaplace_of_pos hs]
  calc
    _ ≤ (1 - Real.exp (-s)) / (s - a) := div_le_div_of_nonneg_right hnum hsa.le
    _ = (s / (s - a)) * ((1 - Real.exp (-s)) / s) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (hrat.trans (by simpa only [add_comm] using Real.add_one_le_exp (2 * a / s)))
      (div_nonneg (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))) hs.le)
theorem pairLaplace_omission_product {ι : Type*} (I : Finset ι) {s : ℝ}
    (a : ι → ℝ) (ha : ∀ i ∈ I, 0 ≤ a i) (hcap : ∀ i ∈ I, a i ≤ 6)
    (hsum : (∑ i ∈ I, a i) ≤ 2 * s) :
    (∏ i ∈ I, pairLaplace (s - a i)) ≤ Real.exp 24 * pairLaplace s ^ I.card := by
  by_cases h : s ≤ 12
  · calc
      _ ≤ ∏ i ∈ I, Real.exp (a i) * pairLaplace s :=
        Finset.prod_le_prod (fun _ _ ↦ pairLaplace_nonneg _)
          (fun i hi ↦ pairLaplace_le_exp_mul (ha i hi))
      _ = Real.exp (∑ i ∈ I, a i) * pairLaplace s ^ I.card := by
        rw [Finset.prod_mul_distrib, Real.exp_sum, Finset.prod_const]
      _ ≤ _ := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith))
        (pow_nonneg (pairLaplace_nonneg s) _)
  · have hs' : 0 < s := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 12) (le_of_not_ge h)
    calc
      _ ≤ ∏ i ∈ I, Real.exp (2 * a i / s) * pairLaplace s :=
        Finset.prod_le_prod (fun _ _ ↦ pairLaplace_nonneg _)
          (fun i hi ↦ pairLaplace_le_exp_relative hs' (ha i hi) (by linarith [hcap i hi]))
      _ = Real.exp (2 * (∑ i ∈ I, a i) / s) * pairLaplace s ^ I.card := by
        rw [Finset.prod_mul_distrib, ← Real.exp_sum, Finset.prod_const, Finset.mul_sum,
          Finset.sum_div]
      _ ≤ _ := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
          ((div_le_iff₀ hs').mpr (by linarith)))
        (pow_nonneg (pairLaplace_nonneg s) _)
private theorem unitScoreLaw_Ico_of_mem_Icc {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    unitScoreLaw (Ico a b) = ENNReal.ofReal (b - a) := by
  have hsub : Ico a b ⊆ Icc 0 1 := fun _ ht ↦ ⟨ha.trans ht.1, ht.2.le.trans hb⟩
  rw [unitScoreLaw, Measure.restrict_apply measurableSet_Ico, inter_eq_left.mpr hsub,
    Real.volume_Ico]
theorem unitScorePairLaw_jointNonblocking_of_le {x₁ y₁ x₂ y₂ : ℝ}
    (hx₁ : x₁ ∈ Icc 0 1) (hx₂ : x₂ ∈ Icc 0 1) (hy₁ : y₁ ∈ Icc 0 1)
    (hy₂ : y₂ ∈ Icc 0 1) (hx : x₁ ≤ x₂) :
    unitScorePairLaw (jointNonblockingScoreCell x₁ y₁ x₂ y₂) =
      1 - ENNReal.ofReal (x₁ * max y₁ y₂ + (x₂ - x₁) * y₂) := by
  let A := Iio x₁ ×ˢ Iio (max y₁ y₂)
  let B := Ico x₁ x₂ ×ˢ Iio y₂
  have hA : MeasurableSet A := measurableSet_Iio.prod measurableSet_Iio
  have hB : MeasurableSet B := measurableSet_Ico.prod measurableSet_Iio
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_left]
    intro p hp hq
    exact (not_lt_of_ge (show x₁ ≤ p.1 from hq.1.1)) (show p.1 < x₁ from hp.1)
  have heq : jointNonblockingScoreCell x₁ y₁ x₂ y₂ = (A ∪ B)ᶜ := by
    ext p
    simp only [jointNonblockingScoreCell, nonblockingScoreCell, A, B, Set.mem_inter_iff,
      Set.mem_union, Set.mem_compl_iff, Set.mem_prod, Set.mem_Iio, Set.mem_Ico, lt_max_iff]
    constructor
    · rintro ⟨h₁, h₂⟩ (⟨hp, h₃ | h₄⟩ | ⟨⟨_, hq⟩, h₄⟩)
      · exact h₁ ⟨hp, h₃⟩
      · exact h₂ ⟨hp.trans_le hx, h₄⟩
      · exact h₂ ⟨hq, h₄⟩
    · intro h
      refine ⟨fun ⟨hp, hq⟩ ↦ h (Or.inl ⟨hp, Or.inl hq⟩), ?_⟩
      rintro ⟨hp, hq⟩
      rcases lt_or_ge p.1 x₁ with hlt | hge
      · exact h (Or.inl ⟨hlt, Or.inr hq⟩)
      · exact h (Or.inr ⟨⟨hge, hp⟩, hq⟩)
  have hymax : max y₁ y₂ ∈ Icc 0 1 := ⟨hy₁.1.trans (le_max_left _ _), max_le hy₁.2 hy₂.2⟩
  rw [heq, measure_compl (hA.union hB) (measure_ne_top _ _), measure_univ,
    measure_union hdisj hB]
  dsimp only [A, B]
  rw [unitScorePairLaw, Measure.prod_prod, Measure.prod_prod, unitScoreLaw_Iio_of_mem_Icc hx₁,
    unitScoreLaw_Iio_of_mem_Icc hymax, unitScoreLaw_Ico_of_mem_Icc hx₁.1 hx₂.2,
    unitScoreLaw_Iio_of_mem_Icc hy₂, ← ENNReal.ofReal_mul hx₁.1,
    ← ENNReal.ofReal_mul (sub_nonneg.mpr hx), ← ENNReal.ofReal_add (mul_nonneg hx₁.1 hymax.1)
      (mul_nonneg (sub_nonneg.mpr hx) hy₂.1)]
theorem unitScorePairLaw_jointNonblocking_le_exp_of_le {x₁ y₁ x₂ y₂ : ℝ}
    (hx₁ : x₁ ∈ Icc 0 1) (hx₂ : x₂ ∈ Icc 0 1) (hy₁ : y₁ ∈ Icc 0 1)
    (hy₂ : y₂ ∈ Icc 0 1) (hx : x₁ ≤ x₂) :
    unitScorePairLaw (jointNonblockingScoreCell x₁ y₁ x₂ y₂) ≤
      ENNReal.ofReal (Real.exp (-(x₁ * max y₁ y₂ + (x₂ - x₁) * y₂))) := by
  rw [unitScorePairLaw_jointNonblocking_of_le hx₁ hx₂ hy₁ hy₂ hx,
    ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub]
  · exact ENNReal.ofReal_le_ofReal (Real.one_sub_le_exp_neg _)
  · exact add_nonneg (mul_nonneg hx₁.1 (hy₁.1.trans (le_max_left _ _)))
      (mul_nonneg (sub_nonneg.mpr hx) hy₂.1)
private def jointSpouseOrientation {μ ν : Matching n} (A B : Finset (Fin n)) :
    Set (JointSpouseScores μ ν) :=
  {d | (∀ m, if m ∈ A then jointManSpouseScoreLeft d m ≤ jointManSpouseScoreRight d m
      else jointManSpouseScoreRight d m ≤ jointManSpouseScoreLeft d m) ∧
    ∀ w, if w ∈ B then jointWomanSpouseScoreRight d w ≤ jointWomanSpouseScoreLeft d w
      else jointWomanSpouseScoreLeft d w ≤ jointWomanSpouseScoreRight d w}
private def JointSpouseThresholdsUnit {μ ν : Matching n} (d : JointSpouseScores μ ν) : Prop :=
  (∀ m, jointManSpouseScoreLeft d m ∈ Icc 0 1 ∧ jointManSpouseScoreRight d m ∈ Icc 0 1) ∧
  (∀ w, jointWomanSpouseScoreLeft d w ∈ Icc 0 1 ∧ jointWomanSpouseScoreRight d w ∈ Icc 0 1)
private def jointBetterMaleScore {μ ν : Matching n} (d : JointSpouseScores μ ν) (m : Fin n) : ℝ :=
  min (jointManSpouseScoreLeft d m) (jointManSpouseScoreRight d m)
private def jointMaleScoreGap {μ ν : Matching n} (d : JointSpouseScores μ ν) (m : Fin n) : ℝ :=
  max (jointManSpouseScoreLeft d m) (jointManSpouseScoreRight d m) - jointBetterMaleScore d m
private def jointWorseFemaleScore {μ ν : Matching n} (d : JointSpouseScores μ ν) (w : Fin n) : ℝ :=
  max (jointWomanSpouseScoreLeft d w) (jointWomanSpouseScoreRight d w)
private def jointExtraFemaleThreshold {μ ν : Matching n} (d : JointSpouseScores μ ν)
    (A : Finset (Fin n)) (m w : Fin n) : ℝ :=
  if m ∈ A then jointWomanSpouseScoreRight d w else jointWomanSpouseScoreLeft d w
theorem jointNonblockingCellAt_mass_le_orientedExp {μ ν : Matching n}
    {d : JointSpouseScores μ ν} {A B : Finset (Fin n)}
    (hd : JointSpouseThresholdsUnit d) (ho : d ∈ jointSpouseOrientation A B)
    (q : ScorePairIndex n) :
    unitScorePairLaw (jointNonblockingCellAt d q) ≤ ENNReal.ofReal (Real.exp (-
      (jointBetterMaleScore d q.1 * jointWorseFemaleScore d q.2 +
        jointMaleScoreGap d q.1 * jointExtraFemaleThreshold d A q.1 q.2))) := by
  have hm := ho.1 q.1
  by_cases h : q.1 ∈ A
  · have hle : jointManSpouseScoreLeft d q.1 ≤ jointManSpouseScoreRight d q.1 := by
      simpa only [if_pos h] using hm
    simpa only [jointNonblockingCellAt, jointBetterMaleScore, jointWorseFemaleScore,
      jointMaleScoreGap, jointExtraFemaleThreshold, if_pos h, min_eq_left hle, max_eq_right hle]
      using unitScorePairLaw_jointNonblocking_le_exp_of_le (hd.1 q.1).1 (hd.1 q.1).2
        (hd.2 q.2).1 (hd.2 q.2).2 hle
  · have hle : jointManSpouseScoreRight d q.1 ≤ jointManSpouseScoreLeft d q.1 := by
      simpa only [if_neg h] using hm
    have hswap : jointNonblockingCellAt d q =
        jointNonblockingScoreCell (jointManSpouseScoreRight d q.1)
          (jointWomanSpouseScoreRight d q.2) (jointManSpouseScoreLeft d q.1)
          (jointWomanSpouseScoreLeft d q.2) := Set.inter_comm _ _
    rw [hswap]
    simpa only [jointBetterMaleScore, jointWorseFemaleScore, jointMaleScoreGap,
      jointExtraFemaleThreshold, if_neg h, min_eq_right hle, max_eq_left hle, max_comm]
      using unitScorePairLaw_jointNonblocking_le_exp_of_le (hd.1 q.1).2 (hd.1 q.1).1
        (hd.2 q.2).2 (hd.2 q.2).1 hle
private def pairOmittedWomen (μ ν : Matching n) (m : Fin n) : Finset (Fin n) := {μ m, ν m}
private def pairUnmarkedRowSum (μ ν : Matching n) (m : Fin n) (y : Fin n → ℝ) : ℝ :=
  ∑ w ∈ Finset.univ \ pairOmittedWomen μ ν m, y w
private def pairRowLoss (μ ν : Matching n) (m : Fin n) (y : Fin n → ℝ) : ℝ :=
  ∑ w ∈ pairOmittedWomen μ ν m, y w
theorem pairUnmarkedRowSum_eq_sub (μ ν : Matching n) (m : Fin n) (y : Fin n → ℝ) :
    pairUnmarkedRowSum μ ν m y = (∑ w, y w) - pairRowLoss μ ν m y := by
  rw [pairUnmarkedRowSum, pairRowLoss, Finset.sum_sdiff_eq_sub (Finset.subset_univ _)]
private def jointOffSpouseByRow (μ ν : Matching n) :
    JointOffSpouseIndex μ ν ≃
      Σ m : Fin n, {w : Fin n // w ∈ Finset.univ \ pairOmittedWomen μ ν m} where
  toFun q := ⟨q.val.1, q.val.2, by
    simpa [JointSpouseCell, pairOmittedWomen, eq_comm] using q.property⟩
  invFun q := ⟨(q.1, q.2.val), by
    have h := (Finset.mem_sdiff.mp q.2.property).2
    simpa only [JointSpouseCell, pairOmittedWomen, Finset.mem_insert, Finset.mem_singleton,
      eq_comm] using h⟩
  left_inv _ := rfl
  right_inv _ := rfl
private theorem sum_jointOffSpouseIndex (μ ν : Matching n) (f : Fin n → Fin n → ℝ) :
    (∑ q : JointOffSpouseIndex μ ν, f q.val.1 q.val.2) =
      ∑ m, pairUnmarkedRowSum μ ν m (f m) := by
  calc
    _ = ∑ q : Σ m : Fin n, {w : Fin n // w ∈ Finset.univ \ pairOmittedWomen μ ν m},
        f q.1 q.2.val :=
      Fintype.sum_equiv (jointOffSpouseByRow μ ν) _ _ (fun _ ↦ rfl)
    _ = _ := ?_
  rw [Fintype.sum_sigma]
  congr 1
  funext m
  exact (Finset.sum_subtype (Finset.univ \ pairOmittedWomen μ ν m)
    (fun _ ↦ Iff.rfl) (f m)).symm
theorem jointOffSpouseScoreLaw_nonblocking_le_rowExp {μ ν : Matching n}
    {d : JointSpouseScores μ ν} {A B : Finset (Fin n)}
    (hd : JointSpouseThresholdsUnit d) (ho : d ∈ jointSpouseOrientation A B) :
    jointOffSpouseScoreLaw μ ν (jointOffSpouseNonblocking d) ≤ ENNReal.ofReal (Real.exp (-
      ∑ m, (jointBetterMaleScore d m * pairUnmarkedRowSum μ ν m (jointWorseFemaleScore d) +
        jointMaleScoreGap d m * pairUnmarkedRowSum μ ν m (jointExtraFemaleThreshold d A m)))) := by
  let e (m w : Fin n) := jointBetterMaleScore d m * jointWorseFemaleScore d w +
    jointMaleScoreGap d m * jointExtraFemaleThreshold d A m w
  rw [jointOffSpouseScoreLaw_nonblocking]
  calc
    _ ≤ ∏ q : JointOffSpouseIndex μ ν, ENNReal.ofReal (Real.exp (-e q.val.1 q.val.2)) :=
      Finset.prod_le_prod (fun _ _ => bot_le) fun q _ ↦ jointNonblockingCellAt_mass_le_orientedExp hd ho q.val
    _ = _ := by
      rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ ↦ (Real.exp_pos _).le), ← Real.exp_sum]
      simp only [Finset.sum_neg_distrib]
      rw [sum_jointOffSpouseIndex μ ν e]
      congr 3
      apply Finset.sum_congr rfl
      intro m _
      simp only [pairUnmarkedRowSum, e, Finset.sum_add_distrib, Finset.mul_sum]
private theorem pairRowLoss_le_two_scores (μ ν : Matching n) (m : Fin n)
    {y : Fin n → ℝ} (hy : ∀ w, 0 ≤ y w) :
    pairRowLoss μ ν m y ≤ y (μ m) + y (ν m) := by
  by_cases h : μ m = ν m
  · simp only [pairRowLoss, pairOmittedWomen, h, Finset.insert_eq_of_mem, Finset.mem_singleton,
      Finset.sum_singleton]
    linarith [hy (ν m)]
  · simp [pairRowLoss, pairOmittedWomen, h]
private theorem pairRowLoss_sum_le (μ ν : Matching n) (I : Finset (Fin n))
    {y : Fin n → ℝ} (hy : ∀ w, 0 ≤ y w) :
    (∑ m ∈ I, pairRowLoss μ ν m y) ≤ 2 * ∑ w, y w := by
  calc
    _ ≤ ∑ m ∈ I, (y (μ m) + y (ν m)) :=
      Finset.sum_le_sum fun m _ ↦ pairRowLoss_le_two_scores μ ν m hy
    _ ≤ ∑ m, (y (μ m) + y (ν m)) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun m _ _ ↦
        add_nonneg (hy (μ m)) (hy (ν m))
    _ = _ := by
      rw [Finset.sum_add_distrib, Equiv.sum_comp μ y, Equiv.sum_comp ν y, two_mul]
theorem pairLaplace_unmarkedRowSum_product (μ ν : Matching n) (I : Finset (Fin n))
    {y : Fin n → ℝ} (hy : ∀ w, y w ∈ Icc 0 1) :
    (∏ m ∈ I, pairLaplace (pairUnmarkedRowSum μ ν m y)) ≤
      Real.exp 24 * pairLaplace (∑ w, y w) ^ I.card := by
  simp_rw [pairUnmarkedRowSum_eq_sub]
  refine pairLaplace_omission_product I _ (fun m _ ↦ Finset.sum_nonneg fun w _ ↦ (hy w).1)
    (fun m _ ↦ ?_) (pairRowLoss_sum_le μ ν I (fun w ↦ (hy w).1))
  have hm := pairRowLoss_le_two_scores μ ν m (fun w ↦ (hy w).1)
  linarith [(hy (μ m)).2, (hy (ν m)).2]
private def jointBetterFemaleScore {μ ν : Matching n} (d : JointSpouseScores μ ν) (w : Fin n) : ℝ :=
  min (jointWomanSpouseScoreLeft d w) (jointWomanSpouseScoreRight d w)
private def jointFemaleScoreGap {μ ν : Matching n} (d : JointSpouseScores μ ν) (w : Fin n) : ℝ :=
  jointWorseFemaleScore d w - jointBetterFemaleScore d w
private def jointFemaleAggregate {μ ν : Matching n} (d : JointSpouseScores μ ν) (B : Finset (Fin n)) :
    ℝ × ℝ × ℝ :=
  (∑ w, jointBetterFemaleScore d w,
    ∑ w ∈ B, jointFemaleScoreGap d w,
    ∑ w ∈ Finset.univ \ B, jointFemaleScoreGap d w)
private theorem jointFemale_sum_left_right {μ ν : Matching n}
    {d : JointSpouseScores μ ν} {A B : Finset (Fin n)} (ho : d ∈ jointSpouseOrientation A B) :
    (∑ w, jointWomanSpouseScoreLeft d w) =
        (jointFemaleAggregate d B).1 + (jointFemaleAggregate d B).2.1 ∧
      (∑ w, jointWomanSpouseScoreRight d w) =
        (jointFemaleAggregate d B).1 + (jointFemaleAggregate d B).2.2 := by
  have hL (w : Fin n) : jointWomanSpouseScoreLeft d w = jointBetterFemaleScore d w +
      if w ∈ B then jointFemaleScoreGap d w else 0 := by
    have h := ho.2 w
    by_cases hw : w ∈ B
    · simp only [if_pos hw] at h ⊢
      simp [jointFemaleScoreGap, jointBetterFemaleScore, jointWorseFemaleScore,
        min_eq_right h, max_eq_left h]
    · simp only [if_neg hw] at h ⊢
      simp [jointBetterFemaleScore, min_eq_left h]
  have hR (w : Fin n) : jointWomanSpouseScoreRight d w = jointBetterFemaleScore d w +
      if w ∈ Finset.univ \ B then jointFemaleScoreGap d w else 0 := by
    have h := ho.2 w
    by_cases hw : w ∈ B
    · simp only [if_pos hw] at h
      simp [jointBetterFemaleScore, hw, min_eq_right h]
    · simp only [if_neg hw] at h
      simp [jointFemaleScoreGap, jointBetterFemaleScore, jointWorseFemaleScore, hw,
        min_eq_left h, max_eq_right h]
  constructor
  · simp_rw [hL, Finset.sum_add_distrib, ← Finset.sum_filter]
    simp [jointFemaleAggregate]
  · simp_rw [hR, Finset.sum_add_distrib, ← Finset.sum_filter]
    simp [jointFemaleAggregate, Finset.sdiff_eq_filter]
private theorem jointFemale_sum_worse {μ ν : Matching n} (d : JointSpouseScores μ ν)
    (B : Finset (Fin n)) :
    (∑ w, jointWorseFemaleScore d w) =
      (jointFemaleAggregate d B).1 + (jointFemaleAggregate d B).2.1 +
        (jointFemaleAggregate d B).2.2 := by
  have h (w : Fin n) :
      jointWorseFemaleScore d w = jointBetterFemaleScore d w + jointFemaleScoreGap d w := by
    simp [jointFemaleScoreGap]
  simp only [h, Finset.sum_add_distrib, jointFemaleAggregate]
  rw [Finset.sum_sdiff_eq_sub (Finset.subset_univ B)]
  ring
private noncomputable def pairAggregateLaplace (n u v : ℕ) (s : ℝ × ℝ × ℝ) : ℝ :=
  pairLaplace (s.1 + s.2.1 + s.2.2) ^ n *
    pairLaplace (s.1 + s.2.2) ^ u * pairLaplace (s.1 + s.2.1) ^ v
theorem pairLaplace_rows_le_aggregate {μ ν : Matching n} {d : JointSpouseScores μ ν}
    {A B : Finset (Fin n)} (hd : JointSpouseThresholdsUnit d)
    (ho : d ∈ jointSpouseOrientation A B) (I J : Finset (Fin n)) :
    (∏ m, pairLaplace (pairUnmarkedRowSum μ ν m (jointWorseFemaleScore d))) *
        (∏ m ∈ I, pairLaplace (pairUnmarkedRowSum μ ν m (jointWomanSpouseScoreRight d))) *
        (∏ m ∈ J, pairLaplace (pairUnmarkedRowSum μ ν m (jointWomanSpouseScoreLeft d))) ≤
      Real.exp 72 * pairAggregateLaplace n I.card J.card (jointFemaleAggregate d B) := by
  have hW (w : Fin n) : jointWorseFemaleScore d w ∈ Icc 0 1 :=
    ⟨(hd.2 w).1.1.trans (le_max_left _ _), max_le (hd.2 w).1.2 (hd.2 w).2.2⟩
  have h₀ := pairLaplace_unmarkedRowSum_product μ ν Finset.univ hW
  have h₁ := pairLaplace_unmarkedRowSum_product μ ν I (fun w ↦ (hd.2 w).2)
  have h₂ := pairLaplace_unmarkedRowSum_product μ ν J (fun w ↦ (hd.2 w).1)
  rw [Finset.card_univ, Fintype.card_fin, jointFemale_sum_worse d B] at h₀
  rw [(jointFemale_sum_left_right ho).2] at h₁
  rw [(jointFemale_sum_left_right ho).1] at h₂
  have hle := mul_le_mul
    (mul_le_mul h₀ h₁ (Finset.prod_nonneg fun _ _ ↦ pairLaplace_nonneg _)
      (mul_nonneg (Real.exp_pos _).le (pow_nonneg (pairLaplace_nonneg _) _)))
    h₂ (Finset.prod_nonneg fun _ _ ↦ pairLaplace_nonneg _)
    (mul_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg (pairLaplace_nonneg _) _))
      (mul_nonneg (Real.exp_pos _).le (pow_nonneg (pairLaplace_nonneg _) _)))
  apply hle.trans_eq
  rw [show (72 : ℝ) = 24 + 24 + 24 by norm_num, Real.exp_add, Real.exp_add,
    pairAggregateLaplace]
  ring
private theorem measurable_jointManSpouseScoreLeft (μ ν : Matching n) (m : Fin n) :
    Measurable (fun d : JointSpouseScores μ ν ↦ jointManSpouseScoreLeft d m) :=
  measurable_fst.comp (measurable_pi_apply _)
private theorem measurable_jointManSpouseScoreRight (μ ν : Matching n) (m : Fin n) :
    Measurable (fun d : JointSpouseScores μ ν ↦ jointManSpouseScoreRight d m) :=
  measurable_fst.comp (measurable_pi_apply _)
private theorem measurable_jointWomanSpouseScoreLeft (μ ν : Matching n) (w : Fin n) :
    Measurable (fun d : JointSpouseScores μ ν ↦ jointWomanSpouseScoreLeft d w) :=
  measurable_snd.comp (measurable_pi_apply _)
private theorem measurable_jointWomanSpouseScoreRight (μ ν : Matching n) (w : Fin n) :
    Measurable (fun d : JointSpouseScores μ ν ↦ jointWomanSpouseScoreRight d w) :=
  measurable_snd.comp (measurable_pi_apply _)
theorem measurableSet_jointSpouseOrientation (μ ν : Matching n) (A B : Finset (Fin n)) :
    MeasurableSet (jointSpouseOrientation (μ := μ) (ν := ν) A B) := by
  unfold jointSpouseOrientation
  rw [Set.ofPred_and, Set.ofPred_forall, Set.ofPred_forall]
  refine (MeasurableSet.iInter fun m ↦ ?_).inter (MeasurableSet.iInter fun w ↦ ?_)
  · by_cases hm : m ∈ A
    · simpa only [if_pos hm] using measurableSet_le (measurable_jointManSpouseScoreLeft μ ν m)
        (measurable_jointManSpouseScoreRight μ ν m)
    · simpa only [if_neg hm] using measurableSet_le (measurable_jointManSpouseScoreRight μ ν m)
        (measurable_jointManSpouseScoreLeft μ ν m)
  · by_cases hw : w ∈ B
    · simpa only [if_pos hw] using measurableSet_le (measurable_jointWomanSpouseScoreRight μ ν w)
        (measurable_jointWomanSpouseScoreLeft μ ν w)
    · simpa only [if_neg hw] using measurableSet_le (measurable_jointWomanSpouseScoreLeft μ ν w)
        (measurable_jointWomanSpouseScoreRight μ ν w)
theorem measurable_jointFemaleAggregate (μ ν : Matching n) (B : Finset (Fin n)) :
    Measurable (fun d : JointSpouseScores μ ν ↦ jointFemaleAggregate d B) := by
  have hL := measurable_jointWomanSpouseScoreLeft μ ν
  have hR := measurable_jointWomanSpouseScoreRight μ ν
  have hb (w : Fin n) : Measurable (fun d : JointSpouseScores μ ν ↦ jointBetterFemaleScore d w) :=
    (hL w).min (hR w)
  have hg (w : Fin n) : Measurable (fun d : JointSpouseScores μ ν ↦ jointFemaleScoreGap d w) :=
    ((hL w).max (hR w)).sub (hb w)
  exact (Finset.measurable_sum _ fun w _ ↦ hb w).prodMk
    ((Finset.measurable_sum _ fun w _ ↦ hg w).prodMk (Finset.measurable_sum _ fun w _ ↦ hg w))
theorem ae_jointSpouseThresholdsUnit (μ ν : Matching n) :
    ∀ᵐ d ∂jointSpouseScoreLaw μ ν, JointSpouseThresholdsUnit d := by
  have h : ∀ᵐ p ∂unitScorePairLaw, p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := by
    have h₁ : ∀ᵐ t ∂unitScoreLaw, t ∈ Icc (0 : ℝ) 1 := ae_restrict_mem measurableSet_Icc
    exact (Measure.ae_prod_mem_iff_ae_ae_mem (measurableSet_Icc.prod measurableSet_Icc)).mpr
      (h₁.mono fun _ ht ↦ h₁.mono fun _ hs ↦ ⟨ht, hs⟩)
  have hd : ∀ᵐ d ∂jointSpouseScoreLaw μ ν,
      ∀ q, d q ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 :=
    ae_all_iff.mpr fun q ↦ (measurePreserving_eval (fun _ ↦ unitScorePairLaw) q).quasiMeasurePreserving.ae h
  filter_upwards [hd] with d h
  exact ⟨fun m ↦ ⟨(h ⟨(m, μ m), Or.inl rfl⟩).1, (h ⟨(m, ν m), Or.inr rfl⟩).1⟩,
    fun w ↦ ⟨(h ⟨(μ.symm w, w), Or.inl (μ.apply_symm_apply w)⟩).2,
      (h ⟨(ν.symm w, w), Or.inr (ν.apply_symm_apply w)⟩).2⟩⟩
private def twoStableOrientationEvent (μ ν : Matching n) (A B : Finset (Fin n)) : Set (ScoreProfile n) :=
  {x | IsScoreStable x μ ∧ IsScoreStable x ν ∧
    (splitTwoMatchingScores μ ν x).1 ∈ jointSpouseOrientation A B}
private noncomputable def orientedPairRowExp {μ ν : Matching n} (d : JointSpouseScores μ ν)
    (A : Finset (Fin n)) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-
    ∑ m, (jointBetterMaleScore d m * pairUnmarkedRowSum μ ν m (jointWorseFemaleScore d) +
      jointMaleScoreGap d m * pairUnmarkedRowSum μ ν m (jointExtraFemaleThreshold d A m))))
theorem continuousScoreLaw_lintegral_twoStableOrientation_le_rowExp (μ ν : Matching n)
    (A B : Finset (Fin n)) {g : ℝ × ℝ × ℝ → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ x in twoStableOrientationEvent μ ν A B,
      g (jointFemaleAggregate (splitTwoMatchingScores μ ν x).1 B) ∂continuousScoreLaw n) ≤
      ∫⁻ d in jointSpouseOrientation A B, g (jointFemaleAggregate d B) * orientedPairRowExp d A
        ∂jointSpouseScoreLaw μ ν := by
  let f (x : ScoreProfile n) := g (jointFemaleAggregate (splitTwoMatchingScores μ ν x).1 B)
  have hf : Measurable f := hg.comp ((measurable_jointFemaleAggregate μ ν B).comp
    (measurable_fst.comp (splitTwoMatchingScores μ ν).measurable))
  let C := jointSpouseOrientation (μ := μ) (ν := ν) A B
  have hC : MeasurableSet C := measurableSet_jointSpouseOrientation μ ν A B
  change (∫⁻ x in _, f x ∂continuousScoreLaw n) ≤ _
  rw [twoStableOrientationEvent, continuousScoreLaw_lintegral_twoStable μ ν hC hf]
  have heq (d : JointSpouseScores μ ν) :
      (∫⁻ v, f ((splitTwoMatchingScores μ ν).symm (d, v))
        ∂(Measure.pi (jointOffSpouseCellLaw d))) =
      g (jointFemaleAggregate d B) *
        jointOffSpouseScoreLaw μ ν (jointOffSpouseNonblocking d) := by
    simp only [f, MeasurableEquiv.apply_symm_apply, lintegral_const]
    rw [← jointOffSpouseScoreLaw_restrict_nonblocking, Measure.restrict_apply_univ]
  simp_rw [heq]
  calc
    _ ≤ ∫⁻ d in C, g (jointFemaleAggregate d B) *
        jointOffSpouseScoreLaw μ ν (jointOffSpouseNonblocking d) ∂jointSpouseScoreLaw μ ν :=
      lintegral_mono_set Set.inter_subset_left
    _ ≤ _ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_of_ae (ae_jointSpouseThresholdsUnit μ ν),
        ae_restrict_mem hC] with d hd ho
      exact mul_le_mul_right (jointOffSpouseScoreLaw_nonblocking_le_rowExp hd ho) _
private noncomputable def pairUnitArrayLaw (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi fun _ ↦ unitScoreLaw
private instance (ι : Type*) [Fintype ι] : IsProbabilityMeasure (pairUnitArrayLaw ι) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : ι ↦ unitScoreLaw))
private def pairUnitCube (ι : Type*) : Set (ι → ℝ) :=
  univ.pi fun _ ↦ Icc 0 1
private theorem pairUnitArrayLaw_eq_restrict (ι : Type*) [Fintype ι] :
    pairUnitArrayLaw ι = (volume : Measure (ι → ℝ)).restrict (pairUnitCube ι) :=
  (Measure.restrict_pi_pi (fun _ : ι ↦ volume) _).symm
theorem pairUnitArrayLaw_lintegral_orderedGap_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (owner : κ → ι) {f : (ι → ℝ) × (κ → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ p in {p : (ι → ℝ) × (κ → ℝ) | ∀ j, p.1 (owner j) ≤ p.2 j},
      f (p.1, fun j ↦ p.2 j - p.1 (owner j))
        ∂((pairUnitArrayLaw ι).prod (pairUnitArrayLaw κ))) ≤
      ∫⁻ p, f p ∂((pairUnitArrayLaw ι).prod (pairUnitArrayLaw κ)) := by
  let Ω := (ι → ℝ) × (κ → ℝ)
  let μ := (volume : Measure (ι → ℝ)).prod (volume : Measure (κ → ℝ))
  let S : Set Ω := {p | ∀ j, p.1 (owner j) ≤ p.2 j}
  let T : Set Ω := pairUnitCube ι ×ˢ pairUnitCube κ
  let F : Ω → Ω := fun p ↦ (p.1, p.2 - fun j ↦ p.1 (owner j))
  have hS : MeasurableSet S := by
    rw [show S = ⋂ j : κ, {p : Ω | p.1 (owner j) ≤ p.2 j} from Set.ofPred_forall _]
    exact MeasurableSet.iInter fun j ↦ measurableSet_le
      ((measurable_pi_apply _).comp measurable_fst) ((measurable_pi_apply _).comp measurable_snd)
  have hT : MeasurableSet T :=
    (MeasurableSet.univ_pi fun _ ↦ measurableSet_Icc).prod
      (MeasurableSet.univ_pi fun _ ↦ measurableSet_Icc)
  have hF : MeasurePreserving F μ μ := by
    have hm : Measurable (fun p : Ω ↦ p.2 - fun j ↦ p.1 (owner j)) :=
      measurable_snd.sub (measurable_pi_iff.2 fun _ ↦
        (measurable_pi_apply _).comp measurable_fst)
    exact (MeasurePreserving.id (volume : Measure (ι → ℝ))).skew_product hm
      (Filter.Eventually.of_forall fun x ↦ by
        simpa only [sub_eq_add_neg] using
          (measurePreserving_add_right (volume : Measure (κ → ℝ))
            (-(fun j ↦ x (owner j)))).map_eq)
  have hsub : S ∩ T ⊆ F ⁻¹' T := by
    rintro ⟨x, y⟩ ⟨hxy, hx, hy⟩
    refine ⟨hx, Set.mem_univ_pi.mpr fun j ↦ ?_⟩
    change y j - x (owner j) ∈ Icc 0 1
    exact ⟨sub_nonneg.mpr (hxy j), sub_le_self _ ((Set.mem_univ_pi.mp hx (owner j)).1)
      |>.trans ((Set.mem_univ_pi.mp hy j).2)⟩
  change (∫⁻ p in S, f (F p) ∂_) ≤ _
  rw [pairUnitArrayLaw_eq_restrict, pairUnitArrayLaw_eq_restrict, Measure.prod_restrict,
    Measure.restrict_restrict hS]
  change (∫⁻ p in S ∩ T, f (F p) ∂μ) ≤ ∫⁻ p in T, f p ∂μ
  exact (lintegral_mono_set hsub).trans_eq (hF.setLIntegral_comp_preimage hT hf)
private noncomputable def pairExpSum {α : Type*} [Fintype α] (r : α → ℝ) (x : α → ℝ) :=
  ENNReal.ofReal (Real.exp (-(∑ i, x i * r i)))
private theorem measurable_pairExpSum {α : Type*} [Fintype α] (r : α → ℝ) :
    Measurable (pairExpSum r) := by
  apply ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (Measurable.neg ?_))
  exact Finset.measurable_sum _ fun i _ ↦ (measurable_pi_apply i).mul_const _
private theorem pairUnitArrayLaw_lintegral_exp_sum {α : Type*} [Fintype α] (r : α → ℝ) :
    (∫⁻ x, pairExpSum r x ∂pairUnitArrayLaw α) = ENNReal.ofReal (∏ i, pairLaplace (r i)) := by
  let k (i : α) (t : ℝ) := ENNReal.ofReal (Real.exp (-(t * r i)))
  have hk (i : α) : Measurable (k i) := by unfold k; fun_prop
  have heq (x : α → ℝ) : pairExpSum r x = ∏ i, k i (x i) := by
    rw [pairExpSum, ← Finset.sum_neg_distrib, Real.exp_sum, ENNReal.ofReal_prod_of_nonneg]
    exact fun _ _ ↦ (Real.exp_pos _).le
  have hcoord (i : α) : (∫⁻ x : α → ℝ, k i (x i) ∂pairUnitArrayLaw α) =
      ENNReal.ofReal (pairLaplace (r i)) := by
    unfold pairUnitArrayLaw
    rw [(measurePreserving_eval (fun _ : α ↦ unitScoreLaw) i).lintegral_comp (hk i)]
    have hk' (t : ℝ) : k i t = ENNReal.ofReal (Real.exp (-r i * t)) := by
      dsimp only [k]
      ring_nf
    simp_rw [hk']
    exact (ofReal_integral_eq_lintegral_ofReal (pairLaplace_integrable _)
      (Filter.Eventually.of_forall fun _ ↦ (Real.exp_pos _).le)).symm
  simp_rw [heq]
  change (∫⁻ x : α → ℝ, ∏ i, k i (x i) ∂Measure.pi (fun _ : α ↦ unitScoreLaw)) = _
  rw [ProbabilityTheory.lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ _
    (ProbabilityTheory.iIndepFun_pi fun i ↦ (hk i).aemeasurable)
    (fun i ↦ (hk i).comp (measurable_pi_apply i))]
  rw [ENNReal.ofReal_prod_of_nonneg (fun _ _ ↦ pairLaplace_nonneg _)]
  exact Finset.prod_congr rfl fun i _ ↦ hcoord i
theorem pairUnitArrayLaw_lintegral_exp_sums {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → ℝ) (b : κ → ℝ) :
    (∫⁻ p : (ι → ℝ) × (κ → ℝ), ENNReal.ofReal (Real.exp
      (-(∑ i, p.1 i * a i) - ∑ j, p.2 j * b j))
      ∂((pairUnitArrayLaw ι).prod (pairUnitArrayLaw κ))) =
      ENNReal.ofReal ((∏ i, pairLaplace (a i)) * ∏ j, pairLaplace (b j)) := by
  have heq (p : (ι → ℝ) × (κ → ℝ)) : ENNReal.ofReal (Real.exp
      (-(∑ i, p.1 i * a i) - ∑ j, p.2 j * b j)) = pairExpSum a p.1 * pairExpSum b p.2 := by
    rw [pairExpSum, pairExpSum, sub_eq_add_neg, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
  simp_rw [heq]
  rw [lintegral_prod_mul (measurable_pairExpSum a).aemeasurable (measurable_pairExpSum b).aemeasurable,
    pairUnitArrayLaw_lintegral_exp_sum, pairUnitArrayLaw_lintegral_exp_sum, ENNReal.ofReal_mul]
  exact Finset.prod_nonneg fun _ _ ↦ pairLaplace_nonneg _
private abbrev PairMovedMan (μ ν : Matching n) := {m : Fin n // μ m ≠ ν m}
private def pairBetterSpouseCell (μ ν : Matching n) (A : Finset (Fin n))
    (m : Fin n) : JointSpouseIndex μ ν :=
  if m ∈ A then ⟨(m, μ m), Or.inl rfl⟩ else ⟨(m, ν m), Or.inr rfl⟩
private def pairWorseSpouseCell (μ ν : Matching n) (A : Finset (Fin n))
    (m : Fin n) : JointSpouseIndex μ ν :=
  if m ∈ A then ⟨(m, ν m), Or.inr rfl⟩ else ⟨(m, μ m), Or.inl rfl⟩
private theorem pairBetterSpouseCell_row (μ ν : Matching n) (A : Finset (Fin n)) (m : Fin n) :
    (pairBetterSpouseCell μ ν A m).val.1 = m := by
  unfold pairBetterSpouseCell
  split <;> rfl
private theorem pairWorseSpouseCell_row (μ ν : Matching n) (A : Finset (Fin n)) (m : Fin n) :
    (pairWorseSpouseCell μ ν A m).val.1 = m := by
  unfold pairWorseSpouseCell
  split <;> rfl
private theorem pairBetterSpouseCell_ne_worse (μ ν : Matching n) (A : Finset (Fin n))
    {m : Fin n} (hm : μ m ≠ ν m) :
    pairBetterSpouseCell μ ν A m ≠ pairWorseSpouseCell μ ν A m := by
  by_cases hA : m ∈ A
  · intro h
    have h' := congrArg (fun q : JointSpouseIndex μ ν ↦ q.val.2) h
    exact hm (by simpa [pairBetterSpouseCell, pairWorseSpouseCell, hA] using h')
  · intro h
    have h' := congrArg (fun q : JointSpouseIndex μ ν ↦ q.val.2) h
    exact hm (by simpa [pairBetterSpouseCell, pairWorseSpouseCell, hA, eq_comm] using h')
private noncomputable def pairSpouseCellByRow (μ ν : Matching n) (A : Finset (Fin n)) :
    (Fin n ⊕ PairMovedMan μ ν) ≃ JointSpouseIndex μ ν := by
  let F : Fin n ⊕ PairMovedMan μ ν → JointSpouseIndex μ ν :=
    Sum.elim (pairBetterSpouseCell μ ν A) (fun m ↦ pairWorseSpouseCell μ ν A m.val)
  refine Equiv.ofBijective F ⟨?_, ?_⟩
  · intro i j hij
    have h := congrArg (fun q : JointSpouseIndex μ ν ↦ q.val.1) hij
    rcases i with i | i <;> rcases j with j | j
    · simpa only [F, Sum.elim_inl, pairBetterSpouseCell_row, Sum.inl.injEq] using h
    · have h' : i = j.val := by
        simpa only [F, Sum.elim_inl, Sum.elim_inr, pairBetterSpouseCell_row,
          pairWorseSpouseCell_row] using h
      subst i
      exact (pairBetterSpouseCell_ne_worse μ ν A j.property hij).elim
    · have h' : i.val = j := by
        simpa only [F, Sum.elim_inl, Sum.elim_inr, pairBetterSpouseCell_row,
          pairWorseSpouseCell_row] using h
      subst j
      exact (pairBetterSpouseCell_ne_worse μ ν A i.property hij.symm).elim
    · congr 1
      apply Subtype.ext
      simpa only [F, Sum.elim_inr, pairWorseSpouseCell_row] using h
  · rintro ⟨⟨m, w⟩, hw⟩
    rcases hw with (h : μ m = w) | (h : ν m = w)
    · subst w
      by_cases hm : m ∈ A
      · exact ⟨.inl m, by simp [F, pairBetterSpouseCell, hm]⟩
      · by_cases heq : μ m = ν m
        · exact ⟨.inl m, by simp [F, pairBetterSpouseCell, hm, heq]⟩
        · exact ⟨.inr ⟨m, heq⟩, by simp [F, pairWorseSpouseCell, hm]⟩
    · subst w
      by_cases hm : m ∈ A
      · by_cases heq : μ m = ν m
        · exact ⟨.inl m, by simp [F, pairBetterSpouseCell, hm, heq]⟩
        · exact ⟨.inr ⟨m, heq⟩, by simp [F, pairWorseSpouseCell, hm]⟩
      · exact ⟨.inl m, by simp [F, pairBetterSpouseCell, hm]⟩
private def pairSpouseCellTranspose (μ ν : Matching n) :
    JointSpouseIndex μ.symm ν.symm ≃ JointSpouseIndex μ ν where
  toFun q := ⟨q.val.swap, by
    rcases q.property with h | h
    · exact Or.inl ((μ.symm_apply_eq).mp h).symm
    · exact Or.inr ((ν.symm_apply_eq).mp h).symm⟩
  invFun q := ⟨q.val.swap, by
    rcases q.property with h | h
    · exact Or.inl ((μ.symm_apply_eq).mpr h.symm)
    · exact Or.inr ((ν.symm_apply_eq).mpr h.symm)⟩
  left_inv _ := rfl
  right_inv _ := rfl
private abbrev PairMovedWoman (μ ν : Matching n) := PairMovedMan μ.symm ν.symm
private noncomputable def pairSpouseCellByColumn (μ ν : Matching n) (B : Finset (Fin n)) :
    (Fin n ⊕ PairMovedWoman μ ν) ≃ JointSpouseIndex μ ν :=
  (pairSpouseCellByRow μ.symm ν.symm (Finset.univ \ B)).trans (pairSpouseCellTranspose μ ν)
private abbrev PairOrderedSpouseArrays (n : ℕ) (κ : Type*) := (Fin n → ℝ) × (κ → ℝ)
private noncomputable def pairSplitSpouseScores (μ ν : Matching n) (A B : Finset (Fin n)) :
    JointSpouseScores μ ν ≃ᵐ
      PairOrderedSpouseArrays n (PairMovedMan μ ν) ×
        PairOrderedSpouseArrays n (PairMovedWoman μ ν) :=
  let J := JointSpouseIndex μ ν
  (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ J).trans <|
    ((MeasurableEquiv.arrowCongr' (pairSpouseCellByRow μ ν A).symm (.refl ℝ)).trans
      (MeasurableEquiv.sumPiEquivProdPi fun _ ↦ ℝ)).prodCongr
    ((MeasurableEquiv.arrowCongr' (pairSpouseCellByColumn μ ν B).symm (.refl ℝ)).trans
      (MeasurableEquiv.sumPiEquivProdPi fun _ ↦ ℝ))
private noncomputable def pairOrderedSpouseLaw (n : ℕ) (κ : Type*) [Fintype κ] :
    Measure (PairOrderedSpouseArrays n κ) :=
  (pairUnitArrayLaw (Fin n)).prod (pairUnitArrayLaw κ)
private instance (n : ℕ) (κ : Type*) [Fintype κ] : IsProbabilityMeasure (pairOrderedSpouseLaw n κ) :=
  inferInstanceAs (IsProbabilityMeasure ((pairUnitArrayLaw (Fin n)).prod (pairUnitArrayLaw κ)))
theorem measurePreserving_pairSplitSpouseScores (μ ν : Matching n) (A B : Finset (Fin n)) :
    MeasurePreserving (pairSplitSpouseScores μ ν A B) (jointSpouseScoreLaw μ ν)
      ((pairOrderedSpouseLaw n (PairMovedMan μ ν)).prod
        (pairOrderedSpouseLaw n (PairMovedWoman μ ν))) := by
  let J := JointSpouseIndex μ ν
  have hM := (measurePreserving_sumPiEquivProdPi
    (fun _ : Fin n ⊕ PairMovedMan μ ν ↦ unitScoreLaw)).comp
      (measurePreserving_arrowCongr' (fun _ ↦ unitScoreLaw)
        (fun _ : Fin n ⊕ PairMovedMan μ ν ↦ unitScoreLaw)
        (pairSpouseCellByRow μ ν A).symm (.refl ℝ) (fun _ ↦ MeasurePreserving.id _))
  have hW := (measurePreserving_sumPiEquivProdPi
    (fun _ : Fin n ⊕ PairMovedWoman μ ν ↦ unitScoreLaw)).comp
      (measurePreserving_arrowCongr' (fun _ ↦ unitScoreLaw)
        (fun _ : Fin n ⊕ PairMovedWoman μ ν ↦ unitScoreLaw)
        (pairSpouseCellByColumn μ ν B).symm (.refl ℝ) (fun _ ↦ MeasurePreserving.id _))
  exact (hM.prod hW).comp (measurePreserving_arrowProdEquivProdArrow ℝ ℝ J
    (fun _ ↦ unitScoreLaw) (fun _ ↦ unitScoreLaw))
theorem pairSplitSpouseScores_male_first (μ ν : Matching n) (A B : Finset (Fin n))
    (d : JointSpouseScores μ ν) (m : Fin n) :
    (pairSplitSpouseScores μ ν A B d).1.1 m =
      if m ∈ A then jointManSpouseScoreLeft d m else jointManSpouseScoreRight d m := by
  change (d (pairBetterSpouseCell μ ν A m)).1 = _
  by_cases h : m ∈ A <;> simp [pairBetterSpouseCell, h, jointManSpouseScoreLeft,
    jointManSpouseScoreRight]
theorem pairSplitSpouseScores_male_second (μ ν : Matching n) (A B : Finset (Fin n))
    (d : JointSpouseScores μ ν) (m : PairMovedMan μ ν) :
    (pairSplitSpouseScores μ ν A B d).1.2 m =
      if m.val ∈ A then jointManSpouseScoreRight d m.val else jointManSpouseScoreLeft d m.val := by
  change (d (pairWorseSpouseCell μ ν A m.val)).1 = _
  by_cases h : m.val ∈ A <;> simp [pairWorseSpouseCell, h, jointManSpouseScoreLeft,
    jointManSpouseScoreRight]
theorem pairSplitSpouseScores_female_first (μ ν : Matching n) (A B : Finset (Fin n))
    (d : JointSpouseScores μ ν) (w : Fin n) :
    (pairSplitSpouseScores μ ν A B d).2.1 w =
      if w ∈ B then jointWomanSpouseScoreRight d w else jointWomanSpouseScoreLeft d w := by
  change (d (pairSpouseCellTranspose μ ν
    (pairBetterSpouseCell μ.symm ν.symm (Finset.univ \ B) w))).2 = _
  by_cases h : w ∈ B <;> simp [pairBetterSpouseCell, h, pairSpouseCellTranspose,
    jointWomanSpouseScoreLeft, jointWomanSpouseScoreRight]
theorem pairSplitSpouseScores_female_second (μ ν : Matching n) (A B : Finset (Fin n))
    (d : JointSpouseScores μ ν) (w : PairMovedWoman μ ν) :
    (pairSplitSpouseScores μ ν A B d).2.2 w =
      if w.val ∈ B then jointWomanSpouseScoreLeft d w.val else jointWomanSpouseScoreRight d w.val := by
  change (d (pairSpouseCellTranspose μ ν
    (pairWorseSpouseCell μ.symm ν.symm (Finset.univ \ B) w.val))).2 = _
  by_cases h : w.val ∈ B <;> simp [pairWorseSpouseCell, h, pairSpouseCellTranspose,
    jointWomanSpouseScoreLeft, jointWomanSpouseScoreRight]
private def pairOrderedArraySet {κ : Type*} (owner : κ → Fin n) :
    Set (PairOrderedSpouseArrays n κ) :=
  {p | ∀ j, p.1 (owner j) ≤ p.2 j}
private theorem measurableSet_pairOrderedArraySet {κ : Type*} [Fintype κ]
    (owner : κ → Fin n) : MeasurableSet (pairOrderedArraySet owner) := by
  unfold pairOrderedArraySet
  rw [Set.ofPred_forall]
  exact MeasurableSet.iInter fun _ ↦ measurableSet_le
    ((measurable_pi_apply _).comp measurable_fst) ((measurable_pi_apply _).comp measurable_snd)
private theorem jointWomanSpouseScoreLeft_eq_right {μ ν : Matching n} (d : JointSpouseScores μ ν)
    {w : Fin n} (hw : μ.symm w = ν.symm w) :
    jointWomanSpouseScoreLeft d w = jointWomanSpouseScoreRight d w := by
  unfold jointWomanSpouseScoreLeft jointWomanSpouseScoreRight
  exact congrArg (fun q : JointSpouseIndex μ ν ↦ (d q).2)
    (Subtype.ext (Prod.ext hw rfl))
private theorem jointSpouseOrientation_iff_pairOrdered {μ ν : Matching n}
    (A B : Finset (Fin n)) (d : JointSpouseScores μ ν) :
    d ∈ jointSpouseOrientation A B ↔
      (pairSplitSpouseScores μ ν A B d).1 ∈
        pairOrderedArraySet (fun m : PairMovedMan μ ν ↦ m.val) ∧
      (pairSplitSpouseScores μ ν A B d).2 ∈
        pairOrderedArraySet (fun w : PairMovedWoman μ ν ↦ w.val) := by
  change (_ ∧ _) ↔ (_ ∧ _)
  apply and_congr
  · change (∀ m, _) ↔ ∀ m : PairMovedMan μ ν, _
    simp only [pairSplitSpouseScores_male_first, pairSplitSpouseScores_male_second]
    constructor
    · intro h m
      by_cases hm : m.val ∈ A <;> simpa only [hm, ite_true, ite_false] using h m.val
    · intro h m
      by_cases hne : μ m = ν m
      · simp [jointManSpouseScoreLeft_eq_right d hne]
      · by_cases hm : m ∈ A
        · simpa only [if_pos hm] using h ⟨m, hne⟩
        · simpa only [if_neg hm] using h ⟨m, hne⟩
  · change (∀ w, _) ↔ ∀ w : PairMovedWoman μ ν, _
    simp only [pairSplitSpouseScores_female_first, pairSplitSpouseScores_female_second]
    constructor
    · intro h w
      by_cases hw : w.val ∈ B <;> simpa only [hw, ite_true, ite_false] using h w.val
    · intro h w
      by_cases hne : μ.symm w = ν.symm w
      · simp [jointWomanSpouseScoreLeft_eq_right d hne]
      · by_cases hw : w ∈ B
        · simpa only [if_pos hw] using h ⟨w, hne⟩
        · simpa only [if_neg hw] using h ⟨w, hne⟩
private theorem jointBetterMaleScore_pairSplit {μ ν : Matching n}
    {A B : Finset (Fin n)} {d : JointSpouseScores μ ν} (ho : d ∈ jointSpouseOrientation A B)
    (m : Fin n) :
    jointBetterMaleScore d m = (pairSplitSpouseScores μ ν A B d).1.1 m := by
  have h := ho.1 m
  rw [pairSplitSpouseScores_male_first, jointBetterMaleScore]
  by_cases hm : m ∈ A
  · simp only [if_pos hm] at h ⊢
    exact min_eq_left h
  · simp only [if_neg hm] at h ⊢
    exact min_eq_right h
private theorem jointMaleScoreGap_pairSplit {μ ν : Matching n}
    {A B : Finset (Fin n)} {d : JointSpouseScores μ ν} (ho : d ∈ jointSpouseOrientation A B)
    (m : PairMovedMan μ ν) :
    jointMaleScoreGap d m.val =
      (pairSplitSpouseScores μ ν A B d).1.2 m - (pairSplitSpouseScores μ ν A B d).1.1 m.val := by
  have h := ho.1 m.val
  rw [jointMaleScoreGap, jointBetterMaleScore_pairSplit ho, pairSplitSpouseScores_male_second]
  by_cases hm : m.val ∈ A
  · simp only [if_pos hm] at h ⊢
    rw [max_eq_right h]
  · simp only [if_neg hm] at h ⊢
    rw [max_eq_left h]
private theorem jointMaleScoreGap_common {μ ν : Matching n}
    (d : JointSpouseScores μ ν) {m : Fin n} (hm : μ m = ν m) : jointMaleScoreGap d m = 0 := by
  simp [jointMaleScoreGap, jointBetterMaleScore, jointManSpouseScoreLeft_eq_right d hm]
private theorem jointWomanSpouseScores_inverse_congr {μ ν : Matching n}
    (A B : Finset (Fin n)) (p q : PairOrderedSpouseArrays n (PairMovedMan μ ν))
    (y : PairOrderedSpouseArrays n (PairMovedWoman μ ν)) (w : Fin n) :
    let d := (pairSplitSpouseScores μ ν A B).symm (p, y)
    let d' := (pairSplitSpouseScores μ ν A B).symm (q, y)
    jointWomanSpouseScoreLeft d w = jointWomanSpouseScoreLeft d' w ∧
      jointWomanSpouseScoreRight d w = jointWomanSpouseScoreRight d' w := by
  let e := pairSplitSpouseScores μ ν A B
  let d := e.symm (p, y)
  let d' := e.symm (q, y)
  have h₁ := pairSplitSpouseScores_female_first μ ν A B d w
  have h₁' := pairSplitSpouseScores_female_first μ ν A B d' w
  change (e (e.symm (p, y))).2.1 w = _ at h₁
  change (e (e.symm (q, y))).2.1 w = _ at h₁'
  rw [MeasurableEquiv.apply_symm_apply] at h₁ h₁'
  by_cases hw : μ.symm w = ν.symm w
  · rw [jointWomanSpouseScoreLeft_eq_right d hw] at h₁
    rw [jointWomanSpouseScoreLeft_eq_right d' hw] at h₁'
    simp only [ite_self] at h₁ h₁'
    exact ⟨(jointWomanSpouseScoreLeft_eq_right d hw).trans
      (h₁.symm.trans (h₁'.trans (jointWomanSpouseScoreLeft_eq_right d' hw).symm)),
      h₁.symm.trans h₁'⟩
  · let j : PairMovedWoman μ ν := ⟨w, hw⟩
    have h₂ := pairSplitSpouseScores_female_second μ ν A B d j
    have h₂' := pairSplitSpouseScores_female_second μ ν A B d' j
    change (e (e.symm (p, y))).2.2 j = _ at h₂
    change (e (e.symm (q, y))).2.2 j = _ at h₂'
    rw [MeasurableEquiv.apply_symm_apply] at h₂ h₂'
    by_cases hB : w ∈ B
    · simp only [j, if_pos hB] at h₁ h₁' h₂ h₂'
      exact ⟨h₂.symm.trans h₂', h₁.symm.trans h₁'⟩
    · simp only [j, if_neg hB] at h₁ h₁' h₂ h₂'
      exact ⟨h₁.symm.trans h₁', h₂.symm.trans h₂'⟩
private theorem sum_jointMaleScoreGap {μ ν : Matching n} (d : JointSpouseScores μ ν)
    (f : Fin n → ℝ) :
    (∑ m, jointMaleScoreGap d m * f m) =
      ∑ m : PairMovedMan μ ν, jointMaleScoreGap d m.val * f m.val := by
  have h (m : Fin n) : jointMaleScoreGap d m * f m =
      if μ m ≠ ν m then jointMaleScoreGap d m * f m else 0 := by
    by_cases hm : μ m = ν m
    · simp [hm, jointMaleScoreGap_common d hm]
    · simp [hm]
  calc
    _ = ∑ m, if μ m ≠ ν m then jointMaleScoreGap d m * f m else 0 :=
      Finset.sum_congr rfl fun m _ ↦ h m
    _ = _ := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (by simp) (fun m ↦ jointMaleScoreGap d m * f m)
private theorem pairOrderedSpouseLaw_inner_le {μ ν : Matching n}
    (A B : Finset (Fin n)) (y : PairOrderedSpouseArrays n (PairMovedWoman μ ν))
    (hy : y ∈ pairOrderedArraySet (fun w : PairMovedWoman μ ν ↦ w.val)) :
    let e := pairSplitSpouseScores μ ν A B
    let d₀ := e.symm ((fun _ ↦ 0, fun _ ↦ 0), y)
    let a m := pairUnmarkedRowSum μ ν m (jointWorseFemaleScore d₀)
    let b (m : PairMovedMan μ ν) :=
      pairUnmarkedRowSum μ ν m.val (jointExtraFemaleThreshold d₀ A m.val)
    (∫⁻ p in pairOrderedArraySet (fun m : PairMovedMan μ ν ↦ m.val),
      orientedPairRowExp (e.symm (p, y)) A ∂pairOrderedSpouseLaw n (PairMovedMan μ ν)) ≤
      ENNReal.ofReal ((∏ m, pairLaplace (a m)) * ∏ m, pairLaplace (b m)) := by
  dsimp only
  let e := pairSplitSpouseScores μ ν A B
  let d₀ := e.symm ((fun _ ↦ 0, fun _ ↦ 0), y)
  let a m := pairUnmarkedRowSum μ ν m (jointWorseFemaleScore d₀)
  let b (m : PairMovedMan μ ν) :=
    pairUnmarkedRowSum μ ν m.val (jointExtraFemaleThreshold d₀ A m.val)
  let f (p : PairOrderedSpouseArrays n (PairMovedMan μ ν)) :=
    ENNReal.ofReal (Real.exp (-(∑ m, p.1 m * a m) - ∑ m, p.2 m * b m))
  have hf : Measurable f := by
    unfold f
    apply ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (Measurable.sub
      (Measurable.neg ?_) ?_))
    · exact Finset.measurable_sum _ fun _ _ ↦ ((measurable_pi_apply _).comp measurable_fst).mul_const _
    · exact Finset.measurable_sum _ fun _ _ ↦ ((measurable_pi_apply _).comp measurable_snd).mul_const _
  have hchange : (∫⁻ p in pairOrderedArraySet (fun m : PairMovedMan μ ν ↦ m.val),
      orientedPairRowExp (e.symm (p, y)) A ∂pairOrderedSpouseLaw n (PairMovedMan μ ν)) =
      ∫⁻ p in pairOrderedArraySet (fun m : PairMovedMan μ ν ↦ m.val),
        f (p.1, fun m ↦ p.2 m - p.1 m.val) ∂pairOrderedSpouseLaw n (PairMovedMan μ ν) := by
    apply setLIntegral_congr_fun (measurableSet_pairOrderedArraySet _)
    intro p hp
    let d := e.symm (p, y)
    have ho : d ∈ jointSpouseOrientation A B := (jointSpouseOrientation_iff_pairOrdered A B d).mpr
      (by simpa only [d, e, MeasurableEquiv.apply_symm_apply] using And.intro hp hy)
    have hW : jointWorseFemaleScore d = jointWorseFemaleScore d₀ := by
      funext w
      have h := jointWomanSpouseScores_inverse_congr A B p (fun _ ↦ 0, fun _ ↦ 0) y w
      exact congrArg₂ max h.1 h.2
    have hE (m : Fin n) : jointExtraFemaleThreshold d A m = jointExtraFemaleThreshold d₀ A m := by
      funext w
      have h := jointWomanSpouseScores_inverse_congr A B p (fun _ ↦ 0, fun _ ↦ 0) y w
      unfold jointExtraFemaleThreshold
      split
      · exact h.2
      · exact h.1
    change orientedPairRowExp d A = _
    unfold orientedPairRowExp f
    rw [Finset.sum_add_distrib, sum_jointMaleScoreGap]
    simp only [jointBetterMaleScore_pairSplit ho, jointMaleScoreGap_pairSplit ho,
      hW, hE, d, e, MeasurableEquiv.apply_symm_apply, a, b, neg_add_rev, sub_eq_add_neg]
    exact congrArg (fun s ↦ ENNReal.ofReal (Real.exp s)) (add_comm _ _)
  rw [hchange]
  exact (pairUnitArrayLaw_lintegral_orderedGap_le (fun m : PairMovedMan μ ν ↦ m.val) hf).trans_eq
    (pairUnitArrayLaw_lintegral_exp_sums a b)
private def pairOrientedMovedMen (μ ν : Matching n) (A : Finset (Fin n)) : Finset (Fin n) :=
  A.filter fun m ↦ μ m ≠ ν m
private theorem pairProd_moved_male_gap {μ ν : Matching n} (d : JointSpouseScores μ ν)
    (A : Finset (Fin n)) :
    (∏ m : PairMovedMan μ ν,
      pairLaplace (pairUnmarkedRowSum μ ν m.val (jointExtraFemaleThreshold d A m.val))) =
      (∏ m ∈ pairOrientedMovedMen μ ν A,
        pairLaplace (pairUnmarkedRowSum μ ν m (jointWomanSpouseScoreRight d))) *
      (∏ m ∈ pairOrientedMovedMen μ ν (Finset.univ \ A),
        pairLaplace (pairUnmarkedRowSum μ ν m (jointWomanSpouseScoreLeft d))) := by
  let F m := pairLaplace (pairUnmarkedRowSum μ ν m (jointExtraFemaleThreshold d A m))
  have h₀ : (∏ m : PairMovedMan μ ν, F m.val) =
      ∏ m ∈ Finset.univ.filter (fun m ↦ μ m ≠ ν m), F m :=
    (Finset.prod_subtype _ (by simp) F).symm
  rw [h₀, ← Finset.prod_filter_mul_prod_filter_not _ (fun m ↦ m ∈ A) F]
  have h₁ : (Finset.univ.filter (fun m ↦ μ m ≠ ν m)).filter (fun m ↦ m ∈ A) =
      pairOrientedMovedMen μ ν A := by
    ext m
    simp [pairOrientedMovedMen, and_comm]
  have h₂ : (Finset.univ.filter (fun m ↦ μ m ≠ ν m)).filter (fun m ↦ m ∉ A) =
      pairOrientedMovedMen μ ν (Finset.univ \ A) := by
    ext m
    simp [pairOrientedMovedMen, and_comm]
  rw [h₁, h₂]
  congr 1
  · apply Finset.prod_congr rfl
    intro m hm
    have h := (Finset.mem_filter.mp hm).1
    have he : jointExtraFemaleThreshold d A m = jointWomanSpouseScoreRight d := by
      funext w
      simp only [jointExtraFemaleThreshold, if_pos h]
    simp only [F, he]
  · apply Finset.prod_congr rfl
    intro m hm
    have h := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hm).1).2
    have he : jointExtraFemaleThreshold d A m = jointWomanSpouseScoreLeft d := by
      funext w
      simp only [jointExtraFemaleThreshold, if_neg h]
    simp only [F, he]
private theorem pairSplitSpouseScores_thresholdsUnit {μ ν : Matching n}
    (A B : Finset (Fin n)) (d : JointSpouseScores μ ν)
    (hm₀ : ∀ m, (pairSplitSpouseScores μ ν A B d).1.1 m ∈ Icc 0 1)
    (hm₁ : ∀ m, (pairSplitSpouseScores μ ν A B d).1.2 m ∈ Icc 0 1)
    (hw₀ : ∀ w, (pairSplitSpouseScores μ ν A B d).2.1 w ∈ Icc 0 1)
    (hw₁ : ∀ w, (pairSplitSpouseScores μ ν A B d).2.2 w ∈ Icc 0 1) :
    JointSpouseThresholdsUnit d := by
  constructor
  · intro m
    have h₀ := hm₀ m
    rw [pairSplitSpouseScores_male_first] at h₀
    by_cases he : μ m = ν m
    · rw [jointManSpouseScoreLeft_eq_right d he, ite_self] at h₀
      simpa only [jointManSpouseScoreLeft_eq_right d he] using And.intro h₀ h₀
    · have h₁ := hm₁ ⟨m, he⟩
      rw [pairSplitSpouseScores_male_second] at h₁
      by_cases h : m ∈ A
      · exact ⟨by simpa only [if_pos h] using h₀, by simpa only [if_pos h] using h₁⟩
      · exact ⟨by simpa only [if_neg h] using h₁, by simpa only [if_neg h] using h₀⟩
  · intro w
    have h₀ := hw₀ w
    rw [pairSplitSpouseScores_female_first] at h₀
    by_cases he : μ.symm w = ν.symm w
    · rw [jointWomanSpouseScoreLeft_eq_right d he, ite_self] at h₀
      simpa only [jointWomanSpouseScoreLeft_eq_right d he] using And.intro h₀ h₀
    · have h₁ := hw₁ ⟨w, he⟩
      rw [pairSplitSpouseScores_female_second] at h₁
      by_cases h : w ∈ B
      · exact ⟨by simpa only [if_pos h] using h₁, by simpa only [if_pos h] using h₀⟩
      · exact ⟨by simpa only [if_neg h] using h₀, by simpa only [if_neg h] using h₁⟩
private theorem ae_pairOrderedSpouseLaw_unit (n : ℕ) (κ : Type*) [Fintype κ] :
    ∀ᵐ p ∂pairOrderedSpouseLaw n κ,
      (∀ i, p.1 i ∈ Icc 0 1) ∧ ∀ j, p.2 j ∈ Icc 0 1 := by
  rw [pairOrderedSpouseLaw, pairUnitArrayLaw_eq_restrict, pairUnitArrayLaw_eq_restrict,
    Measure.prod_restrict]
  exact (ae_restrict_mem ((MeasurableSet.univ_pi fun _ ↦ measurableSet_Icc).prod
    (MeasurableSet.univ_pi fun _ ↦ measurableSet_Icc))).mono fun _ h ↦
      ⟨Set.mem_univ_pi.mp h.1, Set.mem_univ_pi.mp h.2⟩
private theorem measurable_orientedPairRowExp (μ ν : Matching n) (A : Finset (Fin n)) :
    Measurable (fun d : JointSpouseScores μ ν ↦ orientedPairRowExp d A) := by
  have hx₁ := measurable_jointManSpouseScoreLeft μ ν
  have hx₂ := measurable_jointManSpouseScoreRight μ ν
  have hy₁ := measurable_jointWomanSpouseScoreLeft μ ν
  have hy₂ := measurable_jointWomanSpouseScoreRight μ ν
  apply ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (Measurable.neg ?_))
  refine Finset.measurable_sum _ fun m _ ↦ Measurable.add (Measurable.mul
    ((hx₁ m).min (hx₂ m)) ?_) (Measurable.mul (((hx₁ m).max (hx₂ m)).sub
    ((hx₁ m).min (hx₂ m))) ?_)
  · exact Finset.measurable_sum _ fun w _ ↦ (hy₁ w).max (hy₂ w)
  · refine Finset.measurable_sum _ fun w _ ↦ ?_
    by_cases h : m ∈ A
    · simpa only [jointExtraFemaleThreshold, if_pos h] using hy₂ w
    · simpa only [jointExtraFemaleThreshold, if_neg h] using hy₁ w
private theorem jointFemaleAggregate_inverse_congr {μ ν : Matching n}
    (A B : Finset (Fin n)) (p q : PairOrderedSpouseArrays n (PairMovedMan μ ν))
    (y : PairOrderedSpouseArrays n (PairMovedWoman μ ν)) :
    jointFemaleAggregate ((pairSplitSpouseScores μ ν A B).symm (p, y)) B =
      jointFemaleAggregate ((pairSplitSpouseScores μ ν A B).symm (q, y)) B := by
  simp only [jointFemaleAggregate, jointBetterFemaleScore, jointFemaleScoreGap,
    jointWorseFemaleScore, (jointWomanSpouseScores_inverse_congr A B p q y _).1,
    (jointWomanSpouseScores_inverse_congr A B p q y _).2]
private noncomputable def pairFemaleAggregateFromOrdered {μ ν : Matching n} (A B : Finset (Fin n))
    (y : PairOrderedSpouseArrays n (PairMovedWoman μ ν)) : ℝ × ℝ × ℝ :=
  jointFemaleAggregate ((pairSplitSpouseScores μ ν A B).symm ((fun _ ↦ 0, fun _ ↦ 0), y)) B
theorem continuousScoreLaw_lintegral_twoStableOrientation_le_femaleAggregate (μ ν : Matching n)
    (A B : Finset (Fin n)) {g : ℝ × ℝ × ℝ → ℝ≥0∞} (hg : Measurable g) :
    let u := (pairOrientedMovedMen μ ν A).card
    let v := (pairOrientedMovedMen μ ν (Finset.univ \ A)).card
    (∫⁻ x in twoStableOrientationEvent μ ν A B,
      g (jointFemaleAggregate (splitTwoMatchingScores μ ν x).1 B) ∂continuousScoreLaw n) ≤
      ∫⁻ y in pairOrderedArraySet (fun w : PairMovedWoman μ ν ↦ w.val),
        g (pairFemaleAggregateFromOrdered A B y) * ENNReal.ofReal
          (Real.exp 72 * pairAggregateLaplace n u v (pairFemaleAggregateFromOrdered A B y))
        ∂pairOrderedSpouseLaw n (PairMovedWoman μ ν) := by
  dsimp only
  let e := pairSplitSpouseScores μ ν A B
  let M := PairMovedMan μ ν
  let W := PairMovedWoman μ ν
  let p₀ : PairOrderedSpouseArrays n M := (fun _ ↦ 0, fun _ ↦ 0)
  let S := pairOrderedArraySet (fun m : M ↦ m.val)
  let T := pairOrderedArraySet (fun w : W ↦ w.val)
  let H (z : PairOrderedSpouseArrays n M × PairOrderedSpouseArrays n W) :=
    g (jointFemaleAggregate (e.symm z) B) * orientedPairRowExp (e.symm z) A
  have hH : Measurable H := ((hg.comp (measurable_jointFemaleAggregate μ ν B)).mul
    (measurable_orientedPairRowExp μ ν A)).comp e.symm.measurable
  have hST : e ⁻¹' (S ×ˢ T) = jointSpouseOrientation A B := by
    ext d
    exact (jointSpouseOrientation_iff_pairOrdered A B d).symm
  have hS : MeasurableSet S := measurableSet_pairOrderedArraySet _
  have hT : MeasurableSet T := measurableSet_pairOrderedArraySet _
  refine (continuousScoreLaw_lintegral_twoStableOrientation_le_rowExp μ ν A B hg).trans ?_
  have htransport := (measurePreserving_pairSplitSpouseScores μ ν A B).setLIntegral_comp_preimage
    (hS.prod hT) hH
  rw [hST] at htransport
  simp only [H, e, MeasurableEquiv.symm_apply_apply] at htransport
  rw [htransport]
  change (∫⁻ z in S ×ˢ T, H z
    ∂((pairOrderedSpouseLaw n M).prod (pairOrderedSpouseLaw n W))) ≤ _
  rw [← Measure.prod_restrict, lintegral_prod_symm' H hH]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem hT,
    ae_restrict_of_ae (ae_pairOrderedSpouseLaw_unit n W)] with y hy hyu
  let d₀ := e.symm (p₀, y)
  have hunit : JointSpouseThresholdsUnit d₀ := by
    apply pairSplitSpouseScores_thresholdsUnit A B d₀
    · intro m
      simp [d₀, e, p₀]
    · intro m
      simp [d₀, e, p₀]
    · simpa only [d₀, e, MeasurableEquiv.apply_symm_apply] using hyu.1
    · simpa only [d₀, e, MeasurableEquiv.apply_symm_apply] using hyu.2
  have ho₀ : d₀ ∈ jointSpouseOrientation A B := by
    apply (jointSpouseOrientation_iff_pairOrdered A B d₀).mpr
    refine ⟨?_, by simpa only [d₀, e, MeasurableEquiv.apply_symm_apply] using hy⟩
    simp [d₀, e, p₀, pairOrderedArraySet]
  have hcongr (p : PairOrderedSpouseArrays n M) :
      H (p, y) = g (jointFemaleAggregate d₀ B) * orientedPairRowExp (e.symm (p, y)) A := by
    unfold H
    rw [jointFemaleAggregate_inverse_congr A B p p₀ y]
  simp_rw [hcongr]
  have hmeas : Measurable (fun p : PairOrderedSpouseArrays n M ↦
      orientedPairRowExp (e.symm (p, y)) A) :=
    (measurable_orientedPairRowExp μ ν A).comp
      (e.symm.measurable.comp (measurable_id.prodMk measurable_const))
  rw [lintegral_const_mul _ hmeas]
  apply mul_le_mul_right
  refine (pairOrderedSpouseLaw_inner_le A B y hy).trans ?_
  apply ENNReal.ofReal_le_ofReal
  rw [pairProd_moved_male_gap d₀ A, ← mul_assoc]
  exact pairLaplace_rows_le_aggregate hunit ho₀ _ _
private def pairFemaleAggregateFromGaps {μ ν : Matching n} (B : Finset (Fin n))
    (z : PairOrderedSpouseArrays n (PairMovedWoman μ ν)) : ℝ × ℝ × ℝ :=
  (∑ w, z.1 w,
    ∑ w : PairMovedWoman μ ν with w.val ∈ B, z.2 w,
    ∑ w : PairMovedWoman μ ν with w.val ∉ B, z.2 w)
theorem measurable_pairFemaleAggregateFromGaps (μ ν : Matching n) (B : Finset (Fin n)) :
    Measurable (pairFemaleAggregateFromGaps (μ := μ) (ν := ν) B) := by
  exact (Finset.measurable_sum _ fun w _ ↦ (measurable_pi_apply w).comp measurable_fst).prodMk
    ((Finset.measurable_sum _ fun w _ ↦ (measurable_pi_apply w).comp measurable_snd).prodMk
      (Finset.measurable_sum _ fun w _ ↦ (measurable_pi_apply w).comp measurable_snd))
private theorem jointBetterFemaleScore_pairSplit {μ ν : Matching n}
    {A B : Finset (Fin n)} {d : JointSpouseScores μ ν} (ho : d ∈ jointSpouseOrientation A B)
    (w : Fin n) :
    jointBetterFemaleScore d w = (pairSplitSpouseScores μ ν A B d).2.1 w := by
  have h := ho.2 w
  rw [pairSplitSpouseScores_female_first, jointBetterFemaleScore]
  by_cases hw : w ∈ B
  · simp only [if_pos hw] at h ⊢
    exact min_eq_right h
  · simp only [if_neg hw] at h ⊢
    exact min_eq_left h
private theorem jointFemaleScoreGap_pairSplit {μ ν : Matching n}
    {A B : Finset (Fin n)} {d : JointSpouseScores μ ν} (ho : d ∈ jointSpouseOrientation A B)
    (w : PairMovedWoman μ ν) :
    jointFemaleScoreGap d w.val =
      (pairSplitSpouseScores μ ν A B d).2.2 w - (pairSplitSpouseScores μ ν A B d).2.1 w.val := by
  have h := ho.2 w.val
  rw [jointFemaleScoreGap, jointBetterFemaleScore_pairSplit ho, pairSplitSpouseScores_female_second,
    jointWorseFemaleScore]
  by_cases hw : w.val ∈ B
  · simp only [if_pos hw] at h ⊢
    rw [max_eq_left h]
  · simp only [if_neg hw] at h ⊢
    rw [max_eq_right h]
private theorem jointFemaleScoreGap_common {μ ν : Matching n}
    (d : JointSpouseScores μ ν) {w : Fin n} (hw : μ.symm w = ν.symm w) :
    jointFemaleScoreGap d w = 0 := by
  simp [jointFemaleScoreGap, jointBetterFemaleScore, jointWorseFemaleScore,
    jointWomanSpouseScoreLeft_eq_right d hw]
private theorem jointFemaleScoreGap_sum_filter {μ ν : Matching n} (d : JointSpouseScores μ ν)
    (I : Finset (Fin n)) :
    (∑ w ∈ I, jointFemaleScoreGap d w) =
      ∑ w : PairMovedWoman μ ν with w.val ∈ I, jointFemaleScoreGap d w.val := by
  let f w := if w ∈ I then jointFemaleScoreGap d w else 0
  have h (w : Fin n) : f w = if μ.symm w ≠ ν.symm w then f w else 0 := by
    by_cases hw : μ.symm w = ν.symm w
    · simp [f, hw, jointFemaleScoreGap_common d hw]
    · simp [hw]
  have hI : Finset.univ.filter (fun w : Fin n ↦ w ∈ I) = I := by
    ext w
    simp
  calc
    _ = ∑ w, f w := by
      conv_lhs => rw [← hI, Finset.sum_filter]
    _ = ∑ w, if μ.symm w ≠ ν.symm w then f w else 0 :=
      Finset.sum_congr rfl fun w _ ↦ h w
    _ = ∑ w : PairMovedWoman μ ν, f w.val := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (by simp) f
    _ = _ := by rw [Finset.sum_filter]
private theorem pairFemaleAggregateFromOrdered_eq {μ ν : Matching n} (A B : Finset (Fin n))
    (y : PairOrderedSpouseArrays n (PairMovedWoman μ ν))
    (hy : y ∈ pairOrderedArraySet (fun w : PairMovedWoman μ ν ↦ w.val)) :
    pairFemaleAggregateFromOrdered A B y =
      pairFemaleAggregateFromGaps B (y.1, fun w ↦ y.2 w - y.1 w.val) := by
  let e := pairSplitSpouseScores μ ν A B
  let d := e.symm ((fun _ ↦ 0, fun _ ↦ 0), y)
  have ho : d ∈ jointSpouseOrientation A B := by
    apply (jointSpouseOrientation_iff_pairOrdered A B d).mpr
    refine ⟨?_, by simpa only [d, e, MeasurableEquiv.apply_symm_apply] using hy⟩
    simp [d, e, pairOrderedArraySet]
  unfold pairFemaleAggregateFromOrdered pairFemaleAggregateFromGaps jointFemaleAggregate
  change (∑ w, jointBetterFemaleScore d w, ∑ w ∈ B, jointFemaleScoreGap d w,
    ∑ w ∈ Finset.univ \ B, jointFemaleScoreGap d w) = _
  rw [jointFemaleScoreGap_sum_filter d B, jointFemaleScoreGap_sum_filter d (Finset.univ \ B)]
  simp only [jointBetterFemaleScore_pairSplit ho, jointFemaleScoreGap_pairSplit ho, d, e,
    MeasurableEquiv.apply_symm_apply, Finset.mem_sdiff, Finset.mem_univ, true_and]
private theorem measurable_pairAggregateLaplace (n u v : ℕ) :
    Measurable (pairAggregateLaplace n u v) := by
  unfold pairAggregateLaplace
  let p : ℝ × ℝ × ℝ → ℝ := Prod.fst
  let q : ℝ × ℝ × ℝ → ℝ := fun x ↦ x.2.1
  let r : ℝ × ℝ × ℝ → ℝ := fun x ↦ x.2.2
  have hp : Measurable p := measurable_fst
  have hq : Measurable q := measurable_fst.comp measurable_snd
  have hr : Measurable r := measurable_snd.comp measurable_snd
  exact (((measurable_pairLaplace.comp ((hp.add hq).add hr)).pow_const _).mul
    ((measurable_pairLaplace.comp (hp.add hr)).pow_const _)).mul
    ((measurable_pairLaplace.comp (hp.add hq)).pow_const _)
theorem continuousScoreLaw_lintegral_twoStableOrientation_le_gapAggregate (μ ν : Matching n)
    (A B : Finset (Fin n)) {g : ℝ × ℝ × ℝ → ℝ≥0∞} (hg : Measurable g) :
    let u := (pairOrientedMovedMen μ ν A).card
    let v := (pairOrientedMovedMen μ ν (Finset.univ \ A)).card
    (∫⁻ x in twoStableOrientationEvent μ ν A B,
      g (jointFemaleAggregate (splitTwoMatchingScores μ ν x).1 B) ∂continuousScoreLaw n) ≤
      ∫⁻ z, g (pairFemaleAggregateFromGaps (μ := μ) (ν := ν) B z) * ENNReal.ofReal
          (Real.exp 72 * pairAggregateLaplace n u v (pairFemaleAggregateFromGaps B z))
        ∂pairOrderedSpouseLaw n (PairMovedWoman μ ν) := by
  dsimp only
  let u := (pairOrientedMovedMen μ ν A).card
  let v := (pairOrientedMovedMen μ ν (Finset.univ \ A)).card
  let W := PairMovedWoman μ ν
  let T := pairOrderedArraySet (fun w : W ↦ w.val)
  let F (z : PairOrderedSpouseArrays n W) :=
    g (pairFemaleAggregateFromGaps (μ := μ) (ν := ν) B z) * ENNReal.ofReal
      (Real.exp 72 * pairAggregateLaplace n u v (pairFemaleAggregateFromGaps B z))
  have hF : Measurable F :=
    (hg.mul (ENNReal.measurable_ofReal.comp (measurable_const.mul
      (measurable_pairAggregateLaplace n u v)))).comp
        (measurable_pairFemaleAggregateFromGaps μ ν B)
  refine (continuousScoreLaw_lintegral_twoStableOrientation_le_femaleAggregate μ ν A B hg).trans ?_
  calc
    _ = ∫⁻ y in T, F (y.1, fun w ↦ y.2 w - y.1 w.val) ∂pairOrderedSpouseLaw n W := by
      apply setLIntegral_congr_fun (measurableSet_pairOrderedArraySet _)
      intro y hy
      simp only [F, pairFemaleAggregateFromOrdered_eq A B y hy, u, v]
      rfl
    _ ≤ _ := pairUnitArrayLaw_lintegral_orderedGap_le (fun w : W ↦ w.val) hF
private noncomputable def pairUniformSumLaw (ι : Type*) [Fintype ι] : Measure ℝ :=
  (pairUnitArrayLaw ι).map (fun z ↦ ∑ i, z i)
private instance (ι : Type*) [Fintype ι] : IsProbabilityMeasure (pairUniformSumLaw ι) :=
  Measure.isProbabilityMeasure_map (by fun_prop : Measurable (fun z : ι → ℝ ↦ ∑ i, z i)).aemeasurable
theorem pairUniformSumLaw_le_spouseRadialLaw (ι : Type*) [Fintype ι]
    (hι : 0 < Fintype.card ι) :
    pairUniformSumLaw ι ≤ spouseRadialLaw (Fintype.card ι) := by
  let k := Fintype.card ι
  let e := Fintype.equivFin ι
  let T := MeasurableEquiv.arrowCongr' e (.refl ℝ)
  have hT : MeasurePreserving T (pairUnitArrayLaw ι) (pairUnitArrayLaw (Fin k)) :=
    measurePreserving_arrowCongr' _ _ _ _ (fun _ ↦ MeasurePreserving.id unitScoreLaw)
  have hs : Measurable (fun x : Fin k → ℝ ↦ ∑ i, x i) :=
    Finset.measurable_sum _ fun i _ ↦ measurable_pi_apply i
  have hcomp : (fun x : Fin k → ℝ ↦ ∑ i, x i) ∘ T = (fun z : ι → ℝ ↦ ∑ i, z i) := by
    funext z
    change (∑ i : Fin k, z (e.symm i)) = ∑ i : ι, z i
    exact Equiv.sum_comp e.symm z
  have heq : pairUniformSumLaw ι = pairUniformSumLaw (Fin k) := by
    unfold pairUniformSumLaw
    rw [← hcomp, ← Measure.map_map hs hT.measurable, hT.map_eq]
  have hmap :
      ((volume : Measure (Fin k → ℝ)).restrict {z | ∀ i, 0 ≤ z i}).map
        (fun z ↦ ∑ i, z i) = spouseRadialLaw k := by
    ext s hS
    let f := s.indicator (1 : ℝ → ℝ≥0∞)
    have hf : Measurable f := measurable_const.indicator hS
    calc
      _ = ∫⁻ t, f t ∂((volume : Measure (Fin k → ℝ)).restrict {z | ∀ i, 0 ≤ z i}).map
          (fun z ↦ ∑ i, z i) := (lintegral_indicator_one hS).symm
      _ = ∫⁻ z, f (∑ i, z i) ∂((volume : Measure (Fin k → ℝ)).restrict {z | ∀ i, 0 ≤ z i}) :=
        lintegral_map hf hs
      _ = ∫⁻ t, ∫⁻ w, f (∑ i, t * w i) ∂spouseAngularLaw k ∂spouseRadialLaw k :=
        lintegral_spouseRadialAngular hι (hf.comp hs)
      _ = ∫⁻ t, f t ∂spouseRadialLaw k := by
        apply lintegral_congr
        intro t
        calc
          _ = ∫⁻ _w : Fin k → ℝ, f t ∂spouseAngularLaw k := by
            apply lintegral_congr_ae
            filter_upwards [ae_spouseAngularLaw hι] with w hw
            rw [← Finset.mul_sum, hw.2, mul_one]
          _ = _ := by rw [lintegral_const, measure_univ, mul_one]
      _ = _ := lintegral_indicator_one hS
  rw [heq, ← hmap, pairUniformSumLaw, pairUnitArrayLaw_eq_restrict]
  have hsub : pairUnitCube (Fin k) ⊆ {z : Fin k → ℝ | ∀ i, 0 ≤ z i} :=
    fun z hz ↦ show ∀ i, 0 ≤ z i from fun i ↦ (Set.mem_univ_pi.mp hz i).1
  exact Measure.map_mono (Measure.restrict_mono hsub le_rfl) hs
private abbrev PairFemaleGapClass (μ ν : Matching n) (B : Finset (Fin n)) :=
  {w : PairMovedWoman μ ν // w.val ∈ B}
private abbrev PairFemaleOtherGapClass (μ ν : Matching n) (B : Finset (Fin n)) :=
  {w : PairMovedWoman μ ν // w.val ∉ B}
theorem map_pairFemaleAggregateFromGaps (μ ν : Matching n) (B : Finset (Fin n)) :
    (pairOrderedSpouseLaw n (PairMovedWoman μ ν)).map (pairFemaleAggregateFromGaps B) =
      (pairUniformSumLaw (Fin n)).prod
        ((pairUniformSumLaw (PairFemaleGapClass μ ν B)).prod
          (pairUniformSumLaw (PairFemaleOtherGapClass μ ν B))) := by
  let W := PairMovedWoman μ ν
  let V := PairFemaleGapClass μ ν B
  let U := PairFemaleOtherGapClass μ ν B
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : W ↦ ℝ) (fun w ↦ w.val ∈ B)
  let E := (MeasurableEquiv.refl (Fin n → ℝ)).prodCongr e
  have hE : MeasurePreserving E (pairOrderedSpouseLaw n W)
      ((pairUnitArrayLaw (Fin n)).prod ((pairUnitArrayLaw V).prod (pairUnitArrayLaw U))) :=
    (MeasurePreserving.id _).prod (measurePreserving_piEquivPiSubtypeProd (fun _ ↦ unitScoreLaw) _)
  let s₀ (x : Fin n → ℝ) := ∑ i, x i
  let s₁ (x : V → ℝ) := ∑ i, x i
  let s₂ (x : U → ℝ) := ∑ i, x i
  have hs₀ : Measurable s₀ := Finset.measurable_sum _ fun _ _ ↦ measurable_pi_apply _
  have hs₁ : Measurable s₁ := Finset.measurable_sum _ fun _ _ ↦ measurable_pi_apply _
  have hs₂ : Measurable s₂ := Finset.measurable_sum _ fun _ _ ↦ measurable_pi_apply _
  let F := Prod.map s₀ (Prod.map s₁ s₂)
  have hF : Measurable F := hs₀.prodMap (hs₁.prodMap hs₂)
  have heq : F ∘ E = pairFemaleAggregateFromGaps (μ := μ) (ν := ν) B := by
    funext p
    unfold pairFemaleAggregateFromGaps
    change (∑ w, p.1 w, ∑ w : V, p.2 w.val, ∑ w : U, p.2 w.val) = _
    congr 1
    exact Prod.ext
      ((Finset.sum_subtype (p := fun w : W ↦ w.val ∈ B)
        (Finset.univ.filter (fun w : W ↦ w.val ∈ B))
        (fun _ ↦ by simp) p.2).symm)
      ((Finset.sum_subtype (p := fun w : W ↦ w.val ∉ B)
        (Finset.univ.filter (fun w : W ↦ w.val ∉ B))
        (fun _ ↦ by simp) p.2).symm)
  rw [← heq, ← Measure.map_map hF hE.measurable, hE.map_eq]
  unfold F
  rw [← Measure.map_prod_map _ _ hs₀ (hs₁.prodMap hs₂), ← Measure.map_prod_map _ _ hs₁ hs₂]
  rfl
private def pairAggregateCutoff (n : ℕ) : Set (ℝ × ℝ × ℝ) :=
  {s | s.1 + s.2.1 + s.2.2 ≤ (n : ℝ)}
private theorem measurableSet_pairAggregateCutoff (n : ℕ) :
    MeasurableSet (pairAggregateCutoff n) := by
  apply measurableSet_le _ measurable_const
  exact (measurable_fst.add (measurable_fst.comp measurable_snd)).add
    (measurable_snd.comp measurable_snd)
theorem jointFemaleAggregate_mem_cutoff {μ ν : Matching n} {d : JointSpouseScores μ ν}
    (hd : JointSpouseThresholdsUnit d) (B : Finset (Fin n)) :
    jointFemaleAggregate d B ∈ pairAggregateCutoff n := by
  change (jointFemaleAggregate d B).1 + (jointFemaleAggregate d B).2.1 +
    (jointFemaleAggregate d B).2.2 ≤ (n : ℝ)
  rw [← jointFemale_sum_worse d B]
  calc
    _ ≤ ∑ _w : Fin n, (1 : ℝ) := Finset.sum_le_sum fun w _ ↦ max_le (hd.2 w).1.2 (hd.2 w).2.2
    _ = _ := by simp
private noncomputable def pairRadialUpperKernel (n u v : ℕ) : ℝ × ℝ × ℝ → ℝ≥0∞ :=
  (pairAggregateCutoff n).indicator (fun s ↦ ENNReal.ofReal (pairAggregateLaplace n u v s))
theorem measurable_pairRadialUpperKernel (n u v : ℕ) : Measurable (pairRadialUpperKernel n u v) :=
  (ENNReal.measurable_ofReal.comp (measurable_pairAggregateLaplace n u v)).indicator
    (measurableSet_pairAggregateCutoff n)
theorem continuousScoreLaw_twoStableOrientation_le_radial (μ ν : Matching n)
    (A B : Finset (Fin n)) {u v : ℕ}
    (hu : (pairOrientedMovedMen μ ν A).card = u)
    (hv : (pairOrientedMovedMen μ ν (Finset.univ \ A)).card = v)
    (hB : Fintype.card (PairFemaleGapClass μ ν B) = u)
    (hBc : Fintype.card (PairFemaleOtherGapClass μ ν B) = v)
    (hn : 0 < n) (hu₀ : 0 < u) (hv₀ : 0 < v) :
    continuousScoreLaw n (twoStableOrientationEvent μ ν A B) ≤ ENNReal.ofReal (Real.exp 72) *
      ∫⁻ ξ, ∫⁻ η, ∫⁻ ζ, pairRadialUpperKernel n u v (ξ, η, ζ)
        ∂spouseRadialLaw v ∂spouseRadialLaw u ∂spouseRadialLaw n := by
  let g := (pairAggregateCutoff n).indicator (1 : ℝ × ℝ × ℝ → ℝ≥0∞)
  have hg : Measurable g := measurable_const.indicator (measurableSet_pairAggregateCutoff n)
  let E := twoStableOrientationEvent μ ν A B
  let G := pairFemaleAggregateFromGaps (μ := μ) (ν := ν) B
  let F := pairRadialUpperKernel n u v
  have hF : Measurable F := measurable_pairRadialUpperKernel n u v
  have hpres : MeasurePreserving (fun x ↦ (splitTwoMatchingScores μ ν x).1)
      (continuousScoreLaw n) (jointSpouseScoreLaw μ ν) :=
    measurePreserving_fst.comp (measurePreserving_splitTwoMatchingScores μ ν)
  have hL : continuousScoreLaw n E =
      ∫⁻ x in E, g (jointFemaleAggregate (splitTwoMatchingScores μ ν x).1 B) ∂continuousScoreLaw n := by
    rw [← setLIntegral_one]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_of_ae (hpres.quasiMeasurePreserving.ae
      (ae_jointSpouseThresholdsUnit μ ν))] with x hx
    dsimp only [g]
    rw [Set.indicator_of_mem (jointFemaleAggregate_mem_cutoff hx B)]
    rfl
  have hmul (s : ℝ × ℝ × ℝ) :
      g s * ENNReal.ofReal (Real.exp 72 * pairAggregateLaplace n u v s) =
      ENNReal.ofReal (Real.exp 72) * F s := by
    by_cases hs : s ∈ pairAggregateCutoff n
    · simp only [g, F, pairRadialUpperKernel, Set.indicator_of_mem hs, Pi.one_apply,
        one_mul, ENNReal.ofReal_mul (Real.exp_pos _).le]
    · simp only [g, F, pairRadialUpperKernel, Set.indicator_of_notMem hs, zero_mul, mul_zero]
  rw [hL]
  have h := continuousScoreLaw_lintegral_twoStableOrientation_le_gapAggregate μ ν A B hg
  dsimp only at h
  rw [hu, hv] at h
  refine h.trans ?_
  simp_rw [hmul]
  have hmeas : Measurable (fun z ↦ F (G z)) :=
    hF.comp (measurable_pairFemaleAggregateFromGaps μ ν B)
  rw [lintegral_const_mul _ hmeas]
  apply mul_le_mul_right
  change (∫⁻ z, F (G z) ∂pairOrderedSpouseLaw n (PairMovedWoman μ ν)) ≤ _
  rw [← lintegral_map hF (measurable_pairFemaleAggregateFromGaps μ ν B),
    map_pairFemaleAggregateFromGaps]
  rw [lintegral_prod _ hF.aemeasurable]
  have h₀ := pairUniformSumLaw_le_spouseRadialLaw (Fin n) (by simpa using hn)
  have h₁ := pairUniformSumLaw_le_spouseRadialLaw (PairFemaleGapClass μ ν B) (hB ▸ hu₀)
  have h₂ := pairUniformSumLaw_le_spouseRadialLaw (PairFemaleOtherGapClass μ ν B) (hBc ▸ hv₀)
  rw [Fintype.card_fin] at h₀
  rw [hB] at h₁
  rw [hBc] at h₂
  refine lintegral_mono' h₀ fun ξ ↦ ?_
  have hξ : Measurable (fun t : ℝ × ℝ ↦ F (ξ, t)) :=
    hF.comp (measurable_const.prodMk measurable_id)
  rw [lintegral_prod _ hξ.aemeasurable]
  exact lintegral_mono' h₁ fun η ↦ lintegral_mono' h₂ le_rfl
private theorem pairMoved_iff_movedWoman (μ ν : Matching n) (m : Fin n) :
    μ m ≠ ν m ↔ μ.symm (μ m) ≠ ν.symm (μ m) := by
  constructor
  · intro hm h
    have he : ν m = μ m := by
      simpa only [μ.symm_apply_apply, ν.apply_symm_apply] using congrArg ν h
    exact hm he.symm
  · intro h he
    apply h
    simp only [μ.symm_apply_apply]
    rw [he, ν.symm_apply_apply]
private theorem pairCard_femaleGapClass (μ ν : Matching n) (A B : Finset (Fin n))
    (hAB : ∀ m, μ m ∈ B ↔ m ∈ A) :
    Fintype.card (PairFemaleGapClass μ ν B) = (pairOrientedMovedMen μ ν A).card := by
  let P (m : Fin n) := μ m ≠ ν m ∧ m ∈ A
  let Q (w : Fin n) := μ.symm w ≠ ν.symm w ∧ w ∈ B
  let e : Subtype P ≃ Subtype Q := μ.subtypeEquiv fun m ↦
    and_congr (pairMoved_iff_movedWoman μ ν m) (hAB m).symm
  let f : PairFemaleGapClass μ ν B ≃ Subtype Q :=
    Equiv.subtypeSubtypeEquivSubtypeInter _ _
  rw [Fintype.card_congr (f.trans e.symm), Fintype.card_subtype]
  congr 1
  ext m
  simp [pairOrientedMovedMen, and_comm]
private theorem pairCard_femaleOtherGapClass (μ ν : Matching n) (A B : Finset (Fin n))
    (hAB : ∀ m, μ m ∈ B ↔ m ∈ A) :
    Fintype.card (PairFemaleOtherGapClass μ ν B) =
      (pairOrientedMovedMen μ ν (Finset.univ \ A)).card := by
  let P (m : Fin n) := μ m ≠ ν m ∧ m ∉ A
  let Q (w : Fin n) := μ.symm w ≠ ν.symm w ∧ w ∉ B
  let e : Subtype P ≃ Subtype Q := μ.subtypeEquiv fun m ↦
    and_congr (pairMoved_iff_movedWoman μ ν m) (not_congr (hAB m).symm)
  let f : PairFemaleOtherGapClass μ ν B ≃ Subtype Q :=
    Equiv.subtypeSubtypeEquivSubtypeInter (fun w : Fin n ↦ μ.symm w ≠ ν.symm w)
      (fun w : Fin n ↦ w ∉ B)
  rw [Fintype.card_congr (f.trans e.symm), Fintype.card_subtype]
  congr 1
  ext m
  simp [pairOrientedMovedMen, and_comm]
theorem continuousScoreLaw_twoStableOrientation_image_le_radial (μ ν : Matching n)
    (A : Finset (Fin n)) {u v : ℕ}
    (hu : (pairOrientedMovedMen μ ν A).card = u)
    (hv : (pairOrientedMovedMen μ ν (Finset.univ \ A)).card = v)
    (hn : 0 < n) (hu₀ : 0 < u) (hv₀ : 0 < v) :
    continuousScoreLaw n (twoStableOrientationEvent μ ν A (A.image μ)) ≤
      ENNReal.ofReal (Real.exp 72) *
        ∫⁻ ξ, ∫⁻ η, ∫⁻ ζ, pairRadialUpperKernel n u v (ξ, η, ζ)
          ∂spouseRadialLaw v ∂spouseRadialLaw u ∂spouseRadialLaw n := by
  have hA (m : Fin n) : μ m ∈ A.image μ ↔ m ∈ A := by
    rw [Finset.mem_image]
    exact ⟨fun ⟨m', hm', h⟩ ↦ μ.injective h ▸ hm', fun hm ↦ ⟨m, hm, rfl⟩⟩
  exact continuousScoreLaw_twoStableOrientation_le_radial μ ν A (A.image μ) hu hv
    ((pairCard_femaleGapClass μ ν A _ hA).trans hu)
    ((pairCard_femaleOtherGapClass μ ν A _ hA).trans hv) hn hu₀ hv₀
theorem lintegral_pairRadialUpperKernel_eq_closed (n u v : ℕ) :
    (∫⁻ ξ, ∫⁻ η, ∫⁻ ζ, pairRadialUpperKernel n u v (ξ, η, ζ)
        ∂spouseRadialLaw v ∂spouseRadialLaw u ∂spouseRadialLaw n) =
      ∫⁻ ξ, ∫⁻ η, ∫⁻ ζ, if ξ + η + ζ ≤ (n : ℝ) then
        ENNReal.ofReal (((1 - Real.exp (-(ξ + η + ζ))) / (ξ + η + ζ)) ^ n *
          ((1 - Real.exp (-(ξ + ζ))) / (ξ + ζ)) ^ u *
          ((1 - Real.exp (-(ξ + η))) / (ξ + η)) ^ v) else 0
        ∂spouseRadialLaw v ∂spouseRadialLaw u ∂spouseRadialLaw n := by
  apply lintegral_congr_ae
  filter_upwards [ae_spouseRadialLaw_pos n] with ξ hξ
  apply lintegral_congr_ae
  filter_upwards [ae_spouseRadialLaw_pos u] with η hη
  apply lintegral_congr_ae
  filter_upwards [ae_spouseRadialLaw_pos v] with ζ hζ
  have h₀ : 0 < ξ + η + ζ := by positivity
  have h₁ : 0 < ξ + ζ := by positivity
  have h₂ : 0 < ξ + η := by positivity
  simp only [pairRadialUpperKernel, Set.indicator, pairAggregateCutoff, Set.mem_ofPred_eq,
    pairAggregateLaplace, pairLaplace_of_pos h₀, pairLaplace_of_pos h₁, pairLaplace_of_pos h₂]
theorem twoStableOrientation_of_male_class {μ ν : Matching n} {x : ScoreProfile n}
    (hμ : IsScoreStable x μ) (hν : IsScoreStable x ν)
    (hx : ∀ r, Function.Injective (x r)) (A : Finset (Fin n))
    (hA : ∀ m, μ m ≠ ν m → (m ∈ A ↔ x (.inl m) (μ m) < x (.inl m) (ν m))) :
    x ∈ twoStableOrientationEvent μ ν A (A.image μ) ∧ A.image μ = A.image ν := by
  have hMleft (m : Fin n) (hm : m ∈ A) :
      x (.inl m) (μ m) ≤ x (.inl m) (ν m) := by
    by_cases he : μ m = ν m
    · rw [he]
    · exact ((hA m he).mp hm).le
  have hMright (m : Fin n) (hm : m ∉ A) :
      x (.inl m) (ν m) ≤ x (.inl m) (μ m) := by
    by_cases he : μ m = ν m
    · rw [he]
    · exact le_of_not_gt fun h ↦ hm ((hA m he).mpr h)
  have hWright (m : Fin n) (hm : m ∈ A) :
      x (.inr (μ m)) (ν.symm (μ m)) ≤ x (.inr (μ m)) m := by
    by_cases he : μ m = ν m
    · rw [he, ν.symm_apply_apply]
    · exact le_of_not_gt fun h ↦
        hν m (μ m) ⟨Ne.symm he, (hA m he).mp hm, h⟩
  have hWleft (m : Fin n) (hm : m ∉ A) :
      x (.inr (ν m)) (μ.symm (ν m)) ≤ x (.inr (ν m)) m := by
    by_cases he : μ m = ν m
    · rw [← he, μ.symm_apply_apply]
    · have hlt : x (.inl m) (ν m) < x (.inl m) (μ m) :=
        lt_of_le_of_ne (hMright m hm) fun h ↦ he ((hx (.inl m) h).symm)
      exact le_of_not_gt fun h ↦ hμ m (ν m) ⟨he, hlt, h⟩
  have hsub : A.image μ ⊆ A.image ν := by
    intro w hw
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hw
    let j := ν.symm (μ m)
    have hj : ν j = μ m := ν.apply_symm_apply _
    refine Finset.mem_image.mpr ⟨j, ?_, hj⟩
    by_contra h
    have h₁ := hWright m hm
    have h₂ := hWleft j h
    rw [hj, μ.symm_apply_apply] at h₂
    have hmj : j = m := hx (.inr (μ m)) (le_antisymm h₁ h₂)
    exact h (hmj ▸ hm)
  have hImage : A.image μ = A.image ν := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [Finset.card_image_of_injective _ μ.injective, Finset.card_image_of_injective _ ν.injective]
  refine ⟨⟨hμ, hν, ?_⟩, hImage⟩
  constructor
  · intro m
    rw [jointManSpouseScoreLeft_split, jointManSpouseScoreRight_split]
    by_cases hm : m ∈ A
    · simpa only [if_pos hm] using hMleft m hm
    · simpa only [if_neg hm] using hMright m hm
  · intro w
    rw [jointWomanSpouseScoreLeft_split, jointWomanSpouseScoreRight_split]
    by_cases hw : w ∈ A.image μ
    · simp only [if_pos hw]
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hw
      simpa only [μ.symm_apply_apply] using hWright m hm
    · simp only [if_neg hw]
      let m := ν.symm w
      have hνm : ν m = w := ν.apply_symm_apply w
      have hm : m ∉ A := fun h ↦ hw (hImage ▸ Finset.mem_image.mpr ⟨m, h, hνm⟩)
      have h := hWleft m hm
      rwa [hνm] at h
end IncomparableLP
end

-- TwoStableBetaIntegral
section
open MeasureTheory Set
open scoped ENNReal
namespace IncomparableLP
private noncomputable def pairLaplaceClosed (x : ℝ) : ℝ :=
  (1 - Real.exp (-x)) / x
theorem measurable_pairLaplaceClosed : Measurable pairLaplaceClosed := by
  unfold pairLaplaceClosed
  fun_prop
private theorem pairLaplaceClosed_nonneg {x : ℝ} (hx : 0 < x) :
    0 ≤ pairLaplaceClosed x := by
  apply div_nonneg _ hx.le
  linarith [Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx.le)]
private theorem pairLaplaceClosed_le_one {x : ℝ} (hx : 0 < x) :
    pairLaplaceClosed x ≤ 1 := by
  apply (div_le_iff₀ hx).2
  linarith [Real.one_sub_le_exp_neg x]
private theorem pairLaplaceClosed_le_inv {x : ℝ} (hx : 0 < x) :
    pairLaplaceClosed x ≤ x⁻¹ := by
  rw [← one_div, pairLaplaceClosed]
  gcongr
  linarith [Real.exp_nonneg (-x)]
theorem lintegral_pairLaplaceClosed_le (n : ℕ) (hn : 1 ≤ n) :
    (∫⁻ x in Ioc (0 : ℝ) n, ENNReal.ofReal (pairLaplaceClosed x)) ≤
      ENNReal.ofReal (1 + Real.log n) := by
  have hn' : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr hn
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn'
  have hlow : (∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal (pairLaplaceClosed x)) ≤ 1 := by
    calc
      _ ≤ ∫⁻ _ in Ioc (0 : ℝ) 1, (1 : ℝ≥0∞) := by
        apply setLIntegral_mono' measurableSet_Ioc
        intro x hx
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (pairLaplaceClosed_le_one hx.1)
      _ = _ := by simp [Real.volume_Ioc]
  have hinv : IntegrableOn (fun x : ℝ ↦ x⁻¹) (Ioc 1 n) := by
    have hc : ContinuousOn (fun x : ℝ ↦ x⁻¹) (Icc 1 n) :=
      continuousOn_id.inv₀ fun x hx ↦ (zero_lt_one.trans_le hx.1).ne'
    exact hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hhigh : (∫⁻ x in Ioc (1 : ℝ) n, ENNReal.ofReal (pairLaplaceClosed x)) ≤
      ENNReal.ofReal (Real.log n) := by
    calc
      _ ≤ ∫⁻ x in Ioc (1 : ℝ) n, ENNReal.ofReal x⁻¹ := by
        exact setLIntegral_mono' measurableSet_Ioc fun x hx ↦
          ENNReal.ofReal_le_ofReal (pairLaplaceClosed_le_inv (zero_lt_one.trans hx.1))
      _ = ENNReal.ofReal (∫ x in Ioc (1 : ℝ) n, x⁻¹) := by
        symm
        exact ofReal_integral_eq_lintegral_ofReal hinv
          ((ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun x hx ↦
            inv_nonneg.mpr (zero_le_one.trans hx.1.le)))
      _ = _ := by
        rw [← intervalIntegral.integral_of_le hn', integral_inv_of_pos zero_lt_one
          (zero_lt_one.trans_le hn'), div_one]
  have hdisj : Disjoint (Ioc (0 : ℝ) 1) (Ioc 1 n) :=
    Set.disjoint_left.mpr fun _ h₁ h₂ ↦ (not_lt_of_ge h₁.2) h₂.1
  calc
    _ = (∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal (pairLaplaceClosed x)) +
          ∫⁻ x in Ioc (1 : ℝ) n, ENNReal.ofReal (pairLaplaceClosed x) := by
      rw [← Ioc_union_Ioc_eq_Ioc zero_le_one hn',
        lintegral_union measurableSet_Ioc hdisj]
    _ ≤ 1 + ENNReal.ofReal (Real.log n) := add_le_add hlow hhigh
    _ = _ := by rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one hlog]
private theorem intervalIntegral_beta_nat (i j : ℕ) :
    (∫ x in (0 : ℝ)..1, x ^ i * (1 - x) ^ j) =
      ((i.factorial : ℝ) * j.factorial) / (i + j + 1).factorial := by
  have hu : 0 < (((i : ℂ) + 1).re) := by simp; positivity
  have hv : 0 < (((j : ℂ) + 1).re) := by simp; positivity
  have hsum : ((i : ℂ) + 1) + ((j : ℂ) + 1) = ((i + j + 1 : ℕ) : ℂ) + 1 := by
    push_cast
    ring
  have hc := Complex.betaIntegral_eq_Gamma_mul_div ((i : ℂ) + 1) ((j : ℂ) + 1) hu hv
  rw [hsum] at hc
  simp only [Complex.Gamma_nat_eq_factorial, Complex.betaIntegral, add_sub_cancel_right,
    Complex.cpow_natCast] at hc
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  simpa only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_sub, Complex.ofReal_one,
    Complex.ofReal_div, Complex.ofReal_natCast] using hc
private noncomputable def pairBetaDensity (n k : ℕ) (s : ℝ) : ℝ :=
  s ^ (k - 1) * (1 - s) ^ (n - k - 1)
private theorem measurable_pairBetaDensity (n k : ℕ) : Measurable (pairBetaDensity n k) := by
  unfold pairBetaDensity
  fun_prop
theorem lintegral_pairBetaDensity (n k : ℕ) (hk : 0 < k) (hkn : k < n) :
    (∫⁻ s in Ioo (0 : ℝ) 1, ENNReal.ofReal (pairBetaDensity n k s)) =
      ENNReal.ofReal (pairSizeBetaFactor n k) := by
  have hi : IntegrableOn (pairBetaDensity n k) (Ioo 0 1) := by
    have hc : Continuous (pairBetaDensity n k) := by unfold pairBetaDensity; fun_prop
    exact hc.continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hi]
  · rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
    unfold pairBetaDensity pairSizeBetaFactor
    rw [intervalIntegral_beta_nat, show k - 1 + (n - k - 1) + 1 = n - 1 by omega]
  · exact (ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun s hs ↦
      mul_nonneg (pow_nonneg hs.1.le _) (pow_nonneg (sub_nonneg.mpr hs.2.le) _))
private theorem map_restrict_Ioo_div {x : ℝ} (hx : 0 < x) :
    (volume.restrict (Ioo (0 : ℝ) x)).map (x⁻¹ * ·) =
      ENNReal.ofReal x • volume.restrict (Ioo (0 : ℝ) 1) := by
  have hpre : (x⁻¹ * ·) ⁻¹' Ioo (0 : ℝ) 1 = Ioo (0 : ℝ) x := by
    ext y
    change (0 < x⁻¹ * y ∧ x⁻¹ * y < 1) ↔ 0 < y ∧ y < x
    rw [← div_eq_inv_mul, div_lt_one hx]
    have hpos : 0 < y / x ↔ 0 < y := by
      rw [lt_div_iff₀ hx, zero_mul]
    rw [hpos]
  calc
    _ = ((volume : Measure ℝ).map (x⁻¹ * ·)).restrict (Ioo (0 : ℝ) 1) := by
      rw [Measure.restrict_map (measurable_const_mul _) measurableSet_Ioo, hpre]
    _ = _ := by
      rw [Real.map_volume_mul_left (inv_ne_zero hx.ne'), inv_inv, abs_of_pos hx,
        Measure.restrict_smul]
private noncomputable def pairBetaDilation (n k : ℕ) (x : ℝ) : ℝ → ℝ≥0∞ :=
  (Ioo 0 x).indicator (fun y ↦ ENNReal.ofReal (x⁻¹ * pairBetaDensity n k (x⁻¹ * y)))
private theorem measurable_pairBetaDilation (n k : ℕ) (x : ℝ) :
    Measurable (pairBetaDilation n k x) := by
  unfold pairBetaDilation
  refine Measurable.indicator ?_ measurableSet_Ioo
  unfold pairBetaDensity
  fun_prop
private theorem lintegral_pairBetaDilation {n k : ℕ} (hk : 0 < k) (hkn : k < n)
    {x : ℝ} (hx : 0 < x) :
    (∫⁻ y, pairBetaDilation n k x y) = ENNReal.ofReal (pairSizeBetaFactor n k) := by
  have hf : Measurable (fun s ↦ ENNReal.ofReal (pairBetaDensity n k s)) :=
    (measurable_pairBetaDensity n k).ennreal_ofReal
  have hcomp : Measurable (fun y ↦ ENNReal.ofReal (pairBetaDensity n k (x⁻¹ * y))) :=
    hf.comp (measurable_const_mul _)
  rw [pairBetaDilation, lintegral_indicator measurableSet_Ioo]
  simp_rw [ENNReal.ofReal_mul (inv_nonneg.mpr hx.le)]
  rw [lintegral_const_mul _ hcomp]
  rw [← lintegral_map hf (measurable_const_mul x⁻¹), map_restrict_Ioo_div hx,
    lintegral_smul_measure, smul_eq_mul, ← mul_assoc,
    ← ENNReal.ofReal_mul (inv_nonneg.mpr hx.le), inv_mul_cancel₀ hx.ne', ENNReal.ofReal_one,
    one_mul, lintegral_pairBetaDensity n k hk hkn]
private theorem lintegral_rotate_triple {F : ℝ × ℝ × ℝ → ℝ≥0∞} (hF : Measurable F)
    (μ ν ρ : Measure ℝ) [SFinite μ] [SFinite ν] [SFinite ρ] :
    (∫⁻ y, ∫⁻ z, ∫⁻ x, F (x, y, z) ∂μ ∂ρ ∂ν) =
      ∫⁻ x, ∫⁻ y, ∫⁻ z, F (x, y, z) ∂ρ ∂ν ∂μ := by
  have hpair : Measurable (fun q : (ℝ × ℝ) × ℝ ↦ F (q.2, q.1)) :=
    hF.comp (measurable_snd.prodMk measurable_fst)
  have hinner : Measurable (fun q : ℝ × ℝ ↦ ∫⁻ x, F (x, q) ∂μ) :=
    hpair.lintegral_prod_right'
  calc
    _ = ∫⁻ q : ℝ × ℝ, (∫⁻ x, F (x, q) ∂μ) ∂ν.prod ρ :=
      (lintegral_prod _ hinner.aemeasurable).symm
    _ = ∫⁻ x, ∫⁻ q : ℝ × ℝ, F (x, q) ∂ν.prod ρ ∂μ :=
      lintegral_lintegral_swap hpair.aemeasurable
    _ = _ := by
      refine lintegral_congr fun x ↦ lintegral_prod _ ?_
      exact (hF.comp (measurable_const.prodMk measurable_id)).aemeasurable
private theorem lintegral_translate_triple {F : ℝ × ℝ × ℝ → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ y : ℝ, ∫⁻ z : ℝ, ∫⁻ w : ℝ, F (w + (y + z), y, z)) =
      ∫⁻ x : ℝ, ∫⁻ y : ℝ, ∫⁻ z : ℝ, F (x, y, z) := by
  rw [← lintegral_rotate_triple hF volume volume volume]
  refine lintegral_congr fun y ↦ lintegral_congr fun z ↦ ?_
  exact lintegral_add_right_eq_self (fun x : ℝ ↦ F (x, y, z)) (y + z)
private noncomputable def twoStableClosedLaplaceAggregateKernel (n u v : ℕ) (w y z : ℝ) : ℝ :=
  pairLaplaceClosed (w + (y + z)) ^ n * pairLaplaceClosed (w + z) ^ u *
    pairLaplaceClosed (w + y) ^ v * (w ^ (n - 1) * y ^ (u - 1) * z ^ (v - 1))
private theorem scaled_pairBetaDensity_eq {n k : ℕ} (hk : 0 < k) (hkn : k < n)
    {x : ℝ} (hx : 0 < x) (y : ℝ) :
    x⁻¹ * pairBetaDensity n k (x⁻¹ * y) =
      y ^ (k - 1) * (x - y) ^ (n - k - 1) / x ^ (n - 1) := by
  have hdiv : 1 - x⁻¹ * y = (x - y) / x := by
    rw [← div_eq_inv_mul, sub_div, div_self hx.ne']
  unfold pairBetaDensity
  rw [hdiv, mul_pow, inv_pow, div_pow]
  calc
    _ = y ^ (k - 1) * (x - y) ^ (n - k - 1) / (x * (x ^ (k - 1) * x ^ (n - k - 1))) := by
      field_simp
    _ = _ := by
      rw [← pow_add, ← pow_succ', show k - 1 + (n - k - 1) + 1 = n - 1 by omega]
private theorem twoStableClosedLaplaceAggregateKernel_le_beta {n u v : ℕ}
    (h : ValidPairSizes n (u, v)) {x y z : ℝ} (hy : 0 < y) (hz : 0 < z)
    (hxyz : y + z < x) :
    twoStableClosedLaplaceAggregateKernel n u v (x - (y + z)) y z ≤
      pairLaplaceClosed x * (x⁻¹ * pairBetaDensity n u (x⁻¹ * y)) *
        (x⁻¹ * pairBetaDensity n v (x⁻¹ * z)) := by
  obtain ⟨hu, hv, huv⟩ := h
  have hup : 0 < u := by omega
  have hvp : 0 < v := by omega
  have hun : u < n := by omega
  have hvn : v < n := by omega
  have hn : 1 ≤ n := by omega
  have hx : 0 < x := by linarith
  have hxy : 0 < x - y := by linarith
  have hxz : 0 < x - z := by linarith
  have htriangle : 0 ≤ x - (y + z) := (sub_pos.mpr hxyz).le
  have htriangle' : x - (y + z) ≤ (x - y) * (x - z) / x := by
    apply (le_div_iff₀ hx).2
    nlinarith only [mul_nonneg hy.le hz.le]
  have hφ := pairLaplaceClosed_nonneg hx
  have hφyn := pairLaplaceClosed_nonneg hxy
  have hφzn := pairLaplaceClosed_nonneg hxz
  have hφx : pairLaplaceClosed x ^ n ≤ pairLaplaceClosed x * x⁻¹ ^ (n - 1) := calc
    _ = pairLaplaceClosed x * pairLaplaceClosed x ^ (n - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hn]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hφ (pairLaplaceClosed_le_inv hx) _) hφ
  have hφy := pow_le_pow_left₀ hφyn (pairLaplaceClosed_le_inv hxy) u
  have hφz := pow_le_pow_left₀ hφzn (pairLaplaceClosed_le_inv hxz) v
  have hβu : (x - y) ^ (n - 1) = (x - y) ^ u * (x - y) ^ (n - u - 1) := by
    rw [← pow_add, show u + (n - u - 1) = n - 1 by omega]
  have hβv : (x - z) ^ (n - 1) = (x - z) ^ v * (x - z) ^ (n - v - 1) := by
    rw [← pow_add, show v + (n - v - 1) = n - 1 by omega]
  unfold twoStableClosedLaplaceAggregateKernel
  rw [sub_add_cancel, show x - (y + z) + z = x - y by ring,
    show x - (y + z) + y = x - z by ring]
  calc
    _ ≤ (pairLaplaceClosed x * x⁻¹ ^ (n - 1) * (x - y)⁻¹ ^ u * (x - z)⁻¹ ^ v) *
          ((x - (y + z)) ^ (n - 1) * y ^ (u - 1) * z ^ (v - 1)) := by
      gcongr
    _ ≤ (pairLaplaceClosed x * x⁻¹ ^ (n - 1) * (x - y)⁻¹ ^ u * (x - z)⁻¹ ^ v) *
          (((x - y) * (x - z) / x) ^ (n - 1) * y ^ (u - 1) * z ^ (v - 1)) := by
      gcongr
    _ = _ := by
      rw [scaled_pairBetaDensity_eq hup hun hx, scaled_pairBetaDensity_eq hvp hvn hx,
        div_pow, mul_pow, hβu, hβv]
      simp only [inv_pow]
      field_simp
private def translatedPairDomain (N : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {p | 0 < p.2.1 ∧ 0 < p.2.2 ∧ p.2.1 + p.2.2 < p.1 ∧ p.1 ≤ N}
private theorem measurableSet_translatedPairDomain (N : ℝ) :
    MeasurableSet (translatedPairDomain N) := by
  have hy : Measurable (fun p : ℝ × ℝ × ℝ ↦ p.2.1) := by fun_prop
  have hz : Measurable (fun p : ℝ × ℝ × ℝ ↦ p.2.2) := by fun_prop
  exact (measurableSet_lt measurable_const hy).inter
    ((measurableSet_lt measurable_const hz).inter
      ((measurableSet_lt (hy.add hz) measurable_fst).inter
        (measurableSet_le measurable_fst measurable_const)))
private noncomputable def translatedPairKernel (n u v : ℕ) : ℝ × ℝ × ℝ → ℝ≥0∞ :=
  (translatedPairDomain n).indicator fun p ↦ ENNReal.ofReal
    (twoStableClosedLaplaceAggregateKernel n u v (p.1 - (p.2.1 + p.2.2)) p.2.1 p.2.2)
private theorem measurable_translatedPairKernel (n u v : ℕ) :
    Measurable (translatedPairKernel n u v) := by
  unfold translatedPairKernel twoStableClosedLaplaceAggregateKernel
  refine Measurable.indicator ?_ (measurableSet_translatedPairDomain n)
  unfold pairLaplaceClosed
  fun_prop
private theorem translatedPairKernel_eval (n u v : ℕ) (w y z : ℝ) :
    translatedPairKernel n u v (w + (y + z), y, z) =
      if 0 < y ∧ 0 < z ∧ 0 < w ∧ w + (y + z) ≤ n then
        ENNReal.ofReal (twoStableClosedLaplaceAggregateKernel n u v w y z) else 0 := by
  have htri : y + z < w + (y + z) ↔ 0 < w := by
    constructor <;> intro hh <;> linarith
  simp [translatedPairKernel, translatedPairDomain, indicator_apply, htri]
private theorem lintegral_closedLaplace_eq_translated (n u v : ℕ) :
    (∫⁻ y in Ioi (0 : ℝ), ∫⁻ z in Ioi (0 : ℝ), ∫⁻ w in Ioi (0 : ℝ),
      if w + (y + z) ≤ n then
        ENNReal.ofReal (twoStableClosedLaplaceAggregateKernel n u v w y z) else 0) =
      ∫⁻ x : ℝ, ∫⁻ y : ℝ, ∫⁻ z : ℝ, translatedPairKernel n u v (x, y, z) := by
  rw [← lintegral_translate_triple (measurable_translatedPairKernel n u v)]
  simp_rw [← lintegral_indicator measurableSet_Ioi, indicator_apply, mem_Ioi,
    translatedPairKernel_eval]
  refine lintegral_congr fun y ↦ ?_
  by_cases hy : 0 < y
  · simp only [hy, ite_true, true_and]
    refine lintegral_congr fun z ↦ ?_
    by_cases hz : 0 < z
    · simp only [hz, ite_true, true_and]
      refine lintegral_congr fun w ↦ ?_
      by_cases hw : 0 < w <;> simp [hw]
    · simp [hz]
  · simp [hy]
private noncomputable def pairRadialFactor (n : ℕ) : ℝ → ℝ≥0∞ :=
  (Ioc (0 : ℝ) n).indicator (fun x ↦ ENNReal.ofReal (pairLaplaceClosed x))
private theorem measurable_pairRadialFactor (n : ℕ) : Measurable (pairRadialFactor n) :=
  measurable_pairLaplaceClosed.ennreal_ofReal.indicator measurableSet_Ioc
private theorem translatedPairKernel_le {n u v : ℕ} (h : ValidPairSizes n (u, v))
    (x y z : ℝ) :
    translatedPairKernel n u v (x, y, z) ≤
      (pairRadialFactor n x * pairBetaDilation n u x y) * pairBetaDilation n v x z := by
  by_cases hp : (x, y, z) ∈ translatedPairDomain n
  · have hp' := hp
    obtain ⟨hy, hz, htri, hn⟩ := hp'
    change 0 < y at hy
    change 0 < z at hz
    change y + z < x at htri
    have hx : 0 < x := by linarith
    have hyx : 0 < x - y := by linarith
    have hxD : x ∈ Ioc (0 : ℝ) n := ⟨hx, hn⟩
    have hyD : y ∈ Ioo 0 x := ⟨hy, by linarith⟩
    have hzD : z ∈ Ioo 0 x := ⟨hz, by linarith⟩
    have hφ := pairLaplaceClosed_nonneg hx
    have hβ : 0 ≤ x⁻¹ * pairBetaDensity n u (x⁻¹ * y) := by
      rw [scaled_pairBetaDensity_eq
        (show 0 < u by obtain ⟨hu, hv, huv⟩ := h; omega)
        (show u < n by obtain ⟨hu, hv, huv⟩ := h; omega) hx]
      positivity
    rw [translatedPairKernel, indicator_of_mem hp, pairRadialFactor, indicator_of_mem hxD,
      pairBetaDilation, pairBetaDilation, indicator_of_mem hyD, indicator_of_mem hzD,
      ← ENNReal.ofReal_mul hφ, ← ENNReal.ofReal_mul (mul_nonneg hφ hβ)]
    exact ENNReal.ofReal_le_ofReal
      (twoStableClosedLaplaceAggregateKernel_le_beta h hy hz htri)
  · rw [translatedPairKernel, indicator_of_notMem hp]
    exact zero_le
private theorem lintegral_pairRadialDilation {n u v : ℕ} (h : ValidPairSizes n (u, v)) :
    (∫⁻ x : ℝ, ∫⁻ y : ℝ, ∫⁻ z : ℝ,
      (pairRadialFactor n x * pairBetaDilation n u x y) * pairBetaDilation n v x z) =
    (∫⁻ x in Ioc (0 : ℝ) n, ENNReal.ofReal (pairLaplaceClosed x)) *
      ENNReal.ofReal (pairSizeBetaFactor n u) * ENNReal.ofReal (pairSizeBetaFactor n v) := by
  obtain ⟨hu, hv, huv⟩ := h
  have hup : 0 < u := by omega
  have hvp : 0 < v := by omega
  have hun : u < n := by omega
  have hvn : v < n := by omega
  have houter (x : ℝ) :
      (∫⁻ y : ℝ, ∫⁻ z : ℝ,
        (pairRadialFactor n x * pairBetaDilation n u x y) * pairBetaDilation n v x z) =
      pairRadialFactor n x * ENNReal.ofReal (pairSizeBetaFactor n u) *
        ENNReal.ofReal (pairSizeBetaFactor n v) := by
    by_cases hx : x ∈ Ioc (0 : ℝ) n
    · have hm : Measurable (fun y ↦ pairRadialFactor n x * pairBetaDilation n u x y) :=
        measurable_const.mul (measurable_pairBetaDilation n u x)
      simp_rw [lintegral_const_mul _ (measurable_pairBetaDilation n v x),
        lintegral_pairBetaDilation hvp hvn hx.1]
      rw [lintegral_mul_const _ hm, lintegral_const_mul _ (measurable_pairBetaDilation n u x),
        lintegral_pairBetaDilation hup hun hx.1]
    · have hz : pairRadialFactor n x = 0 := indicator_of_notMem hx _
      simp [hz]
  simp_rw [houter]
  rw [lintegral_mul_const _ ((measurable_pairRadialFactor n).mul_const _),
    lintegral_mul_const _ (measurable_pairRadialFactor n), pairRadialFactor,
    lintegral_indicator measurableSet_Ioc]
theorem lintegral_twoStableClosedLaplaceAggregate_le {n u v : ℕ}
    (h : ValidPairSizes n (u, v)) :
    (∫⁻ y in Ioi (0 : ℝ), ∫⁻ z in Ioi (0 : ℝ), ∫⁻ w in Ioi (0 : ℝ),
      if w + (y + z) ≤ n then
        ENNReal.ofReal (twoStableClosedLaplaceAggregateKernel n u v w y z) else 0) ≤
      ENNReal.ofReal ((1 + Real.log n) * pairSizeBetaFactor n u * pairSizeBetaFactor n v) := by
  have hn : 1 ≤ n := by obtain ⟨hu, hv, huv⟩ := h; omega
  have hlog : 0 ≤ 1 + Real.log (n : ℝ) :=
    add_nonneg zero_le_one (Real.log_nonneg (Nat.one_le_cast.mpr hn))
  have hbu : 0 ≤ pairSizeBetaFactor n u := by unfold pairSizeBetaFactor; positivity
  rw [lintegral_closedLaplace_eq_translated]
  calc
    _ ≤ ∫⁻ x : ℝ, ∫⁻ y : ℝ, ∫⁻ z : ℝ,
          (pairRadialFactor n x * pairBetaDilation n u x y) * pairBetaDilation n v x z :=
      lintegral_mono fun x ↦ lintegral_mono fun y ↦ lintegral_mono (translatedPairKernel_le h x y)
    _ = _ := lintegral_pairRadialDilation h
    _ ≤ (ENNReal.ofReal (1 + Real.log n) * ENNReal.ofReal (pairSizeBetaFactor n u)) *
          ENNReal.ofReal (pairSizeBetaFactor n v) := by
      gcongr
      exact lintegral_pairLaplaceClosed_le n hn
    _ = _ := by rw [← ENNReal.ofReal_mul hlog, ← ENNReal.ofReal_mul (mul_nonneg hlog hbu)]
private theorem lintegral_triple_prod {F : ℝ × ℝ × ℝ → ℝ≥0∞} (hF : Measurable F)
    (μ ν ρ : Measure ℝ) [SFinite ν] [SFinite ρ] :
    (∫⁻ p, F p ∂μ.prod (ν.prod ρ)) =
      ∫⁻ x, ∫⁻ y, ∫⁻ z, F (x, y, z) ∂ρ ∂ν ∂μ := by
  rw [lintegral_prod _ hF.aemeasurable]
  refine lintegral_congr fun x ↦ lintegral_prod _ ?_
  exact (hF.comp (measurable_const.prodMk measurable_id)).aemeasurable
theorem lintegral_twoStableClosedLaplaceRadial_le {n u v : ℕ}
    (h : ValidPairSizes n (u, v)) :
    (∫⁻ w, ∫⁻ y, ∫⁻ z, (if w + y + z ≤ n then ENNReal.ofReal
        (pairLaplaceClosed (w + y + z) ^ n * pairLaplaceClosed (w + z) ^ u *
          pairLaplaceClosed (w + y) ^ v) else 0)
        ∂spouseRadialLaw v ∂spouseRadialLaw u ∂spouseRadialLaw n) ≤
      ENNReal.ofReal ((1 + Real.log n) * pairSizeBetaFactor n u * pairSizeBetaFactor n v /
        ((↑(n - 1).factorial : ℝ) * ↑(u - 1).factorial * ↑(v - 1).factorial)) := by
  let R := (volume : Measure ℝ).restrict (Ioi (0 : ℝ))
  let F (p : ℝ × ℝ × ℝ) : ℝ≥0∞ :=
    if p.1 + p.2.1 + p.2.2 ≤ n then ENNReal.ofReal
      (pairLaplaceClosed (p.1 + p.2.1 + p.2.2) ^ n * pairLaplaceClosed (p.1 + p.2.2) ^ u *
        pairLaplaceClosed (p.1 + p.2.1) ^ v) else 0
  let G (p : ℝ × ℝ × ℝ) : ℝ≥0∞ :=
    if p.1 + (p.2.1 + p.2.2) ≤ n then ENNReal.ofReal
      (twoStableClosedLaplaceAggregateKernel n u v p.1 p.2.1 p.2.2) else 0
  let D (k : ℕ) (s : ℝ) : ℝ := s ^ (k - 1) / ↑(k - 1).factorial
  let ρ (k : ℕ) (s : ℝ) : ℝ≥0∞ := ENNReal.ofReal (D k s)
  let H (p : ℝ × ℝ × ℝ) : ℝ≥0∞ := ρ n p.1 * (ρ u p.2.1 * ρ v p.2.2)
  let C : ℝ := ((↑(n - 1).factorial : ℝ) * ↑(u - 1).factorial * ↑(v - 1).factorial)⁻¹
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hF : Measurable F := by
    dsimp [F]
    refine Measurable.ite (measurableSet_le (by fun_prop) measurable_const) ?_ measurable_const
    unfold pairLaplaceClosed
    fun_prop
  have hG : Measurable G := by
    dsimp [G]
    refine Measurable.ite (measurableSet_le (by fun_prop) measurable_const) ?_ measurable_const
    unfold twoStableClosedLaplaceAggregateKernel pairLaplaceClosed
    fun_prop
  have hρ (k : ℕ) : Measurable (ρ k) := by
    dsimp [ρ, D]
    fun_prop
  have hH : Measurable H :=
    ((hρ n).comp measurable_fst).mul
      (((hρ u).comp (measurable_fst.comp measurable_snd)).mul
        ((hρ v).comp (measurable_snd.comp measurable_snd)))
  have hmeasure :
      (spouseRadialLaw n).prod ((spouseRadialLaw u).prod (spouseRadialLaw v)) =
        (R.prod (R.prod R)).withDensity H := by
    change (R.withDensity (ρ n)).prod ((R.withDensity (ρ u)).prod (R.withDensity (ρ v))) = _
    have hinner : Measurable (fun p : ℝ × ℝ ↦ ρ u p.1 * ρ v p.2) :=
      ((hρ u).comp measurable_fst).mul ((hρ v).comp measurable_snd)
    rw [prod_withDensity (hρ u) (hρ v), prod_withDensity (hρ n) hinner]
  have hpoint (w y z : ℝ) (hw : 0 < w) (hy : 0 < y) (hz : 0 < z) :
      (H * F) (w, y, z) = ENNReal.ofReal C * G (w, y, z) := by
    by_cases hcut : w + (y + z) ≤ n
    · have hcut' : w + y + z ≤ n := by simpa only [add_assoc] using hcut
      let P := pairLaplaceClosed (w + y + z) ^ n * pairLaplaceClosed (w + z) ^ u *
        pairLaplaceClosed (w + y) ^ v
      have hwn : 0 ≤ D n w := by dsimp [D]; positivity
      have hyn : 0 ≤ D u y := by dsimp [D]; positivity
      have hzn : 0 ≤ D v z := by dsimp [D]; positivity
      simp only [Pi.mul_apply, H, F, G, hcut, hcut', ite_true]
      change (ENNReal.ofReal (D n w) * (ENNReal.ofReal (D u y) * ENNReal.ofReal (D v z))) *
          ENNReal.ofReal P = ENNReal.ofReal C *
            ENNReal.ofReal (twoStableClosedLaplaceAggregateKernel n u v w y z)
      rw [← ENNReal.ofReal_mul hyn, ← ENNReal.ofReal_mul hwn,
        ← ENNReal.ofReal_mul (mul_nonneg hwn (mul_nonneg hyn hzn)), ← ENNReal.ofReal_mul hC]
      congr 1
      dsimp [D, C, P, twoStableClosedLaplaceAggregateKernel]
      rw [add_assoc]
      ring
    · have hcut' : ¬w + y + z ≤ n := by simpa only [add_assoc] using hcut
      simp [F, G, hcut, hcut']
  change (∫⁻ w, ∫⁻ y, ∫⁻ z, F (w, y, z) ∂spouseRadialLaw v ∂spouseRadialLaw u
    ∂spouseRadialLaw n) ≤ _
  calc
    _ = ∫⁻ p, F p ∂(spouseRadialLaw n).prod ((spouseRadialLaw u).prod (spouseRadialLaw v)) :=
      (lintegral_triple_prod hF _ _ _).symm
    _ = ∫⁻ p, (H * F) p ∂ R.prod (R.prod R) := by
      rw [hmeasure, lintegral_withDensity_eq_lintegral_mul _ hH hF]
    _ = ∫⁻ w, ∫⁻ y, ∫⁻ z, (H * F) (w, y, z) ∂ R ∂ R ∂ R := by
      exact lintegral_triple_prod (hH.mul hF) R R R
    _ = ∫⁻ w, ∫⁻ y, ∫⁻ z, ENNReal.ofReal C * G (w, y, z) ∂ R ∂ R ∂ R := by
      refine setLIntegral_congr_fun measurableSet_Ioi fun w hw ↦ ?_
      refine setLIntegral_congr_fun measurableSet_Ioi fun y hy ↦ ?_
      exact setLIntegral_congr_fun measurableSet_Ioi fun z hz ↦ hpoint w y z hw hy hz
    _ = ENNReal.ofReal C * (∫⁻ w, ∫⁻ y, ∫⁻ z, G (w, y, z) ∂ R ∂ R ∂ R) := by
      simp_rw [lintegral_const_mul' (ENNReal.ofReal C) _ ENNReal.ofReal_ne_top]
    _ = ENNReal.ofReal C * (∫⁻ y, ∫⁻ z, ∫⁻ w, G (w, y, z) ∂ R ∂ R ∂ R) := by
      rw [lintegral_rotate_triple hG R R R]
    _ ≤ ENNReal.ofReal C *
        ENNReal.ofReal ((1 + Real.log n) * pairSizeBetaFactor n u * pairSizeBetaFactor n v) := by
      gcongr
      exact lintegral_twoStableClosedLaplaceAggregate_le h
    _ = _ := by rw [← ENNReal.ofReal_mul hC, div_eq_inv_mul]
end IncomparableLP
end

-- TwoStableOrientationCounting
section
open Equiv Equiv.Perm Finset StableMarriage
open scoped BigOperators ENNReal
namespace IncomparableLP
variable {n : ℕ}
private structure LabeledPairOrientation (μ ν : Matching n) (U V : Finset (Fin n)) : Prop where
  disjoint : Disjoint U V
  union_support : U ∪ V = (relativeMenPermutation μ ν).support
  preserves_left : ∀ i, relativeMenPermutation μ ν i ∈ U ↔ i ∈ U
  preserves_right : ∀ i, relativeMenPermutation μ ν i ∈ V ↔ i ∈ V
namespace LabeledPairOrientation
variable {μ ν : Matching n} {U V : Finset (Fin n)}
private def leftPerm (h : LabeledPairOrientation μ ν U V) : Perm U :=
  (relativeMenPermutation μ ν).subtypePerm h.preserves_left
private def rightPerm (h : LabeledPairOrientation μ ν U V) : Perm V :=
  (relativeMenPermutation μ ν).subtypePerm h.preserves_right
theorem leftPerm_apply_ne (h : LabeledPairOrientation μ ν U V) (i : U) :
    h.leftPerm i ≠ i := by
  intro he
  apply mem_support.mp (h.union_support ▸ mem_union_left V i.property)
  exact congrArg Subtype.val he
theorem rightPerm_apply_ne (h : LabeledPairOrientation μ ν U V) (i : V) :
    h.rightPerm i ≠ i := by
  intro he
  apply mem_support.mp (h.union_support ▸ mem_union_right U i.property)
  exact congrArg Subtype.val he
end LabeledPairOrientation
private abbrev OrientationSideChoices (n u v : ℕ) :=
  Σ U : ↥((univ : Finset (Fin n)).powersetCard u), ↥(U.valᶜ.powersetCard v)
theorem card_orientationSideChoices (n u v : ℕ) :
    Nat.card (OrientationSideChoices n u v) = n.choose u * (n - u).choose v := by
  rw [Nat.card_sigma]
  have hcard (U : ↥((univ : Finset (Fin n)).powersetCard u)) : U.val.card = u :=
    (mem_powersetCard.mp U.property).2
  simp only [Nat.card_eq_finsetCard, card_powersetCard, card_compl, Fintype.card_fin, hcard,
    sum_const, nsmul_eq_mul, card_univ, Fintype.card_coe]
  rfl
private abbrev RestrictedOrientationPerm (k : ℕ) (P : Multiset ℕ → Prop) :=
  {f : Perm (Fin k) // (∀ i, f i ≠ i) ∧ P f.cycleType}
private abbrev LabeledOrientationPairs (n u v : ℕ) (P Q : Multiset ℕ → Prop) :=
  {z : (Matching n × Matching n) × (Finset (Fin n) × Finset (Fin n)) //
    ∃ h : LabeledPairOrientation z.1.1 z.1.2 z.2.1 z.2.2,
      z.2.1.card = u ∧ z.2.2.card = v ∧ P h.leftPerm.cycleType ∧ Q h.rightPerm.cycleType}
private noncomputable def relabelOrientationSide {k : ℕ} {S : Finset (Fin n)}
    (hS : S.card = k) : Fin k ≃ S :=
  Fintype.equivOfCardEq (by simp [hS])
private theorem cycleType_ofSubtype_finset {S : Finset (Fin n)} (p : Perm S) :
    p.ofSubtype.cycleType = p.cycleType :=
  cycleType_ofSubtype (g := p)
private theorem relabelSide_cycleType {k : ℕ} {S : Finset (Fin n)}
    (e : Fin k ≃ S) (p : Perm S) : (e.permCongr.symm p).cycleType = p.cycleType := by
  rw [← cycleType_extendDomain e]
  change (ofSubtype (e.permCongr (e.permCongr.symm p))).cycleType = _
  rw [e.permCongr.apply_symm_apply, cycleType_ofSubtype_finset]
private theorem relabelSide_apply_ne {k : ℕ} {S : Finset (Fin n)}
    (e : Fin k ≃ S) {p : Perm S} (hp : ∀ i, p i ≠ i) (j : Fin k) :
    e.permCongr.symm p j ≠ j := by
  intro he
  apply hp (e j)
  simpa only [Equiv.permCongr_symm_apply, Equiv.apply_symm_apply] using congrArg e he
private noncomputable def labeledOrientationPairsEmbedding (n u v : ℕ) (P Q : Multiset ℕ → Prop) :
    LabeledOrientationPairs n u v P Q ↪
      Matching n × OrientationSideChoices n u v ×
        RestrictedOrientationPerm u P × RestrictedOrientationPerm v Q := by
  let encode (z : LabeledOrientationPairs n u v P Q) :
      Matching n × OrientationSideChoices n u v ×
        RestrictedOrientationPerm u P × RestrictedOrientationPerm v Q := by
    let h := z.property.choose
    have hU := z.property.choose_spec.1
    have hV := z.property.choose_spec.2.1
    have hP := z.property.choose_spec.2.2.1
    have hQ := z.property.choose_spec.2.2.2
    let eU := relabelOrientationSide hU
    let eV := relabelOrientationSide hV
    exact ⟨z.val.1.1, ⟨⟨z.val.2.1, mem_powersetCard.mpr ⟨subset_univ _, hU⟩⟩,
      ⟨z.val.2.2, mem_powersetCard.mpr
        ⟨fun _ hi ↦ mem_compl.mpr fun hU' ↦ disjoint_left.mp h.disjoint hU' hi, hV⟩⟩⟩,
      ⟨eU.permCongr.symm h.leftPerm, relabelSide_apply_ne eU h.leftPerm_apply_ne,
        (relabelSide_cycleType eU h.leftPerm).symm ▸ hP⟩,
      ⟨eV.permCongr.symm h.rightPerm, relabelSide_apply_ne eV h.rightPerm_apply_ne,
        (relabelSide_cycleType eV h.rightPerm).symm ▸ hQ⟩⟩
  refine ⟨encode, ?_⟩
  rintro ⟨⟨⟨μ, ν⟩, U, V⟩, hz⟩ ⟨⟨⟨μ', ν'⟩, U', V'⟩, hw⟩ he
  have hμ : μ = μ' := congrArg (fun z ↦ z.1) he
  have hU : U = U' := congrArg (fun z ↦ z.2.1.1.val) he
  have hV : V = V' := congrArg (fun z ↦ z.2.1.2.val) he
  subst μ' U' V'
  have hleft : hz.choose.leftPerm = hw.choose.leftPerm := by
    have hp := congrArg (fun z ↦ z.2.2.1.val) he
    exact (relabelOrientationSide hz.choose_spec.1).permCongr.symm.injective hp
  have hright : hz.choose.rightPerm = hw.choose.rightPerm := by
    have hp := congrArg (fun z ↦ z.2.2.2.val) he
    exact (relabelOrientationSide hz.choose_spec.2.1).permCongr.symm.injective hp
  have hrel : relativeMenPermutation μ ν = relativeMenPermutation μ ν' := by
    apply Equiv.ext
    intro i
    by_cases hiU : i ∈ U
    · exact congrArg (fun f : Perm U ↦ (f ⟨i, hiU⟩).val) hleft
    by_cases hiV : i ∈ V
    · exact congrArg (fun f : Perm V ↦ (f ⟨i, hiV⟩).val) hright
    have hi : i ∉ U ∪ V := fun h ↦ (mem_union.mp h).elim hiU hiV
    exact (notMem_support.mp (hz.choose.union_support ▸ hi)).trans
      (notMem_support.mp (hw.choose.union_support ▸ hi)).symm
  have hνsymm : ν.symm = ν'.symm := by
    apply Equiv.ext
    intro i
    simpa only [relativeMenPermutation, Equiv.trans_apply, Equiv.apply_symm_apply] using
      congrArg (fun f : Matching n ↦ f (μ.symm i)) hrel
  have hν : ν = ν' := congrArg Equiv.symm hνsymm
  exact Subtype.ext (congrArg (fun m ↦ ((μ, m), U, V)) hν)
theorem card_labeledOrientationPairs_le (n u v : ℕ) (P Q : Multiset ℕ → Prop) :
    Nat.card (LabeledOrientationPairs n u v P Q) ≤
      n.factorial * (n.choose u * (n - u).choose v) *
        (Nat.card (RestrictedOrientationPerm u P) * Nat.card (RestrictedOrientationPerm v Q)) := by
  have h := Nat.card_le_card_of_injective _ (labeledOrientationPairsEmbedding n u v P Q).injective
  refine h.trans_eq ?_
  rw [Nat.card_prod, Nat.card_prod, Nat.card_prod, card_orientationSideChoices,
    Nat.card_eq_fintype_card (α := Matching n)]
  simp only [Matching, Fintype.card_perm, Fintype.card_fin, mul_assoc]
private theorem orientationChoices_mul_factorials {n u v : ℕ} :
    (n.choose u * (n - u).choose v) * u.factorial * v.factorial =
      n.descFactorial (u + v) := by
  calc
    _ = ((n - u).choose v * v.factorial) * (n.choose u * u.factorial) := by ring
    _ = (n - u).descFactorial v * n.descFactorial u := by
      simp only [Nat.descFactorial_eq_factorial_mul_choose, mul_comm]
    _ = _ := by
      simpa only [Nat.add_sub_cancel_left] using
        (Nat.descFactorial_mul_descFactorial (n := n) (Nat.le_add_right u v))
theorem card_labeledOrientationPairs_real_le {n u v : ℕ} (h : u + v ≤ n)
    (P Q : Multiset ℕ → Prop) :
    (Nat.card (LabeledOrientationPairs n u v P Q) : ℝ) ≤
      ((n.factorial : ℝ) ^ 2 / (n - u - v).factorial) *
        ((Nat.card (RestrictedOrientationPerm u P) : ℝ) / u.factorial) *
          ((Nat.card (RestrictedOrientationPerm v Q) : ℝ) / v.factorial) := by
  have hdesc : (n.factorial : ℝ) / (n - u - v).factorial =
      (n.descFactorial (u + v) : ℝ) := by
    apply (div_eq_iff (by positivity)).mpr
    rw [← Nat.sub_add_eq, mul_comm]
    exact_mod_cast (Nat.factorial_mul_descFactorial h).symm
  have hc : (n.choose u : ℝ) * (n - u).choose v * u.factorial * v.factorial =
      (n.descFactorial (u + v) : ℝ) := by exact_mod_cast orientationChoices_mul_factorials
  calc
    _ ≤ (n.factorial : ℝ) * ((n.choose u : ℝ) * (n - u).choose v) *
        ((Nat.card (RestrictedOrientationPerm u P) : ℝ) *
          Nat.card (RestrictedOrientationPerm v Q)) := by
      exact_mod_cast card_labeledOrientationPairs_le n u v P Q
    _ = _ := by
      rw [pow_two, mul_div_assoc, hdesc, ← hc]
      field_simp
private noncomputable def orientationCycleTypeFraction (k : ℕ) (P : Multiset ℕ → Prop) : ℝ≥0∞ :=
  (Nat.card {f : Perm (Fin k) // P f.cycleType} : ℝ≥0∞) / k.factorial
theorem card_labeledOrientationPairs_le_cycleTypeFractions {n u v : ℕ} (h : u + v ≤ n)
    (P Q : Multiset ℕ → Prop) :
    (Nat.card (LabeledOrientationPairs n u v P Q) : ℝ≥0∞) ≤
      ((n.factorial : ℝ≥0∞) ^ 2 / (n - u - v).factorial) *
        orientationCycleTypeFraction u P * orientationCycleTypeFraction v Q := by
  let B (k : ℕ) (F : Multiset ℕ → Prop) := Nat.card {f : Perm (Fin k) // F f.cycleType}
  have hB (k : ℕ) (F : Multiset ℕ → Prop) : Nat.card (RestrictedOrientationPerm k F) ≤ B k F :=
    Nat.card_le_card_of_injective (fun f : RestrictedOrientationPerm k F ↦ ⟨f.val, f.property.2⟩)
      (fun _ _ he ↦ Subtype.ext (congrArg (fun f : {f : Perm (Fin k) // F f.cycleType} ↦ f.val) he))
  have hr := card_labeledOrientationPairs_real_le h P Q
  have ht : (Nat.card (LabeledOrientationPairs n u v P Q) : ℝ) ≤
      ((n.factorial : ℝ) ^ 2 / (n - u - v).factorial) *
        ((B u P : ℝ) / u.factorial) * ((B v Q : ℝ) / v.factorial) := by
    refine hr.trans ?_
    gcongr
    · exact_mod_cast hB u P
    · exact_mod_cast hB v Q
  have he := ENNReal.ofReal_le_ofReal ht
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_div_of_pos (by positivity),
    ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_pow (by positivity)] at he
  simpa only [ENNReal.ofReal_natCast, orientationCycleTypeFraction, B] using he
@[simp] theorem orientationCycleTypeFraction_true (k : ℕ) :
    orientationCycleTypeFraction k (fun _ ↦ True) = 1 := by
  unfold orientationCycleTypeFraction
  have e : {f : Perm (Fin k) // True} ≃ Perm (Fin k) :=
    Equiv.subtypeUnivEquiv (fun _ ↦ trivial)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  exact ENNReal.div_self (by positivity) (ENNReal.natCast_ne_top _)
theorem card_labeledOrientationPairs_unrestricted_le {n u v : ℕ} (h : u + v ≤ n) :
    (Nat.card (LabeledOrientationPairs n u v (fun _ ↦ True) (fun _ ↦ True)) : ℝ≥0∞) ≤
      (n.factorial : ℝ≥0∞) ^ 2 / (n - u - v).factorial := by
  simpa only [orientationCycleTypeFraction_true, mul_one] using
    card_labeledOrientationPairs_le_cycleTypeFractions h (fun _ ↦ True) (fun _ ↦ True)
theorem womanRank_second_lt_first_of_worsePartnerMen {p : Profile n} {μ ν : Matching n}
    (hν : IsStable p ν) {i : Fin n} (hi : i ∈ worsePartnerMen p ν μ) :
    p.womanRank (μ i) (ν.symm (μ i)) < p.womanRank (μ i) i := by
  have hm := (mem_filter.mp hi).2
  have hne : ν i ≠ μ i := fun h ↦ hm.ne (congrArg (p.manRank i) h).symm
  have hj : ν.symm (μ i) ≠ i := fun h ↦ hne (ν.symm_apply_eq.mp h).symm
  refine lt_of_le_of_ne (le_of_not_gt ?_) ((p.womanRank (μ i)).injective.ne hj)
  exact fun h ↦ hν i (μ i) ⟨hne, hm, h⟩
private theorem relativeMenPermutation_maps_worsePartnerMen {p : Profile n} {μ ν : Matching n}
    (hμ : IsStable p μ) (hν : IsStable p ν) {i : Fin n} (hi : i ∈ worsePartnerMen p ν μ) :
    relativeMenPermutation μ ν i ∈ worsePartnerMen p ν μ := by
  let j := ν.symm (μ i)
  have hνj : ν j = μ i := ν.apply_symm_apply _
  have hw : p.womanRank (μ i) j < p.womanRank (μ i) i :=
    womanRank_second_lt_first_of_worsePartnerMen hν hi
  have hμj : μ j ≠ ν j := by
    intro h
    have hj : j = i := μ.injective (h.trans hνj)
    exact hw.ne (congrArg (p.womanRank (μ i)) hj)
  refine mem_filter.mpr ⟨mem_univ _, lt_of_le_of_ne (le_of_not_gt ?_)
    ((p.manRank j).injective.ne hμj)⟩
  intro h
  exact hμ j (μ i) ⟨fun h' ↦ hμj (h'.trans hνj.symm), hνj ▸ h,
    by simpa only [Equiv.symm_apply_apply] using hw⟩
private theorem perm_mem_iff_of_maps_finset (f : Matching n) (S : Finset (Fin n))
    (hf : ∀ i ∈ S, f i ∈ S) (i : Fin n) : f i ∈ S ↔ i ∈ S := by
  have he : S.image f = S := eq_of_subset_of_card_le (by
    intro j hj
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hj
    exact hf k hk) ((card_image_of_injective S f.injective).ge)
  refine ⟨fun h ↦ ?_, hf i⟩
  obtain ⟨k, hk, heq⟩ := mem_image.mp (he.symm ▸ h)
  exact f.injective heq ▸ hk
theorem labeledPairOrientation_of_stable {p : Profile n} {μ ν : Matching n}
    (hμ : IsStable p μ) (hν : IsStable p ν) :
    LabeledPairOrientation μ ν (worsePartnerMen p μ ν) (worsePartnerMen p ν μ) := by
  have hright := perm_mem_iff_of_maps_finset (relativeMenPermutation μ ν) (worsePartnerMen p ν μ)
    (fun _ hi ↦ relativeMenPermutation_maps_worsePartnerMen hμ hν hi)
  have hleft' := perm_mem_iff_of_maps_finset (relativeMenPermutation ν μ) (worsePartnerMen p μ ν)
    (fun _ hi ↦ relativeMenPermutation_maps_worsePartnerMen hν hμ hi)
  refine ⟨disjoint_worsePartnerMen p μ ν, union_worsePartnerMen_eq_support p μ ν, ?_, hright⟩
  intro i
  have hi := hleft' (relativeMenPermutation μ ν i)
  have he : relativeMenPermutation ν μ (relativeMenPermutation μ ν i) = i := by
    simp only [relativeMenPermutation, Equiv.trans_apply, Equiv.apply_symm_apply,
      Equiv.symm_apply_apply]
  rw [he] at hi
  exact hi.symm
end IncomparableLP
end

-- TwoStableFixedPairBound
section
open MeasureTheory Set StableMarriage
open scoped ENNReal
namespace IncomparableLP
private noncomputable def labeledStablePairMassBound (n u v : ℕ) : ℝ :=
  Real.exp 72 * ((1 + Real.log n) * pairSizeBetaFactor n u * pairSizeBetaFactor n v /
    ((↑(n - 1).factorial : ℝ) * ↑(u - 1).factorial * ↑(v - 1).factorial))
theorem measure_twoStableOrientationEvent_le_labeledStablePairMassBound
    {n u v : ℕ} (h : ValidPairSizes n (u, v)) (μ ν : Matching n) (A : Finset (Fin n))
    (hu : (pairOrientedMovedMen μ ν A).card = u)
    (hv : (pairOrientedMovedMen μ ν (Finset.univ \ A)).card = v) :
    continuousScoreLaw n (twoStableOrientationEvent μ ν A (A.image μ)) ≤
      ENNReal.ofReal (labeledStablePairMassBound n u v) := by
  have hn : 0 < n := by have := h.1; have := h.2.2; omega
  have hu₀ : 0 < u := by have := h.1; omega
  have hv₀ : 0 < v := by have := h.2.1; omega
  have hp := continuousScoreLaw_twoStableOrientation_image_le_radial μ ν A hu hv hn hu₀ hv₀
  rw [lintegral_pairRadialUpperKernel_eq_closed] at hp
  refine hp.trans ?_
  rw [labeledStablePairMassBound, ENNReal.ofReal_mul (Real.exp_pos _).le]
  exact mul_le_mul_right
    (by simpa only [pairLaplaceClosed] using lintegral_twoStableClosedLaplaceRadial_le h) _
private theorem pairOrientedMovedMen_eq_sides {n : ℕ} {μ ν : Matching n}
    {U V : Finset (Fin n)} (hUV : LabeledPairOrientation μ ν U V) :
    pairOrientedMovedMen ν μ U = U ∧
      pairOrientedMovedMen ν μ (Finset.univ \ U) = V := by
  have hm (i : Fin n) : ν i ≠ μ i ↔ i ∈ U ∨ i ∈ V := by
    rw [← Finset.mem_union, hUV.union_support]
    simp only [relativeMenPermutation, Equiv.Perm.mem_support, Equiv.trans_apply]
    exact ne_comm.trans (not_congr ν.symm_apply_eq).symm
  constructor
  · ext i
    simp only [pairOrientedMovedMen, Finset.mem_filter, hm, and_iff_left_iff_imp]
    exact fun hi ↦ Or.inl hi
  · ext i
    simp only [pairOrientedMovedMen, Finset.mem_filter, Finset.mem_sdiff,
      Finset.mem_univ, true_and, hm]
    exact ⟨fun ⟨hi, h⟩ ↦ h.resolve_left hi,
      fun hi ↦ ⟨fun hj ↦ Finset.disjoint_left.mp hUV.disjoint hj hi, Or.inr hi⟩⟩
theorem measure_stablePairSector_le_labeledStablePairMassBound {n u v : ℕ}
    {μ ν : Matching n} {U V : Finset (Fin n)}
    (h : ValidPairSizes n (u, v)) (hUV : LabeledPairOrientation μ ν U V)
    (hu : U.card = u) (hv : V.card = v)
    {E : Set (ScoreProfile n)}
    (hE : ∀ᵐ x ∂continuousScoreLaw n, x ∈ E →
      IsScoreStable x μ ∧ IsScoreStable x ν ∧
        U = worsePartnerMen (profileOfScores x) μ ν) :
    continuousScoreLaw n E ≤ ENNReal.ofReal (labeledStablePairMassBound n u v) := by
  have hsub : continuousScoreLaw n E ≤
      continuousScoreLaw n (twoStableOrientationEvent ν μ U (U.image ν)) := by
    apply measure_mono_ae
    filter_upwards [ae_injective_rows n, hE] with x hx hs he
    obtain ⟨hμ, hν, hU⟩ := hs he
    exact (twoStableOrientation_of_male_class hν hμ hx U
      (fun m _ ↦ hU ▸ mem_worsePartnerMen_iff_score_lt hx μ ν m)).1
  exact hsub.trans (measure_twoStableOrientationEvent_le_labeledStablePairMassBound
    h ν μ U ((congrArg Finset.card (pairOrientedMovedMen_eq_sides hUV).1).trans hu)
    ((congrArg Finset.card (pairOrientedMovedMen_eq_sides hUV).2).trans hv))
theorem labeledStablePairMassBound_mul_factorials {n u v : ℕ}
    (h : ValidPairSizes n (u, v)) :
    ((n.factorial : ℝ) ^ 2 / ↑(n - u - v).factorial) * labeledStablePairMassBound n u v =
      Real.exp 72 * (1 + Real.log n) * twoStablePairSizeKernel n (u, v) := by
  rw [twoStablePairSizeKernel_eq_beta_factors h, labeledStablePairMassBound]
  ring
end IncomparableLP
end

-- TwoStablePairMassSums
section
open Filter Finset MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace IncomparableLP
variable {n : ℕ}
private abbrev LabeledMatchingOrientation (n : ℕ) :=
  (Matching n × Matching n) × (Finset (Fin n) × Finset (Fin n))
private noncomputable def scorePairOrientationSides (x : ScoreProfile n) (μ ν : Matching n) :
    Finset (Fin n) × Finset (Fin n) :=
  (worsePartnerMen (profileOfScores x) μ ν, worsePartnerMen (profileOfScores x) ν μ)
private noncomputable def scorePairOrientationSizes (x : ScoreProfile n) (μ ν : Matching n) : ℕ × ℕ :=
  ((scorePairOrientationSides x μ ν).1.card, (scorePairOrientationSides x μ ν).2.card)
theorem measurableSet_scorePairOrientationSides_eq (μ ν : Matching n)
    (uv : Finset (Fin n) × Finset (Fin n)) :
    MeasurableSet {x : ScoreProfile n | scorePairOrientationSides x μ ν = uv} :=
  measurable_profileOfScores n (MeasurableSet.of_discrete :
    MeasurableSet {p : Profile n | (worsePartnerMen p μ ν, worsePartnerMen p ν μ) = uv})
theorem measurable_scorePairOrientationSizes (μ ν : Matching n) :
    Measurable (fun x : ScoreProfile n ↦ scorePairOrientationSizes x μ ν) :=
  (Measurable.of_discrete (f := fun p : Profile n ↦
    ((worsePartnerMen p μ ν).card, (worsePartnerMen p ν μ).card))).comp
      (measurable_profileOfScores n)
private def scoreFixedOrientationPairEvent (R : ScoreProfile n → Matching n → Matching n → Prop)
    (z : LabeledMatchingOrientation n) : Set (ScoreProfile n) :=
  scoreIncomparablePairEvent R z.1.1 z.1.2 ∩
    {x | scorePairOrientationSides x z.1.1 z.1.2 = z.2}
theorem scoreFixedOrientationPairEvent_data
    {R : ScoreProfile n → Matching n → Matching n → Prop}
    {z : LabeledMatchingOrientation n} {x : ScoreProfile n}
    (hx : x ∈ scoreFixedOrientationPairEvent R z) :
    IsScoreStable x z.1.1 ∧ IsScoreStable x z.1.2 ∧
      z.2.1 = worsePartnerMen (profileOfScores x) z.1.1 z.1.2 ∧
      z.2.2 = worsePartnerMen (profileOfScores x) z.1.2 z.1.1 := by
  have he : scorePairOrientationSides x z.1.1 z.1.2 = z.2 := hx.2
  exact ⟨hx.1.1, hx.1.2.1, (congrArg Prod.fst he).symm, (congrArg Prod.snd he).symm⟩
private noncomputable def scorePairSizeMass (R : ScoreProfile n → Matching n → Matching n → Prop)
    (s : ℕ × ℕ) : ℝ≥0∞ :=
  ∑ μ : Matching n, ∑ ν : Matching n, continuousScoreLaw n
    (scoreIncomparablePairEvent R μ ν ∩ {x | scorePairOrientationSizes x μ ν = s})
theorem scorePairSizeMass_ne_top (R : ScoreProfile n → Matching n → Matching n → Prop)
    (s : ℕ × ℕ) : scorePairSizeMass R s ≠ ⊤ :=
  ENNReal.sum_ne_top.mpr fun _ _ ↦ ENNReal.sum_ne_top.mpr fun _ _ ↦ measure_ne_top _ _
private theorem measure_eq_sum_inter_fibers {Ω α : Type*} [MeasurableSpace Ω]
    {m : Measure Ω} {E : Set Ω} {f : Ω → α}
    (hE : MeasurableSet E) (hf : ∀ a, MeasurableSet {x | f x = a}) (s : Finset α)
    (hc : ∀ᵐ x ∂m, x ∈ E → f x ∈ s) :
    m E = ∑ a ∈ s, m (E ∩ {x | f x = a}) := by
  have hu : E =ᵐ[m] ⋃ a ∈ s, E ∩ {x | f x = a} := by
    filter_upwards [hc] with x hx
    apply propext
    change x ∈ E ↔ x ∈ ⋃ a ∈ s, E ∩ {x | f x = a}
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    exact ⟨fun h ↦ ⟨f x, hx h, h, rfl⟩, fun ⟨_, _, h, _⟩ ↦ h⟩
  rw [measure_congr hu]
  refine measure_biUnion_finset (fun a _ b _ hab ↦ Set.disjoint_left.mpr ?_) fun a _ ↦
    hE.inter (hf a)
  exact fun _ ha hb ↦ hab (ha.2.symm.trans hb.2)
private noncomputable def orientationSupportsOfSizes (n : ℕ) (s : ℕ × ℕ) :
    Finset (Finset (Fin n) × Finset (Fin n)) := by
  classical
  exact univ.filter fun uv ↦ (uv.1.card, uv.2.card) = s
private noncomputable def fixedOrientationSizeMarks (n : ℕ) (s : ℕ × ℕ) :
    Finset (LabeledMatchingOrientation n) :=
  (univ : Finset (Matching n × Matching n)).product (orientationSupportsOfSizes n s)
private theorem mem_fixedOrientationSizeMarks {z : LabeledMatchingOrientation n} {s : ℕ × ℕ} :
    z ∈ fixedOrientationSizeMarks n s ↔ (z.2.1.card, z.2.2.card) = s := by
  classical
  simp [fixedOrientationSizeMarks, orientationSupportsOfSizes, product_eq_sprod]
private theorem scorePairSizeMass_eq_sum_fixedMarks
    {R : ScoreProfile n → Matching n → Matching n → Prop}
    (hR : ∀ μ ν, MeasurableSet {x | R x μ ν}) (s : ℕ × ℕ) :
    scorePairSizeMass R s =
      ∑ z ∈ fixedOrientationSizeMarks n s, continuousScoreLaw n
        (scoreFixedOrientationPairEvent R z) := by
  classical
  unfold scorePairSizeMass fixedOrientationSizeMarks
  rw [product_eq_sprod, sum_product, Fintype.sum_prod_type]
  refine sum_congr rfl fun μ _ ↦ sum_congr rfl fun ν _ ↦ ?_
  let E := scoreIncomparablePairEvent R μ ν
  let G := {x | scorePairOrientationSizes x μ ν = s}
  let f (x : ScoreProfile n) := scorePairOrientationSides x μ ν
  have hmG : MeasurableSet G :=
    (measurable_scorePairOrientationSizes μ ν) (measurableSet_singleton s)
  have hc : ∀ᵐ x ∂continuousScoreLaw n, x ∈ E ∩ G → f x ∈ orientationSupportsOfSizes n s :=
    Eventually.of_forall fun x hx ↦ mem_filter.mpr ⟨mem_univ _, hx.2⟩
  rw [measure_eq_sum_inter_fibers ((measurableSet_scoreIncomparablePairEvent hR μ ν).inter hmG)
    (measurableSet_scorePairOrientationSides_eq μ ν) _ hc]
  refine sum_congr rfl fun uv huv ↦ congrArg (continuousScoreLaw n) ?_
  have hsize := (mem_filter.mp huv).2
  ext x
  change (x ∈ E ∧ x ∈ G) ∧ f x = uv ↔ x ∈ E ∧ f x = uv
  refine ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun h ↦ ⟨⟨h.1, ?_⟩, h.2⟩⟩
  exact (congrArg (fun uv : Finset (Fin n) × Finset (Fin n) ↦ (uv.1.card, uv.2.card))
    h.2).trans hsize
theorem ae_scoreFixedOrientationPairEvent_labeled
    (R : ScoreProfile n → Matching n → Matching n → Prop) (z : LabeledMatchingOrientation n) :
    ∀ᵐ x ∂continuousScoreLaw n, x ∈ scoreFixedOrientationPairEvent R z →
      LabeledPairOrientation z.1.1 z.1.2 z.2.1 z.2.2 := by
  filter_upwards [ae_injective_rows n] with x ht hx
  have hs : IsStable (profileOfScores x) z.1.1 :=
    (isStable_profileOfScores_iff ht _).mpr hx.1.1
  have hs' : IsStable (profileOfScores x) z.1.2 :=
    (isStable_profileOfScores_iff ht _).mpr hx.1.2.1
  have h := labeledPairOrientation_of_stable hs hs'
  have he : scorePairOrientationSides x z.1.1 z.1.2 = z.2 := hx.2
  change LabeledPairOrientation z.1.1 z.1.2
    (scorePairOrientationSides x z.1.1 z.1.2).1 (scorePairOrientationSides x z.1.1 z.1.2).2 at h
  rwa [he] at h
private noncomputable def labeledOrientationBin (n : ℕ) (s : ℕ × ℕ) (P T : Multiset ℕ → Prop) :
    Finset (LabeledMatchingOrientation n) := by
  classical
  exact univ.filter fun z ↦
    ∃ h : LabeledPairOrientation z.1.1 z.1.2 z.2.1 z.2.2,
      z.2.1.card = s.1 ∧ z.2.2.card = s.2 ∧ P h.leftPerm.cycleType ∧ T h.rightPerm.cycleType
theorem mem_labeledOrientationBin {s : ℕ × ℕ} {P T : Multiset ℕ → Prop}
    {z : LabeledMatchingOrientation n} :
    z ∈ labeledOrientationBin n s P T ↔
      ∃ h : LabeledPairOrientation z.1.1 z.1.2 z.2.1 z.2.2,
        z.2.1.card = s.1 ∧ z.2.2.card = s.2 ∧ P h.leftPerm.cycleType ∧ T h.rightPerm.cycleType := by
  classical
  simp [labeledOrientationBin]
theorem card_labeledOrientationBin (n : ℕ) (s : ℕ × ℕ) (P T : Multiset ℕ → Prop) :
    (labeledOrientationBin n s P T).card = Nat.card (LabeledOrientationPairs n s.1 s.2 P T) := by
  rw [← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun _ ↦ mem_labeledOrientationBin)
theorem scorePairSizeMass_eq_sum_labeled
    {R : ScoreProfile n → Matching n → Matching n → Prop}
    (hR : ∀ μ ν, MeasurableSet {x | R x μ ν}) (s : ℕ × ℕ) (P T : Multiset ℕ → Prop)
    (hcycle : ∀ (z : LabeledMatchingOrientation n)
      (h : LabeledPairOrientation z.1.1 z.1.2 z.2.1 z.2.2),
      ∀ᵐ x ∂continuousScoreLaw n, x ∈ scoreFixedOrientationPairEvent R z →
        P h.leftPerm.cycleType ∧ T h.rightPerm.cycleType) :
    scorePairSizeMass R s = ∑ z ∈ labeledOrientationBin n s P T,
      continuousScoreLaw n (scoreFixedOrientationPairEvent R z) := by
  rw [scorePairSizeMass_eq_sum_fixedMarks hR]
  symm
  refine sum_subset (fun z hz ↦ ?_) fun z hz hnot ↦ ?_
  · obtain ⟨_, hu, hv, _, _⟩ := mem_labeledOrientationBin.mp hz
    exact mem_fixedOrientationSizeMarks.mpr (Prod.ext hu hv)
  have hsize := mem_fixedOrientationSizeMarks.mp hz
  rw [measure_eq_zero_iff_ae_notMem]
  by_cases h : LabeledPairOrientation z.1.1 z.1.2 z.2.1 z.2.2
  · filter_upwards [hcycle z h] with x hx he
    exact hnot (mem_labeledOrientationBin.mpr
      ⟨h, congrArg Prod.fst hsize, congrArg Prod.snd hsize, hx he⟩)
  · filter_upwards [ae_scoreFixedOrientationPairEvent_labeled R z] with x hx he
    exact h (hx he)
theorem scorePairSizeMass_le_card_mul
    {R : ScoreProfile n → Matching n → Matching n → Prop}
    (hR : ∀ μ ν, MeasurableSet {x | R x μ ν}) (s : ℕ × ℕ) (P T : Multiset ℕ → Prop)
    (hcycle : ∀ (z : LabeledMatchingOrientation n)
      (h : LabeledPairOrientation z.1.1 z.1.2 z.2.1 z.2.2),
      ∀ᵐ x ∂continuousScoreLaw n, x ∈ scoreFixedOrientationPairEvent R z →
        P h.leftPerm.cycleType ∧ T h.rightPerm.cycleType)
    {U : ℝ≥0∞}
    (hU : ∀ z : LabeledOrientationPairs n s.1 s.2 P T,
      continuousScoreLaw n (scoreFixedOrientationPairEvent R z.val) ≤ U) :
    scorePairSizeMass R s ≤ (Nat.card (LabeledOrientationPairs n s.1 s.2 P T) : ℝ≥0∞) * U := by
  rw [scorePairSizeMass_eq_sum_labeled hR s P T hcycle]
  calc
    _ ≤ ∑ _z ∈ labeledOrientationBin n s P T, U :=
      sum_le_sum fun z hz ↦ hU ⟨z, mem_labeledOrientationBin.mp hz⟩
    _ = _ := by rw [sum_const, nsmul_eq_mul, card_labeledOrientationBin]
private noncomputable def validPairSizeFinset (n : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((range (n + 1)).product (range (n + 1))).filter (ValidPairSizes n)
@[simp] theorem mem_validPairSizeFinset {s : ℕ × ℕ} :
    s ∈ validPairSizeFinset n ↔ ValidPairSizes n s := by
  classical
  constructor
  · intro h
    exact (mem_filter.mp h).2
  · intro h
    have hs := h.2.2
    exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_range.mpr (by omega),
      mem_range.mpr (by omega)⟩, h⟩
private theorem two_le_finsetCard_of_fixedPointFree {α : Type*} {s : Finset α}
    (hs : s.Nonempty) (f : Equiv.Perm s) (hf : ∀ i, f i ≠ i) : 2 ≤ s.card := by
  obtain ⟨i, hi⟩ := hs
  exact one_lt_card.mpr ⟨(f ⟨i, hi⟩).val, (f ⟨i, hi⟩).property, i, hi,
    fun h ↦ hf _ (Subtype.ext h)⟩
private theorem worsePartnerMen_nonempty_of_not_menWeaklyPrefer {p : Profile n} {μ ν : Matching n}
    (h : ¬ MenWeaklyPrefer p μ ν) : (worsePartnerMen p μ ν).Nonempty := by
  by_contra h0
  apply h
  intro m
  exact le_of_not_gt fun hm ↦ h0 ⟨m, mem_filter.mpr ⟨mem_univ _, hm⟩⟩
theorem LabeledPairOrientation.validPairSizes_of_nonempty {μ ν : Matching n}
    {U V : Finset (Fin n)} (h : LabeledPairOrientation μ ν U V)
    (hU : U.Nonempty) (hV : V.Nonempty) : ValidPairSizes n (U.card, V.card) := by
  refine ⟨two_le_finsetCard_of_fixedPointFree hU h.leftPerm h.leftPerm_apply_ne,
    two_le_finsetCard_of_fixedPointFree hV h.rightPerm h.rightPerm_apply_ne, ?_⟩
  rw [← card_union_of_disjoint h.disjoint, h.union_support]
  exact (card_le_univ _).trans_eq (Fintype.card_fin n)
theorem ae_validPairSizes_of_scoreIncomparablePairEvent
    (R : ScoreProfile n → Matching n → Matching n → Prop) (μ ν : Matching n) :
    ∀ᵐ x ∂continuousScoreLaw n, x ∈ scoreIncomparablePairEvent R μ ν →
      ValidPairSizes n (scorePairOrientationSizes x μ ν) := by
  filter_upwards [ae_injective_rows n] with x ht hx
  have h := labeledPairOrientation_of_stable
    ((isStable_profileOfScores_iff ht μ).mpr hx.1)
    ((isStable_profileOfScores_iff ht ν).mpr hx.2.1)
  exact h.validPairSizes_of_nonempty
    (worsePartnerMen_nonempty_of_not_menWeaklyPrefer hx.2.2.1.1)
    (worsePartnerMen_nonempty_of_not_menWeaklyPrefer hx.2.2.1.2)
theorem scorePairMass_eq_sum_sizeMass
    {R : ScoreProfile n → Matching n → Matching n → Prop}
    (hR : ∀ μ ν, MeasurableSet {x | R x μ ν}) (S : Finset (ℕ × ℕ))
    (hS : ∀ μ ν : Matching n, ∀ᵐ x ∂continuousScoreLaw n,
      x ∈ scoreIncomparablePairEvent R μ ν → scorePairOrientationSizes x μ ν ∈ S) :
    (∑ μ : Matching n, ∑ ν : Matching n,
      continuousScoreLaw n (scoreIncomparablePairEvent R μ ν)) =
        ∑ s ∈ S, scorePairSizeMass R s := by
  let g (μ ν : Matching n) (s : ℕ × ℕ) :=
    continuousScoreLaw n (scoreIncomparablePairEvent R μ ν ∩
      {x | scorePairOrientationSizes x μ ν = s})
  calc
    _ = ∑ μ : Matching n, ∑ ν : Matching n, ∑ s ∈ S, g μ ν s := by
      refine sum_congr rfl fun μ _ ↦ sum_congr rfl fun ν _ ↦ ?_
      exact measure_eq_sum_inter_fibers (measurableSet_scoreIncomparablePairEvent hR μ ν)
        (fun s ↦ (measurable_scorePairOrientationSizes μ ν) (measurableSet_singleton s))
        S (hS μ ν)
    _ = ∑ μ : Matching n, ∑ s ∈ S, ∑ ν : Matching n, g μ ν s :=
      sum_congr rfl fun _ _ ↦ sum_comm
    _ = _ := sum_comm
theorem scorePairMass_real_eq_sum_sizeMass
    {R : ScoreProfile n → Matching n → Matching n → Prop}
    (hR : ∀ μ ν, MeasurableSet {x | R x μ ν}) (S : Finset (ℕ × ℕ))
    (hS : ∀ μ ν : Matching n, ∀ᵐ x ∂continuousScoreLaw n,
      x ∈ scoreIncomparablePairEvent R μ ν → scorePairOrientationSizes x μ ν ∈ S) :
    (∑ μ : Matching n, ∑ ν : Matching n,
      (continuousScoreLaw n).real (scoreIncomparablePairEvent R μ ν)) =
        ∑ s ∈ S, (scorePairSizeMass R s).toReal := by
  have h := congrArg ENNReal.toReal (scorePairMass_eq_sum_sizeMass hR S hS)
  rw [ENNReal.toReal_sum (fun _ _ ↦ ENNReal.sum_ne_top.mpr fun _ _ ↦ measure_ne_top _ _),
    ENNReal.toReal_sum (fun s _ ↦ scorePairSizeMass_ne_top R s)] at h
  simp_rw [ENNReal.toReal_sum (fun _ _ ↦ measure_ne_top _ _)] at h
  exact h
end IncomparableLP
end

-- TwoStablePairPerSizeBounds
section
open Filter MeasureTheory Set StableMarriage
open scoped ENNReal
namespace IncomparableLP
variable {n : ℕ}
private theorem factorialEnvelope_mul_labeledMass {u v : ℕ}
    (hs : ValidPairSizes n (u, v)) :
    ((n.factorial : ℝ≥0∞) ^ 2 / (n - u - v).factorial) *
        ENNReal.ofReal (labeledStablePairMassBound n u v) =
      ENNReal.ofReal (Real.exp 72 * (1 + Real.log n) * twoStablePairSizeKernel n (u, v)) := by
  have he : (n.factorial : ℝ≥0∞) ^ 2 / (n - u - v).factorial =
      ENNReal.ofReal ((n.factorial : ℝ) ^ 2 / (n - u - v).factorial) := by
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_pow (by positivity),
      ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  rw [he, ← ENNReal.ofReal_mul (by positivity), labeledStablePairMassBound_mul_factorials hs]
private theorem scorePairSizeMass_toReal_le_of_envelope
    {R : ScoreProfile n → Matching n → Matching n → Prop} {u v : ℕ}
    (hs : ValidPairSizes n (u, v)) {a : ℝ} (ha : 0 ≤ a)
    (h : scorePairSizeMass R (u, v) ≤ ENNReal.ofReal a *
      (((n.factorial : ℝ≥0∞) ^ 2 / (n - u - v).factorial) *
        ENNReal.ofReal (labeledStablePairMassBound n u v))) :
    (scorePairSizeMass R (u, v)).toReal ≤
      a * (Real.exp 72 * (1 + Real.log n) * twoStablePairSizeKernel n (u, v)) := by
  rw [factorialEnvelope_mul_labeledMass hs, ← ENNReal.ofReal_mul ha] at h
  have hlog := Real.log_natCast_nonneg n
  have hk := twoStablePairSizeKernel_nonneg n (u, v)
  have hn : 0 ≤ a * (Real.exp 72 * (1 + Real.log n) * twoStablePairSizeKernel n (u, v)) := by
    positivity
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top h).trans_eq (ENNReal.toReal_ofReal hn)
private theorem scoreFixedOrientationPairEvent_le_labeledMass
    {R : ScoreProfile n → Matching n → Matching n → Prop} {u v : ℕ}
    (hs : ValidPairSizes n (u, v)) {P T : Multiset ℕ → Prop}
    (z : LabeledOrientationPairs n u v P T) :
    continuousScoreLaw n (scoreFixedOrientationPairEvent R z.val) ≤
      ENNReal.ofReal (labeledStablePairMassBound n u v) := by
  obtain ⟨hor, hu, hv, _, _⟩ := z.property
  apply measure_stablePairSector_le_labeledStablePairMassBound hs hor hu hv
  exact Eventually.of_forall fun _ hx ↦
    ⟨(scoreFixedOrientationPairEvent_data hx).1, (scoreFixedOrientationPairEvent_data hx).2.1,
      (scoreFixedOrientationPairEvent_data hx).2.2.1⟩
theorem scorePairSizeMass_toReal_le_kernel
    {R : ScoreProfile n → Matching n → Matching n → Prop}
    (hR : ∀ μ ν, MeasurableSet {x | R x μ ν}) {s : ℕ × ℕ} (hs : ValidPairSizes n s) :
    (scorePairSizeMass R s).toReal ≤
      Real.exp 72 * (1 + Real.log n) * twoStablePairSizeKernel n s := by
  rcases s with ⟨u, v⟩
  have h := scorePairSizeMass_le_card_mul hR (u, v) (fun _ ↦ True) (fun _ ↦ True)
    (fun _ _ ↦ Eventually.of_forall fun _ _ ↦ ⟨trivial, trivial⟩)
    (scoreFixedOrientationPairEvent_le_labeledMass hs)
  have hcount := card_labeledOrientationPairs_unrestricted_le hs.2.2
  have hmass := h.trans (mul_le_mul_left hcount _)
  exact (scorePairSizeMass_toReal_le_of_envelope hs (a := 1) zero_le_one
    (by simpa only [ENNReal.ofReal_one, one_mul] using hmass)).trans_eq (one_mul _)
end IncomparableLP
end

-- PivotPairEnvelopeBounds
section
open Filter MeasureTheory Set StableMarriage Asymptotics
open scoped BigOperators
namespace IncomparableLP
variable {n : ℕ}
private theorem sum_scoreTwoLongOrientations_le (hn : 0 < n) {b : ℝ} (hb : 0 < b) :
    (∑ μ : Matching n, ∑ ν : Matching n,
      (continuousScoreLaw n).real (scoreIncomparablePairEvent (ScoreTwoLongOrientations b) μ ν)) ≤
      longPairEnvelope (Real.exp 72) b n := by
  classical
  let S := (validPairSizeFinset n).filter fun s ↦
    b * Real.sqrt (n : ℝ) ≤ (s.1 : ℝ) ∧ b * Real.sqrt (n : ℝ) ≤ (s.2 : ℝ)
  have hS (s : ℕ × ℕ) (hs : s ∈ S) : ValidPairSizes n s :=
    mem_validPairSizeFinset.mp (Finset.mem_filter.mp hs).1
  rw [scorePairMass_real_eq_sum_sizeMass (measurableSet_scoreTwoLongOrientations b) S ?_]
  · exact sum_twoStablePairSizeWeights_le hn S
      (fun s ↦ (scorePairSizeMass (ScoreTwoLongOrientations b) s).toReal)
      (Real.exp_pos 72).le
      (fun s hs ↦ scorePairSizeMass_toReal_le_kernel (measurableSet_scoreTwoLongOrientations b)
        (hS s hs))
      (sum_twoStablePairSizeKernel_le_both_long hn S hS hb
        (fun s hs ↦ (Finset.mem_filter.mp hs).2))
  · intro μ ν
    filter_upwards [ae_validPairSizes_of_scoreIncomparablePairEvent
      (ScoreTwoLongOrientations b) μ ν] with x hx he
    exact Finset.mem_filter.mpr ⟨mem_validPairSizeFinset.mpr (hx he), he.2.2.2⟩
theorem PivotCountParameters.integral_incomparableCountProductMass_le_envelope
    (q : PivotCountParameters) (hn : 0 < n) {κ : ℝ} (hb : 0 < q.lowerLength)
    (hκ : κ < q.lowerLength) (hcap : (q.supportCap : ℝ) ≤ κ * Real.sqrt (n : ℝ)) :
    (∫ x, q.incomparableCountProductMass x ∂continuousScoreLaw n) ≤
      longPairEnvelope (Real.exp 72) q.lowerLength n :=
  (q.integral_incomparableCountProducts_le_sum hn hκ hcap).trans
    (sum_scoreTwoLongOrientations_le hn hb)
private theorem incomparableCountProductMass_nonneg (q : PivotCountParameters)
    {n : ℕ} (x : ScoreProfile n) : 0 ≤ q.incomparableCountProductMass x := by
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  exact Set.indicator_nonneg (fun y _ ↦
    mul_nonneg (q.count_mem_Icc i y).1 (q.count_mem_Icc j y).1) x
end IncomparableLP
end

noncomputable section
open MeasureTheory Filter IncomparableLP Asymptotics
open scoped Topology IncomparableLP
private def params (b A B κ : ℝ) (n : ℕ) : PivotCountParameters :=
  ⟨b,A,B,pivotDecorationSupportCap κ n,logarithmicCycleCutoff n⟩

private def admissible (b A B κ : ℝ) : Prop :=
  0 < b ∧ b ≤ 1 ∧ 1 ≤ A ∧ 0 < B ∧ 0 < κ ∧ κ < b ∧
    24*κ^2/2 + (B+1)*κ ≤ 1/4 ∧
    Real.exp (κ*(2*(1+B))) * (2*κ*(B/(1/128))) ≤ 3/32


private theorem incomparable_estimate : (∀ b A B κ : ℝ, admissible b A B κ →
  (fun n : ℕ => ∫ x, (params b A B κ n).incomparableCountProductMass x ∂continuousScoreLaw n) =o[atTop]
    (fun n : ℕ => ((n:ℝ)*Real.log n)^2)) := by
  intro b A B κ hq
  apply isLittleO_iff.mpr
  intro e he
  filter_upwards [eventually_pivotDecorationSupportCap_bounds hq.2.2.2.2.1,
    eventually_longPairEnvelope_le (Real.exp_pos 72) hq.1 he,
    eventually_gt_atTop (0 : ℕ)] with n hK hsmall hn
  let q := params b A B κ n
  have hp := q.integral_incomparableCountProductMass_le_envelope hn hq.1 hq.2.2.2.2.2.1 hK.2.1
  have hnon : 0 ≤ ∫ x, q.incomparableCountProductMass x ∂continuousScoreLaw n :=
    integral_nonneg fun x => incomparableCountProductMass_nonneg q x
  change ‖∫ x, q.incomparableCountProductMass x ∂continuousScoreLaw n‖ ≤ e * ‖((n:ℝ)*Real.log n)^2‖
  simpa only [Real.norm_eq_abs, abs_of_nonneg hnon,
    abs_of_nonneg (sq_nonneg ((n:ℝ)*Real.log n))] using hp.trans hsmall
end

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 30000 in
theorem OMA.solution : OMA.R_LennonPittel_lennon_pittel_conjecture_R3_H2_R1_H2_R1.H4 := incomparable_estimate
