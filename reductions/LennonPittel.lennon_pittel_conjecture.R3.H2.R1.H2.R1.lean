import OMAReductions.R_LennonPittel_lennon_pittel_conjecture_R3_H2_R1
import Mathlib

/-! The marked score model of Bo Cowgill, bocowgill/lennon-pittel at
cf950d059659, Apache-2.0. The reduction separates abundance of the
conditional means from estimates on the diagonal and ordered pairs of marks. -/
-- Credit: @marcusbuffett


-- IidScoreRanks
section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace MarkedLP
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
end MarkedLP
end

-- MarkedCounting
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace MarkedLP
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
end MarkedLP
end

-- ScoreRanks
section
open Function MeasureTheory Set
namespace MarkedLP
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
end MarkedLP
end

-- ContinuousScoreBridge
section
open scoped BigOperators ENNReal MarkedLP
open MeasureTheory Set
namespace MarkedLP
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
end MarkedLP
end

-- CoexposureGoodScores
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal MarkedLP
namespace MarkedLP
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
end MarkedLP
end

-- ExposedRotations
section
open StableMarriage
namespace MarkedLP
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
end MarkedLP
end

-- CoexposureScoreProduct
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace MarkedLP
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
end MarkedLP
end

-- PivotSpouseProductLower
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace MarkedLP
private def maleSpouseTotal {n : ℕ} (x : ScoreProfile n) (μ : Matching n) : ℝ :=
  ∑ i, maleSpouseScore x μ i
theorem measurable_maleSpouseTotal {n : ℕ} (μ : Matching n) :
    Measurable (fun x : ScoreProfile n ↦ maleSpouseTotal x μ) :=
  Finset.measurable_sum _ fun i _ ↦ measurable_maleSpouseScore μ i
end MarkedLP
end

-- PivotForwardRevealCell
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace MarkedLP
private def forwardEligibleScoreCell (x y : ℝ) : Set (ℝ × ℝ) :=
  Ioi x ×ˢ Iio y
theorem measurableSet_forwardEligibleScoreCell (x y : ℝ) :
    MeasurableSet (forwardEligibleScoreCell x y) :=
  measurableSet_Ioi.prod measurableSet_Iio
private noncomputable def stableScoreCellLaw (x y : ℝ) : Measure (ℝ × ℝ) :=
  unitScorePairLaw.restrict (nonblockingScoreCell x y)
private instance (x y : ℝ) : IsFiniteMeasure (stableScoreCellLaw x y) :=
  inferInstanceAs (IsFiniteMeasure (unitScorePairLaw.restrict _))
theorem stableScoreCellLaw_restrict_forwardEligible (x y : ℝ) :
    (stableScoreCellLaw x y).restrict (forwardEligibleScoreCell x y) =
      (unitScoreLaw.restrict (Ioi x)).prod (unitScoreLaw.restrict (Iio y)) := by
  rw [stableScoreCellLaw, Measure.restrict_restrict_of_subset]
  · exact (Measure.prod_restrict (Ioi x) (Iio y)).symm
  · rintro z hz hblock
    have h₁ : x < z.1 := (mem_prod.mp hz).1
    have h₂ : z.1 < x := (mem_prod.mp hblock).1
    exact (not_lt_of_ge h₁.le) h₂
private theorem unitScorePairLaw_ae_fst_ne (x : ℝ) :
    ∀ᵐ z ∂unitScorePairLaw, z.1 ≠ x := by
  exact (Measure.quasiMeasurePreserving_fst (μ := unitScoreLaw) (ν := unitScoreLaw)).ae
    (unitScoreLaw.ae_ne x)
theorem stableScoreCellLaw_restrict_not_forwardEligible (x y : ℝ) :
    (stableScoreCellLaw x y).restrict (forwardEligibleScoreCell x y)ᶜ =
      unitScoreLaw.prod (unitScoreLaw.restrict (Ici y)) := by
  rw [stableScoreCellLaw,
    Measure.restrict_restrict (measurableSet_forwardEligibleScoreCell x y).compl]
  calc
    _ = unitScorePairLaw.restrict (univ ×ˢ Ici y) := by
      apply Measure.restrict_congr_set
      filter_upwards [unitScorePairLaw_ae_fst_ne x] with z hz
      apply propext
      change (¬ (x < z.1 ∧ z.2 < y)) ∧ (¬ (z.1 < x ∧ z.2 < y)) ↔ z ∈ univ ×ˢ Ici y
      simp only [mem_prod, mem_univ, true_and, mem_Ici]
      refine ⟨fun h ↦ le_of_not_gt ?_,
        fun hy ↦ ⟨fun h ↦ hy.not_gt h.2, fun h ↦ hy.not_gt h.2⟩⟩
      intro hy
      exact (lt_or_gt_of_ne hz).elim (fun hlt ↦ h.2 ⟨hlt, hy⟩) (fun hlt ↦ h.1 ⟨hlt, hy⟩)
    _ = _ := by rw [unitScorePairLaw, ← Measure.prod_restrict, Measure.restrict_univ]
private noncomputable def inactiveFemaleScoreLaw (y : ℝ) : Measure ℝ :=
  (unitScoreLaw (Ici y))⁻¹ • unitScoreLaw.restrict (Ici y)
theorem unitScoreLaw_Ici_of_mem_Icc {y : ℝ} (hy : y ∈ Icc 0 1) :
    unitScoreLaw (Ici y) = ENNReal.ofReal (1 - y) := by
  rw [← compl_Iio, measure_compl measurableSet_Iio (measure_ne_top _ _),
    measure_univ, unitScoreLaw_Iio_of_mem_Icc hy, ENNReal.ofReal_sub _ hy.1, ENNReal.ofReal_one]
theorem inactiveFemaleScoreLaw_isProbabilityMeasure {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) :
    IsProbabilityMeasure (inactiveFemaleScoreLaw y) := by
  have hm : unitScoreLaw (Ici y) ≠ 0 := by
    rw [unitScoreLaw_Ici_of_mem_Icc ⟨hy0, hy1.le⟩]
    exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hy1)).ne'
  refine ⟨?_⟩
  rw [inactiveFemaleScoreLaw, Measure.smul_apply, Measure.restrict_apply_univ,
    smul_eq_mul, ENNReal.inv_mul_cancel hm (measure_ne_top _ _)]
private def forwardScoreCellFlagEvent (x y : ℝ) (b : Bool) : Set (ℝ × ℝ) :=
  if b then forwardEligibleScoreCell x y else (forwardEligibleScoreCell x y)ᶜ
theorem measurableSet_forwardScoreCellFlagEvent (x y : ℝ) (b : Bool) :
    MeasurableSet (forwardScoreCellFlagEvent x y b) := by
  cases b
  · exact (measurableSet_forwardEligibleScoreCell x y).compl
  · exact measurableSet_forwardEligibleScoreCell x y
private noncomputable def forwardScoreCellFlagLaw (x y : ℝ) (b : Bool) : Measure (ℝ × ℝ) :=
  if b then (unitScoreLaw.restrict (Ioi x)).prod (unitScoreLaw.restrict (Iio y))
  else unitScoreLaw.prod (unitScoreLaw.restrict (Ici y))
private instance (x y : ℝ) (b : Bool) : IsFiniteMeasure (forwardScoreCellFlagLaw x y b) := by
  cases b
  · exact inferInstanceAs
      (IsFiniteMeasure (unitScoreLaw.prod (unitScoreLaw.restrict (Ici y))))
  · exact inferInstanceAs
      (IsFiniteMeasure ((unitScoreLaw.restrict (Ioi x)).prod (unitScoreLaw.restrict (Iio y))))
theorem stableScoreCellLaw_restrict_flag (x y : ℝ) (b : Bool) :
    (stableScoreCellLaw x y).restrict (forwardScoreCellFlagEvent x y b) =
      forwardScoreCellFlagLaw x y b := by
  cases b
  · exact stableScoreCellLaw_restrict_not_forwardEligible x y
  · exact stableScoreCellLaw_restrict_forwardEligible x y
private abbrev OffDiagonalCellIndex (n : ℕ) := {q : ScorePairIndex n // q.1 ≠ q.2}
private def forwardScoreMaskEvent {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) : Set (OffDiagonalScorePairs n) :=
  univ.pi fun q ↦ forwardScoreCellFlagEvent
    (diagonalPairAt d q.val.1).1 (diagonalPairAt d q.val.2).2 (flag q)
theorem measurableSet_forwardScoreMaskEvent {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) : MeasurableSet (forwardScoreMaskEvent d flag) :=
  (measurableSet_pi countable_univ).2 (Or.inl fun _ _ ↦
    measurableSet_forwardScoreCellFlagEvent _ _ _)
theorem offDiagonalScoreLaw_restrict_nonblocking_mask {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) :
    ((offDiagonalScoreLaw n).restrict (offDiagonalNonblocking d)).restrict
        (forwardScoreMaskEvent d flag) =
      Measure.pi fun q : OffDiagonalCellIndex n ↦ forwardScoreCellFlagLaw
        (diagonalPairAt d q.val.1).1 (diagonalPairAt d q.val.2).2 (flag q) := by
  rw [offDiagonalScoreLaw_restrict_nonblocking, forwardScoreMaskEvent, Measure.restrict_pi_pi]
  congr 1
  funext q
  exact stableScoreCellLaw_restrict_flag _ _ _
theorem measurePreserving_offDiagonalScoreLaw_splitMask {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) :
    MeasurePreserving
      (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : OffDiagonalCellIndex n ↦ ℝ × ℝ)
        (fun q ↦ flag q = true))
      (((offDiagonalScoreLaw n).restrict (offDiagonalNonblocking d)).restrict
        (forwardScoreMaskEvent d flag))
      ((Measure.pi fun q : {q : OffDiagonalCellIndex n // flag q = true} ↦
        (unitScoreLaw.restrict (Ioi (diagonalPairAt d q.val.val.1).1)).prod
          (unitScoreLaw.restrict (Iio (diagonalPairAt d q.val.val.2).2))).prod
        (Measure.pi fun q : {q : OffDiagonalCellIndex n // flag q ≠ true} ↦
          unitScoreLaw.prod (unitScoreLaw.restrict (Ici (diagonalPairAt d q.val.val.2).2)))) := by
  rw [offDiagonalScoreLaw_restrict_nonblocking_mask]
  convert measurePreserving_piEquivPiSubtypeProd
    (fun q : OffDiagonalCellIndex n ↦ forwardScoreCellFlagLaw
      (diagonalPairAt d q.val.1).1 (diagonalPairAt d q.val.2).2 (flag q))
    (fun q ↦ flag q = true) using 2
  · congr 1
    funext q
    simp [forwardScoreCellFlagLaw, q.property]
  · congr 1
    funext q
    simp [forwardScoreCellFlagLaw, q.property]
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
private theorem measurePreserving_forwardInactiveColumnsEquiv_pi {n : ℕ}
    (flag : OffDiagonalCellIndex n → Bool)
    (μ : ForwardInactiveCellIndex flag → Measure (ℝ × ℝ)) [∀ q, SigmaFinite (μ q)] :
    MeasurePreserving (forwardInactiveColumnsEquiv flag) (Measure.pi μ)
      (Measure.pi fun j : Fin n ↦
        Measure.pi fun q : ForwardInactiveColumnIndex flag j ↦ μ q.val) := by
  let e := (forwardInactiveColumnsEquiv flag).symm
  refine MeasurePreserving.symm e ⟨e.measurable, (Measure.pi_eq fun s _ ↦ ?_).symm⟩
  rw [MeasurableEquiv.map_apply]
  rw [show e ⁻¹' (univ.pi s) = univ.pi
      (fun j : Fin n ↦ univ.pi fun q : ForwardInactiveColumnIndex flag j ↦ s q.val) by
    ext z
    simp only [mem_preimage, mem_pi, mem_univ, forall_true_left, e,
      forwardInactiveColumnsEquiv, MeasurableEquiv.symm_mk, MeasurableEquiv.coe_mk,
      Equiv.symm, Equiv.coe_fn_mk]
    constructor
    · intro h j q
      obtain ⟨q, rfl⟩ := q
      exact h q
    · intro h q
      exact h q.val.val.2 ⟨q, rfl⟩]
  simp_rw [Measure.pi_pi]
  rw [← Fintype.prod_sigma']
  exact Fintype.prod_equiv
    (Equiv.sigmaFiberEquiv (fun q : ForwardInactiveCellIndex flag ↦ q.val.val.2))
    (fun q : Σ j : Fin n, ForwardInactiveColumnIndex flag j ↦ μ q.2.val (s q.2.val))
    (fun q : ForwardInactiveCellIndex flag ↦ μ q (s q)) (fun _ ↦ rfl)
private noncomputable def forwardScoreMaskInactiveColumnLaw {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) :
    Measure ((j : Fin n) → ForwardInactiveColumnIndex flag j → ℝ × ℝ) :=
  Measure.pi fun j : Fin n ↦ Measure.pi fun _ : ForwardInactiveColumnIndex flag j ↦
    unitScoreLaw.prod (unitScoreLaw.restrict (Ici (diagonalPairAt d j).2))
private instance {n : ℕ} (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool) :
    IsFiniteMeasure (forwardScoreMaskInactiveColumnLaw d flag) := by
  unfold forwardScoreMaskInactiveColumnLaw
  infer_instance
theorem measurePreserving_forwardInactiveColumnsEquiv {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) :
    MeasurePreserving (forwardInactiveColumnsEquiv flag) (forwardScoreMaskInactiveLaw d flag)
      (forwardScoreMaskInactiveColumnLaw d flag) := by
  unfold forwardScoreMaskInactiveLaw forwardScoreMaskInactiveColumnLaw
  convert measurePreserving_forwardInactiveColumnsEquiv_pi flag
    (fun q ↦ unitScoreLaw.prod (unitScoreLaw.restrict (Ici (diagonalPairAt d q.val.val.2).2)))
    using 2
  funext j
  congr 1
  funext q
  rw [q.property]
private noncomputable def normalizedForwardInactiveColumnLaw {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) (j : Fin n) :
    Measure (ForwardInactiveColumnIndex flag j → ℝ × ℝ) :=
  Measure.pi fun _ : ForwardInactiveColumnIndex flag j ↦
    unitScoreLaw.prod (inactiveFemaleScoreLaw (diagonalPairAt d j).2)
theorem normalizedForwardInactiveColumnLaw_isProbabilityMeasure {n : ℕ}
    (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool) (j : Fin n)
    (hy0 : 0 ≤ (diagonalPairAt d j).2) (hy1 : (diagonalPairAt d j).2 < 1) :
    IsProbabilityMeasure (normalizedForwardInactiveColumnLaw d flag j) := by
  have := inactiveFemaleScoreLaw_isProbabilityMeasure hy0 hy1
  unfold normalizedForwardInactiveColumnLaw
  infer_instance
private theorem pi_smul_finite {ι : Type*} [Fintype ι] {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] (ν : ∀ i, Measure (X i))
    [∀ i, IsFiniteMeasure (ν i)] (a : ι → ℝ≥0∞) (ha : ∀ i, a i ≠ ⊤) :
    (Measure.pi fun i ↦ a i • ν i) = (∏ i, a i) • Measure.pi ν := by
  have (i : ι) : IsFiniteMeasure (a i • ν i) := Measure.smul_finite (ν i) (ha i)
  refine Measure.pi_eq fun s _ ↦ ?_
  simp only [Measure.smul_apply, smul_eq_mul, Measure.pi_pi, Finset.prod_mul_distrib]
theorem forwardScoreMaskInactiveColumnLaw_eq_smul {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool)
    (hy0 : ∀ j, 0 ≤ (diagonalPairAt d j).2) (hy1 : ∀ j, (diagonalPairAt d j).2 < 1) :
    forwardScoreMaskInactiveColumnLaw d flag =
      (∏ j, (ENNReal.ofReal (1 - (diagonalPairAt d j).2)) ^
        Fintype.card (ForwardInactiveColumnIndex flag j)) •
        Measure.pi (normalizedForwardInactiveColumnLaw d flag) := by
  let a (j : Fin n) := ENNReal.ofReal (1 - (diagonalPairAt d j).2)
  have (j : Fin n) : IsProbabilityMeasure (normalizedForwardInactiveColumnLaw d flag j) :=
    normalizedForwardInactiveColumnLaw_isProbabilityMeasure d flag j (hy0 j) (hy1 j)
  have hcolumn (j : Fin n) :
      (Measure.pi fun _ : ForwardInactiveColumnIndex flag j ↦
        unitScoreLaw.prod (unitScoreLaw.restrict (Ici (diagonalPairAt d j).2))) =
        a j ^ Fintype.card (ForwardInactiveColumnIndex flag j) •
          normalizedForwardInactiveColumnLaw d flag j := by
    let y := (diagonalPairAt d j).2
    have := inactiveFemaleScoreLaw_isProbabilityMeasure (hy0 j) (hy1 j)
    have hcell : unitScoreLaw.prod (unitScoreLaw.restrict (Ici y)) =
        a j • (unitScoreLaw.prod (inactiveFemaleScoreLaw y)) := by
      rw [inactiveFemaleScoreLaw, Measure.prod_smul_right, smul_smul,
        unitScoreLaw_Ici_of_mem_Icc ⟨hy0 j, (hy1 j).le⟩]
      change _ = (a j * (a j)⁻¹) • _
      rw [ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.mpr (sub_pos.mpr (hy1 j))).ne'
        ENNReal.ofReal_ne_top, one_smul]
    change (Measure.pi fun _ : ForwardInactiveColumnIndex flag j ↦
      unitScoreLaw.prod (unitScoreLaw.restrict (Ici y))) = _
    simp_rw [hcell]
    simpa only [Finset.prod_const, Finset.card_univ, normalizedForwardInactiveColumnLaw] using
      pi_smul_finite (fun _ : ForwardInactiveColumnIndex flag j ↦
        unitScoreLaw.prod (inactiveFemaleScoreLaw y)) (fun _ ↦ a j)
        (fun _ ↦ ENNReal.ofReal_ne_top)
  unfold forwardScoreMaskInactiveColumnLaw
  simp_rw [hcolumn]
  exact pi_smul_finite (normalizedForwardInactiveColumnLaw d flag) _
    (fun j ↦ ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
end MarkedLP
end

-- PivotReverseRowLaw
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace MarkedLP
variable {ι : Type*}
private def reverseSuccessorPairEvent (y x : ℝ) (v : ι → ℝ) :
    Set ((ℝ × ℝ) × (ι → ℝ × ℝ)) :=
  {z | y < z.1.2 ∧ z.1.1 < x ∧ ∀ j, ¬((z.2 j).2 < z.1.2 ∧ (z.2 j).1 < v j)}
private def reverseSuccessorColumnEvent [DecidableEq ι] (y : ℝ) (v : ι → ℝ) (i : ι) :
    Set (ι → ℝ × ℝ) :=
  (fun z : ι → ℝ × ℝ ↦ (z i, fun j : {j : ι // j ≠ i} ↦ z j.val)) ⁻¹'
    reverseSuccessorPairEvent y (v i) (fun j : {j : ι // j ≠ i} ↦ v j.val)
end MarkedLP
end

-- ReverseSuccessorRotation
section
open StableMarriage
namespace MarkedLP
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
end MarkedLP
end

-- PivotReverseScoreSuccessor
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace MarkedLP
theorem exists_reverseSuccessorColumnEvent_of_isSuccessor {n : ℕ}
    (μ : Matching n) (x : ScoreProfile n) (flag : OffDiagonalCellIndex n → Bool)
    (hs : IsScoreStable x μ) (ht : ∀ r, Function.Injective (x r))
    (hmask : (splitScorePairs μ x).2 ∈ forwardScoreMaskEvent (splitScorePairs μ x).1 flag)
    (i j : Fin n) (hji : j ≠ i)
    (hj : IsSuccessor (swapProfile (profileOfScores x)) μ.symm (μ i) j) :
    ∃ q : ForwardInactiveColumnIndex flag i, q.val.val.val.1 = j ∧
      (forwardInactiveColumnsEquiv flag (fun q ↦ (splitScorePairs μ x).2 q.val)) i ∈
        reverseSuccessorColumnEvent (diagonalPairAt (splitScorePairs μ x).1 i).2
          (fun k ↦ (diagonalPairAt (splitScorePairs μ x).1 k.val.val.val.1).1) q := by
  let d := (splitScorePairs μ x).1
  let z := (splitScorePairs μ x).2
  let a : OffDiagonalCellIndex n := ⟨(j, i), hji⟩
  have hmale (m : Fin n) (w w' : Fin n) :
      (profileOfScores x).manRank m w < (profileOfScores x).manRank m w' ↔
        x (.inl m) w < x (.inl m) w' := rankPermutation_lt_iff (ht (.inl m)) w w'
  have hfemale (m m' : Fin n) :
      (profileOfScores x).womanRank (μ i) m < (profileOfScores x).womanRank (μ i) m' ↔
        x (.inr (μ i)) m < x (.inr (μ i)) m' := rankPermutation_lt_iff (ht (.inr (μ i))) m m'
  have hmalej : x (.inl j) (μ i) < x (.inl j) (μ j) :=
    (hmale _ _ _).mp (by simpa only [swapProfile, Equiv.symm_symm] using hj.eligible.2)
  have hfemalej : x (.inr (μ i)) i < x (.inr (μ i)) j :=
    (hfemale _ _).mp (by simpa only [swapProfile, Equiv.symm_apply_apply] using hj.eligible.1)
  have ha : flag a ≠ true := by
    intro h
    have hh := mem_pi.mp hmask a (mem_univ _)
    change z a ∈ forwardScoreCellFlagEvent (diagonalPairAt d j).1
      (diagonalPairAt d i).2 (flag a) at hh
    dsimp only [z, d] at hh
    rw [h, forwardScoreCellFlagEvent, if_pos rfl, forwardEligibleScoreCell,
      splitScorePairs_offDiagonal_apply, diagonalPairAt_splitScorePairs] at hh
    exact hmalej.not_gt (mem_prod.mp hh).1
  let q : ForwardInactiveColumnIndex flag i := ⟨⟨a, ha⟩, rfl⟩
  let col := (forwardInactiveColumnsEquiv flag (fun k ↦ z k.val)) i
  have hcell (k : ForwardInactiveColumnIndex flag i) :
      col k = (x (.inl k.val.val.val.1) (μ i), x (.inr (μ i)) k.val.val.val.1) := by
    change (splitScorePairs μ x).2 k.val.val = _
    rw [splitScorePairs_offDiagonal_apply, k.property]
  refine ⟨q, rfl, ?_⟩
  change col ∈ reverseSuccessorColumnEvent (diagonalPairAt d i).2
    (fun k ↦ (diagonalPairAt d k.val.val.val.1).1) q
  change (diagonalPairAt d i).2 < (col q).2 ∧
    (col q).1 < (diagonalPairAt d j).1 ∧
    ∀ k : {k : ForwardInactiveColumnIndex flag i // k ≠ q},
      ¬ ((col k.val).2 < (col q).2 ∧
        (col k.val).1 < (diagonalPairAt d k.val.val.val.val.1).1)
  simp only [hcell, d, diagonalPairAt_splitScorePairs, q, a]
  refine ⟨hfemalej, hmalej, fun k h ↦ ?_⟩
  let m := k.val.val.val.val.1
  have hne : m ≠ i := fun hm ↦ k.val.val.val.property (hm.trans k.val.property.symm)
  have hbetter : x (.inl m) (μ i) < x (.inl m) (μ m) := h.2
  have hnotbetter : ¬ x (.inr (μ i)) m < x (.inr (μ i)) i :=
    fun hh ↦ hs m (μ i) ⟨μ.injective.ne hne, hbetter,
      by simpa only [Equiv.symm_apply_apply] using hh⟩
  have hww : x (.inr (μ i)) i < x (.inr (μ i)) m :=
    lt_of_le_of_ne (le_of_not_gt hnotbetter) ((ht (.inr (μ i))).ne hne.symm)
  have hel : IsEligibleSuccessor (swapProfile (profileOfScores x)) μ.symm (μ i) m := by
    simpa only [IsEligibleSuccessor, swapProfile, Equiv.symm_apply_apply, Equiv.symm_symm] using
      And.intro ((hfemale _ _).mpr hww) ((hmale _ _ _).mpr hbetter)
  exact (not_lt_of_ge (hj.min_rank m hel)) ((hfemale _ _).mpr h.1)
private def forwardInactiveReverseArcEvent {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) (i j : Fin n) :
    Set (ForwardInactiveColumnIndex flag i → ℝ × ℝ) :=
  ⋃ q : {q : ForwardInactiveColumnIndex flag i // q.val.val.val.1 = j},
    reverseSuccessorColumnEvent (diagonalPairAt d i).2
      (fun k ↦ (diagonalPairAt d k.val.val.val.1).1) q.val
theorem isSuccessor_swapProfile_iff_forwardInactiveReverseArcEvent {n : ℕ}
    (μ : Matching n) (x : ScoreProfile n) (flag : OffDiagonalCellIndex n → Bool)
    (hs : IsScoreStable x μ) (ht : ∀ r, Function.Injective (x r))
    (hmask : (splitScorePairs μ x).2 ∈ forwardScoreMaskEvent (splitScorePairs μ x).1 flag)
    (i j : Fin n) (hji : j ≠ i) :
    IsSuccessor (swapProfile (profileOfScores x)) μ.symm (μ i) j ↔
      (forwardInactiveColumnsEquiv flag (fun q ↦ (splitScorePairs μ x).2 q.val)) i ∈
        forwardInactiveReverseArcEvent (splitScorePairs μ x).1 flag i j := by
  constructor
  · intro hj
    obtain ⟨q, hq, htest⟩ := exists_reverseSuccessorColumnEvent_of_isSuccessor
      μ x flag hs ht hmask i j hji hj
    exact mem_iUnion.mpr ⟨⟨q, hq⟩, htest⟩
  · intro h
    obtain ⟨q, hq⟩ := mem_iUnion.mp h
    let d := (splitScorePairs μ x).1
    let z := (splitScorePairs μ x).2
    let col := (forwardInactiveColumnsEquiv flag (fun k ↦ z k.val)) i
    have hcell (k : ForwardInactiveColumnIndex flag i) :
        col k = (x (.inl k.val.val.val.1) (μ i), x (.inr (μ i)) k.val.val.val.1) := by
      change (splitScorePairs μ x).2 k.val.val = _
      rw [splitScorePairs_offDiagonal_apply, k.property]
    change (diagonalPairAt d i).2 < (col q.val).2 ∧
      (col q.val).1 < (diagonalPairAt d q.val.val.val.val.1).1 ∧
      ∀ k : {k : ForwardInactiveColumnIndex flag i // k ≠ q.val},
        ¬ ((col k.val).2 < (col q.val).2 ∧
          (col k.val).1 < (diagonalPairAt d k.val.val.val.val.1).1) at hq
    simp only [hcell, d, diagonalPairAt_splitScorePairs, q.property] at hq
    have hf (a b : Fin n) : (profileOfScores x).womanRank (μ i) a <
        (profileOfScores x).womanRank (μ i) b ↔ x (.inr (μ i)) a < x (.inr (μ i)) b :=
      rankPermutation_lt_iff (ht (.inr (μ i))) a b
    have hm (a : Fin n) : (profileOfScores x).manRank a (μ i) <
        (profileOfScores x).manRank a (μ a) ↔ x (.inl a) (μ i) < x (.inl a) (μ a) :=
      rankPermutation_lt_iff (ht (.inl a)) _ _
    refine ⟨?_, ?_⟩
    · simpa only [IsEligibleSuccessor, swapProfile, Equiv.symm_symm, Equiv.symm_apply_apply] using
        And.intro ((hf i j).mpr hq.1) ((hm j).mpr hq.2.1)
    · intro m hel
      change (profileOfScores x).womanRank (μ i) j ≤ (profileOfScores x).womanRank (μ i) m
      apply le_of_not_gt
      intro hlt
      have hsmall := (hf m j).mp hlt
      have hmale : x (.inl m) (μ i) < x (.inl m) (μ m) :=
        (hm m).mp (by simpa only [swapProfile, Equiv.symm_symm] using hel.2)
      have hmi : m ≠ i := fun e ↦ (lt_irrefl _ (e ▸ hmale))
      let a : OffDiagonalCellIndex n := ⟨(m, i), hmi⟩
      have ha : flag a ≠ true := by
        intro he
        have hh := mem_pi.mp hmask a (mem_univ _)
        change (splitScorePairs μ x).2 a ∈ forwardScoreCellFlagEvent
          (diagonalPairAt (splitScorePairs μ x).1 m).1
          (diagonalPairAt (splitScorePairs μ x).1 i).2 (flag a) at hh
        rw [he, forwardScoreCellFlagEvent, if_pos rfl, forwardEligibleScoreCell,
          splitScorePairs_offDiagonal_apply, diagonalPairAt_splitScorePairs] at hh
        exact hmale.not_gt (mem_prod.mp hh).1
      let k : ForwardInactiveColumnIndex flag i := ⟨⟨a, ha⟩, rfl⟩
      have hk : k ≠ q.val := fun he ↦ hsmall.ne
        (congrArg (fun b : ForwardInactiveColumnIndex flag i ↦
          x (.inr (μ i)) b.val.val.val.1) he |>.trans (congrArg (x (.inr (μ i))) q.property))
      exact hq.2.2 ⟨k, hk⟩ ⟨hsmall, hmale⟩
end MarkedLP
end

-- FinitePrerequisites
section
namespace MarkedLP
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
end MarkedLP
end

-- RotationDiamond
section
open StableMarriage
namespace MarkedLP
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
end MarkedLP
end

-- ManOptimal
section
open StableMarriage
open scoped BigOperators
namespace MarkedLP
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
end MarkedLP
end

-- RotationCycle
section
namespace MarkedLP
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
end MarkedLP
end

-- TargetSuccessor
section
open StableMarriage
namespace MarkedLP
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
end MarkedLP
end

-- RotationReachability
section
open scoped BigOperators
open StableMarriage
namespace MarkedLP
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
end MarkedLP
end

-- RotationLabels
section
open StableMarriage
namespace MarkedLP
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
end MarkedLP
end

-- RotationPathIndependence
section
open StableMarriage
namespace MarkedLP
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
end MarkedLP
end

-- RotationTrace
section
open StableMarriage
namespace MarkedLP
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
end MarkedLP
end

-- RotationIdeals
section
open StableMarriage
namespace MarkedLP
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
end MarkedLP
end

-- CoexposedRotations
section
open StableMarriage
namespace MarkedLP
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
end MarkedLP
end

-- CoexposureCycleMoment
section
open StableMarriage MeasureTheory
open scoped BigOperators ENNReal
namespace MarkedLP
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
end MarkedLP
end

-- PivotReverseMaskJointLaw
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace MarkedLP
private noncomputable def forwardMaskRevealLaw {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) (A : Set (ForwardActiveCellIndex flag → ℝ)) :
    Measure (OffDiagonalScorePairs n) :=
  (((offDiagonalScoreLaw n).restrict (offDiagonalNonblocking d)).restrict
    (forwardScoreMaskEvent d flag)).restrict
      ((Prod.fst ∘ forwardScoreMaskRevealAndInactive flag) ⁻¹' A)
end MarkedLP
end

-- PivotReverseMaskLowerMoment
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace MarkedLP
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
end MarkedLP
end

-- PivotReverseCompetitorMass
section
open StableMarriage
open scoped BigOperators ENNReal
namespace MarkedLP
private noncomputable def forwardMaskOmittedMass {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) (j : Fin n) : ℝ :=
  ∑ i : {i : Fin n // i ≠ j}, if flag ⟨(i.val, j), i.property⟩ then
    (diagonalPairAt d i.val).1 else 0
end MarkedLP
end

-- PivotForwardMaskProbability
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace MarkedLP
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
end MarkedLP
end

-- PivotForwardRevealRectangle
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace MarkedLP
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
end MarkedLP
end

-- PivotForwardPivotReadout
section
open MeasureTheory Set StableMarriage
namespace MarkedLP
private noncomputable def forwardPivotIncrement {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) (ρ : Matching n)
    (a : ForwardRevealedMaleScores flag) (m : Fin n) : ℝ :=
  if hm : ρ m ≠ m then
    let q : OffDiagonalCellIndex n := ⟨(m, ρ m), hm.symm⟩
    if hq : flag q = true then a ⟨q, hq⟩ - (diagonalPairAt d m).1 else 0
  else 0
end MarkedLP
end

-- SingletonIdealAnchor
section
namespace MarkedLP
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
end MarkedLP
end

-- SingletonRotationAnchor
section
open StableMarriage
namespace MarkedLP
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
theorem eq_singletonRotationAnchor_iff (hopt : IsManOptimal p μ₀) (r : Rotation p μ₀)
    (ν : {ν : Matching n // IsStable p ν}) :
    ν = singletonRotationAnchor hopt r ↔
      ∀ s : Rotation p μ₀, s.IsExposedAt ν.val ↔ s = r := by
  let e := stableMatchingEquivRotationIdeals hopt
  change ν = e.symm (singletonAnchorIdeal r) ↔ _
  rw [← e.apply_eq_iff_eq, e.apply_symm_apply, lowerSet_eq_singletonAnchorIdeal_iff]
  simp only [Rotation.isExposedAt_iff_minimal hopt ν.property]
  rfl
end MarkedLP
end

-- UndoableRotations
section
open StableMarriage
namespace MarkedLP
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
end MarkedLP
end

-- ReverseRotationIdeals
section
open StableMarriage
namespace MarkedLP
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
end MarkedLP
end

-- PivotCrossBlocker
section
open StableMarriage
namespace MarkedLP
variable {n : ℕ} {p : Profile n} {A N : Matching n} {ρ : Equiv.Perm (Fin n)}
private def IsPivotCrossBlocker (p : Profile n) (A N : Matching n) (ρ : Equiv.Perm (Fin n))
    (m w : Fin n) : Prop :=
  ρ m ≠ m ∧ N.symm w ≠ A.symm w ∧
    p.manRank m w < p.manRank m (A (ρ m)) ∧ p.womanRank w m < p.womanRank w (N.symm w)
theorem rotationLabel_eq_of_fixed_on_cycle
    (hfixed : ∀ m, ρ m ≠ m → N m = A m) :
    rotationLabel N ρ = rotationLabel A ρ := by
  unfold rotationLabel
  congr 1
  funext m
  by_cases hm : ρ m = m
  · simp [hm]
  · simp [hm, hfixed m hm]
private theorem IsPivotCrossBlocker.old_partner_ne {m w : Fin n}
    (h : IsPivotCrossBlocker p A N ρ m w) (hfixed : ∀ m, ρ m ≠ m → N m = A m) :
    A m ≠ w := by
  rintro rfl
  apply h.2.1
  rw [← hfixed m h.1, N.symm_apply_apply, hfixed m h.1, A.symm_apply_apply]
theorem IsPivotCrossBlocker.manRank_old_lt {m w : Fin n}
    (h : IsPivotCrossBlocker p A N ρ m w) (hN : IsStable p N)
    (hfixed : ∀ m, ρ m ≠ m → N m = A m) :
    p.manRank m (A m) < p.manRank m w := by
  have hne := h.old_partner_ne hfixed
  have hnot : ¬ p.manRank m w < p.manRank m (A m) := fun hlt ↦
    hN m w ⟨(hfixed m h.1).trans_ne hne, (hfixed m h.1).symm ▸ hlt, h.2.2.2⟩
  exact lt_of_le_of_ne (le_of_not_gt hnot) (fun heq ↦ hne ((p.manRank m).injective heq))
theorem IsPivotCrossBlocker.womanRank_old_lt {m w : Fin n}
    (h : IsPivotCrossBlocker p A N ρ m w) (hρ : IsExposedRotation p A ρ)
    (hN : IsStable p N) (hfixed : ∀ m, ρ m ≠ m → N m = A m) :
    p.womanRank w (A.symm w) < p.womanRank w m := by
  have hnot : ¬ p.womanRank w m < p.womanRank w (A.symm w) := fun hlt ↦
    (not_lt_of_ge ((hρ.successor m h.1).min_rank w ⟨h.manRank_old_lt hN hfixed, hlt⟩)) h.2.2.1
  apply lt_of_le_of_ne (le_of_not_gt hnot)
  intro heq
  have hh := (p.womanRank w).injective heq
  exact h.old_partner_ne hfixed ((congrArg A hh).symm.trans (A.apply_symm_apply w))
theorem isExposedRotation_iff_no_pivotCrossBlocker
    (hρ : IsExposedRotation p A ρ) (hN : IsStable p N)
    (hfixed : ∀ m, ρ m ≠ m → N m = A m) :
    IsExposedRotation p N ρ ↔ ∀ m w, ¬ IsPivotCrossBlocker p A N ρ m w := by
  constructor
  · intro he m w h
    have ht := hfixed (ρ m) (ρ.injective.ne h.1)
    have hman : p.manRank m (N m) < p.manRank m w := by
      rw [hfixed m h.1]
      exact h.manRank_old_lt hN hfixed
    have hle := (he.successor m h.1).min_rank w ⟨hman, h.2.2.2⟩
    rw [ht] at hle
    exact (not_lt_of_ge hle) h.2.2.1
  · intro h
    refine ⟨hρ.isCycle, fun m hm ↦ ?_⟩
    have hold := hfixed m hm
    have ht := hfixed (ρ m) (ρ.injective.ne hm)
    have hs := hρ.successor m hm
    constructor
    · constructor
      · simpa only [hold, ht] using hs.eligible.1
      · have hinv := N.symm_apply_apply (ρ m)
        rw [ht] at hinv
        simpa only [ht, hinv, Equiv.symm_apply_apply] using hs.eligible.2
    · intro w hw
      by_cases hw' : N.symm w = A.symm w
      · have hwA : IsEligibleSuccessor p A m w :=
          ⟨by simpa only [hold] using hw.1, by simpa only [hw'] using hw.2⟩
        simpa only [ht] using hs.min_rank w hwA
      · apply le_of_not_gt
        intro hlt
        exact h m w ⟨hm, hw', by simpa only [ht] using hlt, hw.2⟩
private def IsPivotCrossRectangle (x : ScoreProfile n) (A N : Matching n)
    (ρ : Equiv.Perm (Fin n)) (m w : Fin n) : Prop :=
  ρ m ≠ m ∧ N.symm w ≠ A.symm w ∧
    x (.inl m) (A m) < x (.inl m) w ∧ x (.inl m) w < x (.inl m) (A (ρ m)) ∧
    x (.inr w) (A.symm w) < x (.inr w) m ∧ x (.inr w) m < x (.inr w) (N.symm w)
theorem isPivotCrossBlocker_iff_score_rectangle {x : ScoreProfile n}
    (hx : ∀ i, Function.Injective (x i))
    (hρ : IsExposedRotation (profileOfScores x) A ρ) (hN : IsStable (profileOfScores x) N)
    (hfixed : ∀ m, ρ m ≠ m → N m = A m) (m w : Fin n) :
    IsPivotCrossBlocker (profileOfScores x) A N ρ m w ↔ IsPivotCrossRectangle x A N ρ m w := by
  let hm := rankPermutation_lt_iff (hx (.inl m))
  let hw := rankPermutation_lt_iff (hx (.inr w))
  exact ⟨fun h ↦ ⟨h.1, h.2.1, (hm _ _).mp (h.manRank_old_lt hN hfixed),
    (hm _ _).mp h.2.2.1, (hw _ _).mp (h.womanRank_old_lt hρ hN hfixed), (hw _ _).mp h.2.2.2⟩,
    fun ⟨ha, hb, _, hc, _, hd⟩ ↦ ⟨ha, hb, (hm _ _).mpr hc, (hw _ _).mpr hd⟩⟩
theorem isExposedRotation_profileOfScores_iff_no_pivotCrossRectangle {x : ScoreProfile n}
    (hx : ∀ i, Function.Injective (x i))
    (hρ : IsExposedRotation (profileOfScores x) A ρ) (hN : IsScoreStable x N)
    (hfixed : ∀ m, ρ m ≠ m → N m = A m) :
    IsExposedRotation (profileOfScores x) N ρ ↔
      ∀ m w, ¬ IsPivotCrossRectangle x A N ρ m w := by
  have hstable := (isStable_profileOfScores_iff hx N).mpr hN
  simpa only [isPivotCrossBlocker_iff_score_rectangle hx hρ hstable hfixed] using
    isExposedRotation_iff_no_pivotCrossBlocker hρ hstable hfixed
end MarkedLP
end

-- PivotReversePermutationCompatibility
section
open StableMarriage
namespace MarkedLP
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
theorem undoReverseRotation_apply_of_not_mem_support {m : Fin n} (hm : μ m ∉ σ.support) :
    undoReverseRotation μ σ m = μ m :=
  (undoReverseRotation μ σ).symm.injective <| calc
    (undoReverseRotation μ σ).symm (undoReverseRotation μ σ m) = m :=
      (undoReverseRotation μ σ).symm_apply_apply m
    _ = μ.symm (μ m) := (μ.symm_apply_apply m).symm
    _ = (undoReverseRotation μ σ).symm (μ m) := by
      rw [undoReverseRotation_symm_apply, Equiv.Perm.notMem_support.mp hm]
end MarkedLP
end

-- UndoMaximalSubset
section
open StableMarriage
namespace MarkedLP
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
end MarkedLP
end

-- PivotIdealExposure
section
open StableMarriage
namespace MarkedLP
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
end MarkedLP
end

-- ReverseRotationPersistence
section
open StableMarriage
namespace MarkedLP
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
end MarkedLP
end

-- RotationUndoSequences
section
open StableMarriage
namespace MarkedLP
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
end MarkedLP
end

-- PivotIncidenceCounting
section
open StableMarriage
open scoped BigOperators
namespace MarkedLP
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
end MarkedLP
end

-- PivotReversePermutationDecoration
section
open StableMarriage
open scoped BigOperators
namespace MarkedLP
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
theorem compatibleReversePermutationToDecoration_matching (hopt : IsManOptimal p μ₀)
    (K : ℕ) (r : Rotation p μ₀) (σ : CompatibleReversePermutation hopt K r) :
    (compatibleReversePermutationToDecoration hopt K r σ).matching.val =
      undoReverseRotation (singletonRotationAnchor hopt r).val σ.val :=
  undoMaximalSubsetEmbedding_realizedReverseRemovedLabels hopt
    (singletonRotationAnchor hopt r).property σ.property.1
end MarkedLP
end

-- PivotCompatibleLowerMoment
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace MarkedLP
private noncomputable def compatibleReversePermutations {n : ℕ} (S : Finset (Matching n))
    (p : Profile n) (μ ρ : Matching n) : Finset (Matching n) := by
  classical
  exact S.filter fun σ ↦ RealizesSuccessorPermutation (swapProfile p) μ.symm σ ∧
    IsExposedRotation p (undoReverseRotation μ σ) ρ
theorem mem_compatibleReversePermutations {n : ℕ} {S : Finset (Matching n)}
    {p : Profile n} {μ ρ σ : Matching n} : σ ∈ compatibleReversePermutations S p μ ρ ↔
    σ ∈ S ∧ RealizesSuccessorPermutation (swapProfile p) μ.symm σ ∧
      IsExposedRotation p (undoReverseRotation μ σ) ρ := by
  classical
  simp [compatibleReversePermutations]
private noncomputable def compatibleReverseSupportFamily {n : ℕ} (μ ρ : Matching n)
    (flag : OffDiagonalCellIndex n → Bool) (k : ℕ) (p : Profile n) : Finset (Matching n) :=
  compatibleReversePermutations
    (goodReverseSupportPermutations k (ρ.support.map μ.toEmbedding)
      (forwardMaskForbiddenTargets μ flag)) p μ ρ
end MarkedLP
end

-- PivotReverseIncrementFilter
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace MarkedLP
private def reverseScoreIncrement {n : ℕ} (x : ScoreProfile n) (μ : Matching n)
    (w j : Fin n) : ℝ := x (.inr w) j - x (.inr w) (μ.symm w)
theorem measurable_reverseScoreIncrement {n : ℕ} (μ : Matching n) (w j : Fin n) :
    Measurable (fun x : ScoreProfile n ↦ reverseScoreIncrement x μ w j) := by
  have hrow : Measurable (fun x : ScoreProfile n ↦ x (.inr w)) := measurable_pi_apply _
  exact ((measurable_pi_apply j).comp hrow).sub ((measurable_pi_apply (μ.symm w)).comp hrow)
private noncomputable def reverseIncrementCutoff (n : ℕ) (X : ℝ) : ℝ := 16 * Real.log (n : ℝ) / X
end MarkedLP
end

-- PivotReverseFilteredCount
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace MarkedLP
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
end MarkedLP
end

-- PivotReverseMaskMoment
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace MarkedLP
theorem ae_diagonal_ae_injective_scoreRows {n : ℕ} (μ : Matching n) :
    ∀ᵐ d ∂diagonalScoreLaw n, ∀ᵐ z ∂offDiagonalScoreLaw n,
      ∀ r, Function.Injective ((splitScorePairs μ).symm (d, z) r) :=
  Measure.ae_ae_of_ae_prod
    (((measurePreserving_splitScorePairs μ).symm).quasiMeasurePreserving.ae (ae_injective_rows n))
end MarkedLP
end

-- PivotScoreLock
section
open StableMarriage
namespace MarkedLP
variable {n : ℕ} {p : Profile n} {μ₀ μ ν : Matching n} {r : Rotation p μ₀}
theorem RotationSequence.womanRank_end_le {rs : List (Equiv.Perm (Fin n))}
    (hpath : RotationSequence p μ rs ν) (j : Fin n) :
    p.womanRank j (ν.symm j) ≤ p.womanRank j (μ.symm j) := by
  induction hpath with
  | nil => exact le_rfl
  | cons _ hρ _ ih => exact ih.trans (hρ.womanRank_eliminate_le j)
end MarkedLP
end

-- PivotForwardExposureReveal
section
open MeasureTheory Set StableMarriage
namespace MarkedLP
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
end MarkedLP
end

-- PivotEligibleRevealControls
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace MarkedLP
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
end MarkedLP
end

-- PivotSpouseBandMask
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace MarkedLP
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
end MarkedLP
end

-- PivotForwardRowDeficit
section
open Filter MeasureTheory Set
open scoped BigOperators ENNReal
namespace MarkedLP
private noncomputable def forwardSpouseWeight {n : ℕ} (d : DiagonalScorePairs n) (i : Fin n) : ℝ :=
  (diagonalPairAt d i).2 / ∑ j, (diagonalPairAt d j).2
end MarkedLP
end

-- PivotForwardForest
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace MarkedLP
private def IsSoleForwardExposedRotation {n : ℕ} (p : Profile n) (μ σ : Matching n) : Prop :=
  IsExposedRotation p μ σ ∧ ∀ τ, IsExposedRotation p μ τ → τ = σ
end MarkedLP
end

-- PivotLocalEligibility
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace MarkedLP
private structure LocalPivotGeometry {n : ℕ} (b A B : ℝ) (μ ρ : Matching n)
    (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool) : Prop where
  base : d ∈ pivotBaseDiagonalBand n
  lower_band : (n : ℝ) ^ (1 / 10 : ℝ) ≤ pivotDiagonalFemaleTotal d
  length_lower : b * Real.sqrt (n : ℝ) ≤ (ρ.support.card : ℝ)
  length_upper : (ρ.support.card : ℝ) ≤ A * Real.sqrt (n : ℝ)
  male_squares : (∑ j, (reverseSpouseWeights μ d j) ^ 2) ≤
    ENNReal.ofReal (24 / (n : ℝ))
  female_squares : (∑ i, (forwardSpouseWeight d i) ^ 2) ≤ 24 / (n : ℝ)
  omitted_score : ∀ j, forwardMaskOmittedMass d flag j ≤
    (n : ℝ) ^ (-11 / 20 : ℝ) * reverseDiagonalMaleTotal d
  pivot_score : (∑ i ∈ ρ.support, (diagonalPairAt d i).1) ≤
    (B / Real.sqrt (n : ℝ)) * reverseDiagonalMaleTotal d
private noncomputable def localPivotIncrementCap {n : ℕ} (B : ℝ) (d : DiagonalScorePairs n) : ℝ :=
  B * Real.sqrt (n : ℝ) / pivotDiagonalFemaleTotal d
private def IsLocallyEligiblePivot {n : ℕ} (b A B : ℝ) (x : ScoreProfile n)
    (μ ρ : Matching n) : Prop :=
  let z := splitScorePairs μ x
  let flag := forwardMaskOfScores z.1 z.2
  LocalPivotGeometry b A B μ ρ z.1 flag ∧
    (forwardRevealWithColumns flag z.2).1 ∈
      eligiblePivotRevealSet z.1 flag ρ (localPivotIncrementCap B z.1)
theorem isLocallyEligiblePivot_reconstruct_iff {n : ℕ} {b A B : ℝ}
    (μ ρ : Matching n) (d : DiagonalScorePairs n) (z : OffDiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) (hmask : z ∈ forwardScoreMaskEvent d flag) :
    IsLocallyEligiblePivot b A B ((splitScorePairs μ).symm (d, z)) μ ρ ↔
      LocalPivotGeometry b A B μ ρ d flag ∧
        (forwardRevealWithColumns flag z).1 ∈
          eligiblePivotRevealSet d flag ρ (localPivotIncrementCap B d) := by
  have hflag := (forwardMaskOfScores_eq_iff d z flag).mpr hmask
  unfold IsLocallyEligiblePivot
  rw [MeasurableEquiv.apply_symm_apply]
  dsimp only
  rw [hflag]
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
theorem reverseDiagonalMaleTotal_splitScorePairs {n : ℕ}
    (μ : Matching n) (x : ScoreProfile n) :
    reverseDiagonalMaleTotal (splitScorePairs μ x).1 = maleSpouseTotal x μ :=
  Finset.sum_congr rfl fun i _ ↦ congrArg Prod.fst (diagonalPairAt_splitScorePairs μ x i)
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
    MeasurableSet {d : DiagonalScorePairs n | LocalPivotGeometry b A B μ ρ d flag} := by
  have hmale (j : Fin n) : Measurable (fun d : DiagonalScorePairs n ↦ reverseSpouseWeights μ d j) :=
    ENNReal.measurable_ofReal.comp ((measurable_diagonalMaleScore (μ.symm j)).div
      (measurable_reverseDiagonalMaleTotal n))
  have hfemale (i : Fin n) : Measurable (fun d : DiagonalScorePairs n ↦ forwardSpouseWeight d i) :=
    (measurable_diagonalFemaleScore i).div (measurable_pivotDiagonalFemaleTotal n)
  have homit (j : Fin n) : Measurable (fun d : DiagonalScorePairs n ↦
      forwardMaskOmittedMass d flag j) := by
    unfold forwardMaskOmittedMass
    refine Finset.measurable_sum _ fun i _ ↦ ?_
    split
    · exact measurable_diagonalMaleScore i.val
    · exact measurable_const
  have hEq : {d : DiagonalScorePairs n | LocalPivotGeometry b A B μ ρ d flag} =
      {d | d ∈ pivotBaseDiagonalBand n ∧
        (n : ℝ) ^ (1 / 10 : ℝ) ≤ pivotDiagonalFemaleTotal d ∧
        b * Real.sqrt (n : ℝ) ≤ (ρ.support.card : ℝ) ∧
        (ρ.support.card : ℝ) ≤ A * Real.sqrt (n : ℝ) ∧
        (∑ j, (reverseSpouseWeights μ d j) ^ 2) ≤ ENNReal.ofReal (24 / (n : ℝ)) ∧
        (∑ i, (forwardSpouseWeight d i) ^ 2) ≤ 24 / (n : ℝ) ∧
        (∀ j, forwardMaskOmittedMass d flag j ≤
          (n : ℝ) ^ (-11 / 20 : ℝ) * reverseDiagonalMaleTotal d) ∧
        (∑ i ∈ ρ.support, (diagonalPairAt d i).1) ≤
          (B / Real.sqrt (n : ℝ)) * reverseDiagonalMaleTotal d} := by
    ext d
    exact ⟨fun h ↦ ⟨h.base, h.lower_band, h.length_lower, h.length_upper, h.male_squares,
      h.female_squares, h.omitted_score, h.pivot_score⟩,
      fun ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ ↦ ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩⟩
  rw [hEq]
  simp only [ofPred_and, ofPred_forall, Set.ofPred_mem_eq]
  exact (measurableSet_pivotBaseDiagonalBand n).inter <|
    (measurableSet_le measurable_const (measurable_pivotDiagonalFemaleTotal n)).inter <|
    (MeasurableSet.const _).inter <| (MeasurableSet.const _).inter <|
    (measurableSet_le (Finset.measurable_sum _ fun j _ ↦ (hmale j).pow_const _)
      measurable_const).inter <|
    (measurableSet_le (Finset.measurable_sum _ fun i _ ↦ (hfemale i).pow_const _)
      measurable_const).inter <|
    (MeasurableSet.iInter fun j ↦ measurableSet_le (homit j)
      (measurable_const.mul (measurable_reverseDiagonalMaleTotal n))).inter <|
    measurableSet_le (Finset.measurable_sum _ fun i _ ↦ measurable_diagonalMaleScore i)
      (measurable_const.mul (measurable_reverseDiagonalMaleTotal n))
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
end MarkedLP
end

-- PivotMarkedDecorationCount
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace MarkedLP
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
theorem integrable_localFilteredDecorationCount (b A B : ℝ) (K L : ℕ) (μ ρ : Matching n)
    (ν : Measure (ScoreProfile n)) [IsFiniteMeasure ν] :
    Integrable (localFilteredDecorationCount b A B K L μ ρ) ν := by
  refine (integrable_const (n.factorial : ℝ)).mono'
    (measurable_localFilteredDecorationCount b A B K L μ ρ).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (localFilteredDecorationCount_nonneg b A B K L μ ρ x)]
  exact localFilteredDecorationCount_le_factorial b A B K L μ ρ x
theorem localFilteredDecorationCount_of_eligible_of_fixedMask {b A B : ℝ}
    (K L : ℕ) {μ ρ : Matching n} {x : ScoreProfile n} {flag : OffDiagonalCellIndex n → Bool}
    (h : IsLocallyEligiblePivot b A B x μ ρ)
    (hmask : (splitScorePairs μ x).2 ∈ forwardScoreMaskEvent (splitScorePairs μ x).1 flag) :
    localFilteredDecorationCount b A B K L μ ρ x = ((
      markedFilteredChoices μ ρ flag K L
        (reverseIncrementCutoff n (reverseDiagonalMaleTotal (splitScorePairs μ x).1)) x).card :
      ℝ) := by
  classical
  rw [localFilteredDecorationCount, if_pos h, (forwardMaskOfScores_eq_iff _ _ _).mpr hmask,
    reverseDiagonalMaleTotal_splitScorePairs]
theorem localFilteredDecorationCount_of_not_eligible {b A B : ℝ} (K L : ℕ)
    {μ ρ : Matching n} {x : ScoreProfile n} (h : ¬ IsLocallyEligiblePivot b A B x μ ρ) :
    localFilteredDecorationCount b A B K L μ ρ x = 0 := by
  classical
  rw [localFilteredDecorationCount, if_neg h]
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
private noncomputable def totalLocalFilteredDecorationCount (b A B : ℝ) (K L : ℕ)
    (x : ScoreProfile n) : ℝ := by
  classical
  exact ∑ μ : Matching n, ∑ ρ : Matching n,
    if IsScoreStable x μ then localFilteredDecorationCount b A B K L μ ρ x else 0
theorem measurable_totalLocalFilteredDecorationCount (b A B : ℝ) (K L : ℕ) :
    Measurable (totalLocalFilteredDecorationCount (n := n) b A B K L) := by
  classical
  unfold totalLocalFilteredDecorationCount
  exact Finset.measurable_sum _ fun μ _ ↦ Finset.measurable_sum _ fun ρ _ ↦
    (measurable_localFilteredDecorationCount b A B K L μ ρ).ite
      (measurableSet_isScoreStable μ) measurable_const
private noncomputable def stableMarkedChoices (b A B : ℝ) (K L : ℕ)
    (x : ScoreProfile n) (μ ρ : Matching n) : Finset (Matching n) := by
  classical
  exact if IsScoreStable x μ ∧ IsLocallyEligiblePivot b A B x μ ρ then
    markedFilteredChoices μ ρ
      (forwardMaskOfScores (splitScorePairs μ x).1 (splitScorePairs μ x).2)
      K L (reverseIncrementCutoff n (maleSpouseTotal x μ)) x
    else ∅
theorem totalLocalFilteredDecorationCount_le_numStableMatchings {b A B : ℝ} {K L : ℕ}
    {x : ScoreProfile n} (ht : ∀ row, Function.Injective (x row))
    (hl : ∀ μ ρ : Matching n, IsScoreStable x μ → IsLocallyEligiblePivot b A B x μ ρ →
      K < ρ.support.card) :
    totalLocalFilteredDecorationCount b A B K L x ≤
      (numStableMatchings (profileOfScores x) : ℝ) := by
  classical
  let F (i : Matching n × Matching n) := stableMarkedChoices b A B K L x i.1 i.2
  let P := (Finset.univ : Finset (Matching n × Matching n)).sigma F
  let g (a : Σ _ : Matching n × Matching n, Matching n) := undoReverseRotation a.1.1 a.2
  have hdata (a : ↥P) :
      IsStable (profileOfScores x) a.val.1.1 ∧
      IsSoleForwardExposedRotation (profileOfScores x) a.val.1.1 a.val.1.2 ∧
      K < a.val.1.2.support.card ∧
      a.val.2 ∈ markedFilteredChoices a.val.1.1 a.val.1.2
        (forwardMaskOfScores (splitScorePairs a.val.1.1 x).1 (splitScorePairs a.val.1.1 x).2)
        K L (reverseIncrementCutoff n (maleSpouseTotal x a.val.1.1)) x := by
    have ha := (Finset.mem_sigma.mp a.property).2
    change a.val.2 ∈ stableMarkedChoices b A B K L x a.val.1.1 a.val.1.2 at ha
    unfold stableMarkedChoices at ha
    split at ha
    · rename_i h
      exact ⟨(isStable_profileOfScores_iff ht _).mpr h.1, h.2.isSoleForwardExposed ht,
        hl _ _ h.1 h.2, ha⟩
    · exact (Finset.notMem_empty _ ha).elim
  let e (a : ↥P) : {μ : Matching n // IsStable (profileOfScores x) μ} :=
    ⟨g a.val, isStable_undoReverseRotation_of_mem_markedFilteredChoices (hdata a).1
      (hdata a).2.2.2⟩
  have hinj : Function.Injective e := by
    intro a a' he
    obtain ⟨ha, has, hal, ham⟩ := hdata a
    obtain ⟨ha', has', hal', ham'⟩ := hdata a'
    have hg : g a.val = g a'.val := congrArg Subtype.val he
    obtain ⟨μ₀, hopt⟩ := exists_manOptimal_of_exists_stable ⟨a.val.1.1, ha⟩
    obtain ⟨hm, hr, hc⟩ :=
      markedFilteredChoices_endpoint_injective hopt ha ha' has has' hal hal' ham ham' hg
    apply Subtype.ext
    exact Sigma.ext (Prod.ext hm hr) (heq_of_eq hc)
  have hcard : P.card ≤ numStableMatchings (profileOfScores x) := by
    have h := Nat.card_le_card_of_injective e hinj
    rwa [Nat.card_eq_finsetCard, Nat.card_eq_fintype_card] at h
  have hsum : (P.card : ℝ) = totalLocalFilteredDecorationCount b A B K L x := by
    rw [show P = (Finset.univ : Finset (Matching n × Matching n)).sigma F from rfl,
      Finset.card_sigma, Nat.cast_sum, Fintype.sum_prod_type]
    unfold totalLocalFilteredDecorationCount
    refine Finset.sum_congr rfl fun μ _ ↦ Finset.sum_congr rfl fun ρ _ ↦ ?_
    change ((stableMarkedChoices b A B K L x μ ρ).card : ℝ) = _
    by_cases hμ : IsScoreStable x μ <;> by_cases hρ : IsLocallyEligiblePivot b A B x μ ρ <;>
      simp [stableMarkedChoices, localFilteredDecorationCount, hμ, hρ]
  rw [← hsum]
  exact_mod_cast hcard
theorem IsLocallyEligiblePivot.supportCap_lt {b A B κ : ℝ} {K : ℕ} {x : ScoreProfile n}
    {μ ρ : Matching n} (h : IsLocallyEligiblePivot b A B x μ ρ)
    (hn : 0 < n) (hκ : κ < b) (hK : (K : ℝ) ≤ κ * Real.sqrt (n : ℝ)) :
    K < ρ.support.card := by
  have hr : (K : ℝ) < (ρ.support.card : ℝ) :=
    hK.trans_lt ((mul_lt_mul_of_pos_right hκ (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn))).trans_le
      h.1.length_lower)
  exact_mod_cast hr
end MarkedLP
end

-- PivotRestrictedMoment
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace MarkedLP
section ConditionalOrder
variable {Ω : Type*} {m m₀ : MeasurableSpace Ω}
end ConditionalOrder
private noncomputable def stableMarkScoreLaw {n : ℕ} (μ : Matching n) : Measure (ScoreProfile n) :=
  (continuousScoreLaw n).restrict {x | IsScoreStable x μ}
private instance {n : ℕ} (μ : Matching n) : IsFiniteMeasure (stableMarkScoreLaw μ) :=
  inferInstanceAs (IsFiniteMeasure ((continuousScoreLaw n).restrict _))
theorem lintegral_stableMarkScoreLaw {n : ℕ} (μ : Matching n)
    {f : ScoreProfile n → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x, f x ∂stableMarkScoreLaw μ) =
      ∫⁻ d, ∫⁻ z, f ((splitScorePairs μ).symm (d, z))
        ∂((offDiagonalScoreLaw n).restrict (offDiagonalNonblocking d)) ∂diagonalScoreLaw n := by
  simpa only [stableMarkScoreLaw, mem_univ, and_true, Measure.restrict_univ] using
    continuousScoreLaw_lintegral_stable_and_diagonal μ (C := univ) MeasurableSet.univ hf
theorem lintegral_offDiagonalNonblocking_eq_sum_masks {n : ℕ}
    (d : DiagonalScorePairs n) (f : OffDiagonalScorePairs n → ℝ≥0∞) :
    (∫⁻ z, f z ∂((offDiagonalScoreLaw n).restrict (offDiagonalNonblocking d))) =
      ∑ flag : OffDiagonalCellIndex n → Bool,
        ∫⁻ z in forwardScoreMaskEvent d flag, f z
          ∂((offDiagonalScoreLaw n).restrict (offDiagonalNonblocking d)) := by
  classical
  have hU : (⋃ flag ∈ (Finset.univ : Finset (OffDiagonalCellIndex n → Bool)),
      forwardScoreMaskEvent d flag) = univ := by
    ext z
    constructor
    · exact fun _ ↦ mem_univ _
    · intro _
      exact mem_iUnion.mpr ⟨forwardMaskOfScores d z, mem_iUnion.mpr
        ⟨Finset.mem_univ _, (forwardMaskOfScores_eq_iff _ _ _).mp rfl⟩⟩
  let ν := (offDiagonalScoreLaw n).restrict (offDiagonalNonblocking d)
  calc
    _ = ∫⁻ z in ⋃ flag ∈ (Finset.univ : Finset (OffDiagonalCellIndex n → Bool)),
        forwardScoreMaskEvent d flag, f z ∂ν := by rw [hU, Measure.restrict_univ]
    _ = _ := by
      refine lintegral_biUnion_finset ?_ (fun flag _ ↦ measurableSet_forwardScoreMaskEvent d flag) _
      intro a _ b _ hab
      exact Set.disjoint_left.mpr fun z ha hb ↦ hab
        (((forwardMaskOfScores_eq_iff d z a).mpr ha).symm.trans
          ((forwardMaskOfScores_eq_iff d z b).mpr hb))
end MarkedLP
end

-- PivotFullRevealLaw
section
open MeasureTheory Set StableMarriage
open scoped ENNReal
namespace MarkedLP
private abbrev PivotMaleRevealData (n : ℕ) :=
  DiagonalScorePairs n × (OffDiagonalCellIndex n → Bool) × (OffDiagonalCellIndex n → ℝ)
private abbrev PivotFullRevealData (n : ℕ) := PivotMaleRevealData n × (OffDiagonalCellIndex n → ℝ)
variable {n : ℕ}
private def extendPivotActiveValues (flag : OffDiagonalCellIndex n → Bool)
    (a : ForwardActiveCellIndex flag → ℝ) (q : OffDiagonalCellIndex n) : ℝ :=
  if h : flag q = true then a ⟨q, h⟩ else 0
theorem measurable_extendPivotActiveValues (flag : OffDiagonalCellIndex n → Bool) :
    Measurable (extendPivotActiveValues flag) := by
  apply measurable_pi_iff.2
  intro q
  by_cases h : flag q = true
  · simpa only [extendPivotActiveValues, dif_pos h] using
      (measurable_pi_apply (⟨q, h⟩ : ForwardActiveCellIndex flag))
  · simp only [extendPivotActiveValues, dif_neg h]
    exact measurable_const
private noncomputable def pivotMaleRevealFromScores (z : DiagonalScorePairs n × OffDiagonalScorePairs n) :
    PivotMaleRevealData n :=
  let flag := forwardMaskOfScores z.1 z.2
  (z.1, flag, fun q ↦ if flag q = true then (z.2 q).1 else 0)
private noncomputable def pivotFullRevealFromScores (z : DiagonalScorePairs n × OffDiagonalScorePairs n) :
    PivotFullRevealData n :=
  (pivotMaleRevealFromScores z,
    fun q ↦ if forwardMaskOfScores z.1 z.2 q = true then (z.2 q).2 else 0)
theorem measurable_pivotMaleRevealFromScores (n : ℕ) :
    Measurable (@pivotMaleRevealFromScores n) := by
  have hmask := measurable_jointForwardMaskOfScores n
  apply measurable_fst.prodMk (hmask.prodMk ?_)
  apply measurable_pi_iff.2
  intro q
  exact Measurable.ite (measurableSet_eq_fun ((measurable_pi_apply q).comp hmask)
    measurable_const) ((measurable_pi_apply q).comp measurable_snd).fst measurable_const
theorem measurable_pivotFullRevealFromScores (n : ℕ) :
    Measurable (@pivotFullRevealFromScores n) := by
  have hmask := measurable_jointForwardMaskOfScores n
  apply (measurable_pivotMaleRevealFromScores n).prodMk
  apply measurable_pi_iff.2
  intro q
  exact Measurable.ite (measurableSet_eq_fun ((measurable_pi_apply q).comp hmask)
    measurable_const) ((measurable_pi_apply q).comp measurable_snd).snd measurable_const
private noncomputable def pivotMaleReveal (μ : Matching n) (x : ScoreProfile n) : PivotMaleRevealData n :=
  pivotMaleRevealFromScores (splitScorePairs μ x)
private noncomputable def pivotFullReveal (μ : Matching n) (x : ScoreProfile n) : PivotFullRevealData n :=
  pivotFullRevealFromScores (splitScorePairs μ x)
@[simp] theorem pivotFullReveal_fst (μ : Matching n) (x : ScoreProfile n) :
    (pivotFullReveal μ x).1 = pivotMaleReveal μ x := rfl
theorem measurable_pivotMaleReveal (μ : Matching n) : Measurable (pivotMaleReveal μ) :=
  (measurable_pivotMaleRevealFromScores n).comp (splitScorePairs μ).measurable
theorem measurable_pivotFullReveal (μ : Matching n) : Measurable (pivotFullReveal μ) :=
  (measurable_pivotFullRevealFromScores n).comp (splitScorePairs μ).measurable
private noncomputable def pivotMaleRevealSpace (μ : Matching n) : MeasurableSpace (ScoreProfile n) :=
  MeasurableSpace.comap (pivotMaleReveal μ) inferInstance
private noncomputable def pivotFullRevealSpace (μ : Matching n) : MeasurableSpace (ScoreProfile n) :=
  MeasurableSpace.comap (pivotFullReveal μ) inferInstance
theorem pivotMaleRevealSpace_le (μ : Matching n) :
    pivotMaleRevealSpace μ ≤ (inferInstance : MeasurableSpace (ScoreProfile n)) :=
  (measurable_pivotMaleReveal μ).comap_le
theorem pivotFullRevealSpace_le (μ : Matching n) :
    pivotFullRevealSpace μ ≤ (inferInstance : MeasurableSpace (ScoreProfile n)) :=
  (measurable_pivotFullReveal μ).comap_le
theorem pivotMaleRevealSpace_le_full (μ : Matching n) :
    pivotMaleRevealSpace μ ≤ pivotFullRevealSpace μ := by
  unfold pivotMaleRevealSpace pivotFullRevealSpace
  change MeasurableSpace.comap (Prod.fst ∘ pivotFullReveal μ) _ ≤ _
  rw [← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono measurable_fst.comap_le
private def pivotMaleRevealSection (flag : OffDiagonalCellIndex n → Bool)
    (z : DiagonalScorePairs n × ForwardRevealedMaleScores flag) : PivotMaleRevealData n :=
  (z.1, flag, extendPivotActiveValues flag z.2)
private def pivotFullRevealSection (flag : OffDiagonalCellIndex n → Bool)
    (z : DiagonalScorePairs n × ForwardRevealedMaleScores flag × ForwardRevealedMaleScores flag) :
    PivotFullRevealData n :=
  (pivotMaleRevealSection flag (z.1, z.2.1), extendPivotActiveValues flag z.2.2)
theorem measurable_pivotMaleRevealSection (flag : OffDiagonalCellIndex n → Bool) :
    Measurable (pivotMaleRevealSection flag) :=
  measurable_fst.prodMk
    (measurable_const.prodMk ((measurable_extendPivotActiveValues flag).comp measurable_snd))
theorem measurable_pivotFullRevealSection (flag : OffDiagonalCellIndex n → Bool) :
    Measurable (pivotFullRevealSection flag) :=
  ((measurable_pivotMaleRevealSection flag).comp
    (measurable_fst.prodMk measurable_snd.fst)).prodMk
    ((measurable_extendPivotActiveValues flag).comp measurable_snd.snd)
theorem pivotMaleReveal_reconstruct (μ : Matching n) (d : DiagonalScorePairs n)
    (z : OffDiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool)
    (hflag : z ∈ forwardScoreMaskEvent d flag) :
    pivotMaleReveal μ ((splitScorePairs μ).symm (d, z)) =
      pivotMaleRevealSection flag (d, (forwardRevealWithColumns flag z).1) := by
  have he : forwardMaskOfScores d z = flag := (forwardMaskOfScores_eq_iff d z flag).2 hflag
  simp only [pivotMaleReveal, MeasurableEquiv.apply_symm_apply, pivotMaleRevealFromScores, he,
    pivotMaleRevealSection]
  congr 2
theorem pivotFullReveal_reconstruct (μ : Matching n) (d : DiagonalScorePairs n)
    (z : OffDiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool)
    (hflag : z ∈ forwardScoreMaskEvent d flag) :
    pivotFullReveal μ ((splitScorePairs μ).symm (d, z)) =
      pivotFullRevealSection flag
        (d, (forwardRevealWithColumns flag z).1, fun q ↦ (z q.val).2) := by
  have he : forwardMaskOfScores d z = flag := (forwardMaskOfScores_eq_iff d z flag).2 hflag
  apply Prod.ext
  · exact pivotMaleReveal_reconstruct μ d z flag hflag
  · simp only [pivotFullReveal, MeasurableEquiv.apply_symm_apply, pivotFullRevealFromScores,
      pivotFullRevealSection, he]
    funext q
    by_cases h : flag q = true <;> simp [extendPivotActiveValues, h]
private def pivotEligibleRevealDataSet (b A B : ℝ) (μ ρ : Matching n) : Set (PivotMaleRevealData n) :=
  {z | LocalPivotGeometry b A B μ ρ z.1 z.2.1 ∧
    (fun q : ForwardActiveCellIndex z.2.1 ↦ z.2.2 q.val) ∈
      eligiblePivotRevealSet z.1 z.2.1 ρ (localPivotIncrementCap B z.1)}
theorem measurableSet_pivotEligibleRevealDataSet (b A B : ℝ) (μ ρ : Matching n) :
    MeasurableSet (pivotEligibleRevealDataSet b A B μ ρ) := by
  let F (flag : OffDiagonalCellIndex n → Bool) (z : PivotMaleRevealData n) :
      DiagonalScorePairs n × ForwardRevealedMaleScores flag :=
    (z.1, fun q ↦ z.2.2 q.val)
  have hF (flag : OffDiagonalCellIndex n → Bool) : Measurable (F flag) :=
    measurable_fst.prodMk (measurable_pi_iff.2 fun q ↦
      (measurable_pi_apply q.val).comp measurable_snd.snd)
  let E (flag : OffDiagonalCellIndex n → Bool) : Set (PivotMaleRevealData n) :=
    {z | z.2.1 = flag} ∩
    (Prod.fst ⁻¹' {d | LocalPivotGeometry b A B μ ρ d flag} ∩
      F flag ⁻¹' {z | z.2 ∈ eligiblePivotRevealSet z.1 flag ρ (localPivotIncrementCap B z.1)})
  have he : pivotEligibleRevealDataSet b A B μ ρ = ⋃ flag, E flag := by
    ext z
    refine ⟨fun h ↦ mem_iUnion.mpr ⟨z.2.1, rfl, h.1, h.2⟩, fun h ↦ ?_⟩
    obtain ⟨flag, heq, hd, ha⟩ := mem_iUnion.mp h
    change z.2.1 = flag at heq
    subst flag
    exact ⟨hd, ha⟩
  rw [he]
  refine MeasurableSet.iUnion fun flag ↦
    (measurableSet_eq_fun measurable_snd.fst measurable_const).inter ?_
  exact ((measurableSet_localPivotGeometry b A B μ ρ flag).preimage measurable_fst).inter
    ((measurableSet_jointEligiblePivotReveal B flag ρ).preimage (hF flag))
theorem mem_pivotEligibleRevealDataSet_iff (b A B : ℝ) (μ ρ : Matching n)
    (x : ScoreProfile n) :
    pivotMaleReveal μ x ∈ pivotEligibleRevealDataSet b A B μ ρ ↔
      IsLocallyEligiblePivot b A B x μ ρ := by
  let z := splitScorePairs μ x
  let flag := forwardMaskOfScores z.1 z.2
  have h : (fun q : ForwardActiveCellIndex flag ↦
      (pivotMaleReveal μ x).2.2 q.val) = (forwardRevealWithColumns flag z.2).1 := by
    funext q
    change (if flag q.val = true then (z.2 q.val).1 else 0) = (z.2 q.val).1
    rw [if_pos q.property]
  change (LocalPivotGeometry b A B μ ρ z.1 flag ∧
    (fun q : ForwardActiveCellIndex flag ↦ (pivotMaleReveal μ x).2.2 q.val) ∈
      eligiblePivotRevealSet z.1 flag ρ (localPivotIncrementCap B z.1)) ↔
    IsLocallyEligiblePivot b A B x μ ρ
  rw [h]
  rfl
theorem measurableSet_isLocallyEligiblePivot_maleRevealSpace (b A B : ℝ)
    (μ ρ : Matching n) :
    @MeasurableSet (ScoreProfile n) (pivotMaleRevealSpace μ)
      {x | IsLocallyEligiblePivot b A B x μ ρ} := by
  exact MeasurableSpace.measurableSet_comap.mpr
    ⟨pivotEligibleRevealDataSet b A B μ ρ, measurableSet_pivotEligibleRevealDataSet b A B μ ρ,
      Set.ext fun _ ↦ mem_pivotEligibleRevealDataSet_iff b A B μ ρ _⟩
private noncomputable def pivotActiveMaleIntervalLaw (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) : Measure (ForwardRevealedMaleScores flag) :=
  Measure.pi fun q : ForwardActiveCellIndex flag ↦
    unitScoreLaw.restrict (Ioi (diagonalPairAt d q.val.val.1).1)
private noncomputable def pivotActiveFemaleIntervalLaw (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) : Measure (ForwardRevealedMaleScores flag) :=
  Measure.pi fun q : ForwardActiveCellIndex flag ↦
    unitScoreLaw.restrict (Iio (diagonalPairAt d q.val.val.2).2)
private instance (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool) :
    IsFiniteMeasure (pivotActiveMaleIntervalLaw d flag) := by
  unfold pivotActiveMaleIntervalLaw
  infer_instance
private instance (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool) :
    IsFiniteMeasure (pivotActiveFemaleIntervalLaw d flag) := by
  unfold pivotActiveFemaleIntervalLaw
  infer_instance
private def pivotFullRevealWithColumns (flag : OffDiagonalCellIndex n → Bool)
    (z : OffDiagonalScorePairs n) :
    ForwardRevealedMaleScores flag × ForwardRevealedMaleScores flag ×
      ForwardInactiveColumns flag :=
  ((forwardRevealWithColumns flag z).1, fun q ↦ (z q.val).2, (forwardRevealWithColumns flag z).2)
theorem measurePreserving_pivotFullRevealWithColumns (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) :
    MeasurePreserving (pivotFullRevealWithColumns flag) (forwardMaskRevealLaw d flag univ)
      ((pivotActiveMaleIntervalLaw d flag).prod ((pivotActiveFemaleIntervalLaw d flag).prod
        (forwardScoreMaskInactiveColumnLaw d flag))) := by
  let m (q : ForwardActiveCellIndex flag) :=
    unitScoreLaw.restrict (Ioi (diagonalPairAt d q.val.val.1).1)
  let f (q : ForwardActiveCellIndex flag) :=
    unitScoreLaw.restrict (Iio (diagonalPairAt d q.val.val.2).2)
  let (q : ForwardActiveCellIndex flag) : IsFiniteMeasure (m q) := by dsimp [m]; infer_instance
  let (q : ForwardActiveCellIndex flag) : IsFiniteMeasure (f q) := by dsimp [f]; infer_instance
  have hActive := measurePreserving_arrowProdEquivProdArrow ℝ ℝ
    (ForwardActiveCellIndex flag) m f
  have hInactive := measurePreserving_forwardInactiveColumnsEquiv d flag
  have h :=
    (measurePreserving_prodAssoc (pivotActiveMaleIntervalLaw d flag)
      (pivotActiveFemaleIntervalLaw d flag) (forwardScoreMaskInactiveColumnLaw d flag)).comp
        ((hActive.prod hInactive).comp (measurePreserving_offDiagonalScoreLaw_splitMask d flag))
  rw [forwardMaskRevealLaw, preimage_univ, Measure.restrict_univ]
  exact h
private noncomputable def pivotInactiveSectionMean (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool)
    (F : ForwardRevealedMaleScores flag × ForwardInactiveColumns flag → ℝ≥0∞)
    (a : ForwardRevealedMaleScores flag) : ℝ≥0∞ :=
  ∫⁻ c, F (a, c) ∂Measure.pi (normalizedForwardInactiveColumnLaw d flag)
theorem measurable_pivotInactiveSectionMean (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool)
    {F : ForwardRevealedMaleScores flag × ForwardInactiveColumns flag → ℝ≥0∞}
    (hF : Measurable F) (hy0 : ∀ i, 0 ≤ (diagonalPairAt d i).2)
    (hy1 : ∀ i, (diagonalPairAt d i).2 < 1) :
    Measurable (pivotInactiveSectionMean d flag F) := by
  let (i : Fin n) : IsProbabilityMeasure (normalizedForwardInactiveColumnLaw d flag i) :=
    normalizedForwardInactiveColumnLaw_isProbabilityMeasure d flag i (hy0 i) (hy1 i)
  exact hF.lintegral_prod_right'
theorem lintegral_pivotFullReveal_test_eq_inactiveSectionMean
    (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool)
    {F : ForwardRevealedMaleScores flag × ForwardInactiveColumns flag → ℝ≥0∞}
    (hF : Measurable F)
    {G : ForwardRevealedMaleScores flag × ForwardRevealedMaleScores flag → ℝ≥0∞}
    (hG : Measurable G) (hy0 : ∀ i, 0 ≤ (diagonalPairAt d i).2)
    (hy1 : ∀ i, (diagonalPairAt d i).2 < 1) :
    let R := pivotFullRevealWithColumns flag
    let μ := forwardMaskRevealLaw d flag univ
    (∫⁻ z, G ((R z).1, (R z).2.1) * F ((R z).1, (R z).2.2) ∂μ) =
      ∫⁻ z, G ((R z).1, (R z).2.1) * pivotInactiveSectionMean d flag F (R z).1 ∂μ := by
  dsimp only
  let A := ForwardRevealedMaleScores flag
  let C := ForwardInactiveColumns flag
  let M := pivotActiveMaleIntervalLaw d flag
  let W := pivotActiveFemaleIntervalLaw d flag
  let L := forwardScoreMaskInactiveColumnLaw d flag
  let (i : Fin n) : IsProbabilityMeasure (normalizedForwardInactiveColumnLaw d flag i) :=
    normalizedForwardInactiveColumnLaw_isProbabilityMeasure d flag i (hy0 i) (hy1 i)
  let h := (measurePreserving_prodAssoc M W L).symm.comp
    (measurePreserving_pivotFullRevealWithColumns d flag)
  let F₁ (p : (A × A) × C) := G p.1 * F (p.1.1, p.2)
  let F₂ (p : (A × A) × C) := G p.1 * pivotInactiveSectionMean d flag F p.1.1
  have hF₁ : Measurable F₁ := (hG.comp measurable_fst).mul
    (hF.comp (measurable_fst.fst.prodMk measurable_snd))
  have hF₂ : Measurable F₂ := (hG.comp measurable_fst).mul
    ((measurable_pivotInactiveSectionMean d flag hF hy0 hy1).comp measurable_fst.fst)
  change (∫⁻ z, F₁ ((⇑(MeasurableEquiv.prodAssoc (α := A) (β := A) (γ := C)).symm ∘
      pivotFullRevealWithColumns flag) z)
      ∂forwardMaskRevealLaw d flag univ) =
    ∫⁻ z, F₂ ((⇑(MeasurableEquiv.prodAssoc (α := A) (β := A) (γ := C)).symm ∘
      pivotFullRevealWithColumns flag) z)
      ∂forwardMaskRevealLaw d flag univ
  rw [h.lintegral_comp hF₁, h.lintegral_comp hF₂, lintegral_prod F₁ hF₁.aemeasurable,
    lintegral_prod F₂ hF₂.aemeasurable]
  apply lintegral_congr
  intro a
  change (∫⁻ c, G a * F (a.1, c) ∂L) =
    ∫⁻ _ : C, G a * pivotInactiveSectionMean d flag F a.1 ∂L
  have hFa : Measurable (fun c : C ↦ F (a.1, c)) :=
    hF.comp (measurable_const.prodMk measurable_id)
  rw [lintegral_const_mul _ hFa, lintegral_const]
  change G a * (∫⁻ c, F (a.1, c) ∂forwardScoreMaskInactiveColumnLaw d flag) =
    G a * pivotInactiveSectionMean d flag F a.1 * L univ
  have hL := forwardScoreMaskInactiveColumnLaw_eq_smul d flag hy0 hy1
  have hmass : L univ = ∏ j, ENNReal.ofReal (1 - (diagonalPairAt d j).2) ^
      Fintype.card (ForwardInactiveColumnIndex flag j) := by
    change forwardScoreMaskInactiveColumnLaw d flag univ = _
    rw [hL, Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
  rw [hL, lintegral_smul_measure, smul_eq_mul, ← hmass]
  change G a * (L univ * pivotInactiveSectionMean d flag F a.1) = _
  ac_rfl
private noncomputable def pivotInactiveColumnBaseLaw (flag : OffDiagonalCellIndex n → Bool) :
    Measure (ForwardInactiveColumns flag) :=
  Measure.pi fun j ↦ Measure.pi fun _ : ForwardInactiveColumnIndex flag j ↦ unitScorePairLaw
private instance (flag : OffDiagonalCellIndex n → Bool) :
    IsProbabilityMeasure (pivotInactiveColumnBaseLaw flag) := by
  unfold pivotInactiveColumnBaseLaw
  infer_instance
private def pivotInactiveAllowed (flag : OffDiagonalCellIndex n → Bool) :
    Set (DiagonalScorePairs n × ForwardInactiveColumns flag) :=
  {z | ∀ j (q : ForwardInactiveColumnIndex flag j),
    (diagonalPairAt z.1 j).2 ≤ (z.2 j q).2}
theorem measurableSet_pivotInactiveAllowed (flag : OffDiagonalCellIndex n → Bool) :
    MeasurableSet (pivotInactiveAllowed flag) := by
  unfold pivotInactiveAllowed
  simp only [ofPred_forall]
  refine MeasurableSet.iInter fun j ↦ MeasurableSet.iInter fun q ↦ ?_
  have hy : Measurable (fun z : DiagonalScorePairs n × ForwardInactiveColumns flag ↦
      (diagonalPairAt z.1 j).2) := by
    have hd : Measurable (@Prod.fst (DiagonalScorePairs n) (ForwardInactiveColumns flag)) :=
      measurable_fst
    exact ((measurable_pi_apply (⟨(j, j), rfl⟩ : {q : ScorePairIndex n // q.1 = q.2})).comp
      hd).snd
  have hc : Measurable (fun z : DiagonalScorePairs n × ForwardInactiveColumns flag ↦
      (z.2 j q).2) := ((measurable_pi_apply q).comp
        ((measurable_pi_apply j).comp measurable_snd)).snd
  exact measurableSet_le hy hc
theorem pivotInactiveColumnBaseLaw_restrict (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) :
    (pivotInactiveColumnBaseLaw flag).restrict (Prod.mk d ⁻¹' pivotInactiveAllowed flag) =
      forwardScoreMaskInactiveColumnLaw d flag := by
  have he : Prod.mk d ⁻¹' pivotInactiveAllowed flag =
      univ.pi fun j ↦ univ.pi fun _ : ForwardInactiveColumnIndex flag j ↦
        (univ : Set ℝ) ×ˢ Ici (diagonalPairAt d j).2 := by
    ext z
    simp [pivotInactiveAllowed]
  rw [he, pivotInactiveColumnBaseLaw, Measure.restrict_pi_pi,
    forwardScoreMaskInactiveColumnLaw]
  congr 1
  funext j
  rw [Measure.restrict_pi_pi]
  congr 1
  funext q
  rw [unitScorePairLaw, ← Measure.prod_restrict, Measure.restrict_univ]
private noncomputable def pivotInactiveColumnMass (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) : ℝ≥0∞ :=
  ∏ j, ENNReal.ofReal (1 - (diagonalPairAt d j).2) ^
    Fintype.card (ForwardInactiveColumnIndex flag j)
theorem measurable_pivotInactiveColumnMass (flag : OffDiagonalCellIndex n → Bool) :
    Measurable (fun d ↦ pivotInactiveColumnMass d flag) := by
  unfold pivotInactiveColumnMass
  refine Finset.univ.measurable_prod fun j _ ↦ ?_
  have hy : Measurable (fun d : DiagonalScorePairs n ↦ (diagonalPairAt d j).2) :=
    (measurable_pi_apply (⟨(j, j), rfl⟩ : {q : ScorePairIndex n // q.1 = q.2})).snd
  exact (ENNReal.measurable_ofReal.comp (measurable_const.sub hy)).pow_const _
private noncomputable def pivotJointInactiveMean (flag : OffDiagonalCellIndex n → Bool)
    (F : DiagonalScorePairs n × ForwardRevealedMaleScores flag ×
      ForwardInactiveColumns flag → ℝ≥0∞)
    (da : DiagonalScorePairs n × ForwardRevealedMaleScores flag) : ℝ≥0∞ :=
  (pivotInactiveColumnMass da.1 flag)⁻¹ *
    ∫⁻ c, (pivotInactiveAllowed flag).indicator (fun z ↦ F (z.1, da.2, z.2)) (da.1, c)
      ∂pivotInactiveColumnBaseLaw flag
theorem measurable_pivotJointInactiveMean (flag : OffDiagonalCellIndex n → Bool)
    {F : DiagonalScorePairs n × ForwardRevealedMaleScores flag ×
      ForwardInactiveColumns flag → ℝ≥0∞} (hF : Measurable F) :
    Measurable (pivotJointInactiveMean flag F) := by
  let D := DiagonalScorePairs n
  let A := ForwardRevealedMaleScores flag
  let C := ForwardInactiveColumns flag
  let W : Set ((D × A) × C) := (fun z ↦ (z.1.1, z.2)) ⁻¹' pivotInactiveAllowed flag
  have hW : MeasurableSet W := (measurableSet_pivotInactiveAllowed flag).preimage
    (measurable_fst.fst.prodMk measurable_snd)
  let J (z : (D × A) × C) := W.indicator (fun z ↦ F (z.1.1, z.1.2, z.2)) z
  have hJ : Measurable J := (hF.comp (measurable_fst.fst.prodMk
    (measurable_fst.snd.prodMk measurable_snd))).indicator hW
  have hInt : Measurable (fun da : D × A ↦
      ∫⁻ c, J (da, c) ∂pivotInactiveColumnBaseLaw flag) := hJ.lintegral_prod_right'
  have hmass : Measurable (fun da : D × A ↦ (pivotInactiveColumnMass da.1 flag)⁻¹) :=
    ((measurable_pivotInactiveColumnMass flag).comp measurable_fst).inv
  exact hmass.mul hInt
theorem pivotJointInactiveMean_eq_sectionMean (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool)
    {F : DiagonalScorePairs n × ForwardRevealedMaleScores flag ×
      ForwardInactiveColumns flag → ℝ≥0∞}
    (a : ForwardRevealedMaleScores flag) (hy0 : ∀ i, 0 ≤ (diagonalPairAt d i).2)
    (hy1 : ∀ i, (diagonalPairAt d i).2 < 1) :
    pivotJointInactiveMean flag F (d, a) =
      pivotInactiveSectionMean d flag (fun z ↦ F (d, z.1, z.2)) a := by
  let E := Prod.mk d ⁻¹' pivotInactiveAllowed flag
  have hE : MeasurableSet E :=
    (measurableSet_pivotInactiveAllowed flag).preimage measurable_prodMk_left
  have hfun : (fun c ↦ (pivotInactiveAllowed flag).indicator
      (fun z ↦ F (z.1, a, z.2)) (d, c)) = E.indicator (fun c ↦ F (d, a, c)) := by
    funext c
    by_cases hc : c ∈ E
    · rw [indicator_of_mem (show (d, c) ∈ pivotInactiveAllowed flag from hc),
        indicator_of_mem hc]
    · rw [indicator_of_notMem (show (d, c) ∉ pivotInactiveAllowed flag from hc),
        indicator_of_notMem hc]
  have h0 : pivotInactiveColumnMass d flag ≠ 0 := by
    unfold pivotInactiveColumnMass
    exact Finset.prod_ne_zero_iff.mpr fun j _ ↦
      pow_ne_zero _ (ENNReal.ofReal_pos.mpr (sub_pos.mpr (hy1 j))).ne'
  have htop : pivotInactiveColumnMass d flag ≠ ∞ := by
    unfold pivotInactiveColumnMass
    exact ENNReal.prod_ne_top fun j _ ↦ ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  unfold pivotJointInactiveMean
  simp only [hfun, lintegral_indicator hE]
  change _ * (∫⁻ c, F (d, a, c) ∂(pivotInactiveColumnBaseLaw flag).restrict E) = _
  rw [pivotInactiveColumnBaseLaw_restrict, forwardScoreMaskInactiveColumnLaw_eq_smul d flag hy0 hy1,
    lintegral_smul_measure, smul_eq_mul]
  exact ENNReal.inv_mul_cancel_left h0 htop
private noncomputable def pivotInactiveMeanFromReveal
    (F : ∀ flag : OffDiagonalCellIndex n → Bool, DiagonalScorePairs n ×
      ForwardRevealedMaleScores flag × ForwardInactiveColumns flag → ℝ≥0∞)
    (z : PivotMaleRevealData n) : ℝ≥0∞ :=
  pivotJointInactiveMean z.2.1 (F z.2.1) (z.1, fun q ↦ z.2.2 q.val)
set_option maxHeartbeats 600000 in
theorem measurable_pivotInactiveMeanFromReveal
    {F : ∀ flag : OffDiagonalCellIndex n → Bool, DiagonalScorePairs n ×
      ForwardRevealedMaleScores flag × ForwardInactiveColumns flag → ℝ≥0∞}
    (hF : ∀ flag, Measurable (F flag)) :
    Measurable (pivotInactiveMeanFromReveal F) := by
  let D := DiagonalScorePairs n
  let A := OffDiagonalCellIndex n → ℝ
  let P := OffDiagonalCellIndex n → Bool
  let read (flag : P) (z : D × A) : D × ForwardRevealedMaleScores flag :=
    (z.1, fun q ↦ z.2 q.val)
  have hread (flag : P) : Measurable (read flag) :=
    measurable_fst.prodMk (measurable_pi_iff.2 fun q ↦
      (measurable_pi_apply q.val).comp measurable_snd)
  let T (z : (D × A) × P) :=
    pivotJointInactiveMean z.2 (F z.2) (read z.2 z.1)
  have hT : Measurable T := by
    apply measurable_from_prod_countable_left
    intro flag
    change Measurable (pivotJointInactiveMean flag (F flag) ∘ read flag)
    exact (measurable_pivotJointInactiveMean flag (hF flag)).comp (hread flag)
  let g (z : PivotMaleRevealData n) : (D × A) × P := ((z.1, z.2.2), z.2.1)
  have hg : Measurable g :=
    (measurable_fst.prodMk measurable_snd.snd).prodMk measurable_snd.fst
  change Measurable (T ∘ g)
  exact hT.comp hg
theorem pivotInactiveMeanFromReveal_section
    (F : ∀ flag : OffDiagonalCellIndex n → Bool, DiagonalScorePairs n ×
      ForwardRevealedMaleScores flag × ForwardInactiveColumns flag → ℝ≥0∞)
    (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool)
    (a : ForwardRevealedMaleScores flag) :
    pivotInactiveMeanFromReveal F (pivotMaleRevealSection flag (d, a)) =
      pivotJointInactiveMean flag (F flag) (d, a) := by
  change pivotJointInactiveMean flag (F flag)
    (d, fun q ↦ extendPivotActiveValues flag a q.val) = _
  have he : (fun q : ForwardActiveCellIndex flag ↦ extendPivotActiveValues flag a q.val) = a := by
    funext q
    rw [extendPivotActiveValues, dif_pos q.property]
  rw [he]
theorem pivotInactiveMeanFromReveal_section_le {B : ℝ≥0∞}
    {F : ∀ flag : OffDiagonalCellIndex n → Bool, DiagonalScorePairs n ×
      ForwardRevealedMaleScores flag × ForwardInactiveColumns flag → ℝ≥0∞}
    (hB : ∀ flag z, F flag z ≤ B) (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) (a : ForwardRevealedMaleScores flag)
    (hy0 : ∀ i, 0 ≤ (diagonalPairAt d i).2) (hy1 : ∀ i, (diagonalPairAt d i).2 < 1) :
    pivotInactiveMeanFromReveal F (pivotMaleRevealSection flag (d, a)) ≤ B := by
  rw [pivotInactiveMeanFromReveal_section, pivotJointInactiveMean_eq_sectionMean d flag a hy0 hy1]
  let (i : Fin n) : IsProbabilityMeasure (normalizedForwardInactiveColumnLaw d flag i) :=
    normalizedForwardInactiveColumnLaw_isProbabilityMeasure d flag i (hy0 i) (hy1 i)
  unfold pivotInactiveSectionMean
  refine (lintegral_mono fun c ↦ hB flag (d, a, c)).trans_eq ?_
  rw [lintegral_const, measure_univ, mul_one]
theorem ae_diagonalFemale_mem_Ico (n : ℕ) :
    ∀ᵐ d ∂diagonalScoreLaw n, ∀ i, (diagonalPairAt d i).2 ∈ Ico (0 : ℝ) 1 := by
  have hu : ∀ᵐ t ∂unitScoreLaw, t ∈ Ico (0 : ℝ) 1 := by
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Icc :
      MeasurableSet (Icc (0 : ℝ) 1)), unitScoreLaw.ae_ne (1 : ℝ)] with t ht hn
    exact ⟨ht.1, lt_of_le_of_ne ht.2 hn⟩
  have hp : ∀ᵐ z ∂unitScorePairLaw, z.2 ∈ Ico (0 : ℝ) 1 :=
    (Measure.quasiMeasurePreserving_snd (μ := unitScoreLaw) (ν := unitScoreLaw)).ae hu
  exact ae_all_iff.2 fun i ↦ (Measure.tendsto_eval_ae_ae
    (μ := fun _ : {q : ScorePairIndex n // q.1 = q.2} ↦ unitScorePairLaw)
    (i := ⟨(i, i), rfl⟩)).eventually hp
theorem ae_pivotInactiveMeanFromReveal_le_stableMarkScoreLaw
    (μ : Matching n) {B : ℝ≥0∞}
    {F : ∀ flag : OffDiagonalCellIndex n → Bool, DiagonalScorePairs n ×
      ForwardRevealedMaleScores flag × ForwardInactiveColumns flag → ℝ≥0∞}
    (hB : ∀ flag z, F flag z ≤ B) :
    ∀ᵐ x ∂stableMarkScoreLaw μ,
      pivotInactiveMeanFromReveal F (pivotMaleReveal μ x) ≤ B := by
  have hd : MeasurePreserving (fun x ↦ (splitScorePairs μ x).1)
      (continuousScoreLaw n) (diagonalScoreLaw n) :=
    measurePreserving_fst.comp (measurePreserving_splitScorePairs μ)
  have h := hd.quasiMeasurePreserving.ae (ae_diagonalFemale_mem_Ico n)
  apply ae_restrict_of_ae
  filter_upwards [h] with x hx
  let d := (splitScorePairs μ x).1
  let z := (splitScorePairs μ x).2
  let flag := forwardMaskOfScores d z
  have hf : z ∈ forwardScoreMaskEvent d flag := (forwardMaskOfScores_eq_iff d z flag).mp rfl
  have he : pivotMaleReveal μ x =
      pivotMaleRevealSection flag (d, (forwardRevealWithColumns flag z).1) := by
    simpa only [d, z, Prod.mk.eta, MeasurableEquiv.symm_apply_apply] using
      pivotMaleReveal_reconstruct μ d z flag hf
  rw [he]
  exact pivotInactiveMeanFromReveal_section_le hB d flag _ (fun i ↦ (hx i).1) (fun i ↦ (hx i).2)
set_option maxHeartbeats 900000 in
theorem setLIntegral_stableMark_fullReveal_eq_inactiveMean (μ : Matching n)
    {F : ∀ flag : OffDiagonalCellIndex n → Bool, DiagonalScorePairs n ×
      ForwardRevealedMaleScores flag × ForwardInactiveColumns flag → ℝ≥0∞}
    (hF : ∀ flag, Measurable (F flag)) {Z : ScoreProfile n → ℝ≥0∞} (hZ : Measurable Z)
    (hY : ∀ᵐ d ∂diagonalScoreLaw n, ∀ i, (diagonalPairAt d i).2 ∈ Ico (0 : ℝ) 1)
    (hfactor : ∀ᵐ d ∂diagonalScoreLaw n, ∀ flag,
      ∀ᵐ z ∂forwardMaskRevealLaw d flag univ,
        Z ((splitScorePairs μ).symm (d, z)) =
          F flag (d, (forwardRevealWithColumns flag z).1, (forwardRevealWithColumns flag z).2))
    {S : Set (ScoreProfile n)} (hS : @MeasurableSet _ (pivotFullRevealSpace μ) S) :
    (∫⁻ x in S, Z x ∂stableMarkScoreLaw μ) =
      ∫⁻ x in S, pivotInactiveMeanFromReveal F (pivotMaleReveal μ x)
        ∂stableMarkScoreLaw μ := by
  have hS₀ : MeasurableSet S := pivotFullRevealSpace_le μ S hS
  obtain ⟨U, hU, hUeq⟩ := MeasurableSpace.measurableSet_comap.mp hS
  have hmean : Measurable (fun x ↦ pivotInactiveMeanFromReveal F (pivotMaleReveal μ x)) :=
    (measurable_pivotInactiveMeanFromReveal hF).comp (measurable_pivotMaleReveal μ)
  rw [← lintegral_indicator hS₀, ← lintegral_indicator hS₀,
    lintegral_stableMarkScoreLaw μ (hZ.indicator hS₀),
    lintegral_stableMarkScoreLaw μ (hmean.indicator hS₀)]
  apply lintegral_congr_ae
  filter_upwards [hY, hfactor] with d hd hD
  rw [lintegral_offDiagonalNonblocking_eq_sum_masks, lintegral_offDiagonalNonblocking_eq_sum_masks]
  apply Finset.sum_congr rfl
  intro flag _
  let ν := forwardMaskRevealLaw d flag univ
  have hν : ν = ((offDiagonalScoreLaw n).restrict (offDiagonalNonblocking d)).restrict
      (forwardScoreMaskEvent d flag) := by
    simp only [ν, forwardMaskRevealLaw, preimage_univ, Measure.restrict_univ]
  rw [← hν]
  have hmask : ∀ᵐ z ∂ν, z ∈ forwardScoreMaskEvent d flag := by
    rw [hν]
    exact ae_restrict_mem (measurableSet_forwardScoreMaskEvent d flag)
  let R := pivotFullRevealWithColumns flag
  let X (z : OffDiagonalScorePairs n) := (splitScorePairs μ).symm (d, z)
  let A := ForwardRevealedMaleScores flag
  let V : Set (A × A) := (fun a ↦ pivotFullRevealSection flag (d, a)) ⁻¹' U
  let G : A × A → ℝ≥0∞ := V.indicator 1
  let T (p : A × ForwardInactiveColumns flag) := F flag (d, p.1, p.2)
  have hV : MeasurableSet V := hU.preimage
    ((measurable_pivotFullRevealSection flag).comp (measurable_const.prodMk measurable_id))
  have hG : Measurable G := measurable_const.indicator hV
  have hT : Measurable T := (hF flag).comp (measurable_const.prodMk measurable_id)
  have hSiff (z : OffDiagonalScorePairs n) (hz : z ∈ forwardScoreMaskEvent d flag) :
      X z ∈ S ↔ ((R z).1, (R z).2.1) ∈ V := by
    rw [← hUeq]
    change pivotFullReveal μ (X z) ∈ U ↔
      pivotFullRevealSection flag (d, (R z).1, (R z).2.1) ∈ U
    rw [pivotFullReveal_reconstruct μ d z flag hz]
    rfl
  calc
    _ = ∫⁻ z, G ((R z).1, (R z).2.1) * T ((R z).1, (R z).2.2) ∂ν := by
      apply lintegral_congr_ae
      filter_upwards [hmask, hD flag] with z hz hfz
      change S.indicator Z (X z) =
        V.indicator 1 ((R z).1, (R z).2.1) * T ((R z).1, (R z).2.2)
      by_cases h : X z ∈ S
      · rw [indicator_of_mem h _, indicator_of_mem ((hSiff z hz).mp h) _]
        change Z (X z) = 1 * T ((R z).1, (R z).2.2)
        rw [one_mul]
        exact hfz
      · rw [indicator_of_notMem h _, indicator_of_notMem (mt (hSiff z hz).mpr h) _, zero_mul]
    _ = ∫⁻ z, G ((R z).1, (R z).2.1) * pivotInactiveSectionMean d flag T (R z).1 ∂ν :=
      lintegral_pivotFullReveal_test_eq_inactiveSectionMean d flag hT hG
        (fun i ↦ (hd i).1) (fun i ↦ (hd i).2)
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [hmask] with z hz
      have hm : pivotInactiveMeanFromReveal F (pivotMaleReveal μ (X z)) =
          pivotInactiveSectionMean d flag T (R z).1 := by
        rw [show X z = (splitScorePairs μ).symm (d, z) from rfl,
          pivotMaleReveal_reconstruct μ d z flag hz, pivotInactiveMeanFromReveal_section]
        exact pivotJointInactiveMean_eq_sectionMean d flag _
          (fun i ↦ (hd i).1) (fun i ↦ (hd i).2)
      change V.indicator 1 ((R z).1, (R z).2.1) * pivotInactiveSectionMean d flag T (R z).1 =
        S.indicator (fun x ↦ pivotInactiveMeanFromReveal F (pivotMaleReveal μ x)) (X z)
      by_cases h : X z ∈ S
      · rw [indicator_of_mem h _, indicator_of_mem ((hSiff z hz).mp h) _, hm]
        exact one_mul _
      · rw [indicator_of_notMem h _,
          indicator_of_notMem (mt (hSiff z hz).mpr h) _, zero_mul]
end MarkedLP
end

-- PivotConditionalMean
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace MarkedLP
variable {n : ℕ}
private noncomputable def localPivotConditionalMean (b A B : ℝ) (K L : ℕ) (μ ρ : Matching n) :
    ScoreProfile n → ℝ :=
  (stableMarkScoreLaw μ)[localFilteredDecorationCount b A B K L μ ρ|pivotMaleRevealSpace μ]
end MarkedLP
end

-- DeferredAcceptanceTranscript
section
open StableMarriage
open scoped BigOperators
namespace MarkedLP
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
end MarkedLP
end

-- DAStreamSimulation
section
open StableMarriage
namespace MarkedLP
private structure DAStreamState (n : ℕ) where
  da : DAState n
  observed : Fin n → List (Fin n)
namespace DAStreamState
variable {n T : ℕ}
private def initial (n : ℕ) : DAStreamState n := ⟨DAState.initial n, fun _ ↦ []⟩
end DAStreamState
end MarkedLP
end

-- PivotAggregateMean
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace MarkedLP
variable {n : ℕ}
private noncomputable def stablePivotMeanTerm (b A B : ℝ) (K L : ℕ)
    (x : ScoreProfile n) (i : Matching n × Matching n) : ℝ :=
  {y | IsScoreStable y i.1}.indicator (localPivotConditionalMean b A B K L i.1 i.2) x
private noncomputable def totalLocalPivotConditionalMean (b A B : ℝ) (K L : ℕ)
    (x : ScoreProfile n) : ℝ :=
  ∑ i : Matching n × Matching n, stablePivotMeanTerm b A B K L x i
theorem measurable_totalLocalPivotConditionalMean (b A B : ℝ) (K L : ℕ) :
    Measurable (totalLocalPivotConditionalMean (n := n) b A B K L) := by
  unfold totalLocalPivotConditionalMean stablePivotMeanTerm
  exact Finset.measurable_sum _ fun i _ ↦
    ((stronglyMeasurable_condExp.mono (pivotMaleRevealSpace_le i.1)).measurable.indicator
      (measurableSet_isScoreStable i.1))
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
theorem ae_totalLocalFilteredDecorationCount_le {b A B κ : ℝ} {K L : ℕ}
    (hn : 0 < n) (hκ : κ < b) (hK : (K : ℝ) ≤ κ * Real.sqrt (n : ℝ)) :
    ∀ᵐ x ∂continuousScoreLaw n, totalLocalFilteredDecorationCount b A B K L x ≤
      (numStableMatchings (profileOfScores x) : ℝ) := by
  filter_upwards [ae_injective_rows n] with x ht
  exact totalLocalFilteredDecorationCount_le_numStableMatchings ht fun _ _ _ he ↦
    he.supportCap_lt hn hκ hK
end MarkedLP
end

-- PivotDecorationRevealInvariance
section
open MeasureTheory Set StableMarriage
namespace MarkedLP
variable {n : ℕ} {μ ρ σ : Matching n} {x y : ScoreProfile n}
  {flag : OffDiagonalCellIndex n → Bool}
private structure SameReverseReveal (μ : Matching n) (flag : OffDiagonalCellIndex n → Bool)
    (x y : ScoreProfile n) : Prop where
  diagonal : (splitScorePairs μ x).1 = (splitScorePairs μ y).1
  observed : forwardRevealWithColumns flag (splitScorePairs μ x).2 =
    forwardRevealWithColumns flag (splitScorePairs μ y).2
theorem SameReverseReveal.symm (h : SameReverseReveal μ flag x y) :
    SameReverseReveal μ flag y x := ⟨h.diagonal.symm, h.observed.symm⟩
theorem SameReverseReveal.inactiveCell_eq (h : SameReverseReveal μ flag x y)
    (q : ForwardInactiveCellIndex flag) :
    (splitScorePairs μ x).2 q.val = (splitScorePairs μ y).2 q.val :=
  congrFun (congrFun (congrArg Prod.snd h.observed) q.val.val.2)
    (⟨q, rfl⟩ : ForwardInactiveColumnIndex flag q.val.val.2)
theorem SameReverseReveal.male_eq (h : SameReverseReveal μ flag x y) (m w : Fin n) :
    x (.inl m) w = y (.inl m) w := by
  by_cases hw : w = μ m
  · subst w
    simpa only [diagonalPairAt_splitScorePairs] using
      congrArg (fun d ↦ (diagonalPairAt d m).1) h.diagonal
  · let q : OffDiagonalCellIndex n :=
      ⟨(m, μ.symm w), fun he ↦ hw ((congrArg μ he).trans (μ.apply_symm_apply w)).symm⟩
    have hcell : ((splitScorePairs μ x).2 q).1 = ((splitScorePairs μ y).2 q).1 := by
      by_cases hq : flag q = true
      · exact congrFun (congrArg Prod.fst h.observed) (⟨q, hq⟩ : ForwardActiveCellIndex flag)
      · exact congrArg Prod.fst (h.inactiveCell_eq ⟨q, hq⟩)
    simpa only [splitScorePairs_offDiagonal_apply, q, Equiv.apply_symm_apply] using hcell
theorem SameReverseReveal.female_spouse_eq (h : SameReverseReveal μ flag x y) (w : Fin n) :
    x (.inr w) (μ.symm w) = y (.inr w) (μ.symm w) := by
  simpa only [diagonalPairAt_splitScorePairs, Equiv.apply_symm_apply] using
    congrArg (fun d ↦ (diagonalPairAt d (μ.symm w)).2) h.diagonal
private theorem SameReverseReveal.female_eq_of_spouse_lt
    (h : SameReverseReveal μ flag x y)
    (hmask : (splitScorePairs μ x).2 ∈ forwardScoreMaskEvent (splitScorePairs μ x).1 flag)
    {m w : Fin n} (hw : x (.inr w) (μ.symm w) < x (.inr w) m) :
    x (.inr w) m = y (.inr w) m := by
  have hne : m ≠ μ.symm w := fun e ↦ hw.ne (congrArg (x (.inr w)) e.symm)
  let q : OffDiagonalCellIndex n := ⟨(m, μ.symm w), hne⟩
  have hq : flag q ≠ true := by
    intro he
    have hc := mem_pi.mp hmask q (mem_univ _)
    change (splitScorePairs μ x).2 q ∈ forwardScoreCellFlagEvent
      (diagonalPairAt (splitScorePairs μ x).1 m).1
      (diagonalPairAt (splitScorePairs μ x).1 (μ.symm w)).2 (flag q) at hc
    rw [he, forwardScoreCellFlagEvent, if_pos rfl, forwardEligibleScoreCell,
      splitScorePairs_offDiagonal_apply, diagonalPairAt_splitScorePairs,
      diagonalPairAt_splitScorePairs] at hc
    exact hw.not_gt (by simpa only [q, Equiv.apply_symm_apply, mem_Iio] using (mem_prod.mp hc).2)
  simpa only [splitScorePairs_offDiagonal_apply, q, Equiv.apply_symm_apply] using
    congrArg Prod.snd (h.inactiveCell_eq ⟨q, hq⟩)
private theorem SameReverseReveal.reverseSuccessor_iff (h : SameReverseReveal μ flag x y)
    (hsx : IsScoreStable x μ) (hsy : IsScoreStable y μ)
    (htx : ∀ r, Function.Injective (x r)) (hty : ∀ r, Function.Injective (y r))
    (hmx : (splitScorePairs μ x).2 ∈ forwardScoreMaskEvent (splitScorePairs μ x).1 flag)
    (hmy : (splitScorePairs μ y).2 ∈ forwardScoreMaskEvent (splitScorePairs μ y).1 flag)
    (w j : Fin n) (hj : j ≠ μ.symm w) :
    IsSuccessor (swapProfile (profileOfScores x)) μ.symm w j ↔
      IsSuccessor (swapProfile (profileOfScores y)) μ.symm w j := by
  let i := μ.symm w
  have hcol := congrFun (congrArg Prod.snd h.observed) i
  have hx := isSuccessor_swapProfile_iff_forwardInactiveReverseArcEvent μ x flag hsx htx hmx i j hj
  have hy := isSuccessor_swapProfile_iff_forwardInactiveReverseArcEvent μ y flag hsy hty hmy i j hj
  change _ ↔ (forwardRevealWithColumns flag (splitScorePairs μ x).2).2 i ∈
    forwardInactiveReverseArcEvent (splitScorePairs μ x).1 flag i j at hx
  rw [hcol, h.diagonal] at hx
  simpa only [i, Equiv.apply_symm_apply] using hx.trans hy.symm
private theorem SameReverseReveal.forwardExposed_iff (h : SameReverseReveal μ flag x y)
    (htx : ∀ r, Function.Injective (x r)) (hty : ∀ r, Function.Injective (y r))
    (hmx : (splitScorePairs μ x).2 ∈ forwardScoreMaskEvent (splitScorePairs μ x).1 flag)
    (hmy : (splitScorePairs μ y).2 ∈ forwardScoreMaskEvent (splitScorePairs μ y).1 flag) :
    IsExposedRotation (profileOfScores x) μ ρ ↔ IsExposedRotation (profileOfScores y) μ ρ := by
  rw [isExposedRotation_iff_forwardRevealExposureEvent μ ρ x flag htx hmx,
    isExposedRotation_iff_forwardRevealExposureEvent μ ρ y flag hty hmy, h.observed]
private theorem reverseScore_spouse_lt
    (ht : ∀ r, Function.Injective (x r))
    {w j : Fin n} (h : IsSuccessor (swapProfile (profileOfScores x)) μ.symm w j) :
    x (.inr w) (μ.symm w) < x (.inr w) j :=
  (rankPermutation_lt_iff (ht (.inr w)) _ _).mp h.eligible.1
private theorem SameReverseReveal.crossRectangle
    (h : SameReverseReveal μ flag x y)
    (hmx : (splitScorePairs μ x).2 ∈ forwardScoreMaskEvent (splitScorePairs μ x).1 flag)
    (htx : ∀ r, Function.Injective (x r))
    (hσ : RealizesSuccessorPermutation (swapProfile (profileOfScores x)) μ.symm σ)
    {m w : Fin n}
    (hR : IsPivotCrossRectangle x μ (undoReverseRotation μ σ) ρ m w) :
    IsPivotCrossRectangle y μ (undoReverseRotation μ σ) ρ m w := by
  have hw : w ∈ σ.support := Equiv.Perm.mem_support.mpr fun he ↦
    hR.2.1 (by rw [undoReverseRotation_symm_apply, he])
  have hf := h.female_eq_of_spouse_lt hmx hR.2.2.2.2.1
  have hj := h.female_eq_of_spouse_lt hmx (reverseScore_spouse_lt htx (hσ w hw))
  unfold IsPivotCrossRectangle
  rw [← h.male_eq, ← h.male_eq, ← h.male_eq, ← h.female_spouse_eq, ← hf,
    undoReverseRotation_symm_apply, ← hj, ← undoReverseRotation_symm_apply]
  exact hR
theorem filteredReverseSupportFamily_eq_of_same_forwardReveal
    (h : SameReverseReveal μ flag x y)
    (hsx : IsScoreStable x μ) (hsy : IsScoreStable y μ)
    (htx : ∀ r, Function.Injective (x r)) (hty : ∀ r, Function.Injective (y r))
    (hmx : (splitScorePairs μ x).2 ∈ forwardScoreMaskEvent (splitScorePairs μ x).1 flag)
    (hmy : (splitScorePairs μ y).2 ∈ forwardScoreMaskEvent (splitScorePairs μ y).1 flag)
    (hρx : IsExposedRotation (profileOfScores x) μ ρ) (k L : ℕ) (t : ℝ) :
    filteredReverseSupportFamily μ ρ flag k L t x =
      filteredReverseSupportFamily μ ρ flag k L t y := by
  classical
  have hρy := h.forwardExposed_iff htx hty hmx hmy |>.mp hρx
  ext σ
  simp only [filteredReverseSupportFamily, Finset.mem_filter, compatibleReverseSupportFamily,
    mem_compatibleReversePermutations]
  have hreal : RealizesSuccessorPermutation (swapProfile (profileOfScores x)) μ.symm σ ↔
      RealizesSuccessorPermutation (swapProfile (profileOfScores y)) μ.symm σ := by
    have hiff (w : Fin n) (hw : w ∈ σ.support) := h.reverseSuccessor_iff hsx hsy htx hty hmx hmy
      w (μ.symm (σ w)) (μ.symm.injective.ne (Equiv.Perm.mem_support.mp hw))
    exact ⟨fun hr w hw ↦ (hiff w hw).mp (hr w hw), fun hr w hw ↦ (hiff w hw).mpr (hr w hw)⟩
  have hcompat (hc : σ ∈ goodReverseSupportPermutations k (ρ.support.map μ.toEmbedding)
      (forwardMaskForbiddenTargets μ flag))
      (hrx : RealizesSuccessorPermutation (swapProfile (profileOfScores x)) μ.symm σ)
      (hry : RealizesSuccessorPermutation (swapProfile (profileOfScores y)) μ.symm σ) :
      IsExposedRotation (profileOfScores x) (undoReverseRotation μ σ) ρ ↔
        IsExposedRotation (profileOfScores y) (undoReverseRotation μ σ) ρ := by
    have hdisj : ∀ m ∈ ρ.support, μ m ∉ σ.support := by
      exact fun m hm hms ↦ (mem_goodReverseSupportPermutations.mp hc).2 _ hms |>.1
        (Finset.mem_map.mpr ⟨m, hm, rfl⟩)
    have hfixed (m : Fin n) (hm : ρ m ≠ m) : undoReverseRotation μ σ m = μ m :=
      undoReverseRotation_apply_of_not_mem_support (hdisj m (Equiv.Perm.mem_support.mpr hm))
    have hxN := (isStable_profileOfScores_iff htx _).mp
      (hrx.undo_stable ((isStable_profileOfScores_iff htx μ).mpr hsx))
    have hyN := (isStable_profileOfScores_iff hty _).mp
      (hry.undo_stable ((isStable_profileOfScores_iff hty μ).mpr hsy))
    rw [isExposedRotation_profileOfScores_iff_no_pivotCrossRectangle htx hρx hxN hfixed,
      isExposedRotation_profileOfScores_iff_no_pivotCrossRectangle hty hρy hyN hfixed]
    exact ⟨fun hn m w hr ↦ hn m w (h.symm.crossRectangle hmy hty hry hr),
      fun hn m w hr ↦ hn m w (h.crossRectangle hmx htx hrx hr)⟩
  have hinc (hrx : RealizesSuccessorPermutation (swapProfile (profileOfScores x)) μ.symm σ) :
      reverseCollectionIncrementGood x μ σ t ↔ reverseCollectionIncrementGood y μ σ t := by
    have he (w : Fin n) (hw : w ∈ σ.support) :
        reverseScoreIncrement x μ w (μ.symm (σ w)) =
          reverseScoreIncrement y μ w (μ.symm (σ w)) := by
      unfold reverseScoreIncrement
      rw [h.female_eq_of_spouse_lt hmx (reverseScore_spouse_lt htx (hrx w hw)),
        h.female_spouse_eq]
    exact ⟨fun hi w hw ↦ he w hw ▸ hi w hw, fun hi w hw ↦ (he w hw).symm ▸ hi w hw⟩
  constructor
  · rintro ⟨⟨hc, hrx, hex⟩, hs, hi⟩
    have hry := hreal.mp hrx
    exact ⟨⟨hc, hry, (hcompat hc hrx hry).mp hex⟩, hs, (hinc hrx).mp hi⟩
  · rintro ⟨⟨hc, hry, hey⟩, hs, hi⟩
    have hrx := hreal.mpr hry
    exact ⟨⟨hc, hrx, (hcompat hc hrx hry).mpr hey⟩, hs, (hinc hrx).mpr hi⟩
private noncomputable def reverseRevealFillOffDiagonal (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool)
    (r : ForwardRevealedMaleScores flag × ForwardInactiveColumns flag) :
    OffDiagonalScorePairs n :=
  fun q ↦ if h : flag q = true then
    (r.1 ⟨q, h⟩, (diagonalPairAt d q.val.2).2 * (((q.val.1.val : ℝ) + 1) / (n + 1)))
  else r.2 q.val.2 ⟨⟨q, h⟩, rfl⟩
theorem measurable_reverseRevealFillOffDiagonal (flag : OffDiagonalCellIndex n → Bool) :
    Measurable (fun a : DiagonalScorePairs n ×
      (ForwardRevealedMaleScores flag × ForwardInactiveColumns flag) ↦
      reverseRevealFillOffDiagonal a.1 flag a.2) := by
  refine measurable_pi_iff.2 fun q ↦ ?_
  by_cases h : flag q = true
  · have hm : Measurable (fun a : DiagonalScorePairs n ×
        (ForwardRevealedMaleScores flag × ForwardInactiveColumns flag) ↦ a.2.1 ⟨q, h⟩) :=
      (measurable_pi_apply _).comp (measurable_fst.comp measurable_snd)
    have hf : Measurable (fun a : DiagonalScorePairs n ×
        (ForwardRevealedMaleScores flag × ForwardInactiveColumns flag) ↦
        (diagonalPairAt a.1 q.val.2).2) :=
      measurable_snd.comp ((measurable_pi_apply _).comp measurable_fst)
    simpa only [reverseRevealFillOffDiagonal, dif_pos h] using hm.prodMk (hf.mul_const _)
  · have hI : Measurable (fun a : DiagonalScorePairs n ×
        (ForwardRevealedMaleScores flag × ForwardInactiveColumns flag) ↦
        a.2.2 q.val.2 ⟨⟨q, h⟩, rfl⟩) :=
      (measurable_pi_apply _).comp ((measurable_pi_apply _).comp
        (measurable_snd.comp measurable_snd))
    simpa only [reverseRevealFillOffDiagonal, dif_neg h] using hI
private noncomputable def reverseRevealFill (μ : Matching n) (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool)
    (r : ForwardRevealedMaleScores flag × ForwardInactiveColumns flag) : ScoreProfile n :=
  (splitScorePairs μ).symm (d, reverseRevealFillOffDiagonal d flag r)
theorem measurable_reverseRevealFill (μ : Matching n) (flag : OffDiagonalCellIndex n → Bool) :
    Measurable (fun a : DiagonalScorePairs n ×
      (ForwardRevealedMaleScores flag × ForwardInactiveColumns flag) ↦
      reverseRevealFill μ a.1 flag a.2) :=
  (splitScorePairs μ).symm.measurable.comp
    (measurable_fst.prodMk (measurable_reverseRevealFillOffDiagonal flag))
@[simp] theorem splitScorePairs_reverseRevealFill (μ : Matching n) (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool)
    (r : ForwardRevealedMaleScores flag × ForwardInactiveColumns flag) :
    splitScorePairs μ (reverseRevealFill μ d flag r) =
      (d, reverseRevealFillOffDiagonal d flag r) :=
  (splitScorePairs μ).apply_symm_apply _
@[simp] theorem forwardRevealWithColumns_reverseRevealFillOffDiagonal (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool)
    (r : ForwardRevealedMaleScores flag × ForwardInactiveColumns flag) :
    forwardRevealWithColumns flag (reverseRevealFillOffDiagonal d flag r) = r := by
  apply Prod.ext
  · funext q
    change ((reverseRevealFillOffDiagonal d flag r) q.val).1 = _
    simp only [reverseRevealFillOffDiagonal, dif_pos q.property]
  · funext i q
    obtain ⟨q, rfl⟩ := q
    change (reverseRevealFillOffDiagonal d flag r) q.val = _
    simp only [reverseRevealFillOffDiagonal, dif_neg q.property]
private noncomputable def discardActiveFemale (μ : Matching n) (flag : OffDiagonalCellIndex n → Bool)
    (x : ScoreProfile n) : ScoreProfile n :=
  reverseRevealFill μ (splitScorePairs μ x).1 flag
    (forwardRevealWithColumns flag (splitScorePairs μ x).2)
theorem sameReverseReveal_discardActiveFemale (μ : Matching n)
    (flag : OffDiagonalCellIndex n → Bool) (x : ScoreProfile n) :
    SameReverseReveal μ flag x (discardActiveFemale μ flag x) := by
  constructor <;> simp only [discardActiveFemale, splitScorePairs_reverseRevealFill,
    forwardRevealWithColumns_reverseRevealFillOffDiagonal]
private def markedCellActive (μ : Matching n) (flag : OffDiagonalCellIndex n → Bool)
    (m w : Fin n) : Prop :=
  ∃ h : m ≠ μ.symm w, flag ⟨(m, μ.symm w), h⟩ = true
private theorem activeCell_scores
    (hmask : (splitScorePairs μ x).2 ∈ forwardScoreMaskEvent (splitScorePairs μ x).1 flag)
    {m w : Fin n} (ha : markedCellActive μ flag m w) :
    x (.inl m) (μ m) < x (.inl m) w ∧ x (.inr w) m < x (.inr w) (μ.symm w) := by
  obtain ⟨hne, hf⟩ := ha
  let q : OffDiagonalCellIndex n := ⟨(m, μ.symm w), hne⟩
  have hc := mem_pi.mp hmask q (mem_univ _)
  change (splitScorePairs μ x).2 q ∈ forwardScoreCellFlagEvent
    (diagonalPairAt (splitScorePairs μ x).1 m).1
    (diagonalPairAt (splitScorePairs μ x).1 (μ.symm w)).2 (flag q) at hc
  rw [show flag q = true from hf, forwardScoreCellFlagEvent, if_pos rfl,
    forwardEligibleScoreCell, splitScorePairs_offDiagonal_apply,
    diagonalPairAt_splitScorePairs, diagonalPairAt_splitScorePairs] at hc
  simpa only [q, Equiv.apply_symm_apply, mem_prod, mem_Ioi, mem_Iio] using hc
private theorem spouse_le_female_of_not_active (hs : IsScoreStable x μ)
    (ht : ∀ row, Function.Injective (x row))
    (hmask : (splitScorePairs μ x).2 ∈ forwardScoreMaskEvent (splitScorePairs μ x).1 flag)
    {m w : Fin n} (ha : ¬ markedCellActive μ flag m w) :
    x (.inr w) (μ.symm w) ≤ x (.inr w) m := by
  apply le_of_not_gt
  intro hf
  have hne : m ≠ μ.symm w := fun he ↦ hf.ne (congrArg (x (.inr w)) he)
  have hw : μ m ≠ w := fun he ↦ hne (μ.symm_apply_eq.mpr he.symm).symm
  have hm : x (.inl m) (μ m) < x (.inl m) w :=
    lt_of_le_of_ne (le_of_not_gt fun hlt ↦ hs m w ⟨hw, hlt, hf⟩)
      (fun he ↦ hw (ht (.inl m) he))
  let q : OffDiagonalCellIndex n := ⟨(m, μ.symm w), hne⟩
  have hq : flag q ≠ true := fun he ↦ ha ⟨hne, he⟩
  have hc := mem_pi.mp hmask q (mem_univ _)
  change (splitScorePairs μ x).2 q ∈ forwardScoreCellFlagEvent
    (diagonalPairAt (splitScorePairs μ x).1 m).1
    (diagonalPairAt (splitScorePairs μ x).1 (μ.symm w)).2 (flag q) at hc
  rw [forwardScoreCellFlagEvent, if_neg hq, forwardEligibleScoreCell,
    splitScorePairs_offDiagonal_apply, diagonalPairAt_splitScorePairs,
    diagonalPairAt_splitScorePairs] at hc
  apply hc
  simpa only [q, Equiv.apply_symm_apply, mem_prod, mem_Ioi, mem_Iio] using And.intro hm hf
private theorem female_discardActiveFemale_of_active {m w : Fin n}
    (ha : markedCellActive μ flag m w) :
    discardActiveFemale μ flag x (.inr w) m =
      x (.inr w) (μ.symm w) * (((m.val : ℝ) + 1) / (n + 1)) := by
  obtain ⟨hne, hf⟩ := ha
  let q : OffDiagonalCellIndex n := ⟨(m, μ.symm w), hne⟩
  have hq : flag q = true := hf
  have h := congrArg (fun a ↦ (a.2 q).2)
    (splitScorePairs_reverseRevealFill μ (splitScorePairs μ x).1 flag
      (forwardRevealWithColumns flag (splitScorePairs μ x).2))
  simpa only [discardActiveFemale, splitScorePairs_offDiagonal_apply, q, Equiv.apply_symm_apply,
    reverseRevealFillOffDiagonal, dif_pos hq, diagonalPairAt_splitScorePairs] using h
private theorem female_discardActiveFemale_of_not_active {m w : Fin n}
    (ha : ¬ markedCellActive μ flag m w) :
    discardActiveFemale μ flag x (.inr w) m = x (.inr w) m := by
  have h := sameReverseReveal_discardActiveFemale μ flag x
  by_cases hm : m = μ.symm w
  · subst m
    exact (h.female_spouse_eq w).symm
  · let q : OffDiagonalCellIndex n := ⟨(m, μ.symm w), hm⟩
    have hq : flag q ≠ true := fun he ↦ ha ⟨hm, he⟩
    simpa only [splitScorePairs_offDiagonal_apply, q, Equiv.apply_symm_apply] using
      (congrArg Prod.snd (h.inactiveCell_eq ⟨q, hq⟩)).symm
private theorem fraction_lt_one (m : Fin n) : ((m.val : ℝ) + 1) / (n + 1) < 1 := by
  apply (div_lt_iff₀ (by positivity : (0 : ℝ) < n + 1)).mpr
  rw [one_mul]
  have hm : (m.val : ℝ) < n := by exact_mod_cast m.isLt
  linarith
private theorem female_discardActiveFemale_lt_of_active
    (h0 : ∀ i j, 0 ≤ x i j)
    (hmask : (splitScorePairs μ x).2 ∈ forwardScoreMaskEvent (splitScorePairs μ x).1 flag)
    {m w : Fin n} (ha : markedCellActive μ flag m w) :
    discardActiveFemale μ flag x (.inr w) m < x (.inr w) (μ.symm w) := by
  have hpos := (h0 (.inr w) m).trans_lt (activeCell_scores hmask ha).2
  rw [female_discardActiveFemale_of_active ha]
  simpa only [mul_one] using mul_lt_mul_of_pos_left (fraction_lt_one m) hpos
theorem discardActiveFemale_valid (hs : IsScoreStable x μ)
    (ht : ∀ row, Function.Injective (x row)) (h0 : ∀ i j, 0 ≤ x i j)
    (hmask : (splitScorePairs μ x).2 ∈ forwardScoreMaskEvent (splitScorePairs μ x).1 flag) :
    let y := discardActiveFemale μ flag x
    IsScoreStable y μ ∧ (∀ row, Function.Injective (y row)) ∧
      (splitScorePairs μ y).2 ∈ forwardScoreMaskEvent (splitScorePairs μ y).1 flag := by
  intro y
  let h := sameReverseReveal_discardActiveFemale μ flag x
  change SameReverseReveal μ flag x y at h
  have hlt {m w : Fin n} (ha : markedCellActive μ flag m w) :
      y (.inr w) m < x (.inr w) (μ.symm w) :=
    female_discardActiveFemale_lt_of_active h0 hmask ha
  have hunchanged {m w : Fin n} (ha : ¬ markedCellActive μ flag m w) :
      y (.inr w) m = x (.inr w) m := female_discardActiveFemale_of_not_active ha
  have hnot {m w : Fin n} (ha : ¬ markedCellActive μ flag m w) :
      x (.inr w) (μ.symm w) ≤ y (.inr w) m :=
    (spouse_le_female_of_not_active hs ht hmask ha).trans_eq (hunchanged ha).symm
  refine ⟨?_, ?_, ?_⟩
  · intro m w hb
    by_cases ha : markedCellActive μ flag m w
    · have hm := (activeCell_scores hmask ha).1
      rw [h.male_eq, h.male_eq] at hm
      exact hm.not_gt hb.2.1
    · exact (hnot ha).not_gt (by rw [h.female_spouse_eq]; exact hb.2.2)
  · intro r
    cases r with
    | inl m =>
      intro a b he
      exact ht (.inl m) (by simpa only [h.male_eq] using he)
    | inr w =>
      intro a b he
      by_cases ha : markedCellActive μ flag a w <;> by_cases hb : markedCellActive μ flag b w
      · have hpos := (h0 (.inr w) a).trans_lt (activeCell_scores hmask ha).2
        change discardActiveFemale μ flag x (.inr w) a =
          discardActiveFemale μ flag x (.inr w) b at he
        rw [female_discardActiveFemale_of_active ha, female_discardActiveFemale_of_active hb] at he
        have hdiv := mul_left_cancel₀ hpos.ne' he
        have hcast : (a.val : ℝ) = (b.val : ℝ) := by
          have hh := (div_left_inj' (by positivity : (n : ℝ) + 1 ≠ 0)).mp hdiv
          linarith
        exact Fin.ext (by exact_mod_cast hcast)
      · exact ((he ▸ hlt ha).not_ge (hnot hb)).elim
      · exact ((he.symm ▸ hlt hb).not_ge (hnot ha)).elim
      · exact ht (.inr w) ((hunchanged ha).symm.trans (he.trans (hunchanged hb)))
  · apply mem_pi.mpr
    intro q _
    let m := q.val.1
    let i := q.val.2
    change (splitScorePairs μ y).2 q ∈ forwardScoreCellFlagEvent
      (diagonalPairAt (splitScorePairs μ y).1 m).1
      (diagonalPairAt (splitScorePairs μ y).1 i).2 (flag q)
    by_cases hf : flag q = true
    · have hq : markedCellActive μ flag m (μ i) := by
        have hne : m ≠ μ.symm (μ i) := by
          simpa only [Equiv.symm_apply_apply] using q.property
        refine ⟨hne, ?_⟩
        convert hf using 2
        exact Subtype.ext (by simp only [m, i, Equiv.symm_apply_apply])
      have hm := (activeCell_scores hmask hq).1
      rw [h.male_eq, h.male_eq] at hm
      have hY := hlt hq
      rw [h.female_spouse_eq] at hY
      rw [hf, forwardScoreCellFlagEvent, if_pos rfl, forwardEligibleScoreCell,
        splitScorePairs_offDiagonal_apply, diagonalPairAt_splitScorePairs,
        diagonalPairAt_splitScorePairs]
      exact ⟨hm, by simpa only [Equiv.symm_apply_apply, mem_Iio, m, i] using hY⟩
    · rw [← h.diagonal, ← h.inactiveCell_eq ⟨q, hf⟩]
      exact mem_pi.mp hmask q (mem_univ _)
theorem filteredReverseSupportFamily_eq_discardActiveFemale
    (hs : IsScoreStable x μ) (ht : ∀ row, Function.Injective (x row))
    (h0 : ∀ i j, 0 ≤ x i j)
    (hmask : (splitScorePairs μ x).2 ∈ forwardScoreMaskEvent (splitScorePairs μ x).1 flag)
    (hρ : IsExposedRotation (profileOfScores x) μ ρ) (k L : ℕ) (t : ℝ) :
    filteredReverseSupportFamily μ ρ flag k L t x =
      filteredReverseSupportFamily μ ρ flag k L t (discardActiveFemale μ flag x) := by
  obtain ⟨hs', ht', hmask'⟩ := discardActiveFemale_valid hs ht h0 hmask
  exact filteredReverseSupportFamily_eq_of_same_forwardReveal
    (sameReverseReveal_discardActiveFemale μ flag x) hs hs' ht ht' hmask hmask' hρ k L t
@[simp] theorem discardActiveFemale_reconstruct (μ : Matching n) (d : DiagonalScorePairs n)
    (z : OffDiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool) :
    discardActiveFemale μ flag ((splitScorePairs μ).symm (d, z)) =
      reverseRevealFill μ d flag (forwardRevealWithColumns flag z) := by
  simp only [discardActiveFemale, MeasurableEquiv.apply_symm_apply]
theorem SameReverseReveal.localEligibility_iff (h : SameReverseReveal μ flag x y)
    (hmx : (splitScorePairs μ x).2 ∈ forwardScoreMaskEvent (splitScorePairs μ x).1 flag)
    (hmy : (splitScorePairs μ y).2 ∈ forwardScoreMaskEvent (splitScorePairs μ y).1 flag)
    (b A B : ℝ) :
    IsLocallyEligiblePivot b A B x μ ρ ↔ IsLocallyEligiblePivot b A B y μ ρ := by
  have ex := isLocallyEligiblePivot_reconstruct_iff (b := b) (A := A) (B := B) μ ρ
    (splitScorePairs μ x).1 (splitScorePairs μ x).2 flag hmx
  have ey := isLocallyEligiblePivot_reconstruct_iff (b := b) (A := A) (B := B) μ ρ
    (splitScorePairs μ y).1 (splitScorePairs μ y).2 flag hmy
  rw [Prod.mk.eta, MeasurableEquiv.symm_apply_apply, h.diagonal,
    congrArg Prod.fst h.observed] at ex
  rw [Prod.mk.eta, MeasurableEquiv.symm_apply_apply] at ey
  exact ex.trans ey.symm
theorem localFilteredDecorationCount_eq_discardActiveFemale
    (hs : IsScoreStable x μ) (ht : ∀ row, Function.Injective (x row))
    (h0 : ∀ i j, 0 ≤ x i j)
    (hmask : (splitScorePairs μ x).2 ∈ forwardScoreMaskEvent (splitScorePairs μ x).1 flag)
    (b A B : ℝ) (K L : ℕ) (ρ : Matching n) :
    localFilteredDecorationCount b A B K L μ ρ x =
      localFilteredDecorationCount b A B K L μ ρ (discardActiveFemale μ flag x) := by
  classical
  obtain ⟨_, _, hmask'⟩ := discardActiveFemale_valid hs ht h0 hmask
  have h := sameReverseReveal_discardActiveFemale μ flag x
  have he := h.localEligibility_iff (ρ := ρ) hmask hmask' b A B
  by_cases hE : IsLocallyEligiblePivot b A B x μ ρ
  · rw [localFilteredDecorationCount_of_eligible_of_fixedMask K L hE hmask,
      localFilteredDecorationCount_of_eligible_of_fixedMask K L (he.mp hE) hmask',
      ← h.diagonal]
    have hρ := (hE.isSoleForwardExposed ht).1
    congr 2
    ext σ
    simp only [mem_markedFilteredChoices]
    rw [filteredReverseSupportFamily_eq_discardActiveFemale hs ht h0 hmask hρ]
  · have hy := fun h' ↦ hE (he.mpr h')
    simp only [localFilteredDecorationCount, if_neg hE, if_neg hy]
theorem ae_diagonal_ae_localFilteredDecorationCount_eq_reverseRevealFill
    (b A B : ℝ) (K L : ℕ) (μ ρ : Matching n) :
    ∀ᵐ d ∂diagonalScoreLaw n, ∀ (flag : OffDiagonalCellIndex n → Bool)
      (U : Set (ForwardRevealedMaleScores flag)), ∀ᵐ z ∂forwardMaskRevealLaw d flag U,
      localFilteredDecorationCount b A B K L μ ρ ((splitScorePairs μ).symm (d, z)) =
        localFilteredDecorationCount b A B K L μ ρ
          (reverseRevealFill μ d flag (forwardRevealWithColumns flag z)) := by
  have hu : ∀ᵐ a ∂(diagonalScoreLaw n).prod (offDiagonalScoreLaw n),
      ∀ r i, (splitScorePairs μ).symm a r i ∈ Ioo (0 : ℝ) 1 :=
    (measurePreserving_splitScorePairs μ).symm.quasiMeasurePreserving.ae (ae_unitOpen_scores n)
  filter_upwards [ae_diagonal_ae_injective_scoreRows μ, Measure.ae_ae_of_ae_prod hu]
    with d ht h0
  intro flag U
  have hnon : MeasurableSet (offDiagonalNonblocking d) :=
    MeasurableSet.univ_pi fun _ ↦ (measurableSet_Iio.prod measurableSet_Iio).compl
  filter_upwards [ae_restrict_of_ae (ae_restrict_of_ae (ae_restrict_of_ae ht)),
    ae_restrict_of_ae (ae_restrict_of_ae (ae_restrict_of_ae h0)),
    ae_restrict_of_ae (ae_restrict_of_ae (ae_restrict_mem hnon)),
    ae_restrict_of_ae (ae_restrict_mem (measurableSet_forwardScoreMaskEvent d flag))]
    with z hz hu hstable hmask
  let x := (splitScorePairs μ).symm (d, z)
  have hsplit : splitScorePairs μ x = (d, z) := (splitScorePairs μ).apply_symm_apply _
  have hs : IsScoreStable x μ := (isScoreStable_iff_splitScorePairs μ x).mpr
    (by simpa only [hsplit] using hstable)
  have hm : (splitScorePairs μ x).2 ∈ forwardScoreMaskEvent (splitScorePairs μ x).1 flag := by
    simpa only [hsplit] using hmask
  simpa only [x, discardActiveFemale_reconstruct] using
    localFilteredDecorationCount_eq_discardActiveFemale hs hz
      (fun r i ↦ (hu r i).1.le) hm b A B K L ρ
end MarkedLP
end

-- PivotEnlargedConditionalMean
section
open Filter MeasureTheory Set StableMarriage
open scoped ENNReal
namespace MarkedLP
variable {n : ℕ}
private noncomputable def localPivotInactiveStatistic (b A B : ℝ) (K L : ℕ)
    (μ ρ : Matching n) (flag : OffDiagonalCellIndex n → Bool)
    (s : DiagonalScorePairs n × ForwardRevealedMaleScores flag × ForwardInactiveColumns flag) :
    ℝ≥0∞ :=
  ENNReal.ofReal (localFilteredDecorationCount b A B K L μ ρ (reverseRevealFill μ s.1 flag s.2))
theorem measurable_localPivotInactiveStatistic (b A B : ℝ) (K L : ℕ) (μ ρ : Matching n)
    (flag : OffDiagonalCellIndex n → Bool) :
    Measurable (localPivotInactiveStatistic b A B K L μ ρ flag) :=
  ENNReal.measurable_ofReal.comp ((measurable_localFilteredDecorationCount b A B K L μ ρ).comp
    (measurable_reverseRevealFill μ flag))
private theorem localPivotInactiveStatistic_le (b A B : ℝ) (K L : ℕ) (μ ρ : Matching n)
    (flag : OffDiagonalCellIndex n → Bool)
    (s : DiagonalScorePairs n × ForwardRevealedMaleScores flag × ForwardInactiveColumns flag) :
    localPivotInactiveStatistic b A B K L μ ρ flag s ≤ ENNReal.ofReal (n.factorial : ℝ) :=
  ENNReal.ofReal_le_ofReal (localFilteredDecorationCount_le_factorial b A B K L μ ρ _)
private noncomputable def localPivotInactiveMean (b A B : ℝ) (K L : ℕ) (μ ρ : Matching n)
    (x : ScoreProfile n) : ℝ :=
  (pivotInactiveMeanFromReveal (localPivotInactiveStatistic b A B K L μ ρ)
    (pivotMaleReveal μ x)).toReal
theorem measurable_maleReveal_localPivotInactiveMean (b A B : ℝ) (K L : ℕ)
    (μ ρ : Matching n) :
    Measurable[pivotMaleRevealSpace μ] (localPivotInactiveMean b A B K L μ ρ) := by
  have hmap : Measurable[pivotMaleRevealSpace μ] (pivotMaleReveal μ) :=
    fun S hS ↦ ⟨S, hS, rfl⟩
  exact ENNReal.measurable_toReal.comp
    ((measurable_pivotInactiveMeanFromReveal
      (measurable_localPivotInactiveStatistic b A B K L μ ρ)).comp hmap)
private theorem ae_localPivotInactiveMeanENN_le (b A B : ℝ) (K L : ℕ) (μ ρ : Matching n) :
    ∀ᵐ x ∂stableMarkScoreLaw μ, pivotInactiveMeanFromReveal
      (localPivotInactiveStatistic b A B K L μ ρ) (pivotMaleReveal μ x) ≤
        ENNReal.ofReal (n.factorial : ℝ) :=
  ae_pivotInactiveMeanFromReveal_le_stableMarkScoreLaw μ
    (localPivotInactiveStatistic_le b A B K L μ ρ)
theorem integrable_localPivotInactiveMean (b A B : ℝ) (K L : ℕ) (μ ρ : Matching n) :
    Integrable (localPivotInactiveMean b A B K L μ ρ) (stableMarkScoreLaw μ) := by
  refine (integrable_const (n.factorial : ℝ)).mono'
    (((measurable_maleReveal_localPivotInactiveMean b A B K L μ ρ).mono
      (pivotMaleRevealSpace_le μ) le_rfl).aestronglyMeasurable) ?_
  filter_upwards [ae_localPivotInactiveMeanENN_le b A B K L μ ρ] with x hx
  have hnonneg : 0 ≤ localPivotInactiveMean b A B K L μ ρ x := ENNReal.toReal_nonneg
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hx).trans_eq
    (ENNReal.toReal_ofReal (Nat.cast_nonneg _))
theorem setIntegral_localPivotInactiveMean_eq {b A B : ℝ} (K L : ℕ) (μ ρ : Matching n)
    {S : Set (ScoreProfile n)} (hS : MeasurableSet[pivotFullRevealSpace μ] S) :
    (∫ x in S, localPivotInactiveMean b A B K L μ ρ x ∂stableMarkScoreLaw μ) =
      ∫ x in S, localFilteredDecorationCount b A B K L μ ρ x ∂stableMarkScoreLaw μ := by
  let F := localPivotInactiveStatistic b A B K L μ ρ
  let Z := localFilteredDecorationCount b A B K L μ ρ
  let ν := stableMarkScoreLaw μ
  let m := localPivotInactiveMean b A B K L μ ρ
  have hfactor : ∀ᵐ d ∂diagonalScoreLaw n, ∀ flag,
      ∀ᵐ z ∂forwardMaskRevealLaw d flag univ,
        ENNReal.ofReal (Z ((splitScorePairs μ).symm (d, z))) =
          F flag (d, (forwardRevealWithColumns flag z).1, (forwardRevealWithColumns flag z).2) := by
    filter_upwards [ae_diagonal_ae_localFilteredDecorationCount_eq_reverseRevealFill b A B K L μ ρ]
      with d hd flag
    exact (hd flag univ).mono fun z hz ↦ congrArg ENNReal.ofReal hz
  have he := setLIntegral_stableMark_fullReveal_eq_inactiveMean μ
    (measurable_localPivotInactiveStatistic b A B K L μ ρ)
    (ENNReal.measurable_ofReal.comp (measurable_localFilteredDecorationCount b A B K L μ ρ))
    (ae_diagonalFemale_mem_Ico n) hfactor hS
  have hraw : (fun x ↦ ENNReal.ofReal (m x)) =ᵐ[ν.restrict S]
      fun x ↦ pivotInactiveMeanFromReveal F (pivotMaleReveal μ x) := by
    filter_upwards [ae_restrict_of_ae (ae_localPivotInactiveMeanENN_le b A B K L μ ρ)] with x hx
    exact ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hx)
  have hnm : 0 ≤ᵐ[ν.restrict S] m := Eventually.of_forall fun _ ↦ ENNReal.toReal_nonneg
  have hnZ : 0 ≤ᵐ[ν.restrict S] Z :=
    Eventually.of_forall (localFilteredDecorationCount_nonneg b A B K L μ ρ)
  change (∫ x in S, m x ∂ν) = ∫ x in S, Z x ∂ν
  rw [integral_eq_lintegral_of_nonneg_ae hnm
      ((integrable_localPivotInactiveMean b A B K L μ ρ).integrableOn (s := S)).aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae hnZ
      ((integrable_localFilteredDecorationCount b A B K L μ ρ ν).integrableOn (s := S)).aestronglyMeasurable,
    lintegral_congr_ae hraw]
  exact congrArg ENNReal.toReal he.symm
theorem localPivotInactiveMean_ae_eq_conditionalMean (b A B : ℝ) (K L : ℕ)
    (μ ρ : Matching n) :
    localPivotInactiveMean b A B K L μ ρ =ᵐ[stableMarkScoreLaw μ]
      localPivotConditionalMean b A B K L μ ρ := by
  let ν := stableMarkScoreLaw μ
  have hf := integrable_localFilteredDecorationCount b A B K L μ ρ ν
  have hg := integrable_localPivotInactiveMean b A B K L μ ρ
  have hm := (measurable_maleReveal_localPivotInactiveMean b A B K L μ ρ).stronglyMeasurable
  exact ae_eq_condExp_of_forall_setIntegral_eq (pivotMaleRevealSpace_le μ) hf
    (fun _ _ _ ↦ hg.integrableOn) (fun _ hS _ ↦
      setIntegral_localPivotInactiveMean_eq K L μ ρ (pivotMaleRevealSpace_le_full μ _ hS))
    hm.aestronglyMeasurable
theorem localPivotConditionalMean_ae_eq_fullReveal (b A B : ℝ) (K L : ℕ) (μ ρ : Matching n) :
    localPivotConditionalMean b A B K L μ ρ =ᵐ[stableMarkScoreLaw μ]
      (stableMarkScoreLaw μ)[localFilteredDecorationCount b A B K L μ ρ|pivotFullRevealSpace μ] := by
  let ν := stableMarkScoreLaw μ
  have hf := integrable_localFilteredDecorationCount b A B K L μ ρ ν
  have hg := integrable_localPivotInactiveMean b A B K L μ ρ
  have hm := (measurable_maleReveal_localPivotInactiveMean b A B K L μ ρ).stronglyMeasurable
  have hG := ae_eq_condExp_of_forall_setIntegral_eq (pivotFullRevealSpace_le μ) hf
    (fun _ _ _ ↦ hg.integrableOn) (fun _ hS _ ↦ setIntegral_localPivotInactiveMean_eq K L μ ρ hS)
    (hm.mono (pivotMaleRevealSpace_le_full μ)).aestronglyMeasurable
  exact (localPivotInactiveMean_ae_eq_conditionalMean b A B K L μ ρ).symm.trans hG
theorem localPivotConditionalMean_mem_Icc_ae (b A B : ℝ) (K L : ℕ) (μ ρ : Matching n) :
    ∀ᵐ x ∂stableMarkScoreLaw μ,
      localPivotConditionalMean b A B K L μ ρ x ∈ Icc (0 : ℝ) (n.factorial : ℝ) := by
  filter_upwards [localPivotInactiveMean_ae_eq_conditionalMean b A B K L μ ρ,
    ae_localPivotInactiveMeanENN_le b A B K L μ ρ] with x h hx
  rw [← h]
  exact ⟨ENNReal.toReal_nonneg, (ENNReal.toReal_mono ENNReal.ofReal_ne_top hx).trans_eq
    (ENNReal.toReal_ofReal (Nat.cast_nonneg _))⟩
theorem integral_localPivotCentered_mul_eq_zero (b A B : ℝ) (K L : ℕ)
    (μ ρ : Matching n) (g : ScoreProfile n → ℝ)
    (hg : AEStronglyMeasurable[pivotFullRevealSpace μ] g (stableMarkScoreLaw μ))
    (hZg : Integrable (localFilteredDecorationCount b A B K L μ ρ * g) (stableMarkScoreLaw μ))
    (hMg : Integrable (localPivotConditionalMean b A B K L μ ρ * g) (stableMarkScoreLaw μ)) :
    (∫ x, (localFilteredDecorationCount b A B K L μ ρ x -
      localPivotConditionalMean b A B K L μ ρ x) * g x ∂stableMarkScoreLaw μ) = 0 := by
  let ν := stableMarkScoreLaw μ
  let Z := localFilteredDecorationCount b A B K L μ ρ
  let M := localPivotConditionalMean b A B K L μ ρ
  let m := pivotFullRevealSpace μ
  have hpull : ν[Z * g|m] =ᵐ[ν] M * g :=
    (condExp_mul_of_aestronglyMeasurable_right hg hZg
      (integrable_localFilteredDecorationCount b A B K L μ ρ ν)).trans
      ((localPivotConditionalMean_ae_eq_fullReveal b A B K L μ ρ).symm.mono
        fun x hx ↦ congrArg (fun t : ℝ ↦ t * g x) hx)
  have heq : (∫ x, (Z * g) x ∂ν) = ∫ x, (M * g) x ∂ν :=
    (integral_condExp (pivotFullRevealSpace_le μ)).symm.trans (integral_congr_ae hpull)
  change (∫ x, (Z x - M x) * g x ∂ν) = 0
  simp_rw [sub_mul]
  exact (integral_sub hZg hMg).trans (sub_eq_zero.mpr heq)
end MarkedLP
end

-- PivotLaterRevealReplay
section
open MeasureTheory Set StableMarriage
namespace MarkedLP
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
theorem FullForwardRevealAgrees.womanSpouse (h : FullForwardRevealAgrees x y A) (w : Fin n) :
    x (.inr w) (A.symm w) = y (.inr w) (A.symm w) := by
  simpa only [A.apply_symm_apply] using (h.spouse (A.symm w)).2
private theorem rankPermutation_le_iff_of_injective {u : Fin n → ℝ}
    (hu : Function.Injective u) (i j : Fin n) :
    rankPermutation u i ≤ rankPermutation u j ↔ u i ≤ u j := by
  rw [← not_lt, ← not_lt, rankPermutation_lt_iff hu]
theorem isEligibleSuccessor_profileOfScores_iff (hx : ∀ row, Function.Injective (x row))
    (A : Matching n) (m w : Fin n) :
    IsEligibleSuccessor (profileOfScores x) A m w ↔ ScoreForwardEligible x A m w := by
  simp only [IsEligibleSuccessor, profileOfScores, ScoreForwardEligible,
    rankPermutation_lt_iff (hx (.inl m)), rankPermutation_lt_iff (hx (.inr w))]
theorem scoreForwardEligible_of_woman_lt (hA : IsScoreStable x A)
    {m w : Fin n} (hm : Function.Injective (x (.inl m)))
    (hw : x (.inr w) m < x (.inr w) (A.symm w)) :
    ScoreForwardEligible x A m w := by
  have hne : A m ≠ w := by
    rintro rfl
    rw [A.symm_apply_apply] at hw
    exact lt_irrefl _ hw
  have hle : x (.inl m) (A m) ≤ x (.inl m) w :=
    le_of_not_gt fun hlt ↦ hA m w ⟨hne, hlt, hw⟩
  exact ⟨lt_of_le_of_ne hle (fun he ↦ hne (hm he)), hw⟩
private theorem FullForwardRevealAgrees.replay_spouses (h : FullForwardRevealAgrees x y A)
    (hx : ∀ row, Function.Injective (x row))
    (hA : IsScoreStable x A) (hB : IsStable (profileOfScores x) B)
    (hAB : MenWeaklyPrefer (profileOfScores x) A B) :
    (∀ m, ScorePairAgrees x y m (B m)) ∧
      (∀ w, x (.inr w) (B.symm w) ≤ x (.inr w) (A.symm w)) := by
  obtain ⟨_, hpath⟩ :=
    exists_rotationSequence_of_menWeaklyPrefer ((isStable_profileOfScores_iff hx A).mpr hA) hB hAB
  have hw (w : Fin n) : x (.inr w) (B.symm w) ≤ x (.inr w) (A.symm w) :=
    (rankPermutation_le_iff_of_injective (hx (.inr w)) _ _).mp (hpath.womanRank_end_le w)
  refine ⟨fun m ↦ ?_, hw⟩
  by_cases he : A m = B m
  · rw [← he]
    exact h.spouse m
  · have hne : m ≠ A.symm (B m) := fun hh ↦ he ((A.symm_apply_eq).mp hh.symm).symm
    have hle : x (.inr (B m)) m ≤ x (.inr (B m)) (A.symm (B m)) := by
      simpa only [B.symm_apply_apply] using hw (B m)
    exact h.cell m (B m) (scoreForwardEligible_of_woman_lt hA (hx (.inl m))
      (lt_of_le_of_ne hle (fun heq ↦ hne (hx (.inr (B m)) heq))))
theorem FullForwardRevealAgrees.later (h : FullForwardRevealAgrees x y A)
    (hx : ∀ row, Function.Injective (x row)) (hy : ∀ row, Function.Injective (y row))
    (hAx : IsStable (profileOfScores x) A) (hAy : IsStable (profileOfScores y) A)
    (hBx : IsStable (profileOfScores x) B) (hAB : MenWeaklyPrefer (profileOfScores x) A B) :
    IsStable (profileOfScores y) B ∧ MenWeaklyPrefer (profileOfScores y) A B ∧
      FullForwardRevealAgrees x y B := by
  have hAx' := (isStable_profileOfScores_iff hx A).mp hAx
  have hAy' := (isStable_profileOfScores_iff hy A).mp hAy
  obtain ⟨hsp, hwx⟩ := h.replay_spouses hx hAx' hBx hAB
  have hwsp (w : Fin n) : x (.inr w) (B.symm w) = y (.inr w) (B.symm w) := by
    simpa only [B.apply_symm_apply] using (hsp (B.symm w)).2
  have hmx (m : Fin n) : x (.inl m) (A m) ≤ x (.inl m) (B m) :=
    (rankPermutation_le_iff_of_injective (hx (.inl m)) _ _).mp (hAB m)
  have hmy (m : Fin n) : y (.inl m) (A m) ≤ y (.inl m) (B m) := by
    rw [← (h.spouse m).1, ← (hsp m).1]
    exact hmx m
  have hwy (w : Fin n) : y (.inr w) (B.symm w) ≤ y (.inr w) (A.symm w) := by
    rw [← hwsp w, ← h.womanSpouse w]
    exact hwx w
  have hstable : IsScoreStable y B := by
    intro m w hb
    have he := scoreForwardEligible_of_woman_lt hAy' (hy (.inl m)) (hb.2.2.trans_le (hwy w))
    have hc := h.cell m w ((h.eligible_iff m w).mpr he)
    apply (isStable_profileOfScores_iff hx B).mp hBx m w
    exact ⟨hb.1, hc.1.symm ▸ (hsp m).1.symm ▸ hb.2.1, hc.2.symm ▸ (hwsp w).symm ▸ hb.2.2⟩
  refine ⟨(isStable_profileOfScores_iff hy B).mpr hstable,
    fun m ↦ (rankPermutation_le_iff_of_injective (hy (.inl m)) _ _).mpr (hmy m),
    ⟨hsp, ?_, ?_⟩⟩
  · intro m w
    constructor
    · intro he
      have hc := h.cell m w ⟨(hmx m).trans_lt he.1, he.2.trans_le (hwx w)⟩
      exact ⟨(hsp m).1 ▸ hc.1 ▸ he.1, hwsp w ▸ hc.2 ▸ he.2⟩
    · intro he
      have hc := h.symm.cell m w ⟨(hmy m).trans_lt he.1, he.2.trans_le (hwy w)⟩
      exact ⟨(hsp m).1.symm ▸ hc.1 ▸ he.1, (hwsp w).symm ▸ hc.2 ▸ he.2⟩
  · intro m w he
    exact h.cell m w ⟨(hmx m).trans_lt he.1, he.2.trans_le (hwx w)⟩
theorem FullForwardRevealAgrees.successor_iff (h : FullForwardRevealAgrees x y A)
    (hx : ∀ row, Function.Injective (x row)) (hy : ∀ row, Function.Injective (y row))
    (m w : Fin n) :
    IsSuccessor (profileOfScores x) A m w ↔ IsSuccessor (profileOfScores y) A m w := by
  have transport {u v : ScoreProfile n} (huv : FullForwardRevealAgrees u v A)
      (hu : ∀ row, Function.Injective (u row)) (hv : ∀ row, Function.Injective (v row))
      (hs : IsSuccessor (profileOfScores u) A m w) : IsSuccessor (profileOfScores v) A m w := by
    let ex := isEligibleSuccessor_profileOfScores_iff hu A m
    let ey := isEligibleSuccessor_profileOfScores_iff hv A m
    have hw := (ex w).mp hs.eligible
    refine ⟨(ey w).mpr ((huv.eligible_iff m w).mp hw), fun w' hw' ↦ ?_⟩
    have hw' := (huv.eligible_iff m w').mpr ((ey w').mp hw')
    have hle := (rankPermutation_le_iff_of_injective (hu (.inl m)) w w').mp
      (hs.min_rank w' ((ex w').mpr hw'))
    apply (rankPermutation_le_iff_of_injective (hv (.inl m)) w w').mpr
    rw [← (huv.cell m w hw).1, ← (huv.cell m w' hw').1]
    exact hle
  exact ⟨transport h hx hy, transport h.symm hy hx⟩
theorem FullForwardRevealAgrees.exposedRotation_iff (h : FullForwardRevealAgrees x y A)
    (hx : ∀ row, Function.Injective (x row)) (hy : ∀ row, Function.Injective (y row))
    (ρ : Matching n) :
    IsExposedRotation (profileOfScores x) A ρ ↔ IsExposedRotation (profileOfScores y) A ρ :=
  ⟨fun hρ ↦ ⟨hρ.isCycle, fun m hm ↦
      (h.successor_iff hx hy m _).mp (hρ.successor m hm)⟩,
    fun hρ ↦ ⟨hρ.isCycle, fun m hm ↦ (h.successor_iff hx hy m _).mpr (hρ.successor m hm)⟩⟩
theorem FullForwardRevealAgrees.pair_agrees_of_woman_le (h : FullForwardRevealAgrees x y A)
    (hx : ∀ row, Function.Injective (x row)) (hA : IsScoreStable x A) {m w : Fin n}
    (hw : x (.inr w) m ≤ x (.inr w) (A.symm w)) : ScorePairAgrees x y m w := by
  rcases lt_or_eq_of_le hw with hlt | he
  · exact h.cell m w (scoreForwardEligible_of_woman_lt hA (hx (.inl m)) hlt)
  · have hm : m = A.symm w := hx (.inr w) he
    have hw' : A m = w := ((Equiv.symm_apply_eq A).mp hm.symm).symm
    rw [← hw']
    exact h.spouse m
private theorem reverseEligible_profileOfScores_iff
    (hx : ∀ row, Function.Injective (x row)) (B : Matching n) (w m : Fin n) :
    IsEligibleSuccessor (swapProfile (profileOfScores x)) B.symm w m ↔
      x (.inr w) (B.symm w) < x (.inr w) m ∧ x (.inl m) w < x (.inl m) (B m) := by
  simp only [IsEligibleSuccessor, swapProfile, profileOfScores, Equiv.symm_symm,
    rankPermutation_lt_iff (hx (.inr w)), rankPermutation_lt_iff (hx (.inl m))]
private theorem reverseEligible_anchorHusband_of_changed
    (hx : ∀ row, Function.Injective (x row)) (hA : IsStable (profileOfScores x) A)
    (hB : IsStable (profileOfScores x) B) (hAB : MenWeaklyPrefer (profileOfScores x) A B)
    {w : Fin n} (hw : B.symm w ≠ A.symm w) :
    IsEligibleSuccessor (swapProfile (profileOfScores x)) B.symm w (A.symm w) := by
  obtain ⟨_, hpath⟩ := exists_rotationSequence_of_menWeaklyPrefer hA hB hAB
  apply (reverseEligible_profileOfScores_iff hx B w _).mpr
  constructor
  · apply (rankPermutation_lt_iff (hx (.inr w)) _ _).mp
    exact lt_of_le_of_ne (hpath.womanRank_end_le w)
      (fun he ↦ hw ((rankPermutation (x (.inr w))).injective he))
  · have hne : w ≠ B (A.symm w) := fun he ↦ hw ((Equiv.symm_apply_eq B).mpr he)
    have hle : x (.inl (A.symm w)) w ≤ x (.inl (A.symm w)) (B (A.symm w)) := by
      simpa only [A.apply_symm_apply] using
        (rankPermutation_le_iff_of_injective (hx (.inl (A.symm w))) _ _).mp (hAB (A.symm w))
    exact lt_of_le_of_ne hle (fun he ↦ hne (hx (.inl (A.symm w)) he))
private theorem FullForwardRevealAgrees.reverseSearchPrefix_iff (h : FullForwardRevealAgrees x y A)
    (hB : FullForwardRevealAgrees x y B)
    (hx : ∀ row, Function.Injective (x row)) (hy : ∀ row, Function.Injective (y row))
    (hAx : IsScoreStable x A) (hAy : IsScoreStable y A) (w m : Fin n) :
    (IsEligibleSuccessor (swapProfile (profileOfScores x)) B.symm w m ∧
      x (.inr w) m ≤ x (.inr w) (A.symm w)) ↔
    (IsEligibleSuccessor (swapProfile (profileOfScores y)) B.symm w m ∧
      y (.inr w) m ≤ y (.inr w) (A.symm w)) := by
  have transport {u v : ScoreProfile n} (huv : FullForwardRevealAgrees u v A)
      (hBuv : FullForwardRevealAgrees u v B)
      (hu : ∀ row, Function.Injective (u row)) (hv : ∀ row, Function.Injective (v row))
      (hAu : IsScoreStable u A) :
      (IsEligibleSuccessor (swapProfile (profileOfScores u)) B.symm w m ∧
        u (.inr w) m ≤ u (.inr w) (A.symm w)) →
      (IsEligibleSuccessor (swapProfile (profileOfScores v)) B.symm w m ∧
        v (.inr w) m ≤ v (.inr w) (A.symm w)) := by
    rintro ⟨he, hl⟩
    have hc := huv.pair_agrees_of_woman_le hu hAu hl
    refine ⟨(reverseEligible_profileOfScores_iff hv B w m).mpr ?_, ?_⟩
    · rw [← (hBuv.spouse m).1, ← hBuv.womanSpouse w, ← hc.1, ← hc.2]
      exact (reverseEligible_profileOfScores_iff hu B w m).mp he
    · rwa [← hc.2, ← huv.womanSpouse w]
  exact ⟨transport h hB hx hy hAx, transport h.symm hB.symm hy hx hAy⟩
theorem FullForwardRevealAgrees.reverseSuccessor_iff_of_changed (h : FullForwardRevealAgrees x y A)
    (hx : ∀ row, Function.Injective (x row)) (hy : ∀ row, Function.Injective (y row))
    (hAx : IsStable (profileOfScores x) A) (hAy : IsStable (profileOfScores y) A)
    (hBx : IsStable (profileOfScores x) B) (hAB : MenWeaklyPrefer (profileOfScores x) A B)
    {w : Fin n} (hw : B.symm w ≠ A.symm w) (m : Fin n) :
    IsSuccessor (swapProfile (profileOfScores x)) B.symm w m ↔
      IsSuccessor (swapProfile (profileOfScores y)) B.symm w m := by
  obtain ⟨hBy, hABy, hB⟩ := h.later hx hy hAx hAy hBx hAB
  have transport {u v : ScoreProfile n} (huv : FullForwardRevealAgrees u v A)
      (hBuv : FullForwardRevealAgrees u v B)
      (hu : ∀ row, Function.Injective (u row)) (hv : ∀ row, Function.Injective (v row))
      (hAu : IsStable (profileOfScores u) A) (hAv : IsStable (profileOfScores v) A)
      (hBu : IsStable (profileOfScores u) B)
      (hABu : MenWeaklyPrefer (profileOfScores u) A B)
      (hs : IsSuccessor (swapProfile (profileOfScores u)) B.symm w m) :
      IsSuccessor (swapProfile (profileOfScores v)) B.symm w m := by
    have hAu' := (isStable_profileOfScores_iff hu A).mp hAu
    have hAv' := (isStable_profileOfScores_iff hv A).mp hAv
    let eqPrefix := huv.reverseSearchPrefix_iff hBuv hu hv hAu' hAv' w
    have hb := (rankPermutation_le_iff_of_injective (hu (.inr w)) _ _).mp
      (hs.min_rank _ (reverseEligible_anchorHusband_of_changed hu hAu hBu hABu hw))
    obtain ⟨he, hm⟩ := (eqPrefix m).mp ⟨hs.eligible, hb⟩
    refine ⟨he, fun m' hm' ↦ ?_⟩
    apply (rankPermutation_le_iff_of_injective (hv (.inr w)) _ _).mpr
    by_cases hl : v (.inr w) m' ≤ v (.inr w) (A.symm w)
    · obtain ⟨he', hb'⟩ := (eqPrefix m').mpr ⟨hm', hl⟩
      have hscore := (rankPermutation_le_iff_of_injective (hu (.inr w)) _ _).mp
        (hs.min_rank m' he')
      rw [← (huv.pair_agrees_of_woman_le hu hAu' hb).2,
        ← (huv.pair_agrees_of_woman_le hu hAu' hb').2]
      exact hscore
    · exact hm.trans (le_of_not_ge hl)
  exact ⟨transport h hB hx hy hAx hAy hBx hAB,
    transport h.symm hB.symm hy hx hAy hAx hBy hABy⟩
theorem FullForwardRevealAgrees.reverseSuccessor_pair_agrees_of_changed
    (h : FullForwardRevealAgrees x y A)
    (hx : ∀ row, Function.Injective (x row))
    (hAx : IsStable (profileOfScores x) A) (hBx : IsStable (profileOfScores x) B)
    (hAB : MenWeaklyPrefer (profileOfScores x) A B)
    {w m : Fin n} (hw : B.symm w ≠ A.symm w)
    (hs : IsSuccessor (swapProfile (profileOfScores x)) B.symm w m) :
    ScorePairAgrees x y m w :=
  h.pair_agrees_of_woman_le hx ((isStable_profileOfScores_iff hx A).mp hAx) <|
    (rankPermutation_le_iff_of_injective (hx (.inr w)) _ _).mp
      (hs.min_rank _ (reverseEligible_anchorHusband_of_changed hx hAx hBx hAB hw))
theorem FullForwardRevealAgrees.reversePermutation_iff_of_changed (h : FullForwardRevealAgrees x y A)
    (hx : ∀ row, Function.Injective (x row)) (hy : ∀ row, Function.Injective (y row))
    (hAx : IsStable (profileOfScores x) A) (hAy : IsStable (profileOfScores y) A)
    (hBx : IsStable (profileOfScores x) B) (hAB : MenWeaklyPrefer (profileOfScores x) A B)
    (σ : Matching n) (hchanged : ∀ w ∈ σ.support, B.symm w ≠ A.symm w) :
    RealizesSuccessorPermutation (swapProfile (profileOfScores x)) B.symm σ ↔
      RealizesSuccessorPermutation (swapProfile (profileOfScores y)) B.symm σ := by
  constructor
  · intro hs w hw
    exact (h.reverseSuccessor_iff_of_changed hx hy hAx hAy hBx hAB
      (hchanged w hw) _).mp (hs w hw)
  · intro hs w hw
    exact (h.reverseSuccessor_iff_of_changed hx hy hAx hAy hBx hAB
      (hchanged w hw) _).mpr (hs w hw)
theorem FullForwardRevealAgrees.undo_femaleSpouse_agrees_of_changed
    (h : FullForwardRevealAgrees x y A) (hB : FullForwardRevealAgrees x y B)
    (hx : ∀ row, Function.Injective (x row))
    (hAx : IsStable (profileOfScores x) A) (hBx : IsStable (profileOfScores x) B)
    (hAB : MenWeaklyPrefer (profileOfScores x) A B) {σ : Matching n}
    (hσ : RealizesSuccessorPermutation (swapProfile (profileOfScores x)) B.symm σ)
    (hchanged : ∀ w ∈ σ.support, B.symm w ≠ A.symm w) (w : Fin n) :
    femaleSpouseScore x (undoReverseRotation B σ) w =
      femaleSpouseScore y (undoReverseRotation B σ) w := by
  simp only [femaleSpouseScore, undoReverseRotation_symm_apply]
  by_cases hw : w ∈ σ.support
  · exact (h.reverseSuccessor_pair_agrees_of_changed hx hAx hBx hAB
      (hchanged w hw) (hσ w hw)).2
  · rw [Equiv.Perm.notMem_support.mp hw]
    exact hB.womanSpouse w
private theorem FullForwardRevealAgrees.crossRectangle_of_changed
    (h : FullForwardRevealAgrees x y A) (hB : FullForwardRevealAgrees x y B)
    (hx : ∀ row, Function.Injective (x row))
    (hAx : IsStable (profileOfScores x) A) (hBx : IsStable (profileOfScores x) B)
    (hAB : MenWeaklyPrefer (profileOfScores x) A B) {ρ σ : Matching n}
    (hρ : IsExposedRotation (profileOfScores x) B ρ)
    (hσ : RealizesSuccessorPermutation (swapProfile (profileOfScores x)) B.symm σ)
    (hchanged : ∀ w ∈ σ.support, B.symm w ≠ A.symm w) {m w : Fin n}
    (hc : IsPivotCrossRectangle x B (undoReverseRotation B σ) ρ m w) :
    IsPivotCrossRectangle y B (undoReverseRotation B σ) ρ m w := by
  have hw : w ∈ σ.support := Equiv.Perm.mem_support.mpr fun he ↦
    hc.2.1 (by rw [undoReverseRotation_symm_apply, he])
  have hf : x (.inr w) ((undoReverseRotation B σ).symm w) ≤ x (.inr w) (A.symm w) := by
    rw [undoReverseRotation_symm_apply]
    exact (rankPermutation_le_iff_of_injective (hx (.inr w)) _ _).mp
      ((hσ w hw).min_rank _
        (reverseEligible_anchorHusband_of_changed hx hAx hBx hAB (hchanged w hw)))
  have hp := h.pair_agrees_of_woman_le hx ((isStable_profileOfScores_iff hx A).mp hAx)
    (hc.2.2.2.2.2.le.trans hf)
  have ht := hB.cell m (B (ρ m)) <|
    (isEligibleSuccessor_profileOfScores_iff hx B m _).mp (hρ.successor m hc.1).eligible
  have hN := h.undo_femaleSpouse_agrees_of_changed hB hx hAx hBx hAB hσ hchanged w
  simp only [femaleSpouseScore] at hN
  simpa only [IsPivotCrossRectangle, (hB.spouse m).1, hp.1, ht.1, hB.womanSpouse w,
    hp.2, hN] using hc
theorem FullForwardRevealAgrees.undo_compatible_iff_of_changed
    (h : FullForwardRevealAgrees x y A)
    (hx : ∀ row, Function.Injective (x row)) (hy : ∀ row, Function.Injective (y row))
    (hAx : IsStable (profileOfScores x) A) (hAy : IsStable (profileOfScores y) A)
    (hBx : IsStable (profileOfScores x) B) (hAB : MenWeaklyPrefer (profileOfScores x) A B)
    {ρ σ : Matching n} (hρ : IsExposedRotation (profileOfScores x) B ρ)
    (hσ : RealizesSuccessorPermutation (swapProfile (profileOfScores x)) B.symm σ)
    (hchanged : ∀ w ∈ σ.support, B.symm w ≠ A.symm w)
    (hdisj : ∀ m ∈ ρ.support, B m ∉ σ.support) :
    IsExposedRotation (profileOfScores x) (undoReverseRotation B σ) ρ ↔
      IsExposedRotation (profileOfScores y) (undoReverseRotation B σ) ρ := by
  obtain ⟨hBy, hABy, hB⟩ := h.later hx hy hAx hAy hBx hAB
  have hρy := (hB.exposedRotation_iff hx hy ρ).mp hρ
  have hσy := (h.reversePermutation_iff_of_changed hx hy hAx hAy hBx hAB σ hchanged).mp hσ
  have hfixed (m : Fin n) (hm : ρ m ≠ m) : undoReverseRotation B σ m = B m :=
    undoReverseRotation_apply_of_not_mem_support (hdisj m (Equiv.Perm.mem_support.mpr hm))
  rw [isExposedRotation_profileOfScores_iff_no_pivotCrossRectangle hx hρ
    ((isStable_profileOfScores_iff hx _).mp (hσ.undo_stable hBx)) hfixed,
    isExposedRotation_profileOfScores_iff_no_pivotCrossRectangle hy hρy
      ((isStable_profileOfScores_iff hy _).mp (hσy.undo_stable hBy)) hfixed]
  exact ⟨fun he m w hc ↦ he m w
      (h.symm.crossRectangle_of_changed hB.symm hy hAy hBy hABy hρy hσy hchanged hc),
    fun he m w hc ↦ he m w (h.crossRectangle_of_changed hB hx hAx hBx hAB hρ hσ hchanged hc)⟩
theorem FullForwardRevealAgrees.mem_filteredReverseSupportFamily_iff_of_changed
    (h : FullForwardRevealAgrees x y A)
    (hx : ∀ row, Function.Injective (x row)) (hy : ∀ row, Function.Injective (y row))
    (hAx : IsStable (profileOfScores x) A) (hAy : IsStable (profileOfScores y) A)
    (hBx : IsStable (profileOfScores x) B) (hAB : MenWeaklyPrefer (profileOfScores x) A B)
    {ρ σ : Matching n} (hρ : IsExposedRotation (profileOfScores x) B ρ)
    (hchanged : ∀ w ∈ σ.support, B.symm w ≠ A.symm w)
    (flag : OffDiagonalCellIndex n → Bool) (k L : ℕ) (t : ℝ) :
    σ ∈ filteredReverseSupportFamily B ρ flag k L t x ↔
      σ ∈ filteredReverseSupportFamily B ρ flag k L t y := by
  obtain ⟨hBy, hABy, hB⟩ := h.later hx hy hAx hAy hBx hAB
  have transport {u v : ScoreProfile n} (huv : FullForwardRevealAgrees u v A)
      (hBuv : FullForwardRevealAgrees u v B)
      (hu : ∀ row, Function.Injective (u row)) (hv : ∀ row, Function.Injective (v row))
      (hAu : IsStable (profileOfScores u) A) (hAv : IsStable (profileOfScores v) A)
      (hBu : IsStable (profileOfScores u) B) (hABu : MenWeaklyPrefer (profileOfScores u) A B)
      (hρu : IsExposedRotation (profileOfScores u) B ρ)
      (hmem : σ ∈ filteredReverseSupportFamily B ρ flag k L t u) :
      σ ∈ filteredReverseSupportFamily B ρ flag k L t v := by
    simp only [filteredReverseSupportFamily, Finset.mem_filter, compatibleReverseSupportFamily,
      mem_compatibleReversePermutations] at hmem ⊢
    rcases hmem with ⟨⟨hcand, hreal, hcompat⟩, hcap, hinc⟩
    have hdisj (m : Fin n) (hm : m ∈ ρ.support) : B m ∉ σ.support := fun hw ↦
      ((mem_goodReverseSupportPermutations.mp hcand).2 _ hw).1
        (Finset.mem_map.mpr ⟨m, hm, rfl⟩)
    refine ⟨⟨hcand, (huv.reversePermutation_iff_of_changed hu hv hAu hAv hBu hABu
      σ hchanged).mp hreal, (huv.undo_compatible_iff_of_changed hu hv hAu hAv hBu hABu
      hρu hreal hchanged hdisj).mp hcompat⟩, hcap, ?_⟩
    intro w hw
    have hp := huv.reverseSuccessor_pair_agrees_of_changed hu hAu hBu hABu
      (hchanged w hw) (hreal w hw)
    simpa only [reverseScoreIncrement, hp.2, hBuv.womanSpouse w] using hinc w hw
  exact ⟨transport h hB hx hy hAx hAy hBx hAB hρ,
    transport h.symm hB.symm hy hx hAy hAx hBy hABy
      ((hB.exposedRotation_iff hx hy ρ).mp hρ)⟩
theorem FullForwardRevealAgrees.diagonal_eq (h : FullForwardRevealAgrees x y A) :
    (splitScorePairs A x).1 = (splitScorePairs A y).1 := by
  funext q
  have he : q = ⟨(q.val.1, q.val.1), rfl⟩ :=
    Subtype.ext (Prod.ext rfl q.property.symm)
  rw [he]
  change diagonalPairAt (splitScorePairs A x).1 q.val.1 =
    diagonalPairAt (splitScorePairs A y).1 q.val.1
  rw [diagonalPairAt_splitScorePairs, diagonalPairAt_splitScorePairs]
  exact Prod.ext (h.spouse _).1 (h.spouse _).2
theorem forwardMaskOfScores_eq_true_iff (x : ScoreProfile n) (A : Matching n)
    (q : OffDiagonalCellIndex n) :
    forwardMaskOfScores (splitScorePairs A x).1 (splitScorePairs A x).2 q = true ↔
      ScoreForwardEligible x A q.val.1 (A q.val.2) := by
  rw [forwardMaskOfScores, forwardCellFlag_eq_true, splitScorePairs_offDiagonal_apply,
    diagonalPairAt_splitScorePairs, diagonalPairAt_splitScorePairs]
  simp only [forwardEligibleScoreCell, Set.mem_prod, Set.mem_Ioi, Set.mem_Iio,
    ScoreForwardEligible, Equiv.symm_apply_apply]
theorem FullForwardRevealAgrees.mask_eq (h : FullForwardRevealAgrees x y A) :
    forwardMaskOfScores (splitScorePairs A x).1 (splitScorePairs A x).2 =
      forwardMaskOfScores (splitScorePairs A y).1 (splitScorePairs A y).2 := by
  funext q
  apply Bool.eq_iff_iff.mpr
  exact (forwardMaskOfScores_eq_true_iff x A q).trans
    ((h.eligible_iff q.val.1 (A q.val.2)).trans (forwardMaskOfScores_eq_true_iff y A q).symm)
theorem FullForwardRevealAgrees.active_pair_eq (h : FullForwardRevealAgrees x y A)
    (flag : OffDiagonalCellIndex n → Bool)
    (hflag : forwardMaskOfScores (splitScorePairs A x).1 (splitScorePairs A x).2 = flag)
    (q : ForwardActiveCellIndex flag) :
    (splitScorePairs A x).2 q.val = (splitScorePairs A y).2 q.val := by
  have he : forwardMaskOfScores (splitScorePairs A x).1 (splitScorePairs A x).2 q.val = true := by
    rw [hflag]
    exact q.property
  have hp := h.cell _ _ ((forwardMaskOfScores_eq_true_iff x A q.val).mp he)
  rw [splitScorePairs_offDiagonal_apply, splitScorePairs_offDiagonal_apply]
  exact Prod.ext hp.1 hp.2
theorem FullForwardRevealAgrees.locallyEligible_iff (h : FullForwardRevealAgrees x y A)
    (b a c : ℝ) (ρ : Matching n) :
    IsLocallyEligiblePivot b a c x A ρ ↔ IsLocallyEligiblePivot b a c y A ρ := by
  let flag := forwardMaskOfScores (splitScorePairs A x).1 (splitScorePairs A x).2
  let Test (d : DiagonalScorePairs n) (v : ForwardRevealedMaleScores flag) : Prop :=
    LocalPivotGeometry b a c A ρ d flag ∧
      v ∈ eligiblePivotRevealSet d flag ρ (localPivotIncrementCap c d)
  have hm : (forwardRevealWithColumns flag (splitScorePairs A x).2).1 =
      (forwardRevealWithColumns flag (splitScorePairs A y).2).1 :=
    funext fun q ↦ congrArg Prod.fst (h.active_pair_eq flag rfl q)
  have hx : IsLocallyEligiblePivot b a c x A ρ ↔
      Test (splitScorePairs A x).1 (forwardRevealWithColumns flag (splitScorePairs A x).2).1 :=
    Iff.rfl
  have hy : IsLocallyEligiblePivot b a c y A ρ ↔
      Test (splitScorePairs A y).1 (forwardRevealWithColumns flag (splitScorePairs A y).2).1 := by
    unfold IsLocallyEligiblePivot
    dsimp only
    rw [← h.mask_eq]
  rw [hx, hy, hm, h.diagonal_eq]
theorem fullForwardRevealAgrees_iff_pivotFullReveal_eq
    {x y : ScoreProfile n} {A : Matching n} :
    FullForwardRevealAgrees x y A ↔ pivotFullReveal A x = pivotFullReveal A y := by
  constructor
  · intro h
    unfold pivotFullReveal pivotFullRevealFromScores pivotMaleRevealFromScores
    dsimp only
    refine Prod.ext (Prod.ext h.diagonal_eq (Prod.ext h.mask_eq ?_)) ?_
    · funext q
      rw [← h.mask_eq]
      dsimp only
      split
      · rename_i hq
        exact congrArg Prod.fst (h.active_pair_eq _ rfl ⟨q, hq⟩)
      · rfl
    · funext q
      rw [← h.mask_eq]
      dsimp only
      split
      · rename_i hq
        exact congrArg Prod.snd (h.active_pair_eq _ rfl ⟨q, hq⟩)
      · rfl
  · intro h
    have hd : (splitScorePairs A x).1 = (splitScorePairs A y).1 :=
      congrArg (fun z : PivotFullRevealData n ↦ z.1.1) h
    have hm : forwardMaskOfScores (splitScorePairs A x).1 (splitScorePairs A x).2 =
        forwardMaskOfScores (splitScorePairs A y).1 (splitScorePairs A y).2 :=
      congrArg (fun z : PivotFullRevealData n ↦ z.1.2.1) h
    have hp (q : OffDiagonalCellIndex n)
        (hq : forwardMaskOfScores (splitScorePairs A x).1 (splitScorePairs A x).2 q = true) :
        (splitScorePairs A x).2 q = (splitScorePairs A y).2 q := by
      have hqy : forwardMaskOfScores (splitScorePairs A y).1 (splitScorePairs A y).2 q = true := by
        rwa [← hm]
      apply Prod.ext
      · have he := congrArg (fun z : PivotFullRevealData n ↦ z.1.2.2 q) h
        simpa only [pivotFullReveal, pivotFullRevealFromScores, pivotMaleRevealFromScores,
          hq, hqy, ite_true] using he
      · have he := congrArg (fun z : PivotFullRevealData n ↦ z.2 q) h
        simpa only [pivotFullReveal, pivotFullRevealFromScores, hq, hqy, ite_true] using he
    have hindex (m w : Fin n) (hne : A m ≠ w) : m ≠ A.symm w := fun he ↦
      hne (((Equiv.symm_apply_eq A).mp he.symm).symm)
    refine ⟨fun m ↦ ?_, fun m w ↦ ?_, fun m w he ↦ ?_⟩
    · have he := congrArg (fun d ↦ diagonalPairAt d m) hd
      rw [diagonalPairAt_splitScorePairs, diagonalPairAt_splitScorePairs] at he
      exact ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩
    · by_cases he : A m = w
      · subst w
        simp only [ScoreForwardEligible, lt_self_iff_false, false_and]
      · let q : OffDiagonalCellIndex n := ⟨(m, A.symm w), hindex m w he⟩
        have hq : A q.val.2 = w := A.apply_symm_apply w
        have hx := forwardMaskOfScores_eq_true_iff x A q
        have hy := forwardMaskOfScores_eq_true_iff y A q
        rw [hq] at hx hy
        rw [← hx, ← hy, hm]
    · have hne : A m ≠ w := fun hmw ↦ he.1.ne (congrArg (x (.inl m)) hmw)
      let q : OffDiagonalCellIndex n := ⟨(m, A.symm w), hindex m w hne⟩
      have hq : A q.val.2 = w := A.apply_symm_apply w
      have hx := forwardMaskOfScores_eq_true_iff x A q
      rw [hq] at hx
      have hpair := hp q (hx.mpr he)
      rw [splitScorePairs_offDiagonal_apply, splitScorePairs_offDiagonal_apply, hq] at hpair
      exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩
private theorem ne_inverse_of_ne_partner {A : Matching n} {m w : Fin n} (h : A m ≠ w) :
    m ≠ A.symm w :=
  fun he ↦ h (((Equiv.symm_apply_eq A).mp he.symm).symm)
private def fullRevealCompletionPair (A : Matching n) (R : PivotFullRevealData n) (m w : Fin n) :
    ℝ × ℝ :=
  if h : A m = w then diagonalPairAt R.1.1 m
  else
    let q : OffDiagonalCellIndex n := ⟨(m, A.symm w), ne_inverse_of_ne_partner h⟩
    if R.1.2.1 q = true then (R.1.2.2 q, R.2 q) else (2 + (A.symm w).val, 2 + m.val)
private def pivotFullRevealCompletion (A : Matching n) (R : PivotFullRevealData n) : ScoreProfile n :=
  fun row i ↦ match row with
    | .inl m => (fullRevealCompletionPair A R m i).1
    | .inr w => (fullRevealCompletionPair A R i w).2
private theorem measurable_fullRevealCompletionPair (A : Matching n) (m w : Fin n) :
    Measurable (fun R : PivotFullRevealData n ↦ fullRevealCompletionPair A R m w) := by
  by_cases h : A m = w
  · simp only [fullRevealCompletionPair, dif_pos h]
    exact (measurable_pi_apply _).comp (measurable_fst.comp measurable_fst)
  · let q : OffDiagonalCellIndex n := ⟨(m, A.symm w), ne_inverse_of_ne_partner h⟩
    simp only [fullRevealCompletionPair, dif_neg h]
    have hflag : Measurable (fun R : PivotFullRevealData n ↦ R.1.2.1 q) :=
      (measurable_pi_apply q).comp (measurable_fst.comp (measurable_snd.comp measurable_fst))
    have hmale : Measurable (fun R : PivotFullRevealData n ↦ R.1.2.2 q) :=
      (measurable_pi_apply q).comp (measurable_snd.comp (measurable_snd.comp measurable_fst))
    have hfemale : Measurable (fun R : PivotFullRevealData n ↦ R.2 q) :=
      (measurable_pi_apply q).comp measurable_snd
    exact Measurable.ite (measurableSet_eq_fun hflag measurable_const)
      (hmale.prodMk hfemale) measurable_const
theorem measurable_pivotFullRevealCompletion (A : Matching n) :
    Measurable (pivotFullRevealCompletion A) := by
  refine measurable_pi_iff.2 fun r ↦ measurable_pi_iff.2 fun i ↦ ?_
  cases r with
  | inl m => exact (measurable_fullRevealCompletionPair A m i).fst
  | inr w => exact (measurable_fullRevealCompletionPair A i w).snd
theorem measurable_pivotFullRevealCompletion_from_reveal (A : Matching n) :
    Measurable[pivotFullRevealSpace A]
      (fun x ↦ pivotFullRevealCompletion A (pivotFullReveal A x)) :=
  (measurable_pivotFullRevealCompletion A).comp
    (comap_measurable (pivotFullReveal A))
private theorem fullRevealCompletionPair_of_observed (A : Matching n) (x : ScoreProfile n)
    (m w : Fin n) (h : A m = w ∨ ScoreForwardEligible x A m w) :
    fullRevealCompletionPair A (pivotFullReveal A x) m w =
      (x (.inl m) w, x (.inr w) m) := by
  by_cases hmw : A m = w
  · subst w
    rw [fullRevealCompletionPair, dif_pos rfl]
    exact diagonalPairAt_splitScorePairs A x m
  · let q : OffDiagonalCellIndex n := ⟨(m, A.symm w), ne_inverse_of_ne_partner hmw⟩
    have hq : A q.val.2 = w := A.apply_symm_apply w
    have hflag : forwardMaskOfScores (splitScorePairs A x).1 (splitScorePairs A x).2 q = true :=
      (forwardMaskOfScores_eq_true_iff x A q).mpr (hq.symm ▸ h.resolve_left hmw)
    have hp := splitScorePairs_offDiagonal_apply A x q
    rw [hq] at hp
    rw [fullRevealCompletionPair, dif_neg hmw]
    change (if forwardMaskOfScores (splitScorePairs A x).1 (splitScorePairs A x).2 q = true
      then ((pivotFullReveal A x).1.2.2 q, (pivotFullReveal A x).2 q) else _) = _
    simp only [pivotFullReveal, pivotFullRevealFromScores, pivotMaleRevealFromScores,
      hflag, ite_true]
    exact hp
private theorem fullRevealCompletionPair_of_inactive (A : Matching n) (x : ScoreProfile n)
    (m w : Fin n) (h : ¬ (A m = w ∨ ScoreForwardEligible x A m w)) :
    fullRevealCompletionPair A (pivotFullReveal A x) m w =
      ((2 : ℝ) + (A.symm w).val, (2 : ℝ) + m.val) := by
  have hmw : A m ≠ w := fun he ↦ h (Or.inl he)
  let q : OffDiagonalCellIndex n := ⟨(m, A.symm w), ne_inverse_of_ne_partner hmw⟩
  have hq : A q.val.2 = w := A.apply_symm_apply w
  have hflag : forwardMaskOfScores (splitScorePairs A x).1 (splitScorePairs A x).2 q ≠ true :=
    fun he ↦ h (Or.inr (hq ▸ (forwardMaskOfScores_eq_true_iff x A q).mp he))
  rw [fullRevealCompletionPair, dif_neg hmw]
  change (if forwardMaskOfScores (splitScorePairs A x).1 (splitScorePairs A x).2 q = true
    then ((pivotFullReveal A x).1.2.2 q, (pivotFullReveal A x).2 q) else _) = _
  rw [if_neg hflag]
private theorem injective_row_of_filling {u v : Fin n → ℝ} {P : Fin n → Prop}
    (f : Fin n → Fin n) (hf : Function.Injective f) (hu : Function.Injective u)
    (hsmall : ∀ i, u i < 1) (hseen : ∀ i, P i → v i = u i)
    (hfill : ∀ i, ¬ P i → v i = 2 + (f i).val) : Function.Injective v := by
  intro i j he
  by_cases hi : P i <;> by_cases hj : P j
  · exact hu ((hseen i hi).symm.trans (he.trans (hseen j hj)))
  · have hlt := hsmall i
    rw [hseen i hi, hfill j hj] at he
    have hnon : 0 ≤ ((f j).val : ℝ) := Nat.cast_nonneg _
    linarith
  · have hlt := hsmall j
    rw [hfill i hi, hseen j hj] at he
    have hnon : 0 ≤ ((f i).val : ℝ) := Nat.cast_nonneg _
    linarith
  · rw [hfill i hi, hfill j hj] at he
    exact hf (Fin.ext (by exact_mod_cast (add_left_cancel he)))
theorem pivotFullRevealCompletion_spec {x : ScoreProfile n} {A : Matching n}
    (hx : ∀ row, Function.Injective (x row)) (hu : ∀ r i, x r i < 1) :
    let y := pivotFullRevealCompletion A (pivotFullReveal A x)
    (∀ row, Function.Injective (y row)) ∧ IsStable (profileOfScores y) A ∧
      FullForwardRevealAgrees x y A := by
  dsimp only
  let R := pivotFullReveal A x
  let y := pivotFullRevealCompletion A R
  let P (m w : Fin n) := A m = w ∨ ScoreForwardEligible x A m w
  have hseen (m w : Fin n) (h : P m w) : ScorePairAgrees x y m w := by
    have h' := fullRevealCompletionPair_of_observed A x m w h
    exact ⟨(congrArg Prod.fst h').symm, (congrArg Prod.snd h').symm⟩
  have hfill (m w : Fin n) (h : ¬ P m w) :
      y (.inl m) w = 2 + (A.symm w).val ∧ y (.inr w) m = 2 + m.val := by
    have h' := fullRevealCompletionPair_of_inactive A x m w h
    exact ⟨congrArg Prod.fst h', congrArg Prod.snd h'⟩
  have hsp (m : Fin n) := hseen m (A m) (Or.inl rfl)
  have hwsp (w : Fin n) : x (.inr w) (A.symm w) = y (.inr w) (A.symm w) := by
    simpa only [A.apply_symm_apply] using (hsp (A.symm w)).2
  have hytie (r : Fin n ⊕ Fin n) : Function.Injective (y r) := by
    cases r with
    | inl m =>
      exact injective_row_of_filling (P := P m) A.symm A.symm.injective (hx (.inl m))
        (hu (.inl m)) (fun w hw ↦ (hseen m w hw).1.symm) (fun w hw ↦ (hfill m w hw).1)
    | inr w =>
      exact injective_row_of_filling (P := fun m ↦ P m w) id Function.injective_id (hx (.inr w))
        (hu (.inr w)) (fun m hm ↦ (hseen m w hm).2.symm) (fun m hm ↦ (hfill m w hm).2)
  have hinactive (m w : Fin n) (hn : ¬ P m w) :
      ¬ y (.inr w) m < y (.inr w) (A.symm w) := by
    rw [(hfill m w hn).2, ← hwsp w]
    have hnon : 0 ≤ (m.val : ℝ) := Nat.cast_nonneg _
    linarith [hu (.inr w) (A.symm w)]
  have helig (m w : Fin n) (he : ScoreForwardEligible x A m w) :
      ScoreForwardEligible y A m w := by
    have hp := hseen m w (Or.inr he)
    constructor
    · rw [← (hsp m).1, ← hp.1]
      exact he.1
    · rw [← hwsp w, ← hp.2]
      exact he.2
  refine ⟨hytie, (isStable_profileOfScores_iff hytie A).mpr ?_,
    ⟨hsp, ?_, fun m w he ↦ hseen m w (Or.inr he)⟩⟩
  · intro m w hb
    by_cases he : ScoreForwardEligible x A m w
    · exact (helig m w he).1.not_gt hb.2.1
    · exact hinactive m w (fun h ↦ h.elim hb.1 he) hb.2.2
  · intro m w
    refine ⟨helig m w, fun he ↦ ?_⟩
    have hne : A m ≠ w := fun hh ↦ he.1.ne (congrArg (y (.inl m)) hh)
    by_contra hn
    exact hinactive m w (fun h ↦ h.elim hne hn) he.2
end MarkedLP
end

-- PivotMovedCenteredTest
section
open Filter MeasureTheory Set StableMarriage
namespace MarkedLP
variable {n : ℕ}
private def IsStrictLaterStable (x : ScoreProfile n) (μ ν : Matching n) : Prop :=
  IsScoreStable x ν ∧ μ ≠ ν ∧ MenWeaklyPrefer (profileOfScores x) μ ν
theorem measurableSet_isStrictLaterStable (μ ν : Matching n) :
    MeasurableSet {x : ScoreProfile n | IsStrictLaterStable x μ ν} :=
  (measurableSet_isScoreStable ν).inter ((MeasurableSet.const _).inter
    (measurable_profileOfScores n (MeasurableSet.of_discrete :
      MeasurableSet {p : Profile n | MenWeaklyPrefer p μ ν})))
private noncomputable def markedMovedChoices (μ ν σ : Matching n)
    (flag : OffDiagonalCellIndex n → Bool) (K L : ℕ) (t : ℝ) (x : ScoreProfile n) :
    Finset (Matching n) := by
  classical
  exact (markedFilteredChoices ν σ flag K L t x).filter
    (fun τ ↦ ∀ w ∈ τ.support, ν.symm w ≠ μ.symm w)
theorem mem_markedMovedChoices {μ ν σ τ : Matching n} {flag : OffDiagonalCellIndex n → Bool}
    {K L : ℕ} {t : ℝ} {x : ScoreProfile n} :
    τ ∈ markedMovedChoices μ ν σ flag K L t x ↔
      τ ∈ markedFilteredChoices ν σ flag K L t x ∧
        ∀ w ∈ τ.support, ν.symm w ≠ μ.symm w := by
  classical
  simp only [markedMovedChoices, Finset.mem_filter]
private noncomputable def localMovedDecorationCount (b A B : ℝ) (K L : ℕ)
    (μ ν σ : Matching n) (x : ScoreProfile n) : ℝ := by
  classical
  exact if IsLocallyEligiblePivot b A B x ν σ then
    ((markedMovedChoices μ ν σ (forwardMaskOfScores (splitScorePairs ν x).1
      (splitScorePairs ν x).2) K L (reverseIncrementCutoff n (maleSpouseTotal x ν)) x).card : ℝ)
    else 0
theorem localMovedDecorationCount_nonneg (b A B : ℝ) (K L : ℕ) (μ ν σ : Matching n)
    (x : ScoreProfile n) : 0 ≤ localMovedDecorationCount b A B K L μ ν σ x := by
  classical
  unfold localMovedDecorationCount
  split <;> positivity
theorem localMovedDecorationCount_le (b A B : ℝ) (K L : ℕ) (μ ν σ : Matching n)
    (x : ScoreProfile n) :
    localMovedDecorationCount b A B K L μ ν σ x ≤ localFilteredDecorationCount b A B K L ν σ x := by
  classical
  by_cases h : IsLocallyEligiblePivot b A B x ν σ
  · simp only [localMovedDecorationCount, localFilteredDecorationCount, if_pos h, Nat.cast_le]
    exact Finset.card_le_card (Finset.filter_subset _ _)
  · simp only [localMovedDecorationCount, localFilteredDecorationCount, if_neg h, le_refl]
private theorem measurable_moved_mask_switch {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [Countable β]
    [MeasurableSingletonClass β] {M : α → β} (hM : Measurable M)
    {f : β → α → γ} (hf : ∀ j, Measurable (f j)) :
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
theorem measurable_localMovedDecorationCount (b A B : ℝ) (K L : ℕ) (μ ν σ : Matching n) :
    Measurable (localMovedDecorationCount b A B K L μ ν σ) := by
  classical
  let M (x : ScoreProfile n) :=
    forwardMaskOfScores (splitScorePairs ν x).1 (splitScorePairs ν x).2
  let t (x : ScoreProfile n) := reverseIncrementCutoff n (maleSpouseTotal x ν)
  let f (flag : OffDiagonalCellIndex n → Bool) (x : ScoreProfile n) :=
    ((markedMovedChoices μ ν σ flag K L (t x) x).card : ℝ)
  have hM : Measurable M := (measurable_jointForwardMaskOfScores n).comp
    (splitScorePairs ν).measurable
  have ht : Measurable t := measurable_const.div (measurable_maleSpouseTotal ν)
  have hf (flag : OffDiagonalCellIndex n → Bool) : Measurable (f flag) := by
    have hmem (τ : Matching n) :
        MeasurableSet {x : ScoreProfile n | τ ∈ markedMovedChoices μ ν σ flag K L (t x) x} := by
      simp only [mem_markedMovedChoices, ofPred_and]
      exact (measurableSet_mem_markedFilteredChoices ν σ τ flag K L ht).inter
        (MeasurableSet.const _)
    simpa only [Function.comp_def, ENNReal.toReal_natCast] using
      ENNReal.measurable_toReal.comp (measurable_finsetCard_of_mem _ hmem)
  exact (measurable_moved_mask_switch hM hf).ite
    (measurableSet_isLocallyEligiblePivot b A B ν σ) measurable_const
theorem FullForwardRevealAgrees.isStrictLaterStable_iff
    {x y : ScoreProfile n} {μ ν : Matching n} (h : FullForwardRevealAgrees x y μ)
    (hx : ∀ row, Function.Injective (x row)) (hy : ∀ row, Function.Injective (y row))
    (hμx : IsStable (profileOfScores x) μ) (hμy : IsStable (profileOfScores y) μ) :
    IsStrictLaterStable x μ ν ↔ IsStrictLaterStable y μ ν := by
  have transport {u v : ScoreProfile n} (huv : FullForwardRevealAgrees u v μ)
      (hu : ∀ row, Function.Injective (u row)) (hv : ∀ row, Function.Injective (v row))
      (hμu : IsStable (profileOfScores u) μ) (hμv : IsStable (profileOfScores v) μ)
      (hs : IsStrictLaterStable u μ ν) : IsStrictLaterStable v μ ν := by
    obtain ⟨hνv, hμνv, _⟩ := huv.later hu hv hμu hμv
      ((isStable_profileOfScores_iff hu ν).mpr hs.1) hs.2.2
    exact ⟨(isStable_profileOfScores_iff hv ν).mp hνv, hs.2.1, hμνv⟩
  exact ⟨transport h hx hy hμx hμy, transport h.symm hy hx hμy hμx⟩
theorem FullForwardRevealAgrees.localMovedDecorationCount_eq_of_later
    {x y : ScoreProfile n} {μ ν : Matching n} (h : FullForwardRevealAgrees x y μ)
    (hx : ∀ row, Function.Injective (x row)) (hy : ∀ row, Function.Injective (y row))
    (hμx : IsStable (profileOfScores x) μ) (hμy : IsStable (profileOfScores y) μ)
    (hνx : IsStable (profileOfScores x) ν) (hμν : MenWeaklyPrefer (profileOfScores x) μ ν)
    (b A B : ℝ) (K L : ℕ) (σ : Matching n) :
    localMovedDecorationCount b A B K L μ ν σ x = localMovedDecorationCount b A B K L μ ν σ y := by
  classical
  obtain ⟨_, _, hνReveal⟩ := h.later hx hy hμx hμy hνx hμν
  have hE := hνReveal.locallyEligible_iff b A B σ
  by_cases hEx : IsLocallyEligiblePivot b A B x ν σ
  · have hEy := hE.mp hEx
    have hσ := (hEx.isSoleForwardExposed hx).1
    have htot : maleSpouseTotal x ν = maleSpouseTotal y ν := by
      rw [← reverseDiagonalMaleTotal_splitScorePairs ν x, ← reverseDiagonalMaleTotal_splitScorePairs ν y,
        hνReveal.diagonal_eq]
    simp only [localMovedDecorationCount, if_pos hEx, if_pos hEy,
      ← hνReveal.mask_eq, ← htot]
    congr 2
    ext τ
    simp only [mem_markedMovedChoices, mem_markedFilteredChoices]
    by_cases hw : ∀ w ∈ τ.support, ν.symm w ≠ μ.symm w
    · rw [h.mem_filteredReverseSupportFamily_iff_of_changed hx hy hμx hμy hνx hμν
        hσ hw _ _ _ _]
    · simp only [hw, and_false]
  · simp only [localMovedDecorationCount, if_neg hEx, if_neg (mt hE.mpr hEx)]
private noncomputable def actualLaterMovedCenteredTest (b A B : ℝ) (K L : ℕ)
    (μ ν σ : Matching n) (x : ScoreProfile n) : ℝ := by
  classical
  exact if IsStrictLaterStable x μ ν then
    localMovedDecorationCount b A B K L μ ν σ x - localPivotInactiveMean b A B K L ν σ x else 0
private noncomputable def laterMovedCenteredTest (b A B : ℝ) (K L : ℕ)
    (μ ν σ : Matching n) (x : ScoreProfile n) : ℝ :=
  actualLaterMovedCenteredTest b A B K L μ ν σ
    (pivotFullRevealCompletion μ (pivotFullReveal μ x))
theorem measurable_laterMovedCenteredTest (b A B : ℝ) (K L : ℕ) (μ ν σ : Matching n) :
    Measurable[pivotFullRevealSpace μ] (laterMovedCenteredTest b A B K L μ ν σ) := by
  have hbase : Measurable (actualLaterMovedCenteredTest b A B K L μ ν σ) :=
    ((measurable_localMovedDecorationCount b A B K L μ ν σ).sub
      ((measurable_maleReveal_localPivotInactiveMean b A B K L ν σ).mono
        (pivotMaleRevealSpace_le ν) le_rfl)).ite (measurableSet_isStrictLaterStable μ ν)
          measurable_const
  exact hbase.comp (measurable_pivotFullRevealCompletion_from_reveal μ)
open scoped Classical in
theorem laterMovedCenteredTest_ae_eq (b A B : ℝ) (K L : ℕ) (μ ν σ : Matching n) :
    laterMovedCenteredTest b A B K L μ ν σ =ᵐ[stableMarkScoreLaw μ]
      fun x ↦ if IsStrictLaterStable x μ ν then
        localMovedDecorationCount b A B K L μ ν σ x -
          localPivotConditionalMean b A B K L ν σ x else 0 := by
  have hmean : ∀ᵐ x ∂stableMarkScoreLaw μ, IsScoreStable x ν →
      localPivotInactiveMean b A B K L ν σ x = localPivotConditionalMean b A B K L ν σ x := by
    apply ae_restrict_of_ae
    exact (ae_restrict_iff' (measurableSet_isScoreStable ν)).mp
      (localPivotInactiveMean_ae_eq_conditionalMean b A B K L ν σ)
  filter_upwards [ae_restrict_mem (measurableSet_isScoreStable μ),
    ae_restrict_of_ae (ae_injective_rows n), ae_restrict_of_ae (ae_unitOpen_scores n),
    hmean] with x hμs hx hu hmean
  let y := pivotFullRevealCompletion μ (pivotFullReveal μ x)
  obtain ⟨hy, hμy, h⟩ := pivotFullRevealCompletion_spec (A := μ) hx (fun r i ↦ (hu r i).2)
  have hμx := (isStable_profileOfScores_iff hx μ).mpr hμs
  have hs : IsStrictLaterStable x μ ν ↔ IsStrictLaterStable y μ ν :=
    h.isStrictLaterStable_iff hx hy hμx hμy
  change (if IsStrictLaterStable y μ ν then
    localMovedDecorationCount b A B K L μ ν σ y - localPivotInactiveMean b A B K L ν σ y
    else 0) = _
  by_cases hsx : IsStrictLaterStable x μ ν
  · have hsy := hs.mp hsx
    have hνx := (isStable_profileOfScores_iff hx ν).mpr hsx.1
    have hmov := h.localMovedDecorationCount_eq_of_later hx hy hμx hμy hνx hsx.2.2 b A B K L σ
    obtain ⟨_, _, hνReveal⟩ := h.later hx hy hμx hμy hνx hsx.2.2
    have hreveal : pivotMaleReveal ν x = pivotMaleReveal ν y := by
      have hfull := fullForwardRevealAgrees_iff_pivotFullReveal_eq.mp hνReveal
      simpa only [pivotFullReveal_fst] using congrArg Prod.fst hfull
    have hmeanXY : localPivotInactiveMean b A B K L ν σ x =
        localPivotInactiveMean b A B K L ν σ y := by
      unfold localPivotInactiveMean
      rw [hreveal]
    rw [if_pos hsy, if_pos hsx, ← hmov, ← hmeanXY, hmean hsx.1]
  · rw [if_neg (mt hs.mpr hsx), if_neg hsx]
theorem laterMovedCenteredTest_abs_le_factorial_ae (b A B : ℝ) (K L : ℕ)
    (μ ν σ : Matching n) :
    ∀ᵐ x ∂stableMarkScoreLaw μ, |laterMovedCenteredTest b A B K L μ ν σ x| ≤ (n.factorial : ℝ) := by
  classical
  have hmean : ∀ᵐ x ∂stableMarkScoreLaw μ, IsScoreStable x ν →
      localPivotConditionalMean b A B K L ν σ x ∈ Icc (0 : ℝ) (n.factorial : ℝ) := by
    apply ae_restrict_of_ae
    exact (ae_restrict_iff' (measurableSet_isScoreStable ν)).mp
      (localPivotConditionalMean_mem_Icc_ae b A B K L ν σ)
  filter_upwards [laterMovedCenteredTest_ae_eq b A B K L μ ν σ, hmean] with x he hmean
  rw [he]
  by_cases hs : IsStrictLaterStable x μ ν
  · rw [if_pos hs, abs_le]
    have hh := hmean hs.1
    have hm0 := localMovedDecorationCount_nonneg b A B K L μ ν σ x
    have hmle := (localMovedDecorationCount_le b A B K L μ ν σ x).trans
      (localFilteredDecorationCount_le_factorial b A B K L ν σ x)
    constructor <;> linarith [hh.1, hh.2]
  · rw [if_neg hs, abs_zero]
    positivity
end MarkedLP
end

-- PivotComparableCentered
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace MarkedLP
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
private noncomputable def localMean (q : PivotCountParameters) (i : PivotMark n) :
    ScoreProfile n → ℝ :=
  localPivotConditionalMean q.lowerLength q.upperLength q.geometryBudget
    q.supportCap q.shortCutoff i.1 i.2
private noncomputable def localCentered (q : PivotCountParameters) (i : PivotMark n) :
    ScoreProfile n → ℝ :=
  q.localCount i - q.localMean i
private noncomputable def onStableMark (i : PivotMark n) (f : ScoreProfile n → ℝ) :
    ScoreProfile n → ℝ :=
  {x | IsScoreStable x i.1}.indicator f
private noncomputable def count (q : PivotCountParameters) (i : PivotMark n) :
    ScoreProfile n → ℝ :=
  onStableMark i (q.localCount i)
private noncomputable def mean (q : PivotCountParameters) (i : PivotMark n) :
    ScoreProfile n → ℝ :=
  onStableMark i (q.localMean i)
private noncomputable def centered (q : PivotCountParameters) (i : PivotMark n) :
    ScoreProfile n → ℝ :=
  onStableMark i (q.localCentered i)
theorem measurable_localCount (q : PivotCountParameters) (i : PivotMark n) :
    Measurable (q.localCount i) :=
  measurable_localFilteredDecorationCount _ _ _ _ _ _ _
theorem stronglyMeasurable_maleReveal_localMean (q : PivotCountParameters) (i : PivotMark n) :
    StronglyMeasurable[pivotMaleRevealSpace i.1] (q.localMean i) :=
  stronglyMeasurable_condExp
theorem measurable_localMean (q : PivotCountParameters) (i : PivotMark n) :
    Measurable (q.localMean i) :=
  ((q.stronglyMeasurable_maleReveal_localMean i).mono (pivotMaleRevealSpace_le i.1)).measurable
theorem measurable_localCentered (q : PivotCountParameters) (i : PivotMark n) :
    Measurable (q.localCentered i) := (q.measurable_localCount i).sub (q.measurable_localMean i)
theorem measurable_onStableMark (i : PivotMark n) {f : ScoreProfile n → ℝ} (hf : Measurable f) :
    Measurable (onStableMark i f) := hf.indicator (measurableSet_isScoreStable i.1)
theorem measurable_count (q : PivotCountParameters) (i : PivotMark n) : Measurable (q.count i) :=
  measurable_onStableMark i (q.measurable_localCount i)
theorem measurable_mean (q : PivotCountParameters) (i : PivotMark n) : Measurable (q.mean i) :=
  measurable_onStableMark i (q.measurable_localMean i)
theorem measurable_centered (q : PivotCountParameters) (i : PivotMark n) :
    Measurable (q.centered i) := measurable_onStableMark i (q.measurable_localCentered i)
theorem localCount_mem_Icc (q : PivotCountParameters) (i : PivotMark n) (x : ScoreProfile n) :
    q.localCount i x ∈ Icc (0 : ℝ) (n.factorial : ℝ) :=
  ⟨localFilteredDecorationCount_nonneg _ _ _ _ _ _ _ _,
    localFilteredDecorationCount_le_factorial _ _ _ _ _ _ _ _⟩
theorem localMean_mem_Icc_ae (q : PivotCountParameters) (i : PivotMark n) :
    ∀ᵐ x ∂stableMarkScoreLaw i.1, q.localMean i x ∈ Icc (0 : ℝ) (n.factorial : ℝ) :=
  localPivotConditionalMean_mem_Icc_ae _ _ _ _ _ _ _
theorem localMean_zero_on_ineligible_ae (q : PivotCountParameters) (i : PivotMark n) :
    ∀ᵐ x ∂stableMarkScoreLaw i.1,
      ¬ IsLocallyEligiblePivot q.lowerLength q.upperLength q.geometryBudget x i.1 i.2 →
        q.localMean i x = 0 := by
  let E : Set (ScoreProfile n) :=
    {x | IsLocallyEligiblePivot q.lowerLength q.upperLength q.geometryBudget x i.1 i.2}
  have hE : MeasurableSet[pivotMaleRevealSpace i.1] E :=
    measurableSet_isLocallyEligiblePivot_maleRevealSpace _ _ _ _ _
  have hE' : MeasurableSet E := pivotMaleRevealSpace_le i.1 _ hE
  have hz : q.localCount i =ᵐ[(stableMarkScoreLaw i.1).restrict Eᶜ] 0 := by
    filter_upwards [ae_restrict_mem hE'.compl] with x hx
    exact localFilteredDecorationCount_of_not_eligible _ _ hx
  exact (ae_restrict_iff' hE'.compl).mp (condExp_ae_eq_restrict_zero hE.compl hz)
theorem ae_scoreLaw_on_stableMark (i : PivotMark n) {P : ScoreProfile n → Prop}
    (h : ∀ᵐ x ∂stableMarkScoreLaw i.1, P x) :
    ∀ᵐ x ∂continuousScoreLaw n, IsScoreStable x i.1 → P x :=
  (ae_restrict_iff' (measurableSet_isScoreStable i.1)).mp h
theorem count_mem_Icc (q : PivotCountParameters) (i : PivotMark n) (x : ScoreProfile n) :
    q.count i x ∈ Icc (0 : ℝ) (n.factorial : ℝ) := by
  by_cases h : x ∈ {y | IsScoreStable y i.1}
  · simpa only [count, onStableMark, indicator_of_mem h] using q.localCount_mem_Icc i x
  · simp [count, onStableMark, h]
theorem mean_mem_Icc_ae (q : PivotCountParameters) (i : PivotMark n) :
    ∀ᵐ x ∂continuousScoreLaw n, q.mean i x ∈ Icc (0 : ℝ) (n.factorial : ℝ) := by
  filter_upwards [ae_scoreLaw_on_stableMark i (q.localMean_mem_Icc_ae i)] with x hx
  by_cases h : x ∈ {y | IsScoreStable y i.1}
  · simpa only [mean, onStableMark, indicator_of_mem h] using hx h
  · simp [mean, onStableMark, h]
theorem centered_eq_sub (q : PivotCountParameters) (i : PivotMark n) (x : ScoreProfile n) :
    q.centered i x = q.count i x - q.mean i x := by
  by_cases h : x ∈ {y | IsScoreStable y i.1}
  · simp only [centered, count, mean, onStableMark, indicator_of_mem h, localCentered, Pi.sub_apply]
  · simp only [centered, count, mean, onStableMark, indicator_of_notMem h, sub_zero]
theorem abs_centered_le_ae (q : PivotCountParameters) (i : PivotMark n) :
    ∀ᵐ x ∂continuousScoreLaw n, |q.centered i x| ≤ (n.factorial : ℝ) := by
  filter_upwards [q.mean_mem_Icc_ae i] with x hx
  have hz := q.count_mem_Icc i x
  rw [q.centered_eq_sub]
  exact abs_le.mpr ⟨by linarith [hz.1, hx.2], by linarith [hz.2, hx.1]⟩
theorem integral_onStableMark (i : PivotMark n) (f : ScoreProfile n → ℝ) :
    (∫ x, onStableMark i f x ∂continuousScoreLaw n) = ∫ x, f x ∂stableMarkScoreLaw i.1 :=
  integral_indicator (measurableSet_isScoreStable i.1)
theorem integral_sq_centered_le_localCount_sq (q : PivotCountParameters) (i : PivotMark n) :
    (∫ x, (q.centered i x) ^ 2 ∂continuousScoreLaw n) ≤
      ∫ x, (q.localCount i x) ^ 2 ∂stableMarkScoreLaw i.1 := by
  have he : (fun x ↦ (q.centered i x) ^ 2) =
      onStableMark i (fun x ↦ (q.localCentered i x) ^ 2) := by
    funext x
    by_cases hx : x ∈ {y | IsScoreStable y i.1}
    · simp only [centered, onStableMark, indicator_of_mem hx]
    · simp [centered, onStableMark, hx]
  rw [he, integral_onStableMark]
  let ν := stableMarkScoreLaw i.1
  let Z := q.localCount i
  let M := q.localMean i
  let C := (n.factorial : ℝ)
  have hZ (x : ScoreProfile n) : |Z x| ≤ C := by
    rw [abs_of_nonneg (q.localCount_mem_Icc i x).1]
    exact (q.localCount_mem_Icc i x).2
  have hM : ∀ᵐ x ∂ν, |M x| ≤ C := (q.localMean_mem_Icc_ae i).mono fun x hx ↦
    (abs_of_nonneg hx.1).symm ▸ hx.2
  have hi {f g : ScoreProfile n → ℝ} (hf : Measurable f) (hg : Measurable g)
      (hf' : ∀ᵐ x ∂ν, |f x| ≤ C) (hg' : ∀ᵐ x ∂ν, |g x| ≤ C) :
      Integrable (f * g) ν :=
    integrable_mul_of_ae_abs_le_real hf hg (by positivity) hf' hg'
  have hZZ := hi (q.measurable_localCount i) (q.measurable_localCount i)
    (Eventually.of_forall hZ) (Eventually.of_forall hZ)
  have hZM := hi (q.measurable_localCount i) (q.measurable_localMean i) (Eventually.of_forall hZ) hM
  have hMM := hi (q.measurable_localMean i) (q.measurable_localMean i) hM hM
  have hzero := integral_localPivotCentered_mul_eq_zero q.lowerLength q.upperLength
    q.geometryBudget q.supportCap q.shortCutoff i.1 i.2 M
    (((q.stronglyMeasurable_maleReveal_localMean i).mono
      (pivotMaleRevealSpace_le_full i.1)).aestronglyMeasurable) hZM hMM
  change (∫ x, (Z x - M x) * M x ∂ν) = 0 at hzero
  have hZM_eq : (∫ x, (Z * M) x ∂ν) = ∫ x, (M * M) x ∂ν := by
    apply sub_eq_zero.mp
    calc
      _ = ∫ x, (Z * M) x - (M * M) x ∂ν := (integral_sub hZM hMM).symm
      _ = _ := by simpa only [sub_mul, Pi.mul_apply] using hzero
  change (∫ x, (Z x - M x) ^ 2 ∂ν) ≤ _
  have hre : (fun x ↦ (Z x - M x) ^ 2) = fun x ↦
      ((Z * Z) x - 2 * (Z * M) x) + (M * M) x := by
    funext x
    simp only [Pi.mul_apply]
    ring
  have hsplit : (∫ x, ((Z * Z) x - 2 * (Z * M) x) + (M * M) x ∂ν) =
      (∫ x, (Z * Z) x ∂ν) - (∫ x, 2 * (Z * M) x ∂ν) + ∫ x, (M * M) x ∂ν := by
    calc
      _ = (∫ x, (Z * Z) x - 2 * (Z * M) x ∂ν) + ∫ x, (M * M) x ∂ν :=
        integral_add (hZZ.sub (hZM.const_mul 2)) hMM
      _ = _ := congrArg (· + ∫ x, (M * M) x ∂ν) (integral_sub hZZ (hZM.const_mul 2))
  rw [hre, hsplit, integral_const_mul, hZM_eq]
  have hnn : 0 ≤ ∫ x, (M * M) x ∂ν := integral_nonneg fun x ↦ mul_self_nonneg (M x)
  simp_rw [pow_two]
  change (∫ x, (Z * Z) x ∂ν) - 2 * (∫ x, (M * M) x ∂ν) + (∫ x, (M * M) x ∂ν) ≤
    ∫ x, (Z * Z) x ∂ν
  linarith
private noncomputable def localLaterCentered (q : PivotCountParameters) (i j : PivotMark n)
    (x : ScoreProfile n) : ℝ := by
  classical
  exact if IsStrictLaterStable x i.1 j.1 then q.localCentered j x else 0
private noncomputable def localLaterResidual (q : PivotCountParameters) (i j : PivotMark n)
    (x : ScoreProfile n) : ℝ := by
  classical
  exact if IsStrictLaterStable x i.1 j.1 then q.localCount j x -
    localMovedDecorationCount q.lowerLength q.upperLength q.geometryBudget q.supportCap
      q.shortCutoff i.1 j.1 j.2 x else 0
theorem localLaterResidual_mem_Icc (q : PivotCountParameters) (i j : PivotMark n)
    (x : ScoreProfile n) : q.localLaterResidual i j x ∈ Icc (0 : ℝ) (n.factorial : ℝ) := by
  classical
  unfold localLaterResidual
  split
  · exact ⟨sub_nonneg.mpr (localMovedDecorationCount_le _ _ _ _ _ _ _ _ _),
      (sub_le_self _ (localMovedDecorationCount_nonneg _ _ _ _ _ _ _ _ _)).trans
        (q.localCount_mem_Icc j x).2⟩
  · simp
theorem measurable_localLaterResidual (q : PivotCountParameters) (i j : PivotMark n) :
    Measurable (q.localLaterResidual i j) :=
  ((q.measurable_localCount j).sub (measurable_localMovedDecorationCount _ _ _ _ _ _ _ _)).ite
    (measurableSet_isStrictLaterStable i.1 j.1) measurable_const
private theorem abs_localCentered_le_ae (q : PivotCountParameters) (i : PivotMark n) :
    ∀ᵐ x ∂stableMarkScoreLaw i.1, |q.localCentered i x| ≤ (n.factorial : ℝ) := by
  filter_upwards [q.localMean_mem_Icc_ae i] with x hx
  have hz := q.localCount_mem_Icc i x
  change |q.localCount i x - q.localMean i x| ≤ _
  exact abs_le.mpr ⟨by linarith [hz.1, hx.2], by linarith [hz.2, hx.1]⟩
private noncomputable def comparableCenteredTerm (q : PivotCountParameters) (i j : PivotMark n)
    (x : ScoreProfile n) : ℝ := by
  classical
  exact if IsStrictLaterStable x i.1 j.1 then q.centered i x * q.centered j x else 0
private noncomputable def comparableResidualTerm (q : PivotCountParameters) (i j : PivotMark n)
    (x : ScoreProfile n) : ℝ :=
  q.count i x * q.localLaterResidual i j x
theorem measurable_comparableCenteredTerm (q : PivotCountParameters) (i j : PivotMark n) :
    Measurable (q.comparableCenteredTerm i j) :=
  ((q.measurable_centered i).mul (q.measurable_centered j)).ite
    (measurableSet_isStrictLaterStable i.1 j.1) measurable_const
theorem integrable_comparableCenteredTerm (q : PivotCountParameters) (i j : PivotMark n) :
    Integrable (q.comparableCenteredTerm i j) (continuousScoreLaw n) := by
  classical
  refine integrable_of_ae_abs_le_real (q.measurable_comparableCenteredTerm i j)
    (C := (n.factorial : ℝ) * (n.factorial : ℝ)) ?_
  filter_upwards [q.abs_centered_le_ae i, q.abs_centered_le_ae j] with x hi hj
  by_cases h : IsStrictLaterStable x i.1 j.1
  · rw [comparableCenteredTerm, if_pos h, abs_mul]
    exact mul_le_mul hi hj (abs_nonneg _) (by positivity)
  · rw [comparableCenteredTerm, if_neg h, abs_zero]
    positivity
theorem integrable_comparableResidualTerm (q : PivotCountParameters) (i j : PivotMark n) :
    Integrable (q.comparableResidualTerm i j) (continuousScoreLaw n) :=
  integrable_mul_of_ae_abs_le_real (q.measurable_count i) (q.measurable_localLaterResidual i j)
    (by positivity) (Eventually.of_forall fun x ↦
      (abs_of_nonneg (q.count_mem_Icc i x).1).symm ▸ (q.count_mem_Icc i x).2)
    (Eventually.of_forall fun x ↦
      (abs_of_nonneg (q.localLaterResidual_mem_Icc i j x).1).symm ▸
        (q.localLaterResidual_mem_Icc i j x).2)
private theorem integral_local_comparable_le_residual (q : PivotCountParameters) (i j : PivotMark n) :
    (∫ x, q.localCentered i x * q.localLaterCentered i j x ∂stableMarkScoreLaw i.1) ≤
      ∫ x, q.localCount i x * q.localLaterResidual i j x ∂stableMarkScoreLaw i.1 := by
  classical
  let ν := stableMarkScoreLaw i.1
  let Z := q.localCount i
  let M := q.localMean i
  let W := q.localCentered i
  let R := q.localLaterResidual i j
  let T := laterMovedCenteredTest q.lowerLength q.upperLength q.geometryBudget q.supportCap
    q.shortCutoff i.1 j.1 j.2
  let C := (n.factorial : ℝ)
  have hTm : Measurable[pivotFullRevealSpace i.1] T :=
    measurable_laterMovedCenteredTest _ _ _ _ _ _ _ _
  have hT : Measurable T := hTm.mono (pivotFullRevealSpace_le i.1) le_rfl
  have hTb : ∀ᵐ x ∂ν, |T x| ≤ C := laterMovedCenteredTest_abs_le_factorial_ae _ _ _ _ _ _ _ _
  have hZ : ∀ᵐ x ∂ν, |Z x| ≤ C := Eventually.of_forall fun x ↦
    (abs_of_nonneg (q.localCount_mem_Icc i x).1).symm ▸ (q.localCount_mem_Icc i x).2
  have hM : ∀ᵐ x ∂ν, |M x| ≤ C := (q.localMean_mem_Icc_ae i).mono fun x hx ↦
    (abs_of_nonneg hx.1).symm ▸ hx.2
  have hW : ∀ᵐ x ∂ν, |W x| ≤ C := q.abs_localCentered_le_ae i
  have hR : ∀ᵐ x ∂ν, |R x| ≤ C := Eventually.of_forall fun x ↦
    (abs_of_nonneg (q.localLaterResidual_mem_Icc i j x).1).symm ▸
      (q.localLaterResidual_mem_Icc i j x).2
  have hi {f g : ScoreProfile n → ℝ} (hf : Measurable f) (hg : Measurable g)
      (hf' : ∀ᵐ x ∂ν, |f x| ≤ C) (hg' : ∀ᵐ x ∂ν, |g x| ≤ C) : Integrable (f * g) ν :=
    integrable_mul_of_ae_abs_le_real hf hg (by positivity) hf' hg'
  have hWR : Integrable (W * R) ν := hi (q.measurable_localCentered i)
    (q.measurable_localLaterResidual i j) hW hR
  have hZR : Integrable (Z * R) ν := hi (q.measurable_localCount i)
    (q.measurable_localLaterResidual i j) hZ hR
  have hWT : Integrable (W * T) ν := hi (q.measurable_localCentered i) hT hW hTb
  have hzero : (∫ x, W x * T x ∂ν) = 0 :=
    integral_localPivotCentered_mul_eq_zero q.lowerLength q.upperLength q.geometryBudget
      q.supportCap q.shortCutoff i.1 i.2 T hTm.stronglyMeasurable.aestronglyMeasurable
      (hi (q.measurable_localCount i) hT hZ hTb) (hi (q.measurable_localMean i) hT hM hTb)
  have hs : (fun x ↦ W x * q.localLaterCentered i j x) =ᵐ[ν]
      fun x ↦ W x * T x + W x * R x := by
    filter_upwards [laterMovedCenteredTest_ae_eq q.lowerLength q.upperLength q.geometryBudget
      q.supportCap q.shortCutoff i.1 j.1 j.2] with x hx
    change T x = _ at hx
    rw [hx]
    by_cases h : IsStrictLaterStable x i.1 j.1
    · simp only [localLaterCentered, R, localLaterResidual, if_pos h, localCentered,
        localCount, localMean, Pi.sub_apply]
      ring
    · simp [localLaterCentered, R, localLaterResidual, h]
  change (∫ x, W x * q.localLaterCentered i j x ∂ν) ≤ ∫ x, Z x * R x ∂ν
  calc
    _ = (∫ x, W x * T x ∂ν) + ∫ x, W x * R x ∂ν :=
      (integral_congr_ae hs).trans (integral_add hWT hWR)
    _ = _ := by rw [hzero, zero_add]
    _ ≤ _ := by
      apply integral_mono_ae hWR hZR
      filter_upwards [q.localMean_mem_Icc_ae i] with x hx
      have hw : W x ≤ Z x := sub_le_self _ hx.1
      exact mul_le_mul_of_nonneg_right hw (q.localLaterResidual_mem_Icc i j x).1
theorem integral_comparableCenteredTerm_le_residual (q : PivotCountParameters) (i j : PivotMark n) :
    (∫ x, q.comparableCenteredTerm i j x ∂continuousScoreLaw n) ≤
      ∫ x, q.comparableResidualTerm i j x ∂continuousScoreLaw n := by
  classical
  have hC : q.comparableCenteredTerm i j =
      onStableMark i (fun x ↦ q.localCentered i x * q.localLaterCentered i j x) := by
    funext x
    by_cases h : IsStrictLaterStable x i.1 j.1
    · have hj : x ∈ {y | IsScoreStable y j.1} := h.1
      by_cases hi : x ∈ {y | IsScoreStable y i.1} <;>
        simp [comparableCenteredTerm, localLaterCentered, centered, onStableMark, hi, hj, h]
    · by_cases hi : x ∈ {y | IsScoreStable y i.1} <;>
        simp [comparableCenteredTerm, localLaterCentered, onStableMark, hi, h]
  have hR : q.comparableResidualTerm i j =
      onStableMark i (fun x ↦ q.localCount i x * q.localLaterResidual i j x) := by
    funext x
    by_cases h : x ∈ {y | IsScoreStable y i.1} <;>
      simp [comparableResidualTerm, count, onStableMark, h]
  rw [hC, hR, integral_onStableMark, integral_onStableMark]
  exact q.integral_local_comparable_le_residual i j
end PivotCountParameters
end MarkedLP
end

-- PivotCenteredReduction
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators
namespace MarkedLP
variable {n : ℕ}
private def IncomparableAnchors (p : Profile n) (μ ν : Matching n) : Prop :=
  ¬ MenWeaklyPrefer p μ ν ∧ ¬ MenWeaklyPrefer p ν μ
theorem measurableSet_incomparableAnchors (μ ν : Matching n) :
    MeasurableSet {x : ScoreProfile n | IncomparableAnchors (profileOfScores x) μ ν} :=
  measurable_profileOfScores n (MeasurableSet.of_discrete :
    MeasurableSet {p : Profile n | IncomparableAnchors p μ ν})
private theorem menWeaklyPrefer_antisymm {p : Profile n} {μ ν : Matching n}
    (h : MenWeaklyPrefer p μ ν) (h' : MenWeaklyPrefer p ν μ) : μ = ν :=
  Equiv.ext fun m ↦ (p.manRank m).injective (le_antisymm (h m) (h' m))
namespace PivotCountParameters
private noncomputable def incomparableCenteredTerm (q : PivotCountParameters) (i j : PivotMark n) :
    ScoreProfile n → ℝ :=
  {x | IncomparableAnchors (profileOfScores x) i.1 j.1}.indicator (q.centered i * q.centered j)
private noncomputable def incomparableUpperTerm (q : PivotCountParameters) (i j : PivotMark n) :
    ScoreProfile n → ℝ :=
  {x | IncomparableAnchors (profileOfScores x) i.1 j.1}.indicator
    (q.count i * q.count j + q.mean i * q.mean j)
private noncomputable def comparableCenteredMass (q : PivotCountParameters) (x : ScoreProfile n) : ℝ :=
  ∑ i : PivotMark n, ∑ j : PivotMark n, q.comparableCenteredTerm i j x
private noncomputable def comparableResidualMass (q : PivotCountParameters) (x : ScoreProfile n) : ℝ :=
  ∑ i : PivotMark n, ∑ j : PivotMark n, q.comparableResidualTerm i j x
private noncomputable def incomparableCenteredMass (q : PivotCountParameters) (x : ScoreProfile n) : ℝ :=
  ∑ i : PivotMark n, ∑ j : PivotMark n, q.incomparableCenteredTerm i j x
private noncomputable def incomparableUpperMass (q : PivotCountParameters) (x : ScoreProfile n) : ℝ :=
  ∑ i : PivotMark n, ∑ j : PivotMark n, q.incomparableUpperTerm i j x
private theorem centered_eq_zero_of_not_stable (q : PivotCountParameters) (i : PivotMark n)
    {x : ScoreProfile n} (h : ¬ IsScoreStable x i.1) : q.centered i x = 0 :=
  indicator_of_notMem (show x ∉ {x | IsScoreStable x i.1} from h) _
private theorem centered_zero_on_ineligible_ae (q : PivotCountParameters) (i : PivotMark n) :
    ∀ᵐ x ∂continuousScoreLaw n,
      ¬ IsLocallyEligiblePivot q.lowerLength q.upperLength q.geometryBudget x i.1 i.2 →
        q.centered i x = 0 := by
  filter_upwards [ae_scoreLaw_on_stableMark i (q.localMean_zero_on_ineligible_ae i)]
    with x hx hE
  by_cases h : x ∈ {x | IsScoreStable x i.1}
  · rw [centered, onStableMark, indicator_of_mem h, localCentered, Pi.sub_apply, hx h hE]
    exact sub_eq_zero.mpr (localFilteredDecorationCount_of_not_eligible _ _ hE)
  · exact q.centered_eq_zero_of_not_stable i h
private theorem centered_product_eq_zero_of_same_anchor (q : PivotCountParameters)
    {x : ScoreProfile n} (ht : ∀ row, Function.Injective (x row)) (i j : PivotMark n)
    (h : i.1 = j.1) (hne : i ≠ j)
    (hz : ∀ k : PivotMark n,
      ¬ IsLocallyEligiblePivot q.lowerLength q.upperLength q.geometryBudget x k.1 k.2 →
        q.centered k x = 0) :
    q.centered i x * q.centered j x = 0 := by
  by_cases hi : IsLocallyEligiblePivot q.lowerLength q.upperLength q.geometryBudget x i.1 i.2
  · by_cases hj : IsLocallyEligiblePivot q.lowerLength q.upperLength q.geometryBudget x j.1 j.2
    · have hei := hi.isSoleForwardExposed ht
      have hej := hj.isSoleForwardExposed ht
      have he : j.2 = i.2 := hei.2 j.2 (h ▸ hej.1)
      exact (hne (Prod.ext h he.symm)).elim
    · rw [hz j hj, mul_zero]
  · rw [hz i hi, zero_mul]
private theorem centered_product_split (q : PivotCountParameters)
    {x : ScoreProfile n} (ht : ∀ row, Function.Injective (x row)) (i j : PivotMark n)
    (hz : ∀ k : PivotMark n,
      ¬ IsLocallyEligiblePivot q.lowerLength q.upperLength q.geometryBudget x k.1 k.2 →
        q.centered k x = 0) :
    q.centered i x * q.centered j x =
      (if i = j then (q.centered i x) ^ 2 else 0) +
        q.comparableCenteredTerm i j x + q.comparableCenteredTerm j i x +
        q.incomparableCenteredTerm i j x := by
  classical
  by_cases he : i = j
  · subst j
    have hle : MenWeaklyPrefer (profileOfScores x) i.1 i.1 := fun _ ↦ le_rfl
    simp [comparableCenteredTerm, IsStrictLaterStable, incomparableCenteredTerm,
      IncomparableAnchors, hle, pow_two]
  · by_cases hi : IsScoreStable x i.1
    · by_cases hj : IsScoreStable x j.1
      · by_cases hsame : i.1 = j.1
        · have hle : MenWeaklyPrefer (profileOfScores x) j.1 j.1 := fun _ ↦ le_rfl
          simp [q.centered_product_eq_zero_of_same_anchor ht i j hsame he hz,
            comparableCenteredTerm, IsStrictLaterStable, incomparableCenteredTerm,
            IncomparableAnchors, he, hsame, hle]
        · by_cases hle : MenWeaklyPrefer (profileOfScores x) i.1 j.1
          · have hge : ¬ MenWeaklyPrefer (profileOfScores x) j.1 i.1 :=
              fun h ↦ hsame (menWeaklyPrefer_antisymm hle h)
            simp [comparableCenteredTerm, IsStrictLaterStable, incomparableCenteredTerm,
              IncomparableAnchors, he, hi, hj, hsame, hle, hge]
          · by_cases hge : MenWeaklyPrefer (profileOfScores x) j.1 i.1
            · simp [comparableCenteredTerm, IsStrictLaterStable, incomparableCenteredTerm,
                IncomparableAnchors, he, hi, hj, Ne.symm hsame, hle, hge, mul_comm]
            · simp [comparableCenteredTerm, IsStrictLaterStable, incomparableCenteredTerm,
                IncomparableAnchors, he, hi, hj, hle, hge]
      · simp [q.centered_eq_zero_of_not_stable j hj, comparableCenteredTerm,
          incomparableCenteredTerm, indicator_apply, he]
    · simp [q.centered_eq_zero_of_not_stable i hi, comparableCenteredTerm,
        incomparableCenteredTerm, indicator_apply, he]
private theorem totalCount_sub_totalMean_eq_sum_centered (q : PivotCountParameters) (x : ScoreProfile n) :
    totalLocalFilteredDecorationCount q.lowerLength q.upperLength q.geometryBudget
        q.supportCap q.shortCutoff x -
      totalLocalPivotConditionalMean q.lowerLength q.upperLength q.geometryBudget
        q.supportCap q.shortCutoff x = ∑ i : PivotMark n, q.centered i x := by
  classical
  have he : totalLocalFilteredDecorationCount q.lowerLength q.upperLength q.geometryBudget
      q.supportCap q.shortCutoff x = ∑ i : PivotMark n, q.count i x := by
    rw [Fintype.sum_prod_type]
    unfold totalLocalFilteredDecorationCount
    apply Finset.sum_congr rfl
    intro μ _
    apply Finset.sum_congr rfl
    intro ρ _
    simp [count, onStableMark, localCount, indicator_apply]
  rw [he, totalLocalPivotConditionalMean, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ (q.centered_eq_sub i x).symm
private theorem centered_secondMoment_integrand_ae (q : PivotCountParameters) :
    ∀ᵐ x ∂continuousScoreLaw n,
      (totalLocalFilteredDecorationCount q.lowerLength q.upperLength q.geometryBudget
          q.supportCap q.shortCutoff x -
        totalLocalPivotConditionalMean q.lowerLength q.upperLength q.geometryBudget
          q.supportCap q.shortCutoff x) ^ 2 =
        (∑ i : PivotMark n, (q.centered i x) ^ 2) + 2 * q.comparableCenteredMass x +
          q.incomparableCenteredMass x := by
  classical
  have hz : ∀ᵐ x ∂continuousScoreLaw n, ∀ i : PivotMark n,
      ¬ IsLocallyEligiblePivot q.lowerLength q.upperLength q.geometryBudget x i.1 i.2 →
        q.centered i x = 0 := ae_all_iff.2 q.centered_zero_on_ineligible_ae
  filter_upwards [ae_injective_rows n, hz] with x ht hz
  rw [q.totalCount_sub_totalMean_eq_sum_centered x, pow_two, Finset.sum_mul]
  simp_rw [Finset.mul_sum, q.centered_product_split ht _ _ hz]
  simp only [Finset.sum_add_distrib]
  have hd : (∑ i : PivotMark n, ∑ j : PivotMark n,
      if i = j then (q.centered i x) ^ 2 else 0) = ∑ i : PivotMark n, (q.centered i x) ^ 2 := by
    simp
  have hswap : (∑ i : PivotMark n, ∑ j : PivotMark n, q.comparableCenteredTerm j i x) =
      q.comparableCenteredMass x := Finset.sum_comm
  rw [hd, hswap]
  unfold comparableCenteredMass incomparableCenteredMass
  ring
private theorem integrable_centered_mul (q : PivotCountParameters) (i j : PivotMark n) :
    Integrable (q.centered i * q.centered j) (continuousScoreLaw n) :=
  integrable_mul_of_ae_abs_le_real (q.measurable_centered i) (q.measurable_centered j)
    (by positivity) (q.abs_centered_le_ae i) (q.abs_centered_le_ae j)
private theorem integrable_incomparableCenteredTerm (q : PivotCountParameters) (i j : PivotMark n) :
    Integrable (q.incomparableCenteredTerm i j) (continuousScoreLaw n) :=
  (q.integrable_centered_mul i j).indicator (measurableSet_incomparableAnchors i.1 j.1)
private theorem integrable_incomparableUpperTerm (q : PivotCountParameters) (i j : PivotMark n) :
    Integrable (q.incomparableUpperTerm i j) (continuousScoreLaw n) := by
  have hc (k : PivotMark n) : ∀ᵐ x ∂continuousScoreLaw n, |q.count k x| ≤ (n.factorial : ℝ) :=
    Eventually.of_forall fun x ↦ (abs_of_nonneg (q.count_mem_Icc k x).1).symm ▸
      (q.count_mem_Icc k x).2
  have hm (k : PivotMark n) : ∀ᵐ x ∂continuousScoreLaw n, |q.mean k x| ≤ (n.factorial : ℝ) :=
    (q.mean_mem_Icc_ae k).mono fun x hx ↦ (abs_of_nonneg hx.1).symm ▸ hx.2
  exact ((integrable_mul_of_ae_abs_le_real (q.measurable_count i) (q.measurable_count j)
    (by positivity) (hc i) (hc j)).add
      (integrable_mul_of_ae_abs_le_real (q.measurable_mean i) (q.measurable_mean j)
        (by positivity) (hm i) (hm j))).indicator (measurableSet_incomparableAnchors i.1 j.1)
private theorem integral_incomparableCenteredMass_le (q : PivotCountParameters) :
    (∫ x, q.incomparableCenteredMass x ∂continuousScoreLaw n) ≤
      ∫ x, q.incomparableUpperMass x ∂continuousScoreLaw n := by
  apply integral_mono_ae
  · exact integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦
      q.integrable_incomparableCenteredTerm i j
  · exact integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦
      q.integrable_incomparableUpperTerm i j
  have hM := ae_all_iff.2 (q.mean_mem_Icc_ae (n := n))
  filter_upwards [hM] with x hx
  apply Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ ?_
  classical
  by_cases h : x ∈ {x | IncomparableAnchors (profileOfScores x) i.1 j.1}
  · rw [incomparableCenteredTerm, incomparableUpperTerm, indicator_of_mem h, indicator_of_mem h]
    simp only [Pi.mul_apply, Pi.add_apply, q.centered_eq_sub]
    nlinarith [mul_nonneg (q.count_mem_Icc i x).1 (hx j).1,
      mul_nonneg (hx i).1 (q.count_mem_Icc j x).1]
  · rw [incomparableCenteredTerm, incomparableUpperTerm, indicator_of_notMem h, indicator_of_notMem h]
private theorem integral_comparableCenteredMass_le (q : PivotCountParameters) :
    (∫ x, q.comparableCenteredMass x ∂continuousScoreLaw n) ≤
      ∫ x, q.comparableResidualMass x ∂continuousScoreLaw n := by
  unfold comparableCenteredMass comparableResidualMass
  rw [integral_finsetSum _ (fun i _ ↦ integrable_finsetSum _ fun j _ ↦
    q.integrable_comparableCenteredTerm i j),
    integral_finsetSum _ (fun i _ ↦ integrable_finsetSum _ fun j _ ↦
      q.integrable_comparableResidualTerm i j)]
  apply Finset.sum_le_sum
  intro i _
  rw [integral_finsetSum _ (fun j _ ↦ q.integrable_comparableCenteredTerm i j),
    integral_finsetSum _ (fun j _ ↦ q.integrable_comparableResidualTerm i j)]
  exact Finset.sum_le_sum fun j _ ↦ q.integral_comparableCenteredTerm_le_residual i j
theorem integral_centered_sq_le_pair_terms (q : PivotCountParameters) :
    (∫ x, (totalLocalFilteredDecorationCount q.lowerLength q.upperLength q.geometryBudget
          q.supportCap q.shortCutoff x -
        totalLocalPivotConditionalMean q.lowerLength q.upperLength q.geometryBudget
          q.supportCap q.shortCutoff x) ^ 2 ∂continuousScoreLaw n) ≤
      (∑ i : PivotMark n, ∫ x, (q.localCount i x) ^ 2 ∂stableMarkScoreLaw i.1) +
        2 * (∫ x, q.comparableResidualMass x ∂continuousScoreLaw n) +
        ∫ x, q.incomparableUpperMass x ∂continuousScoreLaw n := by
  let ν := continuousScoreLaw n
  let D (x : ScoreProfile n) := ∑ i : PivotMark n, (q.centered i x) ^ 2
  have hD (i : PivotMark n) : Integrable (fun x ↦ (q.centered i x) ^ 2) ν := by
    simp only [pow_two]
    exact q.integrable_centered_mul i i
  have hd : Integrable D ν := integrable_finsetSum _ fun i _ ↦ hD i
  have hc : Integrable (q.comparableCenteredMass (n := n)) ν :=
    integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦
      q.integrable_comparableCenteredTerm i j
  have hi : Integrable (q.incomparableCenteredMass (n := n)) ν :=
    integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦
      q.integrable_incomparableCenteredTerm i j
  rw [integral_congr_ae q.centered_secondMoment_integrand_ae]
  have he : (∫ x, D x + 2 * q.comparableCenteredMass x + q.incomparableCenteredMass x ∂ν) =
      (∫ x, D x ∂ν) + 2 * (∫ x, q.comparableCenteredMass x ∂ν) +
        ∫ x, q.incomparableCenteredMass x ∂ν := by
    calc
      _ = (∫ x, D x + 2 * q.comparableCenteredMass x ∂ν) +
          ∫ x, q.incomparableCenteredMass x ∂ν := integral_add (hd.add (hc.const_mul 2)) hi
      _ = _ := by rw [integral_add hd (hc.const_mul 2), integral_const_mul]
  rw [he]
  refine add_le_add (add_le_add ?_ (mul_le_mul_of_nonneg_left
    q.integral_comparableCenteredMass_le (by norm_num))) q.integral_incomparableCenteredMass_le
  unfold D
  rw [integral_finsetSum _ (fun i _ ↦ hD i)]
  exact Finset.sum_le_sum fun i _ ↦ q.integral_sq_centered_le_localCount_sq i
end PivotCountParameters
end MarkedLP
end

-- LogarithmicCutoffs
section
open Filter
open scoped Topology BigOperators
namespace MarkedLP
private noncomputable def logarithmicCycleCutoff (n : ℕ) : ℕ := ⌊Real.log (n : ℝ)⌋₊
end MarkedLP
end

-- LennonPittelLowerTailCriterion
section
open Filter MeasureTheory StableMarriage
open scoped ENNReal Topology
namespace MarkedLP
private noncomputable def scaledCenteredCountMoment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (a : ℝ) (T M : Ω → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (((T x - M x) / a) ^ 2) ∂μ
end MarkedLP
end

-- PivotVarianceClosure
section
open Filter MeasureTheory Set StableMarriage Asymptotics
open scoped BigOperators ENNReal Topology
namespace MarkedLP
namespace PivotCountParameters
variable {n : ℕ}
private noncomputable def incomparableMeanProductMass (q : PivotCountParameters) (x : ScoreProfile n) : ℝ :=
  ∑ i : PivotMark n, ∑ j : PivotMark n,
    {x | IncomparableAnchors (profileOfScores x) i.1 j.1}.indicator (q.mean i * q.mean j) x
private noncomputable def incomparableCountProductMass (q : PivotCountParameters) (x : ScoreProfile n) : ℝ :=
  ∑ i : PivotMark n, ∑ j : PivotMark n,
    {x | IncomparableAnchors (profileOfScores x) i.1 j.1}.indicator (q.count i * q.count j) x
theorem integrable_incomparableMeanProductMass (q : PivotCountParameters) :
    Integrable (q.incomparableMeanProductMass (n := n)) (continuousScoreLaw n) := by
  have h (i : PivotMark n) : ∀ᵐ x ∂continuousScoreLaw n, |q.mean i x| ≤ (n.factorial : ℝ) :=
    (q.mean_mem_Icc_ae i).mono fun x hx ↦ (abs_of_nonneg hx.1).symm ▸ hx.2
  exact integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦
    (integrable_mul_of_ae_abs_le_real (q.measurable_mean i) (q.measurable_mean j)
      (by positivity) (h i) (h j)).indicator (measurableSet_incomparableAnchors i.1 j.1)
theorem integrable_incomparableCountProductMass (q : PivotCountParameters) :
    Integrable (q.incomparableCountProductMass (n := n)) (continuousScoreLaw n) := by
  have h (i : PivotMark n) : ∀ᵐ x ∂continuousScoreLaw n, |q.count i x| ≤ (n.factorial : ℝ) :=
    Eventually.of_forall fun x ↦ (abs_of_nonneg (q.count_mem_Icc i x).1).symm ▸
      (q.count_mem_Icc i x).2
  exact integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦
    (integrable_mul_of_ae_abs_le_real (q.measurable_count i) (q.measurable_count j)
      (by positivity) (h i) (h j)).indicator (measurableSet_incomparableAnchors i.1 j.1)
theorem integral_incomparableUpperMass_eq (q : PivotCountParameters) :
    (∫ x, q.incomparableUpperMass x ∂continuousScoreLaw n) =
      (∫ x, q.incomparableCountProductMass x ∂continuousScoreLaw n) +
        ∫ x, q.incomparableMeanProductMass x ∂continuousScoreLaw n := by
  have h (x : ScoreProfile n) : q.incomparableUpperMass x =
      q.incomparableCountProductMass x + q.incomparableMeanProductMass x := by
    have hterm (i j : PivotMark n) :
        q.incomparableUpperTerm i j x =
          {x | IncomparableAnchors (profileOfScores x) i.1 j.1}.indicator (q.count i * q.count j) x +
          {x | IncomparableAnchors (profileOfScores x) i.1 j.1}.indicator (q.mean i * q.mean j) x := by
      classical
      by_cases hmem : x ∈ {y | IncomparableAnchors (profileOfScores y) i.1 j.1}
      · simp only [incomparableUpperTerm, indicator_of_mem hmem, Pi.add_apply]
      · simp only [incomparableUpperTerm, indicator_of_notMem hmem, add_zero]
    simp only [incomparableUpperMass, incomparableCountProductMass,
      incomparableMeanProductMass, hterm, Finset.sum_add_distrib]
  simp_rw [h]
  exact integral_add q.integrable_incomparableCountProductMass q.integrable_incomparableMeanProductMass
end PivotCountParameters
variable {n : ℕ}
private noncomputable def pivotRawDiagonalMass (q : PivotCountParameters) (n : ℕ) : ℝ :=
  ∑ i : PivotMark n, ∫ x, (q.localCount i x) ^ 2 ∂stableMarkScoreLaw i.1
namespace PivotCountParameters
private noncomputable def aggregateCount (q : PivotCountParameters) (n : ℕ) : ScoreProfile n → ℝ :=
  totalLocalFilteredDecorationCount q.lowerLength q.upperLength q.geometryBudget
    q.supportCap q.shortCutoff
private noncomputable def aggregateMean (q : PivotCountParameters) (n : ℕ) : ScoreProfile n → ℝ :=
  totalLocalPivotConditionalMean q.lowerLength q.upperLength q.geometryBudget
    q.supportCap q.shortCutoff
private theorem aggregateCount_sub_mean_eq_sum (q : PivotCountParameters) (x : ScoreProfile n) :
    q.aggregateCount n x - q.aggregateMean n x = ∑ i : PivotMark n, q.centered i x := by
  classical
  have hcount : q.aggregateCount n x = ∑ i : PivotMark n, q.count i x := by
    rw [Fintype.sum_prod_type]
    unfold aggregateCount totalLocalFilteredDecorationCount
    refine Finset.sum_congr rfl fun μ _ ↦ Finset.sum_congr rfl fun ρ _ ↦ ?_
    simp [count, onStableMark, localCount, indicator_apply]
  rw [hcount, aggregateMean, totalLocalPivotConditionalMean, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ (q.centered_eq_sub i x).symm
private theorem integrable_sq_aggregateCount_sub_mean (q : PivotCountParameters) :
    Integrable (fun x ↦ (q.aggregateCount n x - q.aggregateMean n x) ^ 2)
      (continuousScoreLaw n) := by
  simp_rw [aggregateCount_sub_mean_eq_sum, pow_two, Finset.sum_mul, Finset.mul_sum]
  exact integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦
    integrable_mul_of_ae_abs_le_real (q.measurable_centered i) (q.measurable_centered j)
      (by positivity) (q.abs_centered_le_ae i) (q.abs_centered_le_ae j)
private theorem scaledCenteredCountMoment_aggregate_eq (q : PivotCountParameters) (a : ℝ) :
    scaledCenteredCountMoment (continuousScoreLaw n) a (q.aggregateCount n) (q.aggregateMean n) =
      ENNReal.ofReal ((∫ x, (q.aggregateCount n x - q.aggregateMean n x) ^ 2
        ∂continuousScoreLaw n) / a ^ 2) := by
  unfold scaledCenteredCountMoment
  simp_rw [div_pow]
  have hi := (q.integrable_sq_aggregateCount_sub_mean (n := n)).div_const (a ^ 2)
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun x ↦ by positivity),
    integral_div]
end PivotCountParameters
end MarkedLP
end

noncomputable section
namespace OMA.R_LennonPittel_lennon_pittel_conjecture_R3_H2_R1_H2_R1
open Filter MeasureTheory Set StableMarriage MarkedLP Asymptotics
open scoped ENNReal Topology MarkedLP
private def params (b A B κ : ℝ) (n : ℕ) : PivotCountParameters :=
  ⟨b,A,B,pivotDecorationSupportCap κ n,logarithmicCycleCutoff n⟩

private def admissible (b A B κ : ℝ) : Prop :=
  0 < b ∧ b ≤ 1 ∧ 1 ≤ A ∧ 0 < B ∧ 0 < κ ∧ κ < b ∧
    24*κ^2/2 + (B+1)*κ ≤ 1/4 ∧
    Real.exp (κ*(2*(1+B))) * (2*κ*(B/(1/128))) ≤ 3/32

/-- The mean number of eligible reverse decorations, conditional on the male-side reveal,
has order at least n log n outside a set of arbitrarily small probability. -/
def H1 : Prop := ∀ η : ℝ, 0 < η → ∃ b A B κ d : ℝ,
  admissible b A B κ ∧ 0 < d ∧ ∀ᶠ n : ℕ in atTop,
    ENNReal.ofReal (1-η) ≤ continuousScoreLaw n
      {x | d*((n:ℝ)*Real.log n) ≤ (params b A B κ n).aggregateMean n x}

/-- The raw diagonal and the products of conditional means of incomparable anchors
are negligible on the squared target scale. -/
def H2 : Prop := ∀ b A B κ : ℝ, admissible b A B κ →
  (fun n : ℕ => pivotRawDiagonalMass (params b A B κ n) n +
    ∫ x, (params b A B κ n).incomparableMeanProductMass x ∂continuousScoreLaw n) =o[atTop]
      (fun n : ℕ => ((n:ℝ)*Real.log n)^2)

/-- The ordered comparable-anchor residual is negligible. -/
def H3 : Prop := ∀ b A B κ : ℝ, admissible b A B κ →
  (fun n : ℕ => ∫ x, (params b A B κ n).comparableResidualMass x ∂continuousScoreLaw n) =o[atTop]
    (fun n : ℕ => ((n:ℝ)*Real.log n)^2)

/-- The raw products of decoration counts for incomparable anchors are negligible. -/
def H4 : Prop := ∀ b A B κ : ℝ, admissible b A B κ →
  (fun n : ℕ => ∫ x, (params b A B κ n).incomparableCountProductMass x ∂continuousScoreLaw n) =o[atTop]
    (fun n : ℕ => ((n:ℝ)*Real.log n)^2)

section
private lemma stable_measurable (n : ℕ) :
    Measurable (fun x : ScoreProfile n => (Nat.card {m : Matching n // IsScoreStable x m} : ℝ)) := by
  classical
  have he (x : ScoreProfile n) : (Nat.card {m : Matching n // IsScoreStable x m} : ℝ) =
      ∑ m : Matching n, ({x : ScoreProfile n | IsScoreStable x m}.indicator (fun _ => (1:ℝ))) x := by
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
    simp [Set.indicator_apply,Finset.sum_boole]
  simp_rw [he]
  exact Finset.measurable_sum _ fun m _ => measurable_const.indicator (measurableSet_isScoreStable m)

end

theorem main : H1 → H2 → H3 → H4 → OMA.R_LennonPittel_lennon_pittel_conjecture_R3_H2_R1.H2 := by
  classical
  intro abund diag comparable incomparable η hη
  obtain ⟨b,A,B,κ,d,hq,hd,hm⟩ := abund η hη
  refine ⟨d,hd,fun e he => ?_⟩
  let q := params b A B κ
  let S (n : ℕ) (x : ScoreProfile n) : ℝ := Nat.card {m : Matching n // IsScoreStable x m}
  let T (n : ℕ) (x : ScoreProfile n) := min ((q n).aggregateCount n x) (S n x)
  refine ⟨T,fun n => (q n).aggregateMean n,
    fun n => (measurable_totalLocalFilteredDecorationCount _ _ _ _ _).min (stable_measurable n),
    fun n => measurable_totalLocalPivotConditionalMean _ _ _ _ _, fun n x => min_le_right _ _, ?_⟩
  have hb := isLittleO_iff.mp (((diag b A B κ hq).add
    ((comparable b A B κ hq).const_mul_left (2:ℝ))).add (incomparable b A B κ hq)) he
  have hK := eventually_pivotDecorationSupportCap_bounds hq.2.2.2.2.1
  filter_upwards [hb,hm,hK,eventually_gt_atTop (1:ℕ)] with n hh hm hK hn
  refine ⟨hm,?_⟩
  have hle := ae_totalLocalFilteredDecorationCount_le (by omega : 0<n) hq.2.2.2.2.2.1 hK.2.1
    (A:=A) (B:=B) (L:=logarithmicCycleCutoff n)
  have hT : T n =ᵐ[continuousScoreLaw n] (q n).aggregateCount n := by
    filter_upwards [hle,ae_injective_rows n] with x hx hi
    have hcard : Nat.card {m : Matching n // IsScoreStable x m} = numStableMatchings (profileOfScores x) := by
      rw [numStableMatchings,← Nat.card_eq_fintype_card]
      exact Nat.card_congr (Equiv.subtypeEquivRight fun m => (isStable_profileOfScores_iff hi m).symm)
    apply min_eq_left
    change _ ≤ (Nat.card {m : Matching n // IsScoreStable x m} : ℝ)
    rwa [hcard]
  change (∫⁻ x, ENNReal.ofReal (((T n x - (q n).aggregateMean n x) / ((n:ℝ)*Real.log n))^2)
    ∂continuousScoreLaw n) ≤ _
  rw [lintegral_congr_ae (hT.mono fun x hx => by rw [hx])]
  change scaledCenteredCountMoment (continuousScoreLaw n) ((n:ℝ)*Real.log n)
    ((q n).aggregateCount n) ((q n).aggregateMean n) ≤ _
  rw [(q n).scaledCenteredCountMoment_aggregate_eq]
  apply ENNReal.ofReal_le_ofReal
  apply (div_le_iff₀ (sq_pos_of_pos (mul_pos (by positivity) (Real.log_pos (by exact_mod_cast hn))))).2
  have hq' := (q n).integral_centered_sq_le_pair_terms (n:=n)
  rw [(q n).integral_incomparableUpperMass_eq] at hq'
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ((n:ℝ)*Real.log n))] at hh
  apply le_trans hq'
  have hu := (le_abs_self _).trans hh
  change pivotRawDiagonalMass (q n) n + 2*_ + (_ + _) ≤ _
  change pivotRawDiagonalMass (q n) n + _ + 2*_ + _ ≤ _ at hu
  linarith only [hu]
end OMA.R_LennonPittel_lennon_pittel_conjecture_R3_H2_R1_H2_R1
end
