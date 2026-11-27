import FormalConjectures.ErdosProblems.«1154»
import Mathlib.MeasureTheory.MeasurableSpace.Card
import Mathlib.Algebra.Polynomial.Cardinal
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
Mauldin, Subfields of R with arbitrary Hausdorff dimension (2016).
https://doi.org/10.1017/S0305004116000207
The geometric step uses the dyadic rational-image construction of Wang,
arXiv:2610.09707v1, §3, with one-stage lookahead in the interval estimates.
The transfinite construction uses CH only to enumerate the small Borel sets.
-/

noncomputable section

open Set MeasureTheory TopologicalSpace
open scoped Cardinal ENNReal NNReal

namespace MauldinRecursion

private abbrev W := (Ordinal.omega.{0} 1).ToType

theorem countable_initial (ξ : W) : (Iio ξ).Countable := by
  apply Cardinal.le_aleph0_iff_set_countable.mp
  apply Cardinal.lt_aleph_one_iff.mp
  have h := Cardinal.mk_Iio_lt ξ (by
    rw [Cardinal.mk_toType, Ordinal.card_omega, Cardinal.ord_aleph, Ordinal.type_toType])
  simpa only [W, Cardinal.mk_toType, Ordinal.card_omega] using h

theorem measurable_superset_of_dimH_lt {s : Set ℝ} {a : ℝ≥0∞} (h : dimH s < a) :
    ∃ t : Set ℝ, MeasurableSet t ∧ dimH t < a ∧ s ⊆ t := by
  obtain ⟨b, hsb, hba⟩ := exists_between h
  have hb : b ≠ ⊤ := hba.ne_top
  lift b to ℝ≥0 using hb
  let t := toMeasurable μH[b] s
  have ht : μH[b] t = 0 := (measure_toMeasurable s).trans (hausdorffMeasure_of_dimH_lt hsb)
  exact ⟨t, measurableSet_toMeasurable _ _, (dimH_le_of_hausdorffMeasure_ne_top (by rw [ht]; simp)).trans_lt hba,
    subset_toMeasurable _ _⟩

private theorem cardinal_borel_le : #{t : Set ℝ | MeasurableSet t} ≤ 𝔠 := by
  have hbase : #(countableBasis ℝ) ≤ 𝔠 :=
    (Cardinal.le_aleph0_iff_set_countable.mpr (countable_countableBasis ℝ)).trans
      Cardinal.aleph0_le_continuum
  have hB := (isBasis_countableBasis ℝ).borel_eq_generateFrom
  have hm : (inferInstance : MeasurableSpace ℝ) = MeasurableSpace.generateFrom (countableBasis ℝ) :=
    (BorelSpace.measurable_eq (α := ℝ)).trans hB
  change #{t : Set ℝ | @MeasurableSet ℝ (inferInstance : MeasurableSpace ℝ) t} ≤ 𝔠
  rw [hm]
  exact MeasurableSpace.cardinal_measurableSet_le_continuum hbase

private abbrev SmallBorel (a : ℝ≥0∞) :=
  {s : Set ℝ // MeasurableSet s ∧ dimH s < a}

private theorem exists_enumeration {a : ℝ≥0∞} (ha : 0 < a) [Fact ((ℵ₁ : Cardinal.{0}) = 𝔠)] :
    ∃ t : W → SmallBorel a, Function.Surjective t := by
  classical
  have hcard : #(SmallBorel a) ≤ #W := by
    have hl : #(SmallBorel a) ≤ #{s : Set ℝ | MeasurableSet s} :=
      Cardinal.mk_le_of_injective (f := fun s : SmallBorel a => (⟨s.val,s.2.1⟩ : {s : Set ℝ // MeasurableSet s}))
        (fun _ _ h => Subtype.ext (congrArg (fun s : {s : Set ℝ // MeasurableSet s} => s.val) h))
    have hc := (Fact.out : (ℵ₁ : Cardinal.{0}) = 𝔠)
    rw [Cardinal.mk_toType, Ordinal.card_omega, hc]
    exact hl.trans cardinal_borel_le
  obtain ⟨e⟩ := (Cardinal.le_def _ _).mp hcard
  let : Nonempty (SmallBorel a) := ⟨⟨∅, MeasurableSet.empty, by simpa using ha⟩⟩
  exact ⟨Function.invFun e, Function.invFun_surjective e.injective⟩

def adjoining (F : Subfield ℝ) (x : ℝ) : Subfield ℝ :=
  Subfield.closure (insert x (F : Set ℝ))

theorem le_adjoining (F : Subfield ℝ) (x : ℝ) : F ≤ adjoining F x :=
  fun _ hx => Subfield.subset_closure (Or.inr hx)

theorem mem_adjoining (F : Subfield ℝ) (x : ℝ) : x ∈ adjoining F x :=
  Subfield.subset_closure (mem_insert _ _)

private theorem closure_countable {s : Set ℝ} (hs : s.Countable) :
    (Subfield.closure s : Set ℝ).Countable :=
  Cardinal.le_aleph0_iff_set_countable.mp
    ((Subfield.cardinalMk_closure_le_max s).trans
      (max_le (Cardinal.le_aleph0_iff_set_countable.mpr hs) le_rfl))

private theorem iSup_countable {ι : Type*} [Countable ι] {F : ι → Subfield ℝ}
    (h : ∀ i, (F i : Set ℝ).Countable) : (↑(⨆ i, F i) : Set ℝ).Countable := by
  have hsub : (⨆ i, F i) ≤ Subfield.closure (⋃ i, (F i : Set ℝ)) :=
    iSup_le (fun i x hx => Subfield.subset_closure (mem_iUnion.mpr ⟨i,hx⟩))
  exact (closure_countable (countable_iUnion h)).mono hsub

private theorem coe_iSup_subset_of_monotone {ι : Type*} [LinearOrder ι] {F : ι → Subfield ℝ}
    (hF : Monotone F) {D : Set ℝ} (hD : (⊥ : Subfield ℝ).carrier ⊆ D)
    (h : ∀ i, (F i : Set ℝ) ⊆ D) : (↑(⨆ i, F i) : Set ℝ) ⊆ D := by
  classical
  cases isEmpty_or_nonempty ι
  · rw [show (⨆ i, F i) = ⊥ from le_antisymm (iSup_le (fun i => isEmptyElim i)) bot_le]
    exact hD
  · intro x hx
    have hm := (Subfield.mem_iSup_of_directed hF.directed_le).mp hx
    obtain ⟨i, hi⟩ := hm
    exact h i hi

/-- Sufficient extension property in the geometric part of the proof. -/
def Extension (D : Set ℝ) (a : ℝ≥0∞) : Prop :=
  ∀ F : Subfield ℝ, (F : Set ℝ).Countable → (F : Set ℝ) ⊆ D →
    ∀ E : Set ℝ, dimH E < a → ∃ x ∉ E, (adjoining F x : Set ℝ) ⊆ D

set_option maxHeartbeats 950000 in
/-- Recursively choose outside each Borel set of smaller dimension while staying in D. -/
theorem exists_subfield_of_extension {a : ℝ≥0∞} (ha : 0 < a) [Fact ((ℵ₁ : Cardinal.{0}) = 𝔠)]
    (D : Set ℝ) (hD : dimH D ≤ a) (hq : (⊥ : Subfield ℝ).carrier ⊆ D)
    (hExt : Extension D a) : ∃ F : Subfield ℝ, dimH (F : Set ℝ) = a := by
  classical
  obtain ⟨E, hE⟩ := exists_enumeration ha
  let prior (ξ : W) (prev : ∀ η : W, η < ξ → Subfield ℝ) :=
    ⨆ η : Iio ξ, prev η η.2
  let ok (F : Subfield ℝ) := (F : Set ℝ).Countable ∧ (F : Set ℝ) ⊆ D
  let step (ξ : W) (prev : ∀ η : W, η < ξ → Subfield ℝ) : Subfield ℝ :=
    if h : ok (prior ξ prev) then
      adjoining (prior ξ prev) (hExt _ h.1 h.2 (E ξ).val (E ξ).2.2).choose
    else prior ξ prev
  let F := wellFounded_lt.fix step
  let P (ξ : W) := prior ξ (fun η _ => F η)
  have eqF (ξ : W) : F ξ = step ξ (fun η _ => F η) := WellFounded.fix_eq _ _ _
  have step_ge (ξ : W) (prev : ∀ η : W, η < ξ → Subfield ℝ) : prior ξ prev ≤ step ξ prev := by
    unfold step
    split
    · exact le_adjoining _ _
    · exact le_rfl
  have monoF : Monotone F := by
    apply monotone_iff_forall_lt.mpr
    intro i j hij
    have h₁ : F i ≤ P j := le_iSup (fun η : Iio j => F η) ⟨i, hij⟩
    have h₂ : P j ≤ F j := by
      rw [eqF j]
      change prior j (fun η _ => F η) ≤ step j (fun η _ => F η)
      exact step_ge j (fun η _ => F η)
    exact h₁.trans h₂
  have good : ∀ ξ : W, ok (F ξ) := by
    let wf : WellFounded ((· < ·) : W → W → Prop) := wellFounded_lt
    intro ξ
    refine wf.induction (C := fun η => ok (F η)) ξ ?_
    intro ξ ih
    let : Countable (Iio ξ) := (countable_initial ξ).to_subtype
    have hpC : (P ξ : Set ℝ).Countable := iSup_countable (fun η : Iio ξ => (ih η.val (mem_Iio.mp η.2)).1)
    have hpD : (P ξ : Set ℝ) ⊆ D := coe_iSup_subset_of_monotone
      (fun i j hij => monoF (show i.val ≤ j.val from hij)) hq (fun η : Iio ξ => (ih η.val (mem_Iio.mp η.2)).2)
    have hp : ok (P ξ) := ⟨hpC,hpD⟩
    have eq : F ξ = adjoining (P ξ) (hExt _ hpC hpD (E ξ).val (E ξ).2.2).choose := by
      exact (eqF ξ).trans (dif_pos hp)
    change (F ξ : Set ℝ).Countable ∧ (F ξ : Set ℝ) ⊆ D
    rw [eq]
    exact ⟨closure_countable (hpC.insert _), (hExt (P ξ) hpC hpD (E ξ).val (E ξ).2.2).choose_spec.2⟩
  let R := ⨆ ξ, F ξ
  have hR : (R : Set ℝ) ⊆ D := coe_iSup_subset_of_monotone monoF hq (fun ξ => (good ξ).2)
  refine ⟨R, le_antisymm ((dimH_mono hR).trans hD) ?_⟩
  by_contra! hsmall
  obtain ⟨B, hBm, hBdim, hRB⟩ := measurable_superset_of_dimH_lt hsmall
  obtain ⟨ξ, hξ⟩ := hE ⟨B, hBm, hBdim⟩
  have hPB : ok (P ξ) := by
    let : Countable (Iio ξ) := (countable_initial ξ).to_subtype
    exact ⟨iSup_countable (fun η : Iio ξ => (good η).1),
      coe_iSup_subset_of_monotone (fun i j hij => monoF (show i.val ≤ j.val from hij))
        hq (fun η : Iio ξ => (good η).2)⟩
  let x := (hExt _ hPB.1 hPB.2 (E ξ).val (E ξ).2.2).choose
  have hnx : x ∉ (E ξ).val := (hExt (P ξ) hPB.1 hPB.2 (E ξ).val (E ξ).2.2).choose_spec.1
  have hx : x ∈ F ξ := by
    have eq : F ξ = adjoining (P ξ) x := (eqF ξ).trans (dif_pos hPB)
    rw [eq]
    exact mem_adjoining _ _
  have hxE := hRB (le_iSup F ξ hx)
  exact hnx ((congrArg Subtype.val hξ).symm ▸ hxE)

open Polynomial
open scoped Polynomial

/-- A polynomial quotient which is nonconstant as a function wherever defined. -/
structure RationalPair where
  num : ℝ[X]
  den : ℝ[X]
  den_ne : den ≠ 0
  nonconstant : ∀ c : ℝ, num ≠ Polynomial.C c * den

def RationalPair.eval (f : RationalPair) (x : ℝ) : ℝ := f.num.eval x / f.den.eval x

/-- The precise dimension lower bound needed to complete the geometric step. -/
def CommonPreimageLarge (D : Set ℝ) (a : ℝ≥0∞) : Prop :=
  ∀ f : ℕ → RationalPair, a ≤ dimH {x : ℝ | ∀ n, (f n).eval x ∈ D}

theorem quotient_representation (F : Subfield ℝ) (x y : ℝ) (hy : y ∈ adjoining F x) :
    ∃ p q : F[X], y = (p.map F.subtype).eval x / (q.map F.subtype).eval x := by
  have hrange : range (algebraMap F ℝ) = (F : Set ℝ) := by
    ext z
    constructor
    · rintro ⟨u, rfl⟩
      exact u.2
    · intro h
      exact ⟨⟨z, h⟩, rfl⟩
  have he : (IntermediateField.adjoin F ({x} : Set ℝ)).toSubfield = adjoining F x := by
    rw [IntermediateField.adjoin_toSubfield, hrange, adjoining]
    congr 1
    ext z
    simp
  have hmem : y ∈ IntermediateField.adjoin F ({x} : Set ℝ) :=
    show y ∈ (IntermediateField.adjoin F ({x} : Set ℝ)).toSubfield from he.symm ▸ hy
  obtain ⟨p, q, h⟩ := (IntermediateField.mem_adjoin_simple_iff F y).mp hmem
  exact ⟨p, q, by simpa only [Polynomial.aeval_def, Polynomial.eval_map, Subfield.algebraMap_ofSubfield] using h⟩

private abbrev ValidPair (F : Subfield ℝ) :=
  {p : F[X] × F[X] // p.2 ≠ 0 ∧
    ∀ c : ℝ, p.1.map F.subtype ≠ Polynomial.C c * p.2.map F.subtype}

private def realPair {F : Subfield ℝ} (p : ValidPair F) : RationalPair :=
  ⟨p.val.1.map F.subtype, p.val.2.map F.subtype,
    fun h => p.2.1 (Polynomial.map_injective F.subtype Subtype.val_injective (by simpa using h)),
    p.2.2⟩

private theorem valid_nonempty (F : Subfield ℝ) : Nonempty (ValidPair F) := by
  refine ⟨⟨(Polynomial.X, 1), one_ne_zero, fun c h => ?_⟩⟩
  have hc := congrArg (fun p : ℝ[X] => p.coeff 1) h
  simp at hc

private theorem ratio_mem_of_proportional (F : Subfield ℝ) (p q : F[X]) (x : ℝ)
    (hq : q ≠ 0) {c : ℝ} (hp : p.map F.subtype = Polynomial.C c * q.map F.subtype) :
    (p.map F.subtype).eval x / (q.map F.subtype).eval x ∈ F := by
  obtain ⟨i, hi⟩ : ∃ i : ℕ, q.coeff i ≠ 0 := by
    by_contra! h
    exact hq (Polynomial.ext (fun i => by simpa using h i))
  have hc := congrArg (fun r : ℝ[X] => r.coeff i) hp
  simp only [Polynomial.coeff_map, Polynomial.coeff_C_mul] at hc
  have hqi : F.subtype (q.coeff i) ≠ 0 := fun h => hi (F.subtype.injective (h.trans F.subtype.map_zero.symm))
  have hcF : c ∈ F := by
    have he : F.subtype (p.coeff i) / F.subtype (q.coeff i) = c := (div_eq_iff hqi).mpr hc
    rw [← he]
    exact F.div_mem (p.coeff i).2 (q.coeff i).2
  rw [hp, Polynomial.eval_mul, Polynomial.eval_C]
  by_cases he : (q.map F.subtype).eval x = 0
  · simp [he]
  · rwa [mul_div_cancel_right₀ _ he]

/-- A dimension lower bound on common preimages turns into the single-extension hypothesis. -/
theorem extension_of_commonPreimageLarge {D : Set ℝ} {a : ℝ≥0∞}
    (hl : CommonPreimageLarge D a) : Extension D a := by
  classical
  intro F hF hFD E hE
  let : Countable F := hF.to_subtype
  let : Countable F[X] := Cardinal.mk_le_aleph0_iff.mp
    (Polynomial.cardinalMk_le_max.trans (max_le hF.le_aleph0 le_rfl))
  let : Nonempty (ValidPair F) := valid_nonempty F
  obtain ⟨f, hf⟩ := exists_surjective_nat (ValidPair F)
  let K := {x : ℝ | ∀ n, (realPair (f n)).eval x ∈ D}
  have hK : a ≤ dimH K := hl (fun n => realPair (f n))
  have hnot : ¬ K ⊆ E := fun hh => hE.not_ge (hK.trans (dimH_mono hh))
  obtain ⟨x, hx, hxE⟩ := not_subset.mp hnot
  refine ⟨x, hxE, fun y hy => ?_⟩
  obtain ⟨p, q, rfl⟩ := quotient_representation F x y hy
  by_cases hq : q = 0
  · simpa [hq] using hFD F.zero_mem
  by_cases hc : ∃ c : ℝ, p.map F.subtype = Polynomial.C c * q.map F.subtype
  · obtain ⟨c, hc⟩ := hc
    exact hFD (ratio_mem_of_proportional F p q x hq hc)
  · let pq : ValidPair F := ⟨(p,q), hq, fun c he => hc ⟨c,he⟩⟩
    obtain ⟨n, hn⟩ := hf pq
    have h := hx n
    rwa [hn] at h

/-- The numerator of the derivative of a rational function. -/
def RationalPair.derivNum (f : RationalPair) : ℝ[X] :=
  f.num.derivative * f.den - f.num * f.den.derivative

def RationalPair.derivativeValue (f : RationalPair) (x : ℝ) : ℝ :=
  f.derivNum.eval x / (f.den.eval x)^2

theorem RationalPair.hasDerivAt_of_den_ne_zero (f : RationalPair) {x : ℝ}
    (hx : f.den.eval x ≠ 0) : HasDerivAt f.eval (f.derivativeValue x) x := by
  change HasDerivAt ((fun t => f.num.eval t) / (fun t => f.den.eval t))
    (f.derivativeValue x) x
  simpa only [RationalPair.derivativeValue, RationalPair.derivNum, Polynomial.eval_sub,
    Polynomial.eval_mul] using (f.num.hasDerivAt x).div (f.den.hasDerivAt x) hx

theorem RationalPair.derivNum_ne_zero (f : RationalPair) : f.derivNum ≠ 0 := by
  intro hzero
  have hex : ∃ x : ℝ, f.den.eval x ≠ 0 := by
    by_contra! h
    exact Set.infinite_univ.not_finite ((Polynomial.finite_setOfPred_isRoot f.den_ne).subset (fun x _ => h x))
  obtain ⟨x, hx⟩ := hex
  have hopen : IsOpen {y : ℝ | f.den.eval y ≠ 0} :=
    isOpen_ne_fun f.den.continuous continuous_const
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hopen x hx
  have hs (y : ℝ) (hy : y ∈ Metric.ball x r) : f.den.eval y ≠ 0 := hsub hy
  have hdiff : DifferentiableOn ℝ f.eval (Metric.ball x r) :=
    fun y hy => (f.hasDerivAt_of_den_ne_zero (hs y hy)).differentiableAt.differentiableWithinAt
  have hdz : (Metric.ball x r).EqOn (deriv f.eval) 0 := by
    intro y hy
    rw [(f.hasDerivAt_of_den_ne_zero (hs y hy)).deriv]
    simp [RationalPair.derivativeValue, hzero]
  obtain ⟨c, hc⟩ := Metric.isOpen_ball.exists_is_const_of_deriv_eq_zero
    (convex_ball x r).isPreconnected hdiff hdz
  have hf := Polynomial.finite_setOfPred_isRoot (sub_ne_zero.mpr (f.nonconstant c))
  have hfinite : (Metric.ball x r).Finite := hf.subset (fun y hy => by
    have h := (div_eq_iff (hs y hy)).mp (hc y hy)
    simpa only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C, sub_eq_zero, Set.mem_ofPred_eq] using h)
  rw [Real.ball_eq_Ioo] at hfinite
  exact (Set.Ioo_infinite (by linarith)).not_finite hfinite

/-- The finitely many potential poles and stationary points. -/
def RationalPair.exceptional (f : RationalPair) : Finset ℝ :=
  (f.den * f.derivNum).roots.toFinset

theorem RationalPair.regular (f : RationalPair) {x : ℝ} (hx : x ∉ f.exceptional) :
    f.den.eval x ≠ 0 ∧ f.derivNum.eval x ≠ 0 := by
  have hprod : f.den * f.derivNum ≠ 0 := mul_ne_zero f.den_ne f.derivNum_ne_zero
  have he : f.den.eval x * f.derivNum.eval x ≠ 0 := by
    simpa only [RationalPair.exceptional, Multiset.mem_toFinset, Polynomial.mem_roots hprod,
      Polynomial.IsRoot, Polynomial.eval_mul] using hx
  exact ⟨fun h => he (by simp [h]), fun h => he (by simp [h])⟩

/-- Bounds in both directions for a rational map on an interval avoiding its finite bad set. -/
theorem RationalPair.interval_comparison (f : RationalPair) {a b : ℝ} (hab : a ≤ b)
    (hgood : ∀ x ∈ Icc a b, x ∉ f.exceptional) :
    ∃ L : ℝ, 1 ≤ L ∧ ContinuousOn f.eval (Icc a b) ∧
      ∀ x ∈ Icc a b, ∀ y ∈ Icc a b,
        |f.eval y - f.eval x| ≤ L * |y-x| ∧ |y-x| ≤ L * |f.eval y - f.eval x| := by
  have hd (x : ℝ) (hx : x ∈ Icc a b) := (f.regular (hgood x hx)).1
  have hderiv (x : ℝ) (hx : x ∈ Icc a b) := f.hasDerivAt_of_den_ne_zero (hd x hx)
  have hf : ContinuousOn f.eval (Icc a b) :=
    fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
  have hh : ContinuousOn (fun x => |f.derivativeValue x|) (Icc a b) :=
    (f.derivNum.continuous.continuousOn.div (f.den.continuous.pow 2).continuousOn
      (fun x hx => pow_ne_zero _ (hd x hx))).abs
  obtain ⟨u, hu, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab) hh
  obtain ⟨v, hv, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab) hh
  let δ := |f.derivativeValue u|
  have hdpos : 0 < δ := abs_pos.mpr
    (div_ne_zero (f.regular (hgood u hu)).2 (pow_ne_zero _ (hd u hu)))
  let L := max 1 (max |f.derivativeValue v| δ⁻¹)
  have hone : 1 ≤ L := le_max_left _ _
  have hupper : |f.derivativeValue v| ≤ L := (le_max_left _ _).trans (le_max_right _ _)
  have hlower : δ⁻¹ ≤ L := (le_max_right _ _).trans (le_max_right _ _)
  have hinc (x y : ℝ) (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hlt : x < y) :
      |f.eval y-f.eval x| ≤ L * |y-x| ∧ |y-x| ≤ L * |f.eval y-f.eval x| := by
    have hsub : Icc x y ⊆ Icc a b := Icc_subset_Icc hx.1 hy.2
    obtain ⟨t, ht, h⟩ := exists_hasDerivAt_eq_slope f.eval f.derivativeValue hlt
      (hf.mono hsub) (fun z hz => hderiv z (hsub (Ioo_subset_Icc_self hz)))
    have hmem := hsub (Ioo_subset_Icc_self ht)
    have hh1 : |f.derivativeValue t| ≤ L := (hmax hmem).trans hupper
    have hh2 : δ ≤ |f.derivativeValue t| := hmin hmem
    have hp : 0 < y-x := sub_pos.mpr hlt
    rw [h, abs_div, abs_of_pos hp] at hh1 hh2
    rw [abs_of_pos hp]
    constructor
    · exact (div_le_iff₀ hp).mp hh1
    · have hm : δ * (y-x) ≤ |f.eval y-f.eval x| := (le_div_iff₀ hp).mp hh2
      have hi' : 1 ≤ L*δ := (inv_le_iff_one_le_mul₀ hdpos).mp hlower
      calc
        _ ≤ (L*δ) * (y-x) := by simpa using mul_le_mul_of_nonneg_right hi' hp.le
        _ = L * (δ * (y-x)) := mul_assoc _ _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left hm (zero_le_one.trans hone)
  refine ⟨L, hone, hf, fun x hx y hy => ?_⟩
  rcases lt_trichotomy x y with h | rfl | h
  · exact hinc x y hx hy h
  · simp
  · simpa only [abs_sub_comm (f.eval x) (f.eval y), abs_sub_comm x y] using hinc y x hy hx h

/-- By repeatedly taking a quarter interval, remove any finite bad set while retaining a
definite fraction of the original interval length. -/
theorem trim_interval (B : Finset ℝ) {a b : ℝ} (hab : a < b) :
    ∃ u v : ℝ, a ≤ u ∧ v ≤ b ∧ u < v ∧
      (b-a)/(4:ℝ)^B.card ≤ v-u ∧ (∀ z ∈ Icc u v, z ∉ B) := by
  classical
  induction B using Finset.induction_on generalizing a b with
  | empty => exact ⟨a,b,le_rfl,le_rfl,hab,by simp,by simp⟩
  | @insert x S hx ih =>
    let l := if x ≤ (a+b)/2 then (a+3*b)/4 else a
    let r := if x ≤ (a+b)/2 then b else (3*a+b)/4
    have hl : a ≤ l := by dsimp [l]; split_ifs <;> linarith
    have hr : r ≤ b := by dsimp [r]; split_ifs <;> linarith
    have hlr : l < r := by dsimp [l,r]; split_ifs <;> linarith
    have hlen : r-l = (b-a)/4 := by dsimp [l,r]; split_ifs <;> linarith
    have hn : x ∉ Icc l r := by
      by_cases h : x ≤ (a+b)/2
      · have hxlt : x < l := by dsimp [l]; rw [if_pos h]; linarith
        exact fun he => hxlt.not_ge he.1
      · have hxgt : r < x := by dsimp [r]; rw [if_neg h]; linarith
        exact fun he => hxgt.not_ge he.2
    obtain ⟨u,v,hu,hv,huv,hΔ,hS⟩ := ih hlr
    refine ⟨u,v,hl.trans hu,hv.trans hr,huv,?_ ,?_⟩
    · rw [Finset.card_insert_of_notMem hx, pow_succ]
      rw [hlen] at hΔ
      simpa only [div_div, mul_comm ((4:ℝ)^S.card)] using hΔ
    · intro z hz hzB
      rcases Finset.mem_insert.mp hzB with rfl | h
      · exact hn ⟨hu.trans hz.1, hz.2.trans hv⟩
      · exact hS z hz h

end MauldinRecursion


open Set MeasureTheory Metric Filter
open scoped ENNReal NNReal Topology

namespace MauldinDyadic

def grid (n : ℕ) (k : ℤ) : ℝ := (k : ℝ) / (2 : ℝ)^n

/-- The reals lying in a dyadic grid window at arbitrarily fine scales. -/
def core (r : ℝ≥0∞) : Set ℝ :=
  {x | ∀ N : ℕ, ∃ n ≥ N, ∃ k : ℤ, x ∈ closedEBall (grid n k) (r^n)}

def parameter (a : ℝ≥0) : ℝ≥0∞ := (2 : ℝ≥0∞) ^ (-(a : ℝ)⁻¹)

def envelope (a : ℝ≥0) : Set ℝ :=
  range ((↑) : ℚ → ℝ) ∪ core (parameter a)

theorem bottom_subset (a : ℝ≥0) : (↑(⊥ : Subfield ℝ) : Set ℝ) ⊆ envelope a := by
  intro x hx
  apply Or.inl
  have he : (⊥ : Subfield ℝ) ≤ (Rat.castHom ℝ).fieldRange := bot_le
  simpa using he hx

private def cap (m n : ℕ) : ℕ := (m+1) * 2^n

private abbrev tiles (m n : ℕ) := Fin (2 * cap m n + 1)

private def tile (r : ℝ≥0∞) (m n : ℕ) (i : tiles m n) : Set ℝ :=
  closedEBall (grid n ((i.val : ℤ) - (cap m n : ℤ))) (r^n)

private theorem exists_tile {r : ℝ≥0∞} (hr : r ≤ 1) {m n : ℕ} {x : ℝ}
    (hx : x ∈ Icc (-(m : ℝ)) m) {k : ℤ} (hk : x ∈ closedEBall (grid n k) (r^n)) :
    ∃ i : tiles m n, x ∈ tile r m n i := by
  have he : edist x (grid n k) ≤ 1 := hk.trans (pow_le_one₀ (zero_le (a := r)) hr)
  rw [edist_dist, Real.dist_eq, ← ENNReal.ofReal_one] at he
  have habs : |x - grid n k| ≤ 1 := (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp he
  have hlo : -(m : ℝ)-1 ≤ grid n k := by have := (abs_le.mp habs).2; linarith [hx.1]
  have hhi : grid n k ≤ (m : ℝ)+1 := by have := (abs_le.mp habs).1; linarith [hx.2]
  have hp : 0 < (2 : ℝ)^n := by positivity
  unfold grid at hlo hhi
  have hL : -((cap m n : ℕ) : ℤ) ≤ k := by
    exact_mod_cast (show -((cap m n : ℕ) : ℝ) ≤ (k : ℝ) by
      have h := (le_div_iff₀ hp).mp hlo
      push_cast [cap]
      convert h using 1 <;> first | rfl | ring)
  have hU : k ≤ (cap m n : ℤ) := by
    exact_mod_cast (show (k : ℝ) ≤ (cap m n : ℝ) by
      exact (div_le_iff₀ hp).mp hhi |>.trans (by simp [cap]))
  let i : tiles m n := ⟨(k+(cap m n : ℤ)).toNat, by omega⟩
  have hi : (i.val : ℤ) - (cap m n : ℤ) = k := by dsimp [i]; omega
  exact ⟨i, by simpa only [tile, hi] using hk⟩

private theorem tile_ediam (r : ℝ≥0∞) (m n : ℕ) (i : tiles m n) :
    ediam (tile r m n i) ≤ 2*r^n := ediam_closedEBall_le

private theorem tile_sum (r : ℝ≥0∞) (m n : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    (∑ i : tiles m n, ediam (tile r m n i)^s) ≤
      ((2*(m+1)+1 : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)^s * (2*r^s)^n := by
  classical
  calc
    _ ≤ ∑ _i : tiles m n, (2*r^n)^s :=
      Finset.sum_le_sum (fun i _ => ENNReal.rpow_le_rpow (tile_ediam r m n i) hs)
    _ = ((2*cap m n+1 : ℕ) : ℝ≥0∞) * (2*r^n)^s := by
      simp [tiles, nsmul_eq_mul]
    _ ≤ (((2*(m+1)+1)*2^n : ℕ) : ℝ≥0∞) * (2*r^n)^s := by
      have hp : 1 ≤ (2 : ℕ)^n := Nat.one_le_pow _ _ (by decide)
      have hcard : 2*cap m n+1 ≤ (2*(m+1)+1)*2^n := by
        calc
          _ ≤ 2 * ((m+1)*2^n) + 2^n := Nat.add_le_add_left hp _
          _ = _ := by ring
      exact mul_le_mul_left (by exact_mod_cast hcard) _
    _ = ((2*(m+1)+1 : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)^s * (2*r^s)^n := by
      rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, ENNReal.mul_rpow_of_nonneg _ _ hs,
        ← ENNReal.rpow_natCast_mul, mul_comm (n : ℝ) s, ENNReal.rpow_mul_natCast, mul_pow]
      simp only [mul_comm, mul_assoc, mul_left_comm]

private theorem localized_null {r : ℝ≥0∞} (hr : r < 1) {s : ℝ}
    (hs : 0 ≤ s) (hθ : 2 * r^s < 1) (m : ℕ) :
    μH[s] (Icc (-(m : ℝ)) m ∩ core r) = 0 := by
  classical
  let t (N : ℕ) (p : Σ i : ℕ, tiles m (N+i)) := tile r m (N+p.1) p.2
  have ht (N : ℕ) (p : Σ i : ℕ, tiles m (N+i)) : ediam (t N p) ≤ 2 * r^N :=
    (tile_ediam _ _ _ _).trans (by
      exact mul_le_mul_right (pow_le_pow_right_of_le_one' hr.le (Nat.le_add_right _ _)) _)
  have hcov (N : ℕ) : Icc (-(m : ℝ)) m ∩ core r ⊆ ⋃ p, t N p := by
    rintro x ⟨hx, hD⟩
    obtain ⟨n, hn, k, hk⟩ := hD N
    obtain ⟨i, hi⟩ := exists_tile hr.le hx hk
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
    exact mem_iUnion.mpr ⟨⟨j,i⟩,hi⟩
  have hlim : Tendsto (fun N : ℕ => 2 * r^N) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul (a := (2 : ℝ≥0∞))
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hr) (Or.inr (by norm_num))
  let θ : ℝ≥0∞ := 2*r^s
  let C : ℝ≥0∞ := ((2*(m+1)+1 : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)^s
  let B : ℝ≥0∞ := C * (1-θ)⁻¹
  have hBn : B ≠ ⊤ := ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.rpow_ne_top_of_nonneg hs (by norm_num)))
    (ENNReal.inv_ne_top.mpr (tsub_pos_of_lt hθ).ne')
  have hsum (N : ℕ) : (∑' p, ediam (t N p)^s) ≤ B * θ^N := by
    rw [ENNReal.tsum_sigma']
    calc
      _ ≤ ∑' i : ℕ, C * θ^(N+i) := by
        refine ENNReal.tsum_le_tsum (fun i => ?_)
        rw [tsum_fintype]
        exact tile_sum _ _ _ _ hs
      _ = _ := by
        simp only [pow_add, ← mul_assoc, ENNReal.tsum_mul_left, ENNReal.tsum_geometric, B]
        ac_rfl
  have hzero : Tendsto (fun N : ℕ => B*θ^N) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul (a := B)
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hθ) (Or.inr hBn)
  have hm := Measure.hausdorffMeasure_le_liminf_tsum s _ _ hlim t
    (Eventually.of_forall ht) (Eventually.of_forall hcov)
  exact le_antisymm (hm.trans ((liminf_le_liminf (Eventually.of_forall hsum)).trans_eq
    hzero.liminf_eq)) zero_le

theorem core_null {r : ℝ≥0∞} (hr : r < 1) {s : ℝ}
    (hs : 0 ≤ s) (hθ : 2 * r^s < 1) : μH[s] (core r) = 0 := by
  have heq : core r = ⋃ m : ℕ, Icc (-(m : ℝ)) m ∩ core r := by
    ext x
    constructor
    · intro hx
      obtain ⟨m, hm⟩ := exists_nat_ge |x|
      exact mem_iUnion.mpr ⟨m, ⟨(abs_le.mp hm).1, (abs_le.mp hm).2⟩, hx⟩
    · intro hx
      obtain ⟨m, hm⟩ := mem_iUnion.mp hx
      exact hm.2
  rw [heq]
  exact measure_iUnion_null (fun m => localized_null hr hs hθ m)

theorem parameter_lt_one {a : ℝ≥0} (ha : 0 < a) : parameter a < 1 := by
  unfold parameter
  calc
    _ < (2 : ℝ≥0∞) ^ (0 : ℝ) :=
      ENNReal.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)
        (neg_neg_of_pos (inv_pos.mpr (by exact_mod_cast ha)))
    _ = 1 := ENNReal.rpow_zero

theorem dimH_envelope_le {a : ℝ≥0} (ha : 0 < a) : dimH (envelope a) ≤ (a : ℝ≥0∞) := by
  unfold envelope
  rw [dimH_union, (countable_range ((↑) : ℚ → ℝ)).dimH_zero, zero_max]
  apply dimH_le
  intro s hs
  by_contra hle
  have has : (a : ℝ) < (s : ℝ) := by exact_mod_cast (lt_of_not_ge hle)
  have hpos : 0 < (a : ℝ) := by exact_mod_cast ha
  have he : 1 + (-(a : ℝ)⁻¹) * (s : ℝ) < 0 := by
    have h : 1 < (s : ℝ) / (a : ℝ) := (lt_div_iff₀ hpos).mpr (by simpa using has)
    rw [div_eq_mul_inv] at h
    nlinarith
  have hθ : 2 * (parameter a)^ (s:ℝ) < 1 := by
    calc
      _ = (2 : ℝ≥0∞) ^ (1 + (-(a : ℝ)⁻¹)*(s : ℝ)) := by
        rw [parameter, ← ENNReal.rpow_mul, ENNReal.rpow_add _ _ (by norm_num) (by norm_num),
          ENNReal.rpow_one]
      _ < (2 : ℝ≥0∞) ^ (0 : ℝ) :=
        ENNReal.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num) he
      _ = 1 := ENNReal.rpow_zero
  rw [core_null (parameter_lt_one ha) s.coe_nonneg hθ] at hs
  exact ENNReal.zero_ne_top hs

end MauldinDyadic



open Set MeasureTheory Metric
open scoped ENNReal NNReal Topology

namespace MauldinCantor

def size (arity : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | n+1 => size arity n * arity n

structure IntervalTree where
  arity : ℕ → ℕ
  arity_pos : ∀ n, 0 < arity n
  lo : ℕ → ℕ → ℝ
  hi : ℕ → ℕ → ℝ
  valid : ∀ n i, i < size arity n → lo n i ≤ hi n i
  nested : ∀ n i, i < size arity (n+1) →
    Icc (lo (n+1) i) (hi (n+1) i) ⊆ Icc (lo n (i / arity n)) (hi n (i / arity n))

namespace IntervalTree

variable (T : IntervalTree)

theorem size_pos (n : ℕ) : 0 < size T.arity n := by
  induction n with
  | zero => exact Nat.zero_lt_one
  | succ n ih => exact Nat.mul_pos ih (T.arity_pos n)

def piece (n : ℕ) (i : ℕ) : Set ℝ := Icc (T.lo n i) (T.hi n i)

def limitSet : Set ℝ := ⋂ n : ℕ, ⋃ i : Fin (size T.arity n), T.piece n i.val

theorem isClosed_limitSet : IsClosed T.limitSet :=
  isClosed_iInter (fun _ => isClosed_iUnion_of_finite (fun _ => isClosed_Icc))

private def index (n : ℕ) (x : ℝ) : ℕ := ⌊(size T.arity n : ℝ)*x⌋₊

private theorem index_lt (n : ℕ) {x : ℝ} (hx : x ∈ Ico (0:ℝ) 1) : T.index n x < size T.arity n := by
  rw [index, Nat.floor_lt (mul_nonneg (Nat.cast_nonneg _) hx.1)]
  have hp : (0 : ℝ) < size T.arity n := by exact_mod_cast T.size_pos n
  simpa using mul_lt_mul_of_pos_left hx.2 hp

private theorem index_parent (n : ℕ) (x : ℝ) : T.index (n+1) x / T.arity n = T.index n x := by
  simp only [index, size, Nat.cast_mul]
  conv_lhs => rw [mul_right_comm]
  apply Nat.mul_cast_floor_div_cancel (T.arity_pos n).ne'

private def sample (n : ℕ) (x : ℝ) : ℝ := T.lo n (T.index n x)

private theorem sample_mem (n : ℕ) {x : ℝ} (hx : x ∈ Ico (0:ℝ) 1) :
    T.sample n x ∈ T.piece n (T.index n x) :=
  ⟨le_rfl, T.valid _ _ (T.index_lt n hx)⟩

private theorem pieces_nested {x : ℝ} (hx : x ∈ Ico (0:ℝ) 1) (n : ℕ) :
    T.piece (n+1) (T.index (n+1) x) ⊆ T.piece n (T.index n x) := by
  simpa only [piece, index_parent] using T.nested n _ (T.index_lt (n+1) hx)

private theorem sample_mono {x : ℝ} (hx : x ∈ Ico (0:ℝ) 1) :
    Monotone (fun n => T.sample n x) :=
  monotone_nat_of_le_succ (fun n => (T.pieces_nested hx n (T.sample_mem (n+1) hx)).1)

private theorem sample_le_hi {x : ℝ} (hx : x ∈ Ico (0:ℝ) 1) (n k : ℕ) :
    T.sample k x ≤ T.hi n (T.index n x) := by
  by_cases h : k ≤ n
  · exact (T.sample_mono hx h).trans (T.sample_mem n hx).2
  · have h' : n ≤ k := by omega
    have hand : Antitone (fun i => T.piece i (T.index i x)) :=
      antitone_nat_of_succ_le (fun n => T.pieces_nested hx n)
    exact (hand h' (T.sample_mem k hx)).2

def limit (x : ℝ) : ℝ := ⨆ n : ℕ, T.sample n x

private theorem limit_mem_piece {x : ℝ} (hx : x ∈ Ico (0:ℝ) 1) (n : ℕ) :
    T.limit x ∈ T.piece n (T.index n x) := by
  change T.sample n x ≤ (⨆ k, T.sample k x) ∧ (⨆ k, T.sample k x) ≤ T.hi n (T.index n x)
  have hbdd : BddAbove (range (fun k => T.sample k x)) := by
    refine ⟨T.hi n (T.index n x), ?_⟩
    rintro z ⟨k,rfl⟩
    exact T.sample_le_hi hx n k
  exact ⟨le_ciSup hbdd n, ciSup_le (T.sample_le_hi hx n)⟩

private theorem limit_mem {x : ℝ} (hx : x ∈ Ico (0:ℝ) 1) : T.limit x ∈ T.limitSet :=
  mem_iInter.mpr (fun n => mem_iUnion.mpr ⟨⟨T.index n x, T.index_lt n hx⟩, T.limit_mem_piece hx n⟩)

private theorem measurable_limit : Measurable T.limit := by
  apply Measurable.iSup
  intro n
  apply Measurable.comp (g := T.lo n) (f := T.index n) (measurable_of_countable _)
  unfold index
  fun_prop

/-- Lebesgue mass on [0,1) pushed to the limit set by the nested interval sampler. -/
def mass : Measure ℝ := Measure.map T.limit (volume.restrict (Ico 0 1))

theorem mass_limitSet : T.mass T.limitSet = 1 := by
  rw [mass, Measure.map_apply T.measurable_limit T.isClosed_limitSet.measurableSet,
    Measure.restrict_apply (T.measurable_limit T.isClosed_limitSet.measurableSet)]
  have he : T.limit ⁻¹' T.limitSet ∩ Ico 0 1 = Ico 0 1 :=
    inter_eq_right.mpr (fun x hx => T.limit_mem hx)
  rw [he]
  simp [Real.volume_Ico]

private def sampleCell (n : ℕ) (i : ℕ) : Set ℝ :=
  Ico ((i : ℝ) / (size T.arity n : ℝ)) (((i : ℝ) + 1) / (size T.arity n : ℝ))

private theorem mem_sampleCell {n : ℕ} {x : ℝ} (hx : x ∈ Ico (0:ℝ) 1) :
    x ∈ T.sampleCell n (T.index n x) := by
  have hp : (0 : ℝ) < size T.arity n := by exact_mod_cast T.size_pos n
  have hn : 0 ≤ (size T.arity n : ℝ) * x := mul_nonneg hp.le hx.1
  constructor
  · exact (div_le_iff₀ hp).mpr (by rw [mul_comm]; exact Nat.floor_le hn)
  · exact (lt_div_iff₀ hp).mpr (by rw [mul_comm]; exact Nat.lt_floor_add_one _)

private theorem volume_sampleCell (n i : ℕ) :
    volume (T.sampleCell n i) = (size T.arity n : ℝ≥0∞)⁻¹ := by
  have hp : (0 : ℝ) < size T.arity n := by exact_mod_cast T.size_pos n
  rw [sampleCell, Real.volume_Ico, ← sub_div]
  simp only [add_sub_cancel_left]
  rw [ENNReal.ofReal_div_of_pos hp]
  simp [one_div]

/-- The mass of a measurable set is at most the total mass of its intersecting intervals. -/
theorem mass_le_intersections (n : ℕ) {s : Set ℝ} (hs : MeasurableSet s) (J : Finset ℕ)
    (hJ : ∀ i < size T.arity n, (s ∩ T.piece n i).Nonempty → i ∈ J) :
    T.mass s ≤ (J.card : ℝ≥0∞) * (size T.arity n : ℝ≥0∞)⁻¹ := by
  rw [mass, Measure.map_apply T.measurable_limit hs, Measure.restrict_apply (T.measurable_limit hs)]
  have hsub : T.limit ⁻¹' s ∩ Ico (0:ℝ) 1 ⊆ ⋃ i : J, T.sampleCell n i := by
    rintro x ⟨hx, hI⟩
    have hi : T.index n x ∈ J := hJ _ (T.index_lt n hI) ⟨T.limit x, hx, T.limit_mem_piece hI n⟩
    exact mem_iUnion.mpr ⟨⟨T.index n x, hi⟩, T.mem_sampleCell hI⟩
  refine (measure_mono hsub).trans ?_
  refine (measure_iUnion_le (fun i : J => T.sampleCell n i)).trans_eq ?_
  simp [T.volume_sampleCell, tsum_fintype, nsmul_eq_mul]

private theorem hit_card_le {ε : ℝ} (hε : 0 < ε) (n : ℕ)
    (gap : ∀ i j, i < j → j < size T.arity n → T.hi n i + ε * ((j:ℝ)-i) ≤ T.lo n j)
    {s : Set ℝ} (hs : ediam s ≠ ⊤) (J : Finset ℕ)
    (hJ : ∀ i ∈ J, i < size T.arity n ∧ (s ∩ T.piece n i).Nonempty) :
    (J.card : ℝ) ≤ 1 + (ediam s).toReal / ε := by
  classical
  by_cases he : J.Nonempty
  · let i := J.min' he
    let j := J.max' he
    have hi : i ∈ J := J.min'_mem he
    have hj : j ∈ J := J.max'_mem he
    have hij : i ≤ j := J.le_max' _ hi
    have hcard : J.card ≤ j + 1 - i := by
      calc
        _ ≤ (Finset.Icc i j).card := Finset.card_le_card (fun t ht =>
          Finset.mem_Icc.mpr ⟨J.min'_le _ ht, J.le_max' _ ht⟩)
        _ = _ := Nat.card_Icc _ _
    have hcast : (J.card : ℝ) ≤ (j : ℝ) + 1 - (i : ℝ) := by
      have h := (Nat.cast_le (α := ℝ)).mpr hcard
      rwa [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one] at h
    have hspan : ε * ((j : ℝ) - (i : ℝ)) ≤ (ediam s).toReal := by
      rcases lt_or_eq_of_le hij with hlt | heq
      · obtain ⟨x, hx, hxi⟩ := (hJ i hi).2
        obtain ⟨y, hy, hyj⟩ := (hJ j hj).2
        have hΔ : ε * ((j : ℝ) - (i : ℝ)) ≤ y - x := by
          have hg := gap i j hlt (hJ j hj).1
          have hxi' : x ≤ T.hi n i := hxi.2
          have hyj' : T.lo n j ≤ y := hyj.1
          linarith only [hg, hxi', hyj']
        have hd : dist y x ≤ (ediam s).toReal := by
          have h := ENNReal.toReal_mono hs (edist_le_ediam_of_mem hy hx)
          simpa [edist_dist, ENNReal.toReal_ofReal dist_nonneg] using h
        exact hΔ.trans ((le_abs_self _).trans (by simpa [Real.dist_eq] using hd))
      · rw [heq, sub_self, mul_zero]
        exact ENNReal.toReal_nonneg
    have hdiff : (j : ℝ) - (i : ℝ) ≤ (ediam s).toReal / ε :=
      (le_div_iff₀ hε).mpr (by simpa only [mul_comm] using hspan)
    linarith
  · have hn : J = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    rw [hn, Finset.card_empty, Nat.cast_zero]
    positivity

private theorem mass_le_pack {s : Set ℝ} (hs : MeasurableSet s) (hs' : ediam s ≠ ⊤) (n : ℕ)
    {ε : ℝ} (hε : 0 < ε)
    (gap : ∀ i j, i < j → j < size T.arity n → T.hi n i + ε * ((j:ℝ)-i) ≤ T.lo n j) :
    T.mass s ≤ ENNReal.ofReal ((1 + (ediam s).toReal / ε) / size T.arity n) := by
  classical
  let J := (Finset.range (size T.arity n)).filter (fun i => (s ∩ T.piece n i).Nonempty)
  have hJ : ∀ i ∈ J, i < size T.arity n ∧ (s ∩ T.piece n i).Nonempty := by
    intro i hi
    simpa [J] using (Finset.mem_filter.mp hi)
  have hmass := T.mass_le_intersections n hs J
    (fun i hi h => Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, h⟩)
  have hpos : (0:ℝ) < size T.arity n := by exact_mod_cast T.size_pos n
  have hcard := T.hit_card_le hε n gap hs' J hJ
  refine hmass.trans ?_
  rw [ENNReal.ofReal_div_of_pos hpos, ENNReal.ofReal_natCast, div_eq_mul_inv]
  exact mul_le_mul_left (by simpa using ENNReal.ofReal_le_ofReal hcard) _

private theorem mass_le_single {s : Set ℝ} (hs : MeasurableSet s) (n : ℕ)
    {ε : ℝ} (hε : 0 < ε) (hlt : ediam s < ENNReal.ofReal ε)
    (gap : ∀ i j, i < j → j < size T.arity n → T.hi n i + ε * ((j:ℝ)-i) ≤ T.lo n j) :
    T.mass s ≤ ENNReal.ofReal (1 / size T.arity n) := by
  classical
  let J := (Finset.range (size T.arity n)).filter (fun i => (s ∩ T.piece n i).Nonempty)
  have hJ : ∀ i ∈ J, i < size T.arity n ∧ (s ∩ T.piece n i).Nonempty := by
    intro i hi
    simpa [J] using (Finset.mem_filter.mp hi)
  have hmass := T.mass_le_intersections n hs J
    (fun i hi h => Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, h⟩)
  have hfin : ediam s ≠ ⊤ := hlt.ne_top
  have hlt' : (ediam s).toReal < ε := by
    have he : (ediam s).toReal < (ENNReal.ofReal ε).toReal :=
      (ENNReal.toReal_lt_toReal hfin ENNReal.ofReal_ne_top).mpr hlt
    simpa [ENNReal.toReal_ofReal hε.le] using he
  have hcard := T.hit_card_le hε n gap hfin J hJ
  have hJcard : J.card ≤ 1 := by
    have hJ' : (J.card : ℝ) < 2 :=
      hcard.trans_lt (by
        have h : (ediam s).toReal / ε < 1 := (div_lt_iff₀ hε).mpr (by simpa using hlt')
        linarith)
    exact Nat.lt_succ_iff.mp (by exact_mod_cast hJ')
  have hpos : (0:ℝ) < size T.arity n := by exact_mod_cast T.size_pos n
  refine hmass.trans ?_
  rw [ENNReal.ofReal_div_of_pos hpos, ENNReal.ofReal_natCast, ENNReal.ofReal_one, one_div]
  simpa using mul_le_mul_left (show (J.card : ℝ≥0∞) ≤ 1 by exact_mod_cast hJcard)
    ((size T.arity n : ℝ≥0∞)⁻¹)

private theorem two_scale_estimate {d r e M m : ℝ} (hd : 0 < d) (hd1 : d ≤ 1)
    (he : 0 < e) (her : e ≤ r) (hM : 0 < M) (hm : 0 < m)
    (budget : 1 ≤ M * (m*e)^d) :
    min (1/M) ((1+r/e)/(M*m)) ≤ 2*r^d := by
  have hr : 0 < r := he.trans_le her
  have hp : 0 < m*e := mul_pos hm he
  have hp' : 0 < (m*e)^d := Real.rpow_pos_of_pos hp _
  by_cases h : r ≤ m*e
  · refine (min_le_right _ _).trans ?_
    have hratio : r/(m*e) ≤ 1 := (div_le_one hp).mpr h
    have hpower : r/(m*e) ≤ (r/(m*e))^d := by
      calc
        _ = (r/(m*e))^(1:ℝ) := (Real.rpow_one _).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge (by positivity) hratio hd1
    have hratio2 : 1 + r/e ≤ 2*r/e := by
      have h' : 1 ≤ r/e := (le_div_iff₀ he).mpr (by simpa using her)
      rw [mul_div_assoc]
      linarith
    calc
      _ ≤ (2*r/e)/(M*m) := div_le_div_of_nonneg_right hratio2 (mul_nonneg hM.le hm.le)
      _ = (2*(r/(m*e)))/M := by field_simp
      _ ≤ (2*(r/(m*e))^d)/M := by gcongr
      _ = (2*r^d)/(M*(m*e)^d) := by rw [Real.div_rpow hr.le hp.le]; field_simp
      _ ≤ 2*r^d := div_le_self (by positivity) budget
  · refine (min_le_left _ _).trans ?_
    have hle : (m*e)^d ≤ r^d := Real.rpow_le_rpow hp.le (le_of_not_ge h) hd.le
    have hbudget : 1 ≤ M*r^d := budget.trans (mul_le_mul_of_nonneg_left hle hM.le)
    have hinv : 1/M ≤ r^d := (div_le_iff₀ hM).mpr (by simpa only [mul_comm] using hbudget)
    exact hinv.trans (by linarith [Real.rpow_nonneg hr.le d])

private theorem size_ge_pow_two (hb : ∀ n, 2 ≤ T.arity n) (n : ℕ) :
    2^n ≤ size T.arity n := by
  induction n with
  | zero => simp [size]
  | succ n ih => exact Nat.mul_le_mul ih (hb n)

private theorem mass_zero_of_ediam_zero {s : Set ℝ} (hs : MeasurableSet s) (h0 : ediam s = 0)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hb : ∀ n, 2 ≤ T.arity n)
    (gap : ∀ n i j, i < j → j < size T.arity n → T.hi n i + ε n * ((j:ℝ)-i) ≤ T.lo n j) :
    T.mass s = 0 := by
  refine ENNReal.eq_zero_of_le_mul_pow (r := (2 : ℝ≥0∞)⁻¹) (ε := 1) (by norm_num) (fun n => ?_)
  have h : ediam s < ENNReal.ofReal (ε n) := by simpa [h0] using hε n
  refine (T.mass_le_single hs n (hε n) h (gap n)).trans ?_
  have hpos : (0:ℝ) < size T.arity n := by exact_mod_cast T.size_pos n
  rw [ENNReal.ofReal_div_of_pos hpos, ENNReal.ofReal_one, ENNReal.ofReal_natCast, ENNReal.coe_one, one_mul,
    ← ENNReal.inv_pow, one_div]
  exact ENNReal.inv_le_inv.mpr (by exact_mod_cast T.size_ge_pow_two hb n)

private theorem mass_ediam_bound {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hlim : Filter.Tendsto ε Filter.atTop (𝓝 0))
    (hb : ∀ n, 2 ≤ T.arity n)
    (gap : ∀ n i j, i < j → j < size T.arity n → T.hi n i + ε n * ((j:ℝ)-i) ≤ T.lo n j)
    (budget : ∀ n ≥ 1, 1 ≤ (size T.arity n : ℝ) * ((T.arity n : ℝ)*ε (n+1))^d)
    {s : Set ℝ} (hs : MeasurableSet s) (hsmall : ediam s < ENNReal.ofReal (ε 1)) :
    T.mass s ≤ 2*(ediam s)^d := by
  by_cases hzero : ediam s = 0
  · rw [T.mass_zero_of_ediam_zero hs hzero ε hε hb gap]
    exact zero_le
  have hfin : ediam s ≠ ⊤ := hsmall.ne_top
  let r := (ediam s).toReal
  have hr : 0 < r := ENNReal.toReal_pos hzero hfin
  have hlt : r < ε 1 := by
    simpa [r, ENNReal.toReal_ofReal (hε 1).le] using
      (ENNReal.toReal_lt_toReal hfin ENNReal.ofReal_ne_top).mpr hsmall
  have hex : ∃ j : ℕ, 1 ≤ j ∧ ε j ≤ r := by
    have h₁ := hlim.eventually (gt_mem_nhds hr)
    obtain ⟨j, hj, h⟩ := ((Filter.eventually_ge_atTop 1).and h₁).exists
    exact ⟨j,hj,h.le⟩
  let j := Nat.find hex
  have hj : 1 ≤ j ∧ ε j ≤ r := Nat.find_spec hex
  have hj2 : 2 ≤ j := by
    by_contra! h
    have he : j = 1 := by omega
    exact hlt.not_ge (he ▸ hj.2)
  let n := j-1
  have hn : 1 ≤ n := by dsimp [n]; omega
  have hnj : n+1 = j := by dsimp [n]; omega
  have hel : ε (n+1) ≤ r := hnj.symm ▸ hj.2
  have heu : r < ε n := by
    by_contra! h
    have hjmin : j ≤ n := Nat.find_min' hex ⟨hn,h⟩
    omega
  have hsmall_n : ediam s < ENNReal.ofReal (ε n) := by
    apply (ENNReal.toReal_lt_toReal hfin ENNReal.ofReal_ne_top).mp
    simpa [ENNReal.toReal_ofReal (hε n).le] using heu
  have hcoarse := T.mass_le_single hs n (hε n) hsmall_n (gap n)
  have hfine := T.mass_le_pack hs hfin (n+1) (hε (n+1)) (gap (n+1))
  have hmin := le_min hcoarse hfine
  rw [← ENNReal.ofReal_min, size, Nat.cast_mul] at hmin
  have h := two_scale_estimate hd hd1 (hε (n+1)) hel
    (show (0:ℝ) < size T.arity n by exact_mod_cast T.size_pos n)
    (show (0:ℝ) < T.arity n by exact_mod_cast T.arity_pos n) (budget n hn)
  refine hmin.trans ((ENNReal.ofReal_le_ofReal h).trans_eq ?_)
  rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat,
    ← ENNReal.ofReal_rpow_of_nonneg hr.le hd.le, ENNReal.ofReal_toReal hfin]

/-- A nested interval tree has dimension at least d when each level provides enough
mass decay for the next level's total gap length. -/
theorem dimH_ge (d : ℝ≥0) (hd : 0 < d) (hd1 : d ≤ 1)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hlim : Filter.Tendsto ε Filter.atTop (𝓝 0))
    (hb : ∀ n, 2 ≤ T.arity n)
    (gap : ∀ n i j, i < j → j < size T.arity n → T.hi n i + ε n * ((j:ℝ)-i) ≤ T.lo n j)
    (budget : ∀ n ≥ 1, 1 ≤ (size T.arity n : ℝ) * ((T.arity n : ℝ)*ε (n+1))^(d:ℝ)) :
    (d : ℝ≥0∞) ≤ dimH T.limitSet := by
  have hdom : (2 : ℝ≥0∞)⁻¹ • T.mass ≤ μH[d] := by
    apply Measure.le_hausdorffMeasure (d:ℝ) _ (ENNReal.ofReal (ε 1 / 2))
      (by simpa using half_pos (hε 1))
    intro s hs
    let t := closure s
    have ht : ediam t = ediam s := Metric.ediam_closure s
    have hed : ediam t < ENNReal.ofReal (ε 1) := by
      rw [ht]
      exact hs.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (hε 1)).mpr (half_lt_self (hε 1)))
    have hbnd : T.mass s ≤ 2*(ediam s)^(d:ℝ) := by
      have hbnd := T.mass_ediam_bound (d := (d:ℝ)) (by exact_mod_cast hd)
        (by exact_mod_cast hd1) ε hε hlim hb gap budget isClosed_closure.measurableSet hed
      exact (measure_mono subset_closure).trans (ht ▸ hbnd)
    rw [Measure.smul_apply, smul_eq_mul]
    refine (mul_le_mul_right hbnd _).trans_eq ?_
    rw [← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
  have hpos : μH[d] T.limitSet ≠ 0 := by
    intro he
    have h := Measure.le_iff.mp hdom T.limitSet T.isClosed_limitSet.measurableSet
    rw [Measure.smul_apply, smul_eq_mul, T.mass_limitSet, he, mul_one] at h
    exact (by norm_num : ¬ ((2 : ℝ≥0∞)⁻¹ ≤ 0)) h
  exact le_dimH_of_hausdorffMeasure_ne_zero hpos

end IntervalTree

end MauldinCantor



open Set

namespace MauldinPacking

structure Children (f : ℝ → ℝ) (a b L h w : ℝ) (m : ℕ) where
  lo : Fin m → ℝ
  hi : Fin m → ℝ
  inside : ∀ i, a ≤ lo i ∧ hi i ≤ b
  length_le : ∀ i, 2*w/L ≤ hi i - lo i
  consecutive : ∀ (i j : Fin m), j.val = i.val+1 → hi i + h/(2*L) ≤ lo j
  window : ∀ i, ∃ k : ℤ, ∀ x ∈ Icc (lo i) (hi i), |f x - (k:ℝ)*h| ≤ w

private theorem increasing_children (f : ℝ → ℝ) {a b L h w : ℝ} {m : ℕ}
    (hab : a ≤ b) (hL : 0 < L) (hh : 0 < h) (hw : 0 < w) (hwh : 4*w ≤ h)
    (hcon : ContinuousOn f (Icc a b)) (hm : StrictMonoOn f (Icc a b))
    (hup : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |f y - f x| ≤ L * |y-x|)
    (hspan : ((m : ℝ)+2)*h ≤ f b - f a) :
    Nonempty (Children f a b L h w m) := by
  let k := ⌈(f a+w)/h⌉
  have hkl : f a+w ≤ (k:ℝ)*h := (div_le_iff₀ hh).mp (Int.le_ceil _)
  have hku : (k:ℝ)*h < f a+w+h := by
    have ht := (Int.ceil_lt_add_one ((f a+w)/h))
    have ht' := (mul_lt_mul_of_pos_right ht hh)
    rwa [add_mul, div_mul_cancel₀ _ hh.ne', one_mul] at ht'
  let g (i : Fin m) : ℝ := ((k + (i.val : ℤ) : ℤ):ℝ)*h
  have within (i : Fin m) : f a ≤ g i-w ∧ g i+w ≤ f b := by
    have hcast : (i.val:ℝ) < m := by exact_mod_cast i.isLt
    simp only [g, Int.cast_add, Int.cast_natCast, add_mul]
    have h₁ : 0 ≤ (i.val:ℝ)*h := by positivity
    have h₂ := mul_lt_mul_of_pos_right hcast hh
    constructor <;> nlinarith only [hkl,hku,h₁,h₂,hspan,hw,hwh,hh]
  have all (i : Fin m) : (g i-w) ∈ f '' Icc a b ∧ (g i+w) ∈ f '' Icc a b := by
    have hx := within i
    have hy : g i - w ≤ g i + w := by linarith
    exact ⟨intermediate_value_Icc hab hcon ⟨hx.1,hy.trans hx.2⟩,
      intermediate_value_Icc hab hcon ⟨hx.1.trans hy,hx.2⟩⟩
  choose l hl hlval using fun i => (all i).1
  choose r hr hrval using fun i => (all i).2
  have mback {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hxy : f x ≤ f y) : x ≤ y := by
    by_contra! he
    exact hxy.not_gt (hm hy hx he)
  have ller (i : Fin m) : l i ≤ r i :=
    mback (hl i) (hr i) (by rw [hlval,hrval]; linarith)
  refine ⟨⟨l,r,fun i => ⟨(hl i).1,(hr i).2⟩, ?_, ?_, ?_⟩⟩
  · intro i
    apply (div_le_iff₀ hL).mpr
    have hh' := hup (l i) (hl i) (r i) (hr i)
    rw [hlval, hrval, abs_of_nonneg (sub_nonneg.mpr (ller i)),
      abs_of_nonneg (by linarith : 0 ≤ (g i+w)-(g i-w))] at hh'
    linarith
  · intro i j hij
    have he : g j - g i = h := by
      simp only [g, hij, Int.cast_add, Int.cast_natCast, Nat.cast_add, Nat.cast_one]
      ring
    have hel : 0 < f (l j) - f (r i) := by rw [hlval,hrval]; linarith
    have hrl := mback (hr i) (hl j) (sub_nonneg.mp hel.le)
    have h' := hup (r i) (hr i) (l j) (hl j)
    rw [abs_of_pos hel, abs_of_nonneg (sub_nonneg.mpr hrl), hlval, hrval] at h'
    have hl' : h/(2*L) ≤ l j - r i := by
      apply (div_le_iff₀ (by positivity : 0 < 2*L)).mpr
      linarith only [h', he, hwh]
    linarith
  · intro i
    refine ⟨k+(i.val:ℤ), fun x hx => ?_⟩
    have hx' : x ∈ Icc a b := ⟨(hl i).1.trans hx.1,hx.2.trans (hr i).2⟩
    have hlx := hm.monotoneOn (hl i) hx' hx.1
    have hxr := hm.monotoneOn hx' (hr i) hx.2
    rw [hlval] at hlx
    rw [hrval] at hxr
    change |f x - g i| ≤ w
    exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Uniformly many separated children fit into an interval with a bi-Lipschitz image. -/
theorem exists_children (f : ℝ → ℝ) {a b L h w : ℝ} {m : ℕ}
    (hab : a ≤ b) (hL : 0 < L) (hh : 0 < h) (hw : 0 < w) (hwh : 4*w ≤ h)
    (hcon : ContinuousOn f (Icc a b))
    (hb : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b,
      |f y - f x| ≤ L * |y-x| ∧ |y-x| ≤ L * |f y-f x|)
    (hspan : ((m : ℝ)+2)*h ≤ (b-a)/L) :
    Nonempty (Children f a b L h w m) := by
  have hinj : InjOn f (Icc a b) := by
    intro x hx y hy he
    have hh := (hb x hx y hy).2
    rw [he, sub_self, abs_zero, mul_zero, abs_nonpos_iff, sub_eq_zero] at hh
    exact hh.symm
  have he : (b-a)/L ≤ |f b-f a| := by
    apply (div_le_iff₀ hL).mpr
    simpa [abs_of_nonneg (sub_nonneg.mpr hab), mul_comm] using
      (hb a ⟨le_rfl,hab⟩ b ⟨hab,le_rfl⟩).2
  rcases hcon.strictMonoOn_of_injOn_Icc' hab hinj with hinc | hdec
  · apply increasing_children f hab hL hh hw hwh hcon hinc (fun x hx y hy => (hb x hx y hy).1)
    exact hspan.trans (by simpa [abs_of_nonneg (sub_nonneg.mpr (hinc.monotoneOn
      ⟨le_rfl,hab⟩ ⟨hab,le_rfl⟩ hab))] using he)
  · let g (x : ℝ) := -f x
    have hmon : StrictMonoOn g (Icc a b) := fun x hx y hy hxy => neg_lt_neg (hdec hx hy hxy)
    have hhg : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |g y-g x| ≤ L*|y-x| := by
      intro x hx y hy
      have hEq : g y - g x = -(f y-f x) := by simp [g]; ring
      simpa only [hEq, abs_neg] using (hb x hx y hy).1
    have hspan' : ((m:ℝ)+2)*h ≤ g b - g a := by
      refine hspan.trans ?_
      rw [abs_of_nonpos (sub_nonpos.mpr (hdec.antitoneOn ⟨le_rfl,hab⟩ ⟨hab,le_rfl⟩ hab))] at he
      convert he using 1 <;> first | rfl | (simp [g]; ring)
    obtain ⟨P⟩ := increasing_children g hab hL hh hw hwh hcon.neg hmon hhg hspan'
    refine ⟨⟨P.lo, P.hi, P.inside, P.length_le, P.consecutive, fun i => ?_⟩⟩
    obtain ⟨k,hk⟩ := P.window i
    refine ⟨-k,fun x hx => ?_⟩
    have hEq : f x - ((-k : ℤ):ℝ)*h = -(g x - (k:ℝ)*h) := by simp [g]; ring
    simpa only [hEq, abs_neg] using hk x hx

end MauldinPacking



open Filter
open scoped Topology

namespace MauldinScale

/-- As the grid gets finer, the number of branches increases faster than the
d-power of the child intervals decreases. -/
theorem exists_scale {r d A C L ε M : ℝ} (hr : 0 < r) (hr₂ : 2*r < 1) (_hd : 0 ≤ d)
    (hrd : 1 < 2*r^d) (hA : 0 < A) (hC : 0 < C) (hL : 0 < L) (hε : 0 < ε) (hM : 0 < M)
    (n₀ : ℕ) :
    ∃ n : ℕ, n₀ < n ∧
      let h := (2 : ℝ)⁻¹ ^ n
      let w := r^n
      let m := ⌊A/(4*h)⌋₊
      4*w ≤ h ∧ h/(2*L) ≤ ε ∧ 2 ≤ m ∧ ((m:ℝ)+2)*h ≤ A ∧
        A/(16*L) ≤ (m:ℝ)*(h/(2*L)) ∧ 1 ≤ (M*m)*(C*w)^d := by
  have hh : Tendsto (fun n : ℕ => (2:ℝ)⁻¹ ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hr₀ : Tendsto (fun n : ℕ => (2*r)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hr₂
  have hbudget_pos : 0 < M*(A/8)*C^d := by positivity
  have hbudget : Tendsto (fun n : ℕ => (2*r^d)^n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hrd
  have e₁ : ∀ᶠ n : ℕ in atTop, (2:ℝ)⁻¹ ^ n < A/8 :=
    hh.eventually (gt_mem_nhds (by positivity))
  have e₂ : ∀ᶠ n : ℕ in atTop, (2:ℝ)⁻¹ ^ n < 2*L*ε :=
    hh.eventually (gt_mem_nhds (by positivity))
  have e₃ : ∀ᶠ n : ℕ in atTop, (2*r)^n < (1:ℝ)/4 :=
    hr₀.eventually (gt_mem_nhds (by norm_num))
  have e₄ : ∀ᶠ n : ℕ in atTop, (M*(A/8)*C^d)⁻¹ ≤ (2*r^d)^n :=
    (tendsto_atTop.1 hbudget) _
  obtain ⟨n,h₀,h₁,h₂,h₃,h₄⟩ :=
    ((eventually_gt_atTop n₀).and (e₁.and (e₂.and (e₃.and e₄)))).exists
  refine ⟨n,h₀,?_⟩
  dsimp
  set h : ℝ := (2:ℝ)⁻¹ ^ n with he
  set w : ℝ := r^n with we
  let q := A/(4*h)
  let m := ⌊q⌋₊
  have hhp : 0 < h := by rw [he]; positivity
  have hwp : 0 < w := by rw [we]; positivity
  have hq : 2 ≤ q := (le_div_iff₀ (by positivity : 0 < 4*h)).mpr (by linarith)
  have hm₀ : 2 ≤ m := (Nat.le_floor_iff (by positivity : 0 ≤ q)).mpr (by exact_mod_cast hq)
  have hm₁ : (m:ℝ) ≤ q := Nat.floor_le (by positivity)
  have hm₂ : q < (m:ℝ)+1 := Nat.lt_floor_add_one _
  have hm₃ : A/(8*h) ≤ (m:ℝ) := by
    have heq : A/(8*h) = q/2 := by dsimp [q]; field_simp; ring
    rw [heq]
    linarith [show (2:ℝ) ≤ (m:ℝ) by exact_mod_cast hm₀]
  have hwsmall : 4*w ≤ h := by
    rw [mul_pow, ← we] at h₃
    have hh' : 0 < (2:ℝ)^n := by positivity
    rw [he, inv_pow, ← one_div]
    exact (le_div_iff₀ hh').mpr (by nlinarith)
  have hese : h/(2*L) ≤ ε := (div_le_iff₀ (by positivity)).mpr (by nlinarith)
  have hmspan : ((m:ℝ)+2)*h ≤ A := by
    have hq' : q*h = A/4 := by dsimp [q]; field_simp
    have hmB := mul_le_mul_of_nonneg_right (show (m:ℝ)+2 ≤ 2*q by linarith) hhp.le
    nlinarith
  have hg : A/(16*L) ≤ (m:ℝ)*(h/(2*L)) := by
    have h' := mul_le_mul_of_nonneg_right hm₃ (show 0 ≤ h/(2*L) by positivity)
    have hEq : A/(8*h)*(h/(2*L)) = A/(16*L) := by field_simp; ring
    rwa [hEq] at h'
  refine ⟨hwsmall,hese,hm₀,hmspan,hg,?_⟩
  have hb : M*(A/8)*C^d * (2*r^d)^n ≤ (M*m)*(C*w)^d := by
    have hrpow : (w:ℝ)^d = (r^d)^n := by
      rw [we, ← Real.rpow_natCast, ← Real.rpow_mul hr.le, mul_comm, Real.rpow_mul hr.le, Real.rpow_natCast]
    have heq : M*(A/8)*C^d*(2*r^d)^n = (M*(A/(8*h)))*(C*w)^d := by
      rw [mul_pow, Real.mul_rpow hC.le hwp.le, hrpow, he, inv_pow]
      have hpow : (2:ℝ)^n ≠ 0 := by positivity
      field_simp
    rw [heq]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm₃ hM.le) (by positivity)
  exact (show 1 ≤ M*(A/8)*C^d*(2*r^d)^n by
    simpa only [mul_comm ((2*r^d)^n)] using (inv_le_iff_one_le_mul₀ hbudget_pos).mp h₄).trans hb

end MauldinScale

namespace MauldinConstruction

open Set MeasureTheory
open scoped Topology ENNReal NNReal
open MauldinRecursion MauldinScale MauldinPacking

private def loss (g : ℕ → RationalPair) (n : ℕ) : ℝ :=
  (4:ℝ)^(g (n+1)).exceptional.card

private theorem loss_pos (g : ℕ → RationalPair) (n : ℕ) : 0 < loss g n := by
  unfold loss
  positivity

/-- A level of intervals and the constants needed to refine it. -/
private structure Layer (g : ℕ → RationalPair) (d : ℝ) (n : ℕ) where
  count : ℕ
  count_pos : 0 < count
  lo : Fin count → ℝ
  hi : Fin count → ℝ
  δ : ℝ
  δpos : 0 < δ
  length_lower : ∀ i, δ ≤ hi i - lo i
  ε : ℝ
  εpos : 0 < ε
  scale : ℕ
  εsmall : ε ≤ (2:ℝ)⁻¹ ^ scale
  adjacent : ∀ (i j : Fin count), j.val = i.val+1 → hi i + ε ≤ lo j
  L : ℝ
  Lge : 1 ≤ L
  continuous : ∀ i, ContinuousOn (g n).eval (Icc (lo i) (hi i))
  compare : ∀ i, ∀ x ∈ Icc (lo i) (hi i), ∀ y ∈ Icc (lo i) (hi i),
    |(g n).eval y - (g n).eval x| ≤ L * |y-x| ∧
    |y-x| ≤ L * |(g n).eval y - (g n).eval x|
  budget : 0 < n → 1 ≤ (count:ℝ) * (δ/(16*L^2*loss g n))^d

private theorem Layer.valid {g : ℕ → RationalPair} {d : ℝ} {n : ℕ} (S : Layer g d n)
    (i : Fin S.count) : S.lo i ≤ S.hi i := by
  have := S.length_lower i
  linarith [S.δpos]

private theorem Layer.gap {g : ℕ → RationalPair} {d : ℝ} {n : ℕ} (S : Layer g d n)
    {i j : Fin S.count} (hij : i < j) :
    S.hi i + S.ε * ((j.val:ℝ)-i.val) ≤ S.lo j := by
  have aux (t : ℕ) (jt : i.val+t < S.count) (ht : 0<t) :
      S.hi i + S.ε*(t:ℝ) ≤ S.lo ⟨i.val+t,jt⟩ := by
    induction t with
    | zero => omega
    | succ t ih =>
      let j' : Fin S.count := ⟨i.val+t, by omega⟩
      have h := S.adjacent j' ⟨i.val+t+1,jt⟩ rfl
      rcases Nat.eq_zero_or_pos t with he | hp
      · subst t
        have heq : j' = i := Fin.ext (Nat.add_zero _)
        simpa [heq] using h
      · have h1 := ih j'.isLt hp
        have h2 := S.valid j'
        push_cast
        change S.hi i + S.ε*((t:ℝ)+1) ≤ S.lo ⟨i.val+t+1,jt⟩
        linarith only [h1,h2,h]
  have ht : 0 < j.val-i.val := Nat.sub_pos_of_lt hij
  have he : i.val+(j.val-i.val) = j.val := Nat.add_sub_of_le hij.le
  have hjt : i.val+(j.val-i.val) < S.count := he.symm ▸ j.isLt
  have h := aux (j.val-i.val) hjt ht
  rw [Nat.cast_sub hij.le] at h
  convert h using 1
  exact congrArg S.lo (Fin.ext he.symm)

private theorem first_layer (g : ℕ → RationalPair) (d : ℝ) :
    ∃ S : Layer g d 0, S.count = 1 := by
  obtain ⟨u,v,_,_,huv,_,hgood⟩ := trim_interval (g 0).exceptional (show (0:ℝ)<1 by norm_num)
  obtain ⟨L,hL,hc,hcomp⟩ := (g 0).interval_comparison huv.le hgood
  refine ⟨{
    count := 1
    count_pos := by decide
    lo := fun _ => u
    hi := fun _ => v
    δ := v-u
    δpos := sub_pos.mpr huv
    length_lower := fun _ => le_rfl
    ε := 1
    εpos := by norm_num
    scale := 0
    εsmall := by simp
    adjacent := fun i j h => by have := j.isLt; omega
    L := L
    Lge := hL
    continuous := fun _ => hc
    compare := fun _ => hcomp
    budget := fun h => False.elim (Nat.lt_irrefl _ h)
  }, rfl⟩

private def parentIndex {M m : ℕ} (hm : 0 < m) {i : ℕ} (hi : i < M*m) : Fin M :=
  ⟨i/m,(Nat.div_lt_iff_lt_mul hm).mpr hi⟩

private def localIndex {m : ℕ} (hm : 0 < m) (i : ℕ) : Fin m := ⟨i%m,Nat.mod_lt _ hm⟩

/-- The links from a new level to its parents and approximation scale. -/
private structure Step {g : ℕ → RationalPair} {d : ℝ} {n : ℕ} (S : Layer g d n) (r : ℝ) where
  children : ℕ
  children_ge : 2 ≤ children
  layer : Layer g d (n+1)
  size : layer.count = S.count*children
  subset_parent : ∀ (i : Fin layer.count),
    let p := parentIndex (M := S.count) (m := children) (i := i.val) (by omega)
      (by simpa only [← size] using i.isLt)
    Icc (layer.lo i) (layer.hi i) ⊆ Icc (S.lo p) (S.hi p)
  scale_gt : S.scale < layer.scale
  budget_factor : S.δ/(16*S.L^2*loss g n) ≤ (children:ℝ)*layer.ε
  window : ∀ i, ∃ k : ℤ, ∀ x ∈ Icc (layer.lo i) (layer.hi i),
    |(g n).eval x - (k:ℝ)*(2:ℝ)⁻¹ ^ layer.scale| ≤ r^layer.scale

private theorem next_layer {g : ℕ → RationalPair} {d r : ℝ} {n : ℕ}
    (hd : 0 ≤ d) (hr : 0 < r) (hr₂ : 2*r < 1) (hrd : 1 < 2*r^d)
    (S : Layer g d n) : Nonempty (Step S r) := by
  classical
  have trim (i : Fin S.count) := trim_interval (g (n+1)).exceptional
    (show S.lo i < S.hi i by linarith [S.δpos,S.length_lower i])
  choose u v hu hv huv hlen hgood using trim
  have comp (i : Fin S.count) := (g (n+1)).interval_comparison (huv i).le (hgood i)
  choose Lp hLp hcont hpcomp using comp
  let Ll : ℝ := 1+∑ i, Lp i
  have hLl1 : 1 ≤ Ll := le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => (hLp i).trans' zero_le_one))
  have hLl (i : Fin S.count) : Lp i ≤ Ll := by
    have h := Finset.single_le_sum (f := Lp)
      (fun j _ => zero_le_one.trans (hLp j)) (Finset.mem_univ i)
    exact h.trans (le_add_of_nonneg_left zero_le_one)
  have ccont (i : Fin S.count) := hcont i
  have ccomp (i : Fin S.count) (x : ℝ) (hx : x ∈ Icc (u i) (v i))
      (y : ℝ) (hy : y ∈ Icc (u i) (v i)) :
      |(g (n+1)).eval y-(g (n+1)).eval x| ≤ Ll*|y-x| ∧
        |y-x| ≤ Ll*|(g (n+1)).eval y-(g (n+1)).eval x| := by
    exact ⟨((hpcomp i x hx y hy).1).trans (mul_le_mul_of_nonneg_right (hLl i) (abs_nonneg _)),
      ((hpcomp i x hx y hy).2).trans (mul_le_mul_of_nonneg_right (hLl i) (abs_nonneg _))⟩
  let A := S.δ/(S.L*loss g n)
  let C := (2/S.L)/(16*Ll^2*loss g (n+1))
  have hL0 : 0 < S.L := zero_lt_one.trans_le S.Lge
  have hLl0 : 0 < Ll := zero_lt_one.trans_le hLl1
  have hposA : 0 < A := div_pos S.δpos (mul_pos hL0 (loss_pos g n))
  have hposC : 0 < C := by dsimp [C]; have := loss_pos g (n+1); positivity
  have hposM : (0:ℝ) < S.count := by exact_mod_cast S.count_pos
  obtain ⟨scale,hscale,hwsmall,heps,hm,hmspan,hbudgetf,hbudget⟩ :=
    exists_scale hr hr₂ hd hrd hposA hposC hL0 S.εpos hposM S.scale
  let h := (2:ℝ)⁻¹ ^ scale
  let w := r^scale
  let m := ⌊A/(4*h)⌋₊
  have hmpos : 0 < m := lt_of_lt_of_le (by decide) hm
  have hh : 0 < h := by dsimp [h]; positivity
  have hw : 0 < w := by dsimp [w]; positivity
  have all (i : Fin S.count) : Nonempty (Children (g n).eval (u i) (v i) S.L h w m) := by
    let hs : Icc (u i) (v i) ⊆ Icc (S.lo i) (S.hi i) := Icc_subset_Icc (hu i) (hv i)
    apply exists_children (g n).eval (huv i).le hL0 hh hw hwsmall
      ((S.continuous i).mono hs) (fun x hx y hy => S.compare i x (hs hx) y (hs hy))
    refine hmspan.trans ?_
    have hδ : S.δ/loss g n ≤ v i-u i :=
      (div_le_div_of_nonneg_right (S.length_lower i) (loss_pos g n).le).trans (hlen i)
    have hdiv := div_le_div_of_nonneg_right hδ hL0.le
    unfold A
    rwa [div_div, mul_comm (loss g n) S.L] at hdiv
  let P (i : Fin S.count) := Classical.choice (all i)
  let parent (i : Fin (S.count*m)) := parentIndex hmpos i.isLt
  let childIndex (i : Fin (S.count*m)) := localIndex hmpos i.val
  let lo (i : Fin (S.count*m)) := (P (parent i)).lo (childIndex i)
  let hi (i : Fin (S.count*m)) := (P (parent i)).hi (childIndex i)
  have hcontain (i : Fin (S.count*m)) : Icc (lo i) (hi i) ⊆ Icc (u (parent i)) (v (parent i)) :=
    Icc_subset_Icc ((P (parent i)).inside (childIndex i)).1 ((P (parent i)).inside (childIndex i)).2
  have hadj (i j : Fin (S.count*m)) (hij : j.val=i.val+1) :
      hi i + h/(2*S.L) ≤ lo j := by
    by_cases hp : parent i = parent j
    · have h1 := Nat.mod_add_div i.val m
      have h2 := Nat.mod_add_div j.val m
      have hpv : i.val/m=j.val/m := congrArg Fin.val hp
      rw [hpv] at h1
      have hloc : (childIndex j).val = (childIndex i).val+1 := by
        change j.val % m = i.val % m + 1
        omega
      change (P (parent i)).hi (childIndex i) + _ ≤ (P (parent j)).lo (childIndex j)
      rw [← hp]
      exact (P (parent i)).consecutive _ _ hloc
    · have hle : parent i ≤ parent j := Nat.div_le_div_right (by omega)
      have hlt : parent i < parent j := lt_of_le_of_ne hle hp
      have hg := S.gap hlt
      have hjump : 1 ≤ ((parent j).val:ℝ)-(parent i).val := by
        have h' : ((parent i).val:ℝ)+1 ≤ (parent j).val := by exact_mod_cast hlt
        linarith
      have hg' := mul_le_mul_of_nonneg_left hjump S.εpos.le
      have hip : hi i ≤ S.hi (parent i) := ((P (parent i)).inside (childIndex i)).2.trans (hv _)
      have hjp : S.lo (parent j) ≤ lo j := (hu _).trans ((P (parent j)).inside (childIndex j)).1
      rw [mul_one] at hg'
      calc
        _ ≤ S.hi (parent i) + S.ε := add_le_add hip heps
        _ ≤ S.hi (parent i) + S.ε * (((parent j).val:ℝ)-(parent i).val) :=
          add_le_add (le_refl _) hg'
        _ ≤ S.lo (parent j) := hg
        _ ≤ _ := hjp
  let T : Layer g d (n+1) :=
    { count := S.count*m, count_pos := Nat.mul_pos S.count_pos hmpos,
      lo := lo, hi := hi, δ := 2*w/S.L, δpos := by positivity,
      length_lower := fun i => (P (parent i)).length_le (childIndex i),
      ε := h/(2*S.L), εpos := by positivity, scale := scale,
      εsmall := (div_le_self hh.le (by linarith [S.Lge])),
      adjacent := hadj, L := Ll, Lge := hLl1,
      continuous := fun i => (ccont _).mono (hcontain i),
      compare := fun i x hx y hy => ccomp _ x (hcontain i hx) y (hcontain i hy),
      budget := fun _ => by
        rw [Nat.cast_mul]
        have he : (2*w/S.L)/(16*Ll^2*loss g (n+1)) = C*w := by
          unfold C
          ring
        rw [he]
        exact hbudget }
  refine ⟨⟨m,hm,T,rfl,?_,hscale,?_,?_⟩⟩
  · intro i
    exact (hcontain i).trans (Icc_subset_Icc (hu _) (hv _))
  · have he : S.δ/(16*S.L^2*loss g n) = A/(16*S.L) := by
      unfold A
      rw [div_div]
      ring
    rwa [he]
  · exact fun i => (P (parent i)).window (childIndex i)

end MauldinConstruction
namespace MauldinConstruction

open MauldinRecursion

private theorem large_preimage_at_exponent {r d : ℝ} (hr : 0 < r) (hr₂ : 2*r < 1)
    (dpos : 0 < d) (dlt : d ≤ 1) (hrd : 1 < 2*r^d) (f : ℕ → RationalPair) :
    (ENNReal.ofReal d) ≤ dimH {x : ℝ | ∀ n, (f n).eval x ∈ MauldinDyadic.core (ENNReal.ofReal r)} := by
  classical
  let g (n : ℕ) := f (Nat.unpair n).1
  let layer : (n : ℕ) → Layer g d n :=
    Nat.rec (first_layer g d).choose
      (fun _ L => (Classical.choice (next_layer dpos.le hr hr₂ hrd L)).layer)
  let step (n : ℕ) : Step (layer n) r := Classical.choice (next_layer dpos.le hr hr₂ hrd (layer n))
  let ar (n : ℕ) := (step n).children
  have size_eq (n : ℕ) : MauldinCantor.size ar n = (layer n).count := by
    induction n with
    | zero => exact (first_layer g d).choose_spec.symm
    | succ n ih =>
      change MauldinCantor.size ar n * (step n).children = (step n).layer.count
      rw [ih,(step n).size]
  let lo (n i : ℕ) := if h : i < (layer n).count then (layer n).lo ⟨i,h⟩ else 0
  let hi (n i : ℕ) := if h : i < (layer n).count then (layer n).hi ⟨i,h⟩ else 0
  have arge (n : ℕ) : 2 ≤ ar n := (step n).children_ge
  have idxlt (n i : ℕ) (h : i < MauldinCantor.size ar n) : i < (layer n).count := by
    rwa [← size_eq]
  let T : MauldinCantor.IntervalTree :=
    { arity := ar, arity_pos := fun n => by have := arge n; omega
      lo := lo, hi := hi
      valid := fun n i h => by
        have h' := idxlt n i h
        simpa only [lo,hi,dif_pos h'] using (layer n).valid ⟨i,h'⟩
      nested := fun n i h => by
        have h' := idxlt (n+1) i h
        let j : Fin (layer (n+1)).count := ⟨i,h'⟩
        have hpar : i/ar n < (layer n).count := by
          apply (Nat.div_lt_iff_lt_mul (by have := arge n; omega : 0 < ar n)).mpr
          exact (step n).size ▸ h'
        have hs := (step n).subset_parent j
        change Icc ((layer (n+1)).lo j) ((layer (n+1)).hi j) ⊆
          Icc ((layer n).lo ⟨i / ar n,hpar⟩) ((layer n).hi ⟨i / ar n,hpar⟩) at hs
        simpa only [lo,hi,dif_pos h',dif_pos hpar,j] using hs }
  let ε (n : ℕ) := (layer n).ε
  have hscale (n : ℕ) : n ≤ (layer n).scale := by
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih => exact (Nat.succ_le_succ ih).trans (step n).scale_gt
  have hεlim : Filter.Tendsto ε Filter.atTop (𝓝 0) := by
    apply squeeze_zero (fun n => (layer n).εpos.le)
      (fun n => (layer n).εsmall.trans
        (pow_le_pow_of_le_one (by norm_num) (by norm_num) (hscale n)))
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 2⁻¹) (by norm_num)
  have dHaus : (ENNReal.ofReal d) ≤ dimH T.limitSet := by
    have hh := T.dimH_ge (Real.toNNReal d) (by simpa using dpos) (by simpa using dlt)
      ε (fun n => (layer n).εpos) hεlim arge
    rw [Real.coe_toNNReal _ dpos.le] at hh
    apply hh
    · intro n i j hij hj
      have hj' := idxlt n j hj
      have hi' := hij.trans hj'
      simpa only [T,lo,hi,dif_pos hi',dif_pos hj'] using
        (layer n).gap (i := ⟨i,hi'⟩) (j := ⟨j,hj'⟩) hij
    · intro n hn
      change 1 ≤ (MauldinCantor.size ar n : ℝ)*((ar n:ℝ)*ε (n+1))^d
      rw [size_eq]
      have hbase : 0 ≤ (layer n).δ / (16*(layer n).L^2*loss g n) :=
        div_nonneg (layer n).δpos.le (by have := (loss_pos g n).le; positivity)
      exact ((layer n).budget hn).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hbase (step n).budget_factor dpos.le) (Nat.cast_nonneg _))
  refine dHaus.trans (dimH_mono ?_)
  intro x hx n K
  let j := Nat.pair n K
  let scale := (layer (j+1)).scale
  have hK : K ≤ scale := (Nat.right_le_pair _ _).trans
    ((Nat.le_succ j).trans (hscale (j+1)))
  obtain ⟨i, hi'⟩ := mem_iUnion.mp (mem_iInter.mp hx (j+1))
  have hzi : i.val < (layer (j+1)).count := idxlt (j+1) i.val i.isLt
  let z : Fin (layer (j+1)).count := ⟨i.val,hzi⟩
  have hm : x ∈ Icc ((layer (j+1)).lo z) ((layer (j+1)).hi z) := by
    simpa only [MauldinCantor.IntervalTree.piece,T,lo,hi,dif_pos hzi,z] using hi'
  obtain ⟨k,hk⟩ := (step j).window z
  have he : (Nat.unpair j).1 = n := by simp [j, Nat.unpair_pair]
  have hdist := hk x hm
  change |(f (Nat.unpair j).1).eval x - (k:ℝ)*(2:ℝ)⁻¹ ^ scale| ≤ r^scale at hdist
  rw [he] at hdist
  refine ⟨scale,hK,k,?_⟩
  rw [Metric.mem_closedEBall, edist_dist, Real.dist_eq, ← ENNReal.ofReal_pow hr.le]
  apply ENNReal.ofReal_le_ofReal
  simpa only [MauldinDyadic.grid, inv_pow, div_eq_mul_inv] using hdist

private theorem real_parameter_props {a d : ℝ} (ha : 0 < a) (ha1 : a < 1) (hd : d < a) :
    let r := (2:ℝ)^(-a⁻¹)
    0 < r ∧ 2*r < 1 ∧ 1 < 2*r^d := by
  let r := (2:ℝ)^(-a⁻¹)
  have hratio : (1:ℝ) < a⁻¹ := by
    rw [← one_div]
    exact (lt_div_iff₀ ha).mpr (by simpa using ha1)
  have hrpw : r < (2:ℝ)^(-1:ℝ) := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
  rw [Real.rpow_neg_one] at hrpw
  refine ⟨by positivity, by linarith,?_⟩
  have hratio' : d/a < 1 := (div_lt_iff₀ ha).mpr (by simpa using hd)
  have hexp : 0 < 1+(-a⁻¹)*d := by rw [div_eq_mul_inv] at hratio'; nlinarith
  have he : 2*r^d = (2:ℝ)^(1+(-a⁻¹)*d) := by
    unfold r
    rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),Real.rpow_add (by norm_num),Real.rpow_one]
  rw [he]
  simpa only [Real.rpow_zero] using
    (Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ)<2) hexp)

theorem commonPreimageLarge {a : ℝ≥0} (ha : 0 < a) (ha1 : a < 1) :
    CommonPreimageLarge (MauldinDyadic.envelope a) (a:ℝ≥0∞) := by
  intro f
  by_contra! hbad
  obtain ⟨d, hdim, hda⟩ := exists_between hbad
  have hdt : d ≠ ⊤ := hda.ne_top
  lift d to ℝ≥0 using hdt
  have hd : 0 < d := by exact_mod_cast (zero_le.trans_lt hdim)
  have hda' : d < a := by exact_mod_cast hda
  let r := (2:ℝ)^(-(a:ℝ)⁻¹)
  have hrs := real_parameter_props (a := (a:ℝ)) (d := (d:ℝ)) (by exact_mod_cast ha)
    (by exact_mod_cast ha1) (by exact_mod_cast hda')
  change 0 < r ∧ 2*r < 1 ∧ 1 < 2*r^(d:ℝ) at hrs
  obtain ⟨hr,hr₂,hrd⟩ := hrs
  have hR : ENNReal.ofReal r = MauldinDyadic.parameter a := by
    unfold r MauldinDyadic.parameter
    rw [← ENNReal.ofReal_rpow_of_pos (by norm_num : (0:ℝ) < 2), ENNReal.ofReal_ofNat]
  have h := large_preimage_at_exponent hr hr₂ (by exact_mod_cast hd)
    (by exact_mod_cast hda'.le.trans ha1.le : (d:ℝ) ≤ 1) hrd f
  rw [hR, ENNReal.ofReal_coe_nnreal] at h
  exact hdim.not_ge (h.trans (dimH_mono (fun x hx n => Or.inr (hx n))))

end MauldinConstruction

private theorem mauldin_ch_zero.{u} (h : (ℵ₁ : Cardinal.{u}) = 𝔠) :
    (ℵ₁ : Cardinal.{0}) = 𝔠 :=
  Cardinal.lift_inj.{0,u}.mp (by simpa using h)

/-- Mauldin's theorem under CH, using the dyadic construction of rational common preimages
from the geometric part of Wang's proof, arXiv:2610.09707v1, §3. -/
theorem OMA.solution : type_of% @Erdos1154.erdos_1154.variants.continuumHypothesis_field := by
  intro a ha hCH
  let : Fact ((ℵ₁ : Cardinal.{0}) = 𝔠) := ⟨mauldin_ch_zero hCH.out⟩
  rcases eq_or_lt_of_le ha.1 with hzero | hpos
  · rw [← hzero]
    exact Erdos1154.erdos_1154.variants.exists_subfield_dimH_eq_zero
  by_cases h1 : a = 1
  · rw [h1]
    exact Erdos1154.erdos_1154.variants.exists_subfield_dimH_eq_one
  have hlt : a < 1 := lt_of_le_of_ne ha.2 h1
  have ht : a ≠ ⊤ := hlt.ne_top
  lift a to ℝ≥0 using ht
  have ha0 : 0 < a := by exact_mod_cast hpos
  have ha1 : a < 1 := by exact_mod_cast hlt
  exact MauldinRecursion.exists_subfield_of_extension hpos (MauldinDyadic.envelope a)
    (MauldinDyadic.dimH_envelope_le ha0) (MauldinDyadic.bottom_subset a)
    (MauldinRecursion.extension_of_commonPreimageLarge (MauldinConstruction.commonPreimageLarge ha0 ha1))